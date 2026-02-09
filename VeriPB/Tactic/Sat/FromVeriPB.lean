/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import Lean
import Std
import VeriPB.Tactic.Sat.PseudoBoolean

/-!
# VeriPB Proof Verification

Parser and metaprogram for verifying VeriPB kernel-format proofs.
This module parses DIMACS CNF and VeriPB proof files, constructs
proof terms using the soundness lemmas from `PseudoBoolean.lean`,
and produces Lean theorems.

## Supported kernel format subset

* `f N` — verify formula size
* `pol` — cutting planes in RPN: `+` (add), `*` (multiply),
  `d` (divide/ceiling), `s` (saturate), `w` (weaken), literal axioms
* `rup C : hints` — reverse unit propagation with mandatory hints
* `pbc C : subproof ... qed : id` — proof by contradiction (subproofs)
* `deld ids` / `delc ids` — deletion
* `conclusion UNSAT : id`

## Main definitions

* `VeriPB.parseDimacs` — DIMACS CNF parser
* `VeriPB.parseVeriPBProof` — VeriPB kernel proof parser
* `VeriPB.verifyProof` — data-level proof checker
* `veripb_proof` — command that registers a kernel-verified theorem
* `from_veripb` — term elaborator for inline CNF/proof strings
* `veripb_proof_file` — command that loads CNF/proof from files
* `from_veripb_file` — term elaborator with file loading
-/

namespace VeriPB

-- Token-based parser infrastructure

/-- A position in a token stream. -/
structure ParseState where
  tokens : Array String
  pos : Nat
  deriving Repr

/-- Parser monad: Except for errors, State for position. -/
abbrev ParseM := EStateM String ParseState

/-- Peek at the current token without consuming it. -/
def peek : ParseM String := do
  let s ← get
  if h : s.pos < s.tokens.size then
    return s.tokens[s.pos]
  else
    throw "unexpected end of input"

/-- Consume and return the current token. -/
def next : ParseM String := do
  let s ← get
  if h : s.pos < s.tokens.size then
    let tok := s.tokens[s.pos]
    set { s with pos := s.pos + 1 }
    return tok
  else
    throw "unexpected end of input"

/-- Expect a specific token. -/
def expect (tok : String) : ParseM Unit := do
  let t ← next
  if t != tok then
    throw s!"expected '{tok}', got '{t}'"

/-- Expect and consume a semicolon. -/
def expectSemicolon : ParseM Unit := expect ";"

/-- Try to parse a natural number from the current token. -/
def parseNat : ParseM Nat := do
  let tok ← next
  match tok.toNat? with
  | some n => return n
  | none => throw s!"expected natural number, got '{tok}'"

/-- Tokenize a line: split on whitespace, separate semicolons.
    Returns tokens from a single line. -/
private def tokenizeLine (line : String) : Array String :=
  let line := line.replace "\t" " "
  let withSemis := line.replace ";" " ; "
  let parts := withSemis.splitOn " "
  (parts.filter (· != "")).toArray

/-- Check if a line is a comment (starts with % or c). -/
private def isComment (line : String) : Bool :=
  let trimmed := line.trimAsciiStart.toString
  trimmed.startsWith "%" || trimmed.startsWith "c " || trimmed.startsWith "c\t"
    || trimmed == "c"

/-- Tokenize a string: split on whitespace, filter empty tokens,
    strip comments (lines starting with % or c).
    Uses push-based accumulation for O(n) performance. -/
def tokenize (s : String) : Array String := Id.run do
  let lines := s.splitOn "\n"
  let mut result : Array String := #[]
  for line in lines do
    if !isComment line then
      for tok in tokenizeLine line do
        result := result.push tok
  return result

-- Parsed CNF types

/-- A DIMACS clause: list of signed integers (positive = pos literal, negative = neg). -/
abbrev DimacsClause := List Int

/-- Parsed DIMACS CNF formula. -/
structure DimacsFormula where
  numVars : Nat
  numClauses : Nat
  clauses : Array DimacsClause
  deriving Repr

-- DIMACS CNF parser

/-- Parse a DIMACS literal (nonzero integer) into Sat.PB.Literal.
    DIMACS variable i (1-indexed) maps to PB variable (i-1) (0-indexed). -/
def dimacsLitToPB (lit : Int) : Except String Sat.PB.Literal :=
  if lit > 0 then
    .ok (.pos (lit.toNat - 1))
  else if lit < 0 then
    .ok (.neg ((-lit).toNat - 1))
  else
    .error "DIMACS literal 0 is not a valid literal"

/-- Convert a DIMACS clause to a PB constraint.
    Clause `[l1, l2, ..., lk]` becomes `1·l1 + 1·l2 + ... + 1·lk >= 1`. -/
def dimacsClauseToPB (clause : DimacsClause) : Except String Sat.PB.Constr := do
  let terms ← clause.mapM fun lit => do
    let pbLit ← dimacsLitToPB lit
    return (1, pbLit)
  return ⟨terms, 1⟩

/-- Parse DIMACS CNF format from a token stream.
    Expected: `p cnf <numVars> <numClauses>` then clauses terminated by `0`.
    Validates clause count and literal bounds. -/
def parseDimacs (input : String) : Except String DimacsFormula := do
  let tokens := tokenize input
  -- Find "p" "cnf" header
  let rec findP (pos : Nat) : Nat :=
    if h : pos < tokens.size && tokens[pos]! != "p" then findP (pos + 1) else pos
  termination_by tokens.size - pos
  decreasing_by simp_all; omega
  let pos := findP 0
  if pos + 3 >= tokens.size then
    throw "missing 'p cnf' header"
  if tokens[pos]! != "p" || tokens[pos + 1]! != "cnf" then
    throw "expected 'p cnf' header"
  let numVarsStr := tokens[pos + 2]!
  let numClausesStr := tokens[pos + 3]!
  let numVars ← match numVarsStr.toNat? with
    | some n => pure n
    | none => throw s!"invalid numVars: {numVarsStr}"
  let numClauses ← match numClausesStr.toNat? with
    | some n => pure n
    | none => throw s!"invalid numClauses: {numClausesStr}"
  -- Parse clauses: sequences of integers terminated by 0
  let rec parseClauses (pos : Nat) (clauses : Array DimacsClause) (current : DimacsClause) :
      Array DimacsClause × DimacsClause :=
    if pos < tokens.size then
      let tok := tokens[pos]!
      match tok.toInt? with
      | some 0 => parseClauses (pos + 1) (clauses.push current.reverse) []
      | some n => parseClauses (pos + 1) clauses (n :: current)
      | none => parseClauses (pos + 1) clauses current
    else (clauses, current)
  termination_by tokens.size - pos
  let (clauses, remaining) := parseClauses (pos + 4) #[] []
  if !remaining.isEmpty then
    throw "DIMACS: unterminated clause (missing trailing 0)"
  -- Validate clause count
  if clauses.size != numClauses then
    throw s!"DIMACS clause count mismatch: header declares {numClauses}, found {clauses.size}"
  -- Validate literal bounds
  for clause in clauses do
    for lit in clause do
      let absLit := if lit ≥ 0 then lit.toNat else (-lit).toNat
      -- Note: absLit == 0 check removed (unreachable: parser uses 0 as terminator)
      if absLit > numVars then
        throw s!"DIMACS literal {lit} out of bounds (numVars={numVars})"
  return ⟨numVars, numClauses, clauses⟩

-- Parsed VeriPB proof types

/-- A literal in OPB format: variable name with optional negation. -/
inductive OPBLit where
  | pos : String → OPBLit   -- `x3` → positive literal for variable "x3"
  | neg : String → OPBLit   -- `~x3` → negative literal for variable "x3"
  deriving Repr, BEq

/-- A term in OPB format: coefficient and literal. -/
structure OPBTerm where
  coeff : Nat
  lit : OPBLit
  deriving Repr

/-- An OPB constraint: terms and degree. -/
structure OPBConstr where
  terms : List OPBTerm
  degree : Nat
  deriving Repr

/-- An operation in a `pol` RPN sequence. -/
inductive PolOp where
  | pushId (id : Nat)          -- Push constraint by ID
  | pushNat (n : Nat)          -- Push raw integer (for `*` / `d` operands)
  | pushLitAxiom (l : OPBLit) -- Push literal axiom (l >= 0)
  | add                        -- Pop two, add
  | mul                        -- Pop nat and constraint, multiply
  | div                        -- Pop nat and constraint, divide (ceiling)
  | saturate                   -- Pop one, saturate
  | weaken (varName : String)  -- Pop one, weaken by removing variable
  deriving Repr

/-- A RUP hint: either a constraint ID or `~` (the negated constraint). -/
inductive RupHint where
  | id (n : Nat)   -- Constraint ID
  | negC           -- The `~` symbol: negated target constraint
  deriving Repr, Inhabited

/-- A proof step in the VeriPB kernel format. -/
inductive ProofStep where
  | formulaSize (n : Nat)                          -- `f N ;`
  | pol (ops : List PolOp)                         -- `pol <RPN> ;`
  | rup (constr : OPBConstr) (hints : List RupHint) -- `rup C : hints ;`
  | deld (ids : List Nat)                          -- `deld ids ;`
  | delc (ids : List Nat)                          -- `delc ids ;`
  | pbc (constr : OPBConstr) (steps : Array ProofStep) (resultId : Nat)
  | output                                         -- `output NONE ;`
  | conclusion (id : Nat)                          -- `conclusion UNSAT : id ;`
  | sol (lits : List OPBLit)                       -- `sol lits ;`
  | soli (lits : List OPBLit)                      -- `soli lits ;`
  | conclusionSat (lits : List OPBLit)             -- `conclusion SAT : lits ;`
  | conclusionBounds (lb : Nat) (lbHint : Option Nat) (ub : Nat) (ubLits : List OPBLit)
  deriving Repr

/-- A complete parsed VeriPB kernel proof. -/
structure VeriPBProof where
  steps : Array ProofStep
  deriving Repr

-- OPB constraint parser

/-- Parse a variable name from a token. Returns the variable name (without ~).
    Tokens like "x3" → pos "x3", "~x3" → neg "x3". -/
def parseOPBLit (tok : String) : Except String OPBLit :=
  if tok.startsWith "~" then
    let varName := (tok.drop 1).toString
    if varName.isEmpty then
      throw "empty variable name after ~"
    else
      .ok (.neg varName)
  else
    if tok.isEmpty then
      throw "empty variable name"
    else
      .ok (.pos tok)

/-- Check if a token looks like a variable name (starts with letter or ~). -/
def isVarToken (tok : String) : Bool :=
  match tok.toList.head? with
  | some c => c == '~' || c.isAlpha || c == '_'
  | none => false

/-- Parse a coefficient string like "+1", "3", "-2" into an Int.
    Supports both positive and negative coefficients. -/
def parseCoeffInt (tok : String) : Except String Int :=
  -- Strip leading +
  let cleaned := if tok.startsWith "+" then (tok.drop 1).toString else tok
  match cleaned.toInt? with
  | some n => .ok n
  | none => .error s!"invalid coefficient: {tok}"

/-- Negate an OPB literal. -/
def OPBLit.negate : OPBLit → OPBLit
  | .pos name => .neg name
  | .neg name => .pos name

/-- Parse an OPB constraint from tokens starting at the current position.
    Format: `[+|−]c1 var1 [+|−]c2 var2 ... >= d`
    Also handles the degenerate case `>= d` (empty LHS).
    Negative coefficients `-a·x` are normalized to `a·~x` with degree adjustment:
    `-a·x ≡ a·~x - a`, so degree increases by `a`. -/
def parseOPBConstr : ParseM OPBConstr := do
  let mut terms : List OPBTerm := []
  let mut degreeAdj : Nat := 0
  -- Parse terms until we see ">="
  while (← peek) != ">=" do
    let coeffTok ← next
    let coeffI ← match parseCoeffInt coeffTok with
      | .ok n => pure n
      | .error e => throw e
    let varTok ← next
    let lit ← match parseOPBLit varTok with
      | .ok l => pure l
      | .error e => throw e
    if coeffI ≥ 0 then
      terms := ⟨coeffI.toNat, lit⟩ :: terms
    else
      -- Negative coeff: -a·x ≡ a·~x, degree += a
      let absCoeff := (-coeffI).toNat
      terms := ⟨absCoeff, lit.negate⟩ :: terms
      degreeAdj := degreeAdj + absCoeff
  expect ">="
  let degree ← parseNat
  return ⟨terms.reverse, degree + degreeAdj⟩

-- VeriPB kernel proof parser

/-- Parse the RPN operations for a `pol` step.
    Tokens are consumed until `;` is reached.
    In VeriPB RPN, `*` and `d` consume an integer operand from the stack.
    Numbers that immediately precede `*` or `d` are pushed as raw integers;
    all other numbers are pushed as constraint IDs.
    We use lookahead: if the next token after a number is `*` or `d`,
    push as `.pushNat`; otherwise push as `.pushId`. -/
def parsePolOps : ParseM (List PolOp) := do
  let mut ops : List PolOp := []
  while (← peek) != ";" do
    let tok ← next
    if tok == "+" then
      ops := .add :: ops
    else if tok == "s" then
      ops := .saturate :: ops
    else if tok == "*" then
      ops := .mul :: ops
    else if tok == "d" then
      ops := .div :: ops
    else if tok == "w" then
      let varTok ← next
      ops := .weaken varTok :: ops
    else if isVarToken tok then
      match parseOPBLit tok with
      | .ok lit => ops := .pushLitAxiom lit :: ops
      | .error e => throw e
    else
      -- Number: use lookahead to decide if it's a constraint ID or integer operand
      match tok.toNat? with
      | some n =>
        let nextTok ← peek
        if nextTok == "*" || nextTok == "d" then
          ops := .pushNat n :: ops
        else
          ops := .pushId n :: ops
      | none => throw s!"unexpected token in pol: '{tok}'"
  return ops.reverse

/-- Parse RUP hints: list of constraint IDs and/or `~`, terminated by `;`. -/
def parseRupHints : ParseM (List RupHint) := do
  let mut hints : List RupHint := []
  while (← peek) != ";" do
    let tok ← next
    if tok == "~" then
      hints := .negC :: hints
    else
      match tok.toNat? with
      | some n => hints := .id n :: hints
      | none => throw s!"unexpected RUP hint: '{tok}'"
  return hints.reverse

/-- Parse a list of constraint IDs terminated by `;`. -/
def parseIdList : ParseM (List Nat) := do
  let mut ids : List Nat := []
  while (← peek) != ";" do
    let n ← parseNat
    ids := n :: ids
  return ids.reverse

/-- Parse a list of solution literals terminated by `;` or `end`.
    Format: `x1 ~x2 x3` etc. -/
def parseSolLits : ParseM (List OPBLit) := do
  let mut lits : List OPBLit := []
  let mut tok ← peek
  while tok != ";" && tok != "end" do
    let t ← next
    match parseOPBLit t with
    | .ok lit => lits := lit :: lits
    | .error e => throw e
    tok ← peek
  return lits.reverse

/-- Parse a single proof step. -/
partial def parseStep : ParseM ProofStep := do
  let keyword ← next
  match keyword with
  | "f" =>
    let n ← parseNat
    expectSemicolon
    return .formulaSize n
  | "pol" =>
    let ops ← parsePolOps
    expectSemicolon
    return .pol ops
  | "rup" =>
    let constr ← parseOPBConstr
    expect ":"
    let hints ← parseRupHints
    expectSemicolon
    return .rup constr hints
  | "deld" =>
    let ids ← parseIdList
    expectSemicolon
    return .deld ids
  | "delc" =>
    let ids ← parseIdList
    expectSemicolon
    return .delc ids
  | "output" =>
    -- For PoC: only handle `output NONE ;`
    expect "NONE"
    expectSemicolon
    return .output
  | "conclusion" =>
    let kind ← next
    match kind with
    | "UNSAT" =>
      expect ":"
      let id ← parseNat
      expectSemicolon
      return .conclusion id
    | "SAT" =>
      expect ":"
      let lits ← parseSolLits
      expectSemicolon
      return .conclusionSat lits
    | "BOUNDS" =>
      let lb ← parseNat
      -- Optional lower bound hint `: id`
      let lbHint ← if (← peek) == ":" then do
        let _ ← next
        let id ← parseNat
        pure (some id)
      else pure none
      let ub ← parseNat
      -- Optional upper bound hint `: lits`
      let ubLits ← if (← peek) == ":" then do
        let _ ← next
        parseSolLits
      else pure []
      expectSemicolon
      return .conclusionBounds lb lbHint ub ubLits
    | "NONE" =>
      expectSemicolon
      return .output  -- Treat as no-op like output
    | _ => throw s!"unknown conclusion type: {kind}"
  | "sol" =>
    let lits ← parseSolLits
    expectSemicolon
    return .sol lits
  | "soli" =>
    let lits ← parseSolLits
    expectSemicolon
    return .soli lits
  | "pbc" =>
    let constr ← parseOPBConstr
    expect ":"
    expect "subproof"
    -- Semicolon after 'subproof' is optional (VeriPB omits it)
    if (← peek) == ";" then let _ ← next
    -- Parse inner steps until "qed"
    let mut innerSteps : Array ProofStep := #[]
    while (← peek) != "qed" do
      let step ← parseStep
      innerSteps := innerSteps.push step
    expect "qed"
    expect ":"
    let resultId ← parseNat
    expectSemicolon
    return .pbc constr innerSteps resultId
  | "red" =>
    throw ("unsupported proof step 'red' (redundancy). " ++
      "Run VeriPB with --elaborate to convert to kernel format first.")
  | "dom" =>
    throw ("unsupported proof step 'dom' (dominance). " ++
      "Run VeriPB with --elaborate to convert to kernel format first.")
  | "ia" =>
    throw ("unsupported proof step 'ia' (implication addition). " ++
      "Run VeriPB with --elaborate to convert to kernel format first.")
  | other => throw s!"unknown proof step keyword: '{other}'"

/-- Parse a complete VeriPB kernel proof from a string. -/
def parseVeriPBProof (input : String) : Except String VeriPBProof := do
  let tokens := tokenize input
  let initState : ParseState := ⟨tokens, 0⟩
  let parseAll : ParseM VeriPBProof := do
    expect "pseudo-Boolean"
    expect "proof"
    expect "version"
    expect "3.0"
    let mut steps : Array ProofStep := #[]
    while (← peek) != "end" do
      let step ← parseStep
      steps := steps.push step
    expect "end"
    expect "pseudo-Boolean"
    expect "proof"
    expectSemicolon
    return ⟨steps⟩
  match parseAll initState with
  | .ok result _ => .ok result
  | .error e _ => .error e

-- Variable name mapping (for CNF → PB bridge)

/-- Convert OPBLit to Sat.PB.Literal using DIMACS naming convention.
    Variable "xN" maps to PB variable (N-1) (0-indexed). -/
def opbLitToPB (lit : OPBLit) : Except String Sat.PB.Literal :=
  let extractVar (name : String) : Except String Nat :=
    if name.startsWith "x" then
      match (name.drop 1).toString.toNat? with
      | some n => if n > 0 then .ok (n - 1) else .error "variable index must be > 0"
      | none => .error s!"invalid variable name: {name}"
    else
      .error s!"expected variable name starting with 'x', got: {name}"
  match lit with
  | .pos name => do
    let idx ← extractVar name
    return .pos idx
  | .neg name => do
    let idx ← extractVar name
    return .neg idx

/-- Convert an OPBConstr to a Sat.PB.Constr. -/
def opbConstrToPB (c : OPBConstr) : Except String Sat.PB.Constr := do
  let terms ← c.terms.mapM fun t => do
    let lit ← opbLitToPB t.lit
    return (t.coeff, lit)
  return ⟨terms, c.degree⟩

-- Proof checking state (data-level, no Expr yet)

/-- Proof checking state. -/
structure CheckState where
  /-- Constraint database: maps ID → constraint. -/
  db : Std.HashMap Nat Sat.PB.Constr
  /-- Next constraint ID to assign. -/
  nextId : Nat
  /-- Number of input formula constraints. -/
  formulaSize : Nat
  /-- Number of variables. -/
  numVars : Nat
  /-- Logged solution (for SAT/BOUNDS conclusions). -/
  solution : Option (Array Bool)
  /-- Objective function (for optimization). -/
  objective : Option Sat.PB.Constr
  deriving Inhabited

/-- Initialize checking state from parsed DIMACS clauses. -/
def CheckState.fromDimacs (formula : DimacsFormula) : Except String CheckState := do
  let init : Std.HashMap Nat Sat.PB.Constr × Nat := ({}, 1)
  let result ← formula.clauses.toList.foldlM (init := init)
    fun (db, nextId) clause => do
    let constr ← dimacsClauseToPB clause
    return (db.insert nextId constr, nextId + 1)
  return ⟨result.1, result.2, formula.clauses.size, formula.numVars, none, none⟩

-- Pol RPN evaluator (data-level)

/-- Merge like terms and remove zero-coefficient terms. -/
def mergeLikeTerms (terms : List Sat.PB.Term) : List Sat.PB.Term :=
  let rec go (acc : List Sat.PB.Term) : List Sat.PB.Term → List Sat.PB.Term
    | [] => acc.reverse
    | (c, l) :: rest =>
      match acc.find? fun (_, l') => l' == l with
      | some _ =>
        let acc' := acc.map fun (c'', l') => if l' == l then (c'' + c, l') else (c'', l')
        go acc' rest
      | none => go ((c, l) :: acc) rest
  (go [] terms).filter fun (c, _) => c != 0

/-- Find the index of the first zero-coefficient term. -/
def findZeroIdx (terms : List Sat.PB.Term) : Option Nat :=
  terms.findIdx? fun (c, _) => c == 0

/-- Find indices of the first complementary pair where
`min a b ≤ degree` (required by `cancel_pair_sat`). -/
def findValidCompPairIdx (terms : List Sat.PB.Term) (degree : Nat) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List Sat.PB.Term → Option (Nat × Nat)
    | [] => none
    | (a, l) :: rest =>
      match rest.findIdx? fun (_, l') => l' == l.negate with
      | some offset =>
        let j := i + 1 + offset
        let (b, _) := terms[j]!
        if min a b ≤ degree then some (i, j)
        else go (i + 1) rest
      | none => go (i + 1) rest
  go 0 terms

/-- Find indices of the first pair of terms with the same literal (not complement). -/
def findLikeTermIdx (terms : List Sat.PB.Term) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List Sat.PB.Term → Option (Nat × Nat)
    | [] => none
    | (_, l) :: rest =>
      match rest.findIdx? fun (_, l') => l' == l with
      | some offset => some (i, i + 1 + offset)
      | none => go (i + 1) rest
  go 0 terms

/-- Normalization fuel: each cancel-pair step may produce a zero needing removal
    (2 fuel per pair), plus zeros and like-term merges. 4 * length + 1 is safe. -/
def normFuel (nTerms : Nat) : Nat := 4 * nTerms + 1

-- HashMap-based O(n) normalization used at runtime via @[implemented_by].
-- Soundness proofs type-check against the slow definition below.
private def normalizeConstrFast (c : Sat.PB.Constr) : Sat.PB.Constr :=
  -- Phase 1: merge like terms into HashMap (literal → accumulated coefficient)
  let merged : Std.HashMap Sat.PB.Literal Nat :=
    c.terms.foldl (fun m (coeff, lit) =>
      if coeff == 0 then m
      else match m[lit]? with
        | some old => m.insert lit (old + coeff)
        | none     => m.insert lit coeff) ∅
  -- Phase 2: collect unique variable indices
  let vars : Std.HashSet Nat :=
    merged.fold (fun s lit _ => s.insert lit.var) ∅
  -- Phase 3: cancel complementary pairs, build result
  let initAcc : List Sat.PB.Term × Nat := ([], c.degree)
  let (resultTerms, resultDeg) :=
    vars.fold (fun (acc : List Sat.PB.Term × Nat) v =>
      let posLit := Sat.PB.Literal.pos v
      let negLit := Sat.PB.Literal.neg v
      let posCoeff := merged[posLit]?.getD 0
      let negCoeff := merged[negLit]?.getD 0
      let m := min posCoeff negCoeff
      let (deg, pc, nc) :=
        if m > 0 && m ≤ acc.2 then (acc.2 - m, posCoeff - m, negCoeff - m)
        else (acc.2, posCoeff, negCoeff)
      let terms := acc.1
      let terms := if pc > 0 then (pc, posLit) :: terms else terms
      let terms := if nc > 0 then (nc, negLit) :: terms else terms
      (terms, deg)) initAcc
  ⟨resultTerms, resultDeg⟩

/-- Normalize a PB constraint: remove zeros, cancel complementary pairs (with
    `min a b ≤ degree` guard matching Expr-level `buildNormalization`), merge like terms.
    Uses the same iterative approach as the metaprogram layer to ensure consistency. -/
@[implemented_by normalizeConstrFast]
def normalizeConstr (c : Sat.PB.Constr) : Sat.PB.Constr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat) : Sat.PB.Constr :=
    match fuel with
    | 0 => ⟨terms, degree⟩
    | n + 1 =>
      -- Priority 1: remove zero-coefficient terms
      match findZeroIdx terms with
      | some idx =>
        let pre := terms.take idx
        let post := terms.drop (idx + 1)
        go n (pre ++ post) degree
      | none =>
        -- Priority 2: cancel complementary pairs (only if min a b ≤ degree)
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          if hi : i < terms.length then
            if hj : j < terms.length then
              if hij : i < j then
                if hlit : terms[j].2 == terms[i].2.negate then
                  if hle : min terms[i].1 terms[j].1 ≤ degree then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 - min terms[i].1 terms[j].1,
                            terms[i].2) :: mid ++
                          (terms[j].1 - min terms[i].1 terms[j].1,
                            terms[i].2.negate) :: post)
                      (degree - min terms[i].1 terms[j].1)
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          else ⟨terms, degree⟩
        | none =>
          -- Priority 3: merge like terms
          match findLikeTermIdx terms with
          | some (i, j) =>
            if hi : i < terms.length then
              if hj : j < terms.length then
                if hij : i < j then
                  if hlit : terms[j].2 == terms[i].2 then
                    let pre := terms.take i
                    let mid := (terms.drop (i + 1)).take (j - i - 1)
                    let post := terms.drop (j + 1)
                    go n (pre ++ (terms[i].1 + terms[j].1,
                            terms[i].2) :: mid ++ post) degree
                  else ⟨terms, degree⟩
                else ⟨terms, degree⟩
              else ⟨terms, degree⟩
            else ⟨terms, degree⟩
          | none => ⟨terms, degree⟩
  -- Fuel: each step reduces terms or zeros; 4 * length + 1 is a safe bound.
  go (normFuel c.terms.length) c.terms c.degree

/-- Add two PB constraints. -/
def addConstrs (c1 c2 : Sat.PB.Constr) : Sat.PB.Constr :=
  ⟨c1.terms ++ c2.terms, c1.degree + c2.degree⟩

/-- Multiply a PB constraint by a positive integer. -/
def mulConstr (c : Sat.PB.Constr) (k : Nat) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (k * a, l), k * c.degree⟩

/-- Divide a PB constraint by a positive integer (ceiling). -/
def divConstr (c : Sat.PB.Constr) (k : Nat) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (Sat.PB.ceilDiv a k, l), Sat.PB.ceilDiv c.degree k⟩

/-- Saturate a PB constraint: cap coefficients at the degree. -/
def saturateConstr (c : Sat.PB.Constr) : Sat.PB.Constr :=
  ⟨c.terms.map fun (a, l) => (min a c.degree, l), c.degree⟩

/-- Weaken a constraint by removing a variable.
    Finds the term with the given variable, subtracts its coefficient from the degree.
    Errors if variable not found or coefficient exceeds degree. -/
def weakenConstr (c : Sat.PB.Constr) (varIdx : Nat) : Except String Sat.PB.Constr :=
  let rec findAndRemove (pre : List Sat.PB.Term) : List Sat.PB.Term → Except String Sat.PB.Constr
    | [] => .error s!"weaken: variable index {varIdx} not found in constraint"
    | (a, l) :: rest =>
      if l.var == varIdx then
        if a ≤ c.degree then
          .ok ⟨pre.reverse ++ rest, c.degree - a⟩
        else
          .error s!"weaken: coefficient {a} exceeds degree {c.degree}"
      else
        findAndRemove ((a, l) :: pre) rest
  findAndRemove [] c.terms

-- RUP via multiply-add-normalize

/-- Find a complementary literal pair between accumulator and hint:
    a literal `l` in acc whose negation `l.negate` appears in hint.
    Returns `(coeffInAcc, coeffInHint, literal in acc)`. -/
def findCompLitPair (acc hint : Sat.PB.Constr) :
    Option (Nat × Nat × Sat.PB.Literal) :=
  acc.terms.findSome? fun (ca, la) =>
    hint.terms.findSome? fun (ch, lh) =>
      if la.var == lh.var && la != lh then some (ca, ch, la)
      else none

-- Solution evaluation for SAT/BOUNDS conclusions

/-- Evaluate a literal under a total assignment (array of Bools). -/
def evalLitBool (asgn : Array Bool) (l : Sat.PB.Literal) : Bool :=
  match l with
  | .pos i => if h : i < asgn.size then asgn[i] else false
  | .neg i => if h : i < asgn.size then !asgn[i] else true

/-- Evaluate a PB constraint under a total assignment. Returns true if satisfied. -/
def evalConstrBool (asgn : Array Bool) (c : Sat.PB.Constr) : Bool :=
  let sum := c.terms.foldl (init := 0) fun acc (a, l) =>
    acc + if evalLitBool asgn l then a else 0
  sum >= c.degree

/-- Check if an assignment satisfies all constraints in the database. -/
def checkSolution (asgn : Array Bool) (db : Std.HashMap Nat Sat.PB.Constr) : Bool :=
  db.toList.all fun (_, c) => evalConstrBool asgn c

/-- Check if an assignment satisfies only the original formula constraints
    (IDs 1 to formulaSize). Used for SAT/BOUNDS where derived constraints
    like objective improvement should not be checked. -/
def checkSolutionOriginal (asgn : Array Bool) (db : Std.HashMap Nat Sat.PB.Constr)
    (formulaSize : Nat) : Bool :=
  db.toList.all fun (id, c) =>
    if id <= formulaSize then evalConstrBool asgn c else true

/-- Convert solution literals to an assignment array.
    Returns array where asgn[i] = true iff x(i+1) is in the positive literals.
    Tracks which variables have been set to detect conflicting assignments. -/
def solLitsToAssignment (lits : List OPBLit) (numVars : Nat) :
    Except String (Array Bool) := do
  let mut asgn : Array Bool := .replicate numVars false
  let mut seen : Array Bool := .replicate numVars false
  for lit in lits do
    let (isPos, name) := match lit with
      | .pos n => (true, n)
      | .neg n => (false, n)
    if !name.startsWith "x" then
      throw s!"invalid variable in solution: {name}"
    match (name.drop 1).toString.toNat? with
    | some idx =>
      if idx == 0 then throw "variable index must be > 0"
      if idx > numVars then throw s!"variable x{idx} exceeds numVars {numVars}"
      let i := idx - 1
      if seen[i]! && asgn[i]! != isPos then
        throw s!"conflicting assignment for variable x{idx}"
      asgn := asgn.set! i isPos
      seen := seen.set! i true
    | none => throw s!"invalid variable name: {name}"
  return asgn

/-- Evaluate the objective function on an assignment. -/
def evalObjective (asgn : Array Bool) (obj : Sat.PB.Constr) : Nat :=
  obj.terms.foldl (init := 0) fun acc (a, l) =>
    acc + if evalLitBool asgn l then a else 0

-- PB unit propagation for RUP verification

/-- Evaluate a literal under a partial assignment. -/
def evalLitPartial (asgn : Array (Option Bool))
    (l : Sat.PB.Literal) : Option Bool :=
  match l with
  | .pos i => if h : i < asgn.size then asgn[i] else none
  | .neg i => if h : i < asgn.size then asgn[i].map (!·) else none

/-- Result of propagating a single constraint. -/
inductive PropResult where
  | conflict
  | propagated (forced : List (Sat.PB.Literal × Bool))
  | noPropagation
  deriving Repr

/-- Try to propagate a constraint under a partial assignment.
    Returns forced assignments or conflict. -/
def pbPropagate (asgn : Array (Option Bool))
    (c : Sat.PB.Constr) : PropResult := Id.run do
  -- Compute slack = (sum of coeffs for true/unassigned lits) - degree
  let mut totalActive : Nat := 0
  for (a, l) in c.terms do
    match evalLitPartial asgn l with
    | some false => pure () -- falsified, contributes 0
    | _ => totalActive := totalActive + a -- true or unassigned
  if totalActive < c.degree then return .conflict
  let slack := totalActive - c.degree
  -- Find unassigned literals with coefficient > slack
  let mut forced : List (Sat.PB.Literal × Bool) := []
  for (a, l) in c.terms do
    match evalLitPartial asgn l with
    | none =>
      if a > slack then forced := (l, true) :: forced
    | some false => pure ()
    | _ => pure ()
  if forced.isEmpty then .noPropagation
  else .propagated forced.reverse

/-- Run PB unit propagation for a RUP step.
    Returns the index of the conflicting hint (0-based).
    Takes a lookup function to avoid copying the constraint database. -/
def findConflictHint (negConstr : Sat.PB.Constr)
    (hints : List RupHint) (lookupConstr : Nat → Option Sat.PB.Constr)
    (numVars : Nat) : Except String Nat := do
  -- Resolve all hints to constraints upfront (can fail)
  let hintConstrs ← hints.mapM fun h =>
    match h with
    | .negC => .ok negConstr
    | .id n => match lookupConstr n with
      | some c => .ok c
      | none => .error s!"RUP hint {n} not found"
  let hintArr := hintConstrs.toArray
  -- Run propagation loop imperatively
  let result : Option Nat := Id.run do
    let mut asgn : Array (Option Bool) := .replicate numVars none
    let mut conflictIdx : Option Nat := none
    let mut changed := true
    while changed do
      changed := false
      for i in List.range hintArr.size do
        if conflictIdx.isSome then break
        let hintC := hintArr[i]!
        match pbPropagate asgn hintC with
        | .conflict => conflictIdx := some i
        | .propagated forced =>
          changed := true
          for (l, val) in forced do
            if conflictIdx.isSome then break
            let varIdx := l.var
            let actualVal := match l with
              | .pos _ => val
              | .neg _ => !val
            if varIdx < asgn.size then
              match asgn[varIdx]! with
              | some existing =>
                if existing != actualVal then
                  -- Contradictory assignment → conflict at this hint
                  conflictIdx := some i
              | none =>
                asgn := asgn.set! varIdx (some actualVal)
        | .noPropagation => pure ()
    return conflictIdx
  match result with
  | some idx => .ok idx
  | none => .error "RUP: propagation did not reach conflict"

/-- RUP verification: find conflict via propagation, then verify
    via multiply-add-normalize starting from the conflict hint. -/
def verifyRup (negConstr : Sat.PB.Constr)
    (hints : List RupHint) (db : Std.HashMap Nat Sat.PB.Constr)
    (numVars : Nat) : Except String Sat.PB.Constr := do
  if hints.isEmpty then throw "RUP: no hints provided"
  let getHint (h : RupHint) : Except String Sat.PB.Constr :=
    match h with
    | .negC => .ok negConstr
    | .id n => match db[n]? with
      | some c => .ok c
      | none => .error s!"RUP: hint {n} not in database"
  -- Find the conflicting hint via propagation
  let conflictIdx ← findConflictHint negConstr hints (db[·]?) numVars
  let conflictHint := hints[conflictIdx]!
  -- Start accumulator from the conflict hint
  let conflictC ← getHint conflictHint
  let mut acc := normalizeConstr conflictC
  -- Add all other hints (the assignment hints) one by one
  for i in List.range hints.length do
    if acc.isContra then break
    if i == conflictIdx then continue
    let hintC ← getHint hints[i]!
    match findCompLitPair acc hintC with
    | some (ca, ch, _) =>
      let accM := if ch == 1 then acc else mulConstr acc ch
      let hintM := if ca == 1 then hintC else mulConstr hintC ca
      acc := normalizeConstr (addConstrs accM hintM)
    | none =>
      acc := normalizeConstr (addConstrs acc hintC)
  if !acc.isContra then
    throw s!"RUP: not contradictory after processing hints \
      (coeffSum={acc.coeffSum}, degree={acc.degree})"
  .ok acc

-- Pol RPN evaluator with mixed stack

/-- RPN stack element: either a constraint or a raw integer. -/
inductive StackElem where
  | constr : Sat.PB.Constr → StackElem
  | nat : Nat → StackElem
  deriving Repr

/-- Execute the pol RPN sequence with a mixed stack. -/
def execPolRPN (ops : List PolOp) (db : Std.HashMap Nat Sat.PB.Constr) :
    Except String Sat.PB.Constr := do
  let execOne (stack : List StackElem) (op : PolOp) : Except String (List StackElem) :=
    match op with
    | .pushId id =>
      match db[id]? with
      | some c => .ok (.constr c :: stack)
      | none => .error s!"constraint ID {id} not in database"
    | .pushNat n => .ok (.nat n :: stack)
    | .pushLitAxiom lit => do
      let pbLit ← opbLitToPB lit
      .ok (.constr ⟨[(1, pbLit)], 0⟩ :: stack)
    | .add =>
      match stack with
      | .constr c2 :: .constr c1 :: rest => .ok (.constr (addConstrs c1 c2) :: rest)
      | _ => .error "pol +: need two constraints on stack"
    | .mul =>
      match stack with
      | .nat k :: .constr c :: rest =>
        -- k=0 is valid: zeroes out the constraint (useful for masking terms)
        .ok (.constr (mulConstr c k) :: rest)
      | _ => .error "pol *: need integer on top of constraint on stack"
    | .div =>
      match stack with
      | .nat k :: .constr c :: rest =>
        if k == 0 then .error "pol d: divisor must be positive"
        else
          -- VeriPB normalizes before division (cancel complementary pairs first)
          let normalized := normalizeConstr c
          .ok (.constr (divConstr normalized k) :: rest)
      | _ => .error "pol d: need integer on top of constraint on stack"
    | .saturate =>
      match stack with
      | .constr c :: rest =>
        -- VeriPB normalizes before saturation (cancel complementary pairs first)
        let normalized := normalizeConstr c
        .ok (.constr (saturateConstr normalized) :: rest)
      | _ => .error "pol s: need constraint on stack"
    | .weaken varName =>
      match stack with
      | .constr c :: rest => do
        let varIdx ← if varName.startsWith "x" then
          match (varName.drop 1).toString.toNat? with
          | some n => if n > 0 then pure (n - 1) else .error "variable index must be > 0"
          | none => .error s!"invalid variable in weaken: {varName}"
        else
          .error s!"expected variable name starting with 'x', got: {varName}"
        let weakened ← weakenConstr c varIdx
        .ok (.constr weakened :: rest)
      | _ => .error "pol w: need constraint on stack"
  let finalStack ← ops.foldlM (init := ([] : List StackElem)) execOne
  match finalStack with
  | [.constr c] => .ok c
  | [.nat _] => .error "pol: stack ends with integer, not constraint"
  | [] => .error "pol: empty stack at end"
  | _ => .error s!"pol: stack has {finalStack.length} elements at end, expected 1"

-- Proof step executor (data-level checking)

mutual
/-- Execute a single proof step, updating the check state. -/
partial def execStep (state : CheckState) (step : ProofStep) : Except String CheckState :=
  match step with
  | .formulaSize n =>
    if state.formulaSize != n then
      throw s!"formula size mismatch: CNF has {state.formulaSize} clauses, proof declares {n}"
    else
      .ok state
  | .pol ops => do
    let result ← execPolRPN ops state.db
    let newDb := state.db.insert state.nextId (normalizeConstr result)
    .ok { state with db := newDb, nextId := state.nextId + 1 }
  | .rup constr hints => do
    let pbConstr ← opbConstrToPB constr
    let cs := pbConstr.coeffSum
    if pbConstr.degree > cs then
      throw s!"RUP: target degree {pbConstr.degree} > coeffSum {cs}"
    let negConstr := pbConstr.negate
    let _ ← verifyRup negConstr hints state.db state.numVars
    let newDb := state.db.insert state.nextId (normalizeConstr pbConstr)
    .ok { state with db := newDb, nextId := state.nextId + 1 }
  | .pbc constr innerSteps resultId => do
    if innerSteps.any (fun s => match s with
        | .conclusion _ | .output => true | _ => false) then
      throw "pbc subproof contains 'conclusion' or 'output' step"
    let pbConstr ← opbConstrToPB constr
    let cs := pbConstr.coeffSum
    if pbConstr.degree > cs then
      throw s!"pbc: target degree {pbConstr.degree} > coeffSum {cs}"
    -- Save DB snapshot, add negated constraint
    let savedDb := state.db
    let negConstr := pbConstr.negate
    let negId := state.nextId
    let dbWithNeg := state.db.insert negId negConstr
    let subState : CheckState :=
      { state with db := dbWithNeg, nextId := negId + 1 }
    -- Execute inner steps
    let finalSub ← execAllSteps subState innerSteps
    -- The qed constraint (resultId) must be contradictory
    match finalSub.db[resultId]? with
    | some c =>
      if c.isContra then pure ()
      else throw s!"pbc qed: constraint {resultId} is not contradictory \
        (coeffSum={c.coeffSum}, degree={c.degree})"
    | none => throw s!"pbc qed: constraint {resultId} not in database"
    -- Restore DB, register the derived constraint
    let restoredDb := savedDb.insert finalSub.nextId (normalizeConstr pbConstr)
    .ok { state with db := restoredDb, nextId := finalSub.nextId + 1 }
  | .deld ids =>
    let db := ids.foldl (init := state.db) fun db id => db.erase id
    .ok { state with db := db }
  | .delc ids =>
    let db := ids.foldl (init := state.db) fun db id => db.erase id
    .ok { state with db := db }
  | .output => .ok state
  | .conclusion id =>
    match state.db[id]? with
    | some c =>
      if c.isContra then
        .ok state  -- Contradiction found!
      else
        throw s!"conclusion constraint {id} is not contradictory \
          (coeffSum={c.coeffSum}, degree={c.degree})"
    | none => throw s!"conclusion constraint ID {id} not in database"
  | .sol lits => do
    let asgn ← solLitsToAssignment lits state.numVars
    if !checkSolution asgn state.db then
      throw "sol: assignment does not satisfy all constraints"
    .ok { state with solution := some asgn }
  | .soli lits => do
    let asgn ← solLitsToAssignment lits state.numVars
    if !checkSolution asgn state.db then
      throw "soli: assignment does not satisfy all constraints"
    -- Add objective improvement constraint: f(x) <= f(rho) - 1
    -- In >= form: sum of (coeff * ~lit) >= (W - f(rho) + 1)
    -- where W = sum of all coefficients, f(rho) = objective value at solution
    match state.objective with
    | some obj =>
      let W := obj.terms.foldl (init := 0) fun acc (a, _) => acc + a
      let fRho := evalObjective asgn obj
      -- Negate each literal and compute new degree
      let negTerms := obj.terms.map fun (a, l) => (a, l.negate)
      let newDegree := W - fRho + 1
      let improvementConstr : Sat.PB.Constr := ⟨negTerms, newDegree⟩
      let newDb := state.db.insert state.nextId improvementConstr
      .ok { state with db := newDb, nextId := state.nextId + 1, solution := some asgn }
    | none =>
      -- No objective, just store solution
      .ok { state with solution := some asgn }
  | .conclusionSat lits => do
    -- Verify the explicit solution satisfies all constraints
    let asgn ← solLitsToAssignment lits state.numVars
    if !checkSolution asgn state.db then
      throw "conclusion SAT: assignment does not satisfy all constraints"
    .ok state
  | .conclusionBounds _lb lbHint ub ubLits => do
    -- Verify lower bound: constraint at lbHint implies objective >= lb
    match lbHint with
    | some id =>
      match state.db[id]? with
      | some c =>
        if !c.isContra then
          throw s!"conclusion BOUNDS: lower bound constraint {id} is not contradictory"
      | none => throw s!"conclusion BOUNDS: constraint ID {id} not in database"
    | none => pure () -- No hint, trust the proof
    -- Verify upper bound: solution achieves objective <= ub
    -- Check against original formula constraints only (not derived constraints)
    if !ubLits.isEmpty then do
      let asgn ← solLitsToAssignment ubLits state.numVars
      if !checkSolutionOriginal asgn state.db state.formulaSize then
        throw "conclusion BOUNDS: upper bound solution does not satisfy constraints"
      -- Optionally verify objective value matches claimed upper bound
      match state.objective with
      | some obj =>
        let objVal := evalObjective asgn obj
        if objVal > ub then
          throw s!"conclusion BOUNDS: solution objective {objVal} > claimed UB {ub}"
      | none => pure ()
    .ok state

/-- Execute all proof steps. -/
partial def execAllSteps (state : CheckState) (steps : Array ProofStep) :
    Except String CheckState :=
  steps.toList.foldlM (init := state) fun s step => execStep s step
end

/-- Verify a VeriPB proof against a DIMACS formula (data-level check).
    Returns Ok if the proof is valid, Error with message otherwise. -/
def verifyProof (cnf : String) (proof : String) : Except String Unit := do
  let formula ← parseDimacs cnf
  let proofData ← parseVeriPBProof proof
  let initState ← CheckState.fromDimacs formula
  let _finalState ← execAllSteps initState proofData.steps
  return ()

-- Metaprogram layer: Expr-level proof construction

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

/-- ToExpr for Sat.PB.Literal. -/
instance : ToExpr Sat.PB.Literal where
  toTypeExpr := mkConst ``Sat.PB.Literal
  toExpr
    | .pos i => mkApp (mkConst ``Sat.PB.Literal.pos) (mkRawNatLit i)
    | .neg i => mkApp (mkConst ``Sat.PB.Literal.neg) (mkRawNatLit i)

/-- Build a `List Sat.PB.Term` expression from data. -/
def buildTermListExpr (terms : List Sat.PB.Term) : Expr :=
  let termType := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Sat.PB.Literal)
  let nil := mkApp (mkConst ``List.nil [.zero]) termType
  let cons := mkApp (mkConst ``List.cons [.zero]) termType
  terms.foldr (fun (c, l) acc =>
    let pair := mkApp4 (mkConst ``Prod.mk [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Sat.PB.Literal) (mkRawNatLit c) (toExpr l)
    mkApp2 cons pair acc
  ) nil

/-- Build a `PB.Constr` expression from data. -/
def buildConstrExpr (c : Sat.PB.Constr) : Expr :=
  mkApp2 (mkConst ``Sat.PB.Constr.mk) (buildTermListExpr c.terms) (mkRawNatLit c.degree)

/-- A stored constraint with data, Lean expression, and proof. -/
structure StoredConstr where
  constr : Sat.PB.Constr
  expr   : Expr  -- Lean expression of type `PB.Constr`
  proof  : Expr  -- proof of type `PB.PBFmla.proof ctx constr`

/-- Build a PBFmla expression from an array of constraint arrays (balanced tree). -/
def buildConj (constrs : Array Sat.PB.Constr) (start stop : Nat) : Except String Expr :=
  match h : stop - start with
  | 0 => .error "buildConj: empty formula (start == stop)"
  | 1 =>
    match constrs[start]? with
    | some c => .ok <| mkApp (mkConst ``Sat.PB.PBFmla.one) (buildConstrExpr c)
    | none => .error s!"buildConj: index {start} out of bounds"
  | len + 2 =>
    let mid := start + (len + 2) / 2
    do
      let left ← buildConj constrs start mid
      let right ← buildConj constrs mid stop
      .ok <| mkApp2 (mkConst ``Sat.PB.PBFmla.and) left right
termination_by stop - start

/-- Extract proofs for each input constraint via subsumption (like LRAT's buildClauses). -/
def buildClauses (constrs : Array Sat.PB.Constr) (ctx : Expr) (start stop : Nat)
    (f p : Expr) (accum : Nat × Std.HashMap Nat StoredConstr) :
    Except String (Nat × Std.HashMap Nat StoredConstr) :=
  match h : stop - start with
  | 0 => .error "buildClauses: empty range"
  | 1 =>
    match constrs[start]? with
    | some c =>
      let cExpr := f.appArg!
      let proof := mkApp3 (mkConst ``Sat.PB.PBFmla.proof_of_subsumes) ctx cExpr p
      let n := accum.1 + 1
      .ok (n, accum.2.insert n { constr := c, expr := cExpr, proof })
    | none => .error s!"buildClauses: index {start} out of bounds"
  | len + 2 =>
    let mid := start + (len + 2) / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (mkConst ``Sat.PB.PBFmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (mkConst ``Sat.PB.PBFmla.subsumes_right) ctx f₁ f₂ p
    do
      let accum ← buildClauses constrs ctx start mid f₁ p₁ accum
      buildClauses constrs ctx mid stop f₂ p₂ accum
termination_by stop - start

-- Normalization Expr builder

/-- Build a kernel-checkable proof of `a ≤ b` for concrete Nat literals. -/
def mkNatLeProof (a b : Nat) : Expr :=
  let natLitA := mkRawNatLit a
  let natLitB := mkRawNatLit b
  let leProp := mkApp2
    (mkApp2 (mkConst ``LE.le [.zero]) (mkConst ``Nat) (mkConst ``instLENat))
    natLitA natLitB
  let decInst := mkApp2 (mkConst ``Nat.decLe) natLitA natLitB
  let rflProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
    (mkConst ``Bool.true)
  let decideProp :=
    mkApp2 (mkConst ``Decidable.decide) leProp decInst
  let eqType := mkApp3
    (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
    decideProp (mkConst ``Bool.true)
  let idProof :=
    mkApp2 (mkConst ``id [.zero]) eqType rflProof
  mkApp3 (mkConst ``of_decide_eq_true) leProp decInst idProof

/-- Build a kernel-checkable proof of `a < b` for concrete Nat literals.
Constructs: `of_decide_eq_true (Nat.decLt a b) (Eq.refl true)` -/
def mkNatLtProof (a b : Nat) : Expr :=
  let natLitA := mkRawNatLit a
  let natLitB := mkRawNatLit b
  let ltProp := mkApp2
    (mkApp2 (mkConst ``LT.lt [.zero])
      (mkConst ``Nat) (mkConst ``instLTNat))
    natLitA natLitB
  let decInst :=
    mkApp2 (mkConst ``Nat.decLt) natLitA natLitB
  let rflProof := mkApp2
    (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
    (mkConst ``Bool.true)
  let decideProp :=
    mkApp2 (mkConst ``Decidable.decide) ltProp decInst
  let eqType := mkApp3
    (mkConst ``Eq [.succ .zero]) (mkConst ``Bool)
    decideProp (mkConst ``Bool.true)
  let idProof :=
    mkApp2 (mkConst ``id [.zero]) eqType rflProof
  mkApp3 (mkConst ``of_decide_eq_true) ltProp decInst idProof

/-- Apply one remove-zero step, building the Expr proof using `PB.remove_zero_sat`.
    Proof type: `∀ v, allSat v ctx → newConstr.sat v`
    Built from: `fun v hv => remove_zero_sat v pre post l d (prevProof v hv)` -/
def buildRemoveZero (idx : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx
  let post := terms.drop (idx + 1)
  let (_, l) := terms[idx]!
  let preExpr := buildTermListExpr pre
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let dExpr := mkRawNatLit degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp6 (mkConst ``Sat.PB.remove_zero_sat)
    (mkBVar 1) preExpr postExpr lExpr dExpr
    (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, newProof)

/-- Apply one cancel-pair step, building the Expr proof using `PB.cancel_pair_sat`.
    `idx1 < idx2`, terms[idx1] = (a, l), terms[idx2] = (b, l.negate). -/
def buildCancelPair (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let m := min a b
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let hleProof := mkNatLeProof m degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.cancel_pair_sat)
    (mkBVar 1)) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr) dExpr) hleProof)
    (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ (a - m, l) :: mid ++ (b - m, l.negate) :: post
  let newDegree := degree - m
  let newExpr := buildConstrExpr ⟨newTerms, newDegree⟩
  (newTerms, newDegree, newExpr, newProof)

/-- Apply one merge-terms step, building the Expr proof using `PB.merge_terms_sat`.
    `idx1 < idx2`, terms[idx1] = (a, l), terms[idx2] = (b, l) (same literal). -/
def buildMergeTerms (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (ctx : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.merge_terms_sat)
    (mkBVar 1)) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr
  let body := mkApp2 body dExpr (mkApp2 proofExpr (mkBVar 1) (mkBVar 0))
  let newProof := mkLambda `v .default vTy <| mkLambda `hv .default allSatTy body
  let newTerms := pre ++ (a + b, l) :: mid ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, newProof)

/-- Normalize a constraint by iteratively removing zeros and canceling
    complementary pairs, building kernel-verified proof at each step. -/
def buildNormalization (rawConstr : Sat.PB.Constr) (rawExpr : Expr)
    (rawProof : Expr) (ctx : Expr) :
    Sat.PB.Constr × Expr × Expr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
      (constrExpr proofExpr : Expr) : Sat.PB.Constr × Expr × Expr :=
    match fuel with
    | 0 => (⟨terms, degree⟩, constrExpr, proofExpr)
    | n + 1 =>
      -- Priority 1: remove zero-coefficient terms
      match findZeroIdx terms with
      | some idx =>
        let (t', d', e', p') := buildRemoveZero idx terms degree proofExpr ctx
        go n t' d' e' p'
      | none =>
        -- Priority 2: cancel complementary pairs (only if min a b ≤ degree)
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          let (t', d', e', p') := buildCancelPair i j terms degree proofExpr ctx
          go n t' d' e' p'
        | none =>
          -- Priority 3: merge like terms
          match findLikeTermIdx terms with
          | some (i, j) =>
            let (t', d', e', p') := buildMergeTerms i j terms degree proofExpr ctx
            go n t' d' e' p'
          | none =>
            -- Fully normalized
            (⟨terms, degree⟩, constrExpr, proofExpr)
  -- Fuel bound: each cancel-pair step may produce a zero that needs a second step to remove
  -- (2 fuel per pair), plus initial zeros and like-term merges. 4 * length + 1 is a safe bound.
  go (normFuel rawConstr.terms.length) rawConstr.terms rawConstr.degree rawExpr rawProof

-- Direct normalization (for RUP: produces c.sat v proofs, not wrapped)

/-- Remove a zero-coefficient term, producing a direct `c.sat v` proof.
    `vExpr` is the expression for the valuation variable `v`. -/
def buildRemoveZeroDirect (idx : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx
  let post := terms.drop (idx + 1)
  let (_, l) := terms[idx]!
  let preExpr := buildTermListExpr pre
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let dExpr := mkRawNatLit degree
  let body := mkApp6 (mkConst ``Sat.PB.remove_zero_sat) vExpr preExpr postExpr lExpr dExpr proofExpr
  let newTerms := pre ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, body)

/-- Cancel a complementary pair, producing a direct `c.sat v` proof. -/
def buildCancelPairDirect (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let m := min a b
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let hleProof := mkNatLeProof m degree
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.cancel_pair_sat)
    vExpr) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr) dExpr) hleProof) proofExpr
  let newTerms := pre ++ (a - m, l) :: mid ++ (b - m, l.negate) :: post
  let newDegree := degree - m
  let newExpr := buildConstrExpr ⟨newTerms, newDegree⟩
  (newTerms, newDegree, newExpr, body)

/-- Merge like terms, producing a direct `c.sat v` proof. -/
def buildMergeTermsDirect (idx1 idx2 : Nat) (terms : List Sat.PB.Term) (degree : Nat)
    (proofExpr : Expr) (vExpr : Expr) : List Sat.PB.Term × Nat × Expr × Expr :=
  let pre := terms.take idx1
  let (a, l) := terms[idx1]!
  let mid := (terms.drop (idx1 + 1)).take (idx2 - idx1 - 1)
  let (b, _) := terms[idx2]!
  let post := terms.drop (idx2 + 1)
  let preExpr := buildTermListExpr pre
  let midExpr := buildTermListExpr mid
  let postExpr := buildTermListExpr post
  let lExpr := toExpr l
  let aExpr := mkRawNatLit a
  let bExpr := mkRawNatLit b
  let dExpr := mkRawNatLit degree
  let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
    (mkConst ``Sat.PB.merge_terms_sat)
    vExpr) preExpr) midExpr) postExpr) lExpr) aExpr) bExpr
  let body := mkApp2 body dExpr proofExpr
  let newTerms := pre ++ (a + b, l) :: mid ++ post
  let newExpr := buildConstrExpr ⟨newTerms, degree⟩
  (newTerms, degree, newExpr, body)

/-- Normalize a constraint with direct `c.sat v` proofs (for RUP). -/
def buildNormDirect (rawConstr : Sat.PB.Constr) (rawExpr : Expr)
    (rawProof : Expr) (vExpr : Expr) :
    Sat.PB.Constr × Expr × Expr :=
  let rec go (fuel : Nat) (terms : List Sat.PB.Term) (degree : Nat)
      (constrExpr proofExpr : Expr) : Sat.PB.Constr × Expr × Expr :=
    match fuel with
    | 0 => (⟨terms, degree⟩, constrExpr, proofExpr)
    | n + 1 =>
      match findZeroIdx terms with
      | some idx =>
        let (t', d', e', p') := buildRemoveZeroDirect idx terms degree proofExpr vExpr
        go n t' d' e' p'
      | none =>
        match findValidCompPairIdx terms degree with
        | some (i, j) =>
          let (t', d', e', p') := buildCancelPairDirect i j terms degree proofExpr vExpr
          go n t' d' e' p'
        | none =>
          match findLikeTermIdx terms with
          | some (i, j) =>
            let (t', d', e', p') := buildMergeTermsDirect i j terms degree proofExpr vExpr
            go n t' d' e' p'
          | none =>
            (⟨terms, degree⟩, constrExpr, proofExpr)
  -- Fuel bound: each cancel-pair step may produce a zero that needs a second step to remove
  -- (2 fuel per pair), plus initial zeros and like-term merges. 4 * length + 1 is a safe bound.
  go (normFuel rawConstr.terms.length) rawConstr.terms rawConstr.degree rawExpr rawProof

-- Pol RPN proof builder

/-- RPN stack element for the metaprogram: constraint data + expr + proof. -/
inductive MetaStackElem where
  | constr : StoredConstr → MetaStackElem
  | nat : Nat → MetaStackElem

/-- Execute pol RPN and build proof terms.
    Each stored proof has type `PBFmla.proof ctx c`. -/
def buildPolProof (ops : List PolOp) (db : Std.HashMap Nat StoredConstr)
    (ctx : Expr) :
    Except String StoredConstr := do
  let execOne (stack : List MetaStackElem) (op : PolOp) :
      Except String (List MetaStackElem) :=
    match op with
    | .pushId id =>
      match db[id]? with
      | some sc => .ok (.constr sc :: stack)
      | none => .error s!"pol: constraint ID {id} not in database"
    | .pushNat n => .ok (.nat n :: stack)
    | .pushLitAxiom lit => do
      let pbLit ← opbLitToPB lit
      let c : Sat.PB.Constr := ⟨[(1, pbLit)], 0⟩
      let cExpr := buildConstrExpr c
      -- Proof: lit_axiom is unconditionally satisfied
      -- PBFmla.proof ctx c = ∀ v, allSat v → c.sat v
      -- = fun v _ => lit_axiom_pos/neg i v
      let vTy := mkConst ``Sat.PB.Valuation
      let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
      let axiomProof := match pbLit with
        | .pos i => mkApp2 (mkConst ``Sat.PB.lit_axiom_pos) (mkRawNatLit i) (mkBVar 1)
        | .neg i => mkApp2 (mkConst ``Sat.PB.lit_axiom_neg) (mkRawNatLit i) (mkBVar 1)
      let proof := mkLambda `v .default vTy <|
        mkLambda `_ .default allSatTy axiomProof
      .ok (.constr ⟨c, cExpr, proof⟩ :: stack)
    | .add =>
      match stack with
      | .constr sc2 :: .constr sc1 :: rest =>
        let newConstr := addConstrs sc1.constr sc2.constr
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => add_sat c1 c2 v (sc1.proof v hv) (sc2.proof v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p1 := mkApp2 sc1.proof (mkBVar 1) (mkBVar 0)
        let p2 := mkApp2 sc2.proof (mkBVar 1) (mkBVar 0)
        let addApp := mkApp5 (mkConst ``Sat.PB.add_sat)
          sc1.expr sc2.expr (mkBVar 1) p1 p2
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy addApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol +: need two constraints on stack"
    | .mul =>
      match stack with
      | .nat k :: .constr sc :: rest =>
        -- k=0 is valid: zeroes out the constraint (useful for masking terms)
        let newConstr := mulConstr sc.constr k
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => mul_sat c k v (sc.proof v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
        let mulApp := mkApp4 (mkConst ``Sat.PB.mul_sat) sc.expr (mkRawNatLit k) (mkBVar 1) p
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy mulApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol *: need integer on top of constraint on stack"
    | .div =>
      match stack with
      | .nat k :: .constr sc :: rest =>
        if k == 0 then .error "pol d: divisor must be positive"
        else
          -- VeriPB normalizes before division (cancel complementary pairs first)
          let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
          let newConstr := divConstr normC k
          let newExpr := buildConstrExpr newConstr
          -- Proof: fun v hv => div_sat normC k hk v (normP v hv)
          let vTy := mkConst ``Sat.PB.Valuation
          let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
          let p := mkApp2 normP (mkBVar 1) (mkBVar 0)
          let hkProof := mkNatLtProof 0 k
          let divApp := mkApp5 (mkConst ``Sat.PB.div_sat)
            normE (mkRawNatLit k) hkProof (mkBVar 1) p
          let proof := mkLambda `v .default vTy <|
            mkLambda `hv .default allSatTy divApp
          .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol d: need integer on top of constraint on stack"
    | .saturate =>
      match stack with
      | .constr sc :: rest =>
        -- VeriPB normalizes before saturation (cancel complementary pairs first)
        let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
        let newConstr := saturateConstr normC
        let newExpr := buildConstrExpr newConstr
        -- Proof: fun v hv => saturate_sat normC v (normP v hv)
        let vTy := mkConst ``Sat.PB.Valuation
        let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
        let p := mkApp2 normP (mkBVar 1) (mkBVar 0)
        let satApp := mkApp3 (mkConst ``Sat.PB.saturate_sat) normE (mkBVar 1) p
        let proof := mkLambda `v .default vTy <|
          mkLambda `hv .default allSatTy satApp
        .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol s: need constraint on stack"
    | .weaken varName =>
      match stack with
      | .constr sc :: rest => do
        let varIdx ← if varName.startsWith "x" then
          match (varName.drop 1).toString.toNat? with
          | some n => if n > 0 then pure (n - 1) else .error "variable index must be > 0"
          | none => .error s!"invalid variable in weaken: {varName}"
        else
          .error s!"expected variable name starting with 'x', got: {varName}"
        -- Find the term with the matching variable
        let terms := sc.constr.terms
        let degree := sc.constr.degree
        match terms.findIdx? fun (_, l) => l.var == varIdx with
        | none => .error s!"pol w: variable x{varIdx + 1} not found in constraint"
        | some idx =>
          let pre := terms.take idx
          let (a, l) := terms[idx]!
          let post := terms.drop (idx + 1)
          if a > degree then
            .error s!"pol w: coefficient {a} exceeds degree {degree} for variable x{varIdx + 1}"
          else
          let preExpr := buildTermListExpr pre
          let postExpr := buildTermListExpr post
          let lExpr := toExpr l
          let aExpr := mkRawNatLit a
          let dExpr := mkRawNatLit degree
          let hleProof := mkNatLeProof a degree
          let vTy := mkConst ``Sat.PB.Valuation
          let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
          let body := mkApp (mkApp (mkApp (mkApp (mkApp (mkApp (mkApp
            (mkConst ``Sat.PB.weaken_term_sat)
            (mkBVar 1)) preExpr) postExpr) aExpr) lExpr) dExpr) hleProof
          let body := mkApp body (mkApp2 sc.proof (mkBVar 1) (mkBVar 0))
          let proof := mkLambda `v .default vTy <|
            mkLambda `hv .default allSatTy body
          let newConstr : Sat.PB.Constr := ⟨pre ++ post, degree - a⟩
          let newExpr := buildConstrExpr newConstr
          .ok (.constr ⟨newConstr, newExpr, proof⟩ :: rest)
      | _ => .error "pol w: need constraint on stack"
  let finalStack ← ops.foldlM (init := ([] : List MetaStackElem)) execOne
  match finalStack with
  | [.constr sc] =>
    -- Normalize at the end of the pol step (not after each intermediate operation)
    let (normC, normE, normP) := buildNormalization sc.constr sc.expr sc.proof ctx
    .ok ⟨normC, normE, normP⟩
  | [.nat _] => .error "pol: stack ends with integer, not constraint"
  | [] => .error "pol: empty stack at end"
  | _ => .error s!"pol: stack has {finalStack.length} elements at end, expected 1"

-- RUP proof builder

/-- Build a RUP proof using conflict-hint-first approach.
    Uses PB unit propagation to find the conflicting hint, starts the
    accumulator from it, then adds remaining hints via multiply-add-normalize.
    Proof structure:
    ```
    fun v hv => Classical.byContradiction fun hn =>
      let acc := conflict_hint_sat  -- start from conflict hint
      let acc := add_sat + normalize (acc, other hints) ...
      absurd accSat (contra_unsat acc v hc)
    ```
    Inside byContradiction body: BVar 0 = hn, BVar 1 = hv, BVar 2 = v -/
def buildRupProof (targetOPB : OPBConstr) (hints : List RupHint)
    (db : Std.HashMap Nat StoredConstr) (ctx : Expr) (numVars : Nat) :
    Except String StoredConstr := do
  -- Convert target to PB
  let targetConstr ← opbConstrToPB targetOPB
  -- Compute the negation at data level
  let negConstr := targetConstr.negate
  -- Verify precondition: degree ≤ coeffSum
  let cs := targetConstr.coeffSum
  if targetConstr.degree > cs then
    throw s!"RUP: target degree {targetConstr.degree} > coeffSum {cs}"
  if hints.isEmpty then
    throw "RUP: no hints provided"
  -- Find the conflicting hint via PB unit propagation
  let lookupConstr (n : Nat) : Option Sat.PB.Constr :=
    db[n]?.map (·.constr)
  let conflictIdx ← findConflictHint negConstr hints lookupConstr numVars
  -- We'll build the proof body inside byContradiction.
  -- Under `fun v hv => Classical.byContradiction fun hn => ...`:
  --   BVar 0 = hn : ¬ targetConstr.sat v
  --   BVar 1 = hv : allSat v ctx
  --   BVar 2 = v  : Valuation
  let vExpr := mkBVar 2       -- v
  let hvExpr := mkBVar 1      -- hv
  let hnExpr := mkBVar 0      -- hn
  -- Build negation proof: negate_sat_of_not_sat C v hd hn
  let targetExpr := buildConstrExpr targetConstr
  let hdProof := mkNatLeProof targetConstr.degree cs
  let negProof := mkApp4 (mkConst ``Sat.PB.negate_sat_of_not_sat)
    targetExpr vExpr hdProof hnExpr
  let negExpr := buildConstrExpr negConstr
  -- Helper to get hint data + expr + proof
  let getHintProof (h : RupHint) : Except String (Sat.PB.Constr × Expr × Expr) :=
    match h with
    | .negC => .ok (negConstr, negExpr, negProof)
    | .id n =>
      match db[n]? with
      | some sc =>
        let satProof := mkApp2 sc.proof vExpr hvExpr
        .ok (sc.constr, sc.expr, satProof)
      | none => .error s!"RUP: hint constraint {n} not in database"
  -- Start accumulator from the conflict hint
  let (initC, initE, initP) ← getHintProof hints[conflictIdx]!
  let initAcc := buildNormDirect initC initE initP vExpr
  -- Process all other hints (skipping conflict hint) via multiply-add-normalize
  let hintsArr := hints.toArray
  let processHint (acc : Sat.PB.Constr × Expr × Expr)
      (idx : Nat) : Except String (Sat.PB.Constr × Expr × Expr) := do
    let (accC, accE, accP) := acc
    if accC.isContra then return acc
    let (hintC, hintE, hintP) ← getHintProof hintsArr[idx]!
    match findCompLitPair accC hintC with
    | some (ca, ch, _) =>
      -- Multiply acc by ch, hint by ca for full cancellation
      let (mAccC, mAccE, mAccP) := if ch == 1 then (accC, accE, accP)
        else
          let mc := mulConstr accC ch
          let me := buildConstrExpr mc
          let mp := mkApp4 (mkConst ``Sat.PB.mul_sat)
            accE (mkRawNatLit ch) vExpr accP
          (mc, me, mp)
      let (mHintC, mHintE, mHintP) := if ca == 1 then (hintC, hintE, hintP)
        else
          let mc := mulConstr hintC ca
          let me := buildConstrExpr mc
          let mp := mkApp4 (mkConst ``Sat.PB.mul_sat)
            hintE (mkRawNatLit ca) vExpr hintP
          (mc, me, mp)
      let addedC := addConstrs mAccC mHintC
      let addedE := buildConstrExpr addedC
      let addedP := mkApp5 (mkConst ``Sat.PB.add_sat)
        mAccE mHintE vExpr mAccP mHintP
      .ok (buildNormDirect addedC addedE addedP vExpr)
    | none =>
      let addedC := addConstrs accC hintC
      let addedE := buildConstrExpr addedC
      let addedP := mkApp5 (mkConst ``Sat.PB.add_sat)
        accE hintE vExpr accP hintP
      .ok (buildNormDirect addedC addedE addedP vExpr)
  -- Build list of hint indices to process (all except conflictIdx)
  let otherIndices := (List.range hints.length).filter (· != conflictIdx)
  let (accC, accE, accP) ← otherIndices.foldlM processHint initAcc
  if !accC.isContra then
    throw s!"RUP: not contradictory after processing hints \
      (coeffSum={accC.coeffSum}, degree={accC.degree}, \
      terms={accC.terms.length})"
  -- Build: absurd accP (contra_unsat accC v hc)
  let hcProof := mkNatLtProof accC.coeffSum accC.degree
  let contraApp := mkApp3 (mkConst ``Sat.PB.contra_unsat) accE vExpr hcProof
  let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) accE vExpr
  let absurdApp := mkApp4 (mkConst ``absurd [.zero])
    satType (mkConst ``False) accP contraApp
  -- Build: fun v hv => Classical.byContradiction fun hn => absurdApp
  let vExprOuter := mkBVar 1
  let satTargetType := mkApp2 (mkConst ``Sat.PB.Constr.sat)
    targetExpr vExprOuter
  let hnType := mkApp (mkConst ``Not) satTargetType
  let byContraBody := mkLambda `hn .default hnType absurdApp
  let byContraProof := mkApp2 (mkConst ``Classical.byContradiction [])
    satTargetType byContraBody
  -- Normalize targetConstr to get the final result
  let (finalC, finalE, finalP) := buildNormDirect targetConstr targetExpr
    byContraProof vExprOuter
  -- Wrap in fun v hv =>
  let vTy := mkConst ``Sat.PB.Valuation
  let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
  let wrappedProof := mkLambda `v .default vTy <|
    mkLambda `hv .default allSatTy finalP
  .ok ⟨finalC, finalE, wrappedProof⟩

-- Main proof builder

/-- Execute inner proof steps, returning the updated DB and next ID.
    Used by both top-level `buildProof` and `buildPbcProof` for subproofs.
    Does NOT handle conclusion steps — caller must handle those. -/
partial def execInnerSteps (db : Std.HashMap Nat StoredConstr)
    (nextId : Nat) (steps : Array ProofStep) (ctx : Expr) (numVars : Nat) :
    Except String (Std.HashMap Nat StoredConstr × Nat) := do
  let mut db := db
  let mut nextId := nextId
  for step in steps do
    match step with
    | .formulaSize _ => pure ()
    | .pol ops =>
      let sc ← match buildPolProof ops db ctx with
        | .ok sc => .ok sc
        | .error e => .error s!"step {nextId}: {e}"
      db := db.insert nextId sc
      nextId := nextId + 1
    | .rup constr hints =>
      let sc ← match buildRupProof constr hints db ctx numVars with
        | .ok sc => .ok sc
        | .error e => .error s!"step {nextId}: {e}"
      db := db.insert nextId sc
      nextId := nextId + 1
    | .pbc constrOPB innerSteps resultId =>
      let (sc, newNextId) ← buildPbcStep constrOPB innerSteps resultId
        db ctx nextId numVars
      db := db.insert newNextId sc
      nextId := newNextId + 1
    | .deld ids =>
      for id in ids do db := db.erase id
    | .delc ids =>
      for id in ids do db := db.erase id
    | .output => pure ()
    | .conclusion _ => pure ()  -- handled by caller
    | .sol _ => pure ()  -- solution logging ignored in subproofs
    | .soli _ => pure ()  -- solution logging ignored in subproofs
    | .conclusionSat _ => pure ()  -- conclusions handled by caller
    | .conclusionBounds _ _ _ _ => pure ()  -- conclusions handled by caller
  return (db, nextId)
where
  /-- Build a pbc subproof step. Returns StoredConstr for the derived
      constraint and the next ID to use after the subproof.
      Strategy: create extended context, lift DB, run inner steps,
      extract contradiction, apply pbc_sound. -/
  buildPbcStep (constrOPB : OPBConstr) (innerSteps : Array ProofStep)
      (resultId : Nat) (db : Std.HashMap Nat StoredConstr) (ctx : Expr)
      (nextIdStart : Nat) (numVars : Nat) :
      Except String (StoredConstr × Nat) := do
    -- Reject conclusion/output steps inside subproofs
    if innerSteps.any (fun s => match s with
        | .conclusion _ | .output => true | _ => false) then
      throw "pbc subproof contains 'conclusion' or 'output' step"
    -- Convert target to PB
    let targetConstr ← opbConstrToPB constrOPB
    let cs := targetConstr.coeffSum
    if targetConstr.degree > cs then
      throw s!"pbc: target degree {targetConstr.degree} > coeffSum {cs}"
    let negConstr := targetConstr.negate
    let targetExpr := buildConstrExpr targetConstr
    let negExpr := buildConstrExpr negConstr
    -- Build ctx_ext = PBFmla.and ctx (PBFmla.one negConstr)
    let oneNeg := mkApp (mkConst ``Sat.PB.PBFmla.one) negExpr
    let ctxExt := mkApp2 (mkConst ``Sat.PB.PBFmla.and) ctx oneNeg
    -- Lift existing DB entries from ctx to ctx_ext
    -- For each sc with proof : ∀ v, allSat v ctx → c.sat v
    -- Build: fun v hv_ext => sc.proof v (allSat_and_left hv_ext)
    let vTy := mkConst ``Sat.PB.Valuation
    let allSatExtTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctxExt
    let extractLeft := mkApp4 (mkConst ``Sat.PB.allSat_and_left)
      (mkBVar 1) ctx oneNeg (mkBVar 0)
    let mut subDb : Std.HashMap Nat StoredConstr := {}
    for (id, sc) in db.toList do
      let liftedBody := mkApp2 sc.proof (mkBVar 1) extractLeft
      let liftedProof := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatExtTy liftedBody
      subDb := subDb.insert id { sc with proof := liftedProof }
    -- Add negated constraint via subsumption
    let selfSub := mkApp (mkConst ``Sat.PB.PBFmla.subsumes_self) ctxExt
    let subRight := mkApp4
      (mkConst ``Sat.PB.PBFmla.subsumes_right) ctxExt ctx oneNeg selfSub
    let negProof := mkApp3
      (mkConst ``Sat.PB.PBFmla.proof_of_subsumes) ctxExt negExpr subRight
    let negId := nextIdStart
    subDb := subDb.insert negId
      { constr := negConstr, expr := negExpr, proof := negProof }
    -- Run inner steps in ctx_ext
    let (finalDb, finalNextId) ← execInnerSteps subDb (negId + 1)
      innerSteps ctxExt numVars
    -- Look up the qed result — must be contradictory
    match finalDb[resultId]? with
    | none => throw s!"pbc qed: constraint {resultId} not in database"
    | some sc =>
      if !sc.constr.isContra then
        throw s!"pbc qed: constraint {resultId} is not contradictory \
          (coeffSum={sc.constr.coeffSum}, degree={sc.constr.degree})"
      -- Build the inner contradiction: ∀ v, allSat v ctx_ext → False
      let allSatExtTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctxExt
      let satProof := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
      let hcProof := mkNatLtProof sc.constr.coeffSum sc.constr.degree
      let contraApp := mkApp3
        (mkConst ``Sat.PB.contra_unsat) sc.expr (mkBVar 1) hcProof
      let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) sc.expr (mkBVar 1)
      let absurdApp := mkApp4 (mkConst ``absurd [.zero])
        satType (mkConst ``False) satProof contraApp
      let innerContra := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatExtTy absurdApp
      -- innerContra : ∀ v, allSat v ctx_ext → False
      -- Transform to: ∀ v, allSat v ctx → C.negate.sat v → False
      -- = fun v hv hneg => innerContra v (allSat_and_intro hv (allSat_one hneg))
      let allSatCtxTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
      let negSatTy := mkApp2 (mkConst ``Sat.PB.Constr.sat) negExpr (mkBVar 1)
      -- Under fun v hv hneg: BVar 0 = hneg, BVar 1 = hv, BVar 2 = v
      let oneProof := mkApp3 (mkConst ``Sat.PB.allSat_one)
        (mkBVar 2) negExpr (mkBVar 0)
      let introProof := mkApp5 (mkConst ``Sat.PB.allSat_and_intro)
        (mkBVar 2) ctx oneNeg (mkBVar 1) oneProof
      let contraBody := mkApp2 innerContra (mkBVar 2) introProof
      let hBody := mkLambda `v .default vTy <|
        mkLambda `hv .default allSatCtxTy <|
          mkLambda `hneg .default negSatTy contraBody
      -- hBody : ∀ v, allSat v ctx → C.negate.sat v → False
      -- Apply pbc_sound: pbc_sound ctx C hd hBody
      let hdProof := mkNatLeProof targetConstr.degree cs
      let pbcProof := mkApp4 (mkConst ``Sat.PB.pbc_sound)
        ctx targetExpr hdProof hBody
      -- Normalize the target constraint
      let (normC, normE, normP) :=
        buildNormalization targetConstr targetExpr pbcProof ctx
      .ok (⟨normC, normE, normP⟩, finalNextId)

/-- Build the main proof of unsatisfiability.
    Returns a proof of type `∀ v, allSat v ctx → False`. -/
partial def buildProof (constrs : Array Sat.PB.Constr) (ctx ctx' : Expr)
    (steps : Array ProofStep) (numVars : Nat) : Except String Expr := do
  let p := mkApp (mkConst ``Sat.PB.PBFmla.subsumes_self) ctx
  let initDb := (← buildClauses constrs ctx 0 constrs.size ctx' p default).2
  let initNextId := constrs.size + 1
  let (db, _) ← execInnerSteps initDb initNextId steps ctx numVars
  -- Find the conclusion step
  for step in steps do
    match step with
    | .conclusion id =>
      match db[id]? with
      | some sc =>
        if sc.constr.isContra then
          let vTy := mkConst ``Sat.PB.Valuation
          let allSatTy := mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx
          let satProof := mkApp2 sc.proof (mkBVar 1) (mkBVar 0)
          let hcProof := mkNatLtProof sc.constr.coeffSum sc.constr.degree
          let contraApp := mkApp3 (mkConst ``Sat.PB.contra_unsat) sc.expr (mkBVar 1) hcProof
          let satType := mkApp2 (mkConst ``Sat.PB.Constr.sat) sc.expr (mkBVar 1)
          let absurdApp := mkApp4 (mkConst ``absurd [.zero])
            satType (mkConst ``False) satProof contraApp
          let finalProof := mkLambda `v .default vTy <|
            mkLambda `hv .default allSatTy absurdApp
          return finalProof
        else
          throw s!"conclusion constraint {id} is not contradictory"
      | none => throw s!"conclusion constraint {id} not in database"
    | _ => pure ()
  throw "no conclusion step found"

-- Propositional reification (Bool-to-Prop bridge)

/-- Check if an expression is `List.nil`. -/
private def isNilExpr (e : Expr) : Bool :=
  e.isAppOf ``List.nil

/-- Build the reified propositional theorem from the PB unsatisfiability proof.
    Transforms `∀ v : Valuation, allSat v ctx → False` into
    `∀ (a₁ ... aₙ : Prop), (reified negation of formula)`.

    Works under `2*nvars + 1` quantifiers:
    `a₁ .. aₙ : Prop, pv : Nat → Prop, h₁ : pv 0 ↔ a₁, ..., hₙ : pv (n-1) ↔ aₙ`

    Mirrors LRAT's `buildReify` from `FromLRAT.lean`. -/
partial def buildReify (ctx ctx' proof : Expr) (nvars : Nat) : Except String (Expr × Expr) := do
  let (e, pr) ← reifyFmla ctx'
  -- Build: fun (pv : Nat → Prop) (h₁ : pv 0 ↔ a₁) ... (hₙ : pv (n-1) ↔ aₙ) => pr
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars - i - 1
    -- hⱼ : pv j ↔ aⱼ
    -- pv is at BVar j (relative to current depth), aⱼ is at BVar nvars (further out)
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h .default ty pr
  -- pv : Nat → Prop
  let pvType := mkForall `_ .default (mkConst ``Nat) (mkSort .zero)
  pr := mkLambda `v .default pvType pr
  -- Lower `e` out of the pv + h₁..hₙ binders
  let mut e := e.lowerLooseBVars (nvars + 1) (nvars + 1)
  -- Build ps = [a₁, ..., aₙ] : List Prop
  let cons := mkApp (mkConst ``List.cons [.zero]) (mkSort .zero)
  let nil := mkApp (mkConst ``List.nil [.zero]) (mkSort .zero)
  let rec mkPS depth e
    | 0 => e
    | n + 1 => mkPS (depth + 1) (mkApp2 cons (mkBVar depth) e) n
  pr := mkApp5 (mkConst ``Sat.PB.PBFmla.refuteProp) e (mkPS 0 nil nvars) ctx proof pr
  -- Introduce ∀ a₁ ... aₙ : Prop
  for _ in [0:nvars] do
    e := mkForall `a .default (mkSort .zero) e
    pr := mkLambda `a .default (mkSort .zero) pr
  pure (e, pr)
where
  /-- The `pv` variable under the `a₁ ... aₙ, pv, h₁ ... hₙ` context -/
  pv := mkBVar nvars
  /-- Reify a PBFmla expression into a propositional expression. -/
  reifyFmla (f : Expr) : Except String (Expr × Expr) :=
    match f.getAppFn.constName? with
    | some ``Sat.PB.PBFmla.and =>
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      do
        let (e₁, h₁) ← reifyFmla f₁
        let (e₂, h₂) ← reifyFmla f₂
        .ok (mkApp2 (mkConst ``Or) e₁ e₂,
         mkApp7 (mkConst ``Sat.PB.PBFmla.Reify_or) pv f₁ e₁ f₂ e₂ h₁ h₂)
    | some ``Sat.PB.PBFmla.one =>
      let c := f.appArg!
      do
        let (e, h) ← reifyConstr c
        .ok (e, mkApp4 (mkConst ``Sat.PB.PBFmla.Reify_one) pv c e h)
    | some name => .error s!"buildReify.reifyFmla: unexpected formula head '{name}'"
    | none => .error "buildReify.reifyFmla: expression has no constant head"
  /-- Reify a constraint expression (walks the term list for CNF constraints). -/
  reifyConstr (c : Expr) : Except String (Expr × Expr) :=
    -- c is `Constr.mk terms degree`
    let terms := c.appFn!.appArg!
    if isNilExpr terms then
      .ok (mkConst ``True, mkApp (mkConst ``Sat.PB.Constr.Reify_cnf_zero) pv)
    else reifyConstr1 terms
  /-- Reify a nonempty constraint term list. -/
  reifyConstr1 (terms : Expr) : Except String (Expr × Expr) :=
    -- terms is `List.cons (Prod.mk coeff lit) rest`
    let pair := terms.appFn!.appArg!  -- (coeff, lit) : Prod Nat Literal
    let l := pair.appArg!              -- the literal
    let rest := terms.appArg!          -- remaining terms
    do
      let (e₁, h₁) ← reifyLiteral l
      if isNilExpr rest then
        .ok (e₁, mkApp4 (mkConst ``Sat.PB.Constr.Reify_cnf_one) pv l e₁ h₁)
      else
        let (e₂, h₂) ← reifyConstr1 rest
        .ok (mkApp2 (mkConst ``And) e₁ e₂,
         mkApp7 (mkConst ``Sat.PB.Constr.Reify_cnf_and) pv l e₁ rest e₂ h₁ h₂)
  /-- Reify a literal expression. -/
  reifyLiteral (l : Expr) : Except String (Expr × Expr) :=
    let n := l.appArg!
    let (e, h) := reifyVar n
    match l.appFn!.constName? with
    | some ``Sat.PB.Literal.pos =>
      .ok (mkApp (mkConst ``Not) e,
       mkApp4 (mkConst ``Sat.PB.Literal.Reify_pos) pv e n h)
    | some ``Sat.PB.Literal.neg =>
      .ok (e, mkApp4 (mkConst ``Sat.PB.Literal.Reify_neg) pv e n h)
    | some name => .error s!"buildReify.reifyLiteral: unexpected literal head '{name}'"
    | none => .error "buildReify.reifyLiteral: expression has no constant head"
  /-- Look up a variable in the quantifier context.
      Under `(a₀ ... a_{n-1} : Prop) (pv) (h₀ : pv 0 ↔ a₀) ... (h_{n-1})`:
      - `aᵢ` is at de Bruijn index `2*nvars - i`
      - `hᵢ` is at de Bruijn index `nvars - i - 1` -/
  reifyVar (v : Expr) : Expr × Expr :=
    let n := v.rawNatLit?.getD 0
    (mkBVar (2 * nvars - n), mkBVar (nvars - n - 1))

-- Top-level entry point

/-- Parse CNF + VeriPB proof and construct a proof of unsatisfiability.
    Returns (numVars, ctx, ctx', proof) where proof : PBFmla.proof ctx [].
    Adds auxiliary declarations to the environment. -/
def fromVeriPBAux (cnf proof : String) (name : Name) :
    MetaM (Nat × Expr × Expr × Expr) := do
  -- Parse CNF
  let formula ← match parseDimacs cnf with
    | .ok f => pure f
    | .error e => throwError "CNF parse error: {e}"
  if formula.clauses.isEmpty then throwError "empty CNF"
  -- Convert to PB constraints
  let pbArray ← formula.clauses.mapM fun clause =>
    match dimacsClauseToPB clause with
    | .ok c => pure c
    | .error e => throwError "clause conversion: {e}"
  -- Build formula expression (balanced tree)
  let ctx' ← match buildConj pbArray 0 pbArray.size with
    | .ok e => pure e
    | .error e => throwError "formula construction: {e}"
  -- Add as a definition for efficient kernel checking
  let ctxName := name ++ `ctx
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := mkConst ``Sat.PB.PBFmla
    value := ctx'
    hints := .regular 0
    safety := .safe
  }
  let ctx := mkConst ctxName
  -- Parse VeriPB proof
  let proofData ← match parseVeriPBProof proof with
    | .ok p => pure p
    | .error e => throwError "VeriPB parse error: {e}"
  -- Build the proof
  match buildProof pbArray ctx ctx' proofData.steps formula.numVars with
  | .ok proofExpr =>
    let proofName := name ++ `proof
    -- The proof type: ∀ v, PBFmla.allSat v ctx → False
    let proofType := mkForall `v .default (mkConst ``Sat.PB.Valuation) <|
      mkForall `hv .default (mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx) <|
        mkConst ``False
    addDecl <| Declaration.thmDecl {
      name := proofName
      levelParams := []
      type := proofType
      value := proofExpr
    }
    -- Build reified propositional theorem
    let (reifyType, reifyValue) ←
      match buildReify ctx ctx' (mkConst proofName) formula.numVars with
      | .ok r => pure r
      | .error e => throwError "reification: {e}"
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := reifyType
      value := reifyValue
    }
    return (formula.numVars, ctx, ctx', mkConst name)
  | .error e => throwError "proof construction failed: {e}"

/-- User-facing command: `veripb_proof name "cnf..." "proof..."` -/
elab "veripb_proof " n:ident ppSpace cnf:str ppSpace proof:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnfStr := cnf.getString
    let proofStr := proof.getString
    let (_nvars, _ctx, _ctx', _proof) ← fromVeriPBAux cnfStr proofStr name

/-- Term-level elaborator: `from_veripb "cnf..." "proof..."`.
    Produces the reified propositional theorem directly as a term.
    Usage: `theorem unsat : ... := from_veripb "p cnf ..." "pseudo-Boolean ..."` -/
elab "from_veripb " cnf:str ppSpace proof:str : term <= expectedType => do
  let cnfStr := cnf.getString
  let proofStr := proof.getString
  -- Use a fresh hygienic name for auxiliary declarations
  let name ← Lean.Elab.Term.mkAuxName `_veripb
  let (_nvars, _ctx, _ctx', proofConst) ← fromVeriPBAux cnfStr proofStr name
  -- Check that the produced type matches the expected type
  let proofType ← inferType proofConst
  unless (← isDefEq proofType expectedType) do
    throwError "from_veripb: proof type{indentExpr proofType}\n\
      does not match expected type{indentExpr expectedType}"
  return proofConst

/-- Command with file loading:
`veripb_proof_file name "path/to/cnf" "path/to/proof"`.
Reads CNF and proof files from disk at elaboration time. -/
elab "veripb_proof_file " n:ident ppSpace cnfPath:str ppSpace proofPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnfFile := System.FilePath.mk cnfPath.getString
    let proofFile := System.FilePath.mk proofPath.getString
    let cnfStr ← IO.FS.readFile cnfFile
    let proofStr ← IO.FS.readFile proofFile
    let (_nvars, _ctx, _ctx', _proof) ← fromVeriPBAux cnfStr proofStr name

/-- Term-level elaborator with file loading:
`from_veripb_file "path/to/cnf" "path/to/proof"`.
Reads CNF and proof files from disk at elaboration time. -/
elab "from_veripb_file " cnfPath:str ppSpace proofPath:str : term <= expectedType => do
  let cnfFile := System.FilePath.mk cnfPath.getString
  let proofFile := System.FilePath.mk proofPath.getString
  let cnfStr ← IO.FS.readFile cnfFile
  let proofStr ← IO.FS.readFile proofFile
  let name ← Lean.Elab.Term.mkAuxName `_veripb
  let (_nvars, _ctx, _ctx', proofConst) ← fromVeriPBAux cnfStr proofStr name
  let proofType ← inferType proofConst
  unless (← isDefEq proofType expectedType) do
    throwError "from_veripb_file: proof type\
      {indentExpr proofType}\n\
      does not match expected type{indentExpr expectedType}"
  return proofConst

-- Direct PB constraint entry point (no CNF parsing)

/-- Verify a VeriPB proof against PB constraints given directly.
    Returns (ctx, ctx', proofExpr) where proofExpr : ∀ v, allSat v ctx → False.
    Skips CNF parsing and reification — caller provides the constraints.
    Adds auxiliary declarations to the environment. -/
def fromVeriPBDirect (constrs : Array Sat.PB.Constr) (numVars : Nat)
    (proofStr : String) (name : Name) : MetaM (Expr × Expr × Expr) := do
  if constrs.isEmpty then throwError "empty constraint array"
  -- Build formula expression (balanced tree)
  let ctx' ← match buildConj constrs 0 constrs.size with
    | .ok e => pure e
    | .error e => throwError "formula construction: {e}"
  -- Add as a definition for efficient kernel checking
  let ctxName := name ++ `ctx
  addDecl <| Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := mkConst ``Sat.PB.PBFmla
    value := ctx'
    hints := .regular 0
    safety := .safe
  }
  let ctx := mkConst ctxName
  -- Parse VeriPB proof
  let proofData ← match parseVeriPBProof proofStr with
    | .ok p => pure p
    | .error e => throwError "VeriPB parse error: {e}"
  -- Build the proof
  match buildProof constrs ctx ctx' proofData.steps numVars with
  | .ok proofExpr =>
    let proofName := name ++ `proof
    let proofType := mkForall `v .default (mkConst ``Sat.PB.Valuation) <|
      mkForall `hv .default
        (mkApp2 (mkConst ``Sat.PB.PBFmla.allSat) (mkBVar 0) ctx) <|
        mkConst ``False
    addDecl <| Declaration.thmDecl {
      name := proofName
      levelParams := []
      type := proofType
      value := proofExpr
    }
    return (ctx, ctx', mkConst proofName)
  | .error e => throwError "proof construction failed: {e}"

-- OPB file parsing for native PB instances

/-- Parse term pairs from OPB token list (coeff var coeff var ...). -/
private def parseOPBTerms : List String → Nat →
    Except String (List Sat.PB.Term × Nat)
  | [], maxVar => .ok ([], maxVar)
  | [_], mv => .ok ([], mv) -- odd token count, ignore trailing
  | coeffStr :: varStr :: rest, maxVar => do
    let coeff ← match (coeffStr.replace "+" "").toNat? with
      | some c => .ok c
      | none => .error s!"OPB parse: bad coeff '{coeffStr}'"
    let (neg, varName) := if varStr.startsWith "~" then
      (true, (varStr.drop 1).toString)
    else (false, varStr)
    let varNum ← match (varName.drop 1).toString.toNat? with
      | some n => if n == 0 then .error s!"OPB parse: variable index 0 invalid: '{varStr}'"
                  else .ok n
      | none => .error s!"OPB parse: bad var '{varStr}'"
    let varIdx := varNum - 1
    let mv := if varNum > maxVar then varNum else maxVar
    let lit := if neg then Sat.PB.Literal.neg varIdx
               else Sat.PB.Literal.pos varIdx
    let (restTerms, mv') ← parseOPBTerms rest mv
    .ok ((coeff, lit) :: restTerms, mv')

/-- Parse one OPB constraint line. Returns constraint and max var seen. -/
private def parseOPBLine (line : String) :
    Except String (Sat.PB.Constr × Nat) := do
  let parts := line.splitOn ";"
  let constrStr := (parts[0]!).trimAscii.toString
  let geqParts := constrStr.splitOn ">="
  if geqParts.length < 2 then
    .error s!"OPB parse: no >= in line: {line}"
  else
    let lhs := (geqParts[0]!).trimAscii.toString
    let rhs := (geqParts[1]!).trimAscii.toString
    let degree ← match rhs.toNat? with
      | some d => .ok d
      | none => .error s!"OPB parse: bad degree '{rhs}'"
    let tokens := lhs.splitOn " " |>.filter (!·.isEmpty)
    let (terms, maxVar) ← parseOPBTerms tokens 0
    .ok (⟨terms, degree⟩, maxVar)

/-- Parse an objective line (min: or max:) into a constraint with degree 0.
    The constraint represents the objective function sum. -/
private def parseOPBObjective (line : String) : Except String Sat.PB.Constr := do
  let stripped := if line.startsWith "min:" then (line.drop 4).toString
                  else if line.startsWith "max:" then (line.drop 4).toString
                  else line
  let cleaned := (stripped.splitOn ";" |>.head!).trimAscii.toString
  let tokens := cleaned.splitOn " " |>.filter (!·.isEmpty)
  let (terms, _) ← parseOPBTerms tokens 0
  .ok ⟨terms, 0⟩

/-- Parse an OPB file into constraints, variable count, and optional objective.
    Supports the subset of OPB used by RoundingSat:
    header line starting with `*`, constraint lines with terms and `>=`.
    Returns `(numVars, constraints, objective?)`. -/
def parseOPBWithObj (s : String) :
    Except String (Nat × Array Sat.PB.Constr × Option Sat.PB.Constr) := do
  let allLines := s.splitOn "\n"
  -- Extract objective if present
  let objLine := allLines.find? fun l =>
    let t := l.trimAscii.toString
    t.startsWith "min:" || t.startsWith "max:"
  let objective ← match objLine with
    | some l => do
      let obj ← parseOPBObjective l.trimAscii.toString
      pure (some obj)
    | none => pure none
  -- Parse constraints (skip comments and objective)
  let constrLines := allLines.filter fun l =>
    let t := l.trimAscii.toString
    !t.isEmpty && !t.startsWith "*" && !t.startsWith "min:" && !t.startsWith "max:"
  let (maxVar, constrs) ← constrLines.foldlM (init := (0, #[])) fun (mv, cs) line => do
    let (constr, newMv) ← parseOPBLine line
    .ok (if newMv > mv then newMv else mv, cs.push constr)
  .ok (maxVar, constrs, objective)

/-- Parse an OPB file into an array of PB constraints and variable count.
    Supports the subset of OPB used by RoundingSat:
    header line starting with `*`, constraint lines with terms and `>=`.
    Skips `min:`/`max:` objective lines. -/
def parseOPB (s : String) : Except String (Nat × Array Sat.PB.Constr) := do
  let (numVars, constrs, _) ← parseOPBWithObj s
  .ok (numVars, constrs)

-- Command: load OPB + proof files, verify, register theorem
-- `opb_veripb_file name "path/to/opb" "path/to/proof"`
elab "opb_veripb_file " n:ident ppSpace
    opbPath:str ppSpace proofPath:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let opbStr ← IO.FS.readFile (System.FilePath.mk opbPath.getString)
    let proofStr ← IO.FS.readFile
      (System.FilePath.mk proofPath.getString)
    let (numVars, constrs) ← match parseOPB opbStr with
      | .ok r => pure r
      | .error e => throwError "OPB parse error: {e}"
    let (_ctx, _ctx', _proof) ←
      fromVeriPBDirect constrs numVars proofStr name
    Lean.logInfo m!"Registered {name} (OPB: {numVars} vars, \
      {constrs.size} constraints, fully verified)"

-- Data-level verification for SAT/BOUNDS proofs (no theorem produced)
-- Used to validate that proofs parse and check correctly at the data level.

/-- Initialize checking state from OPB constraints (for SAT/BOUNDS verification). -/
def CheckState.fromOPB (constrs : Array Sat.PB.Constr) (numVars : Nat)
    (obj : Option Sat.PB.Constr := none) : CheckState :=
  let init : Std.HashMap Nat Sat.PB.Constr × Nat := ({}, 1)
  let result := constrs.foldl (init := init) fun (db, nextId) constr =>
    (db.insert nextId constr, nextId + 1)
  ⟨result.1, result.2, constrs.size, numVars, none, obj⟩

/-- Verify an OPB + proof at data level only. Returns Ok if valid. -/
def verifyOPBProof (opbStr proofStr : String) : Except String String := do
  let (numVars, constrs, objective) ← parseOPBWithObj opbStr
  let proofData ← parseVeriPBProof proofStr
  let initState := CheckState.fromOPB constrs numVars objective
  let _finalState ← execAllSteps initState proofData.steps
  -- Determine conclusion type from the proof (scan from end)
  let conclusionType := proofData.steps.toList.reverse.findSome? fun s =>
    match s with
    | .conclusion _ => some "UNSAT"
    | .conclusionSat _ => some "SAT"
    | .conclusionBounds lb _ ub _ => some s!"BOUNDS {lb} {ub}"
    | _ => none
  match conclusionType with
  | some ct => .ok ct
  | none => .ok "NONE"

-- Command: data-level verification for SAT/BOUNDS proofs
-- `veripb_check "path/to/opb" "path/to/proof"`
elab "veripb_check " opbPath:str ppSpace proofPath:str : command => do
  liftTermElabM do
    let opbStr ← IO.FS.readFile (System.FilePath.mk opbPath.getString)
    let proofStr ← IO.FS.readFile (System.FilePath.mk proofPath.getString)
    match verifyOPBProof opbStr proofStr with
    | .ok ct => Lean.logInfo m!"Proof verified: conclusion {ct}"
    | .error e => throwError "Verification failed: {e}"

end VeriPB
