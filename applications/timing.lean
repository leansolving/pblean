/-
Copyright (c) 2026 Stefan Szeider. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Szeider
-/
import VeriPB.Tactic.Sat.Reflect

/-!
Checker-only timing of `checkProofBool` (parse + check, and parse alone) on
the Paley instances. The checker modules are precompiled, so this must be
run with the checker library loaded, exactly as `lake build` does; otherwise
the checker runs in the IR interpreter (about 20x slower):

    lake env lean --load-dynlib=.lake/build/lib/libveripb_VeriPBReflect.dylib \
      applications/timing.lean

(`.so` on Linux). `applications/benchmark.py` measures the end-to-end
`veripb_reflect` command, which adds Lean startup, the compilation of the
constraint array inside `nativeEqTrue`, and the kernel check.
-/

namespace VeriPB.Timing

/-- Opaque barrier: keeps the compiler from sinking a pure computation past
the surrounding timestamps. -/
@[noinline] def force (b : Bool) : IO Bool := pure b
@[noinline] def forceN (n : Nat) : IO Nat := pure n

def timeOne (p : Nat) : IO Unit := do
  let opbStr ← IO.FS.readFile s!"applications/paley/Paley_{p}.opb"
  let proofStr ← IO.FS.readFile s!"applications/paley/Paley_{p}_kernel.pbp"
  let (numVars, constrs) ← match VeriPB.parseOPB opbStr with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let t0 ← IO.monoMsNow
  let ok ← force (VeriPB.Reflect.checkProofBool constrs numVars proofStr)
  let t1 ← IO.monoMsNow
  let n ← forceN (match VeriPB.parseVeriPBProof proofStr with
    | .ok d => d.steps.size | .error _ => 0)
  let t2 ← IO.monoMsNow
  IO.println s!"Paley({p}): {n} steps, checkProofBool = {ok} in {t1 - t0} ms \
    (parse alone {t2 - t1} ms)"

end VeriPB.Timing

#eval show IO Unit from do
  for p in [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101] do
    VeriPB.Timing.timeOne p
