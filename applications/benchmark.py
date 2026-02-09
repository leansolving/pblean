#!/usr/bin/env python3
"""
Benchmark all showcase theorems for VeriPB application instances.
Produces timing tables in milliseconds.

Usage:
    python3 benchmark.py           # Lean verification times only
    python3 benchmark.py --full    # Also re-solve + re-elaborate
    python3 benchmark.py --direct  # Also run direct (Expr-building) method
    python3 benchmark.py --paley   # Only Paley instances
    python3 benchmark.py --comb    # Only combinatorial instances

Requirements:
    - lake (Lean 4 build tool) available in PATH
    - VeriPB project built (lake build from project root)
    - For --full: roundingsat and veripb in PATH
"""

import subprocess
import os
import time
import sys
import signal
import tempfile
import re
import argparse

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
VERIBP_DIR = os.path.dirname(SCRIPT_DIR)

# ============================================================
# Utility functions
# ============================================================


def run_lean(code, timeout=600):
    """Run Lean code via lake env lean, return (wall_ms, status).

    Status is True (success), False (error), 'TO' (timeout), or 'MO' (memory).
    Uses process groups so the entire lean process tree is killed on timeout."""
    fd, path = tempfile.mkstemp(suffix='.lean', dir=VERIBP_DIR)
    try:
        with os.fdopen(fd, 'w') as f:
            f.write(code)
        t0 = time.time()
        proc = subprocess.Popen(
            ["lake", "env", "lean", path],
            cwd=VERIBP_DIR,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=True
        )
        try:
            _, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            proc.wait()
            elapsed = (time.time() - t0) * 1000
            return round(elapsed), 'TO'
        elapsed = (time.time() - t0) * 1000
        if proc.returncode != 0:
            stderr_text = stderr.decode(errors='replace')
            if 'out of memory' in stderr_text.lower():
                return round(elapsed), 'MO'
            sys.stderr.write(
                f"Lean error:\n{stderr_text[:500]}\n")
            return round(elapsed), False
        return round(elapsed), True
    finally:
        os.unlink(path)


def run_solve_and_elaborate(opb_path, timeout=300):
    """Run RoundingSat + VeriPB elaborate, return (solve_ms, elab_ms).

    Uses a temporary directory for intermediate files."""
    with tempfile.TemporaryDirectory() as tmpdir:
        proof_base = os.path.join(tmpdir, 'proof')
        kernel_out = os.path.join(tmpdir, 'kernel.pbp')

        # Solve
        t0 = time.time()
        result = subprocess.run(
            ["roundingsat", opb_path,
             f"--proof-log={proof_base}"],
            capture_output=True, text=True, timeout=timeout
        )
        solve_ms = (time.time() - t0) * 1000

        if "s UNSATISFIABLE" not in result.stdout:
            sys.stderr.write(
                f"RoundingSat: not UNSAT for {opb_path}\n")
            return round(solve_ms), 0

        # Elaborate
        t0 = time.time()
        subprocess.run(
            ["veripb", "--elaborate", kernel_out,
             opb_path, proof_base],
            capture_output=True, text=True, timeout=timeout
        )
        elab_ms = (time.time() - t0) * 1000

        return round(solve_ms), round(elab_ms)


def opb_stats(opb_path):
    """Parse OPB header for (variables, constraints)."""
    with open(opb_path) as f:
        for line in f:
            m = re.search(
                r'#variable=\s*(\d+)\s+#constraint=\s*(\d+)',
                line)
            if m:
                return int(m.group(1)), int(m.group(2))
    return 0, 0


def proof_lines(kernel_path):
    """Count lines in kernel proof."""
    lines = 0
    with open(kernel_path) as f:
        for line in f:
            lines += 1
    return lines


def paley_alpha(opb_path):
    """Extract alpha from Paley OPB.

    The last constraint is the budget: sum >= alpha+1 (UNSAT)."""
    budget = 0
    with open(opb_path) as f:
        for line in f:
            if not line.startswith('*'):
                m = re.search(r'>= (\d+)', line)
                if m:
                    budget = int(m.group(1))
    return budget - 1


def paley_edges(p):
    """Number of edges in Paley(p): p*(p-1)/4."""
    return p * (p - 1) // 4


def machine_info():
    """Return CPU model string."""
    try:
        result = subprocess.run(
            ['sysctl', '-n', 'machdep.cpu.brand_string'],
            capture_output=True, text=True, timeout=5)
        return result.stdout.strip()
    except Exception:
        return "unknown"


def fmt_result(ms, status):
    """Format a benchmark result for table display."""
    if status == 'TO':
        return f" {'TO':>8}"
    elif status == 'MO':
        return f" {'MO':>8}"
    elif status is True:
        return f" {ms:>8}"
    else:
        return f" {'FAIL':>8}"


# ============================================================
# Benchmark instances
# ============================================================

COMBINATORIAL = [
    {
        'name': 'Langford L(2,6)',
        'opb': os.path.join(
            SCRIPT_DIR, 'langford', 'langford6.opb'),
        'kernel': os.path.join(
            SCRIPT_DIR, 'langford', 'langford6_kernel.pbp'),
    },
    {
        'name': 'Schur S(2)=4',
        'opb': os.path.join(SCRIPT_DIR, 'schur', 'schur5.opb'),
        'kernel': os.path.join(
            SCRIPT_DIR, 'schur', 'schur5_kernel.pbp'),
    },
    {
        'name': 'Van der Waerden W(2,3)=9',
        'opb': os.path.join(SCRIPT_DIR, 'vdw', 'vdw9.opb'),
        'kernel': os.path.join(
            SCRIPT_DIR, 'vdw', 'vdw9_kernel.pbp'),
    },
    {
        'name': 'Ramsey R(3,3)=6',
        'opb': os.path.join(
            SCRIPT_DIR, 'ramsey', 'ramsey6.opb'),
        'kernel': os.path.join(
            SCRIPT_DIR, 'ramsey', 'ramsey6_kernel.pbp'),
    },
    {
        'name': 'Eq. Coloring chi_eq(K_{3,3,1})=5',
        'opb': os.path.join(
            SCRIPT_DIR, 'eqcoloring', 'k331_4.opb'),
        'kernel': os.path.join(
            SCRIPT_DIR, 'eqcoloring', 'k331_4_kernel.pbp'),
    },
]

PALEY_PRIMES = [13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101]


# ============================================================
# Main
# ============================================================

def main():
    parser = argparse.ArgumentParser(
        description='Benchmark VeriPB showcase theorems')
    parser.add_argument(
        '--full', action='store_true',
        help='Re-solve + re-elaborate (needs roundingsat, '
             'veripb)')
    parser.add_argument(
        '--paley', action='store_true',
        help='Only Paley instances')
    parser.add_argument(
        '--comb', action='store_true',
        help='Only combinatorial instances')
    parser.add_argument(
        '--direct', action='store_true',
        help='Also run direct (Expr-building) method')
    parser.add_argument(
        '--timeout', type=int, default=600,
        help='Timeout in seconds for reflect method (default: 600)')
    parser.add_argument(
        '--direct-timeout', type=int, default=60,
        help='Timeout in seconds for direct method (default: 60)')
    args = parser.parse_args()

    print(f"VeriPB Benchmark — all times in milliseconds")
    print(f"Machine: {machine_info()}")

    # ----------------------------------------------------------
    # Combinatorial showcase
    # ----------------------------------------------------------
    if not args.paley:
        print(f"\n{'='*80}")
        print("Combinatorial Showcase Theorems")
        print(f"{'='*80}")
        hdr_parts = [f"{'Problem':<35}", f"{'Vars':>5}",
                     f"{'Cstrs':>6}", f"{'Lines':>6}"]
        if args.full:
            hdr_parts += [f"{'Solve':>6}", f"{'Elab':>5}"]
        if args.direct:
            hdr_parts.append(f"{'Direct':>8}")
        hdr_parts.append(f"{'Reflect':>8}")
        hdr = ' '.join(hdr_parts)
        print(hdr)
        print("-" * len(hdr))

        for inst in COMBINATORIAL:
            name = inst['name']
            v, c = opb_stats(inst['opb'])
            l = proof_lines(inst['kernel'])

            lean_code = (
                'import VeriPB.Tactic.Sat.Reflect\n'
                f'veripb_reflect bench\n'
                f'  "{inst["opb"]}"\n'
                f'  "{inst["kernel"]}"\n'
            )

            solve_str = ''
            if args.full:
                s, e = run_solve_and_elaborate(inst['opb'])
                solve_str = f" {s:>6} {e:>5}"

            direct_str = ''
            if args.direct:
                direct_lean = (
                    'import VeriPB.Tactic.Sat.FromVeriPB\n'
                    f'opb_veripb_file bench\n'
                    f'  "{inst["opb"]}"\n'
                    f'  "{inst["kernel"]}"\n'
                )
                d_ms, d_ok = run_lean(
                    direct_lean, timeout=args.direct_timeout)
                direct_str = fmt_result(d_ms, d_ok)

            r_ms, r_ok = run_lean(lean_code, timeout=args.timeout)
            reflect_str = fmt_result(r_ms, r_ok)

            print(f"{name:<35} {v:>5} {c:>6} "
                  f"{l:>6}"
                  f"{solve_str}{direct_str}{reflect_str}")

    # ----------------------------------------------------------
    # Paley independent set
    # ----------------------------------------------------------
    if not args.comb:
        print(f"\n{'='*80}")
        print("Independent Set on Paley Graphs")
        print(f"{'='*80}")
        hdr_parts = [f"{'p':>4}", f"{'m':>6}",
                     f"{chr(945):>3}", f"{'Lines':>6}"]
        if args.full:
            hdr_parts += [f"{'Solve':>6}", f"{'Elab':>5}"]
        if args.direct:
            hdr_parts.append(f"{'Direct':>8}")
        hdr_parts.append(f"{'Reflect':>8}")
        hdr = ' '.join(hdr_parts)
        print(hdr)
        print("-" * len(hdr))

        for p in PALEY_PRIMES:
            opb = os.path.join(
                SCRIPT_DIR, 'paley', f'Paley_{p}.opb')
            kernel = os.path.join(
                SCRIPT_DIR, 'paley',
                f'Paley_{p}_kernel.pbp')

            if not os.path.exists(opb):
                print(f"{p:>4}  — OPB missing")
                continue
            if not os.path.exists(kernel):
                print(f"{p:>4}  — kernel proof missing")
                continue

            m = paley_edges(p)
            alpha = paley_alpha(opb)
            l = proof_lines(kernel)

            lean_code = (
                'import VeriPB.Tactic.Sat.Reflect\n'
                'set_option maxRecDepth 200000\n'
                'set_option maxHeartbeats 800000\n'
                f'veripb_reflect bench\n'
                f'  "{opb}"\n'
                f'  "{kernel}"\n'
            )

            solve_str = ''
            if args.full:
                s, e = run_solve_and_elaborate(opb)
                solve_str = f" {s:>6} {e:>5}"

            direct_str = ''
            if args.direct:
                direct_lean = (
                    'import VeriPB.Tactic.Sat.FromVeriPB\n'
                    f'opb_veripb_file bench\n'
                    f'  "{opb}"\n'
                    f'  "{kernel}"\n'
                )
                d_ms, d_ok = run_lean(
                    direct_lean, timeout=args.direct_timeout)
                direct_str = fmt_result(d_ms, d_ok)

            r_ms, r_ok = run_lean(lean_code, timeout=args.timeout)
            reflect_str = fmt_result(r_ms, r_ok)

            print(f"{p:>4} {m:>6} {alpha:>3} "
                  f"{l:>6}"
                  f"{solve_str}{direct_str}{reflect_str}")

    print()


if __name__ == '__main__':
    main()
