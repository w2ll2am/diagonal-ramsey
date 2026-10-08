# R(k,k) ≤ 3.4986238^k

**R(k,k) ≤ 3.4986238^k** (an e^{1.2523697k} bound) for all sufficiently large k, formally verified in Lean 4 (Mathlib).

## What to read

- [`Theorems/Thm_DiagRamsey_diagonal_le_three_point_five_pow.lean`](Theorems/Thm_DiagRamsey_diagonal_le_three_point_five_pow.lean): the statement.
- [`Definitions/Def_DiagRamsey_Basic.lean`](Definitions/Def_DiagRamsey_Basic.lean): the definition of `ramseyNumber`.

Everything else is machine-checked.

## Verify

From the repository root (Linux x86_64 or macOS, with [elan](https://github.com/leanprover/elan) installed):

```bash
lake exe cache get && LEAN_NUM_THREADS=<N> lake build
```

The build succeeds only if every module compiles and `FinalCheck.lean` passes. It checks that the main theorem proves
the statement in `Theorems/`, and that it, `diagonal_le_3p4986238_pow` and `diagonal_le_exp_z` depend only on the
axioms `[propext, Classical.choice, Quot.sound]`.

**Resources:** choose `N = min(cores, RAM_GB / 20)` (some modules need 16–20 GB each; for example N = 36 on a 768 GB
machine); allow at least 700 GB of disk and about 7–9 hours at N ≈ 36 (an estimate); run `ulimit -n 1048576` first,
and make sure `sysctl vm.max_map_count` is at least 1048576.

## Paper

[`preprint/A-3.49-k-bound-for-diagonal-Ramsey-numbers-October-8-2026/main.pdf`](preprint/A-3.49-k-bound-for-diagonal-Ramsey-numbers-October-8-2026/main.pdf)

The proof builds on Lu and Wang's Lean development
([github.com/sichen-wang/diagonal-ramsey-numbers](https://github.com/sichen-wang/diagonal-ramsey-numbers), commit
`5ec98f47`), which it uses as a dependency; we thank them for making it public.

## Licence

MIT; see [`LICENSE`](LICENSE). The Lu–Wang dependency is also MIT-licensed.
