# Publication extract for P0r12: `R(k,k) ≤ 3.4986238^k` (read-only)

aidan-of-lindisfarne, 2026-10-08, on the Q18R2 build volume (`/data`, `vol-0a39aea95edbce9fc`), r7a.4xlarge.
Everything new is under `/data/publication_staging/`. Nothing under `/data/ten-thousand-agents` or `/data/q18r2` was
modified. No `verify.sh`, `port_full*.py`, `port_mem.py`, `lake build`, `lake update` or `PORT_FRESH`, and no edits to
existing Lean. The only Lean runs were plain `lean` on the two new staging files. One of them wrote a single
`.olean`, to `/data/publication_staging/fc_build/` only. Afterwards no file in the port build or in
`lean-luwang/.lake/build` was newer than the staged files (checked with `find -newer` after steps 5 and 6).

## Result

| check | result |
|---|---|
| closure (port rule) | **82,143** modules = the `82143/82143 modules compile under 4.32.1` line; 0 `Theorems.*` |
| stamp identity (step 4) | **82,143 / 82,143 match**, top module included |
| Bridge sources | 42/42 OK (12 hand-written vs git `7b131253`, 30 `P06Lines*` vs `MANIFEST_P0r12`) |
| record files | 4/4 sha256 = CERTIFICATE_OF_RECORD.md §2, plus the uncompressed bank |
| `SharpBound.lean` (= `Tight.lean`) | exit 0; output byte-identical to `Tight.out` |
| `FinalCheck.lean` | exit 0, empty output: statement verbatim, all 3 `#guard_msgs` pass |

Axioms (`SharpBound.out`, step 5; the step 6 `lean -o` compile printed the same three lines):

```
'DiagRamsey.diagonal_le_exp_z' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiagRamsey.diagonal_le_3p4987_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiagRamsey.diagonal_le_3p4986238_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`FinalCheck.lean` checks, in one file that imports both the port's top module and `SharpBound`, that
`DiagRamsey.diagonal_le_three_point_five_pow`, `diagonal_le_3p4986238_pow` and `diagonal_le_exp_z` each depend on
exactly `[propext, Classical.choice, Quot.sound]`.

## 1. Preflight (09:47 UTC)

- `lean-luwang/.lake/portfullp0_P0r12/` has `Composite.lean Definitions Lemmas Solutions Theorems build`.
- 16 vCPU, 123 GB RAM (`free -g`), no swap. `/data`: 590 G, 152 G used.
- git HEAD after `pull --rebase --autostash`: `443f5b7d46a5fc3de9306782630b95c2c915730b`.
- `lean/lean-toolchain` (v4.33.1): `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`.
- `lean-luwang/lean-toolchain` (v4.32.1): `8e3538e0ab5f81a3ee04927d8838c8c674e0e112838b4b3ce87ec218143276af`.

## 2. Closure (`tools/closure.py`, 10 s)

Starting point: `Solutions.Sol_DiagRamsey_diagonal_le_three_point_five_pow` in the port tree, following
`^import (\S+)`. I applied the same rule as `port_full.run()`: local means `Definitions`, `Theorems`, `Solutions` or
`Lemmas`, minus the two `shared` definitions. Those two `.olean` files are copied from `lean-luwang`'s build and are
not compiled by the port, so they are not in its count.

- **82,143** port modules: 6 Definitions, 38 Lemmas, 82,099 Solutions, 0 Theorems. This equals the port log's
  `82143/82143 modules compile under 4.32.1`.
- 2 shared definitions: `Definitions.Def_DiagRamsey_Basic`, `Definitions.Def_DiagRamsey_LuWangSource`.
- **42 Bridge modules**, resolved in `lean-luwang/Bridge/`. 12 hand-written: Arrows, Concave, Data, DataDerivs,
  DataKnots, DataValues, Foundations, KernelRfl, ParseRat, Source, Tangent, TangentLines. Plus `P06LinesP0r12` and
  `P06LinesP0r12_{0..28}`. No other `lean-luwang` local module is reached.
- External roots reached: Mathlib, Batteries, Std, and Lu–Wang's `RamseyCurrent` package (libraries
  `RamseyRefinement`, `RamseyLean`). The brief's stop-list didn't include Batteries, `RamseyRefinement` or
  `RamseyLean`, so I added them; all three are pinned packages in `lean-luwang/lake-manifest.json`.
- The full list, in three sections, is in `closure_modules.txt`.

## 3. Staging (11 s copy, `rsync -a` / `cp -p` / `git show`)

- `repo/`: 82,192 files, 1,819,418,761 bytes. That is 82,143 closure files, 2 shared definitions,
  `Theorems/Thm_DiagRamsey_diagonal_le_three_point_five_pow.lean`, 42 Bridge files, `lean-toolchain`,
  `lake-manifest.json`, and (steps 5–6) `SharpBound.lean` and `FinalCheck.lean`.
- `reference/Composite.lean`: the port tree's copy.
- `evidence/q18r2_publish/`: `/data/q18r2/publish/` copied whole (18 files, 38 MB).
- `evidence/record/`, via `git show 7b131253…:diagonal-ramsey/research/hermann-joseph/p05/record/<f>`. The brief gave
  this path relative to `diagonal-ramsey/`.

  | file | sha256 | §2 |
  |---|---|---|
  | `bank_r12_rootpair.json.gz` | f18ba11260a8a2822de0ea5c0a724ae53015deeaf7e670b77de0cb854dd60fb6 | match |
  | … uncompressed | bc3c24cf97cb9684b97f76ab7bf0e57775525d550a5dd1424d563900897442bc | match |
  | `record_r12_rootpair_merged.json` | 46a50d7275981c981b1f1ba14bd2c03aad426c7902ab180ff2a3b12e8f07c87c | match |
  | `gates_r12_rootpair.json` | 1f31acf5b1c7ad429f32d303d6601dcba783caa33d91ddb4090d10f0bca858a3 | match |
  | `CERTIFICATE_OF_RECORD.md` | b48a110b4b8aab78647240b9928d7a9d806f16e1703c18ca0eaf3d6da4a5f8c7 | (itself) |

- `find repo -name '*.lean' -size +95M`: nothing.

## 4. Identity proof (`tools/stamps.py`, 14 s, no Lean)

- For every staged port module, I recomputed the stamp from the staged file using `_stamp()`'s formula exactly:
  sha256 of the toolchain bytes, the source bytes, and `M=dep\n` for each import. Here dep is the stored stamp if M's
  source is in the port tree (`unbuilt` if it has none, as for the shared definitions), else the sha256 of M's
  `.olean` in the port `build/` or `lean-luwang/.lake/build/lib/lean/`, else `external`.
  **82,143 / 82,143 match the stored `build/<path>.olean.stamp`.** Top module:
  `d84fa275c41d36d3032320a31e8c16ec6011455cf0e73bd179b6af4b23ef8b74`, written 2026-10-06 22:32:46 UTC.
- Shared definitions: the staged source equals `lean-luwang/Definitions/` and the port build's `.olean` equals
  `lean-luwang`'s, for both modules.
- Bridge sources: 12/12 hand-written equal `git show 7b131253:diagonal-ramsey/lean-luwang/Bridge/<f>`. All 30
  `P06Lines*` files equal `verify/MANIFEST_P0r12.sha256`, which is byte-identical to `/data/q18r2/publish/`'s copy.
  `Theorems/Thm_DiagRamsey_lu_wang_lines_P0r12.lean` matches the manifest in both the port tree and `lean/`.
- Bridge `.olean` files: a stamp contains only a digest, so an `.olean`'s hash can't be read out of it. Instead,
  each recomputed stamp uses the current sha256 of every Bridge `.olean` its module imports, so a match pins those
  files. Exactly two Bridge modules are imported directly by port modules, and both are pinned:
  `Bridge.Foundations` (5aadddc6…, via `Lemmas.DiagRamsey_JB_Main`) and `Bridge.P06LinesP0r12` (4554f5b7…, via
  `Solutions.P06.P0r12.Final`).
  - **Limit:** the other 40 Bridge `.olean` files are imported only by Bridge modules, so no stamp pins them. Their
    sources match (above). All of them were written before the Q18R2 port phase began (18:48:30 UTC 2026-10-06):
    the lake-built ones on 2026-10-05, `TangentLines` at 18:35:07, and `P06LinesP0r12_*` at 18:46:43–18:48:18
    (Q18R2's `lines` phase). Nothing in `lean-luwang/.lake/build/lib/lean/Bridge/` has been written since, except
    `P06LinesP0r12.ilean`, written seconds after its `.olean`. Each `.olean`'s sha256 is in `logs/stamp_report.txt`.
- `SOURCE_SHA256SUMS`: 82,190 staged `.lean` files, with paths relative to `repo/`.

## 5. Sharp-bound re-check (09:51:31 → 10:01:09 UTC, 578 s, max RSS 50 GB)

`repo/SharpBound.lean` = `git show main:…/Q18R2_exp_z/Tight.lean`, unchanged. It was compiled with the command from
the brief and exited 0. `SharpBound.out` is byte-identical to `Tight.out`. Nothing was rebuilt.

## 6. FinalCheck (10:02:01 → 10:03:45 UTC)

- `FinalCheck.lean` follows the brief's template, with the statement copied verbatim from
  `Theorems/Thm_DiagRamsey_diagonal_le_three_point_five_pow.lean`.
- `lean -o fc_build/SharpBound.olean SharpBound.lean`: exit 0, 53 s. It printed the same three axioms lines
  (`logs/SharpBound_olean.out`, byte-identical to `SharpBound.out`). Faster than step 5 because the oleans were cached
  in memory.
- `FinalCheck.lean` with `LEAN_PATH=fc_build:port build:…`: exit 0, 52 s, **empty output**. The brief expected the
  three `SharpBound` lines here. They don't appear because Lean doesn't replay an imported module's messages, and
  `#guard_msgs` swallows messages that match. A mismatch would have been an error and a non-zero exit.
- Both commands need `--root=/data/publication_staging/repo`. My first attempt at 10:01:34, without it, failed after
  0.9 s with "input file … must be contained in root directory (…/lean-luwang/)". It wrote nothing; its logs are
  kept as `logs/*attempt1*`.

## 7. Package

`tar -cf - repo evidence reference SOURCE_SHA256SUMS SharpBound.out FinalCheck.out | zstd -T16 -19`, run
10:10:16 → 10:12:32 UTC (136 s). Output went to a `.tmp` file, renamed only on success.

- **Path:** `/data/publication_staging/publication_P0r12.tar.zst`
- **sha256:** `f51c83e4c8a41945aa12603e4f2cb11eb3fa4613a4743361e2dc066fc7d1959a`
- **Size:** 314,349,777 bytes (300 MB), from about 1.87 GB uncompressed.
- **Entries:** 83,148 = 83,145 files and dirs under `repo/ evidence/ reference/` + 3 top-level files. `zstd -t` OK.

## Files

On the volume (`/data/publication_staging/`): `repo/ evidence/ reference/ SOURCE_SHA256SUMS SharpBound.out
FinalCheck.out closure_modules.txt fc_build/SharpBound.olean tools/{closure,stamps}.py logs/` and the tarball.
In git (this directory): this report, `closure_modules.txt`, `SOURCE_SHA256SUMS`, `SharpBound.out`, `FinalCheck.lean`,
`FinalCheck.out`.
