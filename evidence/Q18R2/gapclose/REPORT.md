# U-08 gap close, Stage A: fresh from-source build of the 770 cached modules behind Q18R2

aidan-of-lindisfarne, 2026-10-08, following `../../GAP_CLOSE_U08.md` (commit `32005d66`). **Only Stage A was run.**
Stage B was not started and needs the account holder's go-ahead.

## Outcome

- **Fresh build: OK.** On a clean `.lake` with no `lean-cache`, all 770 modules, plus `TangentLines` and the 30
  `P06Lines*`, were compiled from source by the kernel: 741 Lu–Wang, 16 RamseyLean, Bridge and both Definitions.
  Zero errors.
- **A4 axioms (fresh build):** both lines are `[propext, Classical.choice, Quot.sound]`.
- **A5:** 801 `.olean` files compared. **796 are byte-identical and 5 differ.**
- **The 5 differences are metadata only.** Each `.olean` embeds the absolute path of its source file, and nothing
  else differs. A declaration-level check of all 710 constants in the 5 modules (name, kind, type hash and
  proof/value hash), loaded from each tree, gives identical results.
- **Decision under `GAP_CLOSE_U08.md`:** "any DIFF" applies, so this report stops before Stage B.
  `reviews/Q18R2_source_audit.md` was **not** updated. Whether the gap counts as closed is the account holder's call
  (see "Assessment").
- **Closed, 2026-10-08:** the account holder reviewed this report and accepted it as closing the gap. Stage B was not
  run. A one-line closure note was added to `reviews/Q18R2_source_audit.md` §6.1.

## Box

- r7a.4xlarge: 16 vCPU, 123 GB RAM (`free -g`), no swap.
- `/data`: 590 G, 154 G used at the start, 436 G free.
- The box last booted about 10:35 UTC; the `/data` device is now `nvme0n1`.
- Repo HEAD at A0: `32005d66f794e2ed43db30aa25e33f7e8eb53d78`.

## Times (UTC, 2026-10-08)

| step | start | end | wall |
|---|---|---|---|
| A0 preflight and pull | 10:39:14 | 10:39:15 | 1 s |
| A1 copy (rsync without `.lake`) and manifest check | 10:39:20 | 10:39:21 | under 1 s |
| A2 `lake exe cache get` (also clones the packages) | 10:39:36 | 10:40:49 | 73 s |
| A3 `lake build Bridge Definitions` | 10:41:47 | 11:59:43 | **77 min 56 s** |
| A3 `TangentLines` | 11:59:43 | 11:59:49 | 6 s |
| A3 29 lines chunks (16 in parallel), then `P06LinesP0r12` | 11:59:49 | 12:04:05 | 4 min 16 s |
| A4 axioms | 12:04:23 | 12:04:26 | 3 s |
| A5 byte comparison | 12:04:41 | 12:04:45 | 4 s |
| A5 metadata/content check | 12:05 | 12:08 | about 3 min |

## A1: isolated copy

- `rsync -a --exclude '.lake'` copied `lean-luwang/` to `/data/gapclose/lean-luwang/`, with no `.lake` anywhere and
  no `.olean`/`.trace`/`.hash` files.
- All 30 `Bridge/P06LinesP0r12{,_0..28}.lean` match `verify/MANIFEST_P0r12.sha256`.

## A2: packages (all equal `lake-manifest.json`)

| package | revision | `.olean` files after `cache get` |
|---|---|---|
| RamseyCurrent | 5ec98f470c43be747ea638f796d1494f9b4c0177 | **0** (no `.lake` directory) |
| RamseyLean | 90e87da214701dd6eb3d56a2c7121839d8269d14 | **0** (no `.lake` directory) |
| mathlib | 520045ab14e26149ee970e2e617ca04b09bde5d6 | 8275 (Mathlib cache) |
| batteries | 023ce7d62a0531e22a5331e20b587817a80d49ff | 188 |
| aesop | a7dbf0c63b694e47f425f3dcddbc0e178bb432d3 | 132 |
| Qq | 38d591e778f100aec9762bb582f9c7f55f50e9dc | 14 |
| plausible | e12c1910fe855cbfc38803cd4e55543906d5fa62 | 13 |
| proofwidgets | 6e311e2a844da9b2cc3971187df2fe0066947b93 | 13 |
| importGraph | 7e9612bf0b9ee66db3cb5b9988a35afc706f5a12 | 10 |
| LeanSearchClient | c5d5b8fe6e5158def25cd28eb94e4141ad97c843 | 4 |
| Cli | 88679d088c9720c27ebdf2ba4dafe17341747f94 | 0 |

- `cache get` reported "No files to download". It unpacked 8,638 Mathlib-cache files from `~/.cache/mathlib` (which
  points to `/data/cache/mathlib`) into Mathlib and its own dependencies only.
- `lean-cache` and `retrace_loop.sh` were not used, and no `.olean`/`.trace`/`.hash` was copied from the original tree.

## A3: proof that nothing for Lu–Wang came prebuilt

- `build_bridge.log` has 4,183 jobs, including the cached Mathlib jobs, and ends `Build completed successfully`.
  - It contains **741** `Built RamseyCurrent.*`/`RamseyRefinement.*` lines, **16** `Built RamseyLean.*`, 14
    `Built Bridge*` and 2 `Built Definitions.*`.
  - It has **0** "up to date" or "replayed" lines and 0 error lines.
- The 288 `RamseyCurrent.SourceCertificates.Chunk*` modules took **19.2 CPU-h** in total, between 18 s and 331 s
  each (e.g. `[4042/4183] Built RamseyCurrent.SourceCertificates.Chunk0000 (148s)`). The whole `lake build` took
  78 minutes on 16 cores, matching the expected ~18 CPU-h in `SourceCertificates`.
- `TangentLines`, the 29 chunks and `P06LinesP0r12` were built with `lake env lean -o`, all with exit 0
  (`logs/A3_times.txt` on the volume).
- `build_bridge.log` here is trimmed to the first 200 lines, every error/warning line (warnings only: linter
  messages, as in Q18R2's own log), and the last 200 lines.

## A4: axioms of the freshly built inputs

```
'DiagRamsey.lu_wang_uniform_source_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DiagRamsey.lu_wang_lines_P0r12' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean --root=/data/gapclose/lean-luwang /data/gapclose/ax.lean` printed these with exit 0. Running the same
file against the original tree's `.olean` files gives the same two lines.

## A5: byte comparison (`olean_compare.tsv`)

The module set is the import closure of the 11 cached Bridge modules, `TangentLines` and the 30 lines modules. It has
**801** modules, i.e. exactly the 770 + 31 listed in `GAP_CLOSE_U08.md`: 723 `RamseyCurrent` + 18 `RamseyRefinement`
(741 Lu–Wang), 16 RamseyLean, 42 Bridge and 2 Definitions.

| group | same | DIFF |
|---|---:|---:|
| Lu–Wang `RamseyCurrent` | 723 | 0 |
| Lu–Wang `RamseyRefinement` | 15 | 3 |
| RamseyLean | 15 | 1 |
| Bridge (11 cached + `TangentLines` + 30 lines) | 41 | 1 |
| shared Definitions | 2 | 0 |
| **total** | **796** | **5** |

The 5 that differ are `Bridge.Tangent`, `RamseyLean.Numerics.Core`, `RamseyRefinement.FixedPointInterval`,
`RamseyRefinement.IntervalDerivative` and `RamseyRefinement.ShapeCertificate`.

The B0 modules are **all identical**: `Bridge.Foundations`, `Bridge.P06LinesP0r12`, `Def_DiagRamsey_Basic` and
`Def_DiagRamsey_LuWangSource`.

### Why the 5 differ: the embedded source path only

- `strings` on each pair differs in exactly one string, the absolute path of the source file:
  - `Bridge.Tangent`: fresh `/data/gapclose/lean-luwang/Bridge/Tangent.lean`, original
    `/home/ubuntu/repos/ten-thousand-agents/diagonal-ramsey/lean-luwang/Bridge/Tangent.lean`. That is the machine
    that built the `lean-cache` archive.
  - The other four: fresh `/data/gapclose/lean-luwang/.lake/packages/…`, original
    `/data/ten-thousand-agents/diagonal-ramsey/lean-luwang/.lake/packages/…`.
- The size differences (40 bytes for `Tangent`, 24–32 for the others) equal the path-length difference, up to
  8-byte alignment. The thousands of differing bytes are later offsets shifted by that string.
- The other 796 modules don't embed their path, so they came out byte-identical even though the build directory
  differs.

### Content check (`decl_compare_5modules.tsv`)

- A small meta program loaded the 5 modules in each tree. The fresh tree used `lake env`'s `LEAN_PATH`. The original
  used the same `LEAN_PATH` with the prefix replaced, a plain `lean --run` that is read-only and runs no lake.
- For each module it listed every constant: name, kind, `Expr.hash` of the type, and `Expr.hash` of the value or
  proof for every def/thm/opaque.
- Both trees give **710 constants, identical** (`sha256 7479ca23…2643` of each listing). Only 1 inductive, 1
  constructor and 1 recursor have no value to hash, and those match on type.
- This is hash-based, not a proof of byte-equal content, but it covers every declaration and every proof term.

### Which of the 5 were already compiled in Q18R2

Q18R2's own setup log (`/data/q18r2/publish/logs/verify-P0r12.log`, lines 883–963) shows four of them as
**`Built`** during Q18R2 `setup` at 18:31–18:32 UTC on 2026-10-06, which matches their `.olean` mtimes:
`RamseyRefinement.FixedPointInterval` (4.6 s), `RamseyRefinement.IntervalDerivative` (2.2 s),
`RamseyLean.Numerics.Core` (3.0 s) and `RamseyRefinement.ShapeCertificate` (37 s).

So the kernel checked those four in Q18R2 itself. Only `Bridge.Tangent`'s original `.olean`, dated 2026-10-05 from
`lean-cache`, came from the archive among the 5.

## Assessment (for the account holder)

- **For 796 of the 801 imported `.olean` files, the gap is closed**, including every module the port's stamps depend
  on. Those files are byte-identical to ones the kernel checked from source today.
- **For the 5 others:**
  - 4 were kernel-checked from source in Q18R2's own setup.
  - All 5 differ from today's fresh build only in their embedded source path.
  - All 5 declare identical constants, types and proofs. `Bridge.Tangent` is the only one whose imported bytes came
    from `lean-cache`.
- **Stage B would probably add nothing.** The port's stamps fold in only `Bridge.Foundations` and
  `Bridge.P06LinesP0r12` (`publication_extract/REPORT.md` §4); both are byte-identical here and the shared
  Definitions are identical too. So a Stage B port run on the fresh inputs would most likely skip all 82,143 modules
  as up to date. I haven't run it, per rule 4.
- The audit line was not appended. Under the file's rule it is conditional on "all identical", which is not literally
  met.

## Files

- **Here:** `REPORT.md`, `olean_compare.tsv` (801 rows), `decl_compare_5modules.tsv` (710 rows) and
  `build_bridge.log` (trimmed).
- **On the volume, `/data/gapclose/`:** the fresh `lean-luwang/` with its `.lake`, the full `build_bridge.log`,
  `ax.lean`, `logs/` (A0 preflight, A2 package and manifest revisions, A3 times and per-step logs, A4 output,
  `modlist.py`/`modlist.json`, `compare.py`) and `declcmp/` (`DeclDump.lean`, both listings, both `LEAN_PATH`s,
  `ax_orig.out`).
- Nothing under `/data/ten-thousand-agents` (apart from this folder), `/data/q18r2` or `/data/publication_staging`
  was changed. Nothing in the original `lean-luwang/.lake` has been written since 10:39 UTC.
