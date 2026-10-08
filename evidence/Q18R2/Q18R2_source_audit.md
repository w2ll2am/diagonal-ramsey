# Q18R2 source audit: kernel bypasses and trust outside the kernel

**Subject:** the checked closure of `DiagRamsey.diagonal_le_three_point_five_pow` (`R(k,k) ≤ 3.5^k`), as compiled by
run Q18R2 (2026-10-06, `nodes/aidan-of-lindisfarne/results/Q18R2.md`, PASS, `#print axioms` =
`[propext, Classical.choice, Quot.sound]`).
**Question:** does any source in that closure bypass or weaken the kernel check, or add trust outside the kernel, in
a way `#print axioms` cannot see?
**Auditor / date:** Claude (subagent session), 2026-10-08.

## Verdict

**No problem found at the source level.** Every source compiled by the Q18R2 port, and every source of the
pre-built oleans it imports from `lean-luwang/`, was scanned (82,945 files, 1.84 GB, 5.48 M lines).

- There is no `debug.*` option, `set_option trust`, `unsafe`, `implemented_by`, `@[extern]`, `opaque`,
  `native_decide`, `Lean.ofReduceBool`/`ofReduceNat`, `Lean.trustCompiler`, `axiom`, `sorry`/`admit`/`sorryAx` (in code),
  `@[csimp]`, `prelude`/`noImplicitPrelude`, `initialize`, `run_cmd`/`run_elab`/`#eval`, `macro`, `syntax`, or
  `import Lean` anywhere in the closure.
- There is exactly one piece of metaprogramming: the `kernel_rfl` tactic in `lean-luwang/Bridge/KernelRfl.lean:33`.
  It is harmless (see §4).
- The only `set_option`s are resource limits and linters (`maxRecDepth`, `maxHeartbeats`, `Elab.async`,
  `autoImplicit`, `linter.*`). None of them affects what the kernel accepts.
- The port's source changes are exactly its 5 proof-only shims, import rewiring (`Theorems.*` stub →
  `Solutions.*` / `Bridge.*`), and the renaming of 25 `theorem solution` wrappers. No definition or statement text
  changes. The compiled `Definitions/` are byte-identical to `lean/Definitions/`, and the statement text equals
  `lean/Theorems/Thm_DiagRamsey_diagonal_le_three_point_five_pow.lean`.

**One residual trust gap (not a source problem, see §6.1):** 770 modules of the closure were not compiled in Q18R2. They
are the Lu–Wang development (757 modules), 11 `lean-luwang/Bridge/*` modules including `Bridge.Foundations`, and the
two shared `Definitions`. Their `.olean`s came from `verify.sh setup`. On a fresh box, setup restores them from the
`lean-cache` branch archives, which other agents built on 2026-10-05, and retraces them instead of rebuilding them.
Lean does not re-check imported oleans. These modules were kernel-checked when they were built, but not in Q18R2.
Their sources are clean (§5).

## 1. What Q18R2 compiled

Code commit `7b13125338abda4dfaa24befe39b0c7c1aef5eeb`. The audit ran on `origin/main` = `90cbd948`, which differs from
`7b131253` only in `nodes/aidan-of-lindisfarne/*` and `verify/AWS.md` (`git diff --stat 7b131253 HEAD -- lean lean-luwang verify research`:
only AWS.md), so every compiled source and generator is identical.

`MODE=single`: `verify.sh` steps `setup gen manifest lines port`. `port` runs `verify/port_mem.py` → `verify/port_full_p0.py`
→ `lean-luwang/port_full.py` under Lean **4.32.1** (`lean-luwang/lean-toolchain`) with **Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`** (`lean-luwang/lake-manifest.json`, inherited from Lu–Wang). The `lean/`
tree's Mathlib (`0df444a3…`, Lean 4.33.1) is used only by `setup`/`lines` and is not in the checked closure.
`port_full.run` copies `lean/{Definitions,Theorems,Solutions,Lemmas}` into `lean-luwang/.lake/portfullp0_P0r12/`, applies
its patches, rewires imports, and builds the import closure of `Solutions.Sol_DiagRamsey_diagonal_le_three_point_five_pow`
with `lean -o` (LEAN_PATH = port build dir first, then `lake env`'s path). There are no `-D`/`--trust` flags, no `LEAN_OPTS`,
and no `leanOptions` other than `autoImplicit = false` in any lakefile in play.

**Exact module list.** I ran the real `port_mem.py → port_full_p0.py → port_full.py` code with `subprocess.run` replaced
by a stub that returns success. It does no Lean work, so it reproduces the exact post-patch tree and the exact `lean`
command list (script `fakeport.py`, §8). Its output matches Q18R2's log:
`82143 lean/ modules in the closure`, `Theorems.* modules left in the closure: none`, `statement text MATCH`,
`resume: 0 modules up to date`. It issued 82,175 `lean` commands: 82,143 port modules, 31 bridge-line modules
(`Bridge/TangentLines` and the 30 `P06LinesP0r12*`, built by `port_full_p0.py`'s pre-step), and `Composite.lean`.

### Inventory of the checked closure (82,944 modules + `Composite.lean`)

| part | files | origin | compiled in Q18R2? |
|---|---:|---|---|
| CERT controls `Solutions/SharpCertFast/P06P0r12c{0..917}/*` | 80,567 | generated (`gen_fast.py` + `gen_kernel.py`) | yes (port) |
| bank `Solutions/P06/P0r12/*.lean` (T, TD*, D*, Raw*, Closed*, Src*, Data, Bank, CertLink, Final) | 1,519 | generated (`v5_to_lean.py`) | yes (port) |
| `Solutions/Sol_DiagRamsey_diagonal_le_three_point_five_pow.lean` | 1 | generated (`v5_to_lean.py`) | yes (port) |
| tangent lines `lean-luwang/Bridge/P06LinesP0r12{,_0..28}.lean` | 30 | generated (`lw_lines.py`) | yes (port pre-step; also `lines`) |
| `Definitions/Def_DiagRamsey_{Cert,JointBank,JointBank2,NestedMoment,SourceBank,WeightedHost}` | 6 | hand | yes (port) |
| `Lemmas/DiagRamsey_*` (V5*, PL, PLCheck, JB_*, SB_*, SE_*, closure_*, balanced_cut, retained_route, sharp_envelope, diagonal_wrapper) | 38 | hand | yes (port) |
| `Solutions/SharpCert/{Checker,Exp,Gen,GenChain,Integral}` | 5 | hand | yes (port) |
| `Solutions/SharpCertFast/{BlockI,CertAny,CheckerI,IExp}` | 4 | hand | yes (port) |
| `Solutions/Sol_DiagRamsey_{majority_colour_balanced_cut,positive_weight_finite_host_closure,weighted_host_lower_bound}` | 3 | hand | yes (port) |
| `lean-luwang/Bridge/TangentLines` | 1 | hand | yes (port pre-step) |
| `Composite.lean` (written by `port_full.run`) | 1 | port | yes |
| `lean-luwang/Definitions/Def_DiagRamsey_{Basic,LuWangSource}` (sha256-equal to `lean/Definitions`, checked by `port_full.run`) | 2 | hand | **no**: olean from `setup` |
| `lean-luwang/Bridge/{Foundations,Tangent,Source,Concave,Arrows,Data,DataKnots,DataValues,DataDerivs,ParseRat,KernelRfl}` | 11 | hand | **no**: olean from `setup` (`lean-cache` Bridge-pre / Bridge-rest) |
| Lu–Wang `sichen-wang/diagonal-ramsey-numbers@5ec98f47` `lean/src` (`RamseyCurrent.*`, `RamseyRefinement.*`) | 741 | external | **no**: olean from `setup` (`lean-cache`) |
| `snorin239/RamseyLean@90e87da2` | 16 | external | **no**: olean from `setup` |
| Mathlib / Batteries / Std (73 distinct imports at the boundary) | — | trusted, out of scope | no (`lake exe cache get`) |

`Theorems/*` is **not** in the closure: every stub import is rewired. `lean/Theorems/Thm_DiagRamsey_lu_wang_lines_P0r12.lean`
(generated, `sorry`) is replaced by `Bridge.P06LinesP0r12`.

Generators in scope: `research/turibius-of-mogrovejo/p06/v5_to_lean.py` (526 lines), `…/p06/lw_lines.py` (182),
`research/isidore-the-farmer/p06/gen_fast.py` (97), `lean/Solutions/SharpCert/gen_kernel.py` (232) and its helper
`generate.py` (`lq`, `GLOB_FIELDS`), and the K table `research/coordinator/p06k/kfix_P0r12.tsv`. Port patches:
`lean-luwang/port_full.py` `PATCHES`, `verify/port_full_p0.py` (`EXTRA_PATCHES = []`, P06 import rewiring).

## 2. Generated files: full regeneration, manifest OK

I regenerated **all** generated sources and checked them against the published manifest:

```
cd diagonal-ramsey && TAG=P0r12 J=4 STEPS="gen manifest" ./verify/verify.sh
[2026-10-08T10:09:44Z] gen done: bank Lean + 918 controls
[2026-10-08T10:09:48Z] manifest OK (82122 files)
real 126m33s   (4 vCPU / 15 GB; v5_to_lean ≈ 7 min, 918 controls at J=4 ≈ 119 min)
```

- `gen` needs the pinned Lu–Wang repository at `lean-luwang/.lake/packages/RamseyCurrent` and at `ref/`, which `setup` normally
  creates. I did not run `setup`. Instead I cloned `https://github.com/sichen-wang/diagonal-ramsey-numbers` at
  `5ec98f470c43be747ea638f796d1494f9b4c0177` and symlinked it into both places. `data/source.json` sha256 =
  `f3e4a4ea…9718c08c`, the value `verify.sh setup` asserts.
- Python packages: `pip install mpmath numpy` (mpmath 1.4.1, numpy 2.4.6), Python 3.11.15.
- The 82,122 manifest entries are 80,567 CERT files + 1,519 bank `.lean` + 3 bank `.tsv` + 30 lines + Sol + Theorems
  lines stub + the gunzipped bank JSON. The set of untracked files the generators wrote equals the manifest file set exactly,
  in both directions. So no generated file outside the manifest reaches the port.

I also read the four generators' templates in full. Every emitted string is a fixed template. The interpolated parts
are rationals or integers (`Lq`, `lq`, `_q`, `str(int)`), indices, and names built from the tag
(`P06P0r12`, `P06P0r12c<i>`). The bank file name also appears inside one doc comment. The templates emit only
`import`, `namespace`/`open`/`end`, `noncomputable section`, `set_option maxRecDepth 100000`,
`set_option maxHeartbeats 0`, `def`, and `theorem … := by decide +kernel` / `simp only` / `rw` / `exact` /
`first | exact … | exact …` / `norm_num` / `push_cast` / `linarith`. They emit no `native_decide`, no metaprogramming and no options beyond
those two. The only `sorry` they can emit is in `lw_lines.stub` (the `lean/Theorems` lines stub, not compiled by the port).

## 3. Commands run

```bash
git fetch -q origin main && git checkout -q --detach origin/main            # 90cbd948
git diff --stat 7b13125338abda4dfaa24befe39b0c7c1aef5eeb HEAD -- diagonal-ramsey/{lean,lean-luwang,verify,research}
git clone https://github.com/sichen-wang/diagonal-ramsey-numbers  (checkout 5ec98f47…); git clone https://github.com/snorin239/RamseyLean (checkout 90e87da2…)
ln -s <clone> diagonal-ramsey/ref; ln -s <clone> diagonal-ramsey/lean-luwang/.lake/packages/RamseyCurrent
pip install mpmath numpy
TAG=P0r12 J=4 STEPS="gen manifest" ./verify/verify.sh                       # §2
(lean-luwang) python3 fakeport.py P0r12   # real port code, subprocess.run stubbed; writes .lake/portfullp0_P0r12 + command list
diff -rq lean/{Definitions,Theorems,Solutions,Lemmas} lean-luwang/.lake/portfullp0_P0r12/…   # §4 port changes
python3 closure.py …  Solutions.Sol_DiagRamsey_diagonal_le_three_point_five_pow             # import closure: 82,944 local modules
python3 scan.py all_scan.txt all_hits.tsv                                    # pattern scan of all 82,945 files (13.5 min)
git fetch --depth 1 origin lean-cache; git show FETCH_HEAD:{README.md,luwang-5ec98f47/{STATUS.md,retrace.py,retrace_loop.sh,restore.sh}}
```

`scan.py` greps each file for the patterns below and marks each hit as code or comment. Comment detection uses nested
`/- -/` and `--` tokens. Every code hit and every comment hit was then read by hand. Patterns: `debug\.`, `set_option`,
`trust|trustCompiler`, `unsafe`, `implemented_by`, `extern`, `opaque`,
`native_decide|nativeDecide|ofReduceBool|ofReduceNat|reduceBool|reduceNat`, `axiom`, `sorry|admit|sorryAx`,
`elab|elab_rules|simproc|dsimproc`, `macro|macro_rules`, `syntax|declare_syntax_cat`, `notation|infix[lr]?|prefix|postfix`,
`initialize|builtin_initialize`, `run_cmd|run_elab|run_meta|#eval|#exit|#guard_msgs|#reduce`,
`addDecl|addAndCompile|modifyEnv|setEnv|Environment|Kernel\.|Lean\.Elab|Lean\.Meta|MetaM|TacticM|CommandElabM|TermElabM|CoreM`,
`^import Lean`, `open (scoped )?Lean`, `csimp`, `^prelude|noImplicitPrelude`, `register_*attr|register_option|initialize_`,
`instance`, `^export`, `priority :=`, `partial def`, `@[…]` other than `@[simp]`, `^attribute [`,
`namespace (Nat|Int|Rat|Real|Lean|Mathlib|Decidable|Bool|List|Array|Std)`.

## 4. Results per pattern (whole closure, 82,945 files)

| pattern | code hits | comment hits | verdict |
|---|---:|---:|---|
| `debug.*` (incl. `debug.skipKernelTC`), `set_option trust` | 0 | 0 | — |
| `unsafe`, `implemented_by`, `@[extern]`, `opaque`, `partial def` | 0 | 0 | — |
| `native_decide`, `ofReduceBool`/`ofReduceNat`, `reduceBool`/`reduceNat`, `trustCompiler` | 0 | 1 (`trust`) | comment only: `RamseyLean/Analysis/CertifiedNumerics.lean:15` ("they do not encode or trust …") |
| `axiom` | 0 | 0 | — |
| `sorry` / `admit` / `sorryAx` | 0 | 3 | comments only: `Lemmas/DiagRamsey_closure_nbgp.lean:8`, `Lemmas/DiagRamsey_closure_wgp.lean:8` ("verified, no sorryAx"), Lu–Wang `RamseyRefinement/IntervalNormalizedDerivative.lean:4` ("also admit exact differentiation") |
| `elab` / `open Lean` | 1 + 1 | 0 | `lean-luwang/Bridge/KernelRfl.lean:31,33`, **harmless**, see below |
| `macro`, `syntax`, `initialize`, `run_cmd`/`run_elab`/`#eval`/`#exit`, `addDecl`/`Environment`/`MetaM`… | 0 | 0 | — |
| `import Lean*` | 0 | 0 | — |
| `@[csimp]`, `prelude`/`noImplicitPrelude`, attribute registration, `attribute […]` command, `export` | 0 | 0 | — |
| attributes other than `@[simp]` | 0 | — | only `@[simp]` occurs (2 hand-written, 59 Lu–Wang) |
| `namespace` of a core/Mathlib root | 0 | — | — |
| `notation` | 2 | 4 | `local notation "F" => certIntegrand …` in `Solutions/SharpCert/Integral.lean:101` and `Solutions/SharpCertFast/CertAny.lean:96`: **harmless**, local to its section, abbreviates a project definition, cannot reach the statement. 4 comment-only hits |
| `instance` | 1 | 2 | `Lemmas/DiagRamsey_balanced_cut.lean:38` `instance … : DecidablePred (Separates m σ) := by …`: **harmless**, a proved `Decidable` instance for a project predicate. It does not touch `ℝ`/`ℕ`/`LE`/`HPow`/`OfNat`, so it cannot change the meaning of the statement |
| `priority :=` | 0 | — | — |
| `set_option` | 85,482 | — | all **harmless** resource limits or linters (below) |

`set_option` breakdown:

| option | generated CERT | generated bank / lines / Sol | hand (lean + Bridge) | Lu–Wang + RamseyLean |
|---|---:|---:|---:|---:|
| `maxRecDepth` (100000; 23× 1000000; 1× 20000) | 80,567 | 1,549 | 8 | 673 |
| `maxHeartbeats` (0, or 800000 … 8000000) | 0 | 1,548 | 9 | 675 |
| `Elab.async false` | — | — | — | 360 |
| `autoImplicit false` | — | — | — | 87 |
| `linter.unusedVariables` / `linter.unusedSectionVars` false | — | — | 2 / 4 | — |

These options limit or schedule elaboration. None of them changes what the kernel accepts.

**`kernel_rfl` (`lean-luwang/Bridge/KernelRfl.lean:31–37`).** `elab "kernel_rfl" : tactic` takes a goal `a = b` and assigns
it `Eq.refl a` (`mkEqRefl a`) without the elaborator's defeq check. The definitional equality is then checked by the kernel
when the declaration is added, as with `decide +kernel`, so a false goal is a kernel error. It adds nothing to the
environment and calls no `addDecl`/`ofReduceBool`. It strengthens reliance on the kernel; it does not weaken it.
It is used in `Bridge/Data{,Knots,Values,Derivs}.lean`.

**Port source changes** (`diff -r lean/… portfullp0_P0r12/…`: 36 files differ, 111 changed lines):
- 5 `PATCHES` from `port_full.py`, all proof-only:
  - `Solutions/SharpCert/Checker.lean:179–180`: `exact_mod_cast of_decide_eq_true hK{1,2}` → `exact_mod_cast hK{1,2}`.
  - `Lemmas/DiagRamsey_balanced_cut.lean:178,210`: `rfl` → `rfl, rfl`.
  - `Lemmas/DiagRamsey_route_diagonal.lean:27`: `set_option maxHeartbeats 1000000 in` before `theorem route_diagonal`.
    That file is not in this theorem's closure.
- `verify/port_full_p0.py` adds no patches (`EXTRA_PATCHES = []`). Its rewiring changes one line:
  `Solutions/P06/P0r12/Final.lean`: `import Theorems.Thm_DiagRamsey_lu_wang_lines_P0r12` → `import Bridge.P06LinesP0r12`.
- Import rewiring in `Sol_*` and `Lemmas`: 27 `import Theorems.*` lines removed. They are replaced by `Solutions.Sol_*` (17),
  `Bridge.Foundations` (5), `Bridge.Tangent`, `Bridge.Tangent3p5` (duplicates dropped).
- Renaming of `theorem solution` → `theorem solution_<X>` in 25 `Sol_*` files.
- No other line differs. `Definitions/` and every statement are unchanged.

**Statement and definitions.** The compiled `Sol_DiagRamsey_diagonal_le_three_point_five_pow.lean` states
`∃ K : ℕ, ∀ k : ℕ, K ≤ k → (ramseyNumber k k : ℝ) ≤ (7 / 2 : ℝ) ^ k` in `namespace DiagRamsey`, textually equal to
`lean/Theorems/…`. `Composite.lean` re-elaborates the Theorems text against it.

`ramseyNumber` resolves to `DiagRamsey.ramseyNumber` (`Def_DiagRamsey_Basic.lean:19`, `sInf {N | RamseyArrows k l N}`), the
reviewed definition. The other `ramseyNumber` in the closure is `RamseyLean.ramseyNumber` (`RamseyLean/Ramsey.lean:178`). It is
namespaced and not opened by `Sol`, `Final` or `Composite`, so it is not a candidate.

No instance in the closure targets `ℝ`, `ℕ`, `LE`, `HPow`, `HDiv` or `OfNat`, so the statement's notation has its
Mathlib meaning. The port's `Definitions/` copy is byte-identical to `lean/Definitions/`. The two shared definitions were
compiled in `lean-luwang/` from files with the same sha256 (`66a13f99…`, `832f61f3…`), which `port_full.run` checks.

## 5. Hand-written, Lu–Wang and RamseyLean sources

These were scanned with the same patterns (included in the table above). Every hit is listed there. The Lu–Wang closure
has 741 modules and 506k lines. It contains no `native_decide`, `axiom`, `sorry`, `unsafe`, `implemented_by`,
`extern`, `opaque`, `macro`/`syntax`/`elab`, `instance` override or `import Lean`. Its numerical evidence uses
`decide`/`decide +kernel`. Sources: `diagonal-ramsey-numbers@5ec98f470c43be747ea638f796d1494f9b4c0177` (`lean/src`),
`RamseyLean@90e87da214701dd6eb3d56a2c7121839d8269d14`, the revisions in `lean-luwang/lake-manifest.json`.

## 6. Residual gaps

1. **Pre-built oleans not re-checked in Q18R2.**
   - `verify.sh setup` (`verify.sh:82–92`) runs `lake build --no-build Bridge.Tangent`. On a fresh volume that fails,
     so setup extracts the `lean-cache` archives `luwang-5ec98f47/chunks/*` (SourceCertificates and Links chunks,
     `Bridge-pre`, `Bridge-rest`) and runs `retrace_loop.sh`. That script rewrites lake traces so the archived oleans count
     as up to date. Only modules in no archive are built for real.
   - Q18R_lessons.md:44 confirms that setup on this box used "the Lu–Wang build from a shallow `lean-cache` clone".
     Setup took 5 m 23 s, far less than a Lu–Wang rebuild.
   - So the 770 imported modules in §1 (Lu–Wang, RamseyLean, 11 `Bridge.*` including `Bridge.Foundations`, which supplies
     `lu_wang_uniform_source_bound`) were kernel-checked by the agents who built the archives on 2026-10-05, not in Q18R2.
     Lean loads `.olean` declarations without re-checking them, and `#print axioms` reads whatever the olean says.
   - `retrace.py` rewrites a trace only when the source hash, the Lean version hash and the import-artifact hash agree.
     So the archived oleans claim these exact sources. The olean bytes themselves are trusted.
   - The lean-cache README says "U-08 (the clean rebuild) removes the trust in these archives". QUEUE Q7, the U-08 clean
     rebuild without lean-cache, is marked "not needed".
   - **Remedy:** run `setup` with an empty `.lake` and without `lean-cache` (build `Bridge` from source), then rerun the
     port. Or rebuild `Bridge` from source on the existing volume and compare the oleans with the archives.
   - **Closed by U-08 gap close (results/gapclose/REPORT.md)**, 2026-10-08: all 770 modules were rebuilt from source without `lean-cache`; 796/801 oleans are byte-identical, and the other 5 differ only in their embedded source-file path, with all 710 of their declarations (types and proofs) identical. The account holder accepted this as closing the gap.
2. **Mathlib/Batteries/Std oleans** come from `lake exe cache get` (Mathlib `520045ab…`). They are out of scope and trusted, as instructed.
3. **Method limits.**
   - This is a static source audit. I did not re-run Lean, so the olean of each module was not compared with its source.
     Q18R2's `BUILD_SHA256SUMS` exists only on the build volume.
   - The pattern scan is lexical. Identifiers that spell a pattern differently (e.g. through a `notation`/`macro` defined
     elsewhere) would be missed. But the closure defines no macro or syntax, and the only notations are the two
     `local notation "F"`.
   - The audit trusts that Q18R2 ran this code at `7b131253`. Its log line `commit=5d078f4b`, explained in Q18R2.md as a
     notes-only commit, was not independently checked.
4. **Composite check scope.** `Composite.lean` elaborates the Theorems text in an environment that imports the top module.
   That is sound here because no imported module redefines notation or instances (§4).

## 7. Files and reproducibility

- Generated sources were regenerated byte-identically (manifest OK), scanned, and then deleted. The port tree copy and the
  local clones/symlinks were also deleted. Only this report is committed.
- Audit scripts (session scratch, not committed): `scan.py` (pattern scanner), `closure.py` (import closure over the
  port tree, `lean-luwang/Bridge`, Lu–Wang, RamseyLean), `fakeport.py` (the real port code with `subprocess.run` stubbed).
