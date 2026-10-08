# P0 certificate of record: an exact joint-bank certificate with exponent 1.2523697 < log 3.5

hermann-joseph (P0.5 exporter / record owner), 2026-10-05, about 19:45 UTC. P0 is bruno-of-querfurt's route. The recipe
is peter-of-verona's (`reviews/P0_strict_model--hostile-audit.md` §Recommendation; handoff in
`research/peter-of-verona/NOTES.md`).

**Status.** The exact certificate passes, and the one blind hostile referee has reported:
`reviews/DiagRamsey_P0_certificate_of_record--referee.md`, **accepted with errata**, no fatal issue. Errata E1–E8
below are applied. End-to-end Lean (Verification policy 3c: turibius's `p06/v5_to_lean.py` plus the MacBook run) is
pending.

## 1. Result

| item | value |
|---|---|
| checker | `research/hildegard-of-bingen/joint_bank_certificate_v5.py` (unmodified), `verify` |
| status | **PASS_EXACT_JOINT_BANK** |
| exponent z | **626184844701/500000000000 = 1.252369689402** |
| e^z < 7/2 (`below_three_point_five`) | **True** (log 3.5 = 1.2527630; margin 3.93·10⁻⁴) |
| controls | 918, every one certified negative at 8192 cells, **none** with empty_domain |
| root | profile `QROOT` (CLOSED, p = 1/2, nodes [1, 81/80]), realized by **one `complementary_raw` piece** (red = blue = `R12_39_79`, p = 1/2 + 1/2 ≤ 1) — the realization the diagonal corollary requires; round r\* = 12 |
| model root (float) | 1.2523697894 at r\* = 12 (rounds 13–14: 1.25237000, 1.25237021) |

## 2. Files and hashes (all under `diagonal-ramsey/`)

| file | sha256 |
|---|---|
| **`research/hermann-joseph/p05/record/bank_r12_rootpair.json.gz`** (gzip -9 -n), THE bank | f18ba11260a8a2822de0ea5c0a724ae53015deeaf7e670b77de0cb854dd60fb6 |
| … uncompressed bank JSON (what v5 reads) | **bc3c24cf97cb9684b97f76ab7bf0e57775525d550a5dd1424d563900897442bc** |
| **`research/hermann-joseph/p05/record/record_r12_rootpair_merged.json`** (THE record, with interval-module provenance) | 46a50d7275981c981b1f1ba14bd2c03aad426c7902ab180ff2a3b12e8f07c87c |
| **`research/hermann-joseph/p05/record/gates_r12_rootpair.json`** (exact gates G1–G5, `p05/record_gates.py`) | 1f31acf5b1c7ad429f32d303d6601dcba783caa33d91ddb4090d10f0bca858a3 |
| superseded: `bank_r12.json.gz` / `record_r12_merged.json`; same bank, but the root C12_39_79 is realized by a `raw_density` copy (PASS, z = 1.252369889401) | 327397bd… / 925fa8b6… |
| `…/record/ctl_W4-0.jsonl` … `ctl_W4-3.jsonl` (per-control certify outputs) | d1986720… / b179e299… / c4b13299… / 949b0896… |
| `research/hildegard-of-bingen/joint_bank_certificate_v5.py` | f46f4b707a60125156fd569aab936145ccbb77c27ea50a73c1a5782176c0b783 |
| `research/hildegard-of-bingen/finite_sharp_certificate.py` | 371922b8be5fd4c4df3e465bba9decf8b4262d743860818b9ee95535737a7ca2 |
| `research/anselm-of-canterbury/sharp_control_fast_classical.py` | d4cc13ed19569e1558ed8a2966160844074f171f0359632fa3ead5ccc39c09fd |
| `research/anselm-of-canterbury/sharp_control_monotone.py` | f2017d1f74e922d3383ca48b16fa1079442197068c30aebe751c3c20ee23eb56 |
| `ref/proof/ramsey_verify/intervals.py` | 2a95901712cce1ff3330a3bd5cc5479c2b05e816cc1f5b6415d58892b4b42d88 |
| `ref/data/source.json` (Lu–Wang source; v5 checks this hash) | f3e4a4eaf3f778ae125466eb6d47647a38fd38430fdcdffe8c5f774f9718c08c |
| `ref` clone commit | 5ec98f470c43be747ea638f796d1494f9b4c0177 |
| cap table `research/bruno-of-querfurt/capx_merged.json` (peter signed off) | 633829881b146c2e52d706921044ccb34daa21b4c6bd61fba5935d7eb60281ae |

## 2½. Why the root is QROOT (fix applied before the referee)
- `statements/DiagRamsey_joint_integer_target_bank_v2.md`, Corollary (diagonal), concludes R(k,k) ≤ e^{zk} only if
  the root CLOSED profile Q (1 ∈ I_Q) is **realized at r = 1 by a `complementary_raw` (or
  `complementary_ratio_monotone`) piece**, and L_Q(1) < z.
- v5 does not check this: it requires only p_Q ≤ 1/2, 1 ∈ I_Q and z > L_Q(1). The first export's root C12_39_79 was a
  `raw_density` copy at r = 1.
- `export_v5b.py` with `ROOTPAIR=1` adds the CLOSED profile QROOT on [1, 81/80], realized by complementary_raw with
  red = blue = R12_39_79 (p = 1/2, so p_R + p_S = 1 ≤ 1). Its value at 1 is max(R(1), 1·R(1)) = R(1). The RAW part is
  extended to cover [79/80, 81/80] ⊇ {1/r : r ∈ [1, 81/80]}. No new control was needed.

## 3. How the record was produced, and what it does and does not establish

1. **Model.** bruno's `bank_model.Model.step` (sha256 78e6aa55…, `cellfeed.py` 35035df6…) is run by
   `p05/dryrun_model.py`:
   - SINGLEPAIR = 1, TERMCHK = 1, HIST = 0 (pure round bank);
   - legal round 1, leaves only from the no-call state;
   - FINE = 2, 1/80, NH = 601, LMAX = 5, CAPRED = 2e-4;
   - `CAPFIX = p05/record/capfix_final.json`, the per-control reserve from the certified ladder.

   14 rounds; r\* = 12 is the first best round.
2. **Caps.** Every control used by the model in any round (3353) is certified exactly on peter's ladder
   (`p05/cert_ladder.py`; shards W1–W3 in `P0_5_SHARDS.md`).
   - Rungs: 3345 at 1e-4, 164 at 2e-4, 119 at 5e-4, 27 at 1e-3.
   - 14 nulls, all empty-domain at p ≥ 77/80, are excluded from the model and are outside the cone.
3. **Export.** `p05/export_v5b.py N = 12` with `CAPX = p05/record/capx_final.json` exports the root's dependency cone
   (`n_notes = 0`; root-pair bank): 918 controls, 2713 sources, 1902 RAW parts, 1003 CLOSED profiles (1002 + QROOT), 304 695 route calls.
4. **Peter's conditions** (re-run on the root-pair bank: `bank_r12_rootpair_conditions.json`,
   `captable_signoff_r12_rootpair.json`, both clean).
   - (a) Every control is in `capx_merged.json` with the identical x, at cells 8192 and β = 999/1000:
     `record/bank_r12_rootpair_conditions.json` and `record/captable_signoff_r12_rootpair.json` (0 errors, no null in
     the cone).
   - (b) All 17 183 terminal ξ are strictly below their control's x.
   - (c) The root is C12 (= r\*), and the bank holds rounds 1..12 only.
5. **The run of record** (`p05/record_merge.py`, TO_CLAUDE 45 sharding):
   - the 918 control certificates are exactly the calls v5 makes (`v5_ctl_shard.py`, shards W4-0..3 by bruno, anno
     and me, each with the certify-file hashes);
   - then the **unmodified** `v5.verify` on the bank, where the only substitution is that `certify` returns the
     recorded output of the identical exact call (a missing or mismatched call raises);
   - gates: PASS, below 3.5, no empty_domain, all controls used. Wall time 283 s.
   - The record is run on the root-pair bank: PASS, z = 626184844701/500000000000, `gate_pass` true (283 s).
     The same 918 control outputs give PASS on the superseded copy-root bank too.
   - A fully unhooked serial `research/peter-of-verona/record_check.py` run of the copy-root bank (identical controls
     and identical cone, except for the root piece) started at 18:47 UTC as a cross-check. Its result will be appended
     here.
6. **Structure-only cross-check.** Earlier, the same cone (pre-CAPX export) passed the unmodified v5 with zero
   structural failures and the identical exponent (`p05/v5_struct_r10_80_N12.json`).

**What this establishes.**
- Hypotheses that v5 does **not** check, settled by `p05/record_gates.py` → `record/gates_r12_rootpair.json`, all
  passing:
  - **G1 (F ≠ ∅, referee issue 1).** For every one of the 918 controls, q = μ ∈ F exactly:
    (log p + β·A(μ)).hi < 0 = β·B(μ) in outward intervals. This replaces my earlier, invalid inference from
    "empty_domain = False": that flag only means "not certified empty".
  - **G2.** 0 < x < min(p, (1−μ)^w) with a certified margin; cells = 8192.
  - **G3 (issue 7).** Kind inventory: RAW pieces are leaf 9899 and route 7284; CLOSED pieces are raw_density 9908 and
    complementary_raw 1686; source cells are grounded_tangent 733, original_tangent 254 371 and profile pairs 1 238 773.
    There are **no** `proper_source` pieces and **no** `classical_logs` controls, so every object is of a kind covered by
    `joint_integer_target_bank_v2`. That statement names "the v5m checker"; v5 checks a superset of the kinds used
    here.
  - **G4 (issue 2).** The root QROOT is CLOSED with p = 1/2, and its piece at r = 1 is `complementary_raw`. This is the
    diagonal corollary's realization hypothesis, which v5 does not check.
  - **G5 (issue 4).** The interval arithmetic actually loaded is `ref/proof/ramsey_verify/{intervals,supports}.py`
    at BITS = 224. This is recorded in the record too (`provenance_ok`).
- **Grounded tangents (issue 5).** v5's `grounded_tangent` check, `A ≥ f̂′(t) + ε, B ≥ f̂(t) − t·f̂′(t) + ε`, compares the
  bank line with the tangent of F̂ at 1/t. It is sound by the symmetry F̂(λ) = λF̂(1/λ)
  (`DiagRamsey_lu_wang_symmetric_source_concave`). Note this is the reverse of the `original_tangent` convention,
  which uses the tangent at t.
- **Conclusion.** By the accepted theorems, a PASS together with G1–G5 gives
  **R(k, k) ≤ e^{z k} for all large k with z = 1.2523697 < log 3.5, i.e. R(k,k) < 3.5^k for all large k.**
  The theorems are:
  - `DiagRamsey_joint_integer_target_bank_v2` (diagonal corollary);
  - `DiagRamsey_source_bank_minimal_host[_routes]`;
  - `DiagRamsey_positive_weight_sharp_envelope` and `DiagRamsey_positive_weight_finite_host_closure`, which take the
    control hypotheses, F ≠ ∅ by G1;
  - the Lu–Wang source statements, including `DiagRamsey_lu_wang_symmetric_source_concave` for tails, kink cells and
    tangents.

  The control certifier's correctness rests on the accepted reviews `SHARP_CONTROL_MONOTONE` and
  `SHARP_CONTROL_FAST_CLASSICAL`.
- **Trust base.** It is computer-assisted. The trusted parts are: those natural-language theorems; v5 and its
  integer-only outward interval arithmetic; anselm's control certifier; and the Lu–Wang source data (hash checked by
  v5). **None of it is Lean-verified yet.**
- **Margins (issue 9).** The minimum source gap is 10⁻¹², and QROOT(1) equals R12_39_79(1) exactly (CLOSED pieces are
  non-strict). A Lean port must reproduce the enclosures to about 10⁻¹³.
- It does **not** prove any coupling lemma (CL). Route P0 is CL-free.

## Errata applied after the referee (reviews/DiagRamsey_P0_certificate_of_record--referee.md)
| # | referee issue | fix |
|---|---|---|
| E1 | 1 (major): F ≠ ∅ was not established | exact witness gate G1 in `record_gates.py` (q = μ for all 918); sentence replaced |
| E2 | 2: v5's root check is weaker than the corollary | gate G4 |
| E3 | 3: the record is a replay | **closed:** the referee re-ran the real `certify` on all 918 controls; all negative, none empty_domain, each bit-identical to its W4 row (report §A.5). The unhooked serial `record_check.py` cross-check is appended below when done |
| E4 | 4: interval-module provenance | gate G5; `record_merge.py` now records the loaded module path and BITS (`provenance_ok`) |
| E5 | 5: grounded-tangent convention | documented above |
| E6 | 6: trust base | cited above |
| E7 | 7: kinds, and v5 vs v5m | gate G3 inventory |
| E8 | 8: stale numbers | updated (2713 sources, 304 695 calls, 17 183 terminals; root-pair files) |

## 4. Reproduce
See `p05/FINAL_RUN.md`. In short, from `diagonal-ramsey/`:
- `gunzip -k research/hermann-joseph/p05/record/bank_r12_rootpair.json.gz`;
- `ln -s ref reference-lu-wang` (do not commit);
- either `python3 research/peter-of-verona/record_check.py <bank.json> <out.json>` (serial, about 3 h), or the W4
  shards plus `record_merge.py` (about 50 min on 16 cores).

For Lean: `python3 research/turibius-of-mogrovejo/p06/v5_to_lean.py <bank.json> R12 <outdir>`.

## 5. For P0.6 (LAPTOP_RUNBOOK step 1)
- **TAG = `P0r12`**.
- **BANK** = the uncompressed `research/hermann-joseph/p05/record/bank_r12_rootpair.json.gz`. Get it with
  `gunzip -k research/hermann-joseph/p05/record/bank_r12_rootpair.json.gz`.
  `shasum -a 256 research/hermann-joseph/p05/record/bank_r12_rootpair.json` must be
  `bc3c24cf97cb9684b97f76ab7bf0e57775525d550a5dd1424d563900897442bc`.
- Root profile **QROOT**, exponent 626184844701/500000000000, r\* = 12.
- **Per-control K/N**: `record/controls_P0r12.tsv` (918 rows, name-keyed; exact p, μ, w, β, x copied verbatim from the
  bank). K = 8192 is the cell count at which v5's certify passed each control; N = 201 is isidore's default.
  `p06_controls.py` regenerates the indexed list from `Bank.lean`; this file is the cross-check of the rationals.

## 6. Unhooked serial cross-check (appended 21:47 UTC)
`research/peter-of-verona/record_check.py` is the **unmodified v5 with real `certify` on every control and no
substitution at all**. It was run on the copy-root bank `bank_r12.json.gz` (JSON sha256 52d2e683…2115e). That bank
has the same 918 controls and the same cone as the record bank; only the root is a raw_density copy.
- Result: `PASS_EXACT_JOINT_BANK`, exponent 1252369889401/10¹², below_three_point_five = True, gate_pass = True, no
  empty_domain control.
- Wall time: 10 781 s (3.0 h serial). ref commit 5ec98f47.
- Output: `record/record_check_serial_copyroot.json` (sha256 c76ca8babba3c827b85ed744d99421e2e085275f206d1e7a4f3c7a673b12a15f).

Together with the referee's full real re-certification (§E3), every control outcome in the record has now been
produced by a real `certify` call twice, independently of the W4 replay.
