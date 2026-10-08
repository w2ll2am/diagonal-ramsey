import Lemmas.DiagRamsey_V5Bank
import Lemmas.DiagRamsey_JB_Main
import Lemmas.DiagRamsey_JB_Diagonal

/-!
# v5 banks in Lean (P0.6): the whole bank

A finite bank `BankD` (sources, controls, RAW and CLOSED profiles with their pieces, SOURCE covers, tangent lines)
and one Boolean check `BankD.check` mirroring `joint_bank_certificate_v5m.verify` for the kinds `export_v5.py`
emits. `BankD.sound` turns a passing check, the CERT facts of the controls and the tangent lines of the Lu–Wang
symmetric source into the conclusion of `joint_integer_target_bank_v2` (via `joint_main_v2`); `BankD.diagonal` adds
the root profile and gives `R(k, k) ≤ e^{z k}` eventually.

Grounded SOURCE cells and the two tails of each source are discharged by global lines `F̂(s) ≤ c + d s`
(`LineOK c d`), listed once in `BankD.lines`. These are the tangent lines v5m evaluates by interval arithmetic
(`grounded_tangent`, `original_tangent`, the left/right tails); they are hypotheses here.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.V5

open DiagRamsey.PL DiagRamsey.SharpCert

/-! ## Covers by consecutive intervals -/

/-- `ps` are consecutive intervals from `a` to `b`: `p₀.lo = a`, `pⱼ.hi = pⱼ₊₁.lo`, last `hi = b`. -/
def chainQ : ℚ → List (ℚ × ℚ) → ℚ → Bool
  | a, [p], b => decide (p.1 = a) && decide (p.2 = b)
  | a, p :: q :: rest, b => decide (p.1 = a) && chainQ p.2 (q :: rest) b
  | _, [], _ => false

lemma chain_cover : ∀ (ps : List (ℚ × ℚ)) (a b : ℚ), chainQ a ps b = true →
    ∀ r : ℝ, (a : ℝ) ≤ r → r ≤ b → ∃ p ∈ ps, (p.1 : ℝ) ≤ r ∧ r ≤ p.2
  | [p], a, b, h, r, h1, h2 => by
      simp only [chainQ, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, by simp, by rw [h.1]; exact h1, by rw [h.2]; exact h2⟩
  | p :: q :: rest, a, b, h, r, h1, h2 => by
      simp only [chainQ, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hr : r ≤ p.2
      · exact ⟨p, by simp, by rw [h.1]; exact h1, hr⟩
      · obtain ⟨x, hx, hx1, hx2⟩ := chain_cover (q :: rest) p.2 b h.2 r (le_of_lt (not_le.mp hr)) h2
        exact ⟨x, List.mem_cons_of_mem _ hx, hx1, hx2⟩
  | [], _, _, h, _, _, _ => by simp [chainQ] at h

lemma chain_cover_fin {α : Type} (l : List α) (f : α → ℚ × ℚ) (a b : ℚ) (h : chainQ a (l.map f) b = true)
    (r : ℝ) (h1 : (a : ℝ) ≤ r) (h2 : r ≤ b) : ∃ J : Fin l.length, ((f (l.get J)).1 : ℝ) ≤ r ∧ r ≤ (f (l.get J)).2 := by
  obtain ⟨p, hp, hp1, hp2⟩ := chain_cover _ a b h r h1 h2
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  obtain ⟨J, rfl⟩ := List.get_of_mem hx
  exact ⟨J, hp1, hp2⟩

lemma all_finRange {n : ℕ} {f : Fin n → Bool} (h : (List.finRange n).all f = true) (i : Fin n) : f i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

lemma affine_nonneg {u v lo hi t : ℝ} (h1 : lo ≤ t) (h2 : t ≤ hi) (hlo : 0 ≤ u + v * lo) (hhi : 0 ≤ u + v * hi) :
    0 ≤ u + v * t := by
  rcases le_total 0 v with hv | hv
  · nlinarith [mul_le_mul_of_nonneg_left h1 hv]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hv]

/-! ## RAW pieces -/

inductive RawD (ι : Type) (nCtl m : ℕ)
  | leaf (L : LeafD nCtl m)
  | route (R : RouteD ι nCtl m)

variable {ι : Type} {nCtl m : ℕ}

def RawD.lo : RawD ι nCtl m → ℚ
  | .leaf L => L.lo
  | .route R => R.lo

def RawD.hi : RawD ι nCtl m → ℚ
  | .leaf L => L.hi
  | .route R => R.hi

def RawD.margin : RawD ι nCtl m → ℚ
  | .leaf L => L.margin
  | .route R => R.margin

noncomputable def RawD.toPiece (ctl : Fin nCtl → CtrlD) (B : Fin m → ℚ) (i0 : ι) : RawD ι nCtl m → RawPiece ι m
  | .leaf L => .leaf (L.ctrl ctl B)
  | .route R => .route (R.toPiece ctl B i0)

def RawD.check (ctl : Fin nCtl → CtrlD) (A B : Fin m → ℚ) (pd : ι → ProfD) (i0 : ι) (P : ProfD) :
    RawD ι nCtl m → Bool
  | .leaf L => L.check ctl A B P
  | .route R => R.check ctl A B pd i0 P

lemma RawD.valid_of_check (ctl : Fin nCtl → CtrlD) (hcert : ∀ c, (ctl c).CertOK) (A B : Fin m → ℚ)
    (pd : ι → ProfD) (prof : ι → BankProfile) (hprof : ∀ i, prof i = (pd i).toBP) (i0 : ι) (P : ProfD)
    (x : RawD ι nCtl m) (h : x.check ctl A B pd i0 P = true) :
    0 < (x.margin : ℝ) ∧ (x.toPiece ctl B i0).Valid' (fun i => (A i : ℝ)) (fun i => (B i : ℝ)) prof P.toBP
      x.lo x.hi x.margin := by
  cases x with
  | leaf L => exact LeafD.valid_of_check ctl hcert A B prof P L h
  | route R => exact RouteD.valid_of_check ctl hcert A B pd prof hprof i0 P R h

/-! ## SOURCE covers -/

/-- A global line above the symmetric Lu–Wang source: `F̂(s) ≤ c + d s` for all `s > 0`. -/
def LineOK (c d : ℚ) : Prop :=
  ∀ s : ℝ, 0 < s → symmetricProfile luWangSource 1 s ≤ (c : ℝ) + d * s

/-- `c + d x ≤ A + B x - η (1 + x)`. -/
def lineLeQ (c d A B η x : ℚ) : Bool := decide (c + d * x ≤ A + B * x - η * (1 + x))

lemma line_le_on {c d A B η lo hi : ℚ} (h1 : lineLeQ c d A B η lo = true) (h2 : lineLeQ c d A B η hi = true)
    (t : ℝ) (ht1 : (lo : ℝ) ≤ t) (ht2 : t ≤ hi) : (c : ℝ) + d * t ≤ A + B * t - η * (1 + t) := by
  simp only [lineLeQ, decide_eq_true_eq] at h1 h2
  have h1' : (c : ℝ) + d * lo ≤ A + B * lo - η * (1 + lo) := by exact_mod_cast h1
  have h2' : (c : ℝ) + d * hi ≤ A + B * hi - η * (1 + hi) := by exact_mod_cast h2
  have := affine_nonneg (u := (A : ℝ) - η - c) (v := (B : ℝ) - η - d) ht1 ht2 (by linarith) (by linarith)
  linarith

inductive SrcCellD (ι : Type)
  | grounded (k : ℕ) (lo hi : ℚ)
  | pair (PR PB : ι) (lo hi : ℚ) (bp : List ℚ)

def SrcCellD.lo : SrcCellD ι → ℚ
  | .grounded _ lo _ => lo
  | .pair _ _ lo _ _ => lo

def SrcCellD.hi : SrcCellD ι → ℚ
  | .grounded _ _ hi => hi
  | .pair _ _ _ hi _ => hi

def SrcCellD.toCell : SrcCellD ι → SourceCell ι
  | .grounded _ _ _ => .grounded
  | .pair PR PB _ _ _ => .pair PR PB

def SrcCellD.check (pd : ι → ProfD) (lines : List (ℚ × ℚ)) (A B η : ℚ) : SrcCellD ι → Bool
  | .grounded k lo hi => decide (k < lines.length) &&
      lineLeQ (lines.getD k 0).1 (lines.getD k 0).2 A B η lo && lineLeQ (lines.getD k 0).1 (lines.getD k 0).2 A B η hi
  | .pair PR PB lo hi bp => sourcePairCheck (pd PR) (pd PB) A B η lo hi bp

lemma lineOK_getD {lines : List (ℚ × ℚ)} (hl : ∀ p ∈ lines, LineOK p.1 p.2) {k : ℕ} (hk : k < lines.length) :
    LineOK (lines.getD k 0).1 (lines.getD k 0).2 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hl _ (List.getElem_mem hk)

lemma SrcCellD.valid_of_check (pd : ι → ProfD) (prof : ι → BankProfile) (hprof : ∀ i, prof i = (pd i).toBP)
    (lines : List (ℚ × ℚ)) (hl : ∀ p ∈ lines, LineOK p.1 p.2) (A B η : ℚ) (x : SrcCellD ι)
    (h : x.check pd lines A B η = true) : x.toCell.Valid prof A B η x.lo x.hi := by
  cases x with
  | grounded k lo hi =>
    simp only [SrcCellD.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, h1⟩, h2⟩ := h
    intro t ht h1' h2'
    exact (lineOK_getD hl hk t ht).trans (line_le_on h1 h2 t h1' h2')
  | pair PR PB lo hi bp => exact sourcePair_valid prof PR PB (pd PR) (pd PB) (hprof PR) (hprof PB) A B η lo hi bp h

/-- One source: cover `[Lo, Hi]` by cells, tails `t ≤ Lo` / `t ≥ Hi` by the lines `kL`, `kR` with slack `ε`. -/
structure SourceD (ι : Type) where
  Lo : ℚ
  Hi : ℚ
  ε : ℚ
  η : ℚ
  kL : ℕ
  kR : ℕ
  cells : List (SrcCellD ι)

def SourceD.check (pd : ι → ProfD) (lines : List (ℚ × ℚ)) (A B : ℚ) (S : SourceD ι) : Bool :=
  decide (0 < S.Lo) && decide (S.Lo < S.Hi) && decide (0 < S.ε) && decide (0 < S.η) &&
    decide (S.kL < lines.length) && decide (S.kR < lines.length) &&
    lineLeQ (lines.getD S.kL 0).1 (lines.getD S.kL 0).2 A B S.ε 0 &&
    lineLeQ (lines.getD S.kL 0).1 (lines.getD S.kL 0).2 A B S.ε S.Lo &&
    lineLeQ (lines.getD S.kR 0).1 (lines.getD S.kR 0).2 A B S.ε S.Hi &&
    decide ((lines.getD S.kR 0).2 ≤ B - S.ε) &&
    chainQ S.Lo (S.cells.map (fun c => (c.lo, c.hi))) S.Hi && S.cells.all (SrcCellD.check pd lines A B S.η)

lemma SourceD.tail (lines : List (ℚ × ℚ)) (hl : ∀ p ∈ lines, LineOK p.1 p.2) (pd : ι → ProfD) (A B : ℚ)
    (S : SourceD ι) (h : S.check pd lines A B = true) (t : ℝ) (ht : 0 < t) (hs : t ≤ S.Lo ∨ S.Hi ≤ t) :
    symmetricProfile luWangSource 1 t ≤ A + B * t - S.ε * (1 + t) := by
  simp only [SourceD.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hkL⟩, hkR⟩, hL0⟩, hLL⟩, hRH⟩, hdR⟩, -⟩, -⟩ := h
  rcases hs with hs | hs
  · exact (lineOK_getD hl hkL t ht).trans (line_le_on hL0 hLL t (by simpa using ht.le) hs)
  · refine (lineOK_getD hl hkR t ht).trans ?_
    simp only [lineLeQ, decide_eq_true_eq] at hRH
    have h1 : ((lines.getD S.kR 0).1 : ℝ) + (lines.getD S.kR 0).2 * S.Hi ≤ A + B * S.Hi - S.ε * (1 + S.Hi) := by
      exact_mod_cast hRH
    have h2 : ((lines.getD S.kR 0).2 : ℝ) ≤ B - S.ε := by exact_mod_cast hdR
    nlinarith [mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr h2)]

/-! ## The bank -/

structure BankD (nCtl m nR nC : ℕ) where
  A : Fin m → ℚ
  B : Fin m → ℚ
  ctl : Fin nCtl → CtrlD
  raw : Fin nR → ProfD
  rawMin : Fin nR → ℚ
  closed : Fin nC → ProfD
  closedMin : Fin nC → ℚ
  rawPieces : Fin nR → List (RawD (Fin nR ⊕ Fin nC) nCtl m)
  closedPieces : Fin nC → List (ClosedPD nR)
  src : Fin m → SourceD (Fin nR ⊕ Fin nC)
  lines : List (ℚ × ℚ)
  i0 : Fin nR ⊕ Fin nC

variable {nR nC : ℕ}

def BankD.pd (D : BankD nCtl m nR nC) : Fin nR ⊕ Fin nC → ProfD := Sum.elim D.raw D.closed

def BankD.check (D : BankD nCtl m nR nC) : Bool :=
  (List.finRange m).all (fun h => decide (0 < D.A h) && decide (0 < D.B h) &&
    (D.src h).check D.pd D.lines (D.A h) (D.B h)) &&
  (List.finRange nR).all (fun i => (D.raw i).ok (D.rawMin i) &&
    chainQ ((D.raw i).xs.headD 0) ((D.rawPieces i).map (fun x => (x.lo, x.hi))) ((D.raw i).xs.getLastD 0) &&
    (D.rawPieces i).all (RawD.check D.ctl D.A D.B D.pd D.i0 (D.raw i))) &&
  (List.finRange nC).all (fun i => (D.closed i).ok (D.closedMin i) &&
    chainQ ((D.closed i).xs.headD 0) ((D.closedPieces i).map (fun x => (x.lo, x.hi)))
      ((D.closed i).xs.getLastD 0) &&
    (D.closedPieces i).all (ClosedPD.check D.raw (D.closed i)))

theorem BankD.sound (D : BankD nCtl m nR nC) (hcert : ∀ c, (D.ctl c).CertOK)
    (hl : ∀ p ∈ D.lines, LineOK p.1 p.2) (h : D.check = true) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ i, (D.raw i).toBP.Assert C) ∧ (∀ i, (D.closed i).toBP.Assert C) ∧
      ∀ s (k b : ℕ), 0 < k → 0 < b → ∀ N : ℕ,
        C * Real.exp ((D.A s : ℝ) * k + (D.B s : ℝ) * b) ≤ (N : ℝ) → RamseyArrows k b N := by
  simp only [BankD.check, Bool.and_eq_true] at h
  obtain ⟨⟨hS, hR⟩, hC⟩ := h
  have hS' := fun s => all_finRange hS s
  have hR' := fun i => all_finRange hR i
  have hC' := fun i => all_finRange hC i
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS' hR' hC'
  have hprof : ∀ i, Sum.elim (fun i => (D.raw i).toBP) (fun i => (D.closed i).toBP) i = (D.pd i).toBP := by
    intro i; cases i <;> rfl
  have hsrc := fun s => (hS' s).2
  have hsc := fun s => hsrc s
  simp only [SourceD.check, Bool.and_eq_true, decide_eq_true_eq] at hsc
  refine joint_main_v2 (fun s => (D.A s : ℝ)) (fun s => (D.B s : ℝ))
    (fun s => by exact_mod_cast (hS' s).1.1) (fun s => by exact_mod_cast (hS' s).1.2)
    (fun i => (D.raw i).toBP) (fun i => (D.closed i).toBP)
    (fun i => ProfD.valid_of_ok _ _ (hR' i).1.1) (fun i => ProfD.valid_of_ok _ _ (hC' i).1.1)
    (fun i => (D.rawPieces i).length) (fun i J => ((D.rawPieces i).get J).lo)
    (fun i J => ((D.rawPieces i).get J).hi) (fun i J => ((D.rawPieces i).get J).margin)
    (fun i J => ((D.rawPieces i).get J).toPiece D.ctl D.B D.i0)
    (fun i r h1 h2 => chain_cover_fin _ _ _ _ (hR' i).1.2 r h1 h2)
    (fun i J => RawD.valid_of_check D.ctl hcert D.A D.B D.pd _ hprof D.i0 (D.raw i) _
      (List.all_eq_true.mp (hR' i).2 _ (List.get_mem _ _)))
    (fun i => (D.closedPieces i).length) (fun i J => ((D.closedPieces i).get J).lo)
    (fun i J => ((D.closedPieces i).get J).hi) (fun i J => ((D.closedPieces i).get J).toPiece)
    (fun i r h1 h2 => chain_cover_fin _ _ _ _ (hC' i).1.2 r h1 h2)
    (fun i J => ClosedPD.valid_of_check D.raw (D.closed i) _
      (List.all_eq_true.mp (hC' i).2 _ (List.get_mem _ _)))
    (fun s => ((D.src s).Lo : ℝ)) (fun s => ((D.src s).Hi : ℝ)) (fun s => ((D.src s).ε : ℝ))
    (fun s => ((D.src s).η : ℝ))
    (fun s => by exact_mod_cast (hsc s).1.1.1.1.1.1.1.1.1.1.1)
    (fun s => by exact_mod_cast (hsc s).1.1.1.1.1.1.1.1.1.1.2)
    (fun s => by exact_mod_cast (hsc s).1.1.1.1.1.1.1.1.1.2)
    (fun s => by exact_mod_cast (hsc s).1.1.1.1.1.1.1.1.2)
    (fun s t ht hs => SourceD.tail D.lines hl D.pd _ _ (D.src s) (hsrc s) t ht hs)
    (fun s => (D.src s).cells.length) (fun s J => ((D.src s).cells.get J).lo)
    (fun s J => ((D.src s).cells.get J).hi) (fun s J => ((D.src s).cells.get J).toCell)
    (fun s t h1 h2 => chain_cover_fin _ _ _ _ (hsc s).1.2 t h1 h2)
    (fun s J => ?_)
  have := SrcCellD.valid_of_check D.pd _ hprof D.lines hl (D.A s) (D.B s) (D.src s).η ((D.src s).cells.get J)
    (List.all_eq_true.mp (hsc s).2 _ (List.get_mem _ _))
  exact_mod_cast this

/-- The root: a profile of density `≤ 1/2` whose domain contains `1`, with `L(1) < z`. -/
def BankD.rootCheck (D : BankD nCtl m nR nC) (root : Fin nR ⊕ Fin nC) (z : ℚ) : Bool :=
  decide ((D.pd root).p ≤ 1 / 2) && decide ((D.pd root).xs.headD 0 ≤ 1) && decide (1 ≤ (D.pd root).xs.getLastD 0) &&
    decide (evalQ (D.pd root).xs (D.pd root).ys 1 < z)

theorem BankD.diagonal (D : BankD nCtl m nR nC) (hcert : ∀ c, (D.ctl c).CertOK)
    (hl : ∀ p ∈ D.lines, LineOK p.1 p.2) (h : D.check = true) (root : Fin nR ⊕ Fin nC) (z : ℚ)
    (hr : D.rootCheck root z = true) :
    ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp (z * k) := by
  obtain ⟨C, hC, hRa, hCa, -⟩ := D.sound hcert hl h
  have hval : (D.pd root).toBP.Valid := by
    have h' := h
    simp only [BankD.check, Bool.and_eq_true] at h'
    rcases root with i | i
    · have := all_finRange h'.1.2 i
      simp only [Bool.and_eq_true] at this
      exact ProfD.valid_of_ok _ _ this.1.1
    · have := all_finRange h'.2 i
      simp only [Bool.and_eq_true] at this
      exact ProfD.valid_of_ok _ _ this.1.1
  have hA : (D.pd root).toBP.Assert C := by
    rcases root with i | i
    · exact hRa i
    · exact hCa i
  simp only [BankD.rootCheck, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨hp, hlo⟩, hhi⟩, hz⟩ := hr
  have hlo' : (D.pd root).toBP.lo ≤ 1 := by simp only [ProfD.toBP]; exact_mod_cast hlo
  have hhi' : 1 ≤ (D.pd root).toBP.hi := by simp only [ProfD.toBP]; exact_mod_cast hhi
  have hp' : (D.pd root).toBP.p + (D.pd root).toBP.p ≤ 1 := by
    simp only [ProfD.toBP]; have : ((D.pd root).p : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hp
    norm_num at this
    linarith
  have hz' : max ((D.pd root).toBP.L 1) ((D.pd root).toBP.L 1) < z := by
    rw [max_self]; simp only [ProfD.toBP]
    have e := evalR_cast (D.pd root).xs (D.pd root).ys 1
    push_cast at e; rw [e]; exact_mod_cast hz
  exact joint_diagonal hC _ _ hA hA hval hval hlo' hhi' hlo' hhi' hp' z hz'

end DiagRamsey.V5
