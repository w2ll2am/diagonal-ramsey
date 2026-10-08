import Lemmas.DiagRamsey_PLCheck
import Definitions.Def_DiagRamsey_JointBank2
import Solutions.SharpCert.Exp

/-!
# v5 banks in Lean (P0.6): profiles, CLOSED pieces, SOURCE pair cells

Rational data mirroring the v5 JSON, Boolean checks mirroring `joint_bank_certificate_v5m.verify`, and soundness
into the hypotheses of `joint_integer_target_bank_v2`. Each piecewise-affine inequality comes with a breakpoint
list `bp` supplied by the generator. The kernel checks that `bp` is sorted, has the right ends and has no knot
strictly inside a segment, and checks the inequality at the breakpoints in exact rationals.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.V5

open DiagRamsey.PL DiagRamsey.SharpCert

/-- An exported profile: density `p`, nodes `xs`, values `ys`. -/
structure ProfD where
  p : ℚ
  xs : List ℚ
  ys : List ℚ

/-- The profile as a `BankProfile`: `I = [xs.head, xs.last]`, `L` the interpolant. -/
noncomputable def ProfD.toBP (P : ProfD) : BankProfile :=
  ⟨P.p, (P.xs.headD 0 : ℝ), (P.xs.getLastD 0 : ℝ), evalR P.xs P.ys⟩

/-- `Profile.__init__` of v5: `0 < p < 1`, at least two nodes, positive increasing nodes, positive values, and a
rational lower bound `m > 0` of the values (the minimum). -/
def ProfD.ok (P : ProfD) (m : ℚ) : Bool :=
  decide (0 < P.p) && decide (P.p < 1) && decide (2 ≤ P.xs.length) && decide (P.xs.length = P.ys.length) &&
    sortedQ P.xs && posQ P.xs && decide (0 < m) && P.xs.all (fun x => decide (m ≤ evalQ P.xs P.ys x)) &&
    noKnotQ P.xs P.xs

/-- The generic certified inequality: `f ≤ g` on `[l, h]` from a breakpoint list. -/
lemma le_on_of_bp (f g : ℝ → ℝ) (bp : List ℚ) (l h : ℚ) (hs : sortedQ bp = true)
    (hl : bp.head? = some l) (hh : bp.getLast? = some h)
    (haf : AffineOnList f bp) (hag : AffineOnList g bp) (hpts : ∀ x ∈ bp, f x ≤ g x) :
    ∀ r : ℝ, (l : ℝ) ≤ r → r ≤ h → f r ≤ g r := by
  intro r h1 h2
  have := nonneg_of_list (fun r => g r - f r) bp hs (hag.sub haf) (fun x hx => by
    have := hpts x hx; linarith) l (by rw [hl]; rfl) h (by rw [hh]; rfl) r h1 h2
  linarith

lemma head_le_last : ∀ (xs : List ℚ), sortedQ xs = true → xs ≠ [] → xs.headD 0 ≤ xs.getLastD 0
  | [a], _, _ => by simp
  | a :: b :: rest, hs, _ => by
      simp only [sortedQ, Bool.and_eq_true, decide_eq_true_eq] at hs
      have := head_le_last (b :: rest) hs.2 (by simp)
      simp only [List.headD_cons] at this ⊢
      rw [List.getLastD_eq_getLast?, List.getLast?_cons_cons] at *
      rw [← List.getLastD_eq_getLast?] at *
      linarith [hs.1]
  | [], _, h => absurd rfl h

lemma head?_eq (xs : List ℚ) (h : xs ≠ []) : xs.head? = some (xs.headD 0) := by
  cases xs with
  | nil => exact absurd rfl h
  | cons a l => rfl

lemma getLast?_eq (xs : List ℚ) (h : xs ≠ []) : xs.getLast? = some (xs.getLastD 0) := by
  rw [List.getLastD_eq_getLast?]
  cases hx : xs.getLast? with
  | none => simp at hx; exact absurd hx h
  | some a => rfl

lemma ProfD.valid_of_ok (P : ProfD) (m : ℚ) (h : P.ok m = true) : P.toBP.Valid := by
  simp only [ProfD.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hlen⟩, -⟩, hs⟩, hpos⟩, hm⟩, hpts⟩, hk⟩ := h
  have hne : P.xs ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have hhead : (0 : ℚ) < P.xs.headD 0 := by
    cases hx : P.xs with
    | nil => exact absurd hx hne
    | cons a l => rw [hx] at hpos; simpa [posQ] using hpos
  simp only [ProfD.toBP, BankProfile.Valid]
  refine ⟨by exact_mod_cast hp0, by exact_mod_cast hp1, by exact_mod_cast hhead,
    by exact_mod_cast head_le_last P.xs hs hne, fun r h1 h2 => ?_⟩
  have := le_on_of_bp (fun _ => (m : ℝ)) (evalR P.xs P.ys) P.xs _ _ hs (head?_eq _ hne) (getLast?_eq _ hne)
    (by simpa using affineOnList_affine (m : ℝ) 0 P.xs) (affineOnList_evalR P.xs P.ys P.xs hs hk)
    (fun x hx => by rw [evalR_cast]; exact_mod_cast hpts x hx) r h1 h2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  linarith

/-- Breakpoint-list checks shared by all certified inequalities on `[lo, hi]`. -/
def bpOk (bp : List ℚ) (lo hi : ℚ) : Bool :=
  sortedQ bp && decide (bp.head? = some lo) && decide (bp.getLast? = some hi) && posQ bp

lemma bpOk_spec {bp : List ℚ} {lo hi : ℚ} (h : bpOk bp lo hi = true) :
    sortedQ bp = true ∧ bp.head? = some lo ∧ bp.getLast? = some hi ∧ posQ bp = true := by
  simp only [bpOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- `L_R ≤ L_Q` on `[lo, hi]`. -/
def plLeQ (R Q : ProfD) (bp : List ℚ) : Bool :=
  noKnotQ R.xs bp && noKnotQ Q.xs bp && bp.all (fun x => decide (evalQ R.xs R.ys x ≤ evalQ Q.xs Q.ys x))

lemma plLe_spec {R Q : ProfD} {bp : List ℚ} {lo hi : ℚ} (hb : bpOk bp lo hi = true) (h : plLeQ R Q bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → evalR R.xs R.ys r ≤ evalR Q.xs Q.ys r := by
  obtain ⟨hs, hl, hh, -⟩ := bpOk_spec hb
  simp only [plLeQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact le_on_of_bp _ _ bp lo hi hs hl hh (affineOnList_evalR _ _ bp hs h.1.1)
    (affineOnList_evalR _ _ bp hs h.1.2) (fun x hx => by rw [evalR_cast, evalR_cast]; exact_mod_cast h.2 x hx)

/-- `r L_S(1/r) ≤ L_Q(r)` on `[lo, hi]`. -/
def plReflLeQ (S Q : ProfD) (bp : List ℚ) : Bool :=
  noKnotReflQ S.xs bp && noKnotQ Q.xs bp &&
    bp.all (fun x => decide (x * evalQ S.xs S.ys (1 / x) ≤ evalQ Q.xs Q.ys x))

lemma plReflLe_spec {S Q : ProfD} {bp : List ℚ} {lo hi : ℚ} (hb : bpOk bp lo hi = true)
    (h : plReflLeQ S Q bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → r * evalR S.xs S.ys (1 / r) ≤ evalR Q.xs Q.ys r := by
  obtain ⟨hs, hl, hh, hp⟩ := bpOk_spec hb
  simp only [plReflLeQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine le_on_of_bp _ _ bp lo hi hs hl hh (affineOnList_evalR_refl _ _ bp hs hp h.1.1)
    (affineOnList_evalR _ _ bp hs h.1.2) (fun x hx => ?_)
  have e : (1 : ℝ) / (x : ℝ) = ((1 / x : ℚ) : ℝ) := by push_cast; ring
  rw [e, evalR_cast, evalR_cast]
  exact_mod_cast h.2 x hx

/-- Exported CLOSED pieces (the kinds `export_v5.py` emits), with their breakpoint lists. -/
inductive ClosedPD (nR : ℕ)
  | rawDensity (R : Fin nR) (lo hi : ℚ) (bp : List ℚ)
  | complRaw (R S : Fin nR) (lo hi : ℚ) (bp : List ℚ)

def ClosedPD.lo {nR : ℕ} : ClosedPD nR → ℚ
  | .rawDensity _ lo _ _ => lo
  | .complRaw _ _ lo _ _ => lo

def ClosedPD.hi {nR : ℕ} : ClosedPD nR → ℚ
  | .rawDensity _ _ hi _ => hi
  | .complRaw _ _ _ hi _ => hi

def ClosedPD.toPiece {nR : ℕ} : ClosedPD nR → ClosedPiece nR
  | .rawDensity R _ _ _ => .rawDensity R
  | .complRaw R S _ _ _ => .complRaw R S

/-- The v5m CLOSED-stage check of one piece of the closed profile `Q`. -/
def ClosedPD.check {nR : ℕ} (raw : Fin nR → ProfD) (Q : ProfD) : ClosedPD nR → Bool
  | .rawDensity R lo hi bp =>
      decide ((raw R).p ≤ Q.p) && decide ((raw R).xs.headD 0 ≤ lo) && decide (hi ≤ (raw R).xs.getLastD 0) &&
        bpOk bp lo hi && plLeQ (raw R) Q bp
  | .complRaw R S lo hi bp =>
      decide ((raw R).p + (raw S).p ≤ 1) && decide ((raw R).xs.headD 0 ≤ lo) &&
        decide (hi ≤ (raw R).xs.getLastD 0) && decide ((raw S).xs.headD 0 ≤ 1 / hi) &&
        decide (1 / lo ≤ (raw S).xs.getLastD 0) && decide (0 < lo) &&
        bpOk bp lo hi && plLeQ (raw R) Q bp && plReflLeQ (raw S) Q bp

lemma ClosedPD.valid_of_check {nR : ℕ} (raw : Fin nR → ProfD) (Q : ProfD) (c : ClosedPD nR)
    (h : c.check raw Q = true) :
    c.toPiece.Valid (fun i => (raw i).toBP) Q.toBP (c.lo : ℝ) (c.hi : ℝ) := by
  rcases c with ⟨R, lo, hi, bp⟩ | ⟨R, S, lo, hi, bp⟩
  · simp only [ClosedPD.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hp, hlo⟩, hhi⟩, hb⟩, hle⟩ := h
    refine ⟨by simp only [ProfD.toBP]; exact_mod_cast hp, by simp only [ProfD.toBP, ClosedPD.lo]; exact_mod_cast hlo,
      by simp only [ProfD.toBP, ClosedPD.hi]; exact_mod_cast hhi, fun r h1 h2 => ?_⟩
    exact plLe_spec hb hle r h1 h2
  · simp only [ClosedPD.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hlo⟩, hhi⟩, hSlo⟩, hShi⟩, hlo0⟩, hb⟩, hle⟩, hrefl⟩ := h
    have hlo0' : (0 : ℝ) < lo := by exact_mod_cast hlo0
    refine ⟨by simp only [ProfD.toBP]; exact_mod_cast hp, by simp only [ProfD.toBP, ClosedPD.lo]; exact_mod_cast hlo,
      by simp only [ProfD.toBP, ClosedPD.hi]; exact_mod_cast hhi, fun r h1 h2 => ?_⟩
    simp only [ClosedPD.lo, ClosedPD.hi] at h1 h2
    have hr0 : 0 < r := lt_of_lt_of_le hlo0' h1
    refine ⟨?_, ?_, max_le (plLe_spec hb hle r h1 h2) (plReflLe_spec hb hrefl r h1 h2)⟩
    · simp only [ProfD.toBP]
      have : ((raw S).xs.headD 0 : ℝ) ≤ 1 / (hi : ℝ) := by exact_mod_cast hSlo
      exact this.trans (one_div_le_one_div_of_le hr0 h2)
    · simp only [ProfD.toBP]
      have : 1 / (lo : ℝ) ≤ ((raw S).xs.getLastD 0 : ℝ) := by exact_mod_cast hShi
      exact (one_div_le_one_div_of_le hlo0' h1).trans this

/-- `L_R(s) ≤ c + d s` on `[lo, hi]`. -/
def plLeAffQ (R : ProfD) (c d : ℚ) (bp : List ℚ) : Bool :=
  noKnotQ R.xs bp && bp.all (fun x => decide (evalQ R.xs R.ys x ≤ c + d * x))

lemma plLeAff_spec {R : ProfD} {c d : ℚ} {bp : List ℚ} {lo hi : ℚ} (hb : bpOk bp lo hi = true)
    (h : plLeAffQ R c d bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → evalR R.xs R.ys r ≤ c + d * r := by
  obtain ⟨hs, hl, hh, -⟩ := bpOk_spec hb
  simp only [plLeAffQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact le_on_of_bp _ (fun r => (c : ℝ) + d * r) bp lo hi hs hl hh (affineOnList_evalR _ _ bp hs h.1)
    (affineOnList_affine _ _ bp) (fun x hx => by rw [evalR_cast]; exact_mod_cast h.2 x hx)

/-- `s L_B(1/s) ≤ c + d s` on `[lo, hi]`. -/
def plReflLeAffQ (S : ProfD) (c d : ℚ) (bp : List ℚ) : Bool :=
  noKnotReflQ S.xs bp && bp.all (fun x => decide (x * evalQ S.xs S.ys (1 / x) ≤ c + d * x))

lemma plReflLeAff_spec {S : ProfD} {c d : ℚ} {bp : List ℚ} {lo hi : ℚ} (hb : bpOk bp lo hi = true)
    (h : plReflLeAffQ S c d bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → r * evalR S.xs S.ys (1 / r) ≤ c + d * r := by
  obtain ⟨hs, hl, hh, hp⟩ := bpOk_spec hb
  simp only [plReflLeAffQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine le_on_of_bp _ (fun r => (c : ℝ) + d * r) bp lo hi hs hl hh (affineOnList_evalR_refl _ _ bp hs hp h.1)
    (affineOnList_affine _ _ bp) (fun x hx => ?_)
  have e : (1 : ℝ) / (x : ℝ) = ((1 / x : ℚ) : ℝ) := by push_cast; ring
  rw [e, evalR_cast]
  exact_mod_cast h.2 x hx

/-- A SOURCE pair cell `[lo, hi]` of the source `(A, B)` with margin `η`: v5m's stage-3 profile cell. -/
def sourcePairCheck (R S : ProfD) (A B η lo hi : ℚ) (bp : List ℚ) : Bool :=
  decide (R.p + S.p ≤ 1) && decide (R.xs.headD 0 ≤ lo) && decide (hi ≤ R.xs.getLastD 0) &&
    decide (S.xs.headD 0 ≤ 1 / hi) && decide (1 / lo ≤ S.xs.getLastD 0) && decide (0 < lo) &&
    bpOk bp lo hi && plLeAffQ R (A - η) (B - η) bp && plReflLeAffQ S (A - η) (B - η) bp

lemma sourcePair_valid {ι : Type} (prof : ι → BankProfile) (PR PB : ι) (R S : ProfD)
    (hR : prof PR = R.toBP) (hS : prof PB = S.toBP) (A B η lo hi : ℚ) (bp : List ℚ)
    (h : sourcePairCheck R S A B η lo hi bp = true) :
    (SourceCell.pair PR PB).Valid prof A B η lo hi := by
  simp only [sourcePairCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hlo⟩, hhi⟩, hSlo⟩, hShi⟩, hlo0⟩, hb⟩, hle⟩, hrefl⟩ := h
  have hlo0' : (0 : ℝ) < lo := by exact_mod_cast hlo0
  simp only [SourceCell.Valid]
  rw [hR, hS]
  refine ⟨by simp only [ProfD.toBP]; exact_mod_cast hp, by simp only [ProfD.toBP]; exact_mod_cast hlo,
    by simp only [ProfD.toBP]; exact_mod_cast hhi, fun t h1 h2 => ?_⟩
  have hr0 : 0 < t := lt_of_lt_of_le hlo0' h1
  have e : ((A - η : ℚ) : ℝ) + ((B - η : ℚ) : ℝ) * t = (A : ℝ) + B * t - η * (1 + t) := by push_cast; ring
  refine ⟨?_, ?_, max_le ?_ ?_⟩
  · simp only [ProfD.toBP]
    have : (S.xs.headD 0 : ℝ) ≤ 1 / (hi : ℝ) := by exact_mod_cast hSlo
    exact this.trans (one_div_le_one_div_of_le hr0 h2)
  · simp only [ProfD.toBP]
    have : 1 / (lo : ℝ) ≤ (S.xs.getLastD 0 : ℝ) := by exact_mod_cast hShi
    exact (one_div_le_one_div_of_le hlo0' h1).trans this
  · have := plLeAff_spec hb hle t h1 h2; rw [e] at this; exact this
  · have := plReflLeAff_spec hb hrefl t h1 h2; rw [e] at this; exact this

/-- `c + d s ≤ L_R(s)` on `[lo, hi]`. -/
def plGeAffQ (R : ProfD) (c d : ℚ) (bp : List ℚ) : Bool :=
  noKnotQ R.xs bp && bp.all (fun x => decide (c + d * x ≤ evalQ R.xs R.ys x))

lemma plGeAff_spec {R : ProfD} {c d : ℚ} {bp : List ℚ} {lo hi : ℚ} (hb : bpOk bp lo hi = true)
    (h : plGeAffQ R c d bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → (c : ℝ) + d * r ≤ evalR R.xs R.ys r := by
  obtain ⟨hs, hl, hh, -⟩ := bpOk_spec hb
  simp only [plGeAffQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact le_on_of_bp (fun r => (c : ℝ) + d * r) _ bp lo hi hs hl hh (affineOnList_affine _ _ bp)
    (affineOnList_evalR _ _ bp hs h.1) (fun x hx => by rw [evalR_cast]; exact_mod_cast h.2 x hx)

/-- An exported sharp control with log brackets `log x ≤ lxU`, `l1mL ≤ log (1 - μ)`. -/
structure CtrlD where
  p : ℚ
  μ : ℚ
  w : ℚ
  β : ℚ
  x : ℚ
  lxU : ℚ
  l1mL : ℚ

/-- The scalar part of control validity (CERT is separate). -/
def CtrlD.ok (c : CtrlD) : Bool :=
  decide (0 < c.p) && decide (c.p < 1) && decide (0 < c.μ) && decide (c.μ < 1) && decide (0 < c.w) &&
    decide (0 < c.β) && decide (c.β < 1) && decide (0 < c.x) && decide (c.x < c.p) &&
    decide (c.x ≤ expLo c.lxU) && expLeB c.l1mL (1 - c.μ) && decide (c.lxU < c.w * c.l1mL)

/-- The CERT facts of a control (item 1 of the P0.6 pipeline). -/
def CtrlD.CertOK (c : CtrlD) : Prop :=
  (certFeasible (c.p : ℝ) c.μ c.w c.β c.x).Nonempty ∧ cert (c.p : ℝ) c.μ c.w c.β c.x < 0

lemma CtrlD.x_lt_rpow (c : CtrlD) (h : c.ok = true) : (c.x : ℝ) < (1 - (c.μ : ℝ)) ^ (c.w : ℝ) := by
  simp only [CtrlD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hμ1⟩, hw⟩, -⟩, -⟩, hx0⟩, -⟩, hxe⟩, hl1⟩, hlt⟩ := h
  have hlx : Real.log c.x ≤ c.lxU := log_le_of_le_expLo hx0 hxe
  have hl1' := le_log_of_expLeB (by linarith : (0 : ℚ) < 1 - c.μ) hl1
  have hw' : (0 : ℝ) < c.w := by exact_mod_cast hw
  have hlt' : (c.lxU : ℝ) < c.w * c.l1mL := by exact_mod_cast hlt
  have h1μ : (0 : ℝ) < 1 - c.μ := sub_pos.mpr (by exact_mod_cast hμ1)
  rw [Real.rpow_def_of_pos h1μ]
  have hx0' : (0 : ℝ) < c.x := by exact_mod_cast hx0
  rw [← Real.exp_log hx0']
  apply Real.exp_lt_exp.mpr
  push_cast at hl1'
  nlinarith

/-- An exported leaf piece of a RAW profile: control `c`, source `σ`, terminal data `ξ, ν, y_slack`, upper bounds
`aU ≥ -log ξ`, `bU ≥ -log ν`, margin, interval `[lo, hi]`, breakpoints. -/
structure LeafD (nCtl m : ℕ) where
  c : Fin nCtl
  σ : Fin m
  ξ : ℚ
  ν : ℚ
  ys : ℚ
  aU : ℚ
  bU : ℚ
  margin : ℚ
  lo : ℚ
  hi : ℚ
  bp : List ℚ

/-- The sharp control of a leaf: `y₀ = e^{-(B_σ + y_slack)}`. -/
noncomputable def LeafD.ctrl {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (B : Fin m → ℚ) (L : LeafD nCtl m) :
    SharpControl m :=
  ⟨(ctl L.c).p, (ctl L.c).μ, (ctl L.c).w, (ctl L.c).β, (ctl L.c).x, L.σ, L.ξ,
    Real.exp (-((B L.σ : ℝ) + L.ys)), L.ν⟩

def LeafD.check {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (A B : Fin m → ℚ) (P : ProfD) (L : LeafD nCtl m) : Bool :=
  (ctl L.c).ok && decide (0 < L.ξ) && decide (L.ξ < (ctl L.c).x) && decide (L.ξ < expLo (-A L.σ)) &&
    decide (0 < L.ν) && decide (L.ν < (ctl L.c).μ) && decide (0 < L.ys) && expLeB (-L.aU) L.ξ &&
    expLeB (-L.bU) L.ν && decide ((ctl L.c).p ≤ P.p) && decide (0 < L.margin) && decide (0 < L.lo) &&
    bpOk L.bp L.lo L.hi &&
    plGeAffQ P (L.margin + L.aU / (1 + (ctl L.c).w))
      (L.margin + (B L.σ + L.ys + (ctl L.c).w * L.bU) / (1 + (ctl L.c).w)) L.bp

lemma LeafD.valid_of_check {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (hcert : ∀ c, (ctl c).CertOK)
    (A B : Fin m → ℚ) (prof : ι → BankProfile) (P : ProfD) (L : LeafD nCtl m) (h : L.check ctl A B P = true) :
    0 < (L.margin : ℝ) ∧ (RawPiece.leaf (L.ctrl ctl B)).Valid' (fun i => (A i : ℝ)) (fun i => (B i : ℝ)) prof
      P.toBP L.lo L.hi L.margin := by
  have hok := (show (ctl L.c).ok = true by
    simp only [LeafD.check, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1.1.1.1.1)
  have hxr := (ctl L.c).x_lt_rpow hok
  simp only [LeafD.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hξ0⟩, hξx⟩, hξA⟩, hν0⟩, hνμ⟩, hys⟩, haU⟩, hbU⟩, hpp⟩, hm⟩, hlo⟩, hb⟩, hge⟩ := h
  simp only [CtrlD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hμ0⟩, hμ1⟩, hw⟩, hβ0⟩, hβ1⟩, hx0⟩, hxp⟩, -⟩, -⟩, -⟩ := hok
  have hξ0' : (0 : ℝ) < L.ξ := by exact_mod_cast hξ0
  have hν0' : (0 : ℝ) < L.ν := by exact_mod_cast hν0
  have hw' : (0 : ℝ) < (ctl L.c).w := by exact_mod_cast hw
  -- `-log ξ ≤ aU`, `-log ν ≤ bU`
  have hA' : -Real.log L.ξ ≤ L.aU := by
    have := le_log_of_expLeB hξ0 haU; push_cast at this; linarith
  have hB' : -Real.log L.ν ≤ L.bU := by
    have := le_log_of_expLeB hν0 hbU; push_cast at this; linarith
  simp only [RawPiece.Valid', SharpControl.Valid, LeafD.ctrl]
  refine ⟨by exact_mod_cast hm, ?_, by simp only [ProfD.toBP]; exact_mod_cast hpp, ?_⟩
  · -- control validity
    refine ⟨by exact_mod_cast hp0, by exact_mod_cast hp1, by exact_mod_cast hμ0, by exact_mod_cast hμ1, hw',
      by exact_mod_cast hβ0, by exact_mod_cast hβ1, by exact_mod_cast hx0, by exact_mod_cast hxp, hxr,
      (hcert L.c).1, (hcert L.c).2, hξ0', by exact_mod_cast hξx, ?_, Real.exp_pos _, ?_, hν0',
      by exact_mod_cast hνμ⟩
    · have h1 : (L.ξ : ℝ) < expLo (-A L.σ) := by exact_mod_cast hξA
      have h2 := expLo_le (-A L.σ)
      push_cast at h2
      exact lt_of_lt_of_le h1 h2
    · apply Real.exp_lt_exp.mpr
      have : (0 : ℝ) < L.ys := by exact_mod_cast hys
      linarith
  · -- the leaf inequality
    intro r h1 h2
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by exact_mod_cast hlo) h1
    have hge' := plGeAff_spec hb hge r h1 h2
    simp only [ProfD.toBP]
    have hline : (L.ctrl ctl B).leafLine r ≤
        ((L.aU : ℝ) + r * ((B L.σ : ℝ) + L.ys + (ctl L.c).w * L.bU)) / (1 + (ctl L.c).w) := by
      simp only [SharpControl.leafLine, SharpControl.Aγ, SharpControl.Bγ, SharpControl.bγ, LeafD.ctrl,
        Real.log_exp, neg_neg]
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : r * ((B L.σ : ℝ) + L.ys + -((ctl L.c).w : ℝ) * Real.log L.ν) ≤
          r * ((B L.σ : ℝ) + L.ys + (ctl L.c).w * L.bU) := by
        apply mul_le_mul_of_nonneg_left _ hr0.le; nlinarith
      nlinarith
    have hm' : (0 : ℝ) ≤ L.margin := by exact_mod_cast hm.le
    push_cast at hge'
    have e : ((L.aU : ℝ) + r * ((B L.σ : ℝ) + L.ys + (ctl L.c).w * L.bU)) / (1 + (ctl L.c).w) =
        L.aU / (1 + (ctl L.c).w) + (B L.σ + L.ys + (ctl L.c).w * L.bU) / (1 + (ctl L.c).w) * r := by
      field_simp
    rw [e] at hline
    simp only [LeafD.ctrl] at hline
    nlinarith [mul_nonneg hm' hr0.le]

/-- Clamp sum over consecutive nodes: `∑_j d_j · max 0 (min s u_{j+1} - u_j)` (list form). -/
noncomputable def gL : List ℚ → List ℚ → ℝ → ℝ
  | u0 :: u1 :: us, d0 :: ds, s => (d0 : ℝ) * max 0 (min s (u1 : ℝ) - u0) + gL (u1 :: us) ds s
  | _, _, _ => 0

def gLQ : List ℚ → List ℚ → ℚ → ℚ
  | u0 :: u1 :: us, d0 :: ds, s => d0 * max 0 (min s u1 - u0) + gLQ (u1 :: us) ds s
  | _, _, _ => 0

lemma gL_cast : ∀ (us ds : List ℚ) (s : ℚ), gL us ds (s : ℝ) = (gLQ us ds s : ℝ)
  | u0 :: u1 :: us, d0 :: ds, s => by
      simp only [gL, gLQ, gL_cast (u1 :: us) ds s]; push_cast [Rat.cast_max, Rat.cast_min]; ring
  | [], _, _ => by simp [gL, gLQ]
  | [_], _, _ => by simp [gL, gLQ]
  | _ :: _ :: _, [], _ => by simp [gL, gLQ]

lemma gL_segAffine {a b : ℝ} (hab : a ≤ b) : ∀ (us ds : List ℚ),
    (∀ x ∈ us, (x : ℝ) ≤ a ∨ b ≤ x) → SegAffine (gL us ds) a b
  | u0 :: u1 :: us, d0 :: ds, hk => by
      have h := ((segAffine_clamp hab (hk u0 (by simp)) (hk u1 (by simp))).smul (d0 : ℝ)).add
        (gL_segAffine hab (u1 :: us) ds (fun x hx => hk x (List.mem_cons_of_mem _ hx)))
      intro r h1 h2; have := h r h1 h2; simp only [gL] at this ⊢; linarith
  | [], _, _ => segAffine_const 0
  | [_], _, _ => segAffine_const 0
  | _ :: _ :: _, [], _ => segAffine_const 0

lemma affineOnList_gL (us ds : List ℚ) : ∀ (bp : List ℚ), sortedQ bp = true → noKnotQ us bp = true →
    AffineOnList (gL us ds) bp
  | a :: b :: rest, hs, hk => by
      simp only [sortedQ, noKnotQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.or_eq_true] at hs hk
      refine ⟨fun r h1 h2 => gL_segAffine (by exact_mod_cast hs.1.le) us ds (fun x hx => ?_) r h1 h2,
        affineOnList_gL us ds (b :: rest) hs.2 hk.2⟩
      rcases hk.1 x hx with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  | [], _, _ => trivial
  | [_], _, _ => trivial

/-- The `Fin`-indexed clamp sum of a `RoutePiece` built from lists equals `gL`. -/
lemma fin_sum_eq_gL : ∀ (us ds : List ℚ), us.length = ds.length + 1 → ∀ s : ℝ,
    ∑ j : Fin ds.length, ((ds.getD j 0 : ℚ) : ℝ) *
      max 0 (min s ((us.getD (j + 1) 0 : ℚ) : ℝ) - ((us.getD j 0 : ℚ) : ℝ)) = gL us ds s
  | u0 :: u1 :: us, d0 :: ds, hlen, s => by
      erw [Fin.sum_univ_succ (n := ds.length)]
      simp only [List.length_cons] at hlen
      have ih := fin_sum_eq_gL (u1 :: us) ds (by simp only [List.length_cons]; omega) s
      simp only [gL, Fin.val_zero, List.getD_cons_zero, zero_add, List.getD_cons_succ, Fin.val_succ]
      rw [← ih]
      congr 1
  | [_], [], _, s => by simp [gL]
  | [], _, hlen, _ => by simp at hlen
  | [_], _ :: _, hlen, _ => by simp at hlen
  | _ :: _ :: _, [], hlen, _ => by simp at hlen

lemma affineOnList_smul {f : ℝ → ℝ} (c : ℝ) : ∀ {bp : List ℚ}, AffineOnList f bp →
    AffineOnList (fun r => c * f r) bp
  | _ :: _ :: _, hf => ⟨fun r h1 h2 => by
      have := hf.1 r h1 h2; simp only; linear_combination c * this, affineOnList_smul c hf.2⟩
  | [], _ => trivial
  | [_], _ => trivial

lemma sortedQ_getD_lt : ∀ (l : List ℚ), sortedQ l = true → ∀ i j : ℕ, i < j → j < l.length →
    l.getD i 0 < l.getD j 0
  | a :: b :: rest, hs, i, j, hij, hj => by
      simp only [sortedQ, Bool.and_eq_true, decide_eq_true_eq] at hs
      have ih := sortedQ_getD_lt (b :: rest) hs.2
      rcases i with _ | i
      · rcases j with _ | j
        · omega
        · simp only [List.getD_cons_zero, List.getD_cons_succ]
          rcases j with _ | j
          · simpa using hs.1
          · have := ih 0 (j + 1) (by omega) (by simpa using hj)
            simp only [List.getD_cons_zero] at this; linarith
      · rcases j with _ | j
        · omega
        · simp only [List.getD_cons_succ]
          exact ih i j (by omega) (by simpa using hj)
  | [], _, _, _, _, hj => by simp at hj
  | [_], _, _, _, hij, hj => by simp at hj; omega

/-- `c0 + c1 s + c2 g_L(s) ≤ L_P(s)` on `[lo, hi]`. -/
def gLeQ (P : ProfD) (us ds : List ℚ) (c0 c1 c2 : ℚ) (bp : List ℚ) : Bool :=
  noKnotQ P.xs bp && noKnotQ us bp &&
    bp.all (fun x => decide (c0 + c1 * x + c2 * gLQ us ds x ≤ evalQ P.xs P.ys x))

lemma gLe_spec {P : ProfD} {us ds : List ℚ} {c0 c1 c2 : ℚ} {bp : List ℚ} {lo hi : ℚ}
    (hb : bpOk bp lo hi = true) (h : gLeQ P us ds c0 c1 c2 bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → (c0 : ℝ) + c1 * r + c2 * gL us ds r ≤ evalR P.xs P.ys r := by
  obtain ⟨hs, hl, hh, -⟩ := bpOk_spec hb
  simp only [gLeQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact le_on_of_bp (fun r => (c0 : ℝ) + c1 * r + c2 * gL us ds r) _ bp lo hi hs hl hh
    ((affineOnList_affine _ _ bp).add (affineOnList_smul _ (affineOnList_gL us ds bp hs h.1.2)))
    (affineOnList_evalR _ _ bp hs h.1.1)
    (fun x hx => by rw [evalR_cast, gL_cast]; exact_mod_cast h.2 x hx)

/-- `L_P(s) ≤ c0 + c1 s + c2 g_L(s)` on `[lo, hi]`. -/
def gGeQ (P : ProfD) (us ds : List ℚ) (c0 c1 c2 : ℚ) (bp : List ℚ) : Bool :=
  noKnotQ P.xs bp && noKnotQ us bp &&
    bp.all (fun x => decide (evalQ P.xs P.ys x ≤ c0 + c1 * x + c2 * gLQ us ds x))

lemma gGe_spec {P : ProfD} {us ds : List ℚ} {c0 c1 c2 : ℚ} {bp : List ℚ} {lo hi : ℚ}
    (hb : bpOk bp lo hi = true) (h : gGeQ P us ds c0 c1 c2 bp = true) :
    ∀ r : ℝ, (lo : ℝ) ≤ r → r ≤ hi → evalR P.xs P.ys r ≤ (c0 : ℝ) + c1 * r + c2 * gL us ds r := by
  obtain ⟨hs, hl, hh, -⟩ := bpOk_spec hb
  simp only [gGeQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact le_on_of_bp _ (fun r => (c0 : ℝ) + c1 * r + c2 * gL us ds r) bp lo hi hs hl hh
    (affineOnList_evalR _ _ bp hs h.1.1)
    ((affineOnList_affine _ _ bp).add (affineOnList_smul _ (affineOnList_gL us ds bp hs h.1.2)))
    (fun x hx => by rw [evalR_cast, gL_cast]; exact_mod_cast h.2 x hx)

/-- Terminal data shared by leaves and routes: control `c`, source `σ`, `ξ, ν, y_slack`, `aU ≥ -log ξ`,
`bU ≥ -log ν`. -/
structure TermD (nCtl m : ℕ) where
  c : Fin nCtl
  σ : Fin m
  ξ : ℚ
  ν : ℚ
  ys : ℚ
  aU : ℚ
  bU : ℚ

noncomputable def TermD.ctrl {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (B : Fin m → ℚ) (T : TermD nCtl m) :
    SharpControl m :=
  ⟨(ctl T.c).p, (ctl T.c).μ, (ctl T.c).w, (ctl T.c).β, (ctl T.c).x, T.σ, T.ξ,
    Real.exp (-((B T.σ : ℝ) + T.ys)), T.ν⟩

def TermD.check {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (A : Fin m → ℚ) (T : TermD nCtl m) : Bool :=
  (ctl T.c).ok && decide (0 < T.ξ) && decide (T.ξ < (ctl T.c).x) && decide (T.ξ < expLo (-A T.σ)) &&
    decide (0 < T.ν) && decide (T.ν < (ctl T.c).μ) && decide (0 < T.ys) && expLeB (-T.aU) T.ξ &&
    expLeB (-T.bU) T.ν

lemma TermD.spec {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (hcert : ∀ c, (ctl c).CertOK)
    (A B : Fin m → ℚ) (T : TermD nCtl m) (h : T.check ctl A = true) :
    (T.ctrl ctl B).Valid (fun i => (A i : ℝ)) (fun i => (B i : ℝ)) ∧ (T.ctrl ctl B).Aγ ≤ T.aU ∧
      (T.ctrl ctl B).Bγ = (B T.σ : ℝ) + T.ys ∧ (T.ctrl ctl B).bγ ≤ T.bU ∧ (T.ctrl ctl B).w = (ctl T.c).w ∧
      (T.ctrl ctl B).p = (ctl T.c).p := by
  have hok := (show (ctl T.c).ok = true by
    simp only [TermD.check, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1)
  have hxr := (ctl T.c).x_lt_rpow hok
  simp only [TermD.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hξ0⟩, hξx⟩, hξA⟩, hν0⟩, hνμ⟩, hys⟩, haU⟩, hbU⟩ := h
  simp only [CtrlD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hμ0⟩, hμ1⟩, hw⟩, hβ0⟩, hβ1⟩, hx0⟩, hxp⟩, -⟩, -⟩, -⟩ := hok
  have hξ0' : (0 : ℝ) < T.ξ := by exact_mod_cast hξ0
  have hw' : (0 : ℝ) < (ctl T.c).w := by exact_mod_cast hw
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [SharpControl.Valid, TermD.ctrl]
    refine ⟨by exact_mod_cast hp0, by exact_mod_cast hp1, by exact_mod_cast hμ0, by exact_mod_cast hμ1, hw',
      by exact_mod_cast hβ0, by exact_mod_cast hβ1, by exact_mod_cast hx0, by exact_mod_cast hxp, hxr,
      (hcert T.c).1, (hcert T.c).2, hξ0', by exact_mod_cast hξx, ?_, Real.exp_pos _, ?_, by exact_mod_cast hν0,
      by exact_mod_cast hνμ⟩
    · have h1 : (T.ξ : ℝ) < expLo (-A T.σ) := by exact_mod_cast hξA
      have h2 := expLo_le (-A T.σ)
      push_cast at h2
      exact lt_of_lt_of_le h1 h2
    · apply Real.exp_lt_exp.mpr
      have : (0 : ℝ) < T.ys := by exact_mod_cast hys
      linarith
  · simp only [SharpControl.Aγ, TermD.ctrl]
    have := le_log_of_expLeB hξ0 haU; push_cast at this; linarith
  · simp only [SharpControl.Bγ, TermD.ctrl, Real.log_exp, neg_neg]
  · simp only [SharpControl.bγ, TermD.ctrl]
    have := le_log_of_expLeB hν0 hbU; push_cast at this; linarith

/-- One call of a route: child `ch`, rational `z` with `e^{-d} ≤ z < 1 - p_ch`, breakpoints on its cell. -/
structure CallD (ι : Type) where
  ch : ι
  z : ℚ
  bp : List ℚ

/-- An exported route piece: terminal `t`, nodes `us`, slopes `ds`, calls, start value `g0`, height margin `hm`,
output margin, interval `[lo, hi]`, breakpoints `bp`. -/
structure RouteD (ι : Type) (nCtl m : ℕ) where
  t : TermD nCtl m
  us : List ℚ
  ds : List ℚ
  calls : List (CallD ι)
  g0 : ℚ
  hm : ℚ
  margin : ℚ
  lo : ℚ
  hi : ℚ
  bp : List ℚ

noncomputable def RouteD.toPiece {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (B : Fin m → ℚ) (i0 : ι)
    (R : RouteD ι nCtl m) : RoutePiece ι m :=
  ⟨R.t.ctrl ctl B, R.ds.length, fun i => (R.us.getD i 0 : ℝ), fun j => (R.ds.getD j 0 : ℝ),
    fun j => (R.calls.getD j ⟨i0, 0, []⟩).ch, R.g0⟩

def RouteD.cellCheck {ι : Type} {nCtl m : ℕ} (pd : ι → ProfD) (i0 : ι) (R : RouteD ι nCtl m) (j : ℕ) : Bool :=
  let cl := R.calls.getD j ⟨i0, 0, []⟩
  let Pc := pd cl.ch
  decide (Pc.xs.headD 0 ≤ R.us.getD j 0) && decide (R.us.getD (j + 1) 0 ≤ Pc.xs.getLastD 0) &&
    decide (0 < cl.z) && expLeB (-R.ds.getD j 0) cl.z && decide (cl.z < 1 - Pc.p) &&
    bpOk cl.bp (R.us.getD j 0) (R.us.getD (j + 1) 0) && gGeQ Pc R.us R.ds (R.g0 - R.hm) 0 1 cl.bp

def RouteD.check {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (A B : Fin m → ℚ) (pd : ι → ProfD) (i0 : ι)
    (P : ProfD) (R : RouteD ι nCtl m) : Bool :=
  let w := (ctl R.t.c).w
  let θ := R.us.getD 0 0
  R.t.check ctl A && decide ((ctl R.t.c).p < P.p) && decide (R.us.length = R.ds.length + 1) &&
    decide (0 < R.ds.length) && sortedQ R.us && decide (0 < θ) && decide (0 < R.g0) && decide (θ ≤ R.lo) &&
    decide (R.hi ≤ R.us.getD R.ds.length 0) && decide (0 < R.hm) && decide (0 < R.margin) &&
    (List.range R.ds.length).all (R.cellCheck pd i0) && bpOk R.bp R.lo R.hi &&
    gLeQ P R.us R.ds (R.margin + R.g0) 0 1 R.bp &&
    gLeQ P R.us R.ds (R.margin + (R.t.aU + w * θ * R.t.bU) / (1 + w)) ((B R.t.σ + R.t.ys) / (1 + w))
      (w / (1 + w)) R.bp

lemma RouteD.g_eq {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (B : Fin m → ℚ) (i0 : ι)
    (R : RouteD ι nCtl m) (hlen : R.us.length = R.ds.length + 1) (s : ℝ) :
    (R.toPiece ctl B i0).g s = R.g0 + gL R.us R.ds s := by
  simp only [RoutePiece.g, RouteD.toPiece, Fin.val_succ, Fin.val_castSucc]
  exact congrArg (fun x => (R.g0 : ℝ) + x) (fin_sum_eq_gL _ _ hlen s)

lemma RouteD.valid_of_check {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlD) (hcert : ∀ c, (ctl c).CertOK)
    (A B : Fin m → ℚ) (pd : ι → ProfD) (prof : ι → BankProfile) (hprof : ∀ i, prof i = (pd i).toBP) (i0 : ι)
    (P : ProfD) (R : RouteD ι nCtl m) (h : R.check ctl A B pd i0 P = true) :
    0 < (R.margin : ℝ) ∧ (RawPiece.route (R.toPiece ctl B i0)).Valid' (fun i => (A i : ℝ))
      (fun i => (B i : ℝ)) prof P.toBP R.lo R.hi R.margin := by
  simp only [RouteD.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, hpp⟩, hlen⟩, hM⟩, hs⟩, hθ⟩, hg0⟩, hθlo⟩, hhi⟩, hhm⟩, hmg⟩, hcells⟩, hb⟩,
    hv1⟩, hv2⟩ := h
  obtain ⟨hTv, hAU, hBeq, hbU, hwe, hpe⟩ := TermD.spec ctl hcert A B R.t hT
  have hg := RouteD.g_eq ctl B i0 R hlen
  have hw' : (0 : ℝ) < (ctl R.t.c).w := by
    have := hTv.2.2.2.2.1; rwa [hwe] at this
  have hθ' : (0 : ℝ) < (R.us.getD 0 0 : ℚ) := by exact_mod_cast hθ
  refine ⟨by exact_mod_cast hmg, ?_⟩
  simp only [RawPiece.Valid', RawPiece.Valid]
  refine ⟨hTv, ?_, hM, ?_, ?_, by simp only [RouteD.toPiece]; exact_mod_cast hg0, ?_, ?_, ?_, ?_⟩
  · simp only [RouteD.toPiece, ProfD.toBP]; rw [hpe]; exact_mod_cast hpp
  · simp only [RoutePiece.θ, RouteD.toPiece, Fin.val_zero]; exact hθ'
  · intro i j hij
    simp only [RouteD.toPiece]
    have := sortedQ_getD_lt R.us hs i j hij (by have := j.2; change (j : ℕ) < R.ds.length + 1 at this; omega)
    exact_mod_cast this
  · simp only [RoutePiece.θ, RouteD.toPiece, Fin.val_zero]; exact_mod_cast hθlo
  · simp only [RoutePiece.ω, RouteD.toPiece, Fin.val_last]; exact_mod_cast hhi
  · intro j
    rw [List.all_eq_true] at hcells
    have hc := hcells j (List.mem_range.mpr j.2)
    simp only [RouteD.cellCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hlo, hhi'⟩, hz0⟩, hez⟩, hz1⟩, hbc⟩, hge⟩ := hc
    simp only [RouteD.toPiece, hprof, ProfD.toBP, Fin.val_succ, Fin.val_castSucc]
    refine ⟨by exact_mod_cast hlo, by exact_mod_cast hhi', ?_, fun s h1 h2 => ?_⟩
    · have hz0' : (0 : ℝ) < (R.calls.getD (↑j) ⟨i0, 0, []⟩).z := by exact_mod_cast hz0
      have h1 := le_log_of_expLeB hz0 hez
      have h2 : Real.log ((R.calls.getD (↑j) ⟨i0, 0, []⟩).z : ℝ) <
          Real.log (1 - ((pd (R.calls.getD (↑j) ⟨i0, 0, []⟩).ch).p : ℝ)) :=
        Real.log_lt_log hz0' (by exact_mod_cast hz1)
      push_cast at h1
      linarith
    · have h3 := gGe_spec hbc hge s h1 h2
      have e := hg s
      simp only [RouteD.toPiece] at e
      rw [e]
      have : (0 : ℝ) < R.hm := by exact_mod_cast hhm
      push_cast at h3 ⊢
      linarith
  · intro r h1 h2
    have hr0 : 0 < r := lt_of_lt_of_le (lt_of_lt_of_le hθ' (by exact_mod_cast hθlo)) h1
    have e1 := gLe_spec hb hv1 r h1 h2
    have e2 := gLe_spec hb hv2 r h1 h2
    simp only [RoutePiece.value, ProfD.toBP]
    rw [hg r, show (R.toPiece ctl B i0).g₀ = (R.g0 : ℝ) from rfl]
    simp only [RoutePiece.θ, RouteD.toPiece, Fin.val_zero, hwe]
    push_cast at e1 e2
    rw [add_max]
    refine max_le (by linarith) ?_
    rw [hBeq]
    set w : ℝ := ((ctl R.t.c).w : ℝ)
    have hw1 : 0 < 1 + w := by linarith
    have hA := hAU
    have hbb : w * ((R.us.getD 0 0 : ℚ) : ℝ) * (R.t.ctrl ctl B).bγ ≤ w * (R.us.getD 0 0 : ℚ) * R.t.bU :=
      mul_le_mul_of_nonneg_left hbU (by positivity)
    have key : ((R.t.ctrl ctl B).Aγ + r * ((B R.t.σ : ℝ) + R.t.ys) +
        w * (((R.us.getD 0 0 : ℚ) : ℝ) * (R.t.ctrl ctl B).bγ + (R.g0 + gL R.us R.ds r) - R.g0)) / (1 + w) ≤
        (R.t.aU + w * (R.us.getD 0 0 : ℚ) * R.t.bU) / (1 + w) + ((B R.t.σ : ℝ) + R.t.ys) / (1 + w) * r +
          w / (1 + w) * gL R.us R.ds r := by
      rw [show (R.t.aU + w * (R.us.getD 0 0 : ℚ) * R.t.bU) / (1 + w) + ((B R.t.σ : ℝ) + R.t.ys) / (1 + w) * r +
          w / (1 + w) * gL R.us R.ds r = (R.t.aU + w * (R.us.getD 0 0 : ℚ) * R.t.bU + ((B R.t.σ : ℝ) + R.t.ys) * r +
          w * gL R.us R.ds r) / (1 + w) by ring]
      apply div_le_div_of_nonneg_right _ hw1.le
      nlinarith
    linarith

end DiagRamsey.V5
