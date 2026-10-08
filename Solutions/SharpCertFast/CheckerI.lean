import Solutions.SharpCert.Checker
import Solutions.SharpCertFast.IExp

/-! isidore-the-farmer: `cellOk` with the integer fixed-point `IExp.expLo/expLeB` (names resolve to
`IExp` inside this namespace); `cell_specI` has the conclusion of `cell_spec`. -/

namespace DiagRamsey.SharpCert.IExp
open Real Set MeasureTheory

section cell
variable (g : Glob) (c : Cell)
def cellOkI : Bool :=
  decide (c.a < c.b) && decide (g.q0 ≤ c.a) && decide (c.b ≤ g.mu) &&
  decide (g.mu / c.a ≤ expLo c.lmA) && expLeB c.lmB (g.mu / c.b) &&
  decide (1 - c.a ≤ expLo c.l1A) && expLeB c.l1B (1 - c.b) &&
  decide (0 ≤ c.LLo g) &&
  expLeB (g.beta * c.BHi g) c.uHi && decide (c.eLo ≤ expLo (g.beta * c.ALo g)) &&
  (!c.bdPos g || decide (c.z g ≤ expLo c.y)) &&
  (if c.skip then !c.nbPos g && !c.bdPos g
   else (!c.nbPos g || c.lineOk g (c.BHi g)) && (!c.bdPos g || c.lineOk g (c.Mb g)))
end cell

/-- All per-cell checks at once (`cellFull` with `cellOkI`). -/
def cellFullI (g : Glob) (pts : List Pt) (c : Cell) : Bool :=
  cellOkI g c && pts.all (lineBelow g c)

lemma cell_specI {g : Glob} {c : Cell} (hg : GlobFacts g) (hc : cellOkI g c = true) {q : ℝ}
    (ha : (c.a : ℝ) ≤ q) (hb : q ≤ c.b) (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) :
    c.skip = false ∧ q * (certM g.p g.mu g.w g.beta g.x q + g.w) ≤ c.c := by
  simp only [cellOkI, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hq0a⟩, hbmu⟩, hlmA⟩, hlmB⟩, hl1A⟩, hl1B⟩, hLLo⟩, huHi⟩, heLo⟩, hy⟩,
    hcase⟩ := hc
  have ha0 : (0 : ℝ) < c.a := lt_of_lt_of_le hg.q00 (by exact_mod_cast hq0a)
  have hq0 : 0 < q := ha0.trans_le ha
  have hb' : (c.b : ℝ) ≤ g.mu := by exact_mod_cast hbmu
  have hmu1 := hg.mu1
  have hq1 : q < 1 := by linarith [hg.mu1]
  have hmu0 : (0 : ℝ) < g.mu := hg.q00.trans hg.q0mu
  have hb0 : (0 : ℝ) < c.b := hq0.trans_le hb
  have hw := hg.w0
  -- logarithm bounds
  have hlmA' : Real.log (g.mu / c.a) ≤ c.lmA := by
    have := log_le_of_le_expLo (div_pos (by exact_mod_cast hmu0) (by exact_mod_cast ha0)) hlmA
    push_cast at this; exact this
  have hlmB' : (c.lmB : ℝ) ≤ Real.log (g.mu / c.b) := by
    have := le_log_of_expLeB (div_pos (by exact_mod_cast hmu0) (by exact_mod_cast hb0)) hlmB
    push_cast at this; exact this
  have hl1A' : Real.log (1 - c.a) ≤ c.l1A := by
    have := log_le_of_le_expLo (by have : (c.a : ℝ) < 1 := by linarith
                                   exact_mod_cast (sub_pos.mpr this)) hl1A
    push_cast at this; exact this
  have hl1B' : (c.l1B : ℝ) ≤ Real.log (1 - c.b) := by
    have := le_log_of_expLeB (by have : (c.b : ℝ) < 1 := by linarith
                                 exact_mod_cast (sub_pos.mpr this)) hl1B
    push_cast at this; exact this
  -- B bounds
  have hBq : certB (g.mu : ℝ) g.w q = g.w * Real.log (g.mu / q) := rfl
  have hBhi : certB (g.mu : ℝ) g.w q ≤ c.BHi g := by
    rw [hBq, Cell.BHi]; push_cast
    apply mul_le_mul_of_nonneg_left _ hw.le
    refine le_trans (Real.log_le_log (div_pos hmu0 hq0) ?_) hlmA'
    exact div_le_div_of_nonneg_left hmu0.le ha0 ha
  have hBlo : (c.BLo g : ℝ) ≤ certB (g.mu : ℝ) g.w q := by
    rw [hBq, Cell.BLo]; push_cast
    apply mul_le_mul_of_nonneg_left _ hw.le
    refine hlmB'.trans (Real.log_le_log (div_pos hmu0 hb0) ?_)
    exact div_le_div_of_nonneg_left hmu0.le hq0 hb
  -- A bounds
  have hA := certA_eq (w := (g.w : ℝ)) hg.p0 hg.x0 hq1
  have hl1q : Real.log (1 - q) ≤ Real.log (1 - c.a) := Real.log_le_log (by linarith) (by linarith)
  have hl1q' : Real.log (1 - c.b) ≤ Real.log (1 - q) := Real.log_le_log (by linarith) (by linarith)
  have hLlo : (c.LLo g : ℝ) ≤ Real.log (g.p / g.x) + g.w * Real.log (1 - q) := by
    rw [Cell.LLo]; push_cast; have := hg.lpxLo; nlinarith
  have hLhi : Real.log (g.p / g.x) + g.w * Real.log (1 - q) ≤ c.LHi g := by
    rw [Cell.LHi]; push_cast; have := hg.lpxHi; nlinarith
  have hLLo' : (0 : ℝ) ≤ c.LLo g := by exact_mod_cast hLLo
  have hf1 : (1 - (c.b : ℝ)) / c.b ≤ (1 - q) / q := by
    rw [sub_div, sub_div, div_self hb0.ne', div_self hq0.ne']
    linarith [one_div_le_one_div_of_le hq0 hb]
  have hf2 : (1 - q) / q ≤ (1 - (c.a : ℝ)) / c.a := by
    rw [sub_div, sub_div, div_self ha0.ne', div_self hq0.ne']
    linarith [one_div_le_one_div_of_le ha0 ha]
  have hf0 : (0 : ℝ) ≤ (1 - c.b) / c.b := div_nonneg (by linarith) hb0.le
  have hAlo : (c.ALo g : ℝ) ≤ certA (g.p : ℝ) g.w g.x q := by
    rw [hA, Cell.ALo]; push_cast
    exact mul_le_mul hf1 hLlo hLLo' (hf0.trans hf1)
  have hAhi : certA (g.p : ℝ) g.w g.x q ≤ c.AHi g := by
    rw [hA, Cell.AHi]; push_cast
    exact mul_le_mul hf2 hLhi (hLLo'.trans hLlo) (hf0.trans (hf1.trans hf2))
  rcases hq.2.2 with hnb | ⟨hBA, hbind⟩
  · -- non-binding
    have hnbP : c.nbPos g = true := by
      simp only [Cell.nbPos, decide_eq_true_eq]
      exact_mod_cast hAlo.trans (hnb.trans hBhi)
    have hM : certM (g.p : ℝ) g.mu g.w g.beta g.x q = certB (g.mu : ℝ) g.w q := by
      simp [certM, hnb]
    cases hs : c.skip
    · rw [hs] at hcase
      simp only [hnbP, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true] at hcase
      refine ⟨rfl, ?_⟩
      rw [hM]; exact lineOk_spec hBhi ha hb ha0 hcase.1
    · rw [hs] at hcase; simp [hnbP] at hcase
  · -- binding
    have hU1 := exp_le_of_expLeB huHi
    push_cast at hU1
    have hU : certU (g.mu : ℝ) g.w g.beta q ≤ c.uHi :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hBhi hg.b0.le)).trans hU1
    have hE1 : (c.eLo : ℝ) ≤ expLo (g.beta * c.ALo g) := by exact_mod_cast heLo
    have hE2 := expLo_le (g.beta * c.ALo g)
    push_cast at hE2
    have hE : (c.eLo : ℝ) ≤ Real.exp (g.beta * certA (g.p : ℝ) g.w g.x q) :=
      hE1.trans (hE2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAlo hg.b0.le)))
    have hp1 : (0 : ℝ) < 1 - g.p := by linarith [hg.p1]
    set zr := (certU (g.mu : ℝ) g.w g.beta q - g.p * Real.exp (g.beta * certA (g.p : ℝ) g.w g.x q))
      / (1 - g.p) with hzr
    have hzr0 : 0 < zr := div_pos (by linarith) hp1
    have hzz : zr ≤ c.z g := by
      rw [Cell.z]; push_cast
      apply div_le_div_of_nonneg_right _ hp1.le
      nlinarith [hg.p0]
    have hbdP : c.bdPos g = true := by
      simp only [Cell.bdPos, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact_mod_cast hBlo.trans_lt (hBA.trans_le hAhi)
      · exact_mod_cast hzr0.trans_le hzz
    rw [hbdP] at hy
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hy
    have hlogz : Real.log zr ≤ c.y := by
      have := log_le_of_le_expLo (by exact_mod_cast hzr0.trans_le hzz) hy
      exact (Real.log_le_log hzr0 hzz).trans this
    have hM : certM (g.p : ℝ) g.mu g.w g.beta g.x q ≤ c.Mb g := by
      rw [certM, if_neg (not_le.mpr hBA), Cell.Mb]; push_cast
      have h1 : (g.p : ℝ) * certA g.p g.w g.x q ≤ g.p * c.AHi g :=
        mul_le_mul_of_nonneg_left hAhi hg.p0.le
      have h2 : (1 - (g.p : ℝ)) / g.beta * Real.log zr ≤ (1 - g.p) / g.beta * c.y :=
        mul_le_mul_of_nonneg_left hlogz (div_nonneg hp1.le hg.b0.le)
      rw [← hzr]; linarith
    cases hs : c.skip
    · rw [hs] at hcase
      simp only [hbdP, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        Bool.and_eq_true] at hcase
      exact ⟨rfl, lineOk_spec hM ha hb ha0 hcase.2⟩
    · rw [hs] at hcase; simp [hbdP] at hcase


end DiagRamsey.SharpCert.IExp
