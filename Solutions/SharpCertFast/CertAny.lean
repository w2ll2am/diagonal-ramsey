import Solutions.SharpCert.GenChain
import Solutions.SharpCertFast.CheckerI

/-! isidore-the-farmer: `Integral`/`Gen`/`GenChain` re-run with `cellOkAny = cellOk || cellOkI`, so a
certificate may mix rupert's `cellFull` Cells modules with `cellFullI` ones. The block between the
markers is `Integral.lean` lines 20-41 and 60-294 with `cellOk` -> `cellOkAny`, `cell_spec` -> `cell_specAny`. -/

namespace DiagRamsey.SharpCert.IExp
open Real Set MeasureTheory intervalIntegral

def cellOkAny (g : Glob) (c : Cell) : Bool := cellOk g c || cellOkI g c

lemma cellOkI_q0 {g : Glob} {c : Cell} (hc : cellOkI g c = true) : g.q0 ≤ c.a := by
  simp only [cellOkI, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  exact h

lemma cellOkAny_q0 {g : Glob} {c : Cell} (hc : cellOkAny g c = true) : g.q0 ≤ c.a := by
  simp only [cellOkAny, Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact cellOk_q0 h
  · exact cellOkI_q0 h

lemma cell_specAny {g : Glob} {c : Cell} (hg : GlobFacts g) (hc : cellOkAny g c = true) {q : ℝ}
    (ha : (c.a : ℝ) ≤ q) (hb : q ≤ c.b) (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) :
    c.skip = false ∧ q * (certM g.p g.mu g.w g.beta g.x q + g.w) ≤ c.c := by
  simp only [cellOkAny, Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact cell_spec hg h ha hb hq
  · exact cell_specI hg h ha hb hq

-- begin Integral.lean 20-41, 60-294 (ptOk_spec/ptsOk_head reused)
lemma chord {cc s l0 l1 E0 E1 l : ℝ} (h0 : cc - s * l0 ≤ E0) (h1 : cc - s * l1 ≤ E1)
    (hl : l0 < l1) (ha : l0 ≤ l) (hb : l ≤ l1) :
    cc - s * l ≤ E0 + (E1 - E0) / (l1 - l0) * (l - l0) := by
  have hd : 0 < l1 - l0 := sub_pos.mpr hl
  rw [← sub_nonneg]
  have key : E0 + (E1 - E0) / (l1 - l0) * (l - l0) - (cc - s * l) =
      ((E0 - (cc - s * l0)) * (l1 - l) + (E1 - (cc - s * l1)) * (l - l0)) / (l1 - l0) := by
    field_simp; ring
  rw [key]
  apply div_nonneg _ hd.le
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))

lemma integral_aff (a b α β : ℝ) :
    ∫ t in a..b, (α + β * Real.log t) = α * (b - a) + β * (b * log b - a * log a - b + a) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_log'.const_mul β),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_log]
  simp only [smul_eq_mul]; ring

lemma intervalIntegrable_aff (a b α β : ℝ) :
    IntervalIntegrable (fun t => α + β * Real.log t) volume a b :=
  intervalIntegrable_const.add (intervalIntegrable_log'.const_mul β)

lemma sub01 {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    uIcc a b ⊆ uIcc (0 : ℝ) 1 :=
  uIcc_subset_uIcc (mem_uIcc_of_le ha0 ha1) (mem_uIcc_of_le hb0 hb1)

section main
variable {g : Glob} {cells : List Cell}

/-- Every feasible `q` lies in a non-skipped cell, with `q (M q + w) ≤ c`. -/
lemma elem_cell (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) {q : ℝ}
    (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) :
    ∃ c ∈ cells, c.skip = false ∧ (g.q0 : ℝ) ≤ c.a ∧ (c.a : ℝ) ≤ q ∧
      q * (certM g.p g.mu g.w g.beta g.x q + g.w) ≤ c.c := by
  obtain ⟨c, hc, ha, hb⟩ := chain_mem cells _ _ hch q (excl hg hq) hq.2.1
  obtain ⟨hs, hle⟩ := cell_specAny hg (hcells c hc) ha hb hq
  exact ⟨c, hc, hs, by exact_mod_cast cellOkAny_q0 (hcells c hc), ha, hle⟩

/-- The value of the element of the `sSup` at `q`, `t`. -/
noncomputable def val (g : Glob) (q t : ℝ) : ℝ :=
  q * certM g.p g.mu g.w g.beta g.x q + g.w * q * (1 + Real.log t)

lemma val_le (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) {q t : ℝ}
    (hq : q ∈ certFeasible g.p g.mu g.w g.beta g.x) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ c ∈ cells, c.skip = false ∧ (g.q0 : ℝ) ≤ c.a ∧
      val g q t ≤ c.c - g.w * c.a * (-Real.log t) := by
  obtain ⟨c, hc, hs, hq0, ha, hle⟩ := elem_cell hg hch hcells hq
  refine ⟨c, hc, hs, hq0, ?_⟩
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  have hw := hg.w0
  have : g.w * q * Real.log t ≤ g.w * c.a * Real.log t := by
    have : (g.w : ℝ) * c.a ≤ g.w * q := mul_le_mul_of_nonneg_left ha hw.le
    nlinarith
  unfold val
  nlinarith

lemma line_at {c : Cell} {P : Pt} (hs : c.skip = false) (h : lineBelow g c P = true) :
    (c.c : ℝ) - g.w * c.a * P.lam ≤ P.E := by
  simp only [lineBelow, hs, Bool.false_or, decide_eq_true_eq] at h
  exact_mod_cast h

local notation "F" => certIntegrand (Glob.p g : ℝ) (Glob.mu g) (Glob.w g) (Glob.beta g) (Glob.x g)

lemma F_eq (t : ℝ) : F t = sSup ((fun q => val g q t) '' certFeasible g.p g.mu g.w g.beta g.x) :=
  rfl

lemma img_nonempty (hg : GlobFacts g) (t : ℝ) :
    ((fun q => val g q t) '' certFeasible g.p g.mu g.w g.beta g.x).Nonempty :=
  ⟨_, ⟨_, (witness hg).1, rfl⟩⟩

/-- Pointwise bound by any `B` dominating all the cell lines. -/
lemma F_le (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) {t B : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hB : ∀ c ∈ cells, c.skip = false → (g.q0 : ℝ) ≤ c.a →
      (c.c : ℝ) - g.w * c.a * (-Real.log t) ≤ B) :
    F t ≤ B := by
  rw [F_eq]
  apply csSup_le (img_nonempty hg t)
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨c, hc, hs, hq0, hle⟩ := val_le hg hch hcells hq ht0 ht1
  exact hle.trans (hB c hc hs hq0)

lemma F_bdd (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) {P0 : Pt} (hP0 : P0.lam = 0)
    (hl : ∀ c ∈ cells, lineBelow g c P0 = true) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    BddAbove ((fun q => val g q t) '' certFeasible g.p g.mu g.w g.beta g.x) ∧ F t ≤ P0.E := by
  have hB : ∀ c ∈ cells, c.skip = false → (g.q0 : ℝ) ≤ c.a →
      (c.c : ℝ) - g.w * c.a * (-Real.log t) ≤ P0.E := by
    intro c hc hs hq0
    have h := line_at hs (hl c hc)
    rw [hP0] at h; push_cast at h
    have : 0 ≤ (g.w : ℝ) * c.a * (-Real.log t) :=
      mul_nonneg (mul_nonneg hg.w0.le (hg.q00.le.trans hq0))
        (by linarith [Real.log_nonpos ht0.le ht1])
    linarith
  refine ⟨⟨P0.E, ?_⟩, F_le hg hch hcells ht0 ht1 hB⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨c, hc, hs, hq0, hle⟩ := val_le hg hch hcells hq ht0 ht1
  exact hle.trans (hB c hc hs hq0)

lemma F_integrable (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) {P0 : Pt} (hP0 : P0.lam = 0)
    (hl : ∀ c ∈ cells, lineBelow g c P0 = true) :
    IntervalIntegrable F volume 0 1 := by
  have hw := hg.w0
  have hmu0 : (0 : ℝ) < g.mu := hg.q00.trans hg.q0mu
  set m0 : ℝ := certM g.p g.mu g.w g.beta g.x g.mu
  let low : ℝ → ℝ := fun t => (g.mu * m0 + g.w * g.mu) + (g.w * g.mu) * Real.log t
  have hlow : ∀ t, 0 < t → t ≤ 1 → low t ≤ F t := by
    intro t ht0 ht1
    rw [F_eq]
    have := le_csSup (F_bdd hg hch hcells hP0 hl ht0 ht1).1 ⟨g.mu, (witness hg).1, rfl⟩
    refine le_trans (le_of_eq ?_) this
    simp only [low, val]; ring
  have hmono : MonotoneOn F (Ioc 0 1) := by
    intro t ht t' ht' htt'
    rw [F_eq, F_eq]
    apply csSup_le (img_nonempty hg t)
    rintro _ ⟨q, hq, rfl⟩
    refine le_trans ?_ (le_csSup (F_bdd hg hch hcells hP0 hl ht'.1 ht'.2).1 ⟨q, hq, rfl⟩)
    unfold val
    have : Real.log t ≤ Real.log t' := Real.log_le_log ht.1 htt'
    have : 0 ≤ (g.w : ℝ) * q := mul_nonneg hw.le hq.1.le
    nlinarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Integrable.mono' (g := fun t => |low t| + |(P0.E : ℝ)|) ?_ ?_ ?_
  · have h1 : IntervalIntegrable (fun t => |low t| + |(P0.E : ℝ)|) volume 0 1 :=
      (intervalIntegrable_aff 0 1 _ _).abs.add intervalIntegrable_const
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1
  · exact (aemeasurable_restrict_of_monotoneOn measurableSet_Ioc hmono).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have h1 := hlow t ht.1 ht.2
    have h2 := (F_bdd hg hch hcells hP0 hl ht.1 ht.2).2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (low t), abs_nonneg (P0.E : ℝ)]
    · linarith [le_abs_self (P0.E : ℝ), abs_nonneg (low t)]

lemma exp_neg_le_one {l : ℝ} (h : 0 ≤ l) : Real.exp (-l) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by linarith)

lemma int_le (hg : GlobFacts g) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true) (hint : IntervalIntegrable F volume 0 1) :
    ∀ (rest : List Pt) (P : Pt), (∀ c ∈ cells, ∀ Q ∈ P :: rest, lineBelow g c Q = true) →
      ptsOk (P :: rest) = true → (0 : ℝ) ≤ P.lam →
      ∫ t in (0 : ℝ)..Real.exp (-P.lam), F t ≤ intUB g (P :: rest) := by
  have hw := hg.w0
  intro rest
  induction rest with
  | nil =>
    intro P hl hok hP
    simp only [ptsOk] at hok
    obtain ⟨htlo, hthi⟩ := ptOk_spec hok
    set tN := Real.exp (-(P.lam : ℝ)) with htN
    have htN0 : 0 < tN := Real.exp_pos _
    have htN1 : tN ≤ 1 := exp_neg_le_one hP
    set σ : ℝ := g.w * g.q0
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (f := F)
      (g := fun t => ((P.E : ℝ) + σ * P.lam) + σ * Real.log t) htN0.le
      (hint.mono_set (sub01 le_rfl zero_le_one htN0.le htN1)) (intervalIntegrable_aff _ _ _ _)
      (by
        intro t ht
        have ht1 : t ≤ 1 := ht.2.le.trans htN1
        apply F_le hg hch hcells ht.1 ht1
        intro c hc hs hq0
        have h := line_at hs (hl c hc P List.mem_cons_self)
        have hlt : Real.log t ≤ -P.lam := by
          have := Real.log_le_log ht.1 ht.2.le
          rwa [htN, Real.log_exp] at this
        have : (g.w : ℝ) * g.q0 * (-Real.log t - P.lam) ≤ g.w * c.a * (-Real.log t - P.lam) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq0 hw.le) (by linarith)
        simp only [σ]; nlinarith)
    have e : ∫ t in (0 : ℝ)..tN, (((P.E : ℝ) + σ * P.lam) + σ * Real.log t) =
        tN * ((P.E : ℝ) - σ) := by
      rw [integral_aff, htN, Real.log_exp]; simp; ring
    rw [e] at hmono
    refine hmono.trans ?_
    simp only [intUB, tailUB]
    have := mulUB_spec (c := P.E - g.w * g.q0) htlo hthi
    push_cast at this ⊢
    exact this
  | cons P1 rest ih =>
    intro P hl hok hP
    simp only [ptsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hok0, hlt⟩, hok1⟩ := hok
    have hlt' : (P.lam : ℝ) < P1.lam := by exact_mod_cast hlt
    have hP1 : (0 : ℝ) ≤ P1.lam := hP.trans hlt'.le
    have IH := ih P1 (fun c hc Q hQ => hl c hc Q (List.mem_cons_of_mem _ hQ)) hok1 hP1
    obtain ⟨hlo0, hhi0⟩ := ptOk_spec hok0
    obtain ⟨hlo1, hhi1⟩ := ptOk_spec (ptsOk_head hok1)
    set t0 := Real.exp (-(P.lam : ℝ)) with ht0
    set t1 := Real.exp (-(P1.lam : ℝ)) with ht1
    have ht00 : 0 < t0 := Real.exp_pos _
    have ht10 : 0 < t1 := Real.exp_pos _
    have ht01 : t0 ≤ 1 := exp_neg_le_one hP
    have ht11 : t1 ≤ 1 := exp_neg_le_one hP1
    have ht10' : t1 ≤ t0 := Real.exp_le_exp.mpr (by linarith)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (sub01 le_rfl zero_le_one ht10.le ht11))
      (hint.mono_set (sub01 ht10.le ht11 ht00.le ht01))]
    simp only [intUB]
    rw [add_comm (segUB P P1)]
    push_cast
    apply add_le_add IH
    set m : ℝ := ((P1.E : ℝ) - P.E) / (P1.lam - P.lam) with hm
    have hseg := intervalIntegral.integral_mono_on (f := F)
      (g := fun t => ((P.E : ℝ) - m * P.lam) + (-m) * Real.log t) ht10'
      (hint.mono_set (sub01 ht10.le ht11 ht00.le ht01)) (intervalIntegrable_aff _ _ _ _)
      (by
        intro t ht
        have htp : 0 < t := ht10.trans_le ht.1
        apply F_le hg hch hcells htp (ht.2.trans ht01)
        intro c hc hs hq0
        have h0 := line_at hs (hl c hc P List.mem_cons_self)
        have h1 := line_at hs (hl c hc P1 (List.mem_cons_of_mem _ List.mem_cons_self))
        have hl0 : Real.log t ≤ -P.lam := by
          have := Real.log_le_log htp ht.2
          rwa [ht0, Real.log_exp] at this
        have hl1 : -(P1.lam : ℝ) ≤ Real.log t := by
          have := Real.log_le_log ht10 ht.1
          rwa [ht1, Real.log_exp] at this
        have := chord (l := -Real.log t) h0 h1 hlt' (by linarith) (by linarith)
        rw [← hm] at this
        linarith)
    refine hseg.trans ?_
    rw [integral_aff, ht0, ht1, Real.log_exp, Real.log_exp, ← ht0, ← ht1]
    have hE1 : (P1.E : ℝ) = P.E + m * (P1.lam - P.lam) := by
      rw [hm]; field_simp [(sub_pos.mpr hlt').ne']; ring
    have e : (P.E - m * P.lam) * (t0 - t1) + -m * (t0 * -P.lam - t1 * -P1.lam - t0 + t1) =
        t0 * (P.E + m) + t1 * (-(P1.E + m)) := by rw [hE1]; ring
    rw [e]
    simp only [segUB]; push_cast
    have a1 := mulUB_spec (c := P.E + (P1.E - P.E) / (P1.lam - P.lam)) hlo0 hhi0
    have a2 := mulUB_spec (c := -(P1.E + (P1.E - P.E) / (P1.lam - P.lam))) hlo1 hhi1
    push_cast at a1 a2
    rw [← hm] at a1 a2
    linarith

end main

theorem cert_neg_of_checks (g : Glob) (cells : List Cell) (P0 : Pt) (rest : List Pt)
    (hg : g.ok = true) (hch : chainOk g.q0 cells g.mu = true)
    (hcells : ∀ c ∈ cells, cellOkAny g c = true)
    (hl : ∀ c ∈ cells, ∀ Q ∈ P0 :: rest, lineBelow g c Q = true)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  have hgf := Glob.facts hg
  refine ⟨⟨_, (witness hgf).1⟩, ?_⟩
  have hint := F_integrable hgf hch hcells hP0 (fun c hc => hl c hc P0 List.mem_cons_self)
  have h := int_le hgf hch hcells hint rest P0 hl hpts (by rw [hP0]; simp)
  rw [hP0] at h
  simp only [Rat.cast_zero, neg_zero, Real.exp_zero] at h
  have hneg' : ((intUB g (P0 :: rest) : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  exact h.trans_lt hneg'
-- end Integral.lean copy

def cellFullAny (g : Glob) (pts : List Pt) (c : Cell) : Bool :=
  cellOkAny g c && pts.all (lineBelow g c)

theorem all_any_of_full {g : Glob} {K : ℕ} {pts : List Pt} {l : List CellD}
    (h : (l.map (mkCellD g K)).all (cellFull g pts) = true) :
    (l.map (mkCellD g K)).all (cellFullAny g pts) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  simp only [cellFull, cellFullAny, cellOkAny, Bool.and_eq_true, Bool.or_eq_true] at this ⊢
  exact ⟨Or.inl this.1, this.2⟩

theorem all_any_of_fullI {g : Glob} {K : ℕ} {pts : List Pt} {l : List CellD}
    (h : (l.map (mkCellD g K)).all (cellFullI g pts) = true) :
    (l.map (mkCellD g K)).all (cellFullAny g pts) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  simp only [cellFullI, cellFullAny, cellOkAny, Bool.and_eq_true, Bool.or_eq_true] at this ⊢
  exact ⟨Or.inr this.1, this.2⟩

theorem all_app_okAny (g : Glob) (K : ℕ) (pts : List Pt) {l1 l2 : List CellD}
    (h1 : (l1.map (mkCellD g K)).all (cellFullAny g pts) = true)
    (h2 : (l2.map (mkCellD g K)).all (cellFullAny g pts) = true) :
    ((l1 ++ l2).map (mkCellD g K)).all (cellFullAny g pts) = true := by
  rw [List.map_append, List.all_append, h1, h2]; rfl

theorem cert_neg_of_dataAny (g : Glob) (K : ℕ) (pts : List Pt) (D : List CellD)
    (hg : g.ok = true) (hch : chainOk g.q0 (D.map (mkCellD g K)) g.mu = true)
    (hall : (D.map (mkCellD g K)).all (cellFullAny g pts) = true)
    {P0 : Pt} {rest : List Pt} (hpts0 : pts = P0 :: rest)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  subst hpts0
  have hmem : ∀ c ∈ D.map (mkCellD g K), cellFullAny g (P0 :: rest) c = true :=
    fun c hc => List.all_eq_true.mp hall c hc
  refine cert_neg_of_checks g (D.map (mkCellD g K)) P0 rest hg hch ?_ ?_ hP0 hpts hneg
  · intro c hc
    have := hmem c hc
    simp only [cellFullAny, Bool.and_eq_true] at this
    exact this.1
  · intro c hc Q hQ
    have := hmem c hc
    simp only [cellFullAny, Bool.and_eq_true] at this
    exact List.all_eq_true.mp this.2 Q hQ

theorem cert_neg_of_data_ksAny (g : Glob) (K : ℕ) (pts : List Pt) (D : List CellD)
    (hg : g.ok = true) (hks : D.map (·.k) = List.range' 0 K)
    (h0 : gridPt g K 0 = g.q0) (hK : gridPt g K K = g.mu)
    (hall : (D.map (mkCellD g K)).all (cellFullAny g pts) = true)
    {P0 : Pt} {rest : List Pt} (hpts0 : pts = P0 :: rest)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  have hch := chainOk_of_ks g K D 0 K hks
  rw [h0, zero_add, hK] at hch
  exact cert_neg_of_dataAny g K pts D hg hch hall hpts0 hP0 hpts hneg

end DiagRamsey.SharpCert.IExp
