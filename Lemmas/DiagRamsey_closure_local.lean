import Lemmas.DiagRamsey_closure_basic

/-! The finite local consequence of the sharp envelope (Lemma 1 of
`proofs/DiagRamsey_positive_weight_finite_host_closure.md`), with the envelope's local conclusion as a hypothesis. -/

set_option linter.unusedSectionVars false

namespace DiagRamsey.ClosureEnv

section Local

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pot_beta (G : SimpleGraph V) (X Y : Finset V) (c w r β : ℝ) (hβ : β ≠ 0) (hr : r ≠ 0) :
    potential G X Y c w r (β * r) =
      (X.card : ℝ) ^ w * (Y.card : ℝ) * (colMomentSum G X Y c (β * r) / (Y.card : ℝ)) ^ (1 / β) := by
  rw [potential_eq, show r / (β * r) = 1 / β by field_simp]

lemma rpow_compare (a M S a' M' S' K w β : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hM : 0 < M)
    (hM' : 0 < M') (hS : 0 ≤ S) (hS' : 0 ≤ S') (hK : 0 ≤ K)
    (h : a' ^ w * M' * (S' / M') ^ (1 / β) < K * (a ^ w * M * (S / M) ^ (1 / β))) :
    a' ^ (w * β) * M' ^ β * (S' / M') < K ^ β * (a ^ (w * β) * M ^ β * (S / M)) := by
  have h0 : 0 ≤ a' ^ w * M' * (S' / M') ^ (1 / β) := by positivity
  have h1 := Real.rpow_lt_rpow h0 h hβ
  have e1 : (a' ^ w * M' * (S' / M') ^ (1 / β)) ^ β = a' ^ (w * β) * M' ^ β * (S' / M') := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha', ← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
  have e2 : (K * (a ^ w * M * (S / M) ^ (1 / β))) ^ β = K ^ β * (a ^ (w * β) * M ^ β * (S / M)) := by
    rw [Real.mul_rpow hK (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha, ← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
  rw [e1, e2] at h1
  exact h1

open Classical in
lemma card_mul_colDensity (G : SimpleGraph V) (A : Finset V) (y : V) :
    (A.card : ℝ) * colDensity G A y = ∑ u ∈ A, if G.Adj u y then (1 : ℝ) else 0 := by
  classical
  unfold colDensity
  rw [Finset.sum_boole]
  rcases A.eq_empty_or_nonempty with hA | hA
  · simp [hA]
  · rw [mul_div_cancel₀ _ (by exact_mod_cast hA.card_pos.ne')]

/-- `X = {i} ⊔ B_i ⊔ R_i` for `i ∈ X`. -/
lemma sum_split (G : SimpleGraph V) (X : Finset V) (i : V) (hi : i ∈ X) (f : V → ℝ) :
    ∑ u ∈ X, f u = f i + ∑ u ∈ graphNbhd Gᶜ X i, f u + ∑ u ∈ redNbhd G X i, f u := by
  classical
  have h1 : (X.erase i).filter (fun u => G.Adj i u) = redNbhd G X i := by
    ext u
    simp only [redNbhd, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨(G.ne_of_adj h').symm, h⟩, h'⟩
  have h2 : (X.erase i).filter (fun u => ¬ G.Adj i u) = graphNbhd Gᶜ X i := by
    ext u
    simp only [graphNbhd, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨⟨hne, h⟩, h'⟩; exact ⟨h, fun e => hne e.symm, h'⟩
    · rintro ⟨h, hne, h'⟩; exact ⟨⟨fun e => hne e.symm, h⟩, h'⟩
  rw [← Finset.add_sum_erase X f hi,
    ← Finset.sum_filter_add_sum_filter_not (X.erase i) (fun u => G.Adj i u), h1, h2]
  ring

/-- Row maximality forces every row to have a red neighbour in `Y` (remove a row with none). -/
lemma rowDensity_pos_of_rowMax (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hc : 0 ≤ c)
    (hw : 0 < w) (hwr : w < r) (hs : 0 < s) (hY : Y.Nonempty) (hH : 0 < momentNorm G X Y c s)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s)
    (v : V) (hv : v ∈ X) (hN : 2 ≤ X.card) : 0 < rowDensity G v Y := by
  classical
  have hM0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  by_contra hneg
  have hnone : ∀ y ∈ Y, ¬ G.Adj v y := by
    intro y hy hadj
    apply hneg
    unfold rowDensity
    apply div_pos _ hM0
    have : 0 < (Y.filter (fun y => G.Adj v y)).card :=
      Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hadj⟩⟩
    exact_mod_cast this
  have hN2 : (2 : ℝ) ≤ X.card := by exact_mod_cast hN
  have hX'card : ((X.erase v).card : ℝ) = (X.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hv, Nat.cast_sub (by omega), Nat.cast_one]
  have hX'ne : (X.erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
  have hN1 : (0 : ℝ) < (X.card : ℝ) - 1 := by linarith
  have hlam1 : 1 < (X.card : ℝ) / ((X.card : ℝ) - 1) := by
    rw [one_lt_div hN1]; linarith
  have hlam0 : 0 < (X.card : ℝ) / ((X.card : ℝ) - 1) := by linarith
  have hcol : ∀ y ∈ Y, colDensity G (X.erase v) y =
      (X.card : ℝ) / ((X.card : ℝ) - 1) * colDensity G X y := by
    intro y hy
    unfold colDensity
    have : (X.erase v).filter (fun u => G.Adj u y) = X.filter (fun u => G.Adj u y) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, h1⟩, h2⟩
        rintro rfl; exact hnone y hy h2
    rw [this, hX'card]
    field_simp
  have hterm : ∀ y ∈ Y, ((X.card : ℝ) / ((X.card : ℝ) - 1)) ^ s * (max (colDensity G X y - c) 0) ^ s ≤
      (max (colDensity G (X.erase v) y - c) 0) ^ s := by
    intro y hy
    rw [← Real.mul_rpow hlam0.le (le_max_right _ _)]
    apply Real.rpow_le_rpow (mul_nonneg hlam0.le (le_max_right _ _)) _ hs.le
    rw [hcol y hy]
    rcases le_total (colDensity G X y - c) 0 with h | h
    · rw [max_eq_right h, mul_zero]; exact le_max_right _ _
    · rw [max_eq_left h]
      apply le_max_of_le_left
      nlinarith
  have hsum : ((X.card : ℝ) / ((X.card : ℝ) - 1)) ^ s * colMomentSum G X Y c s ≤
      colMomentSum G (X.erase v) Y c s := by
    unfold colMomentSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hS0 := colMomentSum_nonneg G X Y c s
  have hSM : 0 < colMomentSum G X Y c s / (Y.card : ℝ) := by
    rcases (div_nonneg hS0 hM0.le).lt_or_eq with h | h
    · exact h
    · rw [momentNorm_eq, ← h, Real.zero_rpow (by positivity)] at hH; exact absurd hH (lt_irrefl 0)
  set lam := (X.card : ℝ) / ((X.card : ℝ) - 1) with hlam
  have hP' : ((X.card : ℝ) - 1) ^ w * (Y.card : ℝ) * (lam ^ r * (colMomentSum G X Y c s / Y.card) ^ (r / s))
      ≤ potential G (X.erase v) Y c w r s := by
    rw [potential_eq, hX'card]
    have e : lam ^ r * (colMomentSum G X Y c s / Y.card) ^ (r / s) =
        (lam ^ s * colMomentSum G X Y c s / Y.card) ^ (r / s) := by
      rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hlam0.le _) hSM.le, ← Real.rpow_mul hlam0.le,
        show s * (r / s) = r by field_simp]
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hN1.le _) hM0.le)
    apply Real.rpow_le_rpow (div_nonneg (mul_nonneg (Real.rpow_nonneg hlam0.le _) hS0) hM0.le) _
      (div_nonneg (by linarith) hs.le)
    exact div_le_div_of_nonneg_right hsum hM0.le
  have key : (X.card : ℝ) ^ w < ((X.card : ℝ) - 1) ^ w * lam ^ r := by
    have e1 : lam ^ r = lam ^ w * lam ^ (r - w) := by
      rw [← Real.rpow_add hlam0]; congr 1; ring
    have e2 : ((X.card : ℝ) - 1) ^ w * lam ^ w = (X.card : ℝ) ^ w := by
      rw [← Real.mul_rpow hN1.le hlam0.le, hlam]; congr 1; field_simp
    have e3 : 1 < lam ^ (r - w) := Real.one_lt_rpow hlam1 (by linarith)
    have hNw : 0 < (X.card : ℝ) ^ w := by positivity
    rw [e1, ← mul_assoc, e2]
    nlinarith
  have hlt : potential G X Y c w r s < potential G (X.erase v) Y c w r s := by
    rw [potential_eq]
    refine lt_of_lt_of_le ?_ hP'
    have hpos : 0 < (Y.card : ℝ) * (colMomentSum G X Y c s / Y.card) ^ (r / s) :=
      mul_pos hM0 (Real.rpow_pos_of_pos hSM _)
    nlinarith
  exact absurd (hrow _ (Finset.erase_subset v X) hX'ne) (not_le.mpr hlt)


lemma blue_failure (G : SimpleGraph V) (X Y : Finset V) (c μ w β r : ℝ) (hβ0 : 0 < β) (hr0 : 0 < r)
    (hμ0 : 0 < μ) (hX : X.Nonempty) (hY : Y.Nonempty) (i : V) (hq : 0 < graphFrac Gᶜ X i)
    (h : potential G (graphNbhd Gᶜ X i) Y c w r (β * r) < μ ^ w * potential G X Y c w r (β * r)) :
    SharpBlueFailure G Gᶜ X Y c μ w β (β * r) i := by
  have hN0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hM0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hS0 := colMomentSum_nonneg G X Y c (β * r)
  have hq' : graphFrac Gᶜ X i = ((graphNbhd Gᶜ X i).card : ℝ) / X.card := rfl
  have hB0 : 0 < ((graphNbhd Gᶜ X i).card : ℝ) := by
    rw [hq'] at hq; exact (div_pos_iff_of_pos_right hN0).mp hq
  rw [pot_beta G X Y c w r β hβ0.ne' hr0.ne', pot_beta G _ Y c w r β hβ0.ne' hr0.ne'] at h
  have h2 := rpow_compare _ _ _ _ _ _ _ w β hβ0 hN0.le hB0.le hM0 hM0 hS0
    (colMomentSum_nonneg G _ Y c (β * r)) (Real.rpow_nonneg hμ0.le w) h
  rw [← Real.rpow_mul hμ0.le] at h2
  unfold SharpBlueFailure
  have e0 : μ / (((graphNbhd Gᶜ X i).card : ℝ) / X.card) = μ * X.card / (graphNbhd Gᶜ X i).card := by
    rw [div_div_eq_mul_div]
  rw [hq', e0, Real.div_rpow (mul_nonneg hμ0.le hN0.le) hB0.le, Real.mul_rpow hμ0.le hN0.le,
    div_mul_eq_mul_div, lt_div_iff₀ (Real.rpow_pos_of_pos hB0 _)]
  have hMβ : 0 < (Y.card : ℝ) ^ β / Y.card := div_pos (Real.rpow_pos_of_pos hM0 _) hM0
  have e1 : ((graphNbhd Gᶜ X i).card : ℝ) ^ (w * β) * (Y.card : ℝ) ^ β *
      (colMomentSum G (graphNbhd Gᶜ X i) Y c (β * r) / Y.card) =
      ((Y.card : ℝ) ^ β / Y.card) *
        (colMomentSum G (graphNbhd Gᶜ X i) Y c (β * r) * ((graphNbhd Gᶜ X i).card : ℝ) ^ (w * β)) := by
    ring
  have e2 : μ ^ (w * β) * ((X.card : ℝ) ^ (w * β) * (Y.card : ℝ) ^ β *
      (colMomentSum G X Y c (β * r) / Y.card)) =
      ((Y.card : ℝ) ^ β / Y.card) *
        (μ ^ (w * β) * (X.card : ℝ) ^ (w * β) * colMomentSum G X Y c (β * r)) := by ring
  rw [e1, e2] at h2
  exact lt_of_mul_lt_mul_left h2 hMβ.le

/-- The exact red identity: `a (ρ_y - c') ≥ (1-q)(g_y - c) - q (b_y - g_y)` on `Y_i`. -/
lemma red_pointwise (N Bc Rc g b ρ q a c Δ : ℝ) (hN0 : 0 < N) (hpart : N = 1 + Bc + Rc)
    (hqN : q * N = Bc) (haN : a * N = Rc) (hcount : N * g = 1 + Bc * b + Rc * ρ)
    (hRΔ : 1 - c ≤ Rc * Δ) :
    (1 - q) * (g - c) - q * (b - g) ≤ a * (ρ - (c - Δ)) := by
  apply le_of_mul_le_mul_right _ hN0
  have e1 : ((1 - q) * (g - c) - q * (b - g)) * N = N * g - N * c + (q * N) * c - (q * N) * b := by ring
  have e2 : a * (ρ - (c - Δ)) * N = (a * N) * ρ - (a * N) * c + (a * N) * Δ := by ring
  have hNc : N * c = c + Bc * c + Rc * c := by linear_combination c * hpart
  rw [e1, e2, hqN, haN]
  linarith

lemma red_failure (G : SimpleGraph V) (X Y : Finset V) (c Δ cap w β r x : ℝ) (hw : 0 < w)
    (hβ0 : 0 < β) (hwr : w < r) (hx0 : 0 < x) (hX : X.Nonempty) (hY : Y.Nonempty) (hc0 : 0 ≤ c)
    (hΔ0 : 0 ≤ Δ) (hΔ : 1 - c ≤ ((X.card : ℝ) * (1 - cap) - 1) * Δ)
    (hNcap : 0 < (X.card : ℝ) * (1 - cap) - 1) (hN2 : 2 ≤ X.card)
    (hH : 0 < momentNorm G X Y c (β * r))
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r (β * r) ≤ potential G X Y c w r (β * r))
    (i : V) (hiX : i ∈ X) (hqi : graphFrac Gᶜ X i ≤ cap)
    (h : potential G (redNbhd G X i) (redNbhd G Y i) (c - Δ) w r (β * r) <
      x * potential G X Y c w r (β * r)) :
    SharpRedFailure G Gᶜ X Y c w β (β * r) x i := by
  classical
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < β * r := mul_pos hβ0 hr0
  have hN0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hM0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hS0 := colMomentSum_nonneg G X Y c (β * r)
  have hBc : graphFrac Gᶜ X i * X.card = ((graphNbhd Gᶜ X i).card : ℝ) := by
    unfold graphFrac; exact div_mul_cancel₀ _ hN0.ne'
  have hpart : (X.card : ℝ) = 1 + (graphNbhd Gᶜ X i).card + (redNbhd G X i).card := by
    have := sum_split G X i hiX (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  have hqN : graphFrac Gᶜ X i * X.card ≤ cap * X.card := mul_le_mul_of_nonneg_right hqi hN0.le
  have hRlow : (X.card : ℝ) * (1 - cap) - 1 ≤ (redNbhd G X i).card := by
    have : (X.card : ℝ) * (1 - cap) - 1 = X.card - 1 - cap * X.card := by ring
    rw [this]; linarith
  have hR0 : (0 : ℝ) < (redNbhd G X i).card := by linarith
  have hRΔ : 1 - c ≤ ((redNbhd G X i).card : ℝ) * Δ :=
    hΔ.trans (mul_le_mul_of_nonneg_right hRlow hΔ0)
  have hπ := rowDensity_pos_of_rowMax G X Y c w r (β * r) hc0 hw hwr hs0 hY hH hrow i hiX hN2
  have hπdef : rowDensity G i Y = ((redNbhd G Y i).card : ℝ) / Y.card := rfl
  have hYi : (0 : ℝ) < (redNbhd G Y i).card := by
    rw [hπdef] at hπ; exact (div_pos_iff_of_pos_right hM0).mp hπ
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((redNbhd G X i).card : ℝ) / X.card := ⟨_, rfl⟩
  have haN : a * X.card = (redNbhd G X i).card := by rw [ha]; exact div_mul_cancel₀ _ hN0.ne'
  have ha0 : 0 < a := by rw [ha]; exact div_pos hR0 hN0
  have ha1 : a ≤ 1 - graphFrac Gᶜ X i := by
    have : a * X.card ≤ (1 - graphFrac Gᶜ X i) * X.card := by
      rw [haN, sub_mul, one_mul, hBc]; linarith
    exact le_of_mul_le_mul_right this hN0
  have hpt : ∀ y ∈ redNbhd G Y i,
      (max ((1 - graphFrac Gᶜ X i) * (colDensity G X y - c) -
        graphFrac Gᶜ X i * (colDensity G (graphNbhd Gᶜ X i) y - colDensity G X y)) 0) ^ (β * r) ≤
      a ^ (β * r) * (max (colDensity G (redNbhd G X i) y - (c - Δ)) 0) ^ (β * r) := by
    intro y hy
    have hadj : G.Adj i y := (Finset.mem_filter.mp hy).2
    have hcount : (X.card : ℝ) * colDensity G X y = 1 +
        ((graphNbhd Gᶜ X i).card : ℝ) * colDensity G (graphNbhd Gᶜ X i) y +
        ((redNbhd G X i).card : ℝ) * colDensity G (redNbhd G X i) y := by
      rw [card_mul_colDensity, card_mul_colDensity, card_mul_colDensity,
        sum_split G X i hiX, if_pos hadj]
    have hz := red_pointwise _ _ _ _ _ _ _ _ c Δ hN0 hpart hBc haN hcount hRΔ
    have hm : max ((1 - graphFrac Gᶜ X i) * (colDensity G X y - c) -
        graphFrac Gᶜ X i * (colDensity G (graphNbhd Gᶜ X i) y - colDensity G X y)) 0 ≤
        a * max (colDensity G (redNbhd G X i) y - (c - Δ)) 0 :=
      max_le (hz.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ha0.le))
        (mul_nonneg ha0.le (le_max_right _ _))
    rw [← Real.mul_rpow ha0.le (le_max_right _ _)]
    exact Real.rpow_le_rpow (le_max_right _ _) hm hs0.le
  have hL := Finset.sum_le_sum hpt
  rw [← Finset.mul_sum] at hL
  change _ ≤ a ^ (β * r) * colMomentSum G (redNbhd G X i) (redNbhd G Y i) (c - Δ) (β * r) at hL
  rw [pot_beta G X Y c w r β hβ0.ne' hr0.ne', pot_beta G _ _ (c - Δ) w r β hβ0.ne' hr0.ne'] at h
  have h2 := rpow_compare _ _ _ _ _ _ _ w β hβ0 hN0.le hR0.le hM0 hYi hS0
    (colMomentSum_nonneg G _ _ (c - Δ) (β * r)) hx0.le h
  rw [← haN, Real.mul_rpow ha0.le hN0.le] at h2
  obtain ⟨S', hS'⟩ : ∃ S', S' = colMomentSum G (redNbhd G X i) (redNbhd G Y i) (c - Δ) (β * r) :=
    ⟨_, rfl⟩
  rw [← hS'] at h2 hL
  obtain ⟨Yc, hYc⟩ : ∃ Yc : ℝ, Yc = ((redNbhd G Y i).card : ℝ) := ⟨_, rfl⟩
  rw [← hYc] at h2 hπdef hYi
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (Y.card : ℝ) := ⟨_, rfl⟩
  rw [← hM] at h2 hπdef hM0
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = colMomentSum G X Y c (β * r) := ⟨_, rfl⟩
  rw [← hSd] at h2 hS0
  obtain ⟨Nw, hNw⟩ : ∃ Nw : ℝ, Nw = (X.card : ℝ) ^ (w * β) := ⟨_, rfl⟩
  rw [← hNw] at h2
  have hNw0 : 0 < Nw := by rw [hNw]; exact Real.rpow_pos_of_pos hN0 _
  have hYiβ : 0 < Yc ^ β := Real.rpow_pos_of_pos hYi _
  have hMβ : 0 < M ^ β := Real.rpow_pos_of_pos hM0 _
  have hπβ : rowDensity G i Y ^ (1 - β) = Yc / M * (M ^ β / Yc ^ β) := by
    rw [Real.rpow_sub hπ, Real.rpow_one, hπdef, Real.div_rpow hYi.le hM0.le]
    field_simp
  have hfac : 0 < Nw * Yc ^ β / Yc := div_pos (mul_pos hNw0 hYiβ) hYi
  have key2 : a ^ (w * β) * S' < x ^ β * rowDensity G i Y ^ (1 - β) * S := by
    apply lt_of_mul_lt_mul_left _ hfac.le
    calc Nw * Yc ^ β / Yc * (a ^ (w * β) * S')
        = a ^ (w * β) * Nw * Yc ^ β * (S' / Yc) := by ring
      _ < x ^ β * (Nw * M ^ β * (S / M)) := h2
      _ = Nw * Yc ^ β / Yc * (x ^ β * rowDensity G i Y ^ (1 - β) * S) := by
        rw [hπβ]; field_simp
  have hexp : 0 < β * r - w * β := by nlinarith
  have hsplit : a ^ (β * r) = a ^ (β * r - w * β) * a ^ (w * β) := by
    rw [← Real.rpow_add ha0]; congr 1; ring
  have hmono : a ^ (β * r - w * β) ≤ (1 - graphFrac Gᶜ X i) ^ (β * r - w * β) :=
    Real.rpow_le_rpow ha0.le ha1 hexp.le
  have hapos : 0 < a ^ (β * r - w * β) := Real.rpow_pos_of_pos ha0 _
  have hQ0 : 0 ≤ x ^ β * rowDensity G i Y ^ (1 - β) * S :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hπ.le _)) hS0
  unfold SharpRedFailure
  rw [← hSd]
  calc ∑ y ∈ Y.filter (fun y => G.Adj i y),
        (max ((1 - graphFrac Gᶜ X i) * (colDensity G X y - c) -
          graphFrac Gᶜ X i * (colDensity G (graphNbhd Gᶜ X i) y - colDensity G X y)) 0) ^ (β * r)
      ≤ a ^ (β * r) * S' := hL
    _ = a ^ (β * r - w * β) * (a ^ (w * β) * S') := by rw [hsplit]; ring
    _ < a ^ (β * r - w * β) * (x ^ β * rowDensity G i Y ^ (1 - β) * S) :=
      mul_lt_mul_of_pos_left key2 hapos
    _ ≤ (1 - graphFrac Gᶜ X i) ^ (β * r - w * β) * (x ^ β * rowDensity G i Y ^ (1 - β) * S) :=
      mul_le_mul_of_nonneg_right hmono hQ0
    _ = _ := by ring

/-- Lemma 1: the finite local consequence of the sharp envelope. If both the red and the blue alternative fail
at every row, the configuration (with the blue graph `Gᶜ` as `B` and the good rows `q_v ≤ cap`) contradicts the
envelope's local conclusion `hloc`. -/
theorem local_step (p μ w β x η τ ζ R : ℝ)
    (hw : 0 < w) (hβ0 : 0 < β) (hx0 : 0 < x) (hμ0 : 0 < μ)
    (hloc : ∀ r : ℝ, R ≤ r →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G B : SimpleGraph V) (X Y : Finset V) (c : ℝ),
        X.Nonempty → Y.Nonempty → Disjoint X Y → |c - p| ≤ η →
        (∀ y ∈ Y, c < colDensity G X y) →
        RowColMaximal G X Y c w r (β * r) →
        (∀ i ∈ X, 0 < graphFrac B X i → SharpBlueFailure G B X Y c μ w β (β * r) i) →
        ∀ Xg : Finset V, Xg ⊆ X → (X.card : ℝ) - (Xg.card : ℝ) ≤ ζ * (X.card : ℝ) →
        (∀ i ∈ Xg, graphFrac B X i ≤ μ + τ ∧ SharpRedFailure G B X Y c w β (β * r) x i) →
        False)
    (r : ℝ) (hrR : R ≤ r) (hwr : w < r) (hβr : β * r < r)
    {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) (X Y : Finset W) (c Δ cap : ℝ)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y) (hcp : |c - p| ≤ η) (hc0 : 0 ≤ c)
    (hcap0 : 0 ≤ cap) (hcapτ : cap ≤ μ + τ) (hΔ0 : 0 ≤ Δ)
    (hNcap : 0 < (X.card : ℝ) * (1 - cap) - 1) (hΔ : 1 - c ≤ ((X.card : ℝ) * (1 - cap) - 1) * Δ)
    (hH : 0 < momentNorm G X Y c (β * r)) (hmax : RowColMaximal G X Y c w r (β * r))
    (hexc : (X.card : ℝ) - ((X.filter (fun v => graphFrac Gᶜ X v ≤ cap)).card : ℝ) ≤
      ζ * (X.card : ℝ)) :
    ∃ v ∈ X, (graphFrac Gᶜ X v ≤ cap ∧
        x * potential G X Y c w r (β * r) ≤
          potential G (redNbhd G X v) (redNbhd G Y v) (c - Δ) w r (β * r)) ∨
      μ ^ w * potential G X Y c w r (β * r) ≤ potential G (graphNbhd Gᶜ X v) Y c w r (β * r) := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_le] at hcon
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < β * r := mul_pos hβ0 hr0
  have hN1 : (1 : ℝ) < X.card := by
    have : (X.card : ℝ) * (1 - cap) ≤ X.card := by
      have := Nat.cast_nonneg (α := ℝ) X.card
      nlinarith
    linarith
  have hN2 : 2 ≤ X.card := by
    have : 1 < X.card := by exact_mod_cast hN1
    omega
  refine hloc r hrR W G Gᶜ X Y c hX hY hXY hcp ?_ hmax ?_ (X.filter (fun v => graphFrac Gᶜ X v ≤ cap))
    (Finset.filter_subset _ _) hexc ?_
  · intro y hy
    have h1 := wgp_col_lower G X Y c w r (β * r) hs0 hβr hX hY hH hmax.2 y hy
    have h2 : 0 < (1 - β * r / r) ^ (1 / (β * r)) * momentNorm G X Y c (β * r) := by
      apply mul_pos (Real.rpow_pos_of_pos _ _) hH
      rw [sub_pos, div_lt_one hr0]; exact hβr
    linarith
  · intro i hi hq
    exact blue_failure G X Y c μ w β r hβ0 hr0 hμ0 hX hY i hq (hcon i hi).2
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiX, hqi⟩ := hi
    exact ⟨hqi.trans hcapτ, red_failure G X Y c Δ cap w β r x hw hβ0 hwr hx0 hX hY hc0 hΔ0 hΔ hNcap hN2
      hH hmax.1 i hiX hqi ((hcon i hiX).1 hqi)⟩

end Local

end DiagRamsey.ClosureEnv
