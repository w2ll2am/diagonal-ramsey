import Lemmas.DiagRamsey_closure_local

/-! The strengthened induction (I_n) of `proofs/DiagRamsey_positive_weight_finite_host_closure.md` §4, with all
constants as parameters and their required properties as hypotheses. `lam`, `yy` are the proof's `λ`, `y`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DiagRamsey.ClosureEnv

/-- The induction threshold `C^(w+1) λ^(-k) y^(-ℓ) μ^(-wt)`. -/
noncomputable def Thr (C w lam yy μ : ℝ) (ℓ k t : ℕ) : ℝ :=
  C ^ (w + 1) / (lam ^ k * yy ^ ℓ * (μ ^ w) ^ t)

/-- The statement (I_n). -/
def IndHyp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C w lam yy μ p δ r β : ℝ)
    (ℓ n : ℕ) : Prop :=
  ∀ k t : ℕ, k + t = n → 1 ≤ k → 1 ≤ t → ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y →
    Thr C w lam yy μ ℓ k t ≤ potential G X Y (p - δ / (n : ℝ)) w r (β * r) →
    HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ

lemma Thr_pos (C w lam yy μ : ℝ) (ℓ k t : ℕ) (hC : 0 < C) (hlam : 0 < lam) (hyy : 0 < yy) (hμ : 0 < μ) :
    0 < Thr C w lam yy μ ℓ k t := by
  unfold Thr; positivity

lemma Thr_blue (C w lam yy μ : ℝ) (ℓ k t b : ℕ) (hbt : b ≤ t) (hlam : 0 < lam) (hyy : 0 < yy)
    (hμ : 0 < μ) :
    Thr C w lam yy μ ℓ k (t - b) = Thr C w lam yy μ ℓ k t * (μ ^ w) ^ b := by
  unfold Thr
  have hμw : 0 < μ ^ w := Real.rpow_pos_of_pos hμ w
  have e : (μ ^ w) ^ t = (μ ^ w) ^ (t - b) * (μ ^ w) ^ b := by rw [← pow_add, Nat.sub_add_cancel hbt]
  rw [e]
  field_simp

lemma Thr_red (C w lam yy μ : ℝ) (ℓ k t : ℕ) (hk : 1 ≤ k) (hlam : 0 < lam) (hyy : 0 < yy)
    (hμ : 0 < μ) :
    Thr C w lam yy μ ℓ (k - 1) t = Thr C w lam yy μ ℓ k t * lam := by
  unfold Thr
  have hμw : 0 < μ ^ w := Real.rpow_pos_of_pos hμ w
  have e : lam ^ k = lam ^ (k - 1) * lam := by rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [e]
  field_simp

section Steps

variable {V : Type} [Fintype V] [DecidableEq V]

lemma blueNbhd_eq (G : SimpleGraph V) (X : Finset V) (v : V) : blueNbhd G X v = graphNbhd Gᶜ X v := by
  ext u
  simp only [blueNbhd, graphNbhd, Finset.mem_filter, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨h, hne, h'⟩; exact ⟨h, fun e => hne e.symm, fun a => h' a.symm⟩
  · rintro ⟨h, hne, h'⟩; exact ⟨h, fun e => hne e.symm, fun a => h' a.symm⟩

/-- Failure of the Y-stop forces `|X| > e^{a(n+ℓ)}` (inequality (EXP)). -/
lemma size_lemma (C w lam yy μ xhat yhat a N M : ℝ) (ℓ k t : ℕ) (hC : 1 ≤ C) (hw : 0 < w)
    (hlam : 0 < lam) (hyy : 0 < yy) (hμ0 : 0 < μ) (hxh : 0 < xhat) (hyh : 0 < yhat) (hN : 0 < N)
    (hM : 0 < M) (hax : a * w ≤ Real.log (xhat / lam)) (hay : a * w ≤ Real.log (yhat / yy))
    (haμ : a ≤ Real.log (1 / μ))
    (h1 : Thr C w lam yy μ ℓ k t ≤ N ^ w * M) (h2 : M < C / (xhat ^ k * yhat ^ ℓ)) :
    Real.exp (a * (((k + t : ℕ) : ℝ) + ℓ)) < N := by
  have hC0 : 0 < C := by linarith
  have hNw : 0 < N ^ w := Real.rpow_pos_of_pos hN w
  have h3 : Thr C w lam yy μ ℓ k t < N ^ w * (C / (xhat ^ k * yhat ^ ℓ)) :=
    lt_of_le_of_lt h1 (mul_lt_mul_of_pos_left h2 hNw)
  have hT0 := Thr_pos C w lam yy μ ℓ k t hC0 hlam hyy hμ0
  have h4 := Real.log_lt_log hT0 h3
  unfold Thr at h4
  have hμw : 0 < μ ^ w := Real.rpow_pos_of_pos hμ0 w
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hC0, Real.log_rpow hN, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_rpow hμ0] at h4
  rw [Real.log_div hxh.ne' hlam.ne'] at hax
  rw [Real.log_div hyh.ne' hyy.ne'] at hay
  rw [one_div, Real.log_inv] at haμ
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hl0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have key : w * (a * (((k + t : ℕ) : ℝ) + ℓ)) < w * Real.log N := by
    push_cast
    have e1 := mul_le_mul_of_nonneg_left hax hk0
    have e2 := mul_le_mul_of_nonneg_left hay hl0
    have e3 := mul_le_mul_of_nonneg_left haμ (mul_nonneg hw.le ht0)
    have e4 := mul_nonneg hw.le hlogC
    linarith
  have key2 : a * (((k + t : ℕ) : ℝ) + ℓ) < Real.log N := lt_of_mul_lt_mul_left key hw.le
  exact (Real.lt_log_iff_exp_lt hN).mp key2

/-- Book case of the inductive step. -/
lemma book_step (G : SimpleGraph V) (C w lam yy μ p δ r β θ cap D : ℝ) (ℓ n k t b m : ℕ)
    (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hwr : w < r) (hs1 : 1 < β * r) (hμ0 : 0 < μ)
    (hθ0 : 0 < θ) (hθcap : θ < cap) (hcap1 : cap < 1) (hδ0 : 0 < δ) (hC0 : 0 < C) (hlam : 0 < lam)
    (hyy : 0 < yy)
    (hDr : w / (r - w) + 1 - (1 - β) ^ (1 / (β * r)) ≤ D) (hD4 : D ≤ 1 / 4)
    (hb1 : 1 ≤ b) (hbm : b ≤ m) (hbmh : (b : ℝ) / m ≤ (cap - θ - D) / 2) (hh : 0 < cap - θ - D)
    (hbook : (μ ^ w) ^ b ≤ (θ ^ w) ^ b * (δ / (n : ℝ) ^ 2) ^ r / 2 ^ w)
    (hkt : k + t = n) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (X Y : Finset V) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hH : 0 < momentNorm G X Y (p - δ / n) (β * r)) (hmax : RowColMaximal G X Y (p - δ / n) w r (β * r))
    (hT : Thr C w lam yy μ ℓ k t ≤ (X.card : ℝ) ^ w * (Y.card : ℝ))
    (hm4 : 4 * (m : ℝ) ≤ X.card) (hmh : 2 * (m : ℝ) / (cap - θ - D) ≤ X.card)
    (hW : ramseyNumber k m ≤ (X.filter (fun v => cap * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ))).card)
    (IH : ∀ n' < n, IndHyp G C w lam yy μ p δ r β ℓ n') :
    HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ := by
  classical
  have hr0 : 0 < r := by linarith
  have hN0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hM0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨hwg1, hwg2⟩ := cl_weighted_good_pages G X Y w β r (p - δ / n) 0 hw hβ0 hβ1 hwr hs1 le_rfl
    hX hY hXY hH hmax
  set P := X.filter (fun v => p - δ / n - 0 ≤ rowDensity G v Y) with hP
  have hρ : 1 - (P.card : ℝ) / X.card ≤ D := (hwg1.trans hwg2).trans hDr
  have hm4' : (m : ℝ) / X.card ≤ 1 / 4 := by
    rw [div_le_iff₀ hN0]; linarith
  have hmN : (m : ℝ) / X.card ≤ (cap - θ - D) / 2 := by
    rw [div_le_iff₀ hN0]
    rw [div_le_iff₀ hh] at hmh
    linarith
  have h2 : D + (m : ℝ) / X.card + (b : ℝ) / m ≤ cap - θ := by linarith
  rcases cl_nested_book_good_pages G X P θ cap D b m k hX (Finset.filter_subset _ _) hθ0 hθcap hcap1
      hb1 hbm hρ hD4 hm4' h2 hW with hred | ⟨S, T, hSX, hTP, hST, hS, hSTadj, hTcard⟩
  · exact Or.inl (hasRed_mono hred Finset.subset_union_left)
  by_cases htb : t ≤ b
  · obtain ⟨U, hUS, hU⟩ := isNClique_sub hS htb
    exact Or.inr (Or.inl ⟨U, hUS.trans hSX, hU⟩)
  push_neg at htb
  have hTX : T ⊆ X := hTP.trans (Finset.filter_subset _ _)
  have hθb : 0 < θ ^ b * (X.card : ℝ) / 2 := by positivity
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast (lt_of_lt_of_le hθb hTcard)
  have hT0 : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hTY : Disjoint T Y := Finset.disjoint_of_subset_left hTX hXY
  -- the pages have row density at least `c_n`
  have hrowT : ∀ v ∈ T, p - δ / n ≤ rowDensity G v Y := by
    intro v hv
    have := (Finset.mem_filter.mp (hTP hv)).2
    linarith
  have havg : p - δ / n ≤ (∑ y ∈ Y, colDensity G T y) / (Y.card : ℝ) := by
    rw [wgp_avg_eq G T Y hTne hY, le_div_iff₀ hT0]
    calc (p - δ / n) * (T.card : ℝ) = ∑ _v ∈ T, (p - δ / n) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ T, rowDensity G v Y := Finset.sum_le_sum hrowT
  have hnb : ((n - b : ℕ) : ℝ) = (n : ℝ) - b := by
    rw [Nat.cast_sub (by omega)]
  have hnb0 : (0 : ℝ) < (n : ℝ) - b := by
    have : (b : ℝ) < n := by exact_mod_cast (show b < n by omega)
    linarith
  have hb1' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hgap : δ / (n : ℝ) ^ 2 ≤ (p - δ / n) - (p - δ / ((n - b : ℕ) : ℝ)) := by
    rw [hnb]
    have e : (p - δ / n) - (p - δ / ((n : ℝ) - b)) = δ * b / (n * ((n : ℝ) - b)) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hsq : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * b := le_mul_of_one_le_right (sq_nonneg _) hb1'
    have hnb' : 0 ≤ (n : ℝ) * b := mul_nonneg hn0 (by linarith)
    have : (n : ℝ) * ((n : ℝ) - b) ≤ (n : ℝ) ^ 2 * b := by
      have e2 : (n : ℝ) * ((n : ℝ) - b) = (n : ℝ) ^ 2 - n * b := by ring
      rw [e2]; linarith
    have h3 := mul_le_mul_of_nonneg_left this hδ0.le
    calc δ * ((n : ℝ) * ((n : ℝ) - b)) ≤ δ * ((n : ℝ) ^ 2 * b) := h3
      _ = δ * b * (n : ℝ) ^ 2 := by ring
  have hH' : δ / (n : ℝ) ^ 2 ≤ momentNorm G T Y (p - δ / ((n - b : ℕ) : ℝ)) (β * r) := by
    have := avg_sub_le_momentNorm G T Y (p - δ / ((n - b : ℕ) : ℝ)) (β * r) hY hs1.le
    linarith
  -- potential of the page pair
  have hpot : Thr C w lam yy μ ℓ k (t - b) ≤
      potential G T Y (p - δ / ((n - b : ℕ) : ℝ)) w r (β * r) := by
    rw [Thr_blue C w lam yy μ ℓ k t b htb.le hlam hyy hμ0]
    have hμw : 0 < (μ ^ w) ^ b := by positivity
    have e1 : (θ ^ b * (X.card : ℝ) / 2) ^ w = (θ ^ w) ^ b * (X.card : ℝ) ^ w / 2 ^ w := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity) hN0.le,
        ← Real.rpow_natCast θ b, ← Real.rpow_mul hθ0.le, mul_comm (b : ℝ) w, Real.rpow_mul hθ0.le,
        Real.rpow_natCast]
    have hTw : (θ ^ b * (X.card : ℝ) / 2) ^ w ≤ (T.card : ℝ) ^ w :=
      Real.rpow_le_rpow hθb.le hTcard hw.le
    have hHr : (δ / (n : ℝ) ^ 2) ^ r ≤ momentNorm G T Y (p - δ / ((n - b : ℕ) : ℝ)) (β * r) ^ r :=
      Real.rpow_le_rpow (by positivity) hH' hr0.le
    have hd0 : 0 ≤ (δ / (n : ℝ) ^ 2) ^ r := by positivity
    unfold potential
    calc Thr C w lam yy μ ℓ k t * (μ ^ w) ^ b ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) * (μ ^ w) ^ b :=
          mul_le_mul_of_nonneg_right hT hμw.le
      _ ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) * ((θ ^ w) ^ b * (δ / (n : ℝ) ^ 2) ^ r / 2 ^ w) :=
          mul_le_mul_of_nonneg_left hbook (by positivity)
      _ = (θ ^ b * (X.card : ℝ) / 2) ^ w * (Y.card : ℝ) * (δ / (n : ℝ) ^ 2) ^ r := by
          rw [e1]; ring
      _ ≤ (T.card : ℝ) ^ w * (Y.card : ℝ) *
            momentNorm G T Y (p - δ / ((n - b : ℕ) : ℝ)) (β * r) ^ r := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hTw hM0.le) hHr hd0
          exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hM0.le
  rcases IH (n - b) (by omega) k (t - b) (by omega) hk (by omega) T Y hTne hY hTY hpot with
    hred | hblue | hblue
  · exact Or.inl (hasRed_mono hred (Finset.union_subset_union hTX le_rfl))
  · obtain ⟨U, hUT, hU⟩ := hblue
    have hSU : Disjoint S U := Finset.disjoint_of_subset_right hUT hST
    have hcl := isNClique_union hS hU hSU (fun u hu v hv => hSTadj u hu v (hUT hv))
    rw [show b + (t - b) = t by omega] at hcl
    exact Or.inr (Or.inl ⟨S ∪ U, Finset.union_subset hSX (hUT.trans hTX), hcl⟩)
  · exact Or.inr (Or.inr hblue)


lemma redNbhd_sub (G : SimpleGraph V) (S : Finset V) (v : V) : redNbhd G S v ⊆ S := by
  classical
  unfold redNbhd; exact Finset.filter_subset _ _

lemma adj_of_mem_redNbhd {G : SimpleGraph V} {S : Finset V} {v u : V} (h : u ∈ redNbhd G S v) :
    G.Adj v u := by
  classical
  unfold redNbhd at h; exact (Finset.mem_filter.mp h).2

lemma graphNbhd_sub (B : SimpleGraph V) (X : Finset V) (v : V) : graphNbhd B X v ⊆ X := by
  classical
  unfold graphNbhd; exact Finset.filter_subset _ _

lemma adj_of_mem_graphNbhd {B : SimpleGraph V} {X : Finset V} {v u : V} (h : u ∈ graphNbhd B X v) :
    B.Adj v u := by
  classical
  unfold graphNbhd at h; exact (Finset.mem_filter.mp h).2

/-- Local case of the inductive step (few high-blue-degree rows): Lemma 1 gives a red or a blue child. -/
lemma local_case (G : SimpleGraph V) (p μ w β x η τ ζ R C lam yy cap δ r : ℝ) (ℓ n k t m : ℕ)
    (hloc : ∀ r : ℝ, R ≤ r →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G B : SimpleGraph V) (X Y : Finset V) (c : ℝ),
        X.Nonempty → Y.Nonempty → Disjoint X Y → |c - p| ≤ η →
        (∀ y ∈ Y, c < colDensity G X y) →
        RowColMaximal G X Y c w r (β * r) →
        (∀ i ∈ X, 0 < graphFrac B X i → SharpBlueFailure G B X Y c μ w β (β * r) i) →
        ∀ Xg : Finset V, Xg ⊆ X → (X.card : ℝ) - (Xg.card : ℝ) ≤ ζ * (X.card : ℝ) →
        (∀ i ∈ Xg, graphFrac B X i ≤ μ + τ ∧ SharpRedFailure G B X Y c w β (β * r) x i) →
        False)
    (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hμ0 : 0 < μ) (hlam : 0 < lam)
    (hlamx : lam < x) (hyy : 0 < yy) (hC0 : 0 < C) (hRr : R ≤ r) (hwr : w < r) (hcap0 : 0 ≤ cap)
    (hcapτ : cap ≤ μ + τ) (hδ0 : 0 < δ) (hδη : δ ≤ η) (hδp : δ < p)
    (hkt : k + t = n) (hk : 2 ≤ k) (ht : 2 ≤ t)
    (X Y : Finset V) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hH : 0 < momentNorm G X Y (p - δ / n) (β * r)) (hmax : RowColMaximal G X Y (p - δ / n) w r (β * r))
    (hT : Thr C w lam yy μ ℓ k t ≤ potential G X Y (p - δ / n) w r (β * r))
    (hm1 : 1 ≤ m) (hRam : (((n + m : ℕ)) : ℝ) ^ m ≤ ζ * X.card)
    (hNreq : 1 + (n : ℝ) ^ 2 / δ ≤ X.card * (1 - cap))
    (hW : (X.filter (fun v => cap * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ))).card < ramseyNumber k m)
    (IH : ∀ n' < n, IndHyp G C w lam yy μ p δ r β ℓ n') :
    HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ := by
  have hr0 : 0 < r := by linarith
  have hβr : β * r < r := mul_lt_of_lt_one_left hr0 hβ1
  have hn4 : 4 ≤ n := by omega
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hN0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hδn : δ / n ≤ δ := div_le_self hδ0.le (by linarith)
  have hδn0 : 0 ≤ δ / n := div_nonneg hδ0.le (by linarith)
  have hc0 : 0 ≤ p - δ / n := by linarith
  have hcp : |p - δ / n - p| ≤ η := by
    rw [show p - δ / n - p = -(δ / n) by ring, abs_neg, abs_of_nonneg hδn0]; linarith
  have hn1c : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : ℝ, Δ = (p - δ / n) - (p - δ / ((n - 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hΔeq : Δ = δ / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [hΔd, hn1c]; field_simp; ring
  have hΔ0 : 0 ≤ Δ := by rw [hΔeq]; exact div_nonneg hδ0.le (mul_nonneg (by linarith) hn1.le)
  have hsq : 0 < (n : ℝ) ^ 2 / δ := by positivity
  have hNcap : 0 < (X.card : ℝ) * (1 - cap) - 1 := by linarith
  have hΔ : 1 - (p - δ / n) ≤ ((X.card : ℝ) * (1 - cap) - 1) * Δ := by
    have h1 : (n : ℝ) ^ 2 / δ ≤ (X.card : ℝ) * (1 - cap) - 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hΔ0
    have e : (n : ℝ) ^ 2 / δ * Δ = (n : ℝ) / ((n : ℝ) - 1) := by
      rw [hΔeq]; field_simp
    have h3 : 1 ≤ (n : ℝ) / ((n : ℝ) - 1) := by rw [le_div_iff₀ hn1]; linarith
    have hp0 : 0 < p - δ / n := by linarith
    linarith
  have hRamN : (ramseyNumber k m : ℝ) ≤ ζ * X.card := by
    have h := ramseyNumber_le_pow k m n (by omega) hm1 (by omega)
    have h' : (ramseyNumber k m : ℝ) ≤ (((n + m : ℕ)) : ℝ) ^ m := by exact_mod_cast h
    linarith
  have hexc : (X.card : ℝ) - ((X.filter (fun v => graphFrac Gᶜ X v ≤ cap)).card : ℝ) ≤ ζ * (X.card : ℝ) := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := X) (fun v => graphFrac Gᶜ X v ≤ cap)
    have hsub : X.filter (fun v => ¬ graphFrac Gᶜ X v ≤ cap) ⊆
        X.filter (fun v => cap * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ)) := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      have h := not_le.mp hv.2
      rw [blueNbhd_eq]
      unfold graphFrac at h
      rw [lt_div_iff₀ hN0] at h
      exact h.le
    have h1 := Finset.card_le_card hsub
    have h2 : ((X.filter (fun v => graphFrac Gᶜ X v ≤ cap)).card : ℝ) +
        ((X.filter (fun v => ¬ graphFrac Gᶜ X v ≤ cap)).card : ℝ) = X.card := by exact_mod_cast hsplit
    have h3 : ((X.filter (fun v => ¬ graphFrac Gᶜ X v ≤ cap)).card : ℝ) ≤
        ((X.filter (fun v => cap * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ))).card : ℝ) := by
      exact_mod_cast h1
    have h4 : ((X.filter (fun v => cap * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ))).card : ℝ) <
        (ramseyNumber k m : ℝ) := by exact_mod_cast hW
    linarith
  have hT0 := Thr_pos C w lam yy μ ℓ k t hC0 hlam hyy hμ0
  have hcΔ : p - δ / n - Δ = p - δ / ((n - 1 : ℕ) : ℝ) := by rw [hΔd]; ring
  have hn1' : n - 1 < n := by omega
  obtain ⟨v, hvX, hred | hblue⟩ := local_step p μ w β x η τ ζ R hw hβ0 hx0 hμ0 hloc r hRr hwr hβr G X Y
    (p - δ / n) Δ cap hX hY hXY hcp hc0 hcap0 hcapτ hΔ0 hNcap hΔ hH hmax hexc
  · obtain ⟨_, hxv⟩ := hred
    rw [hcΔ] at hxv
    have hpot : Thr C w lam yy μ ℓ (k - 1) t ≤
        potential G (redNbhd G X v) (redNbhd G Y v) (p - δ / ((n - 1 : ℕ) : ℝ)) w r (β * r) := by
      rw [Thr_red C w lam yy μ ℓ k t (by omega) hlam hyy hμ0]
      calc Thr C w lam yy μ ℓ k t * lam ≤ x * Thr C w lam yy μ ℓ k t := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right hlamx.le hT0.le
        _ ≤ x * potential G X Y (p - δ / n) w r (β * r) := mul_le_mul_of_nonneg_left hT hx0.le
        _ ≤ _ := hxv
    obtain ⟨hne1, hne2⟩ := nonempty_of_potential_pos G _ _ _ w r (β * r) hw
      (lt_of_lt_of_le (Thr_pos C w lam yy μ ℓ (k - 1) t hC0 hlam hyy hμ0) hpot)
    have hRX : redNbhd G X v ⊆ X := redNbhd_sub G X v
    have hRY : redNbhd G Y v ⊆ Y := redNbhd_sub G Y v
    have hdisj : Disjoint (redNbhd G X v) (redNbhd G Y v) :=
      Finset.disjoint_of_subset_left hRX (Finset.disjoint_of_subset_right hRY hXY)
    rcases IH (n - 1) hn1' (k - 1) t (by omega) (by omega) (by omega) _ _ hne1 hne2 hdisj hpot with
      h | h | h
    · obtain ⟨S, hS, hcl⟩ := h
      have hadj : ∀ u ∈ S, G.Adj v u := by
        intro u hu
        rcases Finset.mem_union.mp (hS hu) with h' | h'
        · exact adj_of_mem_redNbhd h'
        · exact adj_of_mem_redNbhd h'
      have hcl' := hcl.insert hadj
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hcl'
      refine Or.inl ⟨insert v S, Finset.insert_subset (Finset.mem_union_left _ hvX)
        (hS.trans (Finset.union_subset_union hRX hRY)), hcl'⟩
    · exact Or.inr (Or.inl (hasBlue_mono h hRX))
    · exact Or.inr (Or.inr (hasBlue_mono h hRY))
  · have hBX : graphNbhd Gᶜ X v ⊆ X := graphNbhd_sub Gᶜ X v
    have hpot : Thr C w lam yy μ ℓ k (t - 1) ≤
        potential G (graphNbhd Gᶜ X v) Y (p - δ / ((n - 1 : ℕ) : ℝ)) w r (β * r) := by
      rw [Thr_blue C w lam yy μ ℓ k t 1 (by omega) hlam hyy hμ0, pow_one]
      have hμw : 0 < μ ^ w := Real.rpow_pos_of_pos hμ0 w
      calc Thr C w lam yy μ ℓ k t * μ ^ w ≤ μ ^ w * potential G X Y (p - δ / n) w r (β * r) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hT hμw.le
        _ ≤ potential G (graphNbhd Gᶜ X v) Y (p - δ / n) w r (β * r) := hblue
        _ ≤ _ := by
          rw [← hcΔ]
          exact potential_anti G _ Y _ _ w r (β * r) (by linarith) (by positivity) hr0.le
    obtain ⟨hne1, _⟩ := nonempty_of_potential_pos G _ _ _ w r (β * r) hw
      (lt_of_lt_of_le (Thr_pos C w lam yy μ ℓ k (t - 1) hC0 hlam hyy hμ0) hpot)
    have hdisj : Disjoint (graphNbhd Gᶜ X v) Y := Finset.disjoint_of_subset_left hBX hXY
    rcases IH (n - 1) hn1' k (t - 1) (by omega) (by omega) (by omega) _ _ hne1 hY hdisj hpot with
      h | h | h
    · exact Or.inl (hasRed_mono h (Finset.union_subset_union hBX le_rfl))
    · obtain ⟨U, hU, hcl⟩ := h
      have hadj : ∀ u ∈ U, Gᶜ.Adj v u := fun u hu => adj_of_mem_graphNbhd (hU hu)
      have hcl' := hcl.insert hadj
      rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hcl'
      exact Or.inr (Or.inl ⟨insert v U, Finset.insert_subset hvX (hU.trans hBX), hcl'⟩)
    · exact Or.inr (Or.inr h)


/-- The strengthened induction (I_n), for all `n`, from the local envelope consequence, the host stopping
property, and the parameter requirements. -/
theorem closure_induction (G : SimpleGraph V)
    (p μ w β x η τ ζ R C lam yy xhat yhat cap θ D δ r a : ℝ) (ℓ : ℕ) (b m : ℕ → ℕ)
    (hloc : ∀ r : ℝ, R ≤ r →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G B : SimpleGraph V) (X Y : Finset V) (c : ℝ),
        X.Nonempty → Y.Nonempty → Disjoint X Y → |c - p| ≤ η →
        (∀ y ∈ Y, c < colDensity G X y) →
        RowColMaximal G X Y c w r (β * r) →
        (∀ i ∈ X, 0 < graphFrac B X i → SharpBlueFailure G B X Y c μ w β (β * r) i) →
        ∀ Xg : Finset V, Xg ⊆ X → (X.card : ℝ) - (Xg.card : ℝ) ≤ ζ * (X.card : ℝ) →
        (∀ i ∈ Xg, graphFrac B X i ≤ μ + τ ∧ SharpRedFailure G B X Y c w β (β * r) x i) →
        False)
    (hstop : HostStopping G C xhat yhat ℓ)
    (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hμ0 : 0 < μ) (hlam : 0 < lam)
    (hlamx : lam < x) (hyy : 0 < yy) (hC : 1 ≤ C) (hxh0 : 0 < xhat) (hyh0 : 0 < yhat)
    (hRr : R ≤ r) (hwr : w < r) (hs1 : 1 < β * r)
    (hcap0 : 0 ≤ cap) (hcapτ : cap ≤ μ + τ) (hcap1 : cap < 1) (hθ0 : 0 < θ) (hθcap : θ < cap)
    (hδ0 : 0 < δ) (hδη : δ ≤ η) (hδp : δ < p)
    (hDr : w / (r - w) + 1 - (1 - β) ^ (1 / (β * r)) ≤ D) (hD4 : D ≤ 1 / 4) (hh : 0 < cap - θ - D)
    (hax : a * w ≤ Real.log (xhat / lam)) (hay : a * w ≤ Real.log (yhat / yy))
    (haμ : a ≤ Real.log (1 / μ))
    (hbn : ∀ n, 1 ≤ b n ∧ b n ≤ m n ∧ (b n : ℝ) / (m n) ≤ (cap - θ - D) / 2)
    (hbook : ∀ n : ℕ, 1 ≤ n → (μ ^ w) ^ (b n) ≤ (θ ^ w) ^ (b n) * (δ / (n : ℝ) ^ 2) ^ r / 2 ^ w)
    (hsize : ∀ n : ℕ, 1 ≤ n → ∀ N : ℝ, Real.exp (a * ((n : ℝ) + ℓ)) < N →
      4 * (m n : ℝ) ≤ N ∧ 2 * (m n : ℝ) / (cap - θ - D) ≤ N ∧
        (((n + m n : ℕ)) : ℝ) ^ (m n) ≤ ζ * N ∧ 1 + (n : ℝ) ^ 2 / δ ≤ N * (1 - cap)) :
    ∀ n, IndHyp G C w lam yy μ p δ r β ℓ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k t hkt hk ht X Y hX hY hXY hT
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    exact Or.inl (hasRed_one (hX.mono Finset.subset_union_left))
  rcases Nat.lt_or_ge t 2 with ht1 | ht2
  · obtain rfl : t = 1 := by omega
    exact Or.inr (Or.inl (hasBlue_one hX))
  have hn : 1 ≤ n := by omega
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < β * r := by positivity
  have hC0 : 0 < C := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc0 : 0 ≤ p - δ / n := by
    have : δ / n ≤ δ := div_le_self hδ0.le hn'
    linarith
  have hT0 := Thr_pos C w lam yy μ ℓ k t hC0 hlam hyy hμ0
  obtain ⟨X', hX'X, Y', hY'Y, hX', hY', hΦ', hmax⟩ :=
    exists_maximal_pair G X Y hX hY (p - δ / n) w r (β * r)
  have hT' := hT.trans hΦ'
  have hXY' : Disjoint X' Y' := Finset.disjoint_of_subset_left hX'X (Finset.disjoint_of_subset_right hY'Y hXY)
  suffices key : HasRedClique G (X' ∪ Y') k ∨ HasBlueClique G X' t ∨ HasBlueClique G Y' ℓ by
    rcases key with h | h | h
    · exact Or.inl (hasRed_mono h (Finset.union_subset_union hX'X hY'Y))
    · exact Or.inr (Or.inl (hasBlue_mono h hX'X))
    · exact Or.inr (Or.inr (hasBlue_mono h hY'Y))
  have hH := momentNorm_pos_of_potential_pos G X' Y' _ w r (β * r) hr0 (lt_of_lt_of_le hT0 hT')
  have hPle := potential_le G X' Y' (p - δ / n) w r (β * r) hc0 hs0 hr0
  have hN0 : (0 : ℝ) < X'.card := by exact_mod_cast hX'.card_pos
  have hM0 : (0 : ℝ) < Y'.card := by exact_mod_cast hY'.card_pos
  by_cases hstopY : C / (xhat ^ k * yhat ^ ℓ) ≤ (Y'.card : ℝ)
  · have hne : Y' ≠ Finset.univ := by
      intro h
      obtain ⟨v, hv⟩ := hX'
      exact Finset.disjoint_left.mp hXY' hv (h ▸ Finset.mem_univ v)
    have hthr : C * xhat ^ (-(k : ℝ)) * yhat ^ (-(ℓ : ℝ)) ≤ (Y'.card : ℝ) := by
      rw [Real.rpow_neg hxh0.le, Real.rpow_neg hyh0.le, Real.rpow_natCast, Real.rpow_natCast]
      calc C * (xhat ^ k)⁻¹ * (yhat ^ ℓ)⁻¹ = C / (xhat ^ k * yhat ^ ℓ) := by
            rw [div_eq_mul_inv, mul_inv]; ring
        _ ≤ _ := hstopY
    rcases hstop k (by omega) Y' hne hthr with h | h
    · exact Or.inl (hasRed_mono h Finset.subset_union_right)
    · exact Or.inr (Or.inr h)
  push_neg at hstopY
  have hN := size_lemma C w lam yy μ xhat yhat a X'.card Y'.card ℓ k t hC hw hlam hyy hμ0 hxh0 hyh0 hN0 hM0
    hax hay haμ (hT'.trans hPle) hstopY
  rw [hkt] at hN
  obtain ⟨h4, h2m, hRam, hNreq⟩ := hsize n hn _ hN
  obtain ⟨hb1, hbm, hbmh⟩ := hbn n
  by_cases hbk : ramseyNumber k (m n) ≤
      (X'.filter (fun v => cap * (X'.card : ℝ) ≤ ((blueNbhd G X' v).card : ℝ))).card
  · exact book_step G C w lam yy μ p δ r β θ cap D ℓ n k t (b n) (m n) hw hβ0 hβ1 hwr hs1 hμ0 hθ0 hθcap
      hcap1 hδ0 hC0 hlam hyy hDr hD4 hb1 hbm hbmh hh (hbook n hn) hkt hk ht X' Y' hX' hY' hXY' hH hmax
      (hT'.trans hPle) h4 h2m hbk ih
  · push_neg at hbk
    exact local_case G p μ w β x η τ ζ R C lam yy cap δ r ℓ n k t (m n) hloc hw hβ0 hβ1 hx0 hμ0 hlam hlamx
      hyy hC0 hRr hwr hcap0 hcapτ hδ0 hδη hδp hkt hk2 ht2 X' Y' hX' hY' hXY' hH hmax hT'
      (hb1.trans hbm) hRam hNreq hbk ih

end Steps

end DiagRamsey.ClosureEnv
