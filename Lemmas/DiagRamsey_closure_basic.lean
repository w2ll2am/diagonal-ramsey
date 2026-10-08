import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_DiagRamsey_Basic
import Definitions.Def_DiagRamsey_WeightedHost
import Lemmas.DiagRamsey_closure_nbgp
import Lemmas.DiagRamsey_closure_wgp

/-! Elementary facts used by the finite-host closure: potential bookkeeping, a maximal sub-pair, the
Erdős–Szekeres bound for `ramseyNumber`, clique gluing, and the `(log n)^2 = o(n)` growth bounds. -/

set_option linter.unusedSectionVars false

namespace DiagRamsey.ClosureEnv

section Potential

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma colMomentSum_nonneg (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) :
    0 ≤ colMomentSum G X Y c s :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (le_max_right _ _) s)

lemma momentNorm_eq (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) :
    momentNorm G X Y c s = (colMomentSum G X Y c s / (Y.card : ℝ)) ^ (1 / s) := rfl

lemma momentNorm_nonneg (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) :
    0 ≤ momentNorm G X Y c s :=
  Real.rpow_nonneg (div_nonneg (colMomentSum_nonneg G X Y c s) (Nat.cast_nonneg _)) _

lemma potential_nonneg (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) :
    0 ≤ potential G X Y c w r s :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
    (Real.rpow_nonneg (momentNorm_nonneg G X Y c s) _)

lemma potential_eq (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) :
    potential G X Y c w r s =
      (X.card : ℝ) ^ w * (Y.card : ℝ) * (colMomentSum G X Y c s / (Y.card : ℝ)) ^ (r / s) := by
  unfold potential
  rw [momentNorm_eq, ← Real.rpow_mul (div_nonneg (colMomentSum_nonneg G X Y c s) (Nat.cast_nonneg _)),
    one_div_mul_eq_div]

lemma nonempty_of_potential_pos (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hw : 0 < w)
    (h : 0 < potential G X Y c w r s) : X.Nonempty ∧ Y.Nonempty := by
  unfold potential at h
  constructor
  · rcases X.eq_empty_or_nonempty with hX | hX
    · rw [hX, Finset.card_empty, Nat.cast_zero, Real.zero_rpow hw.ne'] at h; simp at h
    · exact hX
  · rcases Y.eq_empty_or_nonempty with hY | hY
    · rw [hY, Finset.card_empty, Nat.cast_zero] at h; simp at h
    · exact hY

lemma momentNorm_pos_of_potential_pos (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hr : 0 < r)
    (h : 0 < potential G X Y c w r s) : 0 < momentNorm G X Y c s := by
  rcases (momentNorm_nonneg G X Y c s).lt_or_eq with h1 | h1
  · exact h1
  · unfold potential at h
    rw [← h1, Real.zero_rpow hr.ne'] at h; simp at h

lemma colDensity_nonneg (G : SimpleGraph V) (X : Finset V) (y : V) : 0 ≤ colDensity G X y :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma colDensity_le_one (G : SimpleGraph V) (X : Finset V) (y : V) : colDensity G X y ≤ 1 := by
  classical
  unfold colDensity
  rcases X.eq_empty_or_nonempty with hX | hX
  · simp [hX]
  · rw [div_le_one (by exact_mod_cast hX.card_pos)]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_filter.mp hv).1

lemma momentNorm_le_one (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (hc : 0 ≤ c) (hs : 0 < s) :
    momentNorm G X Y c s ≤ 1 := by
  rw [momentNorm_eq]
  apply Real.rpow_le_one (div_nonneg (colMomentSum_nonneg G X Y c s) (Nat.cast_nonneg _)) _
    (by positivity)
  rcases Y.eq_empty_or_nonempty with hY | hY
  · simp [hY]
  rw [div_le_one (by exact_mod_cast hY.card_pos)]
  unfold colMomentSum
  calc ∑ y ∈ Y, (max (colDensity G X y - c) 0) ^ s ≤ ∑ _y ∈ Y, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        apply Real.rpow_le_one (le_max_right _ _) _ hs.le
        apply max_le _ zero_le_one
        linarith [colDensity_le_one G X y]
    _ = Y.card := by simp

lemma potential_le (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hc : 0 ≤ c) (hs : 0 < s)
    (hr : 0 < r) : potential G X Y c w r s ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) := by
  unfold potential
  have h1 : momentNorm G X Y c s ^ r ≤ 1 :=
    Real.rpow_le_one (momentNorm_nonneg G X Y c s) (momentNorm_le_one G X Y c s hc hs) hr.le
  have h2 : 0 ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  calc (X.card : ℝ) ^ w * (Y.card : ℝ) * momentNorm G X Y c s ^ r
      ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := mul_one _

lemma momentNorm_anti (G : SimpleGraph V) (X Y : Finset V) (c c' s : ℝ) (hcc : c' ≤ c) (hs : 0 < s) :
    momentNorm G X Y c s ≤ momentNorm G X Y c' s := by
  rw [momentNorm_eq, momentNorm_eq]
  apply Real.rpow_le_rpow (div_nonneg (colMomentSum_nonneg G X Y c s) (Nat.cast_nonneg _)) _
    (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro y _
  exact Real.rpow_le_rpow (le_max_right _ _) (max_le_max (by linarith) le_rfl) hs.le

lemma potential_anti (G : SimpleGraph V) (X Y : Finset V) (c c' w r s : ℝ) (hcc : c' ≤ c) (hs : 0 < s)
    (hr : 0 ≤ r) : potential G X Y c w r s ≤ potential G X Y c' w r s := by
  unfold potential
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  exact Real.rpow_le_rpow (momentNorm_nonneg G X Y c s) (momentNorm_anti G X Y c c' s hcc hs) hr

/-- Power mean: the column average minus `c` is at most the moment norm (`s ≥ 1`). -/
lemma avg_sub_le_momentNorm (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (hY : Y.Nonempty)
    (hs1 : 1 ≤ s) :
    (∑ y ∈ Y, colDensity G X y) / (Y.card : ℝ) - c ≤ momentNorm G X Y c s := by
  have hs : 0 < s := by linarith
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  set z : V → ℝ := fun y => max (colDensity G X y - c) 0 with hz
  have hz0 : ∀ y ∈ Y, 0 ≤ z y := fun y _ => le_max_right _ _
  have hTE : (∑ y ∈ Y, colDensity G X y) / (Y.card : ℝ) - c ≤ ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y := by
    rw [← Finset.mul_sum, one_div_mul_eq_div]
    have : ∑ y ∈ Y, colDensity G X y - (Y.card : ℝ) * c ≤ ∑ y ∈ Y, z y := by
      rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun y _ => le_max_left _ _)
    rw [sub_le_iff_le_add, div_add' _ _ _ hY0.ne', div_le_div_iff_of_pos_right hY0]
    linarith
  have hw1 : ∑ y ∈ Y, (1 / (Y.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Y (fun _ => 1 / (Y.card : ℝ)) z
    (fun _ _ => by positivity) hw1 hz0 hs1
  have hE0 : 0 ≤ ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y :=
    Finset.sum_nonneg (fun y hy => mul_nonneg (by positivity) (hz0 y hy))
  have hJ' : ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y ≤ momentNorm G X Y c s := by
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hE0 s) hJ (by positivity : (0:ℝ) ≤ 1 / s)
    rw [← Real.rpow_mul hE0, mul_one_div_cancel hs.ne', Real.rpow_one] at h2
    refine h2.trans (le_of_eq ?_)
    unfold momentNorm
    congr 1
    rw [← Finset.mul_sum, one_div_mul_eq_div]
  linarith

lemma redDensity_eq_avg (G : SimpleGraph V) (X Y : Finset V) (hX : X.Nonempty) :
    redDensity G X Y = (∑ y ∈ Y, colDensity G X y) / (Y.card : ℝ) := by
  classical
  have hX0 : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_pos.ne'
  have hcard : (((X ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) =
      ∑ y ∈ Y, ((X.filter (fun v => G.Adj v y)).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.card_filter, Nat.cast_sum]
  unfold redDensity colDensity
  rw [hcard, ← Finset.sum_div, div_div, mul_comm]

/-- A potential-maximal pair of nonempty subsets is row- and column-maximal. -/
lemma exists_maximal_pair (G : SimpleGraph V) (X Y : Finset V) (hX : X.Nonempty) (hY : Y.Nonempty)
    (c w r s : ℝ) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, X'.Nonempty ∧ Y'.Nonempty ∧
      potential G X Y c w r s ≤ potential G X' Y' c w r s ∧ RowColMaximal G X' Y' c w r s := by
  classical
  set S := (X.powerset.filter (fun A => A.Nonempty)) ×ˢ (Y.powerset.filter (fun A => A.Nonempty))
  have hmem : (X, Y) ∈ S := by simp [S, hX, hY]
  obtain ⟨⟨X', Y'⟩, hm, hmax⟩ := Finset.exists_max_image S (fun q => potential G q.1 q.2 c w r s)
    ⟨_, hmem⟩
  simp only [S, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hm
  obtain ⟨⟨hX'X, hX'⟩, ⟨hY'Y, hY'⟩⟩ := hm
  refine ⟨X', hX'X, Y', hY'Y, hX', hY', hmax _ hmem, ?_, ?_⟩
  · intro A hA hAne
    exact hmax (A, Y') (by simp [S, hAne, hY', hA.trans hX'X, hY'Y])
  · intro A hA hAne
    exact hmax (X', A) (by simp [S, hAne, hX', hA.trans hY'Y, hX'X])

end Potential

section Cliques

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma hasRed_mono {G : SimpleGraph V} {S S' : Finset V} {k : ℕ} (h : HasRedClique G S k) (hS : S ⊆ S') :
    HasRedClique G S' k := by
  obtain ⟨T, hT, hc⟩ := h; exact ⟨T, hT.trans hS, hc⟩

lemma hasBlue_mono {G : SimpleGraph V} {S S' : Finset V} {k : ℕ} (h : HasBlueClique G S k)
    (hS : S ⊆ S') : HasBlueClique G S' k := by
  obtain ⟨T, hT, hc⟩ := h; exact ⟨T, hT.trans hS, hc⟩

lemma isNClique_sub {H : SimpleGraph V} {S : Finset V} {b t : ℕ} (hS : H.IsNClique b S) (htb : t ≤ b) :
    ∃ T ⊆ S, H.IsNClique t T := by
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (show t ≤ S.card by rw [hS.2]; exact htb)
  exact ⟨T, hTS, ⟨hS.1.subset (Finset.coe_subset.mpr hTS), hTc⟩⟩

lemma isNClique_union {H : SimpleGraph V} {S T : Finset V} {a b : ℕ} (hS : H.IsNClique a S)
    (hT : H.IsNClique b T) (hd : Disjoint S T) (hx : ∀ u ∈ S, ∀ v ∈ T, H.Adj u v) :
    H.IsNClique (a + b) (S ∪ T) := by
  refine ⟨?_, ?_⟩
  · show ((S ∪ T : Finset V) : Set V).Pairwise H.Adj
    rw [Finset.coe_union, Set.pairwise_union]
    exact ⟨hS.1, hT.1, fun u hu v hv _ => ⟨hx u hu v hv, (hx u hu v hv).symm⟩⟩
  · rw [Finset.card_union_of_disjoint hd, hS.2, hT.2]

lemma hasRed_one {G : SimpleGraph V} {S : Finset V} (hS : S.Nonempty) : HasRedClique G S 1 := by
  obtain ⟨v, hv⟩ := hS
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩⟩

lemma hasBlue_one {G : SimpleGraph V} {S : Finset V} (hS : S.Nonempty) : HasBlueClique G S 1 := by
  obtain ⟨v, hv⟩ := hS
  exact ⟨{v}, Finset.singleton_subset_iff.mpr hv, SimpleGraph.isNClique_one.mpr ⟨v, rfl⟩⟩

end Cliques

/-- Erdős–Szekeres: `R(a+1, b+1) ≤ C(a+b, a)`, as an arrowing statement. -/
lemma arrows_choose : ∀ n a b : ℕ, a + b = n → RamseyArrows (a + 1) (b + 1) ((a + b).choose a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [Nat.choose_zero_right, zero_add]
      intro G
      exact Or.inl ⟨{0}, SimpleGraph.isNClique_one.mpr ⟨0, rfl⟩⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [add_zero, Nat.choose_self, zero_add]
      intro G
      exact Or.inr ⟨{0}, SimpleGraph.isNClique_one.mpr ⟨0, rfl⟩⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h1 := ih (a' + (b' + 1)) (by omega) a' (b' + 1) rfl
    have h2 := ih ((a' + 1) + b') (by omega) (a' + 1) b' rfl
    set N1 := (a' + (b' + 1)).choose a' with hN1
    set N2 := (a' + 1 + b').choose (a' + 1) with hN2
    have hN : (a' + 1 + (b' + 1)).choose (a' + 1) = N1 + N2 := by
      rw [hN1, hN2, show a' + 1 + (b' + 1) = (a' + (b' + 1)) + 1 by omega, Nat.choose_succ_succ,
        show a' + (b' + 1) = a' + 1 + b' by omega]
    have hN1pos : 0 < N1 := Nat.choose_pos (by omega)
    rw [hN]
    intro G
    classical
    let v : Fin (N1 + N2) := ⟨0, by omega⟩
    let A := (Finset.univ.erase v).filter (fun u => G.Adj v u)
    let B := (Finset.univ.erase v).filter (fun u => ¬ G.Adj v u)
    have hAB : A.card + B.card = N1 + N2 - 1 := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase v)
        (fun u => G.Adj v u)
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at this
      simpa using this
    by_cases hA : N1 ≤ A.card
    · obtain ⟨A', hA'A, hA'c⟩ := Finset.exists_subset_card_eq hA
      rcases arrows_on_finset h1 G A' hA'c with ⟨S, hSA, hS⟩ | ⟨S, hSA, hS⟩
      · left
        refine ⟨insert v S, hS.insert (fun u hu => ?_)⟩
        exact (Finset.mem_filter.mp (hA'A (hSA hu))).2
      · exact Or.inr ⟨S, hS⟩
    · have hB : N2 ≤ B.card := by omega
      obtain ⟨B', hB'B, hB'c⟩ := Finset.exists_subset_card_eq hB
      rcases arrows_on_finset h2 G B' hB'c with ⟨S, hSB, hS⟩ | ⟨S, hSB, hS⟩
      · exact Or.inl ⟨S, hS⟩
      · right
        refine ⟨insert v S, hS.insert (fun u hu => ?_)⟩
        have hu' := Finset.mem_filter.mp (hB'B (hSB hu))
        rw [SimpleGraph.compl_adj]
        exact ⟨fun h => (Finset.mem_erase.mp hu'.1).1 h.symm, hu'.2⟩

/-- `R(k, m) ≤ (n + m)^m` for `1 ≤ k ≤ n`, `1 ≤ m`. -/
lemma ramseyNumber_le_pow (k m n : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkn : k ≤ n) :
    ramseyNumber k m ≤ (n + m) ^ m := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  have h1 : ramseyNumber (a + 1) (b + 1) ≤ (a + b).choose a :=
    Nat.sInf_le (arrows_choose (a + b) a b rfl)
  have h2 : (a + b).choose a ≤ (a + b) ^ b := by
    rw [Nat.choose_symm_add]; exact Nat.choose_le_pow _ _
  have h3 : (a + b) ^ b ≤ (n + (b + 1)) ^ b := Nat.pow_le_pow_left (by omega) _
  have h4 : (n + (b + 1)) ^ b ≤ (n + (b + 1)) ^ (b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- `(log n)^2 = o(n)`, in the form used for all size requirements. -/
lemma log_sq_le (β₀ L : ℝ) (hL : 0 < L) : ∃ K : ℝ, ∀ n : ℕ, β₀ * Real.log n ^ 2 ≤ K + L * n := by
  have hc : 0 < L / (|β₀| + 1) := by positivity
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hc
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp h
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge a
  refine ⟨∑ n ∈ Finset.range N₀, |β₀ * Real.log n ^ 2|, fun n => ?_⟩
  have hK : 0 ≤ ∑ n ∈ Finset.range N₀, |β₀ * Real.log n ^ 2| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases lt_or_ge n N₀ with hn | hn
  · have : |β₀ * Real.log n ^ 2| ≤ ∑ n ∈ Finset.range N₀, |β₀ * Real.log n ^ 2| :=
      Finset.single_le_sum (f := fun n : ℕ => |β₀ * Real.log n ^ 2|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hn)
    have := le_abs_self (β₀ * Real.log n ^ 2)
    nlinarith
  · have hx : a ≤ (n : ℝ) := hN₀.trans (by exact_mod_cast hn)
    have h1 := ha n hx
    simp only [Real.norm_eq_abs, id] at h1
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hn0] at h1
    have h2 : β₀ * Real.log n ^ 2 ≤ |β₀| * Real.log n ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    have h3 : |β₀| * Real.log n ^ 2 ≤ |β₀| * (L / (|β₀| + 1) * n) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have h4 : |β₀| * (L / (|β₀| + 1) * n) ≤ L * n := by
      rw [← mul_assoc, ← mul_div_assoc, mul_comm |β₀| L, mul_div_assoc]
      apply mul_le_mul_of_nonneg_right _ hn0
      have : |β₀| / (|β₀| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    linarith

lemma exp_logsq_le (a b σ : ℝ) (hσ : 1 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, Real.exp (a * Real.log n ^ 2 + b) ≤ K * σ ^ n := by
  obtain ⟨K₀, hK₀⟩ := log_sq_le a (Real.log σ) (Real.log_pos hσ)
  refine ⟨Real.exp (K₀ + b), Real.exp_pos _, fun n => ?_⟩
  have hσn : σ ^ n = Real.exp (n * Real.log σ) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  rw [hσn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := hK₀ n
  nlinarith

/-- The page-loss constant `D_r = w/(r-w) + 1 - (1-β)^(1/(βr))` tends to `0`. -/
lemma exists_r_small (w β R ε : ℝ) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε) :
    ∃ r : ℝ, R ≤ r ∧ 2 * w ≤ r ∧ w / (r - w) + 1 - (1 - β) ^ (1 / (β * r)) < ε := by
  set Λ := -Real.log (1 - β) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set r := max (max R (2 * w)) ((2 * w + Λ / β) / ε + 1) with hr
  have hrR : R ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hrw : 2 * w ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
  have hrε : (2 * w + Λ / β) / ε + 1 ≤ r := le_max_right _ _
  have hr0 : 0 < r := by linarith
  refine ⟨r, hrR, hrw, ?_⟩
  have hA : w / (r - w) ≤ 2 * w / r := by
    rw [div_le_div_iff₀ (by linarith) hr0]; nlinarith
  have hB : 1 - Λ / (β * r) ≤ (1 - β) ^ (1 / (β * r)) := by
    have e : Real.log (1 - β) * (1 / (β * r)) = -(Λ / (β * r)) := by rw [hΛ]; ring
    rw [Real.rpow_def_of_pos (by linarith), e]
    have := Real.add_one_le_exp (-(Λ / (β * r)))
    linarith
  have hC : 2 * w / r + Λ / (β * r) = (2 * w + Λ / β) / r := by field_simp
  have hD : (2 * w + Λ / β) / r < ε := by
    rw [div_lt_iff₀ hr0]
    have h1 : 2 * w + Λ / β < ε * ((2 * w + Λ / β) / ε + 1) := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne']; linarith
    have h2 : ε * ((2 * w + Λ / β) / ε + 1) ≤ ε * r := mul_le_mul_of_nonneg_left hrε hε.le
    linarith
  linarith

end DiagRamsey.ClosureEnv
