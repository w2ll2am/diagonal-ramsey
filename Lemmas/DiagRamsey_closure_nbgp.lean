import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_Basic
import Definitions.Def_DiagRamsey_WeightedHost

/-! Verbatim copy of the proof in `Solutions/Sol_DiagRamsey_nested_book_good_pages.lean` (verified, no sorryAx),
moved to the namespace `DiagRamsey.ClosureEnv` and renamed `cl_nested_book_good_pages`. -/

namespace DiagRamsey.ClosureEnv

/-- Arrowing transfers to every vertex set of the right size, in any vertex type.
(Copied from `Sol_DiagRamsey_ramseyNumber_arrows`.) -/
lemma arrows_on_finset {V : Type*} {a b m : ℕ} (hR : RamseyArrows a b m) (G : SimpleGraph V)
    (Z : Finset V) (hZ : Z.card = m) :
    (∃ S ⊆ Z, G.IsNClique a S) ∨ (∃ S ⊆ Z, Gᶜ.IsNClique b S) := by
  subst hZ
  let f : Fin Z.card ↪ V := ⟨fun i => (Z.equivFin.symm i).1,
    Subtype.val_injective.comp Z.equivFin.symm.injective⟩
  have hsub : ∀ S : Finset (Fin Z.card), S.map f ⊆ Z := by
    intro S x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact (Z.equivFin.symm i).2
  rcases hR (G.comap f) with ⟨S, hS⟩ | ⟨S, hS⟩
  · exact Or.inl ⟨S.map f, hsub S, (hS.map (f := f)).mono (SimpleGraph.map_comap_le f G)⟩
  · refine Or.inr ⟨S.map f, hsub S, ?_⟩
    have hle : (G.comap f)ᶜ ≤ Gᶜ.comap f := by
      intro u v huv
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at huv ⊢
      exact ⟨fun h => huv.1 (f.injective h), huv.2⟩
    exact ((hS.mono hle).map (f := f)).mono (SimpleGraph.map_comap_le f Gᶜ)

/-- Arrowing is monotone in the number of vertices. (Copied.) -/
lemma arrows_mono {a b n n' : ℕ} (hR : RamseyArrows a b n) (hn : n ≤ n') : RamseyArrows a b n' := by
  intro G
  have hZ : (Finset.univ.map (Fin.castLEEmb hn)).card = n := by simp
  rcases arrows_on_finset hR G _ hZ with ⟨S, -, hS⟩ | ⟨S, -, hS⟩
  · exact Or.inl ⟨S, hS⟩
  · exact Or.inr ⟨S, hS⟩

/-- Ramsey's theorem: every pair `(a, b)` is arrowed by some `N`. (Copied.) -/
lemma ramsey_exists : ∀ n a b : ℕ, a + b = n → ∃ N, RamseyArrows a b N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      exact ⟨0, fun G => Or.inl ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      exact ⟨0, fun G => Or.inr ⟨∅, by simp [SimpleGraph.isNClique_empty]⟩⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨N1, h1⟩ := ih (a' + (b' + 1)) (by omega) a' (b' + 1) rfl
    obtain ⟨N2, h2⟩ := ih ((a' + 1) + b') (by omega) (a' + 1) b' rfl
    refine ⟨N1 + N2 + 1, fun G => ?_⟩
    classical
    let v : Fin (N1 + N2 + 1) := 0
    let A := (Finset.univ.erase v).filter (fun u => G.Adj v u)
    let B := (Finset.univ.erase v).filter (fun u => ¬ G.Adj v u)
    have hAB : A.card + B.card = N1 + N2 := by
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

/-- (Copied from `Sol_DiagRamsey_ramseyNumber_arrows`.) -/
lemma ramseyNumber_arrows' (k m N : ℕ) (h : ramseyNumber k m ≤ N) : RamseyArrows k m N := by
  obtain ⟨N0, hN0⟩ := ramsey_exists (k + m) k m rfl
  have hmem : RamseyArrows k m (ramseyNumber k m) :=
    Nat.sInf_mem (s := {N | RamseyArrows k m N}) ⟨N0, hN0⟩
  exact arrows_mono hmem h

/-- `C(m,b) (j-b)^b ≤ C(j,b) m^b` for `b ≥ 1` (truncated subtraction). -/
lemma choose_mul_pow_le {j m b : ℕ} (hb : 1 ≤ b) :
    m.choose b * (j - b) ^ b ≤ j.choose b * m ^ b := by
  rcases lt_or_ge j b with hjb | hjb
  · have h0 : j - b = 0 := by omega
    rw [h0, zero_pow (by omega)]
    simp
  · have h1 : ∏ i ∈ Finset.range b, ((m - i) * (j - b)) = m.descFactorial b * (j - b) ^ b := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Nat.descFactorial_eq_prod_range]
    have h2 : ∏ i ∈ Finset.range b, ((j - i) * m) = j.descFactorial b * m ^ b := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Nat.descFactorial_eq_prod_range]
    have key : m.descFactorial b * (j - b) ^ b ≤ j.descFactorial b * m ^ b := by
      rw [← h1, ← h2]
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      rw [Finset.mem_range] at hi
      calc (m - i) * (j - b) ≤ m * (j - i) := Nat.mul_le_mul (Nat.sub_le m i) (by omega)
        _ = (j - i) * m := Nat.mul_comm _ _
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      mul_assoc, mul_assoc] at key
    exact Nat.le_of_mul_le_mul_left key (Nat.factorial_pos b)

theorem cl_nested_book_good_pages {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X P : Finset V) (θ τ D : ℝ) (b m k : ℕ)
    (hX : X.Nonempty) (hPX : P ⊆ X) (hθ : 0 < θ) (hθτ : θ < τ) (hτ : τ < 1) (hb : 1 ≤ b) (hbm : b ≤ m)
    (hρ : 1 - (P.card : ℝ) / (X.card : ℝ) ≤ D) (hD : D ≤ 1 / 4) (hm : (m : ℝ) / (X.card : ℝ) ≤ 1 / 4)
    (h2 : D + (m : ℝ) / (X.card : ℝ) + (b : ℝ) / (m : ℝ) ≤ τ - θ)
    (hW : ramseyNumber k m ≤ (X.filter (fun v => τ * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ))).card) :
    HasRedClique G X k ∨
      ∃ S T : Finset V, S ⊆ X ∧ T ⊆ P ∧ Disjoint S T ∧ Gᶜ.IsNClique b S ∧
        (∀ u ∈ S, ∀ v ∈ T, Gᶜ.Adj u v) ∧ θ ^ b * (X.card : ℝ) / 2 ≤ (T.card : ℝ) := by
  classical
  have hN : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hWX : X.filter (fun v => τ * (X.card : ℝ) ≤ ((blueNbhd G X v).card : ℝ)) ⊆ X :=
    Finset.filter_subset _ _
  rcases arrows_on_finset (ramseyNumber_arrows' k m _ hW) G _ rfl with ⟨S, hSW, hS⟩ | ⟨U, hUW, hU⟩
  · exact Or.inl ⟨S, hSW.trans hWX, hS⟩
  right
  have hUcard : U.card = m := hU.card_eq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  -- the page pool `P' = P \ U`
  have hPcard : (1 - D) * X.card ≤ (P.card : ℝ) :=
    (le_div_iff₀ hN).mp (by linarith)
  have hmN : (m : ℝ) ≤ 1 / 4 * X.card := (div_le_iff₀ hN).mp hm
  have hP'card : (X.card : ℝ) / 2 ≤ ((P \ U).card : ℝ) := by
    have h1 := Finset.card_sdiff_add_card_inter P U
    have h3 : (P ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
    have h4 : (P.card : ℝ) ≤ ((P \ U).card : ℝ) + m := by
      exact_mod_cast (by omega : P.card ≤ (P \ U).card + m)
    have h5 : (3 / 4 : ℝ) * X.card ≤ (1 - D) * X.card :=
      mul_le_mul_of_nonneg_right (by linarith) hN.le
    linarith
  have hP'N : ((P \ U).card : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset.trans hPX)
  have hp : (0 : ℝ) < ((P \ U).card : ℝ) := by linarith
  -- each spine vertex has many blue neighbours in the page pool
  have hdeg : ∀ u ∈ U, τ * X.card - D * X.card - m ≤
      (((P \ U).filter (fun x => Gᶜ.Adj u x)).card : ℝ) := by
    intro u hu
    have hτu : τ * X.card ≤ ((blueNbhd G X u).card : ℝ) := (Finset.mem_filter.mp (hUW hu)).2
    have hsub : blueNbhd G X u ⊆ ((P \ U).filter (fun x => Gᶜ.Adj u x)) ∪ ((X \ P) ∪ U) := by
      intro x hx
      simp only [blueNbhd, Finset.mem_filter] at hx
      by_cases hxU : x ∈ U
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxU)
      by_cases hxP : x ∈ P
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxP, hxU⟩, ?_⟩)
        rw [SimpleGraph.compl_adj]
        exact ⟨fun h => hx.2.1 h.symm, fun h => hx.2.2 h.symm⟩
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hxP⟩))
    have hc1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc2 := Finset.card_union_le (X \ P) U
    have hc3 := Finset.card_sdiff_add_card_eq_card hPX
    have hc : (blueNbhd G X u).card + P.card ≤
        ((P \ U).filter (fun x => Gᶜ.Adj u x)).card + X.card + m := by omega
    have hc' : ((blueNbhd G X u).card : ℝ) + P.card ≤
        (((P \ U).filter (fun x => Gᶜ.Adj u x)).card : ℝ) + X.card + m := by exact_mod_cast hc
    nlinarith
  -- `j x` = number of blue neighbours of the page `x` in `U`
  set j : V → ℕ := fun x => (U.filter (fun u => Gᶜ.Adj u x)).card with hj
  have hsumj : ∑ x ∈ P \ U, j x = ∑ u ∈ U, ((P \ U).filter (fun x => Gᶜ.Adj u x)).card := by
    simp only [hj, Finset.card_filter]
    exact Finset.sum_comm
  -- the total excess over `b` is at least `θ m |P'|`
  set y : V → ℝ := fun x => ((j x - b : ℕ) : ℝ) with hy
  have hsumy : θ * m * ((P \ U).card : ℝ) ≤ ∑ x ∈ P \ U, y x := by
    have h1 : ∀ x ∈ P \ U, (j x : ℝ) - b ≤ y x := by
      intro x _
      rcases le_total b (j x) with h | h
      · simp only [hy]; rw [Nat.cast_sub h]
      · simp only [hy]; rw [Nat.sub_eq_zero_of_le h]
        have : (j x : ℝ) ≤ b := by exact_mod_cast h
        simp only [Nat.cast_zero]; linarith
    have h1' := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1'
    have h3 : (∑ x ∈ P \ U, (j x : ℝ)) =
        ∑ u ∈ U, ((((P \ U).filter (fun x => Gᶜ.Adj u x)).card : ℕ) : ℝ) := by
      exact_mod_cast hsumj
    have h4 := Finset.sum_le_sum hdeg
    rw [Finset.sum_const, nsmul_eq_mul, hUcard] at h4
    have e : (D + (m : ℝ) / X.card + b / m) * (m * X.card) = D * m * X.card + m * m + b * X.card := by
      field_simp
    have key : D * m * X.card + m * m + b * X.card ≤ (τ - θ) * (m * X.card) := by
      rw [← e]; exact mul_le_mul_of_nonneg_right h2 (mul_pos hmpos hN).le
    have h5 : θ * m * ((P \ U).card : ℝ) ≤ θ * m * X.card :=
      mul_le_mul_of_nonneg_left hP'N (mul_pos hθ hmpos).le
    have h6 : (b : ℝ) * ((P \ U).card : ℝ) ≤ b * X.card :=
      mul_le_mul_of_nonneg_left hP'N (Nat.cast_nonneg _)
    nlinarith
  -- power mean
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hpm := pow_sum_div_card_le_sum_pow (s := P \ U) (f := y) (fun _ _ => Nat.cast_nonneg _) b'
  have hpow : (θ * m) ^ (b' + 1) * ((P \ U).card : ℝ) ≤ ∑ x ∈ P \ U, y x ^ (b' + 1) := by
    refine le_trans ?_ hpm
    rw [le_div_iff₀ (pow_pos hp _)]
    calc (θ * m) ^ (b' + 1) * ((P \ U).card : ℝ) * ((P \ U).card : ℝ) ^ b'
        = (θ * m * ((P \ U).card : ℝ)) ^ (b' + 1) := by ring
      _ ≤ (∑ x ∈ P \ U, y x) ^ (b' + 1) :=
        pow_le_pow_left₀ (mul_pos (mul_pos hθ hmpos) hp).le hsumy _
  -- per-page bound and the averaging conclusion
  have hx : ∀ x ∈ P \ U, (m.choose (b' + 1) : ℝ) * y x ^ (b' + 1) ≤
      ((j x).choose (b' + 1) : ℝ) * (m : ℝ) ^ (b' + 1) := by
    intro x _
    simp only [hy]
    exact_mod_cast choose_mul_pow_le hb
  have hsx := Finset.sum_le_sum hx
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsx
  have hmain : (m.choose (b' + 1) : ℝ) * θ ^ (b' + 1) * ((P \ U).card : ℝ) ≤
      ∑ x ∈ P \ U, ((j x).choose (b' + 1) : ℝ) := by
    have hmb : (0 : ℝ) < (m : ℝ) ^ (b' + 1) := pow_pos hmpos _
    have hc0 : (0 : ℝ) ≤ m.choose (b' + 1) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hpow hc0
    rw [← mul_le_mul_iff_left₀ hmb]
    calc (m.choose (b' + 1) : ℝ) * θ ^ (b' + 1) * ((P \ U).card : ℝ) * (m : ℝ) ^ (b' + 1)
        = (m.choose (b' + 1) : ℝ) * ((θ * m) ^ (b' + 1) * ((P \ U).card : ℝ)) := by ring
      _ ≤ (m.choose (b' + 1) : ℝ) * ∑ x ∈ P \ U, y x ^ (b' + 1) := this
      _ ≤ _ := hsx
  -- double counting spines against pages
  set T : Finset V → Finset V := fun S => (P \ U).filter (fun x => ∀ u ∈ S, Gᶜ.Adj u x) with hT
  have hdc : ∑ S ∈ U.powersetCard (b' + 1), (T S).card = ∑ x ∈ P \ U, (j x).choose (b' + 1) := by
    simp only [hT, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.card_filter, hj, ← Finset.card_powersetCard]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun u hu => ⟨h1 hu, h3 u hu⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨fun u hu => (h1 hu).1, h2⟩, fun u hu => (h1 hu).2⟩
  have hne : (U.powersetCard (b' + 1)).Nonempty := Finset.powersetCard_nonempty.mpr (hUcard ▸ hbm)
  have hsum_le : ∑ _S ∈ U.powersetCard (b' + 1), θ ^ (b' + 1) * (X.card : ℝ) / 2 ≤
      ∑ S ∈ U.powersetCard (b' + 1), ((T S).card : ℝ) := by
    rw [Finset.sum_const, Finset.card_powersetCard, hUcard, nsmul_eq_mul]
    have e : (∑ S ∈ U.powersetCard (b' + 1), ((T S).card : ℝ)) =
        ∑ x ∈ P \ U, ((j x).choose (b' + 1) : ℝ) := by exact_mod_cast hdc
    rw [e]
    have hc0 : (0 : ℝ) ≤ (m.choose (b' + 1) : ℝ) * θ ^ (b' + 1) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_pos hθ _).le
    have := mul_le_mul_of_nonneg_left hP'card hc0
    calc (m.choose (b' + 1) : ℝ) * (θ ^ (b' + 1) * X.card / 2)
        = (m.choose (b' + 1) : ℝ) * θ ^ (b' + 1) * ((X.card : ℝ) / 2) := by ring
      _ ≤ _ := this
      _ ≤ _ := hmain
  obtain ⟨S, hS, hST⟩ := Finset.exists_le_of_sum_le hne hsum_le
  rw [Finset.mem_powersetCard] at hS
  refine ⟨S, T S, hS.1.trans (hUW.trans hWX), ?_, ?_, ?_, ?_, hST⟩
  · exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
  · exact Finset.disjoint_left.mpr fun a haS haT =>
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp haT).1).2 (hS.1 haS)
  · exact ⟨hU.isClique.subset (by exact_mod_cast hS.1), hS.2⟩
  · exact fun u hu v hv => (Finset.mem_filter.mp hv).2 u hu

end DiagRamsey.ClosureEnv
