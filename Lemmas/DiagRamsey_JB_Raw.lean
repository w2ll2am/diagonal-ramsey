import Lemmas.DiagRamsey_JB_Core
import Definitions.Def_DiagRamsey_JointBank2

/-!
# Joint banks: RAW pieces on the whole host (Lemmas 1–2 of the NL proof)

`raw_piece_ok`: for every RAW piece `J` of a RAW profile `P` there is `K_J` such that, for every `C ≥ 1` and every
host `V` with the minimal-host premise, the assertion of `P` holds on `V` at every integer pair `(k, b)` with
`k ≥ K_J` and `b/k ∈ J ∩ I_P`. The prefactors (3 for leaves, `D` for routes, 2 for the vertex deletion of
complementary pieces) are paid by the piece margin `ε_J` once `k ≥ K_J`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

section
variable {m nR nC : ℕ} {A B : Fin m → ℝ} {raw : Fin nR → BankProfile} {closed : Fin nC → BankProfile}

lemma prof_valid (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid) (c : Fin nR ⊕ Fin nC) :
    (Sum.elim raw closed c).Valid := by
  rcases c with i | i
  · exact hraw i
  · exact hclosed i

/-- The shape of the conclusion. -/
def PieceOK (raw : Fin nR → BankProfile) (closed : Fin nC → BankProfile) (A B : Fin m → ℝ) (P : BankProfile)
    (lo hi : ℝ) (KJ : ℕ) : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V], JPrem raw closed A B C V →
    ∀ (G : SimpleGraph V) (k b : ℕ), KJ ≤ k → 0 < k → 0 < b → lo ≤ (b : ℝ) / k → (b : ℝ) / k ≤ hi →
      P.lo ≤ (b : ℝ) / k →
      P.p * (((Finset.univ : Finset V).card : ℝ) * (((Finset.univ : Finset V).card : ℝ) - 1)) ≤
        (redPairs G Finset.univ : ℝ) →
      C * Real.exp (k * P.L ((b : ℝ) / k)) ≤ ((Finset.univ : Finset V).card : ℝ) →
      HasRedClique G Finset.univ k ∨ HasBlueClique G Finset.univ b

/-- Margin bookkeeping: `D e^{k x} ≤ e^{k (x + δ)}` once `k δ ≥ log D`. -/
lemma absorb {D C x δ : ℝ} {k : ℕ} (hD : 1 ≤ D) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hk : Real.log D / δ ≤ k) : D * C * Real.exp (k * x) ≤ C * Real.exp (k * (x + δ)) := by
  have h1 : Real.log D ≤ k * δ := by rwa [div_le_iff₀ hδ] at hk
  have h2 : D * Real.exp (k * x) ≤ Real.exp (k * (x + δ)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < D), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc D * C * Real.exp (k * x) = C * (D * Real.exp (k * x)) := by ring
    _ ≤ C * Real.exp (k * (x + δ)) := mul_le_mul_of_nonneg_left h2 hC

lemma raw_leaf_ok (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (P : BankProfile) (hP : P.Valid)
    (lo hi ε : ℝ) (hε : 0 < ε) (γ : SharpControl m) (hγ : γ.Valid A B) (hple : γ.p ≤ P.p)
    (hL : ∀ r : ℝ, lo ≤ r → r ≤ hi → ε + γ.leafLine r ≤ P.L r) :
    ∃ KJ, PieceOK raw closed A B P lo hi KJ := by
  have hα : 0 < max lo P.lo := lt_of_lt_of_le hP.2.2.1 (le_max_right _ _)
  obtain ⟨D, hD, K0, hK0⟩ := leaf_relValid hA hB γ hγ (max lo P.lo) hi hα
  obtain ⟨K1, hK1⟩ := exists_nat_ge (Real.log D / ε)
  refine ⟨K0 + K1, fun C hC V _ _ hJ G k b hk hk0 hb0 h1 h2 h3 hd hs => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hres := hK0 C hC V (prem_of_jprem hJ) G Finset.univ k ((b : ℝ) / k) (by omega)
    (max_le h1 h3) h2 (le_trans (mul_le_mul_of_nonneg_right hple (by
      rcases Nat.eq_zero_or_pos (Finset.univ : Finset V).card with h0 | h0
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ (Finset.univ : Finset V).card := by exact_mod_cast h0
        nlinarith)) hd) ?_
  · have hkk : (b : ℝ) / k * k = b := by field_simp
    rwa [hkk, Nat.floor_natCast] at hres
  · refine le_trans (absorb hD (by linarith) hε (hK1.trans (by exact_mod_cast (by omega : K1 ≤ k)))) (le_trans ?_ hs)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hkpos.le
    linarith [hL _ h1 h2]

lemma raw_route_ok (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid) (P : BankProfile) (hP : P.Valid)
    (lo hi ε : ℝ) (hε : 0 < ε) (R : RoutePiece (Fin nR ⊕ Fin nC) m)
    (hR : (RawPiece.route R).Valid A B (Sum.elim raw closed) P lo hi ε) :
    ∃ KJ, PieceOK raw closed A B P lo hi KJ := by
  obtain ⟨hγ, hpγ, hM, hθ, hmono, hg0, hθlo, hhiω, hcells, hval⟩ := hR
  let node : RouteNode 1 m :=
    { p := P.p, γ := R.γ, M := R.M, u := R.u, d := R.d, c := fun _ => 0, g₀ := R.g₀, ε := ε / 2 }
  set prof := Sum.elim raw closed with hprof
  have hcall : ∀ j : Fin node.M, RelValidPr (fun C V _ _ => JPrem raw closed A B C V) (prof (R.c j)).p
      (prof (R.c j)).lo (prof (R.c j)).hi (prof (R.c j)).L := by
    intro j
    refine ⟨1, le_rfl, 0, fun C hC V _ _ hJ G W k t hW _ hk ht h1 h2 hd hs => ?_⟩
    exact assertOn_child (hJ G W hW) (R.c j) k t hk ht h1 h2 hd (by simpa using hs)
  obtain ⟨D, hD, K0, hK0⟩ := route_relValidP hA hB (fun C V _ _ => JPrem raw closed A B C V)
    (fun C V _ _ h => prem_of_jprem h) node hγ hpγ hP.2.1 hM hθ hmono hg0 (by positivity)
    (fun j => (prof (R.c j)).p) (fun j => (prof (R.c j)).lo) (fun j => (prof (R.c j)).hi)
    (fun j => (prof (R.c j)).L) hcall (fun j => (hcells j).1) (fun j => (hcells j).2.1)
    (fun j => (prof_valid hraw hclosed (R.c j)).1) (fun j => (prof_valid hraw hclosed (R.c j)).2.1)
    (fun j => (hcells j).2.2.1) (fun j s h1 h2 => (hcells j).2.2.2 s h1 h2)
  obtain ⟨K1, hK1⟩ := exists_nat_ge (Real.log D / (ε / 2))
  refine ⟨K0 + K1, fun C hC V _ _ hJ G k b hk hk0 hb0 h1 h2 h3 hd hs => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hres := hK0 C hC V hJ G Finset.univ k ((b : ℝ) / k) (by omega) (hθlo.trans h1) (h2.trans hhiω) hd ?_
  · have hkk : (b : ℝ) / k * k = b := by field_simp
    rwa [hkk, Nat.floor_natCast] at hres
  · refine le_trans (absorb hD (by linarith) (by positivity : (0 : ℝ) < ε / 2)
      (hK1.trans (by exact_mod_cast (by omega : K1 ≤ k)))) (le_trans ?_ hs)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hkpos.le
    have hv := hval _ h1 h2
    have hout : node.out ((b : ℝ) / k) = ε / 2 + R.value ((b : ℝ) / k) := rfl
    rw [hout]; linarith

lemma raw_compl_ok (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid) (P : BankProfile)
    (lo hi ε : ℝ) (hε : 0 < ε) (PR PB : Fin nR ⊕ Fin nC)
    (hc : (RawPiece.compl (m := m) PR PB).Valid A B (Sum.elim raw closed) P lo hi ε) :
    ∃ KJ, PieceOK raw closed A B P lo hi KJ := by
  obtain ⟨hpsum, hloR, hhiR, hcomp⟩ := hc
  set prof := Sum.elim raw closed with hprof
  obtain ⟨K1, hK1⟩ := exists_nat_ge (Real.log 2 / ε)
  refine ⟨K1, fun C hC V _ _ hJ G k b hk hk0 hb0 h1 h2 h3 hd hs => ?_⟩
  set r : ℝ := (b : ℝ) / k with hr
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have hr0 : 0 < r := div_pos hbpos hkpos
  obtain ⟨hBlo, hBhi, hmax⟩ := hcomp r h1 h2
  have hvR := prof_valid hraw hclosed PR
  have hvB := prof_valid hraw hclosed PB
  have hLR : 0 < (prof PR).L r := hvR.2.2.2.2 r (hloR.trans h1) (h2.trans hhiR)
  have hLB : 0 < (prof PB).L (1 / r) := hvB.2.2.2.2 (1 / r) hBlo hBhi
  set E : ℝ := C * Real.exp (k * max ((prof PR).L r) (r * (prof PB).L (1 / r))) with hE
  have hE1 : 1 ≤ E := by
    have : 0 ≤ (k : ℝ) * max ((prof PR).L r) (r * (prof PB).L (1 / r)) :=
      mul_nonneg hkpos.le (le_trans hLR.le (le_max_left _ _))
    exact one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp this)
  -- |V| ≥ 2E
  have h2E : 2 * E ≤ ((Finset.univ : Finset V).card : ℝ) := by
    have hlog : Real.log 2 ≤ k * ε := by
      have := hK1.trans (show (K1 : ℝ) ≤ k by exact_mod_cast hk)
      rwa [div_le_iff₀ hε] at this
    have h2 : (2 : ℝ) ≤ Real.exp (k * (ε * (1 + r))) := by
      have hkr : 0 ≤ (k : ℝ) * (ε * r) := by positivity
      have e : (k : ℝ) * (ε * (1 + r)) = k * ε + k * (ε * r) := by ring
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (k * (ε * (1 + r))) := Real.exp_le_exp.mpr (by rw [e]; linarith)
    have h3 : 2 * E ≤ Real.exp (k * (ε * (1 + r))) * E :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    refine h3.trans (le_trans ?_ hs)
    rw [hE, ← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    have := hmax
    nlinarith
  -- delete a vertex
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast (show (0 : ℝ) < (Finset.univ : Finset V).card by linarith)
  obtain ⟨v, hv⟩ := hne
  set Z := (Finset.univ : Finset V).erase v with hZ
  have hZne : Z ≠ Finset.univ := fun h => by
    have : v ∈ Z := h ▸ Finset.mem_univ v
    simp [hZ] at this
  have hZcard : (Z.card : ℝ) = ((Finset.univ : Finset V).card : ℝ) - 1 := by
    rw [hZ, Finset.card_erase_of_mem hv]; push_cast [Nat.cast_sub (Finset.card_pos.mpr ⟨v, hv⟩)]; ring
  have hZE : E ≤ Z.card := by rw [hZcard]; linarith
  have hsub : Z ⊆ Finset.univ := Finset.subset_univ _
  have hZ0 : 0 ≤ (Z.card : ℝ) * ((Z.card : ℝ) - 1) := by
    have : (1 : ℝ) ≤ Z.card := le_trans hE1 hZE
    nlinarith
  by_cases hred : (prof PR).p * ((Z.card : ℝ) * ((Z.card : ℝ) - 1)) ≤ (redPairs G Z : ℝ)
  · have hres := assertOn_child (hJ G Z hZne) PR k b hk0 hb0 (hloR.trans h1) (h2.trans hhiR) hred
      (le_trans (by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_left _ _) hkpos.le)) hZE)
    rcases hres with h | h
    · exact Or.inl (ClosureEnv.hasRed_mono h hsub)
    · exact Or.inr (ClosureEnv.hasBlue_mono h hsub)
  · push_neg at hred
    have hcompl := redPairs_add_compl G Z
    have hblue : (prof PB).p * ((Z.card : ℝ) * ((Z.card : ℝ) - 1)) ≤ (redPairs Gᶜ Z : ℝ) := by nlinarith
    have hkb : (k : ℝ) / b = 1 / r := by rw [hr]; field_simp
    have hres := assertOn_child (hJ Gᶜ Z hZne) PB b k hb0 hk0 (by rw [hkb]; exact hBlo)
      (by rw [hkb]; exact hBhi) hblue (le_trans (by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply Real.exp_le_exp.mpr
        rw [hkb]
        have e : (b : ℝ) * (prof PB).L (1 / r) = k * (r * (prof PB).L (1 / r)) := by
          rw [hr]; field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) hkpos.le) hZE)
    rcases hres with ⟨S, hS, h⟩ | ⟨S, hS, h⟩
    · exact Or.inr ⟨S, hS.trans hsub, h⟩
    · rw [compl_compl] at h
      exact Or.inl ⟨S, hS.trans hsub, h⟩

lemma raw_piece_ok (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid) (P : BankProfile) (hP : P.Valid)
    (lo hi ε : ℝ) (hε : 0 < ε) (pc : RawPiece (Fin nR ⊕ Fin nC) m)
    (hpc : pc.Valid A B (Sum.elim raw closed) P lo hi ε) :
    ∃ KJ, PieceOK raw closed A B P lo hi KJ := by
  rcases pc with γ | R | ⟨PR, PB⟩
  · exact raw_leaf_ok hA hB P hP lo hi ε hε γ hpc.1 (le_of_eq hpc.2.1) hpc.2.2
  · exact raw_route_ok hA hB hraw hclosed P hP lo hi ε hε R hpc
  · exact raw_compl_ok hraw hclosed P lo hi ε hε PR PB hpc

/-- The v2 form (leaf density `p_γ ≤ p_R`). -/
lemma raw_piece_ok' (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid) (P : BankProfile) (hP : P.Valid)
    (lo hi ε : ℝ) (hε : 0 < ε) (pc : RawPiece (Fin nR ⊕ Fin nC) m)
    (hpc : pc.Valid' A B (Sum.elim raw closed) P lo hi ε) :
    ∃ KJ, PieceOK raw closed A B P lo hi KJ := by
  rcases pc with γ | R | ⟨PR, PB⟩
  · exact raw_leaf_ok hA hB P hP lo hi ε hε γ hpc.1 hpc.2.1 hpc.2.2
  · exact raw_route_ok hA hB hraw hclosed P hP lo hi ε hε R hpc
  · exact raw_compl_ok hraw hclosed P lo hi ε hε PR PB hpc

lemma rawPiece_valid' {ι : Type} (A B : Fin m → ℝ) (prof : ι → BankProfile) (P : BankProfile) (lo hi ε : ℝ)
    (pc : RawPiece ι m) (h : pc.Valid A B prof P lo hi ε) : pc.Valid' A B prof P lo hi ε := by
  rcases pc with γ | R | ⟨PR, PB⟩
  · exact ⟨h.1, le_of_eq h.2.1, h.2.2⟩
  · exact h
  · exact h

end

end DiagRamsey
