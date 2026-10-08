import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_SourceBank

/-!
# Source banks: the route profile `g` and its discrete height

For a route node with strictly increasing knots `u` and positive slopes `d`:

* `RouteNode.g_eq_g₀`: `g s = g₀` for `s ≤ θ`; `g_ge`: `g ≥ g₀`; `g_mono`: `g` is monotone.
* `RouteNode.jump s = ∑_j d_j [u_j < s]` (the knot-crossing budget), `0 ≤ jump ≤ ∑_j d_j`.
* `RouteNode.step`: for `s₀ < s₁` with `s₁` in cell `j` and `s₁ - s₀ = 1/k`,
  `k (g s₁ - g s₀) + (jump s₁ - jump s₀) ≥ d_j`. Each knot crossing is paid by its own jump.
* `RouteNode.exists_cell`: every `s ∈ (θ, ω]` lies in some cell `(u_j, u_{j+1}]`.

This replaces the two-sided mesh estimate of the NL proof (§3, MESH) by a one-sided one; only the lower bound on
increments and the upper bound `jump ≤ ∑ d` are needed. Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

namespace RouteNode

variable {n m : ℕ} (R : RouteNode n m)

/-- The clamp `max 0 (min s u_{j+1} - u_j)`. -/
noncomputable def clamp (j : Fin R.M) (s : ℝ) : ℝ := max 0 (min s (R.u j.succ) - R.u j.castSucc)

lemma g_eq (s : ℝ) : R.g s = R.g₀ + ∑ j : Fin R.M, R.d j * R.clamp j s := rfl

lemma clamp_nonneg (j : Fin R.M) (s : ℝ) : 0 ≤ R.clamp j s := le_max_left _ _

lemma clamp_mono (j : Fin R.M) {s t : ℝ} (h : s ≤ t) : R.clamp j s ≤ R.clamp j t := by
  unfold clamp
  exact max_le_max le_rfl (by linarith [min_le_min_right (R.u j.succ) h])

lemma clamp_of_le (hmono : StrictMono R.u) (j : Fin R.M) {s : ℝ} (hs : s ≤ R.θ) : R.clamp j s = 0 := by
  unfold clamp
  have h1 : R.θ ≤ R.u j.castSucc := hmono.monotone (Fin.zero_le _)
  apply max_eq_left
  linarith [min_le_left s (R.u j.succ)]

lemma g_eq_g₀ (hmono : StrictMono R.u) {s : ℝ} (hs : s ≤ R.θ) : R.g s = R.g₀ := by
  rw [g_eq]; simp [R.clamp_of_le hmono _ hs]

lemma g_mono (hd : ∀ j, 0 < R.d j) {s t : ℝ} (h : s ≤ t) : R.g s ≤ R.g t := by
  rw [g_eq, g_eq]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (R.clamp_mono j h) (hd j).le)
  linarith

lemma g_ge (hd : ∀ j, 0 < R.d j) (s : ℝ) : R.g₀ ≤ R.g s := by
  rw [g_eq]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    mul_nonneg (hd j).le (R.clamp_nonneg j s))
  linarith

/-- The knot-crossing budget `∑_j d_j [u_j < s]`. -/
noncomputable def jump (s : ℝ) : ℝ := ∑ j : Fin R.M, if R.u j.castSucc < s then R.d j else 0

lemma jump_nonneg (hd : ∀ j, 0 < R.d j) (s : ℝ) : 0 ≤ R.jump s :=
  Finset.sum_nonneg fun j _ => by split_ifs <;> [exact (hd j).le; exact le_rfl]

lemma jump_le (hd : ∀ j, 0 < R.d j) (s : ℝ) : R.jump s ≤ ∑ j : Fin R.M, R.d j :=
  Finset.sum_le_sum fun j _ => by split_ifs <;> [exact le_rfl; exact (hd j).le]

lemma jump_of_le (hmono : StrictMono R.u) {s : ℝ} (hs : s ≤ R.θ) : R.jump s = 0 := by
  unfold jump
  apply Finset.sum_eq_zero
  intro j _
  have h1 : R.θ ≤ R.u j.castSucc := hmono.monotone (Fin.zero_le _)
  rw [if_neg (by linarith)]

lemma jump_mono_term (j : Fin R.M) {s t : ℝ} (h : s ≤ t) (hd : 0 < R.d j) :
    (if R.u j.castSucc < s then R.d j else 0) ≤ (if R.u j.castSucc < t then R.d j else 0) := by
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 h) h2
  · exact hd.le
  · exact le_rfl

/-- One step of the discrete height. -/
lemma step (hd : ∀ j, 0 < R.d j) (j : Fin R.M) {s₀ s₁ κ : ℝ} (hκ : 0 < κ) (hs : s₁ - s₀ = 1 / κ)
    (hj1 : R.u j.castSucc < s₁) (hj2 : s₁ ≤ R.u j.succ) :
    R.d j ≤ κ * (R.g s₁ - R.g s₀) + (R.jump s₁ - R.jump s₀) := by
  have h01 : s₀ ≤ s₁ := by have : 0 < 1 / κ := by positivity
                           linarith
  -- the sums split off the `j` term, the rest is nonnegative
  have hg : R.d j * (R.clamp j s₁ - R.clamp j s₀) ≤ R.g s₁ - R.g s₀ := by
    rw [g_eq, g_eq]
    have hsplit : ∑ i : Fin R.M, R.d i * R.clamp i s₁ - ∑ i : Fin R.M, R.d i * R.clamp i s₀ =
        ∑ i : Fin R.M, R.d i * (R.clamp i s₁ - R.clamp i s₀) := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
    have hle := Finset.single_le_sum (f := fun i => R.d i * (R.clamp i s₁ - R.clamp i s₀))
      (fun i _ => mul_nonneg (hd i).le (by linarith [R.clamp_mono i h01])) (Finset.mem_univ j)
    linarith
  have hjmp : (if R.u j.castSucc < s₁ then R.d j else 0) - (if R.u j.castSucc < s₀ then R.d j else 0) ≤
      R.jump s₁ - R.jump s₀ := by
    unfold jump
    rw [← Finset.sum_sub_distrib]
    have hle := Finset.single_le_sum
      (f := fun i => (if R.u i.castSucc < s₁ then R.d i else 0) - (if R.u i.castSucc < s₀ then R.d i else 0))
      (fun i _ => by have := R.jump_mono_term i h01 (hd i); linarith) (Finset.mem_univ j)
    simpa using hle
  rw [if_pos hj1] at hjmp
  by_cases h0 : R.u j.castSucc < s₀
  · rw [if_pos h0] at hjmp
    have hc : R.clamp j s₁ - R.clamp j s₀ = 1 / κ := by
      unfold clamp
      rw [min_eq_left hj2, min_eq_left (h01.trans hj2), max_eq_right (by linarith),
        max_eq_right (by linarith)]
      linarith
    rw [hc] at hg
    have : κ * (R.d j * (1 / κ)) = R.d j := by field_simp
    nlinarith
  · rw [if_neg h0] at hjmp
    have hc : 0 ≤ R.clamp j s₁ - R.clamp j s₀ := by linarith [R.clamp_mono j h01]
    have := mul_nonneg (hd j).le hc
    nlinarith

/-- Every `s ∈ (θ, ω]` lies in a cell. -/
lemma exists_cell (hmono : StrictMono R.u) {s : ℝ} (h1 : R.θ < s) (h2 : s ≤ R.ω) :
    ∃ j : Fin R.M, R.u j.castSucc < s ∧ s ≤ R.u j.succ := by
  -- the least knot index `i` with `s ≤ u i`
  have hex : ∃ i : ℕ, ∃ hi : i < R.M + 1, s ≤ R.u ⟨i, hi⟩ := ⟨R.M, Nat.lt_succ_self _, h2⟩
  classical
  set i := Nat.find hex with hidef
  obtain ⟨hi, hsi⟩ := Nat.find_spec hex
  have hi0 : i ≠ 0 := by
    intro h
    have e : (⟨i, hi⟩ : Fin (R.M + 1)) = 0 := Fin.ext (by simp [h])
    rw [e] at hsi
    exact absurd hsi (not_le.mpr h1)
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hjM : j < R.M := by omega
  refine ⟨⟨j, hjM⟩, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have := Nat.find_min hex (show j < i by omega)
    exact this ⟨by omega, by simpa [Fin.castSucc] using hc⟩
  · have : (⟨j, hjM⟩ : Fin R.M).succ = ⟨i, hi⟩ := by ext; simp [hj]
    rw [this]; exact hsi

end RouteNode

end DiagRamsey
