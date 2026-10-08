import Lemmas.DiagRamsey_SB_Leaf
import Lemmas.DiagRamsey_SB_RouteG
import Lemmas.DiagRamsey_retained_route

/-!
# Source banks: retained-route nodes are relatively valid

`proofs/DiagRamsey_source_bank_minimal_host_routes.md` §3, with one change of bookkeeping: the discrete height is
`Γ(t) = k (g(t/k) + h) + jump(t/k)` (`DiagRamsey_SB_RouteG`). Each step then satisfies `Γ(t-1) ≤ Γ(t) - d_{j(t)}`,
where `j(t)` is the cell of `t/k`, and `k (g + h) ≤ Γ ≤ k (g + h) + ∑ d`. The shift `h ≥ ε/2` pays the callee
constants, so no compactness minimum is needed.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

/-- Relative validity under an abstract host premise `Pm` (`RelValid A B` is the case `Pm = Prem A B`). -/
def RelValidP (Pm : ∀ (C : ℝ) (V : Type) [Fintype V] [DecidableEq V], Prop) (p lo hi : ℝ) (L : ℝ → ℝ) : Prop :=
  ∃ D : ℝ, 1 ≤ D ∧ ∃ K : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V], Pm C V →
    ∀ (G : SimpleGraph V) (W : Finset V) (k : ℕ) (r : ℝ), K ≤ k → lo ≤ r → r ≤ hi →
      p * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs G W : ℝ) →
      D * C * Real.exp (k * L r) ≤ (W.card : ℝ) → HasRedClique G W k ∨ HasBlueClique G W ⌊r * k⌋₊

/-- Validity at integer pairs `(k, t)` on proper sub-hosts `W ≠ univ` (what a route needs of its children). -/
def RelValidPr (Pm : ∀ (C : ℝ) (V : Type) [Fintype V] [DecidableEq V], Prop) (p lo hi : ℝ) (L : ℝ → ℝ) : Prop :=
  ∃ D : ℝ, 1 ≤ D ∧ ∃ K : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V], Pm C V →
    ∀ (G : SimpleGraph V) (W : Finset V) (k t : ℕ), W ≠ Finset.univ → K ≤ k → 0 < k → 0 < t →
      lo ≤ (t : ℝ) / k → (t : ℝ) / k ≤ hi →
      p * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs G W : ℝ) →
      D * C * Real.exp (k * L ((t : ℝ) / k)) ≤ (W.card : ℝ) → HasRedClique G W k ∨ HasBlueClique G W t

set_option maxHeartbeats 4000000 in
theorem route_relValidP {m n : ℕ} {A B : Fin m → ℝ} (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (Pm : ∀ (C : ℝ) (V : Type) [Fintype V] [DecidableEq V], Prop)
    (hPm : ∀ (C : ℝ) (V : Type) [Fintype V] [DecidableEq V], Pm C V → Prem A B C V)
    (R : RouteNode n m) (hγ : R.γ.Valid A B) (hpγ : R.γ.p < R.p) (hp1 : R.p < 1) (hM : 0 < R.M) (hθ : 0 < R.θ)
    (hmono : StrictMono R.u) (hg0 : 0 < R.g₀) (hε : 0 < R.ε)
    (pc lo hi : Fin R.M → ℝ) (Lc : Fin R.M → ℝ → ℝ)
    (hcall : ∀ j, RelValidPr Pm (pc j) (lo j) (hi j) (Lc j))
    (hlo : ∀ j, lo j ≤ R.u j.castSucc) (hhi : ∀ j, R.u j.succ ≤ hi j)
    (hpc0 : ∀ j, 0 < pc j) (hpc1 : ∀ j, pc j < 1)
    (hdj : ∀ j, -Real.log (1 - pc j) < R.d j)
    (hgt : ∀ j s, R.u j.castSucc ≤ s → s ≤ R.u j.succ → Lc j s < R.g s) :
    RelValidP Pm R.p R.θ R.ω R.out := by
  obtain ⟨L₀, hL₀⟩ := fh_of_prem R.γ hγ hA hB
  choose Dc hDc1 Kc hKc using hcall
  have hγ' := hγ
  obtain ⟨hπ0, hπ1, hμ0, hμ1, hw, -, -, -, -, -, -, -, hξ0, -, hξA, hy0, hyB, hν0, hνμ⟩ := hγ'
  set π := R.γ.p with hπdef
  set w := R.γ.w with hwdef
  -- terminal constants
  have hAγ : 0 < R.γ.Aγ := by
    have := Real.log_lt_log hξ0 hξA; rw [Real.log_exp] at this
    simp only [SharpControl.Aγ]; linarith [hA R.γ.σ]
  have hBγ : 0 < R.γ.Bγ := by
    have := Real.log_lt_log hy0 hyB; rw [Real.log_exp] at this
    simp only [SharpControl.Bγ]; linarith [hB R.γ.σ]
  have hbγ : 0 < R.γ.bγ := by
    simp only [SharpControl.bγ]; linarith [Real.log_neg hν0 (by linarith : R.γ.ν < 1)]
  -- slopes
  have hexp : ∀ j, Real.exp (-R.d j) < 1 - pc j := by
    intro j
    have h1 : 0 < 1 - pc j := by linarith [hpc1 j]
    calc Real.exp (-R.d j) < Real.exp (Real.log (1 - pc j)) := Real.exp_lt_exp.mpr (by linarith [hdj j])
      _ = 1 - pc j := Real.exp_log h1
  have hd : ∀ j, 0 < R.d j := by
    intro j
    have : Real.log (1 - pc j) < 0 := Real.log_neg (by linarith [hpc1 j]) (by linarith [hpc0 j])
    linarith [hdj j]
  have hgap : ∀ j, 0 < 1 - pc j - Real.exp (-R.d j) := fun j => by linarith [hexp j]
  set Q : Fin R.M → ℝ := fun j => (1 - pc j) / (1 - pc j - Real.exp (-R.d j)) with hQ
  set Qmax : ℝ := 1 + ∑ j, Q j with hQmax
  have hQpos : ∀ j, 0 < Q j := fun j => div_pos (by linarith [hpc1 j]) (hgap j)
  have hQle : ∀ j, Q j ≤ Qmax := by
    intro j
    have := single_le_sum (fun i (_ : i ∈ univ) => (hQpos i).le) (mem_univ j)
    rw [hQmax]; linarith
  have hQmax1 : 1 ≤ Qmax := by
    rw [hQmax]; linarith [sum_nonneg (fun i (_ : i ∈ univ) => (hQpos i).le)]
  set Dmax : ℝ := 1 + ∑ j, |Dc j| with hDmax
  have hDle : ∀ j, Dc j ≤ Dmax := by
    intro j
    have := single_le_sum (fun i (_ : i ∈ univ) => abs_nonneg (Dc i)) (mem_univ j)
    rw [hDmax]; linarith [le_abs_self (Dc j)]
  have hDmax1 : 1 ≤ Dmax := by
    rw [hDmax]; linarith [sum_nonneg (fun i (_ : i ∈ univ) => abs_nonneg (Dc i))]
  set Vd : ℝ := ∑ j, R.d j with hVd
  have hVd0 : 0 ≤ Vd := sum_nonneg fun j _ => (hd j).le
  set Kmax : ℕ := ∑ j, Kc j with hKmax
  have hKle : ∀ j, Kc j ≤ Kmax := fun j => single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
  -- the output constant
  have hpπ : 0 < R.p - π := by linarith
  set Dv : ℝ := 3 * (1 - π) / (R.p - π) with hDv
  have hDv3 : 3 ≤ Dv := by
    rw [hDv, le_div_iff₀ hpπ]; linarith
  -- the threshold
  obtain ⟨K, hK⟩ := exists_nat_ge ((Kmax : ℝ) + ((L₀ : ℝ) + 1) / R.θ +
    2 * (Vd + Real.log Dmax) / R.ε + Real.log Qmax / R.g₀)
  have hlogD : 0 ≤ Real.log Dmax := Real.log_nonneg hDmax1
  have hlogQ : 0 ≤ Real.log Qmax := Real.log_nonneg hQmax1
  refine ⟨Dv, by linarith, K, fun C hC V _ _ hPmV G W k r hk hr1 hr2 hdens hsize => ?_⟩
  have hP : Prem A B C V := hPm C V hPmV
  have hC0 : 0 < C := by linarith
  have hkK : (K : ℝ) ≤ k := by exact_mod_cast hk
  have t1 : 0 ≤ ((L₀ : ℝ) + 1) / R.θ := by positivity
  have t2 : 0 ≤ 2 * (Vd + Real.log Dmax) / R.ε := by positivity
  have t3 : 0 ≤ Real.log Qmax / R.g₀ := by positivity
  have hkKmax : (Kmax : ℝ) ≤ k := by linarith
  have hkθ : (L₀ : ℝ) + 1 ≤ R.θ * k := by
    have : ((L₀ : ℝ) + 1) / R.θ ≤ k := by linarith
    rw [div_le_iff₀ hθ] at this; linarith
  have hkε : Vd + Real.log Dmax ≤ k * R.ε / 2 := by
    have : 2 * (Vd + Real.log Dmax) / R.ε ≤ k := by linarith
    rw [div_le_iff₀ hε] at this; linarith
  have hkg : Real.log Qmax ≤ k * R.g₀ := by
    have : Real.log Qmax / R.g₀ ≤ k := by linarith
    rw [div_le_iff₀ hg0] at this; linarith
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hkθ; linarith [show (0 : ℝ) ≤ L₀ by positivity]
    · exact h
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  -- the output value
  set gr := R.g r with hgr
  set T : ℝ := (R.γ.Aγ + r * R.γ.Bγ + w * (R.θ * R.γ.bγ + gr - R.g₀)) / (1 + w) with hT
  set E : ℝ := max gr T with hE
  have hz : R.out r = R.ε + E := rfl
  set h : ℝ := E - gr + R.ε / 2 with hh
  have hEg : gr ≤ E := le_max_left _ _
  have hET : T ≤ E := le_max_right _ _
  have hgr0 : R.g₀ ≤ gr := R.g_ge hd r
  set z := R.out r with hzdef
  have hz0 : 0 < z := by rw [hz]; linarith
  -- terminal gap
  have hgapT : R.γ.Aγ + r * R.γ.Bγ + w * R.θ * R.γ.bγ ≤ z + w * (R.g₀ + h) := by
    have h1 : (1 + w) * T = R.γ.Aγ + r * R.γ.Bγ + w * R.θ * R.γ.bγ + w * gr - w * R.g₀ := by
      rw [hT]; field_simp; ring
    have h2 := mul_le_mul_of_nonneg_left hET (by linarith : (0 : ℝ) ≤ 1 + w)
    have hwε : 0 ≤ w * R.ε := by positivity
    rw [hz, hh]
    have e : R.ε + E + w * (R.g₀ + (E - gr + R.ε / 2)) =
        (1 + w) * E + w * R.g₀ - w * gr + R.ε + w * R.ε / 2 := by ring
    rw [e]; linarith
  -- the cut
  have hW3 : (3 : ℝ) ≤ W.card := by
    have h1 : 1 ≤ C * Real.exp (k * z) :=
      one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp (mul_pos hkpos hz0).le)
    have h2 : (3 : ℝ) * 1 ≤ Dv * (C * Real.exp (k * z)) := mul_le_mul hDv3 h1 (by norm_num) (by linarith)
    rw [← mul_assoc] at h2
    linarith
  have hW2 : 2 ≤ W.card := by exact_mod_cast (show (2 : ℝ) ≤ W.card by linarith)
  obtain ⟨X₀, hX₀W, hX3, hY3, hcross⟩ :=
    density_balanced_cut G W hW2 R.p (by unfold redPairs at hdens; exact hdens)
  set Y := W \ X₀ with hYdef
  have hYne : Y.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨hret, hZd⟩ := retained_rows G X₀ Y R.p π hπ1 hYne hcross
  set X := X₀.filter (fun v => π * (Y.card : ℝ) ≤ ((Y.filter (fun y => G.Adj v y)).card : ℝ)) with hXdef
  have hXX₀ : X ⊆ X₀ := filter_subset _ _
  have hezk : 0 < C * Real.exp (k * z) := by positivity
  have hXbig : C * Real.exp (k * z) ≤ X.card := by
    have h3 : (W.card : ℝ) ≤ 3 * X₀.card := by exact_mod_cast hX3
    have hD : Dv * (R.p - π) = 3 * (1 - π) := by rw [hDv]; field_simp
    have : (1 - π) * (C * Real.exp (k * z)) ≤ (1 - π) * X.card := by
      have e1 : (1 - π) * (C * Real.exp (k * z)) * 3 = (R.p - π) * (Dv * C * Real.exp (k * z)) := by
        rw [show (R.p - π) * (Dv * C * Real.exp (k * z)) = Dv * (R.p - π) * (C * Real.exp (k * z)) by ring,
          hD]; ring
      nlinarith [mul_le_mul_of_nonneg_left hsize hpπ.le]
    exact le_of_mul_le_mul_left this (by linarith)
  have hYbig : C * Real.exp (k * z) ≤ Y.card := by
    have h3 : (W.card : ℝ) ≤ 3 * Y.card := by exact_mod_cast hY3
    have : C * Real.exp (k * z) * 3 ≤ Dv * C * Real.exp (k * z) := by nlinarith
    linarith
  -- cells
  have hcell : ∀ s : ℝ, ∃ j : Fin R.M, R.θ < s → s ≤ R.ω → R.u j.castSucc < s ∧ s ≤ R.u j.succ := by
    intro s
    by_cases hs : R.θ < s ∧ s ≤ R.ω
    · obtain ⟨j, hj⟩ := R.exists_cell hmono hs.1 hs.2
      exact ⟨j, fun _ _ => hj⟩
    · exact ⟨⟨0, hM⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose J hJ using hcell
  -- the discrete height
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℕ → ℝ, Γ = fun t : ℕ => k * (R.g ((t : ℝ) / k) + h) + R.jump ((t : ℝ) / k) :=
    ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℕ → ℝ, Mf = fun t : ℕ => C * Real.exp (Γ t) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, q = fun t : ℕ => pc (J ((t : ℝ) / k)) := ⟨_, rfl⟩
  set ℓ := ⌊r * k⌋₊ with hℓdef
  set n₀ := ⌊R.θ * k⌋₊ with hn₀def
  have hℓr : (ℓ : ℝ) ≤ r * k := Nat.floor_le (by nlinarith)
  have hn₀θ : (n₀ : ℝ) ≤ R.θ * k := Nat.floor_le (by positivity)
  have hn₀L : L₀ + 1 ≤ n₀ := by
    rw [hn₀def]; apply Nat.le_floor; push_cast; linarith
  have hn₀ℓ : n₀ ≤ ℓ := Nat.floor_le_floor (by nlinarith)
  have hh2 : R.ε / 2 ≤ h := by rw [hh]; linarith
  have hΓlow : ∀ t : ℕ, k * (R.g ((t : ℝ) / k) + h) ≤ Γ t := fun t => by
    simp only [hΓ]; linarith [R.jump_nonneg hd ((t : ℝ) / k)]
  have hΓg0 : ∀ t : ℕ, Real.log Qmax ≤ Γ t := fun t => by
    have := hΓlow t
    have := R.g_ge hd ((t : ℝ) / k)
    nlinarith
  have hΓbase : ∀ t : ℕ, t ≤ n₀ → Γ t = k * (R.g₀ + h) := by
    intro t ht
    have hs : (t : ℝ) / k ≤ R.θ := by
      rw [div_le_iff₀ hkpos]; have : (t : ℝ) ≤ n₀ := by exact_mod_cast ht
      linarith
    simp only [hΓ, R.g_eq_g₀ hmono hs, R.jump_of_le hmono hs, add_zero]
  -- the induction
  have hMpos : ∀ t, 0 < Mf t := fun t => by rw [hMf]; positivity
  have key := retained_route_induction G X Y k ℓ n₀ ℓ Mf q hMpos ?base ?leaf ?pivot ℓ le_rfl X subset_rfl ?fin
  · rcases key with ⟨S, hS, hcl⟩ | ⟨S, hS, hcl⟩ | ⟨S, hS, hcl⟩
    · exact Or.inl ⟨S, hS.trans (union_subset (hXX₀.trans hX₀W) sdiff_subset), hcl⟩
    · exact Or.inr ⟨S, hS.trans (hXX₀.trans hX₀W), hcl⟩
    · exact Or.inr ⟨S, hS.trans sdiff_subset, hcl⟩
  case base =>
    intro t ht0 ht Z hZX hZne hZ
    have hZc : (0 : ℝ) < Z.card := by exact_mod_cast hZne.card_pos
    have hYc : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
    have hdZ : π ≤ redDensity G Z Y := by
      unfold redDensity; rw [le_div_iff₀ (mul_pos hZc hYc)]; exact hZd Z hZX
    have hdisj : Disjoint Z Y := disjoint_of_subset_left (hZX.trans hXX₀) disjoint_sdiff
    have hlZ : Real.log C + k * (R.g₀ + h) ≤ Real.log Z.card := by
      have := hZ; simp only [hMf, hΓbase t ht] at this
      rw [← Real.log_exp (k * (R.g₀ + h)), ← Real.log_mul hC0.ne' (Real.exp_pos _).ne']
      exact Real.log_le_log (by positivity) this
    have hlY : Real.log C + k * z ≤ Real.log Y.card := by
      rw [← Real.log_exp (k * z), ← Real.log_mul hC0.ne' (Real.exp_pos _).ne']
      exact Real.log_le_log (by positivity) hYbig
    have htθ : (t : ℝ) ≤ R.θ * k := by
      have : (t : ℝ) ≤ n₀ := by exact_mod_cast ht
      linarith
    refine hL₀ C hC V hP G k ℓ t hk0 ht0 (by omega) (by omega) Z Y hZne hYne hdisj hdZ ?_
    have e1 : (ℓ : ℝ) * R.γ.Bγ ≤ r * k * R.γ.Bγ := mul_le_mul_of_nonneg_right hℓr hBγ.le
    have e2 : w * t * R.γ.bγ ≤ w * (R.θ * k) * R.γ.bγ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htθ hw.le) hbγ.le
    have e3 := mul_le_mul_of_nonneg_left hgapT hkpos.le
    nlinarith [mul_le_mul_of_nonneg_left hlZ hw.le]
  case leaf =>
    intro t ht1 ht2 Z hZX hZ hZd'
    have htk : (t : ℝ) / k * k = t := by field_simp
    have hs1 : R.θ < (t : ℝ) / k := by
      rw [lt_div_iff₀ hkpos]
      have : (n₀ : ℝ) + 1 ≤ t := by exact_mod_cast ht1
      have : R.θ * k < n₀ + 1 := Nat.lt_floor_add_one _
      linarith
    have hs2 : (t : ℝ) / k ≤ R.ω := by
      rw [div_le_iff₀ hkpos]
      have : (t : ℝ) ≤ ℓ := by exact_mod_cast ht2
      nlinarith
    set j := J ((t : ℝ) / k) with hjdef
    obtain ⟨hj1, hj2⟩ := hJ ((t : ℝ) / k) hs1 hs2
    have hqt : q t = pc j := by rw [hq]
    rw [hqt] at hZd'
    have hZne : Z ≠ Finset.univ := by
      intro hZu
      obtain ⟨y, hy⟩ := hYne
      have : y ∈ Z := hZu ▸ Finset.mem_univ y
      exact (Finset.mem_sdiff.mp hy).2 (hXX₀ (hZX this))
    have hval := hKc j C hC V hPmV G Z k t hZne ((hKle j).trans (by exact_mod_cast hkKmax)) hk0 (by omega)
      ((hlo j).trans hj1.le) (hj2.trans (hhi j)) (by unfold redPairs; exact hZd') ?_
    · exact hval
    · refine le_trans ?_ hZ
      have hlt := hgt j ((t : ℝ) / k) hj1.le hj2
      have hΓt := hΓlow t
      have hDj : Real.log (Dc j) ≤ Real.log Dmax := Real.log_le_log (by linarith [hDc1 j]) (hDle j)
      have hkl := mul_lt_mul_of_pos_left hlt hkpos
      have hgh : k * (R.g ((t : ℝ) / k) + h) = k * R.g ((t : ℝ) / k) + k * h := by ring
      have hkh : k * (R.ε / 2) ≤ k * h := mul_le_mul_of_nonneg_left hh2 hkpos.le
      have hex : Dc j * Real.exp (k * Lc j ((t : ℝ) / k)) ≤ Real.exp (Γ t) := by
        calc Dc j * Real.exp (k * Lc j ((t : ℝ) / k))
            = Real.exp (Real.log (Dc j) + k * Lc j ((t : ℝ) / k)) := by
              rw [Real.exp_add, Real.exp_log (by linarith [hDc1 j])]
          _ ≤ Real.exp (Γ t) := by
              apply Real.exp_le_exp.mpr
              have : k * R.ε / 2 = k * (R.ε / 2) := by ring
              linarith
      have e : Dc j * C * Real.exp (k * Lc j ((t : ℝ) / k)) =
          C * (Dc j * Real.exp (k * Lc j ((t : ℝ) / k))) := by ring
      rw [e, hMf]
      exact mul_le_mul_of_nonneg_left hex hC0.le
  case pivot =>
    intro t ht1 ht2 Z hZX hZ
    have ht0 : 1 ≤ t := by omega
    have hs1 : R.θ < (t : ℝ) / k := by
      rw [lt_div_iff₀ hkpos]
      have : (n₀ : ℝ) + 1 ≤ t := by exact_mod_cast ht1
      have : R.θ * k < n₀ + 1 := Nat.lt_floor_add_one _
      linarith
    have hs2 : (t : ℝ) / k ≤ R.ω := by
      rw [div_le_iff₀ hkpos]
      have : (t : ℝ) ≤ ℓ := by exact_mod_cast ht2
      nlinarith
    set j := J ((t : ℝ) / k) with hjdef
    obtain ⟨hj1, hj2⟩ := hJ ((t : ℝ) / k) hs1 hs2
    have hcast : (((t - 1 : ℕ)) : ℝ) = t - 1 := by push_cast [Nat.cast_sub ht0]; ring
    have hdiff : (t : ℝ) / k - ((t - 1 : ℕ) : ℝ) / k = 1 / k := by rw [hcast]; ring
    have hstep := R.step hd j hkpos hdiff hj1 hj2
    have hΓd : Γ t - Γ (t - 1) = k * (R.g ((t : ℝ) / k) - R.g (((t - 1 : ℕ) : ℝ) / k)) +
        (R.jump ((t : ℝ) / k) - R.jump (((t - 1 : ℕ) : ℝ) / k)) := by
      rw [hΓ]; ring
    have hΓstep : Γ (t - 1) ≤ Γ t - R.d j := by linarith
    have hZpos : (0 : ℝ) < Z.card := lt_of_lt_of_le (hMpos t) hZ
    -- |Z| ≥ Q_j
    have hZQ : Q j ≤ Z.card := by
      have h1 : Qmax ≤ Real.exp (Γ t) := by
        rw [← Real.exp_log (by linarith : (0 : ℝ) < Qmax)]; exact Real.exp_le_exp.mpr (hΓg0 t)
      have h2 : Real.exp (Γ t) ≤ C * Real.exp (Γ t) := le_mul_of_one_le_left (Real.exp_pos _).le hC
      have hM' : Mf t = C * Real.exp (Γ t) := by rw [hMf]
      linarith [hQle j]
    have hpiv : Real.exp (-R.d j) * Z.card ≤ (1 - pc j) * ((Z.card : ℝ) - 1) := by
      have := hgap j
      have hQ' : (1 - pc j) ≤ (1 - pc j - Real.exp (-R.d j)) * Z.card := by
        have := hZQ; simp only [hQ] at this
        rw [div_le_iff₀ (hgap j)] at this; linarith
      nlinarith
    have hqt : q t = pc j := by rw [hq]
    rw [hqt]
    have hZ' : C * Real.exp (Γ t) ≤ Z.card := by rw [hMf] at hZ; exact hZ
    calc Mf (t - 1) = C * Real.exp (Γ (t - 1)) := by rw [hMf]
      _ ≤ C * Real.exp (Γ t - R.d j) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hΓstep) hC0.le
      _ = Real.exp (-R.d j) * (C * Real.exp (Γ t)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ Real.exp (-R.d j) * Z.card := mul_le_mul_of_nonneg_left hZ' (Real.exp_pos _).le
      _ ≤ (1 - pc j) * ((Z.card : ℝ) - 1) := hpiv
  case fin =>
    refine le_trans ?_ hXbig
    rw [hMf]
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply Real.exp_le_exp.mpr
    have hsr : (ℓ : ℝ) / k ≤ r := by rw [div_le_iff₀ hkpos]; linarith
    have hgm := R.g_mono hd hsr
    have hjl := R.jump_le hd ((ℓ : ℝ) / k)
    have hΓl : Γ ℓ = k * R.g ((ℓ : ℝ) / k) + k * h + R.jump ((ℓ : ℝ) / k) := by rw [hΓ]; ring
    have hkg' := mul_le_mul_of_nonneg_left hgm hkpos.le
    have hzE : k * z = k * R.ε + k * E := by rw [hz]; ring
    have hkh : k * h = k * E - k * gr + k * R.ε / 2 := by rw [hh]; ring
    rw [hΓl, hzE, hkh]
    linarith

theorem relValid_iff {m : ℕ} (A B : Fin m → ℝ) (p lo hi : ℝ) (L : ℝ → ℝ) :
    RelValid A B p lo hi L ↔ RelValidP (fun C V _ _ => Prem A B C V) p lo hi L := Iff.rfl

theorem relValidPr_of_relValidP {Pm : ∀ (C : ℝ) (V : Type) [Fintype V] [DecidableEq V], Prop} {p lo hi : ℝ}
    {L : ℝ → ℝ} (h : RelValidP Pm p lo hi L) : RelValidPr Pm p lo hi L := by
  obtain ⟨D, hD, K, hK⟩ := h
  refine ⟨D, hD, K, fun C hC V _ _ hV G W k t _ hk hk0 _ h1 h2 h3 h4 => ?_⟩
  have := hK C hC V hV G W k ((t : ℝ) / k) hk h1 h2 h3 h4
  have hkk : (t : ℝ) / k * k = t := by field_simp
  rwa [hkk, Nat.floor_natCast] at this

/-- The source-bank form: callees relatively valid under the source premise. -/
theorem route_relValid {m n : ℕ} {A B : Fin m → ℝ} (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (R : RouteNode n m) (hγ : R.γ.Valid A B) (hpγ : R.γ.p < R.p) (hp1 : R.p < 1) (hM : 0 < R.M) (hθ : 0 < R.θ)
    (hmono : StrictMono R.u) (hg0 : 0 < R.g₀) (hε : 0 < R.ε)
    (pc lo hi : Fin R.M → ℝ) (Lc : Fin R.M → ℝ → ℝ)
    (hcall : ∀ j, RelValid A B (pc j) (lo j) (hi j) (Lc j))
    (hlo : ∀ j, lo j ≤ R.u j.castSucc) (hhi : ∀ j, R.u j.succ ≤ hi j)
    (hpc0 : ∀ j, 0 < pc j) (hpc1 : ∀ j, pc j < 1)
    (hdj : ∀ j, -Real.log (1 - pc j) < R.d j)
    (hgt : ∀ j s, R.u j.castSucc ≤ s → s ≤ R.u j.succ → Lc j s < R.g s) :
    RelValid A B R.p R.θ R.ω R.out :=
  route_relValidP hA hB (fun C V _ _ => Prem A B C V) (fun _ _ _ _ h => h) R hγ hpγ hp1 hM hθ hmono hg0 hε
    pc lo hi Lc (fun j => relValidPr_of_relValidP (hcall j)) hlo hhi hpc0 hpc1 hdj hgt

end DiagRamsey
