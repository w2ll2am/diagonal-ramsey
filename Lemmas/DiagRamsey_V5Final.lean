import Lemmas.DiagRamsey_V5Assemble

/-!
# v5 banks in Lean (P0.6): from `e^{zk}` to `3.5^k`

`le_pow_of_eventually`: if `R(k, k) ≤ e^{z k}` eventually and `expLeB z (7/2)` (so `e^z ≤ 7/2`), then
`∃ K, ∀ k ≥ K, R(k, k) ≤ (7/2)^k`. This is the statement shape of
`DiagRamsey.diagonal_le_three_point_five_pow`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.V5

open DiagRamsey.SharpCert

/-- A cheap rational literal for generated bank data: `qq a b = a / b`. -/
def qq (a : ℤ) (b : ℕ) : ℚ := (a : ℚ) / (b : ℚ)

theorem le_pow_of_eventually (z : ℚ) (hz : expLeB z (7 / 2) = true)
    (h : ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp ((z : ℝ) * k)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (ramseyNumber k k : ℝ) ≤ (7 / 2 : ℝ) ^ k := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 h
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  have he : Real.exp z ≤ 7 / 2 := by
    have := exp_le_of_expLeB hz
    push_cast at this
    linarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he k

/-! ## Splitting `BankD.check` per object (for per-profile kernel checks) -/

variable {nCtl m nR nC : ℕ}

def BankD.srcOk (D : BankD nCtl m nR nC) (h : Fin m) : Bool :=
  decide (0 < D.A h) && decide (0 < D.B h) && (D.src h).check D.pd D.lines (D.A h) (D.B h)

def BankD.rawOk (D : BankD nCtl m nR nC) (i : Fin nR) : Bool :=
  (D.raw i).ok (D.rawMin i) &&
    chainQ ((D.raw i).xs.headD 0) ((D.rawPieces i).map (fun x => (x.lo, x.hi))) ((D.raw i).xs.getLastD 0) &&
    (D.rawPieces i).all (RawD.check D.ctl D.A D.B D.pd D.i0 (D.raw i))

def BankD.clOk (D : BankD nCtl m nR nC) (i : Fin nC) : Bool :=
  (D.closed i).ok (D.closedMin i) &&
    chainQ ((D.closed i).xs.headD 0) ((D.closedPieces i).map (fun x => (x.lo, x.hi)))
      ((D.closed i).xs.getLastD 0) &&
    (D.closedPieces i).all (ClosedPD.check D.raw (D.closed i))

theorem BankD.check_of (D : BankD nCtl m nR nC) (hs : ∀ h, D.srcOk h = true) (hr : ∀ i, D.rawOk i = true)
    (hc : ∀ i, D.clOk i = true) : D.check = true := by
  simp only [BankD.srcOk, BankD.rawOk, BankD.clOk, Bool.and_eq_true, List.all_eq_true] at hs hr hc
  simp only [BankD.check, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨fun h _ => hs h, fun i _ => hr i⟩, fun i _ => hc i⟩

theorem BankD.rawOk_of (D : BankD nCtl m nR nC) (i : Fin nR)
    (h1 : ((D.raw i).ok (D.rawMin i) &&
      chainQ ((D.raw i).xs.headD 0) ((D.rawPieces i).map (fun x => (x.lo, x.hi))) ((D.raw i).xs.getLastD 0)) = true)
    (h2 : ∀ x ∈ D.rawPieces i, RawD.check D.ctl D.A D.B D.pd D.i0 (D.raw i) x = true) : D.rawOk i = true := by
  simp only [BankD.rawOk, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨h1, h2⟩

theorem BankD.clOk_of (D : BankD nCtl m nR nC) (i : Fin nC)
    (h1 : ((D.closed i).ok (D.closedMin i) &&
      chainQ ((D.closed i).xs.headD 0) ((D.closedPieces i).map (fun x => (x.lo, x.hi)))
        ((D.closed i).xs.getLastD 0)) = true)
    (h2 : ∀ x ∈ D.closedPieces i, ClosedPD.check D.raw (D.closed i) x = true) : D.clOk i = true := by
  simp only [BankD.clOk, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨h1, h2⟩

end DiagRamsey.V5
