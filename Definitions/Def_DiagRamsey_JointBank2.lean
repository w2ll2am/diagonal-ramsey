import Definitions.Def_DiagRamsey_JointBank

/-!
# Integer-target banks, v2 piece condition

`RawPiece.Valid'` is `RawPiece.Valid` (`Def_DiagRamsey_JointBank`) except that a leaf needs only `p_γ ≤ p_R`
(v1: `p_γ = p_R`). This is the condition the v5/v5m checkers accept. Route and complementary pieces are unchanged.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

/-- The v2 hypotheses on a RAW piece: as `RawPiece.Valid`, with `γ.p ≤ P.p` for leaves. -/
def RawPiece.Valid' {ι : Type} {m : ℕ} (A B : Fin m → ℝ) (prof : ι → BankProfile) (P : BankProfile)
    (lo hi ε : ℝ) : RawPiece ι m → Prop
  | .leaf γ => γ.Valid A B ∧ γ.p ≤ P.p ∧ ∀ r : ℝ, lo ≤ r → r ≤ hi → ε + γ.leafLine r ≤ P.L r
  | .route R => (RawPiece.route R).Valid A B prof P lo hi ε
  | .compl PR PB => (RawPiece.compl PR PB).Valid A B prof P lo hi ε

end DiagRamsey
