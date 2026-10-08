import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_Basic
import Definitions.Def_DiagRamsey_LuWangSource
import Definitions.Def_DiagRamsey_SourceBank
import Definitions.Def_DiagRamsey_JointBank
import Definitions.Def_DiagRamsey_JointBank2
import Bridge.Foundations
import Lemmas.DiagRamsey_JB_Closed

/-!
# Joint banks: the host-order induction (v2 hypotheses)

`proofs/DiagRamsey_joint_integer_target_bank.md` §§1–2. Induction on the host order. On a host `V` whose proper
sub-hosts satisfy every assertion (`JPrem`, obtained from smaller hosts `↥Z` by `allOn_of_induced`):
* Stage 1 (RAW): grounding for `k < K`, otherwise `raw_piece_ok'`.
* Stage 2 (CLOSED): grounding, otherwise `closed_piece_ok` on top of Stage 1 in both colour namings.
* Stage 3 (SOURCE): Erdős–Szekeres for small `min(k, b)`; Lu–Wang for ratios outside `(Lo, Hi)` and for grounded
  cells; otherwise the cell's red profile, or its blue profile after exchanging colours.
`joint_integer_target_bank` (v1) and `joint_integer_target_bank_v2` both follow.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

set_option maxHeartbeats 8000000 in
theorem joint_main_v2 {m nR nC : ℕ}
    (A B : Fin m → ℝ) (hA : ∀ h, 0 < A h) (hB : ∀ h, 0 < B h)
    (raw : Fin nR → BankProfile) (closed : Fin nC → BankProfile)
    (hraw : ∀ i, (raw i).Valid) (hclosed : ∀ i, (closed i).Valid)
    -- (R) RAW realizations
    (nRP : Fin nR → ℕ) (rpLo rpHi rpEps : (i : Fin nR) → Fin (nRP i) → ℝ)
    (rp : (i : Fin nR) → Fin (nRP i) → RawPiece (Fin nR ⊕ Fin nC) m)
    (hrcover : ∀ i (r : ℝ), (raw i).lo ≤ r → r ≤ (raw i).hi → ∃ J, rpLo i J ≤ r ∧ r ≤ rpHi i J)
    (hrp : ∀ i J, 0 < rpEps i J ∧
      (rp i J).Valid' A B (Sum.elim raw closed) (raw i) (rpLo i J) (rpHi i J) (rpEps i J))
    -- (U) CLOSED realizations
    (nCP : Fin nC → ℕ) (cpLo cpHi : (i : Fin nC) → Fin (nCP i) → ℝ)
    (cp : (i : Fin nC) → Fin (nCP i) → ClosedPiece nR)
    (hccover : ∀ i (r : ℝ), (closed i).lo ≤ r → r ≤ (closed i).hi → ∃ J, cpLo i J ≤ r ∧ r ≤ cpHi i J)
    (hcp : ∀ i J, (cp i J).Valid raw (closed i) (cpLo i J) (cpHi i J))
    -- (S) SOURCE cover
    (Lo Hi ε η : Fin m → ℝ) (hLo : ∀ h, 0 < Lo h) (hLH : ∀ h, Lo h < Hi h)
    (hε : ∀ h, 0 < ε h) (hη : ∀ h, 0 < η h)
    (htail : ∀ h (t : ℝ), 0 < t → (t ≤ Lo h ∨ Hi h ≤ t) →
      symmetricProfile luWangSource 1 t ≤ A h + B h * t - ε h * (1 + t))
    (nSC : Fin m → ℕ) (scLo scHi : (h : Fin m) → Fin (nSC h) → ℝ)
    (sc : (h : Fin m) → Fin (nSC h) → SourceCell (Fin nR ⊕ Fin nC))
    (hscover : ∀ h (t : ℝ), Lo h ≤ t → t ≤ Hi h → ∃ J, scLo h J ≤ t ∧ t ≤ scHi h J)
    (hsc : ∀ h J, (sc h J).Valid (Sum.elim raw closed) (A h) (B h) (η h) (scLo h J) (scHi h J)) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ i, (raw i).Assert C) ∧ (∀ i, (closed i).Assert C) ∧
      ∀ h (k b : ℕ), 0 < k → 0 < b → ∀ N : ℕ,
        C * Real.exp (A h * k + B h * b) ≤ (N : ℝ) → RamseyArrows k b N := by
  set prof := Sum.elim raw closed with hprof
  -- piece thresholds
  have hpiece : ∀ i J, ∃ KJ, PieceOK raw closed A B (raw i) (rpLo i J) (rpHi i J) KJ := fun i J =>
    raw_piece_ok' hA hB hraw hclosed (raw i) (hraw i) _ _ _ (hrp i J).1 (rp i J) (hrp i J).2
  choose KJ hKJ using hpiece
  set K : ℕ := 1 + (∑ i, ∑ J, KJ i J) + ∑ i, ∑ J, kRM (cp i J) with hKdef
  have hKJle : ∀ i J, KJ i J ≤ K := by
    intro i J
    have h1 := single_le_sum (f := fun J => KJ i J) (fun _ _ => Nat.zero_le _) (mem_univ J)
    have h2 := single_le_sum (f := fun i => ∑ J, KJ i J) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  have hKRMle : ∀ i J, kRM (cp i J) ≤ K := by
    intro i J
    have h1 := single_le_sum (f := fun J => kRM (cp i J)) (fun _ _ => Nat.zero_le _) (mem_univ J)
    have h2 := single_le_sum (f := fun i => ∑ J, kRM (cp i J)) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  have hK1 : 1 ≤ K := by omega
  -- the ratio bound M
  set M : ℝ := 1 + ∑ i, |(raw i).hi| + ∑ i, |(closed i).hi| with hM
  have hMr : ∀ i, (raw i).hi ≤ M := by
    intro i
    have := single_le_sum (f := fun i => |(raw i).hi|) (fun _ _ => abs_nonneg _) (mem_univ i)
    have := sum_nonneg (fun i (_ : i ∈ univ) => abs_nonneg (closed i).hi)
    linarith [le_abs_self (raw i).hi]
  have hMc : ∀ i, (closed i).hi ≤ M := by
    intro i
    have := single_le_sum (f := fun i => |(closed i).hi|) (fun _ _ => abs_nonneg _) (mem_univ i)
    have := sum_nonneg (fun i (_ : i ∈ univ) => abs_nonneg (raw i).hi)
    linarith [le_abs_self (closed i).hi]
  have hM1 : 1 ≤ M := by
    have := sum_nonneg (fun i (_ : i ∈ univ) => abs_nonneg (raw i).hi)
    have := sum_nonneg (fun i (_ : i ∈ univ) => abs_nonneg (closed i).hi)
    linarith
  set BB : ℕ := ⌈M⌉₊ * K + 1 with hBB
  have hbBB : ∀ (P : BankProfile), P.hi ≤ M → ∀ k b : ℕ, 0 < k → k < K → (b : ℝ) / k ≤ P.hi → b < BB := by
    intro P hP k b hk hkK hb
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : (b : ℝ) ≤ M * k := by rw [div_le_iff₀ hkpos] at hb; nlinarith
    have h2 : M * k ≤ (⌈M⌉₊ : ℝ) * K := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hkK.le
      nlinarith [Nat.le_ceil M]
    have : (b : ℝ) < BB := by rw [hBB]; push_cast; linarith
    exact_mod_cast this
  -- the source constants
  set ε' : Fin m → ℝ := fun h => min (ε h) (η h) with hε'
  have hε'0 : ∀ h, 0 < ε' h := fun h => lt_min (hε h) (hη h)
  have hLW := lu_wang_uniform_source_bound
  choose Cε hCε1 hCε using fun h => hLW (ε' h) (hε'0 h)
  set cmin : Fin m → ℝ := fun h => min (A h) (B h) with hcmin
  have hcmin0 : ∀ h, 0 < cmin h := fun h => lt_min (hA h) (hB h)
  set Csm : ℝ := ∑ h, (K.factorial : ℝ) / cmin h ^ K with hCsm
  have hCsm0 : ∀ h, (K.factorial : ℝ) / cmin h ^ K ≤ Csm := fun h =>
    single_le_sum (fun j (_ : j ∈ univ) => div_nonneg (by positivity) (pow_pos (hcmin0 j) K).le) (mem_univ h)
  have hCsm_nn : 0 ≤ Csm := sum_nonneg fun j _ => div_nonneg (by positivity) (pow_pos (hcmin0 j) K).le
  have hCε0 : ∀ h, Cε h ≤ ∑ j, Cε j := fun h =>
    single_le_sum (fun j (_ : j ∈ univ) => by linarith [hCε1 j]) (mem_univ h)
  have hCεs : 0 ≤ ∑ j, Cε j := sum_nonneg fun j _ => by linarith [hCε1 j]
  set C : ℝ := cProf K BB + Csm + ∑ h, Cε h with hCdef
  have hCprof : cProf K BB ≤ C := by rw [hCdef]; linarith
  have hC1 : 1 ≤ C := by have := cProf_one K BB; linarith
  have hC0 : 0 < C := by linarith
  -- profile positivity on the domain
  have hLpos : ∀ (P : BankProfile), P.Valid → ∀ r, P.lo ≤ r → r ≤ P.hi → 0 < P.L r :=
    fun P hP r h1 h2 => hP.2.2.2.2 r h1 h2
  -- the induction on the host order
  have main : ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ G : SimpleGraph V, AllOn raw closed A B C G Finset.univ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro V _ _ hVn
    -- the premise on proper sub-hosts
    have hJ : JPrem raw closed A B C V := by
      intro G Z hZ
      have hlt : Z.card < n := by
        rw [← hVn]
        have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hZ)
        simpa using this
      exact allOn_of_induced G Z (ih Z.card hlt Z (by simp) (induced G Z))
    have hcardpos : ∀ x : ℝ, 0 ≤ x → C * Real.exp x ≤ ((Finset.univ : Finset V).card : ℝ) →
        1 ≤ ((Finset.univ : Finset V).card : ℝ) := fun x hx hs =>
      le_trans (one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hx)) hs
    -- Stage 1: RAW
    have hRAW : ∀ (G : SimpleGraph V) (i : Fin nR), AssertOn (raw i) C G Finset.univ := by
      intro G i k b hk hb h1 h2 hd hs
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hL0 := hLpos (raw i) (hraw i) _ h1 h2
      by_cases hkK : k < K
      · exact ground G hCprof hk hb hkK (hbBB (raw i) (hMr i) k b hk hkK h2) (by positivity) hs
      push_neg at hkK
      obtain ⟨J, hJ1, hJ2⟩ := hrcover i _ h1 h2
      exact hKJ i J C hC1 V hJ G k b ((hKJle i J).trans hkK) hk hb hJ1 hJ2 h1 hd hs
    -- Stage 2: CLOSED
    have hCL : ∀ (G : SimpleGraph V) (i : Fin nC), AssertOn (closed i) C G Finset.univ := by
      intro G i k b hk hb h1 h2 hd hs
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
      have hL0 := hLpos (closed i) (hclosed i) _ h1 h2
      by_cases hkK : k < K
      · exact ground G hCprof hk hb hkK (hbBB (closed i) (hMc i) k b hk hkK h2) (by positivity) hs
      push_neg at hkK
      obtain ⟨J, hJ1, hJ2⟩ := hccover i _ h1 h2
      exact closed_piece_ok raw hraw (closed i) _ _ (cp i J) (hcp i J) C hC1 hRAW G k b
        ((hKRMle i J).trans hkK) hk hb hJ1 hJ2 hd hs
    have hPROF : ∀ (G : SimpleGraph V) (c : Fin nR ⊕ Fin nC), AssertOn (prof c) C G Finset.univ := by
      intro G c; rcases c with i | i
      · exact hRAW G i
      · exact hCL G i
    -- Stage 3: SOURCE
    refine fun G => ⟨hRAW G, hCL G, fun h k b hk hb hN => ?_⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
    set NV := (Finset.univ : Finset V).card with hNV
    -- small cases
    by_cases hsmall : k < K ∨ b < K
    · obtain ⟨a', rfl⟩ : ∃ a', k = a' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      refine clique_of_arrows G (ClosureEnv.arrows_choose (a' + b') a' b' rfl) ?_
      have hx1 : (1 : ℝ) ≤ ((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hchoose : (((a' + b').choose a' : ℕ) : ℝ) ≤ (((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ)) ^ K := by
        have hle : ((a' + b').choose a' : ℕ) ≤ (a' + b') ^ (min a' b') := by
          rcases le_total a' b' with hh | hh
          · rw [min_eq_left hh]; exact Nat.choose_le_pow _ _
          · rw [min_eq_right hh, Nat.choose_symm_add]; exact Nat.choose_le_pow _ _
        have hmK : min a' b' ≤ K := by omega
        calc (((a' + b').choose a' : ℕ) : ℝ) ≤ ((a' + b' : ℕ) : ℝ) ^ (min a' b') := by exact_mod_cast hle
          _ ≤ (((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ)) ^ (min a' b') := by
              apply pow_le_pow_left₀ (by positivity); push_cast; linarith
          _ ≤ (((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ)) ^ K := pow_le_pow_right₀ hx1 hmK
      have hpe := pow_le_exp (hcmin0 h)
        (by positivity : (0 : ℝ) ≤ ((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ)) K
      have hcab : cmin h * (((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ)) ≤
          A h * ((a' + 1 : ℕ) : ℝ) + B h * ((b' + 1 : ℕ) : ℝ) := by
        have h1 : cmin h ≤ A h := min_le_left _ _
        have h2 : cmin h ≤ B h := min_le_right _ _
        nlinarith
      have hCs : (K.factorial : ℝ) / cmin h ^ K ≤ C := by rw [hCdef]; linarith [hCsm0 h, cProf_one K BB]
      calc (((a' + b').choose a' : ℕ) : ℝ) ≤ (K.factorial : ℝ) / cmin h ^ K *
            Real.exp (cmin h * (((a' + 1 : ℕ) : ℝ) + ((b' + 1 : ℕ) : ℝ))) := hchoose.trans hpe
        _ ≤ C * Real.exp (A h * ((a' + 1 : ℕ) : ℝ) + B h * ((b' + 1 : ℕ) : ℝ)) :=
            mul_le_mul hCs (Real.exp_le_exp.mpr hcab) (Real.exp_pos _).le hC0.le
        _ ≤ NV := hN
    push_neg at hsmall
    obtain ⟨hkK, hbK⟩ := hsmall
    set t : ℝ := (b : ℝ) / k with htdef
    have ht0 : 0 < t := div_pos hbpos hkpos
    have hta : t * k = b := by rw [htdef]; field_simp
    -- the Lu–Wang bound at slope `ε'`, used for the tail and for grounded cells
    have hLWcase : symmetricProfile luWangSource 1 t ≤ A h + B h * t - ε' h * (1 + t) →
        HasRedClique G Finset.univ k ∨ HasBlueClique G Finset.univ b := by
      intro hF
      refine clique_of_arrows G (hCε h k b hk hb NV (le_trans ?_ hN)) le_rfl
      have hhom := symmetricProfile_hom luWangSource (b := (b : ℝ)) hkpos
      rw [← htdef] at hhom
      have hexp : symmetricProfile luWangSource (k : ℝ) (b : ℝ) + ε' h * ((k : ℝ) + (b : ℝ)) ≤
          A h * k + B h * b := by
        rw [hhom]
        have := mul_le_mul_of_nonneg_left hF hkpos.le
        have e : (k : ℝ) * (A h + B h * t - ε' h * (1 + t)) =
            A h * k + B h * (t * k) - ε' h * (k + t * k) := by ring
        rw [e, hta] at this
        linarith
      exact mul_le_mul (by rw [hCdef]; linarith [hCε0 h, cProf_one K BB]) (Real.exp_le_exp.mpr hexp)
        (Real.exp_pos _).le hC0.le
    by_cases htl : t ≤ Lo h ∨ Hi h ≤ t
    · exact hLWcase ((htail h t ht0 htl).trans (by
        have : ε' h * (1 + t) ≤ ε h * (1 + t) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
        linarith))
    push_neg at htl
    obtain ⟨J, hJ1, hJ2⟩ := hscover h t htl.1.le htl.2.le
    have hcellv := hsc h J
    rcases hcs : sc h J with _ | ⟨PR, PB⟩
    · -- grounded cell
      rw [hcs] at hcellv
      exact hLWcase ((hcellv t ht0 hJ1 hJ2).trans (by
        have : ε' h * (1 + t) ≤ η h * (1 + t) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        linarith))
    · rw [hcs] at hcellv
      obtain ⟨hpsum, hRlo, hRhi, hrest⟩ := hcellv
      obtain ⟨hBlo, hBhi, hmax⟩ := hrest t hJ1 hJ2
      have hsize : ∀ x : ℝ, x ≤ k * (A h + B h * t - η h * (1 + t)) → C * Real.exp x ≤ NV := by
        intro x hx
        refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0.le) hN
        have e : (k : ℝ) * (A h + B h * t - η h * (1 + t)) = A h * k + B h * (t * k) - η h * (k + t * k) := by
          ring
        rw [e, hta] at hx
        have : 0 ≤ η h * ((k : ℝ) + b) := by have := hη h; positivity
        linarith
      have hnn := natsq_nonneg NV
      by_cases hred : (prof PR).p * ((NV : ℝ) * ((NV : ℝ) - 1)) ≤ (redPairs G Finset.univ : ℝ)
      · exact hPROF G PR k b hk hb (hRlo.trans hJ1) (hJ2.trans hRhi) hred
          (hsize _ (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hmax) hkpos.le))
      · have hblue := density_split G Finset.univ hpsum hnn hred
        have hkb : (k : ℝ) / b = 1 / t := by rw [htdef]; field_simp
        have hres := hPROF Gᶜ PB b k hb hk (by rw [hkb]; exact hBlo) (by rw [hkb]; exact hBhi) hblue
          (hsize _ (by
            rw [hkb]
            have e : (b : ℝ) * (prof PB).L (1 / t) = k * (t * (prof PB).L (1 / t)) := by
              rw [← hta]; ring
            rw [e]
            exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hmax) hkpos.le))
        rcases hres with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
        · exact Or.inr ⟨T, hT, hc⟩
        · rw [compl_compl] at hc; exact Or.inl ⟨T, hT, hc⟩
  -- conversion to hosts `Fin N`
  have hFin : ∀ (N : ℕ) (G : SimpleGraph (Fin N)), AllOn raw closed A B C G Finset.univ :=
    fun N G => main N (Fin N) (Fintype.card_fin N) G
  have hcardN : ∀ N : ℕ, ((Finset.univ : Finset (Fin N)).card : ℝ) = N := fun N => by simp
  have hassert : ∀ (P : BankProfile), P.Valid →
      (∀ (N : ℕ) (G : SimpleGraph (Fin N)), AssertOn P C G Finset.univ) → P.Assert C := by
    intro P hP hA' k b hk hb h1 h2 N G hd hs
    have hres := hA' N G k b hk hb h1 h2 (pairs_of_density G hP.1 hd) (by rw [hcardN]; exact hs)
    rcases hres with ⟨S, -, hc⟩ | ⟨S, -, hc⟩
    · exact Or.inl ⟨S, hc⟩
    · exact Or.inr ⟨S, hc⟩
  refine ⟨C, hC1, fun i => hassert _ (hraw i) (fun N G => (hFin N G).1 i),
    fun i => hassert _ (hclosed i) (fun N G => (hFin N G).2.1 i), fun h k b hk hb N hN G => ?_⟩
  rcases (hFin N G).2.2 h k b hk hb (by rw [hcardN]; exact hN) with ⟨S, -, hc⟩ | ⟨S, -, hc⟩
  · exact Or.inl ⟨S, hc⟩
  · exact Or.inr ⟨S, hc⟩

end DiagRamsey
