import Solutions.SharpCert.Gen
import Solutions.SharpCertFast.CheckerI

/-! isidore-the-farmer: block-wise `lineBelow` (bisecting on failure). For a block of cells with slopes `s = w * a` in
`[sLo, sHi]`, if one λ-grid point `P` minimises `E + s * lam` over `pts` at both ends, it minimises it on
the whole interval (affine in `s`), so each cell needs one comparison instead of `pts.length`.
Falls back to the full scan otherwise; sound either way. -/

namespace DiagRamsey.SharpCert.IExp
open DiagRamsey.SharpCert

def ptVal (s : ℚ) (P : Pt) : ℚ := P.E + s * P.lam

def argminPt (s : ℚ) : Pt → List Pt → Pt
  | P, [] => P
  | P, Q :: qs => argminPt s (if ptVal s Q < ptVal s P then Q else P) qs

/-- Envelope test with no fallback: `false` if `P` is not minimal at both slope ends. -/
def blockAt (g : Glob) (pts : List Pt) (cs : List Cell) (sLo sHi : ℚ) (P : Pt) : Bool :=
  pts.all (fun Q => decide (ptVal sLo P ≤ ptVal sLo Q) && decide (ptVal sHi P ≤ ptVal sHi Q)) &&
    cs.all (fun c => c.skip || (decide (sLo ≤ g.w * c.a) && decide (g.w * c.a ≤ sHi) &&
      decide (c.c - g.w * c.a * P.lam ≤ P.E)))

def blockTry (g : Glob) (pts : List Pt) (cs : List Cell) : Bool :=
  match pts, cs with
  | [], _ => true
  | _, [] => true
  | P0 :: ps, c0 :: _ =>
    let s0 := g.w * c0.a
    let s1 := g.w * (cs.getLastD c0).a
    blockAt g pts cs (min s0 s1) (max s0 s1) (argminPt ((s0 + s1) / 2) P0 ps)

/-- Try the envelope on the block; on failure bisect (fuel `n`), finally scan. -/
def blockRec (g : Glob) (pts : List Pt) : ℕ → List Cell → Bool
  | 0, cs => cs.all (fun c => pts.all (lineBelow g c))
  | n + 1, cs => blockTry g pts cs ||
      (blockRec g pts n (cs.take (cs.length / 2)) && blockRec g pts n (cs.drop (cs.length / 2)))

lemma affine_le {a b u v sLo sHi s : ℚ} (h1 : sLo ≤ s) (h2 : s ≤ sHi)
    (hLo : a + sLo * u ≤ b + sLo * v) (hHi : a + sHi * u ≤ b + sHi * v) :
    a + s * u ≤ b + s * v := by
  rcases le_total 0 (v - u) with hd | hd
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) hd]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hd)]

lemma blockAt_spec {g : Glob} {pts : List Pt} {cs : List Cell} {sLo sHi : ℚ} {P : Pt}
    (h : blockAt g pts cs sLo sHi P = true) : ∀ c ∈ cs, ∀ Q ∈ pts, lineBelow g c Q = true := by
  intro c hc Q hQ
  unfold blockAt at h
  rw [Bool.and_eq_true] at h
  have hc' := List.all_eq_true.mp h.2 c hc
  have hQ' := List.all_eq_true.mp h.1 Q hQ
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc' hQ'
  unfold lineBelow
  rcases hc' with hs | ⟨⟨h1, h2⟩, h3⟩
  · simp [hs]
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    unfold ptVal at hQ'
    have := affine_le h1 h2 hQ'.1 hQ'.2
    linarith

lemma blockTry_spec {g : Glob} {pts : List Pt} {cs : List Cell}
    (h : blockTry g pts cs = true) : ∀ c ∈ cs, ∀ Q ∈ pts, lineBelow g c Q = true := by
  unfold blockTry at h
  split at h
  · intro c _ Q hQ; simp at hQ
  · intro c hc; simp at hc
  · exact blockAt_spec h

lemma blockRec_spec {g : Glob} {pts : List Pt} :
    ∀ (n : ℕ) {cs : List Cell}, blockRec g pts n cs = true →
      ∀ c ∈ cs, ∀ Q ∈ pts, lineBelow g c Q = true
  | 0, cs, h => fun c hc Q hQ => List.all_eq_true.mp (List.all_eq_true.mp h c hc) Q hQ
  | n + 1, cs, h => by
    intro c hc Q hQ
    unfold blockRec at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact blockTry_spec h c hc Q hQ
    · rw [Bool.and_eq_true] at h
      rw [← List.take_append_drop (cs.length / 2) cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact blockRec_spec n h.1 c hc Q hQ
      · exact blockRec_spec n h.2 c hc Q hQ

theorem full_of_block {g : Glob} {pts : List Pt} {l : List Cell}
    (h : (l.all (cellOkI g) && blockRec g pts 6 (l.filter (fun c => !c.skip))) = true) :
    l.all (cellFullI g pts) = true := by
  rw [Bool.and_eq_true] at h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  simp only [cellFullI, Bool.and_eq_true, List.all_eq_true]
  refine ⟨h.1 c hc, fun Q hQ => ?_⟩
  cases hs : c.skip
  · exact blockRec_spec 6 h.2 c (List.mem_filter.2 ⟨hc, by simp [hs]⟩) Q hQ
  · simp [lineBelow, hs]


/-! Per-control lower envelope: segments `(lo, hi, j)` of grid indices with point `pts[j]`. -/
def sOf (g : Glob) (K k : ℕ) : ℚ := g.w * gridPt g K k

def minV (s : ℚ) : List Pt → ℚ
  | [] => 0
  | [P] => ptVal s P
  | P :: Q :: ps => min (ptVal s P) (minV s (Q :: ps))

lemma minV_le (s : ℚ) : ∀ (l : List Pt), ∀ Q ∈ l, minV s l ≤ ptVal s Q
  | [], Q, h => by simp at h
  | [P], Q, h => by
    simp only [List.mem_singleton] at h
    subst h; simp [minV]
  | P :: R :: ps, Q, h => by
    simp only [minV]
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (minV_le s (R :: ps) Q h)

def segOk (g : Glob) (K : ℕ) (pts : List Pt) (seg : ℕ × ℕ × ℕ) : Bool :=
  let P := pts.getD seg.2.2 ⟨0, 0, 0, 0⟩
  decide (ptVal (sOf g K seg.1) P ≤ minV (sOf g K seg.1) pts) &&
    decide (ptVal (sOf g K seg.2.1) P ≤ minV (sOf g K seg.2.1) pts)

def envOk (g : Glob) (K : ℕ) (pts : List Pt) (env : List (ℕ × ℕ × ℕ)) : Bool :=
  decide (g.q0 ≤ g.mu) && decide (0 ≤ g.w) && env.all (segOk g K pts)

def lineEnv (g : Glob) (K : ℕ) (pts : List Pt) (env : List (ℕ × ℕ × ℕ)) (d : CellD) : Bool :=
  (mkCellD g K d).skip || env.any (fun seg => decide (seg.1 ≤ d.k) && decide (d.k ≤ seg.2.1) &&
    (let P := pts.getD seg.2.2 ⟨0, 0, 0, 0⟩
     decide ((mkCellD g K d).c - sOf g K d.k * P.lam ≤ P.E)))

lemma sOf_mono {g : Glob} {K i j : ℕ} (hq : g.q0 ≤ g.mu) (hw : 0 ≤ g.w) (h : i ≤ j) :
    sOf g K i ≤ sOf g K j := by
  unfold sOf gridPt
  apply mul_le_mul_of_nonneg_left _ hw
  have hij : (i : ℚ) ≤ j := by exact_mod_cast h
  have hm : 0 ≤ g.mu - g.q0 := sub_nonneg.mpr hq
  have := mul_le_mul_of_nonneg_left hij hm
  have := div_le_div_of_nonneg_right this (Nat.cast_nonneg (α := ℚ) K)
  linarith

theorem lineBelow_of_env {g : Glob} {K : ℕ} {pts : List Pt} {env es : List (ℕ × ℕ × ℕ)}
    (he : envOk g K pts env = true) (hsub : es.all (fun s => env.contains s) = true)
    {d : CellD} (hd : lineEnv g K pts es d = true) :
    ∀ Q ∈ pts, lineBelow g (mkCellD g K d) Q = true := by
  intro Q hQ
  unfold lineEnv at hd
  unfold lineBelow
  rcases Bool.or_eq_true_iff.mp hd with hs | hd
  · simp [hs]
  obtain ⟨seg, hseg, hc⟩ := List.any_eq_true.mp hd
  have hseg : seg ∈ env := by
    have := List.all_eq_true.mp hsub seg hseg
    simpa using this
  unfold envOk at he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he hc
  obtain ⟨⟨hq, hw⟩, hall⟩ := he
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have hsg := List.all_eq_true.mp hall seg hseg
  unfold segOk at hsg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsg
  have hQ1 := le_trans hsg.1 (minV_le _ pts Q hQ)
  have hQ2 := le_trans hsg.2 (minV_le _ pts Q hQ)
  unfold ptVal at hQ1 hQ2
  have hk := affine_le (sOf_mono (K := K) hq hw h1) (sOf_mono (K := K) hq hw h2) hQ1 hQ2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  right
  have hs : g.w * (mkCellD g K d).a = sOf g K d.k := rfl
  rw [hs]
  linarith

theorem full_of_env {g : Glob} {K : ℕ} {pts : List Pt} {env : List (ℕ × ℕ × ℕ)}
    (he : envOk g K pts env = true) {D : List CellD} {es : List (ℕ × ℕ × ℕ)}
    (h : (es.all (fun s => env.contains s) &&
      D.all (fun d => cellOkI g (mkCellD g K d) && lineEnv g K pts es d)) = true) :
    (D.map (mkCellD g K)).all (cellFullI g pts) = true := by
  rw [Bool.and_eq_true] at h
  obtain ⟨hsub, h⟩ := h
  rw [List.all_eq_true] at h ⊢
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have := h d hd
  rw [Bool.and_eq_true] at this
  unfold cellFullI
  rw [Bool.and_eq_true]
  exact ⟨this.1, List.all_eq_true.mpr (lineBelow_of_env he hsub this.2)⟩

end DiagRamsey.SharpCert.IExp
