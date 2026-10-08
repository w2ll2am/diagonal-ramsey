import Lemmas.DiagRamsey_PL

/-!
# Kernel-checkable piecewise-affine inequalities (P0.6)

A v5 profile is rational data `(xs, ys)`: nodes and values. Its value is `PLQ.evalR`, the clamp-form
interpolant of `Lemmas/DiagRamsey_PL.lean` with nodes indexed by `Fin`. An inequality between such functions on an
interval is certified by a breakpoint list `bp` supplied as data. The kernel checks three things: `bp` is strictly
increasing, no node of any participating profile lies strictly inside a segment of `bp` (or of its reflection), and
the inequality holds at every breakpoint in exact rationals.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.PL

/-- Rational clamp-form interpolant over lists (nodes `xs`, values `ys`). -/
def evalQ : List ℚ → List ℚ → ℚ → ℚ
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r =>
      y0 + (y1 - y0) / (x1 - x0) * max 0 (min r x1 - x0) - y1 + evalQ (x1 :: xs) (y1 :: ys) r
  | _, y0 :: _, _ => y0
  | _, [], _ => 0

/-- The same over the reals. -/
noncomputable def evalR : List ℚ → List ℚ → ℝ → ℝ
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r =>
      y0 + (y1 - y0) / (x1 - x0) * max 0 (min r x1 - x0) - y1 + evalR (x1 :: xs) (y1 :: ys) r
  | _, y0 :: _, _ => y0
  | _, [], _ => 0

lemma evalR_cast : ∀ (xs ys : List ℚ) (r : ℚ), evalR xs ys (r : ℝ) = (evalQ xs ys r : ℝ)
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r => by
      simp only [evalR, evalQ, evalR_cast (x1 :: xs) (y1 :: ys) r]
      push_cast [Rat.cast_max, Rat.cast_min]; ring
  | [], y0 :: _, r => by simp [evalR, evalQ]
  | [_], y0 :: _, r => by simp [evalR, evalQ]
  | _ :: _ :: _, [y0], r => by simp [evalR, evalQ]
  | xs, [], r => by cases xs <;> simp [evalR, evalQ] <;> (rename_i a l; cases l <;> simp [evalR, evalQ])

/-- `bp` is strictly increasing. -/
def sortedQ : List ℚ → Bool
  | a :: b :: rest => decide (a < b) && sortedQ (b :: rest)
  | _ => true

/-- No element of `xs` strictly inside a segment of `bp`. -/
def noKnotQ (xs : List ℚ) : List ℚ → Bool
  | a :: b :: rest => xs.all (fun x => decide (x ≤ a) || decide (b ≤ x)) && noKnotQ xs (b :: rest)
  | _ => true

/-- No element of `xs` strictly inside a reflected segment `(1/b, 1/a)`. -/
def noKnotReflQ (xs : List ℚ) : List ℚ → Bool
  | a :: b :: rest => xs.all (fun x => decide (x ≤ 1 / b) || decide (1 / a ≤ x)) && noKnotReflQ xs (b :: rest)
  | _ => true

/-- Affine on each segment of a list (real version of `AffineBetween`). -/
def AffineOnList (h : ℝ → ℝ) : List ℚ → Prop
  | a :: b :: rest => (∀ r : ℝ, (a : ℝ) ≤ r → r ≤ b →
      h r * ((b : ℝ) - a) = ((b : ℝ) - r) * h a + (r - a) * h b) ∧ AffineOnList h (b :: rest)
  | _ => True

lemma nonneg_of_list (h : ℝ → ℝ) : ∀ (bp : List ℚ), sortedQ bp = true → AffineOnList h bp →
    (∀ x ∈ bp, 0 ≤ h x) → ∀ a ∈ bp.head?, ∀ b ∈ bp.getLast?, ∀ r : ℝ, (a : ℝ) ≤ r → r ≤ b → 0 ≤ h r
  | [], _, _, _, a, ha, _, _, _, _, _ => by simp at ha
  | [x], _, _, hpts, a, ha, b, hb, r, h1, h2 => by
      simp at ha hb; subst ha; subst hb
      have : r = x := le_antisymm h2 h1
      rw [this]; exact hpts x (by simp)
  | x :: y :: rest, hs, haff, hpts, a, ha, b, hb, r, h1, h2 => by
      simp only [sortedQ, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      subst ha
      by_cases hr : r ≤ (y : ℝ)
      · have hxy : (x : ℝ) < y := by exact_mod_cast hs.1
        exact nonneg_segment hxy h1 hr (haff.1 r h1 hr) (hpts x (by simp)) (hpts y (by simp))
      · push_neg at hr
        refine nonneg_of_list h (y :: rest) hs.2 haff.2 (fun z hz => hpts z (List.mem_cons_of_mem _ hz)) y
          (by simp) b (by simpa using hb) r hr.le h2

/-- `h` is affine on the segment `[a, b]`. -/
def SegAffine (h : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ r : ℝ, a ≤ r → r ≤ b → h r * (b - a) = (b - r) * h a + (r - a) * h b

lemma segAffine_of_eq {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (c d : ℝ) (heq : ∀ r, a ≤ r → r ≤ b → h r = c + d * r) :
    SegAffine h a b := by
  intro r h1 h2
  rw [heq r h1 h2, heq a le_rfl hab, heq b hab le_rfl]; ring

lemma SegAffine.add {f g : ℝ → ℝ} {a b : ℝ} (hf : SegAffine f a b) (hg : SegAffine g a b) :
    SegAffine (fun r => f r + g r) a b := by
  intro r h1 h2; have := hf r h1 h2; have := hg r h1 h2; simp only; linarith

lemma SegAffine.sub {f g : ℝ → ℝ} {a b : ℝ} (hf : SegAffine f a b) (hg : SegAffine g a b) :
    SegAffine (fun r => f r - g r) a b := by
  intro r h1 h2; have := hf r h1 h2; have := hg r h1 h2; simp only; linarith

lemma SegAffine.smul {f : ℝ → ℝ} {a b : ℝ} (c : ℝ) (hf : SegAffine f a b) :
    SegAffine (fun r => c * f r) a b := by
  intro r h1 h2; have := hf r h1 h2; simp only; linear_combination c * this

lemma segAffine_const {a b : ℝ} (c : ℝ) : SegAffine (fun _ => c) a b := by intro r _ _; ring

/-- A clamp term is affine on any segment avoiding its two knots. -/
lemma segAffine_clamp {a b x0 x1 : ℝ} (hab : a ≤ b) (h0 : x0 ≤ a ∨ b ≤ x0) (h1 : x1 ≤ a ∨ b ≤ x1) :
    SegAffine (fun r => max 0 (min r x1 - x0)) a b := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact segAffine_of_eq hab (max 0 (x1 - x0)) 0 (fun r hr _ => by rw [min_eq_right (by linarith)]; ring)
  · exact segAffine_of_eq hab (-x0) 1 (fun r hr hr' => by
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring)
  · exact segAffine_of_eq hab 0 0 (fun r hr _ => by
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring)
  · exact segAffine_of_eq hab 0 0 (fun r _ hr' => by
      rw [max_eq_left (by linarith [min_le_left r x1])]; ring)

/-- The reflected clamp `r ↦ r · clamp(1/r)` is affine on `[a, b] ⊂ (0, ∞)` avoiding `1/x0, 1/x1`. -/
lemma segAffine_clamp_refl {a b x0 x1 : ℝ} (ha : 0 < a) (hab : a ≤ b) (h0 : x0 ≤ 1 / b ∨ 1 / a ≤ x0)
    (h1 : x1 ≤ 1 / b ∨ 1 / a ≤ x1) : SegAffine (fun r => r * max 0 (min (1 / r) x1 - x0)) a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have inv : ∀ r, a ≤ r → r ≤ b → 1 / b ≤ 1 / r ∧ 1 / r ≤ 1 / a := fun r h1 h2 =>
    ⟨one_div_le_one_div_of_le (lt_of_lt_of_le ha h1) h2, one_div_le_one_div_of_le ha h1⟩
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact segAffine_of_eq hab 0 (max 0 (x1 - x0)) (fun r hr hr' => by
      rw [min_eq_right (by linarith [(inv r hr hr').1])]; ring)
  · exact segAffine_of_eq hab 1 (-x0) (fun r hr hr' => by
      have := inv r hr hr'
      have hr0 : 0 < r := lt_of_lt_of_le ha hr
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]; field_simp; ring)
  · exact segAffine_of_eq hab 0 0 (fun r hr hr' => by
      have := inv r hr hr'
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring)
  · exact segAffine_of_eq hab 0 0 (fun r hr hr' => by
      have := inv r hr hr'
      rw [max_eq_left (by linarith [min_le_left (1 / r) x1])]; ring)

lemma evalR_segAffine {a b : ℝ} (hab : a ≤ b) : ∀ (xs ys : List ℚ),
    (∀ x ∈ xs, (x : ℝ) ≤ a ∨ b ≤ x) → SegAffine (evalR xs ys) a b
  | x0 :: x1 :: xs, y0 :: y1 :: ys, hk => by
      have h := (((segAffine_const (y0 : ℝ)).add ((segAffine_clamp hab (hk x0 (by simp)) (hk x1 (by simp))).smul
        (((y1 : ℝ) - y0) / ((x1 : ℝ) - x0)))).sub (segAffine_const (y1 : ℝ))).add
        (evalR_segAffine hab (x1 :: xs) (y1 :: ys) (fun x hx => hk x (List.mem_cons_of_mem _ hx)))
      intro r h1 h2
      have := h r h1 h2
      simp only [evalR] at this ⊢
      linarith
  | [], y0 :: _, _ => by intro r _ _; simp [evalR]; ring
  | [_], y0 :: _, _ => by intro r _ _; simp [evalR]; ring
  | _ :: _ :: _, [_], _ => by intro r _ _; simp [evalR]; ring
  | [], [], _ => by intro r _ _; simp [evalR]
  | [_], [], _ => by intro r _ _; simp [evalR]
  | _ :: _ :: _, [], _ => by intro r _ _; simp [evalR]

lemma evalR_refl_segAffine {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ∀ (xs ys : List ℚ),
    (∀ x ∈ xs, (x : ℝ) ≤ 1 / b ∨ 1 / a ≤ x) → SegAffine (fun r => r * evalR xs ys (1 / r)) a b
  | x0 :: x1 :: xs, y0 :: y1 :: ys, hk => by
      have hc := segAffine_clamp_refl ha hab (hk x0 (by simp)) (hk x1 (by simp))
      have hrest := evalR_refl_segAffine ha hab (x1 :: xs) (y1 :: ys) (fun x hx => hk x (List.mem_cons_of_mem _ hx))
      have hlin : SegAffine (fun r => r * ((y0 : ℝ) - y1)) a b :=
        segAffine_of_eq hab 0 ((y0 : ℝ) - y1) (fun r _ _ => by ring)
      have h := (hlin.add (hc.smul (((y1 : ℝ) - y0) / ((x1 : ℝ) - x0)))).add hrest
      intro r h1 h2
      have := h r h1 h2
      simp only [evalR] at this ⊢
      linear_combination this
  | [], y0 :: _, _ => segAffine_of_eq hab 0 (y0 : ℝ) (fun r _ _ => by simp [evalR]; ring)
  | [_], y0 :: _, _ => segAffine_of_eq hab 0 (y0 : ℝ) (fun r _ _ => by simp [evalR]; ring)
  | _ :: _ :: _, [y0], _ => segAffine_of_eq hab 0 (y0 : ℝ) (fun r _ _ => by simp [evalR]; ring)
  | [], [], _ => segAffine_of_eq hab 0 0 (fun r _ _ => by simp [evalR])
  | [_], [], _ => segAffine_of_eq hab 0 0 (fun r _ _ => by simp [evalR])
  | _ :: _ :: _, [], _ => segAffine_of_eq hab 0 0 (fun r _ _ => by simp [evalR])

lemma AffineOnList.add {f g : ℝ → ℝ} : ∀ {bp : List ℚ}, AffineOnList f bp → AffineOnList g bp →
    AffineOnList (fun r => f r + g r) bp
  | a :: b :: rest, hf, hg => ⟨fun r h1 h2 => by
      have := hf.1 r h1 h2; have := hg.1 r h1 h2; simp only; linarith, AffineOnList.add hf.2 hg.2⟩
  | [], _, _ => trivial
  | [_], _, _ => trivial

lemma AffineOnList.sub {f g : ℝ → ℝ} : ∀ {bp : List ℚ}, AffineOnList f bp → AffineOnList g bp →
    AffineOnList (fun r => f r - g r) bp
  | a :: b :: rest, hf, hg => ⟨fun r h1 h2 => by
      have := hf.1 r h1 h2; have := hg.1 r h1 h2; simp only; linarith, AffineOnList.sub hf.2 hg.2⟩
  | [], _, _ => trivial
  | [_], _, _ => trivial

lemma affineOnList_affine (c d : ℝ) : ∀ (bp : List ℚ), AffineOnList (fun r => c + d * r) bp
  | a :: b :: rest => ⟨fun r _ _ => by ring, affineOnList_affine c d (b :: rest)⟩
  | [] => trivial
  | [_] => trivial

lemma affineOnList_evalR (xs ys : List ℚ) : ∀ (bp : List ℚ), sortedQ bp = true → noKnotQ xs bp = true →
    AffineOnList (evalR xs ys) bp
  | a :: b :: rest, hs, hk => by
      simp only [sortedQ, noKnotQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.or_eq_true] at hs hk
      refine ⟨fun r h1 h2 => evalR_segAffine (by exact_mod_cast hs.1.le) xs ys (fun x hx => ?_) r h1 h2,
        affineOnList_evalR xs ys (b :: rest) hs.2 hk.2⟩
      rcases hk.1 x hx with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  | [], _, _ => trivial
  | [_], _, _ => trivial

/-- Positive first breakpoint. -/
def posQ : List ℚ → Bool
  | a :: _ => decide (0 < a)
  | [] => true

lemma affineOnList_evalR_refl (xs ys : List ℚ) : ∀ (bp : List ℚ), sortedQ bp = true → posQ bp = true →
    noKnotReflQ xs bp = true → AffineOnList (fun r => r * evalR xs ys (1 / r)) bp
  | a :: b :: rest, hs, hp, hk => by
      simp only [sortedQ, noKnotReflQ, posQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.or_eq_true] at hs hk hp
      have ha : (0 : ℝ) < a := by exact_mod_cast hp
      refine ⟨fun r h1 h2 => evalR_refl_segAffine ha (by exact_mod_cast hs.1.le) xs ys (fun x hx => ?_) r h1 h2,
        affineOnList_evalR_refl xs ys (b :: rest) hs.2 (by simp [posQ]; exact_mod_cast hp.trans hs.1) hk.2⟩
      rcases hk.1 x hx with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial

end DiagRamsey.PL
