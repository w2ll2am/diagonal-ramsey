import Lemmas.DiagRamsey_V5Final

/-!
# v5 banks in Lean (P0.6): a fast exact checker

The kernel evaluates `ℚ` arithmetic slowly (≈ 1 ms per operation: normalisation and instance unfolding), while raw
`Nat`/`Int` operations are GMP-accelerated. `FQ` is an unnormalised fraction `n / (d + 1)` (the stored `d` is the
denominator minus one, so every denominator is positive by construction). Each fast function below is proved
*equal* to its `ℚ` counterpart on the mapped data (`FQ.toQ`), so the soundness theorems of `DiagRamsey_V5Bank` /
`DiagRamsey_V5Assemble` apply unchanged.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.V5

/-- The fraction `n / (d + 1)`. -/
structure FQ where
  n : ℤ
  d : ℕ

namespace FQ

def toQ (a : FQ) : ℚ := (a.n : ℚ) / ((a.d + 1 : ℕ) : ℚ)

lemma den_pos (a : FQ) : (0 : ℚ) < ((a.d + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos _

/-- The fraction `n / D` for `D ≥ 1`. -/
def mkD (n : ℤ) (D : ℕ) : FQ := ⟨n, D - 1⟩

lemma toQ_mk (n : ℤ) (D : ℕ) (hD : 1 ≤ D) : (mkD n D).toQ = (n : ℚ) / (D : ℚ) := by
  simp only [toQ, mkD]; rw [Nat.sub_add_cancel hD]

def add (a b : FQ) : FQ := mkD (a.n * (b.d + 1 : ℕ) + b.n * (a.d + 1 : ℕ)) ((a.d + 1) * (b.d + 1))
def sub (a b : FQ) : FQ := mkD (a.n * (b.d + 1 : ℕ) - b.n * (a.d + 1 : ℕ)) ((a.d + 1) * (b.d + 1))
def mul (a b : FQ) : FQ := mkD (a.n * b.n) ((a.d + 1) * (b.d + 1))
def ofInt (n : ℤ) : FQ := ⟨n, 0⟩
/-- `a / b` with `ℚ`'s convention `x / 0 = 0`. -/
def div (a b : FQ) : FQ :=
  if 0 < b.n then mkD (a.n * (b.d + 1 : ℕ)) ((a.d + 1) * b.n.natAbs)
  else if b.n < 0 then mkD (-(a.n * (b.d + 1 : ℕ))) ((a.d + 1) * b.n.natAbs)
  else ⟨0, 0⟩
def le (a b : FQ) : Bool := decide (a.n * (b.d + 1 : ℕ) ≤ b.n * (a.d + 1 : ℕ))
def lt (a b : FQ) : Bool := decide (a.n * (b.d + 1 : ℕ) < b.n * (a.d + 1 : ℕ))
def eq (a b : FQ) : Bool := decide (a.n * (b.d + 1 : ℕ) = b.n * (a.d + 1 : ℕ))
def max (a b : FQ) : FQ := if le a b then b else a
def min (a b : FQ) : FQ := if le a b then a else b

lemma one_le_mul (a b : ℕ) : 1 ≤ (a + 1) * (b + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma toQ_add (a b : FQ) : (add a b).toQ = a.toQ + b.toQ := by
  rw [add, toQ_mk _ _ (one_le_mul _ _)]
  have ha := a.den_pos; have hb := b.den_pos
  simp only [toQ]; push_cast at *; field_simp

lemma toQ_sub (a b : FQ) : (sub a b).toQ = a.toQ - b.toQ := by
  rw [sub, toQ_mk _ _ (one_le_mul _ _)]
  have ha := a.den_pos; have hb := b.den_pos
  simp only [toQ]; push_cast at *; field_simp

lemma toQ_mul (a b : FQ) : (mul a b).toQ = a.toQ * b.toQ := by
  rw [mul, toQ_mk _ _ (one_le_mul _ _)]
  simp only [toQ]; push_cast; rw [div_mul_div_comm]

lemma toQ_ofInt (n : ℤ) : (ofInt n).toQ = n := by simp [toQ, ofInt]

lemma toQ_div (a b : FQ) : (div a b).toQ = a.toQ / b.toQ := by
  have ha := a.den_pos; have hb := b.den_pos
  unfold div
  split_ifs with h1 h2
  · have hD : 1 ≤ (a.d + 1) * b.n.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (by omega))
    rw [toQ_mk _ _ hD]
    have : ((b.n.natAbs : ℕ) : ℚ) = (b.n : ℚ) := by
      rw [Nat.cast_natAbs]; push_cast; exact_mod_cast abs_of_pos h1
    simp only [toQ]; push_cast [this] at *
    have hbn : (b.n : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
    field_simp
  · have hD : 1 ≤ (a.d + 1) * b.n.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (by omega))
    rw [toQ_mk _ _ hD]
    have : ((b.n.natAbs : ℕ) : ℚ) = -(b.n : ℚ) := by
      rw [Nat.cast_natAbs]; push_cast; rw [abs_of_neg (by exact_mod_cast h2)]
    simp only [toQ]; push_cast [this] at *
    have hbn : (b.n : ℚ) ≠ 0 := by exact_mod_cast h2.ne
    field_simp
  · have : b.n = 0 := by omega
    simp [toQ, this]

lemma le_eq (a b : FQ) : le a b = decide (a.toQ ≤ b.toQ) := by
  have ha := a.den_pos; have hb := b.den_pos
  have key : a.n * ((b.d + 1 : ℕ) : ℤ) ≤ b.n * ((a.d + 1 : ℕ) : ℤ) ↔ a.toQ ≤ b.toQ := by
    simp only [toQ]; rw [div_le_div_iff₀ ha hb]; constructor <;> intro h <;> exact_mod_cast h
  simp only [le]; exact decide_eq_decide.mpr key

lemma lt_eq (a b : FQ) : lt a b = decide (a.toQ < b.toQ) := by
  have ha := a.den_pos; have hb := b.den_pos
  have key : a.n * ((b.d + 1 : ℕ) : ℤ) < b.n * ((a.d + 1 : ℕ) : ℤ) ↔ a.toQ < b.toQ := by
    simp only [toQ]; rw [div_lt_div_iff₀ ha hb]; constructor <;> intro h <;> exact_mod_cast h
  simp only [lt]; exact decide_eq_decide.mpr key

lemma eq_eq (a b : FQ) : eq a b = decide (a.toQ = b.toQ) := by
  have ha := a.den_pos; have hb := b.den_pos
  have key : a.n * ((b.d + 1 : ℕ) : ℤ) = b.n * ((a.d + 1 : ℕ) : ℤ) ↔ a.toQ = b.toQ := by
    simp only [toQ]; rw [div_eq_div_iff ha.ne' hb.ne']; constructor <;> intro h <;> exact_mod_cast h
  simp only [eq]; exact decide_eq_decide.mpr key

lemma toQ_max (a b : FQ) : (max a b).toQ = Max.max a.toQ b.toQ := by
  unfold max; rw [le_eq]
  by_cases h : a.toQ ≤ b.toQ
  · simp [h, max_eq_right h]
  · simp [h, max_eq_left (le_of_not_ge h)]

lemma toQ_min (a b : FQ) : (min a b).toQ = Min.min a.toQ b.toQ := by
  unfold min; rw [le_eq]
  by_cases h : a.toQ ≤ b.toQ
  · simp [h, min_eq_left h]
  · simp [h, min_eq_right (le_of_not_ge h)]

end FQ

open DiagRamsey.PL

namespace FQ
def zero : FQ := ⟨0, 0⟩
def one : FQ := ⟨1, 0⟩
lemma toQ_zero : zero.toQ = 0 := by simp [toQ, zero]
lemma toQ_one : one.toQ = 1 := by simp [toQ, one]
end FQ

open FQ

/-- The list mapped to `ℚ`. -/
def mapQ (l : List FQ) : List ℚ := l.map FQ.toQ

@[simp] lemma mapQ_nil : mapQ [] = [] := rfl
@[simp] lemma mapQ_cons (a : FQ) (l : List FQ) : mapQ (a :: l) = a.toQ :: mapQ l := rfl

def sortedF : List FQ → Bool
  | a :: b :: rest => lt a b && sortedF (b :: rest)
  | _ => true

lemma sortedF_eq : ∀ l : List FQ, sortedF l = sortedQ (mapQ l)
  | a :: b :: rest => by simp only [sortedF, sortedQ, mapQ_cons, lt_eq, sortedF_eq (b :: rest)]
  | [] => rfl
  | [_] => rfl

def posF : List FQ → Bool
  | a :: _ => lt zero a
  | [] => true

lemma posF_eq (l : List FQ) : posF l = posQ (mapQ l) := by
  cases l <;> simp [posF, posQ, lt_eq, toQ_zero]

def noKnotF (xs : List FQ) : List FQ → Bool
  | a :: b :: rest => xs.all (fun x => le x a || le b x) && noKnotF xs (b :: rest)
  | _ => true

lemma noKnotF_eq (xs : List FQ) : ∀ bp : List FQ, noKnotF xs bp = noKnotQ (mapQ xs) (mapQ bp)
  | a :: b :: rest => by
      have ih := noKnotF_eq xs (b :: rest)
      show (xs.all (fun x => le x a || le b x) && noKnotF xs (b :: rest)) =
        ((mapQ xs).all (fun x => decide (x ≤ a.toQ) || decide (b.toQ ≤ x)) && noKnotQ (mapQ xs) (mapQ (b :: rest)))
      rw [ih]; congr 1
      simp only [mapQ, List.all_map, le_eq]; rfl
  | [] => rfl
  | [_] => rfl

def noKnotReflF (xs : List FQ) : List FQ → Bool
  | a :: b :: rest => xs.all (fun x => le x (div one b) || le (div one a) x) && noKnotReflF xs (b :: rest)
  | _ => true

lemma noKnotReflF_eq (xs : List FQ) : ∀ bp : List FQ, noKnotReflF xs bp = noKnotReflQ (mapQ xs) (mapQ bp)
  | a :: b :: rest => by
      have ih := noKnotReflF_eq xs (b :: rest)
      show (xs.all (fun x => le x (div one b) || le (div one a) x) && noKnotReflF xs (b :: rest)) =
        ((mapQ xs).all (fun x => decide (x ≤ 1 / b.toQ) || decide (1 / a.toQ ≤ x)) &&
          noKnotReflQ (mapQ xs) (mapQ (b :: rest)))
      rw [ih]; congr 1
      simp only [mapQ, List.all_map, le_eq, toQ_div, toQ_one]; rfl
  | [] => rfl
  | [_] => rfl

/-- Linear interpolation on `[x0, x1]` in `evalQ`'s clamp form. -/
def interp (x0 x1 y0 y1 r : FQ) : FQ :=
  add y0 (mul (div (sub y1 y0) (sub x1 x0)) (max zero (sub (min r x1) x0)))

/-- The interpolant, evaluated on the first segment whose right end is `≥ r` (equal to `evalQ` on sorted nodes). -/
def evalF : List FQ → List FQ → FQ → FQ
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r => if le r x1 then interp x0 x1 y0 y1 r else evalF (x1 :: xs) (y1 :: ys) r
  | _, y0 :: _, _ => y0
  | _, [], _ => zero

/-- On sorted nodes, `evalQ` left of the first node is the first value. -/
lemma evalQ_left : ∀ (xs ys : List ℚ) (r : ℚ), sortedQ xs = true → (∀ x ∈ xs.head?, r ≤ x) →
    evalQ xs ys r = ys.headD 0
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r, hs, hr => by
      simp only [sortedQ, Bool.and_eq_true, decide_eq_true_eq] at hs
      have h0 : r ≤ x0 := hr x0 rfl
      have ih := evalQ_left (x1 :: xs) (y1 :: ys) r hs.2 (fun x hx => by
        simp at hx; subst hx; linarith [hs.1])
      rw [evalQ, ih, min_eq_left (by linarith [hs.1]), max_eq_left (by linarith)]
      simp
  | [], y0 :: _, _, _, _ => by simp [evalQ]
  | [_], y0 :: _, _, _, _ => by simp [evalQ]
  | _ :: _ :: _, [_], _, _, _ => by simp [evalQ]
  | xs, [], _, _, _ => by cases xs <;> simp [evalQ] <;> (rename_i a l; cases l <;> simp [evalQ])

lemma evalF_eq : ∀ (xs ys : List FQ) (r : FQ), sortedF xs = true →
    (evalF xs ys r).toQ = evalQ (mapQ xs) (mapQ ys) r.toQ
  | x0 :: x1 :: xs, y0 :: y1 :: ys, r, hs => by
      have hs' := hs
      simp only [sortedF, Bool.and_eq_true, lt_eq, decide_eq_true_eq] at hs'
      simp only [evalF, mapQ_cons, evalQ]
      split_ifs with h
      · rw [le_eq, decide_eq_true_eq] at h
        have hl := evalQ_left (mapQ (x1 :: xs)) (mapQ (y1 :: ys)) r.toQ (by rw [← sortedF_eq]; exact hs'.2)
          (fun x hx => by simp [mapQ] at hx; subst hx; exact h)
        simp only [mapQ_cons, List.headD_cons] at hl
        rw [hl]
        simp only [interp, toQ_add, toQ_mul, toQ_div, toQ_sub, toQ_max, toQ_min, toQ_zero]
        ring
      · rw [le_eq, decide_eq_true_eq] at h
        have ih := evalF_eq (x1 :: xs) (y1 :: ys) r hs'.2
        simp only [mapQ_cons] at ih
        rw [← ih]
        have hx : x0.toQ < x1.toQ := hs'.1
        rw [min_eq_right (by linarith [not_le.mp h]), max_eq_right (by linarith)]
        field_simp [sub_ne_zero.mpr hx.ne']
        ring
  | [], y0 :: _, _, _ => by simp [evalF, evalQ]
  | [_], y0 :: _, _, _ => by simp [evalF, evalQ]
  | _ :: _ :: _, [_], _, _ => by simp [evalF, evalQ]
  | xs, [], _, _ => by
      cases xs <;> simp [evalF, evalQ, toQ_zero] <;> (rename_i a l; cases l <;> simp [evalF, evalQ, toQ_zero])

/-! ## Fast piecewise-affine checks -/

lemma all_imp {l : List FQ} {f : FQ → Bool} {g : ℚ → Bool} (h : ∀ x ∈ l, f x = true → g x.toQ = true)
    (hf : l.all f = true) : (mapQ l).all g = true := by
  rw [List.all_eq_true] at hf ⊢
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact h x hx (hf x hx)

structure ProfF where
  p : FQ
  xs : List FQ
  ys : List FQ

def ProfF.toD (P : ProfF) : ProfD := ⟨P.p.toQ, mapQ P.xs, mapQ P.ys⟩

def ProfF.ok (P : ProfF) (m : FQ) : Bool :=
  lt zero P.p && lt P.p one && decide (2 ≤ P.xs.length) && decide (P.xs.length = P.ys.length) &&
    sortedF P.xs && posF P.xs && lt zero m && P.xs.all (fun x => le m (evalF P.xs P.ys x)) &&
    noKnotF P.xs P.xs

lemma ProfF.ok_imp (P : ProfF) (m : FQ) (h : P.ok m = true) : P.toD.ok m.toQ = true := by
  simp only [ProfF.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  simp only [ProfD.ok, ProfF.toD, Bool.and_eq_true]
  rw [lt_eq, toQ_zero] at h1 h7; rw [lt_eq, toQ_one] at h2
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, by simpa [mapQ] using h3⟩, by simpa [mapQ] using h4⟩, by rwa [← sortedF_eq]⟩,
    by rwa [← posF_eq]⟩, h7⟩, ?_⟩, by rwa [← noKnotF_eq]⟩
  exact all_imp (fun x _ hx => by rw [le_eq, evalF_eq _ _ _ h5] at hx; exact hx) h8

def headIs (bp : List FQ) (lo : FQ) : Bool :=
  match bp with
  | x :: _ => eq x lo
  | [] => false

def lastIs (bp : List FQ) (hi : FQ) : Bool :=
  match bp.getLast? with
  | some x => eq x hi
  | none => false

def bpOkF (bp : List FQ) (lo hi : FQ) : Bool :=
  sortedF bp && headIs bp lo && lastIs bp hi && posF bp

lemma bpOkF_imp {bp : List FQ} {lo hi : FQ} (h : bpOkF bp lo hi = true) : bpOk (mapQ bp) lo.toQ hi.toQ = true := by
  simp only [bpOkF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [bpOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨by rwa [← sortedF_eq], ?_⟩, ?_⟩, by rwa [← posF_eq]⟩
  · cases bp with
    | nil => simp [headIs] at h2
    | cons x _ => simp only [headIs, eq_eq, decide_eq_true_eq] at h2; simp [mapQ, h2]
  · unfold lastIs at h3
    rw [mapQ, List.getLast?_map]
    cases hl : bp.getLast? with
    | none => rw [hl] at h3; simp at h3
    | some x => rw [hl] at h3; simp only [eq_eq, decide_eq_true_eq] at h3; simp [h3]

def plLeF (R Q : ProfF) (bp : List FQ) : Bool :=
  sortedF R.xs && sortedF Q.xs && noKnotF R.xs bp && noKnotF Q.xs bp &&
    bp.all (fun x => le (evalF R.xs R.ys x) (evalF Q.xs Q.ys x))

lemma plLeF_imp {R Q : ProfF} {bp : List FQ} (h : plLeF R Q bp = true) : plLeQ R.toD Q.toD (mapQ bp) = true := by
  simp only [plLeF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hR, hQ⟩, h1⟩, h2⟩, h3⟩ := h
  simp only [plLeQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨⟨by rwa [← noKnotF_eq], by rwa [← noKnotF_eq]⟩, all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, evalF_eq _ _ _ hR, evalF_eq _ _ _ hQ] at hx; exact hx

def plReflLeF (S Q : ProfF) (bp : List FQ) : Bool :=
  sortedF S.xs && sortedF Q.xs && noKnotReflF S.xs bp && noKnotF Q.xs bp &&
    bp.all (fun x => le (mul x (evalF S.xs S.ys (div one x))) (evalF Q.xs Q.ys x))

lemma plReflLeF_imp {S Q : ProfF} {bp : List FQ} (h : plReflLeF S Q bp = true) :
    plReflLeQ S.toD Q.toD (mapQ bp) = true := by
  simp only [plReflLeF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hS, hQ⟩, h1⟩, h2⟩, h3⟩ := h
  simp only [plReflLeQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨⟨by rwa [← noKnotReflF_eq], by rwa [← noKnotF_eq]⟩, all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_mul, evalF_eq _ _ _ hS, evalF_eq _ _ _ hQ, toQ_div, toQ_one] at hx; exact hx

def plLeAffF (R : ProfF) (c d : FQ) (bp : List FQ) : Bool :=
  sortedF R.xs && noKnotF R.xs bp && bp.all (fun x => le (evalF R.xs R.ys x) (add c (mul d x)))

lemma plLeAffF_imp {R : ProfF} {c d : FQ} {bp : List FQ} (h : plLeAffF R c d bp = true) :
    plLeAffQ R.toD c.toQ d.toQ (mapQ bp) = true := by
  simp only [plLeAffF, Bool.and_eq_true] at h
  obtain ⟨⟨hR, h1⟩, h3⟩ := h
  simp only [plLeAffQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨by rwa [← noKnotF_eq], all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_add, toQ_mul, evalF_eq _ _ _ hR] at hx; exact hx

def plReflLeAffF (S : ProfF) (c d : FQ) (bp : List FQ) : Bool :=
  sortedF S.xs && noKnotReflF S.xs bp &&
    bp.all (fun x => le (mul x (evalF S.xs S.ys (div one x))) (add c (mul d x)))

lemma plReflLeAffF_imp {S : ProfF} {c d : FQ} {bp : List FQ} (h : plReflLeAffF S c d bp = true) :
    plReflLeAffQ S.toD c.toQ d.toQ (mapQ bp) = true := by
  simp only [plReflLeAffF, Bool.and_eq_true] at h
  obtain ⟨⟨hS, h1⟩, h3⟩ := h
  simp only [plReflLeAffQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨by rwa [← noKnotReflF_eq], all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_add, toQ_mul, toQ_mul, evalF_eq _ _ _ hS, toQ_div, toQ_one] at hx; exact hx

def plGeAffF (R : ProfF) (c d : FQ) (bp : List FQ) : Bool :=
  sortedF R.xs && noKnotF R.xs bp && bp.all (fun x => le (add c (mul d x)) (evalF R.xs R.ys x))

lemma plGeAffF_imp {R : ProfF} {c d : FQ} {bp : List FQ} (h : plGeAffF R c d bp = true) :
    plGeAffQ R.toD c.toQ d.toQ (mapQ bp) = true := by
  simp only [plGeAffF, Bool.and_eq_true] at h
  obtain ⟨⟨hR, h1⟩, h3⟩ := h
  simp only [plGeAffQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨by rwa [← noKnotF_eq], all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_add, toQ_mul, evalF_eq _ _ _ hR] at hx; exact hx

def gLF : List FQ → List FQ → FQ → FQ
  | u0 :: u1 :: us, d0 :: ds, s => add (mul d0 (max zero (sub (min s u1) u0))) (gLF (u1 :: us) ds s)
  | _, _, _ => zero

lemma gLF_eq : ∀ (us ds : List FQ) (s : FQ), (gLF us ds s).toQ = gLQ (mapQ us) (mapQ ds) s.toQ
  | u0 :: u1 :: us, d0 :: ds, s => by
      have ih := gLF_eq (u1 :: us) ds s
      simp only [mapQ_cons] at ih ⊢
      simp only [gLF, gLQ, toQ_add, toQ_mul, toQ_max, toQ_sub, toQ_min, toQ_zero, ih]
  | [], _, _ => by simp [gLF, gLQ, toQ_zero]
  | [_], _, _ => by simp [gLF, gLQ, toQ_zero]
  | _ :: _ :: _, [], _ => by simp [gLF, gLQ, toQ_zero]

def gLeF (P : ProfF) (us ds : List FQ) (c0 c1 c2 : FQ) (bp : List FQ) : Bool :=
  sortedF P.xs && noKnotF P.xs bp && noKnotF us bp &&
    bp.all (fun x => le (add (add c0 (mul c1 x)) (mul c2 (gLF us ds x))) (evalF P.xs P.ys x))

lemma gLeF_imp {P : ProfF} {us ds : List FQ} {c0 c1 c2 : FQ} {bp : List FQ} (h : gLeF P us ds c0 c1 c2 bp = true) :
    gLeQ P.toD (mapQ us) (mapQ ds) c0.toQ c1.toQ c2.toQ (mapQ bp) = true := by
  simp only [gLeF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hP, h1⟩, h2⟩, h3⟩ := h
  simp only [gLeQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨⟨by rwa [← noKnotF_eq], by rwa [← noKnotF_eq]⟩, all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_add, toQ_add, toQ_mul, toQ_mul, gLF_eq, evalF_eq _ _ _ hP] at hx; exact hx

def gGeF (P : ProfF) (us ds : List FQ) (c0 c1 c2 : FQ) (bp : List FQ) : Bool :=
  sortedF P.xs && noKnotF P.xs bp && noKnotF us bp &&
    bp.all (fun x => le (evalF P.xs P.ys x) (add (add c0 (mul c1 x)) (mul c2 (gLF us ds x))))

lemma gGeF_imp {P : ProfF} {us ds : List FQ} {c0 c1 c2 : FQ} {bp : List FQ} (h : gGeF P us ds c0 c1 c2 bp = true) :
    gGeQ P.toD (mapQ us) (mapQ ds) c0.toQ c1.toQ c2.toQ (mapQ bp) = true := by
  simp only [gGeF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hP, h1⟩, h2⟩, h3⟩ := h
  simp only [gGeQ, ProfF.toD, Bool.and_eq_true]
  refine ⟨⟨by rwa [← noKnotF_eq], by rwa [← noKnotF_eq]⟩, all_imp (fun x _ hx => ?_) h3⟩
  rw [le_eq, toQ_add, toQ_add, toQ_mul, toQ_mul, gLF_eq, evalF_eq _ _ _ hP] at hx; exact hx

def lineLeF (c d A B η x : FQ) : Bool := le (add c (mul d x)) (sub (add A (mul B x)) (mul η (add one x)))

lemma lineLeF_eq (c d A B η x : FQ) : lineLeF c d A B η x = lineLeQ c.toQ d.toQ A.toQ B.toQ η.toQ x.toQ := by
  simp only [lineLeF, lineLeQ, le_eq, toQ_add, toQ_mul, toQ_sub, toQ_one]

def pairQ (p : FQ × FQ) : ℚ × ℚ := (p.1.toQ, p.2.toQ)

def chainF : FQ → List (FQ × FQ) → FQ → Bool
  | a, [p], b => eq p.1 a && eq p.2 b
  | a, p :: q :: rest, b => eq p.1 a && chainF p.2 (q :: rest) b
  | _, [], _ => false

lemma chainF_eq : ∀ (a : FQ) (ps : List (FQ × FQ)) (b : FQ), chainF a ps b = chainQ a.toQ (ps.map pairQ) b.toQ
  | a, [p], b => by simp [chainF, chainQ, eq_eq, pairQ]
  | a, p :: q :: rest, b => by
      have ih := chainF_eq p.2 (q :: rest) b
      simp only [List.map_cons] at ih ⊢
      simp only [chainF, chainQ, eq_eq, pairQ, ih]
      rfl
  | _, [], _ => by simp [chainF, chainQ]

/-! ## Fast bank objects -/

open DiagRamsey.SharpCert

structure CtrlF where
  p : FQ
  μ : FQ
  w : FQ
  β : FQ
  x : FQ
  lxU : FQ
  l1mL : FQ

def CtrlF.toD (c : CtrlF) : CtrlD := ⟨c.p.toQ, c.μ.toQ, c.w.toQ, c.β.toQ, c.x.toQ, c.lxU.toQ, c.l1mL.toQ⟩

structure LeafF (nCtl m : ℕ) where
  c : Fin nCtl
  σ : Fin m
  ξ : FQ
  ν : FQ
  ys : FQ
  aU : FQ
  bU : FQ
  margin : FQ
  lo : FQ
  hi : FQ
  bp : List FQ

def LeafF.toD {nCtl m : ℕ} (L : LeafF nCtl m) : LeafD nCtl m :=
  ⟨L.c, L.σ, L.ξ.toQ, L.ν.toQ, L.ys.toQ, L.aU.toQ, L.bU.toQ, L.margin.toQ, L.lo.toQ, L.hi.toQ, mapQ L.bp⟩

def LeafF.check {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (P : ProfF) (L : LeafF nCtl m) : Bool :=
  (ctl L.c).toD.ok && lt zero L.ξ && lt L.ξ (ctl L.c).x && decide (L.ξ.toQ < expLo (-(A L.σ).toQ)) &&
    lt zero L.ν && lt L.ν (ctl L.c).μ && lt zero L.ys && expLeB (-L.aU.toQ) L.ξ.toQ &&
    expLeB (-L.bU.toQ) L.ν.toQ && le (ctl L.c).p P.p && lt zero L.margin && lt zero L.lo &&
    bpOkF L.bp L.lo L.hi &&
    plGeAffF P (add L.margin (div L.aU (add one (ctl L.c).w)))
      (add L.margin (div (add (add (B L.σ) L.ys) (mul (ctl L.c).w L.bU)) (add one (ctl L.c).w))) L.bp

lemma LeafF.check_imp {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (P : ProfF) (L : LeafF nCtl m)
    (h : L.check ctl A B P = true) :
    L.toD.check (fun i => (ctl i).toD) (fun i => (A i).toQ) (fun i => (B i).toQ) P.toD = true := by
  simp only [LeafF.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  have h14' := plGeAffF_imp h14
  simp only [toQ_add, toQ_div, toQ_one, toQ_mul] at h14'
  simp only [lt_eq, le_eq, toQ_zero] at h2 h3 h5 h6 h7 h10 h11 h12
  simp only [LeafD.check, LeafF.toD, CtrlF.toD, ProfF.toD, Bool.and_eq_true] at h14' ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, bpOkF_imp h13⟩, h14'⟩

lemma mapQ_length (l : List FQ) : (mapQ l).length = l.length := List.length_map _

lemma mapQ_getD (l : List FQ) (j : ℕ) : (mapQ l).getD j 0 = (l.getD j zero).toQ := by
  rw [show (0 : ℚ) = zero.toQ from toQ_zero.symm, mapQ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

lemma mapQ_headD (l : List FQ) : (mapQ l).headD 0 = (l.headD zero).toQ := by
  cases l <;> simp [mapQ, toQ_zero]

lemma mapQ_getLastD (l : List FQ) : (mapQ l).getLastD 0 = (l.getLastD zero).toQ := by
  induction l with
  | nil => simp [mapQ, toQ_zero]
  | cons a t ih =>
    cases t with
    | nil => simp [mapQ]
    | cons b u => simpa [mapQ, List.getLastD_cons] using ih

structure TermF (nCtl m : ℕ) where
  c : Fin nCtl
  σ : Fin m
  ξ : FQ
  ν : FQ
  ys : FQ
  aU : FQ
  bU : FQ

def TermF.toD {nCtl m : ℕ} (T : TermF nCtl m) : TermD nCtl m :=
  ⟨T.c, T.σ, T.ξ.toQ, T.ν.toQ, T.ys.toQ, T.aU.toQ, T.bU.toQ⟩

def TermF.check {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A : Fin m → FQ) (T : TermF nCtl m) : Bool :=
  (ctl T.c).toD.ok && lt zero T.ξ && lt T.ξ (ctl T.c).x && decide (T.ξ.toQ < expLo (-(A T.σ).toQ)) &&
    lt zero T.ν && lt T.ν (ctl T.c).μ && lt zero T.ys && expLeB (-T.aU.toQ) T.ξ.toQ &&
    expLeB (-T.bU.toQ) T.ν.toQ

lemma TermF.check_imp {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A : Fin m → FQ) (T : TermF nCtl m)
    (h : T.check ctl A = true) : T.toD.check (fun i => (ctl i).toD) (fun i => (A i).toQ) = true := by
  simp only [TermF.check, Bool.and_eq_true, lt_eq, toQ_zero] at h
  simp only [TermD.check, TermF.toD, CtrlF.toD, Bool.and_eq_true]
  exact h

structure CallF (ι : Type) where
  ch : ι
  z : FQ
  bp : List FQ

def CallF.toD {ι : Type} (c : CallF ι) : CallD ι := ⟨c.ch, c.z.toQ, mapQ c.bp⟩

structure RouteF (ι : Type) (nCtl m : ℕ) where
  t : TermF nCtl m
  us : List FQ
  ds : List FQ
  calls : List (CallF ι)
  g0 : FQ
  hm : FQ
  margin : FQ
  lo : FQ
  hi : FQ
  bp : List FQ

def RouteF.toD {ι : Type} {nCtl m : ℕ} (R : RouteF ι nCtl m) : RouteD ι nCtl m :=
  ⟨R.t.toD, mapQ R.us, mapQ R.ds, R.calls.map CallF.toD, R.g0.toQ, R.hm.toQ, R.margin.toQ, R.lo.toQ, R.hi.toQ,
    mapQ R.bp⟩

def RouteF.cellCheck {ι : Type} {nCtl m : ℕ} (pd : ι → ProfF) (i0 : ι) (R : RouteF ι nCtl m) (j : ℕ) : Bool :=
  let cl := R.calls.getD j ⟨i0, zero, []⟩
  let Pc := pd cl.ch
  le (Pc.xs.headD zero) (R.us.getD j zero) && le (R.us.getD (j + 1) zero) (Pc.xs.getLastD zero) &&
    lt zero cl.z && expLeB (-(R.ds.getD j zero).toQ) cl.z.toQ && lt cl.z (sub one Pc.p) &&
    bpOkF cl.bp (R.us.getD j zero) (R.us.getD (j + 1) zero) && gGeF Pc R.us R.ds (sub R.g0 R.hm) zero one cl.bp

lemma calls_getD {ι : Type} (calls : List (CallF ι)) (i0 : ι) (j : ℕ) :
    (calls.map CallF.toD).getD j ⟨i0, 0, []⟩ = (calls.getD j ⟨i0, zero, []⟩).toD := by
  rw [show (⟨i0, 0, []⟩ : CallD ι) = CallF.toD ⟨i0, zero, []⟩ by simp [CallF.toD, toQ_zero, mapQ]]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

lemma RouteF.cellCheck_imp {ι : Type} {nCtl m : ℕ} (pd : ι → ProfF) (i0 : ι) (R : RouteF ι nCtl m) (j : ℕ)
    (h : R.cellCheck pd i0 j = true) : R.toD.cellCheck (fun i => (pd i).toD) i0 j = true := by
  simp only [RouteF.cellCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have h6' := bpOkF_imp h6
  have h7' := gGeF_imp h7
  simp only [toQ_sub, toQ_zero, toQ_one] at h7'
  simp only [le_eq, lt_eq, toQ_zero, toQ_sub, toQ_one] at h1 h2 h3 h5
  simp only [RouteD.cellCheck, RouteF.toD, calls_getD, mapQ_getD, mapQ_headD, mapQ_getLastD, CallF.toD,
    ProfF.toD, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6'⟩, h7'⟩

def RouteF.check {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (pd : ι → ProfF) (i0 : ι)
    (P : ProfF) (R : RouteF ι nCtl m) : Bool :=
  let w := (ctl R.t.c).w
  let θ := R.us.getD 0 zero
  R.t.check ctl A && lt (ctl R.t.c).p P.p && decide (R.us.length = R.ds.length + 1) &&
    decide (0 < R.ds.length) && sortedF R.us && lt zero θ && lt zero R.g0 && le θ R.lo &&
    le R.hi (R.us.getD R.ds.length zero) && lt zero R.hm && lt zero R.margin &&
    (List.range R.ds.length).all (R.cellCheck pd i0) && bpOkF R.bp R.lo R.hi &&
    gLeF P R.us R.ds (add R.margin R.g0) zero one R.bp &&
    gLeF P R.us R.ds (add R.margin (div (add R.t.aU (mul (mul w θ) R.t.bU)) (add one w)))
      (div (add (B R.t.σ) R.t.ys) (add one w)) (div w (add one w)) R.bp

lemma RouteF.check_imp {ι : Type} {nCtl m : ℕ} (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (pd : ι → ProfF)
    (i0 : ι) (P : ProfF) (R : RouteF ι nCtl m) (h : R.check ctl A B pd i0 P = true) :
    R.toD.check (fun i => (ctl i).toD) (fun i => (A i).toQ) (fun i => (B i).toQ) (fun i => (pd i).toD) i0 P.toD
      = true := by
  simp only [RouteF.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  have h1' := TermF.check_imp ctl A R.t h1
  have h13' := bpOkF_imp h13
  have h14' := gLeF_imp h14
  have h15' := gLeF_imp h15
  have h12' : (List.range (mapQ R.ds).length).all (R.toD.cellCheck (fun i => (pd i).toD) i0) = true := by
    rw [mapQ_length, List.all_eq_true] at *
    intro j hj; exact RouteF.cellCheck_imp pd i0 R j (h12 j hj)
  simp only [toQ_add, toQ_div, toQ_one, toQ_mul, toQ_zero] at h14' h15'
  simp only [le_eq, lt_eq, toQ_zero] at h2 h6 h7 h8 h9 h10 h11
  rw [sortedF_eq] at h5
  simp only [RouteD.check, RouteF.toD, CtrlF.toD, ProfF.toD, mapQ_getD, mapQ_length, Bool.and_eq_true] at h12' ⊢
  simp only [RouteF.toD, CtrlF.toD, ProfF.toD, mapQ_getD] at h14' h15'
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1', h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12'⟩, h13'⟩, h14'⟩, h15'⟩

/-! ## CLOSED pieces, SOURCE cells, sources -/

inductive ClosedPF (nR : ℕ)
  | rawDensity (R : Fin nR) (lo hi : FQ) (bp : List FQ)
  | complRaw (R S : Fin nR) (lo hi : FQ) (bp : List FQ)

def ClosedPF.toD {nR : ℕ} : ClosedPF nR → ClosedPD nR
  | .rawDensity R lo hi bp => .rawDensity R lo.toQ hi.toQ (mapQ bp)
  | .complRaw R S lo hi bp => .complRaw R S lo.toQ hi.toQ (mapQ bp)

def ClosedPF.lo {nR : ℕ} : ClosedPF nR → FQ
  | .rawDensity _ lo _ _ => lo
  | .complRaw _ _ lo _ _ => lo

def ClosedPF.hi {nR : ℕ} : ClosedPF nR → FQ
  | .rawDensity _ _ hi _ => hi
  | .complRaw _ _ _ hi _ => hi

lemma ClosedPF.lo_toD {nR : ℕ} (c : ClosedPF nR) : c.toD.lo = c.lo.toQ := by cases c <;> rfl
lemma ClosedPF.hi_toD {nR : ℕ} (c : ClosedPF nR) : c.toD.hi = c.hi.toQ := by cases c <;> rfl

def ClosedPF.check {nR : ℕ} (raw : Fin nR → ProfF) (Q : ProfF) : ClosedPF nR → Bool
  | .rawDensity R lo hi bp =>
      le (raw R).p Q.p && le ((raw R).xs.headD zero) lo && le hi ((raw R).xs.getLastD zero) &&
        bpOkF bp lo hi && plLeF (raw R) Q bp
  | .complRaw R S lo hi bp =>
      le (add (raw R).p (raw S).p) one && le ((raw R).xs.headD zero) lo && le hi ((raw R).xs.getLastD zero) &&
        le ((raw S).xs.headD zero) (div one hi) && le (div one lo) ((raw S).xs.getLastD zero) && lt zero lo &&
        bpOkF bp lo hi && plLeF (raw R) Q bp && plReflLeF (raw S) Q bp

lemma ClosedPF.check_imp {nR : ℕ} (raw : Fin nR → ProfF) (Q : ProfF) (c : ClosedPF nR)
    (h : c.check raw Q = true) : c.toD.check (fun i => (raw i).toD) Q.toD = true := by
  cases c with
  | rawDensity R lo hi bp =>
    simp only [ClosedPF.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    simp only [le_eq] at h1 h2 h3
    simp only [ClosedPF.toD, ClosedPD.check, ProfF.toD, mapQ_headD, mapQ_getLastD, Bool.and_eq_true]
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, bpOkF_imp h4⟩, plLeF_imp h5⟩
  | complRaw R S lo hi bp =>
    simp only [ClosedPF.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    simp only [le_eq, lt_eq, toQ_add, toQ_one, toQ_div, toQ_zero] at h1 h2 h3 h4 h5 h6
    simp only [ClosedPF.toD, ClosedPD.check, ProfF.toD, mapQ_headD, mapQ_getLastD, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, bpOkF_imp h7⟩, plLeF_imp h8⟩, plReflLeF_imp h9⟩

def sourcePairF (R S : ProfF) (A B η lo hi : FQ) (bp : List FQ) : Bool :=
  le (add R.p S.p) one && le (R.xs.headD zero) lo && le hi (R.xs.getLastD zero) &&
    le (S.xs.headD zero) (div one hi) && le (div one lo) (S.xs.getLastD zero) && lt zero lo &&
    bpOkF bp lo hi && plLeAffF R (sub A η) (sub B η) bp && plReflLeAffF S (sub A η) (sub B η) bp

lemma sourcePairF_imp {R S : ProfF} {A B η lo hi : FQ} {bp : List FQ} (h : sourcePairF R S A B η lo hi bp = true) :
    sourcePairCheck R.toD S.toD A.toQ B.toQ η.toQ lo.toQ hi.toQ (mapQ bp) = true := by
  simp only [sourcePairF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have h8' := plLeAffF_imp h8
  have h9' := plReflLeAffF_imp h9
  simp only [toQ_sub] at h8' h9'
  simp only [le_eq, lt_eq, toQ_add, toQ_one, toQ_div, toQ_zero] at h1 h2 h3 h4 h5 h6
  simp only [sourcePairCheck, ProfF.toD, mapQ_headD, mapQ_getLastD, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, bpOkF_imp h7⟩, h8'⟩, h9'⟩

inductive SrcCellF (ι : Type)
  | grounded (k : ℕ) (lo hi : FQ)
  | pair (PR PB : ι) (lo hi : FQ) (bp : List FQ)

def SrcCellF.toD {ι : Type} : SrcCellF ι → SrcCellD ι
  | .grounded k lo hi => .grounded k lo.toQ hi.toQ
  | .pair PR PB lo hi bp => .pair PR PB lo.toQ hi.toQ (mapQ bp)

def SrcCellF.lo {ι : Type} : SrcCellF ι → FQ
  | .grounded _ lo _ => lo
  | .pair _ _ lo _ _ => lo

def SrcCellF.hi {ι : Type} : SrcCellF ι → FQ
  | .grounded _ _ hi => hi
  | .pair _ _ _ hi _ => hi

lemma SrcCellF.lo_toD {ι : Type} (c : SrcCellF ι) : c.toD.lo = c.lo.toQ := by cases c <;> rfl
lemma SrcCellF.hi_toD {ι : Type} (c : SrcCellF ι) : c.toD.hi = c.hi.toQ := by cases c <;> rfl

def linesQ (lines : List (FQ × FQ)) : List (ℚ × ℚ) := lines.map pairQ

lemma linesQ_getD (lines : List (FQ × FQ)) (k : ℕ) : (linesQ lines).getD k 0 = pairQ (lines.getD k (zero, zero)) := by
  rw [show (0 : ℚ × ℚ) = pairQ (zero, zero) by simp [pairQ, toQ_zero]; rfl, linesQ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

lemma linesQ_length (lines : List (FQ × FQ)) : (linesQ lines).length = lines.length := List.length_map _

def SrcCellF.check {ι : Type} (pd : ι → ProfF) (lines : List (FQ × FQ)) (A B η : FQ) : SrcCellF ι → Bool
  | .grounded k lo hi => decide (k < lines.length) &&
      lineLeF (lines.getD k (zero, zero)).1 (lines.getD k (zero, zero)).2 A B η lo &&
      lineLeF (lines.getD k (zero, zero)).1 (lines.getD k (zero, zero)).2 A B η hi
  | .pair PR PB lo hi bp => sourcePairF (pd PR) (pd PB) A B η lo hi bp

lemma SrcCellF.check_imp {ι : Type} (pd : ι → ProfF) (lines : List (FQ × FQ)) (A B η : FQ) (c : SrcCellF ι)
    (h : c.check pd lines A B η = true) :
    c.toD.check (fun i => (pd i).toD) (linesQ lines) A.toQ B.toQ η.toQ = true := by
  cases c with
  | grounded k lo hi =>
    simp only [SrcCellF.check, Bool.and_eq_true, lineLeF_eq] at h
    simp only [SrcCellF.toD, SrcCellD.check, linesQ_getD, linesQ_length, Bool.and_eq_true]
    simpa only [pairQ] using h
  | pair PR PB lo hi bp => exact sourcePairF_imp h

structure SourceF (ι : Type) where
  Lo : FQ
  Hi : FQ
  ε : FQ
  η : FQ
  kL : ℕ
  kR : ℕ
  cells : List (SrcCellF ι)

def SourceF.toD {ι : Type} (S : SourceF ι) : SourceD ι :=
  ⟨S.Lo.toQ, S.Hi.toQ, S.ε.toQ, S.η.toQ, S.kL, S.kR, S.cells.map SrcCellF.toD⟩

def SourceF.check {ι : Type} (pd : ι → ProfF) (lines : List (FQ × FQ)) (A B : FQ) (S : SourceF ι) : Bool :=
  lt zero S.Lo && lt S.Lo S.Hi && lt zero S.ε && lt zero S.η &&
    decide (S.kL < lines.length) && decide (S.kR < lines.length) &&
    lineLeF (lines.getD S.kL (zero, zero)).1 (lines.getD S.kL (zero, zero)).2 A B S.ε zero &&
    lineLeF (lines.getD S.kL (zero, zero)).1 (lines.getD S.kL (zero, zero)).2 A B S.ε S.Lo &&
    lineLeF (lines.getD S.kR (zero, zero)).1 (lines.getD S.kR (zero, zero)).2 A B S.ε S.Hi &&
    le (lines.getD S.kR (zero, zero)).2 (sub B S.ε) &&
    chainF S.Lo (S.cells.map (fun c => (c.lo, c.hi))) S.Hi && S.cells.all (SrcCellF.check pd lines A B S.η)

lemma SourceF.check_imp {ι : Type} (pd : ι → ProfF) (lines : List (FQ × FQ)) (A B : FQ) (S : SourceF ι)
    (h : S.check pd lines A B = true) :
    S.toD.check (fun i => (pd i).toD) (linesQ lines) A.toQ B.toQ = true := by
  simp only [SourceF.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  simp only [lt_eq, le_eq, toQ_zero, toQ_sub, lineLeF_eq, decide_eq_true_eq] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rw [chainF_eq, List.map_map] at h11
  have h12' : (S.cells.map SrcCellF.toD).all
      (SrcCellD.check (fun i => (pd i).toD) (linesQ lines) A.toQ B.toQ S.η.toQ) = true := by
    rw [List.all_eq_true] at h12 ⊢
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact SrcCellF.check_imp pd lines A B S.η x (h12 x hx)
  have hc : S.toD.cells.map (fun c => (c.lo, c.hi)) = List.map (pairQ ∘ fun c => (c.lo, c.hi)) S.cells := by
    simp only [SourceF.toD, List.map_map]
    apply List.map_congr_left; intro c _; cases c <;> rfl
  unfold SourceD.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, linesQ_getD, linesQ_length, hc]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12'⟩

/-! ## RAW pieces and the bank -/

inductive RawF (ι : Type) (nCtl m : ℕ)
  | leaf (L : LeafF nCtl m)
  | route (R : RouteF ι nCtl m)

variable {ι : Type} {nCtl m : ℕ}

def RawF.toD : RawF ι nCtl m → RawD ι nCtl m
  | .leaf L => .leaf L.toD
  | .route R => .route R.toD

def RawF.lo : RawF ι nCtl m → FQ
  | .leaf L => L.lo
  | .route R => R.lo

def RawF.hi : RawF ι nCtl m → FQ
  | .leaf L => L.hi
  | .route R => R.hi

lemma RawF.lo_toD (x : RawF ι nCtl m) : x.toD.lo = x.lo.toQ := by cases x <;> rfl
lemma RawF.hi_toD (x : RawF ι nCtl m) : x.toD.hi = x.hi.toQ := by cases x <;> rfl

def RawF.check (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (pd : ι → ProfF) (i0 : ι) (P : ProfF) :
    RawF ι nCtl m → Bool
  | .leaf L => L.check ctl A B P
  | .route R => R.check ctl A B pd i0 P

lemma RawF.check_imp (ctl : Fin nCtl → CtrlF) (A B : Fin m → FQ) (pd : ι → ProfF) (i0 : ι) (P : ProfF)
    (x : RawF ι nCtl m) (h : x.check ctl A B pd i0 P = true) :
    x.toD.check (fun i => (ctl i).toD) (fun i => (A i).toQ) (fun i => (B i).toQ) (fun i => (pd i).toD) i0 P.toD
      = true := by
  cases x with
  | leaf L => exact LeafF.check_imp ctl A B P L h
  | route R => exact RouteF.check_imp ctl A B pd i0 P R h

variable {nR nC : ℕ}

structure BankF (nCtl m nR nC : ℕ) where
  A : Fin m → FQ
  B : Fin m → FQ
  ctl : Fin nCtl → CtrlF
  raw : Fin nR → ProfF
  rawMin : Fin nR → FQ
  closed : Fin nC → ProfF
  closedMin : Fin nC → FQ
  rawPieces : Fin nR → List (RawF (Fin nR ⊕ Fin nC) nCtl m)
  closedPieces : Fin nC → List (ClosedPF nR)
  src : Fin m → SourceF (Fin nR ⊕ Fin nC)
  lines : List (FQ × FQ)
  i0 : Fin nR ⊕ Fin nC

def BankF.pd (F : BankF nCtl m nR nC) : Fin nR ⊕ Fin nC → ProfF := Sum.elim F.raw F.closed

def BankF.toD (F : BankF nCtl m nR nC) : BankD nCtl m nR nC :=
  ⟨fun h => (F.A h).toQ, fun h => (F.B h).toQ, fun c => (F.ctl c).toD, fun i => (F.raw i).toD,
    fun i => (F.rawMin i).toQ, fun i => (F.closed i).toD, fun i => (F.closedMin i).toQ,
    fun i => (F.rawPieces i).map RawF.toD, fun i => (F.closedPieces i).map ClosedPF.toD,
    fun h => (F.src h).toD, linesQ F.lines, F.i0⟩

lemma BankF.pd_toD (F : BankF nCtl m nR nC) : F.toD.pd = fun i => (F.pd i).toD := by
  funext i; cases i <;> rfl

def BankF.srcOk (F : BankF nCtl m nR nC) (h : Fin m) : Bool :=
  lt zero (F.A h) && lt zero (F.B h) && (F.src h).check F.pd F.lines (F.A h) (F.B h)

def BankF.rawOk (F : BankF nCtl m nR nC) (i : Fin nR) : Bool :=
  (F.raw i).ok (F.rawMin i) &&
    chainF ((F.raw i).xs.headD zero) ((F.rawPieces i).map (fun x => (x.lo, x.hi))) ((F.raw i).xs.getLastD zero) &&
    (F.rawPieces i).all (RawF.check F.ctl F.A F.B F.pd F.i0 (F.raw i))

def BankF.clOk (F : BankF nCtl m nR nC) (i : Fin nC) : Bool :=
  (F.closed i).ok (F.closedMin i) &&
    chainF ((F.closed i).xs.headD zero) ((F.closedPieces i).map (fun x => (x.lo, x.hi)))
      ((F.closed i).xs.getLastD zero) &&
    (F.closedPieces i).all (ClosedPF.check F.raw (F.closed i))

lemma BankF.srcOk_imp (F : BankF nCtl m nR nC) (h : Fin m) (hs : F.srcOk h = true) : F.toD.srcOk h = true := by
  simp only [BankF.srcOk, Bool.and_eq_true, lt_eq, toQ_zero, decide_eq_true_eq] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  have h3' := SourceF.check_imp F.pd F.lines (F.A h) (F.B h) (F.src h) h3
  unfold BankD.srcOk
  rw [BankF.pd_toD]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h1, h2⟩, h3'⟩

lemma BankF.rawOk_imp (F : BankF nCtl m nR nC) (i : Fin nR) (hr : F.rawOk i = true) : F.toD.rawOk i = true := by
  simp only [BankF.rawOk, Bool.and_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  have h1' := ProfF.ok_imp _ _ h1
  rw [chainF_eq, List.map_map] at h2
  unfold BankD.rawOk
  rw [BankF.pd_toD]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨h1', ?_⟩, ?_⟩
  · have hc : ((F.rawPieces i).map RawF.toD).map (fun x => (x.lo, x.hi)) =
        List.map (pairQ ∘ fun x => (x.lo, x.hi)) (F.rawPieces i) := by
      rw [List.map_map]; apply List.map_congr_left; intro c _; cases c <;> rfl
    show chainQ ((mapQ (F.raw i).xs).headD 0) (((F.rawPieces i).map RawF.toD).map (fun x => (x.lo, x.hi)))
      ((mapQ (F.raw i).xs).getLastD 0) = true
    rw [hc, mapQ_headD, mapQ_getLastD]; exact h2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [List.all_eq_true] at h3
    exact RawF.check_imp F.ctl F.A F.B F.pd F.i0 (F.raw i) x (h3 x hx)

lemma BankF.clOk_imp (F : BankF nCtl m nR nC) (i : Fin nC) (hc : F.clOk i = true) : F.toD.clOk i = true := by
  simp only [BankF.clOk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have h1' := ProfF.ok_imp _ _ h1
  rw [chainF_eq, List.map_map] at h2
  unfold BankD.clOk
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨h1', ?_⟩, ?_⟩
  · have hc : ((F.closedPieces i).map ClosedPF.toD).map (fun x => (x.lo, x.hi)) =
        List.map (pairQ ∘ fun x => (x.lo, x.hi)) (F.closedPieces i) := by
      rw [List.map_map]; apply List.map_congr_left; intro c _; cases c <;> rfl
    show chainQ ((mapQ (F.closed i).xs).headD 0) (((F.closedPieces i).map ClosedPF.toD).map (fun x => (x.lo, x.hi)))
      ((mapQ (F.closed i).xs).getLastD 0) = true
    rw [hc, mapQ_headD, mapQ_getLastD]; exact h2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [List.all_eq_true] at h3
    exact ClosedPF.check_imp F.raw (F.closed i) x (h3 x hx)

def half : FQ := ⟨1, 1⟩

def BankF.rootCheck (F : BankF nCtl m nR nC) (root : Fin nR ⊕ Fin nC) (z : FQ) : Bool :=
  sortedF (F.pd root).xs && le (F.pd root).p half && le ((F.pd root).xs.headD zero) one &&
    le one ((F.pd root).xs.getLastD zero) && lt (evalF (F.pd root).xs (F.pd root).ys one) z

lemma BankF.rootCheck_imp (F : BankF nCtl m nR nC) (root : Fin nR ⊕ Fin nC) (z : FQ)
    (h : F.rootCheck root z = true) : F.toD.rootCheck root z.toQ = true := by
  simp only [BankF.rootCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  rw [lt_eq, evalF_eq _ _ _ h0, toQ_one] at h4
  simp only [le_eq, toQ_one, decide_eq_true_eq] at h1 h2 h3
  have hh : half.toQ = 1 / 2 := by simp [half, FQ.toQ]
  rw [hh] at h1
  unfold BankD.rootCheck
  rw [BankF.pd_toD]
  simp only [ProfF.toD, mapQ_headD, mapQ_getLastD, Bool.and_eq_true, decide_eq_true_eq]
  simp only [decide_eq_true_eq] at h4
  exact ⟨⟨⟨by simpa using h1, h2⟩, h3⟩, by first | exact decide_eq_true h4 | exact h4⟩

theorem BankF.check_of (F : BankF nCtl m nR nC) (hs : ∀ h, F.srcOk h = true) (hr : ∀ i, F.rawOk i = true)
    (hc : ∀ i, F.clOk i = true) : F.toD.check = true :=
  BankD.check_of F.toD (fun h => F.srcOk_imp h (hs h)) (fun i => F.rawOk_imp i (hr i)) (fun i => F.clOk_imp i (hc i))

theorem BankF.diagonal (F : BankF nCtl m nR nC) (hcert : ∀ c, (F.ctl c).toD.CertOK)
    (hl : ∀ p ∈ linesQ F.lines, LineOK p.1 p.2) (hchk : F.toD.check = true) (root : Fin nR ⊕ Fin nC) (z : FQ)
    (hr : F.rootCheck root z = true) :
    ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp ((z.toQ : ℝ) * k) :=
  F.toD.diagonal hcert hl hchk root z.toQ (F.rootCheck_imp root z hr)

theorem BankF.rawOk_of (F : BankF nCtl m nR nC) (i : Fin nR)
    (h1 : ((F.raw i).ok (F.rawMin i) &&
      chainF ((F.raw i).xs.headD zero) ((F.rawPieces i).map (fun x => (x.lo, x.hi))) ((F.raw i).xs.getLastD zero))
      = true)
    (h2 : ∀ x ∈ F.rawPieces i, RawF.check F.ctl F.A F.B F.pd F.i0 (F.raw i) x = true) : F.rawOk i = true := by
  simp only [BankF.rawOk, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨h1, h2⟩

theorem BankF.clOk_of (F : BankF nCtl m nR nC) (i : Fin nC)
    (h1 : ((F.closed i).ok (F.closedMin i) &&
      chainF ((F.closed i).xs.headD zero) ((F.closedPieces i).map (fun x => (x.lo, x.hi)))
        ((F.closed i).xs.getLastD zero)) = true)
    (h2 : ∀ x ∈ F.closedPieces i, ClosedPF.check F.raw (F.closed i) x = true) : F.clOk i = true := by
  simp only [BankF.clOk, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨h1, h2⟩

def CtrlF.dflt : CtrlF := ⟨zero, zero, zero, zero, zero, zero, zero⟩
def ProfF.dflt : ProfF := ⟨zero, [], []⟩
def SourceF.dflt {ι : Type} : SourceF ι := ⟨zero, zero, zero, zero, 0, 0, []⟩

end DiagRamsey.V5
