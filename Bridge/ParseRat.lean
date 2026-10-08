import Batteries.Data.String.Lemmas
import Std.Data.String.ToInt
import Std.Data.String.ToNat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Definitions.Def_DiagRamsey_LuWangSource

/-! Reading the project's data strings: `parseRat (q.num.repr ++ "/" ++ q.den.repr) = q`. -/

open String DiagRamsey

namespace LuWangBridge

theorem slash_get' : Pos.Raw.get "/" 0 = '/' := by decide +kernel
theorem slash_end : "/".rawEndPos = ⟨1⟩ := by decide +kernel

theorem splitOnAux_slash (l m r : List Char) (acc : List String) :
    splitOnAux (ofList (l ++ m ++ r)) "/" ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == '/') r m.reverse).map ofList := by
  rw [splitOnAux]
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨c, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    have hget : Pos.Raw.get (ofList (l ++ (m ++ c :: r))) ⟨utf8Len l + utf8Len m⟩ = c := by
      simpa using get_of_valid (l ++ m) (c :: r)
    have hnext : Pos.Raw.next (ofList (l ++ (m ++ c :: r))) ⟨utf8Len l + utf8Len m⟩ =
        ⟨utf8Len l + utf8Len m + c.utf8Size⟩ := by
      simpa using next_of_valid (l ++ m) c r
    have hext : Pos.Raw.extract (ofList (l ++ (m ++ c :: r))) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩
        = ofList m := by
      simpa using extract_of_valid l m (c :: r)
    have hsn : Pos.Raw.next "/" 0 = ⟨1⟩ := by decide +kernel
    rw [slash_get', hget]
    by_cases h : c = '/'
    · subst h
      simp only [beq_self_eq_true, ↓reduceIte, hnext, hsn, slash_end, Pos.Raw.mk_le_mk,
        Nat.le_refl]
      have hu : (⟨utf8Len l + utf8Len m + Char.utf8Size '/'⟩ : Pos.Raw).unoffsetBy ⟨1⟩ =
          ⟨utf8Len l + utf8Len m⟩ := by
        have h1 : Char.utf8Size '/' = 1 := by decide
        apply Pos.Raw.ext; simp [h1]
      rw [hu, hext]
      have := splitOnAux_slash (l ++ m ++ ['/']) [] r (ofList m :: acc)
      simp only [List.append_assoc, List.cons_append, List.nil_append, utf8Len_append,
        utf8Len_cons, utf8Len_nil, List.append_nil, Nat.add_zero] at this
      simp only [Nat.zero_add, Nat.add_assoc] at this ⊢
      rw [this]
      simp [List.splitOnPPrepend_cons_eq_if]
    · have hc : (c == '/') = false := by simpa using h
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hu : (⟨utf8Len l + utf8Len m⟩ : Pos.Raw).unoffsetBy 0 = ⟨utf8Len l + utf8Len m⟩ := by
        apply Pos.Raw.ext; simp
      rw [hu, hnext]
      have := splitOnAux_slash l (m ++ [c]) r acc
      simp only [List.append_assoc, List.cons_append, List.nil_append, utf8Len_append,
        utf8Len_cons, utf8Len_nil, Nat.zero_add, Nat.add_assoc] at this ⊢
      rw [this]
      simp [List.splitOnPPrepend_cons_eq_if, hc]
termination_by r.length

theorem splitOn_slash (x y : List Char) (hx : '/' ∉ x) (hy : '/' ∉ y) :
    (ofList (x ++ '/' :: y)).splitOn "/" = [ofList x, ofList y] := by
  have h := splitOnAux_slash [] [] (x ++ '/' :: y) []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero] at h
  rw [String.splitOn, if_neg (by decide +kernel)]
  refine h.trans ?_
  simp only [List.reverse_nil, List.nil_append, List.splitOnPPrepend_nil_right]
  rw [List.splitOnP_append_cons_of_forall_mem (fun z hz => by simp only [beq_eq_false_iff_ne, ne_eq]; rintro rfl; exact hx hz) '/' (by simp),
    List.splitOnP_eq_singleton (fun z hz => by simp only [beq_eq_false_iff_ne, ne_eq]; rintro rfl; exact hy hz)]
  simp


theorem not_slash_toDigits (n : ℕ) : '/' ∉ Nat.toDigits 10 n := by
  intro h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

theorem not_slash_nat (n : ℕ) : '/' ∉ (Nat.repr n).toList := by
  simpa [Nat.repr] using not_slash_toDigits n

theorem not_slash_int (a : ℤ) : '/' ∉ a.repr.toList := by
  cases a with
  | ofNat n => simpa [Int.repr] using not_slash_nat n
  | negSucc n => simpa [Int.repr] using not_slash_nat (n + 1)

theorem parseRat_repr (a : ℤ) (b : ℕ) :
    parseRat (a.repr ++ "/" ++ Nat.repr b) = (a : ℚ) / (b : ℚ) := by
  have e : a.repr ++ "/" ++ Nat.repr b = ofList (a.repr.toList ++ '/' :: (Nat.repr b).toList) := by
    apply String.toList_injective; simp
  rw [parseRat, e, splitOn_slash _ _ (not_slash_int a) (not_slash_nat b)]
  simp only [String.ofList_toList, Int.toInt?_repr, Nat.toNat?_repr, Option.getD_some]

theorem parseRat_fmt (q : ℚ) : parseRat (q.num.repr ++ "/" ++ Nat.repr q.den) = q := by
  rw [parseRat_repr]; exact Rat.num_div_den q

end LuWangBridge
