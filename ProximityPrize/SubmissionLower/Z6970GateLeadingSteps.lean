import ProximityPrize.SubmissionLower.Z6970GateLeadingBase

set_option Elab.async false
set_option autoImplicit false

namespace Gate6970Leading

def evaluate (c0 c1 c2 c3 c4 n : ℕ) : ℕ :=
  c0 + c1*n + c2*(n*(n-1)/2) + c3*(n*(n-1)*(n-2)/6) + c4*(n*(n-1)*(n-2)*(n-3)/24)

def table (a n : ℕ) : ℕ :=
  let q := n/6
  match a,n%6 with
  | 1, 0 => evaluate 1 63 314 468 216 q
  | 1, 1 => evaluate 3 92 377 504 216 q
  | 1, 2 => evaluate 7 129 446 540 216 q
  | 1, 3 => evaluate 14 175 521 576 216 q
  | 1, 4 => evaluate 25 231 602 612 216 q
  | 1, 5 => evaluate 41 298 689 648 216 q
  | 2, 0 => evaluate 1 38 172 243 108 q
  | 2, 1 => evaluate 2 54 205 261 108 q
  | 2, 2 => evaluate 5 75 241 279 108 q
  | 2, 3 => evaluate 9 100 280 297 108 q
  | 2, 4 => evaluate 16 131 322 315 108 q
  | 2, 5 => evaluate 25 167 367 333 108 q
  | 3, 0 => evaluate 1 30 125 168 72 q
  | 3, 1 => evaluate 2 42 148 180 72 q
  | 3, 2 => evaluate 4 57 173 192 72 q
  | 3, 3 => evaluate 8 76 200 204 72 q
  | 3, 4 => evaluate 13 98 229 216 72 q
  | 3, 5 => evaluate 20 124 260 228 72 q
  | _, _ => 0

def stairs (a : ℕ) (x : ℤ) : ℤ := if x < 0 then 0 else (table a x.toNat : ℤ)

def conforms (a u : ℕ) : Bool :=
  decide (stairs a (u:ℤ) - stairs a ((u:ℤ)-a) = den (u:ℤ))

def check (lo len : ℕ) : Bool :=
  (List.range len).all fun i =>
    let u := lo+i
    conforms 1 u && conforms 2 u && conforms 3 u

theorem check_join {lo n m : ℕ} (h₁ : check lo n = true) (h₂ : check (lo+n) m = true) :
    check lo (n+m) = true := by
  unfold check at *
  rw [List.range_add]
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at *
  exact ⟨h₁, by simpa [Function.comp_def, Nat.add_assoc] using h₂⟩

theorem steps_of_check (ok : check 0 1680 = true) : StepRule stairs := by
  intro a x ha hb hx
  by_cases h : x < 0
  · simp [stairs,den,h,show x-(a:ℤ) < 0 by omega]
  have hh : x.toNat < 1680 := by omega
  have cast_eq : (x.toNat:ℤ) = x := by omega
  have mem := List.all_eq_true.mp ok x.toNat (List.mem_range.mpr hh)
  change (conforms 1 (0+x.toNat) && conforms 2 (0+x.toNat) && conforms 3 (0+x.toNat)) = true at mem
  simp only [Nat.zero_add, Bool.and_eq_true] at mem
  rcases mem with ⟨⟨v1,v2⟩,v3⟩
  interval_cases a
  · simpa only [cast_eq] using (of_decide_eq_true v1)
  · simpa only [cast_eq] using (of_decide_eq_true v2)
  · simpa only [cast_eq] using (of_decide_eq_true v3)

end Gate6970Leading
