import ProximityPrize.SubmissionLower.UpperBranch4

set_option autoImplicit false

namespace KoalaH2430Contact
open K1_14 (Shape)
open P1_7_4 (pairMinSeed pairMinOrdinate sharedBound)
open K1_14_2_2_4 (highCap highScale pairCap residualShape)
open private at_endpoints sectionBound cast_trapezoid from ProximityPrize.SubmissionLower.UpperBranch4

private theorem seed_endpoints_box (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z l u:ℕ} (hl : l ≤ z) (hu : z ≤ u) (hz:u≤pairMinOrdinate s t) (hsJ:s.J≤ s.B) (htJ:t.J≤t.B)
    (hside : u ≤ min (s.B-s.J) (t.B-t.J) ∨ min (s.B-s.J) (t.B-t.J) ≤ l)
    (hL:sectionBound s t a b 0 0 l≤M)
    (hU:sectionBound s t a b 0 0 u≤M) :
    sectionBound s t a b 0 x z≤M:=by
  let C:=min (s.B-s.J) (t.B-t.J)
  let F (y:ℕ):=sectionBound s t a b 0 0 y
  have hcS:C≤ s.B-s.J:=min_le_left _ _
  have hcT:C≤t.B-t.J:=min_le_right _ _
  change F z≤M
  rcases hside with hlow | hhigh
  · refine at_endpoints (F := F) (l := l) (u := u) (a := 0)
      (b:=a - b*((s.J:ℚ)+t.J))
      (c:=b*((s.B:ℚ)*t.J+(t.B:ℚ)*s.J - (s.J:ℚ)*t.J))
      hl hu le_rfl ?_ hL hU
    intro y _ hy
    have hyC : y≤C := hy.trans hlow
    have hsj:s.J≤ s.B-y:=by omega
    have htj:t.J≤t.B-y:=by omega
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y)*min s.J (s.B-y) - min s.J (s.B-y)*min t.J (t.B-y):ℕ):ℚ)=_
    rw [min_eq_left hsj, min_eq_left htj, cast_trapezoid _ _ _ _ hsj,
      Nat.cast_sub (show y≤ s.B by omega),Nat.cast_sub (show y≤t.B by omega)]
    ring
  · refine at_endpoints (F := F) (l := l) (u := u) (a := b)
      (b:=a - b*((s.B:ℚ)+t.B)) (c:=b*(s.B:ℚ)*t.B)
      hl hu hb ?_ hL hU
    intro y hy hyZ
    have hyC : C ≤ y := hhigh.trans hy
    have hyS:=(hyZ.trans hz).trans (min_le_left s.B t.B)
    have hyT:=(hyZ.trans hz).trans (min_le_right s.B t.B)
    change a * (y : ℚ) + b * (((s.B-y) * min t.J (t.B-y) +
      (t.B-y)*min s.J (s.B-y) - min s.J (s.B-y)*min t.J (t.B-y):ℕ):ℚ)=_
    rw [cast_trapezoid _ _ _ _ (min_le_right _ _)]
    rcases min_choice (s.B-s.J) (t.B-t.J) with hc | hc
    · have hj : s.B-y ≤ s.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hyC; omega
      rw [min_eq_right hj,Nat.cast_sub hyS,Nat.cast_sub hyT]
      ring
    · have hj : t.B-y ≤ t.J := by change min (s.B-s.J) (t.B-t.J) ≤ y at hyC; omega
      rw [min_eq_right hj,Nat.cast_sub hyS,Nat.cast_sub hyT]
      ring
private theorem ordinate_endpoints_box (s t : Shape) {a b M : ℚ} (hb : 0 ≤ b)
    {x z l u:ℕ} (hl:l≤x) (hu:x≤u) (hx:u≤pairMinSeed s t) (hsJ:s.J≤ s.B) (htJ:t.J≤t.B)
    (h0:sectionBound s t a b 1 l 0≤M)
    (hX:sectionBound s t a b 1 u 0≤M) :
    sectionBound s t a b 1 x z≤M:=by
  have hmono : sectionBound s t a b 1 x z ≤ sectionBound s t a b 1 x 0 := by
    change a * (x : ℚ) + b * (((s.U-x) * min t.J (t.B-z) +
      (t.U-x)*min s.J (s.B-z):ℕ):ℚ)≤a*(x:ℚ) +
      b*(((s.U-x)*min t.J (t.B-0)+(t.U-x)*min s.J (s.B-0):ℕ):ℚ)
    simp only [Nat.sub_zero,min_eq_left hsJ,min_eq_left htJ]
    apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb)
    exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_left _ (min_le_left _ _))
      (Nat.mul_le_mul_left _ (min_le_left _ _))
  apply hmono.trans
  refine at_endpoints (F := fun y => sectionBound s t a b 1 y 0)
    (l:=l) (u:=u) (a:=0)
    (b:=a - b*((t.J:ℚ)+s.J)) (c:=b*((s.U:ℚ)*t.J+(t.U:ℚ)*s.J))
    hl hu le_rfl ?_ h0 hX
  intro y _ hy
  change a * (y : ℚ) + b * (((s.U-y) * min t.J (t.B-0) +
    (t.U-y)*min s.J (s.B-0):ℕ):ℚ)=_
  simp only [Nat.sub_zero, min_eq_left hsJ, min_eq_left htJ, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub ((hy.trans hx).trans (min_le_left s.U t.U)),
    Nat.cast_sub ((hy.trans hx).trans (min_le_right s.U t.U))]
  ring
private theorem jet_endpoints_box (s t : Shape) {a b M : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {x z l u:ℕ} (hl:l≤x) (hu:x≤u) (hx:u≤pairMinSeed s t)
    (h0:sectionBound s t a b 3 l 0≤M)
    (hX:sectionBound s t a b 3 u 0≤M) :
    sectionBound s t a b 3 x z≤M:=by
  change sectionBound s t a b 3 x 0≤M
  refine at_endpoints (F := fun y => sectionBound s t a b 3 y 0)
    (l:=l) (u:=u) (a:=a+b)
    (b := -b*((s.U:ℚ)+t.U)) (c:=b*(s.U:ℚ)*t.U)
    hl hu (add_nonneg ha hb) ?_ h0 hX
  intro y _ hy
  change a*((y*y:ℕ):ℚ)+b*(((s.U-y)*(t.U-y):ℕ):ℚ)=_
  simp only [Nat.cast_mul, Nat.cast_sub ((hy.trans hx).trans (min_le_left s.U t.U)),
    Nat.cast_sub ((hy.trans hx).trans (min_le_right s.U t.U))]
  ring

private theorem form (s t : Shape) (k : Fin 4) (x z r m : ℕ) :
    sharedBound s t x z r m true k =
      sectionBound s t (highScale r k : ℚ)⁻¹ (((m+1-r)^2 : ℕ) : ℚ)⁻¹ k x z := by
  simp only [sharedBound, sectionBound, Bool.true_or, if_true, div_eq_mul_inv, mul_comm]

theorem seed_box (s t : Shape) {M : ℚ} {x z l u r m : ℕ}
    (hl:l≤z) (hu:z≤u) (hz:u≤pairMinOrdinate s t)
    (hs:s.J≤s.B) (ht:t.J≤t.B)
    (hb:u≤min (s.B-s.J) (t.B-t.J) ∨ min (s.B-s.J) (t.B-t.J)≤l)
    (hL:sharedBound s t 0 l r m true 0≤M) (hU:sharedBound s t 0 u r m true 0≤M) :
    sharedBound s t x z r m true 0≤M := by
  rw [form] at hL hU ⊢
  exact seed_endpoints_box s t (by positivity) hl hu hz hs ht hb hL hU

theorem ordinate_box (s t : Shape) {M : ℚ} {x z l u r m : ℕ}
    (hl:l≤x) (hu:x≤u) (hx:u≤pairMinSeed s t) (hs:s.J≤s.B) (ht:t.J≤t.B)
    (hL:sharedBound s t l 0 r m true 1≤M) (hU:sharedBound s t u 0 r m true 1≤M) :
    sharedBound s t x z r m true 1≤M := by
  rw [form] at hL hU ⊢
  exact ordinate_endpoints_box s t (by positivity) hl hu hx hs ht hL hU

theorem jet_box (s t : Shape) {M : ℚ} {x z l u r m : ℕ}
    (hl:l≤x) (hu:x≤u) (hx:u≤pairMinSeed s t)
    (hL:sharedBound s t l 0 r m true 3≤M) (hU:sharedBound s t u 0 r m true 3≤M) :
    sharedBound s t x z r m true 3≤M := by
  rw [form] at hL hU ⊢
  exact jet_endpoints_box s t (by positivity) (by positivity) hl hu hx hL hU

#print axioms seed_box
#print axioms ordinate_box
#print axioms jet_box
end KoalaH2430Contact

