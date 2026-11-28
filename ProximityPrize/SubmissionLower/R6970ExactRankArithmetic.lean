import ProximityPrize.SubmissionLower.R6970PrimaryRankBill

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace Research6970.ExactRank

abbrev Term := ℚ × ℚ

def pay (cap x : ℚ) (terms : List Term) : ℚ :=
  (terms.map fun t => t.2 * min t.1 (cap-x)).sum

def active (closed : Bool) (cap x : ℚ) (t : Term) : Prop :=
  if closed then cap-x ≤ t.1 else cap-x < t.1

instance (closed : Bool) (cap x : ℚ) (t : Term) : Decidable (active closed cap x t) := by
  unfold active
  cases closed <;> infer_instance

def slope (closed : Bool) (cap x : ℚ) (terms : List Term) : ℚ :=
  (terms.map fun t => if active closed cap x t then t.2 else 0).sum

private theorem term_tangent {c x z : ℚ} {t : Term} (hw : 0 ≤ t.2) (closed : Bool) :
    t.2 * min t.1 (c-z) ≤
      t.2 * min t.1 (c-x) - (if active closed c x t then t.2 else 0) * (z-x) := by
  by_cases on : active closed c x t
  · have h : c-x ≤ t.1 := by
      cases closed
      · exact le_of_lt (by simpa [active] using on)
      · simpa [active] using on
    rw [ite_eq_left on, min_eq_right h]
    have hm := mul_le_mul_of_nonneg_left (min_le_right t.1 (c-z)) hw
    nlinarith only [hm]
  · have h : t.1 ≤ c-x := by
      cases closed
      · exact le_of_not_gt (show ¬ c - x < t.1 from on)
      · exact le_of_not_ge (show ¬ c - x ≤ t.1 from on)
    rw [ite_eq_right on, zero_mul, sub_zero, min_eq_left h]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hw

theorem pay_le_affine {xs : List Term} {c x z : ℚ} (closed : Bool)
    (weights : ∀ t ∈ xs, 0 ≤ t.2) :
    pay c z xs ≤ pay c x xs - slope closed c x xs * (z-x) := by
  induction xs with
  | nil => simp [pay,slope]
  | cons t ts ih =>
    have h0 := term_tangent (c:=c) (x:=x) (z:=z) (weights t (List.mem_cons_self)) closed
    have h1 := ih (fun u hu => weights u (List.mem_cons_of_mem t hu))
    simp only [pay,slope,List.map_cons,List.sum_cons] at *
    nlinarith only [h0,h1]

theorem pay_le_support {xs : List Term} {c x z d : ℚ}
    (weights : ∀ t ∈ xs, 0 ≤ t.2)
    (lo : slope false c x xs ≤ d) (hi : d ≤ slope true c x xs) :
    pay c z xs ≤ pay c x xs - d*(z-x) := by
  rcases le_total z x with h|h
  · have ha := pay_le_affine (c:=c) (x:=x) (z:=z) false weights
    have hb := mul_le_mul_of_nonneg_right lo (sub_nonneg.mpr h)
    nlinarith only [ha,hb]
  · have ha := pay_le_affine (c:=c) (x:=x) (z:=z) true weights
    have hb := mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr h)
    nlinarith only [ha,hb]

def rank (lamCoeff muCoeff : ℚ) (x y : ℚ) : ℚ :=
  4*lamCoeff*(y+2)*(x+1) - 2*lamCoeff*(x+1)^2 + muCoeff*(x+1) + (y+2)^2 + 1

structure Vertex where
  y : ℚ
  x : ℚ
  fall : ℚ
  deriving DecidableEq

structure Frame where
  lamCoeff : ℚ
  muCoeff : ℚ
  capX : ℚ
  capY : ℚ
  xs : List Term
  ys : List Term
  deriving DecidableEq

def deriv (f : Frame) (v : Vertex) : ℚ := 4*f.lamCoeff*(v.y-v.x+1) + f.muCoeff - v.fall

def atVertex (f : Frame) (v : Vertex) : ℚ :=
  rank f.lamCoeff f.muCoeff v.x v.y + pay f.capX v.x f.xs

def support (f : Frame) (v : Vertex) : Prop :=
  slope false f.capX v.x f.xs ≤ v.fall ∧ v.fall ≤ slope true f.capX v.x f.xs ∧
    deriv f v * (-v.x) ≤ 0 ∧ deriv f v * (f.capX-v.x) ≤ 0

instance (f : Frame) (v : Vertex) : Decidable (support f v) := by unfold support; infer_instance

private theorem vertex_bound {f : Frame} {v : Vertex} {x : ℚ}
    (lam : 0 ≤ f.lamCoeff) (weights : ∀ t ∈ f.xs, 0 ≤ t.2)
    (lower : 0 ≤ x) (upper : x ≤ f.capX) (test : support f v) :
    rank f.lamCoeff f.muCoeff x v.y + pay f.capX x f.xs ≤ atVertex f v := by
  have hPay := pay_le_support (z:=x) weights test.1 test.2.1
  have hSquare := mul_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) lam) (sq_nonneg (x-v.x))
  have hDeriv : deriv f v * (x-v.x) ≤ 0 := by
    rcases le_total 0 (deriv f v) with h|h
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right upper _) h).trans test.2.2.2
    · have hmul := mul_le_mul_of_nonpos_left (sub_le_sub_right lower v.x) h
      rw [zero_sub] at hmul
      exact hmul.trans test.2.2.1
  unfold atVertex rank deriv at *
  nlinarith only [hPay,hSquare,hDeriv]

def middle (a b : Vertex) : ℚ := (a.y+b.y)/2

def lineY (f : Frame) (a b : Vertex) (y : ℚ) : ℚ :=
  pay f.capY (middle a b) f.ys - slope true f.capY (middle a b) f.ys * (y-middle a b)

private theorem secant_bound (lamCoeff muCoeff x y l u A B target : ℚ)
    (low : l ≤ y) (high : y ≤ u)
    (h₀ : rank lamCoeff muCoeff x l + (A+B*l) ≤ target)
    (h₁ : rank lamCoeff muCoeff x u + (A+B*u) ≤ target) :
    rank lamCoeff muCoeff x y + (A+B*y) ≤ target := by
  let coeff := 4*lamCoeff*(x+1)+4+B
  by_cases ht : 0 ≤ y+l+coeff
  · have hm := mul_nonneg (sub_nonneg.mpr high) (show 0 ≤ u+y+coeff by linarith only [low,high,ht])
    have eq : rank lamCoeff muCoeff x u + (A+B*u) - (rank lamCoeff muCoeff x y + (A+B*y)) =
        (u-y)*(u+y+coeff) := by unfold rank coeff; ring
    linarith only [hm,eq,h₁]
  · have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr low) (le_of_not_ge ht)
    have eq : rank lamCoeff muCoeff x y + (A+B*y) - (rank lamCoeff muCoeff x l + (A+B*l)) =
        (y-l)*(y+l+coeff) := by unfold rank coeff; ring
    linarith only [hm,eq,h₀]

def adjacent (f : Frame) (limit : ℚ) (a b : Vertex) : Prop :=
  a.y ≤ b.y ∧ atVertex f a + lineY f a b a.y ≤ limit ∧ atVertex f b + lineY f a b b.y ≤ limit

instance (f : Frame) (limit : ℚ) (a b : Vertex) : Decidable (adjacent f limit a b) := by
  unfold adjacent; infer_instance

private theorem segment_bound {f : Frame} {a b : Vertex} {x y limit : ℚ}
    (lam : 0 ≤ f.lamCoeff) (wx : ∀ t ∈ f.xs, 0 ≤ t.2) (wy : ∀ t ∈ f.ys, 0 ≤ t.2)
    (lx : 0 ≤ x) (ux : x ≤ f.capX) (ly : a.y ≤ y) (uy : y ≤ b.y)
    (ha : support f a) (hb : support f b) (edge : adjacent f limit a b) :
    rank f.lamCoeff f.muCoeff x y + pay f.capX x f.xs + pay f.capY y f.ys ≤ limit := by
  have h₀ := vertex_bound lam wx lx ux ha
  have h₁ := vertex_bound lam wx lx ux hb
  have hy := pay_le_affine (c:=f.capY) (x:=middle a b) (z:=y) true wy
  let D := slope true f.capY (middle a b) f.ys
  let A := pay f.capY (middle a b) f.ys + D*middle a b + pay f.capX x f.xs
  have ee (z : ℚ) : A + (-D)*z = lineY f a b z + pay f.capX x f.xs := by
    unfold A D lineY; ring
  have s₀ : rank f.lamCoeff f.muCoeff x a.y + (A+(-D)*a.y) ≤ limit := by
    rw [ee]; linarith only [h₀,edge.2.1]
  have s₁ : rank f.lamCoeff f.muCoeff x b.y + (A+(-D)*b.y) ≤ limit := by
    rw [ee]; linarith only [h₁,edge.2.2]
  have h := secant_bound f.lamCoeff f.muCoeff x y a.y b.y A (-D) limit ly uy s₀ s₁
  rw [ee] at h
  unfold lineY at h
  linarith only [h,hy]

def checkFrom (f : Frame) (limit : ℚ) (a : Vertex) : List Vertex → Prop
  | [] => a.y = f.capY ∧ atVertex f a + pay f.capY a.y f.ys ≤ limit
  | b::more => support f b ∧ adjacent f limit a b ∧ checkFrom f limit b more

instance (f : Frame) (limit : ℚ) (a : Vertex) (rest : List Vertex) :
    Decidable (checkFrom f limit a rest) := by
  induction rest generalizing a with
  | nil => unfold checkFrom; infer_instance
  | cons b bs ih =>
    haveI := ih b
    change Decidable (support f b ∧ adjacent f limit a b ∧ checkFrom f limit b bs)
    infer_instance

private theorem from_bound {f : Frame} {limit x y : ℚ} {a : Vertex} {rest : List Vertex}
    (lam : 0 ≤ f.lamCoeff) (wx : ∀ t ∈ f.xs, 0 ≤ t.2) (wy : ∀ t ∈ f.ys, 0 ≤ t.2)
    (lx : 0 ≤ x) (ux : x ≤ f.capX) (ly : a.y ≤ y) (uy : y ≤ f.capY)
    (ha : support f a) (h : checkFrom f limit a rest) :
    rank f.lamCoeff f.muCoeff x y + pay f.capX x f.xs + pay f.capY y f.ys ≤ limit := by
  induction rest generalizing a with
  | nil =>
    obtain ⟨top,check⟩ := h
    have eq : y = a.y := le_antisymm (top.symm ▸ uy) ly
    rw [eq]
    have b := vertex_bound lam wx lx ux ha
    linarith only [b,check]
  | cons b rest ih =>
    obtain ⟨hb,edge,tail⟩ := h
    rcases le_total y b.y with left|right
    · exact segment_bound lam wx wy lx ux ly left ha hb edge
    · exact ih right hb tail

def checked (f : Frame) (limit : ℚ) (first : Vertex) (rest : List Vertex) : Prop :=
  first.y = 0 ∧ support f first ∧ checkFrom f limit first rest

instance (f : Frame) (limit : ℚ) (first : Vertex) (rest : List Vertex) :
    Decidable (checked f limit first rest) := by unfold checked; infer_instance

theorem bound {f : Frame} {limit x y : ℚ} {first : Vertex} {rest : List Vertex}
    (lam : 0 ≤ f.lamCoeff) (wx : ∀ t ∈ f.xs, 0 ≤ t.2) (wy : ∀ t ∈ f.ys, 0 ≤ t.2)
    (lx : 0 ≤ x) (ux : x ≤ f.capX) (ly : 0 ≤ y) (uy : y ≤ f.capY)
    (test : checked f limit first rest) :
    rank f.lamCoeff f.muCoeff x y + pay f.capX x f.xs + pay f.capY y f.ys ≤ limit :=
  from_bound lam wx wy lx ux (test.1.symm ▸ ly) uy test.2.1 test.2.2

end Research6970.ExactRank
