import ProximityPrize.SubmissionLower.Final50Price

set_option Elab.async false
set_option autoImplicit false

namespace Final50SharedPrice

open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)
open Final50Price (Messages SmallFactor ActiveFits ProperCut taylorLength primaryBox
  physicalPrice physicalDegree errors incidenceGap tiltedFits tiltedSurface)
open scoped Polynomial

abbrev slope : Shape := ⟨60,25,7⟩
abbrev slopeLoss : ℕ := 21385097131841

inductive Surface where
  | ordinary
  | tilted
  deriving DecidableEq

def surfaceScale : Surface → ℕ
  | .ordinary => 32
  | .tilted => 1920

def surface (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixed32 p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltedSurface f.chamber q

def weights (kind : Surface) (f : Shape) : Shape :=
  let b := surface kind f ⟨1,0,0⟩
  let j := surface kind f ⟨1,1,0⟩ - b
  let t := surface kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩

def coord (p : Shape) (i : Fin 3) : ℕ := (![p.b,p.j,p.t] : Fin 3 → ℕ) i

/-- A bound for one of the two linear expressions in the chamber width. -/
def expression (w q : Shape) (useIndex topIndex : Bool) : ℕ :=
  3*w.b*(if useIndex then q.j else q.b) + 3*w.j*q.j +
    w.t*(if topIndex then q.j else 3*q.t)

def deficit (r a : ℕ) (f : Shape) : Shape :=
  ⟨r*slope.b-a*f.b,r*slope.j-a*f.j,r*slope.t-a*f.t⟩

structure Rate where
  kind : Surface
  pivot : Fin 3
  split : ℕ
  topIndex : Bool
  amount : ℕ

/-- The endpoint arithmetic for the common surface cut.
    Both expressions in the width are tested. One top bound suffices on the whole interval. -/
def RateFits (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weights u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))

instance (f : Shape) (u : Rate) : Decidable (RateFits f u) := by
  unfold RateFits
  infer_instance


private theorem expression_line (w f : Shape) (r a : ℕ) (u t : Bool)
    (hb : a*f.b ≤ r*slope.b) (hj : a*f.j ≤ r*slope.j) (ht : a*f.t ≤ r*slope.t) :
    expression w (deficit r a f) u t + a*expression w f u t = r*expression w slope u t := by
  have b := Nat.sub_add_cancel hb
  have j := Nat.sub_add_cancel hj
  have h := Nat.sub_add_cancel ht
  cases u <;> cases t <;> simp only [expression, deficit, Bool.false_eq_true, ↓reduceIte, ite_true]
  all_goals
    rw [mul_add, mul_add]
    simp only [mul_assoc, ← mul_add, ← add_assoc] <;> ring_nf at b j h ⊢
    <;> nlinarith only [congrArg (fun z => w.b*z) b, congrArg (fun z => w.b*z) j,
      congrArg (fun z => w.j*z) j, congrArg (fun z => w.t*z) j, congrArg (fun z => w.t*z) h]

private theorem affine_of_endpoints (p q s x y W r a : ℕ)
    (hp : 0 < p) (hb : a*q ≤ r*p)
    (h₀ : x ≤ W) (h₁ : (q : ℤ)*x-p*y ≤ (q-(s:ℤ)*p)*W) :
    (r : ℤ)*x-a*y ≤ (r-(s:ℤ)*a)*W := by
  have hq : (0 : ℤ) < p := by exact_mod_cast hp
  have hr : (a : ℤ)*q ≤ (r : ℤ)*p := by exact_mod_cast hb
  have hzero : (0 : ℤ) ≤ (W : ℤ)-x := sub_nonneg.mpr (by exact_mod_cast h₀)
  have hA := mul_nonneg (sub_nonneg.mpr hr) hzero
  have hB := mul_nonneg (Int.natCast_nonneg a)
    (show 0 ≤ (p : ℤ)*((y:ℤ)-s*W)-q*((x:ℤ)-W) by linarith)
  apply sub_nonneg.mp
  refine nonneg_of_mul_nonneg_left ?_ hq
  have ident : (p : ℤ)*(((r:ℤ)-s*a)*W-((r:ℤ)*x-a*y)) =
      ((r:ℤ)*p-a*q)*((W:ℤ)-x)+a*(p*((y:ℤ)-s*W)-q*((x:ℤ)-W)) := by ring
  rw [mul_comm, ident]
  exact add_nonneg hA hB

private theorem pivot_pos (i : Fin 3) : 0 < coord slope i := by fin_cases i <;> decide

theorem rate_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (chooseWidth : Bool) :
    expression (weights u.kind f) (deficit r a f) chooseWidth u.topIndex ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let W := 3*surfaceScale u.kind*u.amount
  let w := weights u.kind f
  obtain ⟨_,hs,hpos,hcoord,h₀,h₁⟩ := hu
  have hp : 0 < p := pivot_pos u.pivot
  have hfitPivot : a*q ≤ r*p := hfit u.pivot
  have har : u.split*a ≤ r := by
    by_contra! hbad
    have hleft := Nat.mul_lt_mul_of_pos_right hbad hp
    have hright := Nat.mul_le_mul_left a (Nat.le_of_lt hpos)
    exact (not_lt_of_ge (hfitPivot.trans' (by
      simpa only [mul_left_comm, mul_assoc, mul_comm] using hright : u.split*a*p ≤ a*q))) hleft
  have f0 := expression_line w f q p chooseWidth u.topIndex
    (hcoord 0) (hcoord 1) (hcoord 2)
  have f1 := expression_line w f r a chooseWidth u.topIndex
    (hfit 0) (hfit 1) (hfit 2)
  have hend : ((q : ℤ)*expression w slope chooseWidth u.topIndex -
      p*expression w f chooseWidth u.topIndex) ≤ (q-(u.split:ℤ)*p)*W := by
    have hnum : expression w (deficit q p f) chooseWidth u.topIndex ≤ W*(q-u.split*p) := h₁ chooseWidth
    have hnum' : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤
        (W:ℤ)*(q-(u.split:ℤ)*p) := by
      have hh : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) ≤ (W:ℤ) * ((q-u.split*p : ℕ) : ℤ) := by exact_mod_cast hnum
      change u.split*p < q at hpos
      rwa [Int.ofNat_sub (Nat.le_of_lt hpos)] at hh
    have hline : (expression w (deficit q p f) chooseWidth u.topIndex : ℤ) +
        p*expression w f chooseWidth u.topIndex = q*expression w slope chooseWidth u.topIndex := by
      exact_mod_cast f0
    nlinarith
  have haff := affine_of_endpoints p q u.split _ _ W r a hp hfitPivot (h₀ chooseWidth) hend
  have hline : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) +
      a*expression w f chooseWidth u.topIndex = r*expression w slope chooseWidth u.topIndex := by
    exact_mod_cast f1
  have hgoal : (expression w (deficit r a f) chooseWidth u.topIndex : ℤ) ≤
      (W:ℤ)*(r-(u.split:ℤ)*a) := by nlinarith
  rw [← Nat.cast_mul, ← Nat.cast_sub har, ← Nat.cast_mul] at hgoal
  exact_mod_cast hgoal


theorem remainder_pos {f : Shape} {u : Rate} (hu : RateFits f u) {r a : ℕ}
    (hr : 0 < r) (hfit : ∀ i, a*coord f i ≤ r*coord slope i) : 0 < r-u.split*a := by
  obtain ⟨_,_,hs,_,_,_⟩ := hu
  have hp := pivot_pos u.pivot
  have hmark := hfit u.pivot
  by_cases ha : a = 0
  · simpa [ha] using hr
  have hm := Nat.mul_lt_mul_of_pos_left hs (Nat.pos_of_ne_zero ha)
  have h : u.split*a * coord slope u.pivot < r * coord slope u.pivot := by
    simpa only [mul_left_comm,mul_assoc,mul_comm] using hm.trans_le hmark
  exact Nat.sub_pos_of_lt (Nat.lt_of_mul_lt_mul_right h)

theorem chamber_bound {f : Shape} {u : Rate} (hu : RateFits f u) (r a : ℕ)
    (hfit : ∀ i, a*coord f i ≤ r*coord slope i) (g : Shape)
    (hg : K1_13.InBox g (deficit r a f)) (hgt : 3*g.t ≤ g.j) :
    3*((weights u.kind f).b*g.chamber.b + (weights u.kind f).j*g.j + (weights u.kind f).t*g.t) ≤
      (3*surfaceScale u.kind*u.amount)*(r-u.split*a) := by
  let w := weights u.kind f
  let d := deficit r a f
  have hgB : g.b ≤ d.b := hg.1
  have hgJ : g.j ≤ d.j := hg.2.1
  have hgT : g.t ≤ d.t := hg.2.2
  have hTop : 3*g.t ≤ (if u.topIndex then d.j else 3*d.t) := by
    split
    · exact hgt.trans hgJ
    · exact Nat.mul_le_mul_left _ hgT
  have component (i : Bool)
      (hB : max g.b g.j ≤ (if i then d.j else d.b)) :
      3*(w.b*g.chamber.b + w.j*g.j + w.t*g.t) ≤ expression w d i u.topIndex := by
    change 3*(w.b*max g.b g.j + w.j*g.j + w.t*g.t) ≤ _
    unfold expression
    calc
      _ = 3*w.b*max g.b g.j + 3*w.j*g.j + w.t*(3*g.t) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left _ hB) (Nat.mul_le_mul_left _ hgJ)) (Nat.mul_le_mul_left _ hTop)
  rcases le_total d.b d.j with h | h
  · exact (component true (max_le (hgB.trans h) hgJ)).trans (rate_bound hu r a hfit true)
  · exact (component false (max_le hgB (hgJ.trans h))).trans (rate_bound hu r a hfit false)

def additiveBase (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixed32 p q z h + 2*x.t*mixed32 p p p h
  let pt := mixed32 p q z p + 2*x.t*mixed32 p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)

def nonsharedFee (x : Shape) (l : ℕ) : ℕ :=
  ceilDiv (2*x.b*primaryBox.b^2*(chart (taylorLength+2) x.chamber).b) l

def price (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPrice x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l

/-- Charged proper count with a verified common surface rate. -/
def cShared : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ∀ K, ActiveFits f K →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) →
    ∀ l, 0 < l → ProperCut f Γ s l → ∀ u, RateFits (shape f) u →
      Γ.card ≤ price (shape f) l K u

end Final50SharedPrice
