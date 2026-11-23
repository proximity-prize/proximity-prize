import ProximityPrize.SubmissionLower.R6960Low6960TiltedRectangle
import ProximityPrize.SubmissionLower.R6960Low6960WeightedRate

set_option autoImplicit false
set_option Elab.async false

/-! Closed natural-number forms of the two price primitives (the fourth mixed difference
`mixed32` and the bent ambient mix `tiltedSurface`), and copies of the receipt prices built on
them. Every copy is proved equal to the original, so the allocation receipts may be checked by
the kernel on the fast forms. -/
namespace Low6960FastPrice
open K1_13 (Shape mixed32 volume32 difference chart liftedChart ceilDiv)
open Low6960Prices (BentCap bentIntegral addBent ambientMix tiltedSurface bentGraph bentLift
  taylorLength primaryBox errors incidenceGap physicalDegree tiltedFits activeFitsPrice activeLoss
  activeClips surfaceNumerator32 physicalPriceOld physicalPriceWith physicalPriceTilted
  physicalPriceActive physicalPrice tiltedSurfaceActive)

def mixPos (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  16 * pb * qj * rj * st +
    16 * pb * qj * rt * sj +
    16 * pb * qt * rj * sj +
    144 * pb * qt * rt * st +
    16 * pj * qb * rj * st +
    16 * pj * qb * rt * sj +
    16 * pj * qj * rb * st +
    16 * pj * qj * rt * sb +
    56 * pj * qj * rt * st +
    16 * pj * qt * rb * sj +
    16 * pj * qt * rj * sb +
    56 * pj * qt * rj * st +
    56 * pj * qt * rt * sj +
    16 * pt * qb * rj * sj +
    144 * pt * qb * rt * st +
    16 * pt * qj * rb * sj +
    16 * pt * qj * rj * sb +
    56 * pt * qj * rj * st +
    56 * pt * qj * rt * sj +
    144 * pt * qt * rb * st +
    56 * pt * qt * rj * sj +
    144 * pt * qt * rt * sb +
    216 * pt * qt * rt * st

def mixNeg (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  48 * pb * qj * rt * st +
    48 * pb * qt * rj * st +
    48 * pb * qt * rt * sj +
    48 * pj * qb * rt * st +
    24 * pj * qj * rj * st +
    24 * pj * qj * rt * sj +
    48 * pj * qt * rb * st +
    24 * pj * qt * rj * sj +
    48 * pj * qt * rt * sb +
    120 * pj * qt * rt * st +
    48 * pt * qb * rj * st +
    48 * pt * qb * rt * sj +
    48 * pt * qj * rb * st +
    24 * pt * qj * rj * sj +
    48 * pt * qj * rt * sb +
    120 * pt * qj * rt * st +
    48 * pt * qt * rb * sj +
    48 * pt * qt * rj * sb +
    120 * pt * qt * rj * st +
    120 * pt * qt * rt * sj

def mix4 (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  mixPos pb pj pt qb qj qt rb rj rt sb sj st - mixNeg pb pj pt qb qj qt rb rj rt sb sj st

/-- Closed form of `mixed32`. -/
def mixF (p q r s : Shape) : ℕ :=
  mix4 p.b p.j p.t q.b q.j q.t r.b r.j r.t s.b s.j s.t

theorem mixF_eq (p q r s : Shape) : mixF p q r s = mixed32 p q r s := by
  obtain ⟨pb,pj,pt⟩ := p
  obtain ⟨qb,qj,qt⟩ := q
  obtain ⟨rb,rj,rt⟩ := r
  obtain ⟨sb,sj,st⟩ := s
  have key : difference (difference (difference (difference volume32 ⟨pb,pj,pt⟩) ⟨qb,qj,qt⟩)
      ⟨rb,rj,rt⟩) ⟨sb,sj,st⟩ ⟨0,0,0⟩ = (mixPos pb pj pt qb qj qt rb rj rt sb sj st : ℤ) -
        (mixNeg pb pj pt qb qj qt rb rj rt sb sj st : ℤ) := by
    simp only [difference, volume32, K1_13.Shape.plus, mixPos, mixNeg]
    push_cast
    ring
  unfold mixF mix4 mixed32
  dsimp only
  rw [key]
  omega

def bentPos (B J T H : ℕ) : ℕ :=
  H * (160*T^2*H^2 + 540*T^4 + 960*J*H^3 + 960*J*T^2*H + 840*J^2*T^2 + 240*J^3*H +
    640*B*T*H^2 + 1440*B*T^3 + 640*B*J*H^2 + 960*B*J*T*H + 480*B*J^2*T)

def bentNeg (B J T H : ℕ) : ℕ :=
  H * (576*H^4 + 480*T^3*H + 320*J*T*H^2 + 1200*J*T^3 + 480*J^2*H^2 + 480*J^2*T*H +
    240*J^3*T + 960*B*H^3 + 1440*B*T^2*H + 1440*B*J*T^2 + 480*B*J^2*H)

theorem bent_eq (B J T H : ℕ) :
    bentIntegral B J T H = (bentPos B J T H : ℤ) - (bentNeg B J T H : ℤ) := by
  simp only [bentIntegral, bentPos, bentNeg]
  push_cast
  ring

/-- One signed term of the ambient mix, kept as a positive and a negative part. -/
def mixStep (acc : ℕ × ℕ) (boxes : List BentCap) : ℕ × ℕ :=
  let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
  let a := bentPos s.1.b s.1.j s.1.t s.2
  let n := bentNeg s.1.b s.1.j s.1.t s.2
  if (5 - boxes.length) % 2 = 0 then (acc.1 + a, acc.2 + n) else (acc.1 + n, acc.2 + a)

def ambientMixF (caps : List BentCap) : ℕ :=
  let r := caps.sublists.foldl mixStep (0,0)
  r.1 - r.2

private theorem fold_eq (Ls : List (List BentCap)) (a : ℤ) (acc : ℕ × ℕ)
    (h : a = acc.1 - acc.2) :
    Ls.foldl (fun acc boxes =>
      let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
      acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) a =
      ((Ls.foldl mixStep acc).1 : ℤ) - (Ls.foldl mixStep acc).2 := by
  induction Ls generalizing a acc with
  | nil => simpa using h
  | cons boxes rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [bent_eq, h, neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (5 - boxes.length) with e | e
    · simp only [mixStep, e, ↓reduceIte, pow_zero, one_mul]
      push_cast; ring
    · simp only [mixStep, e, Nat.one_ne_zero, ↓reduceIte, pow_one]
      push_cast; ring

theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = ambientMixF caps := by
  have key := fold_eq caps.sublists 0 (0,0) (by simp)
  unfold ambientMix ambientMixF
  dsimp only at key ⊢
  rw [key]
  omega

/-- Closed form of `tiltedSurface`. -/
def tiltF (p q : Shape) : ℕ :=
  ambientMixF [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]

theorem tiltF_eq (p q : Shape) : tiltF p q = tiltedSurface p q := by
  unfold tiltF tiltedSurface
  rw [ambientMix_eq]

/-! Physical prices. -/

def surfaceNumerator32F (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixF p q (chart (L + 1) p) (chart (L + 2) p))
    (mixF p q a b + (L + 1) * mixF p q g b + (L + 2) * mixF p q g a)

def physicalPriceOldF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32F p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceWithF (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

def physicalPriceF (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOldF x l) (physicalPriceWithF x l (tiltF x.chamber primaryBox))
    if activeFitsPrice x K then
      min base (physicalPriceWithF x l (tiltF x.chamber primaryBox - activeLoss (activeClips x.chamber K)))
    else base
  else physicalPriceOldF x l

theorem physicalPriceOldF_eq (x : Shape) (l : ℕ) : physicalPriceOldF x l = physicalPriceOld x l := by
  simp only [physicalPriceOldF, physicalPriceOld, surfaceNumerator32F, surfaceNumerator32, mixF_eq]

theorem physicalPriceWithF_eq (x : Shape) (l s : ℕ) : physicalPriceWithF x l s = physicalPriceWith x l s := by
  simp only [physicalPriceWithF, physicalPriceWith, mixF_eq]

theorem physicalPriceF_eq (x : Shape) (l K : ℕ) : physicalPriceF x l K = physicalPrice x l K := by
  simp only [physicalPriceF, physicalPrice, physicalPriceTilted, physicalPriceActive,
    tiltedSurfaceActive, physicalPriceOldF_eq, physicalPriceWithF_eq, tiltF_eq]

/-! Cut prices and the contracted price. -/

def chargeF (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b *
      (chart (taylorLength + 1) p).b) incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)

theorem chargeF_eq (x : Shape) (l scale S : ℕ) :
    chargeF x l scale S = Low6960RetainedCut.cutPrice x l scale S := by
  rw [Low6960Rectangle.cut_eq]
  simp only [chargeF, Low6960Rectangle.charge, mixF_eq]

def fourSurfaceF (p q : Shape) : ℕ :=
  mixF p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

theorem fourSurfaceF_eq (p q : Shape) : fourSurfaceF p q = Low6960RetainedCut.fourSurface p q := by
  simp only [fourSurfaceF, Low6960RetainedCut.fourSurface, mixF_eq]

def contractedPriceF (x h : Shape) (l active : ℕ) : ℕ :=
  let q := Low6960RetainedCut.chamberHull (Low6960RetainedCut.residualBox h l)
  let old := physicalPriceF x l active
  let four := if 0 < q.t then min old (chargeF x l 32 (fourSurfaceF x.chamber q)) else old
  if tiltedFits x then min four (chargeF x l (60*32) (tiltF x.chamber q)) else four

theorem contractedPriceF_eq (x h : Shape) (l active : ℕ) :
    contractedPriceF x h l active = Low6960RetainedCut.contractedPrice x h l active := by
  simp only [contractedPriceF, Low6960RetainedCut.contractedPrice, physicalPriceF_eq, chargeF_eq,
    fourSurfaceF_eq, tiltF_eq]

/-! Shared rates. -/
open Low6960SharedPrice (Surface Rate surfaceScale coord expression deficit slope)

def surfaceF (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixF p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltF f.chamber q

theorem surfaceF_eq (kind : Surface) (f q : Shape) :
    surfaceF kind f q = Low6960SharedPrice.surface kind f q := by
  cases kind <;> simp only [surfaceF, Low6960SharedPrice.surface, mixF_eq, tiltF_eq]

def weightsF (kind : Surface) (f : Shape) : Shape :=
  let b := surfaceF kind f ⟨1,0,0⟩
  let j := surfaceF kind f ⟨1,1,0⟩ - b
  let t := surfaceF kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩

theorem weightsF_eq (kind : Surface) (f : Shape) :
    weightsF kind f = Low6960SharedPrice.weights kind f := by
  simp only [weightsF, Low6960SharedPrice.weights, surfaceF_eq]

def RateFitsF (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weightsF u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))

instance (f : Shape) (u : Rate) : Decidable (RateFitsF f u) := by
  unfold RateFitsF
  infer_instance

theorem rateFitsF_iff (f : Shape) (u : Rate) : RateFitsF f u ↔ Low6960SharedPrice.RateFits f u := by
  simp only [RateFitsF, Low6960SharedPrice.RateFits, weightsF_eq]

def additiveBaseF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixF p q z h + 2*x.t*mixF p p p h
  let pt := mixF p q z p + 2*x.t*mixF p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)

def priceF (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPriceF x l K + u.split*additiveBaseF x l + u.split*u.amount + 1)
    (u.split+1) + Low6960SharedPrice.nonsharedFee x l

theorem priceF_eq (x : Shape) (l K : ℕ) (u : Rate) :
    priceF x l K u = Low6960SharedPrice.price x l K u := by
  simp only [priceF, Low6960SharedPrice.price, Low6960SharedPrice.additiveBase, additiveBaseF,
    physicalPriceF_eq, mixF_eq]

open Low6960WeightedRate (Envelope Fits unit boxFee sepBox first second)

def RayBoundsF (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsF .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

def PaysF (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = Low6960WeightedRate.split ∧ 0 < u.amount ∧
    tiltedFits x ∧ RayBoundsF p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (PaysF p x u) := by
  unfold PaysF Fits RayBoundsF
  infer_instance

def AllowedF (x : Shape) (u : Rate) : Prop :=
  RateFitsF x u ∨ PaysF first x u ∨ PaysF second x u

instance (x : Shape) (u : Rate) : Decidable (AllowedF x u) := by unfold AllowedF; infer_instance

theorem allowedF_iff (x : Shape) (u : Rate) : AllowedF x u ↔ Low6960WeightedRate.Allowed x u := by
  simp only [AllowedF, Low6960WeightedRate.Allowed, PaysF, Low6960WeightedRate.Pays, RayBoundsF,
    Low6960WeightedRate.RayBounds, rateFitsF_iff, weightsF_eq]

/-! Rectangle receipts. -/
open Low6960Allocation (Band MassCell start order allowance)
open Low6960Rectangle (hullOf)

def PaidFourF {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ order cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    chargeF ⟨bh,jh,t⟩ l 32 (fourSurfaceF (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t

instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFourF cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))

theorem paidFourF_iff {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    PaidFourF cells t bl jl bh jh l ↔ Low6960Rectangle.PaidFour cells t bl jl bh jh l := by
  simp only [PaidFourF, Low6960Rectangle.PaidFour, chargeF_eq, fourSurfaceF_eq]

def PaidTiltedF {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    chargeF ⟨B,j,t⟩ l 1920 (tiltF (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t

instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTiltedF cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))

theorem paidTiltedF_iff {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    PaidTiltedF cells t b j B l ↔ Low6960Rectangle.PaidTilted cells t b j B l := by
  simp only [PaidTiltedF, Low6960Rectangle.PaidTilted, chargeF_eq, tiltF_eq]

end Low6960FastPrice
