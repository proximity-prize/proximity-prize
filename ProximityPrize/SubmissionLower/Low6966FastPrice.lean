import ProximityPrize.SubmissionLower.Low6966SurfaceLinearFour
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.Low6966Rectangle

set_option Elab.async false

-- merged module Low6966TiltedRectangle
section Merged_Low6966TiltedRectangle

-- merged module R6960Low6966SurfaceLinearFive
section Merged_R6960Low6966SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low6966SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low6966Prices (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
open Low48BentLattice (Chamber)

open Final50SharedPrice (signedFive signed_five_linear signed_five_nonneg)

/-- The tilted signed surface is linear in the cutter shape. Chamber positivity
also certifies the exact natural-number coefficients in the price ledger. -/
theorem surface_tilted_eq_weights {f : Shape} (hf : Valid f) (ht : tiltedFits f) (q : Shape) :
    surface .tilted f q = (weights .tilted f).b*q.b + (weights .tilted f).j*q.j +
      (weights .tilted f).t*q.t := by
  let p := f.chamber
  let g := bentGraph p
  let l := bentLift (taylorLength-4) p
  let r := bentLift (taylorLength-3) p
  have hb : p.j ≤ p.b := le_max_right _ _
  have hp : Chamber (p,0) := ⟨hb,hf.2.1,Nat.zero_le _⟩
  have hg : Chamber g := Low48BentSupport.graph_chamber hf.1 ht.1
  have hl : Chamber l := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-4)
  have hr : Chamber r := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-3)
  have hnonneg (u : Shape) : 0 ≤ signedFive (p,0) (u,0) g l r :=
    signed_five_nonneg u _ _ _ _ hp hg hl hr
  refine surface_eq_weights_of_signed .tilted f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedFive (p,0) (u,0) g l r).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (hnonneg u)]
  exact signed_five_linear u _ _ _ _

end Low6966SharedPrice

end Merged_R6960Low6966SurfaceLinearFive

-- merged module R6960Low6966WidthAffine
section Merged_R6960Low6966WidthAffine

set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Low6966WidthAffine
open K1_13 (Shape)
open Low6966Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
  bentGraph bentLift taylorLength)
open Final50SharedPrice (signedFive signed_five_nonneg)

private abbrev Slot := BentCap × ℕ
private def atWidth (x : ℕ) (s : Slot) : BentCap :=
  (⟨s.1.1.b+x*s.2,s.1.1.j,s.1.1.t⟩,s.1.2)
private def add (a b : Slot) : Slot := (addBent a.1 b.1,a.2+b.2)
private def zero : Slot := ((⟨0,0,0⟩,0),0)

private theorem at_add (x : ℕ) (a b : Slot) :
    atWidth x (add a b) = addBent (atWidth x a) (atWidth x b) := by
  simp only [atWidth,add,addBent,Shape.plus,Prod.mk.injEq,Shape.mk.injEq,and_true]
  ring

private theorem fold_slots (x : ℕ) (s : List Slot) :
    (s.map (atWidth x)).foldl addBent (⟨0,0,0⟩,0) = atWidth x (s.foldl add zero) := by
  change (s.map (atWidth x)).foldl addBent (atWidth x zero) = _
  rw [List.foldl_map]
  exact List.foldl_hom (atWidth x) (fun a b => (at_add x a b).symm)

private def raw (s : List BentCap) : ℤ :=
  s.sublists.foldl (fun acc boxes =>
    let p := boxes.foldl addBent (⟨0,0,0⟩,0)
    acc + (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2) 0

private theorem integral_affine (B x W J T H : ℤ) :
    bentIntegral (B+x*W) J T H = bentIntegral B J T H + x *
      (bentIntegral (B+W) J T H-bentIntegral B J T H) := by
  simp only [bentIntegral]
  ring

private def integralTerm (boxes : List Slot) (x : ℕ) : ℤ :=
  let p := atWidth x (boxes.foldl add zero)
  (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2

private theorem term_affine (boxes : List Slot) (x : ℕ) :
    integralTerm boxes x = integralTerm boxes 0 + (x : ℤ) *
      (integralTerm boxes 1-integralTerm boxes 0) := by
  simp only [integralTerm, atWidth, Nat.cast_add, Nat.cast_mul, zero_mul, one_mul, add_zero, integral_affine]
  ring

private theorem raw_eq_sum (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = (s.sublists.map (fun a => integralTerm a x)).sum := by
  simp only [raw,List.sublists_map,List.sum_eq_foldl]
  rw [List.foldl_map,List.foldl_map]
  simp only [fold_slots,List.length_map,integralTerm]

private theorem raw_affine (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = raw (s.map (atWidth 0)) + (x : ℤ) *
      (raw (s.map (atWidth 1))-raw (s.map (atWidth 0))) := by
  simp only [raw_eq_sum]
  generalize s.sublists = rows
  induction rows with
  | nil => simp
  | cons boxes rows ih =>
    simp only [List.map_cons,List.sum_cons,term_affine boxes x,ih]
    ring

private def slots (j t : ℕ) (q : Shape) : List Slot :=
  let p : Shape := ⟨j+1,j,t⟩
  [((p,0),1), ((q,0),0), (bentGraph p,1),
    (bentLift (taylorLength-4) p,taylorLength-4),
    (bentLift (taylorLength-3) p,taylorLength-3)]

private theorem map_slots (j t x : ℕ) (q : Shape) :
    (slots j t q).map (atWidth x) =
      let p : Shape := ⟨j+1+x,j,t⟩
      [(p,0),(q,0),bentGraph p,bentLift (taylorLength-4) p,bentLift (taylorLength-3) p] := by
  simp [slots, atWidth, bentGraph, bentLift, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

private theorem raw_nonneg (j t x : ℕ) (q : Shape) (ht : 1≤t) (hj : 3*t+3≤j) :
    0 ≤ raw ((slots j t q).map (atWidth x)) := by
  rw [map_slots]
  let p : Shape := ⟨j+1+x,j,t⟩
  have hb : p.j ≤ p.b := by dsimp [p]; omega
  change 0 ≤ signedFive (p,0) (q,0) (bentGraph p) (bentLift (taylorLength-4) p)
    (bentLift (taylorLength-3) p)
  have hch : 3*p.t≤p.j := by dsimp [p]; omega
  exact signed_five_nonneg _ _ _ _ _ ⟨hb,hch,Nat.zero_le _⟩
    (Low48BentSupport.graph_chamber ht hj)
    (Low48BentSupport.lifted_chamber hb hj (by decide))
    (Low48BentSupport.lifted_chamber hb hj (by decide))

/-- Within one index and top degree, the tilted surface increases with width. -/
theorem tilted_width_mono (q : Shape) {b B j t : ℕ} (hb : j+1≤b) (hB : b≤B)
    (ht : 1≤t) (hj : 3*t+3≤j) :
    tiltedSurface (⟨b,j,t⟩ : Shape).chamber q ≤ tiltedSurface (⟨B,j,t⟩ : Shape).chamber q := by
  let s := slots j t q
  let f (x : ℕ) := raw (s.map (atWidth x))
  have ha (x : ℕ) : f x = f 0 + (x : ℤ) * (f 1-f 0) := raw_affine s x
  have hp (x : ℕ) : 0≤f x := raw_nonneg j t x q ht hj
  have hs : 0≤f 1-f 0 := by
    by_contra! h
    have hle : f 1-f 0 ≤ -1 := by omega
    let wid := (f 0).toNat+1
    have hwid : (wid : ℤ)=f 0+1 := by simp [wid,Int.toNat_of_nonneg (hp 0)]
    have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg wid)
    have hx := hp wid
    rw [ha wid,hwid] at hx
    rw [hwid] at hmul
    simp only [mul_neg,mul_one] at hmul
    omega
  have hr (a : ℕ) (h : j+1≤a) :
      tiltedSurface (⟨a,j,t⟩ : Shape).chamber q = (f (a-(j+1))).toNat := by
    have hmax : max a j = a := max_eq_left (by omega)
    have eq : j+1+(a-(j+1))=a := Nat.add_sub_of_le h
    simp only [f,s,map_slots,eq,tiltedSurface,Shape.chamber,hmax,ambientMix,raw]
  rw [hr _ hb,hr _ (hb.trans hB)]
  apply Int.toNat_le_toNat
  rw [ha (b-(j+1)),ha (B-(j+1))]
  have hw : ((b-(j+1) : ℕ) : ℤ) ≤ ((B-(j+1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hB (j+1)
  exact add_le_add (le_refl (f 0)) (mul_le_mul_of_nonneg_right hw hs)

end Low6966WidthAffine

end Merged_R6960Low6966WidthAffine

-- merged module R6960Low6966TiltedRectangle
section Merged_R6960Low6966TiltedRectangle

set_option Elab.async false
set_option maxRecDepth 2400
namespace Low6966Rectangle
open K1_13 (Shape InBox)
open Low6966RetainedCut (cutPrice contractedPrice)
open Low6966Prices (tiltedSurface tiltedFits)
open Low6966Allocation (Band MassCell start order allowance weight_mono order_mono)

/-- A tilted-surface price certificate for a width interval of one index and degree. -/
def PaidTilted {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t

instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTilted cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))

theorem tilted {k : Band} {cells : List (MassCell k)} {a : Shape} {b j B t l : ℕ}
    (h : PaidTilted cells t b j B l) (hb : b≤a.b) (hB : a.b≤B)
    (hj : a.j=j) (ht : a.t=t) :
    ∃ l, 0<l ∧ l≤order cells a ∧ contractedPrice a (start k) l 178≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨lp,lo,ht',hj',hw,fee⟩ := h
  cases a with
  | mk a d z =>
    change d=j at hj
    change z=t at ht
    subst d z
    have geom : tiltedFits ⟨a,j,t⟩ := ⟨hj',hw.trans hb⟩
    have hprice : contractedPrice ⟨a,j,t⟩ (start k) l 178 ≤
        cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) := by
      unfold contractedPrice
      dsimp only
      rw [ite_eq_left geom]
      exact min_le_right _ _
    have ha : 3*t≤j := by omega
    have mono := Low6966WidthAffine.tilted_width_mono (hullOf k l) (hw.trans hb) hB ht' hj'
    have hcut : cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) ≤
        cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) := by
      have box : InBox ⟨a,j,t⟩ ⟨B,j,t⟩ := ⟨hB,le_rfl,le_rfl⟩
      rw [cut_eq,cut_eq]
      exact charge_mono box ha ha l 1920 mono
    exact ⟨l,lp,lo.trans (order_mono cells hb le_rfl), hprice.trans
      (hcut.trans (fee.trans (Nat.div_le_div_right
        (Nat.mul_le_mul_left _ (weight_mono k hb le_rfl le_rfl)))))⟩

end Low6966Rectangle

end Merged_R6960Low6966TiltedRectangle

end Merged_Low6966TiltedRectangle

-- merged module Low6966FastPrice
section Merged_Low6966FastPrice

-- merged module R6960Low6966WeightedRate
section Merged_R6960Low6966WeightedRate

set_option Elab.async false

namespace Low6966WeightedRate
open K1_13 (Shape)
open Low6966SharedPrice (Rate weights)

abbrev unit : ℕ := 1000000000
abbrev split : ℕ := 10

def boxFee (w x : Shape) : ℕ := w.b * max x.b x.j + w.j * x.j + w.t * min x.t (x.j / 3)
def sepBox (x : Shape) : Shape := ⟨x.b - 1, x.j - 3, x.t - 1⟩
def charge (r a d e : ℕ) : ℕ := e * (24 * (r - e*a) + d * (e - 1))

structure Envelope where
  widthLow : ℕ
  indexLow : ℕ
  topLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
  taperLow : ℕ
  taperHigh : ℕ
  coeff : Shape
  sep : ℕ

def Fits (p : Envelope) (x : Shape) : Prop :=
  p.widthLow ≤ x.b ∧ x.b ≤ p.widthHigh ∧ p.indexLow ≤ x.j ∧ x.j ≤ p.indexHigh ∧
    p.topLow ≤ x.t ∧ p.taperLow ≤ 26*x.b ∧ min (26*x.b+25*x.j) (x.b+25*178) ≤ p.taperHigh

def RayBounds (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weights .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

def Pays (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = split ∧ 0 < u.amount ∧ Low6966Prices.tiltedFits x ∧
    RayBounds p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (Pays p x u) := by
  unfold Pays Fits RayBounds
  infer_instance

def first : Envelope := ⟨106,48,4,132,53,2756,4257,⟨4886433,26118015,6676780⟩,1966580209⟩

def Allowed (x : Shape) (u : Rate) : Prop :=
  Low6966SharedPrice.RateFits x u

instance (x : Shape) (u : Rate) : Decidable (Allowed x u) := by unfold Allowed; infer_instance

private theorem ray_expansion (w : Shape) (b j t : ℕ) (hb : j ≤ b) (ht : 3*t ≤ j) :
    w.b*b+w.j*j+w.t*t = w.b*(b-j)+(w.b+w.j)*(j-3*t)+(3*(w.b+w.j)+w.t)*t := by
  let B := b-j
  let J := j-3*t
  change w.b*b+w.j*j+w.t*t = w.b*B+(w.b+w.j)*J+(3*(w.b+w.j)+w.t)*t
  have hB : b = B+J+3*t := by dsimp [B,J]; omega
  have hJ : j = J+3*t := by dsimp [J]; omega
  rw [hB, hJ]
  ring

theorem fee_le {p : Envelope} {x : Shape} {amount : ℕ} (h : RayBounds p x amount) (y : Shape) :
    unit * boxFee (weights .tilted x) y ≤ (1920 * amount) * boxFee p.coeff y := by
  let b := max y.b y.j
  let j := y.j
  let t := min y.t (y.j/3)
  let w := weights .tilted x
  have hb : j ≤ b := le_max_right _ _
  have ht : 3*t ≤ j := by
    have hd : t ≤ y.j/3 := min_le_right _ _
    dsimp only [j]
    omega
  change unit*(w.b*b+w.j*j+w.t*t) ≤ (1920*amount)*(p.coeff.b*b+p.coeff.j*j+p.coeff.t*t)
  rw [ray_expansion w b j t hb ht, ray_expansion p.coeff b j t hb ht]
  calc
    _ = (unit*w.b)*(b-j) + (unit*(w.b+w.j))*(j-3*t) + (unit*(3*(w.b+w.j)+w.t))*t := by ring
    _ ≤ _ := by
      rw [show (1920*amount)*(p.coeff.b*(b-j)+(p.coeff.b+p.coeff.j)*(j-3*t)+
          (3*(p.coeff.b+p.coeff.j)+p.coeff.t)*t) =
          ((1920*amount)*p.coeff.b)*(b-j) + ((1920*amount)*(p.coeff.b+p.coeff.j))*(j-3*t) +
          ((1920*amount)*(3*(p.coeff.b+p.coeff.j)+p.coeff.t))*t by ring]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (Nat.mul_le_mul_right _ h.2.1))
        (Nat.mul_le_mul_right _ h.2.2.1)

theorem transfer {p : Envelope} {x : Shape} {u : Rate} (h : Pays p x u) (y : Shape) (r a d e : ℕ)
    (hp : (split+1-e)*(24*boxFee p.coeff y+d*p.sep) ≤ split*unit*charge r a d e) :
    (u.split+1-e)*(24*boxFee (weights u.kind x) y+d*boxFee (weights u.kind x) (sepBox x)) ≤
      (Low6966SharedPrice.surfaceScale u.kind*(u.split*u.amount))*charge r a d e := by
  obtain ⟨_, hk, hs, _, _, hw⟩ := h
  rw [hk, hs]
  let w := weights .tilted x
  let z := 24*boxFee w y+d*boxFee w (sepBox x)
  let cap := 1920*u.amount
  let bound := 24*boxFee p.coeff y+d*p.sep
  have hz : unit*z ≤ cap*bound := by
    calc
      _ = 24*(unit*boxFee w y)+d*(unit*boxFee w (sepBox x)) := by dsimp [z]; ring
      _ ≤ 24*(cap*boxFee p.coeff y)+d*(cap*p.sep) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (fee_le hw y)) (Nat.mul_le_mul_left _ hw.2.2.2)
      _ = _ := by dsimp [bound]; ring
  change (split+1-e)*z ≤ (1920*(split*u.amount))*charge r a d e
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < unit)
  calc
    unit*((split+1-e)*z) = (split+1-e)*(unit*z) := by ring
    _ ≤ (split+1-e)*(cap*bound) := Nat.mul_le_mul_left _ hz
    _ = cap*((split+1-e)*bound) := by ring
    _ ≤ cap*(split*unit*charge r a d e) := Nat.mul_le_mul_left _ hp
    _ = _ := by dsimp [cap]; ring

end Low6966WeightedRate

end Merged_R6960Low6966WeightedRate

-- merged module R6960Low6966FastPrice
section Merged_R6960Low6966FastPrice
set_option autoImplicit false
set_option Elab.async false
namespace Low6966FastPrice
open K1_13 (Shape mixed32 volume32 difference chart liftedChart ceilDiv)
open Low6966Prices (BentCap bentIntegral addBent ambientMix tiltedSurface bentGraph bentLift
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
def tiltF (p q : Shape) : ℕ :=
  ambientMixF [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]
theorem tiltF_eq (p q : Shape) : tiltF p q = tiltedSurface p q := by
  unfold tiltF tiltedSurface
  rw [ambientMix_eq]
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
    chargeF x l scale S = Low6966RetainedCut.cutPrice x l scale S := by
  rw [Low6966Rectangle.cut_eq]
  simp only [chargeF, Low6966Rectangle.charge, mixF_eq]
def fourSurfaceF (p q : Shape) : ℕ :=
  mixF p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)
theorem fourSurfaceF_eq (p q : Shape) : fourSurfaceF p q = Low6966RetainedCut.fourSurface p q := by
  simp only [fourSurfaceF, Low6966RetainedCut.fourSurface, mixF_eq]
def contractedPriceF (x h : Shape) (l active : ℕ) : ℕ :=
  let q := Low6966RetainedCut.chamberHull (Low6966RetainedCut.residualBox h l)
  let old := physicalPriceF x l active
  let four := if 0 < q.t then min old (chargeF x l 32 (fourSurfaceF x.chamber q)) else old
  if tiltedFits x then min four (chargeF x l (60*32) (tiltF x.chamber q)) else four
theorem contractedPriceF_eq (x h : Shape) (l active : ℕ) :
    contractedPriceF x h l active = Low6966RetainedCut.contractedPrice x h l active := by
  simp only [contractedPriceF, Low6966RetainedCut.contractedPrice, physicalPriceF_eq, chargeF_eq,
    fourSurfaceF_eq, tiltF_eq]
open Low6966SharedPrice (Surface Rate surfaceScale coord expression deficit slope)
def surfaceF (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixF p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltF f.chamber q
theorem surfaceF_eq (kind : Surface) (f q : Shape) :
    surfaceF kind f q = Low6966SharedPrice.surface kind f q := by
  cases kind <;> simp only [surfaceF, Low6966SharedPrice.surface, mixF_eq, tiltF_eq]
def weightsF (kind : Surface) (f : Shape) : Shape :=
  let b := surfaceF kind f ⟨1,0,0⟩
  let j := surfaceF kind f ⟨1,1,0⟩ - b
  let t := surfaceF kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
theorem weightsF_eq (kind : Surface) (f : Shape) :
    weightsF kind f = Low6966SharedPrice.weights kind f := by
  simp only [weightsF, Low6966SharedPrice.weights, surfaceF_eq]
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
theorem rateFitsF_iff (f : Shape) (u : Rate) : RateFitsF f u ↔ Low6966SharedPrice.RateFits f u := by
  simp only [RateFitsF, Low6966SharedPrice.RateFits, weightsF_eq]
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
    (u.split+1) + Low6966SharedPrice.nonsharedFee x l
theorem priceF_eq (x : Shape) (l K : ℕ) (u : Rate) :
    priceF x l K u = Low6966SharedPrice.price x l K u := by
  simp only [priceF, Low6966SharedPrice.price, Low6966SharedPrice.additiveBase, additiveBaseF,
    physicalPriceF_eq, mixF_eq]
open Low6966WeightedRate (Envelope Fits unit boxFee sepBox first)
def RayBoundsF (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsF .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep
def PaysF (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = Low6966WeightedRate.split ∧ 0 < u.amount ∧
    tiltedFits x ∧ RayBoundsF p x u.amount
instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (PaysF p x u) := by
  unfold PaysF Fits RayBoundsF
  infer_instance
def AllowedF (x : Shape) (u : Rate) : Prop :=
  RateFitsF x u
instance (x : Shape) (u : Rate) : Decidable (AllowedF x u) := by unfold AllowedF; infer_instance
theorem allowedF_iff (x : Shape) (u : Rate) : AllowedF x u ↔ Low6966WeightedRate.Allowed x u := by
  simp only [AllowedF, Low6966WeightedRate.Allowed, rateFitsF_iff]
open Low6966Allocation (Band MassCell start order allowance)
open Low6966Rectangle (hullOf)
def PaidFourF {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ order cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    chargeF ⟨bh,jh,t⟩ l 32 (fourSurfaceF (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t
instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFourF cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidFourF_iff {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    PaidFourF cells t bl jl bh jh l ↔ Low6966Rectangle.PaidFour cells t bl jl bh jh l := by
  simp only [PaidFourF, Low6966Rectangle.PaidFour, chargeF_eq, fourSurfaceF_eq]
def PaidTiltedF {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    chargeF ⟨B,j,t⟩ l 1920 (tiltF (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t
instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTiltedF cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidTiltedF_iff {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    PaidTiltedF cells t b j B l ↔ Low6966Rectangle.PaidTilted cells t b j B l := by
  simp only [PaidTiltedF, Low6966Rectangle.PaidTilted, chargeF_eq, tiltF_eq]
end Low6966FastPrice

end Merged_R6960Low6966FastPrice

end Merged_Low6966FastPrice
