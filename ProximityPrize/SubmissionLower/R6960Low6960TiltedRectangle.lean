import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

-- merged module R6960Low6960SurfaceLinearFive
section Merged_R6960Low6960SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low6960SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low6960Prices (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
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

#print axioms surface_tilted_eq_weights
end Low6960SharedPrice

end Merged_R6960Low6960SurfaceLinearFive

-- merged module R6960Low6960WidthAffine
section Merged_R6960Low6960WidthAffine

set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Low6960WidthAffine
open K1_13 (Shape)
open Low6960Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
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

#print axioms tilted_width_mono
end Low6960WidthAffine

end Merged_R6960Low6960WidthAffine

-- merged module R6960Low6960TiltedRectangle
section Merged_R6960Low6960TiltedRectangle

set_option Elab.async false
set_option maxRecDepth 2400
namespace Low6960Rectangle
open K1_13 (Shape InBox)
open Low6960RetainedCut (cutPrice contractedPrice)
open Low6960Prices (tiltedSurface tiltedFits)
open Low6960Allocation (Band MassCell start order allowance weight_mono order_mono)

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
    ∃ l, 0<l ∧ l≤order cells a ∧ contractedPrice a (start k) l 171≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨lp,lo,ht',hj',hw,fee⟩ := h
  cases a with
  | mk a d z =>
    change d=j at hj
    change z=t at ht
    subst d z
    have geom : tiltedFits ⟨a,j,t⟩ := ⟨hj',hw.trans hb⟩
    have hprice : contractedPrice ⟨a,j,t⟩ (start k) l 171 ≤
        cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) := by
      unfold contractedPrice
      dsimp only
      rw [ite_eq_left geom]
      exact min_le_right _ _
    have ha : 3*t≤j := by omega
    have mono := Low6960WidthAffine.tilted_width_mono (hullOf k l) (hw.trans hb) hB ht' hj'
    have hcut : cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) ≤
        cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) := by
      have box : InBox ⟨a,j,t⟩ ⟨B,j,t⟩ := ⟨hB,le_rfl,le_rfl⟩
      rw [cut_eq,cut_eq]
      exact charge_mono box ha ha l 1920 mono
    exact ⟨l,lp,lo.trans (order_mono cells hb le_rfl), hprice.trans
      (hcut.trans (fee.trans (Nat.div_le_div_right
        (Nat.mul_le_mul_left _ (weight_mono k hb le_rfl le_rfl)))))⟩

#print axioms tilted
end Low6960Rectangle

end Merged_R6960Low6960TiltedRectangle
