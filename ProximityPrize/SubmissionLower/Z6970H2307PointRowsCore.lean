import ProximityPrize.SubmissionLower.Z6970H2307PointOrderBuckets
import ProximityPrize.SubmissionLower.Z6970H2307PointPrices
import ProximityPrize.SubmissionLower.Z6970H2307PointAPI
import ProximityPrize.SubmissionLower.Z6970H2307OrderLookup
import ProximityPrize.SubmissionLower.Z6970CompanionBook

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Height2307PointRowsCore
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open K1_13_8_2 (Chamber mixed_mono)
open Height2307Bands
open Height2307Allocation (PointTable Quote residual)
open Height2307PointFastPrice
open Low6969RetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Low6969Prices (physicalPrice physicalPriceOld tiltedSurface tiltedFits)
open Low6969Monotone (box_refl normalize_mono normalize_chamber chart_mono chart_chamber)

abbrev order (k : Band) (x : Shape) := Height2307Orders.order k x.b x.j
abbrev book (k : Band) (x : Shape) := Height2307Companion.book k.val x
structure Gates where
  price : Shape → ℕ
  fits : ℕ → Shape → Prop
  choose : DecidableRel fits

variable (g : Gates)
local instance (k : ℕ) (x : Shape) : Decidable (g.fits k x) := g.choose k x

private theorem one_le_lookup (b j : ℕ) (ps : List Height2307Orders.Threshold) :
    1 ≤ Height2307Orders.lookup b j ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih => exact ih.trans (le_max_right _ _)

theorem lookup_mono {b B j : ℕ} (h : b ≤ B) (ps : List Height2307Orders.Threshold) :
    Height2307Orders.lookup b j ps ≤ Height2307Orders.lookup B j ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih =>
    simp only [Height2307Orders.lookup]
    by_cases h₁ : p.b ≤ b ∧ p.j ≤ j
    · have h₂ : p.b≤B ∧ p.j≤j := ⟨h₁.1.trans h,h₁.2⟩
      rw [if_pos h₁,if_pos h₂]
      exact max_le_max le_rfl ih
    · rw [if_neg h₁]
      exact max_le ((one_le_lookup B j ps).trans (le_max_right _ _)) (ih.trans (le_max_right _ _))

inductive Method
  | old | four | tilt | direct | shared (rate : Low6969SharedPrice.Rate) | gate

structure Tile where
  lo : ℕ
  hi : ℕ
  m : ℕ
  how : Method
  debt : Option ℕ := none
  bucket : ℕ := 0

abbrev hull (k : Band) (m : ℕ) := chamberHull (residualBox (start k) m)

def fee (k : Band) (j t : ℕ) (r : Tile) : ℕ :=
  let y : Shape := ⟨r.hi,j,t⟩
  match r.how with
  | .old => physicalPriceOldF y r.m
  | .four => chargeF y r.m 32 (fourSurfaceF y.chamber (hull k r.m))
  | .tilt => chargeF y r.m 1920 (tiltF y.chamber (hull k r.m))
  | .direct => contractedPriceF y (start k) r.m 179
  | .shared u => priceF y r.m 179 u
  | .gate => additiveBaseF y r.m + Low6969SharedThirdCut.preciseFee y r.m + g.price y

def geom (k : Band) (j t : ℕ) (r : Tile) : Prop :=
  match r.how with
  | .old => True
  | .four => 0 < (hull k r.m).t
  | .tilt => tiltedFits ⟨r.lo,j,t⟩
  | .direct => r.lo = r.hi
  | .shared u => r.lo = r.hi ∧ RateFitsF ⟨r.hi,j,t⟩ u
  | .gate => r.lo = r.hi ∧ g.fits k.val ⟨r.hi,j,t⟩

instance (k : Band) (j t : ℕ) (r : Tile) : Decidable (geom g k j t r) := by
  cases r with
  | mk lo hi m how debt bucket =>
    cases how <;> unfold geom <;> infer_instance

def room (k : Band) (j t : ℕ) (r : Tile) : Prop :=
  match r.debt with
  | none => fee g k j t r ≤ allowance k ((start k).t+t) r.lo j t
  | some d => r.lo = r.hi ∧ book k (residual k ⟨r.hi,j,t⟩) = some d ∧
      fee g k j t r + d + reserve k + Low6969Prices.lowerCap ((start k).t+t) ≤ budget

instance (k : Band) (j t : ℕ) (r : Tile) : Decidable (room g k j t r) := by
  cases r with
  | mk lo hi m how debt bucket =>
    cases debt <;> unfold room <;> infer_instance

private def bucketTest (k : Band) (i : ℕ) (f : Height2307Orders.Threshold → Bool) : Bool :=
  match (Height2307PointOrder.buckets k.val)[i]? with
  | some ps => ps.any f
  | none => false

private def checkOrder (k : Band) (i b j m : ℕ) : Bool :=
  decide (m ≤ 1) || bucketTest k i (fun p => decide (m ≤ p.m ∧ p.b ≤ b ∧ p.j ≤ j))

private theorem bound_of_mem {b j m : ℕ} {p : Height2307Orders.Threshold}
    (hm : m ≤ p.m) (hb : p.b ≤ b) (hj : p.j ≤ j)
    (ps : List Height2307Orders.Threshold) (hp : p ∈ ps) :
    m ≤ Height2307Orders.lookup b j ps := by
  induction ps with
  | nil => simp at hp
  | cons q rest ih =>
    rcases List.mem_cons.mp hp with rfl | hrest
    · simp only [Height2307Orders.lookup, if_pos (show p.b ≤ b ∧ p.j ≤ j from ⟨hb,hj⟩)]
      exact hm.trans (le_max_left _ _)
    · exact (ih hrest).trans (le_max_right _ _)

private theorem checkOrder_sound (k : Band) (i b j m : ℕ)
    (h : checkOrder k i b j m = true) : m ≤ Height2307Orders.lookup b j (Height2307Orders.thresholds k) := by
  unfold checkOrder at h
  rcases Bool.or_eq_true_iff.mp h with h₁ | h₂
  · exact (of_decide_eq_true h₁).trans (one_le_lookup b j _)
  · unfold bucketTest at h₂
    split at h₂
    next ps he =>
      obtain ⟨p,hp,hq⟩ := List.any_eq_true.mp h₂
      obtain ⟨hm,hb,hj⟩ : m ≤ p.m ∧ p.b ≤ b ∧ p.j ≤ j := of_decide_eq_true hq
      exact bound_of_mem hm hb hj _ (Height2307PointOrder.mem_of_bucket he hp)
    next => simp at h₂

def paid (k : Band) (j t : ℕ) (r : Tile) : Bool :=
  (decide (0 < r.m) && checkOrder k r.bucket r.lo j r.m) &&
    decide (geom g k j t r ∧ room g k j t r)

private theorem contracted_old (x h : Shape) (m : ℕ) :
    contractedPrice x h m 179 ≤ physicalPriceOld x m := by
  apply le_trans _ (Low6969Monotone.physicalPrice_le_old x m 179)
  unfold contractedPrice
  dsimp only
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl

private theorem quote_of_geom (k : Band) (j t b : ℕ) (r : Tile)
    (ht : 0<t) (hj : 3*t≤j) (hlo : r.lo ≤ b) (hhi : b ≤ r.hi)
    (h : geom g k j t r) : Quote g.price g.fits k ⟨b,j,t⟩ r.m (fee g k j t r) := by
  obtain ⟨lo,hi,m,how,debt⟩ := r
  dsimp at hlo hhi
  let x : Shape := ⟨b,j,t⟩
  let y : Shape := ⟨hi,j,t⟩
  have hbox : InBox x y := ⟨hhi,le_rfl,le_rfl⟩
  cases how with
  | old =>
    left
    simp only [fee, physicalPriceOldF_eq]
    exact (contracted_old x (start k) m).trans (Low6969Monotone.physical_mono hbox hj hj m)
  | four =>
    left
    have hq : 0 < (hull k m).t := h
    have hqc : Chamber (hull k m) := by
      have r := hull_valid (residualBox (start k) m)
      exact ⟨r.1,r.2.1⟩
    have hp := normalize_mono hbox
    have hpc : Chamber y.chamber := normalize_chamber y hj
    have hsurf : fourSurface x.chamber (hull k m) ≤ fourSurface y.chamber (hull k m) :=
      mixed_mono hp (box_refl _) (chart_mono _ hp) (chart_mono _ hp) hpc hqc
        (chart_chamber _ _) hqc (chart_chamber _ _) (chart_chamber _ _)
    have hc : contractedPrice x (start k) m 179 ≤ cutPrice x m 32 (fourSurface x.chamber (hull k m)) := by
      unfold contractedPrice
      dsimp only
      rw [if_pos hq]
      split
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact min_le_right _ _
    simp only [fee, fourSurfaceF_eq, chargeF_eq]
    exact hc.trans (by
      rw [Height2307PointRectangle.cut_eq, Height2307PointRectangle.cut_eq]
      exact Height2307PointRectangle.charge_mono hbox hj hj m 32 hsurf)
  | tilt =>
    left
    obtain ⟨hj',hb'⟩ : 3*t+3≤j ∧ j+1≤lo := h
    have hx : tiltedFits x := ⟨hj',hb'.trans hlo⟩
    have hc : contractedPrice x (start k) m 179 ≤ cutPrice x m 1920 (tiltedSurface x.chamber (hull k m)) := by
      unfold contractedPrice
      dsimp only
      rw [if_pos hx]
      exact min_le_right _ _
    simp only [fee, tiltF_eq, chargeF_eq]
    exact hc.trans (by
      rw [Height2307PointRectangle.cut_eq, Height2307PointRectangle.cut_eq]
      exact Height2307PointRectangle.charge_mono hbox hj hj m 1920
        (Height2307PointWidthAffine.tilted_width_mono _ (hb'.trans hlo) hhi ht hj'))
  | direct =>
    have eq : b = hi := by have : lo = hi := h; omega
    subst b
    exact Or.inl (by simp only [fee,contractedPriceF_eq,le_refl])
  | shared u =>
    obtain ⟨e,fit⟩ : lo = hi ∧ RateFitsF y u := h
    have eq : b=hi := by omega
    subst b
    exact Or.inr (Or.inl ⟨u,(rateFitsF_iff y u).mp fit,by simp only [fee,priceF_eq,le_refl]⟩)
  | gate =>
    obtain ⟨e,gate⟩ : lo = hi ∧ g.fits k.val y := h
    have eq : b=hi := by omega
    subst b
    exact Or.inr (Or.inr ⟨gate,by simp only [fee,additiveBaseF_eq,Height2307Count6970.gatePrice,le_refl]⟩)

def Point (k : Band) (x : Shape) : Prop :=
    ∃ m amount, 0<m ∧ m≤order k x ∧ Quote g.price g.fits k x m amount ∧
      (amount ≤ allowance k ((start k).t+x.t) x.b x.j x.t ∨
        ∃ d, book k (residual k x) = some d ∧
          amount+d+reserve k+Low6969Prices.lowerCap ((start k).t+x.t)≤budget)

theorem tile_point (k : Band) (j t b : ℕ) (r : Tile)
    (ht : 0<t) (hj : 3*t≤j) (hlo : r.lo ≤ b) (hhi : b ≤ r.hi)
    (h : paid g k j t r = true) : Point g k ⟨b,j,t⟩ := by
  obtain ⟨checks, hroom⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hpos, hord⟩ := Bool.and_eq_true_iff.mp checks
  have pos : 0 < r.m := of_decide_eq_true hpos
  have ord := checkOrder_sound _ _ _ _ _ hord
  obtain ⟨geo,money⟩ : geom g k j t r ∧ room g k j t r := of_decide_eq_true hroom
  refine ⟨r.m,fee g k j t r,pos,?_,quote_of_geom g k j t b r ht hj hlo hhi geo,?_⟩
  · exact ord.trans (lookup_mono hlo (Height2307Orders.thresholds k))
  · cases hd : r.debt with
    | none =>
      left
      have hfee : fee g k j t r ≤ allowance k ((start k).t+t) r.lo j t := by simpa only [room,hd] using money
      exact hfee.trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hlo le_rfl le_rfl)))
    | some d =>
      obtain ⟨eq,booked,bill⟩ : r.lo=r.hi ∧ book k (residual k ⟨r.hi,j,t⟩)=some d ∧
          fee g k j t r+d+reserve k+Low6969Prices.lowerCap ((start k).t+t)≤budget := by
        simpa only [room,hd] using money
      have hb : b=r.hi := by omega
      subst b
      exact Or.inr ⟨d,booked,bill⟩

def covers (upper : ℕ) (next : ℕ) : List Tile → Bool
  | [] => decide (upper<next)
  | r::tail => decide (r.lo=next ∧ next≤r.hi) && covers upper (r.hi+1) tail

theorem pick {upper next b : ℕ} {rs : List Tile}
    (h : covers upper next rs = true) (lo : next≤b) (hi : b≤upper) :
    ∃ r ∈ rs, r.lo≤b ∧ b≤r.hi := by
  induction rs generalizing next with
  | nil =>
    have : upper<next := of_decide_eq_true h
    omega
  | cons r tail ih =>
    simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hr : b≤r.hi
    · exact ⟨r,List.mem_cons_self, by simpa only [h.1.1] using lo,hr⟩
    · obtain ⟨r',mem,hlo,hhi⟩ := ih h.2 (by omega)
      exact ⟨r',List.mem_cons_of_mem _ mem,hlo,hhi⟩

def beginWidth (j t : ℕ) : ℕ := max 1 ((j-t+1)/2)
def endWidth (k : Band) : ℕ := 143-(start k).b

structure Row (k : Band) where
  t : ℕ
  j : ℕ
  tiles : List Tile
  cover : covers (endWidth k) (beginWidth j t) tiles = true
  pay : tiles.all (paid g k j t) = true

def key {k : Band} (r : Row g k) : ℕ × ℕ := (r.t,r.j)

def keys (k : Band) : List (ℕ × ℕ) :=
  ((List.range (16-(start k).t)).map (·+1)).flatMap fun t =>
    ((List.range (61-(start k).j-3*t)).map (·+3*t)).map fun j => (t,j)

theorem of_rows {k : Band} (rs : List (Row g k)) (rowKeys : rs.map (key g) = keys k)
    (x : Shape) (hv : Valid x) (strong : x.j≤2*x.b+x.t)
    (fit : InBox ((start k).plus x) (Low6969Prices.fullCap 16)) : Point g k x := by
  obtain ⟨b,j,t⟩ := x
  change (start k).b+b≤143 ∧ (start k).j+j≤60 ∧ (start k).t+t≤16 at fit
  change 0<t ∧ 3*t≤j ∧ j≤3*b at hv
  change j≤2*b+t at strong
  have present : (t,j) ∈ keys k := by
    apply List.mem_flatMap.mpr
    refine ⟨t,?_,?_⟩
    · apply List.mem_map.mpr
      exact ⟨t-1,List.mem_range.mpr (by omega),by omega⟩
    · apply List.mem_map.mpr
      refine ⟨j,List.mem_map.mpr ⟨j-3*t,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  have mem : (t,j) ∈ rs.map (key g) := by rw [rowKeys]; exact present
  obtain ⟨row,hr,he⟩ := List.mem_map.mp mem
  have ht : row.t=t := congrArg Prod.fst he
  have hj : row.j=j := congrArg Prod.snd he
  have lb : beginWidth row.j row.t ≤ b := by unfold beginWidth; rw [ht,hj]; omega
  have ub : b≤endWidth k := by unfold endWidth; omega
  obtain ⟨r,inside,hlo,hhi⟩ := pick row.cover lb ub
  have good := (List.all_eq_true.mp row.pay) r inside
  rw [ht,hj] at good
  exact tile_point g k j t b r hv.1 hv.2.1 hlo hhi good

end Height2307PointRowsCore
