import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight
import ProximityPrize.SubmissionLower.Low6966Monotone
import ProximityPrize.SubmissionLower.Low6966AllocWeight

set_option Elab.async false

namespace Low6966MassCheck
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open P3_6_8_1 (sumBelow sumBelow_eq sumBelow_add)
theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]
def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs
theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]
end Low6966MassCheck

-- merged module R6960Low6966AllocCore
section Merged_R6960Low6966AllocCore

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Low6966Allocation
open Finset
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape Valid)
open K1_13_8_2 (Threshold orderFor)
open Final50PriceLayer (availableMass fastLayer layerTerm)
open LowProfile6966 (lowDegreeCap)
open Low6966Retained (Box)
open LowProfile6966 (retainedTariff need layerCount)
open LowProfile6966 (degree_bound)
open Low6966MassCheck (check check_sum mass_eq)
open P3_6_8_1 (sumBelow)
open scoped BigOperators Classical

abbrev Band := Fin 34
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData := [
  ⟨0,0,0,0,0⟩,
  ⟨1,1,3,1,2180145243737111⟩,
  ⟨2,2,3,1,2180145243737111⟩,
  ⟨3,3,3,1,2180145243737111⟩,
  ⟨4,4,3,1,2527419063424987⟩,
  ⟨5,5,3,1,2881989181439343⟩,
  ⟨6,6,3,1,3245991096996299⟩,
  ⟨7,7,3,1,3621560309311975⟩,
  ⟨8,8,3,1,4010832317602491⟩,
  ⟨9,9,3,1,4415942621083967⟩,
  ⟨2,2,4,1,5135941333542032⟩,
  ⟨3,3,4,1,5135941333542032⟩,
  ⟨5,13,4,1,13423058699228333⟩,
  ⟨10,20,3,1,10528236217793880⟩,
  ⟨21,27,3,1,16850745667781492⟩,
  ⟨4,4,4,1,5135941333542032⟩,
  ⟨14,25,4,1,28082611121591081⟩,
  ⟨2,16,5,1,29617180082871112⟩,
  ⟨17,22,5,1,41297504443524748⟩,
  ⟨2,19,6,1,50539755336257608⟩,
  ⟨2,7,6,2,70626525673119693⟩,
  ⟨8,10,6,2,97140447466977594⟩,
  ⟨11,12,6,2,115202587969913548⟩,
  ⟨13,16,6,2,152561261641411104⟩,
  ⟨17,19,6,2,181929449515114711⟩,
  ⟨3,14,7,1,50745124296892782⟩,
  ⟨3,5,7,2,111825826368409560⟩,
  ⟨6,8,7,2,125038314751504987⟩,
  ⟨9,11,7,2,165087956014435947⟩,
  ⟨12,13,7,2,192216622042413940⟩,
  ⟨14,14,7,2,205935254139606143⟩,
  ⟨3,6,8,1,42199582081660885⟩,
  ⟨3,3,8,2,178054598401464895⟩,
  ⟨4,6,8,2,178054598401464949⟩]

def band (k : Band) : BandData := bands.get ⟨k.val,k.isLt⟩

def start (k : Band) : Shape := ⟨(band k).lo,(band k).index,(band k).top⟩

def endWidth (k : Band) : ℕ := (band k).hi

def reserve (k : Band) : ℕ := (band k).charge

def Admits (k : Band) (r : Shape) : Prop :=
  (start k).b≤r.b ∧ r.b≤endWidth k ∧ r.j=(start k).j ∧ r.t=(start k).t

instance (k : Band) (r : Shape) : Decidable (Admits k r) := by unfold Admits; infer_instance

theorem start_flat (k : Band) : start k=zeroShape ∨ 0<(start k).j := by
  fin_cases k <;> decide +kernel

theorem empty_admits : Admits empty zeroShape := by decide +kernel

theorem admits_floor {k : Band} {r : Shape} (hr : Admits k r) : InBox (start k) r :=
  ⟨hr.1,hr.2.2.1.symm.le,hr.2.2.2.symm.le⟩

private theorem checked_cover (b : Fin 28) :
    ∀ (j : Fin 9) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      b.val≤lowDegreeCap j.val → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<28 := Nat.lt_succ_of_le box.1
  have hj : j<9 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 (degree_bound v box)

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 28,(start k).b≤b.val → b.val≤endWidth k →
      retainedTariff b.val (start k).j (start k).t≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    retainedTariff r.b r.j r.t≤reserve k := by
  have hm : endWidth k<28 := by fin_cases k <;> decide +kernel
  rw [hr.2.2.1,hr.2.2.2]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 274790602290396470

def factorCap (top : ℕ) : ℕ := budget-Low6966Prices.lowerCap top

def tiered (k : Band) : Bool := k.val == 1 || k.val == 32

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6966AllocWeight.weight b j t else if tiered k then Research6966.LowTierWeight.weight (58-(start k).j) j else j

def pricingDenom (k : Band) : ℕ := if k=empty then 374 else if tiered k then 5*(58-(start k).j) else 58-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤15) (k : Band) : reserve k≤factorCap top := by
  interval_cases top <;> fin_cases k <;> decide +kernel

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using Low6966AllocWeight.mono hb hj ht
  · by_cases t : tiered k
    · simpa [pricingWeight,h,t] using Research6966.LowTierWeight.mono (58-(start k).j) hj
    · simpa [pricingWeight,h,t] using hj

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤15) :
    allowance k a w j t≤allowance k b w j t := by
  have pos : factorCap a≤factorCap b := by
    have ha := h.trans hb
    interval_cases a <;> interval_cases b <;> decide +kernel
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right pos _))

def MassCell (k : Band) :=
  {q : Threshold // 0<q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1)<need}

theorem mass_cell (k : Band) (b j l N : ℕ) (hj : 0<j)
    (hN : (l-1)+1650/((start k).j+j)=N) (vals : List ℕ)
    (worked : check (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals=true)
    (small : vals.sum<need) :
    0<(⟨b,j,l⟩ : Threshold).j ∧
      availableMass (start k) ⟨b,j,0⟩ (l-1)<need := by
  refine ⟨hj,?_⟩
  rw [mass_eq _ _ _ (start_flat k) (by change 0<(start k).j+j; omega),hN]
  have sum := check_sum (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals worked
  have eq : P3_6_8_1.sumBelow (fastLayer (start k) ⟨b,j,0⟩ (l-1)) N=vals.sum := by
    simpa only [Nat.zero_add,P3_6_8_1.sumBelow] using sum
  rwa [eq]

def order {k : Band} (cells : List (MassCell k)) (x : Shape) : ℕ :=
  orderFor x.b x.j (cells.map Subtype.val)

theorem order_pos {k : Band} (cells : List (MassCell k)) (x : Shape) : 0<order cells x :=
  (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).1

theorem order_mono {k : Band} (cells : List (MassCell k)) {x y : Shape}
    (hb : x.b≤y.b) (hj : x.j≤y.j) : order cells x≤order cells y :=
  P0_9_8.orderFor_mono hb hj _

theorem order_valid {k : Band} (cells : List (MassCell k)) (x : Shape) : order cells x=1 ∨
    availableMass (start k) x (order cells x-1)<need := by
  rcases (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).2 with h | ⟨q,hq,hb,hj,eq⟩
  · exact Or.inl h
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
    refine Or.inr ?_
    change order cells x=c.val.l at eq
    rw [eq]
    have pos : 0<(start k).j+c.val.j := by have := c.property.1; omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y:=⟨c.val.b,c.val.j,0⟩)
      (start_flat k) pos hb hj).trans_lt c.property.2

theorem layer_le_available {r y : Shape} {L : ℕ}
    (hr : r=zeroShape ∨ 0<r.j) (hj : 0<r.j+y.j) :
    (∑ k∈range layerCount,layerTerm r y L k)≤availableMass r y L := by
  exact Final50PriceLayer.layerSum_le_available_n _ hr hj


end Low6966Allocation

end
end Merged_R6960Low6966AllocCore

