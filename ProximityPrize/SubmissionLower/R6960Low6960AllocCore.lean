import ProximityPrize.SubmissionLower.R6960Low6960Monotone
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.Final50PriceMass

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Low6960Allocation
open Finset
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape Valid)
open K1_13_8_2 (Threshold orderFor)
open Final50PriceLayer (availableMass fastLayer layerTerm)
open Final50FatReserve (degreeCap)
open Low6960Retained (Box)
open Lower6960.Low (retainedTariff need layerCount)
open private degree_bound from ProximityPrize.SubmissionLower.R6960Low6960Width
open private check check_sum mass_eq from ProximityPrize.SubmissionLower.Final50PriceMass
open private P3_6_8_1.sumBelow from ProximityPrize.SubmissionLower.GoldBranch6N8
open scoped BigOperators Classical

abbrev Band := Fin 15
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData :=
  [
    ⟨0,0,0,0,0⟩,
    ⟨1,16,3,1,10718346357689957⟩,
    ⟨17,25,3,1,18900494517910566⟩,
    ⟨2,23,4,1,34088662333434598⟩,
    ⟨2,20,5,1,51637756646560261⟩,
    ⟨2,16,6,1,60081355090174287⟩,
    ⟨2,9,6,2,124301705663343579⟩,
    ⟨10,12,6,2,161764100501577018⟩,
    ⟨13,14,6,2,187210711761750865⟩,
    ⟨15,15,6,2,200101152787613494⟩,
    ⟨16,16,6,2,213114408959713367⟩,
    ⟨3,10,7,1,54306876026275681⟩,
    ⟨3,7,7,2,157890651360317725⟩,
    ⟨8,9,7,2,194981991053061202⟩,
    ⟨10,10,7,2,213630718831783047⟩
  ]

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

private theorem checked_cover (b : Fin 26) :
    ∀ (j : Fin 8) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      b.val≤degreeCap j.val → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<26 := Nat.lt_succ_of_le box.1
  have hj : j<8 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 (degree_bound v box)

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 26,(start k).b≤b.val → b.val≤endWidth k →
      retainedTariff b.val (start k).j (start k).t≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    retainedTariff r.b r.j r.t≤reserve k := by
  have hm : endWidth k<26 := by fin_cases k <;> decide +kernel
  rw [hr.2.2.1,hr.2.2.2]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 266695718139316639

def factorCap (top : ℕ) : ℕ := budget-Low6960Prices.lowerCap top

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then KoalaAllocationWeight.weight b j t else j

def pricingDenom (k : Band) : ℕ := if k=empty then 352 else 55-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤14) (k : Band) : reserve k≤factorCap top := by
  interval_cases top <;> fin_cases k <;> decide +kernel

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using KoalaAllocationWeight.mono hb hj ht
  · simpa only [pricingWeight,ite_eq_right h] using hj

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤14) :
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
  apply le_trans _ (Final50PriceLayer.layerSum_le_available hr hj)
  exact sum_le_sum_of_subset (range_mono (by decide +kernel))

#print axioms choose_band
#print axioms order_valid

end Low6960Allocation
