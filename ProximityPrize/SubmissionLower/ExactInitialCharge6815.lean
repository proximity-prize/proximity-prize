import ProximityPrize.SubmissionLower.PhasePotential6815
namespace ProximityPrize.SubmissionLower.ExactInitialCharge6815
open scoped BigOperators
open RCN260 AsymmetricHelper
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

def num (L U S r y t : ℕ) : ℕ :=
  leftRegularNumerator (PhasePotential6815.pair L U S r y t)
def cost (L U S r y t : ℕ) : ℕ :=
  leftRegularCountCap (PhasePotential6815.pair L U S r y t)

theorem num_formula (L U S r y t : ℕ) :
    num L U S r y t =
      131073*((1+2*131071*y)*(r*L+t*S)+131071*(2*r-1)*(y*L+t*U)+
        (1+2*131071*t)*(y*S+r*U))+80900*50174*(y*S+r*U) := by
  simp only [num,leftRegularNumerator,PhasePotential6815.pair,
    UnequalParameters.errors,UnequalParameters.gap,UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost,RCN294.dot]
  norm_num only [Nat.reduceSub,Nat.reduceAdd,Nat.reduceMul]
  ring

theorem cost_eq (L U S r y t : ℕ) : cost L U S r y t=num L U S r y t/50174 := by
  simp only [cost,num,leftRegularCountCap,PhasePotential6815.pair,UnequalParameters.gap,Nat.reduceSub]

theorem num_mono (L U S r y t capR capY capT : ℕ) (hr : r≤capR) (hy : y≤capY) (ht : t≤capT) :
    num L U S r y t≤num L U S capR capY capT := by
  rw [num_formula,num_formula]
  gcongr

theorem cost_mono (L U S r y t capR capY capT : ℕ) (hr : r≤capR) (hy : y≤capY) (ht : t≤capT) :
    cost L U S r y t≤cost L U S capR capY capT := by
  rw [cost_eq,cost_eq]
  exact Nat.div_le_div_right (num_mono L U S r y t capR capY capT hr hy ht)

theorem sum_num_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S : ℕ) (r y t : ι → ℕ) :
    (∑ i∈s, num L U S (r i) (y i) (t i))≤
      num L U S (∑ i∈s, r i) (∑ i∈s, y i) (∑ i∈s, t i) := by
  have hterm (i : ι) (hi : i∈s) :
      num L U S (r i) (y i) (t i)≤
        131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80900*50174*(y i*S+r i*U) := by
    have hr := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (r j)) hi
    have hy := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (y j)) hi
    have ht := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (t j)) hi
    rw [num_formula]
    gcongr
  calc
    _≤∑ i∈s, (131073*((1+2*131071*(∑ j∈s,y j))*(r i*L+t i*S)+
          131071*(2*(∑ j∈s,r j)-1)*(y i*L+t i*U)+
          (1+2*131071*(∑ j∈s,t j))*(y i*S+r i*U))+
          80900*50174*(y i*S+r i*U)) := Finset.sum_le_sum hterm
    _=_ := by
      rw [num_formula]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]

theorem sum_cost_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S : ℕ) (r y t : ι → ℕ) :
    (∑ i∈s, cost L U S (r i) (y i) (t i))≤
      cost L U S (∑ i∈s, r i) (∑ i∈s, y i) (∑ i∈s, t i) := by
  conv_rhs => rw [cost_eq]
  apply (Nat.le_div_iff_mul_le (by decide : 0<50174)).mpr
  calc
    _=∑ i∈s, cost L U S (r i) (y i) (t i)*50174 := by rw [Finset.sum_mul]
    _≤∑ i∈s, num L U S (r i) (y i) (t i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [cost_eq]
      exact Nat.div_mul_le_self _ _
    _≤_ := sum_num_le s L U S r y t

theorem helpers_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (L U S capR capY capT : ℕ) (r y t helper : ι → ℕ)
    (hhelper : ∀ i∈s, helper i≤cost L U S (r i) (y i) (t i))
    (hr : (∑ i∈s, r i)≤capR) (hy : (∑ i∈s, y i)≤capY) (ht : (∑ i∈s, t i)≤capT) :
    (∑ i∈s, helper i)≤cost L U S capR capY capT :=
  (Finset.sum_le_sum hhelper).trans ((sum_cost_le s L U S r y t).trans
    (cost_mono L U S _ _ _ capR capY capT hr hy ht))

theorem initial_helpers_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (pr py pt : ℕ) (r y t helper : ι → ℕ)
    (hhelper : ∀ i∈s, helper i≤cost 76330 182 39 (r i) (y i) (t i))
    (hrpos : ∀ i∈s, 1≤r i)
    (hry : ∀ i∈s, r i≤y i) (hyt : ∀ i∈s, y i≤t i)
    (hr : pr+(∑ i∈s, r i)≤50)
    (hy : py+(∑ i∈s, y i)≤229)
    (ht : pt+(∑ i∈s, t i)≤11192) :
    (∑ i∈s, helper i)≤
      let remT := 11192-pt
      let remY := min remT (229-py)
      let remR := min remY (50-pr)
      if remR=0 then 0 else cost 76330 182 39 remR remY remT := by
  have hrySum := Finset.sum_le_sum hry
  have hytSum := Finset.sum_le_sum hyt
  have ht' : (∑ i∈s,t i)≤11192-pt := by omega
  have hy' : (∑ i∈s,y i)≤min (11192-pt) (229-py) := by omega
  have hr' : (∑ i∈s,r i)≤min (min (11192-pt) (229-py)) (50-pr) := by omega
  dsimp only
  split_ifs with hz
  · have hs : s=∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      have hiSum := Finset.single_le_sum (fun j (_ : j∈s) => Nat.zero_le (r j)) hi
      have hiPos := hrpos i hi
      omega
    simp [hs]
  · exact helpers_sum_le s 76330 182 39 _ _ _ r y t helper hhelper hr' hy' ht'

end ProximityPrize.SubmissionLower.ExactInitialCharge6815
