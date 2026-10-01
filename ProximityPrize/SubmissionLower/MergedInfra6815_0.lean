import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.AffineFactorAggregate6808
open scoped BigOperators
set_option autoImplicit false

def BellmanRows (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v R V, 1 ≤ r → r + R ≤ Rcap → r + v + R + V ≤ Ycap →
    b r v + B R V ≤ B (r + R) (v + V)

theorem sum_intercepts_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap) :
    (∑ i ∈ s, b (r i) (v i)) ≤ B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hRi : r a + (∑ i ∈ s, r i) ≤ Rcap := by
      simpa only [Finset.sum_insert ha] using hR
    have hYi : (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ Ycap := by
      simpa only [Finset.sum_insert ha] using hY
    have hrec := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
      (by omega) (by omega)
    have hrow := hrows (r a) (v a) (∑ i ∈ s, r i) (∑ i ∈ s, v i)
      (hr a (Finset.mem_insert_self a s)) hRi (by omega)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

theorem sum_count_le {ι : Type*} [DecidableEq ι]
    (Rcap Ycap slope : ℕ) (b B : ℕ → ℕ → ℕ)
    (hrows : BellmanRows Rcap Ycap b B)
    (s : Finset ι) (r v z count : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i)
    (hR : (∑ i ∈ s, r i) ≤ Rcap)
    (hY : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ Ycap)
    (hcost : ∀ i ∈ s, count i ≤ slope * z i + b (r i) (v i)) :
    (∑ i ∈ s, count i) ≤ slope * (∑ i ∈ s, z i) +
      B (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  calc
    (∑ i ∈ s, count i) ≤ ∑ i ∈ s, (slope * z i + b (r i) (v i)) :=
      Finset.sum_le_sum hcost
    _ = slope * (∑ i ∈ s, z i) + ∑ i ∈ s, b (r i) (v i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add_left (sum_intercepts_le Rcap Ycap b B hrows s r v hr hR hY) _

theorem singleton_helper {ι : Type*} [DecidableEq ι] (a : ι)
    (count helper : ι → ℕ)
    (hsplit : ∃ U : Finset ι, U ⊂ {a} ∧ ∀ i ∈ ({a} : Finset ι) \ U,
      count i ≤ helper i) : count a ≤ helper a := by
  obtain ⟨U, hU, hcount⟩ := hsplit
  have ha : a ∉ U := by
    intro ha
    apply hU.2
    exact Finset.singleton_subset_iff.mpr ha
  exact hcount a (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self a, ha⟩)

end ProximityPrize.SubmissionLower.AffineFactorAggregate6808
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.RectangularPacking6815
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
variable {ι A : Type*} [DecidableEq ι]

def Bellman (Rcap Vcap : ℕ) (own packed : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v R V, 1≤r → r+R≤Rcap → v+V≤Vcap → own r v+packed R V≤packed (r+R) (v+V)

theorem sum_intercepts (Rcap Vcap : ℕ) (own packed : ℕ → ℕ → ℕ) (hb : Bellman Rcap Vcap own packed)
    (s : Finset ι) (r v : ι → ℕ) (hr : ∀ i∈s, 1≤r i)
    (hR : (∑ i∈s,r i)≤Rcap) (hV : (∑ i∈s,v i)≤Vcap) :
    (∑ i∈s,own (r i) (v i))≤packed (∑ i∈s,r i) (∑ i∈s,v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hRi : r a+(∑ i∈s,r i)≤Rcap := by simpa only [Finset.sum_insert ha] using hR
    have hVi : v a+(∑ i∈s,v i)≤Vcap := by simpa only [Finset.sum_insert ha] using hV
    have hrec := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi)) (by omega) (by omega)
    have hrow := hb (r a) (v a) (∑ i∈s,r i) (∑ i∈s,v i) (hr a (Finset.mem_insert_self a s)) hRi hVi
    rw [Finset.sum_insert ha,Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Nat.add_le_add_left hrec _).trans hrow

theorem sum_affine (Rcap Vcap slope : ℕ) (own packed : ℕ → ℕ → ℕ) (hb : Bellman Rcap Vcap own packed)
    (s : Finset ι) (r v z count : ι → ℕ) (hr : ∀ i∈s, 1≤r i)
    (hR : (∑ i∈s,r i)≤Rcap) (hV : (∑ i∈s,v i)≤Vcap)
    (hc : ∀ i∈s, count i≤slope*z i+own (r i) (v i)) :
    (∑ i∈s,count i)≤slope*(∑ i∈s,z i)+packed (∑ i∈s,r i) (∑ i∈s,v i) := by
  have h := Finset.sum_le_sum hc
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at h
  exact h.trans (Nat.add_le_add_left (sum_intercepts Rcap Vcap own packed hb s r v hr hR hV) _)

theorem one_heavy (H Rcap Vcap cap : ℕ) (s : Finset ι) (r v z count : ι → ℕ)
    (slope : A → ℕ) (own packed : A → ℕ → ℕ → ℕ) (single : ℕ → ℕ → ℕ → ℕ)
    (hr : ∀ i∈s, 1≤r i) (hR : (∑ i∈s,r i)≤Rcap) (hV : (∑ i∈s,v i)≤Vcap)
    (hH : (∑ i∈s,r i)<2*H)
    (hb : ∀ a, Bellman Rcap Vcap (own a) (packed a))
    (hlight : ∀ i∈s, r i<H → ∀ a, count i≤slope a*z i+own a (r i) (v i))
    (hsingle : ∀ i∈s, count i≤single (r i) (v i) (z i))
    (hzero : ∃ a, slope a*(∑ i∈s,z i)+packed a (∑ i∈s,r i) (∑ i∈s,v i)≤cap)
    (hheavy : ∀ q u, H≤q → q≤∑ i∈s,r i → u≤∑ i∈s,v i → ∃ a, ∀ x, x≤∑ i∈s,z i →
      single q u x+slope a*((∑ i∈s,z i)-x)+packed a ((∑ i∈s,r i)-q) ((∑ i∈s,v i)-u)≤cap) :
    (∑ i∈s,count i)≤cap := by
  by_cases hex : ∃ j∈s, H≤r j
  · obtain ⟨j,hj,hjH⟩ := hex
    have hsumR := Finset.add_sum_erase s r hj
    have hsumV := Finset.add_sum_erase s v hj
    have hsumZ := Finset.add_sum_erase s z hj
    have hsumC := Finset.add_sum_erase s count hj
    have hrem : ∀ i∈s.erase j, r i<H := by
      intro i hi
      have hri : r i≤∑ k∈s.erase j,r k := Finset.single_le_sum (fun k _ => Nat.zero_le (r k)) hi
      omega
    have hjR : r j≤∑ i∈s,r i := Finset.single_le_sum (fun i _ => Nat.zero_le (r i)) hj
    have hjV : v j≤∑ i∈s,v i := Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) hj
    have hjZ : z j≤∑ i∈s,z i := Finset.single_le_sum (fun i _ => Nat.zero_le (z i)) hj
    obtain ⟨a,ha⟩ := hheavy (r j) (v j) hjH hjR hjV
    have hrest := sum_affine Rcap Vcap (slope a) (own a) (packed a) (hb a) (s.erase j) r v z count
      (fun i hi => hr i (Finset.mem_of_mem_erase hi)) (by omega) (by omega)
      (fun i hi => hlight i (Finset.mem_of_mem_erase hi) (hrem i hi) a)
    have hhead := hsingle j hj
    have hbudget := ha (z j) hjZ
    rw [show (∑ i∈s,r i)-r j=∑ i∈s.erase j,r i by omega,
      show (∑ i∈s,v i)-v j=∑ i∈s.erase j,v i by omega,
      show (∑ i∈s,z i)-z j=∑ i∈s.erase j,z i by omega] at hbudget
    omega
  · have hl : ∀ i∈s, r i<H := by intro i hi; by_contra hn; exact hex ⟨i,hi,by omega⟩
    obtain ⟨a,ha⟩ := hzero
    exact (sum_affine Rcap Vcap (slope a) (own a) (packed a) (hb a) s r v z count hr hR hV
      (fun i hi => hlight i hi (hl i hi) a)).trans ha

end ProximityPrize.SubmissionLower.RectangularPacking6815
end MergedPart1
