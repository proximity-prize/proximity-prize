import ProximityPrize.SubmissionLower.Fast017

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Companion
open K1_13 (Shape InBox)
open Finset
open scoped BigOperators

def legal (x : Shape) : Prop :=
  1 ≤ x.t ∧ 3*x.t ≤ x.j ∧ x.t ≤ x.b ∧ x.j ≤ 2*x.b+x.t

def number (b j t : ℕ) : ℕ := min b (min (j/3) t)

/-- A charge is either per partner or per unit of its degree. -/
def charge (byDegree : Bool) (rate : ℕ) (x : Shape) : ℕ :=
  if byDegree then rate*x.b else rate

def bill (byDegree : Bool) (rate b j t : ℕ) : ℕ :=
  rate * (if byDegree then b else number b j t)

theorem sum_le_bill {ι : Type*} {s : Finset ι} {a : ι → Shape} {cost : ι → ℕ}
    {b j t rate : ℕ} {byDegree : Bool}
    (ha : ∀ i ∈ s, legal (a i))
    (hb : (∑ i ∈ s, (a i).b) ≤ b)
    (hj : (∑ i ∈ s, (a i).j) ≤ j)
    (ht : (∑ i ∈ s, (a i).t) ≤ t)
    (hcost : ∀ i ∈ s, cost i ≤ charge byDegree rate (a i)) :
    (∑ i ∈ s, cost i) ≤ bill byDegree rate b j t := by
  have h := sum_le_sum hcost
  cases byDegree with
  | true =>
      simpa only [charge,bill,if_true,←mul_sum] using h.trans
        (show (∑ i ∈ s, charge true rate (a i)) ≤ bill true rate b j t by
          simpa only [charge,bill,if_true,←mul_sum] using Nat.mul_le_mul_left rate hb)
  | false =>
      have oneT : s.card ≤ ∑ i ∈ s, (a i).t := by
        simpa using (sum_le_sum (fun i hi => (ha i hi).1))
      have topB : (∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).b :=
        sum_le_sum (fun i hi => (ha i hi).2.2.1)
      have threeJ : 3*(∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).j := by
        rw [mul_sum]
        exact sum_le_sum (fun i hi => (ha i hi).2.1)
      have hc : s.card ≤ number b j t := le_min (oneT.trans (topB.trans hb))
        (le_min (by omega) (oneT.trans ht))
      have hz : (∑ i ∈ s, charge false rate (a i)) = rate*s.card := by
        simp [charge,Nat.mul_comm]
      rw [hz] at h
      exact h.trans (Nat.mul_le_mul_left rate hc)

theorem member_fits {ι : Type*} {s : Finset ι} {a : ι → Shape}
    {b j t : ℕ} (hb : (∑ i ∈ s, (a i).b) ≤ b)
    (hj : (∑ i ∈ s, (a i).j) ≤ j) (ht : (∑ i ∈ s, (a i).t) ≤ t)
    {i : ι} (hi : i ∈ s) : InBox (a i) ⟨b,j,t⟩ :=
  ⟨(single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hb,
   (single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hj,
   (single_le_sum (fun _ _ => Nat.zero_le _) hi).trans ht⟩

end Height2307Companion
