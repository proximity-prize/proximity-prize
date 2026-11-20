import Mathlib.Algebra.BigOperators.Ring.Finset
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem germDegreeY_eq (f g : Flag) (hg : g.r ≤ g.y) :
    germDegreeY f g = g.r*f.y+f.r*(g.y-g.r) := by
  unfold germDegreeY
  rw [Nat.mul_sub_left_distrib, Nat.add_sub_assoc (Nat.mul_le_mul_left f.r hg)]

theorem germDegreeT_eq (f g : Flag) (hg : g.r ≤ g.t) :
    germDegreeT f g = g.r*f.t+f.r*(g.t-g.r) := by
  unfold germDegreeT
  rw [Nat.mul_sub_left_distrib, Nat.add_sub_assoc (Nat.mul_le_mul_left f.r hg)]

theorem germDegreeT_mono_left (f f' g : Flag) (hg : g.r ≤ g.t)
    (hr : f.r ≤ f'.r) (ht : f.t ≤ f'.t) : germDegreeT f g ≤ germDegreeT f' g := by
  rw [germDegreeT_eq _ _ hg,germDegreeT_eq _ _ hg]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_right _ hr)

theorem germPrice_sum_le {A : Type*} (S : Finset A) (flags : A → Flag) (f g : Flag)
    (hgy : g.r ≤ g.y) (hgt : g.r ≤ g.t)
    (hr : (∑ i ∈ S, (flags i).r) ≤ f.r) (hy : (∑ i ∈ S, (flags i).y) ≤ f.y)
    (ht : (∑ i ∈ S, (flags i).t) ≤ f.t) :
    (∑ i ∈ S, germPrice (flags i) g) ≤ germPrice f g := by
  unfold germPrice
  simp_rw [germDegreeT_eq _ _ hgt,germDegreeY_eq _ _ hgy]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_right _ hr))
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hy) (Nat.mul_le_mul_right _ hr)))




end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
