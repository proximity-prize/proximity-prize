import ProximityPrize.SubmissionLower.R6960CoverBudget
import Mathlib.GroupTheory.GroupAction.Basic

open scoped BigOperators
open Finset
namespace Lower6960.MarkedSheet

/-- All translates of one nonzero coordinate minor suffice. Transitivity on
single sheets gives the omitted fraction even if most other minors are zero. -/
theorem omission {G I : Type*} [Group G] [Fintype G] [Fintype I] [MulAction G I]
    [MulAction.IsPretransitive G I] [DecidableEq I] (S : Finset I) (point : I) :
    Fintype.card I * (∑ g : G, if g • point ∉ S then 1 else 0 : ℕ) =
      Fintype.card G * (Fintype.card I - S.card) := by
  classical
  let misses (x : I) : ℕ := ∑ g : G, if g • x ∉ S then 1 else 0
  have const (x : I) : misses x = misses point := by
    obtain ⟨h,ho⟩ := MulAction.exists_smul_eq G point x
    rw [←ho]
    dsimp only [misses]
    simp_rw [←mul_smul]
    exact Equiv.sum_comp (Equiv.mulRight h) (fun g : G => if g • point ∉ S then (1:ℕ) else 0)
  have row (g : G) : (∑ x : I, if g • x ∉ S then 1 else 0 : ℕ) = Fintype.card I-S.card := by
    calc _ = ∑ x : I, if x ∉ S then (1:ℕ) else 0 :=
                Equiv.sum_comp (MulAction.toPerm g) (fun x : I => if x ∉ S then (1:ℕ) else 0)
         _ = (univ \ S).card := by
                simp only [Finset.sum_boole, Finset.sdiff_eq_filter, Nat.cast_id]
         _ = _ := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  calc _ = ∑ _x : I, misses point := by simp only [sum_const,card_univ,nsmul_eq_mul]; rfl
       _ = ∑ x : I, misses x := Finset.sum_congr rfl (fun x _ => (const x).symm)
       _ = ∑ g : G, ∑ x : I, if g • x ∉ S then 1 else 0 := Finset.sum_comm
       _ = _ := by simp_rw [row]; simp

def rate (e : ℕ) := (9*e-6)*(e-1)+2*e-1

/-- Combine the two geometric bills at the largest pole degree. -/
theorem good_price (labels a e n s t loss torsion image : ℕ)
    (size : 0<a) (degree : s≤n*a) (positive : 0<e)
    (marked : labels*a≤loss+torsion+e*image)
    (collisions : loss≤8*s*t) (sections : torsion+image≤n+a*t) :
    labels≤(8*n+e)*t+e*n := by
  have h1 : 8*s*t≤8*(n*a)*t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left 8 degree)
  have h2 : torsion+e*image≤e*(n+a*t) := calc
    _ ≤ e*torsion+e*image := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ positive) _
    _ = e*(torsion+image) := (Nat.mul_add ..).symm
    _ ≤ _ := Nat.mul_le_mul_left e sections
  refine Nat.le_of_mul_le_mul_right ?_ size
  calc labels*a ≤ loss+(torsion+e*image) := by simpa only [Nat.add_assoc] using marked
       _ ≤ 8*(n*a)*t+e*(n+a*t) := Nat.add_le_add (collisions.trans h1) h2
       _ = ((8*n+e)*t)*a+e*n := by ring
       _ ≤ ((8*n+e)*t)*a+(e*n)*a := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ size) _
       _ = _ := (Nat.add_mul ..).symm

/-- The additive e(e-1) is paid once per factor, not per unit of scalar degree. -/
theorem endpoint :
    rate 47 = 19275 ∧
    (∀ e : Fin 48, 3≤e.val → 12*e.val≤rate e.val ∧ rate e.val≤rate 47) ∧
    143313454876987920 + 143456202788540 + (rate 47)*(2400*2130706433) +
      47*46 + 48 < 266695718139456639 := by decide +kernel

#print axioms omission
#print axioms good_price
#print axioms endpoint

private def paidOrder : Array ℕ := #[0,1167,1163,1158,1153,1148,1142,1137,1132,1127,1121,1116,1110,1105,1099,1093,1088,1082,1076,1070,1063,1057,1050,1044,1037,1030,1023,1016,1008,1001,993,985,977,968,959,949,939,929,918,905,891,874,836,758,650,517,364,191,0]

theorem graded_endpoint :
    (∀ e : Fin 48, 3≤e.val →
      rate e.val * (2130706433+1) * (paidOrder[e.val]!-1) + e.val*(e.val-1) ≤
        27283109943102372) ∧
    rate 42 * (2130706433+1) * (paidOrder[42]!-1) + 42*41 = 27283109943102372 ∧
    95955697116577759 + 143313454876987920 + 143456202788540 + 48 +
      27283109943102372 = 266695718139456639 := by decide +kernel

#print axioms graded_endpoint
end Lower6960.MarkedSheet
