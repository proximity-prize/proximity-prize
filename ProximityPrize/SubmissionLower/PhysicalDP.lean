/- Apache-2.0. Bome2017. Additive multifactor accounting for KoalaBear 68.35.
   One distinguished factor of least positive rank is split off at each step. -/
import Mathlib.Tactic
namespace Koala6835.Partition
open Finset
open scoped BigOperators Classical
set_option autoImplicit false
abbrev Price := ℕ → ℕ → ℕ → ℕ

structure Certificate (one all many : Price) (rMax yMax tMax width : ℕ) : Prop where
  single : ∀ r e k, 1≤r → r≤rMax → r+e≤yMax → r+e+k*width≤tMax → one r e k ≤ all r e k
  absorb : ∀ r e k, 1≤r → r≤rMax → r+e≤yMax → r+e+k*width≤tMax → many r e k ≤ all r e k
  split : ∀ r e k a m h, 1≤a → 2*a≤r → m≤e → h≤k →
    r≤rMax → r+e≤yMax → r+e+k*width≤tMax →
    one a m h + all (r-a) (e-m) (k-h) ≤ many r e k

theorem finite_partition {I : Type*} (r e k v : I→ℕ) (one all many : Price)
    (rMax yMax tMax width : ℕ) (cert : Certificate one all many rMax yMax tMax width)
    (S : Finset I) (nonempty : S.Nonempty) (pos : ∀i∈S,1≤r i)
    (cost : ∀i∈S,v i≤one (r i) (e i) (k i))
    (rank : ∑i∈S,r i ≤rMax) (middle : (∑i∈S,r i)+(∑i∈S,e i)≤yMax)
    (total : (∑i∈S,r i)+(∑i∈S,e i)+(∑i∈S,k i)*width≤tMax) :
    (∑ i∈S,v i) ≤ all (∑i∈S,r i) (∑i∈S,e i) (∑i∈S,k i) ∧
    (1<S.card → (∑ i∈S,v i) ≤ many (∑i∈S,r i) (∑i∈S,e i) (∑i∈S,k i)) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨i,hi,least⟩ := Finset.exists_min_image S r nonempty
    let T := S.erase i
    have proper : T ⊂ S := erase_ssubset hi
    have sums (f:I→ℕ) : f i+(∑j∈T,f j) = ∑j∈S,f j := by
      rw [add_comm]; exact sum_erase_add _ _ hi
    have hpos := pos i hi
    have hv := cost i hi
    by_cases gone : T=∅
    · have s : S={i} := by rw [←insert_erase hi]; change insert i T={i}; simp only [gone,insert_empty]
      subst S
      simp only [sum_singleton,card_singleton,lt_self_iff_false,false_implies,and_true] at *
      exact hv.trans (cert.single _ _ _ hpos rank middle total)
    have tr : T.Nonempty := nonempty_iff_ne_empty.mpr gone
    obtain ⟨j,hj⟩ := tr
    have tailpos : r i≤∑j∈T,r j :=
      (least j (proper.subset hj)).trans (single_le_sum (f:=r) (fun a _ => Nat.zero_le (r a)) hj)
    have leSum (f:I→ℕ) : (∑j∈T,f j) ≤ ∑j∈S,f j := sum_le_sum_of_subset proper.subset
    obtain ⟨q,_⟩ := ih T proper ⟨j,hj⟩ (fun j hj => pos j (proper.subset hj))
      (fun j hj => cost j (proper.subset hj)) ((leSum r).trans rank)
      ((Nat.add_le_add (leSum r) (leSum e)).trans middle)
      ((Nat.add_le_add (Nat.add_le_add (leSum r) (leSum e))
        (Nat.mul_le_mul_right width (leSum k))).trans total)
    have hs := cert.split (∑j∈S,r j) (∑j∈S,e j) (∑j∈S,k j) (r i) (e i) (k i) hpos
      (by have := sums r; omega) (by have := sums e; omega) (by have := sums k; omega) rank middle total
    have diff (f:I→ℕ) : (∑j∈S,f j)-f i=∑j∈T,f j := by have := sums f; omega
    rw [diff r,diff e,diff k] at hs
    have pay := (sums v).ge.trans ((Nat.add_le_add hv q).trans hs)
    exact ⟨pay.trans (cert.absorb _ _ _ (by have := sums r; omega) rank middle total),fun _ => pay⟩

theorem floor_total {I : Type*} (s : Finset I) (t : I→ℕ) (w:ℕ) (pos : 0<w) :
    (∑i∈s,(t i)/w)≤(∑i∈s,t i)/w := by
  apply (Nat.le_div_iff_mul_le pos).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _

#print axioms finite_partition
#print axioms floor_total
end Koala6835.Partition
