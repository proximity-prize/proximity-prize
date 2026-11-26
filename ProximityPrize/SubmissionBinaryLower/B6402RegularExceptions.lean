import ProximityPrize.SubmissionBinaryLower.B6402RegularWitness

namespace ProximityPrize.SubmissionBinaryLower.B6402RegularExceptions
open Polynomial B6401ContactKerD B6402MixedDegree B6402RegularWitness B6402FibreSlice P64LineOrder
open scoped BigOperators
set_option autoImplicit false
variable {K : Type} {I : Type*} [Field K] [CharP K 2]

theorem nonzero_quartic (F : ContactPoly (Polynomial K)) (x : K) (y : K[X])
    (reg : evalXAt (F.coeff 1) x≠0)
    (form : ordinateHom x y (F.coeff 1)=monomial 4 (quartic F x)) :
    quartic F x≠0 := by
  intro hz
  rw [hz,monomial_zero_right] at form
  change taylor y (evalXAt (F.coeff 1) x)=0 at form
  exact reg ((taylor_eq_zero _ _).mp form)

theorem excluded (F : ContactPoly (Polynomial K)) (q H : ℕ) (height : mixed q F≤H)
    (x : I → K) (good : Finset I) (nonzero : ∀ i∈good,quartic F (x i)≠0) :
    ∃ E : Finset K,E.card≤good.card*H ∧ ∀ z∉E,∀ i∈good,(quartic F (x i)).eval z≠0 := by
  classical
  let E := good.biUnion fun i => (quartic F (x i)).roots.toFinset
  refine ⟨E,?_,?_⟩
  · calc E.card ≤ ∑ i∈good,(quartic F (x i)).roots.toFinset.card := Finset.card_biUnion_le
         _ ≤ ∑ _i∈good,H := by
             apply Finset.sum_le_sum; intro i _
             exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (quartic_degree F (x i) height))
         _ = _ := by simp
  · intro z hz i hi he
    apply hz; apply Finset.mem_biUnion.mpr
    exact ⟨i,hi,Multiset.mem_toFinset.mpr ((mem_roots (nonzero _ hi)).mpr he)⟩

#print axioms excluded
end ProximityPrize.SubmissionBinaryLower.B6402RegularExceptions
