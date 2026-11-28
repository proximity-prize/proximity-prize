import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily

set_option Elab.async false

-- merged module FadicDegree
section Merged_FadicDegree
set_option Elab.async false

-- merged module FadicCount
section Merged_FadicCount
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount cumulative denominator)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open TaperColumns (sumGrade sumOld)
end FadicGate

end Merged_FadicCount

-- merged module FadicSpace
section Merged_FadicSpace
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents)
open MvPolynomial
open scoped BigOperators
open Finset
theorem weight_four (w : Fin 4 → ℕ) (m : JetExp) :
    Finsupp.weight w m = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Fin.sum_univ_four]
theorem w_grade (m : JetExp) : Finsupp.weight gradeWeight m = m 0 + m 1 + m 2 + m 3 := by
  rw [weight_four]; simp [gradeWeight]
theorem w_old (m : JetExp) : Finsupp.weight oldWeight m = m 1 + 2 * m 2 + 3 * m 3 := by
  rw [weight_four]; simp [oldWeight]; omega
section Field
variable {𝕜 : Type*} [Field 𝕜]
local notation "R" => MvPolynomial (Fin 4) 𝕜
def DepthOK (xb xj r a : ℕ) : Prop :=
  3 * a ≤ r ∧ a < r ∧ a * xb ≤ 4012 ∧ a * xj ≤ 1650 ∧ a * (26 * xb + 25 * xj) ≤ 131312
instance (xb xj r a : ℕ) : Decidable (DepthOK xb xj r a) := by unfold DepthOK; infer_instance
end Field
end FadicGate

end Merged_FadicSpace

-- merged module FadicGateDim
section Merged_FadicGateDim
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset
def IsFull (σb σj σt r : ℕ) : Prop := 4012 ≤ r * σb ∧ 1650 ≤ r * σj ∧ 550 ≤ r * σt
instance (σb σj σt r : ℕ) : Decidable (IsFull σb σj σt r) := by unfold IsFull; infer_instance
section Field
variable {𝕜 : Type*} [Field 𝕜]
end Field
end FadicGate

end Merged_FadicGateDim

-- merged module FadicVar
section Merged_FadicVar
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open TaperColumns (jetExponents jetColumns)
open MvPolynomial
open scoped BigOperators
open Finset
def BoxOK (bh jh H a B J : ℕ) : Prop := B + a * bh ≤ 4012 ∧ J + a * jh ≤ 1650 ∧ a * H ≤ 131312
instance (bh jh H a B J : ℕ) : Decidable (BoxOK bh jh H a B J) := by unfold BoxOK; infer_instance
section Field
variable {𝕜 : Type*} [Field 𝕜]
local notation "R" => MvPolynomial (Fin 4) 𝕜
end Field
end FadicGate

end Merged_FadicVar

-- merged module FadicDegree
section Merged_FadicDegree
set_option autoImplicit false
namespace FadicGate
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommSemiring R]
end FadicGate

end Merged_FadicDegree

end Merged_FadicDegree

-- merged module FadicChunk
section Merged_FadicChunk
set_option Elab.async false
set_option autoImplicit false
namespace FadicGate
open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
theorem cappedCount_mono {d d' : ℕ} (hd : d ≤ d') (u t : ℤ) :
    cappedCount d u t ≤ cappedCount d' u t := by
  rw [← capped_card K1_13_2_2_2.proof, ← capped_card K1_13_2_2_2.proof]
  have hcard : (cappedColumns d u t).card ≤ (cappedColumns d' u t).card := by
    let shift : JetExp → JetExp := fun e => e + Finsupp.single 0 (d' - d)
    apply Finset.card_le_card_of_injOn shift
    · intro e he
      obtain ⟨hj, ht⟩ := mem_cappedColumns.mp he
      obtain ⟨hg, hi⟩ := mem_cumulativeColumns.mp hj
      have hg' : ((Finsupp.weight gradeWeight e : ℕ) : ℤ) = (d : ℤ) := hg
      have hi' : ((Finsupp.weight oldWeight e : ℕ) : ℤ) ≤ u := hi
      apply mem_cappedColumns.mpr
      have e0 : shift e 0 = e 0 + (d' - d) := by simp [shift]
      have e1 : shift e 1 = e 1 := by simp [shift]
      have e2 : shift e 2 = e 2 := by simp [shift]
      have e3 : shift e 3 = e 3 := by simp [shift]
      refine ⟨mem_cumulativeColumns.mpr ⟨?_, ?_⟩, ?_⟩
      · change ((Finsupp.weight gradeWeight (shift e) : ℕ) : ℤ) = (d' : ℤ)
        rw [w_grade, e0, e1, e2, e3]
        rw [w_grade] at hg'
        push_cast at hg' ⊢
        omega
      · change ((Finsupp.weight oldWeight (shift e) : ℕ) : ℤ) ≤ u
        rw [w_old, e1, e2, e3, ← w_old]
        exact hi'
      · change ((shift e 3 : ℕ) : ℤ) ≤ t
        rw [e3]
        exact ht
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  exact_mod_cast hcard
end FadicGate

end Merged_FadicChunk
