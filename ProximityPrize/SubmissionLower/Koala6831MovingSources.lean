/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Koala6831MovingStages

namespace ProximityPrize.SubmissionLower.Koala6831MovingSources

open RCN081 RCN156 RCN234 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
open LocatorPhase6800Oracle (SourceNumbers)
open Koala6831MovingStages

noncomputable section

inductive Stage where
  | primary
  | room1
  | room2
  | adaptive1
  | adaptive2
  | adaptive3

def agreement : ℕ := 181078
def weight : ℕ := 131071

namespace Stage

def numbers : Stage → SourceNumbers
  | .primary => ⟨41882, 418, 93, 75072160⟩
  | .room1 => ⟨153515, 2318, 522, 72953148141⟩
  | .room2 => ⟨816249, 2084, 464, 183606490⟩
  | .adaptive1 => adaptiveSource1
  | .adaptive2 => adaptiveSource2
  | .adaptive3 => adaptiveSource3

def multiplicity : Stage → ℕ
  | .primary => 303
  | .room1 => 1679
  | .room2 => 1510
  | .adaptive1 => 1200
  | .adaptive2 => 2600
  | .adaptive3 => 30000

def room : Stage → ℕ
  | .room1 => 171954
  | .room2 => 267484
  | _ => 0

def cutoff (s : Stage) : ℕ := s.multiplicity * agreement - s.room

def roomOrder (s : Stage) : ℕ := s.room / weightGain

theorem room_cutoff (s : Stage) :
    s.cutoff + s.roomOrder * weightGain ≤ s.multiplicity * agreement := by
  cases s <;> decide +kernel

private def remainder : Stage → ℕ
  | .primary => 78956
  | .room1 => 35430
  | .room2 => 8332
  | .adaptive1 => 108953
  | .adaptive2 => 126839
  | .adaptive3 => 102405

private theorem cutoff_eq (s : Stage) :
    s.cutoff = s.numbers.middleCap * weight + s.remainder := by
  cases s <;> decide +kernel

private theorem cutoff_add_slope_le (s : Stage) :
    s.cutoff + s.numbers.slopeCap ≤ weight * (s.numbers.middleCap + 1) := by
  cases s <;> decide +kernel

theorem coefficient_count_sub_rank (s : Stage) :
    RCN100.coefficientCount s.cutoff weight s.numbers.totalCap s.numbers.slopeCap -
      262144 * RCN119.localRankBound s.multiplicity s.numbers.totalCap s.numbers.slopeCap =
      s.numbers.gap := by
  rw [s.cutoff_eq, coefficientCount_eq_oneResidueCoefficientCount
    s.numbers.middleCap s.remainder weight s.numbers.totalCap s.numbers.slopeCap
    (by decide +kernel) (by cases s <;> decide +kernel) (by cases s <;> decide +kernel)
    (by cases s <;> decide +kernel),
    ClosedRank.localRankBound_eq_closed _ _ _ (by cases s <;> decide +kernel)
      (by cases s <;> decide +kernel)]
  cases s <;> decide +kernel

variable (s : Stage) (K : Type*) [Field K]
variable {I : Type*} [Fintype I]

abbrev Kernel (nodes u₀ u₁ : I → K) :=
  ConstraintKernel (K := K) s.cutoff weight s.numbers.totalCap s.numbers.slopeCap
    s.multiplicity nodes u₀ u₁

def reconstruct (nodes u₀ u₁ : I → K) :
    s.Kernel K nodes u₀ u₁ →ₗ[K] MvPolynomial (Fin 4) K :=
  kernelReconstructLinear (K := K) s.cutoff weight s.numbers.totalCap s.numbers.slopeCap
    s.multiplicity nodes u₀ u₁

theorem reconstruct_injective (nodes u₀ u₁ : I → K) :
    Function.Injective (s.reconstruct K nodes u₀ u₁) :=
  kernelReconstructLinear_injective s.cutoff weight s.numbers.totalCap s.numbers.slopeCap
    s.multiplicity nodes u₀ u₁

theorem finrank_lower_bound (nodes u₀ u₁ : I → K) (hcard : Fintype.card I ≤ 262144) :
    s.numbers.gap ≤ Module.finrank K (s.Kernel K nodes u₀ u₁) := by
  rw [← s.coefficient_count_sub_rank]
  exact (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ hcard) _).trans
    (constraintKernel_finrank_lower_bound s.cutoff weight s.numbers.totalCap s.numbers.slopeCap
      s.multiplicity nodes u₀ u₁)

theorem reconstruct_mem_box (nodes u₀ u₁ : I → K) (v : s.Kernel K nodes u₀ u₁) :
    s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K s.cutoff weight
      s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap := by
  let Q := s.reconstruct K nodes u₀ u₁ v
  have hQ : Q ∈ RCN100.globalCoefficientBox K s.cutoff weight s.numbers.totalCap
      s.numbers.slopeCap :=
    RCN100.reconstruct_mem_globalCoefficientBox K s.cutoff weight s.numbers.totalCap
      s.numbers.slopeCap v.1
  have hmiddle := flag_box_ys_bound s.cutoff weight s.numbers.totalCap s.numbers.slopeCap
    s.numbers.middleCap (by decide +kernel) s.cutoff_add_slope_le Q hQ
  intro d hd
  have hterm := hQ hd
  have htermMiddle := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hmiddle
  exact ⟨hterm.1, by simpa [weight_fin4, residualYSWeights] using htermMiddle,
    hterm.2.1, hterm.2.2⟩

theorem reconstruct_contact (nodes u₀ u₁ : I → K) (v : s.Kernel K nodes u₀ u₁) (i : I) :
    ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity
      (s.reconstruct K nodes u₀ u₁ v) :=
  ContactOrderBridge.contactAtLeast_of_mem_kernel K s.cutoff weight s.numbers.totalCap
    s.numbers.slopeCap s.multiplicity nodes u₀ u₁ v.1 v.2 i

theorem exists_source (nodes u₀ u₁ : I → K) (hcard : Fintype.card I ≤ 262144) :
    ∃ v : s.Kernel K nodes u₀ u₁, s.reconstruct K nodes u₀ u₁ v ≠ 0 := by
  have hgap : 0 < s.numbers.gap := by cases s <;> decide +kernel
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (hgap.trans_le (s.finrank_lower_bound K nodes u₀ u₁ hcard))
  refine ⟨v, ?_⟩
  intro hz
  exact hv (s.reconstruct_injective K nodes u₀ u₁ (hz.trans (map_zero _).symm))

end Stage

theorem specialization_zero_of_box_and_agreement
    {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]
    (nodes : I ↪ K) (u₀ u₁ : I → K) (s : Stage)
    (Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (seed : K) (support : Finset I)
    {L YS R : ℕ}
    (hbox : Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight L YS R)
    (hcontact : ∀ i ∈ support, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i)
      s.multiplicity Q)
    (hdegree : P.natDegree ≤ weight) (hcard : agreement ≤ support.card)
    (hvalues : ∀ i ∈ support, P.eval (nodes i) = u₀ i + seed * u₁ i) :
    RCN319.specialization K P seed Q = 0 := by
  rw [← RCN101.specialization_eq_ordinary]
  apply RCN122.specialization_eq_zero_of_contact_and_degree K Q P seed nodes u₀ u₁
    support s.multiplicity
  · intro i hi
    exact (ContactOrderBridge.contactAtLeast_iff_block_divisibility K
      (nodes i) (u₀ i) (u₁ i) s.multiplicity Q).mp (hcontact i hi)
  · exact hvalues
  · have hpos : 0 < s.multiplicity * agreement := by cases s <;> decide +kernel
    exact (RCN122.specialization_natDegree_lt K _ weight L R Q P seed hpos
      (nested_mem_global hbox) hdegree).trans_le (Nat.mul_le_mul_left _ hcard)

end

end ProximityPrize.SubmissionLower.Koala6831MovingSources

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
