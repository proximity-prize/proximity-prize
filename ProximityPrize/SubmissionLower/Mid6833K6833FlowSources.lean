/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Mid6833K6833FlowStages

namespace ProximityPrize.SubmissionLower.K6833FlowSources

open RCN081 RCN156 RCN234 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
open LocatorPhase6800Oracle (SourceNumbers)
open K6833FlowStages

noncomputable section

inductive Stage where
  | primary
  | first
  | second
  | src394
  | src481
  | src485
  | src607
  | src608
  | src609
  | src610
  | src611
  | src612
  | src613
  | src614
  | src615
  | src616
  | src617

def agreement : ℕ := 181068
def weight : ℕ := 131071
namespace Stage
def numbers : Stage → SourceNumbers
  | .primary => ⟨45384, 440, 98, 735140208⟩
  | .first => ⟨45500, 483, 108, 6039609738613⟩
  | .second => ⟨115000, 1381, 310, 3995010826515785⟩
  | .src394 => ⟨465000, 4144, 930, 685794069637265960⟩
  | .src481 => ⟨910000, 9670, 2170, 16875700043383662715⟩
  | .src485 => ⟨1750000, 9670, 2170, 39788501729084862715⟩
  | .src607 => ⟨2250000, 69072, 15500, 2325018269281409525207⟩
  | .src608 => ⟨2750000, 69072, 15500, 7438235100587240525207⟩
  | .src609 => ⟨3500000, 69072, 15500, 15108060347545987025207⟩
  | .src610 => ⟨4250000, 69072, 15500, 22777885594504733525207⟩
  | .src611 => ⟨5250000, 69072, 15500, 33004319257116395525207⟩
  | .src612 => ⟨5750000, 69072, 15500, 38117536088422226525207⟩
  | .src613 => ⟨6500000, 69072, 15500, 45787361335380973025207⟩
  | .src614 => ⟨7750000, 69072, 15500, 58570403413645550525207⟩
  | .src615 => ⟨9000000, 69072, 15500, 71353445491910128025207⟩
  | .src616 => ⟨10750000, 69072, 15500, 89249704401480536525207⟩
  | .src617 => ⟨12500000, 69072, 15500, 107145963311050945025207⟩

def multiplicity : Stage → ℕ
  | .primary => 319
  | .first => 350
  | .second => 1000
  | .src394 => 3000
  | .src481 => 7000
  | .src485 => 7000
  | .src607 => 50000
  | .src608 => 50000
  | .src609 => 50000
  | .src610 => 50000
  | .src611 => 50000
  | .src612 => 50000
  | .src613 => 50000
  | .src614 => 50000
  | .src615 => 50000
  | .src616 => 50000
  | .src617 => 50000
def room (_ : Stage) : ℕ := 0

def cutoff (s : Stage) : ℕ := s.multiplicity * agreement - s.room

def roomOrder (s : Stage) : ℕ := s.room / weightGain

theorem room_cutoff (s : Stage) :
    s.cutoff + s.roomOrder * weightGain ≤ s.multiplicity * agreement := by
  cases s <;> decide +kernel

private def remainder : Stage → ℕ
  | .primary => 89452
  | .first => 66507
  | .second => 58949
  | .src394 => 45776
  | .src481 => 19430
  | .src485 => 19430
  | .src607 => 63888
  | .src608 => 63888
  | .src609 => 63888
  | .src610 => 63888
  | .src611 => 63888
  | .src612 => 63888
  | .src613 => 63888
  | .src614 => 63888
  | .src615 => 63888
  | .src616 => 63888
  | .src617 => 63888

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

end ProximityPrize.SubmissionLower.K6833FlowSources
