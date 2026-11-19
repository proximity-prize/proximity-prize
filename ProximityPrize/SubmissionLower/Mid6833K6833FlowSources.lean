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
  | src700
  | src701
  | src702
  | src703
  | src704
  | src705
  | src706
  | src707
  | src708
  | src709
  | src710
  | src711
  | src712
  | src713
  | src714
  | src715
  | src716
  | src717
  | src718

def agreement : ℕ := 181049
def weight : ℕ := 131071
namespace Stage
def numbers : Stage → SourceNumbers
  | .primary => ⟨65864, 440, 98, 6850239⟩
  | .first => ⟨81900, 483, 108, 25135885764713⟩
  | .second => ⟨138000, 1118, 251, 2380786624169709⟩
  | .src394 => ⟨465000, 3729, 837, 447260495079706511⟩
  | .src481 => ⟨1092000, 9669, 2170, 19146448191765718200⟩
  | .src485 => ⟨1750000, 9669, 2170, 35463691211194888200⟩
  | .src700 => ⟨2250000, 69065, 15500, 327832668981794321295⟩
  | .src701 => ⟨2750000, 69065, 15500, 4989556105393896821295⟩
  | .src702 => ⟨3500000, 69065, 15500, 11982141260012050571295⟩
  | .src703 => ⟨4250000, 69065, 15500, 18974726414630204321295⟩
  | .src704 => ⟨4500000, 69065, 15500, 21305588132836255571295⟩
  | .src705 => ⟨4860000, 69065, 15500, 24662029007052969371295⟩
  | .src706 => ⟨5248800, 69065, 15500, 28286985151207020275295⟩
  | .src707 => ⟨5668704, 69065, 15500, 32201937786893395251615⟩
  | .src708 => ⟨6122200, 69065, 15500, 36430083649931680922295⟩
  | .src709 => ⟨6611976, 69065, 15500, 40996484165516028750375⟩
  | .src710 => ⟨7140934, 69065, 15500, 45928195976471374578765⟩
  | .src711 => ⟨7712209, 69065, 15500, 51254448088744022290140⟩
  | .src712 => ⟨8329185, 69065, 15500, 57006791046551608994220⟩
  | .src713 => ⟨8995520, 69065, 15500, 63219330018554925632895⟩
  | .src714 => ⟨9715162, 69065, 15500, 69928873973007882167505⟩
  | .src715 => ⟨10492375, 69065, 15500, 77175178087376201008170⟩
  | .src716 => ⟨11331765, 69065, 15500, 85001186157956110443120⟩
  | .src717 => ⟨12238306, 69065, 15500, 93453273009493038068025⟩
  | .src718 => ⟨12500000, 69065, 15500, 95893163115429895571295⟩

def multiplicity : Stage → ℕ
  | .primary => 319
  | .first => 350
  | .second => 810
  | .src394 => 2700
  | .src481 => 7000
  | .src485 => 7000
  | .src700 => 50000
  | .src701 => 50000
  | .src702 => 50000
  | .src703 => 50000
  | .src704 => 50000
  | .src705 => 50000
  | .src706 => 50000
  | .src707 => 50000
  | .src708 => 50000
  | .src709 => 50000
  | .src710 => 50000
  | .src711 => 50000
  | .src712 => 50000
  | .src713 => 50000
  | .src714 => 50000
  | .src715 => 50000
  | .src716 => 50000
  | .src717 => 50000
  | .src718 => 50000
def room (_ : Stage) : ℕ := 0

def cutoff (s : Stage) : ℕ := s.multiplicity * agreement - s.room

def roomOrder (s : Stage) : ℕ := s.room / weightGain

theorem room_cutoff (s : Stage) :
    s.cutoff + s.roomOrder * weightGain ≤ s.multiplicity * agreement := by
  cases s <;> decide +kernel

private def remainder : Stage → ℕ
  | .primary => 83391
  | .first => 59857
  | .second => 112312
  | .src394 => 68541
  | .src481 => 17501
  | .src485 => 17501
  | .src700 => 31385
  | .src701 => 31385
  | .src702 => 31385
  | .src703 => 31385
  | .src704 => 31385
  | .src705 => 31385
  | .src706 => 31385
  | .src707 => 31385
  | .src708 => 31385
  | .src709 => 31385
  | .src710 => 31385
  | .src711 => 31385
  | .src712 => 31385
  | .src713 => 31385
  | .src714 => 31385
  | .src715 => 31385
  | .src716 => 31385
  | .src717 => 31385
  | .src718 => 31385

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
