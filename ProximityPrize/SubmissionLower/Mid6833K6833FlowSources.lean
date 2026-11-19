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

def agreement : ℕ := 181059
def weight : ℕ := 131071
namespace Stage
def numbers : Stage → SourceNumbers
  | .primary => ⟨53215, 440, 98, 374865348⟩
  | .first => ⟨68250, 483, 108, 23840157867613⟩
  | .second => ⟨138000, 1243, 279, 3665517527719950⟩
  | .src394 => ⟨465000, 3729, 837, 481946443789867511⟩
  | .src481 => ⟨1092000, 9669, 2170, 20564155566462968200⟩
  | .src485 => ⟨1750000, 9669, 2170, 37739866477992138200⟩
  | .src700 => ⟨2250000, 69069, 15500, 1378953682056338188955⟩
  | .src701 => ⟨2750000, 69069, 15500, 6278298503073855688955⟩
  | .src702 => ⟨3500000, 69069, 15500, 13627315734600131938955⟩
  | .src703 => ⟨4250000, 69069, 15500, 20976332966126408188955⟩
  | .src704 => ⟨4500000, 69069, 15500, 23426005376635166938955⟩
  | .src705 => ⟨4860000, 69069, 15500, 26953533647767779538955⟩
  | .src706 => ⟨5248800, 69069, 15500, 30763264180591001146955⟩
  | .src707 => ⟨5668704, 69069, 15500, 34877773156040080483595⟩
  | .src708 => ⟨6122200, 69069, 15500, 39321439713944400715955⟩
  | .src709 => ⟨6611976, 69069, 15500, 44120602732061752018115⟩
  | .src710 => ⟨7140934, 69069, 15500, 49303698007733320061645⟩
  | .src711 => ⟨7712209, 69069, 15500, 54901444432986884681270⟩
  | .src712 => ⟨8329185, 69069, 15500, 60947000773571092435430⟩
  | .src713 => ⟨8995520, 69069, 15500, 67476210636196507482155⟩
  | .src714 => ⟨9715162, 69069, 15500, 74527759247569884139625⟩
  | .src715 => ⟨10492375, 69069, 15500, 82143428220324859797080⟩
  | .src716 => ⟨11331765, 69069, 15500, 90368350318952647825730⟩
  | .src717 => ⟨12238306, 69069, 15500, 99251264225732730489665⟩
  | .src718 => ⟨12500000, 69069, 15500, 101815522512915446938955⟩

def multiplicity : Stage → ℕ
  | .primary => 319
  | .first => 350
  | .second => 900
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
  | .primary => 86581
  | .first => 63357
  | .second => 31847
  | .src394 => 95541
  | .src481 => 87501
  | .src485 => 87501
  | .src700 => 7101
  | .src701 => 7101
  | .src702 => 7101
  | .src703 => 7101
  | .src704 => 7101
  | .src705 => 7101
  | .src706 => 7101
  | .src707 => 7101
  | .src708 => 7101
  | .src709 => 7101
  | .src710 => 7101
  | .src711 => 7101
  | .src712 => 7101
  | .src713 => 7101
  | .src714 => 7101
  | .src715 => 7101
  | .src716 => 7101
  | .src717 => 7101
  | .src718 => 7101

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
