import ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs
import ProximityPrize.SubmissionLower.Koala6831MovingFixedRooms
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts
import ProximityPrize.SubmissionLower.Koala6831MovingPartner
import ProximityPrize.SubmissionLower.LowerGeometry
section BP0
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/

namespace ProximityPrize.SubmissionLower.Night6836FlowStages

open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)

theorem room_remaining_caps (roomOrder : ℕ) (remaining incoming source : FlagDegree)
    (hincoming : Below remaining incoming)
    (hsource : Below ((roomOrder + 1) • remaining) source) :
    remaining.all ≤ min incoming.all (source.all / (roomOrder + 1)) ∧
    middle remaining ≤ min (middle incoming) (middle source / (roomOrder + 1)) ∧
    total remaining ≤ min (total incoming) (total source / (roomOrder + 1)) := by
  have hpos : 0 < roomOrder + 1 := Nat.succ_pos _
  refine ⟨le_min hincoming.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.1 ((Nat.le_div_iff_mul_le hpos).2 ?_),
    le_min hincoming.2.2 ((Nat.le_div_iff_mul_le hpos).2 ?_)⟩
  · rw [Nat.mul_comm]
    exact hsource.1
  · rw [Nat.mul_comm, middle, Nat.mul_add]
    exact hsource.2.1
  · rw [Nat.mul_comm, total, Nat.mul_add, Nat.mul_add]
    exact hsource.2.2

def weightGain : ℕ := 19228

def adaptiveBand (source : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget weightGain (total p) (middle p) p.all
    (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel p)

theorem adaptiveBand_antitone (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) : adaptiveBand source q ≤ adaptiveBand source p := by
  have hy : 0 < middle p := by unfold middle; omega
  have ht : 0 < total p := by unfold total; omega
  have hfuel : source.fuel q ≤ source.fuel p := by
    unfold LocatorPhase6800Oracle.SourceNumbers.fuel
    exact min_le_min (Nat.div_le_div_left h.2.2 ht)
      (min_le_min (Nat.div_le_div_left h.2.1 hy) (Nat.div_le_div_left h.1 hs))
  unfold adaptiveBand
  have hsameFuel := powerBandBudget_mono weightGain
    (total q) (middle q) q.all (source.totalCap - total q) (source.middleCap - middle q)
    (source.slopeCap - q.all)
    (total p) (middle p) p.all (source.totalCap - total p) (source.middleCap - middle p)
    (source.slopeCap - p.all) (source.fuel q)
    (Nat.sub_le_sub_left h.2.2 _) (Nat.sub_le_sub_left h.2.1 _)
    (Nat.sub_le_sub_left h.1 _) h.2.2 h.2.1 h.1
  exact hsameFuel.trans (powerBandBudget_mono_fuel _ _ _ _ _ _ _ hfuel)

def adaptiveGate (source : SourceNumbers) (p : FlagDegree) : Prop :=
  adaptiveBand source p < source.gap

theorem adaptiveGate_mono (source : SourceNumbers) {p q : FlagDegree}
    (h : Below p q) (hs : 0 < p.all) (hactive : adaptiveGate source p) :
    adaptiveGate source q :=
  (adaptiveBand_antitone source h hs).trans_lt hactive

end ProximityPrize.SubmissionLower.Night6836FlowStages

end BP0

section BP1
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/

namespace ProximityPrize.SubmissionLower.Night6836FlowSources

open RCN081 RCN156 RCN234 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
open LocatorPhase6800Oracle (SourceNumbers)
open Night6836FlowStages

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

def agreement : ℕ := 181039
def weight : ℕ := 131071
namespace Stage
def numbers : Stage → SourceNumbers
  | .primary => ⟨83491, 444, 99, 22199125⟩
  | .first => ⟨104363, 483, 108, 28544464471015⟩
  | .second => ⟨145000, 1174, 263, 2647315136901138⟩
  | .src394 => ⟨465000, 3729, 837, 412574546369545511⟩
  | .src481 => ⟨1092000, 9668, 2170, 17728861626743347808⟩
  | .src485 => ⟨1750000, 9668, 2170, 33187710199896969808⟩
  | .src700 => ⟨2750000, 69061, 15500, 3700892785384505065315⟩
  | .src701 => ⟨2750000, 69061, 15500, 3700892785384505065315⟩
  | .src702 => ⟨3500000, 69061, 15500, 10337067985315684315315⟩
  | .src703 => ⟨4250000, 69061, 15500, 16973243185246863565315⟩
  | .src704 => ⟨4500000, 69061, 15500, 19185301585223923315315⟩
  | .src705 => ⟨4860000, 69061, 15500, 22370665681190889355315⟩
  | .src706 => ⟨5248800, 69061, 15500, 25810858904835212678515⟩
  | .src707 => ⟨5668704, 69061, 15500, 29526267586371081867571⟩
  | .src708 => ⟨6122200, 69061, 15500, 33538906130995068621115⟩
  | .src709 => ⟨6611976, 69061, 15500, 37872558590623726285579⟩
  | .src710 => ⟨7140934, 69061, 15500, 42552902539163988570541⟩
  | .src711 => ⟨7712209, 69061, 15500, 47607677188951567805266⟩
  | .src712 => ⟨8329185, 69061, 15500, 53066824962488553470530⟩
  | .src713 => ⟨8995520, 69061, 15500, 58962712698283409904595⟩
  | .src714 => ⟨9715162, 69061, 15500, 65330273222588574835033⟩
  | .src715 => ⟨10492375, 69061, 15500, 72207235403474056992940⟩
  | .src716 => ⟨11331765, 69061, 15500, 79634354204901033727150⟩
  | .src717 => ⟨12238306, 69061, 15500, 87655640740795448618449⟩
  | .src718 => ⟨12500000, 69061, 15500, 89971170384489835315315⟩
def multiplicity : Stage → ℕ
  | .primary => 322
  | .first => 350
  | .second => 850
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
  | .primary => 99034
  | .first => 56357
  | .second => 5796
  | .src394 => 41541
  | .src481 => 78572
  | .src485 => 78572
  | .src700 => 55669
  | .src701 => 55669
  | .src702 => 55669
  | .src703 => 55669
  | .src704 => 55669
  | .src705 => 55669
  | .src706 => 55669
  | .src707 => 55669
  | .src708 => 55669
  | .src709 => 55669
  | .src710 => 55669
  | .src711 => 55669
  | .src712 => 55669
  | .src713 => 55669
  | .src714 => 55669
  | .src715 => 55669
  | .src716 => 55669
  | .src717 => 55669
  | .src718 => 55669
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

end ProximityPrize.SubmissionLower.Night6836FlowSources

end BP1

section BP2
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/

namespace ProximityPrize.SubmissionLower.Night6836FlowAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN180 RCN234 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorTwoFactorAvoidance
open LocatorBatchProductRoute LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (SourceNumbers)
open Night6836FlowSources Night6836FlowStages Koala6831Moving

noncomputable section

variable {K : Type} [Field K]
variable {I : Type*} [Fintype I]
local instance movingAdaptiveDecidableEq : DecidableEq K := Classical.decEq K

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) : a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem fuel_terminal (s : SourceNumbers) (f : FlagDegree) (hr : 0 < f.all) :
    s.totalCap - s.fuel f * total f < total f ∨
    s.middleCap - s.fuel f * middle f < middle f ∨
    s.slopeCap - s.fuel f * f.all < f.all := by
  have hy : 0 < middle f := by unfold middle; omega
  have ht : 0 < total f := by unfold total; omega
  unfold LocatorPhase6800Oracle.SourceNumbers.fuel
  by_cases hT : s.totalCap / total f ≤ min (s.middleCap / middle f) (s.slopeCap / f.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total f) ht
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle f ≤ s.slopeCap / f.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle f) hy
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap f.all hr

private theorem stage_box_of_weight_lt (s : Stage) (nodes u₀ u₁ : I → K)
    (v : s.Kernel K nodes u₀ u₁) (newCutoff : ℕ)
    (hweight : wt (contactWeights weight) (s.reconstruct K nodes u₀ u₁ v) < newCutoff) :
    s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K newCutoff weight
      s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap := by
  intro d hd
  have hbox := s.reconstruct_mem_box K nodes u₀ u₁ v hd
  have hweighted := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt hweight
  exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, by simpa only [contact_weight] using hweighted⟩

theorem exists_adaptive_exit_source (s : Stage) (nodes u₀ u₁ : I → K)
    (hcard : Fintype.card I ≤ 262144) (H : MvPolynomial (Fin 4) K)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty) (hfield : A.card < ENat.card K)
    (hr : 0 < (originalCumulativeFlag (regularProduct H A)).all)
    (hfuel : 0 < s.numbers.fuel (originalCumulativeFlag (regularProduct H A)))
    (hgate : adaptiveGate s.numbers (originalCumulativeFlag (regularProduct H A))) :
    ∃ U ⊂ A, ∃ v : s.Kernel K nodes u₀ u₁, ∃ j : ℕ,
      j ≤ s.numbers.fuel (originalCumulativeFlag (regularProduct H A)) ∧
      s.reconstruct K nodes u₀ u₁ v ≠ 0 ∧
      s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K
        (s.cutoff - j * weightGain) weight s.numbers.totalCap s.numbers.middleCap
        s.numbers.slopeCap ∧
      ∀ F ∈ A \ U, ∃ J : MvPolynomial (Fin 4) K,
        s.reconstruct K nodes u₀ u₁ v = F.1 ^ j * J ∧ ¬ F.1 ∣ J := by
  classical
  let P := regularProduct H A
  let f := originalCumulativeFlag P
  let r := s.reconstruct K nodes u₀ u₁
  let U₀ := universalFactors H A r
  have hP : P ≠ 0 := regularProduct_ne_zero H A
  have hrInjective := s.reconstruct_injective K nodes u₀ u₁
  have ⟨hR, hY, hT⟩ := originalCumulativeFlag_cumulative P
  change middle (originalCumulativeFlag P) = wt residualYSWeights P at hY
  change total (originalCumulativeFlag P) = wt residualTotalWeights P at hT
  by_cases hU₀ : U₀ = A
  · have hd : ∀ v : s.Kernel K nodes u₀ u₁, P ∣ r v := by
      intro v
      have hv : regularProduct H U₀ ∣ r v := universalProduct_dvd H A r v
      rwa [hU₀] at hv
    obtain ⟨hq, hproduct, hqbox⟩ := quotientLinear_nested_data s.cutoff weight
      s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap r hrInjective
      (s.reconstruct_mem_box K nodes u₀ u₁) P hP hd
    let q := quotientLinear r P hP hd
    let fuel := s.numbers.fuel f
    let steps := fuel - 1
    have hsteps : steps + 1 = fuel := by
      change fuel - 1 + 1 = fuel
      have hp : 0 < fuel := hfuel
      omega
    let dw := wt (contactWeights weight) P
    let dt := wt residualTotalWeights P
    let dy := wt residualYSWeights P
    let dr := wt residualSWeights P
    let hi := s.cutoff - dw
    let low := hi - weightGain
    let availT := s.numbers.totalCap - dt
    let availY := s.numbers.middleCap - dy
    let availR := s.numbers.slopeCap - dr
    have hband : powerBandBudgetThin weight hi weightGain dw dt dy dr availT availY availR (steps + 1) <
        Module.finrank K (s.Kernel K nodes u₀ u₁) := by
      apply (powerBandBudgetThin_le weight weightGain dw dt dy dr (steps + 1) hi availT availY availR).trans_lt
      rw [hsteps]
      have hg : powerBandBudget weightGain dt dy dr availT availY availR fuel < s.numbers.gap := by
        change adaptiveGate s.numbers f at hgate
        simpa only [adaptiveGate, adaptiveBand, f, hR, hY, hT, dt, dy, dr, fuel, availT, availY, availR]
          using hgate
      exact hg.trans_le (s.finrank_lower_bound K nodes u₀ u₁ hcard)
    have hterm : availT - steps * dt < dt ∨ availY - steps * dy < dy ∨
        availR - steps * dr < dr := by
      have hf := fuel_terminal s.numbers f hr
      change s.numbers.totalCap - fuel * total f < total f ∨
        s.numbers.middleCap - fuel * middle f < middle f ∨
        s.numbers.slopeCap - fuel * f.all < f.all at hf
      have ht : dt = total f := hT.symm
      have hy : dy = middle f := hY.symm
      have hs : dr = f.all := hR.symm
      rw [← hsteps, ← ht, ← hy, ← hs] at hf
      simpa only [availT, availY, availR, Nat.add_mul, Nat.one_mul, Nat.sub_sub, Nat.add_comm] using hf
    obtain ⟨j, U, v, J, hU, hv, hJ, heq, hJbox, hJavoid⟩ :=
      exists_batchExitStage_of_bandBudgetThin_succ steps hi low weight weightGain availT availY availR
        (by decide +kernel) rfl q hq hqbox H A hA hband hterm hfield
    have hsourceEq : r v = P ^ (j.val + 1) * J := by
      rw [hproduct v, ← heq, pow_succ', mul_assoc]
    have hnz : r v ≠ 0 := hsourceEq ▸ mul_ne_zero (pow_ne_zero _ hP) hJ
    have hJweight := (nested_mem_weights hJbox hJ).2.2.2
    have hweight : wt (contactWeights weight) (r v) < s.cutoff - (j.val + 1) * weightGain := by
      have hmul := weightedTotalDegree_mul (contactWeights weight) (P ^ (j.val + 1)) J
        (pow_ne_zero _ hP) hJ
      change wt (contactWeights weight) (P ^ (j.val + 1) * J) = _ at hmul
      rw [hsourceEq, hmul]
      change wt (contactWeights weight) (P ^ (j.val + 1)) + wt (contactWeights weight) J < _
      rw [wt_pow_eq _ P hP]
      change wt (contactWeights weight) J < s.cutoff - dw - weightGain -
        j.val * weightGain - j.val * dw at hJweight
      change (j.val + 1) * dw + wt (contactWeights weight) J < _
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hpow : j.val + 1 ≤ fuel := by have hp := j.isLt; omega
    refine ⟨U, hU, v, j.val + 1, hpow, hnz,
      stage_box_of_weight_lt s nodes u₀ u₁ v _ hweight, ?_⟩
    intro F hF
    have hFA := (Finset.mem_sdiff.mp hF).1
    refine ⟨regularCofactor H A F ^ (j.val + 1) * J,
      hsourceEq.trans (regularProduct_power_split H A F hFA _ J), ?_⟩
    exact ((RCN167.positiveRFactors_spec H F.1 F.2).1.isRelPrime_iff_not_dvd).mp
      (regularFactor_isRelPrime_liftedHelper H A F hFA _ J (hJavoid F hF))
  · have hU₀sub := universalFactors_subset H A r
    have hstrict : U₀ ⊂ A := (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hU₀⟩
    have hremoved : (A \ U₀).Nonempty := Finset.sdiff_nonempty.mpr hstrict.not_ge
    have hc : (A \ U₀).card < ENat.card K := by
      have h := Finset.card_le_card (Finset.sdiff_subset (s := A) (t := U₀))
      exact (by exact_mod_cast h : ((A \ U₀).card : ENat) ≤ A.card).trans_lt hfield
    obtain ⟨v, hv, hav⟩ := exists_avoiding_nonuniversal_factors (A \ U₀) hremoved r
      (fun F => F.1) (fun F hF hdiv => (Finset.mem_sdiff.mp hF).2
        ((mem_universalFactors H A r F).mpr ⟨(Finset.mem_sdiff.mp hF).1, hdiv⟩)) hc
    have hnz : r v ≠ 0 := fun h => hv (hrInjective (h.trans (map_zero r).symm))
    refine ⟨U₀, hstrict, v, 0, Nat.zero_le _, hnz, ?_, fun F hF => ?_⟩
    · simpa only [Nat.zero_mul, Nat.sub_zero] using s.reconstruct_mem_box K nodes u₀ u₁ v
    · exact ⟨r v, by rw [pow_zero, one_mul], hav F hF⟩

theorem exists_adaptive_exit_partners {p : ℕ} [CharP K p]
    (s : Stage) (B : FlowData K) (nodes u₀ u₁ normalized : I → K)
    (hcard : Fintype.card I ≤ 262144) (hchar : s.numbers.slopeCap < p)
    (h₀ : ∀ i, B.d0.eval (nodes i) * u₀ i + B.c0.eval (nodes i) =
      B.a0.eval (nodes i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (nodes i) * u₁ i + B.c1.eval (nodes i) =
      B.a1.eval (nodes i) * normalized i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9614)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9614)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hA : A.Nonempty) (hfield : A.card < ENat.card K)
    (hr : 0 < (originalCumulativeFlag (regularProduct H A)).all)
    (hfuel : 0 < s.numbers.fuel (originalCumulativeFlag (regularProduct H A)))
    (hgate : adaptiveGate s.numbers (originalCumulativeFlag (regularProduct H A)))
    (htrans : ∀ F ∈ A, ¬ F.1 ∣ B.flow F.1) :
    ∃ U ⊂ A, ∀ F ∈ A \ U, ∃ Q : MvPolynomial (Fin 4) K,
      IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
        (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
      ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q := by
  obtain ⟨U, hU, v, j, hj, hv, hb, hexact⟩ :=
    exists_adaptive_exit_source s nodes u₀ u₁ hcard H A hA hfield hr hfuel hgate
  have hjSlope : j ≤ s.numbers.slopeCap := by
    let f := originalCumulativeFlag (regularProduct H A)
    change j ≤ s.numbers.fuel f at hj
    have hf : s.numbers.fuel f ≤ s.numbers.slopeCap / f.all :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact hj.trans (hf.trans (Nat.div_le_self _ _))
  have hroom : (s.cutoff - j * weightGain) + j * (2 * 9614) ≤ s.multiplicity * agreement := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hv
    have hpositive := (hb hd).2.2.2
    have hle : j * weightGain ≤ s.cutoff := by omega
    change s.cutoff - j * weightGain + j * weightGain ≤ s.multiplicity * agreement
    rw [Nat.sub_add_cancel hle]
    exact Nat.sub_le _ _
  refine ⟨U, hU, fun F hF => ?_⟩
  have hFA := (Finset.mem_sdiff.mp hF).1
  obtain ⟨J, heq, hJ⟩ := hexact F hF
  have hb' := heq ▸ hb
  have hc : ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i)
      s.multiplicity (F.1 ^ j * J) := by
    intro i
    rw [← heq]
    exact s.reconstruct_contact K nodes u₀ u₁ v i
  obtain ⟨Q, hrel, hbox, hcontact⟩ := B.exists_contact_partner_of_room nodes u₀ u₁ normalized
    h₀ h₁ (RCN167.positiveRFactors_spec H F.1 F.2).1 hJ (htrans F hFA)
    (hjSlope.trans_lt hchar) (by decide +kernel) (by decide +kernel) hden hminor hroom hb' hc
  refine ⟨Q, hrel, ?_, hcontact⟩
  intro d hd
  have h := hbox hd
  exact ⟨h.1.trans (Nat.add_le_add_left hjSlope _), h.2⟩

theorem exhaust_finset_stage {α : Type*} [DecidableEq α] (initial : Finset α)
    (active : Finset α → Prop) (covered : α → Prop)
    (step : ∀ S ⊆ initial, S.Nonempty → active S →
      ∃ U ⊂ S, ∀ a ∈ S \ U, covered a) :
    ∃ U ⊆ initial, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ initial \ U, covered a := by
  classical
  have hfinish (S : Finset α) (hsub : S ⊆ initial) :
      ∃ U ⊆ S, (U = ∅ ∨ ¬ active U) ∧ ∀ a ∈ S \ U, covered a := by
    induction S using Finset.strongInductionOn
    rename_i S ih
    by_cases hact : S.Nonempty ∧ active S
    · obtain ⟨V, hV, hcovered⟩ := step S hsub hact.1 hact.2
      obtain ⟨U, hUV, hstop, hrec⟩ := ih V hV (hV.subset.trans hsub)
      refine ⟨U, hUV.trans hV.subset, hstop, fun a ha => ?_⟩
      obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
      by_cases haV : a ∈ V
      · exact hrec a (Finset.mem_sdiff.mpr ⟨haV, haU⟩)
      · exact hcovered a (Finset.mem_sdiff.mpr ⟨haS, haV⟩)
    · refine ⟨S, fun _ h => h, ?_, fun a ha => ?_⟩
      · by_cases hz : S.Nonempty
        · exact Or.inr (fun hf => hact ⟨hz, hf⟩)
        · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hz)
      · exact ((Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp ha).1).elim
  exact hfinish initial (fun _ h => h)

end

end ProximityPrize.SubmissionLower.Night6836FlowAdaptive

end BP2

section BP3
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the 68.32 work of Bome2017, after Lucieno and BitWonka. New 68.33 source and variable input caps. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/

namespace ProximityPrize.SubmissionLower.Night6836FlowAdaptive

open RCN081 RCN095 RCN130 RCN156 RCN234 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Night6836FlowSources Night6836FlowStages Koala6831Moving

noncomputable section

variable {K : Type} [Field K]
variable {I : Type*} [Fintype I]
local instance movingScheduleDecidableEq : DecidableEq K := Classical.decEq K

abbrev aggregateFlag (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) : FlagDegree :=
  originalCumulativeFlag (regularProduct H A)

theorem aggregateFlag_mono (H : MvPolynomial (Fin 4) K)
    {U A : Finset (RegularIndex H)} (hUA : U ⊆ A) :
    Below (aggregateFlag H U) (aggregateFlag H A) := by
  have hd : regularProduct H U ∣ regularProduct H A :=
    Finset.prod_dvd_prod_of_subset U A (fun F => F.1) hUA
  have hn := regularProduct_ne_zero H A
  have ⟨hrU, hyU, htU⟩ := originalCumulativeFlag_cumulative (regularProduct H U)
  have ⟨hrA, hyA, htA⟩ := originalCumulativeFlag_cumulative (regularProduct H A)
  refine ⟨?_, ?_, ?_⟩
  · rw [aggregateFlag, aggregateFlag, hrU, hrA]
    exact weightedTotalDegree_le_of_dvd residualSWeights _ _ hd hn
  · change middle (originalCumulativeFlag (regularProduct H U)) ≤
      middle (originalCumulativeFlag (regularProduct H A))
    unfold middle
    rw [hyU, hyA]
    exact weightedTotalDegree_le_of_dvd residualYSWeights _ _ hd hn
  · change total (originalCumulativeFlag (regularProduct H U)) ≤
      total (originalCumulativeFlag (regularProduct H A))
    unfold total
    rw [htU, htA]
    exact weightedTotalDegree_le_of_dvd residualTotalWeights _ _ hd hn

theorem aggregateFlag_pos (H : MvPolynomial (Fin 4) K)
    {A : Finset (RegularIndex H)} (hA : A.Nonempty) : 0 < (aggregateFlag H A).all := by
  obtain ⟨F, hF⟩ := hA
  have hFpos := regularCumulativeFlag_positive H F
  have hd : F.1 ∣ regularProduct H A :=
    ⟨regularCofactor H A F, (regularFactor_mul_cofactor H A F hF).symm⟩
  rw [show (regularCumulativeFlag H F).all = wt residualSWeights F.1 from
    (originalCumulativeFlag_cumulative F.1).1] at hFpos
  rw [aggregateFlag, (originalCumulativeFlag_cumulative (regularProduct H A)).1]
  exact hFpos.trans_le (weightedTotalDegree_le_of_dvd residualSWeights _ _ hd
    (regularProduct_ne_zero H A))

def postRoomCap : FlagDegree := ⟨15213, 108, 30⟩

private theorem fuel_pos (s : Stage) (f : FlagDegree)
    (hr : 0 < f.all) (hcap : Below f ⟨s.numbers.totalCap - s.numbers.middleCap,
      s.numbers.middleCap - s.numbers.slopeCap,s.numbers.slopeCap⟩) : 0 < s.numbers.fuel f := by
  have hy : 0 < middle f := by unfold middle; omega
  have ht : 0 < total f := by unfold total; omega
  have hsT : total (⟨s.numbers.totalCap-s.numbers.middleCap,s.numbers.middleCap-s.numbers.slopeCap,s.numbers.slopeCap⟩ : FlagDegree) ≤ s.numbers.totalCap := by cases s <;> decide +kernel
  have hsY : middle (⟨s.numbers.totalCap-s.numbers.middleCap,s.numbers.middleCap-s.numbers.slopeCap,s.numbers.slopeCap⟩ : FlagDegree) ≤ s.numbers.middleCap := by cases s <;> decide +kernel
  have hsR : s.numbers.slopeCap ≤ s.numbers.slopeCap := le_rfl
  unfold LocatorPhase6800Oracle.SourceNumbers.fuel
  apply Nat.lt_of_succ_le
  apply le_min
  · exact (Nat.le_div_iff_mul_le ht).2 (by
      simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.2.2.trans hsT)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hy).2 (by
        simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.2.1.trans hsY)
    · exact (Nat.le_div_iff_mul_le hr).2 (by
        simpa only [Nat.succ_mul, Nat.zero_mul, Nat.zero_add] using hcap.1.trans hsR)

private theorem below_trans {a b c : FlagDegree} (hab : Below a b) (hbc : Below b c) : Below a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩

structure ExhaustedPass (s : Stage) (nodes u₀ u₁ : I → K)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) where
  residue : Finset (RegularIndex H)
  subset_incoming : residue ⊆ A
  stopped : residue = ∅ ∨ ¬ adaptiveGate s.numbers (aggregateFlag H residue)
  partners : ∀ F ∈ A \ residue, ∃ Q : MvPolynomial (Fin 4) K,
    IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
    ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q

theorem exists_exhausted_adaptive_pass [CharP K 2130706433]
    (s : Stage) (B : FlowData K) (nodes u₀ u₁ normalized : I → K)
    (hcard : Fintype.card I ≤ 262144)
    (h₀ : ∀ i, B.d0.eval (nodes i) * u₀ i + B.c0.eval (nodes i) =
      B.a0.eval (nodes i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (nodes i) * u₁ i + B.c1.eval (nodes i) =
      B.a1.eval (nodes i) * normalized i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9614)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9614)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (hfield : A.card < ENat.card K) (hcap : Below (aggregateFlag H A) ⟨s.numbers.totalCap - s.numbers.middleCap,s.numbers.middleCap - s.numbers.slopeCap,s.numbers.slopeCap⟩)
    (htrans : ∀ F ∈ A, ¬ F.1 ∣ B.flow F.1) :
    Nonempty (ExhaustedPass s nodes u₀ u₁ H A) := by
  let active (U : Finset (RegularIndex H)) := adaptiveGate s.numbers (aggregateFlag H U)
  let pays (F : RegularIndex H) := ∃ Q : MvPolynomial (Fin 4) K,
    IsRelPrime F.1 Q ∧ Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + s.numbers.slopeCap) s.numbers.middleCap s.numbers.slopeCap ∧
    ∀ i, ContactOrderBridge.ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity Q
  have hchar : s.numbers.slopeCap < 2130706433 := by cases s <;> decide +kernel
  obtain ⟨U, hsub, hstop, hpays⟩ := exhaust_finset_stage A active pays (fun R hRA hR hactive => by
    have hsmall : R.card < ENat.card K := by
      have h := Finset.card_le_card hRA
      exact (by exact_mod_cast h : (R.card : ENat) ≤ A.card).trans_lt hfield
    have hr := aggregateFlag_pos H hR
    exact exists_adaptive_exit_partners s B nodes u₀ u₁ normalized hcard hchar h₀ h₁ hden hminor
      H R hR hsmall hr (fuel_pos s _ hr
        (below_trans (aggregateFlag_mono H hRA) hcap)) hactive (fun F hF => htrans F (hRA hF)))
  exact ⟨⟨U, hsub, hstop, hpays⟩⟩

end

#print axioms exists_exhausted_adaptive_pass
end ProximityPrize.SubmissionLower.Night6836FlowAdaptive

end BP3

section BP4
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/

namespace ProximityPrize.SubmissionLower.Night6836FlowPaid

open RCN095 RCN130 RCN275 LocatorFactorAggregate
open Koala6831Moving Koala6831MovingLedger Night6836FlowSources Koala6831MovingPairIncidence

def agreementScale : ℕ := 9046156752

theorem agreementScale_eq : agreementScale = 181039 * (181039 - 131071) := by decide +kernel
theorem agreementScale_pos : 0 < agreementScale := by decide +kernel

def primaryIncoming : FlagDegree := ⟨83047, 345, 99⟩


def stageSupport (incoming : FlagDegree) (hpos : 0 < incoming.all) :
    ResidualSupportParameters where
  s := incoming.all
  ys := max 2 (middle incoming)
  total := max 2 (total incoming)
  one_le_s := hpos
  s_le_ys := (Nat.le_add_left _ _).trans (le_max_right _ _)
  ys_le_total := max_le_max_left _ (by unfold middle total; omega)
  two_le_ys := le_max_left _ _

def stagePartnerFlag (s : Stage) (gain : ℕ) : FlagDegree :=
  flagFromCaps (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap

theorem stagePartnerFlag_cumulative (s : Stage) (gain : ℕ) :
    (stagePartnerFlag s gain).all = s.numbers.slopeCap ∧
    middle (stagePartnerFlag s gain) = s.numbers.middleCap ∧
    total (stagePartnerFlag s gain) = s.numbers.totalCap + gain :=
  flagFromCaps_cumulative _ _ _ (by cases s <;> decide +kernel)
    ((show s.numbers.middleCap ≤ s.numbers.totalCap by cases s <;> decide +kernel).trans
      (Nat.le_add_right _ _))

def stageScaledCut (incoming : FlagDegree) (hpos : 0 < incoming.all) : FlagDegree :=
  scaledPairFlag (stageSupport incoming hpos) 262144 131071 181039 81105

def stagePrice (incoming : FlagDegree) (hpos : 0 < incoming.all) (s : Stage) (gain : ℕ) : ℕ :=
  flagMixed incoming (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale

end ProximityPrize.SubmissionLower.Night6836FlowPaid

end BP4

section BP5
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/


namespace ProximityPrize.SubmissionLower.Night6836FlowPaid

open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN156 RCN167 RCN234 RCN238 RCN243 RCN266 RCN275 RCN313 RCN319
open Koala6831Moving Night6836FlowAdaptive Koala6831MovingCarrierPairs Night6836FlowSources
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero regularCofactor regularFactor_mul_cofactor)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
open Night6836FlowStages (adaptiveGate adaptiveGate_mono)

noncomputable section

variable {K : Type} [Field K]

export Koala6831MovingPaid (regularFiber mem_regularFiber regularFiber_subset)

private theorem surface_in_partner_flag (s : Stage) (gain : ℕ) {cutoff : ℕ}
    {Q : P4 K} (hQ : Q ≠ 0)
    (hbox : Q ∈ nestedCoefficientBox K cutoff weight
      (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap) :
    PolynomialInFlag (stagePartnerFlag s gain) (surfaceMap (polynomialEmbedding K) Q) := by
  obtain ⟨hT, hY, hR, _⟩ := nested_mem_weights hbox hQ
  obtain ⟨hmapR, hmapY, hmapT⟩ := surfaceMap_nested_weights_le (polynomialEmbedding K) Q
  let D := surfaceMap (polynomialEmbedding K) Q
  obtain ⟨hD₁, hD₂, hD₃⟩ := surfaceCumulativeFlag_cumulative D
  obtain ⟨h₁, h₂, h₃⟩ := stagePartnerFlag_cumulative s gain
  intro d hd
  have hm := polynomialIn_surfaceCumulativeFlag D d hd
  rw [InFlag, hD₃, hD₂, hD₁] at hm
  change d 1 ≤ (stagePartnerFlag s gain).all ∧
    d 0 + d 1 ≤ middle (stagePartnerFlag s gain) ∧
    d 0 + d 1 + d 2 ≤ total (stagePartnerFlag s gain)
  rw [h₁, h₂, h₃]
  exact ⟨hm.1.trans (hmapR.trans hR), hm.2.1.trans (hmapY.trans hY), hm.2.2.trans (hmapT.trans hT)⟩

private theorem stage_support_of_factor {H : P4 K} {A : Finset (RegularIndex H)}
    {F : RegularIndex H} (hF : F ∈ A) (incoming : FlagDegree) (hpos : 0 < incoming.all)
    (hfit : Below (aggregateFlag H A) incoming) :
    ResidualSupportData (stageSupport incoming hpos) F.1 := by
  have hdiv : F.1 ∣ regularProduct H A :=
    ⟨regularCofactor H A F, (regularFactor_mul_cofactor H A F hF).symm⟩
  have h := contactFlag_below_of_dvd (regularProduct_ne_zero H A) hdiv
  refine ⟨h.1.trans hfit.1, ?_, ?_⟩
  · change _ ≤ max 2 (middle incoming)
    rw [← contactFlag_middle]
    exact (h.2.1.trans hfit.2.1).trans (le_max_right _ _)
  · change _ ≤ max 2 (total incoming)
    rw [← contactFlag_total]
    exact (h.2.2.trans hfit.2.2).trans (le_max_right _ _)

private theorem stage_support_small (incoming : FlagDegree) (hpos : 0 < incoming.all)
    (hcap : Below incoming primaryIncoming) (s : Stage) (gain : ℕ) :
    (stageSupport incoming hpos).total < 2130706433 ∧
      middle (stagePartnerFlag s gain) * (stageSupport incoming hpos).s +
        (stageSupport incoming hpos).ys * (stagePartnerFlag s gain).all < 2130706433 := by
  have hT : (stageSupport incoming hpos).total ≤ 83491 :=
    max_le (by decide +kernel) (hcap.2.2.trans_eq (by decide +kernel))
  have hY : (stageSupport incoming hpos).ys ≤ 444 :=
    max_le (by decide +kernel) (hcap.2.1.trans_eq (by decide +kernel))
  have hR : (stageSupport incoming hpos).s ≤ 99 := hcap.1
  have hy : middle (stagePartnerFlag s gain) ≤ 100000 := by
    rw [(stagePartnerFlag_cumulative s gain).2.1]
    cases s <;> decide +kernel
  have hr : (stagePartnerFlag s gain).all ≤ 20000 := by
    rw [(stagePartnerFlag_cumulative s gain).1]
    cases s <;> decide +kernel
  exact ⟨hT.trans_lt (by decide +kernel),
    (Nat.add_le_add (Nat.mul_le_mul hy hR) (Nat.mul_le_mul hY hr)).trans_lt (by decide +kernel)⟩

theorem regularFiber_le_paid_factor [CharP K 2130706433]
    (H : P4 K) (A : Finset (RegularIndex H)) (F : RegularIndex H) (hF : F ∈ A)
    (incoming : FlagDegree) (hpos : 0 < incoming.all) (hfit : Below (aggregateFlag H A) incoming)
    (hcap : Below incoming primaryIncoming) (s : Stage) (gain : ℕ)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81105)
    (Q : P4 K) (hrel : IsRelPrime F.1 Q)
    (hbox : Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0) :
    (regularFiber H Γ selected F).card ≤
      flagMixed (contactFlag F.1) (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale := by
  classical
  let fiber := regularFiber H Γ selected F
  obtain ⟨hirr, _, hr⟩ := positiveRFactors_spec H F.1 F.2
  have hnF : ¬ F.1 ∣ Q := fun hd => hirr.not_isUnit (hrel dvd_rfl hd)
  have hnQ : Q ≠ 0 := fun hz => hnF (hz ▸ dvd_zero _)
  have hData := stage_support_of_factor hF incoming hpos hfit
  have ⟨hT, hmix⟩ := stage_support_small incoming hpos hcap s gain
  have hRchar : F.1.degreeOf 2 < 2130706433 :=
    (hData.coordinate_bounds.2.1.trans ((stageSupport incoming hpos).s_le_ys.trans
      (stageSupport incoming hpos).ys_le_total)).trans_lt hT
  have hsize : agreement ≤ nodes.card := by rw [hnodes]; decide +kernel
  have hsub : fiber ⊆ Γ := regularFiber_subset H Γ selected F
  have hcount := regular_carrier_seed_card_mul_le (stageSupport incoming hpos) F.1 Q hirr hnF
    2130706433 hr hRchar hData (stagePartnerFlag s gain) (surface_in_partner_flag s gain hnQ hbox)
    selected fiber nodes x u₀ u₁ hx weight agreement 81105
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hsize hT hmix
    (fun γ hγ => hdegree γ (hsub hγ))
    (fun γ hγ => (mem_regularFiber.mp hγ).2.1) (fun γ hγ => hsolution γ (hsub hγ))
    (fun γ hγ => (mem_regularFiber.mp hγ).2.2) (fun γ hγ => hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ fiber weight 81105 hsub hnoPencil)
  apply (Nat.le_div_iff_mul_le agreementScale_pos).mpr
  rw [hnodes] at hcount
  rw [show weight = 131071 by decide +kernel, show agreement = 181039 by decide +kernel] at hcount
  simpa only [agreementScale_eq, stageScaledCut, fiber] using hcount

theorem paid_union_le_stagePrice
    (H : P4 K) (A U : Finset (RegularIndex H)) (hUA : U ⊆ A)
    (Γ : Finset K) (selected : K → Polynomial K) (incoming : FlagDegree)
    (hpos : 0 < incoming.all) (hfit : Below (aggregateFlag H A) incoming) (s : Stage) (gain : ℕ)
    (hcount : ∀ F ∈ U, (regularFiber H Γ selected F).card ≤
      flagMixed (contactFlag F.1) (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale) :
    (U.biUnion (regularFiber H Γ selected)).card ≤ stagePrice incoming hpos s gain := by
  classical
  let right := stagePartnerFlag s gain
  let cut := stageScaledCut incoming hpos
  apply (Nat.le_div_iff_mul_le agreementScale_pos).mpr
  have hsum : (∑ F ∈ U, flagMixed (contactFlag F.1) right cut) =
      flagMixed (aggregateFlag H U) right cut := by
    change _ = flagMixed (contactFlag (regularProduct H U)) right cut
    rw [contactFlag_regularProduct]
    simp only [mixed_expansion, sumFlag_all, sumFlag_middle, sumFlag_total,
      Finset.sum_add_distrib, Finset.mul_sum]
  calc
    _ ≤ (∑ F ∈ U, (regularFiber H Γ selected F).card) * agreementScale :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ F ∈ U, (regularFiber H Γ selected F).card * agreementScale := Finset.sum_mul _ _ _
    _ ≤ ∑ F ∈ U, flagMixed (contactFlag F.1) right cut :=
      Finset.sum_le_sum fun F hF => (Nat.le_div_iff_mul_le agreementScale_pos).mp (hcount F hF)
    _ = _ := hsum
    _ ≤ _ := mixed_mono_first
      ⟨(aggregateFlag_mono H hUA).1.trans hfit.1,
       (aggregateFlag_mono H hUA).2.1.trans hfit.2.1,
       (aggregateFlag_mono H hUA).2.2.trans hfit.2.2⟩ right cut

end

#print axioms regularFiber_le_paid_factor
#print axioms paid_union_le_stagePrice
end ProximityPrize.SubmissionLower.Night6836FlowPaid

end BP5
