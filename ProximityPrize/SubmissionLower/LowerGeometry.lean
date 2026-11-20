import ProximityPrize.SubmissionLower.LowerFoundation
import ProximityPrize.SubmissionLower.Koala6844VirtualShortBasis
set_option linter.all false

section Compact_PackedLocatorTail

section PackedLocator_ChainAmort

open Finset

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainAmort

end ChainAmort

namespace ChainGroupMaj
open ProximityPrize.SubmissionLower.RCN260 ProximityPrize.SubmissionLower.RCN294

end ChainGroupMaj

end PackedLocator_ChainAmort

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorNestedProjection
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN156 RCN180 RCN234
noncomputable section
variable {K:Type*} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def nestedExponents (D w T YS S:ℕ):Set (Fin 4 →₀ ℕ) :=
  {d | d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧ d 2 ≤ S ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D}
def nestedCoefficientBox (K:Type*) [Field K] (D w T YS S:ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K (nestedExponents D w T YS S)

def kernelSumRange (f : ℕ → ℕ) : ℕ → ℕ := KernelEval.sumRange f


theorem kernelSumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    kernelSumRange f n = ∑ i ∈ Finset.range n, f i := by
  exact KernelEval.sumRange_eq f n

theorem finset_sum_range_sub (a m : ℕ) (h : m ≤ a) :
    ∑ r ∈ Finset.range (m + 1), (a - r) =
      (m + 1) * a - (m + 1) * m / 2 := by
  exact KernelEval.sum_range_sub a m h

def channelCount (T YS S:ℕ):ℕ :=
  kernelSumRange (fun y =>
    let M := min S (min (T - y) (YS - y))
    (M + 1) * (T + 1 - y) - (M + 1) * M / 2) (min T YS + 1)

theorem channelCount_eq (T YS S : ℕ) :
    channelCount T YS S =
      ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S (min (T - y) (YS - y)) + 1),
          (T + 1 - y - r) := by
  rw [channelCount, kernelSumRange_eq]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  let M := min S (min (T - y) (YS - y))
  have hM : M ≤ T + 1 - y := by
    have hMT : M ≤ T - y := by
      exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    omega
  simpa [M] using (finset_sum_range_sub (T + 1 - y) M hM).symm
abbrev HighBandIndex (delta T YS S:ℕ) :=
  (y:Fin (min T YS + 1)) ×
    (r:Fin (min S (min (T - y.val) (YS - y.val)) + 1)) ×
      (Fin (T + 1 - y.val - r.val) × Fin delta)
theorem highBandIndex_card (delta T YS S:ℕ) :
    Fintype.card (HighBandIndex delta T YS S) = delta * channelCount T YS S:=by
  rw [channelCount_eq]
  simp [HighBandIndex, Fintype.card_sigma,
    Finset.sum_range, Finset.mul_sum, Nat.mul_comm]
def highBandExponent (w Dlow:ℕ) {delta T YS S:ℕ}
    (c:HighBandIndex delta T YS S):Fin 4 →₀ ℕ :=
  Finsupp.single 0 (Dlow - w * c.1.val - (w - 1) * c.2.1.val + c.2.2.2.val) +
    Finsupp.single 1 c.1.val + Finsupp.single 2 c.2.1.val +
      Finsupp.single 3 c.2.2.1.val
def highBandMap (w Dlow delta T YS S:ℕ) :
    MvPolynomial (Fin 4) K →ₗ[K] (HighBandIndex delta T YS S → K) :=
  LinearMap.pi (fun c => MvPolynomial.lcoeff K (highBandExponent w Dlow c))
@[simp] theorem highBandMap_apply (w Dlow delta T YS S:ℕ)
    (P:MvPolynomial (Fin 4) K) (c:HighBandIndex delta T YS S) :
    highBandMap w Dlow delta T YS S P c =
      AddMonoidAlgebra.coeff P (highBandExponent w Dlow c):=rfl
theorem nested_mem_global {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) :
    P ∈ RCN100.globalCoefficientBox K D w T S:=by
  intro d hd
  have h:=hP hd
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩
theorem nested_mem_weights {D w T YS S:ℕ} {P:MvPolynomial (Fin 4) K}
    (hP:P ∈ nestedCoefficientBox K D w T YS S) (hne:P ≠ 0) :
    wt residualTotalWeights P ≤ T ∧ wt residualYSWeights P ≤ YS ∧
      wt residualSWeights P ≤ S ∧ wt (contactWeights w) P < D:=by
  have hD:0 < D:=by
    obtain ⟨d, hd⟩:=MvPolynomial.support_nonempty.mpr hne
    have h:=(hP hd).2.2.2
    omega
  have h:=(mem_flagGlobalCoefficientBox_iff P D w T S hD).mp
    (nested_mem_global hP)
  refine ⟨h.1, ?_, h.2.1, by omega⟩
  apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
  intro d hd
  have hdYS:=(hP hd).2.1
  rw [weight_fin4]
  simpa [residualYSWeights] using hdYS
section LinearSelection
variable {V:Type*} [AddCommGroup V] [Module K V]
end LinearSelection
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorNestedProjection

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorContact
namespace ProximityPrize.SubmissionLower.LocatorContact
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN122 RCN156 RCN180 RCN234 RCN313 ContactOrderBridge
noncomputable section
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
end
end ProximityPrize.SubmissionLower.LocatorContact
end PackedLocator_LocatorContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
variable {K I:Type*} [Field K] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
end
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorLowQuotient

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem regular_mem_normalizedFactors
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def regularIndexSelf (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1, ?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G => 0 < G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_, hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G => 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_, by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (regular_mem_normalizedFactors H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem regularIndexSelf_val (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(regularIndexSelf H F).1 = F.1:=rfl
end
end ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem quotient_mem_nestedCoefficientBox_of_mul_eq
    (P F Q : MvPolynomial (Fin 4) K) (D w T YS S : ℕ)
    (hP : P ≠ 0) (hF : F ≠ 0) (hQ : Q ≠ 0)
    (hbox : P ∈ nestedCoefficientBox K D w T YS S)
    (heq : P = F * Q) :
    Q ∈ nestedCoefficientBox K
      (D - wt (contactWeights w) F) w
      (T - wt residualTotalWeights F) (YS - wt residualYSWeights F)
      (S - wt residualSWeights F) := by
  have hglobal :
      Q ∈ globalCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F) (S - wt residualSWeights F) :=
    quotient_mem_flagGlobalCoefficientBox_of_mul_eq P F Q D w T S
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) hP hF hQ (nested_mem_global hbox) heq
      le_rfl le_rfl le_rfl
  have hPYS : wt residualYSWeights P ≤ YS :=
    (nested_mem_weights hbox hP).2.1
  have hmul := weightedTotalDegree_mul residualYSWeights F Q hF hQ
  have hsum : wt residualYSWeights F + wt residualYSWeights Q ≤ YS := by
    change MvPolynomial.weightedTotalDegree residualYSWeights F +
      MvPolynomial.weightedTotalDegree residualYSWeights Q ≤ YS
    rw [← hmul, ← heq]
    exact hPYS
  have hQYS : wt residualYSWeights Q ≤ YS - wt residualYSWeights F := by
    omega
  intro d hd
  have hb := hglobal hd
  have hy := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at hy
  simp only [wt] at hQYS
  simp only [residualYSWeights] at hy ⊢
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  change d 1 + d 2 ≤ YS -
    MvPolynomial.weightedTotalDegree residualYSWeights F
  simpa [residualYSWeights] using hy.trans hQYS

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section SecondDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

end SecondDerivative

end

end ProximityPrize.SubmissionLower.LocatorDoubleSquareAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section ThirdDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

end ThirdDerivative

end

end ProximityPrize.SubmissionLower.LocatorTripleCubeAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FourthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

end FourthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFourthPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
open LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K V I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end LinearDichotomy

section FifthDerivative

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I

end FifthDerivative

end

end ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
end PackedLocator_LocatorFifthPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.LocatorLowQuotient
open scoped BigOperators
theorem channelCount_mono {T T' YS YS' S S':ℕ}
    (ht:T ≤ T') (hy:YS ≤ YS') (hs:S ≤ S') :
    channelCount T YS S ≤ channelCount T' YS' S':=by
  rw [channelCount_eq, channelCount_eq]
  calc
    _ ≤ ∑ y ∈ Finset.range (min T YS + 1),
        ∑ r ∈ Finset.range (min S' (min (T' - y) (YS' - y)) + 1),
          (T' + 1 - y - r):=by
      apply Finset.sum_le_sum
      intro y _
      have hin:Finset.range (min S (min (T-y) (YS-y)) + 1) ⊆
          Finset.range (min S' (min (T'-y) (YS'-y)) + 1):=by
        apply Finset.range_mono
        have h:=min_le_min hs
          (min_le_min (Nat.sub_le_sub_right ht y) (Nat.sub_le_sub_right hy y))
        omega
      exact (Finset.sum_le_sum (fun r _ => by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => Nat.zero_le _))
    _ ≤ _:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right (min_le_min ht hy) 1)
      · intro _ _ _
        exact Nat.zero_le _
end ProximityPrize.SubmissionLower.LocatorLowQuotient
end PackedLocator_LocatorQuotientMonotone

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient LocatorDoubleSquareAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K V : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

def powerBandBudget
    (delta dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T YS S +
        powerBandBudget delta dT dY dS
          (T - dT) (YS - dY) (S - dS) k

theorem powerBandBudget_mono
    (delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ dT₂ dY₂ dS₂ T₂ Y₂ S₂ k : ℕ)
    (hT : T₁ ≤ T₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hdT : dT₂ ≤ dT₁) (hdY : dY₂ ≤ dY₁)
    (hdS : dS₂ ≤ dS₁) :
    powerBandBudget delta dT₁ dY₁ dS₁ T₁ Y₁ S₁ k ≤
      powerBandBudget delta dT₂ dY₂ dS₂ T₂ Y₂ S₂ k := by
  induction k generalizing T₁ Y₁ S₁ T₂ Y₂ S₂ with
  | zero =>
      simp only [powerBandBudget]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left delta (channelCount_mono hT hY hS)
      · apply ih
        · omega
        · omega
        · omega

def thinTop (w Dhigh S : ℕ) : ℕ := (Dhigh + S - 1) / w


theorem ys_le_thinTop (Dhigh w T YS S : ℕ) (hw : 1 ≤ w) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ nestedExponents Dhigh w T YS S) :
    d 1 + d 2 ≤ thinTop w Dhigh S := by
  rcases hd with ⟨_, _, hS, hD⟩
  have hwr : w * d 2 = (w - 1) * d 2 + d 2 := by
    calc
      w * d 2 = ((w - 1) + 1) * d 2 := by rw [Nat.sub_add_cancel hw]
      _ = (w - 1) * d 2 + d 2 := by ring
  have hmul : (d 1 + d 2) * w ≤ Dhigh + S - 1 := by
    rw [Nat.mul_comm, Nat.mul_add, hwr]
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

theorem mem_low_of_highBandMap_cut_eq_zero
    (Dhigh Dlow w delta T YS S : ℕ) (hw : 1 ≤ w)
    (hwidth : Dhigh ≤ Dlow + delta) (P : MvPolynomial (Fin 4) K)
    (hP : P ∈ nestedCoefficientBox K Dhigh w T YS S)
    (hzero : highBandMap w Dlow delta T (min YS (thinTop w Dhigh S)) S P = 0) :
    P ∈ nestedCoefficientBox K Dlow w T YS S := by
  intro d hd
  rcases hP hd with ⟨hT, hYS, hS, hD⟩
  have htop := ys_le_thinTop Dhigh w T YS S hw d ⟨hT, hYS, hS, hD⟩
  refine ⟨hT, hYS, hS, ?_⟩
  by_contra hnot
  have hy : d 1 < min T (min YS (thinTop w Dhigh S)) + 1 := by omega
  have hr : d 2 < min S (min (T - d 1) (min YS (thinTop w Dhigh S) - d 1)) + 1 := by
    omega
  have hz : d 3 < T + 1 - d 1 - d 2 := by omega
  have hstart : Dlow - w * d 1 - (w - 1) * d 2 ≤ d 0 := by omega
  have hx : d 0 - (Dlow - w * d 1 - (w - 1) * d 2) < delta := by omega
  let c : HighBandIndex delta T (min YS (thinTop w Dhigh S)) S :=
    ⟨⟨d 1, hy⟩, ⟨⟨d 2, hr⟩,
      ⟨⟨d 3, hz⟩, ⟨d 0 - (Dlow - w * d 1 - (w - 1) * d 2), hx⟩⟩⟩⟩
  have he : highBandExponent w Dlow c = d := by
    ext i
    fin_cases i <;> simp [highBandExponent, c] <;> omega
  have hc := congrFun hzero c
  have hcoeff : AddMonoidAlgebra.coeff P d = 0 := by
    simpa only [highBandMap_apply, he, Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff


def powerBandBudgetThin
    (w Dh delta dc dT dY dS T YS S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      delta * channelCount T (min YS (thinTop w Dh S)) S +
        powerBandBudgetThin w (Dh - delta - dc) delta dc dT dY dS
          (T - dT) (YS - dY) (S - dS) k

theorem powerBandBudgetThin_le (w delta dc dT dY dS : ℕ) :
    ∀ (k Dh T YS S : ℕ),
      powerBandBudgetThin w Dh delta dc dT dY dS T YS S k ≤
        powerBandBudget delta dT dY dS T YS S k := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp [powerBandBudgetThin, powerBandBudget]
  | succ k ih =>
      intro Dh T YS S
      simp only [powerBandBudgetThin, powerBandBudget]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left delta
          (channelCount_mono le_rfl (Nat.min_le_left _ _) le_rfl))
        (ih _ _ _ _)




end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerAvoidance
end PackedLocator_LocatorArbitraryPowerAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {K I : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

def iteratePderivR (j : ℕ) (Q : P4 K) : P4 K :=
  (fun H : P4 K => MvPolynomial.pderiv (2 : Fin 4) H)^[j] Q

@[simp] theorem iteratePderivR_zero (Q : P4 K) :
    iteratePderivR 0 Q = Q := rfl

theorem iteratePderivR_succ (j : ℕ) (Q : P4 K) :
    iteratePderivR (j + 1) Q =
      MvPolynomial.pderiv (2 : Fin 4) (iteratePderivR j Q) := by
  simp only [iteratePderivR, Function.iterate_succ_apply']

@[simp] theorem iteratePderivR_zero_poly (j : ℕ) :
    iteratePderivR (K := K) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratePderivR_succ, ih, map_zero]





section KernelVanishing

variable [Fintype I]
local instance : DecidableEq I := Classical.decEq I


end KernelVanishing




end

end ProximityPrize.SubmissionLower.LocatorArbitraryPowerContact
end PackedLocator_LocatorArbitraryPowerContact

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

private theorem regular_mem_normalizedFactors
    (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H := by
  have hactive : F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf : F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf

theorem regularIndex_isRelPrime_of_ne
    (H : P4 K) (F G : RCN266.RegularIndex H) (hne : F.1 ≠ G.1) :
    IsRelPrime F.1 G.1 := by
  have hFs := RCN167.positiveRFactors_spec H F.1 F.2
  have hGs := RCN167.positiveRFactors_spec H G.1 G.2
  apply hFs.1.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hne
  apply UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
    (regular_mem_normalizedFactors H F) (regular_mem_normalizedFactors H G)
  exact (hFs.1.dvd_irreducible_iff_associated hGs.1).mp hd

theorem quotientLinear_nested_data
    [AddCommGroup V] [Module K V]
    (D w T YS S : ℕ) (q : V →ₗ[K] P4 K)
    (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K D w T YS S)
    (F : P4 K) (hF : F ≠ 0) (hdiv : ∀ v, F ∣ q v) :
    Function.Injective (quotientLinear q F hF hdiv) ∧
      (∀ v, q v = F * quotientLinear q F hF hdiv v) ∧
      ∀ v, quotientLinear q F hF hdiv v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (T - wt residualTotalWeights F)
        (YS - wt residualYSWeights F)
        (S - wt residualSWeights F) := by
  classical
  let qF := quotientLinear q F hF hdiv
  have hqF : Function.Injective qF :=
    quotientLinear_injective q hq F hF hdiv
  have hprod (v : V) : q v = F * qF v :=
    recon_eq_mul_quotientPolynomial q F hdiv v
  refine ⟨hqF, hprod, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    rw [map_zero]
    exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
  · have hqv : q v ≠ 0 := by
      intro hz
      apply hv
      apply hq
      simpa only [map_zero] using hz
    have hqFv : qF v ≠ 0 := by
      intro hz
      apply hqv
      rw [hprod v, hz, mul_zero]
    exact quotient_mem_nestedCoefficientBox_of_mul_eq
      (q v) F (qF v) D w T YS S hqv hF hqFv (hmem v) (hprod v)

theorem wt_pow_eq (weights : Fin 4 → ℕ) (F : P4 K) (hF : F ≠ 0)
    (j : ℕ) : wt weights (F ^ j) = j * wt weights F := by
  unfold wt
  induction j with
  | zero => simp [pow_zero, MvPolynomial.weightedTotalDegree]
  | succ j ih =>
      rw [pow_succ', weightedTotalDegree_mul weights F (F ^ j) hF
        (pow_ne_zero j hF), ih]
      simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul]
      omega

end

end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz + p.all
def total (p:FlagDegree):ℕ:=p.zOnly + p.yz + p.all
def Below (p q:FlagDegree):Prop :=
  p.all ≤ q.all ∧ middle p ≤ middle q ∧ total p ≤ total q
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p + 1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree :=
  ⟨2 * (padT p - padY p) * d,
    1 + 2 * (padY p - padS p) * d,
    2 * (padS p - 1) * d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ :=
  flagMixed p (paddedTail p d) (paddedTail p e)
end ProximityPrize.SubmissionLower.LocatorFactorAggregate
end PackedLocator_LocatorFactorAggregate

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridCost

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open scoped BigOperators
open RCN095 LocatorFactorAggregate

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def rationalFlag (p : FlagDegree) : FlagDegree :=
  ⟨131072 * (padT p - padY p) + 2 * (padT p - padY p),
    131072 * (padY p - padS p - 1) + 2 * (padY p - padS p - 1) + 2,
    131072 * (padS p - 2) + 2 * (padS p - 2) + 3⟩

def movingFiber (p : FlagDegree) : FlagDegree :=
  ⟨padT p - padY p, padY p - padS p, padS p + 1⟩

def movingCut (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 131072, 262144⟩

def HybridApplies (p : FlagDegree) : Prop := 2 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridApplies p) := by
  unfold HybridApplies; infer_instance






end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCost

section PackedLocator_LocatorHybridCostC1

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC1

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def hybridCoordinateC1 (p : FlagDegree) : FlagDegree := rationalFlag p

def HybridAppliesC1 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridAppliesC1 p) := by
  unfold HybridAppliesC1; infer_instance




end ProximityPrize.SubmissionLower.LocatorHybridCostC1
end PackedLocator_LocatorHybridCostC1

section PackedLocator_LocatorHybridCostC2

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC2

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def reducedTail (p : FlagDegree) : FlagDegree := paddedTail p 131072



def hybridCostC2 (p : FlagDegree) : ℕ :=
  flagMixed p (reducedTail p) (hybridCoordinateC1 p) +
    131076 * flagMixed p (movingFiber p) (movingCut p)

def HybridAppliesC2 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridAppliesC2 p) := by
  unfold HybridAppliesC2; infer_instance


end ProximityPrize.SubmissionLower.LocatorHybridCostC2
end PackedLocator_LocatorHybridCostC2

section PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open RCN095 LocatorFactorAggregate LocatorHybridCostC2

def ordinaryCostOf (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then hybridCostC2 p else paddedCost 131072 131073 p

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact LocatorTwoFactorAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

def dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) : Submodule K V where
  carrier := {v | F ∣ q v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x + y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' := by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

@[simp] theorem mem_dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) (v : V) :
    v ∈ dvdSubmodule q F ↔ F ∣ q v := Iff.rfl

theorem dvdSubmodule_ne_top_of_not_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K)
    (h : ¬ ∀ v, F ∣ q v) :
    dvdSubmodule q F ≠ ⊤ := by
  intro htop
  apply h
  intro v
  have hv : v ∈ dvdSubmodule q F := by rw [htop]; trivial
  exact hv

theorem exists_avoiding_nonuniversal_factors
    [AddCommGroup V] [Module K V]
    {A : Type} [DecidableEq A] (s : Finset A) (hs : s.Nonempty)
    (q : V →ₗ[K] P4 K) (factor : A → P4 K)
    (hnonuniversal : ∀ a ∈ s, ¬ ∀ v, factor a ∣ q v)
    (hcard : s.card < ENat.card K) :
    ∃ v, v ≠ 0 ∧ ∀ a ∈ s, ¬ factor a ∣ q v := by
  classical
  let bad : s → Submodule K V := fun a => dvdSubmodule q (factor a.1)
  have hproper : ∀ a : s, bad a ≠ ⊤ := by
    intro a
    exact dvdSubmodule_ne_top_of_not_universal q (factor a.1)
      (hnonuniversal a.1 a.2)
  have hsmall : (Finset.univ : Finset s).card < ENat.card K := by
    simpa using hcard
  have hss := RCN133.finite_iUnion_ssubset
    (Finset.univ : Finset s) bad hproper hsmall
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hss
  have havoid : ∀ a : s, v ∉ bad a := by
    intro a hmem
    apply hv
    simp only [Set.mem_iUnion, Finset.mem_univ, true_and]
    exact ⟨a, trivial, hmem⟩
  have hv0 : v ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hs
    have hnot := havoid ⟨a, ha⟩
    apply hnot
    subst v
    change factor a ∣ q 0
    simp
  refine ⟨v, hv0, ?_⟩
  intro a ha
  simpa only [bad, mem_dvdSubmodule] using havoid ⟨a, ha⟩

def regularProduct (H : P4 K) (A : Finset (RCN266.RegularIndex H)) : P4 K :=
  ∏ F ∈ A, F.1

def regularCofactor (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) : P4 K :=
  ∏ G ∈ A.erase F, G.1

theorem regularFactor_ne_zero (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ≠ 0 :=
  (RCN167.positiveRFactors_spec H F.1 F.2).1.ne_zero

theorem regularProduct_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) : regularProduct H A ≠ 0 := by
  classical
  unfold regularProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  exact regularFactor_ne_zero H F


theorem regularFactor_mul_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    F.1 * regularCofactor H A F = regularProduct H A := by
  classical
  simpa only [regularProduct, regularCofactor] using
    Finset.mul_prod_erase A (fun G => G.1) hFA

theorem regularFactor_isRelPrime_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    IsRelPrime F.1 (regularCofactor H A F) := by
  classical
  unfold regularCofactor
  apply IsRelPrime.prod_right
  intro G hG
  have hGe := Finset.mem_erase.mp hG
  apply regularIndex_isRelPrime_of_ne H F G
  intro heq
  apply hGe.1
  exact Subtype.ext heq.symm

theorem regularProduct_power_split
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) :
    regularProduct H A ^ j * J =
      F.1 ^ j * (regularCofactor H A F ^ j * J) := by
  rw [← regularFactor_mul_cofactor H A F hFA, mul_pow]
  ring

theorem regularFactor_isRelPrime_liftedHelper
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) (hnot : ¬ F.1 ∣ J) :
    IsRelPrime F.1 (regularCofactor H A F ^ j * J) := by
  have hFirred := (RCN167.positiveRFactors_spec H F.1 F.2).1
  apply hFirred.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hnot
  exact ((regularFactor_isRelPrime_cofactor H A F hFA).pow_right)
    |>.dvd_of_dvd_mul_left hd



noncomputable def universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Finset (RCN266.RegularIndex H) := by
  classical
  exact A.filter fun F => ∀ v, F.1 ∣ q v

@[simp] theorem mem_universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (F : RCN266.RegularIndex H) :
    F ∈ universalFactors H A q ↔ F ∈ A ∧ ∀ v, F.1 ∣ q v := by
  classical
  simp only [universalFactors, Finset.mem_filter]

theorem universalFactors_subset
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : universalFactors H A q ⊆ A := by
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.1

theorem regularProduct_dvd_of_each
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (Q : P4 K)
    (hdiv : ∀ F ∈ A, F.1 ∣ Q) : regularProduct H A ∣ Q := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [regularProduct, Finset.notMem_empty,
      Finset.prod_empty, one_dvd]
  | @insert F A hFA ih =>
      have hFdiv : F.1 ∣ Q := hdiv F (Finset.mem_insert_self F A)
      have hAdiv : regularProduct H A ∣ Q := by
        apply ih
        intro G hGA
        exact hdiv G (Finset.mem_insert_of_mem hGA)
      have hrel : IsRelPrime F.1 (regularProduct H A) := by
        unfold regularProduct
        apply IsRelPrime.prod_right
        intro G hGA
        apply regularIndex_isRelPrime_of_ne H F G
        intro heq
        apply hFA
        have hFG : F = G := Subtype.ext heq
        rwa [hFG]
      have hprod : regularProduct H (insert F A) =
          F.1 * regularProduct H A := by
        simp only [regularProduct, Finset.prod_insert hFA]
      rw [hprod]
      exact hrel.mul_dvd hFdiv hAdiv


theorem universalProduct_dvd
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) :
    ∀ v, regularProduct H (universalFactors H A q) ∣ q v := by
  intro v
  apply regularProduct_dvd_of_each
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.2 v



def HasBatchExitStage
    [AddCommGroup V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Prop :=
  ∃ (j : Fin fuel) (U : Finset (RCN266.RegularIndex H)) (v : V) (J : P4 K),
    U ⊂ A ∧ v ≠ 0 ∧ J ≠ 0 ∧
      regularProduct H A ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta -
          j.val * wt (contactWeights w) (regularProduct H A)) w
        (T - j.val * wt residualTotalWeights (regularProduct H A))
        (YS - j.val * wt residualYSWeights (regularProduct H A))
        (S - j.val * wt residualSWeights (regularProduct H A)) ∧
      ∀ F ∈ A \ U, ¬ F.1 ∣ J

theorem exists_batchExitStage_of_bandBudgetThin_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hw : 1 ≤ w) (hDlow : Dlow = Dhigh - delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (hA : A.Nonempty)
    (hsource :
      LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
          (wt (contactWeights w) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          T YS S (steps + 1) < Module.finrank K V)
    (hterminal :
      T - steps * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - steps * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - steps * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfield : A.card < ENat.card K) :
    HasBatchExitStage (steps + 1) Dlow w delta T YS S H A q := by
  classical
  let P := regularProduct H A
  have hP : P ≠ 0 := by
    simpa only [P] using regularProduct_ne_zero H A
  change LocatorArbitraryPowerAvoidance.powerBandBudgetThin w Dhigh delta
      (wt (contactWeights w) P)
      (wt residualTotalWeights P) (wt residualYSWeights P)
      (wt residualSWeights P) T YS S (steps + 1) <
    Module.finrank K V at hsource
  change
    T - steps * wt residualTotalWeights P < wt residualTotalWeights P ∨
    YS - steps * wt residualYSWeights P < wt residualYSWeights P ∨
    S - steps * wt residualSWeights P < wt residualSWeights P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hfirst : delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.add_zero] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v, hv⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        have hdivT : wt residualTotalWeights P ≤
            wt residualTotalWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualTotalWeights P
              (qOne v) (hdivP v) hqv
        have hdivY : wt residualYSWeights P ≤
            wt residualYSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualYSWeights P
              (qOne v) (hdivP v) hqv
        have hdivS : wt residualSWeights P ≤
            wt residualSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualSWeights P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hs
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T
        (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S).comp q
      let lowOne := LinearMap.ker bandOne
      have hwidth : Dhigh ≤ Dlow + delta := by omega
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T
              (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
              (Dhigh - delta - wt (contactWeights w) P) delta
              (wt (contactWeights w) P)
              (wt residualTotalWeights P) (wt residualYSWeights P)
              (wt residualSWeights P)
              (T - wt residualTotalWeights P)
              (YS - wt residualYSWeights P)
              (S - wt residualSWeights P) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T
                (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S +
                LocatorArbitraryPowerAvoidance.powerBandBudgetThin w
                  (Dhigh - delta - wt (contactWeights w) P) delta
                  (wt (contactWeights w) P)
                  (wt residualTotalWeights P) (wt residualYSWeights P)
                  (wt residualSWeights P)
                  (T - wt residualTotalWeights P)
                  (YS - wt residualYSWeights P)
                  (S - wt residualSWeights P) (steps + 1) <
              Module.finrank K V := by
          simpa only [LocatorArbitraryPowerAvoidance.powerBandBudgetThin,
            Nat.succ_eq_add_one, Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T
            (min YS (LocatorArbitraryPowerAvoidance.thinTop w Dhigh S)) S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          LocatorArbitraryPowerAvoidance.mem_low_of_highBandMap_cut_eq_zero
            Dhigh Dlow w delta T YS S hw hwidth (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo := quotientLinear qOne P hP hdivP
        obtain ⟨hqTwo, _hprodTwo, hqTwoBox⟩ :=
          quotientLinear_nested_data Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh := Dlow - wt (contactWeights w) P
        let DOneLow := Dlow - delta - wt (contactWeights w) P
        let TOne := T - wt residualTotalWeights P
        let YOne := YS - wt residualYSWeights P
        let SOne := S - wt residualSWeights P
        have hDlowRest : DOneLow = DOneHigh - delta := by
          simp only [DOneHigh, DOneLow]
          omega
        have hterminalRest :
            TOne - steps * wt residualTotalWeights P <
                wt residualTotalWeights P ∨
            YOne - steps * wt residualYSWeights P <
                wt residualYSWeights P ∨
            SOne - steps * wt residualSWeights P <
                wt residualSWeights P := by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using ht
          · right; left
            simpa only [YOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hy
          · right; right
            simpa only [SOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hs
        obtain ⟨j, child, v, J, hchild, hv, hJ, heq, hbox, havoid⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hDlowRest qTwo hqTwo
            (by simpa only [qTwo, DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [DOneHigh, TOne, YOne, SOne, hDlow] using hlowOneRank)
            hterminalRest
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, child, v.1, J, hchild, ?_, hJ, ?_, ?_, havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P ^ (j.val + 1) * J = q v.1
          calc
            P ^ (j.val + 1) * J = P * (P ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = P * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne P hdivP v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) P =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) P := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights P =
              T - (j.val + 1) * wt residualTotalWeights P := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights P =
              YS - (j.val + 1) * wt residualYSWeights P := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights P =
              S - (j.val + 1) * wt residualSWeights P := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          change J ∈ nestedCoefficientBox K
            (DOneLow - j.val * delta -
              j.val * wt (contactWeights w) P) w
            (TOne - j.val * wt residualTotalWeights P)
            (YOne - j.val * wt residualYSWeights P)
            (SOne - j.val * wt residualSWeights P) at hbox
          change J ∈ nestedCoefficientBox K
            (Dlow - (j.val + 1) * delta -
              (j.val + 1) * wt (contactWeights w) P) w
            (T - (j.val + 1) * wt residualTotalWeights P)
            (YS - (j.val + 1) * wt residualYSWeights P)
            (S - (j.val + 1) * wt residualSWeights P)
          rw [hD, hT, hY, hS] at hbox
          exact hbox
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid



end

end ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end PackedLocator_LocatorBatchProductRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch
end PackedLocator_LocatorGenericHelperFactorSwitch

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open LocatorGenericHelperFactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.LocatorGenericPowerRoute
end PackedLocator_LocatorGenericPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch

set_option autoImplicit false
set_option maxRecDepth 100000

structure Potential where
  totalCoeff : ℕ
  middleCoeff : ℕ
  slopeCoeff : ℕ
  deriving DecidableEq, Repr

def Potential.eval (q : Potential) (p : FlagDegree) : ℕ :=
  q.totalCoeff * total p + q.middleCoeff * middle p + q.slopeCoeff * p.all

structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def sourceR1200 : SourceNumbers :=
  ⟨526750, 10983, 2450, 36963750380693986577⟩

def sourceC : SourceNumbers :=
  ⟨328400, 6641, 1480, 5090867013182078230⟩

def sourceSplit500 : SourceNumbers :=
  ⟨165000, 3320, 750, 315862958949324685⟩

def sourceSplit390 : SourceNumbers :=
  ⟨19500, 539, 120, 91073661700890⟩

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50293 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def rawFlag (r v z : ℕ) : FlagDegree := ⟨z, v, r⟩

@[simp] theorem rawFlag_all (r v z : ℕ) : (rawFlag r v z).all = r := rfl
@[simp] theorem rawFlag_middle (r v z : ℕ) : middle (rawFlag r v z) = r + v := by
  simp [rawFlag, middle, Nat.add_comm]
@[simp] theorem rawFlag_total (r v z : ℕ) : total (rawFlag r v z) = r + v + z := by
  simp [rawFlag, total, Nat.add_comm, Nat.add_left_comm]

def sumFlag {ι : Type} (s : Finset ι) (p : ι → FlagDegree) : FlagDegree :=
  ⟨∑ i ∈ s, (p i).zOnly, ∑ i ∈ s, (p i).yz,
    ∑ i ∈ s, (p i).all⟩

@[simp] theorem sumFlag_all {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    (sumFlag s p).all = ∑ i ∈ s, (p i).all := rfl

@[simp] theorem sumFlag_middle {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    middle (sumFlag s p) = ∑ i ∈ s, middle (p i) := by
  simp only [sumFlag, middle, Finset.sum_add_distrib]

@[simp] theorem sumFlag_total {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    total (sumFlag s p) = ∑ i ∈ s, total (p i) := by
  simp only [sumFlag, total, Finset.sum_add_distrib]

structure ThresholdReceipt where
  r : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : ℕ
  split500 : ℕ
  split1200 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def thresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  let maxZ := 6677 - (r + v)
  if threshold = 0 then s.Routeable (rawFlag r v 0)
  else if threshold ≤ maxZ then
    ¬s.Routeable (rawFlag r v (threshold - 1)) ∧
      s.Routeable (rawFlag r v threshold)
  else threshold = maxZ + 1 ∧ ¬s.Routeable (rawFlag r v maxZ)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (thresholdBoundary s r v threshold) := by
  unfold thresholdBoundary
  infer_instance

def ThresholdReceipt.Valid (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    thresholdBoundary sourceR1200 q.r q.v q.r1200 ∧
    thresholdBoundary LocatorPhase6800Oracle.sourceC q.r q.v q.sourceC ∧
    thresholdBoundary sourceSplit500 q.r q.v q.split500 ∧
    thresholdBoundary sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable q.Valid := by
  unfold ThresholdReceipt.Valid
  infer_instance

structure BaseSegment where
  start : ℕ
  valueAtStart : ℕ
  slope : ℕ
  deriving DecidableEq, Repr

def BaseSegment.evalAt (q : BaseSegment) (z : ℕ) : ℕ :=
  q.valueAtStart + q.slope * (z - q.start)

structure BaseRow where
  r : ℕ
  v : ℕ
  z0 : ℕ
  z1 : ℕ
  z2 : ℕ
  segments : List BaseSegment
  deriving DecidableEq, Repr

def evalBaseSegments : List BaseSegment → ℕ → ℕ
  | [], _ => 0
  | q :: qs, z =>
      (qs.foldl (fun best next => if next.start ≤ z then next else best) q).evalAt z

def BaseRow.evalAt (q : BaseRow) (z : ℕ) : ℕ :=
  if z = 0 then q.z0
  else if z = 1 then q.z1
  else if z = 2 then q.z2
  else evalBaseSegments q.segments z

def baseRowIndex (r v : ℕ) : ℕ :=
  (r - 1) * 136 - ((r - 1) * r) / 2 + v

def defaultBaseRow : BaseRow := ⟨0, 0, 0, 0, 0, []⟩

def lookupBaseRow (rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  (rows[baseRowIndex r v]?).getD defaultBaseRow

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def BaseRowsIndexed (rows : Array BaseRow) : Prop :=
  rows.size = 3509 ∧
    ∀ r ∈ (List.range 29).map (fun q => q + 1),
      ∀ v ∈ List.range (136 - r),
        let q := lookupBaseRow rows r v
        q.r = r ∧ q.v = v

instance (rows : Array BaseRow) : Decidable (BaseRowsIndexed rows) := by
  unfold BaseRowsIndexed
  infer_instance

def BaseRow.ExpectedShape (q : BaseRow) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    q.segments ≠ [] ∧ q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start) ∧
    ∀ s ∈ q.segments, s.start ≤ 6677 - (q.r + q.v)

instance (q : BaseRow) : Decidable q.ExpectedShape := by
  unfold BaseRow.ExpectedShape
  infer_instance

def RawBelow (q p : FlagDegree) : Prop :=
  q.all ≤ p.all ∧ q.yz ≤ p.yz ∧ q.zOnly ≤ p.zOnly

def RawStrictSlopeBelow (q p : FlagDegree) : Prop :=
  RawBelow q p ∧ q.all < p.all

end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOf ⟨z, v, r⟩






























end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex
end PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration

open scoped BigOperators
open LocatorOrdinaryZConvex

set_option autoImplicit false

end ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration
end PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Audit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

theorem powerBandBudget_le_succ
    (delta dT dY dS T YS S k : ℕ) :
    powerBandBudget delta dT dY dS T YS S k ≤
      powerBandBudget delta dT dY dS T YS S (k + 1) := by
  induction k generalizing T YS S with
  | zero =>
      simp only [powerBandBudget, Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      exact Nat.add_le_add_left
        (ih (T := T - dT) (YS := YS - dY) (S := S - dS)) _

theorem powerBandBudget_mono_fuel
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudget delta dT dY dS T YS S k₁ ≤
      powerBandBudget delta dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudget delta dT dY dS T YS S k₁ ≤
            powerBandBudget delta dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudget delta dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudget_le_succ delta dT dY dS T YS S (k₁ + d)
        _ = powerBandBudget delta dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)

def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

def CandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) : Prop :=
  let q := lookupBaseRow rows R V
  let zero := baseZeroCap rows (R - r) (V - v)
  LocatorOrdinaryZConvex.rawCost r v 0 + zero ≤ q.z0 ∧
  LocatorOrdinaryZConvex.rawCost r v 1 + zero ≤ q.z1 ∧
  LocatorOrdinaryZConvex.rawCost r v 2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
        candidateSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
        candidateLine rows R V r v (s₂.start - 1) ≤
          s₁.evalAt (s₂.start - 1) ∧
        candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
        candidateSlope r v ≤ s₂.slope
  | _ => False

instance (rows : Array BaseRow) (R V r v : ℕ) :
    Decidable (CandidateRowCheck rows R V r v) := by
  unfold CandidateRowCheck
  dsimp only
  generalize hq : lookupBaseRow rows R V = q
  cases hs : q.segments with
  | nil =>
      simp only [hs]
      infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil =>
          simp only [hs, ht]
          infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil =>
              simp only [hs, ht, hu]
              infer_instance
          | cons s₃ rest₃ =>
              simp only [hs, ht, hu]
              infer_instance

def CandidateRCheck (rows : Array BaseRow) (R : ℕ) : Prop :=
  ∀ V ∈ List.range (136 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → CandidateRCheck rows R

instance (rows : Array BaseRow) : Decidable (BaseCandidateChecks rows) := by
  unfold BaseCandidateChecks
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6800Audit
end PackedLocator_LocatorPhase6800Audit

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower.LocatorBatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact LocatorGenericHelperFactorSwitch LocatorGenericPowerRoute LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.LocatorBatchPowerRoute
end PackedLocator_LocatorBatchPowerRoute

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 RCN302
open LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

























end ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
end PackedLocator_LocatorFastKernelArithmetic

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorBatchPhase6800

namespace ProximityPrize.SubmissionLower.LocatorBatchPhase6800

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorBatchProductRoute LocatorBatchPowerRoute LocatorGenericHelperFactorSwitch LocatorPhase6800Oracle

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def regularAggregateFlag (H : P4) (A : Finset (RegularIndex H)) : FlagDegree :=
  sumFlag A (regularCumulativeFlag H)

private theorem regularProduct_weight_eq_sum
    (weights : Fin 4 → ℕ) (H : P4) (A : Finset (RegularIndex H)) :
    wt weights (regularProduct H A) = ∑ F ∈ A, wt weights F.1 := by
  have h := weightedTotalDegree_prod_eq weights A
    (fun F : RegularIndex H => F.1)
    (fun F _hF => regularFactor_ne_zero H F)
  simpa only [regularProduct, wt] using h

theorem regularAggregateFlag_all (H : P4) (A : Finset (RegularIndex H)) :
    (regularAggregateFlag H A).all =
      wt residualSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_all]
  calc
    (∑ F ∈ A, (regularCumulativeFlag H F).all) =
        ∑ F ∈ A, wt residualSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).1
    _ = wt residualSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualSWeights H A).symm

theorem regularAggregateFlag_middle (H : P4)
    (A : Finset (RegularIndex H)) :
    middle (regularAggregateFlag H A) =
      wt residualYSWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_middle]
  calc
    (∑ F ∈ A, middle (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualYSWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.1
    _ = wt residualYSWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualYSWeights H A).symm

theorem regularAggregateFlag_total (H : P4)
    (A : Finset (RegularIndex H)) :
    total (regularAggregateFlag H A) =
      wt residualTotalWeights (regularProduct H A) := by
  rw [regularAggregateFlag, sumFlag_total]
  calc
    (∑ F ∈ A, total (regularCumulativeFlag H F)) =
        ∑ F ∈ A, wt residualTotalWeights F.1 := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact (originalCumulativeFlag_cumulative F.1).2.2
    _ = wt residualTotalWeights (regularProduct H A) :=
      (regularProduct_weight_eq_sum residualTotalWeights H A).symm

theorem regularAggregateFlag_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    (regularAggregateFlag H A).all ≤ (regularAggregateFlag H B).all ∧
      middle (regularAggregateFlag H A) ≤
        middle (regularAggregateFlag H B) ∧
      total (regularAggregateFlag H A) ≤
        total (regularAggregateFlag H B) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨Finset.sum_le_sum_of_subset hAB,
    Finset.sum_le_sum_of_subset hAB, Finset.sum_le_sum_of_subset hAB⟩

theorem regularAggregateFlag_all_lt_of_ssubset (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊂ B) :
    (regularAggregateFlag H A).all < (regularAggregateFlag H B).all := by
  have hnBA : ¬ B ⊆ A := by
    intro hBA
    exact hAB.ne (Finset.Subset.antisymm hAB.subset hBA)
  rw [Finset.subset_iff] at hnBA
  push_neg at hnBA
  obtain ⟨F, hFB, hFA⟩ := hnBA
  simp only [regularAggregateFlag, sumFlag_all]
  exact Finset.sum_lt_sum_of_subset hAB.subset hFB hFA
    (regularCumulativeFlag_positive H F)
    (fun _ _ _ => Nat.zero_le _)

theorem regularAggregateFlag_raw_mono (H : P4)
    {A B : Finset (RegularIndex H)} (hAB : A ⊆ B) :
    RawBelow (regularAggregateFlag H A) (regularAggregateFlag H B) := by
  refine ⟨?_, ?_, ?_⟩
  · change (∑ F ∈ A, (regularCumulativeFlag H F).all) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).all
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).yz) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).yz
    exact Finset.sum_le_sum_of_subset hAB
  · change (∑ F ∈ A, (regularCumulativeFlag H F).zOnly) ≤
      ∑ F ∈ B, (regularCumulativeFlag H F).zOnly
    exact Finset.sum_le_sum_of_subset hAB

theorem sum_phasePotential_eval (q : Potential) (H : P4)
    (A : Finset (RegularIndex H)) :
    (∑ F ∈ A, q.eval (regularCumulativeFlag H F)) =
      q.eval (regularAggregateFlag H A) := by
  simp only [Potential.eval, Finset.sum_add_distrib, ← Finset.mul_sum,
    regularAggregateFlag, sumFlag_total, sumFlag_middle, sumFlag_all]

end

end ProximityPrize.SubmissionLower.LocatorBatchPhase6800
end PackedLocator_LocatorBatchPhase6800

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridCells

namespace ProximityPrize.SubmissionLower.LocatorHybridCells
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def cellA (t y : Nat) : Nat := t - y
def cellB (y r : Nat) : Nat := y - r - 1
def cellS (r : Nat) : Nat := r - 2

def cellSupport (t y r : Nat) : ResidualSupportParameters :=
  support (cellA t y) (cellB y r) (cellS r)

def cellFirstTail (t y r : Nat) : FlagDegree :=
  reducedResidualAgreementFlag (cellSupport t y r) (w + 1)

def cellDirection (t y r : Nat) : FlagDegree :=
  RCN206.directionFlag (cellA t y) (cellB y r) (cellS r)

def cellRational (t y r : Nat) : FlagDegree :=
  ⟨(w + 1) * cellA t y + (cellDirection t y r).zOnly,
    (w + 1) * cellB y r + (cellDirection t y r).yz + 1,
    (w + 1) * cellS r + (cellDirection t y r).all⟩

def cellMovingFiber (t y r : Nat) : FlagDegree :=
  RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r)

def cellMovingCut (t y r : Nat) : FlagDegree :=
  cellRational t y r + ⟨0, w + 1, 2 * (w + 1)⟩

theorem flag_ext {f g : FlagDegree} (h1 : f.zOnly = g.zOnly)
    (h2 : f.yz = g.yz) (h3 : f.all = g.all) : f = g := by
  cases f; cases g; simp_all

theorem cellMovingCut_eq_center_add (t y r : Nat) :
    cellMovingCut t y r =
      center (cellA t y) (cellB y r) (cellS r) +
        (w + 1) • RCN206.surfaceFlag (cellA t y) (cellB y r) (cellS r) := by
  refine flag_ext ?_ ?_ ?_ <;>
    simp only [center, direction, unitYZFlag, cellMovingCut, cellRational,
      cellDirection, RCN206.directionFlag, RCN206.surfaceFlag,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

theorem weightedCost_mono
    {Omega : Type} [Field Omega]
    {G T H : MvPolynomial (Fin 3) Omega}
    {surfaceFlag firstTailFlag : FlagDegree}
    (B : PrimeFlagBudgetFamily (G := G) (T := T) (H := H)
      surfaceFlag firstTailFlag)
    (C : RegularComponent Omega G T H)
    {f g : FlagDegree}
    (hz : f.zOnly ≤ g.zOnly) (hy : f.yz ≤ g.yz) (ha : f.all ≤ g.all) :
    B.weightedCost f C ≤ B.weightedCost g C := by
  simp only [PrimeFlagBudgetFamily.weightedCost]
  gcongr

theorem cellRational_yz (t y r : Nat) :
    (cellRational t y r).yz = 131074 * cellB y r + 2 := by
  simp only [cellRational, cellDirection, RCN206.directionFlag, w]
  omega

theorem rationalGate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellRational t y r).yz := by
  rw [cellRational_yz]
  have hB : 1 ≤ cellB y r := by
    simp only [cellB]
    omega
  have := Nat.mul_le_mul_left 131074 hB
  omega

end
end ProximityPrize.SubmissionLower.LocatorHybridCells
end PackedLocator_LocatorHybridCells

section PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower.LocatorHybridCellsC1
open scoped Classical BigOperators
open RCN095 RCN198 RCN206 RCN287 RCN327 RCN263 RCN237 RCN264 RCN275 RCN084
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def cellHybridCoordinateC1 (t y r : Nat) : FlagDegree := cellRational t y r

theorem sharp_absorbs_all_C1 (s delay mult : ℕ) (hs : 1 ≤ s)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    (2 * s + 3) * (131072 + delay) ≤ mult * (131072 * s + (2 * s + 3)) := by
  have key : 131072 * (2 * s + 3) ≤ mult * (131072 * s) := by
    calc 131072 * (2 * s + 3) ≤ 131072 * (6 * s) := by omega
      _ = 6 * (131072 * s) := by ring
      _ ≤ mult * (131072 * s) := Nat.mul_le_mul_right _ hm6
  calc
    (2 * s + 3) * (131072 + delay) ≤ (2 * s + 3) * (131072 + mult) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = 131072 * (2 * s + 3) + mult * (2 * s + 3) := by ring
    _ ≤ mult * (131072 * s) + mult * (2 * s + 3) := Nat.add_le_add_right key _
    _ = mult * (131072 * s + (2 * s + 3)) := by ring

theorem sharp_absorbs_ysall_C1 (B delay mult : ℕ) (hB : 1 ≤ B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * B + 4) * (131072 + delay) ≤ mult * (131072 * B + 2 * B + 5) := by
  have key : 1 + 131072 * (2 * B + 4) ≤ mult * (131072 * B) + mult := by
    have h6 : 6 * (131072 * B) + 6 ≤ mult * (131072 * B) + mult := by
      have := Nat.mul_le_mul_right (131072 * B) hm6
      omega
    have hB' : 262144 * B + 524289 ≤ 786432 * B + 6 := by
      have : (524288 : ℕ) ≤ 524288 * B := by
        calc (524288 : ℕ) = 524288 * 1 := by ring
          _ ≤ 524288 * B := Nat.mul_le_mul_left _ hB
      omega
    calc 1 + 131072 * (2 * B + 4) = 262144 * B + 524289 := by ring
      _ ≤ 786432 * B + 6 := hB'
      _ = 6 * (131072 * B) + 6 := by ring
      _ ≤ mult * (131072 * B) + mult := h6
  calc
    1 + (2 * B + 4) * (131072 + delay) ≤ 1 + (2 * B + 4) * (131072 + mult) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    _ = (1 + 131072 * (2 * B + 4)) + mult * (2 * B + 4) := by ring
    _ ≤ (mult * (131072 * B) + mult) + mult * (2 * B + 4) :=
      Nat.add_le_add_right key _
    _ = mult * (131072 * B + 2 * B + 5) := by ring

theorem sharp_absorbs_total_C1 (A delay mult : ℕ) (hA : 1 ≤ A)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * A + 4) * (131072 + delay) ≤ mult * (131072 * A + 2 * A + 5) :=
  sharp_absorbs_ysall_C1 A delay mult hA hdm hm6

theorem hybridC1Gate_of_le (t y r errorCap : Nat) (hb : r + 2 ≤ y)
    (hcap : errorCap + 1 ≤ 131076) :
    errorCap + 1 ≤ (cellHybridCoordinateC1 t y r).yz :=
  rationalGate_of_le t y r errorCap hb hcap

end
end ProximityPrize.SubmissionLower.LocatorHybridCellsC1
end PackedLocator_LocatorHybridCellsC1

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section BoundedProvider
variable {K0 Omega Iota : Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi : Polynomial K0 →+* Omega} {Gamma0 : Finset K0} {x0 : Iota → K0}
  {pchar errorCap d : ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2 : FlagDegree}
  {support0 : RCN275.ResidualSupportParameters}

structure HybridTailMultiplicityProvider
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound : optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily : PrimeFlagBudgetFamily
    (G := S.G) (T := globalTailCut phi S.F (d + 1))
    (H := regularitySurface phi S.F) flag0 tailFlag1
  multiplicity : FirstTailComponent S → ℕ
  cost : FirstTailComponent S → ℕ
  one_le_multiplicity : ∀ C, 1 ≤ multiplicity C
  tangentYZGate : errorCap + 1 ≤ tailFlag2.yz
  cost_sum_le : (∑ C, cost C) ≤ divisorBound
  componentBound : ∀ C,
    (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
      (regularitySurface phi S.F) Gamma0
      (selectedPoint phi S.selected) C).card ≤ cost C
  dichotomy : ∀ C,
    (∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
      globalTailCut phi S.F (d + 1 + delay) ∉ C.1) ∨
    ((∀ delay, globalTailCut phi S.F (d + 1 + delay) ∈ C.1) ∧
      (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
        (regularitySurface phi S.F) Gamma0
        (selectedPoint phi S.selected) C).card ≤
          (errorCap + 1) * budgetFamily.yzCost C)

theorem stage_card_le_divisorBound
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound : ℕ}
    (P : HybridTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S divisorBound) :
    Gamma0.card ≤ divisorBound := by
  classical
  let T1 := globalTailCut phi S.F (d + 1)
  let H := regularitySurface phi S.F
  let point := selectedPoint phi S.selected
  have hG : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G = 0 := S.on_component
  have hT1 : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    exact selectedPoint_evaluation phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover : Gamma0.card ≤
      ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card :=
    card_le_sum_componentSeeds Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card ≤ ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card := hcover
    _ ≤ ∑ C : RegularComponent Omega S.G T1 H, P.cost C :=
      Finset.sum_le_sum (fun C _ ↦ P.componentBound C)
    _ ≤ divisorBound := P.cost_sum_le

end BoundedProvider

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower.LocatorDerivativeChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

def dR (j : ℕ) (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  (MvPolynomial.pderiv (2 : Fin 4))^[j] F

@[simp] theorem dR_zero (F : MvPolynomial (Fin 4) K) : dR 0 F = F := rfl













theorem exists_active_factor_of_solution (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (γ : K) (hsol : specialization K P γ Q = 0) :
    ∃ F ∈ activeFactors Q, specialization K P γ F = 0 := by
  classical
  let φ := polynomialEmbedding K
  let v : Fin 3 → GenericField K := fun i => initialPoint K P γ i.succ
  have heval (F : MvPolynomial (Fin 4) K) :
      MvPolynomial.eval v (surfaceMap φ F) = 0 ↔ specialization K P γ F = 0 := by
    simpa only [canonical_geometricSurfaceMap] using
      (actual_generic_initial_zero_iff K P γ F)
  obtain ⟨F, hF, hz⟩ := exists_active_factor_of_surface_zero φ
    (polynomialEmbedding_injective K) Q hQ v ((heval Q).mpr hsol)
  exact ⟨F, hF, (heval F).mp hz⟩


section Counting

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota


def rfreeProduct (Q : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∏ F ∈ (activeFactors Q).filter (fun F => F.degreeOf 2 = 0), F




theorem rfreeProduct_dvd (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ∣ Q := by
  classical
  unfold rfreeProduct
  exact (Finset.prod_dvd_prod_of_subset _ (activeFactors Q) id
    (Finset.filter_subset _ _)).trans (activeFactors_product_dvd Q hQ)

theorem rfreeProduct_ne_zero (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    rfreeProduct Q ≠ 0 :=
  ne_zero_of_dvd_ne_zero hQ (rfreeProduct_dvd Q hQ)

theorem rfreeProduct_R_degree (Q : MvPolynomial (Fin 4) K) :
    (rfreeProduct Q).degreeOf 2 = 0 := by
  classical
  unfold rfreeProduct
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  apply Nat.le_of_eq
  apply Finset.sum_eq_zero
  intro F hF
  exact (Finset.mem_filter.mp hF).2


end Counting

section Assembly

variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota

end Assembly

end

end ProximityPrize.SubmissionLower.LocatorDerivativeChain
end PackedLocator_LocatorDerivativeChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower.LocatorFixedChain

open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313 RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 RCN140 LocatorDerivativeChain

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq Iota


end

end ProximityPrize.SubmissionLower.LocatorFixedChain
end PackedLocator_LocatorFixedChain

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorHybridTailProviderC1

namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

theorem sharp_absorbs_total_abs (a B delay mult : ℕ) (hA : 1 ≤ a + B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * a + 2 * B + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * B + 2 * B + 5) := by
  have h := sharp_absorbs_total_C1 (a + B) delay mult hA hdm hm6
  have e1 : 2 * (a + B) + 4 = 2 * a + 2 * B + 4 := by ring
  have e2 : 131072 * (a + B) + 2 * (a + B) + 5 =
      131074 * a + 131072 * B + 2 * B + 5 := by ring
  rw [e1, e2] at h
  exact h

theorem laterTail_in_hybridFlagC1
    (t y r : Nat) (hr3 : 3 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinateC1 t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hs1 : 1 ≤ cellS r := by simp only [cellS]; omega
  have hB1 : 1 ≤ cellB y r + cellS r := by omega
  have hA1 : 1 ≤ cellA t y + (cellB y r + cellS r) := by omega
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have hhallV : (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3)) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_yz, nsmul_all, w]
    ring
  have hhtotV : (mult • cellHybridCoordinateC1 t y r).zOnly +
      (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_zOnly, nsmul_yz, nsmul_all, w]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all_C1 (cellS r) delay mult hs1 hdm hm6)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall_C1 (cellB y r + cellS r) delay mult hB1 hdm hm6)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total_abs (cellA t y) (cellB y r + cellS r) delay mult
        hA1 hdm hm6)

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
end PackedLocator_LocatorHybridTailProviderC1

section PackedLocator_LocatorHybridTransportC2

namespace ProximityPrize.SubmissionLower.LocatorHybridTransportC2
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086 RCN085
open RCN066 RCN135 RCN159 RCN074 RCN237 RCN244 RCN327 RCN263 RCN206 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

section Transport
variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
  {G T T' H : MvPolynomial (Fin 3) Omega}

def unitFamilyOfCongruentCut (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1) :
    AdaptiveUnitProjectionFamily base p q where
  zProjection C := U.zProjection (regularComponentEquiv h C)
  yzProjection C := U.yzProjection (regularComponentEquiv h C)
  allProjection C := U.allProjection (regularComponentEquiv h C)
  zValue C := U.zValue (regularComponentEquiv h C)
  allTranscendental C := U.allTranscendental (regularComponentEquiv h C)
  zPole_eq C := U.zPole_eq (regularComponentEquiv h C)
  yzPole_eq C := U.yzPole_eq (regularComponentEquiv h C)
  allPole_eq C := U.allPole_eq (regularComponentEquiv h C)
  sum_zDegree_le := by
    refine Eq.trans_le ?_ U.sum_zDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_yzDegree_le := by
    refine Eq.trans_le ?_ U.sum_yzDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)
  sum_allDegree_le := by
    refine Eq.trans_le ?_ U.sum_allDegree_le
    exact Fintype.sum_equiv (regularComponentEquiv h) _ _ (fun _ => rfl)

theorem unitFamilyOfCongruentCut_costs (h : G ∣ T - T')
    {base' : ∀ C : RegularComponent Omega G T' H, SeparableLiteralCoordinate C.1}
    {p q : FlagDegree}
    (U : AdaptiveUnitProjectionFamily base' p q)
    (base : ∀ C : RegularComponent Omega G T H, SeparableLiteralCoordinate C.1)
    (C : RegularComponent Omega G T H) :
    (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.zCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).zCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.yzCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).yzCost C ∧
      (unitFamilyOfCongruentCut h U base).toPrimeFlagBudgetFamily.allCost C =
        (PrimeFlagBudgetFamily.ofCongruentCut h
          U.toPrimeFlagBudgetFamily).allCost C := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end Transport

section Budgets
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
  [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E]

theorem exists_firstTail_moving_budgets
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (G T : MvPolynomial (Fin 3) Ω) (a b s w : ℕ) (hw : 1 ≤ w)
    (hT : T = globalTailCut φ F (w + 1))
    (hF : ResidualSupportData (support a b s) F) (flag : FlagDegree)
    (hG : G ≠ 0) (hdiv : G ∣ surfaceMap φ F) (hGflag : PolynomialInFlag flag G)
    (base : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      SeparableLiteralCoordinate C.1)
    (tailFlag : FlagDegree)
    (unit : AdaptiveUnitProjectionFamily base flag tailFlag)
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < pchar) :
    ∃ budget : ∀ C : RegularComponent Ω G T (regularitySurface φ F),
      MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
      (∀ C, (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C, (budget C).movingCost) ≤ flagMixed flag
        (RCN206.fiberFlag a b s)
        (center a b s + (w + 1) • RCN206.surfaceFlag a b s) := by
  classical
  obtain ⟨coeffs, cflags, heq, hcoeff, hclass⟩ := globalTailCut_certificate
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
  obtain ⟨hHflag, hGcontact⟩ := surfaceMap_HG_flags
    φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
  have hderiv : regularitySurface φ F ∈
      Ideal.span ({G, MvPolynomial.pderiv (1 : Fin 3) G} :
        Set (MvPolynomial (Fin 3) Ω)) := by
    rw [regularitySurface, ← RCN267.surfaceMap_pderiv_R]
    exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
  have hT' : T = filteredCut w coeffs (surfaceMap φ (polyH K F))
      (surfaceMap φ (polyG K F)) := hT.trans heq
  clear hT
  subst T
  obtain ⟨budget, hcost, hz, hyz, ha, hm⟩ :=
    exists_moving_pole_budget_family (E := E)
      G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
      base flag tailFlag unit hG hderiv hGflag
      a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
      (by convert hmix using 1 <;> ring)
  refine ⟨budget, hcost, hm.trans ?_⟩
  rw [mixed_affine_third, mixed_affine_third]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _

end Budgets

end
end ProximityPrize.SubmissionLower.LocatorHybridTransportC2
end PackedLocator_LocatorHybridTransportC2

section PackedLocator_LocatorHybridTailProviderC2

namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
end PackedLocator_LocatorHybridTailProviderC2

section PackedLocator_LocatorHybridTailRealizationC2

namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
end PackedLocator_LocatorHybridTailRealizationC2

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

section PackedLocator_LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I:Type*} [CommRing R] [GCDMonoid R]
 [CommRing S] [IsDomain S]
local instance:DecidableEq S:=Classical.decEq S
local instance:DecidableEq I:=Classical.decEq I
end
end ProximityPrize.SubmissionLower.LocatorCover
end PackedLocator_LocatorCover

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

end Compact_PackedLocatorTail

section Compact_AsymmetricLocator
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260 LocatorCoprimeQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def leftRegularNumerator (P : UnequalParameters) : ℕ :=
  (P.n - P.w) * RCN294.dot P.leftAgreement P.mixedCost +
    (P.errors + 1) * P.gap * P.mixedCost.z

def leftRegularCountCap (P : UnequalParameters) : ℕ :=
  leftRegularNumerator P / P.gap


end
end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLocator

section Compact_AsymmetricLinear
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open RCN260
set_option autoImplicit false
set_option maxHeartbeats 1000000

end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLinear

section Compact_Helpers80791

set_option Elab.async false

section Adapted_LocatorGenericHelperFactorSwitch
namespace ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.Lower80791.FactorSwitch

end Adapted_LocatorGenericHelperFactorSwitch

section Adapted_LocatorGenericPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open Lower80791.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.Lower80791.PowerRoute

end Adapted_LocatorGenericPowerRoute

section Adapted_LocatorBatchPowerRoute
namespace ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact Lower80791.FactorSwitch Lower80791.PowerRoute LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

end

end ProximityPrize.SubmissionLower.Lower80791.BatchPowerRoute

end Adapted_LocatorBatchPowerRoute

end Compact_Helpers80791

section Compact_Oracle80791

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80791.PowerRoute Lower80791.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000

structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50283 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50283 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

end ProximityPrize.SubmissionLower.Lower80791.Oracle

end Compact_Oracle80791

section Compact_BatchPhase80791

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorBatchProductRoute Lower80791.BatchPowerRoute Lower80791.FactorSwitch Lower80791.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

end

end ProximityPrize.SubmissionLower.Lower80791.BatchPhase

end Compact_BatchPhase80791

section Compact_ClosedRank

namespace ProximityPrize.SubmissionLower.ClosedRank
open scoped BigOperators
open LocatorFastKernelArithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000















end ProximityPrize.SubmissionLower.ClosedRank

end Compact_ClosedRank

section Compact_OneResidueLower

namespace ProximityPrize.SubmissionLower.OneResidueLower
open scoped BigOperators
open RCN100 RCN302 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.OneResidueLower

end Compact_OneResidueLower

section Compact_Kernels80791

namespace ProximityPrize.SubmissionLower.Kernels80791
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A

end A

namespace B

end B

namespace T

end T

namespace Source00

end Source00

namespace Source01

end Source01

namespace Source02

end Source02

namespace Source03

end Source03

namespace Source04

end Source04

namespace Source05

end Source05

end ProximityPrize.SubmissionLower.Kernels80791

end Compact_Kernels80791

section Compact_Sources80791

set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80791.FactorSwitch Lower80791.PowerRoute
open Lower80791.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Phase00

end Phase00

namespace Phase01

end Phase01

namespace Phase02

end Phase02

namespace Phase03

end Phase03

namespace Phase04

end Phase04

namespace Phase05

end Phase05

end ProximityPrize.SubmissionLower.Lower80791.SourceSound

end Compact_Sources80791

section Compact_SecondJetHybridProvider

namespace ProximityPrize.SubmissionLower.SecondJetHybridProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.SecondJetHybridProvider

end Compact_SecondJetHybridProvider








section Compact_SecondJetFacetSupport

namespace ProximityPrize.SubmissionLower.SecondJetFacetSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetSupport

end Compact_SecondJetFacetSupport

section Compact_SecondJetFacetSpace

namespace ProximityPrize.SubmissionLower.SecondJetFacetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetFacetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s : ℕ) :=
  {d : SecondJetSpace.Index m L B s // (d.val 1).val+(d.val 3).val ≤ B}

instance (m L B s : ℕ) : Fintype (Index m L B s) := by
  unfold Index
  infer_instance

def exponent {m L B s : ℕ} (d : Index m L B s) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

def sourceMap (m L B s : ℕ) : (Index m L B s → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s).range

instance source_finite (m L B s : ℕ) : FiniteDimensional K (source (K := K) m L B s) := by
  unfold source
  infer_instance

end
end ProximityPrize.SubmissionLower.SecondJetFacetSpace

end Compact_SecondJetFacetSpace



section Compact_SecondJetFacetRank

namespace ProximityPrize.SubmissionLower.SecondJetFacetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetFacetSpace
open SecondJetRank (q a b budgets Block blockExponent blockExponent_injective block_monomial contactMap)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetRank

end Compact_SecondJetFacetRank


section Compact_SecondJetFacetCounts

namespace ProximityPrize.SubmissionLower.SecondJetFacetCounts
open scoped BigOperators
open SecondJetFacetSpace SecondJetFacetRank
open SecondJetRank (Block)
open SecondJetCounts (rectangle sum_rectangle kernelCell card_block_closed)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetFacetCounts

end Compact_SecondJetFacetCounts

section Compact_SecondJetGlobalMap

namespace ProximityPrize.SubmissionLower.SecondJetGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def coefficientLocal (e : I → Fin 5 →₀ ℕ) (m : ℕ) (x u0 u1 : K) :
    (I → K) →ₗ[K] Jet (MvPolynomial (Fin 3) K) :=
  (truncateOuter (K := K) m).comp ((flatEquiv (K := K)).toLinearMap.comp
    ((localize x u0 u1).toLinearMap.comp (FiniteMonomials.reconstruct e)))

theorem untruncate_contact {C : Type*} [CommRing C]
    (φ : Jet (MvPolynomial (Fin 3) K) →+* C) (t : C) (m : ℕ)
    (P : Jet (MvPolynomial (Fin 3) K)) (hε : φ Polynomial.X = t)
    (hP : t^m ∣ φ (truncateOuter (K := K) m P)) : t^m ∣ φ P := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet (MvPolynomial (Fin 3) K)) *
      (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  exact heq ▸ dvd_add hP hd

end
end ProximityPrize.SubmissionLower.SecondJetGlobalMap

end Compact_SecondJetGlobalMap

section Compact_SecondJetGlobalIndex

namespace ProximityPrize.SubmissionLower.SecondJetGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetGlobalIndex

end Compact_SecondJetGlobalIndex


section Compact_SecondJetFacetReceipt

namespace ProximityPrize.SubmissionLower.SecondJetFacetReceipt
open SecondJetFacetCounts SecondJetFacetRank
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K : Type*} [Field K]

end ProximityPrize.SubmissionLower.SecondJetFacetReceipt

end Compact_SecondJetFacetReceipt

section Compact_SecondJetGlobalReceipt

namespace ProximityPrize.SubmissionLower.SecondJetGlobalReceipt
open scoped BigOperators
open SecondJetGlobalIndex SecondJetGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K N : Type*} [Field K] [Fintype N]

end ProximityPrize.SubmissionLower.SecondJetGlobalReceipt

end Compact_SecondJetGlobalReceipt

section Compact_SecondJetDifferentiation

namespace ProximityPrize.SubmissionLower.SecondJetDifferentiation
open scoped BigOperators
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def substitute : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.X 3-MvPolynomial.X 0*MvPolynomial.X 1+
      MvPolynomial.X 0^2*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem chain_X (j : Fin 5) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 (MvPolynomial.X j)) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) (MvPolynomial.X j))+
        pderiv 2 (substitute (K := K) (MvPolynomial.X j)) := by
  fin_cases j <;> simp [substitute, pderiv_mul, pderiv_pow, Pi.single_apply] <;> ring

theorem chain_rule (P : Poly (K := K)) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) P)+
        pderiv 2 (substitute (K := K) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute]
  | add P Q hP hQ =>
    simp only [map_add]
    linear_combination hP+hQ
  | mul_X P j hP =>
    have hX := chain_X (K := K) j
    simp only [pderiv_mul, map_add, map_mul]
    linear_combination substitute (K := K) (MvPolynomial.X j)*hP + substitute (K := K) P*hX

theorem pderiv_preserves_epsilon (P : Poly (K := K)) (j : Fin 5) (hj : j ≠ 0) (m : ℕ)
    (hP : MvPolynomial.X 0^m ∣ P) : MvPolynomial.X 0^m ∣ pderiv j P := by
  obtain ⟨Q,rfl⟩ := hP
  rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (Ne.symm hj)]
  simp only [mul_zero, zero_mul, zero_add]
  exact dvd_mul_right _ _

theorem derivative_contact (P : Poly (K := K)) (m : ℕ)
    (hP : MvPolynomial.X 0^(m+1) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (pderiv 1 P) := by
  have hs := pderiv_preserves_epsilon (substitute (K := K) P) 1 (by decide) (m+1) hP
  have ht := pderiv_preserves_epsilon (substitute (K := K) P) 2 (by decide) (m+1) hP
  have hh : MvPolynomial.X 0^(m+1) ∣
      MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) := by
    rw [chain_rule]
    exact dvd_add (dvd_mul_of_dvd_right hs _) ht
  rw [pow_succ'] at hh
  exact (mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero (0 : Fin 5))).mp hh

theorem iterate_derivative_contact (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) ((pderiv 1)^[d] P) := by
  induction d generalizing P with
  | zero => simpa using hP
  | succ d ih =>
    have hfirst := derivative_contact P (m+d) (by simpa only [Nat.add_assoc] using hP)
    simpa only [Function.iterate_succ_apply] using ih (pderiv 1 P) hfirst

theorem substitute_contact (P : Poly (K := K)) :
    (MvPolynomial.finSuccEquiv K 4) (substitute (K := K) P) =
      SecondJetLocal.contact (K := K) (flatEquiv (K := K) P) := by
  have h0 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (0 : Fin 5)) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have h1 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (1 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h2 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (2 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 1)
  have h3 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (3 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 2)
  have h4 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (4 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (3 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 3)
  have h : (MvPolynomial.finSuccEquiv K 4).toAlgHom.comp (substitute (K := K)) =
      (SecondJetLocal.contact (K := K)).comp (flatEquiv (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [substitute, SecondJetSupport.flatEquiv_X, SecondJetLocal.baseEval,
        h0, h1, h2, h3, h4] <;> ring
  exact DFunLike.congr_fun h P

end
end ProximityPrize.SubmissionLower.SecondJetDifferentiation

end Compact_SecondJetDifferentiation

section Compact_SecondJetGlobalDifferentiation

namespace ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem support_pderiv (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (pderiv 1 P).support) : d+Finsupp.single 1 1 ∈ P.support := by
  have h := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact h (by rw [hz, zero_mul])

theorem support_iterate (P : Poly (K := K)) (n : ℕ) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ ((pderiv 1)^[n] P).support) : d+Finsupp.single 1 n ∈ P.support := by
  induction n generalizing d with
  | zero => simpa using hd
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hd
    have hh := ih (d+Finsupp.single 1 1) (support_pderiv _ d hd)
    have he : d+Finsupp.single 1 1+Finsupp.single 1 n = d+Finsupp.single 1 (n+1) := by
      rw [add_assoc, ← Finsupp.single_add, Nat.add_comm 1 n]
    rwa [he] at hh

theorem localize_pderiv (x u0 u1 : K) (P : Poly (K := K)) :
    localize x u0 u1 (pderiv 1 P) = pderiv 1 (localize x u0 u1 P) := by
  have hX (j : Fin 5) : localize x u0 u1 (pderiv 1 (MvPolynomial.X j)) =
      pderiv 1 (localize x u0 u1 (MvPolynomial.X j)) := by
    fin_cases j <;> simp [localize, pderiv_mul, Pi.single_apply]
  induction P using MvPolynomial.induction_on with
  | C c => simp [localize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP => simp only [pderiv_mul, map_add, map_mul, hP, hX]

theorem localize_iterate (x u0 u1 : K) (P : Poly (K := K)) (n : ℕ) :
    localize x u0 u1 ((pderiv 1)^[n] P) = (pderiv 1)^[n] (localize x u0 u1 P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', localize_pderiv, ih]

theorem local_derivative_contact (x u0 u1 : K) (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) (localize x u0 u1 P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 ((pderiv 1)^[d] P)) := by
  rw [localize_iterate]
  exact iterate_derivative_contact (localize x u0 u1 P) m d hP

theorem nested_to_flat_contact (P : Poly (K := K)) (m : ℕ)
    (hP : Polynomial.X^m ∣ SecondJetLocal.contact (K := K) (flatEquiv (K := K) P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) P := by
  obtain ⟨Q,hQ⟩ := hP
  refine ⟨(MvPolynomial.finSuccEquiv K 4).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 4).injective
  rw [substitute_contact, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply]
  exact hQ

end
end ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation

end Compact_SecondJetGlobalDifferentiation

section Compact_SecondJet6804

namespace ProximityPrize.SubmissionLower.SecondJet6804
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetGlobalDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJet6804

end Compact_SecondJet6804

section Compact_SecondJetContact

namespace ProximityPrize.SubmissionLower.SecondJetContact
open Polynomial
noncomputable section
set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem second_contact_residue (q : Polynomial K) :
    (Polynomial.X : Polynomial K)^3 ∣
      q - C (q.coeff 0) - Polynomial.X*q.derivative + Polynomial.X^2*hasseDeriv 2 q := by
  rw [X_pow_dvd_iff]
  intro d hd
  interval_cases d <;>
    simp [coeff_sub, coeff_add, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative, hasseDeriv_coeff] <;> ring

theorem exists_second_contact_expansion (q : Polynomial K) :
    ∃ U : Polynomial K,
      q - C (q.coeff 0) =
        Polynomial.X * (q.derivative - Polynomial.X*hasseDeriv 2 q + Polynomial.X^2*U) := by
  obtain ⟨U, hU⟩ := second_contact_residue q
  refine ⟨U, ?_⟩
  linear_combination hU

theorem taylor_second_contact (f : Polynomial K) (x : K) :
    ∃ U : Polynomial K,
      taylor x f - C (f.eval x) =
        Polynomial.X * ((taylor x f).derivative - Polynomial.X*hasseDeriv 2 (taylor x f) + Polynomial.X^2*U) := by
  simpa only [taylor_coeff_zero] using exists_second_contact_expansion (taylor x f)

end
end ProximityPrize.SubmissionLower.SecondJetContact

end Compact_SecondJetContact

section Compact_SecondJetSpecialize

namespace ProximityPrize.SubmissionLower.SecondJetSpecialize
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem hasse_taylor (f : Polynomial K) (x : K) (n : ℕ) :
    Polynomial.hasseDeriv n (Polynomial.taylor x f) =
      Polynomial.taylor x (Polynomial.hasseDeriv n f) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.taylor_coeff, Polynomial.taylor_coeff]
  have hc := congrArg (fun T : Polynomial K →ₗ[K] Polynomial K => (T f).eval x)
    (Polynomial.hasseDeriv_comp (R := K) i n)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.eval_smul,
    nsmul_eq_mul] at hc
  rw [hc]
  simp [Nat.choose_symm_add, mul_comm]

theorem derivative_taylor (f : Polynomial K) (x : K) :
    (Polynomial.taylor x f).derivative = Polynomial.taylor x f.derivative := by
  simpa only [Polynomial.hasseDeriv_one] using hasse_taylor f x 1

def specialize (f : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 f,f,f.derivative,Polynomial.C z]

def realize (q U : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 q,U,q.derivative,Polynomial.C z]

theorem realize_contact (f U : Polynomial K) (x u0 u1 z : K)
    (hagree : f.eval x = u0+u1*z)
    (hU : Polynomial.taylor x f-Polynomial.C (f.eval x) =
      Polynomial.X*((Polynomial.taylor x f).derivative-
        Polynomial.X*Polynomial.hasseDeriv 2 (Polynomial.taylor x f)+Polynomial.X^2*U))
    (P : Poly (K := K)) :
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) =
      Polynomial.taylor x (specialize f z P) := by
  have heq : (realize (Polynomial.taylor x f) U z).comp
      ((substitute (K := K)).comp (localize x u0 u1)) =
      (Polynomial.taylorAlgHom x).comp (specialize f z) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [realize, substitute, localize, specialize, hasse_taylor, derivative_taylor]
    · ring
    · rw [hagree, map_add, map_mul] at hU
      simp only [derivative_taylor, hasse_taylor] at hU
      linear_combination -hU
  exact DFunLike.congr_fun heq P

theorem root_contact (P : Poly (K := K)) (f : Polynomial K) (x u0 u1 z : K) (m : ℕ)
    (hagree : f.eval x = u0+u1*z)
    (hP : MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 P)) :
    (Polynomial.X-Polynomial.C x)^m ∣ specialize f z P := by
  obtain ⟨U,hU⟩ := SecondJetContact.taylor_second_contact f x
  have hd := map_dvd (realize (Polynomial.taylor x f) U z).toRingHom hP
  change realize (Polynomial.taylor x f) U z (MvPolynomial.X 0^m) ∣
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) at hd
  rw [map_pow, realize_contact f U x u0 u1 z hagree hU P] at hd
  have hx : realize (Polynomial.taylor x f) U z (MvPolynomial.X 0) = Polynomial.X := by
    simp [realize]
  rw [hx] at hd
  obtain ⟨Q,hQ⟩ := hd
  refine ⟨(Polynomial.taylorEquiv x).symm Q,?_⟩
  apply Polynomial.taylor_injective x
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow]
  have hh : Polynomial.taylor x (Polynomial.X-Polynomial.C x) = Polynomial.X := by simp
  rw [hh]
  change Polynomial.taylor x (specialize f z P) = Polynomial.X^m*
    ((Polynomial.taylorEquiv x) ((Polynomial.taylorEquiv x).symm Q))
  rw [AlgEquiv.apply_symm_apply]
  exact hQ

theorem monomial_degree (f : Polynomial K) (z : K) (w : ℕ) (hf : f.natDegree ≤ w)
    (d : Fin 5 →₀ ℕ) (c : K) :
    (specialize f z (MvPolynomial.monomial d c)).natDegree ≤
      d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (specialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by simp [specialize]
    have h0 : (specialize f z (MvPolynomial.X 0)^d 0).natDegree ≤ d 0 := by simp [specialize]
    have hs : (Polynomial.hasseDeriv 2 f).natDegree ≤ w-2 :=
      (Polynomial.natDegree_hasseDeriv_le f 2).trans (Nat.sub_le_sub_right hf 2)
    have hr : f.derivative.natDegree ≤ w-1 :=
      (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)
    have h1 : (specialize f z (MvPolynomial.X 1)^d 1).natDegree ≤ d 1*(w-2) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 1) hs
    have h2 : (specialize f z (MvPolynomial.X 2)^d 2).natDegree ≤ d 2*w := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 2) hf
    have h3 : (specialize f z (MvPolynomial.X 3)^d 3).natDegree ≤ d 3*(w-1) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 3) hr
    have h4 : (specialize f z (MvPolynomial.X 4)^d 4).natDegree ≤ 0 := by simp [specialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2
        (Polynomial.natDegree_mul_le_of_le h3 h4))))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using hh
  · intro i
    simp


end
end ProximityPrize.SubmissionLower.SecondJetSpecialize

end Compact_SecondJetSpecialize

section Compact_SecondJetVanish

namespace ProximityPrize.SubmissionLower.SecondJetVanish
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq N := Classical.decEq N


variable [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetVanish

end Compact_SecondJetVanish

section Compact_SecondJetCoefficients

namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def asS : Poly (K := K) ≃ₐ[K] Polynomial (MvPolynomial (Fin 4) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 5) 1)).trans (MvPolynomial.finSuccEquiv K 4)

def liftExponent (j : ℕ) (d : Fin 4 →₀ ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (d.cons j)

theorem swap_lift (j : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.mapDomain (Equiv.swap (0 : Fin 5) 1) (liftExponent j d) = d.cons j := by
  ext i
  simp [liftExponent, Finsupp.mapDomain_equiv_apply]

set_option maxRecDepth 40000 in
theorem lift_coordinates (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent j d 0 = d 0 ∧ liftExponent j d 1 = j ∧
      liftExponent j d 2 = d 1 ∧ liftExponent j d 3 = d 2 ∧ liftExponent j d 4 = d 3 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals try simp [liftExponent, Finsupp.mapDomain_equiv_apply,
    Equiv.swap_apply_def]
  all_goals rfl

theorem asS_coeff (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ) :
    AddMonoidAlgebra.coeff ((asS (K := K) P).coeff j) d =
      AddMonoidAlgebra.coeff P (liftExponent j d) := by
  change AddMonoidAlgebra.coeff (((MvPolynomial.finSuccEquiv K 4)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) P)).coeff j) d = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, ← swap_lift j d,
    MvPolynomial.coeff_rename_mapDomain _ (Equiv.swap (0 : Fin 5) 1).injective]

theorem coefficient_support (P : Poly (K := K)) (j : ℕ) (d : Fin 4 →₀ ℕ)
    (hd : d ∈ ((asS (K := K) P).coeff j).support) : liftExponent j d ∈ P.support := by
  simpa only [MvPolynomial.mem_support_iff, asS_coeff] using hd

end
end ProximityPrize.SubmissionLower.SecondJetCoefficients

end Compact_SecondJetCoefficients

section Compact_RootMultiplicityValuation

namespace ProximityPrize.SubmissionLower.RootMultiplicityValuation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]
abbrev Value := WithZero (Multiplicative ℤ)

def polyValue (v : Valuation L Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i))

end
end ProximityPrize.SubmissionLower.RootMultiplicityValuation

end Compact_RootMultiplicityValuation

section Compact_RootMultiplicityHeight

namespace ProximityPrize.SubmissionLower.RootMultiplicityHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem log_sum_zero_of_contains (c : L) (hc : c ≠ 0) (W : Finset (Place K L))
    (hW : placesFor K L c hc ⊆ W) : (∑ v ∈ W, (v.val c).log) = 0 := by
  classical
  have hz : (∑ v ∈ placesFor K L c hc, (v.val c).log) = 0 := by
    simpa only [order, Finset.sum_neg_distrib, neg_eq_zero] using
      sum_placesFor_order_zero K L c hc
  calc
    (∑ v ∈ W, (v.val c).log) = ∑ v ∈ placesFor K L c hc, (v.val c).log := by
      symm
      apply Finset.sum_subset hW
      intro v hv hnot
      have ho : order K L v c = 0 := by
        by_contra h
        exact hnot (placesFor_covers K L c hc v h)
      simpa only [order, neg_eq_zero] using ho
    _ = 0 := hz

end
end ProximityPrize.SubmissionLower.RootMultiplicityHeight

end Compact_RootMultiplicityHeight

section Compact_RootMultiplicityFlag

namespace ProximityPrize.SubmissionLower.RootMultiplicityFlag
open scoped Classical BigOperators WithZero
open RCN026 RCN095 RCN187 RCN204
open RCN344 (constant_value_le_one)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower.RootMultiplicityFlag

end Compact_RootMultiplicityFlag

section Compact_SecondJetFlagCoefficients

namespace ProximityPrize.SubmissionLower.SecondJetFlagCoefficients
open scoped BigOperators
open MvPolynomial RCN095 SecondJetCoefficients SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def freeze (x : K) : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![MvPolynomial.C x,MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.X 2]

theorem freeze_monomial (x : K) (d : Fin 4 →₀ ℕ) (c : K) :
    freeze x (MvPolynomial.monomial d c) = MvPolynomial.monomial d.tail (c*x^d 0) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [freeze, Fin.prod_univ_four, Fin.prod_univ_three, Finsupp.tail_apply,
        map_mul, map_pow, mul_assoc]
    · intro i
      simp
  · intro i
    simp

theorem freeze_inFlag (P : MvPolynomial (Fin 4) K) (x : K) (p : FlagDegree)
    (hP : ∀ d ∈ P.support, InFlag p d.tail) : PolynomialInFlag p (freeze x P) := by
  rw [MvPolynomial.as_sum P, map_sum]
  intro e he
  obtain ⟨d,hd,hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [freeze_monomial] at hed
  have heq : e = d.tail := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  subst e
  exact hP d hd

end
end ProximityPrize.SubmissionLower.SecondJetFlagCoefficients

end Compact_SecondJetFlagCoefficients

section Compact_RootMultiplicityWeightedValuation

namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation
open scoped BigOperators WithZero
open RootMultiplicityValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem weighted_sub_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x-y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_sub x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem weighted_add_le (v : Valuation L Value) (x y : L) (b B : Value)
    (hx : v x*b ≤ B) (hy : v y*b ≤ B) : v (x+y)*b ≤ B := by
  exact (mul_le_mul_left (v.map_add x y) b).trans (by rw [max_mul]; exact max_le hx hy)

theorem coeff_bound_large (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : b ≤ v t)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*v t ≤ B := by
  intro i
  induction i with
  | zero =>
    simpa [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, map_mul,
      mul_comm] using hP 0
  | succ i ih =>
    have hprev : v (Q.coeff i)*b^(i+1) ≤ B := by
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_right ht _).trans ih
    have heq : t*Q.coeff (i+1) = Q.coeff i-((Polynomial.X-Polynomial.C t)*Q).coeff (i+1) := by
      simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
      ring
    have hb := weighted_sub_le v _ _ _ _ hprev (hP (i+1))
    rw [← heq, map_mul] at hb
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

theorem coeff_bound_small (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value) (ht : v t ≤ b)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*b ≤ B := by
  have hbound : ∀ n i : ℕ, Q.natDegree+1 ≤ i+n → v (Q.coeff i)*b^i*b ≤ B := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul, zero_mul]
      exact zero_le
    | succ n ih =>
      intro i hi
      have hnext := ih (i+1) (by omega)
      have hmul : v (t*Q.coeff (i+1))*b^(i+1) ≤ B := by
        rw [map_mul]
        have hb := (mul_le_mul_right ht (v (Q.coeff (i+1))*b^(i+1))).trans hnext
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hb
      have heq : Q.coeff i = ((Polynomial.X-Polynomial.C t)*Q).coeff (i+1)+t*Q.coeff (i+1) := by
        simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        ring
      rw [mul_assoc, ← pow_succ, heq]
      exact weighted_add_le v _ _ _ _ (hP (i+1)) hmul
  exact fun i => hbound (Q.natDegree+1) i (by omega)

theorem coeff_bound_linear_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)*Q).coeff i)*b^i ≤ B) :
    ∀ i, v (Q.coeff i)*b^i*max b (v t) ≤ B := by
  by_cases ht : b ≤ v t
  · rw [max_eq_right ht]
    exact coeff_bound_large v b t Q B ht hP
  · rw [max_eq_left (le_of_not_ge ht)]
    exact coeff_bound_small v b t Q B (le_of_not_ge ht) hP

def weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) : Value :=
  P.support.sup (fun i => v (P.coeff i)*b^i)

theorem coeff_le_weightedValue (v : Valuation L Value) (b : Value) (P : Polynomial L) (i : ℕ) :
    v (P.coeff i)*b^i ≤ weightedValue v b P := by
  classical
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)*b^i) hi
  · have hz : P.coeff i = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hi
    rw [hz, map_zero, zero_mul]
    exact zero_le

theorem weightedValue_le (v : Valuation L Value) (b : Value) (P : Polynomial L) (B : Value)
    (h : ∀ i, v (P.coeff i)*b^i ≤ B) : weightedValue v b P ≤ B := by
  exact Finset.sup_le (fun i _ => h i)

theorem weightedValue_linear_factor (v : Valuation L Value) (b : Value) (t : L) (Q : Polynomial L) :
    weightedValue v b Q*max b (v t) ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*Q) := by
  classical
  by_cases hQ : Q = 0
  · subst Q
    simp [weightedValue]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Q.support
    (Polynomial.support_nonempty.mpr hQ) (fun i => v (Q.coeff i)*b^i)
  change Q.support.sup (fun i => v (Q.coeff i)*b^i)*_ ≤ _
  rw [hi]
  exact coeff_bound_linear_factor v b t Q _ (coeff_le_weightedValue v b _) i

theorem weightedValue_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) :
    weightedValue v b Q*(max b (v t))^d ≤
      weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      weightedValue v b Q*(max b (v t))^(d+1) =
          (weightedValue v b Q*(max b (v t))^d)*max b (v t) := by rw [pow_succ, mul_assoc]
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)^d*Q)*max b (v t) :=
        mul_le_mul_left ih _
      _ ≤ weightedValue v b ((Polynomial.X-Polynomial.C t)*((Polynomial.X-Polynomial.C t)^d*Q)) :=
        weightedValue_linear_factor v b t _
      _ = weightedValue v b ((Polynomial.X-Polynomial.C t)^(d+1)*Q) := by
        rw [pow_succ']; congr 1; ring

theorem coeff_bound_pow_factor (v : Valuation L Value) (b : Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B : Value)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*b^i ≤ B) (i : ℕ) :
    v (Q.coeff i)*b^i*(max b (v t))^d ≤ B := by
  exact (mul_le_mul_left (coeff_le_weightedValue v b Q i) _).trans
    ((weightedValue_pow_factor v b t Q d).trans (weightedValue_le v b _ B hP))

end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedValuation

end Compact_RootMultiplicityWeightedValuation

section Compact_RootMultiplicityWeightedHeight

namespace ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight
open scoped Classical BigOperators WithZero
open RCN026 RCN187 RootMultiplicityValuation RootMultiplicityHeight
open RootMultiplicityWeightedValuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {L : Type*} [Field L]

theorem log_max_exp (v : Valuation L Value) (t : L) (lambda : ℤ) (hl : 0 ≤ lambda) :
    (max (WithZero.exp lambda) (v t)).log = max lambda (poleOrder v t) := by
  by_cases ht : v t = 0
  · simp [ht, poleOrder, max_eq_left hl]
  by_cases h : WithZero.exp lambda ≤ v t
  · have hlog : lambda ≤ (v t).log := by
      rw [← WithZero.exp_log ht] at h
      exact WithZero.exp_le_exp.mp h
    rw [max_eq_right h]
    simp only [poleOrder, max_eq_right (hl.trans hlog), max_eq_right hlog]
  · have hv : v t ≤ WithZero.exp lambda := le_of_not_ge h
    have hlog := (WithZero.log_le_iff_le_exp ht).mpr hv
    rw [max_eq_left hv]
    simp only [WithZero.log_exp, poleOrder, max_eq_left (max_le hl hlog)]

theorem coeff_weighted_of_affine (v : Valuation L Value) (P : Polynomial L)
    (B lambda : ℤ)
    (hP : ∀ i, v (P.coeff i) ≤ WithZero.exp (B-(i : ℤ)*lambda)) :
    ∀ i, v (P.coeff i)*(WithZero.exp lambda)^i ≤ WithZero.exp B := by
  intro i
  calc
    v (P.coeff i)*(WithZero.exp lambda)^i ≤
        WithZero.exp (B-(i : ℤ)*lambda)*(WithZero.exp lambda)^i :=
      mul_le_mul_left (hP i) _
    _ = WithZero.exp B := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
      simp

theorem coeff_log_bound_pow_factor (v : Valuation L Value) (t : L)
    (Q : Polynomial L) (d : ℕ) (B lambda : ℤ) (hl : 0 ≤ lambda)
    (hP : ∀ i, v (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp lambda)^i ≤ WithZero.exp B)
    (i : ℕ) (hi : Q.coeff i ≠ 0) :
    (v (Q.coeff i)).log+(i : ℤ)*lambda+
      (d : ℤ)*max lambda (poleOrder v t) ≤ B := by
  have hv : v (Q.coeff i) ≠ 0 := v.ne_zero_iff.mpr hi
  have hb : (WithZero.exp lambda : Value) ≠ 0 := WithZero.exp_ne_zero
  have ht : max (WithZero.exp lambda) (v t) ≠ 0 := by
    intro h
    have hle := le_max_left (WithZero.exp lambda) (v t)
    rw [h] at hle
    exact hb (le_antisymm hle zero_le)
  have hh := (WithZero.log_le_iff_le_exp
    (mul_ne_zero (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht))).mpr
    (RootMultiplicityWeightedValuation.coeff_bound_pow_factor
      v (WithZero.exp lambda) t Q d (WithZero.exp B) hP i)
  simpa only [WithZero.log_mul (mul_ne_zero hv (pow_ne_zero i hb)) (pow_ne_zero d ht),
    WithZero.log_mul hv (pow_ne_zero i hb), WithZero.log_pow, WithZero.log_exp,
    nsmul_eq_mul, log_max_exp v t lambda hl] using hh

theorem finite_log_height_bound {ι : Type*} (W : Finset ι)
    (v : ι → Valuation L Value) (t : L) (Q : Polynomial L) (d : ℕ)
    (B lambda : ι → ℤ) (hl : ∀ w ∈ W, 0 ≤ lambda w)
    (hP : ∀ w ∈ W, ∀ i, v w (((Polynomial.X-Polynomial.C t)^d*Q).coeff i)*
      (WithZero.exp (lambda w))^i ≤ WithZero.exp (B w))
    (i : ℕ) (hi : Q.coeff i ≠ 0)
    (hbalance : (∑ w ∈ W, (v w (Q.coeff i)).log) = 0) :
    (i : ℤ)*(∑ w ∈ W, lambda w)+
      (d : ℤ)*(∑ w ∈ W, max (lambda w) (poleOrder (v w) t)) ≤ ∑ w ∈ W, B w := by
  have hsum := Finset.sum_le_sum (fun w hw =>
    coeff_log_bound_pow_factor (v w) t Q d (B w) (lambda w) (hl w hw) (hP w hw) i hi)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hbalance, zero_add] using hsum

section FunctionField
variable (K : Type*) [Field K] [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem moving_height_bound (P : Polynomial L) (hP : P ≠ 0) (t : L) (d : ℕ)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((P.natDegree-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  obtain ⟨Q, rfl⟩ := hd
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
  have hf : (Polynomial.X-Polynomial.C t)^d ≠ 0 := left_ne_zero_of_mul hP
  have hi : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hdeg : ((Polynomial.X-Polynomial.C t)^d*Q).natDegree-d = Q.natDegree := by
    rw [Polynomial.natDegree_mul hf hQ, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega
  simp only [hdeg] at hbudget
  let V := W ∪ placesFor K L (Q.coeff Q.natDegree) hi
  have hbalance := log_sum_zero_of_contains K L (Q.coeff Q.natDegree) hi V
    Finset.subset_union_right
  have hl : ∀ v, 0 ≤ 2*alpha v-beta v := by intro v; have := ha v; have := hba v; omega
  have hh := finite_log_height_bound V (fun v => v.val) t Q d B
    (fun v => 2*alpha v-beta v) (fun v _ => hl v)
    (fun v _ => coeff_weighted_of_affine v.val _ _ _ (hcoeff v)) Q.natDegree hi hbalance
  have heq (v : Place K L) :
      max (2*alpha v) (beta v+poleOrder v.val t) =
        beta v+max (2*alpha v-beta v) (poleOrder v.val t) := by omega
  have hbound : (d : ℤ)*(∑ v ∈ V, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
    have hbud := hbudget V
    simp_rw [heq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hbud ⊢
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
    nlinarith
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg d)
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro v _ _
  exact (by have := ha v; omega : 0 ≤ 2*alpha v).trans (le_max_left _ _)

theorem moving_height_bound_of_degree (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (d n0 : ℕ) (hn : n0 ≤ P.natDegree)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ P)
    (B alpha beta : Place K L → ℤ) (C : ℤ)
    (ha : ∀ v, 0 ≤ alpha v) (hba : ∀ v, beta v ≤ alpha v)
    (hcoeff : ∀ v (i : ℕ), v.val (P.coeff i) ≤
      WithZero.exp (B v-(i : ℤ)*(2*alpha v-beta v)))
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, (B v+(d : ℤ)*beta v-
        ((n0-d : ℕ) : ℤ)*(2*alpha v-beta v))) ≤ C)
    (W : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ W, max (2*alpha v) (beta v+poleOrder v.val t)) ≤ C := by
  apply moving_height_bound K P hP t d hd B alpha beta C ha hba hcoeff _ W
  intro V
  apply le_trans _ (hbudget V)
  apply Finset.sum_le_sum
  intro v _
  have hl : 0 ≤ 2*alpha v-beta v := by have := ha v; have := hba v; omega
  have hsub : ((n0-d : ℕ) : ℤ) ≤ ((P.natDegree-d : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hn d
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hsub hl) _

end FunctionField
end
end ProximityPrize.SubmissionLower.RootMultiplicityWeightedHeight

end Compact_RootMultiplicityWeightedHeight

section Compact_SecondJetRelaxedFlag

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedFlag
open scoped BigOperators WithZero
open ProximityPrize.SubmissionLower.RootMultiplicityValuation
open MvPolynomial RCN095 RCN026 RCN187 RCN204
open SecondJetCoefficients SecondJetSupport SecondJetFlagCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K L : Type*} [Field K] [Field L]

def coefficientFlag (B U T j : ℕ) : FlagDegree := ⟨T-U,U-B+j,B-2*j⟩

def budgetFlag (B U T d n0 : ℕ) : FlagDegree := ⟨T-U,U-B+n0,B-2*(n0-d)⟩

theorem coefficient_bounds (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (j : ℕ) (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS (K := K) P).coeff j).support) :
    2*j+e 2 ≤ B ∧ j+e 1+e 2 ≤ U ∧ j+e 1+e 2+e 3 ≤ T := by
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rwa [h1,h2,h3,h4] at hh

theorem frozen_coefficient_flag (P : Poly (K := K)) (x : K) (B U T : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) (j : ℕ) :
    PolynomialInFlag (coefficientFlag B U T j) (freeze x ((asS (K := K) P).coeff j)) := by
  apply freeze_inFlag
  intro e he
  have hb := coefficient_bounds P B U T hP j e he
  change e 2 ≤ B-2*j ∧ e 1+e 2 ≤ U-B+j+(B-2*j) ∧
    e 1+e 2+e 3 ≤ T-U+(U-B+j)+(B-2*j)
  omega

theorem coefficient_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T j : ℕ) (hj : 2*j ≤ B) :
    flagPole v x (coefficientFlag B U T j) =
      flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [Nat.cast_sub hj]
  push_cast
  ring

theorem budget_flag_pole (v : Valuation L Value) (x : Fin 3 → L)
    (B U T d n0 : ℕ) (hd : d ≤ n0) (hB : 2*(n0-d) ≤ B) :
    flagPole v x (budgetFlag B U T d n0) =
      flagPole v x (coefficientFlag B U T 0) + (d : ℤ)*flagPole v x unitYZFlag -
        ((n0-d : ℕ) : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag) := by
  simp only [flagPole, budgetFlag, coefficientFlag, unitAllFlag, unitYZFlag, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  simp only [Nat.cast_sub hB, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd, Nat.cast_add]
  ring

theorem frozen_coefficient_valuation (P : Poly (K := K)) (freezeX : K)
    (B U T : ℕ) (hBU : B ≤ U) (hUT : U ≤ T)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (v : Valuation L Value) (coeff : K →+* L) (hc : ∀ c, v (coeff c) ≤ 1)
    (x : Fin 3 → L) (j : ℕ) :
    v (MvPolynomial.eval₂Hom coeff x (freeze freezeX ((asS (K := K) P).coeff j))) ≤
      WithZero.exp (flagPole v x (coefficientFlag B U T 0) -
        (j : ℤ)*(2*flagPole v x unitAllFlag-flagPole v x unitYZFlag)) := by
  by_cases hz : (asS (K := K) P).coeff j = 0
  · simp only [hz, map_zero]
    exact zero_le
  have hs : ((asS (K := K) P).coeff j).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr hz
  obtain ⟨e,he⟩ := hs
  have hj : 2*j ≤ B := by have := coefficient_bounds P B U T hP j e he; omega
  rw [← coefficient_flag_pole v x B U T j hj]
  exact valuation_eval_le_flag v coeff hc x (coefficientFlag B U T j) _
    (frozen_coefficient_flag P freezeX B U T hBU hUT hP j)

section FunctionField
variable [Algebra K L] [IsAlgClosed K]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

theorem moving_bound (P : Poly (K := K)) (freezeX : K) (B U T d n0 : ℕ)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : d ≤ n0) (hB : 2*(n0-d) ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (x : Fin 3 → L) (Q : Polynomial L)
    (hQcoeff : ∀ j, Q.coeff j = MvPolynomial.eval₂Hom (algebraMap K L) x
      (freeze freezeX ((asS (K := K) P).coeff j)))
    (hQ : Q ≠ 0) (hn : n0 ≤ Q.natDegree) (t : L)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ Q) (C : ℤ)
    (hbudget : ∀ V : Finset (Place K L),
      (∑ v ∈ V, flagPole v.val x (budgetFlag B U T d n0)) ≤ C)
    (V : Finset (Place K L)) :
    (d : ℤ)*(∑ v ∈ V, max (2*flagPole v.val x unitAllFlag)
      (flagPole v.val x unitYZFlag+poleOrder v.val t)) ≤ C := by
  apply RootMultiplicityWeightedHeight.moving_height_bound_of_degree K Q hQ t d n0 hn hd
    (fun v => flagPole v.val x (coefficientFlag B U T 0))
    (fun v => flagPole v.val x unitAllFlag) (fun v => flagPole v.val x unitYZFlag) C
    (fun v => flagPole_nonneg v.val x unitAllFlag) ?_ ?_ ?_ V
  · intro v
    rw [flagPole_unitYZ, flagPole_unitAll]
    exact le_max_right _ _
  · intro v j
    rw [hQcoeff j]
    exact frozen_coefficient_valuation P freezeX B U T hBU hUT hP v.val
      (algebraMap K L) (RCN344.constant_value_le_one K L v) x j
  · intro W
    convert hbudget W using 1
    apply Finset.sum_congr rfl
    intro v _
    exact (budget_flag_pole v.val x B U T d n0 hdn hB).symm

end FunctionField

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedFlag

end Compact_SecondJetRelaxedFlag

section Compact_SecondJetSurfaceMap

namespace ProximityPrize.SubmissionLower.SecondJetSurfaceMap
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetFlagCoefficients
open RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

theorem coefficient_map (f : K →+* E) (P : Poly (K := K)) (j : ℕ) :
    (asS (MvPolynomial.map f P)).coeff j = MvPolynomial.map f ((asS P).coeff j) := by
  ext e
  rw [asS_coeff,MvPolynomial.coeff_map,MvPolynomial.coeff_map,asS_coeff]

theorem freeze_map_eq_surface (φ : Polynomial K →+* E) (P : MvPolynomial (Fin 4) K) :
    freeze (φ Polynomial.X) (MvPolynomial.map (φ.comp Polynomial.C) P) = surfaceMap φ P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [freeze]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    simp only [map_mul,hp,MvPolynomial.map_X]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [freeze]
    · rw [surfaceMap_X_succ]
      fin_cases j <;> simp [freeze]

theorem frozen_mapped_coefficient (φ : Polynomial K →+* E) (P : Poly (K := K)) (j : ℕ) :
    freeze (φ Polynomial.X) ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j) =
      surfaceMap φ ((asS P).coeff j) := by
  rw [coefficient_map,freeze_map_eq_surface]

theorem mapped_support_bounds (f : K →+* E) (P : Poly (K := K)) (B U T : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T) :
    ∀ e ∈ (MvPolynomial.map f P).support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T := by
  intro e he
  exact hP e (MvPolynomial.support_map_subset f P he)

end
end ProximityPrize.SubmissionLower.SecondJetSurfaceMap

end Compact_SecondJetSurfaceMap

section Compact_SecondJetCoefficientSpecialization

namespace ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem lift_succ (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent (j+1) d = liftExponent j d+Finsupp.single 1 1 := by
  ext i
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j d
  obtain ⟨g0,g1,g2,g3,g4⟩ := lift_coordinates (j+1) d
  fin_cases i <;> simp [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4,g0,g1,g2,g3,g4]

theorem asS_pderiv (P : Poly (K := K)) :
    asS (pderiv 1 P) = (asS P).derivative := by
  ext j d
  rw [asS_coeff, MvPolynomial.coeff_pderiv, Polynomial.coeff_derivative]
  rw [show ((j : MvPolynomial (Fin 4) K)+1) = MvPolynomial.C (j+1 : K) by simp,
    mul_comm ((asS P).coeff (j+1)) (MvPolynomial.C (j+1 : K)),
    MvPolynomial.coeff_C_mul, asS_coeff]
  rw [← lift_succ, (lift_coordinates j d).2.1]
  simp [mul_comm]

theorem asS_iterate (P : Poly (K := K)) (d : ℕ) :
    asS ((pderiv 1)^[d] P) = (Polynomial.derivative)^[d] (asS P) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', asS_pderiv, ih]

def coefficientSpecialize (f : Polynomial K) (z : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,f,f.derivative,Polynomial.C z]

def evaluateS (f : Polynomial K) (z : K) :
    Polynomial (MvPolynomial (Fin 4) K) →ₐ[K] Polynomial K :=
  { Polynomial.eval₂RingHom (coefficientSpecialize f z).toRingHom (Polynomial.hasseDeriv 2 f) with
    commutes' := by intro c; simp [coefficientSpecialize] }

theorem specialize_eq (P : Poly (K := K)) (f : Polynomial K) (z : K) :
    specialize f z P = (asS P).eval₂ (coefficientSpecialize f z).toRingHom
      (Polynomial.hasseDeriv 2 f) := by
  have heq : specialize f z = (evaluateS f z).comp (asS (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (1 : Fin 5) = g 0 := rfl
    have h2 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (2 : Fin 5) = g 1 := rfl
    have h3 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (3 : Fin 5) = g 2 := rfl
    have h4 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (4 : Fin 5) = g 3 := rfl
    fin_cases i <;> simp [specialize, asS, coefficientSpecialize, evaluateS,
      Equiv.swap_apply_def, MvPolynomial.finSuccEquiv_apply, h1,h2,h3,h4]
  exact DFunLike.congr_fun heq P

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization

end Compact_SecondJetCoefficientSpecialization

section Compact_SecondJetClearedHelper

namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
open SecondJetCoefficientSpecialization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def cleared {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ) (H G : R) : R :=
  ∑ j : Fin (n+1), P.coeff j.val*H^(n-j.val)*G^j.val

theorem map_cleared {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (P : Polynomial R) (n : ℕ) (H G : R) :
    φ (cleared P n H G) = cleared (P.map φ) n (φ H) (φ G) := by
  simp [cleared,Polynomial.coeff_map]

theorem cleared_eval {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ)
    (hn : P.natDegree ≤ n) (H G t : R) (hrel : H*t = G) :
    cleared P n H G = H^n*P.eval t := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < n+1)]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => P.coeff j*t^j)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hrel,mul_pow]
  have hh : H^(n-j.val)*H^j.val = H^n := by rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
  calc
    _ = P.coeff j.val*(H^(n-j.val)*H^j.val)*t^j.val := by ring
    _ = _ := by rw [hh]; ring

theorem coefficientSpecialize_eq (f : Polynomial K) (z : K) :
    (coefficientSpecialize f z).toRingHom = RCN319.specialization K f z := by
  rfl

theorem hasse_two (f : Polynomial K) :
    (2 : Polynomial K)*Polynomial.hasseDeriv 2 f = f.derivative.derivative := by
  have hh := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := 2)) f
  simpa [Function.iterate_succ_apply',nsmul_eq_mul] using hh

def helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (n d : ℕ) :
    MvPolynomial (Fin 4) K :=
  cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)

theorem helper_vanish (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (n d : ℕ) (hn : (asS ((pderiv 1)^[d] P)).natDegree ≤ n)
    (f : Polynomial K) (z : K)
    (hF : RCN319.specialization K f z F = 0)
    (hP : specialize f z ((pderiv 1)^[d] P) = 0) :
    RCN319.specialization K f z (helper P F n d) = 0 := by
  have hrel : RCN319.specialization K f z (2*RCN313.polyH K F)*Polynomial.hasseDeriv 2 f =
      RCN319.specialization K f z (RCN313.polyG K F) := by
    rw [map_mul,map_ofNat]
    calc
      _ = RCN319.specialization K f z (RCN313.polyH K F)*
          ((2 : Polynomial K)*Polynomial.hasseDeriv 2 f) := by ring
      _ = _ := by rw [hasse_two]; exact RCN231.solution_slope_identity K F f z hF
  change (RCN319.specialization K f z).toRingHom
    (cleared (asS ((pderiv 1)^[d] P)) n (2*RCN313.polyH K F) (RCN313.polyG K F)) = 0
  rw [map_cleared]
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
  rw [cleared_eval _ n (Polynomial.natDegree_map_le.trans hn) _ _ _ hrel]
  have hv : ((asS ((pderiv 1)^[d] P)).map (RCN319.specialization K f z)).eval
      (Polynomial.hasseDeriv 2 f) = 0 := by
    rw [Polynomial.eval_map,← coefficientSpecialize_eq,← specialize_eq]
    exact hP
  rw [hv,mul_zero]

end
end ProximityPrize.SubmissionLower.SecondJetClearedHelper

end Compact_SecondJetClearedHelper

section Compact_SecondJetHelperWeights

namespace ProximityPrize.SubmissionLower.SecondJetHelperWeights
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem derivative_coefficient_bounds (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS ((pderiv 1)^[d] P)).coeff j).support) :
    2*(j+d)+e 2 ≤ B ∧ j+d+e 1+e 2 ≤ U ∧ j+d+e 1+e 2+e 3 ≤ L := by
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  simpa [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4] using hb

theorem derivative_coefficient_weights (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L) :
    wt residualSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ B-2*d-2*j ∧
    wt residualYSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ U-d-j ∧
    wt residualTotalWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ L-d-j := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    have hb := derivative_coefficient_bounds P B U L d j hP e he
  · simp [residualSWeights,RCN081.weight_fin4]
    omega
  · simp [residualYSWeights,RCN081.weight_fin4]
    omega
  · simp [residualTotalWeights,RCN081.weight_fin4]
    omega

theorem asS_derivative_degree (P : Poly (K := K)) (s d : ℕ)
    (hP : ∀ e ∈ P.support, e 1 ≤ s) :
    (asS ((pderiv 1)^[d] P)).natDegree ≤ s-d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨e,he⟩ := MvPolynomial.support_nonempty.mpr hn
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  have h1 := (lift_coordinates j e).2.1
  simp [Finsupp.add_apply,Finsupp.single_apply,h1] at hb
  omega

theorem cleared_weight (weights : Fin 4 → ℕ) (P : Polynomial (MvPolynomial (Fin 4) K))
    (n C slope Hcap : ℕ) (H G : MvPolynomial (Fin 4) K)
    (hC : slope*n ≤ C)
    (hP : ∀ j : Fin (n+1), wt weights (P.coeff j.val) ≤ C-slope*j.val)
    (hH : wt weights H ≤ Hcap) (hG : wt weights G ≤ Hcap+slope) :
    wt weights (cleared P n H G) ≤ C+n*Hcap := by
  unfold cleared
  apply RCN235.wt_finset_sum_le
  intro j _
  have hj := j.isLt
  have hp := hP j
  have hh := (wt_pow_le weights H (n-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hg := (wt_pow_le weights G j.val).trans (Nat.mul_le_mul_left _ hG)
  have ht := (wt_mul_le weights (P.coeff j.val*H^(n-j.val)) (G^j.val)).trans
    (Nat.add_le_add ((wt_mul_le weights (P.coeff j.val) (H^(n-j.val))).trans
      (Nat.add_le_add hp hh)) hg)
  have hjn : j.val ≤ n := by omega
  have hjC : slope*j.val ≤ C := (Nat.mul_le_mul_left slope hjn).trans hC
  have hc : C-slope*j.val+slope*j.val = C := Nat.sub_add_cancel hjC
  have hn : n-j.val+j.val = n := Nat.sub_add_cancel hjn
  nlinarith

theorem helper_weights (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (B U L s d capT capY capR : ℕ) (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L)
    (hd : d ≤ s) (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT) :
    wt residualSWeights (helper P F (s-d) d) ≤ B-2*d+(s-d)*(capR-1) ∧
    wt residualYSWeights (helper P F (s-d) d) ≤ U-d+(s-d)*(capY-1) ∧
    wt residualTotalWeights (helper P F (s-d) d) ≤ L-d+(s-d)*(capT-1) := by
  have hw (weights : Fin 4 → ℕ) (cap : ℕ) (hR1 : weights 2 = 1)
      (hFcap : wt weights F ≤ cap) : wt weights (2*RCN313.polyH K F) ≤ cap-1 := by
    have hh := wt_polyH_le weights F cap hFcap
    have hm := wt_mul_le weights (2 : MvPolynomial (Fin 4) K) (RCN313.polyH K F)
    have hc : wt weights (2 : MvPolynomial (Fin 4) K) = 0 := wt_natCast weights 2
    rw [hR1] at hh
    omega
  refine ⟨?_,?_,?_⟩
  · apply cleared_weight residualSWeights _ (s-d) (B-2*d) 2 (capR-1) _ _ (by omega)
      (fun j => (derivative_coefficient_weights P B U L d j.val hP).1)
      (hw _ capR rfl hF.1)
    have hg := wt_polyG_le residualSWeights rfl F capR hF.1
    change wt residualSWeights (RCN313.polyG K F) ≤ capR-1+2
    change wt residualSWeights (RCN313.polyG K F) ≤ capR+1 at hg
    omega
  · apply cleared_weight residualYSWeights _ (s-d) (U-d) 1 (capY-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.1)
      (hw _ capY rfl hF.2.1)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualYSWeights rfl F capY (by decide) hY hF.2.1
    omega
  · apply cleared_weight residualTotalWeights _ (s-d) (L-d) 1 (capT-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.2)
      (hw _ capT rfl hF.2.2)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualTotalWeights rfl F capT (by decide) hT hF.2.2
    omega

end
end ProximityPrize.SubmissionLower.SecondJetHelperWeights

end Compact_SecondJetHelperWeights

section Compact_RootMultiplicityDichotomy

namespace ProximityPrize.SubmissionLower.RootMultiplicityDichotomy
noncomputable section
set_option autoImplicit false
variable {L : Type*} [Field L]

theorem derivative_or_high_multiplicity (P : Polynomial L) (hP : P ≠ 0)
    (t : L) (k : ℕ) (hk : (k.factorial : L) ≠ 0) :
    (∃ d ≤ k, ((Polynomial.derivative)^[d] P).eval t ≠ 0) ∨
      (Polynomial.X-Polynomial.C t)^(k+1) ∣ P := by
  classical
  rcases Classical.em (∀ d ≤ k, ((Polynomial.derivative)^[d] P).eval t = 0) with hroot | hroot
  · right
    have hm := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
      hP hroot (mem_nonZeroDivisors_iff_ne_zero.mpr hk)
    exact (pow_dvd_pow (Polynomial.X-Polynomial.C t) hm).trans (P.pow_rootMultiplicity_dvd t)
  · left
    push_neg at hroot
    exact hroot

end
end ProximityPrize.SubmissionLower.RootMultiplicityDichotomy

end Compact_RootMultiplicityDichotomy

section Compact_SecondJetCarrierDichotomy

namespace ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy
open MvPolynomial SecondJetSupport SecondJetCoefficients
open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K E : Type*} [Field K] [Field E]

def ratio (φ : MvPolynomial (Fin 4) K →+* E) (F : MvPolynomial (Fin 4) K) : E :=
  φ (RCN313.polyG K F)/φ (2*RCN313.polyH K F)

theorem mapped_helper (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s d : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hH : φ (2*RCN313.polyH K F) ≠ 0) :
    φ (helper P F (s-d) d) = φ (2*RCN313.polyH K F)^(s-d)*
      ((Polynomial.derivative)^[d] ((asS P).map φ)).eval (ratio φ F) := by
  rw [helper,map_cleared]
  have hdegree : ((asS ((pderiv 1)^[d] P)).map φ).natDegree ≤ s-d :=
    Polynomial.natDegree_map_le.trans (asS_derivative_degree P s d hS)
  have hrel : φ (2*RCN313.polyH K F)*ratio φ F = φ (RCN313.polyG K F) := by
    unfold ratio
    field_simp
  rw [cleared_eval _ (s-d) hdegree _ _ _ hrel,asS_iterate,← Polynomial.iterate_derivative_map]

theorem helper_or_multiplicity (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0) :
    (∃ d ≤ k, ¬ F ∣ helper P F (s-d) d) ∨
      (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases RootMultiplicityDichotomy.derivative_or_high_multiplicity
    ((asS P).map φ) hP (ratio φ F) k hk with hder | hroot
  · left
    obtain ⟨d,hd,hne⟩ := hder
    refine ⟨d,hd,?_⟩
    intro hdiv
    have hh := map_dvd φ hdiv
    rw [hF,zero_dvd_iff,mapped_helper P F φ s d hS hH] at hh
    exact (mul_ne_zero (pow_ne_zero _ hH) hne) hh
  · exact Or.inr hroot

theorem multiplicity_of_helpers_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (φ : MvPolynomial (Fin 4) K →+* E) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s) (hF : φ F = 0)
    (hH : φ (2*RCN313.polyH K F) ≠ 0)
    (hP : (asS P).map φ ≠ 0) (hk : (k.factorial : E) ≠ 0)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d) :
    (Polynomial.X-Polynomial.C (ratio φ F))^(k+1) ∣ (asS P).map φ := by
  rcases helper_or_multiplicity P F φ s k hS hF hH hP hk with h | h
  · obtain ⟨d,hd,hn⟩ := h
    exact False.elim (hn (hdiv d hd))
  · exact h

end
end ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy

end Compact_SecondJetCarrierDichotomy

section Compact_SecondJetCoefficientAvoidance

namespace ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

theorem map_degree_preserved {R T : Type*} [CommRing R] [CommRing T]
    (P : Polynomial R) (φ : R →+* T) (hC : φ P.leadingCoeff ≠ 0) :
    P.map φ ≠ 0 ∧ (P.map φ).natDegree = P.natDegree := by
  constructor
  · intro hz
    have hh := congrArg (fun Q : Polynomial T => Q.coeff P.natDegree) hz
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.coeff_natDegree] at hh
    exact hC hh
  · exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl hC)

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientAvoidance

end Compact_SecondJetCoefficientAvoidance

section Compact_SecondJetComponentRoots

namespace ProximityPrize.SubmissionLower.SecondJetComponentRoots
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K E : Type} [Field K] [Field E]

def coefficientMap (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] :
    MvPolynomial (Fin 4) K →+* CoordinateField E C :=
  (coordinateEvaluation E C).toRingHom.comp (surfaceMap φ)

def componentPolynomial (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) : Polynomial (CoordinateField E C) :=
  (asS P).map (coefficientMap φ C)

theorem evaluation_zero_iff (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (Q : MvPolynomial (Fin 3) E) : coordinateEvaluation E C Q = 0 ↔ Q ∈ C := by
  change Q ∈ RingHom.ker (coordinateEvaluation E C).toRingHom ↔ Q ∈ C
  rw [coordinateEvaluation_ker]

theorem degree_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C) :
    componentPolynomial φ C P ≠ 0 ∧ (componentPolynomial φ C P).natDegree = (asS P).natDegree := by
  apply SecondJetCoefficientAvoidance.map_degree_preserved
  change coordinateEvaluation E C (surfaceMap φ (asS P).leadingCoeff) ≠ 0
  exact fun hz => hlead ((evaluation_zero_iff C _).mp hz)

theorem coefficients (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (j : ℕ) :
    (componentPolynomial φ C P).coeff j =
      MvPolynomial.eval₂Hom (algebraMap E (CoordinateField E C)) (coordinate E C)
        (SecondJetFlagCoefficients.freeze (φ Polynomial.X)
          ((asS (MvPolynomial.map (φ.comp Polynomial.C) P)).coeff j)) := by
  rw [SecondJetSurfaceMap.frozen_mapped_coefficient]
  rw [componentPolynomial,Polynomial.coeff_map]
  change coordinateEvaluation E C _ = _
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _)

theorem roots_retained (φ : Polynomial K →+* E) (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K) (s k : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hF : surfaceMap φ F ∈ C) (hH : surfaceMap φ (RCN313.polyH K F) ∉ C)
    (hlead : surfaceMap φ (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0) :
    (Polynomial.X-Polynomial.C (RCN064.movingRatio C
      (surfaceMap φ (RCN313.polyH K F)) (surfaceMap φ (RCN313.polyG K F))/2))^(k+1) ∣
      componentPolynomial φ C P := by
  have hf : coefficientMap φ C F = 0 := (evaluation_zero_iff C _).mpr hF
  have hh : coordinateEvaluation E C (surfaceMap φ (RCN313.polyH K F)) ≠ 0 :=
    fun hz => hH ((evaluation_zero_iff C _).mp hz)
  have h2e : (2 : CoordinateField E C) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne h2
  have hfe : (k.factorial : CoordinateField E C) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap E (CoordinateField E C)).injective.ne hfact
  have hden : coefficientMap φ C (2*RCN313.polyH K F) ≠ 0 := by
    rw [map_mul,map_ofNat]
    exact mul_ne_zero h2e hh
  have hr := SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F (coefficientMap φ C)
    s k hS hf hden (degree_retained φ C P hlead).1 hfe hdiv
  have heq : SecondJetCarrierDichotomy.ratio (coefficientMap φ C) F =
      RCN064.movingRatio C (surfaceMap φ (RCN313.polyH K F))
        (surfaceMap φ (RCN313.polyG K F))/2 := by
    simp only [SecondJetCarrierDichotomy.ratio,coefficientMap,RingHom.comp_apply,
      RCN064.movingRatio,map_mul,map_ofNat,AlgHom.toRingHom_eq_coe,RingHom.coe_coe]
    field_simp
    <;> ring
  rwa [heq] at hr

end
end ProximityPrize.SubmissionLower.SecondJetComponentRoots

end Compact_SecondJetComponentRoots

section Compact_SecondJetMovingDegree

namespace ProximityPrize.SubmissionLower.SecondJetMovingDegree
open scoped BigOperators
open RCN026 RCN095 RCN187 RCN204 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end
end ProximityPrize.SubmissionLower.SecondJetMovingDegree

end Compact_SecondJetMovingDegree

section Compact_SecondJetPoleScaling

namespace ProximityPrize.SubmissionLower.SecondJetPoleScaling
open RCN026 RCN187
noncomputable section
set_option autoImplicit false
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem pole_div_constant (v : Place K E) (a : K) (ha : a ≠ 0) (x : E) :
    poleOrder v.val (x/algebraMap K E a) = poleOrder v.val x := by
  letI : v.val.IsTrivialOn K := v.property.2
  have hc : v.val (algebraMap K E a) = 1 := Valuation.IsTrivialOn.eq_one a ha
  simp only [poleOrder,Valuation.map_div,hc,div_one]

theorem pole_half (v : Place K E) (h2 : (2 : K) ≠ 0) (x : E) :
    poleOrder v.val (x/2) = poleOrder v.val x := by
  simpa only [map_ofNat] using pole_div_constant v 2 h2 x

end
end ProximityPrize.SubmissionLower.SecondJetPoleScaling

end Compact_SecondJetPoleScaling

section Compact_SecondJetActiveMovingBudget

namespace ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (SeparableCoordinate coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K : Type} [Field K] [IsAlgClosed K]

end
end ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget

end Compact_SecondJetActiveMovingBudget

section Compact_SecondJetRetainedBudgets

namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets
open scoped Classical BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

end
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets

end Compact_SecondJetRetainedBudgets

section Compact_SecondJetExceptionalComponents

namespace ProximityPrize.SubmissionLower.SecondJetExceptionalComponents
open MvPolynomial RCN264
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K] {Seed : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Seed := Classical.decEq Seed

theorem component_empty_of_nonvanishing (F A H T : MvPolynomial (Fin 3) K)
    (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (C : RegularComponent K F A H) (hT : T ∈ C.1)
    (hne : ∀ x ∈ Gamma, MvPolynomial.eval (point x) T ≠ 0) :
    (componentSeeds K F A H Gamma point C).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxG := componentSeeds_subset K F A H Gamma point C hx
  have hpoint := componentSeeds_on_prime K F A H Gamma point C x hx
  have hz := hpoint hT
  exact hne x hxG hz

end
end ProximityPrize.SubmissionLower.SecondJetExceptionalComponents

end Compact_SecondJetExceptionalComponents

section Compact_SecondJetRetainedStage

namespace ProximityPrize.SubmissionLower.SecondJetRetainedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.SecondJetRetainedStage

end Compact_SecondJetRetainedStage

section Compact_C2Geometry80788

set_option Elab.async false

section Adapted_LocatorFixedStage
namespace ProximityPrize.SubmissionLower.Lower80788.FixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def w:ℕ:=131071
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
    identityCurveDegree flag a b s w=
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
end
end ProximityPrize.SubmissionLower.Lower80788.FixedStage

end Adapted_LocatorFixedStage

section Adapted_LocatorFixed
namespace ProximityPrize.SubmissionLower.Lower80788.Fixed
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 LocatorFactorAggregate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.Fixed

end Adapted_LocatorFixed

section Adapted_LocatorHybridIdentityC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

open RCN095 RCN146 RCN203 RCN206 LocatorFactorAggregate LocatorHybridCost
open LocatorHybridCostC1 LocatorHybridCostC2 RCN198

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def w : ℕ := 131071

theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simp only [identityCurveDegree, paddedCut,
    RCN206.centreFlag, RCN206.directionFlag,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all, w]
  ring

def reducedABS (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * 131072, 1 + (2 * b + 2) * 131072, (2 * s + 2) * 131072⟩
def rationalABS (a b s : ℕ) : FlagDegree :=
  ⟨131072 * a + 2 * a, 131072 * b + 2 * b + 2, 131072 * s + 2 * s + 3⟩
def mfibABS (a b s : ℕ) : FlagDegree := ⟨a, b + 1, s + 3⟩
def mcutABS (a b s : ℕ) : FlagDegree := rationalABS a b s + ⟨0, 131072, 262144⟩

end ProximityPrize.SubmissionLower.Lower80788.HybridIdentityC2

end Adapted_LocatorHybridIdentityC2

section Adapted_LocatorHybridGatesC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2
open RCN095 LocatorHybridCells LocatorHybridCellsC1

end ProximityPrize.SubmissionLower.Lower80788.HybridGatesC2

end Adapted_LocatorHybridGatesC2

section Adapted_LocatorFixedHybridC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN081 RCN135 RCN095 RCN238 RCN243 RCN222 RCN266 RCN221 RCN268 RCN140 RCN275 RCN130 RCN156 RCN159 RCN234 RCN137 RCN198 RCN263 RCN146 RCN287 RCN136 RCN086 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open Lower80788.HybridIdentityC2 LocatorHybridCells LocatorHybridCellsC1
open LocatorHybridTailProvider LocatorHybridTailProviderC1
open Lower80788.HybridGatesC2 Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.FixedHybridC2

end Adapted_LocatorFixedHybridC2

section Adapted_LocatorHybridRealizeC2
namespace ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open LocatorHybridTailProviderC1
open Lower80788.HybridGatesC2
open Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.HybridRealizeC2

end Adapted_LocatorHybridRealizeC2

section Adapted_LocatorFixedOwnBoundC2
namespace ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open LocatorFactorAggregate LocatorHybridCostC2 Lower80788.Fixed
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

end
end ProximityPrize.SubmissionLower.Lower80788.FixedOwnBoundC2

end Adapted_LocatorFixedOwnBoundC2

end Compact_C2Geometry80788

section Compact_SecondJetIdentity

namespace ProximityPrize.SubmissionLower.SecondJetIdentity
open RCN146 RCN086 RCN095 RCN198 RCN206 RCN263 RCN327 LocatorHybridCells LocatorHybridCellsC1
open Lower80788.HybridIdentityC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem cell_first_eq (t y r : ℕ) :
    cellFirstTail t y r = reducedABS (cellA t y) (cellB y r) (cellS r) := by
  unfold cellFirstTail cellSupport
  rw [Lower80788.FixedStage.tail_support_formula]
  simp only [RCN327.w,reducedABS]
  congr 1 <;> ring

theorem cell_normal_eq (t y r : ℕ) :
    cellHybridCoordinateC1 t y r = rationalABS (cellA t y) (cellB y r) (cellS r) := by
  simp only [cellHybridCoordinateC1,cellRational,cellDirection,directionFlag,rationalABS,RCN327.w]
  congr 1 <;> ring

end
end ProximityPrize.SubmissionLower.SecondJetIdentity

end Compact_SecondJetIdentity

section Compact_SecondJetFixedStage

namespace ProximityPrize.SubmissionLower.SecondJetFixedStage
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

end
end ProximityPrize.SubmissionLower.SecondJetFixedStage

end Compact_SecondJetFixedStage

section Compact_SecondJetRegularGeometry

namespace ProximityPrize.SubmissionLower.SecondJetRegularGeometry
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open RCN084 RCN146 RCN087 RCN335 RCN174 RCN275 RCN234 RCN156
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

open RCN081 RCN130 RCN221 RCN222 RCN137 RCN238 RCN275

end
end ProximityPrize.SubmissionLower.SecondJetRegularGeometry

end Compact_SecondJetRegularGeometry

section Compact_SecondJetProperCounting

namespace ProximityPrize.SubmissionLower.SecondJetProperCounting
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001 RCN052
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K] {ι : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ι := Classical.decEq ι


end
end ProximityPrize.SubmissionLower.SecondJetProperCounting

end Compact_SecondJetProperCounting

section Compact_SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open MvPolynomial RCN260 RCN052 RCN294 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type} [Field K]



end
end ProximityPrize.SubmissionLower.SecondJetPairBounds

end Compact_SecondJetPairBounds

section Compact_SecondJetRegularData

namespace ProximityPrize.SubmissionLower.SecondJetRegularData
open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN260 RCN174 RCN275 RCN327
open RCN156 RCN234 LocatorHybridCells LocatorHybridCellsC1 RCN130 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

namespace Data
variable {nodes : I ↪ K} {u0 u1 : I → K}

end Data
end
end ProximityPrize.SubmissionLower.SecondJetRegularData

end Compact_SecondJetRegularData






section Compact_SecondJetClippedRectangle

namespace ProximityPrize.SubmissionLower.SecondJetClippedRectangle
open scoped BigOperators
open SecondJetCounts
set_option autoImplicit false
set_option maxHeartbeats 4000000





end ProximityPrize.SubmissionLower.SecondJetClippedRectangle

end Compact_SecondJetClippedRectangle






section Compact_SecondJetRelaxedCounts

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCounts
open scoped BigOperators
open SecondJetRelaxedSourceCounts SecondJetRelaxedKernelCounts
noncomputable section
set_option autoImplicit false



variable {K : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedCounts

end Compact_SecondJetRelaxedCounts



section Compact_SecondJetRelaxedDifferentiation

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetGlobalDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K]

def reserve (k n0 h : ℕ) : ℕ := if h < n0 then h else k

theorem reserve_ge_order (k n0 h d : ℕ) (hdk : d ≤ k) (hdh : d ≤ h) :
    d ≤ reserve k n0 h := by
  unfold reserve
  split <;> assumption



end
end ProximityPrize.SubmissionLower.SecondJetRelaxedDifferentiation

end Compact_SecondJetRelaxedDifferentiation

section Compact_SecondJetRelaxedCoefficientsReceipt

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetRelaxedDifferentiation
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.SecondJetRelaxedCoefficientsReceipt

end Compact_SecondJetRelaxedCoefficientsReceipt

section Compact_SecondJetRelaxedRanksReceipt

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt
open SecondJetRelaxedCounts SecondJetRelaxedCoefficientsReceipt
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

end ProximityPrize.SubmissionLower.SecondJetRelaxedRanksReceipt

end Compact_SecondJetRelaxedRanksReceipt

section Compact_SecondJetRelaxedInterpolation

namespace ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize SecondJetDifferentiation
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation

end Compact_SecondJetRelaxedInterpolation

section Compact_SecondJetLeadingCoefficient

namespace ProximityPrize.SubmissionLower.SecondJetLeadingCoefficient
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

end
end ProximityPrize.SubmissionLower.SecondJetLeadingCoefficient

end Compact_SecondJetLeadingCoefficient

section Compact_SecondJetProperAlternatives

namespace ProximityPrize.SubmissionLower.SecondJetProperAlternatives
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights SecondJetRelaxedInterpolation
open SecondJetRelaxedCoefficientsReceipt RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetProperAlternatives

end Compact_SecondJetProperAlternatives

section Compact_SecondJetRounding

namespace ProximityPrize.SubmissionLower.SecondJetRounding
set_option autoImplicit false

end ProximityPrize.SubmissionLower.SecondJetRounding

end Compact_SecondJetRounding

section Compact_SecondJetCombinedCount

namespace ProximityPrize.SubmissionLower.SecondJetCombinedCount
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222
open SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetCombinedCount

end Compact_SecondJetCombinedCount

section Compact_SecondJetNumericGeometry

namespace ProximityPrize.SubmissionLower.SecondJetNumericGeometry
open RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetNumericGeometry

end Compact_SecondJetNumericGeometry

section Compact_SecondJetOwnShape

namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open LocatorHybridCells LocatorHybridCellsC1
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}



end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

end Compact_SecondJetOwnShape

section Compact_SecondJetUniformReceipts

namespace ProximityPrize.SubmissionLower.SecondJetUniformReceipts
open SecondJetNumericGeometry RCN260 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetUniformReceipts

end Compact_SecondJetUniformReceipts

section Compact_SecondJetProperReceipts

namespace ProximityPrize.SubmissionLower.SecondJetProperReceipts
open SecondJetNumericGeometry RCN260 RCN095 RCN294
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.SecondJetProperReceipts

end Compact_SecondJetProperReceipts

section Compact_SecondJetProfileBounds

namespace ProximityPrize.SubmissionLower.SecondJetProfileBounds
open RCN135 SecondJetOwnShape
open SecondJetNumericGeometry SecondJetUniformReceipts SecondJetRelaxedInterpolation
open SecondJetProperReceipts
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

end
end ProximityPrize.SubmissionLower.SecondJetProfileBounds

end Compact_SecondJetProfileBounds

section Compact_SecondJetAffineCeiling

namespace ProximityPrize.SubmissionLower.SecondJetAffineCeiling
open RCN095
set_option autoImplicit false
set_option maxHeartbeats 2000000

end ProximityPrize.SubmissionLower.SecondJetAffineCeiling

end Compact_SecondJetAffineCeiling

section Compact_SecondJetSingleCap

namespace ProximityPrize.SubmissionLower.SecondJetSingleCap
open RCN095 LocatorFactorAggregate
open SecondJetOwnShape SecondJetAffineCeiling
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetSingleCap

end Compact_SecondJetSingleCap

section Compact_SecondJetRowIntervals

namespace ProximityPrize.SubmissionLower.SecondJetRowIntervals
open LocatorPhase6800Oracle
set_option autoImplicit false
set_option maxHeartbeats 3000000

def pickTail (z : ℕ) (a : BaseSegment) : List BaseSegment → BaseSegment
  | [] => a
  | s::ss => pickTail z (if s.start ≤ z then s else a) ss

def BaseCell (q : BaseRow) (lo hi : ℕ) : Prop :=
  lo=hi ∨ (3 ≤ lo ∧ match q.segments with
    | [] => True
    | a::ss => a.start ≤ lo ∧ ∀ s ∈ ss, s.start ≤ lo ∨ hi < s.start)
instance (q : BaseRow) (lo hi : ℕ) : Decidable (BaseCell q lo hi) := by
  unfold BaseCell
  cases q.segments <;> infer_instance

end ProximityPrize.SubmissionLower.SecondJetRowIntervals

end Compact_SecondJetRowIntervals
