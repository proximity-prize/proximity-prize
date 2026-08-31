import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch

 









namespace ProximityPrize.SubmissionLower
namespace ContactRFreeFixedSelectedCombinerResearch

open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactImplicitContactLift ContactPrimeSeedIncidence
open ContactRegularFactorFlag6600Research
open ContactFlagBezout6543Research
open ContactGlobalSelectedFamilies6600Research
open ContactTightSingularLedgerResearch
open ContactRobustFixedMeet6656Research
open ContactProfileFixedSelectedCombinerResearch

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 40000

variable {K Iota : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

 
theorem no_regularIndex_of_R_degree_zero
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hR : Q.degreeOf (2 : Fin 4) = 0) :
    IsEmpty (RegularIndex Q) := by
  constructor
  intro F
  have hspec := positiveRFactors_spec Q F.1 F.2
  have hle := ContactFactorCaps.degreeOf_le_of_dvd
    (2 : Fin 4) F.1 Q hspec.2.1 hQ
  omega

 

theorem global_count_le_tight_countCap_of_R_degree_zero
    (p : Profile)
    (t : ContactTightSingularLedgerResearch.TightParameters)
    (A : FixedParameterAlignment p t)
    {prime : ℕ}
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K p.weightedCap p.w
      p.seedTotalCap p.slopeCap)
    (hR : Q.degreeOf (2 : Fin 4) = 0)
    (hs : 1 ≤ p.slopeCap) (hsSmall : p.slopeCap < prime)
    (hw : 1 ≤ p.w) (hchar : p.w < prime)
    (hDw : p.w < (2 * p.slopeCap - 1) * p.weightedCap)
    (hj : 1 ≤ (2 * p.slopeCap - 1) * p.seedTotalCap)
    (hjSmall : (2 * p.slopeCap - 1) * p.seedTotalCap < prime)
    (hjYSmall : t.implicitYCap < prime)
    (hmixedSmall : 2 * t.implicitYCap * t.algebraicCap < prime)
    (hwa : p.w < p.agreements) (han : p.agreements ≤ p.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = p.n)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ p.w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      p.agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma p.w p.errors) :
    Gamma.card ≤ t.countCap := by
  letI : IsEmpty (RegularIndex Q) :=
    no_regularIndex_of_R_degree_zero Q hQ hR
  have h := global_count_le_regular_div_add_tight_countCap
    p t A (prime := prime) (regularNumerator := 0)
    Q hQ hbox hs hsSmall hw hchar hDw hj hjSmall hjYSmall hmixedSmall
    hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution
    hagreement hnoPencil
    (fun _ ↦ ⟨0, 0, 0⟩) (fun _ ↦ 0)
    (fun count _ ↦ by
      have hz : (∑ F : RegularIndex Q, count F) = 0 := by
        exact Finset.sum_eq_zero (fun F _ ↦ isEmptyElim F)
      simp only [hz, zero_mul, le_refl])
    (fun F ↦ isEmptyElim F)
  simpa using h

def e80112RFreeProfile : Profile :=
  ⟨262144, 131071, 182032, 6072504, 1269, 1⟩

def e80112RFreeTight : ContactTightSingularLedgerResearch.TightParameters :=
  ⟨262144, 131071, 182032, 6072504, 1269, 1⟩

def e80112RFreeAlignment :
    FixedParameterAlignment e80112RFreeProfile e80112RFreeTight where
  n := rfl
  w := rfl
  agreements := rfl
  weightedCap := rfl
  seedTotalCap := rfl
  slopeCap := rfl

theorem e80112RFree_countCap_exact :
    e80112RFreeTight.countCap = 118080457743 := by
  norm_num [e80112RFreeTight,
    ContactTightSingularLedgerResearch.TightParameters.errors,
    ContactTightSingularLedgerResearch.TightParameters.gap,
    ContactTightSingularLedgerResearch.TightParameters.kappa,
    ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
    ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
    ContactTightSingularLedgerResearch.TightParameters.agreement,
    ContactTightSingularLedgerResearch.TightParameters.aggregateCost,
    ContactTightSingularLedgerResearch.TightParameters.coreNumerator,
    ContactTightSingularLedgerResearch.TightParameters.tightNumerator,
    ContactTightSingularLedgerResearch.TightParameters.countCap,
    ContactSingularLedger6600Research.dot]

 

theorem e80112_rfree_fixed_count_le
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    [CharP K 2130706433]
    (hbox : H ∈ globalCoefficientBox K 6072504 131071 1269 1)
    (hR : H.degreeOf (2 : Fin 4) = 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma H = 0)
    (hagreement : ∀ gamma ∈ Gamma, 182032 ≤
      (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma 131071 80112) :
    Gamma.card ≤ 118080457743 := by
  have h := global_count_le_tight_countCap_of_R_degree_zero
    e80112RFreeProfile e80112RFreeTight e80112RFreeAlignment
    (prime := 2130706433) H hH hbox hR
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeTight,
      ContactTightSingularLedgerResearch.TightParameters.kappa,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap])
    (by norm_num [e80112RFreeTight,
      ContactTightSingularLedgerResearch.TightParameters.kappa,
      ContactTightSingularLedgerResearch.TightParameters.implicitYCap,
      ContactTightSingularLedgerResearch.TightParameters.algebraicCap])
    (by norm_num [e80112RFreeProfile])
    (by norm_num [e80112RFreeProfile])
    selected Gamma nodes x u0 u1 hinj
    (by simpa [e80112RFreeProfile] using hnodes)
    (by simpa [e80112RFreeProfile] using hdegree)
    hsolution
    (by simpa [e80112RFreeProfile] using hagreement)
    (by simpa [e80112RFreeProfile,
      ContactRobustFixedMeet6656Research.Profile.errors] using hnoPencil)
  simpa only [e80112RFree_countCap_exact] using h

end
end ContactRFreeFixedSelectedCombinerResearch
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactRFreeFixedSelectedCombinerResearch.global_count_le_tight_countCap_of_R_degree_zero
