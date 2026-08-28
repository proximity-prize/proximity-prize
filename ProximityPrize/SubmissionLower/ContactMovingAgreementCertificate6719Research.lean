import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactBaseIdealAgreementFlags6676Research
import ProximityPrize.SubmissionLower.ContactMovingProjection6676Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet6656Research

namespace ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
open scoped Classical BigOperators
open ContactTaylorNumerators ContactGenericSurface ContactPrimeSeedIncidence
open ContactBaseIdealAgreement6676Research ContactBaseIdealAgreementFlags6676Research
open ContactFlagBezout6543Research ContactMovingProjection6676Research
open ContactPost6464MinkowskiRecurrenceResearch ContactIdentityResidualGlobalFlagResearch
open ContactResidualSupportParametersResearch ContactSharpTaylorFixedMeet6656Research

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Ω : Type} [Field K] [Field Ω]

def direction (a b s : ℕ) : FlagDegree := ⟨2*a,2*b+1,2*s+3⟩
def center (a b s : ℕ) : FlagDegree := unitYZFlag + direction a b s
def support (a b s : ℕ) : ResidualSupportParameters :=
  ⟨s+2,b+s+3,a+b+s+3,by omega,by omega,by omega,by omega⟩

theorem shifted_flags (a b s : ℕ) :
    hFlag a (b+1) (s+2) = ⟨a,b+1,s+1⟩ ∧
    gFlag a (b+1) (s+2) = ⟨a,b,s+3⟩ ∧
    directionFlag a (b+1) (s+2) = direction a b s := by
  refine ⟨?_,?_,?_⟩ <;>
    simp only [hFlag,gFlag,directionFlag,direction] <;> congr 1 <;> omega

theorem class_total (a b s k : ℕ) :
    unitYZFlag + (k+1) • direction a b s =
      center a b s + k • direction a b s := by
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [center, direction, unitYZFlag,
    add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

theorem support_data (a b s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : wt ![0,1,1,1] F ≤ a+b+s+3) :
    ResidualSupportData (support a b s) F := by
  refine ⟨?_,hYR,hAll⟩
  have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
    funext i; fin_cases i <;> rfl
  simpa only [hw, wt, support, MvPolynomial.weightedTotalDegree_piSingle] using hR

theorem sharp_flag_eq (a b s d : ℕ) :
    sharpResidualAgreementFlag (support a b s) d =
      unitYZFlag + d • direction a b s := by
  have hdir : sharpAgreementDirection (support a b s) = direction a b s := by
    simp only [sharpAgreementDirection, support, direction]
    congr 1 <;> omega
  simp only [sharpResidualAgreementFlag, hdir, direction, unitYZFlag]
  change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
  congr 1 <;> simp only [add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all] <;> ring

theorem low_agreement_in_center (φ : Polynomial K →+* Ω)
    (a b s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : wt ![0,1,1,1] F ≤ a+b+s+3)
    (d : ℕ) (hd : d ≤ 1) (x u0 u1 : K) :
    PolynomialInFlag (center a b s) (agreementPolynomial φ F d x u0 u1) := by
  have hh := surfaceMap_agreement_in_sharp_flag
    (P := support a b s) (by dsimp [support]; omega) φ
    (support_data a b s F hR hYR hAll) d (fun j : ℕ => (j.factorial : K)⁻¹) x u0 u1
  rw [sharp_flag_eq] at hh
  intro q hq
  have h := hh q hq
  change InFlag (center a b s) q
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
  · simp [InFlag, center, direction, unitYZFlag] at h ⊢
    omega
  · simpa [center, InFlag, direction, unitYZFlag] using h


theorem exists_actual_agreement_certificate (φ : Polynomial K →+* Ω)
    (a b s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : wt ![0,1,1,1] F ≤ a+b+s+3)
    (d : ℕ) (x u0 u1 : K) :
    ∃ (B : Fin (d-1+1) → MvPolynomial (Fin 3) Ω)
      (c : Fin (d-1+1) → FlagDegree),
      agreementPolynomial φ F d x u0 u1 =
        filteredCut (d-1) B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)) ∧
      (∀ j, PolynomialInFlag (c j) (B j)) ∧
      (∀ j, c j + (d-1-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree) +
        j.val • (⟨a,b,s+3⟩ : FlagDegree) =
          center a b s + (d-1) • direction a b s) ∧ d-1 ≤ d := by
  classical
  by_cases hd : 2 ≤ d
  · let coeffs : ℕ → K := fun j => (j.factorial : K)⁻¹
    let B0 := fun j => surfaceMap φ (agreementCoefficients F d coeffs x u0 u1 j)
    refine ⟨(fun j => B0 j.val), (fun j => coefficientFlag a (b+1) (s+2) d j.val), ?_, ?_, ?_, Nat.sub_le _ _⟩
    · change surfaceMap φ (agreementNumerator F d coeffs x u0 u1) = _
      rw [surfaceMap_agreementNumerator_eq_coefficient_sum φ F d hd]
      have hk : d-1+1=d := by omega
      calc
        _ = ∑ j : Fin (d-1+1), surfaceMap φ (polyH K F) ^ (d-1-j.val) *
              surfaceMap φ (polyG K F) ^ j.val * B0 j.val := by
          let f := fun j : ℕ => surfaceMap φ (polyH K F) ^ (d-1-j) *
            surfaceMap φ (polyG K F) ^ j * B0 j
          change (∑ j ∈ Finset.range d, f j) = ∑ j : Fin (d-1+1), f j.val
          rw [Finset.sum_range]
          let E : Fin d ≃ Fin (d-1+1) := {
            toFun := fun j => ⟨j.val, by have := j.isLt; omega⟩
            invFun := fun j => ⟨j.val, by have := j.isLt; omega⟩
            left_inv := fun j => rfl
            right_inv := fun j => rfl }
          exact Fintype.sum_equiv E _ _ (fun _ => rfl)
        _ = _ := by
          unfold filteredCut
          apply Finset.sum_congr rfl
          intro j hj
          ring
    · intro j
      apply surfaceMap_agreementCoefficients_in_flag φ F a (b+1) (s+2)
        (by omega) (by omega) hR (by omega)
        (by omega) d hd coeffs x u0 u1 j.val
      have := j.isLt
      omega
    · intro j
      have hj : j.val < d := by have := j.isLt; omega
      have h := coefficientFlag_add_baseMonomial a (b+1) (s+2) d j.val
        (by omega) (by omega) hj
      rw [(shifted_flags a b s).1, (shifted_flags a b s).2.1,
        (shifted_flags a b s).2.2] at h
      refine h.trans ?_
      have hk : d-1+1=d := by omega
      simpa only [hk] using class_total a b s (d-1)
  · have hd' : d ≤ 1 := by omega
    have hk : d-1=0 := by omega
    refine ⟨(fun _ => agreementPolynomial φ F d x u0 u1), (fun _ => center a b s), ?_, ?_, ?_, Nat.sub_le _ _⟩
    · rw [hk]
      unfold filteredCut
      rw [Fin.sum_univ_one]
      simp
    · intro j
      exact low_agreement_in_center φ a b s F hR hYR hAll d hd' x u0 u1
    · intro j
      have hj : j.val=0 := by have := j.isLt; omega
      simp only [hk, hj, Nat.sub_zero]
      change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
      congr 1 <;> simp [center, direction, unitYZFlag]

end
end ProximityPrize.SubmissionLower.ContactMovingAgreementCertificate6719Research
