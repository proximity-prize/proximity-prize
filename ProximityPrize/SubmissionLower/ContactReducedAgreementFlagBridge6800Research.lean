import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactReducedAgreementPseudoRemainder6800Research
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactReducedAgreementFlagBridge6800Research

open scoped Classical BigOperators
open ContactFactorCaps ContactGenericSurface ContactTaylorNumerators
open ContactFlagBezout6543Research
open ContactReducedAgreementPseudoRemainder6800Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K Omega : Type*} [Field K] [Field Omega]

private abbrev Poly3 (Omega : Type*) [Field Omega] :=
  MvPolynomial (Fin 3) Omega

private abbrev Poly4 (K : Type*) [Field K] :=
  MvPolynomial (Fin 4) K

 


theorem surfaceMap_in_flag_of_source_nested_bounds
    (phi : Polynomial K →+* Omega) (p : FlagDegree) (Q : Poly4 K)
    (hR : Q.degreeOf 2 ≤ p.all)
    (hYR : wt ![0, 1, 1, 0] Q ≤ p.yz + p.all)
    (hTotal : wt ![0, 1, 1, 1] Q ≤ p.zOnly + p.yz + p.all) :
    PolynomialInFlag p (surfaceMap phi Q) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi Q he)
  have hs := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd).trans hR
  have hys :=
    (MvPolynomial.le_weightedTotalDegree ![0, 1, 1, 0] hd).trans hYR
  have htotal :=
    (MvPolynomial.le_weightedTotalDegree ![0, 1, 1, 1] hd).trans hTotal
  rw [weight_fin4] at hys htotal
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ p.yz + p.all at hys
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    p.zOnly + p.yz + p.all at htotal
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at hys htotal
  change d 2 ≤ p.all ∧
    d 1 + d 2 ≤ p.yz + p.all ∧
    d 1 + d 2 + d 3 ≤ p.zOnly + p.yz + p.all
  exact ⟨hs, hys, htotal⟩

 

theorem reducedAgreement_surfaceMap_in_flag
    (phi : Polynomial K →+* Omega) (p : FlagDegree)
    (F : Poly4 K) (cap middle total w : ℕ) (coeffs : ℕ → K)
    (x u₀ u₁ : K)
    (hcap : 1 ≤ cap) (hcapMiddle : cap ≤ middle)
    (hcapTotal : cap ≤ total) (hMiddle : 2 ≤ middle)
    (hTotal : 2 ≤ total)
    (hFcap : F.degreeOf 2 ≤ cap)
    (hFmiddle : wt ![0, 1, 1, 0] F ≤ middle)
    (hFtotal : wt ![0, 1, 1, 1] F ≤ total)
    (houtR : 2 * w * (cap - 1) ≤ p.all)
    (houtMiddle : 1 + 2 * w * (middle - 1) ≤ p.yz + p.all)
    (houtTotal : 1 + 2 * w * (total - 1) ≤
      p.zOnly + p.yz + p.all) :
    PolynomialInFlag p
      (surfaceMap phi (reducedAgreementNumerator F cap w coeffs x u₀ u₁)) := by
  apply surfaceMap_in_flag_of_source_nested_bounds phi p
  · exact (reducedAgreementNumerator_R_degree_le F cap w coeffs x u₀ u₁
      hcap hFcap).trans houtR
  · exact (reducedAgreementNumerator_wt_le_nested ![0, 1, 1, 0]
      (by decide) (by decide) (by decide) (by decide)
      F cap middle w coeffs x u₀ u₁ hcap hcapMiddle hMiddle hFmiddle).trans
        houtMiddle
  · exact (reducedAgreementNumerator_wt_le_nested ![0, 1, 1, 1]
      (by decide) (by decide) (by decide) (by decide)
      F cap total w coeffs x u₀ u₁ hcap hcapTotal hTotal hFtotal).trans
        houtTotal

 


def tailSelector6800 (d j : ℕ) : K := if j = d then 1 else 0

 


def literalGlobalTailCut6800
    (phi : Polynomial K →+* Omega) (F : Poly4 K) (d : ℕ) : Poly3 Omega :=
  surfaceMap phi (agreementNumerator F d (tailSelector6800 d) 0 0 0)

 
def reducedGlobalTailCut
    (phi : Polynomial K →+* Omega) (F : Poly4 K) (cap d : ℕ) :
    Poly3 Omega :=
  surfaceMap phi
    (reducedAgreementNumerator F cap d (tailSelector6800 d) 0 0 0)

 

theorem surfaceMap_source_dvd_globalTailCut_sub_reducedGlobalTailCut
    (phi : Polynomial K →+* Omega) (F : Poly4 K) (cap d : ℕ) :
    surfaceMap phi F ∣
      literalGlobalTailCut6800 phi F d - reducedGlobalTailCut phi F cap d := by
  unfold literalGlobalTailCut6800 reducedGlobalTailCut
  simpa only [map_sub] using map_dvd (surfaceMap phi)
    (agreementNumerator_sub_reducedAgreementNumerator_dvd
      F cap d (tailSelector6800 d) 0 0 0)

 

theorem cut_dvd_globalTailCut_sub_reducedGlobalTailCut
    (phi : Polynomial K →+* Omega) (F : Poly4 K) (G : Poly3 Omega)
    (hcut : G ∣ surfaceMap phi F) (cap d : ℕ) :
    G ∣ literalGlobalTailCut6800 phi F d - reducedGlobalTailCut phi F cap d :=
  hcut.trans
    (surfaceMap_source_dvd_globalTailCut_sub_reducedGlobalTailCut phi F cap d)

theorem reducedGlobalTailCut_in_flag
    (phi : Polynomial K →+* Omega) (p : FlagDegree)
    (F : Poly4 K) (cap middle total d : ℕ)
    (hcap : 1 ≤ cap) (hcapMiddle : cap ≤ middle)
    (hcapTotal : cap ≤ total) (hMiddle : 2 ≤ middle)
    (hTotal : 2 ≤ total)
    (hFcap : F.degreeOf 2 ≤ cap)
    (hFmiddle : wt ![0, 1, 1, 0] F ≤ middle)
    (hFtotal : wt ![0, 1, 1, 1] F ≤ total)
    (houtR : 2 * d * (cap - 1) ≤ p.all)
    (houtMiddle : 1 + 2 * d * (middle - 1) ≤ p.yz + p.all)
    (houtTotal : 1 + 2 * d * (total - 1) ≤
      p.zOnly + p.yz + p.all) :
    PolynomialInFlag p (reducedGlobalTailCut phi F cap d) := by
  exact reducedAgreement_surfaceMap_in_flag phi p F cap middle total d
    (tailSelector6800 d) 0 0 0 hcap hcapMiddle hcapTotal hMiddle hTotal hFcap
    hFmiddle hFtotal houtR houtMiddle houtTotal

 

theorem exists_flag_supported_globalTailCut_representative
    (phi : Polynomial K →+* Omega) (p : FlagDegree)
    (F : Poly4 K) (G : Poly3 Omega) (hcut : G ∣ surfaceMap phi F)
    (cap middle total d : ℕ)
    (hcap : 1 ≤ cap) (hcapMiddle : cap ≤ middle)
    (hcapTotal : cap ≤ total) (hMiddle : 2 ≤ middle)
    (hTotal : 2 ≤ total)
    (hFcap : F.degreeOf 2 ≤ cap)
    (hFmiddle : wt ![0, 1, 1, 0] F ≤ middle)
    (hFtotal : wt ![0, 1, 1, 1] F ≤ total)
    (houtR : 2 * d * (cap - 1) ≤ p.all)
    (houtMiddle : 1 + 2 * d * (middle - 1) ≤ p.yz + p.all)
    (houtTotal : 1 + 2 * d * (total - 1) ≤
      p.zOnly + p.yz + p.all) :
    ∃ Tred : Poly3 Omega,
      PolynomialInFlag p Tred ∧
        G ∣ literalGlobalTailCut6800 phi F d - Tred := by
  exact ⟨reducedGlobalTailCut phi F cap d,
    reducedGlobalTailCut_in_flag phi p F cap middle total d hcap hcapMiddle
      hcapTotal hMiddle hTotal hFcap hFmiddle hFtotal houtR houtMiddle houtTotal,
    cut_dvd_globalTailCut_sub_reducedGlobalTailCut phi F G hcut cap d⟩

end

end ContactReducedAgreementFlagBridge6800Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactReducedAgreementFlagBridge6800Research.exists_flag_supported_globalTailCut_representative
