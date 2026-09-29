import ProximityPrize.SubmissionLower.RelativeHelperExistence
import ProximityPrize.SubmissionLower.RelativeRegularity

namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
open RCN234 (wt)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- Factor-relative interpolation for the whole regular selected family.
The only dimension premise is the explicit integer inequality; the
bounded-image rank and the agreement-order transfer are proved upstream. -/
theorem exists_proper_regular_family_helper
    {I : Type*} [Fintype I] [DecidableEq I] {DF TF RF D w L s nu : ℕ}
    (F : Poly4 K) (hF : F ≠ 0)
    (hbox : F ∈ globalCoefficientBox K DF 1 TF RF) (hT : TF ≤ L) (hR : RF ≤ s)
    (hcode : wt (RCN081.contactWeights w) F = nu)
    (htotal : TF ≤ wt RCN156.residualTotalWeights F)
    (hslope : RF ≤ wt RCN156.residualSWeights F)
    (nodes : I ↪ K) (u0 u1 : I → K) (alpha beta A : ℕ)
    (hDpos : 0 < D) (hD : D ≤ alpha*A-beta*(nu+1-w))
    (hdim : coefficientCount (D-nu) w (L-TF) (s-RF) +
      (∑ i : I,
        (localRankBound (alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)) L s-
         localRankBound ((alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1))-
           contactOrder K (nodes i) (u0 i) (u1 i) F) (L-TF) (s-RF))) <
      coefficientCount D w L s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagreement : ∀ gamma ∈ Gamma, A ≤
      ((Finset.univ : Finset I).filter
        (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card) :
    ∃ Q : Poly4 K, Q ∈ globalCoefficientBox K D w L s ∧ ¬ F ∣ Q ∧
      ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0 := by
  classical
  let m : I → ℕ := fun i => alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)
  obtain ⟨Q,hQ,hproper,hcontact⟩ := exists_proper_relative_helper K F hF hbox hT hR
    hcode.symm.le htotal hslope nodes u0 u1 m hdim
  refine ⟨Q,hQ,hproper,?_⟩
  intro gamma hgamma
  let support := (Finset.univ : Finset I).filter
    (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)
  have hv : ∀ i ∈ support, (selected gamma).eval (nodes i) = u0 i+gamma*u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmass := regular_affine_order_mass K F hF (selected gamma) gamma nodes u0 u1 support
    w nu alpha beta A (hdegree gamma hgamma) hcode.le (hregular gamma hgamma) hv
    (hagreement gamma hgamma)
  apply relative_contact_specialization_eq_zero K F Q (selected gamma) gamma nodes u0 u1 support m
    (hsolution gamma hgamma) hv (fun i _ => hcontact i)
  exact (specialization_natDegree_lt K D w L s Q (selected gamma) gamma hDpos hQ
    (hdegree gamma hgamma)).trans_le (hD.trans hmass)

end
end ProximityPrize.SubmissionLower.RelativeBounded6814

#print axioms ProximityPrize.SubmissionLower.RelativeBounded6814.exists_proper_regular_family_helper
