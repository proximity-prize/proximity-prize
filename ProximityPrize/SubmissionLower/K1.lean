import ProximityPrize.SubmissionLower.K2
import ProximityPrize.SubmissionLower.AN
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedChannel6733Research
open scoped Classical BigOperators
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ActualCurveCoordinateField ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedResidueWeight6733Research
open ContactFlagPlaneIndexedCost6733Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactPlaneRelationCoefficientFiber6733Research
open ContactAdaptiveProjectionCoordinateResearch CoordinateBoxZeroCount
open ContactWeightedGroupedResultantChannel6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {A:Type} [Fintype A]
variable (component:A → RegularComponent Omega G T H)
variable (hcomponent:Function.Injective component)
variable (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
noncomputable def indexedWeightedFlagPlaneChannel_of_fixedFactors
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (multiplicity:A → ℕ)
   (resultant:Polynomial (RatFunc Omega)) (budget:ℕ)
   (hresultant:resultant≠0)
   (hdegree:resultant.natDegree ≤ budget)
   (hfixed:∀ (q:Polynomial (RatFunc Omega))
     (hq:Irreducible q) (hqMonic:q.Monic)
     (a₀:IndexedFactorFiber component lam mu nu order ht q),
     q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
       multiplicity a.1*indexedPlaneResidueWeight component
         lam mu nu order ht hfinite a.1)∣resultant):
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     (fun a↦coordinateDegree Omega (CoordinateField Omega (component a).1)
       (coordinateOfGate
         (flagEvaluation Omega (component a).1 lam mu nu
           (MvPolynomial.X (order 0))) (hgate a))) budget:=by
 let factor:=indexedComponentFactor component lam mu nu order ht
 let weight:=indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   residueWeight:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   groupedPowerDvd:=?_
   cost_le_residue_mul_degree:=?_
   resultant_degree_le:=hdegree}
 · intro a
   exact projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,multiplicity b*weight b)=
         ∑ b:IndexedFactorFiber component lam mu nu order ht (factor a),
           multiplicity b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦multiplicity b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost:=indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
     component lam mu nu order ht hfinite hgen hgate a
   simpa only [factor,weight,Nat.mul_comm] using hcost.le
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedChannel6733Research
