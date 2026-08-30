import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.J
namespace ProximityPrize.SubmissionLower.ContactConstantSeedCoordinateResearch
open scoped Classical
open ActualCurveCoordinateField ActualCurveZeroCount
 ContactPrimeSeedIncidence
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem point_coordinate_eq_scalar
   (i:Fin 3) (c:Ω)
   (hc:algebraMap Ω (CoordinateField Ω P) c=coordinate Ω P i)
   (v:Fin 3 → Ω)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom):
   v i=c:=by
 let Q:MvPolynomial (Fin 3) Ω:=MvPolynomial.X i-MvPolynomial.C c
 have hQ:Q∈P:=by
   rw [←aeval_coordinate_ker Ω P]
   change MvPolynomial.aeval (coordinate Ω P) Q=0
   simp only [Q,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
   exact sub_eq_zero.mpr hc.symm
 have hz:=hv hQ
 change MvPolynomial.aeval v Q=0 at hz
 simpa only [Q,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
   sub_eq_zero,Algebra.algebraMap_self_apply] using hz
theorem selected_seed_set_card_le_one_of_seedCoordinate_isAlgebraic
   (selected:K → Polynomial K) (Γ:Finset K)
   (hpoint:∀ γ∈Γ,
     P ≤ RingHom.ker
       (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hZ:IsAlgebraic Ω (coordinate Ω P 2)):
   Γ.card ≤ 1:=by
 obtain ⟨c,hc⟩:=coordinate_eq_scalar_of_isAlgebraic Ω P 2 hZ
 apply Finset.card_le_one.mpr
 intro γ hγ η hη
 have hcγ:=point_coordinate_eq_scalar P 2 c hc
   (selectedPoint φ selected γ) (hpoint γ hγ)
 have hcη:=point_coordinate_eq_scalar P 2 c hc
   (selectedPoint φ selected η) (hpoint η hη)
 have hc:(φ.comp Polynomial.C) γ=(φ.comp Polynomial.C) η:=by
   simpa only [selectedPoint_seed] using hcγ.trans hcη.symm
 exact (φ.comp Polynomial.C).injective hc
end
end ProximityPrize.SubmissionLower.ContactConstantSeedCoordinateResearch
