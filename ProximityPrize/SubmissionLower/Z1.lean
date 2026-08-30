import ProximityPrize.SubmissionLower.EC
import ProximityPrize.SubmissionLower.Y1
namespace ProximityPrize.SubmissionLower.ContactFlagResidueDegreeCostAdapter6732Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open TrivariateRationalCollection ArbitraryPlaneEvaluationFamilyResearch
open ArbitraryRationalProjectionResearch
open ContactFlagTriangularProjectionResearch
open ContactFlagAffineFamilyDegree6543Research
noncomputable section
set_option autoImplicit false
@[reducible] def residueAlgebra
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   (q:Polynomial F) (J:Ideal B)
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   Algebra (AdjoinRoot q) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap (Polynomial F) B) (by rw [hcontract])).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_finrank_eq_natDegree_mul_residue_finrank
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   [IsScalarTower F (Polynomial F) B]
   (q:Polynomial F) (hq:Irreducible q)
   (J:Ideal B) [J.IsMaximal]
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   letI:=residueAlgebra q J hcontract
   Module.finrank F (B ⧸ J)=
     q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
 letI:Fact (Irreducible q):=⟨hq⟩
 let aResidue:Algebra (AdjoinRoot q) (B ⧸ J):=
   residueAlgebra q J hcontract
 letI:Algebra (AdjoinRoot q) (B ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (B ⧸ J):=aResidue.toSMul
 let aBase:Algebra F (AdjoinRoot q):=inferInstance
 letI:SMul F (AdjoinRoot q):=aBase.toSMul
 let aTotal:Algebra F (B ⧸ J):=inferInstance
 letI:SMul F (B ⧸ J):=aTotal.toSMul
 letI:IsScalarTower F (AdjoinRoot q) (B ⧸ J):=
   IsScalarTower.of_algebraMap_eq (R:=F) (S:=AdjoinRoot q)
     (A:=B ⧸ J) fun c => by
       change Ideal.Quotient.mk J (algebraMap F B c)=
         Ideal.Quotient.mk J
           (algebraMap (Polynomial F) B (Polynomial.C c))
       apply congrArg (Ideal.Quotient.mk J)
       change algebraMap F B c=algebraMap (Polynomial F) B
         (algebraMap F (Polynomial F) c)
       exact IsScalarTower.algebraMap_apply F (Polynomial F) B c
 letI:Module.Free F (AdjoinRoot q):=
   Module.Free.of_divisionRing F (AdjoinRoot q)
 letI:Module.Free (AdjoinRoot q) (B ⧸ J):=
   Module.Free.of_divisionRing (AdjoinRoot q) (B ⧸ J)
 calc
   Module.finrank F (B ⧸ J)=
       Module.finrank F (AdjoinRoot q)*
         Module.finrank (AdjoinRoot q) (B ⧸ J):=
     (Module.finrank_mul_finrank F (AdjoinRoot q) (B ⧸ J)).symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
     rw [show Module.finrank F (AdjoinRoot q)=q.natDegree by
       change Module.finrank F (Polynomial F ⧸ Ideal.span {q})=q.natDegree
       exact finrank_quotient_span_eq_natDegree]
variable (K:Type) [Field K]
@[reducible] def flagBaseAlgebra
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Algebra (RatFunc K) (CoordinateField K P):=
 (elementEmbedding K (CoordinateField K P)
   (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
end
end ProximityPrize.SubmissionLower.ContactFlagResidueDegreeCostAdapter6732Research
