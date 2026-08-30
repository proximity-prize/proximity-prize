import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y0
import ProximityPrize.SubmissionLower.EO
namespace ProximityPrize.SubmissionLower.RCN265
open scoped Classical
open RCN002 RCN136 RCN243
open RCN264 RCN267
open RCN344
open RCN341
open RCN042
open RCN037
open RCN039
open RCN046
open RCN142
open RCN093
open RCN095
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def verticalPoint (y z:Omega):Fin 3 → Polynomial Omega:=
 ![Polynomial.C y,Polynomial.X,Polynomial.C z]
def verticalPolynomial (y z:Omega):
   MvPolynomial (Fin 3) Omega →ₐ[Omega] Polynomial Omega:=
 MvPolynomial.aeval (verticalPoint y z)
theorem verticalPolynomial_derivative (y z:Omega)
   (F:MvPolynomial (Fin 3) Omega):
   (verticalPolynomial y z F).derivative=
     verticalPolynomial y z (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp [verticalPolynomial]
 | add P Q hP hQ => simp only [map_add,Polynomial.derivative_add,hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [verticalPolynomial,verticalPoint,Polynomial.derivative_mul] at hP ⊢ <;>
       rw [hP] <;> ring
theorem aeval_verticalPolynomial_eq_coordinateEvaluation
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (y z:Omega)
   (hy:algebraMap Omega (CoordinateField Omega P) y=coordinate Omega P 0)
   (hz:algebraMap Omega (CoordinateField Omega P) z=coordinate Omega P 2)
   (F:MvPolynomial (Fin 3) Omega):
   Polynomial.aeval (coordinate Omega P 1) (verticalPolynomial y z F)=
     coordinateEvaluation Omega P F:=by
 let lhs:MvPolynomial (Fin 3) Omega →ₐ[Omega] CoordinateField Omega P:=
   (Polynomial.aeval (coordinate Omega P 1)).comp (verticalPolynomial y z)
 have hlhs:lhs=coordinateEvaluation Omega P:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [lhs,verticalPolynomial,verticalPoint,coordinate,hy,hz]
 exact AlgHom.congr_fun hlhs F
theorem y_or_z_transcendental_of_regular_polynomial
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Omega)
   (hF:F∈P)
   (hFR:MvPolynomial.pderiv (1:Fin 3) F∉P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2):=by
 by_contra hYZ
 push_neg at hYZ
 have hYalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hYZ.1
 have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hYZ.2
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hYalg
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZalg
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hiR:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 let Q:=verticalPolynomial y z F
 have hQeval:Polynomial.aeval (coordinate Omega P 1) Q=0:=by
   rw [aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz F]
   change coordinateEvaluation Omega P F=0
   have hm:F∈RingHom.ker (coordinateEvaluation Omega P).toRingHom:=by
     rwa [coordinateEvaluation_ker Omega P]
   exact hm
 have hQ:Q=0:=by
   apply transcendental_iff_injective.mp hi
   simpa using hQeval
 have hQderiv:Q.derivative=0:=by rw [hQ,Polynomial.derivative_zero]
 have hFReval:coordinateEvaluation Omega P
     (MvPolynomial.pderiv (1:Fin 3) F)=0:=by
   rw [←aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz]
   rw [←verticalPolynomial_derivative]
   simpa [Q] using congrArg
     (Polynomial.aeval (coordinate Omega P 1)) hQderiv
 apply hFR
 rw [←coordinateEvaluation_ker Omega P,RingHom.mem_ker]
 exact hFReval
variable {K:Type} [Field K]
theorem regularComponent_y_or_z_transcendental
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   Transcendental Omega (coordinate Omega C.1 0)∨
     Transcendental Omega (coordinate Omega C.1 2):=by
 let H:=regularitySurface phi F
 have hGmem:G∈C.1:=regularComponent_G_mem Omega G T H C
 have hFmem:surfaceMap phi F∈C.1:=by
   obtain ⟨Q,hQ⟩:=hdiv
   rw [hQ]
   exact C.1.mul_mem_right Q hGmem
 have hFRnot:MvPolynomial.pderiv (1:Fin 3) (surfaceMap phi F)∉C.1:=by
   rw [surfaceMap_pderiv_R]
   exact regularComponent_H_not_mem Omega G T H C
 exact y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap phi F)
   hFmem hFRnot (regularComponent_ne_point Omega G T H C)
section RefinedAdaptiveFamily
variable {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamilyYZ
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 family:AdaptiveUnitProjectionFamily base p q
 lam:Omega
 yzValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1)
       (family.yzProjection C)=affineU Omega C.1 lam
def adaptiveUnitProjectionFamilyYZ_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionData base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem AdaptiveUnitProjectionFamilyYZ.one_le_zCost_add_yzCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree}
   (P:AdaptiveUnitProjectionFamilyYZ base p q)
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (hH:H=regularitySurface phi F)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T H):
   1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C+
     P.family.toPrimeFlagBudgetFamily.yzCost C:=by
 subst H
 have hYZ:=regularComponent_y_or_z_transcendental phi F G T hdiv C
 by_cases hZ:Transcendental Omega (coordinate Omega C.1 2)
 · have hzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C:=
     P.family.one_le_toPrimeFlagBudgetFamily_zCost C hZ
   omega
 · have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=
     not_not.mp hZ
   have hY:Transcendental Omega (coordinate Omega C.1 0):=by
     rcases hYZ with hY | hZ'
     · exact hY
     · exact (hZ hZ').elim
   have hU:Transcendental Omega (affineU Omega C.1 P.lam):=by
     exact transcendental_add_smul_of_transcendental_isAlgebraic
       Omega C.1 (coordinate Omega C.1 0) (coordinate Omega C.1 2)
         P.lam hY hZalg
   have hyzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.yzCost C:=by
     apply one_le_coordinateDegree_of_transcendental_value
     rw [P.yzValue C]
     exact hU
   omega
theorem exists_adaptiveUnitProjectionFamilyYZ_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamilyYZ base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionData base hY hZ hSderiv
 exact ⟨adaptiveUnitProjectionFamilyYZ_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end RefinedAdaptiveFamily
end
end ProximityPrize.SubmissionLower.RCN265
