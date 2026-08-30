import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.B0
namespace ProximityPrize.SubmissionLower.RCN166
open RCN002 RCN136 RCN224
open RCN139 RCN233 RCN231
open RCN229 RCN313 RCN047
open RCN147 RCN319 RCN065
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
variable (phi:Polynomial K →+*Omega)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
variable (F:MvPolynomial (Fin 4) K)
variable (hF:surfaceMap phi F∈P)
variable (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem coordinate_y_affine_of_basefield_pencil
   (w:ℕ) (P0 P1:Polynomial K)
   (hp:truncatedPolynomial phi P F hF hH w=
     P0.map (componentCoefficients phi P)+
       Polynomial.C (coordinate Omega P 2)*
         P1.map (componentCoefficients phi P)):
   coordinate Omega P 0=algebraMap Omega (CoordinateField Omega P)
       ((P0.map (phi.comp Polynomial.C)).eval (phi Polynomial.X))+
     coordinate Omega P 2*algebraMap Omega (CoordinateField Omega P)
       ((P1.map (phi.comp Polynomial.C)).eval (phi Polynomial.X)):=by
 have hp':truncatedPolynomial phi P F hF hH w=
     (P0.map (phi.comp Polynomial.C)).map
         (algebraMap Omega (CoordinateField Omega P))+
       Polynomial.C (coordinate Omega P 2)*
         (P1.map (phi.comp Polynomial.C)).map
           (algebraMap Omega (CoordinateField Omega P)):=by
   simpa only [Polynomial.map_map,componentCoefficients] using hp
 rw [←truncatedPolynomial_initial_value phi P F hF hH w,hp']
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply]
include hF hH in
theorem identityNodes_card_le_of_r_dependent_principal_zero_safe
   {iota:Type} [DecidableEq iota]
   (nodes:Finset iota) (x u0 u1:iota → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (g:MvPolynomial (Fin 3) Omega) (hP:P=Ideal.span {g})
   (hr:0 < g.degreeOf 1):
   (identityNodes phi P F nodes x u0 u1 w).card ≤ w:=by
 by_contra h
 have hc:w < (identityNodes phi P F nodes x u0 u1 w).card:=
   Nat.lt_of_not_ge h
 obtain ⟨P0,P1,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities phi P F hF hH
     nodes x u0 u1 w hinj hc
     (fun t:Empty↦t.elim) (fun t:Empty↦t.elim)
     (fun t↦t.elim) (fun t↦t.elim)
 have hy:=coordinate_y_affine_of_basefield_pencil
   phi P F hF hH w P0 P1 hp
 exact not_y_affine_of_r_dependent_principal Omega P g hP hr _ _ hy
end
end ProximityPrize.SubmissionLower.RCN166
