import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.O1
namespace ProximityPrize.SubmissionLower.ContactPolynomiality
open DifferentialTaylorCoefficients DifferentialTaylorHom
open ContactDifferentialRing ContactRegularPoint
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section GeneralTaylorCoordinates
variable {K A L:Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]
theorem iterate_affine_coordinate_ge_two
   (D:Derivation K A A) (a:A) (ha:D a=1) (j:ℕ):
   D^[j+2] a=0:=by
 rw [Function.iterate_add_apply]
 change D^[j] (D (D a))=0
 rw [ha,D.map_one_eq_zero]
 exact iterate_zero D j
theorem jetPolynomial_affine_coordinate
   (D:Derivation K A A) (value:A →+*L) (bound:ℕ)
   (hbound:2 ≤ bound) (a:A) (ha:D a=1):
   jetPolynomial D value bound a=Polynomial.C (value a)+Polynomial.X:=by
 ext j
 cases j with
 | zero =>
   have hb:0 < bound:=by omega
   simp [jetPolynomial_coeff,jetCoefficient,hb]
 | succ j =>
   cases j with
   | zero =>
     have hb:1 < bound:=by omega
     simp [jetPolynomial_coeff,jetCoefficient,hb,ha]
   | succ j =>
     have hz:jetCoefficient D value a (j+2)=0:=by
       simp only [jetCoefficient,iterate_affine_coordinate_ge_two D a ha j,
         map_zero,zero_div]
     have hn0:j+2≠0:=by omega
     have hn1:j+2≠1:=by omega
     change (jetPolynomial D value bound a).coeff (j+2)=
       (Polynomial.C (value a)+Polynomial.X).coeff (j+2)
     simp [jetPolynomial_coeff,hz,Polynomial.coeff_C,Polynomial.coeff_X,hn0,hn1]
theorem jetPolynomial_natDegree_le
   (D:Derivation K A A) (value:A →+*L) (w:ℕ) (a:A):
   (jetPolynomial D value (w+1) a).natDegree ≤ w:=by
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro j hj
 rw [jetPolynomial_coeff,if_neg (by omega)]
end GeneralTaylorCoordinates
section ActualRegularPoint
variable {K L:Type*} [CommRing K] [Field L]
noncomputable def reconstructedPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 jetPolynomial (contactDerivation K F)
   (regularPointValue coefficients F v hF hregular) (w+1)
   (contactCoordinate K F (1:Fin 4))
noncomputable def reconstructionSubstitution
   (v:Fin 4 → L) (P:Polynomial L):Fin 4 → Polynomial L:=
 ![Polynomial.C (v 0)+Polynomial.X,P,P.derivative,Polynomial.C (v 3)]
noncomputable def reconstructedEquation
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
   (reconstructionSubstitution v (reconstructedPolynomial coefficients F v hF hregular w)) F
theorem reconstructedPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).natDegree ≤ w:=
 jetPolynomial_natDegree_le _ _ _ _
theorem reconstructedPolynomial_coeff_zero
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 0=v 1:=by
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,
   regularPointValue_coordinate]
theorem reconstructedPolynomial_coeff_one
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (reconstructedPolynomial coefficients F v hF hregular w).coeff 1=v 2:=by
 have hb:1 < w+1:=by omega
 simp [reconstructedPolynomial,jetPolynomial_coeff,jetCoefficient,hb,
   derivation_coordinate_Y,regularPointValue_coordinate]
theorem coordinate_taylor_eq_reconstruction
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   ∀ i:Fin 4,
     jetPolynomial (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular) bound
       (contactCoordinate K F i)=
     reconstructionSubstitution v
       (reconstructedPolynomial coefficients F v hF hregular w) i:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let P:=reconstructedPolynomial coefficients F v hF hregular w
 have hbound:0 < bound:=by omega
 have hfull:jetPolynomial D value bound (contactCoordinate K F (1:Fin 4))=P:=by
   apply jetPolynomial_eq_shorter_of_tails_zero D value (w+1) bound
     (contactCoordinate K F (1:Fin 4)) hshort
   intro j hj hjbound
   exact htails j (by omega) hjbound.le
 have hlast:jetCoefficient D value (contactCoordinate K F (1:Fin 4)) bound=0:=
   htails bound (by omega) le_rfl
 have hdr:=jetPolynomial_derivation_eq_derivative_of_char D value p bound hchar
   (contactCoordinate K F (1:Fin 4)) hlast
 have hDy:D (contactCoordinate K F (1:Fin 4))=
     contactCoordinate K F (2:Fin 4):=derivation_coordinate_Y K F
 rw [hDy,hfull] at hdr
 have hx:=jetPolynomial_affine_coordinate D value bound (by omega)
   (contactCoordinate K F (0:Fin 4)) (derivation_coordinate_X K F)
 have hvalueX:value (contactCoordinate K F (0:Fin 4))=v 0:=
   regularPointValue_coordinate K coefficients F v hF hregular 0
 rw [hvalueX] at hx
 have hz:=jetPolynomial_of_derivation_eq_zero D value bound hbound
   (contactCoordinate K F (3:Fin 4)) (derivation_coordinate_Z K F)
 have hvalueZ:value (contactCoordinate K F (3:Fin 4))=v 3:=
   regularPointValue_coordinate K coefficients F v hF hregular 3
 rw [hvalueZ] at hz
 intro i
 fin_cases i
 · exact hx
 · exact hfull
 · exact hdr
 · exact hz
theorem polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0)
   (hdegree:(reconstructedEquation coefficients F v hF hregular w).natDegree < bound):
   reconstructedEquation coefficients F v hF hregular w=0:=by
 let D:=contactDerivation K F
 let value:=regularPointValue coefficients F v hF hregular
 let sigmaPolys:=reconstructionSubstitution v
   (reconstructedPolynomial coefficients F v hF hregular w)
 have hcoeff:value.comp (algebraMap K (ContactRing K F))=coefficients:=
   regularPointValue_comp_algebraMap coefficients F v hF hregular
 have hcoordinates:∀ i:Fin 4,
     jetPolynomial D value bound (contactCoordinate K F i)=sigmaPolys i:=
   coordinate_taylor_eq_reconstruction coefficients F v hF hregular p bound w
     hw hshort hchar htails
 have hfactorial:∀ j < bound,(j.factorial:L)≠0:=by
   intro j hj
   exact factorial_cast_ne_zero_below_characteristic p j (hj.trans hchar)
 have hdeg:(MvPolynomial.eval₂Hom
     (Polynomial.C.comp (value.comp (algebraMap K (ContactRing K F)))) sigmaPolys F).natDegree <
       bound:=by
   rw [hcoeff]
   exact hdegree
 have hzero:=polynomial_relation_of_taylor_substitution D value bound (by omega)
   hfactorial (contactCoordinate K F) sigmaPolys hcoordinates F
   (coordinate_relation K F) hdeg
 rw [hcoeff] at hzero
 exact hzero
end ActualRegularPoint
end ProximityPrize.SubmissionLower.ContactPolynomiality
