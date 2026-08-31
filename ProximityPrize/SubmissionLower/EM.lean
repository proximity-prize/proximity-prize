import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BH
import ProximityPrize.SubmissionLower.R6
import ProximityPrize.SubmissionLower.CG
import ProximityPrize.SubmissionLower.EK
namespace ProximityPrize.SubmissionLower.RCN138
open RCN136 RCN132 RCN313
open RCN311 RCN174 RCN319
open RCN135
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]
def geometricPolynomialEmbedding:Polynomial K →+*L:=
 (algebraMap (RationalCoefficients K) L).comp
   (algebraMap (Polynomial K) (RationalCoefficients K))
def geometricSurfaceMap:MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 3) L:=
 (MvPolynomial.map (algebraMap (RationalCoefficients K) L)).comp (rationalSurfaceMap K)
theorem geometricSurfaceMap_eq_surfaceMap:
   geometricSurfaceMap K L=surfaceMap (geometricPolynomialEmbedding K L):=by
 apply RingHom.ext
 intro F
 change MvPolynomial.map (algebraMap (RationalCoefficients K) L)
     (MvPolynomial.map (algebraMap (Polynomial K) (RationalCoefficients K)) (collectX K F))=
   MvPolynomial.map ((algebraMap (RationalCoefficients K) L).comp
     (algebraMap (Polynomial K) (RationalCoefficients K))) (collectX K F)
 exact MvPolynomial.map_map _ _ _
theorem geometricSurfaceMap_separated_caps
   (F:MvPolynomial (Fin 4) K) (ell s zcap:ℕ)
   (hy:F.degreeOf 1 ≤ ell) (hr:F.degreeOf 2 ≤ s) (hz:F.degreeOf 3 ≤ zcap):
   (geometricSurfaceMap K L F).degreeOf 0 ≤ ell∧
     (geometricSurfaceMap K L F).degreeOf 1 ≤ s∧
     (geometricSurfaceMap K L F).degreeOf 2 ≤ zcap:=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_separated_caps _ F ell s zcap hy hr hz
theorem geometricSurfaceMap_joint_seed_cap
   (F:MvPolynomial (Fin 4) K) (cap:ℕ)
   (hcap:∀ d∈F.support,d 1+d 3 ≤ cap):
   ∀ e∈(geometricSurfaceMap K L F).support,e 0+e 2 ≤ cap:=by
 rw [geometricSurfaceMap_eq_surfaceMap]
 exact surfaceMap_joint_seed_cap _ F cap hcap
theorem geometric_factor_dvd_iff
   (F M:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F):
   g∣geometricSurfaceMap K L M ↔ F∣M:=by
 constructor
 · intro hdivM
   have hfrac:rationalSurfaceMap K F∣rationalSurfaceMap K M:=
     RCN350.original_dvd_of_geometric_factor_dvd
       (rationalSurfaceMap K F) (rationalSurfaceMap K M)
       (rationalSurfaceMap_irreducible K F hF hpos) g hg hdivF hdivM
   exact (rationalSurfaceMap_dvd_iff K F M hF hpos).mp hfrac
 · intro hdiv
   exact hdivF.trans (map_dvd (geometricSurfaceMap K L) hdiv)
theorem all_later_tails_of_geometric_first_tail
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F) (w:ℕ)
   (hfirst:g∣geometricSurfaceMap K L (numerator K F (w+1))):
   ∀ j,w < j → F∣numerator K F j:=by
 have hbase:=(geometric_factor_dvd_iff K L F (numerator K F (w+1))
   hF hpos g hg hdivF).mp hfirst
 intro j hj
 exact equation_dvd_all_later_numerators K F (w+1) hbase j (by omega)
theorem first_tail_dichotomy
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3) (w:ℕ):
   (F∣numerator K F (w+1)∧∀ j,w < j → F∣numerator K F j)∨
     (∀ g:MvPolynomial (Fin 3) L,Irreducible g →
       g∣geometricSurfaceMap K L F →
       ¬ g∣geometricSurfaceMap K L (numerator K F (w+1))):=by
 by_cases h:F∣numerator K F (w+1)
 · left
   refine ⟨h,?_⟩
   intro j hj
   exact equation_dvd_all_later_numerators K F (w+1) h j (by omega)
 · right
   intro g hg hdivF hdivM
   exact h ((geometric_factor_dvd_iff K L F (numerator K F (w+1))
     hF hpos g hg hdivF).mp hdivM)
theorem polynomiality_of_geometric_first_tail
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (g:MvPolynomial (Fin 3) L) (hg:Irreducible g)
   (hdivF:g∣geometricSurfaceMap K L F)
   (v:Fin 4 → L)
   (hv:MvPolynomial.eval₂Hom
     ((geometricPolynomialEmbedding K L).comp Polynomial.C) v F=0)
   (hreg:MvPolynomial.eval₂Hom
     ((geometricPolynomialEmbedding K L).comp Polynomial.C) v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1 ≤ w) (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hfirst:g∣geometricSurfaceMap K L (numerator K F (w+1))):
   ∃ P:Polynomial L,P.natDegree ≤ w∧
     specialization L P (v 3)
       (MvPolynomial.map ((geometricPolynomialEmbedding K L).comp Polynomial.C) F)=0∧
     P.eval (v 0)=v 1∧P.derivative.eval (v 0)=v 2:=by
 apply exists_global_polynomial_of_first_tail_dvd
   ((geometricPolynomialEmbedding K L).comp Polynomial.C) F v hv hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 exact (geometric_factor_dvd_iff K L F (numerator K F (w+1))
   hF hpos g hg hdivF).mp hfirst
section CanonicalGenericField
theorem canonical_geometricPolynomialEmbedding:
   geometricPolynomialEmbedding K (GenericField K)=polynomialEmbedding K:=rfl
theorem canonical_geometricSurfaceMap:
   geometricSurfaceMap K (GenericField K)=surfaceMap (polynomialEmbedding K):=by
 rw [geometricSurfaceMap_eq_surfaceMap,canonical_geometricPolynomialEmbedding]
theorem eval_at_actual_generic_initial_point
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=
     polynomialEmbedding K (specialization K P γ F):=by
 rw [canonical_geometricSurfaceMap,eval_surfaceMap]
 change MvPolynomial.eval₂Hom (coefficientEmbedding K)
     (Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)) F=_
 have hv:Fin.cases (initialCoordinate K) (fun i:Fin 3 => initialPoint K P γ i.succ)=
     initialPoint K P γ:=by
   funext i
   refine Fin.cases ?_ (fun j => ?_) i <;> rfl
 rw [hv]
 exact evaluation_at_initialPoint K P γ F
theorem actual_generic_initial_zero_iff
   (P:Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (fun i:Fin 3 => initialPoint K P γ i.succ)
     (geometricSurfaceMap K (GenericField K) F)=0 ↔ specialization K P γ F=0:=by
 rw [eval_at_actual_generic_initial_point,polynomialEmbedding_eq_zero_iff]
theorem canonical_first_tail_dichotomy
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3) (w:ℕ):
   (F∣numerator K F (w+1)∧∀ j,w < j → F∣numerator K F j)∨
     (∀ g:MvPolynomial (Fin 3) (GenericField K),Irreducible g →
       g∣surfaceMap (polynomialEmbedding K) F →
       ¬ g∣surfaceMap (polynomialEmbedding K) (numerator K F (w+1))):=by
 simpa only [canonical_geometricSurfaceMap] using
   first_tail_dichotomy K (GenericField K) F hF hpos w
end CanonicalGenericField
end
end ProximityPrize.SubmissionLower.RCN138
