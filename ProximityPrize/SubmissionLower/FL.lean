import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.T
import ProximityPrize.SubmissionLower.CG
namespace ProximityPrize.SubmissionLower.RCN228
open RCN077 RCN269 RCN233
open RCN313 RCN047 RCN231
open RCN139 RCN229 RCN319
open RCN347 RCN311 RCN174
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000
variable {K L M:Type} [Field K] [Field L] [Field M]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem map_reconstructedPolynomial
   (coefficients:K →+*L) (ψ:L →+*M) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i)) F=0)
   (hreg':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hreg w).map ψ=
     reconstructedPolynomial (ψ.comp coefficients) F (fun i => ψ (v i)) hF' hreg' w:=by
 ext j
 simp only [Polynomial.coeff_map,reconstructedPolynomial,jetPolynomial_coeff]
 by_cases hj:j<w+1
 · simp only [if_pos hj]
   rw [jetCoefficient_eq_evaluated_numerator,jetCoefficient_eq_evaluated_numerator]
   simp only [map_div₀,map_mul,map_pow,map_inv₀,map_natCast,
     MvPolynomial.map_eval₂Hom]
 · simp only [if_neg hj,map_zero]
theorem map_globalPolynomial
   (coefficients:K →+*L) (ψ:L →+*M) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i)) F=0)
   (hreg':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hreg w).map ψ=
     globalPolynomial (ψ.comp coefficients) F (fun i => ψ (v i)) hF' hreg' w:=by
 unfold globalPolynomial
 rw [Polynomial.map_taylor,
   map_reconstructedPolynomial coefficients ψ F v hF hreg hF' hreg' w,map_neg]
theorem globalPolynomial_congr_point
   (coefficients:K →+*L) (F:Poly4 K) {v v':Fin 4 → L} (hv:v=v')
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom coefficients v' F=0)
   (hreg':MvPolynomial.eval₂Hom coefficients v' (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ):
   globalPolynomial coefficients F v hF hreg w=
     globalPolynomial coefficients F v' hF' hreg' w:=by
 cases hv
 rfl
theorem derivative_values_of_same_regular_jet
   (F:Poly4 K) (P Q:Polynomial K) (γ ξ:K)
   (hP:specialization K P γ F=0) (hQ:specialization K Q γ F=0)
   (hv:polynomialPoint (RingHom.id K) P γ ξ=polynomialPoint (RingHom.id K) Q γ ξ)
   (hreg:MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) P γ ξ)
     (polyH K F)≠0) (j:ℕ):
   (Polynomial.derivative^[j] P).eval ξ=(Polynomial.derivative^[j] Q).eval ξ:=by
 have hformula (A:Polynomial K) (hA:specialization K A γ F=0):
     MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) A γ ξ)
         (numerator K F j)=
       (MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) A γ ξ)
         (polyH K F))^(2*j)*(Polynomial.derivative^[j] A).eval ξ:=by
   simp only [eval_polynomialPoint_eq_specialization,Polynomial.eval₂_id]
   rw [specialization_numerator_eq K F A γ hA j,Polynomial.eval_mul,Polynomial.eval_pow]
 have hp:=hformula P hP
 have hq:=hformula Q hQ
 rw [←hv] at hq
 exact mul_left_cancel₀ (pow_ne_zero (2*j) hreg) (hp.symm.trans hq)
theorem canonical_polynomiality_of_first_tail
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   specialization L (globalPolynomial coefficients F v hF hreg w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 apply global_polynomiality_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end
end ProximityPrize.SubmissionLower.RCN228
