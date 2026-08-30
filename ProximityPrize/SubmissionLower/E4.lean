import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.T
namespace ProximityPrize.SubmissionLower.RCN258
open RCN077 RCN269 RCN233
open RCN313 RCN047 RCN231
open RCN139 RCN229 RCN319
open RCN347
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L M:Type*} [Field k] [Field L] [Field M]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem mv_eval_mem (E:Subfield M) (c:k →+*M)
   (hc:∀ a,c a∈E) (v:Fin 4 → M) (hv:∀ i,v i∈E) (Q:Poly4 k):
   MvPolynomial.eval₂Hom c v Q∈E:=by
 induction Q using MvPolynomial.induction_on with
 | C a => simpa using hc a
 | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
 | mul_X P i hP =>
     simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using E.mul_mem hP (hv i)
theorem polynomial_eval_mem (E:Subfield M) (c:L →+*M)
   (P:Polynomial L) (hP:∀ j,c (P.coeff j)∈E) (x:M) (hx:x∈E):
   P.eval₂ c x∈E:=by
 rw [Polynomial.eval₂_eq_sum_range]
 exact E.sum_mem fun j _ => E.mul_mem (hP j) (E.pow_mem hx j)
theorem taylor_coeff_mem (E:Subfield M) (P:Polynomial M)
   (hP:∀ j,P.coeff j∈E) (x:M) (hx:x∈E) (j:ℕ):
   (Polynomial.taylor x P).coeff j∈E:=by
 rw [Polynomial.taylor_coeff]
 apply polynomial_eval_mem E (RingHom.id M) (Polynomial.hasseDeriv j P) _ x hx
 intro n
 simp only [RingHom.id_apply,Polynomial.hasseDeriv_coeff]
 exact E.mul_mem (natCast_mem E _) (hP _)
theorem globalPolynomial_coeff_mem_of_evaluations
   (E:Subfield M) (c:k →+*M) (F:Poly4 k) (v:Fin 4 → M)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hv0:v 0∈E)
   (hnum:∀ j,MvPolynomial.eval₂Hom c v (numerator k F j)∈E)
   (hH:MvPolynomial.eval₂Hom c v (polyH k F)∈E) (j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=by
 unfold globalPolynomial
 apply taylor_coeff_mem E _ _ _ (E.neg_mem hv0) j
 intro n
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 split_ifs with hn
 · rw [jetCoefficient_eq_evaluated_numerator]
   exact E.div_mem (E.mul_mem (hnum n) (E.pow_mem (E.inv_mem hH) _))
     (natCast_mem E _)
 · exact E.zero_mem
theorem globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*M) (hc:∀ a,c a∈E)
   (F:Poly4 k) (v:Fin 4 → M) (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=
 globalPolynomial_coeff_mem_of_evaluations E c F v hF hreg w (hv 0)
   (fun n => mv_eval_mem E c hc v hv (numerator k F n))
   (mv_eval_mem E c hc v hv (polyH k F)) j
theorem map_numeratorStep (c:k →+*L) (F Q:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numeratorStep k F n Q)=
     numeratorStep L (MvPolynomial.map c F) n (MvPolynomial.map c Q):=by
 simp only [numeratorStep,clearedStep,polyH,polyG,MvPolynomial.pderiv_map,
   map_sub,map_add,map_mul,map_pow,map_natCast,map_neg,MvPolynomial.map_X]
theorem map_numerator (c:k →+*L) (F:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numerator k F n)=numerator L (MvPolynomial.map c F) n:=by
 induction n with
 | zero => simp
 | succ n ih => rw [numerator_succ,map_numeratorStep,ih,numerator_succ]
theorem mapped_globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (v:Fin 4 → M)
   (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom φ v (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ v
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (w j:ℕ):
   (globalPolynomial φ (MvPolynomial.map c F) v hF hreg w).coeff j∈E:=by
 apply globalPolynomial_coeff_mem_of_evaluations E φ (MvPolynomial.map c F)
   v hF hreg w (hv 0) _ _ j
 · intro n
   rw [←map_numerator c F n,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (numerator k F n)
 · unfold polyH
   rw [MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (MvPolynomial.pderiv (2:Fin 4) F)
theorem solution_coeff_mem_of_regular_point
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (P:Polynomial L) (γ:L) (ξ:M)
   (hsolution:specialization L P γ (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ (polynomialPoint φ P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (hv:∀ i,polynomialPoint φ P γ ξ i∈E)
   (p w:ℕ) [CharP M p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   φ (P.coeff j)∈E:=by
 have hmem:=mapped_globalPolynomial_coeff_mem E c φ hc F
   (polynomialPoint φ P γ ξ) hv
   (polynomialPoint_relation φ (MvPolynomial.map c F) P γ ξ hsolution)
   hreg w j
 rw [globalPolynomial_eq_map_of_solution φ (MvPolynomial.map c F) P γ ξ
   hsolution hreg p w hw hP,Polynomial.coeff_map] at hmem
 exact hmem
end
end ProximityPrize.SubmissionLower.RCN258
