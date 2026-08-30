import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.H9
namespace ProximityPrize.SubmissionLower.ContactCoefficientCurveResidueApproxResearch
open scoped BigOperators
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k F Γ:Type*} [Field k] [Field F] [Algebra k F]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq F:=Classical.decEq F
theorem polynomial_value_le_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1) (f:F) (hf:v f ≤ 1) (p:k[X]):
   v (p.eval₂ κ f) ≤ 1:=by
 rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro i _
 rw [map_mul,map_pow]
 exact mul_le_one₀ (hκ _) zero_le (pow_le_one₀ zero_le hf)
theorem normalize_relation
   {R:Type*} [CommRing R] [IsDomain R] (κ:R →+*F)
   (u:F) (hu:u≠0) (p:R[X]) (hp:p≠0)
   (hev:p.eval₂ κ u=0):
   ∃ q:R[X],q.coeff 0≠0∧q.eval₂ κ u=0:=by
 classical
 induction hn:p.natDegree using Nat.strong_induction_on generalizing p with
 | h n ih =>
   by_cases hzero:p.coeff 0=0
   · obtain ⟨q,hpq⟩:=Polynomial.X_dvd_iff.mpr hzero
     have hq:q≠0:=by
       intro hz
       exact hp (by simp [hpq,hz])
     have hdeg:q.natDegree < n:=by
       rw [hpq,Polynomial.natDegree_X_mul hq] at hn
       omega
     have hqeval:q.eval₂ κ u=0:=by
       rw [hpq,Polynomial.eval₂_mul,Polynomial.eval₂_X] at hev
       exact (mul_eq_zero.mp hev).resolve_left hu
     exact ih q.natDegree hdeg q hq hqeval rfl
   · exact ⟨p,hzero,hev⟩
theorem exists_constant_close_of_small_polynomial [IsAlgClosed k]
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,c≠0 → v (κ c)=1)
   (f:F) (p:k[X]) (hp:p≠0) (hsmall:v (p.eval₂ κ f) < 1):
   ∃ c:k,v (f-κ c) < 1:=by
 classical
 by_contra h
 push_neg at h
 have hge:1 ≤ v (p.eval₂ κ f):=by
   rw [(IsAlgClosed.splits p).eq_prod_roots,Polynomial.eval₂_mul,
     Polynomial.eval₂_C,map_mul,hκ p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp),
     one_mul,Polynomial.eval₂_multiset_prod,map_multiset_prod]
   simp only [Multiset.map_map,Polynomial.eval₂_sub,Polynomial.eval₂_X,
     Polynomial.eval₂_C,Function.comp_def]
   exact Multiset.one_le_prod_map (fun c _ => h c)
 exact (not_lt_of_ge hge) hsmall
theorem constant_coefficient_value_lt_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1)
   (u f:F) (hu:v u < 1) (hf:v f ≤ 1)
   (q:Polynomial (Polynomial k))
   (hq:q.eval₂ (Polynomial.eval₂RingHom κ f) u=0):
   v ((q.coeff 0).eval₂ κ f) < 1:=by
 have hcoeff:∀ p:k[X],v ((Polynomial.eval₂RingHom κ f) p) ≤ 1:=
   fun p => polynomial_value_le_one v κ hκ f hf p
 have htail:v (q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u) ≤ 1:=by
   rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
   apply v.map_sum_le
   intro i _
   rw [map_mul,map_pow]
   exact mul_le_one₀ (hcoeff _) zero_le (pow_le_one₀ zero_le hu.le)
 have hdecomp:=congrArg
   (fun p:Polynomial (Polynomial k) => p.eval₂ (Polynomial.eval₂RingHom κ f) u)
   (Polynomial.X_mul_divX_add q)
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_X,
   Polynomial.eval₂_C,hq,Polynomial.coe_eval₂RingHom] at hdecomp
 have heq:(q.coeff 0).eval₂ κ f=
     -(u*q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u):=by
   rw [eq_neg_iff_add_eq_zero]
   simpa only [add_comm] using hdecomp
 rw [heq,v.map_neg,map_mul]
 exact (mul_le_mul' le_rfl htail).trans_lt (by simpa using hu)
theorem exists_bivariate_relation_of_trdeg_one
   (htrdeg:Algebra.trdeg k F=1) (u f:F):
   ∃ q:Polynomial (Polynomial k),q≠0∧
     q.eval₂ (Polynomial.eval₂RingHom (algebraMap k F) f) u=0:=by
 have hnot:¬ AlgebraicIndependent k ![f,u]:=by
   intro hi
   have hc:=hi.lift_cardinalMk_le_trdeg
   rw [htrdeg] at hc
   norm_num at hc
 rw [algebraicIndependent_iff] at hnot
 push_neg at hnot
 obtain ⟨p,hpval,hp⟩:=hnot
 let e:=Polynomial.Bivariate.equivMvPolynomial k
 let q:Polynomial (Polynomial k):=e.symm p
 have hq:q≠0:=by
   intro hz
   apply hp
   have:=congrArg e hz
   simpa [q] using this
 have hmaps:
     (Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom=
       MvPolynomial.aeval ![f,u]:=by
   ext i
   fin_cases i <;> simp [e,Polynomial.aevalAeval_C,
     Polynomial.aevalAeval_X,Polynomial.aevalAeval_Y]
 have hev:
     Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u=
       (Polynomial.aevalAeval (R:=k) f u).toRingHom:=by
   ext <;> simp [Polynomial.aevalAeval_C,Polynomial.aevalAeval_X,
     Polynomial.aevalAeval_Y]
 refine ⟨q,hq,?_⟩
 change (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u) q=0
 rw [hev]
 change ((Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom) p=0
 rw [hmaps]
 exact hpval
theorem exists_constant_approx_of_trdeg_one [IsAlgClosed k]
   (v:Valuation F Γ) [v.IsTrivialOn k]
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v u < 1)
   (f:F) (hf:v f ≤ 1):
   ∃ c:k,v (f-algebraMap k F c) < 1:=by
 have hκ:∀ c:k,v (algebraMap k F c) ≤ 1:=by
   intro c
   by_cases hc:c=0
   · simp [hc]
   · exact (Valuation.IsTrivialOn.eq_one c hc).le
 obtain ⟨p,hp,hpval⟩:=exists_bivariate_relation_of_trdeg_one htrdeg u f
 obtain ⟨q,hq0,hqval⟩:=
   normalize_relation (Polynomial.eval₂RingHom (algebraMap k F) f) u hu0 p hp hpval
 exact exists_constant_close_of_small_polynomial v (algebraMap k F)
   (fun c hc => Valuation.IsTrivialOn.eq_one c hc) f (q.coeff 0) hq0
   (constant_coefficient_value_lt_one v (algebraMap k F) hκ u f hu hf q hqval)
variable {L:Type*} [Field L]
open ProximityPrize.SubmissionLower
open ContactCoefficientCurveGaussResearch
theorem residueApprox_of_trdeg_one [IsAlgClosed k]
   (v:Valuation L Γ) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v (φ u) < 1):
   ResidueApprox v φ (algebraMap k F):=by
 let vF:Valuation F Γ:=v.comap φ
 letI:vF.IsTrivialOn k:=⟨hconst⟩
 intro f hf
 exact exists_constant_approx_of_trdeg_one vF htrdeg u hu0 hu f hf
theorem coefficient_pole_le_of_trdeg_one [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (x:L) (hx:v x=1)
   (hunit:ConstantPolynomialUnit v φ (algebraMap k F) x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   ContactLocalPoleBound.poleOrder v (φ (a i)) ≤
     ContactLocalPoleBound.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 by_cases hi:v (φ (a i)) ≤ 1
 · have hz:ContactLocalPoleBound.poleOrder v (φ (a i))=0:=by
     change max 0 (v (φ (a i))).log=0
     rw [←ContactLocalPoleBound.log_max_one,max_eq_left hi,WithZero.log_one]
   rw [hz]
   exact le_max_left _ _
 have hbig:1 < v (φ (a i)):=lt_of_not_ge hi
 let vF:Valuation F (WithZero (Multiplicative ℤ)):=v.comap φ
 haveI:vF.IsNontrivial:=
   ⟨a i,ne_of_gt (zero_lt_one.trans hbig),hbig.ne'⟩
 obtain ⟨u,hu0,hu⟩:=Valuation.IsNontrivial.exists_lt_one (v:=vF)
 exact coefficient_pole_le_generic_value_of_residueApprox v φ (algebraMap k F)
   x hx (residueApprox_of_trdeg_one v φ hconst htrdeg u hu0 hu) hunit a i
theorem constantPolynomialUnit_of_base_constants
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] {w:ℕ}
   (v:Valuation L Γ) [v.IsTrivialOn Ω] (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (x:Ω) (htrans:Transcendental k x):
   ConstantPolynomialUnit v φ (algebraMap k F) (algebraMap Ω L x) w:=by
 classical
 intro c hc
 obtain ⟨i,hi⟩:=hc
 let q:k[X]:=∑ j:Fin (w+1),Polynomial.monomial (j:ℕ) (c j)
 have hcoef:q.coeff (i:ℕ)=c i:=by
   simp only [q,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
   rw [Finset.sum_eq_single i]
   · simp
   · intro j _ hji
     have hval:(j:ℕ)≠(i:ℕ):=fun h => hji (Fin.ext h)
     simp [hval]
   · simp
 have hq:q≠0:=by
   intro hzero
   apply hi
   have h:=congrArg (fun p:k[X] => p.coeff (i:ℕ)) hzero
   simpa only [hcoef,Polynomial.coeff_zero] using h
 have hneq:Polynomial.aeval x q≠0:=by
   intro hzero
   apply hq
   apply (transcendental_iff_injective.mp htrans)
   simpa only [map_zero] using hzero
 have hv:v (algebraMap Ω L (Polynomial.aeval x q))=1:=
   Valuation.IsTrivialOn.eq_one _ hneq
 simpa only [q,map_sum,Polynomial.aeval_monomial,map_mul,map_pow,
   ←hcompat] using hv
theorem coefficient_pole_le_generic_evaluation
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F=1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   ContactLocalPoleBound.poleOrder v (φ (a i)) ≤
     ContactLocalPoleBound.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 have hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1:=by
   intro c hc
   rw [hcompat]
   apply Valuation.IsTrivialOn.eq_one
   intro hz
   apply hc
   apply (algebraMap k Ω).injective
   simpa using hz
 have hx0:x≠0:=by
   intro hz
   apply htrans
   rw [hz]
   exact isAlgebraic_zero
 have hx:v (algebraMap Ω L x)=1:=Valuation.IsTrivialOn.eq_one x hx0
 exact coefficient_pole_le_of_trdeg_one v φ hconst htrdeg (algebraMap Ω L x) hx
   (constantPolynomialUnit_of_base_constants v φ hcompat x htrans) a i
end
end ProximityPrize.SubmissionLower.ContactCoefficientCurveResidueApproxResearch
