import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGenericCoefficientAvoidanceResearch
import ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch
namespace ProximityPrize.SubmissionLower.ContactLeadingCancellationResearch
open scoped Classical BigOperators WithZero
open ContactLocalPoleBound
open ContactGenericCoefficientAvoidanceResearch
open ContactSparsePoleSupportResearch
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
  [DecidableEq σ] [Algebra K L]
def coefficientEvaluation (x:σ → L) (E:Finset (σ →₀ ℕ)):
    (E → K) →ₗ[K] L where
  toFun c:=MvPolynomial.eval₂Hom (algebraMap K L) x
    (polynomialOfSupport E c)
  map_add' c d:=by
    rw [show polynomialOfSupport E (c+d)=
        polynomialOfSupport E c+polynomialOfSupport E d by
      ext m
      by_cases hm:m∈E <;>
        simp [coeff_polynomialOfSupport,hm]]
    exact map_add (MvPolynomial.eval₂Hom (algebraMap K L) x)
      (polynomialOfSupport E c) (polynomialOfSupport E d)
  map_smul' a c:=by
    rw [show polynomialOfSupport E (a • c)=
        a • polynomialOfSupport E c by
      ext m
      by_cases hm:m∈E <;>
        simp [coeff_polynomialOfSupport,hm]]
    simpa [Algebra.smul_def] using
      MvPolynomial.eval₂Hom_smul (algebraMap K L) x a
        (polynomialOfSupport E c)
def livePoleTruncation
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=
  d.filter (fun i↦x i≠0∧0 ≤ (v (x i)).log)
theorem livePoleTruncation_le
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (d:σ →₀ ℕ):
    livePoleTruncation v x d ≤ d:=by
  intro i
  simp only [livePoleTruncation,Finsupp.filter_apply]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _
theorem exponentValuationWeight_livePoleTruncation
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (d:σ →₀ ℕ):
    exponentValuationWeight v x (livePoleTruncation v x d)=
      exponentPoleWeight v x d:=by
  classical
  unfold exponentValuationWeight exponentPoleWeight poleOrder
  apply Finset.sum_congr rfl
  intro i _
  simp only [livePoleTruncation,Finsupp.filter_apply]
  by_cases hx:x i=0
  · simp [hx]
  · by_cases hlog:0 ≤ (v (x i)).log
    · rw [if_pos ⟨hx,hlog⟩,max_eq_right hlog]
    · have hle:(v (x i)).log ≤ 0:=le_of_not_ge hlog
      rw [if_neg (fun h↦hlog h.2),max_eq_left hle]
      simp
theorem livePoleTruncation_coordinate_ne_zero
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (d:σ →₀ ℕ) (i:σ)
    (hi:livePoleTruncation v x d i≠0):x i≠0:=by
  classical
  simp only [livePoleTruncation,Finsupp.filter_apply] at hi
  split at hi
  · exact ‹x i≠0∧0 ≤ (v (x i)).log›.1
  · exact (hi rfl).elim
private theorem exp_sum (s:Finset σ) (z:σ → ℤ):
    WithZero.exp (∑ i∈s,z i)=∏ i∈s,WithZero.exp (z i):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih,WithZero.exp_add]
theorem valuation_eval_monomial_one_eq_exp
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (d:σ →₀ ℕ)
    (hlive:∀ i,d i≠0 → x i≠0):
    v (MvPolynomial.eval₂Hom (algebraMap K L) x
        (MvPolynomial.monomial d (1:K)))=
      WithZero.exp (exponentValuationWeight v x d):=by
  classical
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _↦pow_zero _),map_mul,map_prod]
  simp only [map_one,one_mul,map_pow]
  rw [show WithZero.exp (exponentValuationWeight v x d)=
      ∏ i,WithZero.exp ((d i:ℤ)*(v (x i)).log) by
    unfold exponentValuationWeight
    simpa only using exp_sum (Finset.univ:Finset σ)
      (fun i↦(d i:ℤ)*(v (x i)).log)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hd:d i=0
  · simp [hd]
  · have hvx:v (x i)≠0:=
      (Valuation.ne_zero_iff v).mpr (hlive i hd)
    rw [show ((d i:ℤ)*(v (x i)).log)=
        d i • (v (x i)).log by simp,
      WithZero.exp_nsmul,WithZero.exp_log hvx]
theorem exists_mem_exponentPoleWeight_eq
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (E:Finset (σ →₀ ℕ)) (hzero:0∈E):
    ∃ d∈E,exponentPoleWeight v x d=exponentSetPoleWeight v x E:=by
  classical
  let S:=insert (0:ℤ) (E.image (exponentPoleWeight v x))
  have hS:S.Nonempty:=⟨0,Finset.mem_insert_self 0 _⟩
  have hmem:S.max' hS∈S:=Finset.max'_mem S hS
  change S.max' hS∈insert (0:ℤ) (E.image (exponentPoleWeight v x)) at hmem
  rcases Finset.mem_insert.mp hmem with hmax | hmax
  · refine ⟨0,hzero,?_⟩
    unfold exponentSetPoleWeight
    change exponentPoleWeight v x 0=S.max' hS
    simp only [exponentPoleWeight,Finsupp.zero_apply,Nat.cast_zero,
      zero_mul,Finset.sum_const_zero]
    exact hmax.symm
  · obtain ⟨d,hd,heq⟩:=Finset.mem_image.mp hmax
    refine ⟨d,hd,?_⟩
    unfold exponentSetPoleWeight
    change exponentPoleWeight v x d=S.max' hS
    exact heq
def deltaCoefficient (E:Finset (σ →₀ ℕ)) (e:E):E → K:=
  fun d↦if d=e then 1 else 0
theorem polynomialOfSupport_deltaCoefficient
    (E:Finset (σ →₀ ℕ)) (e:E):
    polynomialOfSupport E (deltaCoefficient E e:E → K)=
      MvPolynomial.monomial e.1 1:=by
  classical
  unfold polynomialOfSupport deltaCoefficient
  rw [Finset.sum_eq_single e]
  · simp
  · intro d _ hd
    simp [hd]
  · simp
theorem exists_exact_support_evaluation_of_downwardClosed
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (E:Finset (σ →₀ ℕ))
    (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
    ∃ c:E → K,
      v (coefficientEvaluation x E c)=
        WithZero.exp (exponentSetPoleWeight v x E):=by
  obtain ⟨d,hd,hmax⟩:=exists_mem_exponentPoleWeight_eq v x E hzero
  let e:σ →₀ ℕ:=livePoleTruncation v x d
  have he:e∈E:=hdown d hd e (livePoleTruncation_le v x d)
  let esub:E:=⟨e,he⟩
  refine ⟨deltaCoefficient E esub,?_⟩
  rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
    polynomialOfSupport_deltaCoefficient]
  rw [valuation_eval_monomial_one_eq_exp v x e
    (livePoleTruncation_coordinate_ne_zero v x d)]
  rw [exponentValuationWeight_livePoleTruncation,hmax]
theorem exponentSetPoleWeight_nonneg
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (x:σ → L) (E:Finset (σ →₀ ℕ)):
    0 ≤ exponentSetPoleWeight v x E:=by
  unfold exponentSetPoleWeight
  exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem poleOrder_eq_of_valuation_eq_exp
    (v:Valuation L (WithZero (Multiplicative ℤ))) (b:L) (q:ℤ)
    (hq:0 ≤ q) (hexact:v b=WithZero.exp q):
    poleOrder v b=q:=by
  unfold poleOrder
  rw [hexact,WithZero.log_exp,max_eq_right hq]
def cancellationSubmodule
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
    (x:σ → L) (E:Finset (σ →₀ ℕ)):
    Submodule K (E → K) where
  carrier:={c | v (coefficientEvaluation x E c) <
    WithZero.exp (exponentSetPoleWeight v x E)}
  zero_mem':=by
    change v (coefficientEvaluation x E 0) <
      WithZero.exp (exponentSetPoleWeight v x E)
    rw [map_zero,map_zero]
    exact WithZero.exp_pos
  add_mem':=by
    intro c d hc hd
    change v (coefficientEvaluation x E (c+d)) <
      WithZero.exp (exponentSetPoleWeight v x E)
    change v (coefficientEvaluation x E c) <
      WithZero.exp (exponentSetPoleWeight v x E) at hc
    change v (coefficientEvaluation x E d) <
      WithZero.exp (exponentSetPoleWeight v x E) at hd
    rw [map_add]
    exact (v.map_add _ _).trans_lt (max_lt hc hd)
  smul_mem':=by
    intro a c hc
    change v (coefficientEvaluation x E (a • c)) <
      WithZero.exp (exponentSetPoleWeight v x E)
    change v (coefficientEvaluation x E c) <
      WithZero.exp (exponentSetPoleWeight v x E) at hc
    rw [map_smul,Algebra.smul_def,map_mul]
    calc
      v (algebraMap K L a)*v (coefficientEvaluation x E c) ≤
          1*v (coefficientEvaluation x E c):=
        mul_le_mul' (hcoeff a) le_rfl
      _ < WithZero.exp (exponentSetPoleWeight v x E):=by
        simpa using hc
theorem cancellationSubmodule_ne_top_of_exact
    (v:Valuation L (WithZero (Multiplicative ℤ)))
    (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
    (x:σ → L) (E:Finset (σ →₀ ℕ))
    (c:E → K)
    (hc:v (coefficientEvaluation x E c)=
      WithZero.exp (exponentSetPoleWeight v x E)):
    cancellationSubmodule v hcoeff x E≠⊤:=by
  intro htop
  have hmem:c∈cancellationSubmodule v hcoeff x E:=by
    rw [htop]
    trivial
  change v (coefficientEvaluation x E c) <
    WithZero.exp (exponentSetPoleWeight v x E) at hmem
  rw [hc] at hmem
  exact (lt_irrefl _ hmem)
theorem exists_simultaneous_exact_support_evaluation
    {τ:Type*} [Finite τ] [Infinite K]
    (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
    (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
    (x:σ → L) (E:Finset (σ →₀ ℕ))
    (hwitness:∀ t,∃ c:E → K,
      v t (coefficientEvaluation x E c)=
        WithZero.exp (exponentSetPoleWeight (v t) x E)):
    ∃ c:E → K,
      (polynomialOfSupport E c).support ⊆ E∧
      ∀ t,v t (MvPolynomial.eval₂Hom (algebraMap K L) x
          (polynomialOfSupport E c))=
        WithZero.exp (exponentSetPoleWeight (v t) x E):=by
  let bad:τ → Submodule K (E → K):=
    fun t↦cancellationSubmodule (v t) (hcoeff t) x E
  have hproper:∀ t,bad t≠⊤:=by
    intro t
    obtain ⟨c,hc⟩:=hwitness t
    exact cancellationSubmodule_ne_top_of_exact
      (v t) (hcoeff t) x E c hc
  obtain ⟨c,hc⟩:=
    exists_avoiding_finite_proper_submodules bad hproper
  refine ⟨c,support_polynomialOfSupport_subset E c,?_⟩
  intro t
  have hlower:WithZero.exp (exponentSetPoleWeight (v t) x E) ≤
      v t (coefficientEvaluation x E c):=by
    apply le_of_not_gt
    intro hlt
    exact hc t hlt
  have hupper:v t (coefficientEvaluation x E c) ≤
      WithZero.exp (exponentSetPoleWeight (v t) x E):=by
    exact valuation_eval_le_exp_exponentSet (v t) (algebraMap K L)
      (hcoeff t) x E (polynomialOfSupport E c)
      (support_polynomialOfSupport_subset E c)
  exact le_antisymm hupper hlower
theorem exists_simultaneous_exact_support_evaluation_of_downwardClosed
    {τ:Type*} [Finite τ] [Infinite K]
    (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
    (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
    (x:σ → L) (E:Finset (σ →₀ ℕ))
    (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
    ∃ c:E → K,
      (polynomialOfSupport E c).support ⊆ E∧
      ∀ t,v t (MvPolynomial.eval₂Hom (algebraMap K L) x
          (polynomialOfSupport E c))=
        WithZero.exp (exponentSetPoleWeight (v t) x E):=by
  exact exists_simultaneous_exact_support_evaluation v hcoeff x E
    (fun t↦exists_exact_support_evaluation_of_downwardClosed
      (v t) x E hdown hzero)
theorem exists_simultaneous_exact_poleOrder_of_downwardClosed
    {τ:Type*} [Finite τ] [Infinite K]
    (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
    (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
    (x:σ → L) (E:Finset (σ →₀ ℕ))
    (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
    ∃ c:E → K,
      (polynomialOfSupport E c).support ⊆ E∧
      ∀ t,poleOrder (v t)
          (MvPolynomial.eval₂Hom (algebraMap K L) x
            (polynomialOfSupport E c))=
        exponentSetPoleWeight (v t) x E:=by
  obtain ⟨c,hsupport,hexact⟩:=
    exists_simultaneous_exact_support_evaluation_of_downwardClosed
      v hcoeff x E hdown hzero
  refine ⟨c,hsupport,fun t↦?_⟩
  exact poleOrder_eq_of_valuation_eq_exp (v t) _ _
    (exponentSetPoleWeight_nonneg (v t) x E) (hexact t)
end
end ProximityPrize.SubmissionLower.ContactLeadingCancellationResearch
