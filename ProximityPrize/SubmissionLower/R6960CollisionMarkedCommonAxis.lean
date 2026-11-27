import ProximityPrize.SubmissionLower.R6960CollisionMarkedIndexSpecialization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
import ProximityPrize.SubmissionLower.R6960RetainedCompressionProjection
import ProximityPrize.SubmissionLower.R6960MarkedTranslatedEquation
import ProximityPrize.SubmissionLower.R6960CollisionTameFibreTrace
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisLaurent
import ProximityPrize.SubmissionLower.R6960MarkedWordResidues

set_option Elab.async false

-- merged module R6960CollisionMarkedAxisGeneric
section Merged_R6960CollisionMarkedAxisGeneric

-- merged module R6960CollisionTameWeights
section Merged_R6960CollisionTameWeights
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
variable {k : Type} [Field k] [DecidableEq k]
def branchFactors (δ : (Polynomial (Polynomial k))) : Finset ((Polynomial (Polynomial k))) := (normalizedFactors δ).toFinset
def branchWeight (δ : (Polynomial (Polynomial k))) (i : branchFactors δ) : ℕ := (normalizedFactors δ).count (i:(Polynomial (Polynomial k)))
def branchProduct (δ : (Polynomial (Polynomial k))) : (Polynomial (Polynomial k)) := ∏ i : branchFactors δ,(i:(Polynomial (Polynomial k)))
theorem branch_weight_pos (δ : (Polynomial (Polynomial k))) (i : branchFactors δ) : 0<branchWeight δ i :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp i.property)
theorem branchFactor_prime (δ : (Polynomial (Polynomial k))) (i : branchFactors δ) : Prime (i:(Polynomial (Polynomial k))) :=
  prime_of_normalized_factor _ (Multiset.mem_toFinset.mp i.property)
theorem branch_weighted_product (δ : (Polynomial (Polynomial k))) (nz : δ≠0) :
    Associated (∏ i : branchFactors δ,(i:(Polynomial (Polynomial k)))^branchWeight δ i) δ := by
  unfold branchWeight
  rw [Finset.prod_coe_sort (branchFactors δ) (fun p : (Polynomial (Polynomial k))=>p^(normalizedFactors δ).count p)]
  change Associated (∏ p∈(normalizedFactors δ).toFinset,p^(normalizedFactors δ).count p) δ
  rw [←Finset.prod_multiset_count]
  exact prod_normalizedFactors nz
theorem branch_weighted_degrees (δ : (Polynomial (Polynomial k))) (nz : δ≠0) :
    (∑ i : branchFactors δ,branchWeight δ i*(i:(Polynomial (Polynomial k))).natDegree)=δ.natDegree ∧
    (∑ i : branchFactors δ,branchWeight δ i*CurvatureSquares.height (i:(Polynomial (Polynomial k))))=
      CurvatureSquares.height δ := by
  have factor := branch_weighted_product δ nz
  constructor
  · have eq := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated factor)
    rw [natDegree_prod _ _ (fun i _=>pow_ne_zero _ (branchFactor_prime δ i).ne_zero)] at eq
    simpa only [natDegree_pow] using eq
  · have eq := factor.map Bivariate.swap.toRingHom
    have swap : Bivariate.swap (∏ i : branchFactors δ,(i:(Polynomial (Polynomial k)))^branchWeight δ i)=
        ∏ i : branchFactors δ,(Bivariate.swap (i:(Polynomial (Polynomial k))))^branchWeight δ i := by
      rw [map_prod]
      simp only [map_pow]
    change Associated (Bivariate.swap (∏ i : branchFactors δ,(i:(Polynomial (Polynomial k)))^branchWeight δ i))
      (Bivariate.swap δ) at eq
    rw [swap] at eq
    have deg := natDegree_eq_of_degree_eq (degree_eq_degree_of_associated eq)
    rw [natDegree_prod _ _ (fun i _=>pow_ne_zero _
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (branchFactor_prime δ i).ne_zero))] at deg
    simpa only [natDegree_pow,CurvatureSquares.height] using deg
theorem branch_index_of_discriminant [IsAlgClosed k]
    (δ : (Polynomial (Polynomial k))) (nz : δ≠0)
    (sep : ((branchProduct δ).map (algebraMap (Polynomial k) (FractionRing (Polynomial k)))).Separable)
    (T : Finset k) (good : ∀ z∈T,(branchProduct δ).map (evalRingHom z)≠0)
    (idx : k→(Polynomial k)) (supported : ∀ z∈T,∀ x∈(idx z).roots,
      2≤((branchProduct δ).map (evalRingHom z)).rootMultiplicity x)
    (disc : ∀ z∈T,idx z^2∣δ.map (evalRingHom z))
    {s t : ℕ} (xcap : δ.natDegree≤2*s) (zcap : CurvatureSquares.height δ≤2*t) :
    (∑ z∈T,(idx z).natDegree)≤8*s*t := by
  let f : branchFactors δ→(Polynomial (Polynomial k)) := Subtype.val
  have weights := branch_weighted_degrees δ nz
  refine BranchIndex.index_degree f (branchWeight δ) (branch_weight_pos δ) (branchProduct δ) rfl
    sep T good idx supported ?_ (weights.1 ▸ xcap) (weights.2 ▸ zcap)
  intro z hz
  have factor := (branch_weighted_product δ nz).map (Polynomial.mapRingHom (evalRingHom z))
  change Associated ((∏ i : branchFactors δ,f i^branchWeight δ i).map (evalRingHom z))
    (δ.map (evalRingHom z)) at factor
  have dp : idx z^2∣(∏ i : branchFactors δ,f i^branchWeight δ i).map (evalRingHom z) :=
    (disc z hz).trans factor.dvd'
  simpa only [Polynomial.map_prod,Polynomial.map_pow] using dp
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameWeights

-- merged module R6960CollisionTameTransverse
section Merged_R6960CollisionTameTransverse
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial UniqueFactorizationMonoid Finset
open scoped Polynomial BigOperators
open Lower6960.BranchIndex (mult_product)
variable {k : Type} [Field k] [DecidableEq k]
private theorem unique_sum_one {I : Type*} [Fintype I] [DecidableEq I]
    (f : I→ℕ) (sum : ∑ i,f i=1) :
    ∃ i, f i=1 ∧ ∀ j≠i,f j=0 := by
  classical
  have pos : ∃ i,0<f i := by
    by_contra! all
    have gone (i : I) : f i=0 := by have q := all i; omega
    simp only [gone,Finset.sum_const_zero,zero_ne_one] at sum
  obtain ⟨i,hi⟩ := pos
  have le : f i≤1 := sum ▸ Finset.single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have eq : f i=1 := by omega
  have rem := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [sum,eq] at rem
  refine ⟨i,eq,fun j ji=>?_⟩
  have mem : j∈(Finset.univ : Finset I).erase i := Finset.mem_erase.mpr ⟨ji,Finset.mem_univ _⟩
  have jel := Finset.single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) mem
  omega
theorem simple_branch_weight (δ : (Polynomial (Polynomial k))) (nz : δ≠0) (z x : k)
    (good : (branchProduct δ).map (evalRingHom z)≠0)
    (simple : ((branchProduct δ).map (evalRingHom z)).rootMultiplicity x=1) :
    ∃ i : branchFactors δ, (((i:(Polynomial (Polynomial k))).map (evalRingHom z)).rootMultiplicity x=1) ∧
      (δ.map (evalRingHom z)).rootMultiplicity x=branchWeight δ i ∧
      emultiplicity (i:(Polynomial (Polynomial k))) δ=(branchWeight δ i:ℕ∞) := by
  classical
  let f (i : branchFactors δ) := (i:(Polynomial (Polynomial k))).map (evalRingHom z)
  let m (i : branchFactors δ) := (f i).rootMultiplicity x
  have gn : (∏ i,f i)≠0 := by
    simpa only [branchProduct,Polynomial.map_prod,f] using good
  have fn (i : branchFactors δ) : f i≠0 := prod_ne_zero_iff.mp gn _ (Finset.mem_univ _)
  have eq : (∑ i,m i)=1 := by
    have h := Lower6960.BranchIndex.mult_product f (fun _=>1) Finset.univ (fun i _=>fn i) x
    simp only [pow_one,one_mul] at h
    exact h.symm.trans (by simpa only [branchProduct,Polynomial.map_prod,f] using simple)
  obtain ⟨i,hi,other⟩ := unique_sum_one m eq
  let W := ∏ j : branchFactors δ,(f j)^branchWeight δ j
  have wn : W≠0 := prod_ne_zero_iff.mpr fun i _=>pow_ne_zero _ (fn i)
  have assoc : Associated W (δ.map (evalRingHom z)) := by
    have h := (branch_weighted_product δ nz).map (mapRingHom (evalRingHom z))
    simpa only [coe_mapRingHom,Polynomial.map_prod,Polynomial.map_pow,f,W] using h
  have δn : δ.map (evalRingHom z)≠0 := by
    intro zero
    exact wn (zero_dvd_iff.mp (zero ▸ assoc.dvd'))
  have mult_eq : (δ.map (evalRingHom z)).rootMultiplicity x=W.rootMultiplicity x := by
    apply le_antisymm
    · exact (le_rootMultiplicity_iff wn).mpr (((δ.map (evalRingHom z)).pow_rootMultiplicity_dvd x).trans assoc.dvd')
    · exact (le_rootMultiplicity_iff δn).mpr ((W.pow_rootMultiplicity_dvd x).trans assoc.dvd)
  refine ⟨i,hi,?_,?_⟩
  · rw [mult_eq,show W=∏ j,(f j)^branchWeight δ j from rfl,
      Lower6960.BranchIndex.mult_product _ _ _ (fun j _=>fn j)]
    change (∑ j,branchWeight δ j*m j)=branchWeight δ i
    rw [Finset.sum_eq_single i,hi,mul_one]
    · intro j _ ji
      rw [other j ji,mul_zero]
    · simp
  · have norm : normalize (i:(Polynomial (Polynomial k)))=(i:(Polynomial (Polynomial k))) :=
      normalize_normalized_factor _ (Multiset.mem_toFinset.mp i.property)
    rw [emultiplicity_eq_count_normalizedFactors (branchFactor_prime δ i).irreducible nz,norm]
    rfl
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameTransverse

-- merged module R6960CollisionTameMarkedCorank
section Merged_R6960CollisionTameMarkedCorank

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1750000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix NormalizedFiber
open scoped Polynomial Matrix BigOperators

variable {k E : Type} [Field k] [DecidableEq k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

/-- At a simple reduced branch crossing the actual scalar-fibre Gram
determinant has order equal to the generic trace corank along that
branch. The fibre denominator is proved to avoid the branch. -/
theorem simple_frame_corank (δ : Plane k) (nz : δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z x : k) (good : (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (simple : ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x=1)
    (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin (finrank (FractionRing (Plane k)) E)→Order k E)
    (f : (Fin (finrank (FractionRing (Plane k)) E)→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (one : g.eval (C z)=1) (clear : ∀ w : Order k E,∃ t,f t=g • w) :
    let T := tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u
    ∃ (q : Plane k) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      (q.eval (C z)).eval x=0 ∧
      ((T.det).eval (C z)).rootMultiplicity x=
        finrank (FractionRing (Plane k)) E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
  classical
  let A := Plane k
  let F := FractionRing A
  let n := finrank F E
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  let evalZ := evalRingHom (C z)
  have swappnz : Bivariate.swap δ≠0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr nz
  obtain ⟨i,qorder,δorder,exponent⟩ := simple_branch_weight (Bivariate.swap δ) swappnz z x good simple
  let q : A := Bivariate.swap (i:Plane k)
  have qp : Prime q := (MulEquiv.prime_iff Bivariate.swap.toMulEquiv).mpr (branchFactor_prime (Bivariate.swap δ) i)
  let P := Ideal.span {q}
  let : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp
  have qroot : (q.eval (C z)).eval x=0 := by
    change IsRoot (q.eval (C z)) x
    apply (rootMultiplicity_pos'.mp ?_).2
    rw [show q.eval (C z)=(i:Plane k).map (evalRingHom z) from RetainedCompression.eval_swap _ _,qorder]
    decide
  have qout : g∉P := by
    intro hgp
    have qdvd : q∣g := Ideal.mem_span_singleton.mp hgp
    obtain ⟨a,eq⟩ := map_dvd (evalRingHom x) (map_dvd evalZ qdvd)
    change (g.eval (C z)).eval x=((q.eval (C z)).eval x)*a at eq
    rw [one,eval_one,qroot,zero_mul] at eq
    exact one_ne_zero eq
  have core := branch_frame_trace_order P q qp.irreducible rfl p small u f sum inj g qout clear
  have Dmem : T.det∈normalizationDiscriminant (A:=A) (E:=E) F := gramIdeal_mem tr u
  have δmem : δ∈normalizationDiscriminant (A:=A) (E:=E) F := by
    rw [principal]; exact Ideal.subset_span (Set.mem_singleton δ)
  have trace_divides : T.det∣g^(2*n)*δ := by
    have h := gramIdeal_clear tr u g (fun w=>by
      obtain ⟨v,hv⟩ := clear w
      exact ⟨v,(sum v).symm.trans hv⟩) δ δmem
    simpa only [Fintype.card_fin] using h
  have δ_divides : δ∣T.det := Ideal.mem_span_singleton.mp (principal ▸ Dmem)
  have g0 : emultiplicity q g=0 := emultiplicity_eq_zero.mpr fun hv=>qout (Ideal.mem_span_singleton.mpr hv)
  have order_eq : emultiplicity q T.det=emultiplicity q δ := by
    apply le_antisymm _ (emultiplicity_le_emultiplicity_of_dvd_right δ_divides)
    have h := emultiplicity_le_emultiplicity_of_dvd_right (a:=q) trace_divides
    rw [emultiplicity_mul qp,emultiplicity_pow qp,g0,mul_zero,zero_add] at h
    exact h
  have sameExponent : emultiplicity q δ=(branchWeight (Bivariate.swap δ) i:ℕ∞) := calc
    _ = emultiplicity q (Bivariate.swap (Bivariate.swap δ)) :=
      congrArg (emultiplicity q) (Bivariate.swap_swap_apply δ).symm
    _ = emultiplicity (i:Plane k) (Bivariate.swap δ) := emultiplicity_map_eq Bivariate.swap
    _ = _ := exponent
  have idxEq : ((branchWeight (Bivariate.swap δ) i):ℕ∞)=
      ((n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) :=
    sameExponent.symm.trans (order_eq.symm.trans core)
  have δeval : δ.eval (C z)=(Bivariate.swap δ).map (evalRingHom z) := by
    simpa only [Bivariate.swap_swap_apply] using RetainedCompression.eval_swap (Bivariate.swap δ) z
  have δpositive : 0<(δ.eval (C z)).rootMultiplicity x := by
    rw [δeval,δorder]
    exact branch_weight_pos _ _
  have δnonzero := (rootMultiplicity_pos'.mp δpositive).1
  have eval_dvd : evalZ T.det∣evalZ δ := by
    have d := map_dvd evalZ trace_divides
    rw [map_mul,map_pow,show evalZ g=1 from one,one_pow,one_mul] at d
    exact d
  have eval_dvd' : evalZ δ∣evalZ T.det := map_dvd evalZ δ_divides
  have tn : evalZ T.det≠0 := fun zero=>δnonzero (zero_dvd_iff.mp (zero ▸ eval_dvd))
  have eq : (evalZ T.det).rootMultiplicity x=(evalZ δ).rootMultiplicity x :=
    le_antisymm ((le_rootMultiplicity_iff δnonzero).mpr ((evalZ T.det).pow_rootMultiplicity_dvd x |>.trans eval_dvd))
      ((le_rootMultiplicity_iff tn).mpr ((evalZ δ).pow_rootMultiplicity_dvd x |>.trans eval_dvd'))
  refine ⟨q,qp,qroot,?_⟩
  change (evalZ T.det).rootMultiplicity x=n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank
  rw [eq]
  change (δ.eval (C z)).rootMultiplicity x=_
  rw [δeval,δorder]
  exact ENat.natCast_inj.mp idxEq

end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameMarkedCorank

-- merged module R6960CollisionTameMarkedSupport
section Merged_R6960CollisionTameMarkedSupport
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Module Matrix NormalizedFiber
open scoped Polynomial Matrix BigOperators
variable {k E : Type} [Field k] [DecidableEq k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
theorem transverse_corank_receipt (δ : Plane k) (nz : δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    (z x : k) (good : (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (simple : ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x=1)
    (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin (finrank (FractionRing (Plane k)) E)→Order k E)
    (f : (Fin (finrank (FractionRing (Plane k)) E)→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (one : g.eval (C z)=1) (clear : ∀ w : Order k E,∃ t,f t=g • w)
    (T : Matrix (Fin (finrank (FractionRing (Plane k)) E)) (Fin (finrank (FractionRing (Plane k)) E)) (Plane k))
    (coefficients : T=tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u) :
    ∃ (q : Plane k) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      ∃ point : Plane k ⧸ P→+*k,
        ((T.map (Ideal.Quotient.mk P)).map point)=(evalRingHom x).mapMatrix (T.map (evalRingHom (C z))) ∧
        ((T.map (evalRingHom (C z))).det).rootMultiplicity x≤
          finrank (FractionRing (Plane k)) E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
  classical
  let R := Plane k
  let F := FractionRing R
  have source : ∃ (q : R) (qp : Prime q), let P := Ideal.span {q};
      letI : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp;
      (q.eval (C z)).eval x=0 ∧
      (T.det.eval (C z)).rootMultiplicity x=finrank F E-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank := by
    rw [coefficients]
    exact simple_frame_corank (E:=E) δ nz principal z x good simple p small u f sum inj g one clear
  obtain ⟨q,qp,qroot,order⟩ := source
  let P := Ideal.span {q}
  let : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp
  let fpoint : R→+*k := (evalRingHom x).comp (evalRingHom (C z))
  let point : R ⧸ P→+*k := Ideal.Quotient.lift P fpoint (fun h hh=>by
    obtain ⟨v,rfl⟩ := Ideal.mem_span_singleton.mp hh
    rw [map_mul,show fpoint q=0 from qroot,zero_mul])
  refine ⟨q,qp,point,?_,?_⟩
  · apply Matrix.ext
    intro i j
    change point (Ideal.Quotient.mk P (T i j))=fpoint (T i j)
    exact Ideal.Quotient.lift_mk _ _ _
  · have detMap : (T.map (evalRingHom (C z))).det=T.det.eval (C z) :=
      ((evalRingHom (C z)).map_det T).symm
    rw [detMap]
    exact le_of_eq order
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameMarkedSupport

-- merged module R6960CollisionMarkedIndexSupport
section Merged_R6960CollisionMarkedIndexSupport
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial Module Matrix NormalizedFiber CollisionTame
open scoped Polynomial Matrix TensorProduct Lower6960.CollisionMarked
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
local instance supportedFibreRing (z:k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)
abbrev FibreGeneric (z:k) := (FractionRing (Polynomial k)) ⊗[(Polynomial k)] Fiber E z
theorem fibre_index_supported (p : ℕ) [CharP k p] [CharP (FractionRing (Polynomial k)) p]
    (small : finrank (FractionRing (Plane k)) E<p)
    (z:k) [IsReduced (FibreGeneric (E:=E) z)]
    (δ:Plane k) (nz:δ≠0)
    (principal : normalizationDiscriminant (A:=Plane k) (E:=E) (FractionRing (Plane k))=Ideal.span {δ})
    [DecidableEq k] :
    (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0 ∧
    ∃ d:(Polynomial k), d≠0 ∧ d^2∣δ.eval (C z) ∧
      (∀ x∈d.roots, 2≤((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x) ∧
      ∀ v:FibreGeneric (E:=E) z, IsIntegral (Polynomial k) v →
        ∃ u:Fiber E z,(1 ⊗ₜ[(Polynomial k)] u : FibreGeneric (E:=E) z)=algebraMap (Polynomial k) (FibreGeneric (E:=E) z) d*v := by
  classical
  let A := Plane k
  let R := (Polynomial k)
  let K := FractionRing R
  let F := FractionRing A
  let V := FibreGeneric (E:=E) z
  let I := Fin (finrank (FractionRing (Plane k)) E)
  let : CommRing (integralClosure R V) :=
    @Subalgebra.toCommRing R V _ _ (inferInstance : Algebra R V) (integralClosure R V)
  let : Algebra R (integralClosure R V) := (integralClosure R V).algebra'
  let j := evalRingHom (C z)
  obtain ⟨b,bf,u,g,red,gen,one,patch⟩ := scalar_fibre_frames (E:=E) z
  let bk : Basis I K V := b.baseChange K
  let : FiniteDimensional K V := Module.Finite.of_basis bk
  have smallV : finrank K V<p := by
    rw [finrank_eq_card_basis bk,Fintype.card_fin]
    exact small
  let φ : Fiber E z→ₐ[R]V := Algebra.TensorProduct.includeRight
  obtain ⟨n,D,dn,nn,⟨lift,lift_apply,coords⟩,trace,clears⟩ :=
    reduced_fibre_index (A:=R) (K:=K) p smallV φ b bk (b.baseChange_apply K)
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  have reduce : T.map j=traceMatrix R b := gram_reduces_on_fibre z b bf u g red gen one patch
  have det_red : j T.det=(traceMatrix R b).det :=
    (RingHom.map_det j T).trans (congrArg Matrix.det reduce)
  have δmem : δ∈normalizationDiscriminant (A:=A) (E:=E) F := by
    rw [principal]
    exact Ideal.subset_span (Set.mem_singleton δ)
  have cleared : T.det∣g^(2*Fintype.card I)*δ := gramIdeal_clear tr u g patch δ δmem
  have trace_div : (traceMatrix R b).det∣j δ := by
    have h := map_dvd j cleared
    rw [map_mul,map_pow,show j g=1 from one,one_pow,one_mul,det_red] at h
    exact h
  have square : D.det^2∣δ.eval (C z) :=
    (trace ▸ BranchIndex.index_square (traceMatrix R n) D).trans trace_div
  let f : (I→A)→ₗ[A]Order k E := ∑ i, (LinearMap.proj i).smulRight (u i)
  have sum (t:I→A) : f t=∑ i,t i • u i := by
    simp only [f,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]
    apply Finset.sum_congr (by ext i; simp)
    intro i _
    rfl
  have inj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro t ht
    have h : (Order k E).val (f t)=(Order k E).val 0 :=
      congrArg (Order k E).val ht
    rw [sum,map_sum,map_zero] at h
    have hh : (∑ i,algebraMap A F (t i) • bf i)=0 := by
      have cols : (∑ i,algebraMap A F (t i) • bf i)=∑ i,((t i • u i:Order k E):E) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [gen,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      rw [cols]
      exact h
    funext i
    apply IsFractionRing.injective A F
    have ki := congrArg (fun a:E=>bf.repr a i) hh
    rw [bf.repr_sum_self,map_zero,Finsupp.zero_apply] at ki
    exact ki.trans (map_zero _).symm
  have clear (x:Order k E) : ∃ t,f t=g • x := by
    obtain ⟨t,ht⟩ := patch x
    exact ⟨t,(sum t).trans ht⟩
  have actual_trace_nonzero : (traceMatrix R b).det≠0 := by
    rw [trace,det_mul,det_mul,det_transpose]
    exact mul_ne_zero (mul_ne_zero dn nn) dn
  have δ_div_T : δ∣T.det := Ideal.mem_span_singleton.mp
    (principal ▸ gramIdeal_mem tr u)
  have δ_div_trace : j δ∣(traceMatrix R b).det := det_red ▸ map_dvd j δ_div_T
  have nzδz : j δ≠0 := fun h=>actual_trace_nonzero (zero_dvd_iff.mp (h ▸ δ_div_trace))
  have good : (branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0 := by
    let δs := Bivariate.swap δ
    let jz : Plane k→+*(Polynomial k) := Polynomial.mapRingHom (evalRingHom z)
    have nzs : δs≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
    have compare := (branch_weighted_product δs nzs).map jz
    intro zero
    change jz (∏ i : branchFactors δs,(i:Plane k))=0 at zero
    rw [map_prod,Finset.prod_eq_zero_iff] at zero
    obtain ⟨i,hi,iz⟩ := zero
    have wzero : jz (∏ l : branchFactors δs,(l:Plane k)^branchWeight δs l)=0 := by
      rw [map_prod]
      apply Finset.prod_eq_zero hi
      rw [map_pow,iz,zero_pow (branch_weight_pos δs i).ne']
    have bad : jz δs=0 := zero_dvd_iff.mp (wzero ▸ compare.dvd)
    apply nzδz
    change δ.eval (C z)=0
    change δs.map (evalRingHom z)=0 at bad
    rw [←RetainedCompression.eval_swap,Bivariate.swap_swap_apply] at bad
    exact bad
  have not_simple (x:k)
      (simple : ((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x=1) :
      D.det.eval x≠0 := by
    obtain ⟨q,qp,v,agree,bound⟩ := transverse_corank_receipt δ nz principal z x good simple
      p small u f sum inj g one clear T rfl
    let P := Ideal.span {q}
    let : P.IsPrime := (Ideal.span_singleton_prime qp.ne_zero).mpr qp
    rw [reduce] at agree bound
    have card : Fintype.card I=finrank F E := Fintype.card_fin _
    have little : Fintype.card I<p := card.symm ▸ small
    let along : Matrix I I (A ⧸ P) := T.map (Ideal.Quotient.mk P)
    have hb : (traceMatrix R b).det.rootMultiplicity x≤Fintype.card I-(along.map (branchResidue P)).rank := by
      rw [card]
      exact bound
    let residual : A ⧸ P→+*IsLocalRing.ResidueField (Localization.AtPrime P) := branchResidue P
    have rg : Function.Injective residual := branchResidue_injective P
    have pt : along.map v=(traceMatrix R b).map (evalRingHom x) := agree
    refine comparison_transverse_unit (k:=k) (B0:=Fiber E z) (N0:=integralClosure R V)
      (J:=I) (A:=A ⧸ P) (F:=IsLocalRing.ResidueField (Localization.AtPrime P))
      b n lift D coords dn nn trace p little x along v residual rg ?_ ?_
    · exact pt
    · exact hb
  refine ⟨good,D.det,dn,square,?_,clears⟩
  intro x hx
  have droot : D.det.eval x=0 := (mem_roots dn).mp hx
  have δroot : (j δ).eval x=0 := by
    obtain ⟨a,ha⟩ := square
    change j δ=D.det^2*a at ha
    rw [ha,eval_mul,eval_pow,droot,zero_pow (by decide),zero_mul]
  let δs := Bivariate.swap δ
  have nzs : δs≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
  let e : Plane k→+*k := (evalRingHom x).comp (evalRingHom (C z))
  have wt := (branch_weighted_product δs nzs).map (e.comp Bivariate.swap.toRingHom)
  have zprod : (e.comp Bivariate.swap.toRingHom) (∏ i : branchFactors δs, (i:Plane k)^branchWeight δs i)=0 := by
    apply zero_dvd_iff.mp
    rw [show (e.comp Bivariate.swap.toRingHom) δs=0 by
      change e (Bivariate.swap (Bivariate.swap δ))=0
      rw [Bivariate.swap_swap_apply]
      exact δroot] at wt
    exact wt.dvd'
  rw [map_prod,Finset.prod_eq_zero_iff] at zprod
  obtain ⟨i,_,iz⟩ := zprod
  have factor_zero : (e.comp Bivariate.swap.toRingHom) (i:Plane k)=0 := by
    by_contra nonzero
    exact pow_ne_zero _ nonzero ((map_pow _ _ _).symm.trans iz)
  have br : ((branchProduct δs).map (evalRingHom z)).eval x=0 := by
    rw [branchProduct,Polynomial.map_prod,eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (((i:Plane k).map (evalRingHom z)).eval x)=0
    rw [←RetainedCompression.eval_swap]
    exact factor_zero
  have pos := (rootMultiplicity_pos'.mpr ⟨good,br⟩ :
    0<((branchProduct δs).map (evalRingHom z)).rootMultiplicity x)
  have ne : ((branchProduct δs).map (evalRingHom z)).rootMultiplicity x≠1 :=
    fun h=>not_simple x h droot
  change 2≤((branchProduct δs).map (evalRingHom z)).rootMultiplicity x
  omega
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedIndexSupport

-- merged module R6960CollisionMarkedAxisGeneric
section Merged_R6960CollisionMarkedAxisGeneric
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4100000
set_option synthInstance.maxHeartbeats 95000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
open Lower6960.LineEuler (chartLocalization)
private theorem lineCoordinateUnit
    (t : Submonoid.powers (Polynomial.X:(Polynomial L))) :
    IsUnit (algebraMap (Polynomial L) (FractionRing (Polynomial L)) (t:(Polynomial L))) := by
  obtain ⟨n,nt⟩ := t.property
  apply IsUnit.mk0
  apply (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (FractionRing (Polynomial L)))).mpr
  rw [←nt]
  exact pow_ne_zero _ Polynomial.X_ne_zero
@[instance_reducible] def laurentOnFraction (b:Bool) : Algebra (Laurent L) (FractionRing (Polynomial L)) :=
  let : Algebra (Polynomial L) (Laurent L) := (chartEmbedding b).toRingHom.toAlgebra
  let : IsLocalization.Away (Polynomial.X:(Polynomial L)) (Laurent L) := Lower6960.LineEuler.chartLocalization b
  (IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:(Polynomial L)))
    (g:=algebraMap (Polynomial L) (FractionRing (Polynomial L))) lineCoordinateUnit).toAlgebra
theorem laurentOnFraction_scalar (b:Bool) (a:(Polynomial L)) :
    let : Algebra (Laurent L) (FractionRing (Polynomial L)) := laurentOnFraction b
    algebraMap (Laurent L) (FractionRing (Polynomial L)) (chartEmbedding b a)=
      algebraMap (Polynomial L) (FractionRing (Polynomial L)) a := by
  let : Algebra (Polynomial L) (Laurent L) := (chartEmbedding b).toRingHom.toAlgebra
  let : IsLocalization.Away (Polynomial.X:(Polynomial L)) (Laurent L) := Lower6960.LineEuler.chartLocalization b
  change IsLocalization.lift (M:=Submonoid.powers (Polynomial.X:(Polynomial L))) lineCoordinateUnit
    (algebraMap (Polynomial L) (Laurent L) a)=_
  exact IsLocalization.lift_eq _ _
@[instance_reducible] def lineOnLaurentFraction (b:Bool) : Algebra (Polynomial L) (FractionRing (Laurent L)) :=
  ((algebraMap (Laurent L) (FractionRing (Laurent L))).comp (chartEmbedding b).toRingHom).toAlgebra
def chartFractionToLaurent (b:Bool) :
    let : Algebra (Polynomial L) (FractionRing (Laurent L)) := lineOnLaurentFraction b
    FractionRing (Polynomial L) ≃ₐ[(Polynomial L)] FractionRing (Laurent L) := by
  let R := (Polynomial L)
  let Λ := Laurent L
  let K := FractionRing R
  let F := FractionRing Λ
  let : Algebra R F := lineOnLaurentFraction b
  let : Algebra R Λ := (chartEmbedding b).toRingHom.toAlgebra
  let : Algebra Λ K := laurentOnFraction b
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : IsScalarTower R Λ K := IsScalarTower.of_algebraMap_eq fun r=>(laurentOnFraction_scalar b r).symm
  let : IsLocalization.Away (Polynomial.X:R) Λ := Lower6960.LineEuler.chartLocalization b
  let : IsFractionRing Λ K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X:R)) Λ K
  let e := IsLocalization.algEquiv (nonZeroDivisors Λ) K F
  refine { e.toRingEquiv with commutes' := fun r=>?_ }
  change e (algebraMap R K r)=algebraMap R F r
  rw [←laurentOnFraction_scalar b r,e.commutes]
  rfl
variable {E : Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E]
local instance genericAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
local instance genericAxisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)
abbrev AxisGeneric (z:L) := (FractionRing (Laurent L))⊗[Laurent L] Axis E true z
def axisGenericData (b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let φ : Fiber E z→+*Axis E true z := (axisFibreData (E:=E) b z nz).val
    { e : FibreGeneric (E:=E) z ≃+* AxisGeneric (E:=E) z //
      (∀ v:Fiber E z,e (1 ⊗ₜ[(Polynomial L)] v)=1 ⊗ₜ[Laurent L] φ v) ∧
      ∀ r:FractionRing (Polynomial L),e (r ⊗ₜ[(Polynomial L)] 1)=chartFractionToLaurent b r ⊗ₜ[Laurent L] 1 } := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let R := (Polynomial L)
  let Λ := Laurent L
  let K := FractionRing R
  let F := FractionRing Λ
  let B := Fiber E z
  let U := Axis E true z
  let : Algebra R Λ := (chartEmbedding b).toRingHom.toAlgebra
  let : Algebra R B := CollisionMarked.fibreAlgebra z
  let : Algebra R F := lineOnLaurentFraction b
  let : Module R Λ := (inferInstance : Algebra R Λ).toModule
  let : Module R B := (inferInstance : Algebra R B).toModule
  let : Module R F := (inferInstance : Algebra R F).toModule
  let : Module Λ F := (inferInstance : Algebra Λ F).toModule
  let : SMul R Λ := (inferInstance : Algebra R Λ).toSMul
  let : SMul Λ F := (inferInstance : Algebra Λ F).toSMul
  let : SMul R F := (inferInstance : Algebra R F).toSMul
  let : IsScalarTower R Λ F := IsScalarTower.of_algebraMap_eq fun _=>rfl
  let : IsScalarTower R R F := IsScalarTower.of_algebraMap_eq (R:=R) (S:=R) (A:=F) fun _=>by
    rw [Algebra.algebraMap_self,RingHom.id_apply]
  let φ := (axisFibreData (E:=E) b z nz).val
  let first : (K⊗[R] B) ≃ₐ[R] (F⊗[R] B) :=
    Algebra.TensorProduct.congr (chartFractionToLaurent b) (AlgEquiv.refl (R:=R) (A₁:=B))
  let : CommRing (Λ⊗[R] B) := Algebra.TensorProduct.instCommRing (R:=R) (A:=Λ) (B:=B)
  let : Algebra Λ (Λ⊗[R] B) :=
    Algebra.TensorProduct.leftAlgebra (R:=R) (S:=Λ) (A:=Λ) (B:=B)
  let : Module Λ (Λ⊗[R] B) := (inferInstance : Algebra Λ (Λ⊗[R] B)).toModule
  let middle := (Algebra.TensorProduct.cancelBaseChange R Λ F F B).symm
  let torus := axisLaurentData (E:=E) b z nz
  let last : (F⊗[Λ] (Λ⊗[R] B))≃ₐ[F](F⊗[Λ] U) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R:=F) (A₁:=F)) torus.val
  have first_tmul (r:K) (v:B) : first (r ⊗ₜ[R] v)=chartFractionToLaurent b r ⊗ₜ[R] v := by
    dsimp only [first]
    rw [Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨first.toRingEquiv.trans (middle.toRingEquiv.trans last.toRingEquiv),?_,?_⟩
  · intro v
    change last (middle (first (1 ⊗ₜ[R] v)))=_
    rw [first_tmul,map_one,Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change (1:F) ⊗ₜ[Λ] torus.val (1 ⊗ₜ[R] v)=_
    rw [torus.property]
  · intro r
    change last (middle (first (r ⊗ₜ[R] (1:B))))=_
    rw [first_tmul,Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change (chartFractionToLaurent b r) ⊗ₜ[Λ] torus.val (1 ⊗ₜ[R] (1:B))=_
    rw [torus.property,map_one]
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisGeneric

end Merged_R6960CollisionMarkedAxisGeneric

-- merged module R6960CollisionMarkedCommonAxis
section Merged_R6960CollisionMarkedCommonAxis

-- merged module R6960CollisionMarkedAxisSection
section Merged_R6960CollisionMarkedAxisSection
set_option synthInstance.maxHeartbeats 200000
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open RetainedSurfaceClass RetainedRestrictionTorus ChartSections
open RetainedTwistedRestriction MarkedEvaluation
variable {E : Type} [Field E] [Algebra ChartField E]
local instance sectionAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
def axisX (z:L) : (Axis E true z)ˣ :=
  Units.map (Ideal.Quotient.mk (axisIdeal E true z)).toMonoidHom (varUnit E false)
theorem fibreSection_of_chart_pair (a:ℕ) (z:L) (v:Axis E true z)
    (finite : v∈chartImage E true z false)
    (infinity : ((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v∈chartImage E true z true) :
    FibreSection (E:=E) a z v := by
  intro b
  cases b
  · obtain ⟨u,reg,val⟩ := finite
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true false)=1 := by
      apply Subtype.ext
      change algebraMap ChartField E (localFrame (reference true false) false)=1
      rw [show localFrame (reference true false) false=1 from rfl,map_one]
    rw [eq,one_pow,one_mul]
    exact val
  · obtain ⟨u,reg,val⟩ := infinity
    refine ⟨u,reg,?_⟩
    have eq : torFrame E (reference true true)=(varUnit E false:Tor E) := rfl
    rw [eq]
    change Ideal.Quotient.mk (axisIdeal E true z) (((varUnit E false:Tor E)^a)*u)=v
    rw [map_mul,map_pow]
    have q : Ideal.Quotient.mk (axisIdeal E true z) (varUnit E false:Tor E)=
        (axisX (E:=E) z:Axis E true z) := rfl
    rw [q,show Ideal.Quotient.mk (axisIdeal E true z) u=((↑(axisX (E:=E) z)⁻¹:Axis E true z)^a)*v from val,
      ←mul_assoc,←mul_pow,Units.mul_inv,one_pow,one_mul]
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedAxisSection

-- merged module R6960CollisionMarkedCommonAxis
section Merged_R6960CollisionMarkedCommonAxis
set_option synthInstance.maxHeartbeats 200000
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open MonicChart (ChartField)
open NormalizedFiber RetainedSurfaceClass LineEuler Polynomial Algebra Module
open scoped Lower6960.CollisionMarked Lower6960.RetainedSurfaceClass Polynomial TensorProduct
variable {E : Type} [Field E] [Algebra ChartField E]
local instance commonAxisRing (z:L) : CommRing (Axis E true z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E true z)
local instance commonAxisFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)
def axisToGeneric (z:L) : Axis E true z→+*AxisGeneric (E:=E) z :=
  (Algebra.TensorProduct.includeRight (R:=Laurent L) (A:=FractionRing (Laurent L))
    (B:=Axis E true z)).toRingHom
theorem axisToGeneric_injective [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (z:L) (nz:z≠0) : Function.Injective (axisToGeneric (E:=E) z) := by
  let U := Axis E true z
  let B := chartImage E true z false
  let Λ := Laurent L
  let F := FractionRing Λ
  let : Module.Free (Polynomial L) B := chart_free E true z false
  let A := Module.Free.chooseBasis (Polynomial L) B
  let b := localFreeBasis false A (nativeMap E true z false) (native_localization E true z nz false)
  let bk := b.baseChange F
  intro v w eq
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have h := congrArg (fun a : F⊗[Λ] U=>bk.repr a i) eq
  change (b.baseChange F).repr ((1:F) ⊗ₜ[Λ] v) i=(b.baseChange F).repr ((1:F) ⊗ₜ[Λ] w) i at h
  rw [Basis.baseChange_repr_tmul,Basis.baseChange_repr_tmul,
    Algebra.smul_def,Algebra.smul_def,mul_one,mul_one] at h
  exact IsFractionRing.injective Λ F h
theorem axis_polyEval (b:Bool) (z:L) (h:(Polynomial L)) :
    polyMap E true z b h=h.eval₂ (algebraMap L (Axis E true z))
      (if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)) := by
  let U := Axis E true z
  let π : Tor E→+*U := Ideal.Quotient.mk (axisIdeal E true z)
  let a : U := if b then ↑(axisX (E:=E) z)⁻¹ else ↑(axisX (E:=E) z)
  let ev := eval₂RingHom (algebraMap L U) a
  have identity : polyMap E true z b=ev := by
    apply Polynomial.ringHom_ext
    · intro c
      change π (along E true b (C c))=ev (C c)
      rw [show along E true b (C c)=algebraMap L (Tor E) c from eval₂_C _ _,show ev (C c)=algebraMap L U c from eval₂_C _ _]
      rfl
    · rw [show ev Polynomial.X=a from eval₂_X _ _]
      change π (along E true b Polynomial.X)=a
      rw [show along E true b Polynomial.X=torVar E false b from eval₂_X _ _]
      cases b <;> rfl
  exact DFunLike.congr_fun identity h
theorem axisGenericData_scalar [FiniteDimensional ChartField E]
    (b:Bool) (z:L) (nz:z≠0) (h:(Polynomial L)) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let V := FibreGeneric (E:=E) z
    let g : V≃+*AxisGeneric (E:=E) z := (axisGenericData (E:=E) b z nz).val
    g (algebraMap (Polynomial L) V h)=axisToGeneric (E:=E) z (polyMap E true z b h) := by
  let : Algebra (Plane L) E := axisPlaneAlgebra b
  let B := Fiber E z
  let V := FibreGeneric (E:=E) z
  let g := axisGenericData (E:=E) b z nz
  let f := axisFibreData (E:=E) b z nz
  have j : algebraMap (Polynomial L) V h=(1 ⊗ₜ[(Polynomial L)] (algebraMap (Polynomial L) B h):V) :=
    (Algebra.TensorProduct.includeRight (R:=(Polynomial L)) (A:=FractionRing (Polynomial L)) (B:=B)).commutes h |>.symm
  change g.val (algebraMap (Polynomial L) V h)=axisToGeneric (E:=E) z (polyMap E true z b h)
  rw [j,g.property.1]
  change axisToGeneric (E:=E) z (f.val (baseMap E z h))=_
  rw [axisFibreData_scalar]
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedCommonAxis

end Merged_R6960CollisionMarkedCommonAxis
