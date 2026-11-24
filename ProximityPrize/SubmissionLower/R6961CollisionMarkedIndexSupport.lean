import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreBaseChange
import ProximityPrize.SubmissionLower.R6961CollisionMarkedIndexSpecialization
import ProximityPrize.SubmissionLower.R6960CollisionTameFibreTrace
import ProximityPrize.SubmissionLower.R6961CollisionTameMarkedSupport

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open Algebra Polynomial Module Matrix Lower6960.NormalizedFiber Lower6960.CollisionTame Lower6961.CollisionTame
open scoped Polynomial Matrix TensorProduct Lower6960.CollisionMarked Lower6961.CollisionMarked

variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

local instance supportedFibreRing (z:k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)

abbrev FibreGeneric (z:k) := (FractionRing (Polynomial k)) ⊗[(Polynomial k)] Fiber E z

/-- The true determinant index of the original fibre order can have roots
only where the reduced surface branch has root multiplicity at least two.
The square divisibility and the return map to the original order use the
same comparison basis. -/
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
    (trace ▸ Lower6960.BranchIndex.index_square (traceMatrix R n) D).trans trace_div
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

#print axioms fibre_index_supported
end
end Lower6961.CollisionMarked
