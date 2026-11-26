import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreIndex
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960MarkedMatrixNorm
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues

section Merged6967_R6960CollisionMarkedIndexSpecialization
set_option Elab.async false






set_option Elab.async false

-- merged module R6960BranchIndex
section Merged_R6960BranchIndex
noncomputable section
set_option Elab.async false
namespace Lower6960.BranchIndex
open Finset Polynomial Matrix
open scoped BigOperators Polynomial Matrix
open BranchCollisions
variable {K : Type} [Field K] [DecidableEq K]
private theorem mult_pow (p : (Polynomial K)) (a : K) (n : ℕ) :
    (p^n).rootMultiplicity a=n*p.rootMultiplicity a := by
  simp only [←Polynomial.count_roots,roots_pow,Multiset.count_nsmul]
theorem mult_product {ι : Type*} (F : ι→(Polynomial K)) (w : ι→ℕ) (S : Finset ι)
    (nz : ∀ i∈S,F i≠0) (x : K) :
    (∏ i∈S,(F i)^w i).rootMultiplicity x=∑ i∈S,w i*(F i).rootMultiplicity x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S ni ih =>
    have rest (j) (hj : j∈S) := nz j (mem_insert_of_mem hj)
    rw [prod_insert ni,sum_insert ni,rootMultiplicity_mul (mul_ne_zero
      (pow_ne_zero _ (nz i (mem_insert_self ..))) (prod_ne_zero_iff.mpr (fun j hj=>pow_ne_zero _ (rest j hj)))),
      mult_pow,ih rest]
theorem index_degree [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (F : ι→Polynomial (Polynomial K)) (w : ι→ℕ) (positive : ∀ i,0<w i)
    (B : Polynomial (Polynomial K)) (prod : B=∏i,F i)
    (sep : (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable)
    (T : Finset K) (good : ∀ z∈T,B.map (evalRingHom z)≠0)
    (idx : K→(Polynomial K)) (supported : ∀ z∈T, ∀ x∈(idx z).roots,2≤(B.map (evalRingHom z)).rootMultiplicity x)
    (disc : ∀ z∈T, idx z^2 ∣ ∏i, ((F i).map (evalRingHom z))^(w i))
    {s t : ℕ} (xcap : (∑ i,w i*(F i).natDegree)≤2*s)
    (zcap : (∑ i,w i*CurvatureSquares.height (F i))≤2*t) :
    (∑ z∈T,(idx z).natDegree)≤8*s*t := by
  classical
  let f (z) (i) := (F i).map (evalRingHom z)
  let xs (z : K) := (idx z).roots.toFinset
  have point (z : K) (hz : z∈T) :
      2*(idx z).natDegree≤∑ i,w i*collisionMass (f z i) (B.map (evalRingHom z)) (xs z) := by
    have nonzero : (∏i,f z i)≠0 := by
      simpa only [prod,Polynomial.map_prod,f] using good z hz
    have nz (i : ι) := prod_ne_zero_iff.mp nonzero i (mem_univ i)
    have big : (∏i,(f z i)^w i)≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (nz i))
    have each (x : K) (hx : x∈xs z) : 2*(idx z).rootMultiplicity x≤
        ∑i,w i*(if 2≤(B.map (evalRingHom z)).rootMultiplicity x then (f z i).rootMultiplicity x else 0) := by
      have h := (le_rootMultiplicity_iff big).mpr
        ((((idx z)^2).pow_rootMultiplicity_dvd x).trans (disc z hz))
      rw [mult_pow,mult_product _ _ _ (fun i _=>nz i)] at h
      simpa only [ite_eq_left (supported z hz x (Multiset.mem_toFinset.mp hx))] using h
    have deg : (∑ x∈xs z,(idx z).rootMultiplicity x)=(idx z).natDegree := by
      simp only [xs,←Polynomial.count_roots,Multiset.toFinset_sum_count_eq]
      exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
    calc 2*(idx z).natDegree = ∑ x∈xs z,2*(idx z).rootMultiplicity x := by rw [←deg,mul_sum]
         _ ≤ _ := sum_le_sum each
         _ = _ := by rw [sum_comm]; simp only [collisionMass,mul_sum]
  have upper := weighted F w positive B prod sep T xs good xcap zcap
  have total := sum_le_sum point
  rw [←mul_sum] at total
  have swap : (∑ z∈T,∑ i,w i*collisionMass (f z i) (B.map (evalRingHom z)) (xs z)) =
      ∑ i,w i*∑ z∈T,collisionMass (f z i) (B.map (evalRingHom z)) (xs z) := by
    rw [sum_comm]; simp only [mul_sum]
  rw [swap] at total
  have paid := total.trans upper
  calc (∑ z∈T,(idx z).natDegree) ≤ (16*s*t)/2 := (Nat.le_div_iff_mul_le (by decide)).mpr
         (by simpa only [Nat.mul_comm _ 2] using paid)
       _ = 8*s*t := by rw [show 16*s*t=8*s*t*2 by ring,Nat.mul_div_cancel _ (by decide)]
omit [DecidableEq K] in
theorem index_square {ι : Type*} [DecidableEq ι] [Fintype ι] (A D : Matrix ι ι (Polynomial K)) :
    D.det^2 ∣ (D.transpose*A*D).det := by
  refine ⟨A.det,?_⟩
  rw [det_mul,det_mul,det_transpose]; ring
omit [DecidableEq K] in
theorem clear_section {ι : Type*} [DecidableEq ι] [Fintype ι] (D : Matrix ι ι (Polynomial K)) (v : ι→(Polynomial K)) :
    ∃ u : ι→(Polynomial K),D.mulVec u=D.det • v := by
  refine ⟨D.adjugate.mulVec v,?_⟩
  rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
#print axioms index_degree
#print axioms clear_section
end Lower6960.BranchIndex

end
end Merged_R6960BranchIndex

-- merged module R6960TraceIndex
section Merged_R6960TraceIndex
noncomputable section
set_option Elab.async false
namespace Lower6960.TraceIndex
open Polynomial Matrix Module
open scoped Polynomial Matrix
variable {K : Type} [Field K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq K] in
private theorem corank_of_basis {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N] (a : Basis ι K M) (b : Basis ι K N) (f : M→ₗ[K]N) :
    Fintype.card ι-(LinearMap.toMatrix a b f).rank=Module.finrank K (LinearMap.ker f) := by
  have : FiniteDimensional K M := Module.Finite.of_basis a
  have : FiniteDimensional K N := Module.Finite.of_basis b
  rw [Matrix.rank_eq_finrank_range_toLin _ b a,Matrix.toLin_toMatrix,←Module.finrank_eq_card_basis a]
  have h:=f.finrank_range_add_finrank_ker
  omega
omit [DecidableEq K] in
private theorem trace_corank {A : Type*} [CommRing A] [Algebra K A] (a : Basis ι K A) :
    Fintype.card ι-(Algebra.traceMatrix K a).rank=Module.finrank K (LinearMap.ker (Algebra.traceForm K A)) := by
  have eq : Algebra.traceMatrix K a=LinearMap.toMatrix a a.dualBasis (Algebra.traceForm K A) := by
    ext i j
    simp only [Algebra.traceMatrix_apply,LinearMap.toMatrix_apply,Basis.dualBasis_repr,
      Algebra.traceForm_apply,mul_comm (a i)]
  rw [eq]; exact corank_of_basis _ _ _
theorem index_le_discriminant_excess {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (a : Basis ι K A) (b : Basis ι K B)
    (p : ℕ) [CharP K p] (small : Fintype.card ι<p) (φ : A→ₐ[K]B) (x : K)
    (D N : Matrix ι ι (Polynomial K)) (dn : D.det≠0) (nn : N.det≠0)
    (mapD : (evalRingHom x).mapMatrix D=LinearMap.toMatrix a b φ.toLinearMap)
    (mapN : (evalRingHom x).mapMatrix N=Algebra.traceMatrix K b)
    (raw : (evalRingHom x).mapMatrix (D.transpose*N*D)=Algebra.traceMatrix K a) :
    D.det.rootMultiplicity x≤(D.transpose*N*D).det.rootMultiplicity x-
      (Fintype.card ι-((evalRingHom x).mapMatrix (D.transpose*N*D)).rank) := by
  have : FiniteDimensional K A := Module.Finite.of_basis a
  have : FiniteDimensional K B := Module.Finite.of_basis b
  have rank := TraceSpecialization.radical_specialization p
    ((Module.finrank_eq_card_basis a).trans_lt small) ((Module.finrank_eq_card_basis b).trans_lt small) φ
  have d := ProximityPrize.SubmissionLower.MatrixRootMultiplicity.corank_le_rootMultiplicity_det D x dn
  have n := ProximityPrize.SubmissionLower.MatrixRootMultiplicity.corank_le_rootMultiplicity_det N x nn
  rw [mapD,corank_of_basis] at d
  rw [mapN,trace_corank] at n
  have eq : (D.transpose*N*D).det=D.det^2*N.det := by rw [det_mul,det_mul,det_transpose]; ring
  rw [raw,eq,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ dn) nn),trace_corank]
  have pow : (D.det^2).rootMultiplicity x=2*D.det.rootMultiplicity x := by
    simp only [←count_roots,roots_pow,Multiset.count_nsmul]
  omega
#print axioms index_le_discriminant_excess
open P1_7_1_1_2 (exists_full_minor)
theorem rank_le_generic {A F L : Type} [CommRing A] [Field F] [Field L]
    {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n A)
    (special : A→+*F) (generic : A→+*L) (inj : Function.Injective generic) :
    (M.map special).rank≤(M.map generic).rank := by
  classical
  let B:=M.map special
  obtain ⟨α,c,hc,sp,li⟩ := exists_linearIndependent' F B.col
  let : Finite α := Finite.of_injective c hc
  let : Fintype α := Fintype.ofFinite α
  have size : Fintype.card α=B.rank := by
    rw [←finrank_span_eq_card li,sp,←Matrix.rank_eq_finrank_span_cols]
  let S:=B.submatrix id c
  have independent : LinearIndependent F S.transpose.row := li
  obtain ⟨r,hr⟩ := exists_full_minor S.transpose independent
  let D := M.submatrix r c
  have nonzero : D.det≠0 := by
    intro hz
    apply hr
    change (D.map special).transpose.det=0
    rw [Matrix.det_transpose]
    change (special.mapMatrix D).det=0
    rw [←RingHom.map_det,hz,map_zero]
  have gd : (D.map generic).det≠0 := by
    change (generic.mapMatrix D).det≠0
    rw [←RingHom.map_det]
    exact (map_ne_zero_iff generic inj).mpr nonzero
  calc (M.map special).rank = (D.map generic).rank := by
         rw [Matrix.rank_of_det_ne_zero gd]; exact size.symm
       _ ≤ _ := Matrix.rank_submatrix_le (M.map generic) r c
#print axioms rank_le_generic
theorem transverse_unit {A B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {j : Type} [Fintype j] [DecidableEq j] (a : Basis j K A) (b : Basis j K B)
    (p : ℕ) [CharP K p] (small : Fintype.card j<p) (φ : A→ₐ[K]B) (x : K)
    (D N : Matrix j j (Polynomial K)) (dn : D.det≠0) (nn : N.det≠0)
    (mapD : (evalRingHom x).mapMatrix D=LinearMap.toMatrix a b φ.toLinearMap)
    (mapN : (evalRingHom x).mapMatrix N=Algebra.traceMatrix K b)
    (raw : (evalRingHom x).mapMatrix (D.transpose*N*D)=Algebra.traceMatrix K a)
    {S L : Type} [CommRing S] [Field L] (along : Matrix j j S) (spec : S→+*K)
    (gen : S→+*L) (inj : Function.Injective gen)
    (point : along.map spec = (evalRingHom x).mapMatrix (D.transpose*N*D))
    (transverse : (D.transpose*N*D).det.rootMultiplicity x≤Fintype.card j-(along.map gen).rank) :
    D.det.eval x≠0 := by
  have rank := rank_le_generic along spec gen inj
  rw [point] at rank
  have index := index_le_discriminant_excess a b p small φ x D N dn nn mapD mapN raw
  intro zero
  have lower : 1≤D.det.rootMultiplicity x := (le_rootMultiplicity_iff dn).mpr
    (by rw [pow_one]; exact dvd_iff_isRoot.mpr zero)
  omega
#print axioms transverse_unit
end Lower6960.TraceIndex

end
end Merged_R6960TraceIndex

-- merged module R6960CollisionMarkedIndexSpecialization
section Merged_R6960CollisionMarkedIndexSpecialization
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Algebra TensorProduct Module Matrix Polynomial
open scoped Matrix Polynomial TensorProduct
variable {R B N I : Type*} {k : Type} [CommRing R] [Field k]
  [CommRing B] [CommRing N] [Algebra R B] [Algebra R N]
  [Fintype I] [DecidableEq I]
theorem comparison_tensor_specialization (j:R→+*k)
    (b:Basis I R B) (n:Basis I R N) (φ:B→ₐ[R]N) :
    let : Algebra R k := j.toAlgebra
    let a := b.baseChange k
    let c := n.baseChange k
    let ψ := Algebra.TensorProduct.map (AlgHom.id k k) φ
    (n.toMatrix (fun i=>φ (b i))).map j=LinearMap.toMatrix a c ψ.toLinearMap ∧
    (traceMatrix R n).map j=traceMatrix k c ∧
    (traceMatrix R b).map j=traceMatrix k a := by
  let : Algebra R k := j.toAlgebra
  refine ⟨?_,?_,?_⟩
  · apply Matrix.ext
    intro i l
    rw [Matrix.map_apply,Basis.toMatrix_apply,LinearMap.toMatrix_apply]
    change j (n.repr (φ (b l)) i) = (n.baseChange k).repr
      ((Algebra.TensorProduct.map (AlgHom.id k k) φ) (b.baseChange k l)) i
    rw [b.baseChange_apply k,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,n.baseChange_repr_tmul k,
      Algebra.smul_def,mul_one]
    rfl
  · exact trace_matrix_map_of_basis j n (n.baseChange k)
      (Algebra.TensorProduct.includeRight (R:=R) (A:=k) (B:=N)).toRingHom
      (fun _=>Algebra.TensorProduct.includeRight.commutes _) (fun i=>(n.baseChange_apply k i).symm)
  · exact trace_matrix_map_of_basis j b (b.baseChange k)
      (Algebra.TensorProduct.includeRight (R:=R) (A:=k) (B:=B)).toRingHom
      (fun _=>Algebra.TensorProduct.includeRight.commutes _) (fun i=>(b.baseChange_apply k i).symm)
variable {B0 N0 : Type} [CommRing B0] [CommRing N0] [Algebra (Polynomial k) B0] [Algebra (Polynomial k) N0]
theorem comparison_transverse_unit {J : Type} [Fintype J] [DecidableEq J]
    (b : Basis J (Polynomial k) B0) (n : Basis J (Polynomial k) N0) (φ : B0→ₐ[(Polynomial k)]N0)
    (D : Matrix J J (Polynomial k)) (coords : D=n.toMatrix (fun i=>φ (b i)))
    (dn : D.det≠0) (nn : (traceMatrix (Polynomial k) n).det≠0)
    (trace : traceMatrix (Polynomial k) b=D.transpose*traceMatrix (Polynomial k) n*D)
    (p : ℕ) [CharP k p] (small : Fintype.card J<p)
    (x : k) {A F : Type} [CommRing A] [Field F]
    (along : Matrix J J A) (spec : A→+*k) (gen : A→+*F) (inj : Function.Injective gen)
    (point : along.map spec=(traceMatrix (Polynomial k) b).map (evalRingHom x))
    (transverse : (traceMatrix (Polynomial k) b).det.rootMultiplicity x≤Fintype.card J-(along.map gen).rank) :
    D.det.eval x≠0 := by
  classical
  let j := evalRingHom x
  let : Algebra (Polynomial k) k := j.toAlgebra
  obtain ⟨dc,nc,bc⟩ := comparison_tensor_specialization j b n φ
  rw [←coords] at dc
  have raw : j.mapMatrix (D.transpose*traceMatrix (Polynomial k) n*D)=traceMatrix k (b.baseChange k) :=
    trace ▸ bc
  exact TraceIndex.transverse_unit (b.baseChange k) (n.baseChange k) p small
    (Algebra.TensorProduct.map (AlgHom.id k k) φ) x D (traceMatrix (Polynomial k) n) dn nn dc nc raw
    along spec gen inj (trace ▸ point) (trace ▸ transverse)
#print axioms comparison_transverse_unit
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedIndexSpecialization

end Merged6967_R6960CollisionMarkedIndexSpecialization

section Merged6967_R6960MarkedTranslatedEquation
set_option Elab.async false













set_option Elab.async false

-- merged module R6960CollisionMarkedFibreBaseChange
section Merged_R6960CollisionMarkedFibreBaseChange
set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Algebra
open scoped Polynomial TensorProduct
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
local instance fibreRing (z : k) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order k E)) ((Order k E).toCommRing) (sliceIdeal E z)
scoped instance fibreAlgebra (z : k) : Algebra (Polynomial k) (Fiber E z) :=
  @RingHom.toAlgebra (Polynomial k) (Fiber E z) _ (fibreRing (E:=E) z).toCommSemiring (baseMap E z)
def fibreBase (z : k) : Plane k→+*(Polynomial k) := evalRingHom (C z)
def genericFibreBase (z : k) : Plane k→+*FractionRing (Polynomial k) :=
  (algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp (fibreBase z)
def fibreAsTensor (z : k) :
    let : Algebra (Plane k) (Polynomial k) := (fibreBase z).toAlgebra
    { e : Fiber E z ≃ₐ[(Polynomial k)] ((Polynomial k)⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (quotientMap E z x)=(1:(Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let B := Order k E
  let : CommRing B := @Subalgebra.toCommRing A E _ _ (inferInstance : Algebra A E) B
  let : Algebra A R := (fibreBase z).toAlgebra
  let : IsScalarTower A A R := IsScalarTower.of_algebraMap_eq (R:=A) (S:=A) (A:=R) fun a=>by
    change algebraMap A R a=algebraMap A R (algebraMap A A a)
    rw [Algebra.algebraMap_self,RingHom.id_apply]
  let I : Ideal A := Ideal.span {Polynomial.X-C (C z)}
  let : CommRing (A ⧸ I) := Ideal.Quotient.commRing I
  let j := algebraMap A B
  have slice : sliceIdeal E z=I.map j := by
    unfold I sliceIdeal
    rw [Ideal.map_span,Set.image_singleton]
  let eq : Fiber E z ≃+* (B ⧸ I.map j) := Ideal.quotEquivOfEq slice
  let Q := Polynomial.quotientSpanXSubCAlgEquiv (C z)
  let base : (A ⧸ I) ≃ₐ[A] R := {
    Q.toRingEquiv with
    commutes' := fun a=>by
      change Q (Ideal.Quotient.mk I a)=a.eval (C z)
      exact Polynomial.quotientSpanXSubCAlgEquiv_mk (C z) a }
  let tensor := Algebra.TensorProduct.congr base (AlgEquiv.refl (R:=A) (A₁:=B))
  let ring : Fiber E z ≃+* (R⊗[A] B) := eq.trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toRingEquiv.trans tensor.toRingEquiv)
  have apply_q (x : B) : ring (quotientMap E z x)=(1:R) ⊗ₜ[A] x := by
    change tensor ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)
      (eq (Ideal.Quotient.mk (sliceIdeal E z) x)))=_
    rw [show eq (Ideal.Quotient.mk (sliceIdeal E z) x)=Ideal.Quotient.mk (I.map j) x from
      Ideal.quotEquivOfEq_mk slice x,Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (base 1) ⊗ₜ[A] x=_
    rw [map_one]
  let e : Fiber E z ≃ₐ[R] (R⊗[A] B) := { ring with
    commutes' := fun c=>by
      change ring (quotientMap E z (j (C c)))=c ⊗ₜ[A] (1:B)
      rw [apply_q,Algebra.algebraMap_eq_smul_one,TensorProduct.tmul_smul]
      change ((C c : A) • (1:R)) ⊗ₜ[A] (1:B)=_
      have h : (C c : A) • (1:R)=c := by
        rw [Algebra.smul_def,mul_one]
        change (C c).eval (C z)=c
        exact eval_C
      rw [h] }
  exact ⟨e,apply_q⟩
def genericFibreAsTensor (z : k) :
    let : Algebra (Plane k) (FractionRing (Polynomial k)) := (genericFibreBase z).toAlgebra
    { e : ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z) ≃ₐ[FractionRing (Polynomial k)]
        ((FractionRing (Polynomial k))⊗[Plane k] Order k E) //
      ∀ x : Order k E,e (1 ⊗ₜ[(Polynomial k)] quotientMap E z x)=(1:FractionRing (Polynomial k)) ⊗ₜ[Plane k] x } := by
  let A := Plane k
  let R := (Polynomial k)
  let K := FractionRing R
  let B := Order k E
  let : Algebra A R := (fibreBase z).toAlgebra
  let : Algebra A K := (genericFibreBase z).toAlgebra
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : SMul A K := (inferInstance : Algebra A K).toSMul
  let : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=K) fun _=>rfl
  let v := fibreAsTensor (E:=E) z
  let c := Algebra.TensorProduct.congr (AlgEquiv.refl (R:=K) (A₁:=K)) v.val
  let d := Algebra.TensorProduct.cancelBaseChange A R K K B
  refine ⟨c.trans d,fun x=>?_⟩
  change d (1 ⊗ₜ[R] v.val (quotientMap E z x))=_
  rw [v.property,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]
#print axioms fibreAsTensor
#print axioms genericFibreAsTensor
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedFibreBaseChange

-- merged module R6960CollisionMarkedActualSheet
section Merged_R6960CollisionMarkedActualSheet
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Module NormalizedFiber
open scoped Polynomial TensorProduct Lower6960.CollisionMarked
section Scale
variable {K : Type*} [Field K]
theorem integralNormalization_separable (p : ℕ) [CharP K p] (q : (Polynomial K))
    (pos : 0<q.natDegree) (small : q.natDegree<p) (sep : q.Separable) :
    q.integralNormalization.Separable := by
  let a := q.leadingCoeff
  let g := q.scaleRoots a
  have an : a≠0 := leadingCoeff_ne_zero.mpr sep.ne_zero
  have en : (q.natDegree:K)≠0 := by
    intro he
    have dv := (CharP.cast_eq_zero_iff K p q.natDegree).mp he
    exact pos.ne' (Nat.eq_zero_of_dvd_of_lt dv small)
  have d := MonicChart.derivative_degree q pos en
  have gn : g.natDegree=q.natDegree := natDegree_scaleRoots _ _
  have res : g.resultant g.derivative≠0 := by
    change (q.scaleRoots a).resultant (q.scaleRoots a).derivative≠0
    rw [MonicChart.scaleRoots_derivative _ _ d,resultant_scaleRoots]
    exact mul_ne_zero (pow_ne_zero _ an) (resultant_ne_zero q q.derivative sep)
  have gs : g.Separable := by
    have proof := separable_map_of_resultant_derivative_ne_zero (RingHom.id K) g (gn.symm ▸ pos)
      (by simpa only [RingHom.id_apply] using res)
    simpa only [Polynomial.map_id] using proof
  have product : (q.integralNormalization * Polynomial.C a).Separable := by
    rw [integralNormalization_mul_C_leadingCoeff]
    exact gs
  exact product.of_mul_left
end Scale
section Generic
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E]
def scaledRoot (P : (Polynomial (Plane k))) (g : E) (pn : P≠0) (root : aeval g P=0) : Order k E :=
  ⟨algebraMap (Plane k) E P.leadingCoeff*g,
    by
      have j : Function.Injective (algebraMap (Plane k) E) := by
        rw [IsScalarTower.algebraMap_eq (Plane k) (FractionRing (Plane k)) E]
        exact (algebraMap (FractionRing (Plane k)) E).injective.comp
          (IsFractionRing.injective (Plane k) (FractionRing (Plane k)))
      exact ⟨P.integralNormalization,monic_integralNormalization pn,
        integralNormalization_aeval_eq_zero root (fun a az=>j (az.trans (map_zero _).symm))⟩⟩
def scaledOrdinate (P : (Polynomial (Plane k))) (g : E) (pn : P≠0) (root : aeval g P=0) (z : k) :
    ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z) :=
  1 ⊗ₜ[(Polynomial k)] quotientMap E z (scaledRoot P g pn root)
theorem actual_scaled_word_sheet (p : ℕ) [CharP (FractionRing (Polynomial k)) p]
    (P : (Polynomial (Plane k))) (large : 2≤P.natDegree) (small : P.natDegree<p)
    (b : PowerBasis (FractionRing (Plane k)) E) (dim : b.dim=P.natDegree)
    (root : aeval b.gen P=0) (z : k) (S : (Polynomial k))
    (full : (P.map (genericFibreBase z)).natDegree=P.natDegree)
    (sep : (P.map (genericFibreBase z)).Separable)
    (word : (P.map (genericFibreBase z)).eval (algebraMap (Polynomial k) (FractionRing (Polynomial k)) S)=0) :
    let pn : P≠0 := fun h=>by rw [h,natDegree_zero] at large; omega
    let q := P.integralNormalization.map (genericFibreBase z)
    let y := genericFibreBase z P.leadingCoeff*algebraMap (Polynomial k) (FractionRing (Polynomial k)) S
    ∃ (e : AdjoinRoot q ≃ₐ[FractionRing (Polynomial k)]
        ((FractionRing (Polynomial k))⊗[(Polynomial k)] Fiber E z)) (H Q : (Polynomial (FractionRing (Polynomial k)))),
      q.Separable ∧ q=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      e (AdjoinRoot.root q)=scaledOrdinate P b.gen pn root z ∧
      let η:=e (AdjoinRoot.mk q H)
      η^2=η ∧ η≠0 ∧ η≠1 ∧
        (scaledOrdinate P b.gen pn root z-(y ⊗ₜ[(Polynomial k)] (1:Fiber E z)))*η=0 := by
  classical
  let A := Plane k
  let F := FractionRing A
  let K := FractionRing (Polynomial k)
  let j := genericFibreBase z
  let raw := P.map j
  have Pn : P≠0 := by intro h; rw [h,natDegree_zero] at large; omega
  have lcn : P.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr Pn
  have rlc : j P.leadingCoeff≠0 := by
    by_contra zero
    have drop := natDegree_map_lt' zero (by omega : 0<P.natDegree)
    exact (full.not_lt drop).elim
  let γ := algebraMap A E P.leadingCoeff*b.gen
  let f := P.integralNormalization
  have fm : f.Monic := monic_integralNormalization Pn
  have fd : f.natDegree=P.natDegree := natDegree_integralNormalization
  have rootγ : aeval γ f=0 := by
    apply integralNormalization_aeval_eq_zero root
    have ai : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    exact fun a az=>ai (az.trans (map_zero _).symm)
  let a := algebraMap A F P.leadingCoeff
  have an : a≠0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr lcn
  let unit := Units.mk0 a an
  let e0 := finCongr (dim.trans fd.symm)
  let B0 : Basis (Fin f.natDegree) F E := b.basis.reindex e0
  let B := B0.unitsSMul (fun i=>unit^(i:ℕ))
  have powers (i : Fin f.natDegree) : B i=γ^(i:ℕ) := by
    rw [show B i=unit^(i:ℕ) • B0 i from Basis.unitsSMul_apply i]
    change (↑(unit^(i:ℕ)):F) • B0 i=_
    rw [Units.val_pow_eq_pow_val]
    rw [show (unit:F)=a from rfl,show B0 i=b.basis (e0.symm i) from Basis.reindex_apply _ _ _,b.basis_eq_pow]
    change (a^(i:ℕ):F) • b.gen^(i:ℕ)=_
    rw [Algebra.smul_def,map_pow,←mul_pow]
    exact congrArg (·^(i:ℕ)) (by
      change algebraMap F E (algebraMap A F P.leadingCoeff)*b.gen=γ
      rw [←IsScalarTower.algebraMap_apply])
  let q := f.map j
  have qeq : q=raw.integralNormalization := (integralNormalization_map j P rlc).symm
  have qs : q.Separable := by
    rw [qeq]
    have d : raw.natDegree=P.natDegree := full
    exact integralNormalization_separable p raw (by rw [d]; omega) (by rw [d]; exact small) sep
  have qdeg : q.natDegree=P.natDegree := (fm.natDegree_map j).trans fd
  let s := algebraMap (Polynomial k) K S
  let y := j P.leadingCoeff*s
  have yroot : q.eval y=0 := by
    have lead : raw.leadingCoeff=j P.leadingCoeff := leadingCoeff_map_of_leadingCoeff_ne_zero _ rlc
    have root' := integralNormalization_eval₂_eq_zero (p:=raw) (z:=s) (RingHom.id K)
      (by change raw.eval s=0; exact word) (fun _ h=>h)
    rw [qeq]
    change raw.integralNormalization.eval (j P.leadingCoeff*s)=0
    change raw.integralNormalization.eval ((RingHom.id K) raw.leadingCoeff*s)=0 at root'
    rw [RingHom.id_apply,lead] at root'
    exact root'
  have simple : q.derivative.eval y≠0 := by
    have one : IsCoprime q q.derivative := qs
    obtain ⟨v,w,h⟩ := one
    intro zero
    have h0 := congrArg (fun t : (Polynomial K)=>t.eval y) h
    rw [eval_add,eval_mul,eval_mul,yroot,zero,mul_zero,mul_zero,zero_add,eval_one] at h0
    exact zero_ne_one h0
  obtain ⟨H,Q,split,one,div,he⟩ := MarkedRoot.sheet (qdeg ▸ large) y yroot simple
  let : Algebra A K := j.toAlgebra
  obtain ⟨E1,gen⟩ := monic_fibre_equiv fm γ rootγ B powers j p (fd.symm ▸ small) qs
  let E2 := (genericFibreAsTensor (E:=E) z).val.symm
  let e := E1.trans E2
  have image : e (AdjoinRoot.root q)=scaledOrdinate P b.gen Pn root z := by
    apply (genericFibreAsTensor (E:=E) z).val.injective
    have forward := (genericFibreAsTensor (E:=E) z).property (scaledRoot P b.gen Pn root)
    change (genericFibreAsTensor (E:=E) z).val (E2 (E1 (AdjoinRoot.root q)))=_
    rw [show (genericFibreAsTensor (E:=E) z).val (E2 (E1 (AdjoinRoot.root q)))=
      E1 (AdjoinRoot.root q) from (genericFibreAsTensor (E:=E) z).val.apply_symm_apply _]
    rw [gen]
    exact forward.symm
  refine ⟨e,H,Q,qs,split,one,div,image,?_⟩
  obtain ⟨idemp,nz,ne⟩ := he
  refine ⟨by rw [←map_pow,idemp],fun h=>nz (e.injective (h.trans (map_zero e).symm)),
    fun h=>ne (e.injective (h.trans (map_one e).symm)),?_⟩
  obtain ⟨J,hJ⟩ := div
  have zero : AdjoinRoot.mk q ((Polynomial.X-C y)*H)=0 := AdjoinRoot.mk_eq_zero.mpr
    ⟨J,by rw [hJ,split,mul_assoc]⟩
  have annih := congrArg e zero
  rw [map_zero,map_mul,map_sub,AdjoinRoot.mk_X,AdjoinRoot.mk_C,map_mul,map_sub,image] at annih
  have ey : e (AdjoinRoot.of q y)=y ⊗ₜ[(Polynomial k)] (1:Fiber E z) := e.commutes y
  rw [ey] at annih
  exact annih
end Generic
#print axioms integralNormalization_separable
#print axioms actual_scaled_word_sheet
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedActualSheet

-- merged module R6960CollisionMarkedProjected
section Merged_R6960CollisionMarkedProjected
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial NormalizedFiber Module
open K1_14 (L)
open RetainedCompression (MarkedFiber specialize incl eval_swap)
open scoped Polynomial TensorProduct Lower6960.CollisionMarked
def projectedRaw (P : CurvatureSquares.Ordinate) : (Polynomial (Plane L)) := P.map Bivariate.swap.toRingHom
theorem projectedRaw_degree (P : CurvatureSquares.Ordinate) :
    (projectedRaw P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective Bivariate.swap.injective _
theorem projectedRaw_fibre (P : CurvatureSquares.Ordinate) (z : L) :
    (projectedRaw P).map (genericFibreBase z)=(specialize P z).map incl := by
  apply Polynomial.ext
  intro i
  simp only [projectedRaw,RetainedCompression.specialize,coeff_map,Polynomial.coe_mapRingHom]
  change incl ((Bivariate.swap (P.coeff i)).eval (Polynomial.C z))=incl ((P.coeff i).map (evalRingHom z))
  rw [eval_swap]
theorem projected_word_sheet {E : Type} [Field E] [Algebra (Plane L) E]
    [Algebra (FractionRing (Plane L)) E] [IsScalarTower (Plane L) (FractionRing (Plane L)) E]
    [FiniteDimensional (FractionRing (Plane L)) E]
    (p : ℕ) [CharP (FractionRing (Polynomial L)) p]
    (P : CurvatureSquares.Ordinate) (large : 2≤P.natDegree) (small : P.natDegree<p)
    (b : PowerBasis (FractionRing (Plane L)) E) (dim : b.dim=P.natDegree)
    (root : aeval b.gen (projectedRaw P)=0) (z : L) (S : (Polynomial L)) (mark : MarkedFiber P z S) :
    let pn : projectedRaw P≠0 := fun h=>by
      have d := projectedRaw_degree P
      rw [h,natDegree_zero] at d
      omega
    let q := (projectedRaw P).integralNormalization.map (genericFibreBase z)
    let y := genericFibreBase z (projectedRaw P).leadingCoeff*incl S
    ∃ (e : AdjoinRoot q ≃ₐ[FractionRing (Polynomial L)] ((FractionRing (Polynomial L))⊗[(Polynomial L)] Fiber E z))
      (H Q : (Polynomial (FractionRing (Polynomial L)))),
      q.Separable ∧ q=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      e (AdjoinRoot.root q)=scaledOrdinate (projectedRaw P) b.gen pn root z ∧
      let η:=e (AdjoinRoot.mk q H)
      η^2=η ∧ η≠0 ∧ η≠1 ∧
        (scaledOrdinate (projectedRaw P) b.gen pn root z-(y ⊗ₜ[(Polynomial L)] (1:Fiber E z)))*η=0 := by
  have full : ((projectedRaw P).map (genericFibreBase z)).natDegree=(projectedRaw P).natDegree := by
    rw [projectedRaw_fibre,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have sep : ((projectedRaw P).map (genericFibreBase z)).Separable := projectedRaw_fibre P z ▸ mark.separable
  have rt : ((projectedRaw P).map (genericFibreBase z)).eval (incl S)=0 := by
    rw [projectedRaw_fibre,Polynomial.eval_map_apply,mark.root,map_zero]
  exact actual_scaled_word_sheet p (projectedRaw P) (projectedRaw_degree P ▸ large)
    (projectedRaw_degree P ▸ small) b (dim.trans (projectedRaw_degree P).symm) root z S full sep rt
#print axioms projected_word_sheet
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedProjected

-- merged module R6960MarkedTranslatedEquation
section Merged_R6960MarkedTranslatedEquation
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open MonicFourChartDescent RetainedSurfaceClass NormalizedFiber CollisionMarked Polynomial Algebra
open scoped Polynomial Lower6960.MonicChart
open Lower6960.RetainedSurfaceClass (oriented_var oriented_const oriented_line)
def translatedX (c:L) : (Polynomial L)→+*Scalar := (translateField Scalar c).toRingHom.comp (algebraMap (Polynomial L) Scalar)
def rowPlane (c:L) : Plane L→+*(Polynomial Scalar) := eval₂RingHom (C.comp (translatedX c)) Polynomial.X
local notation "fp" => algebraMap (Polynomial Scalar) ChartField
private theorem translatedX_const (c a:L) : translatedX c (C a)=inner a := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar (C a))=_
  rw [translate_polynomial,taylor_C];rfl
private theorem translatedX_var (c:L) : translatedX c Polynomial.X=algebraMap (Polynomial L) Scalar Polynomial.X+inner c := by
  change translateField Scalar c (algebraMap (Polynomial L) Scalar Polynomial.X)=_
  rw [translate_polynomial,taylor_X,map_add];rfl
theorem row_plane (c:L) (p:Plane L) :
    rowBase c ((oriented true false p):ChartField)=fp (rowPlane c p) := by
  let f:Plane L→+*ChartField:= (rowBase c).toRingHom.comp ((baseChart _).subtype.comp (oriented true false).toRingHom)
  let g:Plane L→+*ChartField:=(algebraMap (Polynomial Scalar) ChartField).comp (rowPlane c)
  have eq:f=g := by
    apply Polynomial.ringHom_ext
    · intro v
      have innerEq:f.comp C=g.comp C := by
        apply Polynomial.ringHom_ext
        · intro a
          change rowBase c ((oriented true false (C (C a))):ChartField)=fp ((C (C a)).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_const,row_constant,eval₂_C,RingHom.comp_apply,translatedX_const,RatFunc.algebraMap_C];rfl
        · change rowBase c ((oriented true false (C Polynomial.X)):ChartField)=fp ((C Polynomial.X).eval₂ (C.comp (translatedX c)) Polynomial.X)
          rw [Lower6960.RetainedSurfaceClass.oriented_line,eval₂_C,RingHom.comp_apply,translatedX_var,RatFunc.algebraMap_C,map_add]
          exact row_abscissa c
      exact DFunLike.congr_fun innerEq v
    · change rowBase c ((oriented true false Polynomial.X):ChartField)=fp (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X)
      rw [Lower6960.RetainedSurfaceClass.oriented_var,eval₂_X,RatFunc.algebraMap_X];exact row_parameter c
  exact DFunLike.congr_fun eq p
theorem row_specialization (c z:L) :
    (evalRingHom (inner z)).comp (rowPlane c)=(translateField Scalar c).toRingHom.comp (genericFibreBase z) := by
  apply Polynomial.ringHom_ext
  · intro v
    change ((C v).eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar ((C v).eval (C z)))
    rw [eval₂_C,RingHom.comp_apply,eval_C,eval_C];rfl
  · change (Polynomial.X.eval₂ (C.comp (translatedX c)) Polynomial.X).eval (inner z)=
      translateField Scalar c (algebraMap (Polynomial L) Scalar (Polynomial.X.eval (C z)))
    rw [eval₂_X,eval_X,eval_X];exact (translatedX_const c z).symm
theorem normalized_fibre_separable (z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p)
    (mark:RetainedCompression.MarkedFiber P z S) :
    ((projectedRaw P).integralNormalization.map (genericFibreBase z)).Separable := by
  let raw:=projectedRaw P
  let J:=genericFibreBase z
  have full:(raw.map J).natDegree=raw.natDegree := by
    rw [show raw.map J= _ from projectedRaw_fibre P z,natDegree_map_eq_of_injective (IsFractionRing.injective _ _),mark.full,projectedRaw_degree]
  have nz:J raw.leadingCoeff≠0 := fun bad=>(natDegree_map_lt' bad (projectedRaw_degree P ▸ lo)).ne full
  have base:(raw.map J).Separable := projectedRaw_fibre P z ▸ mark.separable
  rw [←integralNormalization_map J raw nz]
  apply integralNormalization_separable p _ _ _ base <;> rwa [full,projectedRaw_degree]
theorem marked_row_separable (c z:L) (P:CurvatureSquares.Ordinate) (S:(Polynomial L))
    (p:ℕ) [CharP Scalar p] (lo:0<P.natDegree) (hi:P.natDegree<p) (mark:RetainedCompression.MarkedFiber P z S) :
    ((((projectedRaw P).integralNormalization.map (rowPlane c)).map (evalRingHom (inner z)))).Separable := by
  rw [Polynomial.map_map,row_specialization,←Polynomial.map_map]
  exact (normalized_fibre_separable z P S p lo hi mark).map
theorem scaled_row_degree {F E Ω:Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]
    (b:PowerBasis F E) (σ:F≃+*F) (ev:E→+*Ω)
    (base:∀a,ev (algebraMap F E a)=algebraMap F Ω (σ a)) (a:F) (nz:a≠0) :
    (minpoly F (ev (algebraMap F E a*b.gen))).natDegree=b.dim := by
  let q:=minpoly F b.gen
  let Q:=q.map σ.toRingHom
  have mon:Q.Monic:=(minpoly.monic b.isIntegral_gen).map _
  have irr:Irreducible Q:=(MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mpr (minpoly.irreducible b.isIntegral_gen)
  have h:(algebraMap F Ω).comp σ.toRingHom=ev.comp (algebraMap F E) := RingHom.ext (fun r=>(base r).symm)
  have zero:aeval (ev b.gen) Q=0 := by
    rw [aeval_def,show Q=q.map σ.toRingHom from rfl,eval₂_map,h,←Polynomial.hom_eval₂]
    exact (congrArg ev (minpoly.aeval F b.gen)).trans (map_zero _)
  have eq:=minpoly.eq_of_irreducible_of_monic irr zero mon
  rw [map_mul,base,←Algebra.smul_def,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff _ σ.injective).mpr nz)
    (show IsIntegral F (ev b.gen) from ⟨Q,mon,zero⟩),natDegree_scaleRoots,←eq,
    show Q=q.map σ.toRingHom from rfl,natDegree_map_eq_of_injective σ.injective,b.natDegree_minpoly]
#print axioms row_plane
#print axioms marked_row_separable
#print axioms scaled_row_degree
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedTranslatedEquation

end Merged6967_R6960MarkedTranslatedEquation

section Merged6967_R6960RetainedGlobalEvaluation
set_option Elab.async false




set_option Elab.async false

-- merged module R6960RetainedLineEvaluation
section Merged_R6960RetainedLineEvaluation
noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedLineEvaluation
open Polynomial Algebra Module
open scoped Polynomial
open Lower6960.TraceSpecialization (idempotent_multiple)
variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra (Polynomial k) S]
omit [Algebra k S] in
private theorem idempotent_survives [Module.Free (Polynomial k) S] {u : S} (id : u^2=u) (ne : u≠0)
    (a : k) : ¬algebraMap (Polynomial k) S (Polynomial.X-C a) ∣ u := by
  classical
  rintro ⟨w,eq⟩
  let b:=Module.Free.chooseBasis (Polynomial k) S
  obtain ⟨i,hi⟩ : ∃ i, b.repr u i≠0 := by
    by_contra! no
    apply ne
    apply b.repr.injective
    apply Finsupp.ext
    intro j
    simpa using no j
  let N:=(b.repr u i).natDegree
  have power (n:ℕ) : u^(n+1)=u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,ih,←pow_two,id]
  have divides : (Polynomial.X-C a)^(N+1)∣b.repr u i := by
    refine ⟨b.repr (w^(N+1)) i,?_⟩
    have rel : u=(Polynomial.X-C a)^(N+1) • w^(N+1) := by
      calc u = u^(N+1) := (power N).symm
           _ = (algebraMap (Polynomial k) S (Polynomial.X-C a)*w)^(N+1) := congrArg (·^(N+1)) eq
           _ = _ := by rw [mul_pow,←map_pow,Algebra.smul_def]
    exact congrArg (fun p=>p i) ((congrArg b.repr rel).trans (b.repr.map_smul ..))
  have bound:=natDegree_le_of_dvd divides hi
  rw [natDegree_pow,natDegree_X_sub_C,mul_one] at bound
  omega
theorem detects_global [IsReduced S] [Module.Free (Polynomial k) S]
    (a : k) (u:S) (alg : IsIntegral k u) (vanish : algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : u=0 := by
  classical
  by_contra ne
  let B:=Algebra.adjoin k ({u}:Set S)
  let : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral alg
  let : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let x : B:= ⟨u,Algebra.self_mem_adjoin_singleton k u⟩
  have nn : ¬IsNilpotent x := by
    intro nil
    exact ne (nil.map B.val.toRingHom).eq_zero
  obtain ⟨r,id,nz⟩:=Lower6960.TraceSpecialization.idempotent_multiple x nn
  have idem : (u*(r:S))^2=u*(r:S) := congrArg Subtype.val id
  have nonzero : u*(r:S)≠0 := fun eq=>nz (Subtype.ext eq)
  exact idempotent_survives idem nonzero a (vanish.trans (dvd_mul_right ..))
#print axioms detects_global
omit [Algebra k S] in
theorem reduced_of_point [Module.Free (Polynomial k) S] {D : Type*} [CommRing D] [IsReduced D]
    (a : k) (atNode : S→+*D)
    (kernel : ∀ u, atNode u=0 → algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : IsReduced S := by
  classical
  constructor
  intro u nil
  let p : (Polynomial k):=Polynomial.X-C a
  have pn : p≠0 := X_sub_C_ne_zero _
  have div (n:ℕ) : ∃ w:S, IsNilpotent w ∧ u=p^n • w := by
    induction n with
    | zero => exact ⟨u,nil,by simp⟩
    | succ n ih =>
      obtain ⟨w,nw,eq⟩:=ih
      obtain ⟨v,rel⟩:=kernel w (nw.map atNode).eq_zero
      obtain ⟨m,hm⟩:=nw
      have van : p^m • v^m=0 := by
        rw [rel,mul_pow] at hm
        rw [Algebra.smul_def,map_pow]; exact hm
      refine ⟨v,⟨m,(smul_eq_zero_iff_right (pow_ne_zero _ pn)).mp van⟩,?_⟩
      rw [eq,rel,pow_succ,mul_smul,Algebra.smul_def p v]
  let b:=Module.Free.chooseBasis (Polynomial k) S
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  by_contra ne
  have nz : b.repr u i≠0 := by simpa using ne
  let n:=(b.repr u i).natDegree
  obtain ⟨v,_,eq⟩:=div (n+1)
  have large : p^(n+1)∣b.repr u i :=
    ⟨b.repr v i,congrArg (fun q=>q i) ((congrArg b.repr eq).trans (b.repr.map_smul ..))⟩
  have bad:=natDegree_le_of_dvd large nz
  rw [natDegree_pow,show p.natDegree=1 from natDegree_X_sub_C _,mul_one] at bad
  omega
#print axioms reduced_of_point
end Lower6960.RetainedLineEvaluation

end
end Merged_R6960RetainedLineEvaluation

-- merged module R6960RetainedAxisPoint
section Merged_R6960RetainedAxisPoint
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus MonicChartProbes
open Module Submodule Algebra Polynomial
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (toCross toCross_kernel finiteX_val finiteZ_val)
open Lower6960.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]

def atCoord (j:Bool) (x z:L) := if j then z else x
def nodeMap (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₗ[L] Crossing E x z :=
  match j with | false=>crossingX E x z | true=>crossingZ E x z
theorem through (j:Bool) (x z:L) (v:Tor E) :
    nodeMap E j x z (red E j (atCoord j x z) v)=Ideal.Quotient.mk _ v := by cases j <;> rfl

theorem onto_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) :
    Function.Surjective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false).subtype) := by
  intro w
  obtain ⟨u,hu⟩ := cross_surjective E x z nx nz w
  have s : reference j false=(false,false) := by cases j <;> rfl
  refine ⟨⟨red E j (atCoord j x z) (fromFinite E u),⟨fromFinite E u,?_,rfl⟩⟩,?_⟩
  · change IsIntegral (baseChart (reference j false)) u.val
    rw [s]; exact u.property
  · exact (through E j x z (fromFinite E u)).trans hu

theorem cut_running (j:Bool) (c:L) :
    along E j false (Polynomial.X-C c)=cut E (!j) c := by
  apply Subtype.ext
  rw [map_sub]
  change ((along E j false Polynomial.X):E)-((along E j false (C c)):E)=_
  rw [show along E j false Polynomial.X=
    (⟨algebraMap ChartField E (coordinate (!j)),isIntegral_algebraMap (x:=(⟨_,torus_coordinate (!j) false⟩:torus))⟩:Tor E)
    from eval₂_X _ _,show along E j false (C c)=algebraMap L (Tor E) c from eval₂_C _ _]
  exact (map_sub (algebraMap ChartField E) _ _).symm

private theorem coordinate_ideal (x z:L) (nx:x≠0) (nz:z≠0) (u:finiteOrder E)
    (zero : Lower6960.RetainedSurfaceClass.toCross E x z u=0) :
    ∃ a b:finiteOrder E, fromFinite E u=cut E false x*fromFinite E a+cut E true z*fromFinite E b := by
  have mem : u∈RingHom.ker (Lower6960.RetainedSurfaceClass.toCross E x z).toRingHom := RingHom.mem_ker.mpr zero
  rw [Lower6960.RetainedSurfaceClass.toCross_kernel E x z nx nz,point_kernel,Ideal.map_sup,
    Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton] at mem
  obtain ⟨_,hu,_,hv,eq⟩:=Submodule.mem_sup.mp mem
  obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp hv
  have fx : fromFinite E (algebraMap Base (finiteOrder E) (finiteX x))=cut E false x :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteX_val x))
  have fz : fromFinite E (algebraMap Base (finiteOrder E) (finiteZ z))=cut E true z :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteZ_val z))
  exact ⟨a,b,by rw [←eq,map_add,map_mul,map_mul,fx,fz]⟩

/-- The kernel of evaluation on the actual finite line chart consists of multiples
of its crossing coordinate. This identifies the point fibre even at the two chart boundaries. -/
theorem kernel_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:chartImage E j (atCoord j x z) false) :
    nodeMap E j x z u=0 ↔ ∃ v:chartImage E j (atCoord j x z) false,
      (u:Axis E j (atCoord j x z))=polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z))*v.val := by
  let R:=axisIdeal E j (atCoord j x z)
  let π:=Ideal.Quotient.mk R
  have fixed : π (cut E j (atCoord j x z))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have variableCut : polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z)) =
      π (cut E (!j) (atCoord (!j) x z)) := congrArg π (cut_running E j _)
  have origin : reference j false=(false,false) := by cases j <;> rfl
  have image (y : finiteOrder E) : π (fromFinite E y)∈chartImage E j (atCoord j x z) false := by
    refine ⟨fromFinite E y,?_,rfl⟩
    change IsIntegral (baseChart (reference j false)) y.val; rw [origin]; exact y.property
  constructor
  · intro hz
    obtain ⟨w,hw,ew⟩:=u.property
    change IsIntegral (baseChart (reference j false)) (w:E) at hw
    rw [origin] at hw
    let W:finiteOrder E:=⟨w,hw⟩
    have fw : fromFinite E W=w := rfl
    rw [←ew,through] at hz
    have zero : Lower6960.RetainedSurfaceClass.toCross E x z W=0 := hz
    obtain ⟨a,b,eq⟩:=coordinate_ideal E x z nx nz W zero
    have ed:=congrArg π eq
    rw [map_add,map_mul,map_mul,fw] at ed
    change π w=u.val at ew
    rw [ew] at ed
    cases j
    · refine ⟨⟨_,image b⟩,?_⟩
      change π (cut E false x)=0 at fixed
      rw [fixed,zero_mul,zero_add] at ed
      rw [variableCut]; exact ed
    · refine ⟨⟨_,image a⟩,?_⟩
      change π (cut E true z)=0 at fixed
      rw [fixed,zero_mul,add_zero] at ed
      rw [variableCut]; exact ed
  · rintro ⟨v,hv⟩
    obtain ⟨w,_,ew⟩:=v.property
    rw [hv,variableCut,←ew]
    change nodeMap E j x z (π (cut E (!j) (atCoord (!j) x z))*π w)=0
    rw [←map_mul]
    change nodeMap E j x z (red E j (atCoord j x z) _)=0
    rw [through E j x z, map_mul]
    have member : cut E (!j) (atCoord (!j) x z)∈axisIdeal E false x⊔axisIdeal E true z := by
      cases j
      · exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
      · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr member,zero_mul]

#print axioms onto_at_node
#print axioms kernel_at_node
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisPoint

-- merged module R6960RetainedNativeEuler
section Merged_R6960RetainedNativeEuler
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open RetainedRestrictionTorus Module Submodule LinearMap LineEuler Polynomial
open scoped Lower6960.RetainedSurfaceClass Polynomial
variable (E:Type) [Field E] [Algebra ChartField E]

abbrev LineGlobals (j:Bool) (c:L) := ↥(chartImage E j c false⊓chartImage E j c true)
abbrev LineObstructions (j:Bool) (c:L) := (Axis E j c) ⧸ (chartImage E j c false⊔chartImage E j c true)

theorem native_frames [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (j:Bool) (c:L) (nc:c≠0) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c false)) ∧
      Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c true)) := by
  have fin (b:Bool) : Module.Finite (Polynomial L) (chartImage E j c b) := chart_finite E j c b
  have free (b:Bool) : Module.Free (Polynomial L) (chartImage E j c b) := chart_free E j c b
  let bf:=Module.finBasis (Polynomial L) (chartImage E j c false)
  let bi:=Module.finBasis (Polynomial L) (chartImage E j c true)
  let U:=localFreeBasis false bf (nativeMap E j c false) (native_localization E j c nc false)
  let V:=localFreeBasis true bi (nativeMap E j c true) (native_localization E j c nc true)
  have same : finrank (Polynomial L) (chartImage E j c true)=finrank (Polynomial L) (chartImage E j c false) := by
    simpa only [Fintype.card_fin] using (finrank_eq_card_basis V).symm.trans (finrank_eq_card_basis U)
  exact ⟨_,⟨bf⟩,⟨Module.finBasisOfFinrankEq (Polynomial L) _ same⟩⟩

/-- Euler's formula on the actual specialized surface order. The determinant is
computed from its finite and infinity bases, even if the fibre is a proper suborder. -/
theorem native_euler (j:Bool) (c:L) (nc:c≠0) {n : ℕ}
    (bf : Basis (Fin n) (Polynomial L) (chartImage E j c false))
    (bi : Basis (Fin n) (Polynomial L) (chartImage E j c true)) :
    let G:=freeTransition bf bi (nativeMap E j c false) (nativeMap E j c true)
      (native_localization E j c nc false) (native_localization E j c nc true)
    FiniteDimensional L (LineGlobals E j c) ∧ FiniteDimensional L (LineObstructions E j c) ∧
      ∃ d:ℤ,G.det.degree=(d:WithBot ℤ) ∧
        (finrank L (LineGlobals E j c):ℤ)-(finrank L (LineObstructions E j c):ℤ)=n+d := by
  let U:=chartImage E j c false
  let V:=chartImage E j c true
  let ff:=nativeMap E j c false
  let fi:=nativeMap E j c true
  let lf:=native_localization E j c nc false
  let li:=native_localization E j c nc true
  let G:=freeTransition bf bi ff fi lf li
  let tower:=laurent_scalar_tower E j c
  let e:Axis E j c≃ₗ[L](Fin n→Laurent L) := (localFreeBasis false bf ff lf).equivFun.restrictScalars L
  have h0 : (U⊓V).map e.toLinearMap=finiteLattice L (Fin n) ⊓ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]
    change (v∈U ∧ v∈V) ↔ _
    apply Iff.trans _ (free_global_iff bf bi ff fi lf li v).symm
    exact and_congr ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
      ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
  have h1 : (U⊔V).map e.toLinearMap=finiteLattice L (Fin n) ⊔ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply,Submodule.mem_sup]
    apply Iff.trans _ (free_boundary_iff bf bi ff fi lf li v).symm
    exact ⟨fun ⟨u,hu,w,hw,s⟩=>⟨⟨u,hu⟩,⟨w,hw⟩,s⟩,fun ⟨u,w,s⟩=>⟨u,u.property,w,w.property,s⟩⟩
  let E0 : LineGlobals E j c≃ₗ[L]H0 G := (e.submoduleMap (U⊓V)).trans (LinearEquiv.ofEq _ _ h0)
  let E1 : LineObstructions E j c≃ₗ[L]H1 G := Submodule.Quotient.equiv _ _ e h1
  have good : IsUnit G := freeTransition_unit (M:=Axis E j c) bf bi ff fi lf li
  obtain ⟨f0,f1,d,ed,index⟩:=euler_index G good
  refine ⟨FiniteDimensional.of_injective E0.toLinearMap E0.injective,
    FiniteDimensional.of_injective E1.toLinearMap E1.injective,d,ed,?_⟩
  rw [E0.finrank_eq,E1.finrank_eq]
  simpa only [Fintype.card_fin] using index

#print axioms native_frames
#print axioms native_euler
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedNativeEuler

-- merged module R6960RetainedGlobalEvaluation
section Merged_R6960RetainedGlobalEvaluation
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus
open Module Submodule LinearMap Algebra Polynomial LineEuler
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (chartSpace)
variable (E:Type) [Field E] [Algebra ChartField E]

def imageAlg (j:Bool) (c:L) (b:Bool) : Subalgebra L (Axis E j c) where
  carrier:=(chartImage E j c b : Set _)
  zero_mem':=(chartImage E j c b).zero_mem
  add_mem':=(chartImage E j c b).add_mem
  one_mem':=by
    change (1:Axis E j c)∈chartImage E j c b
    exact ⟨1,isIntegral_one,map_one (Ideal.Quotient.mk _)⟩
  mul_mem':=by
    rintro _ _ ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u*v,IsIntegral.mul hu hv,map_mul (Ideal.Quotient.mk _) _ _⟩
  algebraMap_mem' r:=by
    change algebraMap L (Axis E j c) r∈chartImage E j c b
    exact ⟨algebraMap L (Tor E) r,
      isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant _ r⟩:baseChart (reference j b))),rfl⟩

def imagePoly (j:Bool) (c:L) (b:Bool) : (Polynomial L)→+*imageAlg E j c b :=
  (polyMap E j c b).codRestrict (imageAlg E j c b) (fun p=>by
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    have h:1∈polyImage E j c b := (imageAlg E j c b).one_mem
    have v:=(polyImage E j c b).smul_mem p h
    change polyMap E j c b p * 1∈_ at v
    rw [mul_one] at v
    exact v)
scoped instance imagePolyAlgebra (j:Bool) (c:L) (b:Bool) :
    Algebra (Polynomial L) (imageAlg E j c b) :=
  RingHom.toAlgebra' (R:=(Polynomial L)) (S:=imageAlg E j c b) (imagePoly E j c b)
    (fun r x => mul_comm (imagePoly E j c b r) x)

private def ringBasis (j:Bool) (c:L) (b:Bool) {n:ℕ}
    (B : Basis (Fin n) (Polynomial L) (chartImage E j c b)) : Basis (Fin n) (Polynomial L) (imageAlg E j c b) :=
  let e : chartImage E j c b≃ₗ[(Polynomial L)]imageAlg E j c b :=
   { toFun:=fun v=>⟨v,v.property⟩
     invFun:=fun v=>⟨v,v.property⟩
     left_inv:=fun _=>rfl
     right_inv:=fun _=>rfl
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
  B.map e

def nodeRing (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₐ[L] Crossing E x z :=
  match j with
  | false=>Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ _⊔axisIdeal E true z from le_sup_left)
  | true=>Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x⊔_ from le_sup_right)

theorem eval_subtype (j:Bool) (x z:L) (u:chartImage E j (atCoord j x z) false) :
    nodeRing E j x z u.val=nodeMap E j x z u.val := by cases j <;> rfl

theorem vanishing_divides (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:imageAlg E j (atCoord j x z) false) (h:nodeRing E j x z u.val=0) :
    algebraMap (Polynomial L) (imageAlg E j (atCoord j x z) false) (Polynomial.X-C (atCoord (!j) x z)) ∣ u := by
  let w : chartImage E j (atCoord j x z) false:=⟨u.val,u.property⟩
  obtain ⟨v,eq⟩:=(kernel_at_node E j x z nx nz w).mp ((eval_subtype E j x z w) ▸ h)
  exact ⟨⟨v.val,v.property⟩,Subtype.ext eq⟩

/-- Global sections form a finite algebra. On the actual affine chart, their
evaluation is injective even if the selected fibre has several components. -/
theorem global_eval_injective (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)]
    [FiniteDimensional L (LineGlobals E j (atCoord j x z))] {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    Function.Injective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false⊓
      chartImage E j (atCoord j x z) true).subtype) := by
  let c:=atCoord j x z
  let R:=imageAlg E j c false
  let U:=imageAlg E j c false⊓imageAlg E j c true
  let e : U≃ₗ[L]LineGlobals E j c :=
    { toFun:=fun v=>⟨v,v.property⟩,invFun:=fun v=>⟨v,v.property⟩
      left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  have : FiniteDimensional L U := FiniteDimensional.of_injective e.toLinearMap e.injective
  let into : U→ₐ[L] R:=Subalgebra.inclusion inf_le_left
  let evaluate:= (nodeRing E j x z).toRingHom.comp R.subtype
  have free : Module.Free (Polynomial L) R := Module.Free.of_basis (ringBasis E j c false bf)
  have redRing : IsReduced R := RetainedLineEvaluation.reduced_of_point (S:=R) (D:=Crossing E x z)
    (atCoord (!j) x z) evaluate (vanishing_divides E j x z nx nz)
  intro u v eq
  let d:=e.symm (u-v)
  have alg : IsIntegral L (into d) := (Algebra.IsIntegral.isIntegral d).map into
  have van : evaluate (into d)=0 := by
    change nodeRing E j x z (u.val-v.val)=0
    rw [map_sub,sub_eq_zero]
    cases j <;> exact eq
  have zero:=RetainedLineEvaluation.detects_global (atCoord (!j) x z) (into d) alg
    (vanishing_divides E j x z nx nz _ van)
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact congrArg (fun w : R=>(w:Axis E j c)) zero

#print axioms global_eval_injective
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedGlobalEvaluation

end Merged6967_R6960RetainedGlobalEvaluation
