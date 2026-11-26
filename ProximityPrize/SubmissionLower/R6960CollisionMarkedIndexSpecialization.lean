import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import ProximityPrize.SubmissionLower.KoalaRectPoleBalance
import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreIndex
import Mathlib.LinearAlgebra.TensorProduct.Basis

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
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedIndexSpecialization
