import ProximityPrize.SubmissionLower.R6960TraceSpecialization
import ProximityPrize.SubmissionLower.R6960BranchIndex
import ProximityPrize.SubmissionLower.UpperBranch1

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

/-- The index costs at most the excess of the local discriminant order
over the residue corank of the trace pairing. This comparison uses only a
change of integral order and the induced algebra map on residue fibres. -/
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

/-- Along an irreducible branch component a matrix rank can only drop
under specialization. The nonzero minor is selected in the special fibre. -/
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

/-- At a transverse branch point, a generically maximal trace corank
implies that the change of order has unit determinant at that point. The
matrix over the divisor is compared first generically and then at the point. -/
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
