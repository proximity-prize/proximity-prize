import ProximityPrize.SubmissionLower.R6960CollisionMarkedInfinitySeeds
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapUnit
import ProximityPrize.SubmissionLower.R6961RetainedCompressionProjection

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open Polynomial LaurentPolynomial Lower6960.CollisionTame Finset
open scoped Polynomial BigOperators

private theorem overlap_degree_one {R:Type} [CommRing R] [IsDomain R]
    (δf δi:(Polynomial R)) (nf:δf≠0) (c:R) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C c*T m*invert δi.toLaurent) :
    (δf.natDegree:ℤ)≤m := by
  let n : ℤ := δf.natDegree
  have left : δf.toLaurent.coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nf,rfl⟩)
  by_contra! bad
  change m<n at bad
  have right : δi.toLaurent.coeff (-(n-m))=0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [support_coeff_toLaurent]
    intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp h
    change (j:ℤ)=-(n-m) at hj
    omega
  have eq := congrArg (fun f:LaurentPolynomial R=>f.coeff n) overlap
  rw [←single_eq_C_mul_T,AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (n-m) (by intro v _; omega),
    invert_apply,right,mul_zero] at eq
  exact left eq

/-- An actual common overlap unit bounds the ordinary degrees of both
principal chart generators. Degree can drop under specialization, so the
bound is applied to the original polynomial plane. -/
theorem plane_overlap_degree_caps {k:Type} [Field k]
    (δf δi:(Polynomial (Polynomial k))) (nf:δf≠0) (c:k) (cn:c≠0) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δi.toLaurent) :
    (δf.natDegree:ℤ)≤m ∧ (δi.natDegree:ℤ)≤m := by
  refine ⟨overlap_degree_one δf δi nf (C c) m overlap,?_⟩
  have ni : δi≠0 := by
    rintro rfl
    apply nf
    exact Polynomial.toLaurent_injective (by simpa only [map_zero,mul_zero] using overlap)
  have moved := congrArg (invert (R:=(Polynomial k))) overlap
  rw [map_mul,map_mul,invert_C,invert_T,involutive_invert] at moved
  have mirror : δi.toLaurent=LaurentPolynomial.C (Polynomial.C c⁻¹)*T m*invert δf.toLaurent := by
    rw [moved]
    calc _ = (LaurentPolynomial.C (Polynomial.C c⁻¹) * LaurentPolynomial.C (Polynomial.C c)) *
              (T m * T (-m)) * δi.toLaurent := by
                 rw [←map_mul,←map_mul,inv_mul_cancel₀ cn,map_one,map_one,←T_add,add_neg_cancel,T_zero,one_mul,one_mul]
         _ = _ := by ring
  exact overlap_degree_one δi δf ni (C c⁻¹) m mirror

/-- The exact measured line transition supplies the exponent of the plane
discriminant overlap. This bounds both original chart degrees by twice
the measured determinant deficit. -/
theorem plane_degree_from_line_transition {k:Type} [Field k]
    (δf δi:(Polynomial (Polynomial k))) (nf:δf≠0) (c:k) (cn:c≠0) (m:ℤ)
    (overlap:δf.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δi.toLaurent)
    (z:k) (good:δf.map (evalRingHom z)≠0)
    (df di:(Polynomial k)) (af:Associated df (δf.map (evalRingHom z))) (ai:Associated di (δi.map (evalRingHom z)))
    (G:LaurentPolynomial k) (unit:IsUnit G) (trace:invert di.toLaurent=G^2*df.toLaurent)
    (s:ℕ) (measure:G.degree=((-(s:ℤ):ℤ):WithBot ℤ)) :
    δf.natDegree≤2*s ∧ δi.natDegree≤2*s := by
  obtain ⟨d,gdeg,exponent⟩ := overlap_transition_exponent δf δi c cn m overlap
    (evalRingHom z) good df di af ai G unit trace
  have d_eq := WithBot.coe_injective (gdeg.symm.trans measure)
  obtain ⟨f,i⟩ := plane_overlap_degree_caps δf δi nf c cn m overlap
  omega

/-- The actual affine determinant indices across the marked seeds obey
the weighted collision budget. Generic branch separability follows from
the measured abscissa cap below the characteristic. -/
theorem native_index_sum {k:Type} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p:ℕ) [CharP (FractionRing (Polynomial k)) p]
    (δ:(Polynomial (Polynomial k))) (nz:δ≠0) (s t:ℕ)
    (xc:CurvatureSquares.height δ≤2*s) (zc:δ.natDegree≤2*t) (tame:2*s<p)
    (U:Finset k) (idx:k→(Polynomial k))
    (good:∀z∈U,(branchProduct (Bivariate.swap δ)).map (evalRingHom z)≠0)
    (support:∀z∈U,∀x∈(idx z).roots,
      2≤((branchProduct (Bivariate.swap δ)).map (evalRingHom z)).rootMultiplicity x)
    (square:∀ z∈U,(idx z)^2∣δ.eval (Polynomial.C z)) :
    (∑ z∈U,(idx z).natDegree)≤8*s*t := by
  let D := Bivariate.swap δ
  have nD : D≠0 := (map_ne_zero_iff Bivariate.swap.toRingHom Bivariate.swap.injective).mpr nz
  have xD : D.natDegree≤2*s := xc
  have zD : CurvatureSquares.height D≤2*t := by
    change (Bivariate.swap (Bivariate.swap δ)).natDegree≤2*t
    rwa [Bivariate.swap_swap_apply]
  have small : (branchProduct D).natDegree<p :=
    (natDegree_le_of_dvd (branch_dvd D nD) nD).trans_lt (xD.trans_lt tame)
  have sep := Lower6960.BranchCollisions.tame_separable p (branch_squarefree D) small
  apply branch_index_of_discriminant D nD sep U good idx support ?_ xD zD
  intro z hz
  have eq : δ.eval (Polynomial.C z)=D.map (evalRingHom z) := by
    simpa only [D,Bivariate.swap_swap_apply] using RetainedCompression.eval_swap D z
  exact eq ▸ square z hz

#print axioms plane_degree_from_line_transition
#print axioms native_index_sum
end
end Lower6961.CollisionMarked
