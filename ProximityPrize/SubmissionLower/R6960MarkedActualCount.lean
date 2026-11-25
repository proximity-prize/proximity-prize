import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisIndex
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6960RetainedCompressionProjection
import ProximityPrize.SubmissionLower.R6960MarkedNativeNorm
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960CollisionMarkedAxisFamily

set_option Elab.async false

-- merged module R6960CollisionMarkedGlobalSum
section Merged_R6960CollisionMarkedGlobalSum
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial LaurentPolynomial CollisionTame Finset
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
  have sep := BranchCollisions.tame_separable p (branch_squarefree D) small
  apply branch_index_of_discriminant D nD sep U good idx support ?_ xD zD
  intro z hz
  have eq : δ.eval (Polynomial.C z)=D.map (evalRingHom z) := by
    simpa only [D,Bivariate.swap_swap_apply] using RetainedCompression.eval_swap D z
  exact eq ▸ square z hz
#print axioms plane_degree_from_line_transition
#print axioms native_index_sum
end
end Lower6960.CollisionMarked

end Merged_R6960CollisionMarkedGlobalSum

-- merged module R6960MarkedActualCount
section Merged_R6960MarkedActualCount
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open CollisionMarked NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass
open RetainedTwistedRestriction Polynomial Finset Algebra Module Submodule
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
open Lower6960.RetainedSurfaceClass (finite_along)
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
local notation "aE" => algebraMap ChartField E

/-- Count the original word fibres with the independently measured chart
deficits. All finite collision losses, marked residues, and evaluation rows
are produced from this same original polynomial. -/
theorem actual_good_count (p:ℕ) [CharP L p] [CharP Scalar p] [DecidableEq L]
    (P:CurvatureSquares.Ordinate) (pn:projectedRaw P≠0) (lo:2≤P.natDegree) (hi:P.natDegree<p)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root:let : Algebra (Plane L) E := axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (s t:ℕ) (positive:0<s) (tame:2*s<p) (surface:Budget E (s-1) (s+s*t))
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:axisDiscriminant (E:=E) false=Ideal.span {δf}) (di:axisDiscriminant (E:=E) true=Ideal.span {δi})
    (xc:CurvatureSquares.height δf≤2*s) (zc:δf.natDegree≤2*t)
    (U:Finset L) (nz:∀z∈U,z≠0) (words:L → Polynomial L) (mark:∀z∈U,RetainedCompression.MarkedFiber P z (words z))
    (boundary:∀z∈U,(Bivariate.swap δi).trailingCoeff.eval z≠0)
    (vertical:∀(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j))→
      finrank Scalar (span Scalar (Set.range v))+s≤P.natDegree*s) :
    U.card≤9*P.natDegree*t+P.natDegree*(P.natDegree-1) := by
  classical
  let ord:=axisScaledOrdinate P pn b.gen root
  let word (z:L):Tor E:=axisScaledWord P z (words z)
  have one (z:U):=(actual_axis_marked_family (E:=E) p P pn lo hi b dim root z.val (nz _ z.property) (words z)
    (mark _ z.property) (s-1) δf δi nf ni df di (boundary _ z.property))
  choose good d dn square support v indep reg kills using one
  let index (z:L):(Polynomial L):=if hz:z∈U then d ⟨z,hz⟩ else 1
  have sum:=native_index_sum p δf nf s t xc zc tame U index (fun z hz=>good ⟨z,hz⟩)
    (fun z hz=>by rw [show index z=d ⟨z,hz⟩ from dif_pos hz];exact support ⟨z,hz⟩)
    (fun z hz=>by rw [show index z=d ⟨z,hz⟩ from dif_pos hz];exact square ⟨z,hz⟩)
  let J (z:U):=Fin (s-1+1-(d z).natDegree)
  obtain ⟨m,f,li,columns,lifts⟩:=family_from_fibres (E:=E) (s-1) (s+s*t) surface U nz J v reg indep ord word kills
  let raw:=projectedRaw P
  let a:=planeFinite raw.leadingCoeff
  have scale : (ord:E)=aE a*b.gen := rfl
  have aa : Function.Injective planeFinite:=Subtype.val_injective.comp (oriented true false).injective
  have an : a≠0 := (map_ne_zero_iff _ aa).mpr (leadingCoeff_ne_zero.mpr pn)
  have rr : raw.eval₂ ((algebraMap ChartField E).comp planeFinite) b.gen=0 := root
  have scaledRoot : raw.integralNormalization.eval₂ ((algebraMap ChartField E).comp planeFinite) (ord:E)=0 := by
    let j:Plane L→+*E:=(algebraMap ChartField E).comp planeFinite
    letI := j.toAlgebra
    exact integralNormalization_aeval_eq_zero (z:=b.gen) (show aeval b.gen raw=0 from rr)
      (fun a h=>((algebraMap ChartField E).injective.comp aa) (h.trans (map_zero j).symm))
  have wordBase (z:L) (_:z∈U):∃w:ChartField,(word z:E)=aE w := by
    let w:=raw.leadingCoeff.eval (C z)*words z
    refine ⟨planeFinite (C w),?_⟩
    have eq:=Lower6960.RetainedSurfaceClass.finite_along E true false w
    exact congrArg (fun v:Tor E=>(v:E)) eq.symm
  obtain ⟨r,poles,rank,dimBound,orbit⟩:=native_norm f li (s-1) U nz ord word columns b
    (Algebra.IsSeparable.isSeparable ChartField b.gen) a an scale raw.integralNormalization scaledRoot
    (fun z hz=>normalized_fibre_separable z P _ p (by omega) hi (mark z hz)) wordBase
  have rle := vertical m f (fun j=>(columns j).1)
  rw [←rank] at rle
  let loss:=∑z∈U,(index z).natDegree
  have localSize :
      U.card*s≤loss+∑z:U,Fintype.card (J z) := by
    rw [show U.card*s=∑z:U,s from (by simp)]
    have together := Finset.sum_le_sum (s:=Finset.univ) (fun (z:U) _=>
      show s≤(index z.val).natDegree+Fintype.card (J z) from by
        rw [show index z.val=d z from dif_pos z.property]
        change s≤(d z).natDegree+Fintype.card (Fin (s-1+1-(d z).natDegree))
        rw [Fintype.card_fin];omega)
    rw [Finset.sum_add_distrib] at together
    have matched : ∑ z:U,(index z.val).natDegree=loss := by
      change ∑ z∈U.attach,(index z.val).natDegree=_
      exact Finset.sum_attach U (fun a=>(index a).natDegree)
    rwa [matched] at together
  rw [dim] at orbit
  rw [Fintype.card_fin] at dimBound
  apply price (loss:=loss) (obstructions:=s+s*t) (ordinary:=s) (meromorphic:=m) (rank:=r) (pole:=poles)
    positive (by omega) rle sum le_rfl le_rfl _ dimBound orbit
  omega

#print axioms actual_good_count
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedActualCount
