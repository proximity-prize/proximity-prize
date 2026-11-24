import ProximityPrize.SubmissionLower.R6961MarkedNativeNorm
import ProximityPrize.SubmissionLower.R6961MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6961CollisionMarkedAxisFamily
import ProximityPrize.SubmissionLower.R6961CollisionMarkedGlobalSum
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6960.NormalizedFiber RetainedRestrictionTorus RetainedSurfaceClass
open RetainedTwistedRestriction Polynomial Finset Algebra Module Submodule
open scoped Polynomial BigOperators Lower6961.MarkedEvaluation Lower6961.RetainedSurfaceClass
open Lower6961.RetainedSurfaceClass (finite_along)
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
    have eq:=Lower6961.RetainedSurfaceClass.finite_along E true false w
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
end Lower6961.MarkedEvaluation
