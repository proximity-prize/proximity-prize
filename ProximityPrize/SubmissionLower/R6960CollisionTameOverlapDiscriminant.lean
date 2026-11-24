import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapUnit
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminantLocalization

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial LaurentPolynomial
open scoped Polynomial

variable (k : Type) [Field k]

abbrev OverlapPlane := (Polynomial (Polynomial k))
abbrev OverlapLaurent := LaurentPolynomial (Polynomial k)

/-- The finite and reciprocal abscissa charts of the overlap, holding the
scalar chart fixed. -/
def overlapChart (s : Bool) : OverlapPlane k→+*OverlapLaurent k :=
  if s then invert.toRingEquiv.toRingHom.comp Polynomial.toLaurent else Polynomial.toLaurent

theorem overlapChart_localizes (s : Bool) :
    let : Algebra (OverlapPlane k) (OverlapLaurent k) := (overlapChart k s).toAlgebra
    IsLocalization.Away (Polynomial.X : OverlapPlane k) (OverlapLaurent k) := by
  let A := OverlapPlane k
  let L := OverlapLaurent k
  let : Algebra A L := (overlapChart k s).toAlgebra
  have inj : Function.Injective (overlapChart k s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact invert.injective.comp Polynomial.toLaurent_injective
  apply IsLocalization.Away.mk (Polynomial.X : A)
  · have image : overlapChart k s (Polynomial.X:A)=T (if s then -1 else 1) := by
      cases s <;> simp [overlapChart,Polynomial.toLaurent_X]
    change IsUnit (overlapChart k s (Polynomial.X:A))
    rw [image]
    exact isUnit_T _
  · intro u
    cases s with
    | false =>
      obtain ⟨n,p,eq⟩ := LaurentPolynomial.exists_T_pow u
      refine ⟨n,p,?_⟩
      change u*(overlapChart k false (Polynomial.X:A))^n=overlapChart k false p
      rw [←map_pow]
      change u*(Polynomial.X^n:A).toLaurent=p.toLaurent
      simpa only [Polynomial.toLaurent_X_pow] using eq.symm
    | true =>
      obtain ⟨n,p,eq⟩ := LaurentPolynomial.exists_T_pow (invert u)
      refine ⟨n,p,?_⟩
      change u*(overlapChart k true (Polynomial.X:A))^n=overlapChart k true p
      rw [←map_pow]
      change u*invert (Polynomial.X^n:A).toLaurent=invert p.toLaurent
      have h := congrArg (invert (R:=(Polynomial k))) eq
      rw [map_mul,involutive_invert u,invert_T] at h
      simpa only [Polynomial.toLaurent_X_pow,invert_T] using h.symm
  · intro a b eq
    exact ⟨0,by rw [inj eq]⟩

variable (F E : Type*) [Field F] [Field E]
  [IsDomain (OverlapLaurent k)] [IsIntegrallyClosed (OverlapLaurent k)] [IsNoetherianRing (OverlapLaurent k)]
  [Algebra (OverlapLaurent k) F] [IsFractionRing (OverlapLaurent k) F]
  [Algebra (OverlapLaurent k) E] [Algebra F E] [IsScalarTower (OverlapLaurent k) F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

omit [Field E] [Algebra (OverlapLaurent k) E] [Algebra F E]
  [IsScalarTower (OverlapLaurent k) F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [IsDomain (OverlapLaurent k)] [IsIntegrallyClosed (OverlapLaurent k)] [IsNoetherianRing (OverlapLaurent k)] in
theorem overlapChart_fraction (s : Bool) :
    let : Algebra (OverlapPlane k) F := ((algebraMap (OverlapLaurent k) F).comp (overlapChart k s)).toAlgebra
    IsFractionRing (OverlapPlane k) F := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  have injR : Function.Injective (overlapChart k s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact invert.injective.comp Polynomial.toLaurent_injective
  have inj : Function.Injective (algebraMap A F) := (IsFractionRing.injective R F).comp injR
  let : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective _ _).mpr inj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨r,u,_,ratio⟩ := IsFractionRing.div_surjective R z
  obtain ⟨n,a,ra⟩ := IsLocalization.Away.surj (Polynomial.X:A) r
  obtain ⟨m,b,ub⟩ := IsLocalization.Away.surj (Polynomial.X:A) u
  let j := algebraMap A R
  let h := algebraMap R F
  let t := j (Polynomial.X:A)
  have tn : h t≠0 := (map_ne_zero_iff _ inj).mpr X_ne_zero
  change r*t^n=j a at ra
  change u*t^m=j b at ub
  have ra' : algebraMap A F (a*Polynomial.X^m)=h r*(h t)^(n+m) := by
    change h (j (a*Polynomial.X^m))=h r*(h t)^(n+m)
    rw [map_mul j,map_pow j]
    change h (j a*t^m)=_
    rw [←ra,map_mul h,map_mul h,map_pow h,map_pow h,mul_assoc,←pow_add]
  have ub' : algebraMap A F (b*Polynomial.X^n)=h u*(h t)^(n+m) := by
    change h (j (b*Polynomial.X^n))=h u*(h t)^(n+m)
    rw [map_mul j,map_pow j]
    change h (j b*t^n)=_
    rw [←ub,map_mul h,map_mul h,map_pow h,map_pow h,mul_assoc,←pow_add,Nat.add_comm m n]
  refine ⟨a*Polynomial.X^m,b*Polynomial.X^n,?_⟩
  rw [ra',ub',mul_div_mul_right _ _ (pow_ne_zero _ tn)]
  exact ratio.symm

/-- The actual discriminant ideal of either plane chart in the common
root field, with its own embedding of the abscissa. -/
def overlapChartDiscriminant (s : Bool) : Ideal (OverlapPlane k) := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=F) fun _=>rfl
  let : IsFractionRing A F := overlapChart_fraction k F s
  let : Algebra A E := ((algebraMap R E).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=F) (A:=E) fun a=>by
    change algebraMap R E (overlapChart k s a)=algebraMap F E (algebraMap R F (overlapChart k s a))
    exact IsScalarTower.algebraMap_apply R F E _
  exact normalizationDiscriminant (A:=A) (E:=E) F

theorem overlapChart_discriminant_map (s : Bool) :
    (overlapChartDiscriminant k F E s).map (overlapChart k s)=
      normalizationDiscriminant (A:=OverlapLaurent k) (E:=E) F := by
  let A := OverlapPlane k
  let R := OverlapLaurent k
  let : Algebra A R := (overlapChart k s).toAlgebra
  let : IsLocalization.Away (Polynomial.X:A) R := overlapChart_localizes k s
  let : Algebra A F := ((algebraMap R F).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=F) fun _=>rfl
  let : IsFractionRing A F := overlapChart_fraction k F s
  let : Algebra A E := ((algebraMap R E).comp (overlapChart k s)).toAlgebra
  let : IsScalarTower A R E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=R) (A:=E) fun _=>rfl
  let : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=F) (A:=E) fun a=>by
    change algebraMap R E (overlapChart k s a)=algebraMap F E (algebraMap R F (overlapChart k s a))
    exact IsScalarTower.algebraMap_apply R F E _
  exact normalizationDiscriminant_map (A:=A) (R:=R) (F:=F) (E:=E) (Submonoid.powers (Polynomial.X:A))

/-- Principal discriminants from the two actual normalization charts
compare by one scalar and one exponent on their common overlap. -/
theorem actual_overlap_unit (δfin δinf : OverlapPlane k)
    (f : overlapChartDiscriminant k F E false=Ideal.span {δfin})
    (i : overlapChartDiscriminant k F E true=Ideal.span {δinf}) :
    ∃ (c : k) (m : ℤ),c≠0 ∧
      δfin.toLaurent=LaurentPolynomial.C (Polynomial.C c)*T m*invert δinf.toLaurent := by
  have a := overlapChart_discriminant_map k F E false
  have b := overlapChart_discriminant_map k F E true
  rw [f,Ideal.map_span,Set.image_singleton] at a
  rw [i,Ideal.map_span,Set.image_singleton] at b
  exact plane_overlap_unit δfin δinf (a.trans b.symm)

#print axioms actual_overlap_unit
end
end Lower6960.CollisionTame
