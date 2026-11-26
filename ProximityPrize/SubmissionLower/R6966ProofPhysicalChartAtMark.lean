import ProximityPrize.SubmissionLower.R6966ProofRegularPhysicalChart

set_option Elab.async false

namespace Research6966.PhysicalChartAtMark
open Finset Polynomial
open K1_14 (L FX Seeds Jet)
open K1_14_1 (SeedPoly PoleData CRTLift poleProduct rawBlock crtPolynomial)
open K1_14_1_2 (RegularRing regularSeeds specialize includeGeneric includeGeneric_injective localLift map_localLift specialize_localLift)
open PhysicalPrimitiveCoeffs (R phys rawCoeff)
open K1_14_1_4 (centerBase evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev B:=K1_14_3.SeedField
abbrev AtSeeds (t:Fin 2→L) := (RegularRing t)[X]

instance (t:Fin 2→L) : IsDomain (RegularRing t) :=
  (includeGeneric_injective t).isDomain (includeGeneric t)

def embed (t:Fin 2→L) : R→+*AtSeeds t := mapRingHom (algebraMap SeedPoly (RegularRing t))
def liftGeneric (t:Fin 2→L) : AtSeeds t→+*K1_14_1.SeedField[X] := mapRingHom (includeGeneric t)
def atSeeds (t:Fin 2→L) : AtSeeds t→+*L[X] := mapRingHom (specialize t)
def H {h} (D:PoleData h) (t:Fin 2→L) : AtSeeds t := embed t (phys (poleProduct D))

theorem generic_comp (t:Fin 2→L) : (liftGeneric t).comp (embed t)=rawCoeff := by
  have base:(includeGeneric t).comp (algebraMap SeedPoly (RegularRing t))=algebraMap SeedPoly K1_14_1.SeedField :=
    IsLocalization.lift_comp _
  apply RingHom.ext
  intro P
  change (P.map _).map _=P.map _
  rw [Polynomial.map_map,base]

theorem actual_comp (t:Fin 2→L) : (atSeeds t).comp (embed t)=mapRingHom (MvPolynomial.eval t) := by
  have base:(specialize t).comp (algebraMap SeedPoly (RegularRing t))=MvPolynomial.eval t:=IsLocalization.lift_comp _
  apply RingHom.ext
  intro P
  change (P.map _).map _=P.map _
  rw [Polynomial.map_map,base]

theorem generic_H {h} (D:PoleData h) (t:Fin 2→L) : liftGeneric t (H D t)=rawBlock D := by
  rw [H,←RingHom.comp_apply,generic_comp]
  change ((poleProduct D).map MvPolynomial.C).map _=_
  rw [Polynomial.map_map];rfl

theorem actual_H {h} (D:PoleData h) (t:Fin 2→L) : atSeeds t (H D t)=poleProduct D := by
  rw [H,←RingHom.comp_apply,actual_comp]
  change ((poleProduct D).map MvPolynomial.C).map (MvPolynomial.eval t)=_
  have eq:(MvPolynomial.eval t).comp (MvPolynomial.C:L→+*SeedPoly)=RingHom.id L:=RingHom.ext (fun _=>MvPolynomial.eval_C _)
  rw [Polynomial.map_map,eq,Polynomial.map_id]

theorem Hnz {h} (D:PoleData h) (t:Fin 2→L) : H D t≠0 := by
  intro z
  have n:= (K1_14_1_4.rawBlock_monic D).ne_zero
  exact n ((generic_H D t).symm.trans (z ▸ map_zero _))

abbrev Chart {h} (D:PoleData h) (t:Fin 2→L) := Localization.Away (H D t)
def into {h} (D:PoleData h) (t:Fin 2→L) : R→+*Chart D t:=(algebraMap (AtSeeds t) (Chart D t)).comp (embed t)
def direct : R→+*B:=(algebraMap Seeds B).comp centerBase

theorem direct_eq : evalRaw.comp rawCoeff=direct := K1_14_1_4.evalRaw_generic
theorem direct_injective : Function.Injective direct :=
  (IsFractionRing.injective Seeds B).comp PadeRawField.center_injective

private theorem regular_H {h} (D:PoleData h) (t:Fin 2→L) :
    Submonoid.powers (H D t)≤nonZeroDivisors (AtSeeds t) := by
  intro x hx
  obtain ⟨n,rfl⟩:=hx
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (Hnz D t))

instance {h} (D:PoleData h) (t:Fin 2→L) : IsDomain (Chart D t) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Chart D t) (regular_H D t)

private def toBase (t:Fin 2→L) : AtSeeds t→+*B:=evalRaw.comp (liftGeneric t)
private theorem toBase_inj (t:Fin 2→L) : Function.Injective (toBase t) :=
  PadeRawField.eval_injective.comp (map_injective _ (includeGeneric_injective t))

def genericMap {h} (D:PoleData h) (t:Fin 2→L) : Chart D t→+*B :=
  IsLocalization.Away.lift (H D t) (g:=toBase t)
    (((map_ne_zero_iff _ (toBase_inj t)).mpr (Hnz D t)).isUnit)

theorem generic_atBase {h} (D:PoleData h) (t:Fin 2→L) (x:AtSeeds t) :
    genericMap D t (algebraMap _ _ x)=toBase t x := IsLocalization.Away.lift_eq _ _ _

theorem generic_atSource {h} (D:PoleData h) (t:Fin 2→L) :
    (genericMap D t).comp (into D t)=direct := by
  apply RingHom.ext
  intro x
  change genericMap D t (algebraMap _ _ (embed t x))=_
  rw [generic_atBase]
  exact (RingHom.congr_fun (congrArg (fun g=>evalRaw.comp g) (generic_comp t)) x).trans (RingHom.congr_fun direct_eq x)

theorem into_injective {h} (D:PoleData h) (t:Fin 2→L) : Function.Injective (into D t) := by
  intro x y id
  exact direct_injective ((RingHom.congr_fun (generic_atSource D t) x).symm.trans
    ((congrArg (genericMap D t) id).trans (RingHom.congr_fun (generic_atSource D t) y)))

theorem generic_injective {h} (D:PoleData h) (t:Fin 2→L) : Function.Injective (genericMap D t) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (H D t)) _).mpr
  intro x y
  rw [generic_atBase,generic_atBase,(toBase_inj t).eq_iff,
    (IsLocalization.injective (Chart D t) (regular_H D t)).eq_iff]

theorem into_clears {h} (D:PoleData h) (t:Fin 2→L) : GlobalPrimitive.Clears (into D t) :=
  GlobalPrimitive.clear_comp _ _ (GlobalPrimitive.lift_clear _ (GlobalPrimitive.clear_localization (regularSeeds t)))
    (GlobalPrimitive.clear_localization (Submonoid.powers (H D t)))

theorem generic_clears {h} (D:PoleData h) (t:Fin 2→L) : GlobalPrimitive.Clears (genericMap D t) := by
  have all:GlobalPrimitive.Clears direct:=GlobalPrimitive.clear_comp _ _ PhysicalPrimitiveCoeffs.native_clears
    (GlobalPrimitive.clear_localization (nonZeroDivisors Seeds))
  intro x
  obtain ⟨a,b,unit,id⟩:=all x
  refine ⟨into D t a,into D t b,?_,?_⟩
  · exact (RingHom.congr_fun (generic_atSource D t) b) ▸ unit
  · exact (RingHom.congr_fun (generic_atSource D t) a).trans
      (id.trans (congrArg (·*x) (RingHom.congr_fun (generic_atSource D t) b).symm))

/-- The same localized chart specializes at every regular code node. -/
def atNode {h} (D:PoleData h) (t:Fin 2→L) (x:L) (nx:(poleProduct D).eval x≠0) : Chart D t→+*L :=
  IsLocalization.Away.lift (H D t) (g:=(evalRingHom x).comp (atSeeds t)) (by
    change IsUnit ((atSeeds t (H D t)).eval x);rw [actual_H];exact nx.isUnit)

/-- It also specializes to the entire rational physical line of each mark. -/
def atLine {h} (D:PoleData h) (t:Fin 2→L) : Chart D t→+*FX :=
  IsLocalization.Away.lift (H D t) (g:=(algebraMap L[X] FX).comp (atSeeds t)) (by
    change IsUnit (algebraMap L[X] FX (atSeeds t (H D t)))
    rw [actual_H]
    exact ((map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr ((D.monic 0).mul (D.monic 1)).ne_zero).isUnit)

end
end Research6966.PhysicalChartAtMark
