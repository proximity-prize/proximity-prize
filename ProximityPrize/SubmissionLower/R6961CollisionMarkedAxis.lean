import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreBaseChange
import ProximityPrize.SubmissionLower.R6961RetainedTwistedRestriction
import ProximityPrize.SubmissionLower.R6961RetainedAxisTransition

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
open Lower6960.CollisionMarked
noncomputable section
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Lower6960.NormalizedFiber MonicFourChartDescent ChartOverlapTests RetainedRestrictionTorus
open RetainedSurfaceClass Polynomial
open scoped Polynomial Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6961.RetainedSurfaceClass Lower6961.MonicChartProbes
open Lower6961.RetainedSurfaceClass (oriented_var oriented_const finite_along embedBase)

variable {E : Type} [Field E] [Algebra ChartField E]

/-- Put the scalar parameter outside and the actual line coordinate
inside, using either abscissa orientation. -/
@[instance_reducible] def linePlaneAlgebra (j b : Bool) : Algebra (Plane L) E :=
  ((algebraMap (baseChart (reference j b)) E).comp (oriented j b).toRingHom).toAlgebra

/-- The polynomial-plane order and the geometric chart order have
identical values in the root field, with the chosen chart parameters. -/
def linePlaneOrder (j b:Bool) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    Order L E ≃+* integralClosure (baseChart (reference j b)) E := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let A := Plane L
  let T := baseChart (reference j b)
  let orient := oriented j b
  let : Algebra A T := orient.toRingHom.toAlgebra
  let : IsScalarTower A T E := IsScalarTower.of_algebraMap_eq fun _=>rfl
  have ai : Algebra.IsIntegral A T := ⟨fun t=>by
    obtain ⟨u,rfl⟩ := orient.surjective t
    exact isIntegral_algebraMap (x:=u)⟩
  let : Algebra.IsIntegral A T := ai
  refine {
    toFun := fun x=>⟨x,(x.property.tower_top (A:=T))⟩
    invFun := fun x=>⟨x,isIntegral_trans (x:E) x.property⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl
    map_mul' := fun _ _=>rfl
    map_add' := fun _ _=>rfl }

local instance markedAxisRing (j:Bool) (z:L) : CommRing (Axis E j z) :=
  @Ideal.Quotient.commRing (Tor E) inferInstance (axisIdeal E j z)

local instance axisPlaneFibreRing [Algebra (Plane L) E] (z:L) : CommRing (Fiber E z) :=
  @Ideal.Quotient.commRing (↥(Order L E)) ((Order L E).toCommRing) (sliceIdeal E z)

def lineOrderMap (j b:Bool) (z:L) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    Order L E→+* Axis E j z := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let toTor := (intoTorus E (reference j b)).comp (linePlaneOrder (E:=E) j b).toRingHom
  exact (Ideal.Quotient.mk (axisIdeal E j z)).comp toTor

theorem lineOrderMap_range (j b:Bool) (z:L) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    ∀ v : Axis E j z,
      (∃ x : Order L E,lineOrderMap (E:=E) j b z x=v) ↔ v∈chartImage E j z b := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  dsimp only
  intro v
  constructor
  · rintro ⟨x,rfl⟩
    let w := linePlaneOrder (E:=E) j b x
    exact ⟨intoTorus E (reference j b) w,w.property,rfl⟩
  · rintro ⟨u,hu,eq⟩
    let w : integralClosure (baseChart (reference j b)) E := ⟨u,hu⟩
    refine ⟨(linePlaneOrder (E:=E) j b).symm w,?_⟩
    change red E j z (intoTorus E (reference j b)
      (linePlaneOrder j b ((linePlaneOrder j b).symm w)))=v
    rw [RingEquiv.apply_symm_apply]
    exact eq

variable [FiniteDimensional ChartField E]

theorem lineOrderMap_ker (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    RingHom.ker (lineOrderMap (E:=E) j b z)=sliceIdeal E z := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let s := reference j b
  let PlaneBase := Plane L
  let A := baseChart s
  let B := Order L E
  let B' := integralClosure A E
  let orient := oriented j b
  let via := linePlaneOrder (E:=E) j b
  let baseCut : PlaneBase := Polynomial.X-C (C z)
  let a := orient baseCut
  have aval : (a:ChartField)=divisor j z := by
    change (orient (Polynomial.X-C (C z)):ChartField)=_
    rw [map_sub]
    change ((orient Polynomial.X):ChartField)-((orient (C (C z))):ChartField)=_
    rw [Lower6961.RetainedSurfaceClass.oriented_var,Lower6961.RetainedSurfaceClass.oriented_const]
    rfl
  have an : a≠0 := (map_ne_zero_iff _ orient.injective).mpr (X_sub_C_ne_zero _)
  let : UniqueFactorizationMonoid A :=
    (MonicChartProbes.planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  have cop : IsRelPrime a (edge s (opposite s)) := by
    cases j
    · have cutval : xcut s z=a := by
        apply Subtype.ext
        rw [xcut_value,aval]
        rw [show localFrame s false=1 from rfl,div_one]
      rw [←cutval]
      exact (IsRelPrime.mul_right_iff.mp (boundary_rel s z 1 nz one_ne_zero)).1.symm
    · have cutval : zcut s z=a := by
        apply Subtype.ext
        rw [zcut_value,aval]
        rw [show localFrame s true=1 from rfl,div_one]
      rw [←cutval]
      exact (IsRelPrime.mul_right_iff.mp (boundary_rel s 1 z one_ne_zero nz)).2.symm
  have mapped : intoTorus E s (via (algebraMap PlaneBase B baseCut))=cut E j z := by
    apply Subtype.ext
    change algebraMap ChartField E (a:ChartField)=algebraMap ChartField E (divisor j z)
    rw [aval]
  ext r
  change lineOrderMap (E:=E) j b z r=0 ↔ r∈Ideal.span {algebraMap PlaneBase B baseCut}
  rw [Ideal.mem_span_singleton]
  change red E j z (intoTorus E s (via r))=0 ↔ algebraMap PlaneBase B baseCut∣r
  constructor
  · intro zero
    have hmem : intoTorus E s (via r)∈Ideal.span {cut E j z} :=
      Ideal.Quotient.eq_zero_iff_mem.mp zero
    obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp hmem
    have value : (r:E)=algebraMap A E a*(w:E) := by
      have h := congrArg (fun r:Tor E=>(r:E)) hw
      change (r:E)=algebraMap ChartField E (divisor j z)*(w:E) at h
      change (r:E)= algebraMap ChartField E (a:ChartField)*(w:E)
      rwa [aval]
    obtain ⟨n,hn⟩ := clear_torus s (w:E) w.property
    have reg : IsIntegral A (w:E) := by
      have reg_a : IsIntegral A (algebraMap A E a*(w:E)) := value ▸ (via r).property
      let g := edge s (opposite s)
      have gn : g≠0 := fun eq=>edge_ne s (opposite s) (congrArg Subtype.val eq)
      exact Lower6960.NormalizedFiber.integral_of_coprime_clearings ChartField an (pow_ne_zero _ gn) cop.pow_right
        _ reg_a (by rw [map_pow]; exact hn)
    let w' : B' := ⟨w,reg⟩
    refine ⟨via.symm w',Subtype.ext ?_⟩
    exact value
  · rintro ⟨q,rfl⟩
    change Ideal.Quotient.mk (axisIdeal E j z)
      (intoTorus E s (via (algebraMap PlaneBase B baseCut*q)))=0
    rw [map_mul,map_mul,map_mul,mapped]
    have eq : Ideal.Quotient.mk (axisIdeal E j z) (cut E j z)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [eq,zero_mul]

private def quotientEmbedding {B C : Type*} [CommRing B] [CommRing C]
    (f : B→+*C) (I : Ideal B) (ker : RingHom.ker f=I) :
    { h : (B⧸I)→+*C // Function.Injective h ∧ ∀ x:B,h (Ideal.Quotient.mk I x)=f x } := by
  have kills (r:B) (hr:r∈I) : f r=0 := by
    have mem : r∈RingHom.ker f := by rw [ker]; exact hr
    exact RingHom.mem_ker.mp mem
  exact ⟨Ideal.Quotient.lift I f kills,
    RingHom.lift_injective_of_ker_le_ideal I kills (le_of_eq ker),
    fun _=>rfl⟩

/-- The original plane fibre embeds into the torus fibre. Here its
image consists exactly of the residues of the original normalized chart. -/
def lineFibreData (j b:Bool) (z:L) (nz:z≠0) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    let f : Order L E→+*Axis E j z := lineOrderMap (E:=E) j b z
    { h : Fiber E z→+*Axis E j z // Function.Injective h ∧
      (∀ r:Order L E,h (quotientMap E z r)=f r) ∧
      ∀ v:Axis E j z,(∃ x:Fiber E z,h x=v) ↔ v∈chartImage E j z b } := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let f : Order L E→+*Axis E j z := lineOrderMap (E:=E) j b z
  let I := sliceIdeal E z
  have ker : RingHom.ker f = I := lineOrderMap_ker j b z nz
  let q := quotientEmbedding (B:=Order L E) (C:=Axis E j z) f I ker
  have range (v:Axis E j z) : (∃ x:Fiber E z,q.val x=v) ↔ v∈chartImage E j z b := by
    rw [←lineOrderMap_range (E:=E) j b z v]
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective r
      exact ⟨u,(q.property.2 u).symm.trans hr⟩
    · rintro ⟨u,hu⟩
      exact ⟨quotientMap E z u,(q.property.2 u).trans hu⟩
  exact ⟨q.val,q.property.1,q.property.2,range⟩

/-- The fibre embedding sends the native polynomial scalar to the
literal line-coordinate polynomial in the common torus quotient. -/
theorem lineFibreData_scalar (j b:Bool) (z:L) (nz:z≠0) (g:(Polynomial L)) :
    let : Algebra (Plane L) E := linePlaneAlgebra j b
    let h : Fiber E z→+*Axis E j z := (lineFibreData (E:=E) j b z nz).val
    h (baseMap E z g)=polyMap E j z b g := by
  let : Algebra (Plane L) E := linePlaneAlgebra j b
  let e := lineFibreData (E:=E) j b z nz
  let s := reference j b
  let A := baseChart s
  let orient := oriented j b
  let u := algebraMap (Plane L) (Order L E) (C g)
  change e.val (quotientMap E z u)=_
  rw [e.property.2.1]
  have he : linePlaneOrder (E:=E) j b u=algebraMap A (integralClosure A E) (orient (C g)) := rfl
  change Ideal.Quotient.mk (axisIdeal E j z) (intoTorus E s (linePlaneOrder j b u))=_
  rw [he]
  change Ideal.Quotient.mk (axisIdeal E j z) (Lower6961.RetainedSurfaceClass.embedBase E s (orient (C g)))=_
  rw [Lower6961.RetainedSurfaceClass.finite_along]
  rfl

@[instance_reducible] def axisPlaneAlgebra (b:Bool) : Algebra (Plane L) E :=
  linePlaneAlgebra true b

abbrev axisPlaneOrder (b:Bool) := linePlaneOrder (E:=E) true b

abbrev axisOrderMap (b:Bool) (z:L) := lineOrderMap (E:=E) true b z

abbrev axisFibreData (b:Bool) (z:L) (nz:z≠0) :=
  lineFibreData (E:=E) true b z nz

theorem axisFibreData_scalar (b:Bool) (z:L) (nz:z≠0) (g:(Polynomial L)) :
    let : Algebra (Plane L) E := axisPlaneAlgebra b
    let h : Fiber E z→+*Axis E true z := (axisFibreData (E:=E) b z nz).val
    h (baseMap E z g)=polyMap E true z b g :=
  lineFibreData_scalar true b z nz g

#print axioms lineFibreData
end
end Lower6961.CollisionMarked
