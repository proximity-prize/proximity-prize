import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
import Mathlib.RingTheory.Polynomial.Ideal

set_option Elab.async false

-- merged module R6960RetainedFibreQuotient
section Merged_R6960RetainedFibreQuotient

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedFibreQuotient
open Algebra
open scoped TensorProduct
variable {k A S : Type*} [Field k] [CommRing A] [CommRing S]
  [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]

/-- Specializing the finite algebra at a scalar-valued point is its quotient by
the extended point ideal, with the original scalar action on that quotient. -/
def atPoint (φ : A →ₐ[k] k) :
    letI := φ.toRingHom.toAlgebra
    (S ⧸ (RingHom.ker φ.toRingHom).map (algebraMap A S)) ≃ₐ[k] (k ⊗[A] S) := by
  letI := φ.toRingHom.toAlgebra
  let I:=RingHom.ker φ.toRingHom
  have sur : Function.Surjective φ.toRingHom := fun x=>⟨algebraMap k A x,φ.commutes x⟩
  let e : (A ⧸ I) ≃ₐ[A] k :=
    { __ := φ.toRingHom.quotientKerEquivOfSurjective sur
      commutes' := fun x=>φ.toRingHom.quotientKerEquivOfSurjective_apply_mk sur x }
  let tensor := Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=A) (A₁:=S))
  let result := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toRingEquiv.trans tensor.toRingEquiv
  refine { __ := result, commutes' := fun c=>?_ }
  change result ((Ideal.Quotient.mk _) (algebraMap k S c))=_
  change tensor (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I (Ideal.Quotient.mk _ (algebraMap k S c)))=_
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  change e 1 ⊗ₜ[A] (algebraMap k S c)=_
  rw [map_one]
  rw [IsScalarTower.algebraMap_apply k A S]
  change (1:k) ⊗ₜ[A] (algebraMap A S (algebraMap k A c))=c ⊗ₜ[A] (1:S)
  rw [Algebra.algebraMap_eq_smul_one,TensorProduct.tmul_smul]
  change (φ (algebraMap k A c) * 1) ⊗ₜ[A] (1:S)=_
  rw [φ.commutes,mul_one]
  rfl

end Lower6960.RetainedFibreQuotient

end
end Merged_R6960RetainedFibreQuotient

-- merged module R6960RetainedCrossingComparison
section Merged_R6960RetainedCrossingComparison

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartProbes ChartOverlapTests RetainedRestrictionTorus
open Polynomial Module Algebra
open scoped Lower6960.RetainedSurfaceClass Polynomial TensorProduct

abbrev Base := baseChart (false,false)
abbrev finiteOrder (E : Type) [Field E] [Algebra ChartField E] := integralClosure Base E
def baseConstants : L →+* Base := constants.codRestrict Base (chart_constant (false,false))
scoped instance baseAlgebra : Algebra L Base := baseConstants.toAlgebra
def finiteConstant (E : Type) [Field E] [Algebra ChartField E] : L→+*finiteOrder E :=
  (algebraMap Base (finiteOrder E)).comp baseConstants
scoped instance finiteAlgebra (E : Type) [Field E] [Algebra ChartField E] : Algebra L (finiteOrder E) :=
  (finiteConstant E).toAlgebra
scoped instance finiteTower (E : Type) [Field E] [Algebra ChartField E] :
    IsScalarTower L Base (finiteOrder E) := IsScalarTower.of_algebraMap_eq (R:=L) (S:=Base) (A:=finiteOrder E) fun _=>rfl

def point (x z:L) : Base→ₐ[L]L :=
  { toRingHom:=((evalRingHom x).comp (mapRingHom (evalRingHom z))).comp (planeEquiv (false,false)).symm.toRingHom
    commutes':=fun a=>by
      have eq:algebraMap L Base a=planeEquiv (false,false) (C (C a)) := Subtype.ext (planeMap_constants ..).symm
      rw [eq]; simp }

def finiteX (x:L) : Base := planeEquiv (false,false) (Polynomial.X-C (C x))
def finiteZ (z:L) : Base := planeEquiv (false,false) (C (Polynomial.X-C z))

theorem finiteX_val (x:L) : (finiteX x:ChartField)=divisor false x := by
  change planeMap _ _=_
  simp [divisor,coordinate,chartCoordinate]
theorem finiteZ_val (z:L) : (finiteZ z:ChartField)=divisor true z := by
  change planeMap _ _=_
  simp [divisor,coordinate,chartCoordinate]

theorem point_kernel (x z:L) : RingHom.ker (point x z).toRingHom =
    Ideal.span ({finiteX x}:Set Base)⊔Ideal.span {finiteZ z} := by
  let e:=planeEquiv (false,false)
  have pol (p:PlaneConstants.Plane L) : point x z (e p)=(p.eval (C x)).eval z := by
    change eval x ((e.symm (e p)).map (evalRingHom z))=(p.eval (C x)).eval z
    rw [e.symm_apply_apply]
    simpa using (Polynomial.eval_map_apply (evalRingHom z) (p:=p) (x:=C x))
  ext a
  obtain ⟨p,rfl⟩:=e.surjective a
  rw [RingHom.mem_ker]
  change point x z (e p)=0 ↔ _
  rw [pol,←Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero,
    Ideal.mem_span_pair]
  constructor
  · rintro ⟨b,c,eq⟩
    rw [←eq,map_add,map_mul,map_mul]
    exact Submodule.mem_sup.mpr ⟨_,Ideal.mem_span_singleton.mpr (dvd_mul_left (finiteX x) (e c)),
      _,Ideal.mem_span_singleton.mpr (dvd_mul_left (finiteZ z) (e b)),add_comm ..⟩
  · intro h
    obtain ⟨b,bx,c,cz,eq⟩:=Submodule.mem_sup.mp h
    obtain ⟨b',rfl⟩:=Ideal.mem_span_singleton.mp bx
    obtain ⟨c',rfl⟩:=Ideal.mem_span_singleton.mp cz
    refine ⟨e.symm c',e.symm b',e.injective ?_⟩
    simp only [map_add,map_mul,e.apply_symm_apply]
    rw [←eq]; change c'*finiteZ z+b'*finiteX x=finiteX x*b'+finiteZ z*c'
    ring

variable (E : Type) [Field E] [Algebra ChartField E]

def fromFinite : finiteOrder E→ₐ[L]Tor E where
  toFun y:=⟨y,order_mono (base_torus (false,false)) y.property⟩
  map_one':=rfl
  map_zero':=rfl
  map_add' _ _:=rfl
  map_mul' _ _:=rfl
  commutes' _:=rfl

def toCross (x z:L) : finiteOrder E→ₐ[L]Crossing E x z :=
  (Ideal.Quotient.mkₐ L (axisIdeal E false x⊔axisIdeal E true z)).comp (fromFinite E)

private theorem scaled (x z:L) (v:Tor E) :
    ∃ n : ℕ, ∃ y:finiteOrder E, toCross E x z y =
      (algebraMap L (Crossing E x z) (x*z))^n * Ideal.Quotient.mk _ v := by
  let J:=axisIdeal E false x⊔axisIdeal E true z
  let π:=Ideal.Quotient.mk J
  let Xp:Tor E:=⟨algebraMap ChartField E RatFunc.X,isIntegral_algebraMap (x:=(⟨_,torus_coordinate false false⟩:torus))⟩
  let Zp:Tor E:=⟨algebraMap ChartField E scalarCoordinate,isIntegral_algebraMap (x:=(⟨_,torus_coordinate true false⟩:torus))⟩
  have xx : π Xp=algebraMap L _ x := by
    apply Ideal.Quotient.eq.mpr
    have eq : Xp-algebraMap L (Tor E) x=cut E false x := by
      apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
    rw [eq]; exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
  have zz : π Zp=algebraMap L _ z := by
    apply Ideal.Quotient.eq.mpr
    have eq : Zp-algebraMap L (Tor E) z=cut E true z := by
      apply Subtype.ext; exact (map_sub (algebraMap ChartField E) _ _).symm
    rw [eq]; exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨n,h⟩:=clear_torus (false,false) v.val v.property
  let y:finiteOrder E:=⟨_,h⟩
  have val : fromFinite E y=(Xp*Zp)^n*v := by
    apply Subtype.ext
    change (algebraMap ChartField E (boundary _ _))^n * v.val = (_*_)^n*v.val
    simp [boundary,opposite,chartCoordinate,map_mul,Xp,Zp]
  refine ⟨n,y,?_⟩
  change π (fromFinite E y)=_
  rw [val,map_mul,map_pow,map_mul,xx,zz,map_mul]

set_option synthInstance.maxHeartbeats 200000 in
theorem cross_surjective (x z:L) (nx:x≠0) (nz:z≠0) : Function.Surjective (toCross E x z) := by
  intro w
  obtain ⟨v,rfl⟩:=Ideal.Quotient.mk_surjective w
  obtain ⟨n,y,eq⟩:=scaled E x z v
  refine ⟨(x*z)⁻¹^n • y,?_⟩
  rw [map_smul,eq,←map_pow,←Algebra.smul_def,smul_smul,←mul_pow,inv_mul_cancel₀ (mul_ne_zero nx nz),one_pow,one_smul]


theorem toCross_kernel (x z:L) (nx:x≠0) (nz:z≠0) :
    RingHom.ker (toCross E x z).toRingHom=(RingHom.ker (point x z).toRingHom).map
      (algebraMap Base (finiteOrder E)) := by
  let S:=finiteOrder E
  let Xp:=algebraMap Base S (finiteX x)
  let Zp:=algebraMap Base S (finiteZ z)
  have xeq : fromFinite E Xp=cut E false x := Subtype.ext (congrArg (algebraMap ChartField E) (finiteX_val x))
  have zeq : fromFinite E Zp=cut E true z := Subtype.ext (congrArg (algebraMap ChartField E) (finiteZ_val z))
  have xf : (xcut (false,false) x:ChartField)=divisor false x := by simp [xcut_value,localFrame,axisBit]
  have zf : (zcut (false,false) z:ChartField)=divisor true z := by simp [zcut_value,localFrame,axisBit]
  rw [point_kernel,Ideal.map_sup,Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton]
  change RingHom.ker _=Ideal.span ({Xp}:Set S) ⊔Ideal.span {Zp}
  apply le_antisymm
  · intro y hy
    have zero : fromFinite E y∈axisIdeal E false x ⊔ axisIdeal E true z :=
      Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨_,h₁,_,h₂,eq⟩:=Submodule.mem_sup.mp zero
    obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp h₁
    obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp h₂
    have coeffX : algebraMap Base E (xcut (false,false) x)=algebraMap ChartField E (divisor false x) :=
      congrArg (algebraMap ChartField E) xf
    have coeffZ : algebraMap Base E (zcut (false,false) z)=algebraMap ChartField E (divisor true z) :=
      congrArg (algebraMap ChartField E) zf
    obtain ⟨w,a',b',_,ia,ib,la,lb⟩:=lift_on_chart (false,false) x z nx nz (y:E) (0:E)
      y.property isIntegral_zero ⟨a,b,a.property,b.property,by
        rw [sub_zero,coeffX,coeffZ]; exact congrArg Subtype.val eq.symm⟩
    refine Submodule.mem_sup.mpr ⟨Xp*⟨a',ia⟩,Ideal.mem_span_singleton.mpr (dvd_mul_right ..),
      Zp*⟨b',ib⟩,Ideal.mem_span_singleton.mpr (dvd_mul_right ..),Subtype.ext ?_⟩
    rw [sub_zero,coeffZ] at lb; rw [coeffX] at la
    change algebraMap ChartField E (finiteX x:ChartField)*a'+algebraMap ChartField E (finiteZ z:ChartField)*b'=y
    rw [finiteX_val,finiteZ_val,←la,←lb,sub_add_cancel]
  · apply sup_le
    · apply Ideal.span_le.mpr; rintro _ ⟨⟩
      change Ideal.Quotient.mk _ (fromFinite E Xp)=0
      rw [xeq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
    · apply Ideal.span_le.mpr; rintro _ ⟨⟩
      change Ideal.Quotient.mk _ (fromFinite E Zp)=0
      rw [zeq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))

def crossingEquiv (x z:L) (nx:x≠0) (nz:z≠0) :
    letI := (point x z).toRingHom.toAlgebra
    Crossing E x z ≃ₐ[L] (L ⊗[Base] finiteOrder E) := by
  letI := (point x z).toRingHom.toAlgebra
  let e:=Ideal.quotientKerAlgEquivOfSurjective (cross_surjective E x z nx nz)
  let transport:=Ideal.quotientEquivAlgOfEq L (toCross_kernel E x z nx nz)
  exact e.symm.trans (transport.trans (RetainedFibreQuotient.atPoint (S:=finiteOrder E) (point x z)))

open RetainedCompression (Curve ordinate view)
/-- The crossing space in the actual restriction map is reduced and has precisely
the ordinate degree, for one finite pair off the coordinate boundary. -/
theorem actual_crossing (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ x z:L,x≠0 ∧ z≠0 ∧ Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧
      IsReduced (Crossing E x z) := by
  obtain ⟨x,z,nx,nz,good⟩:=RetainedCrossingBasis.actual_good_lines f ir lo hi basis root
  letI := (point x z).toRingHom.toAlgebra
  obtain ⟨⟨B⟩,reduced⟩:=good L (point x z).toRingHom le_rfl
  let e:=crossingEquiv E x z nx nz
  refine ⟨x,z,nx,nz,⟨B.map e.symm.toLinearEquiv⟩,?_⟩
  constructor
  intro a ha
  exact e.injective ((ha.map e.toRingHom).eq_zero.trans (map_zero e).symm)

end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedCrossingComparison
