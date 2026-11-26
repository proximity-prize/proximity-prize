import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdCS
import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicFibre
import ProximityPrize.SubmissionLower.R6960LineEulerFree
import ProximityPrize.SubmissionLower.R6960RetainedCrossingLift
import ProximityPrize.SubmissionLower.R6966ProofFarChart

section Merged6967_R6960CollisionMarkedFibreNormalization
set_option Elab.async false





set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Module Algebra
open scoped Polynomial
variable {A K V : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing V] [Algebra A V] [Algebra K V] [IsScalarTower A K V]
  [FiniteDimensional K V]
private theorem small_fields_separable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [CharP K p] (small : finrank K L<p) : Algebra.IsSeparable K L := by
  constructor
  intro x
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible hx)).mpr
    (CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char p _ (minpoly.natDegree_pos hx)
      ((minpoly.natDegree_le x).trans_lt small))
theorem reduced_normalization_finite [IsReduced V] (p : ℕ) [CharP K p]
    (small : finrank K V<p) : Module.Finite A (integralClosure A V) := by
  classical
  let : IsArtinianRing V := isArtinian_of_tower K (inferInstance : IsArtinian K V)
  let I := MaximalSpectrum V
  let L (i : I) := V ⧸ i.asIdeal
  let : ∀ i : I, Field (L i) := fun i=>@Ideal.Quotient.field V _ i.asIdeal i.isMaximal
  let : ∀ i : I, Algebra K (L i) := fun i=>inferInstanceAs (Algebra K (V ⧸ i.asIdeal))
  let : ∀ i : I, Algebra A (L i) := fun i=>inferInstanceAs (Algebra A (V ⧸ i.asIdeal))
  let : ∀ i : I, IsScalarTower A K (L i) := fun i=>
    IsScalarTower.of_algebraMap_eq (R:=A) (S:=K) (A:=L i) fun a=>by
      change Ideal.Quotient.mk _ (algebraMap A V a)=Ideal.Quotient.mk _ (algebraMap K V (algebraMap A K a))
      rw [←IsScalarTower.algebraMap_apply A K V]
  let projK (i : I) : V→ₗ[K]L i := (IsScalarTower.toAlgHom K V (L i)).toLinearMap
  have surj (i : I) : Function.Surjective (projK i) := Ideal.Quotient.mk_surjective
  let : ∀ i : I, FiniteDimensional K (L i) := fun i=>FiniteDimensional.of_surjective (projK i) (surj i)
  let : ∀ i : I, Algebra.IsSeparable K (L i) := fun i=>small_fields_separable p
    ((LinearMap.finrank_le_finrank_of_surjective (f:=projK i) (surj i)).trans_lt small)
  let : ∀ i : I, Module.Finite A (integralClosure A (L i)) := fun i=>
    IsIntegralClosure.finite A K (L i) (integralClosure A (L i))
  let proj (i : I) : V→ₐ[A]L i := IsScalarTower.toAlgHom A V (L i)
  let j : integralClosure A V →ₗ[A] (∀ i : I,integralClosure A (L i)) := {
    toFun := fun v i=>⟨proj i (v:V),v.property.map (proj i)⟩
    map_add' := fun x y=>funext fun i=>Subtype.ext (map_add (proj i) _ _)
    map_smul' := fun a x=>funext fun i=>Subtype.ext ((proj i).toLinearMap.map_smul a (x:V)) }
  have ji : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply (IsArtinianRing.equivPi V).injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact Module.Finite.of_injective j ji
omit [IsPrincipalIdealRing A] in
theorem integral_elements_localize (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K V] [IsScalarTower A K V] [FiniteDimensional K V] :
    IsLocalizedModule (nonZeroDivisors A) (integralClosure A V).val.toLinearMap := by
  let j := (integralClosure A V).val.toLinearMap
  constructor
  · intro r
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun x : V=>(r:A) • x)
    have rK : algebraMap A K (r:A)≠0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp r.property)
    refine ⟨?_,?_⟩
    · intro x y eq
      apply smul_right_injective V rK
      simpa only [IsScalarTower.algebraMap_smul K] using eq
    · intro y
      refine ⟨(algebraMap A K (r:A))⁻¹ • y,?_⟩
      change (r:A) • ((algebraMap A K (r:A))⁻¹ • y)=y
      calc
        _ = (algebraMap A K (r:A)) • ((algebraMap A K (r:A))⁻¹ • y) :=
          (IsScalarTower.algebraMap_smul K _ _).symm
        _ = y := by rw [smul_smul,mul_inv_cancel₀ rK,one_smul]
  · intro x
    have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
    have : Algebra.IsAlgebraic A V := Algebra.IsAlgebraic.trans A K V
    obtain ⟨r,nz,h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R:=A) x).exists_integral_multiple
    exact ⟨⟨⟨r • x,h⟩,⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr nz⟩⟩,rfl⟩
  · intro a b eq
    exact ⟨1,congrArg (1 • ·) (Subtype.ext eq)⟩
theorem reduced_normalization_basis [IsReduced V] (p : ℕ) [CharP K p]
    (small : finrank K V<p) :
    ∃ (b : Basis (Fin (finrank K V)) A (integralClosure A V))
      (bk : Basis (Fin (finrank K V)) K V),∀ i,bk i=(b i:V) := by
  let N := integralClosure A V
  let : Module.Finite A N := reduced_normalization_finite (K:=K) p small
  let : Module.IsTorsionFree A V := Module.IsTorsionFree.of_smul_eq_zero fun r x hx=>by
    by_cases h : r=0
    · exact Or.inl h
    · have nz := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr h
      rw [←IsScalarTower.algebraMap_smul K] at hx
      exact Or.inr ((smul_eq_zero_iff_right nz).mp hx)
  let : Module.IsTorsionFree A N := inferInstanceAs (Module.IsTorsionFree A (integralClosure A V))
  let j := N.val.toLinearMap
  let : IsLocalizedModule (nonZeroDivisors A) j := integral_elements_localize K
  let b := Module.finBasis A N
  let bk := b.ofIsLocalizedModule K (nonZeroDivisors A) j
  have rank : finrank A N=finrank K V := by
    simpa only [Fintype.card_fin] using (finrank_eq_card_basis bk).symm
  refine ⟨b.reindex (finCongr rank),bk.reindex (finCongr rank),fun i=>?_⟩
  rw [Basis.reindex_apply,Basis.reindex_apply,Basis.ofIsLocalizedModule_apply]
  rfl
#print axioms reduced_normalization_finite
#print axioms reduced_normalization_basis
end
end Lower6960.CollisionMarked

end Merged6967_R6960CollisionMarkedFibreNormalization

section Merged6967_R6960RetainedCrossingComparison
set_option Elab.async false






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

#print axioms atPoint
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

#print axioms point_kernel
#print axioms cross_surjective

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

#print axioms actual_crossing
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedCrossingComparison

end Merged6967_R6960RetainedCrossingComparison

section Merged6967_R6960RetainedTwoLineBound
set_option Elab.async false



set_option Elab.async false
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwoLineBound
open Module Submodule LinearMap LineEuler
section
variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]
def difference (P Q : Submodule k U) : (P×Q)→ₗ[k]U := P.subtype.coprod (-Q.subtype)
theorem image (P Q : Submodule k U) : (difference P Q).range = P⊔Q := by
  ext v
  constructor
  · rintro ⟨⟨u,w⟩,rfl⟩
    exact mem_sup.mpr ⟨u,u.property,-(w:U),Q.neg_mem w.property,rfl⟩
  · intro h
    obtain ⟨u,hu,w,hw,rfl⟩:=mem_sup.mp h
    exact ⟨(⟨u,hu⟩,⟨-w,Q.neg_mem hw⟩),by simp [difference]⟩
def diagonal (P Q : Submodule k U) : ↥(P⊓Q) ≃ₗ[k] (difference P Q).ker where
  toFun w:=⟨(⟨w,w.property.1⟩,⟨w,w.property.2⟩),by simp [difference]⟩
  invFun v:=⟨(v.val.1:U),v.val.1.property,by
    have diff : (v.val.1:U)+ -(v.val.2:U)=0 := v.property
    have eq : (v.val.1:U)=(v.val.2:U) := sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using diff)
    exact eq ▸ v.val.2.property⟩
  left_inv _:=rfl
  right_inv v:=by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · apply Subtype.ext
      have diff : (v.val.1:U)+ -(v.val.2:U)=0 := v.property
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using diff)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
end
variable {k ι C : Type*} [Field k] [Fintype ι] [DecidableEq ι]
  [AddCommGroup C] [Module k C] [FiniteDimensional k C]
abbrev diff (G : Matrix ι ι (Laurent k)) := difference (finiteLattice k ι) (transitionLattice G)
abbrev ev (G : Matrix ι ι (Laurent k)) (x : finiteLattice k ι →ₗ[k] C) :=
  x.comp (LinearMap.fst k (finiteLattice k ι) (transitionLattice G))
abbrev globals (G : Matrix ι ι (Laurent k)) (x : finiteLattice k ι →ₗ[k] C) :
    H0 G →ₗ[k] C := x.comp (Submodule.inclusion inf_le_left)
set_option synthInstance.maxHeartbeats 400000 in
theorem two_line_bound (G H : Matrix ι ι (Laurent k)) (g : IsUnit G) (h : IsUnit H)
    (s t : ℕ) (dg : G.det.degree = ((-(s:ℤ) : ℤ) : WithBot ℤ))
    (dh : H.det.degree = ((-(t:ℤ) : ℤ) : WithBot ℤ))
    (x z : finiteLattice k ι →ₗ[k] C) (cross : finrank k C=Fintype.card ι)
    (ix : Function.Injective (globals G x)) (iz : Function.Injective (globals H z)) :
    let B:=RetainedNodalIndex.boundaries (diff G) (diff H) (ev G x) (ev H z)
    FiniteDimensional k (((ι→Laurent k)×(ι→Laurent k)) ⧸ B) ∧
      finrank k (((ι→Laurent k)×(ι→Laurent k)) ⧸ B) ≤ s+t := by
  obtain ⟨fg,fg',m,me,mval⟩:=euler_index G g
  obtain ⟨fh,fh',n,ne,nval⟩:=euler_index H h
  have mg : m= -(s:ℤ) := WithBot.coe_injective (me.symm.trans dg)
  have nh : n= -(t:ℤ) := WithBot.coe_injective (ne.symm.trans dh)
  rw [mg] at mval
  rw [nh] at nval
  have rg : (diff G).range = finiteLattice k ι ⊔ transitionLattice G := image ..
  have rh : (diff H).range = finiteLattice k ι ⊔ transitionLattice H := image ..
  have : FiniteDimensional k ((ι→Laurent k) ⧸ (diff G).range) := rg ▸ fg'
  have : FiniteDimensional k ((ι→Laurent k) ⧸ (diff H).range) := rh ▸ fh'
  obtain ⟨finite,bound⟩:=RetainedNodalIndex.dimension (diff G) (diff H) (ev G x) (ev H z)
  let W:=(diff G).ker.map (ev G x) ⊔ (diff H).ker.map (ev H z)
  have into (v:H0 H) : globals H z v∈W :=
    Submodule.mem_sup_right (Submodule.mem_map.mpr
      ⟨(diagonal _ _ v).val,(diagonal _ _ v).property,rfl⟩)
  let lift: H0 H→ₗ[k]W := (globals H z).codRestrict W into
  have iw := LinearMap.finrank_le_finrank_of_injective (f:=lift)
    (fun u v eq=>iz (congrArg (fun y:W=>(y:C)) eq))
  have c:=LinearMap.finrank_le_finrank_of_injective (f:=globals G x) ix
  rw [rg,rh,cross] at bound
  rw [cross] at c
  change _ + finrank k W ≤ finrank k (H1 G)+finrank k (H1 H)+Fintype.card ι at bound
  exact ⟨finite,by omega⟩
#print axioms two_line_bound
end Lower6960.RetainedTwoLineBound

end
end Merged6967_R6960RetainedTwoLineBound

section Merged6967_R6966ProofFarSurface
set_option Elab.async false




set_option Elab.async false

section Merged_R6960RetainedChartGluing
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedChartGluing
open ChartSections (Chart)
open MonicChart MonicFourChartDescent MonicScalarCorrection ChartGlobalTests
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
open Lower6960.MonicFourChartDescent (finite_inclusion infinity_inclusion)
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem common_correction_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo hi basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate_far f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩
#print axioms common_correction_far
theorem split_cocycle_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (g : Chart→Chart→E)
    (add : ∀ s t r, g s t+g t r=g s r)
    (regular : ∀ s t, IsIntegral (MonicChartLaurent.overlapRing s t)
      (algebraMap ChartField E (frame a b s)*g s t)) :
    ∃ w : Chart→E, (∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*w s)) ∧
      ∀ s t, g s t=w s-w t := by
  let u (s : Chart):=g s (false,false)
  have diff (s t) : u s-u t=g s t := sub_eq_of_eq_add (add s t (false,false)).symm
  obtain ⟨c,hc⟩:=common_correction_far f ir lo hi bounded basis root a b ha hb u
    (fun s t=> by rw [diff]; exact regular s t)
  exact ⟨fun s=>u s-c,hc,fun s t=>by rw [←diff]; ring⟩
#print axioms split_cocycle_far
end Lower6960.RetainedChartGluing

end
end Merged_R6960RetainedChartGluing

section Merged_R6960RetainedLineRestriction
noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedLineRestriction
open MonicFourChartDescent ChartSections MonicChart RetainedChartGluing
open ChartGlobalTests (frame_ne)
open MonicChartLaurent (overlapRing)
open MonicChartProbes (planeMap planeMap_injective)
open RetainedCompression (Curve ordinate view height heightCap)
open Polynomial
open K1_14 (L)
private theorem lines_ne (x z : L) : lines x z≠0 := by
  let m := planeMap (false,false)
  have a : (Polynomial.X (R:=(Polynomial L)))-C (C x)≠0 := X_sub_C_ne_zero _
  have b : (C (Polynomial.X (R:=L)) : (Polynomial (Polynomial L)))-C (C z)≠0 := by
    rw [←map_sub]; exact C_ne_zero.mpr (X_sub_C_ne_zero _)
  have good := (map_ne_zero_iff m (planeMap_injective _)).mpr (mul_ne_zero a b)
  simpa only [m,map_mul,map_sub,MonicChartProbes.planeMap_constants,MonicChartProbes.planeMap_scalar,
    MonicChartProbes.planeMap_abscissa,chartCoordinate,Bool.false_eq_true,ite_false,lines] using good
variable {E : Type*} [Field E] [Algebra ChartField E]
theorem split_of_split_on_lines_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (x z : L) (g : Chart→Chart→E) (add : ∀ s t r, g s t+g t r=g s r)
    (v : Chart→E) (localV : ∀ s, IsIntegral (baseChart s) (v s))
    (restricted : ∀ s t, ∃ r : E, IsIntegral (overlapRing s t) r ∧
      g s t-(v s-v t)=algebraMap ChartField E (lines x z / frame 1 1 s)*r) :
    ∃ w : Chart→E, (∀ s,IsIntegral (baseChart s) (w s)) ∧ ∀ s t,g s t=w s-w t := by
  let ι:=algebraMap ChartField E
  let P:=ι (lines x z)
  have pn : P≠0 := (map_ne_zero_iff ι ι.injective).mpr (lines_ne x z)
  let h (s t:Chart):=(g s t-(v s-v t))/P
  have coc (s t r) : h s t+h t r=h s r := by
    dsimp [h]
    rw [←add_div]
    congr 1
    linear_combination add s t r
  have twist (s t) : IsIntegral (overlapRing s t) (ι (frame 1 1 s)*h s t) := by
    obtain ⟨r,hr,eq⟩:=restricted s t
    have nz := (map_ne_zero_iff ι ι.injective).mpr (frame_ne 1 1 s)
    have recover : ι (frame 1 1 s)*h s t=r := by
      dsimp only [h]; rw [eq,map_div₀]
      change ι (frame 1 1 s)*(P/ι (frame 1 1 s)*r/P)=r
      field_simp
    rwa [recover]
  obtain ⟨w,localW,diff⟩:=split_cocycle_far f ir lo hi bounded basis root 1 1 (by decide) (by decide) h coc twist
  refine ⟨fun s=>v s+P*w s,fun s=>(localV s).add ?_,fun s t=>?_⟩
  · have integral : IsIntegral (baseChart s) (ι (lines x z/frame 1 1 s)) :=
      isIntegral_algebraMap (x:=(⟨_, local_equation x z s⟩ : baseChart s))
    have eq : ι (lines x z / frame 1 1 s)*(ι (frame 1 1 s)*w s)=P*w s := by
      rw [map_div₀,←mul_assoc,div_mul_cancel₀ _ ((map_ne_zero_iff ι ι.injective).mpr (frame_ne _ _ _))]
    exact eq ▸ integral.mul (localW s)
  · have eq := (div_eq_iff pn).mp (diff s t)
    linear_combination eq
#print axioms split_of_split_on_lines_far
end Lower6960.RetainedLineRestriction

end
end Merged_R6960RetainedLineRestriction

section Merged_R6960RetainedPairedResidues

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedRestrictionTorus
open MonicChart (ChartField)
open K1_14 (L)
open MonicFourChartDescent ChartSections MonicChartLaurent ChartOverlapTests Polynomial
open RetainedCompression (Curve ordinate view height heightCap)
open scoped Polynomial
variable {E : Type*} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

private theorem base_x (s : Chart) (x:L) : algebraMap (baseChart s) E (xcut s x) =
    ι (divisor false x)/ι (localFrame s false) := by
  change ι ((xcut s x):ChartField)=_
  rw [xcut_value,map_div₀]
private theorem base_z (s : Chart) (z:L) : algebraMap (baseChart s) E (zcut s z) =
    ι (divisor true z)/ι (localFrame s true) := by
  change ι ((zcut s z):ChartField)=_
  rw [zcut_value,map_div₀]

private theorem glue (s : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (u v:E)
    (hu:IsIntegral (baseChart s) u) (hv:IsIntegral (baseChart s) v) (h:Matched x z u v) :
    ∃ y:E,IsIntegral (baseChart s) y ∧ Congruent false x u y ∧ Congruent true z v y := by
  obtain ⟨a,b,ia,ib,eq⟩:=h
  have fn (j : Bool) : (ι (localFrame s j) : E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s j)
  have m:=lift_on_chart s x z nx nz u v hu hv ⟨ι (localFrame s false)*a,ι (localFrame s true)*b,
    (frame_integral s false).1.mul ia,(frame_integral s true).1.mul ib,by
      rw [base_x,base_z,eq]; field_simp [fn]⟩
  obtain ⟨y,a',b',hy,ia',ib',dx,dz⟩:=m
  refine ⟨y,hy,⟨ι ((localFrame s false)⁻¹)*a',
    (frame_integral s false).2.mul (order_mono (base_torus s) ia'),?_⟩,Congruent.symm
      ⟨ι ((localFrame s true)⁻¹)*b',(frame_integral s true).2.mul (order_mono (base_torus s) ib'),?_⟩⟩
  · rw [dx,base_x,map_inv₀,div_eq_mul_inv,mul_assoc]
  · rw [dz,base_z,map_inv₀,div_eq_mul_inv,mul_assoc]

private theorem product_residue [FiniteDimensional ChartField E]
    (s t : Chart) (x z:L) (nx:x≠0) (nz:z≠0) (v:E)
    (reg : IsIntegral (overlapRing s t) v) (vx : Congruent false x v 0) (vz : Congruent true z v 0) :
    ∃ r:E, IsIntegral (overlapRing s t) r ∧
      v=ι (RetainedLineRestriction.lines x z / frame 1 1 s)*r := by
  obtain ⟨a,ia,ea⟩:=vx; obtain ⟨b,ib,eb⟩:=vz
  rw [sub_zero] at ea eb
  let Xv:=ι (divisor false x)
  let Zv:=ι (divisor true z)
  let P:=ι (localFrame s false)
  let Q:=ι (localFrame s true)
  have mne (p:ChartField) (pn:p≠0) : (ι p:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr pn
  have xn : Xv≠0:=mne _ (divisor_ne false x)
  have zn : Zv≠0:=mne _ (divisor_ne true z)
  have pn : P≠0:=mne _ (localFrame_ne s false)
  have qn : Q≠0:=mne _ (localFrame_ne s true)
  let r:=P*Q*v/(Xv*Zv)
  have xeq : algebraMap (baseChart s) E (xcut s x)*r=Q*b := by
    rw [base_x]; change Xv/P*(P*Q*v/(Xv*Zv))=Q*b
    change v=Zv*b at eb
    rw [eb]; field_simp
  have zeq : algebraMap (baseChart s) E (zcut s z)*r=P*a := by
    rw [base_z]; change Zv/Q*(P*Q*v/(Xv*Zv))=P*a
    change v=Xv*a at ea
    rw [ea]; field_simp
  have both : algebraMap (baseChart s) E (xcut s x*zcut s z)*r=v := by
    rw [map_mul,base_x,base_z]; change Xv/P*(Zv/Q)*(P*Q*v/(Xv*Zv))=v
    field_simp
  refine ⟨r,cancel_both s t x z nx nz r (both ▸ reg)
    (xeq ▸ (frame_integral s true).1.mul ib) (zeq ▸ (frame_integral s false).1.mul ia),?_⟩
  have e : frame 1 1 s=localFrame s false*localFrame s true := by simp [frame,localFrame,axisBit,coordinate]
  rw [e,map_div₀,map_mul]
  rw [RetainedLineRestriction.lines,map_mul]
  change v=(Xv*Zv)/(P*Q)*(P*Q*v/(Xv*Zv))
  field_simp

private theorem lift_axis (j : Bool) (c:L) (nc:c≠0) (u:Chart→E) (v:Bool→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (data : LineData j c u v) (s:Chart) :
    ∃ w:E,IsIntegral (baseChart s) w ∧ Congruent j c (u s-(u (false,false)-v false)) w := by
  let bit:=axisBit s (!j)
  let t:=reference j bit
  have parallel : axisBit s (!j)=axisBit t (!j) := by cases j <;> simp [bit,t,reference,axisBit]
  have r := (reg s t).add (order_mono (chart_cover s t) (data.1 bit))
  obtain ⟨w,hw,cw⟩:=line_representative j c nc s t parallel (u s-u t+v bit) r
  refine ⟨w,hw,Congruent.trans ?_ cw⟩
  have shared : Congruent j c (u (false,false)-u t) (v false-v bit) := by
    cases h:bit with
    | false => have t0:t=(false,false) := by cases j <;> simp [t,h,reference]
               rw [t0,sub_self,sub_self]; exact Congruent.refl j c 0
    | true => simpa only [t,h] using data.2
  obtain ⟨d,id,eq⟩:=shared.symm
  exact ⟨d,id,by rw [←eq]; abel⟩

/-- Only two transition differences and one crossing value are needed to detect an
untwisted obstruction on the original four normalized charts. -/
theorem split_of_paired_data_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) (u:Chart→E)
    (reg : ∀ s t, IsIntegral (overlapRing s t) (u s-u t)) (v w:Bool→E)
    (dv : LineData false x u v) (dw : LineData true z u w) (joined : Matched x z (v false) (w false)) :
    ∃ c:E, Correction 0 0 u c := by
  let : FiniteDimensional ChartField E := basis.finite
  choose a ia ca using lift_axis false x nx u v reg dv
  choose b ib cb using lift_axis true z nz u w reg dw
  obtain ⟨h₁,h₂,ih₁,ih₂,joint⟩:=joined
  have m (s:Chart) : Matched x z (a s) (b s) := by
    obtain ⟨p,ip,ep⟩:=ca s
    obtain ⟨q,iq,eq⟩:=cb s
    refine ⟨h₁-p,h₂+q,ih₁.sub ip,ih₂.add iq,?_⟩
    rw [mul_sub,mul_add]
    linear_combination joint-ep+eq
  choose l il ax az using fun s=>glue s x z nx nz (a s) (b s) (ia s) (ib s) (m s)
  have residual (s t : Chart) (j:Bool) (d:L) (y:E) (lift:∀ i,Congruent j d (u i-y) (l i)) :
      Congruent j d ((u s-u t)-(l s-l t)) 0 := by
    obtain ⟨r,hr,eq⟩:=(lift s).sub (lift t)
    refine ⟨r,hr,?_⟩
    rw [sub_zero,←eq]; abel
  have restriction (s t : Chart) := product_residue s t x z nx nz ((u s-u t)-(l s-l t))
    ((reg s t).sub ((order_mono (into_cleared _ (edge s t)) (il s)).sub (order_mono (chart_cover s t) (il t))))
    (residual s t _ _ _ (fun i=>(ca i).trans (ax i))) (residual s t _ _ _ (fun i=>(cb i).trans (az i)))
  obtain ⟨p,ip,eq⟩:=RetainedLineRestriction.split_of_split_on_lines_far f ir lo hi bounded basis root x z
    (fun s t=>u s-u t) (fun _ _ _=>by abel) l il restriction
  refine ⟨u (false,false)-p (false,false),fun s=>?_⟩
  have id : u s-(u (false,false)-p (false,false))=p s := by linear_combination eq s (false,false)
  simpa [id,frame] using ip s

#print axioms split_of_paired_data_far
end Lower6960.RetainedRestrictionTorus

end
end Merged_R6960RetainedPairedResidues

section Merged_R6960RetainedSurfaceClass

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open ChartSections (Chart)
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6960.MonicChartLaurent

variable (E : Type) [Field E] [Algebra ChartField E]
open scoped Lower6960.RetainedSurfaceClass

private theorem raw_zero (x z:L) (u:potentials E) : rawMap E x z u=0 ↔
    ∃ v:Bool→Tor E, ∃ w:Bool→Tor E,
      (∀ b,IsIntegral (baseChart (reference false b)) (v b:E)) ∧
      (∀ b,IsIntegral (baseChart (reference true b)) (w b:E)) ∧
      red E false x (u.1 (false,false)-u.1 (reference false true))=red E false x (v false-v true) ∧
      red E true z (u.1 (false,false)-u.1 (reference true true))=red E true z (w false-w true) ∧
      (Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z)) (v false) =
        Ideal.Quotient.mk _ (w false) := by
  rw [show rawMap E x z u=0 ↔ _ from Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,eq,edge⟩
    obtain ⟨v0,iv0,h0⟩:=a.property
    obtain ⟨v1,iv1,h1⟩:=b.property
    obtain ⟨w0,iw0,g0⟩:=c.property
    obtain ⟨w1,iw1,g1⟩:=d.property
    let v (i:Bool):Tor E:=if i then v1 else v0
    let w (i:Bool):Tor E:=if i then w1 else w0
    refine ⟨v,w,(fun i=>by cases i <;> first | exact iv0 | exact iv1),
      (fun i=>by cases i <;> first | exact iw0 | exact iw1),?_,?_,?_⟩
    · change _=red E false x (v0-v1)
      rw [map_sub (red E false x) v0 v1,h0,h1]
      have e:= (congrArg Prod.fst edge).symm
      change red E false x (u.1 (false,false)-u.1 (reference false true))=a.1+ -b.1 at e
      simpa only [sub_eq_add_neg] using e
    · change _=red E true z (w0-w1)
      rw [map_sub (red E true z) w0 w1,g0,g1]
      have e:= (congrArg Prod.snd edge).symm
      change red E true z (u.1 (false,false)-u.1 (reference true true))=c.1+ -d.1 at e
      simpa only [sub_eq_add_neg] using e
    · change crossingX E x z a.1+ -(crossingZ E x z c.1)=0 at eq
      rw [←h0,←g0] at eq
      change (Ideal.Quotient.mk _ v0)+ -(Ideal.Quotient.mk _ w0)=0 at eq
      rw [←sub_eq_add_neg] at eq
      exact sub_eq_zero.mp eq
  · rintro ⟨v,w,iv,iw,ex,ez,node⟩
    let a (i:Bool): chartImage E false x i:=⟨_,⟨v i,iv i,rfl⟩⟩
    let b (i:Bool): chartImage E true z i:=⟨_,⟨w i,iw i,rfl⟩⟩
    refine ⟨((a false,a true),(b false,b true)),?_,?_⟩
    · change Ideal.Quotient.mk _ (v false)+ -Ideal.Quotient.mk _ (w false)=0
      rw [node,add_neg_cancel]
    · apply Prod.ext
      · change red E false x (v false)+ -(red E false x (v true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ex.symm
      · change red E true z (w false)+ -(red E true z (w true))=_
        rw [←sub_eq_add_neg,←map_sub]; exact ez.symm

private theorem matched_of_eq (x z:L) (a b:Tor E)
    (eq : Ideal.Quotient.mk (axisIdeal E false x⊔axisIdeal E true z) a=Ideal.Quotient.mk _ b) :
    Matched x z (a:E) (b:E) := by
  obtain ⟨u,hu,v,hv,l⟩:=Submodule.mem_sup.mp (Ideal.Quotient.eq.mp eq)
  obtain ⟨r,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨t,rfl⟩:=Ideal.mem_span_singleton.mp hv
  exact ⟨r,t,r.property,t.property,congrArg Subtype.val l.symm⟩

open RetainedCompression (Curve ordinate view height heightCap)

/-- The actual bounded cover's untwisted obstruction space embeds in the quotient
formed by the two torus fibres and a single shared crossing. -/
theorem restriction_kernel_far (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<48) (bounded : height 164768 f≤heightCap (f.degreeOf ordinate) 164768)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) :
    (rawMap E x z).ker=coboundaries E := by
    ext u
    change rawMap E x z u=0 ↔ ∃ c:E,∀ s,IsIntegral (baseChart s) ((u.1 s:E)-c)
    rw [raw_zero]
    constructor
    · rintro ⟨v,w,iv,iw,ex,ez,node⟩
      have r:=split_of_paired_data_far f ir lo hi bounded basis root x z nx nz
        (fun s=>(u.1 s:E)) u.property (fun b=>(v b:E)) (fun b=>(w b:E))
        ⟨iv,congr_of_eq E false x _ _ ex⟩ ⟨iw,congr_of_eq E true z _ _ ez⟩
        (matched_of_eq E x z _ _ node)
      obtain ⟨c,hc⟩:=r
      exact ⟨c,fun s=>by simpa [frame] using hc s⟩
    · rintro ⟨c,hc⟩
      have ic : IsIntegral torus c := by
        have ii:=(u.1 (false,false)).property.sub (order_mono (base_torus (false,false)) (hc (false,false)))
        simpa only [sub_sub_cancel] using ii
      let ct : Tor E:=⟨c,ic⟩
      let v (j b:Bool):Tor E:=u.1 (reference j b)-ct
      have start (j:Bool) : reference j false=(false,false) := by cases j <;> rfl
      refine ⟨v false,v true,(fun b=>hc _),(fun b=>hc _),?_,?_,?_⟩
      · apply congrArg (red E false x); simp only [v,start]; abel
      · apply congrArg (red E true z); simp only [v,start]; abel
      · rfl
#print axioms restriction_kernel_far
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedSurfaceClass

end Merged6967_R6966ProofFarSurface
