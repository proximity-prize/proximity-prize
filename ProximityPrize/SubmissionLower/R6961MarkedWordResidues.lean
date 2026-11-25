import ProximityPrize.SubmissionLower.R6961RetainedAxisTransition
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import ProximityPrize.SubmissionLower.R6960RetainedTwoLineBound
import ProximityPrize.SubmissionLower.R6960MarkedWordResidues

set_option Elab.async false

-- merged module R6961RetainedLineEvaluation
section Merged_R6961RetainedLineEvaluation

noncomputable section
set_option Elab.async false
namespace Lower6961.RetainedLineEvaluation
open Polynomial Algebra Module
open scoped Polynomial
open Lower6960.TraceSpecialization (idempotent_multiple)

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra (Polynomial k) S]

omit [Algebra k S] in
/-- A nonzero idempotent of a finite free line algebra survives on every point fibre.
If it vanished, its basis coordinates would be divisible by every power of X-a. -/
private theorem idempotent_survives [Module.Free (Polynomial k) S] {u : S} (id : u^2=u) (ne : u≠0)
    (a : k) : ¬algebraMap (Polynomial k) S (Polynomial.X-C a) ∣ u := by
  classical
  rintro ⟨w,eq⟩
  let b:=Module.Free.chooseBasis (Polynomial k) S
  obtain ⟨i,hi⟩ : ∃ i, b.repr u i≠0 := by
    by_contra! no
    apply ne
    apply b.repr.injective
    apply Finsupp.ext
    intro j
    simpa using no j
  let N:=(b.repr u i).natDegree
  have power (n:ℕ) : u^(n+1)=u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,ih,←pow_two,id]
  have divides : (Polynomial.X-C a)^(N+1)∣b.repr u i := by
    refine ⟨b.repr (w^(N+1)) i,?_⟩
    have rel : u=(Polynomial.X-C a)^(N+1) • w^(N+1) := by
      calc u = u^(N+1) := (power N).symm
           _ = (algebraMap (Polynomial k) S (Polynomial.X-C a)*w)^(N+1) := congrArg (·^(N+1)) eq
           _ = _ := by rw [mul_pow,←map_pow,Algebra.smul_def]
    exact congrArg (fun p=>p i) ((congrArg b.repr rel).trans (b.repr.map_smul ..))
  have bound:=natDegree_le_of_dvd divides hi
  rw [natDegree_pow,natDegree_X_sub_C,mul_one] at bound
  omega

/-- A scalar-algebraic section on a reduced free line algebra is detected at a
single point. This allows the horizontal and vertical global sections to be charged
to the same crossing algebra even when the line fibres are reducible. -/
theorem detects_global [IsReduced S] [Module.Free (Polynomial k) S]
    (a : k) (u:S) (alg : IsIntegral k u) (vanish : algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : u=0 := by
  classical
  by_contra ne
  let B:=Algebra.adjoin k ({u}:Set S)
  let : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral alg
  let : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let x : B:= ⟨u,Algebra.self_mem_adjoin_singleton k u⟩
  have nn : ¬IsNilpotent x := by
    intro nil
    exact ne (nil.map B.val.toRingHom).eq_zero
  obtain ⟨r,id,nz⟩:=Lower6960.TraceSpecialization.idempotent_multiple x nn
  have idem : (u*(r:S))^2=u*(r:S) := congrArg Subtype.val id
  have nonzero : u*(r:S)≠0 := fun eq=>nz (Subtype.ext eq)
  exact idempotent_survives idem nonzero a (vanish.trans (dvd_mul_right ..))

#print axioms detects_global

omit [Algebra k S] in
/-- A free polynomial algebra with one reduced point fibre is itself reduced. A
nilpotent can repeatedly be divided by the point equation, since that equation
is a nonzerodivisor and its image at the point vanishes. -/
theorem reduced_of_point [Module.Free (Polynomial k) S] {D : Type*} [CommRing D] [IsReduced D]
    (a : k) (atNode : S→+*D)
    (kernel : ∀ u, atNode u=0 → algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : IsReduced S := by
  classical
  constructor
  intro u nil
  let p : (Polynomial k):=Polynomial.X-C a
  have pn : p≠0 := X_sub_C_ne_zero _
  have div (n:ℕ) : ∃ w:S, IsNilpotent w ∧ u=p^n • w := by
    induction n with
    | zero => exact ⟨u,nil,by simp⟩
    | succ n ih =>
      obtain ⟨w,nw,eq⟩:=ih
      obtain ⟨v,rel⟩:=kernel w (nw.map atNode).eq_zero
      obtain ⟨m,hm⟩:=nw
      have van : p^m • v^m=0 := by
        rw [rel,mul_pow] at hm
        rw [Algebra.smul_def,map_pow]; exact hm
      refine ⟨v,⟨m,(smul_eq_zero_iff_right (pow_ne_zero _ pn)).mp van⟩,?_⟩
      rw [eq,rel,pow_succ,mul_smul,Algebra.smul_def p v]
  let b:=Module.Free.chooseBasis (Polynomial k) S
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  by_contra ne
  have nz : b.repr u i≠0 := by simpa using ne
  let n:=(b.repr u i).natDegree
  obtain ⟨v,_,eq⟩:=div (n+1)
  have large : p^(n+1)∣b.repr u i :=
    ⟨b.repr v i,congrArg (fun q=>q i) ((congrArg b.repr eq).trans (b.repr.map_smul ..))⟩
  have bad:=natDegree_le_of_dvd large nz
  rw [natDegree_pow,show p.natDegree=1 from natDegree_X_sub_C _,mul_one] at bad
  omega

#print axioms reduced_of_point
end Lower6961.RetainedLineEvaluation

end
end Merged_R6961RetainedLineEvaluation

-- merged module R6961RetainedAxisPoint
section Merged_R6961RetainedAxisPoint
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections RetainedRestrictionTorus MonicChartProbes
open Module Submodule Algebra Polynomial
open scoped Lower6961.RetainedSurfaceClass Polynomial
open Lower6961.RetainedSurfaceClass (toCross toCross_kernel finiteX_val finiteZ_val)
open Lower6961.RetainedSurfaceClass (chartSpace)
variable (E : Type) [Field E] [Algebra ChartField E]

def atCoord (j:Bool) (x z:L) := if j then z else x
def nodeMap (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₗ[L] Crossing E x z :=
  match j with | false=>crossingX E x z | true=>crossingZ E x z
theorem through (j:Bool) (x z:L) (v:Tor E) :
    nodeMap E j x z (red E j (atCoord j x z) v)=Ideal.Quotient.mk _ v := by cases j <;> rfl

theorem onto_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) :
    Function.Surjective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false).subtype) := by
  intro w
  obtain ⟨u,hu⟩ := cross_surjective E x z nx nz w
  have s : reference j false=(false,false) := by cases j <;> rfl
  refine ⟨⟨red E j (atCoord j x z) (fromFinite E u),⟨fromFinite E u,?_,rfl⟩⟩,?_⟩
  · change IsIntegral (baseChart (reference j false)) u.val
    rw [s]; exact u.property
  · exact (through E j x z (fromFinite E u)).trans hu

theorem cut_running (j:Bool) (c:L) :
    along E j false (Polynomial.X-C c)=cut E (!j) c := by
  apply Subtype.ext
  rw [map_sub]
  change ((along E j false Polynomial.X):E)-((along E j false (C c)):E)=_
  rw [show along E j false Polynomial.X=
    (⟨algebraMap ChartField E (coordinate (!j)),isIntegral_algebraMap (x:=(⟨_,torus_coordinate (!j) false⟩:torus))⟩:Tor E)
    from eval₂_X _ _,show along E j false (C c)=algebraMap L (Tor E) c from eval₂_C _ _]
  exact (map_sub (algebraMap ChartField E) _ _).symm

private theorem coordinate_ideal (x z:L) (nx:x≠0) (nz:z≠0) (u:finiteOrder E)
    (zero : Lower6961.RetainedSurfaceClass.toCross E x z u=0) :
    ∃ a b:finiteOrder E, fromFinite E u=cut E false x*fromFinite E a+cut E true z*fromFinite E b := by
  have mem : u∈RingHom.ker (Lower6961.RetainedSurfaceClass.toCross E x z).toRingHom := RingHom.mem_ker.mpr zero
  rw [Lower6961.RetainedSurfaceClass.toCross_kernel E x z nx nz,point_kernel,Ideal.map_sup,
    Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton] at mem
  obtain ⟨_,hu,_,hv,eq⟩:=Submodule.mem_sup.mp mem
  obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp hv
  have fx : fromFinite E (algebraMap Base (finiteOrder E) (finiteX x))=cut E false x :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6961.RetainedSurfaceClass.finiteX_val x))
  have fz : fromFinite E (algebraMap Base (finiteOrder E) (finiteZ z))=cut E true z :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6961.RetainedSurfaceClass.finiteZ_val z))
  exact ⟨a,b,by rw [←eq,map_add,map_mul,map_mul,fx,fz]⟩

/-- The kernel of evaluation on the actual finite line chart consists of multiples
of its crossing coordinate. This identifies the point fibre even at the two chart boundaries. -/
theorem kernel_at_node (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:chartImage E j (atCoord j x z) false) :
    nodeMap E j x z u=0 ↔ ∃ v:chartImage E j (atCoord j x z) false,
      (u:Axis E j (atCoord j x z))=polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z))*v.val := by
  let R:=axisIdeal E j (atCoord j x z)
  let π:=Ideal.Quotient.mk R
  have fixed : π (cut E j (atCoord j x z))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have variableCut : polyMap E j (atCoord j x z) false (Polynomial.X-C (atCoord (!j) x z)) =
      π (cut E (!j) (atCoord (!j) x z)) := congrArg π (cut_running E j _)
  have origin : reference j false=(false,false) := by cases j <;> rfl
  have image (y : finiteOrder E) : π (fromFinite E y)∈chartImage E j (atCoord j x z) false := by
    refine ⟨fromFinite E y,?_,rfl⟩
    change IsIntegral (baseChart (reference j false)) y.val; rw [origin]; exact y.property
  constructor
  · intro hz
    obtain ⟨w,hw,ew⟩:=u.property
    change IsIntegral (baseChart (reference j false)) (w:E) at hw
    rw [origin] at hw
    let W:finiteOrder E:=⟨w,hw⟩
    have fw : fromFinite E W=w := rfl
    rw [←ew,through] at hz
    have zero : Lower6961.RetainedSurfaceClass.toCross E x z W=0 := hz
    obtain ⟨a,b,eq⟩:=coordinate_ideal E x z nx nz W zero
    have ed:=congrArg π eq
    rw [map_add,map_mul,map_mul,fw] at ed
    change π w=u.val at ew
    rw [ew] at ed
    cases j
    · refine ⟨⟨_,image b⟩,?_⟩
      change π (cut E false x)=0 at fixed
      rw [fixed,zero_mul,zero_add] at ed
      rw [variableCut]; exact ed
    · refine ⟨⟨_,image a⟩,?_⟩
      change π (cut E true z)=0 at fixed
      rw [fixed,zero_mul,add_zero] at ed
      rw [variableCut]; exact ed
  · rintro ⟨v,hv⟩
    obtain ⟨w,_,ew⟩:=v.property
    rw [hv,variableCut,←ew]
    change nodeMap E j x z (π (cut E (!j) (atCoord (!j) x z))*π w)=0
    rw [←map_mul]
    change nodeMap E j x z (red E j (atCoord j x z) _)=0
    rw [through E j x z, map_mul]
    have member : cut E (!j) (atCoord (!j) x z)∈axisIdeal E false x⊔axisIdeal E true z := by
      cases j
      · exact Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
      · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr member,zero_mul]

#print axioms onto_at_node
#print axioms kernel_at_node
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedAxisPoint

-- merged module R6961RetainedNativeEuler
section Merged_R6961RetainedNativeEuler
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open RetainedRestrictionTorus Module Submodule LinearMap Lower6960.LineEuler Polynomial
open scoped Lower6961.RetainedSurfaceClass Polynomial
variable (E:Type) [Field E] [Algebra ChartField E]

abbrev LineGlobals (j:Bool) (c:L) := ↥(chartImage E j c false⊓chartImage E j c true)
abbrev LineObstructions (j:Bool) (c:L) := (Axis E j c) ⧸ (chartImage E j c false⊔chartImage E j c true)

theorem native_frames [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (j:Bool) (c:L) (nc:c≠0) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c false)) ∧
      Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c true)) := by
  have fin (b:Bool) : Module.Finite (Polynomial L) (chartImage E j c b) := chart_finite E j c b
  have free (b:Bool) : Module.Free (Polynomial L) (chartImage E j c b) := chart_free E j c b
  let bf:=Module.finBasis (Polynomial L) (chartImage E j c false)
  let bi:=Module.finBasis (Polynomial L) (chartImage E j c true)
  let U:=localFreeBasis false bf (nativeMap E j c false) (native_localization E j c nc false)
  let V:=localFreeBasis true bi (nativeMap E j c true) (native_localization E j c nc true)
  have same : finrank (Polynomial L) (chartImage E j c true)=finrank (Polynomial L) (chartImage E j c false) := by
    simpa only [Fintype.card_fin] using (finrank_eq_card_basis V).symm.trans (finrank_eq_card_basis U)
  exact ⟨_,⟨bf⟩,⟨Module.finBasisOfFinrankEq (Polynomial L) _ same⟩⟩

/-- Euler's formula on the actual specialized surface order. The determinant is
computed from its finite and infinity bases, even if the fibre is a proper suborder. -/
theorem native_euler (j:Bool) (c:L) (nc:c≠0) {n : ℕ}
    (bf : Basis (Fin n) (Polynomial L) (chartImage E j c false))
    (bi : Basis (Fin n) (Polynomial L) (chartImage E j c true)) :
    let G:=freeTransition bf bi (nativeMap E j c false) (nativeMap E j c true)
      (native_localization E j c nc false) (native_localization E j c nc true)
    FiniteDimensional L (LineGlobals E j c) ∧ FiniteDimensional L (LineObstructions E j c) ∧
      ∃ d:ℤ,G.det.degree=(d:WithBot ℤ) ∧
        (finrank L (LineGlobals E j c):ℤ)-(finrank L (LineObstructions E j c):ℤ)=n+d := by
  let U:=chartImage E j c false
  let V:=chartImage E j c true
  let ff:=nativeMap E j c false
  let fi:=nativeMap E j c true
  let lf:=native_localization E j c nc false
  let li:=native_localization E j c nc true
  let G:=freeTransition bf bi ff fi lf li
  let tower:=laurent_scalar_tower E j c
  let e:Axis E j c≃ₗ[L](Fin n→Laurent L) := (localFreeBasis false bf ff lf).equivFun.restrictScalars L
  have h0 : (U⊓V).map e.toLinearMap=finiteLattice L (Fin n) ⊓ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]
    change (v∈U ∧ v∈V) ↔ _
    apply Iff.trans _ (free_global_iff bf bi ff fi lf li v).symm
    exact and_congr ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
      ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
  have h1 : (U⊔V).map e.toLinearMap=finiteLattice L (Fin n) ⊔ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply,Submodule.mem_sup]
    apply Iff.trans _ (free_boundary_iff bf bi ff fi lf li v).symm
    exact ⟨fun ⟨u,hu,w,hw,s⟩=>⟨⟨u,hu⟩,⟨w,hw⟩,s⟩,fun ⟨u,w,s⟩=>⟨u,u.property,w,w.property,s⟩⟩
  let E0 : LineGlobals E j c≃ₗ[L]H0 G := (e.submoduleMap (U⊓V)).trans (LinearEquiv.ofEq _ _ h0)
  let E1 : LineObstructions E j c≃ₗ[L]H1 G := Submodule.Quotient.equiv _ _ e h1
  have good : IsUnit G := freeTransition_unit (M:=Axis E j c) bf bi ff fi lf li
  obtain ⟨f0,f1,d,ed,index⟩:=euler_index G good
  refine ⟨FiniteDimensional.of_injective E0.toLinearMap E0.injective,
    FiniteDimensional.of_injective E1.toLinearMap E1.injective,d,ed,?_⟩
  rw [E0.finrank_eq,E1.finrank_eq]
  simpa only [Fintype.card_fin] using index

#print axioms native_frames
#print axioms native_euler
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedNativeEuler

-- merged module R6961RetainedGlobalEvaluation
section Merged_R6961RetainedGlobalEvaluation
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections RetainedRestrictionTorus
open Module Submodule LinearMap Algebra Polynomial Lower6960.LineEuler
open scoped Lower6961.RetainedSurfaceClass Polynomial
open Lower6961.RetainedSurfaceClass (chartSpace)
variable (E:Type) [Field E] [Algebra ChartField E]

def imageAlg (j:Bool) (c:L) (b:Bool) : Subalgebra L (Axis E j c) where
  carrier:=(chartImage E j c b : Set _)
  zero_mem':=(chartImage E j c b).zero_mem
  add_mem':=(chartImage E j c b).add_mem
  one_mem':=by
    change (1:Axis E j c)∈chartImage E j c b
    exact ⟨1,isIntegral_one,map_one (Ideal.Quotient.mk _)⟩
  mul_mem':=by
    rintro _ _ ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u*v,IsIntegral.mul hu hv,map_mul (Ideal.Quotient.mk _) _ _⟩
  algebraMap_mem' r:=by
    change algebraMap L (Axis E j c) r∈chartImage E j c b
    exact ⟨algebraMap L (Tor E) r,
      isIntegral_algebraMap (A:=E) (x:=(⟨_,chart_constant _ r⟩:baseChart (reference j b))),rfl⟩

def imagePoly (j:Bool) (c:L) (b:Bool) : (Polynomial L)→+*imageAlg E j c b :=
  (polyMap E j c b).codRestrict (imageAlg E j c b) (fun p=>by
    letI : Module (Polynomial L) (Axis E j c) := Module.compHom _ (polyMap E j c b)
    have h:1∈polyImage E j c b := (imageAlg E j c b).one_mem
    have v:=(polyImage E j c b).smul_mem p h
    change polyMap E j c b p * 1∈_ at v
    rw [mul_one] at v
    exact v)
scoped instance imagePolyAlgebra (j:Bool) (c:L) (b:Bool) :
    Algebra (Polynomial L) (imageAlg E j c b) :=
  RingHom.toAlgebra' (R:=(Polynomial L)) (S:=imageAlg E j c b) (imagePoly E j c b)
    (fun r x => mul_comm (imagePoly E j c b r) x)

private def ringBasis (j:Bool) (c:L) (b:Bool) {n:ℕ}
    (B : Basis (Fin n) (Polynomial L) (chartImage E j c b)) : Basis (Fin n) (Polynomial L) (imageAlg E j c b) :=
  let e : chartImage E j c b≃ₗ[(Polynomial L)]imageAlg E j c b :=
   { toFun:=fun v=>⟨v,v.property⟩
     invFun:=fun v=>⟨v,v.property⟩
     left_inv:=fun _=>rfl
     right_inv:=fun _=>rfl
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
  B.map e

def nodeRing (j:Bool) (x z:L) : Axis E j (atCoord j x z) →ₐ[L] Crossing E x z :=
  match j with
  | false=>Ideal.Quotient.factorₐ L (show axisIdeal E false x ≤ _⊔axisIdeal E true z from le_sup_left)
  | true=>Ideal.Quotient.factorₐ L (show axisIdeal E true z ≤ axisIdeal E false x⊔_ from le_sup_right)

theorem eval_subtype (j:Bool) (x z:L) (u:chartImage E j (atCoord j x z) false) :
    nodeRing E j x z u.val=nodeMap E j x z u.val := by cases j <;> rfl

theorem vanishing_divides (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0)
    (u:imageAlg E j (atCoord j x z) false) (h:nodeRing E j x z u.val=0) :
    algebraMap (Polynomial L) (imageAlg E j (atCoord j x z) false) (Polynomial.X-C (atCoord (!j) x z)) ∣ u := by
  let w : chartImage E j (atCoord j x z) false:=⟨u.val,u.property⟩
  obtain ⟨v,eq⟩:=(kernel_at_node E j x z nx nz w).mp ((eval_subtype E j x z w) ▸ h)
  exact ⟨⟨v.val,v.property⟩,Subtype.ext eq⟩

/-- Global sections form a finite algebra. On the actual affine chart, their
evaluation is injective even if the selected fibre has several components. -/
theorem global_eval_injective (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)]
    [FiniteDimensional L (LineGlobals E j (atCoord j x z))] {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    Function.Injective ((nodeMap E j x z).comp (chartImage E j (atCoord j x z) false⊓
      chartImage E j (atCoord j x z) true).subtype) := by
  let c:=atCoord j x z
  let R:=imageAlg E j c false
  let U:=imageAlg E j c false⊓imageAlg E j c true
  let e : U≃ₗ[L]LineGlobals E j c :=
    { toFun:=fun v=>⟨v,v.property⟩,invFun:=fun v=>⟨v,v.property⟩
      left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
  have : FiniteDimensional L U := FiniteDimensional.of_injective e.toLinearMap e.injective
  let into : U→ₐ[L] R:=Subalgebra.inclusion inf_le_left
  let evaluate:= (nodeRing E j x z).toRingHom.comp R.subtype
  have free : Module.Free (Polynomial L) R := Module.Free.of_basis (ringBasis E j c false bf)
  have redRing : IsReduced R := RetainedLineEvaluation.reduced_of_point (S:=R) (D:=Crossing E x z)
    (atCoord (!j) x z) evaluate (vanishing_divides E j x z nx nz)
  intro u v eq
  let d:=e.symm (u-v)
  have alg : IsIntegral L (into d) := (Algebra.IsIntegral.isIntegral d).map into
  have van : evaluate (into d)=0 := by
    change nodeRing E j x z (u.val-v.val)=0
    rw [map_sub,sub_eq_zero]
    cases j <;> exact eq
  have zero:=RetainedLineEvaluation.detects_global (atCoord (!j) x z) (into d) alg
    (vanishing_divides E j x z nx nz _ van)
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact congrArg (fun w : R=>(w:Axis E j c)) zero

#print axioms global_eval_injective
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedGlobalEvaluation

-- merged module R6961RetainedSurfaceDimension
section Merged_R6961RetainedSurfaceDimension
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open Module Submodule LinearMap Polynomial Lower6960.LineEuler
open scoped Lower6961.RetainedSurfaceClass Polynomial
open Lower6961.RetainedSurfaceClass (nodeRing eval_subtype)
open Lower6961.RetainedSurfaceClass (cut_running through)
open Lower6961.RetainedSurfaceClass (evalX evalZ)
open Lower6960.RetainedTwoLineBound (diagonal image)
variable (E:Type) [Field E] [Algebra ChartField E]

theorem point_polynomial (j:Bool) (x z:L) (p:(Polynomial L)) :
    Lower6961.RetainedSurfaceClass.nodeRing E j x z (polyMap E j (atCoord j x z) false p) =
      algebraMap L (Crossing E x z) (p.eval (atCoord (!j) x z)) := by
  let a:=atCoord (!j) x z
  let f := (Lower6961.RetainedSurfaceClass.nodeRing E j x z).toRingHom.comp (polyMap E j (atCoord j x z) false)
  let g := (algebraMap L (Crossing E x z)).comp (evalRingHom a)
  have co (r:L) : f (C r)=algebraMap L _ r := by
    have eq : along E j false (C r)=algebraMap L (Tor E) r := eval₂_C _ _
    change Lower6961.RetainedSurfaceClass.nodeRing E j x z (Ideal.Quotient.mk _ (along E j false (C r)))=_
    rw [eq]
    exact (Lower6961.RetainedSurfaceClass.nodeRing E j x z).commutes r
  have eq : f=g := by
    apply Polynomial.ringHom_ext
    · intro r; simpa [g] using co r
    · have van : f (Polynomial.X-C a)=0 := by
        have e:=Lower6961.RetainedSurfaceClass.cut_running E j a
        change Lower6961.RetainedSurfaceClass.nodeRing E j x z (Ideal.Quotient.mk _ (along E j false (Polynomial.X-C a)))=0
        rw [e]
        cases j
        · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
        · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
      rw [map_sub,co,sub_eq_zero] at van
      simpa [g] using van
  exact DFunLike.congr_fun eq p

theorem node_rank_le (j:Bool) (x z:L) (nx:x≠0) (nz:z≠0) {n:ℕ}
    (bf:Basis (Fin n) (Polynomial L) (chartImage E j (atCoord j x z) false)) :
    finrank L (Crossing E x z)≤n := by
  let c:=atCoord j x z
  let F:=(nodeMap E j x z).comp (chartImage E j c false).subtype
  let v (i:Fin n):=F (bf i)
  let generate := (Pi.basisFun L (Fin n)).constr L v
  have action (r:(Polynomial L)) (u:chartImage E j c false) :
      F (r • u) = (r.eval (atCoord (!j) x z)) • F u := by
    change nodeMap E j x z (polyMap E j c false r*u.val)=_
    have eq:=map_mul (Lower6961.RetainedSurfaceClass.nodeRing E j x z) (polyMap E j c false r) u.val
    rw [point_polynomial] at eq
    cases j <;> exact eq
  have onto : Function.Surjective generate := by
    intro y
    obtain ⟨u,eu⟩:=onto_at_node E j x z nx nz y
    refine ⟨fun i=>(bf.repr u i).eval (atCoord (!j) x z),?_⟩
    have rep:=congrArg F (bf.sum_repr u)
    rw [map_sum] at rep
    simp_rw [action] at rep
    simpa [generate,Basis.constr_apply_fintype,v] using rep.trans eu
  have bound:=LinearMap.finrank_le_finrank_of_surjective (f:=generate) onto
  simpa only [Module.finrank_pi,Fintype.card_fin] using bound

def transition (j:Bool) (c:L) (nc:c≠0) {n:ℕ} (bf:Basis (Fin n) (Polynomial L) (chartImage E j c false))
    (bi:Basis (Fin n) (Polynomial L) (chartImage E j c true)) : Matrix (Fin n) (Fin n) (Laurent L) := by
  let : Module (Laurent L) (Axis E j c) := (axisAlgebra E j c).toModule
  exact freeTransition (M:=Axis E j c) bf bi (nativeMap E j c false) (nativeMap E j c true)
    (native_localization E j c nc false) (native_localization E j c nc true)

/-- Bound the very quotient through which the surface restricts. The two determinant
degrees come from the original surface's specialized line orders. -/
theorem paired_bound (x z:L) (nx:x≠0) (nz:z≠0) [IsReduced (Crossing E x z)]
    [FiniteDimensional L (Crossing E x z)] {m n:ℕ}
    (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
    (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)) :
    FiniteDimensional L (Paired E x z) ∧ ∃ s t:ℕ,
      (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
      (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
      finrank L (Paired E x z)≤s+t := by
  obtain ⟨fx,f1x,tx,xt,ex⟩:=native_euler E false x nx xf xi
  obtain ⟨fz,f1z,tz,zt,ez⟩:=native_euler E true z nz zf zi
  let C:=Crossing E x z
  let dx:=difference E false x
  let dz:=difference E true z
  let exv:=Lower6961.RetainedSurfaceClass.evalX E x z
  let ezv:=Lower6961.RetainedSurfaceClass.evalZ E x z
  have rx : dx.range=chartImage E false x false⊔chartImage E false x true := Lower6960.RetainedTwoLineBound.image ..
  have rz : dz.range=chartImage E true z false⊔chartImage E true z true := Lower6960.RetainedTwoLineBound.image ..
  have : FiniteDimensional L ((Axis E false x) ⧸ dx.range) := rx ▸ f1x
  have : FiniteDimensional L ((Axis E true z) ⧸ dz.range) := rz ▸ f1z
  obtain ⟨finite,bound⟩:=Lower6960.RetainedNodalIndex.dimension dx dz exv ezv
  let W:=dx.ker.map exv ⊔ dz.ker.map ezv
  have : FiniteDimensional L C := (inferInstance : FiniteDimensional L (Crossing E x z))
  have : FiniteDimensional L W := FiniteDimensional.of_injective
    (W.subtype : W→ₗ[L]C) Subtype.val_injective
  let hz:LineGlobals E true z→ₗ[L] C := (nodeMap E true x z).comp (chartImage E true z false⊓chartImage E true z true).subtype
  have : FiniteDimensional L (LineGlobals E true (atCoord true x z)) := fz
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fx
  have injz :=global_eval_injective E true x z nx nz zf
  have lift (v:LineGlobals E true z) : hz v∈W := Submodule.mem_sup_right
    ⟨(Lower6960.RetainedTwoLineBound.diagonal _ _ v).val,(Lower6960.RetainedTwoLineBound.diagonal _ _ v).property,rfl⟩
  let into:=hz.codRestrict W lift
  have covered:=LinearMap.finrank_le_finrank_of_injective (f:=into)
    (fun u v eq=>injz (congrArg (fun w:W=>(w:C)) eq))
  have hx:=LinearMap.finrank_le_finrank_of_injective (global_eval_injective E false x z nx nz xf)
  have hz':=LinearMap.finrank_le_finrank_of_injective injz
  have rankx:=node_rank_le E false x z nx nz xf
  have rankz:=node_rank_le E true x z nx nz zf
  rw [rx,rz] at bound
  change finrank L (Paired E x z)+finrank L W ≤finrank L (LineObstructions E false x)+finrank L (LineObstructions E true z)+finrank L C at bound
  change finrank L (LineGlobals E false x)≤finrank L C at hx
  change finrank L (LineGlobals E true z)≤finrank L C at hz'
  change finrank L (LineGlobals E true z)≤finrank L W at covered
  change finrank L C≤m at rankx
  change finrank L C≤n at rankz
  let s:=(-tz).toNat
  let t:=(-tx).toNat
  have ds:tz= -(s:ℤ) := by dsimp [s]; omega
  have dt:tx= -(t:ℤ) := by dsimp [t]; omega
  exact ⟨finite,s,t,dt ▸ xt,ds ▸ zt,by omega⟩

#print axioms paired_bound

open RetainedCompression (Curve ordinate view height heightCap MarkedBand)

/-- The first-cohomology bound for the original retained factor. The kernel equality
identifies the range with its transition classes modulo ordinary coboundaries. -/
theorem actual_surface_budget (B : MarkedBand) (f : Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
        (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)),
      (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
      (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
      (rawMap E x z).ker=coboundaries E ∧ FiniteDimensional L (Paired E x z) ∧
      finrank L (Paired E x z)≤s+t := by
  have : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo (hi.trans B.small_E) basis root
  obtain ⟨x,z,nx,nz,⟨B_bas⟩,red⟩:=actual_crossing E f ir lo (hi.trans B.small_E) basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B_bas
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,count⟩:=paired_bound E x z nx nz xf xi zf zi
  exact ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,
    restriction_kernel E B f ir lo hi bounded basis root x z nx nz,finite,count⟩

#print axioms actual_surface_budget
end Lower6961.RetainedSurfaceClass

end
end Merged_R6961RetainedSurfaceDimension

-- merged module R6961RetainedTwistedRestriction
section Merged_R6961RetainedTwistedRestriction
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Lower6961.RetainedTwistedRestriction
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent MonicChartProbes
open RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Lower6961.RetainedSurfaceClass Lower6961.MonicChartProbes Polynomial
open Lower6961.RetainedRestrictionTorus (frame_integral)
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E
def fr (s:Chart) : E := ι (localFrame s false)
abbrev Regular (s:Chart) (i:ℕ) (v:E) := IsIntegral (baseChart s) ((fr s)⁻¹^i*v)
abbrev Over (s t:Chart) (i:ℕ) (v:E) := IsIntegral (overlapRing s t) ((fr s)⁻¹^i*v)
private theorem fn (s:Chart) : (fr s:E)≠0 :=
  (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)
private theorem baseReg {s:Chart} {v:ChartField} (h:v∈baseChart s) : IsIntegral (baseChart s) (ι v:E) :=
  isIntegral_algebraMap (x:=(⟨v,h⟩:baseChart s))
private theorem invFrame (s:Chart) : (localFrame s false)⁻¹∈baseChart s := by
  by_cases i:s.1=true
  · have h:chartCoordinate s.1 RatFunc.X∈baseChart s:=Subring.subset_closure (Or.inr (Or.inl rfl))
    simpa [localFrame,coordinate,axisBit,chartCoordinate,i] using h
  · simp [localFrame,axisBit,i]

private theorem ratio (s t:Chart) : localFrame t false/localFrame s false∈baseChart s := by
  have h:chartCoordinate s.1 RatFunc.X∈baseChart s:=Subring.subset_closure (Or.inr (Or.inl rfl))
  by_cases a:s.1=true <;> by_cases b:t.1=true <;>
    simp [localFrame,coordinate,axisBit,a,b,RatFunc.X_ne_zero] at * <;>
    simpa [chartCoordinate,a] using h

theorem regular_on_overlap (s t:Chart) (i:ℕ) (v:E) (ok:Regular t i v) : Over s t i v := by
  have r:= (order_mono (into_cleared _ (edge s t)) (baseReg (E:=E) (ratio s t))).pow i
  have a:=r.mul (order_mono (chart_cover s t) ok)
  have eq : ι (localFrame t false/localFrame s false)^i * ((fr t)⁻¹^i*v)=(fr s)⁻¹^i*v := by
    rw [map_div₀]; change ((fr t)/(fr s))^i*(((fr t)⁻¹)^i*v)=_
    rw [div_eq_mul_inv,mul_pow]
    calc _ = ((fr t)^i*((fr t)⁻¹)^i)*(((fr s)⁻¹)^i*v) := by ring
         _ = _ := by rw [←mul_pow,mul_inv_cancel₀ (fn t),one_pow,one_mul]
  rwa [eq] at a

theorem cancel_equation [FiniteDimensional ChartField E] (s t:Chart) (a:baseChart s) (an:a≠0)
    (cop : IsRelPrime a (edge s (opposite s))) (y:E)
    (tw : IsIntegral (overlapRing s t) (algebraMap (baseChart s) E a*y))
    (yes : IsIntegral torus y) : IsIntegral (overlapRing s t) y := by
  let A:=baseChart s
  let : UniqueFactorizationMonoid A := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let g:=edge s (opposite s); let h:=edge s t; let f:=algebraMap A E
  obtain ⟨n,hn⟩:=clear_torus s y yes
  obtain ⟨m,hm⟩:=localize_integral A _ h (edge_ne s t) le_rfl _ tw
  change IsIntegral A (f g^n*y) at hn
  change IsIntegral A (f h^m*(f a*y)) at hm
  have gn : g≠0 := fun eq=>edge_ne s (opposite s) (congrArg Subtype.val eq)
  have clean : IsIntegral A (f h^m*y) := by
    apply Lower6960.NormalizedFiber.integral_of_coprime_clearings ChartField an (pow_ne_zero _ gn) cop.pow_right _
    · change IsIntegral A (f a*(f h^m*y)); convert hm using 1 <;> ring
    · change IsIntegral A (f (g^n)*(f h^m*y))
      have v:=(isIntegral_algebraMap (A:=E) (x:=h^m)).mul hn
      convert v using 1 <;> simp only [map_pow] <;> ring
  let T:=overlapRing s t
  have hi : (boundary s t)⁻¹∈T := ⟨1,by simp [edge_ne]⟩
  have inv : IsIntegral T ((f h)⁻¹) := by
    change IsIntegral T (ι (boundary s t))⁻¹
    rw [←map_inv₀]; exact isIntegral_algebraMap (x:=(⟨_,hi⟩:T))
  have hnz : f h≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (edge_ne s t)
  simpa only [←mul_assoc,←mul_pow,inv_mul_cancel₀ hnz,one_pow,one_mul] using
    (inv.pow m).mul (order_mono (into_cleared A h) clean)

private theorem axis_cancel [FiniteDimensional ChartField E] (s t:Chart) (x:L) (nx:x≠0) (y:E)
    (tw : IsIntegral (overlapRing s t) (algebraMap (baseChart s) E (xcut s x)*y))
    (yes : IsIntegral torus y) : IsIntegral (overlapRing s t) y := by
  have : UniqueFactorizationMonoid (baseChart s) := (planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  apply cancel_equation s t (xcut s x) _ _ y tw yes
  · intro h
    have eq:=congrArg (fun p:baseChart s=>(p:ChartField)) h
    exact (div_ne_zero (divisor_ne false x) (localFrame_ne s false)) ((xcut_value s x).symm.trans eq)
  · exact (IsRelPrime.mul_right_iff.mp (boundary_rel s x 1 nx one_ne_zero)).1.symm

/-- A twist-i transition that splits on the abscissa line is the sum of a
twist-i boundary and the line equation times a twist-(i-1) transition. -/
theorem descend_line [FiniteDimensional ChartField E] (i:ℕ) (x:L) (nx:x≠0) (u:Chart→E)
    (reg:∀ s t, Over s t (i+1) (u s-u t)) (v:Bool→E) (data:LineData false x u v) :
    ∃ w l:Chart→E, (∀ s,IsIntegral torus (w s)) ∧ (∀ s,Regular s (i+1) (l s)) ∧
      (∀ s t,Over s t i (w s-w t)) ∧ ∀s, u s-ι (divisor false x)*w s=l s+(u (false,false)-v false) := by
  let c:=u (false,false)-v false
  let D:=ι (divisor false x)
  have dn : D≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne false x)
  have locals (s:Chart) : ∃ l:E, Regular s (i+1) l ∧ Congruent false x (u s-c) l := by
    let t:=reference false s.2
    have same : axisBit s (!false)=axisBit t (!false) := rfl
    let candidate:=u s-u t+v s.2
    have re: IsIntegral (overlapRing s t) ((fr s)⁻¹^(i+1)*candidate) := by
      rw [show (fr s)⁻¹^(i+1)*candidate=(fr s)⁻¹^(i+1)*(u s-u t)+(fr s)⁻¹^(i+1)*v s.2 by dsimp [candidate];ring]
      apply (reg s t).add
      have inv:IsIntegral (baseChart s) ((fr s:E)⁻¹) := by rw [fr,←map_inv₀];exact baseReg (invFrame s)
      exact ((order_mono (into_cleared _ (edge s t)) inv).pow _).mul (order_mono (chart_cover s t) (data.1 s.2))
    obtain ⟨q,iq,r,ir,eq⟩:=line_representative false x nx s t same _ re
    let l:=fr s^(i+1)*q
    have cancel : (fr s:E)⁻¹^(i+1)*fr s^(i+1)=1 := by rw [←mul_pow,inv_mul_cancel₀ (fn s),one_pow]
    have cg : Congruent false x candidate l := by
      refine ⟨fr s^(i+1)*r,((Lower6961.RetainedRestrictionTorus.frame_integral s false).1.pow _).mul ir,?_⟩
      have zz := congrArg (fun h:E=>fr s^(i+1)*h) eq
      change fr s^(i+1)*((fr s)⁻¹^(i+1)*candidate-q)=fr s^(i+1)*(ι (divisor false x)*r) at zz
      dsimp only [l]
      rw [mul_sub,←mul_assoc,mul_comm (fr s^(i+1)) _,cancel,one_mul] at zz
      rw [zz]; ring
    have atref : Congruent false x (u (false,false)-u t) (v false-v s.2) := by
      cases h:s.2
      · have e:t=(false,false) := by simp [t,reference,h]
        rw [e,sub_self,sub_self]; exact Congruent.refl _ _ _
      · simpa only [t,h] using data.2
    obtain ⟨r',ir',er⟩:=atref.symm
    refine ⟨l,?_,Congruent.trans (v:=candidate) ⟨r',ir',?_⟩ cg⟩
    · change IsIntegral _ ((fr s)⁻¹^(i+1)*(fr s^(i+1)*q)); rw [←mul_assoc,cancel,one_mul]; exact iq
    · rw [←er]; dsimp only [candidate,c]; abel
  choose l il coef icoef val using locals
  refine ⟨coef,l,icoef,il,fun s t=>?_,fun s=>by rw [←val]; dsimp [c]; abel⟩
  have residual : (u s-u t)-(l s-l t)=D*(coef s-coef t) := by
    rw [mul_sub]; change _=ι (divisor false x)*coef s-ι (divisor false x)*coef t
    rw [←val,←val]; abel
  have here:=order_mono (into_cleared _ (edge s t)) (il s)
  have both: IsIntegral (overlapRing s t) ((fr s)⁻¹^(i+1)*((u s-u t)-(l s-l t))) := by
    rw [mul_sub,mul_sub _ (l s) (l t)]
    exact (reg s t).sub (here.sub (regular_on_overlap s t _ _ (il t)))
  apply axis_cancel s t x nx _
  · have cut : algebraMap (baseChart s) E (xcut s x)=D/fr s := by
      change ι (xcut s x:ChartField)=_;rw [xcut_value,map_div₀];rfl
    rw [residual,pow_succ] at both
    rw [cut,div_eq_mul_inv]
    convert both using 1 <;> ring
  · have inv:IsIntegral torus (fr s:E)⁻¹ := by rw [fr,←map_inv₀];exact isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).2⟩:torus))
    exact (inv.pow _).mul ((icoef s).sub (icoef t))

#print axioms descend_line
end Lower6961.RetainedTwistedRestriction

end
end Merged_R6961RetainedTwistedRestriction

-- merged module R6961RetainedTwistedBudget
section Merged_R6961RetainedTwistedBudget
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedTwistedRestriction
open K1_14 (L)
open Lower6960.ChartSections (Chart)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
open Lower6961.RetainedSurfaceClass (chartSpace congr_of_eq)
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def charts (i:ℕ) : Submodule L (Chart→Tor E) where
  carrier:={u | ∀ s t,Over s t i ((u s:E)-(u t:E))}
  zero_mem':=fun s t=>by simpa [Over] using (isIntegral_zero (R:=overlapRing s t) (B:=E))
  add_mem' {u v} hu hv s t:=by
    change IsIntegral _ (_*(((u s:E)+v s)-((u t:E)+v t)))
    convert (hu s t).add (hv s t) using 1 <;> ring
  smul_mem' r u hu s t:=by
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u s:E)-ι (constants r)*(u t:E)))
    have scalar:IsIntegral (overlapRing s t) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))
    convert scalar.mul (hu s t) using 1 <;> ring

def trivial (i:ℕ) : Submodule L (charts E i) where
  carrier:={u | ∃c:E,∀s,Regular s i ((u.1 s:E)-c)}
  zero_mem':=⟨0,fun s=>by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))⟩
  add_mem' {u v} hu hv:=by
    obtain ⟨a,ha⟩:=hu;obtain ⟨b,hb⟩:=hv
    refine ⟨a+b,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(((u.1 s:E)+v.1 s)-(a+b)))
    convert (ha s).add (hb s) using 1 <;> ring
  smul_mem' r u hu:=by
    obtain ⟨a,ha⟩:=hu; refine ⟨ι (constants r)*a,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u.1 s:E)-ι (constants r)*a))
    have scalar : IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    convert scalar.mul (ha s) using 1 <;> ring

private def shift (i:ℕ) (x:L) : charts E i →ₗ[L] charts E (i+1) where
  toFun u:=⟨fun s=>cut E false x*u.1 s, fun s t=>by
    have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
      have p : IsIntegral (baseChart s) (algebraMap (baseChart s) E (xcut s x)):=isIntegral_algebraMap
      change IsIntegral (baseChart s) (ι (xcut s x:ChartField)) at p
      rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
    change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*(u.1 t:E)))
    have loc : IsIntegral (overlapRing s t) (ι (divisor false x)*(fr s:E)⁻¹) :=
      order_mono (into_cleared _ (edge s t)) d
    convert loc.mul (u.property s t) using 1 <;> rw [pow_succ] <;> ring⟩
  map_add' a b:=by apply Subtype.ext; funext s; exact mul_add _ _ _
  map_smul' r a:=by
    apply Subtype.ext; funext s; apply Subtype.ext
    change ι (divisor false x)*(ι (constants r)*(a.1 s:E))=ι (constants r)*(ι (divisor false x)*(a.1 s:E))
    ring

private def lineMap (i:ℕ) (x:L) : charts E i→ₗ[L] LineObstructions E false x :=
  let ev (s:Chart) : (Chart→Tor E) →ₗ[L] Tor E := LinearMap.proj s
  let values := ev (false,false)-ev (false,true)
  (chartImage E false x false⊔chartImage E false x true).mkQ.comp
    ((red E false x).comp (values.comp (charts E i).subtype))

abbrev Budget (i n:ℕ) := Lower6960.RetainedCodimension.Fits (k:=L) (U:=↥(charts E i)) (trivial E i) n

theorem budget_subspace {J:Type} [Fintype J] (i n:ℕ) (H:Budget E i n)
    (f:(J→L) →ₗ[L] charts E i) :
    ∃ D:Submodule L (J→L),finrank L (J→L)≤n+finrank L D ∧
      ∀v:D,∃c:E,∀s,Regular s i (((f v.val).val s:E)-c) := by
  exact @Lower6960.RetainedCodimension.large_subspace L (J→L) ↥(charts E i) inferInstance inferInstance
    inferInstance (charts E i).addCommGroup (charts E i).module inferInstance
    (trivial E i) f n H

private theorem shift_trivial (i:ℕ) (x:L) : trivial E i ≤ (trivial E (i+1)).comap (shift E i x) := by
  rintro u ⟨c,hc⟩
  refine ⟨ι (divisor false x)*c,fun s=>?_⟩
  have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
    have p : IsIntegral (baseChart s) (ι (xcut s x:ChartField):E) := isIntegral_algebraMap (x:=xcut s x)
    rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*c))
  convert d.mul (hc s) using 1 <;> rw [pow_succ] <;> ring

theorem grow [FiniteDimensional ChartField E] (i:ℕ) (x:L) (nx:x≠0)
    [FiniteDimensional L (LineObstructions E false x)] {n t:ℕ}
    (previous:Budget E i n)
    (width:finrank L (LineObstructions E false x)≤t) :
    Budget E (i+1) (n+t) := by
  apply Lower6960.RetainedCodimension.step (k:=L) (U:=↥(charts E i)) (V:=↥(charts E (i+1))) (W:=LineObstructions E false x)
    _ _ (shift E i x) (lineMap E (i+1) x) (shift_trivial E i x) _ previous width
  intro u hu
  change Submodule.Quotient.mk (p:=chartImage E false x false⊔chartImage E false x true)
    (red E false x (u.1 (false,false)-u.1 (false,true)))=0 at hu
  have res := (Submodule.Quotient.mk_eq_zero _).mp hu
  obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp res
  let reps (j:Bool):E:=if j then -(b:E) else a
  have data:LineData false x (fun s=>(u.1 s:E)) reps := by
    refine ⟨fun j=>?_,?_⟩
    · cases j
      · exact ha
      · exact (show IsIntegral (baseChart (reference false true)) (b:E) from hb).neg
    · have e : red E false x (u.1 (false,false)-u.1 (false,true))=red E false x (a+b) :=
        eq.symm.trans (map_add ..).symm
      change Congruent false x ((u.1 (false,false):E)-u.1 (false,true)) ((a:E)- -(b:E))
      rw [sub_neg_eq_add]
      exact Lower6961.RetainedSurfaceClass.congr_of_eq E false x _ _ e
  obtain ⟨w,l,iw,lr,wr,eq⟩:=descend_line i x nx (fun s=>(u.1 s:E)) u.property reps data
  let y:charts E i:=⟨fun s=>⟨w s,iw s⟩,wr⟩
  refine ⟨y,u.1 (false,false)-reps false,fun s=>?_⟩
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(((u.1 s:E)-ι (divisor false x)*w s)-((u.1 (false,false):E)-reps false)))
  rw [eq,add_sub_cancel_right]
  exact lr s

open RetainedCompression (Curve ordinate view height heightCap MarkedBand)

theorem initial (B : MarkedBand) (f : Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<B.maxOrd)
    (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [FiniteDimensional L (Paired E x z)] {b:ℕ}
    (size:finrank L (Paired E x z)≤b) : Budget E 0 b := by
  have spaces:charts E 0=potentials E := by
    ext u; change (∀s t,Over s t 0 _ )↔_
    simp only [Over,pow_zero,one_mul]; rfl
  let e:=LinearEquiv.ofEq _ _ spaces
  let f₀:=(rawMap E x z).comp e.toLinearMap
  apply Lower6960.RetainedCodimension.from_map f₀ _ _ size
  ext u
  change e u∈(rawMap E x z).ker ↔ ∃ c:E,∀s, Regular s 0 ((u.1 s:E)-c)
  rw [restriction_kernel E B f ir lo hi bounded basis root x z nx nz]
  simp only [Regular,pow_zero,one_mul]; rfl

#print axioms grow
#print axioms initial

/-- Uniform surface bound for every positive abscissa twist of the same actual
factor. The degrees s,t are measured on its own two specialized chart orders. -/
theorem actual_all_twists (B : MarkedBand) (f : Curve (Polynomial L)) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<B.maxOrd)
    (bounded:height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial MonicChart.Scalar) ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) (Polynomial L) (chartImage E false x false)) (xi:Basis (Fin m) (Polynomial L) (chartImage E false x true))
        (zf:Basis (Fin n) (Polynomial L) (chartImage E true z false)) (zi:Basis (Fin n) (Polynomial L) (chartImage E true z true)),
        (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
        (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
        Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧ IsReduced (Crossing E x z) ∧
        ∀ i:ℕ, Budget E i (s+(i+1)*t) := by
  have : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo (hi.trans B.small_E) basis root
  obtain ⟨x,z,nx,nz,⟨B_bas⟩,red⟩:=actual_crossing E f ir lo (hi.trans B.small_E) basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B_bas
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,base⟩:=paired_bound E x z nx nz xf xi zf zi
  obtain ⟨fg,fo,d,ed,index⟩:=native_euler E false x nx xf xi
  have de : d= -(t:ℤ) := WithBot.coe_injective (ed.symm.trans dt)
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fg
  have inject:=global_eval_injective E false x z nx nz xf
  have eRank := LinearMap.finrank_le_finrank_of_injective inject
  change finrank L (LineGlobals E false x)≤finrank L (Crossing E x z) at eRank
  have mrank:=node_rank_le E false x z nx nz xf
  have line : finrank L (LineObstructions E false x)≤t := by omega
  refine ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B_bas⟩,red,fun i=>?_⟩
  induction i with
  | zero => simpa only [zero_add,one_mul] using initial E B f ir lo hi bounded basis root x z nx nz base
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,Nat.add_assoc] using grow E i x nx ih line

#print axioms actual_all_twists
end Lower6961.RetainedTwistedRestriction

end
end Merged_R6961RetainedTwistedBudget

-- merged module R6961MarkedPrincipalParts
section Merged_R6961MarkedPrincipalParts

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open RetainedTwistedRestriction RetainedSurfaceClass Module Submodule LinearMap Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass
open Lower6961.RetainedRestrictionTorus (frame_integral)
variable {E:Type} [Field E] [Algebra ChartField E] {J:Type} [Fintype J]
local notation "ι" => algebraMap ChartField E

scoped instance constantFieldAlgebra (E:Type) [Field E] [Algebra ChartField E] : Algebra L E :=
  ((algebraMap ChartField E).comp constants).toAlgebra
open scoped Lower6961.MarkedEvaluation

def principalValue (p:J→Chart→E) (s:Chart) : (J→L) →ₗ[L] E :=
  (Pi.basisFun L J).constr L (fun j=>p j s)

private def regularSpace (i:ℕ) (s:Chart) : Submodule L E where
  carrier:={v|Regular s i v}
  zero_mem':=by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))
  add_mem' {u v} a b:=by change IsIntegral _ (_*(u+v)); rw [mul_add];exact a.add b
  smul_mem' r v a:=by
    have ci:IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*v))
    rw [mul_left_comm]; exact ci.mul a

private theorem anchored (i:ℕ) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ family : (J→L) →ₗ[L] charts E i, ∀ v s,
      ((family v).val s:E)=principalValue p s v-principalValue p (false,false) v := by
  classical
  let a:Chart:=(false,false)
  have regular (j:J) (s:Chart) : IsIntegral torus (p j s-p j a) := by
    have m:=order_mono (to_torus s a) (compatible j s a)
    have inv:= (Lower6961.RetainedRestrictionTorus.frame_integral (E:=E) s false).1.pow i
    have h:=inv.mul m
    change IsIntegral torus (fr s^i*((fr s)⁻¹^i*(p j s-p j a))) at h
    simpa only [←mul_assoc,←mul_pow,mul_inv_cancel₀
      ((map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)),one_pow,one_mul,fr] using h
  let transition (j:J) : charts E i := ⟨fun s=>⟨_,regular j s⟩,fun s t=>by
    change Over s t i ((p j s-p j a)-(p j t-p j a)); rw [sub_sub_sub_cancel_right]; exact compatible j s t⟩
  let family:=(Pi.basisFun L J).constr L transition
  let ev (s:Chart) : charts E i→ₗ[L]E :=
    {toFun:=fun v=>(v.val s:E),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
  have identity (s:Chart) : (ev s).comp family=principalValue p s-principalValue p a := by
    apply (Pi.basisFun L J).ext
    intro j
    rw [LinearMap.comp_apply,LinearMap.sub_apply]
    change ev s (((Pi.basisFun L J).constr L transition) _) =
      ((Pi.basisFun L J).constr L (fun j=>p j s)) _ - ((Pi.basisFun L J).constr L (fun j=>p j a)) _
    simp only [Basis.constr_basis];rfl
  exact ⟨family,fun v s=>LinearMap.congr_fun (identity s) v⟩

private theorem linear_choices {k V U I:Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (eval:I→U→ₗ[k]V) (S:I→Submodule k V) (works:∀u,∃v,∀s,eval s u-v∈S s) :
    ∃ value:U→ₗ[k]V,∀ u s,eval s u-value u∈S s := by
  classical
  let B:=Module.finBasis k U
  choose lift localReg using fun j=>works (B j)
  let value:=B.constr k lift
  refine ⟨value,fun u s=>?_⟩
  let diff:=eval s-value
  have into (j) : diff (B j)∈S s := by
    change eval s (B j)-value (B j)∈S s
    rw [show value (B j)=lift j from B.constr_basis ..]
    exact localReg j s
  change diff u∈S s
  have m : diff (∑ j,B.repr u j • B j) ∈ S s := by
    rw [map_sum]
    exact (S s).sum_mem (fun j _=>by rw [map_smul]; exact (S s).smul_mem _ (into j))
  rwa [B.sum_repr] at m

/-- From local principal parts on the actual surface, construct honest meromorphic
functions in its root field. At most the surface codimension is lost. -/
theorem lift_principal_parts (i n:ℕ) (budget:Budget E i n) (p:J→Chart→E)
    (compatible:∀ j s t,Over s t i (p j s-p j t)) :
    ∃ D:Submodule L (J→L), ∃ value:D→ₗ[L]E,
      Fintype.card J≤n+finrank L D ∧ ∀ (v:D) s,Regular s i (principalValue p s v.val-value v) := by
  classical
  let a:Chart:=(false,false)
  obtain ⟨family,coord⟩:=anchored i p compatible
  obtain ⟨D,count,corr⟩:=budget_subspace E i n budget family
  have works (v:D) : ∃ c:E,∀s,Regular s i (principalValue p s v.val-c) := by
    have hv : ∃ c:E,∀s,Regular s i (((family v.val).val s:E)-c):=corr v
    obtain ⟨c,hc⟩:=hv
    refine ⟨principalValue p a v.val+c,fun s=>?_⟩
    have h:Regular s i (((family v.val).val s:E)-c):=hc s
    rw [coord] at h
    rwa [sub_add_eq_sub_sub]
  have finD : FiniteDimensional L D := FiniteDimensional.of_injective
    (D.subtype : D→ₗ[L](J→L)) Subtype.val_injective
  obtain ⟨value,ok⟩:=linear_choices (k:=L) (U:=↥D) (V:=E) (I:=Chart)
    (fun s=>(principalValue p s).comp D.subtype) (regularSpace i) works
  refine ⟨D,value,?_,?_⟩
  · simpa only [Module.finrank_pi] using count
  · exact fun v s=>ok v s

#print axioms lift_principal_parts
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedPrincipalParts

-- merged module R6961MarkedWordResidues
section Merged_R6961MarkedWordResidues

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent RetainedRestrictionTorus
open RetainedSurfaceClass RetainedTwistedRestriction ChartOverlapTests
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6961.RetainedSurfaceClass Lower6961.MarkedEvaluation
open Lower6961.RetainedTwistedRestriction (regular_on_overlap)
open Lower6961.RetainedSurfaceClass (congr_of_eq)
variable {E:Type} [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def torFrame (E:Type) [Field E] [Algebra ChartField E] (s:Chart) : Tor E :=
  ⟨fr s,isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).1⟩:torus))⟩

/-- A section on the actual specialized abscissa line, with its degree represented
in the infinity frame. The two tested images are the original surface orders. -/
def FibreSection (i:ℕ) (z:L) (v:Axis E true z) : Prop :=
  ∀ b:Bool, ∃u:Tor E, IsIntegral (baseChart (reference true b)) (u:E) ∧
    red E true z ((torFrame E (reference true b))^i*u)=v

private theorem equal_residues (j c) (u v:Tor E) (h:Congruent j c (u:E) (v:E)) :
    red E j c u=red E j c v := by
  obtain ⟨r,ir,eq⟩:=h
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨⟨r,ir⟩,Subtype.ext eq⟩)

/-- Actual affine representatives for a marked fibre section on all four charts.
Dividing these representatives by the scalar parameter gives compatible principal
parts on the normalized surface. -/
theorem word_principal_parts [FiniteDimensional ChartField E]
    (i:ℕ) (z:L) (nz:z≠0) (v:Axis E true z) (sectionOnLine:FibreSection i z v) :
    ∃ w:Chart→Tor E, (∀s,Regular s i (w s:E)) ∧ (∀s, red E true z (w s)=v) ∧
      ∀s t,Over s t i ((w s:E)/ι (divisor true z)-(w t:E)/ι (divisor true z)) := by
  classical
  have atChart (s:Chart):∃w:Tor E,Regular s i (w:E) ∧ red E true z w=v := by
    let t:=reference true s.1
    obtain ⟨a,ia,eq⟩:=sectionOnLine s.1
    have parallel:axisBit s (!true)=axisBit t (!true):=rfl
    obtain ⟨q,iq,matchValue⟩:=line_representative true z nz s t parallel (a:E) (order_mono (chart_cover s t) ia)
    let Q:Tor E:=⟨q,order_mono (base_torus s) iq⟩
    have frameEq:torFrame E t=torFrame E s := rfl
    have eqQ:=equal_residues true z a Q matchValue
    let w:=torFrame E s^i*Q
    refine ⟨w,?_,?_⟩
    · change IsIntegral _ ((fr s)⁻¹^i*(fr s^i*q))
      have nzf : (fr s:E)≠0 := (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s false)
      rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ nzf,one_pow,one_mul]
      exact iq
    · change Ideal.Quotient.mk _ ((torFrame E s)^i*Q)=v
      change Ideal.Quotient.mk _ a=Ideal.Quotient.mk _ Q at eqQ
      rw [map_mul,←eqQ,←map_mul,←frameEq];exact eq
  choose w regular value using atChart
  refine ⟨w,regular,value,fun s t=>?_⟩
  let D:=ι (divisor true z)
  let V:=(fr s)⁻¹^i*((w s:E)/D-(w t:E)/D)
  have dn:D≠0:=(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne _ _)
  have zn:zcut s z≠0:=by
    intro zero
    exact (div_ne_zero (divisor_ne true z) (localFrame_ne s true))
      ((zcut_value s z).symm.trans (congrArg (fun a:baseChart s=>(a:ChartField)) zero))
  have : UniqueFactorizationMonoid (baseChart s) := (MonicChartProbes.planeEquiv s).toMulEquiv.uniqueFactorizationMonoid inferInstance
  apply cancel_equation s t (zcut s z) zn (IsRelPrime.mul_right_iff.mp (boundary_rel s 1 z one_ne_zero nz)).2.symm V
  · have lhs:=order_mono (into_cleared _ (edge s t)) (regular s)
    have rhs:=Lower6961.RetainedTwistedRestriction.regular_on_overlap s t i _ (regular t)
    have base:(localFrame s true)⁻¹∈baseChart s := by
      have h:chartCoordinate s.2 scalarCoordinate∈baseChart s:=Subring.subset_closure (Or.inr (Or.inr rfl))
      by_cases ht:s.2=true <;> simp [localFrame,axisBit,coordinate,ht,chartCoordinate] at * <;> assumption
    have inv:IsIntegral (baseChart s) (ι ((localFrame s true)⁻¹):E) := isIntegral_algebraMap (x:=(⟨_,base⟩:baseChart s))
    have reg:= (order_mono (into_cleared _ (edge s t)) inv).mul (lhs.sub rhs)
    change IsIntegral _ (ι (zcut s z:ChartField)*V)
    rw [zcut_value,map_div₀]
    have eq : (D/ι (localFrame s true))*V = ι ((localFrame s true)⁻¹)*((fr s)⁻¹^i*(w s:E)-(fr s)⁻¹^i*(w t:E)) := by
      dsimp only [V];rw [map_inv₀];field_simp [dn,(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s true)]
      <;> ring
    rw [eq];exact reg
  · obtain ⟨r,ir,rr⟩:=Lower6961.RetainedSurfaceClass.congr_of_eq E true z (w s) (w t) ((value s).trans (value t).symm)
    have inv : IsIntegral torus (fr s:E)⁻¹ := by rw [fr,←map_inv₀];exact isIntegral_algebraMap (x:=(⟨_,(torus_frame s false).2⟩:torus))
    change IsIntegral torus ((fr s)⁻¹^i*((w s:E)/D-(w t:E)/D))
    rw [←sub_div,rr,show ι (divisor true z)=D from rfl,mul_div_cancel_left₀ _ dn]
    exact (inv.pow _).mul ir

#print axioms word_principal_parts
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedWordResidues
