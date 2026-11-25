import ProximityPrize.SubmissionLower.R6960RetainedPairedResidues
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import ProximityPrize.SubmissionLower.R6960RetainedAxisTransition

set_option Elab.async false

-- merged module R6960RetainedLineEvaluation
section Merged_R6960RetainedLineEvaluation
noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedLineEvaluation
open Polynomial Algebra Module
open scoped Polynomial
open Lower6960.TraceSpecialization (idempotent_multiple)
variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra (Polynomial k) S]
omit [Algebra k S] in
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
end Lower6960.RetainedLineEvaluation

end
end Merged_R6960RetainedLineEvaluation

-- merged module R6960RetainedAxisPoint
section Merged_R6960RetainedAxisPoint
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus MonicChartProbes
open Module Submodule Algebra Polynomial
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (toCross toCross_kernel finiteX_val finiteZ_val)
open Lower6960.RetainedSurfaceClass (chartSpace)
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
    (zero : Lower6960.RetainedSurfaceClass.toCross E x z u=0) :
    ∃ a b:finiteOrder E, fromFinite E u=cut E false x*fromFinite E a+cut E true z*fromFinite E b := by
  have mem : u∈RingHom.ker (Lower6960.RetainedSurfaceClass.toCross E x z).toRingHom := RingHom.mem_ker.mpr zero
  rw [Lower6960.RetainedSurfaceClass.toCross_kernel E x z nx nz,point_kernel,Ideal.map_sup,
    Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton] at mem
  obtain ⟨_,hu,_,hv,eq⟩:=Submodule.mem_sup.mp mem
  obtain ⟨a,rfl⟩:=Ideal.mem_span_singleton.mp hu
  obtain ⟨b,rfl⟩:=Ideal.mem_span_singleton.mp hv
  have fx : fromFinite E (algebraMap Base (finiteOrder E) (finiteX x))=cut E false x :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteX_val x))
  have fz : fromFinite E (algebraMap Base (finiteOrder E) (finiteZ z))=cut E true z :=
    Subtype.ext (congrArg (algebraMap ChartField E) (Lower6960.RetainedSurfaceClass.finiteZ_val z))
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
    have zero : Lower6960.RetainedSurfaceClass.toCross E x z W=0 := hz
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
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedAxisPoint

-- merged module R6960RetainedNativeEuler
section Merged_R6960RetainedNativeEuler
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open RetainedRestrictionTorus Module Submodule LinearMap LineEuler Polynomial
open scoped Lower6960.RetainedSurfaceClass Polynomial
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
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedNativeEuler

-- merged module R6960RetainedGlobalEvaluation
section Merged_R6960RetainedGlobalEvaluation
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace Lower6960.RetainedSurfaceClass
open K1_14 (L)
open MonicChart (ChartField)
open MonicFourChartDescent ChartSections RetainedRestrictionTorus
open Module Submodule LinearMap Algebra Polynomial LineEuler
open scoped Lower6960.RetainedSurfaceClass Polynomial
open Lower6960.RetainedSurfaceClass (chartSpace)
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
end Lower6960.RetainedSurfaceClass

end
end Merged_R6960RetainedGlobalEvaluation
