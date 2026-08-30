import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CV
import ProximityPrize.SubmissionLower.T7
import ProximityPrize.SubmissionLower.IF
import ProximityPrize.SubmissionLower.AT
import ProximityPrize.SubmissionLower.F2
import ProximityPrize.SubmissionLower.IY
import ProximityPrize.SubmissionLower.U9
section ProximityFlatProofPort
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
open TensorProduct
attribute [-instance] Module.Free.instFaithfulSMulOfNontrivial Algebra.IsIntegral.isLocalHom
namespace Algebra
variable (R S) in
@[mk_iff,stacks 00PL]
class QuasiFinite:Prop where
 finite_fiber (P:Ideal R) [P.IsPrime]:
   Module.Finite P.ResidueField (P.Fiber S):=by infer_instance
attribute [stacks 00PM] quasiFinite_iff
namespace QuasiFinite
attribute [instance] finite_fiber
instance [QuasiFinite R S] (P:Ideal R) [P.IsPrime]:IsArtinianRing (P.Fiber S):=
 .of_finite P.ResidueField _
lemma finite_comap_preimage_singleton [QuasiFinite R S] (P:PrimeSpectrum R):
   (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite:=
 (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete
lemma finite_primesOver [QuasiFinite R S] (I:Ideal R):(I.primesOver S).Finite:=by
 by_cases h:I.IsPrime
 · refine ((finite_comap_preimage_singleton ⟨I,h⟩).image PrimeSpectrum.asIdeal).subset ?_
   exact fun J hJ↦⟨⟨_,hJ.1⟩,PrimeSpectrum.ext hJ.2.1.symm,rfl⟩
 · convert! Set.finite_empty
   by_contra!
   obtain ⟨J,h₁,⟨rfl⟩⟩:=this
   exact h inferInstance
lemma finite_comap_preimage [QuasiFinite R S] {s:Set (PrimeSpectrum R)} (hs:s.Finite):
   (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite:=
 hs.preimage' fun _ _↦finite_comap_preimage_singleton _
lemma isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P:PrimeSpectrum R):
   IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}):=
 ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩
lemma isDiscrete_comap_preimage [QuasiFinite R S] {s:Set (PrimeSpectrum R)}
   (hs:IsDiscrete s):
   IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s):=
 hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
   fun _↦isDiscrete_comap_preimage_singleton _
instance (priority:=low) [Module.Finite R S]:QuasiFinite R S where
@[stacks 00PP "(3)"]
instance baseChange [QuasiFinite R S] {A:Type*} [CommRing A] [Algebra R A]:
   QuasiFinite A (A ⊗[R] S):=by
 refine ⟨fun P hP↦?_⟩
 let p:=P.under R
 let:=Localization.AtPrime.algebraOfLiesOver p P
 let e:P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S):=
   (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
     (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
 exact .of_surjective e.symm.toLinearMap e.symm.surjective
open IsLocalRing in
private lemma finite_of_isArtinianRing_of_isLocalRing
   [QuasiFinite R S] [IsArtinianRing R] [IsLocalRing R]:Module.Finite R S:=by
 let e:(maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S):=
   (Algebra.TensorProduct.congr (.symm <| .ofBijective _
     (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
   (Algebra.TensorProduct.comm _ _ _).trans
   ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
 have:Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)):=
   have:Module.Finite R ((maximalIdeal R).Fiber S):=
     .trans (maximalIdeal R).ResidueField _
   .of_surjective e.toLinearMap e.surjective
 refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
   ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
 · refine Ideal.mk_ker.trans_le ?_
   rw [Ideal.map_le_iff_le_comap, ←Ring.KrullDimLE.nilradical_eq_maximalIdeal]
   exact fun x hx↦IsNilpotent.map hx _
 · rw [←RingHom.ker_coe_toRingHom,Ideal.Quotient.mkₐ_ker]
   exact Ideal.FG.map (IsNoetherian.noetherian _) _
lemma _root_.Module.Finite.of_quasiFinite [IsArtinianRing R] [QuasiFinite R S]:
   Module.Finite R S:=by
 classical
 let e:R ≃ₐ[R] PrimeSpectrum.PiLocalization R:=
   .ofBijective (IsScalarTower.toAlgHom _ _ _)
     (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
 have:Fintype (PrimeSpectrum R):=.ofFinite _
 let e':S ≃ₐ[R] Π p:PrimeSpectrum R,Localization p.asIdeal.primeCompl ⊗[R] S:=
   (Algebra.TensorProduct.rid R R S).symm.trans <| (Algebra.TensorProduct.congr .refl e).trans <|
     (Algebra.TensorProduct.piRight _ _ _ _).trans <| AlgEquiv.piCongrRight
     fun _↦Algebra.TensorProduct.comm _ _ _
 have (p:PrimeSpectrum R):Module.Finite R (Localization p.asIdeal.primeCompl ⊗[R] S):=
   have:Module.Finite R (Localization.AtPrime p.asIdeal):=
     .of_surjective (Algebra.linearMap _ _)
       (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
   have:Module.Finite (Localization.AtPrime p.asIdeal)
     (Localization.AtPrime p.asIdeal ⊗[R] S):=finite_of_isArtinianRing_of_isLocalRing
   .trans (Localization.AtPrime p.asIdeal) _
 exact .of_surjective e'.symm.toLinearMap e'.symm.surjective
lemma iff_of_isArtinianRing [IsArtinianRing R]:
   QuasiFinite R S ↔ Module.Finite R S:=
 ⟨fun _↦.of_quasiFinite,fun _↦inferInstance⟩
attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
@[stacks 00PO]
lemma «trans» [QuasiFinite R S] [QuasiFinite S T]:QuasiFinite R T:=by
 refine ⟨fun P hP↦?_⟩
 have:Module.Finite (P.Fiber S) ((P.Fiber S) ⊗[S] T):=
   (iff_of_isArtinianRing (R:=P.Fiber S) (S:=(P.Fiber S) ⊗[S] T)).mp inferInstance
 have:Module.Finite P.ResidueField ((P.Fiber S) ⊗[S] T):=
   .trans (P.Fiber S) _
 let e:P.Fiber S ≃ₐ[S] S ⊗[R] P.ResidueField:=
   { __:=Algebra.TensorProduct.comm _ _ _,commutes' _:=rfl}
 let e':(P.Fiber S) ⊗[S] T ≃ₐ[R] P.Fiber T:=
   ((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans <|
   ((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans <|
   ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
   (Algebra.TensorProduct.comm _ _ _)
 let e'':(P.Fiber S) ⊗[S] T ≃ₐ[P.ResidueField] P.Fiber T:=
   { __:=e',commutes' _:=by simp [e',e]}
 exact .of_surjective e''.toLinearMap e''.surjective
omit [Algebra S T] in
lemma of_surjective_algHom [QuasiFinite R S] (f:S →ₐ[R] T) (hf:Function.Surjective f):
   QuasiFinite R T:=
 let:=f.toRingHom.toAlgebra
 let:=IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
 have:Module.Finite S T:=.of_surjective (Algebra.linearMap _ _) hf
 Algebra.QuasiFinite.trans R S T
instance (I:Ideal S) [QuasiFinite R S]:QuasiFinite R (S ⧸ I):=
 of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective
omit [Algebra S T] in
lemma iff_of_algEquiv (e:S ≃ₐ[R] T):
   Algebra.QuasiFinite R S ↔ Algebra.QuasiFinite R T:=
 ⟨fun _↦.of_surjective_algHom e.toAlgHom e.surjective,
   fun _↦.of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩
lemma of_isLocalization (M:Submonoid S) [IsLocalization M T] [QuasiFinite R S]:
   QuasiFinite R T:=
 letI:QuasiFinite S T:=by
   refine ⟨fun P hP↦.of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
   letI:DecidableEq P.ResidueField:=Classical.decEq P.ResidueField
   rw [←LinearMap.coe_restrictScalars (R:=S), ←LinearMap.range_eq_top,
     ←top_le_iff, ←TensorProduct.span_tmul_eq_top,Submodule.span_le]
   rintro _ ⟨p,s,rfl⟩
   obtain ⟨s,t,rfl⟩:=IsLocalization.exists_mk'_eq M s
   use s • p/algebraMap _ _ t.1
   apply ((IsLocalization.map_units T t).map
     Algebra.TensorProduct.includeRight).mul_left_injective
   by_cases ht:algebraMap _ P.ResidueField t.1=0
   · simp [ht]
   trans (s • p) ⊗ₜ[S] 1
   · simp [div_mul_cancel₀ _ ht]
   · dsimp;simp [Algebra.algebraMap_eq_smul_one,smul_tmul]
 Algebra.QuasiFinite.trans R S T
instance (M:Submonoid S) [QuasiFinite R S]:QuasiFinite R (Localization M):=of_isLocalization M
instance (priority:=low) [IsFractionRing R S]:QuasiFinite R S:=
 of_isLocalization (nonZeroDivisors R)
instance [QuasiFinite R S] (p:Ideal R) [p.IsPrime] (q:Ideal (p.Fiber S)) [q.IsPrime]:
   Module.Finite p.ResidueField (Localization.AtPrime q):=
 Module.Finite.of_quasiFinite (R:=p.ResidueField) (S:=Localization.AtPrime q)
instance (P:Ideal S) [P.IsPrime] [QuasiFinite R S]:QuasiFinite R P.ResidueField:=
 .trans _ (S ⧸ P) _
variable (R S T) in
lemma of_restrictScalars [QuasiFinite R T]:QuasiFinite S T:=by
 refine ⟨fun P hP↦?_⟩
 let f:P.ResidueField ⊗[R] T →ₐ[P.ResidueField] P.Fiber T:=
   Algebra.TensorProduct.lift (Algebra.ofId _ _)
     (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _↦.all _ _
 have hf:Function.Surjective f:=by
   rw [←AlgHom.coe_restrictScalars' (R:=S), ←AlgHom.coe_toLinearMap, ←LinearMap.range_eq_top,
     ←top_le_iff, ←TensorProduct.span_tmul_eq_top,Submodule.span_le]
   rintro _ ⟨a,b,rfl⟩
   exact ⟨a ⊗ₜ b,by simp [f]⟩
 have:Module.Finite P.ResidueField (P.ResidueField ⊗[R] T):=.of_quasiFinite
 exact .of_surjective f.toLinearMap hf
variable (R S) in
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S]:
   DiscreteTopology (PrimeSpectrum S):=
 isDiscrete_univ_iff.mp
   (isDiscrete_comap_preimage (R:=R) (S:=S) (isDiscrete_univ_iff.mpr ‹_›))
variable (R S) in
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S]:
   Finite (PrimeSpectrum S):=
 Set.finite_univ_iff.mp
   (finite_comap_preimage (Set.finite_univ (α:=PrimeSpectrum R)))
omit [Algebra S T] in
lemma of_forall_exists_mul_mem_range [QuasiFinite R S] (f:S →ₐ[R] T)
   (H:∀ x:T,∃ s:S,IsUnit (f s)∧x*f s∈f.range):
   QuasiFinite R T:=by
 let φ:Localization ((IsUnit.submonoid T).comap f) →ₐ[R] T:=
   IsLocalization.liftAlgHom (M:=(IsUnit.submonoid T).comap f) (f:=f)
     (by simp [IsUnit.mem_submonoid_iff])
 suffices Function.Surjective φ from .of_surjective_algHom φ this
 intro x
 obtain ⟨s,hs,t,ht⟩:=H x
 refine ⟨IsLocalization.mk' (M:=(IsUnit.submonoid T).comap f) _ t ⟨s,hs⟩,?_⟩
 simpa [φ,IsLocalization.lift_mk',Units.mul_inv_eq_iff_eq_mul,IsUnit.coe_liftRight]
omit [Algebra S T] in
lemma eq_of_le_of_under_eq [QuasiFinite R S] (P Q:Ideal S) [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) (h₂:P.under R=Q.under R):P=Q:=
 congr($((isDiscrete_comap_preimage_singleton ⟨_,inferInstance⟩).eq_of_specializes
   (a:=⟨P,‹_›⟩) (b:=⟨Q,‹_›⟩) (by simpa [←PrimeSpectrum.le_iff_specializes]) rfl
   (PrimeSpectrum.ext h₂.symm)).1)
instance [QuasiFinite R S] (P:Ideal R) [P.IsPrime] (Q:Ideal S) [Q.IsPrime] [Q.LiesOver P]
   [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
   [Localization.AtPrime.IsLiesOverAlgebra P Q]:
   Module.Finite P.ResidueField Q.ResidueField:=
 have:QuasiFinite P.ResidueField Q.ResidueField:=.of_restrictScalars R _ _
 .of_quasiFinite
section Finite
lemma iff_finite_comap_preimage_singleton [FiniteType R S]:
   QuasiFinite R S ↔ ∀ x,(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite:=by
 refine ⟨fun H _↦finite_comap_preimage_singleton _,fun H↦⟨fun P _↦?_⟩⟩
 rw [Module.finite_iff_isArtinianRing,isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
 have:IsJacobsonRing (P.Fiber S):=isJacobsonRing_of_finiteType (A:=P.ResidueField)
 have:Finite (PrimeSpectrum (P.Fiber S)):=
   (PrimeSpectrum.preimageEquivFiber R S ⟨P,‹_›⟩).finite_iff.mp (H ⟨P,‹_›⟩)
 exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
   (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩
lemma iff_finite_primesOver [FiniteType R S]:
   QuasiFinite R S ↔ ∀ I:Ideal R,I.IsPrime → (I.primesOver S).Finite:=by
 rw [iff_finite_comap_preimage_singleton,
   (PrimeSpectrum.equivSubtype R).forall_congr_left,Subtype.forall]
 refine forall₂_congr fun I hI↦?_
 rw [←Set.finite_image_iff (Function.Injective.injOn fun _ _↦PrimeSpectrum.ext)]
 congr!
 ext J
 simp [(PrimeSpectrum.equivSubtype S).exists_congr_left,PrimeSpectrum.ext_iff,eq_comm,
   PrimeSpectrum.equivSubtype,Ideal.primesOver,and_comm,Ideal.liesOver_iff,Ideal.under]
end Finite
end QuasiFinite
section QuasiFiniteAt
variable (R) in
abbrev QuasiFiniteAt (p:Ideal S) [p.IsPrime]:Prop:=
 QuasiFinite R (Localization.AtPrime p)
lemma QuasiFiniteAt.baseChange (p:Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
   {A:Type*} [CommRing A] [Algebra R A] (q:Ideal (A ⊗[R] S)) [q.IsPrime]
   (hq:p=q.comap Algebra.TensorProduct.includeRight.toRingHom):
   QuasiFiniteAt A q:=by
 let f:A ⊗[R] Localization.AtPrime p →ₐ[A] Localization.AtPrime q:=
   Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq,by
     simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
       IsScalarTower.algebraMap_apply R (A ⊗[R] S) (Localization.AtPrime q)]⟩ fun _ _↦.all _ _
 let g:A ⊗[R] S →ₐ[A] A ⊗[R] Localization.AtPrime p:=
   Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
 have:f.comp g=IsScalarTower.toAlgHom _ _ _:=by ext;simp [f,g]
 replace this (x:_):f (g x)=algebraMap _ _ x:=DFunLike.congr_fun this x
 refine .of_forall_exists_mul_mem_range f fun x↦?_
 obtain ⟨x,⟨s,hs⟩,rfl⟩:=IsLocalization.exists_mk'_eq q.primeCompl x
 refine ⟨g s,this s ▸ IsLocalization.map_units _ ⟨s,hs⟩,?_⟩
 rw [this,IsLocalization.mk'_spec_mk]
 exact ⟨g x,this x⟩
set_option backward.isDefEq.respectTransparency false in
omit [Algebra S T] in
lemma QuasiFiniteAt.of_surjectiveOnStalks (p:Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
   (f:S →ₐ[R] T) (hf:f.SurjectiveOnStalks) (q:Ideal T) [q.IsPrime]
   (hq:p=q.comap f.toRingHom):
   QuasiFiniteAt R q:=by
 subst hq
 refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl,?_⟩ (hf q ‹_›)
 simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
   IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]
lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver (p:Ideal S) [p.IsPrime]
   [QuasiFiniteAt R p] (hf:(algebraMap S T).SurjectiveOnStalks) (q:Ideal T) [q.IsPrime]
   [q.LiesOver p]:QuasiFiniteAt R q:=
 .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)
instance QuasiFiniteAt.comap_algEquiv (p:Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
   (f:T ≃ₐ[R] S):QuasiFiniteAt R (p.comap f.toRingHom):=
 .of_surjectiveOnStalks p f.symm.toAlgHom
   (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext;simp)
omit [Algebra S T] in
lemma QuasiFiniteAt.of_le {P Q:Ideal S} [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) [QuasiFiniteAt R Q]:
   QuasiFiniteAt R P:=by
 let f:Localization.AtPrime Q →ₐ[R] Localization.AtPrime P:=
   IsLocalization.liftAlgHom (M:=Q.primeCompl) (f:=IsScalarTower.toAlgHom _ _ _) <| by
     simp only [IsScalarTower.coe_toAlgHom',Subtype.forall,Ideal.mem_primeCompl_iff]
     exact fun a ha↦IsLocalization.map_units (M:=P.primeCompl) _ ⟨a,fun h↦ha (h₁ h)⟩
 refine .of_forall_exists_mul_mem_range f fun x↦?_
 obtain ⟨x,⟨s,hs⟩,rfl⟩:=IsLocalization.exists_mk'_eq P.primeCompl x
 exact ⟨algebraMap _ _ s,by simpa [f] using IsLocalization.map_units _ ⟨s,hs⟩,
   algebraMap _ _ x,by simp [f]⟩
omit [Algebra S T] in
lemma QuasiFiniteAt.eq_of_le_of_under_eq {P Q:Ideal S} [P.IsPrime] [Q.IsPrime]
   (h₁:P ≤ Q) (h₂:P.under R=Q.under R) [QuasiFiniteAt R Q]:
   P=Q:=by
 have:=Q.isPrime_map_of_isLocalizationAtPrime h₁ (S:=Localization.AtPrime Q)
 have H:=QuasiFinite.eq_of_le_of_under_eq (R:=R)
   (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
   (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
     convert! h₂ <;> rw [←Ideal.under_under (B:=S)]
     · rw [Q.under_map_of_isLocalizationAtPrime h₁]
     · rw [Localization.AtPrime.under_maximalIdeal])
 rw [←Localization.AtPrime.under_maximalIdeal (I:=Q), ←H,
   Q.under_map_of_isLocalizationAtPrime h₁]
instance (p:Ideal R) [p.IsPrime] (P:Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P]
   [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
   [Localization.AtPrime.IsLiesOverAlgebra p P]:
   Module.Finite p.ResidueField P.ResidueField:=by
 let m:=IsLocalRing.maximalIdeal (Localization.AtPrime P)
 let:m.LiesOver p:=.trans _ P _
 let:=Localization.AtPrime.algebraOfLiesOver p m
 let:=Localization.AtPrime.algebraOfLiesOver P m
 let e:=AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
   m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
       P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
 exact .of_surjective e.symm.toLinearMap e.symm.surjective
set_option backward.defeqAttrib.useBackward true in
lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
   (p:Ideal S) [p.IsPrime] [IsArtinianRing R] [Algebra.EssFiniteType R S]
   [Algebra.QuasiFiniteAt R p]:
   ∃ f∉p,(PrimeSpectrum.basicOpen f:Set (PrimeSpectrum S))={⟨p,‹_›⟩}:=by
 have:IsLocalizedModule p.primeCompl (.id (R:=S) (M:=Localization.AtPrime p)):=
   ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
     fun y↦⟨⟨y,1⟩,by simp⟩,by simpa using ⟨1,p.primeCompl.one_mem⟩⟩
 have:Module.Finite R (Localization.AtPrime p):=.of_quasiFinite
 have:Module.Finite S (Localization.AtPrime p):=.of_restrictScalars_finite R _ _
 have:IsArtinianRing (Localization.AtPrime p):=.of_finite R _
 have:IsNoetherianRing S:=Algebra.EssFiniteType.isNoetherianRing R S
 have:Module.FinitePresentation S (Localization.AtPrime p):=
   Module.finitePresentation_of_finite _ _
 obtain ⟨r,hrp,H⟩:=IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
   p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
 have:IsLocalization (.powers r) (Localization.AtPrime p):=
   (isLocalizedModule_iff_isLocalization' _ _).mp H
 let φ:Localization.Away r ≃ₐ[S] Localization.AtPrime p:=
   IsLocalization.algEquiv (.powers r) _ _
 refine ⟨r,hrp,subset_antisymm (fun q hrq↦?_) (Set.singleton_subset_iff.mpr hrp)⟩
 obtain ⟨q,rfl⟩:=(PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
 obtain ⟨q,rfl⟩:=(PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
 obtain rfl:q=IsLocalRing.closedPoint _:=Subsingleton.elim _ _
 ext1
 dsimp [-RingEquiv.symm_mk]
 rw [Ideal.comap_comap, ←AlgEquiv.toAlgHom_toRingHom,AlgHom.comp_algebraMap]
 exact IsLocalization.AtPrime.under_maximalIdeal _ _
lemma QuasiFiniteAt.isClopen_singleton
   (p:PrimeSpectrum S) [IsArtinianRing R] [Algebra.FiniteType R S]
   [Algebra.QuasiFiniteAt R p.asIdeal]:IsClopen {p}:=by
 have:IsJacobsonRing S:=isJacobsonRing_of_finiteType (A:=R)
 have:IsNoetherianRing S:=Algebra.FiniteType.isNoetherianRing R S
 refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
 obtain ⟨f,hf,e⟩:=exists_basicOpen_eq_singleton (R:=R) p.asIdeal
 exact e ▸ (PrimeSpectrum.basicOpen f).isOpen
end QuasiFiniteAt
end Algebra
