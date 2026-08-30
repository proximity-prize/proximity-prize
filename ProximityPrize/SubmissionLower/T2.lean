import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.IV
section ProximityFlatProofPort
open scoped TensorProduct
universe u v
namespace Algebra
variable {R:Type u} {A:Type v} {B:Type*} [CommRing R] [CommRing A] [Algebra R A]
 [CommRing B] [Algebra R B]
section
variable (R A) in
@[mk_iff,stacks 00UQ]
class FormallyEtale:Prop where
 subsingleton_kaehlerDifferential:Subsingleton Ω[A⁄R]
 subsingleton_h1Cotangent:Subsingleton (H1Cotangent R A)
attribute [instance]
 FormallyEtale.subsingleton_kaehlerDifferential FormallyEtale.subsingleton_h1Cotangent
end
namespace FormallyEtale
section
instance (priority:=100) [FormallyEtale R A]:
   FormallyUnramified R A:=⟨inferInstance⟩
instance (priority:=100) [FormallyEtale R A]:FormallySmooth R A:=
 ⟨inferInstance,inferInstance⟩
theorem iff_formallyUnramified_and_formallySmooth:
   FormallyEtale R A ↔ FormallyUnramified R A∧FormallySmooth R A:=
 ⟨fun _↦⟨inferInstance,inferInstance⟩,fun ⟨_,_⟩↦⟨inferInstance,inferInstance⟩⟩
theorem of_formallyUnramified_and_formallySmooth [FormallyUnramified R A]
   [FormallySmooth R A]:FormallyEtale R A:=
 FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›,‹_›⟩
instance:FormallyEtale R R:=of_formallyUnramified_and_formallySmooth
variable (R A) in
lemma comp_bijective [FormallyEtale R A] (I:Ideal B) (hI:I^2=⊥):
   Function.Bijective ((Ideal.Quotient.mkₐ R I).comp:(A →ₐ[R] B) → A →ₐ[R] B ⧸ I):=
 ⟨FormallyUnramified.comp_injective I hI,FormallySmooth.comp_surjective R A I hI⟩
theorem iff_comp_bijective:
  FormallyEtale R A ↔ ∀ ⦃B:Type max u v⦄ [CommRing B] [Algebra R B] (I:Ideal B),I^2=⊥ →
     Function.Bijective ((Ideal.Quotient.mkₐ R I).comp:(A →ₐ[R] B) → A →ₐ[R] B ⧸ I):=
 ⟨fun _ _↦comp_bijective R A,fun H↦
   have:FormallyUnramified R A:=FormallyUnramified.iff_comp_injective_of_small.{max u v}.mpr
     (by aesop (add safe Function.Bijective.injective))
   have:FormallySmooth R A:=FormallySmooth.of_comp_surjective
     (by aesop (add safe Function.Bijective.surjective))
  .of_formallyUnramified_and_formallySmooth⟩
end
section OfEquiv
theorem of_equiv [FormallyEtale R A] (e:A ≃ₐ[R] B):FormallyEtale R B:=
 FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
   ⟨FormallyUnramified.of_equiv e,FormallySmooth.of_equiv e⟩
theorem iff_of_equiv (e:A ≃ₐ[R] B):FormallyEtale R A ↔ FormallyEtale R B:=
 ⟨fun _↦of_equiv e,fun _↦of_equiv e.symm⟩
end OfEquiv
section Comp
variable [Algebra A B] [IsScalarTower R A B]
variable (R A B) in
theorem comp [FormallyEtale R A] [FormallyEtale A B]:
   FormallyEtale R B:=
 FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
   ⟨FormallyUnramified.comp R A B,FormallySmooth.comp R A B⟩
lemma of_restrictScalars [FormallyUnramified R A] [FormallyEtale R B]:
   FormallyEtale A B:=
 have:=FormallyUnramified.of_restrictScalars R A B
 have:=FormallySmooth.of_restrictScalars R A B
 .of_formallyUnramified_and_formallySmooth
lemma iff_restrictScalars [FormallyEtale R A]:
   Algebra.FormallyEtale R B ↔ Algebra.FormallyEtale A B:=
 ⟨fun _↦.of_restrictScalars (R:=R),fun _↦.comp _ A _⟩
lemma _root_.Algebra.FormallySmooth.iff_restrictScalars [FormallyEtale R A]:
   Algebra.FormallySmooth R B ↔ Algebra.FormallySmooth A B:=
 ⟨fun _↦.of_restrictScalars R _ _,fun _↦.comp _ A _⟩
set_option linter.dupNamespace false in
@[deprecated (since:="2025-12-09")]
alias Algebra.FormallyEtale.of_restrictScalars:=of_restrictScalars
end Comp
lemma iff_of_surjective
   {R S:Type*} [CommRing R] [CommRing S]
   [Algebra R S] (h:Function.Surjective (algebraMap R S)):
   Algebra.FormallyEtale R S ↔ IsIdempotentElem (RingHom.ker (algebraMap R S)):=by
 rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, ←FormallySmooth.iff_of_surjective h,
   and_iff_right (FormallyUnramified.of_surjective (Algebra.ofId R S) h)]
set_option linter.dupNamespace false in
@[deprecated (since:="2025-12-09")]
alias Algebra.FormallyEtale.iff_of_surjective:=iff_of_surjective
section BaseChange
open scoped TensorProduct
instance [FormallyEtale R A]:FormallyEtale B (B ⊗[R] A):=
 .of_formallyUnramified_and_formallySmooth
end BaseChange
section Localization
variable {R S Rₘ Sₘ:Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M:Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M
theorem of_isLocalization:FormallyEtale R Rₘ:=
 FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
   ⟨FormallyUnramified.of_isLocalization M,FormallySmooth.of_isLocalization M⟩
instance [FormallyEtale R S] (M:Submonoid S):FormallyEtale R (Localization M):=
 .of_formallyUnramified_and_formallySmooth
theorem localization_base [FormallyEtale R Sₘ]:FormallyEtale Rₘ Sₘ:=
 FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
   ⟨FormallyUnramified.localization_base M,FormallySmooth.localization_base M⟩
theorem localization_map [FormallyEtale R S]:FormallyEtale Rₘ Sₘ:=by
 haveI:FormallyEtale S Sₘ:=FormallyEtale.of_isLocalization (M.map (algebraMap R S))
 haveI:FormallyEtale R Sₘ:=FormallyEtale.comp R S Sₘ
 exact FormallyEtale.localization_base M
end Localization
end FormallyEtale
section
variable (R A) in
@[mk_iff,stacks 00U1 "Note that this is a different definition from this Stacks entry, but
<https://stacks.math.columbia.edu/tag/00UR> shows that it is equivalent to the definition here."]
class Etale:Prop where
 formallyEtale:FormallyEtale R A:=by infer_instance
 finitePresentation:FinitePresentation R A:=by infer_instance
lemma Etale.iff_formallyUnramified_and_smooth:
   Etale R A ↔ FormallyUnramified R A∧Smooth R A:=by
 rw [etale_iff,FormallyEtale.iff_formallyUnramified_and_formallySmooth,smooth_iff]
 tauto
end
namespace Etale
attribute [instance] formallyEtale finitePresentation
instance:Etale R R where
instance [Etale R A]:Smooth R A where
instance (priority:=low) [Etale R A]:Unramified R A where
theorem of_equiv [Etale R A] (e:A ≃ₐ[R] B):Etale R B where
 formallyEtale:=FormallyEtale.of_equiv e
 finitePresentation:=FinitePresentation.equiv e
section Comp
variable (R A B)
theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B]:Etale R B where
 formallyEtale:=FormallyEtale.comp R A B
 finitePresentation:=FinitePresentation.trans R A B
instance baseChange [Etale R A]:Etale B (B ⊗[R] A) where
lemma of_restrictScalars [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale R B]:
   Etale A B where
 finitePresentation:=.of_restrict_scalars_finitePresentation R A B
 formallyEtale:=.of_restrictScalars (R:=R)
end Comp
theorem of_isLocalizationAway (r:R) [IsLocalization.Away r A]:Etale R A where
 formallyEtale:=Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
 finitePresentation:=IsLocalization.Away.finitePresentation r
instance (s:A) [Algebra.Etale R A]:Algebra.Etale R (Localization.Away s) where
instance (R S:Type u) [CommRing R] [CommRing S]:
   letI:Algebra (R × S) S:=(RingHom.snd R S).toAlgebra
   Algebra.Etale (R × S) S:=by
 algebraize [RingHom.snd R S]
 exact Algebra.Etale.of_isLocalizationAway (0,1)
instance (S:Type*) [CommRing S]:
   letI:Algebra (R × S) R:=(RingHom.fst R S).toAlgebra
   Algebra.Etale (R × S) R:=by
 algebraize [RingHom.fst R S]
 exact Algebra.Etale.of_isLocalizationAway (1,0)
instance (S:Type*) [CommRing S]:
   letI:Algebra (R × S) S:=(RingHom.snd R S).toAlgebra
   Algebra.Etale (R × S) S:=by
 algebraize [RingHom.snd R S]
 exact Algebra.Etale.of_isLocalizationAway (0,1)
end Etale
end Algebra
namespace RingHom
variable {R S:Type*} [CommRing R] [CommRing S]
@[algebraize Algebra.FormallyEtale]
def FormallyEtale (f:R →+*S):Prop:=
 letI:=f.toAlgebra
 Algebra.FormallyEtale R S
lemma formallyEtale_algebraMap [Algebra R S]:
   (algebraMap R S).FormallyEtale ↔ Algebra.FormallyEtale R S:=by
 rw [FormallyEtale,toAlgebra_algebraMap]
lemma FormallyEtale.comp {T:Type*} [CommRing T] {f:R →+*S} {g:S →+*T} (hf:f.FormallyEtale)
   (hg:g.FormallyEtale):
   (g.comp f).FormallyEtale:=by
 algebraize [f,g,g.comp f]
 exact Algebra.FormallyEtale.comp R S T
end RingHom
