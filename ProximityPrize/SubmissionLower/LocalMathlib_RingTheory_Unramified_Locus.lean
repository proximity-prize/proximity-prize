/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Andrew Yang
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Etale_Kaehler
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_LocalRing_ResidueField_Fiber
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Localization_InvSubmonoid
section ProximityFlatProofPort
universe u
namespace Algebra
section
variable {R A B:Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]
variable (R) in
abbrev IsUnramifiedAt (q:Ideal A) [q.IsPrime]:Prop:=
  FormallyUnramified R (Localization.AtPrime q)
variable (R A) in
def unramifiedLocus:Set (PrimeSpectrum A):=
  { p | IsUnramifiedAt R p.asIdeal}
lemma IsUnramifiedAt.comp
    (p:Ideal A) (P:Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R p] [IsUnramifiedAt A P]:IsUnramifiedAt R P:=by
  let:=Localization.AtPrime.algebraOfLiesOver p P
  have:FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P):=
    .of_restrictScalars A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _
variable (R) in
lemma IsUnramifiedAt.of_restrictScalars (P:Ideal B) [P.IsPrime]
    [IsUnramifiedAt R P]:IsUnramifiedAt A P:=
  FormallyUnramified.of_restrictScalars R _ _
instance (p:Ideal R) [p.IsPrime] (q:Ideal A) [q.IsPrime] [q.LiesOver p] [IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]:
    FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q):=
  .of_restrictScalars R _ _
open _root_.TensorProduct in
theorem IsUnramifiedAt.residueField
    (P:Ideal R) [P.IsPrime] (Q:Ideal A) [Q.IsPrime]
    [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
    (Q':Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ':Q=Q'.comap Algebra.TensorProduct.includeRight.toRingHom):
    IsUnramifiedAt P.ResidueField Q':=by
  let f₀:Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q':=
    Localization.localAlgHom Q Q' _ hQ'
  have hf₀:Function.Surjective f₀:=by
    subst hQ';exact P.surjectiveOnStalks_residueField.baseChange' _ _
  let f:P.Fiber (Localization.AtPrime Q) →ₐ[P.ResidueField] Localization.AtPrime Q':=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _↦.all _ _
  have hf:Function.Surjective f:=hf₀.forall.mpr fun x↦⟨1 ⊗ₜ x,by simp [f]⟩
  exact .of_surjective _ hf
end
section IsUnramifiedIn
variable {R:Type*} [CommRing R]
def IsUnramifiedIn (A:Type*) [CommRing A] [Algebra R A] (𝔭:Ideal R):Prop:=
  ∀ (𝔓:Ideal A) (_:𝔓.IsPrime),𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt R 𝔓
variable (A:Type*) [CommRing A] [Algebra R A]
theorem isUnramifiedIn_top:IsUnramifiedIn A (⊤:Ideal R):=
  fun P hP _↦(hP.ne_top ((Ideal.eq_top_iff_of_liesOver P (⊤:Ideal R)).mpr rfl)).elim
end IsUnramifiedIn
section
variable {R A:Type*} [CommRing R] [CommRing A] [Algebra R A]
lemma unramifiedLocus_eq_compl_support:
    unramifiedLocus R A=(Module.support A Ω[A⁄R])ᶜ:=by
  ext p
  simp only [Set.mem_compl_iff,Module.notMem_support_iff]
  have:=IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm
lemma basicOpen_subset_unramifiedLocus_iff {f:A}:
    ↑(PrimeSpectrum.basicOpen f) ⊆ unramifiedLocus R A ↔
      Algebra.FormallyUnramified R (Localization.Away f):=by
  rw [unramifiedLocus_eq_compl_support,Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl,compl_compl,
    ←LocalizedModule.subsingleton_iff_support_subset,Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
lemma unramifiedLocus_eq_univ_iff:
    unramifiedLocus R A=Set.univ ↔ Algebra.FormallyUnramified R A:=by
  rw [unramifiedLocus_eq_compl_support,compl_eq_comm,Set.compl_univ,eq_comm,
    Module.support_eq_empty_iff,Algebra.formallyUnramified_iff]
theorem formallyUnramified_iff_forall:
    FormallyUnramified R A ↔ ∀ q:PrimeSpectrum A,IsUnramifiedAt R q.1:=
  unramifiedLocus_eq_univ_iff.symm.trans Set.eq_univ_iff_forall
theorem unramified_iff_forall [FiniteType R A]:
    Unramified R A ↔ ∀ q:PrimeSpectrum A,IsUnramifiedAt R q.1:=
  .trans ⟨fun h↦h.formallyUnramified,fun h↦⟨h,inferInstance⟩⟩ formallyUnramified_iff_forall
lemma isOpen_unramifiedLocus [EssFiniteType R A]:IsOpen (unramifiedLocus R A):=by
  rw [unramifiedLocus_eq_compl_support,Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
lemma exists_formallyUnramified_of_isUnramifiedAt [EssFiniteType R A] (p:Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p]:∃ f∉p,Algebra.FormallyUnramified R (Localization.Away f):=by
  obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hpr,hr⟩:=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨p,‹_›⟩∈unramifiedLocus R A from ‹_›) isOpen_unramifiedLocus
  exact ⟨r,hpr,basicOpen_subset_unramifiedLocus_iff.mp hr⟩
lemma exists_unramified_of_isUnramifiedAt [Algebra.FiniteType R A] (p:Ideal A) [p.IsPrime]
    [IsUnramifiedAt R p]:∃ f∉p,Algebra.Unramified R (Localization.Away f):=by
  obtain ⟨f,hfp,H⟩:=exists_formallyUnramified_of_isUnramifiedAt (R:=R) p
  exact ⟨f,hfp,⟨H,.trans ‹_› (IsLocalization.finiteType_of_monoid_fg (.powers f) _)⟩⟩
end
end Algebra
