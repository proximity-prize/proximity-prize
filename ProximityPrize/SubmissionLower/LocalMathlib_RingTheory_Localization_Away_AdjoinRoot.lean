/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense

/-!
Permitted flat proof port of Mathlib.RingTheory.Localization.Away.AdjoinRoot.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 3dd1eb23af494ca086b108075fd260807423faf01e096edcacd17a105d91580d.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
Port elaboration adjustment: explicitly qualify the original polynomial-variable
constant. This prevents target notation capture;
all statements and mathematical arguments are retained.
-/

/-! .


 -/

section ProximityFlatProofPort

open Polynomial AdjoinRoot Localization

variable {R : Type*} [CommRing R]

attribute [local instance] AdjoinRoot.algHom_subsingleton

/-- .
 -/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * Polynomial.X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers r)) _ _)

theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * Polynomial.X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)

theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
  (AdjoinRoot.finitePresentation _).equiv <|
    (Localization.awayEquivAdjoin r).symm.trans <| IsLocalization.algEquiv (Submonoid.powers r) _ _

lemma Algebra.FinitePresentation.of_isLocalizationAway
    {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] (f : S) [IsLocalization.Away f S']
    [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R S' :=
  have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'

instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (f : S) :
    Algebra.FinitePresentation R (Localization.Away f) :=
  .of_isLocalizationAway f

instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (f : S) :
    Algebra.FiniteType R (Localization.Away f) :=
  .trans ‹_› inferInstance
