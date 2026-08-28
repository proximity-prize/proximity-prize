/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_GroupTheory_Submonoid_Inverses

/-!
Permitted flat proof port of Mathlib.RingTheory.Localization.InvSubmonoid.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: 998111af42397bc302fa3267a25a5641fad64ba50e7ac873b537bd577ac1af87.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-! .














 -/

section ProximityFlatProofPort


variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S]

open Function

namespace IsLocalization

section InvSubmonoid

/-- . -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).leftInv

variable [IsLocalization M S]

theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

/-- . -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

/-- . -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)

theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)

@[simp]
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ (submonoid_map_le_is_unit _ _) _

@[simp]
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ (submonoid_map_le_is_unit _ _) ⟨_, _⟩

@[simp]
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert! mul_toInvSubmonoid M S m
  ext
  rw [← Algebra.smul_def]
  rfl

variable {S}

--
--
theorem surj'' (z : S) : ∃ (r : R) (m : M), z = r • (toInvSubmonoid M S m : S) := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine ⟨r, m, ?_⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp

theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp

theorem mem_invSubmonoid_iff_exists_mk' (x : S) :
    x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x := by
  simp_rw [← toInvSubmonoid_eq_mk']
  exact ⟨fun h => ⟨_, congr_arg Subtype.val (toInvSubmonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
    fun h => h.choose_spec ▸ (toInvSubmonoid M S h.choose).prop⟩

variable (S)

theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (toInvSubmonoid M S m).prop)

theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S := by
  have := Monoid.fg_of_surjective _ (toInvSubmonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ (Subalgebra.toSubmodule (Algebra.adjoin R _ : Subalgebra R S) : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_invSubmonoid]
  trivial

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (M : Submonoid S) [Monoid.FG M] : Algebra.FiniteType R (Localization M) :=
  .trans ‹_› (IsLocalization.finiteType_of_monoid_fg M _)

end InvSubmonoid

end IsLocalization
