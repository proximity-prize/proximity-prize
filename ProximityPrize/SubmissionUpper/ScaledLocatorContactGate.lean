/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionUpper.ProjectiveMomentLineGate

/-!
# Affinely scaled locator and common-contact gates

For the prospective `1024`-point outer fibres, let a selector locator have degree `136`.
Multiplying it by a selector-dependent scalar can cancel its leading coefficient against the
fixed affine received-word pencil.  If that scalar is

`scale = a + gamma * b`,

the next scaled coefficient and every cancelled common-root contact have the same projective
shape.  This file records the exact obstruction that shape imposes.

* If the scale is determined by one of `256` product states, injectivity of the challenges caps
  the family by `256`.  Thus normalising the constant coefficient does not absorb the product
  key while retaining a large challenge set.
* At a cancelled common root, an affine code value has the equation

  `(a + gamma * b) * iota(contact) = c + gamma * d`.

  When the two coefficient columns have nonzero determinant, the contact determines `gamma`, so
  an injectively labelled family has at most `|K|` members.  When the determinant is zero and the
  scale is nonzero, the contact is one fixed base-field value.
* Consequently a common shear of two contact values cannot make both physical common-block
  values affine in one challenge.  Either one block confines the challenge to a base-field line,
  or both contacts are fixed on the family.  A shear can package two values abstractly, but the
  two separate agreement equations still obey this dichotomy.

The final arithmetic gates quantify partial contact.  In the general two-common-block cell the
noncommon blocks and the degree-`1023` core contribute only `138239` agreements, so every record
needs `1543` of the `2048` contact slots.  Even after granting `|K|` nonexceptional records to
every slot, one exact contact-value fibre must contain at least
`207175419488376878` records.  In the antipodal two-common-block cell the two contacts coincide;
the parity gain raises the baseline to `139263`, but its remaining `519` contacts still force an
exact fibre of size `69685055432679334`.

There is one especially close structured attempt.  Fix the two common roots with `z² = -1`,
the two reserved roots with `z² = 1`, one further antipodal pair `z² = s`, and choose `33`
of the remaining `62` quartic orbits.  Its locator is

`(z² + 1) * (z² - s) * D(z⁴)`.

The raw family has `choose 62 33 > challengeThreshold` members and needs no coefficient pins.
An off-grid root in the `z⁴` coordinate leaves outer degree `126`, but the common contact is
`D(1)`.  Deleting one of the `33` roots reconstructs it from a fixed nonzero value of `D(1)`, so
every exact contact fibre has at most `floor(choose 62 32 / 33) = 13663142945940429` records.
This is far below the partial-contact incidence requirement, closing this concrete survivor even
when affine scaling is allowed.

These are reduction gates, not global impossibility theorems: an attack may still try to build
the displayed exceptional fibres.  The companion exact audit checks the selector counts and
degree ledgers.
-/

namespace ProximityPrize.SubmissionUpper.ScaledLocatorContactGate

open ProximityPrize.SubmissionUpper.ProjectiveMomentLineGate

/-! ## A finite state cannot be hidden in an injective affine scale -/

/-- If an affine scale factors through a finite state set, injective challenges make the state
map injective as well.  This is the abstract form of normalising a locator by its product. -/
theorem affine_scale_family_card_le_state
    {C F U : Type*} [Fintype C] [Field F] [DecidableEq U]
    (S : Finset U) (state : U → C) (value : C → F) (challenge : U → F)
    (a b : F) (hb : b ≠ 0)
    (hchallenge : Set.InjOn challenge (S : Set U))
    (hscale : ∀ u ∈ S, a + challenge u * b = value (state u)) :
    S.card ≤ Fintype.card C := by
  classical
  have hstate : Set.InjOn state (S : Set U) := by
    intro u hu v hv huv
    apply hchallenge hu hv
    apply (mul_right_cancel₀ hb)
    have hu' := hscale u hu
    have hv' := hscale v hv
    rw [huv] at hu'
    linear_combination hu' - hv'
  calc
    S.card = (S.image state).card := (Finset.card_image_iff.mpr hstate).symm
    _ ≤ (Finset.univ : Finset C).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card C := Finset.card_univ

/-! ## One scaled contact is a projective rank-one equation -/

/-- In the determinant-zero branch, a nonzero affine scale forces one fixed contact value. -/
theorem scaled_contact_fixed_of_det_zero
    {K F : Type*} [Field K] [Field F] (iota : K →+* F)
    {a b c d gamma : F} {contact : K}
    (hb : b ≠ 0)
    (hscale : a + gamma * b ≠ 0)
    (hdet : a * d - c * b = 0)
    (hcontact : c + gamma * d = (a + gamma * b) * iota contact) :
    iota contact = d / b := by
  have hc : c = a * (d / b) := by
    field_simp [hb]
    linear_combination -hdet
  have hright : c + gamma * d = (a + gamma * b) * (d / b) := by
    rw [hc]
    field_simp [hb]
  apply (mul_left_cancel₀ hscale)
  rw [← hcontact, hright]

/-- For a family satisfying two physical contact equations, either one contact column is
projectively nondegenerate and the family has at most `|K|` records, or both contacts are fixed.
This is the precise obstruction to replacing the two equations by one common shear. -/
theorem two_scaled_contacts_family_dichotomy
    {K F U : Type*} [Field K] [Field F] [Fintype K] [DecidableEq U]
    (iota : K →+* F) (S : Finset U)
    (challenge : U → F) (contact₁ contact₂ : U → K)
    (a b c₁ d₁ c₂ d₂ : F)
    (hb : b ≠ 0)
    (hchallenge : Set.InjOn challenge (S : Set U))
    (hscale : ∀ u ∈ S, a + challenge u * b ≠ 0)
    (hcontact₁ : ∀ u ∈ S,
      c₁ + challenge u * d₁ = (a + challenge u * b) * iota (contact₁ u))
    (hcontact₂ : ∀ u ∈ S,
      c₂ + challenge u * d₂ = (a + challenge u * b) * iota (contact₂ u)) :
    S.card ≤ Fintype.card K ∨
      ((∀ u ∈ S, iota (contact₁ u) = d₁ / b) ∧
        (∀ u ∈ S, iota (contact₂ u) = d₂ / b)) := by
  by_cases hdet₁ : a * d₁ - c₁ * b ≠ 0
  · left
    exact projective_moment_family_card_le_base iota S challenge
      (fun u ↦ a + challenge u * b) contact₁ a c₁ b d₁ hdet₁ hchallenge
      (by intro u hu; rfl) hcontact₁
  · by_cases hdet₂ : a * d₂ - c₂ * b ≠ 0
    · left
      exact projective_moment_family_card_le_base iota S challenge
        (fun u ↦ a + challenge u * b) contact₂ a c₂ b d₂ hdet₂ hchallenge
        (by intro u hu; rfl) hcontact₂
    · right
      have hdet₁' : a * d₁ - c₁ * b = 0 := not_ne_iff.mp hdet₁
      have hdet₂' : a * d₂ - c₂ * b = 0 := not_ne_iff.mp hdet₂
      constructor
      · intro u hu
        exact scaled_contact_fixed_of_det_zero iota hb (hscale u hu) hdet₁'
          (hcontact₁ u hu)
      · intro u hu
        exact scaled_contact_fixed_of_det_zero iota hb (hscale u hu) hdet₂'
          (hcontact₂ u hu)

/-- In the antipodal common-pair cell the two reduced cofactor contacts are equal.  Any one
linear shear of them therefore still factors through a single base-field value. -/
theorem equal_contact_shear_image_card_le_base
    {K F U : Type*} [Field K] [Field F] [Fintype K] [DecidableEq U] [DecidableEq F]
    (iota : K →+* F) (S : Finset U) (contact₁ contact₂ : U → K)
    (theta : F) (hequal : ∀ u ∈ S, contact₁ u = contact₂ u) :
    (S.image fun u ↦ iota (contact₁ u) + theta * iota (contact₂ u)).card ≤
      Fintype.card K := by
  classical
  let shear : K → F := fun x ↦ iota x + theta * iota x
  have hsubset :
      S.image (fun u ↦ iota (contact₁ u) + theta * iota (contact₂ u)) ⊆
        (Finset.univ : Finset K).image shear := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨contact₁ u, Finset.mem_univ _, ?_⟩
    simp only [shear]
    rw [hequal u hu]
  calc
    (S.image fun u ↦ iota (contact₁ u) + theta * iota (contact₂ u)).card ≤
        ((Finset.univ : Finset K).image shear).card := Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset K).card := Finset.card_image_le
    _ = Fintype.card K := Finset.card_univ

/-! ## Benchmark receipts and partial-contact concentration -/

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088
def productStateCount : ℕ := 256

def oneCommonNeededContacts : ℕ := 519
def oneCommonContactSlots : ℕ := 1024
def oneCommonExceptionalFibreFloor : ℕ := 139370112996065101

def twoCommonNeededContacts : ℕ := 1543
def twoCommonContactSlots : ℕ := 2048
def twoCommonExceptionalFibreFloor : ℕ := 207175419488376878

def antipodalNeededContacts : ℕ := 519
def antipodalContactSlots : ℕ := 2048
def antipodalExceptionalFibreFloor : ℕ := 69685055432679334

def quarticOrbitSelectorCount : ℕ := 409894288378212890
def quarticDeletionBases : ℕ := 450883717216034179
def quarticContactFibreCap : ℕ := 13663142945940429

theorem benchmark_capacity_receipt :
    productStateCount < baseFieldCardinality ∧
      baseFieldCardinality < challengeThreshold := by
  norm_num [productStateCount, baseFieldCardinality, challengeThreshold]

/-- The `h=0,1,2` scaled-locator degree ledger with block size `1024`, selector weight `136`,
and six fixed projective high coefficients. -/
theorem benchmark_scaled_degree_ledger :
    136 - 6 - 1 = 129 ∧
      135 - 6 - 1 = 128 ∧
      134 - 6 - 1 = 127 ∧
      129 - 2 = 127 ∧
      128 - 1 = 127 := by
  norm_num

theorem benchmark_general_common_agreement_ledger :
    136 * 1024 + 1023 = 140287 ∧
      135 * 1024 + 1023 = 139263 ∧
      134 * 1024 + 1023 = 138239 ∧
      139782 - 139263 = oneCommonNeededContacts ∧
      139782 - 138239 = twoCommonNeededContacts := by
  norm_num [oneCommonNeededContacts, twoCommonNeededContacts]

/-- One cancelled common block needs `519` contacts.  If every nonexceptional affine contact
line contains at most `|K|` injective challenges, incidence forces the displayed exact contact
fibre. -/
theorem one_common_incidence_forces_exceptional_fibre
    (records incidences maxExceptionalFibre : ℕ)
    (hrecords : challengeThreshold ≤ records)
    (hlower : oneCommonNeededContacts * records ≤ incidences)
    (hupper : incidences ≤
      oneCommonContactSlots * (baseFieldCardinality + maxExceptionalFibre)) :
    oneCommonExceptionalFibreFloor ≤ maxExceptionalFibre := by
  norm_num [challengeThreshold, oneCommonNeededContacts, oneCommonContactSlots,
    baseFieldCardinality, oneCommonExceptionalFibreFloor] at hrecords hlower hupper ⊢
  omega

/-- In the general two-common-block cell, `1543` contacts among `2048` slots force a single
exact contact-value fibre containing more than three quarters of a threshold-sized subfamily. -/
theorem two_common_incidence_forces_exceptional_fibre
    (records incidences maxExceptionalFibre : ℕ)
    (hrecords : challengeThreshold ≤ records)
    (hlower : twoCommonNeededContacts * records ≤ incidences)
    (hupper : incidences ≤
      twoCommonContactSlots * (baseFieldCardinality + maxExceptionalFibre)) :
    twoCommonExceptionalFibreFloor ≤ maxExceptionalFibre := by
  norm_num [challengeThreshold, twoCommonNeededContacts, twoCommonContactSlots,
    baseFieldCardinality, twoCommonExceptionalFibreFloor] at hrecords hlower hupper ⊢
  omega

/-- The antipodal common pair has a `2047`-degree fixed core and equal contacts on its two
blocks.  Its remaining `519` incidences still force this exceptional one-value fibre. -/
theorem antipodal_common_incidence_forces_exceptional_fibre
    (records incidences maxExceptionalFibre : ℕ)
    (hrecords : challengeThreshold ≤ records)
    (hlower : antipodalNeededContacts * records ≤ incidences)
    (hupper : incidences ≤
      antipodalContactSlots * (baseFieldCardinality + maxExceptionalFibre)) :
    antipodalExceptionalFibreFloor ≤ maxExceptionalFibre := by
  norm_num [challengeThreshold, antipodalNeededContacts, antipodalContactSlots,
    baseFieldCardinality, antipodalExceptionalFibreFloor] at hrecords hlower hupper ⊢
  omega

theorem benchmark_antipodal_agreement_ledger :
    134 * 1024 + 2047 = 139263 ∧
      139782 - 139263 = antipodalNeededContacts := by
  norm_num [antipodalNeededContacts]

/-- The closest unpinned symmetry family already has enough raw challenges.  Its outer quotient
has degree `126`, leaving the `2047`-degree reserved core used above. -/
theorem benchmark_quartic_orbit_candidate_ledger :
    challengeThreshold < quarticOrbitSelectorCount ∧
      2 + 31 * 4 = 126 ∧
      126 * 1024 + 2047 = 131071 := by
  norm_num [challengeThreshold, quarticOrbitSelectorCount]

/-- Exact arithmetic for the one-root deletion injection on a fixed `D(1)` fibre. -/
theorem benchmark_quartic_contact_deletion_cap :
    33 * quarticContactFibreCap ≤ quarticDeletionBases ∧
      quarticDeletionBases < 33 * (quarticContactFibreCap + 1) ∧
      quarticContactFibreCap < antipodalExceptionalFibreFloor := by
  norm_num [quarticContactFibreCap, quarticDeletionBases,
    antipodalExceptionalFibreFloor]

/-- Once the deletion injection supplies the per-line cap, even a threshold-sized subfamily
cannot obtain `519` contacts among the two common `1024`-blocks. -/
theorem no_quartic_orbit_partial_contact
    (records incidences : ℕ)
    (hrecords : challengeThreshold ≤ records)
    (hlower : antipodalNeededContacts * records ≤ incidences)
    (hupper : incidences ≤ antipodalContactSlots *
      (baseFieldCardinality + quarticContactFibreCap)) : False := by
  norm_num [challengeThreshold, antipodalNeededContacts, antipodalContactSlots,
    baseFieldCardinality, quarticContactFibreCap] at hrecords hlower hupper ⊢
  omega

#print axioms affine_scale_family_card_le_state
#print axioms scaled_contact_fixed_of_det_zero
#print axioms two_scaled_contacts_family_dichotomy
#print axioms equal_contact_shear_image_card_le_base
#print axioms two_common_incidence_forces_exceptional_fibre
#print axioms no_quartic_orbit_partial_contact

end ProximityPrize.SubmissionUpper.ScaledLocatorContactGate
