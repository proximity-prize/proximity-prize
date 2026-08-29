import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AffinePointValuation


/-!
# Actual point valuations on an arbitrary embedded overring

Model label: gpt-5.

Let S be a Dedekind domain with fraction field L, and let S -> B -> L
be a compatible embedding. A field-valued point of B restricting to a
nonzero prime p of S forces ALL of B into the actual p-adic unit ball.
Moreover, its zeros are exactly the elements with valuation below one.

The proof uses actual fractions in S localized at p. It requires neither
B to be Dedekind nor B to be integral over S. This is the bridge needed
when an affine coordinate projection is not globally finite.
-/

namespace ProximityPrize.SubmissionLower.AffineOverringPointValuation

open IsDedekindDomain

noncomputable section

section Fractions

variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L]
  [Algebra S L] [IsFractionRing S L]

theorem base_value_lt_one_iff (p : HeightOneSpectrum S) (a : S) :
    p.valuation L (algebraMap S L a) < 1 ↔ a ∈ p.asIdeal := by
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem denominator_value_one (p : HeightOneSpectrum S) (b : S)
    (hb : b ∉ p.asIdeal) : p.valuation L (algebraMap S L b) = 1 := by
  apply le_antisymm
  · rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact p.intValuation_le_one b
  · exact le_of_not_gt fun h => hb ((base_value_lt_one_iff p b).mp h)

theorem denominator_ne_zero (p : HeightOneSpectrum S) (b : S)
    (hb : b ∉ p.asIdeal) : algebraMap S L b ≠ 0 := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ p.asIdeal.zero_mem)
  simpa only [map_zero] using (IsFractionRing.injective S L).ne hb0

/-- Unit-ball membership gives an actual denominator outside the center,
using equality with the actual prime localization. -/
theorem fraction_of_value_le_one (p : HeightOneSpectrum S) (x : L)
    (hx : p.valuation L x ≤ 1) :
    ∃ a b : S, b ∉ p.asIdeal ∧ x * algebraMap S L b = algebraMap S L a := by
  have hm : x ∈ HeightOneSpectrum.valuationSubringAtPrime L p := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hx
  rcases hm with ⟨a, b, hb, rfl⟩
  refine ⟨a, b, hb, ?_⟩
  simp [denominator_ne_zero p b hb]

end Fractions

section Overring

variable {K S B L : Type*} [Field K] [CommRing S] [IsDedekindDomain S]
  [CommRing B] [Field L]
  [Algebra S B] [Algebra S L] [Algebra B L] [IsScalarTower S B L]
  [IsFractionRing S L]

variable (hinj : Function.Injective (algebraMap B L))
variable (p : HeightOneSpectrum S) (Φ : B →+* K)
variable (hker : RingHom.ker (Φ.comp (algebraMap S B)) = p.asIdeal)

include hker in
theorem base_point_zero_iff (a : S) :
    Φ (algebraMap S B a) = 0 ↔ a ∈ p.asIdeal := by
  rw [← hker]
  rfl

include hinj

theorem lift_multiplication (x : B) (a b : S)
    (h : algebraMap B L x * algebraMap S L a = algebraMap S L b) :
    x * algebraMap S B a = algebraMap S B b := by
  apply hinj
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply S B L] using h

/-- The reciprocal of an overring element with value at least one has an
actual prime-local fraction; clearing it gives x*a=b in the overring. -/
theorem inverse_fraction (x : B)
    (hx : 1 ≤ p.valuation L (algebraMap B L x)) :
    ∃ a b : S, b ∉ p.asIdeal ∧
      x * algebraMap S B a = algebraMap S B b ∧
      p.valuation L (algebraMap S L a) =
        (p.valuation L (algebraMap B L x))⁻¹ := by
  have hv0 : p.valuation L (algebraMap B L x) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hx)
  have hx0 : algebraMap B L x ≠ 0 := (Valuation.ne_zero_iff _).mp hv0
  have hi : p.valuation L ((algebraMap B L x)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hx
  obtain ⟨a, b, hb, hab⟩ := fraction_of_value_le_one p ((algebraMap B L x)⁻¹) hi
  have hmul : algebraMap B L x * algebraMap S L a = algebraMap S L b := by
    rw [← hab, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  have hval : p.valuation L (algebraMap S L a) =
      (p.valuation L (algebraMap B L x))⁻¹ := by
    rw [← hab, map_mul, map_inv₀, denominator_value_one p b hb, mul_one]
  exact ⟨a, b, hb, lift_multiplication hinj x a b hmul, hval⟩

include hker in
/-- The actual point forces every element of B into this valuation ring;
no integrality of B over S is assumed. -/
theorem overring_value_le_one (x : B) :
    p.valuation L (algebraMap B L x) ≤ 1 := by
  by_contra h
  have hx : 1 < p.valuation L (algebraMap B L x) := lt_of_not_ge h
  obtain ⟨a, b, hb, hmul, hval⟩ := inverse_fraction hinj p x hx.le
  have ha : a ∈ p.asIdeal := (base_value_lt_one_iff p a).mp (by
    rw [hval]
    exact inv_lt_one_of_one_lt₀ hx)
  have hzero := (base_point_zero_iff p Φ hker a).mpr ha
  have hnonzero : Φ (algebraMap S B b) ≠ 0 := by
    exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
  have heq := congrArg Φ hmul
  rw [map_mul, hzero, mul_zero] at heq
  exact hnonzero heq.symm

include hker in
theorem overring_value_lt_one_of_point_zero (x : B) (hzero : Φ x = 0) :
    p.valuation L (algebraMap B L x) < 1 := by
  by_contra h
  obtain ⟨a, b, hb, hmul, _⟩ := inverse_fraction hinj p x (le_of_not_gt h)
  have hnonzero : Φ (algebraMap S B b) ≠ 0 := by
    exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
  have heq := congrArg Φ hmul
  rw [map_mul, hzero, zero_mul] at heq
  exact hnonzero heq.symm

include hker in
theorem point_zero_of_overring_value_lt_one (x : B)
    (hx : p.valuation L (algebraMap B L x) < 1) : Φ x = 0 := by
  obtain ⟨a, b, hb, hab⟩ := fraction_of_value_le_one p (algebraMap B L x) hx.le
  have hval : p.valuation L (algebraMap S L a) < 1 := by
    rw [← hab, map_mul, denominator_value_one p b hb, mul_one]
    exact hx
  have ha := (base_value_lt_one_iff p a).mp hval
  have hzero := (base_point_zero_iff p Φ hker a).mpr ha
  have hnonzero : Φ (algebraMap S B b) ≠ 0 := by
    exact fun hz => hb ((base_point_zero_iff p Φ hker b).mp hz)
  have heq := congrArg Φ (lift_multiplication hinj x b a hab)
  rw [map_mul, hzero] at heq
  exact (mul_eq_zero.mp heq).resolve_right hnonzero

include hker in
theorem overring_value_lt_one_iff (x : B) :
    p.valuation L (algebraMap B L x) < 1 ↔ Φ x = 0 :=
  ⟨point_zero_of_overring_value_lt_one hinj p Φ hker x,
    overring_value_lt_one_of_point_zero hinj p Φ hker x⟩

include hker in
theorem overring_zero_order_ge_one (x : B) (hx : x ≠ 0) (hzero : Φ x = 0) :
    1 ≤ -(p.valuation L (algebraMap B L x)).log := by
  have hv0 : p.valuation L (algebraMap B L x) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by
      simpa only [map_zero] using hinj.ne hx)
  have hvlt := overring_value_lt_one_of_point_zero hinj p Φ hker x hzero
  have hlog : (p.valuation L (algebraMap B L x)).log < (0 : ℤ) := by
    simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
  omega

end Overring

end

end ProximityPrize.SubmissionLower.AffineOverringPointValuation
