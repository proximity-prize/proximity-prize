import ProximityPrize.SubmissionLower.HighPrice6921Core
import ProximityPrize.SubmissionLower.HighJoint6921
import ProximityPrize.SubmissionLower.Front6921

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighPrice6921

open K1 K1_14 HighJoint6921 Polynomial

/-- All finite tariff rows use the actual ordinate degree and its tested seed cap. -/
private theorem numeric_profile (b : HeightBand) (e : ℕ)
    (he : 0 < e) (hcap : e ≤ b.ordinateCap) :
    0 < b.seedCap e ∧ singularDegree e (b.seedCap e) < p ∧
      retainedPrice (131071+b.upper) e (b.seedCap e) ≤ K21.highRetained b.upper := by
  cases b
  · change e ≤ 12 at hcap
    interval_cases e <;> decide
  · change e ≤ 5 at hcap
    interval_cases e <;> decide
  · change e ≤ 3 at hcap
    interval_cases e <;> decide
  · change e ≤ 2 at hcap
    interval_cases e <;> decide

private theorem same_tariff (b : HeightBand) {w : ℤ}
    (hlo : (b.lower : ℤ) ≤ w) (hhi : w ≤ (b.upper : ℤ)) :
    K21.highRetained w = K21.highRetained b.upper := by
  cases b <;>
    simp only [HeightBand.lower, HeightBand.upper, Nat.cast_ofNat] at hlo hhi ⊢ <;>
    unfold K21.highRetained <;> split_ifs <;> omega

/-- Count retained labels from their actual covers, without invoking the
anchored-family type or any hypothesis about dropped labels. -/
theorem retained_count (b : HeightBand) {w : ℤ}
    (hlo : (b.lower : ℤ) ≤ w) (hhi : w ≤ (b.upper : ℤ))
    {word : I → K} {T : Finset K} {s : K → K[X]} {z : K → K} {f : Equation}
    (hword : FixedWord word T s (131071 + b.upper))
    (hlabel : Set.InjOn z (T : Set K)) (he : 0 < f.natDegree)
    (hprimitive : f.IsPrimitive)
    (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hcap : f.natDegree ≤ b.ordinateCap) (hseed : SeedBound f (b.seedCap f.natDegree))
    (hroots : ∀ γ ∈ T, atMark f (z γ) (s γ) = 0) :
    T.card ≤ K21.highRetained w := by
  have hd0 : 0 < 131071+b.upper := by omega
  have hd : 131071+b.upper < 180130 := by cases b <;> decide
  obtain ⟨hvp, hchar, hprice⟩ := numeric_profile b f.natDegree he hcap
  have h := retained_charge hword hlabel hd0 hd hvp he le_rfl hprimitive hsep hseed hchar hroots
  rw [same_tariff b hlo hhi]
  exact h.trans hprice

/-- Terminal mass certifies the adaptive retained count on the same equation. -/
theorem retained_of_mass (b : HeightBand) {h : ℕ}
    (hlo : b.lower ≤ h) (hhi : h ≤ b.upper)
    {word : I → K} {T : Finset K} {s : K → K[X]} {z : K → K} {f : Equation}
    (hword : FixedWord word T s (131071 + b.upper))
    (hlabel : Set.InjOn z (T : Set K)) (he : 0 < f.natDegree)
    (hprimitive : f.IsPrimitive)
    (hsep : (f.map (algebraMap Seeds (FractionRing Seeds))).Separable)
    (hfull : TerminalMass b.fullBank h f) (hseed : TerminalMass b.seedBank h f)
    (hroots : ∀ γ ∈ T, atMark f (z γ) (s γ) = 0) :
    T.card ≤ K21.highRetained (h : ℤ) := by
  have hf : f ≠ 0 := by
    intro hz
    simp [hz] at he
  obtain ⟨hcap, hv⟩ := terminal_bounds b hlo hhi hf he hfull hseed
  exact retained_count b (by exact_mod_cast hlo) (by exact_mod_cast hhi) hword hlabel he
    hprimitive hsep hcap hv hroots

end HighPrice6921
