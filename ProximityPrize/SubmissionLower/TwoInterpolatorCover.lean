import ProximityPrize.SubmissionLower.AB
import ProximityPrize.SubmissionLower.RegularColonArithmetic
namespace ProximityPrize.SubmissionLower.TwoInterpolatorCover
open RCN259 RegularColonArithmetic
noncomputable section
variable {R S I : Type*} [CommRing R] [GCDMonoid R]
variable [CommRing S] [IsDomain S]

theorem quotient_vanish (phi : R →+* S) (a b : R)
    (ha : phi a = 0) (hb : phi b = 0) (hg : phi (gcd12 a b) ≠ 0) :
    phi (quotientA a b) = 0 ∧ phi (quotientB a b) = 0 := by
  rw [a_eq_gcd12_mul_quotientA a b, map_mul] at ha
  rw [b_eq_gcd12_mul_quotientB a b, map_mul] at hb
  exact ⟨(mul_eq_zero.mp ha).resolve_left hg, (mul_eq_zero.mp hb).resolve_left hg⟩

def fixed (phi : I → R →+* S) (seeds : Finset I) (a b : R) : Finset I := by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) = 0)
def residual (phi : I → R →+* S) (seeds : Finset I) (a b : R) : Finset I := by
  classical
  exact seeds.filter (fun i => phi i (gcd12 a b) ≠ 0)

theorem partition_card (phi : I → R →+* S) (seeds : Finset I) (a b : R) :
    (fixed phi seeds a b).card + (residual phi seeds a b).card = seeds.card := by
  classical
  exact Finset.card_filter_add_card_filter_not (s := seeds)
    (fun i => phi i (gcd12 a b) = 0)

theorem fixed_vanish (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (i : I) (hi : i ∈ fixed phi seeds a b) : phi i (gcd12 a b) = 0 := by
  classical
  exact (Finset.mem_filter.mp hi).2

theorem residual_vanish (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (ha : ∀ i ∈ seeds, phi i a = 0) (hb : ∀ i ∈ seeds, phi i b = 0)
    (i : I) (hi : i ∈ residual phi seeds a b) :
    phi i (quotientA a b) = 0 ∧ phi i (quotientB a b) = 0 := by
  classical
  have hm := Finset.mem_filter.mp hi
  exact quotient_vanish (phi i) a b (ha i hm.1) (hb i hm.1) hm.2

/- This is a ledger interface, not an unconditional seed bound.
   Its fixed and residual hypotheses must be supplied by the counting proofs. -/
theorem count_lt_ledger (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (T lt : ℕ)
    (hf : (fixed phi seeds a b).card ≤
      fixedCost (T - 53) 40 10 + (fixedSingular T).countCap)
    (hr : (residual phi seeds a b).card <
      (residualStage lt).regularCountCap + (residualSingular lt).countCap + 1) :
    seeds.card < ledger T lt := by
  have hp := partition_card phi seeds a b
  unfold ledger
  omega

theorem count_lt_budget (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (t : ℕ) (ht : t ≤ 1282)
    (hlow : t ≤ 1280 →
      (fixed phi seeds a b).card ≤ fixedCost (1280 - 53) 40 10 +
        (fixedSingular 1280).countCap ∧
      (residual phi seeds a b).card < (residualStage 0).regularCountCap +
        (residualSingular 0).countCap + 1)
    (hhigh : 1281 ≤ t → t ≤ 1282 →
      (fixed phi seeds a b).card ≤ fixedCost (1282 - 53) 40 10 +
        (fixedSingular 1282).countCap ∧
      (residual phi seeds a b).card < (residualStage 1281).regularCountCap +
        (residualSingular 1281).countCap + 1) : seeds.card < budget := by
  by_cases h : t ≤ 1280
  · obtain ⟨hf, hr⟩ := hlow h
    exact (count_lt_ledger phi seeds a b 1280 0 hf hr).trans low_ledger_lt
  · obtain ⟨hf, hr⟩ := hhigh (by omega) ht
    exact (count_lt_ledger phi seeds a b 1282 1281 hf hr).trans high_ledger_lt
end
end ProximityPrize.SubmissionLower.TwoInterpolatorCover
