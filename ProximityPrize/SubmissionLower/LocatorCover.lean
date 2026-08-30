import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorCover
open RCN259
noncomputable section
variable {R S I : Type*} [CommRing R] [GCDMonoid R]
variable [CommRing S] [IsDomain S]
local instance : DecidableEq S := Classical.decEq S
local instance : DecidableEq I := Classical.decEq I

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
  simpa only [fixed, residual] using
    Finset.card_filter_add_card_filter_not (s := seeds)
      (fun i => phi i (gcd12 a b) = 0)

theorem fixed_vanish (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (i : I) (hi : i ∈ fixed phi seeds a b) : phi i (gcd12 a b) = 0 := by
  classical
  have hm : i ∈ seeds ∧ phi i (gcd12 a b) = 0 := by
    simpa only [fixed, Finset.mem_filter] using hi
  exact hm.2

theorem residual_vanish (phi : I → R →+* S) (seeds : Finset I) (a b : R)
    (ha : ∀ i ∈ seeds, phi i a = 0) (hb : ∀ i ∈ seeds, phi i b = 0)
    (i : I) (hi : i ∈ residual phi seeds a b) :
    phi i (quotientA a b) = 0 ∧ phi i (quotientB a b) = 0 := by
  classical
  have hm : i ∈ seeds ∧ phi i (gcd12 a b) ≠ 0 := by
    simpa only [residual, Finset.mem_filter] using hi
  exact quotient_vanish (phi i) a b (ha i hm.1) (hb i hm.1) hm.2

end
end ProximityPrize.SubmissionLower.LocatorCover
