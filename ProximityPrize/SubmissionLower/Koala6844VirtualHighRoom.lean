import ProximityPrize.SubmissionLower.LowerPolynomialFoundation
import Mathlib.Data.Nat.Prime.Factorial



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

theorem pow_succ_dvd_of_room
    (D : Derivation K R R) (f H : R) (p room : ℕ) [CharP R p]
    (hp : p.Prime) (hroom : room < p) (hf : Prime f)
    (transverse : ¬ f ∣ D f)
    (survives : ∀ i ≤ room, f ∣ ((D : R → R)^[i]) H) :
    f ^ (room + 1) ∣ H := by
  classical
  by_contra hbad
  let missing : ∃ i : ℕ, ¬ f ^ i ∣ H := ⟨room+1,hbad⟩
  let n := Nat.find missing
  have hn : ¬ f ^ n ∣ H := Nat.find_spec missing
  have hnb : n ≤ room+1 := Nat.find_min' missing hbad
  have hnpos : 0 < n := by
    by_contra! hzero
    have hz : n = 0 := by omega
    exact hn (by simp [hz])
  let k := n-1
  have hk : k+1 = n := by omega
  have hle : k ≤ room := by omega
  have hdiv : f ^ k ∣ H := by
    by_contra h
    exact Nat.find_min missing (by omega : k < n) h
  obtain ⟨u, hu⟩ := hdiv
  have hunit : IsUnit (k.factorial : R) := by
    apply (CharP.isUnit_natCast_iff hp).mpr
    exact fun h => (not_le_of_gt (hle.trans_lt hroom)) ((Nat.Prime.dvd_factorial hp).mp h)
  have hnotu : ¬ f ∣ u := by
    rintro ⟨v, rfl⟩
    apply hn
    rw [← hk, hu, pow_succ, ← mul_assoc]
    exact dvd_mul_right _ _
  obtain ⟨error, hexp⟩ := RCN324.iterate_pow_mul_expansion D f u k k le_rfl
  have deriv := survives k hle
  rw [hu, hexp] at deriv
  simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, zero_add,
    pow_one] at deriv
  have hdvd : f ∣ (k.factorial : R) * u * (D f)^k :=
    (dvd_add_left (dvd_mul_right f error)).mp deriv
  rcases hf.dvd_mul.mp hdvd with hconst | hpow
  · rcases hf.dvd_mul.mp hconst with h | h
    · exact hf.not_isUnit (isUnit_of_dvd_unit h hunit)
    · exact hnotu h
  · exact transverse (hf.dvd_of_dvd_pow hpow)

theorem residual_caps_of_room {y b c : ℕ}
    (hy : (31+1)*y ≤ 1451) (hb : (31+1)*b ≤ 32586) (hc : (31+1)*c ≤ 32586) :
    y ≤ 45 ∧ b ≤ 1018 ∧ c ≤ 1018 := by omega

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
