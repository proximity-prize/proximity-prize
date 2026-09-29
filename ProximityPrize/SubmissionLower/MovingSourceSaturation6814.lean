import ProximityPrize.SubmissionLower.MovingSourceProperness6814

/-! Construct globally coprime cleared cuts by removing their gcd. The gcd
has no zeros away from the original denominator, so the regular zero set
is unchanged. This is the clearing exception, not an assumed adapter. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSaturation6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open UniqueFactorizationMonoid MovingSourceClearing6814 MovingSourceProperness6814 RCN259

variable {R : Type*} [CommRing R] [IsDomain R]
  [GCDMonoid (Polynomial R)] [NormalizationMonoid (Polynomial R)]
  [UniqueFactorizationMonoid (Polynomial R)]

theorem cleared_gcd_nonzero_at {E : Type*} [CommRing E] [IsDomain E]
    (P Q : Polynomial R) (n m : ℕ) (h q : R)
    (hP : P≠0) (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) (hh : h≠0)
    (hrel : IsRelPrime P Q) (ev : Polynomial R →+* E) (hev : ev (Polynomial.C h)≠0) :
    ev (gcd (targetPolynomial P n h q) (targetPolynomial Q m h q))≠0 := by
  classical
  let A := targetPolynomial P n h q
  let B := targetPolynomial Q m h q
  have hA : A≠0 := targetPolynomial_ne_zero P n h q hP hn hh
  have hG : gcd A B≠0 := gcd_ne_zero_of_left hA
  intro hz
  have hassoc := Associated.map ev (prod_normalizedFactors hG)
  rw [hz] at hassoc
  have hp : ev (normalizedFactors (gcd A B)).prod=0 := (associated_zero_iff_eq_zero _).mp hassoc
  rw [map_multiset_prod] at hp
  obtain ⟨f,hf,hfzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
  have hfi : Irreducible f := irreducible_of_normalized_factor f hf
  have hfg := dvd_of_mem_normalizedFactors hf
  have hfh : f ∣ Polynomial.C h := common_prime_dvd_denominator P Q n m h q hn hm hh hrel
    f hfi.prime (hfg.trans (gcd_dvd_left A B)) (hfg.trans (gcd_dvd_right A B))
  obtain ⟨g,hg⟩ := hfh
  apply hev
  rw [hg,map_mul,hfzero,zero_mul]

theorem exists_coprime_cleared_pair
    (P Q : Polynomial R) (n m : ℕ) (h q : R)
    (hP : P≠0) (hQ : Q≠0) (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m)
    (hh : h≠0) (hrel : IsRelPrime P Q) :
    ∃ A B : Polynomial R, A≠0 ∧ B≠0 ∧ IsRelPrime A B ∧
      A ∣ targetPolynomial P n h q ∧ B ∣ targetPolynomial Q m h q ∧
      ∀ (E : Type*) [CommRing E] [IsDomain E] (ev : Polynomial R →+* E),
        ev (Polynomial.C h)≠0 →
        ((ev A=0 ↔ ev (targetPolynomial P n h q)=0) ∧
         (ev B=0 ↔ ev (targetPolynomial Q m h q)=0)) := by
  let P0 := targetPolynomial P n h q
  let Q0 := targetPolynomial Q m h q
  let A := leftGCDQuotient P0 Q0
  let B := rightGCDQuotient P0 Q0
  have hP0 : P0≠0 := targetPolynomial_ne_zero P n h q hP hn hh
  have hQ0 : Q0≠0 := targetPolynomial_ne_zero Q m h q hQ hm hh
  have hpa : P0=gcd P0 Q0*A := left_eq_gcd_mul_leftGCDQuotient P0 Q0
  have hqb : Q0=gcd P0 Q0*B := right_eq_gcd_mul_rightGCDQuotient P0 Q0
  have hA : A≠0 := by intro hz; exact hP0 (by rw [hpa,hz,mul_zero])
  have hB : B≠0 := by intro hz; exact hQ0 (by rw [hqb,hz,mul_zero])
  refine ⟨A,B,hA,hB,gcdQuotients_isRelPrime hP0,?_,?_,?_⟩
  · exact ⟨gcd P0 Q0,hpa.trans (mul_comm _ _)⟩
  · exact ⟨gcd P0 Q0,hqb.trans (mul_comm _ _)⟩
  · intro E _ _ ev hev
    have hg := cleared_gcd_nonzero_at P Q n m h q hP hn hm hh hrel ev hev
    change ev (gcd P0 Q0)≠0 at hg
    change (ev A=0 ↔ ev P0=0) ∧ (ev B=0 ↔ ev Q0=0)
    have hpv := congrArg ev hpa
    have hqv := congrArg ev hqb
    simp only [map_mul] at hpv hqv
    rw [hpv,hqv]
    simp only [mul_eq_zero,hg,false_or,and_self]

#print axioms cleared_gcd_nonzero_at
#print axioms exists_coprime_cleared_pair
end
end ProximityPrize.SubmissionLower.MovingSourceSaturation6814
