import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphNormFixedContent6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveChallengeRatioRigidity6401
open Polynomial
open BCHKSFrobeniusOffsetProductDegreeAudit6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitiveFaithfulGraphGauge6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
section SixthChallengeTwist
variable {F : Type} [Field F] [DecidableEq F]
noncomputable def challengeFrobeniusIterateRingHom6401
    (sigma : F →+* F) (q : Nat) : Nat → F[X] →+* F[X]
  | 0 => RingHom.id F[X]
  | n + 1 => (challengeFrobeniusRingHom6401 sigma q).comp
      (challengeFrobeniusIterateRingHom6401 sigma q n)
noncomputable def challengeTwistSixRingHom6401
    (sigma : F →+* F) (q : Nat) : F[X] →+* F[X] :=
  challengeFrobeniusIterateRingHom6401 sigma q 6
theorem challengeFrobeniusIterateRingHom_injective6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) (n : Nat) :
    Function.Injective (challengeFrobeniusIterateRingHom6401 sigma q n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
      exact (challengeFrobeniusRingHom_injective6401 sigma q hq).comp ih
theorem challengeTwistSixRingHom_injective6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) :
    Function.Injective (challengeTwistSixRingHom6401 sigma q) := by
  exact challengeFrobeniusIterateRingHom_injective6401 sigma q hq 6
theorem challengeFrobeniusIterate_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (n : Nat) (P : F[X]) :
    (challengeFrobeniusIterateRingHom6401 sigma q n P).natDegree =
      P.natDegree * q ^ n := by
  induction n with
  | zero => simp [challengeFrobeniusIterateRingHom6401]
  | succ n ih =>
      rw [challengeFrobeniusIterateRingHom6401, RingHom.comp_apply,
        challengeFrobeniusRingHom_apply6401,
        challengeFrobenius_natDegree, ih, pow_succ]
      ring
theorem challengeTwistSix_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (P : F[X]) :
    (challengeTwistSixRingHom6401 sigma q P).natDegree =
      P.natDegree * q ^ 6 := by
  exact challengeFrobeniusIterate_natDegree_eq6401 sigma q 6 P
end SixthChallengeTwist
section ExpandingCross
variable {F : Type} [Field F] [DecidableEq F]
theorem coprime_expandingEndomorphism_cross_forces_constant6401
    (T : F[X] →+* F[X]) (Q : Nat) (hQ : 1 < Q)
    (hT : Function.Injective T)
    (hdegree : ∀ P : F[X], (T P).natDegree = P.natDegree * Q)
    (A B : F[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hcross : B * T A = A * T B) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  have hTA : T A ≠ 0 := by
    intro hzero
    apply hA
    apply hT
    simpa using hzero
  have hTB : T B ≠ 0 := by
    intro hzero
    apply hB
    apply hT
    simpa using hzero
  have hAdiv : A ∣ T A := by
    apply hcoprime.dvd_of_dvd_mul_left
    exact ⟨T B, hcross⟩
  have hBdiv : B ∣ T B := by
    apply hcoprime.symm.dvd_of_dvd_mul_left
    exact ⟨T A, hcross.symm⟩
  obtain ⟨UA, hUA⟩ := hAdiv
  obtain ⟨UB, hUB⟩ := hBdiv
  have hUAne : UA ≠ 0 := by
    intro hzero
    apply hTA
    rw [hUA, hzero, mul_zero]
  have hUBne : UB ≠ 0 := by
    intro hzero
    apply hTB
    rw [hUB, hzero, mul_zero]
  have hUeq : UA = UB := by
    have hprod : (A * B) * UA = (A * B) * UB := by
      calc
        (A * B) * UA = B * T A := by rw [hUA]; ring
        _ = A * T B := hcross
        _ = (A * B) * UB := by rw [hUB]; ring
    exact mul_left_cancel₀ (mul_ne_zero hA hB) hprod
  have hcoprimeT : IsCoprime (T A) (T B) := hcoprime.map T
  have hUAdivTA : UA ∣ T A := by
    refine ⟨A, ?_⟩
    rw [hUA]
    ring
  have hUAdivTB : UA ∣ T B := by
    refine ⟨B, ?_⟩
    rw [hUB, ← hUeq]
    ring
  have hUAunit : IsUnit UA :=
    hcoprimeT.isUnit_of_dvd' hUAdivTA hUAdivTB
  have hUAdegree : UA.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hUAunit
  constructor
  · have hmul := Polynomial.natDegree_mul hA hUAne
    rw [← hUA, hdegree A, hUAdegree, add_zero] at hmul
    by_contra hne
    have hpos : 0 < A.natDegree := Nat.pos_of_ne_zero hne
    have hlt : A.natDegree < A.natDegree * Q :=
      lt_mul_of_one_lt_right hpos hQ
    omega
  · have hmul := Polynomial.natDegree_mul hB hUBne
    rw [← hUB, hdegree B] at hmul
    have hUBdegree : UB.natDegree = 0 := by rw [← hUeq, hUAdegree]
    rw [hUBdegree, add_zero] at hmul
    by_contra hne
    have hpos : 0 < B.natDegree := Nat.pos_of_ne_zero hne
    have hlt : B.natDegree < B.natDegree * Q :=
      lt_mul_of_one_lt_right hpos hQ
    omega
theorem coprime_challengeTwistSix_cross_forces_constant6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hcross : B * challengeTwistSixRingHom6401 sigma q A =
      A * challengeTwistSixRingHom6401 sigma q B) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  apply coprime_expandingEndomorphism_cross_forces_constant6401
    (challengeTwistSixRingHom6401 sigma q) (q ^ 6)
  · exact one_lt_pow₀ hq (by norm_num)
  · exact challengeTwistSixRingHom_injective6401 sigma q
      (Nat.zero_lt_of_lt hq)
  · exact challengeTwistSix_natDegree_eq6401 sigma q
  · exact hA
  · exact hB
  · exact hcoprime
  · exact hcross
end ExpandingCross
section ScalarRatio
variable {F : Type} [Field F] [DecidableEq F]
theorem exists_commonPolynomial_constantMultiples_of_sixthTwist_cross6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (cA cB : F[X]) (hcA : cA ≠ 0) (hcB : cB ≠ 0)
    (hcross : cB * challengeTwistSixRingHom6401 sigma q cA =
      cA * challengeTwistSixRingHom6401 sigma q cB) :
    ∃ G : F[X], ∃ a b : F,
      G ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
        cA = G * Polynomial.C a ∧
        cB = G * Polynomial.C b := by
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  let G : F[X] := GCDMonoid.gcd cA cB
  let A : F[X] := cA / G
  let B : F[X] := cB / G
  have hG : G ≠ 0 := gcd_ne_zero_of_left hcA
  have hA : A ≠ 0 := left_div_gcd_ne_zero hcA
  have hB : B ≠ 0 := right_div_gcd_ne_zero hcB
  have hfactorA : G * A = cA := by
    exact EuclideanDomain.mul_div_cancel' hG
      (GCDMonoid.gcd_dvd_left cA cB)
  have hfactorB : G * B = cB := by
    exact EuclideanDomain.mul_div_cancel' hG
      (GCDMonoid.gcd_dvd_right cA cB)
  have hcoprime : IsCoprime A B := isCoprime_div_gcd_div_gcd hcB
  let T := challengeTwistSixRingHom6401 sigma q
  have hTG : T G ≠ 0 := by
    intro hzero
    apply hG
    apply challengeTwistSixRingHom_injective6401 sigma q
      (Nat.zero_lt_of_lt hq)
    simpa [T] using hzero
  have hreducedCross : B * T A = A * T B := by
    apply mul_left_cancel₀ (mul_ne_zero hG hTG)
    calc
      (G * T G) * (B * T A) = cB * T cA := by
        rw [← hfactorA, ← hfactorB, map_mul]
        ring
      _ = cA * T cB := by simpa only [T] using hcross
      _ = (G * T G) * (A * T B) := by
        rw [← hfactorA, ← hfactorB, map_mul]
        ring
  obtain ⟨hAdegree, hBdegree⟩ :=
    coprime_challengeTwistSix_cross_forces_constant6401
      sigma q hq A B hA hB hcoprime (by simpa only [T] using hreducedCross)
  let a : F := A.coeff 0
  let b : F := B.coeff 0
  have hAconst : A = Polynomial.C a :=
    Polynomial.eq_C_of_natDegree_eq_zero hAdegree
  have hBconst : B = Polynomial.C b :=
    Polynomial.eq_C_of_natDegree_eq_zero hBdegree
  have ha : a ≠ 0 := by
    intro hzero
    apply hA
    rw [hAconst, hzero, Polynomial.C_0]
  have hb : b ≠ 0 := by
    intro hzero
    apply hB
    rw [hBconst, hzero, Polynomial.C_0]
  exact ⟨G, a, b, hG, ha, hb,
    hfactorA.symm.trans (congrArg (G * ·) hAconst),
    hfactorB.symm.trans (congrArg (G * ·) hBconst)⟩
end ScalarRatio
end BCHKSExtremePrimitiveChallengeRatioRigidity6401
end ProximityPrize.SubmissionLower
