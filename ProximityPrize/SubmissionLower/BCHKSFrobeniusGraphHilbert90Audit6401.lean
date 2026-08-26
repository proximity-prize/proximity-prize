import ProximityPrize.SubmissionLower.BCHKSFrobeniusHilbert90Normalization6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusOffsetProductDegreeAudit6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailKernelCrossGlobal6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGraphHilbert90Audit6401
open Polynomial
open BCHKSFrobeniusGraphInjectivity6401
open BCHKSFrobeniusOffsetProductDegreeAudit6401
open BCHKSFrobeniusHilbert90Normalization6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusKeyEquationFork6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section GraphTwist
variable {F : Type*} [Field F]
noncomputable def challengeFrobeniusRingHom6401
    (sigma : F →+* F) (q : Nat) : F[X] →+* F[X] :=
  (Polynomial.compRingHom (Polynomial.X ^ q)).comp
    (Polynomial.mapRingHom sigma)
theorem challengeFrobeniusRingHom_apply6401
    (sigma : F →+* F) (q : Nat) (P : F[X]) :
    challengeFrobeniusRingHom6401 sigma q P =
      challengeFrobenius sigma q P := by
  rfl
noncomputable def graphTwist6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  P.map (challengeFrobeniusRingHom6401 sigma q)
noncomputable def graphTwistTwo6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  graphTwist6401 sigma q (graphTwist6401 sigma q P)
noncomputable def graphTwistThree6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  graphTwist6401 sigma q (graphTwistTwo6401 sigma q P)
noncomputable def graphTwistFour6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  graphTwist6401 sigma q (graphTwistThree6401 sigma q P)
noncomputable def graphTwistFive6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  graphTwist6401 sigma q (graphTwistFour6401 sigma q P)
theorem graphTwist_specialize6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphTwist6401 sigma q P).map (Polynomial.evalRingHom z) =
      (P.map (Polynomial.evalRingHom z)).map sigma := by
  ext n
  simp only [graphTwist6401, Polynomial.coeff_map]
  rw [challengeFrobeniusRingHom_apply6401]
  change Polynomial.eval z (challengeFrobenius sigma q (P.coeff n)) =
    sigma (Polynomial.eval z (P.coeff n))
  exact challengeFrobenius_eval sigma q (P.coeff n) z hz
theorem graphTwistTwo_specialize6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphTwistTwo6401 sigma q P).map (Polynomial.evalRingHom z) =
      ((P.map (Polynomial.evalRingHom z)).map sigma).map sigma := by
  rw [graphTwistTwo6401, graphTwist_specialize6401 sigma q _ z hz,
    graphTwist_specialize6401 sigma q P z hz]
theorem graphTwistThree_specialize6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphTwistThree6401 sigma q P).map (Polynomial.evalRingHom z) =
      (((P.map (Polynomial.evalRingHom z)).map sigma).map sigma).map sigma := by
  rw [graphTwistThree6401, graphTwist_specialize6401 sigma q _ z hz,
    graphTwistTwo_specialize6401 sigma q P z hz]
theorem graphTwistFour_specialize6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphTwistFour6401 sigma q P).map (Polynomial.evalRingHom z) =
      ((((P.map (Polynomial.evalRingHom z)).map sigma).map sigma).map sigma).map
        sigma := by
  rw [graphTwistFour6401, graphTwist_specialize6401 sigma q _ z hz,
    graphTwistThree_specialize6401 sigma q P z hz]
theorem graphTwistFive_specialize6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphTwistFive6401 sigma q P).map (Polynomial.evalRingHom z) =
      (((((P.map (Polynomial.evalRingHom z)).map sigma).map sigma).map sigma).map
        sigma).map sigma := by
  rw [graphTwistFive6401, graphTwist_specialize6401 sigma q _ z hz,
    graphTwistFour_specialize6401 sigma q P z hz]
theorem graphTwist_coeffDegreeLE6401
    (sigma : F →+* F) (q D : Nat) (P : F[X][X])
    (hP : BivariateCoeffDegreeLE P D) :
    BivariateCoeffDegreeLE (graphTwist6401 sigma q P) (D * q) := by
  intro n
  rw [graphTwist6401, Polynomial.coeff_map,
    challengeFrobeniusRingHom_apply6401,
    challengeFrobenius_natDegree]
  exact Nat.mul_le_mul_right q (hP n)
theorem graphTwist_iterate_coeffDegreeLE6401
    (sigma : F →+* F) (q D : Nat) (P : F[X][X])
    (hP : BivariateCoeffDegreeLE P D) :
    BivariateCoeffDegreeLE (graphTwist6401 sigma q P) (D * q) ∧
      BivariateCoeffDegreeLE (graphTwistTwo6401 sigma q P) (D * q ^ 2) ∧
      BivariateCoeffDegreeLE (graphTwistThree6401 sigma q P) (D * q ^ 3) ∧
      BivariateCoeffDegreeLE (graphTwistFour6401 sigma q P) (D * q ^ 4) ∧
      BivariateCoeffDegreeLE (graphTwistFive6401 sigma q P) (D * q ^ 5) := by
  have h1 := graphTwist_coeffDegreeLE6401 sigma q D P hP
  have h2 := graphTwist_coeffDegreeLE6401 sigma q (D * q)
    (graphTwist6401 sigma q P) h1
  have h3 := graphTwist_coeffDegreeLE6401 sigma q (D * q ^ 2)
    (graphTwistTwo6401 sigma q P) (by simpa [graphTwistTwo6401, pow_two,
      mul_assoc] using h2)
  have h4 := graphTwist_coeffDegreeLE6401 sigma q (D * q ^ 3)
    (graphTwistThree6401 sigma q P) (by
      simpa [graphTwistThree6401, pow_succ, mul_assoc] using h3)
  have h5 := graphTwist_coeffDegreeLE6401 sigma q (D * q ^ 4)
    (graphTwistFour6401 sigma q P) (by
      simpa [graphTwistFour6401, pow_succ, mul_assoc] using h4)
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · simpa [graphTwistTwo6401, pow_two, mul_assoc] using h2
  · simpa [graphTwistThree6401, pow_succ, mul_assoc] using h3
  · simpa [graphTwistFour6401, pow_succ, mul_assoc] using h4
  · simpa [graphTwistFive6401, pow_succ, mul_assoc] using h5
theorem graphTwistSix_X6401
    (sigma : F →+* F) (q : Nat) :
    graphTwist6401 sigma q (graphTwistFive6401 sigma q
      (Polynomial.C (Polynomial.X : F[X]))) =
      Polynomial.C (Polynomial.X ^ (q ^ 6)) := by
  simp [graphTwistFive6401, graphTwistFour6401, graphTwistThree6401,
    graphTwistTwo6401, graphTwist6401, challengeFrobeniusRingHom6401,
    pow_succ, mul_assoc]
  simp only [← pow_mul]
  congr 1
  ac_rfl
theorem graphTwistSix_X_ne_self6401
    (sigma : F →+* F) (q : Nat) (hq : q ^ 6 ≠ 1) :
    graphTwist6401 sigma q (graphTwistFive6401 sigma q
      (Polynomial.C (Polynomial.X : F[X]))) ≠
      Polynomial.C (Polynomial.X : F[X]) := by
  rw [graphTwistSix_X6401]
  intro h
  have hc := congrArg (fun P : F[X][X] ↦ P.coeff 0) h
  simp only [Polynomial.coeff_C_zero] at hc
  apply hq
  have hd := congrArg Polynomial.natDegree hc
  simpa using hd
end GraphTwist
section GraphGauge
variable {F : Type*} [Field F] [DecidableEq F]
noncomputable def graphHilbert90Denominator6401
    (sigma : F →+* F) (q : Nat) (B : F[X][X]) : F[X][X] :=
  B * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
    graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B
noncomputable def graphHilbert90Numerator6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) (t : F) : F[X][X] :=
  graphHilbert90Denominator6401 sigma q B *
      Polynomial.C (Polynomial.C t) +
    (A * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B) *
        Polynomial.C (Polynomial.C (sigma t)) +
    (A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B) *
        Polynomial.C (Polynomial.C (sigma (sigma t))) +
    (A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B) *
        Polynomial.C (Polynomial.C (sigma (sigma (sigma t)))) +
    (A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q A * graphTwistFour6401 sigma q B) *
        Polynomial.C (Polynomial.C (sigma (sigma (sigma (sigma t))))) +
    (A * graphTwist6401 sigma q A * graphTwistTwo6401 sigma q A *
      graphTwistThree6401 sigma q A * graphTwistFour6401 sigma q A) *
        Polynomial.C
          (Polynomial.C (sigma (sigma (sigma (sigma (sigma t))))))
theorem graphHilbert90Denominator_specialize6401
    (sigma : F →+* F) (q : Nat) (B : F[X][X]) (z : F)
    (hz : sigma z = z ^ q) :
    (graphHilbert90Denominator6401 sigma q B).map
        (Polynomial.evalRingHom z) =
      hilbert90Denominator6401 sigma
        (B.map (Polynomial.evalRingHom z)) := by
  simp only [graphHilbert90Denominator6401, Polynomial.map_mul]
  rw [graphTwist_specialize6401 sigma q B z hz,
    graphTwistTwo_specialize6401 sigma q B z hz,
    graphTwistThree_specialize6401 sigma q B z hz,
    graphTwistFour_specialize6401 sigma q B z hz]
  rfl
theorem graphHilbert90Numerator_specialize6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) (t z : F)
    (hz : sigma z = z ^ q) :
    (graphHilbert90Numerator6401 sigma q A B t).map
        (Polynomial.evalRingHom z) =
      hilbert90Numerator6401 sigma
        (A.map (Polynomial.evalRingHom z))
        (B.map (Polynomial.evalRingHom z)) t := by
  simp only [graphHilbert90Numerator6401, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C,
    graphHilbert90Denominator_specialize6401 sigma q B z hz]
  rw [graphTwist_specialize6401 sigma q A z hz,
    graphTwist_specialize6401 sigma q B z hz,
    graphTwistTwo_specialize6401 sigma q A z hz,
    graphTwistTwo_specialize6401 sigma q B z hz,
    graphTwistThree_specialize6401 sigma q A z hz,
    graphTwistThree_specialize6401 sigma q B z hz,
    graphTwistFour_specialize6401 sigma q A z hz,
    graphTwistFour_specialize6401 sigma q B z hz]
  simp [hilbert90Numerator6401, frobeniusOne6401, frobeniusTwo6401,
    frobeniusThree6401, frobeniusFour6401]
def graphHilbert90OuterCap6401 (q D : Nat) : Nat :=
  D + D * q + D * q ^ 2 + D * q ^ 3 + D * q ^ 4
private theorem fiveGraphFactors_coeffDegreeLE6401
    (P0 P1 P2 P3 P4 : F[X][X]) (D0 D1 D2 D3 D4 : Nat)
    (h0 : BivariateCoeffDegreeLE P0 D0)
    (h1 : BivariateCoeffDegreeLE P1 D1)
    (h2 : BivariateCoeffDegreeLE P2 D2)
    (h3 : BivariateCoeffDegreeLE P3 D3)
    (h4 : BivariateCoeffDegreeLE P4 D4) :
    BivariateCoeffDegreeLE (P0 * P1 * P2 * P3 * P4)
      (D0 + D1 + D2 + D3 + D4) := by
  exact BivariateCoeffDegreeLE_mul
    (BivariateCoeffDegreeLE_mul
      (BivariateCoeffDegreeLE_mul
        (BivariateCoeffDegreeLE_mul h0 h1) h2) h3) h4
private theorem scalarC_coeffDegreeLE_zero6401 (t : F) :
    BivariateCoeffDegreeLE
      (Polynomial.C (Polynomial.C t) : F[X][X]) 0 := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs <;> simp
private theorem graphGaugeFiveFactor_cap6401
    (sigma : F →+* F) (q D : Nat)
    (P0 P1 P2 P3 P4 : F[X][X])
    (h0 : BivariateCoeffDegreeLE P0 D)
    (h1 : BivariateCoeffDegreeLE P1 (D * q))
    (h2 : BivariateCoeffDegreeLE P2 (D * q ^ 2))
    (h3 : BivariateCoeffDegreeLE P3 (D * q ^ 3))
    (h4 : BivariateCoeffDegreeLE P4 (D * q ^ 4)) :
    BivariateCoeffDegreeLE (P0 * P1 * P2 * P3 * P4)
      (graphHilbert90OuterCap6401 q D) := by
  simpa [graphHilbert90OuterCap6401] using
    fiveGraphFactors_coeffDegreeLE6401 P0 P1 P2 P3 P4
      D (D * q) (D * q ^ 2) (D * q ^ 3) (D * q ^ 4)
      h0 h1 h2 h3 h4
theorem graphHilbert90Denominator_coeffDegreeLE6401
    (sigma : F →+* F) (q D : Nat) (B : F[X][X])
    (hB : BivariateCoeffDegreeLE B D) :
    BivariateCoeffDegreeLE (graphHilbert90Denominator6401 sigma q B)
      (graphHilbert90OuterCap6401 q D) := by
  have hBi := graphTwist_iterate_coeffDegreeLE6401 sigma q D B hB
  exact graphGaugeFiveFactor_cap6401 sigma q D B
    (graphTwist6401 sigma q B) (graphTwistTwo6401 sigma q B)
    (graphTwistThree6401 sigma q B) (graphTwistFour6401 sigma q B)
    hB hBi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2.1
theorem graphHilbert90Numerator_coeffDegreeLE6401
    (sigma : F →+* F) (q D : Nat) (A B : F[X][X]) (t : F)
    (hA : BivariateCoeffDegreeLE A D)
    (hB : BivariateCoeffDegreeLE B D) :
    BivariateCoeffDegreeLE (graphHilbert90Numerator6401 sigma q A B t)
      (graphHilbert90OuterCap6401 q D) := by
  have hAi := graphTwist_iterate_coeffDegreeLE6401 sigma q D A hA
  have hBi := graphTwist_iterate_coeffDegreeLE6401 sigma q D B hB
  let C := graphHilbert90OuterCap6401 q D
  have term (P0 P1 P2 P3 P4 : F[X][X]) (s : F)
      (h0 : BivariateCoeffDegreeLE P0 D)
      (h1 : BivariateCoeffDegreeLE P1 (D * q))
      (h2 : BivariateCoeffDegreeLE P2 (D * q ^ 2))
      (h3 : BivariateCoeffDegreeLE P3 (D * q ^ 3))
      (h4 : BivariateCoeffDegreeLE P4 (D * q ^ 4)) :
      BivariateCoeffDegreeLE
        ((P0 * P1 * P2 * P3 * P4) * Polynomial.C (Polynomial.C s)) C := by
    simpa [C] using BivariateCoeffDegreeLE_mul
      (graphGaugeFiveFactor_cap6401 sigma q D P0 P1 P2 P3 P4
        h0 h1 h2 h3 h4)
      (scalarC_coeffDegreeLE_zero6401 s)
  have h0 : BivariateCoeffDegreeLE
      (graphHilbert90Denominator6401 sigma q B *
        Polynomial.C (Polynomial.C t)) C := by
    simpa [C] using BivariateCoeffDegreeLE_mul
      (graphHilbert90Denominator_coeffDegreeLE6401 sigma q D B hB)
      (scalarC_coeffDegreeLE_zero6401 t)
  have h1 := term A (graphTwist6401 sigma q B)
    (graphTwistTwo6401 sigma q B) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma t)
    hA hBi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h2 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q B) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma (sigma t))
    hA hAi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h3 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma (sigma (sigma t)))
    hA hAi.1 hAi.2.1 hBi.2.2.1 hBi.2.2.2.1
  have h4 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q A)
    (graphTwistFour6401 sigma q B) (sigma (sigma (sigma (sigma t))))
    hA hAi.1 hAi.2.1 hAi.2.2.1 hBi.2.2.2.1
  have h5 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q A)
    (graphTwistFour6401 sigma q A)
    (sigma (sigma (sigma (sigma (sigma t)))))
    hA hAi.1 hAi.2.1 hAi.2.2.1 hAi.2.2.2.1
  unfold graphHilbert90Numerator6401
  simpa [C] using BivariateCoeffDegreeLE_add
    (BivariateCoeffDegreeLE_add
      (BivariateCoeffDegreeLE_add
        (BivariateCoeffDegreeLE_add
          (BivariateCoeffDegreeLE_add h0 h1) h2) h3) h4) h5
theorem graphTwist_iterate_natDegree_le6401
    (sigma : F →+* F) (q p : Nat) (P : F[X][X])
    (hP : P.natDegree ≤ p) :
    (graphTwist6401 sigma q P).natDegree ≤ p ∧
      (graphTwistTwo6401 sigma q P).natDegree ≤ p ∧
      (graphTwistThree6401 sigma q P).natDegree ≤ p ∧
      (graphTwistFour6401 sigma q P).natDegree ≤ p := by
  have h1 : (graphTwist6401 sigma q P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans hP
  have h2 : (graphTwistTwo6401 sigma q P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h1
  have h3 : (graphTwistThree6401 sigma q P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h2
  have h4 : (graphTwistFour6401 sigma q P).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans h3
  exact ⟨h1, h2, h3, h4⟩
private theorem fiveGraphFactors_natDegree_le6401
    (P0 P1 P2 P3 P4 : F[X][X]) (p : Nat)
    (h0 : P0.natDegree ≤ p) (h1 : P1.natDegree ≤ p)
    (h2 : P2.natDegree ≤ p) (h3 : P3.natDegree ≤ p)
    (h4 : P4.natDegree ≤ p) :
    (P0 * P1 * P2 * P3 * P4).natDegree ≤ 5 * p := by
  have h01 := Polynomial.natDegree_mul_le (p := P0) (q := P1)
  have h012 := Polynomial.natDegree_mul_le (p := P0 * P1) (q := P2)
  have h0123 := Polynomial.natDegree_mul_le
    (p := P0 * P1 * P2) (q := P3)
  have h01234 := Polynomial.natDegree_mul_le
    (p := P0 * P1 * P2 * P3) (q := P4)
  omega
theorem graphHilbert90Denominator_natDegree_le6401
    (sigma : F →+* F) (q p : Nat) (B : F[X][X])
    (hB : B.natDegree ≤ p) :
    (graphHilbert90Denominator6401 sigma q B).natDegree ≤ 5 * p := by
  have hBi := graphTwist_iterate_natDegree_le6401 sigma q p B hB
  exact fiveGraphFactors_natDegree_le6401 B
    (graphTwist6401 sigma q B) (graphTwistTwo6401 sigma q B)
    (graphTwistThree6401 sigma q B) (graphTwistFour6401 sigma q B)
    p hB hBi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2
theorem graphHilbert90Numerator_natDegree_le6401
    (sigma : F →+* F) (q p : Nat) (A B : F[X][X]) (t : F)
    (hA : A.natDegree ≤ p) (hB : B.natDegree ≤ p) :
    (graphHilbert90Numerator6401 sigma q A B t).natDegree ≤ 5 * p := by
  have hAi := graphTwist_iterate_natDegree_le6401 sigma q p A hA
  have hBi := graphTwist_iterate_natDegree_le6401 sigma q p B hB
  have term (P0 P1 P2 P3 P4 : F[X][X]) (s : F)
      (h0 : P0.natDegree ≤ p) (h1 : P1.natDegree ≤ p)
      (h2 : P2.natDegree ≤ p) (h3 : P3.natDegree ≤ p)
      (h4 : P4.natDegree ≤ p) :
      ((P0 * P1 * P2 * P3 * P4) *
        Polynomial.C (Polynomial.C s)).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (Polynomial.C (Polynomial.C s) : F[X][X]).natDegree = 0 :=
        by simp
      have hp := fiveGraphFactors_natDegree_le6401
        P0 P1 P2 P3 P4 p h0 h1 h2 h3 h4
      omega)
  have h0 : (graphHilbert90Denominator6401 sigma q B *
      Polynomial.C (Polynomial.C t)).natDegree ≤ 5 * p := by
    exact Polynomial.natDegree_mul_le.trans (by
      have hd := graphHilbert90Denominator_natDegree_le6401
        sigma q p B hB
      have hc : (Polynomial.C (Polynomial.C t) : F[X][X]).natDegree = 0 :=
        by simp
      omega)
  have h1 := term A (graphTwist6401 sigma q B)
    (graphTwistTwo6401 sigma q B) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma t)
    hA hBi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2
  have h2 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q B) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma (sigma t))
    hA hAi.1 hBi.2.1 hBi.2.2.1 hBi.2.2.2
  have h3 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q B)
    (graphTwistFour6401 sigma q B) (sigma (sigma (sigma t)))
    hA hAi.1 hAi.2.1 hBi.2.2.1 hBi.2.2.2
  have h4 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q A)
    (graphTwistFour6401 sigma q B) (sigma (sigma (sigma (sigma t))))
    hA hAi.1 hAi.2.1 hAi.2.2.1 hBi.2.2.2
  have h5 := term A (graphTwist6401 sigma q A)
    (graphTwistTwo6401 sigma q A) (graphTwistThree6401 sigma q A)
    (graphTwistFour6401 sigma q A)
    (sigma (sigma (sigma (sigma (sigma t)))))
    hA hAi.1 hAi.2.1 hAi.2.2.1 hAi.2.2.2
  unfold graphHilbert90Numerator6401
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans (max_le
          ((Polynomial.natDegree_add_le _ _).trans (max_le h0 h1)) h2)) h3))
        h4)) h5)
theorem graphHilbert90Numerator_ne_zero_of_anchor6401
    (sigma : F →+* F) (q : Nat) (A B : F[X][X])
    (z : F) (hz : sigma z = z ^ q)
    (x E : F) (hx : sigma x = x)
    (hcoprime : IsCoprime
      (A.map (Polynomial.evalRingHom z))
      (B.map (Polynomial.evalRingHom z)))
    (hE : E ≠ 0) (hsix : (6 : F) ≠ 0)
    (hrel : Polynomial.eval x (A.map (Polynomial.evalRingHom z)) * sigma E =
      Polynomial.eval x (B.map (Polynomial.evalRingHom z)) * E) :
    graphHilbert90Numerator6401 sigma q A B E ≠ 0 := by
  have hseed := hilbert90Numerator_errorSeed_ne_zero6401 sigma
    (A.map (Polynomial.evalRingHom z))
    (B.map (Polynomial.evalRingHom z)) hcoprime x E hx hE hsix hrel
  intro hzero
  apply hseed
  rw [← graphHilbert90Numerator_specialize6401 sigma q A B E z hz,
    hzero, Polynomial.map_zero]
theorem graphHilbert90_badOwner_card_le6401
    (sigma : F →+* F) (q D : Nat) (A B : F[X][X]) (t : F)
    (hA : BivariateCoeffDegreeLE A D)
    (hB : BivariateCoeffDegreeLE B D)
    (hP : graphHilbert90Numerator6401 sigma q A B t ≠ 0)
    (S : Finset F) :
    (S.filter fun z ↦
      (graphHilbert90Numerator6401 sigma q A B t).map
        (Polynomial.evalRingHom z) = 0).card ≤
      graphHilbert90OuterCap6401 q D := by
  have hroot := BCHKSQuadraticKernel6400.specialization_zero_card_le_degreeX
    (graphHilbert90Numerator6401 sigma q A B t) S hP
  apply hroot.trans
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro n hn
  exact graphHilbert90Numerator_coeffDegreeLE6401 sigma q D A B t hA hB n
theorem graphHilbert90_goodOwner_normalization6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : I → F) (A B : F[X][X]) (t : F) (q p : Nat)
    (z : F) (hz : sigma z = z ^ q)
    (hAdegree : A.natDegree ≤ p) (hBdegree : B.natDegree ≤ p)
    (hcoprime : IsCoprime
      (A.map (Polynomial.evalRingHom z))
      (B.map (Polynomial.evalRingHom z)))
    (hnorm : polynomialFrobeniusNormSix sigma
        (A.map (Polynomial.evalRingHom z)) =
      polynomialFrobeniusNormSix sigma
        (B.map (Polynomial.evalRingHom z)))
    (hP : (graphHilbert90Numerator6401 sigma q A B t).map
      (Polynomial.evalRingHom z) ≠ 0)
    (hrelation : TwoLaneFailureRelation sigma alpha E
      (A.map (Polynomial.evalRingHom z))
      (B.map (Polynomial.evalRingHom z))) :
    let Pz := hilbert90Numerator6401 sigma
      (A.map (Polynomial.evalRingHom z))
      (B.map (Polynomial.evalRingHom z)) t
    let Qz := hilbert90Denominator6401 sigma
      (B.map (Polynomial.evalRingHom z))
    let bad := hilbert90BadSet6401 alpha Pz
    Pz = (graphHilbert90Numerator6401 sigma q A B t).map
        (Polynomial.evalRingHom z) ∧
      Qz = (graphHilbert90Denominator6401 sigma q B).map
        (Polynomial.evalRingHom z) ∧
      Pz.natDegree ≤ 5 * p ∧ Qz.natDegree ≤ 5 * p ∧
      bad.card ≤ 5 * p ∧
      ∀ i, i ∉ bad →
        sigma (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Qz) (Polynomial.eval (alpha i) Pz)) =
            hilbert90NormalizeValue6401 (E i)
              (Polynomial.eval (alpha i) Qz)
              (Polynomial.eval (alpha i) Pz) ∧
        (hilbert90NormalizeValue6401 (E i)
          (Polynomial.eval (alpha i) Qz) (Polynomial.eval (alpha i) Pz) = 0 ↔
            E i = 0) := by
  dsimp only
  have hPz : hilbert90Numerator6401 sigma
      (A.map (Polynomial.evalRingHom z))
      (B.map (Polynomial.evalRingHom z)) t ≠ 0 := by
    rw [← graphHilbert90Numerator_specialize6401 sigma q A B t z hz]
    exact hP
  have hAz : (A.map (Polynomial.evalRingHom z)).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans hAdegree
  have hBz : (B.map (Polynomial.evalRingHom z)).natDegree ≤ p :=
    Polynomial.natDegree_map_le.trans hBdegree
  have howner := hilbert90_owner_normalization6401 sigma horder
    alpha hfixed E
    (A.map (Polynomial.evalRingHom z))
    (B.map (Polynomial.evalRingHom z)) hcoprime t p hAz hBz hnorm hPz
      hrelation
  refine ⟨(graphHilbert90Numerator_specialize6401
      sigma q A B t z hz).symm,
    (graphHilbert90Denominator_specialize6401 sigma q B z hz).symm,
    howner.1, howner.2.1, howner.2.2.1, howner.2.2.2⟩
end GraphGauge
def graphHilbert90OuterWeight6401 (q : Nat) : Nat :=
  1 + q + q ^ 2 + q ^ 3 + q ^ 4
theorem graphHilbert90_degree_obstruction_ledger6401 :
    graphHilbert90OuterWeight6401
        BCHKSTwoFrobeniusModuleAudit6401.q6401 =
      20610781942729029644174256251680587781 ∧
    BCHKSTwoFrobeniusModuleAudit6401.q6401 ^ 2 =
      4539909903627583489 ∧
    80251881527475554 <
      BCHKSTwoFrobeniusModuleAudit6401.q6401 ^ 2 ∧
    80251881527475554 <
      graphHilbert90OuterWeight6401
        BCHKSTwoFrobeniusModuleAudit6401.q6401 := by
  native_decide
theorem benchmark_graphTwistSix_not_identity6401 :
    graphTwist6401 (RingHom.id ℚ)
      BCHKSTwoFrobeniusModuleAudit6401.q6401
      (graphTwistFive6401 (RingHom.id ℚ)
        BCHKSTwoFrobeniusModuleAudit6401.q6401
        (Polynomial.C (Polynomial.X : ℚ[X]))) ≠
      Polynomial.C (Polynomial.X : ℚ[X]) := by
  apply graphTwistSix_X_ne_self6401
  native_decide
end BCHKSFrobeniusGraphHilbert90Audit6401
end ProximityPrize.SubmissionLower
