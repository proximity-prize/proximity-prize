import ProximityPrize.SubmissionLower.BCHKSFrobeniusConstantPairClosure6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusRectangularHankelAudit6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusConstantPairEndpoint6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusRectangularHankelAudit6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSFrobeniusConstantPairClosure6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
theorem syndromeWeight_mul_supportCoweight
    {F : Type*} [Field F] {e : Nat}
    (alpha : Fin e ↪ F) (i : Fin e) :
    syndromeWeight alpha i * supportCoweight alpha i = 1 := by
  have hco := supportCoweight_ne_zero alpha alpha.injective i
  unfold syndromeWeight Lagrange.nodalWeight supportCoweight
  rw [Finset.prod_inv_distrib]
  exact inv_mul_cancel₀ hco
theorem exists_ownerPolynomial_of_weightedSyndromes_zero6401
    {F : Type*} [Field F]
    (alpha : Fin n6401 ↪ F) (y : Fin n6401 → F)
    (hzero : ∀ j : Fin keyRedundancy6401,
      weightedSyndrome alpha y j.1 = 0) :
    ∃ Q : Polynomial F,
      Q.natDegree ≤ ownerDegreeCap6401 ∧
      ∀ i, Polynomial.eval (alpha i) Q = y i := by
  classical
  let x : Fin n6401 → F := fun i => syndromeWeight alpha i * y i
  let Q := supportDualPolynomial alpha x
  have hrows : keyRedundancy6401 < n6401 := by native_decide
  have hmoments : ∀ j : Fin keyRedundancy6401,
      ∑ i, x i * alpha i ^ j.1 = 0 := by
    intro j
    simpa [x, weightedSyndrome, mul_assoc, mul_left_comm, mul_comm] using
      hzero j
  have hQlt : Q.natDegree < n6401 - keyRedundancy6401 :=
    supportDualPolynomial_natDegree_lt alpha x alpha.injective hrows hmoments
  have hQdeg : Q.natDegree ≤ ownerDegreeCap6401 := by
    have hnum : n6401 - keyRedundancy6401 = ownerDegreeCap6401 + 1 := by
      native_decide
    rw [hnum] at hQlt
    omega
  refine ⟨Q, hQdeg, ?_⟩
  intro i
  have heval := supportDualPolynomial_eval alpha x alpha.injective i
  change Q.eval (alpha i) = y i
  rw [show Q.eval (alpha i) = x i * supportCoweight alpha i by
    simpa [Q] using heval]
  dsimp [x]
  calc
    syndromeWeight alpha i * y i * supportCoweight alpha i =
        (syndromeWeight alpha i * supportCoweight alpha i) * y i := by ring
    _ = 1 * y i := by rw [syndromeWeight_mul_supportCoweight alpha i]
    _ = y i := one_mul _
theorem sigma_syndromeWeight
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) (i : iota) :
    sigma (syndromeWeight alpha i) = syndromeWeight alpha i := by
  classical
  simp [syndromeWeight, Lagrange.nodalWeight, hfixed]
theorem sigma_weightedSyndrome
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (sigma : F →+* F) (alpha : iota ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (y : iota → F) (j : Nat) :
    sigma (weightedSyndrome alpha y j) =
      weightedSyndrome alpha (fun i => sigma (y i)) j := by
  classical
  simp only [weightedSyndrome, map_sum, map_mul, map_pow,
    sigma_syndromeWeight sigma alpha hfixed]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfixed i]
theorem weightedSyndrome_add
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (alpha : iota ↪ F) (u v : iota → F) (j : Nat) :
    weightedSyndrome alpha (fun i => u i + v i) j =
      weightedSyndrome alpha u j + weightedSyndrome alpha v j := by
  classical
  simp [weightedSyndrome, mul_add, Finset.sum_add_distrib]
theorem weightedSyndrome_const_mul
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (alpha : iota ↪ F) (c : F) (u : iota → F) (j : Nat) :
    weightedSyndrome alpha (fun i => c * u i) j =
      c * weightedSyndrome alpha u j := by
  classical
  simp only [weightedSyndrome, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem weightedSyndrome_affine
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (alpha : iota ↪ F) (u0 u1 : iota → F) (z : F) (j : Nat) :
    weightedSyndrome alpha (fun i => u0 i + z * u1 i) j =
      weightedSyndrome alpha u0 j + z * weightedSyndrome alpha u1 j := by
  rw [weightedSyndrome_add,
    weightedSyndrome_const_mul]
theorem weightedSyndrome_sub_const_mul
    {F iota : Type*} [Field F] [Fintype iota] [DecidableEq iota]
    (alpha : iota ↪ F) (u1 u0 : iota → F) (c : F) (j : Nat) :
    weightedSyndrome alpha (fun i => u1 i - c * u0 i) j =
      weightedSyndrome alpha u1 j - c * weightedSyndrome alpha u0 j := by
  rw [show (fun i => u1 i - c * u0 i) =
      (fun i => u1 i + (-c) * u0 i) by
    funext i
    ring]
  rw [weightedSyndrome_add, weightedSyndrome_const_mul]
  ring
theorem receivedSyndrome_eigen_of_error_eigen6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u0 u1 : Fin n6401 → F) (P : F → Polynomial F)
    (z c : F) (hPdegree : (P z).natDegree ≤ ownerDegreeCap6401)
    (hc : c ≠ 0)
    (heigen : ∀ i,
      sigma (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)) =
        c * (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))) :
    ∀ j : Fin keyRedundancy6401,
      sigma (weightedSyndrome alpha u0 j.1 +
          z * weightedSyndrome alpha u1 j.1) =
        c * (weightedSyndrome alpha u0 j.1 +
          z * weightedSyndrome alpha u1 j.1) := by
  intro j
  let E : Fin n6401 → F := fun i =>
    u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)
  have hdeg : (P z).natDegree + j.1 <
      Fintype.card (Fin n6401) - 1 := by
    have hj : j.1 < keyRedundancy6401 := j.2
    have hp := hPdegree
    norm_num [n6401, keyRedundancy6401, keyRedundancy6401,
      keyErrors6401, ownerDegreeCap6401, bchksErrors6401] at hp hj ⊢
    omega
  have hrecv :
      weightedSyndrome alpha (fun i => u0 i + z * u1 i) j.1 =
        weightedSyndrome alpha E j.1 := by
    apply weightedSyndrome_received_eq_error alpha (P z) E
      (fun i => u0 i + z * u1 i) j.1
    · intro i
      dsimp [E]
      ring
    · exact hdeg
  calc
    sigma (weightedSyndrome alpha u0 j.1 +
        z * weightedSyndrome alpha u1 j.1) =
        sigma (weightedSyndrome alpha E j.1) := by
      rw [← hrecv, weightedSyndrome_affine]
    _ = weightedSyndrome alpha (fun i => sigma (E i)) j.1 :=
      sigma_weightedSyndrome sigma alpha hfixed E j.1
    _ = weightedSyndrome alpha (fun i => c * E i) j.1 := by
      apply congrArg (fun y => weightedSyndrome alpha y j.1)
      funext i
      exact heigen i
    _ = c * weightedSyndrome alpha E j.1 :=
      weightedSyndrome_const_mul alpha c E j.1
    _ = c * (weightedSyndrome alpha u0 j.1 +
        z * weightedSyndrome alpha u1 j.1) := by
      rw [← hrecv, weightedSyndrome_affine]
theorem globalError_eigen_of_constant_failurePair
    {F iota : Type*} [Field F]
    (sigma : F →+* F) (alpha : iota → F) (E : iota → F)
    (W0 W1 : Polynomial F)
    (hW0 : W0 ≠ 0) (hW0deg : W0.natDegree ≤ 0)
    (hW1deg : W1.natDegree ≤ 0)
    (hrel : TwoLaneFailureRelation sigma alpha E W0 W1) :
    ∃ c : F, c ≠ 0 ∧ ∀ i, sigma (E i) = c * E i := by
  classical
  rcases Classical.em (∀ i, E i = 0) with hEzero | hEzero
  · refine ⟨1, one_ne_zero, ?_⟩
    intro i
    simp [hEzero i]
  · obtain ⟨i0, hi0⟩ := Classical.not_forall.mp hEzero
    let a := W0.coeff 0
    let b := W1.coeff 0
    have hW0C : W0 = Polynomial.C a := by
      exact Polynomial.eq_C_of_natDegree_le_zero hW0deg
    have hW1C : W1 = Polynomial.C b := by
      exact Polynomial.eq_C_of_natDegree_le_zero hW1deg
    have ha : a ≠ 0 := by
      intro haz
      apply hW0
      rw [hW0C, haz, Polynomial.C_0]
    have hb : b ≠ 0 := by
      intro hbz
      have hi := hrel i0
      rw [hW0C, hW1C] at hi
      simp only [Polynomial.eval_C] at hi
      rw [hbz, zero_mul] at hi
      have hsE : sigma (E i0) ≠ 0 := by
        intro hzero
        apply hi0
        apply sigma.injective
        simpa using hzero
      exact (mul_ne_zero ha hsE) hi
    refine ⟨b / a, div_ne_zero hb ha, ?_⟩
    intro i
    have hi := hrel i
    rw [hW0C, hW1C] at hi
    simp only [Polynomial.eval_C] at hi
    field_simp
    linear_combination hi
theorem constantFailurePair_ownerCurve6401
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (heigenError : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧ ∀ i,
      sigma (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)) =
        c * (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))) :
    PolynomialAffineCurveWitness6401 S P := by
  classical
  let a : Fin keyRedundancy6401 → F := fun j =>
    weightedSyndrome alpha u0 j.1
  let b : Fin keyRedundancy6401 → F := fun j =>
    weightedSyndrome alpha u1 j.1
  have heigenSyndrome : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧
      ∀ j, sigma (a j + z * b j) = c * (a j + z * b j) := by
    intro z hz
    obtain ⟨c, hc, heig⟩ := heigenError z hz
    refine ⟨c, hc, ?_⟩
    intro j
    exact receivedSyndrome_eigen_of_error_eigen6401
      sigma alpha hfixed u0 u1 P z c (hPdegree z hz) hc heig j
  have hcross : ∀ i j, a i * b j - a j * b i = 0 :=
    benchmark_projectiveFrobenius_forces_cross_zero6401
      sigma S a b hfixedCard hSlarge heigenSyndrome
  by_cases ha : ∀ j, a j = 0
  · obtain ⟨Q, hQdeg, hQeval⟩ :=
      exists_ownerPolynomial_of_weightedSyndromes_zero6401 alpha u0
        (by
          intro j
          exact ha j)
    exact zeroBasePrimitive_ownerCurve6401 alpha u0 u1 S A P Q
      hQdeg hQeval hSlarge hPdegree hrow howner
  · push_neg at ha
    obtain ⟨j0, hj0⟩ := ha
    let c : F := b j0 / a j0
    have hbca : ∀ j, b j = c * a j := by
      intro j
      have hdet := hcross j0 j
      dsimp [c]
      field_simp
      linear_combination hdet
    obtain ⟨V, hVdeg, hVeval⟩ :=
      exists_ownerPolynomial_of_weightedSyndromes_zero6401 alpha
        (fun i => u1 i - c * u0 i) (by
          intro j
          rw [weightedSyndrome_sub_const_mul]
          change b j - c * a j = 0
          rw [hbca j, sub_self])
    exact constantPrimitive_ownerCurve6401 alpha u0 u1 S A P c V
      hVdeg hVeval hSlarge hPdegree hrow howner
theorem constantFailurePair_ownerFamily_card_le_cap6401_of_no_curve
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (heigenError : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧ ∀ i,
      sigma (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)) =
        c * (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)))
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ constantPrimitiveFamilyCap6401 := by
  classical
  let a : Fin keyRedundancy6401 → F := fun j ↦
    weightedSyndrome alpha u0 j.1
  let b : Fin keyRedundancy6401 → F := fun j ↦
    weightedSyndrome alpha u1 j.1
  have heigenSyndrome : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧
      ∀ j, sigma (a j + z * b j) = c * (a j + z * b j) := by
    intro z hz
    obtain ⟨c, hc, heig⟩ := heigenError z hz
    refine ⟨c, hc, ?_⟩
    intro j
    exact receivedSyndrome_eigen_of_error_eigen6401
      sigma alpha hfixed u0 u1 P z c (hPdegree z hz) hc heig j
  by_cases hcross : ∀ i j, a i * b j - a j * b i = 0
  · by_cases ha : ∀ j, a j = 0
    · obtain ⟨Q, hQdeg, hQeval⟩ :=
        exists_ownerPolynomial_of_weightedSyndromes_zero6401 alpha u0
          (by
            intro j
            exact ha j)
      exact ownerFamily_card_le_zeroBaseFamilyCap6401_of_no_curve
        alpha u0 u1 S A P Q hQdeg hQeval hPdegree hrow howner hfail
    · push_neg at ha
      obtain ⟨j0, hj0⟩ := ha
      let c : F := b j0 / a j0
      have hbca : ∀ j, b j = c * a j := by
        intro j
        have hdet := hcross j0 j
        dsimp [c]
        field_simp
        linear_combination hdet
      obtain ⟨V, hVdeg, hVeval⟩ :=
        exists_ownerPolynomial_of_weightedSyndromes_zero6401 alpha
          (fun i ↦ u1 i - c * u0 i) (by
            intro j
            rw [weightedSyndrome_sub_const_mul]
            change b j - c * a j = 0
            rw [hbca j, sub_self])
      exact ownerFamily_card_le_constantPrimitiveFamilyCap6401_of_no_curve
        alpha u0 u1 S A P c V hVdeg hVeval hPdegree hrow howner hfail
  · push_neg at hcross
    obtain ⟨i, j, hij⟩ := hcross
    have hsmall := projectiveFrobenius_affineLine_card_le_fixed_add_one
      sigma S a b i j hij heigenSyndrome
    have hfixedBound :
        (frobeniusFixedScalars sigma).card + 1 ≤ q6401 + 1 :=
      Nat.add_le_add_right hfixedCard 1
    have hnum : q6401 + 1 ≤ constantPrimitiveFamilyCap6401 := by
      native_decide
    exact hsmall.trans (hfixedBound.trans hnum)
theorem constantPolynomialFailurePairs_ownerCurve6401
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hpairs : ∀ z ∈ S, ∃ W0 W1 : Polynomial F,
      W0 ≠ 0 ∧ W0.natDegree ≤ 0 ∧ W1.natDegree ≤ 0 ∧
      TwoLaneFailureRelation sigma alpha
        (fun i => u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
        W0 W1) :
    PolynomialAffineCurveWitness6401 S P := by
  apply constantFailurePair_ownerCurve6401 sigma alpha hfixed hfixedCard
    u0 u1 S A P hSlarge hPdegree hrow howner
  intro z hz
  obtain ⟨W0, W1, hW0, hW0deg, hW1deg, hrel⟩ := hpairs z hz
  exact globalError_eigen_of_constant_failurePair sigma alpha
    (fun i => u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
    W0 W1 hW0 hW0deg hW1deg hrel
theorem twoLaneFailureRelation_of_nonzero_errors
    {F iota : Type*} [Field F]
    (sigma : F →+* F) (alpha E : iota → F) (W0 W1 : Polynomial F)
    (hrel : ∀ i, E i ≠ 0 →
      W0.eval (alpha i) * sigma (E i) = W1.eval (alpha i) * E i) :
    TwoLaneFailureRelation sigma alpha E W0 W1 := by
  intro i
  rcases Classical.em (E i = 0) with hi | hi
  · simp [hi]
  · exact hrel i hi
theorem constantPolynomialFailurePairsOnSupport_ownerCurve6401
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hpairs : ∀ z ∈ S, ∃ W0 W1 : Polynomial F,
      W0 ≠ 0 ∧ W0.natDegree ≤ 0 ∧ W1.natDegree ≤ 0 ∧
      ∀ i,
        u0 i + z * u1 i - Polynomial.eval (alpha i) (P z) ≠ 0 →
        W0.eval (alpha i) *
            sigma (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)) =
          W1.eval (alpha i) *
            (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))) :
    PolynomialAffineCurveWitness6401 S P := by
  apply constantPolynomialFailurePairs_ownerCurve6401 sigma alpha hfixed
    hfixedCard u0 u1 S A P hSlarge hPdegree hrow howner
  intro z hz
  obtain ⟨W0, W1, hW0, hW0deg, hW1deg, hrel⟩ := hpairs z hz
  exact ⟨W0, W1, hW0, hW0deg, hW1deg,
    twoLaneFailureRelation_of_nonzero_errors sigma alpha
      (fun i => u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
      W0 W1 hrel⟩
theorem constantPolynomialFailurePairsOnSupport_ownerFamily_card_le_cap6401
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hpairs : ∀ z ∈ S, ∃ W0 W1 : Polynomial F,
      W0 ≠ 0 ∧ W0.natDegree ≤ 0 ∧ W1.natDegree ≤ 0 ∧
      ∀ i,
        u0 i + z * u1 i - Polynomial.eval (alpha i) (P z) ≠ 0 →
        W0.eval (alpha i) *
            sigma (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)) =
          W1.eval (alpha i) *
            (u0 i + z * u1 i - Polynomial.eval (alpha i) (P z)))
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    S.card ≤ constantPrimitiveFamilyCap6401 := by
  apply constantFailurePair_ownerFamily_card_le_cap6401_of_no_curve
    sigma alpha hfixed hfixedCard u0 u1 S A P hPdegree hrow howner
    (hfail := hfail)
  intro z hz
  obtain ⟨W0, W1, hW0, hW0deg, hW1deg, hrel⟩ := hpairs z hz
  have hglobal : TwoLaneFailureRelation sigma alpha
      (fun i ↦ u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
      W0 W1 :=
    twoLaneFailureRelation_of_nonzero_errors sigma alpha
      (fun i ↦ u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
      W0 W1 hrel
  exact globalError_eigen_of_constant_failurePair sigma alpha
    (fun i ↦ u0 i + z * u1 i - Polynomial.eval (alpha i) (P z))
    W0 W1 hW0 hW0deg hW1deg hglobal
end BCHKSFrobeniusConstantPairEndpoint6401
end ProximityPrize.SubmissionLower
