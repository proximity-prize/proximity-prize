import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphGaugeSupportFork6401
import ProximityPrize.SubmissionLower.BCHKSResultantDegree
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveLaneResultantFork6401
open Polynomial
open Polynomial.Bivariate
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeSupportFork6401
open BCHKSFrobeniusGraphInjectivity6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
def primitiveLaneResultantChallengeCap6401 : Nat :=
  22507 * primitiveLaneZeroChallengeCap6401 +
    22507 * primitiveLaneOneChallengeCap6401
theorem primitiveLaneResultantChallengeCap_exact6401 :
    primitiveLaneResultantChallengeCap6401 = 2158730775527680420 := by
  native_decide
noncomputable def primitiveLaneResultant6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    F[X] :=
  Polynomial.resultant
    (primitiveBivariateFailureLaneZero6401 W)
    (primitiveBivariateFailureLaneOne6401 W)
theorem primitiveBivariateFailureLanes_natDegree_le_22507_6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    (primitiveBivariateFailureLaneZero6401 W).natDegree ≤ 22507 ∧
      (primitiveBivariateFailureLaneOne6401 W).natDegree ≤ 22507 := by
  constructor
  · simpa [primitiveBivariateFailureLaneZero6401,
      primitiveThreeShiftXCap6401] using
        W.sourcePuncture.reduced_caps 2
  · simpa [primitiveBivariateFailureLaneOne6401,
      primitiveThreeShiftXCap6401] using
        W.sourcePuncture.reduced_caps 1
theorem primitiveLaneResultant_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    (primitiveLaneResultant6401 W).natDegree ≤
      primitiveLaneResultantChallengeCap6401 := by
  let L0 := primitiveBivariateFailureLaneZero6401 W
  let L1 := primitiveBivariateFailureLaneOne6401 W
  rcases primitiveBivariateFailureLanes_natDegree_le_22507_6401 W with
    ⟨hL0X, hL1X⟩
  rcases primitiveBivariateFailureLanes_coeffDegreeLE6401 W with
    ⟨hL0Z, hL1Z⟩
  have hdegreeZ0 : degreeX L0 ≤ primitiveLaneZeroChallengeCap6401 := by
    unfold degreeX
    apply Finset.sup_le
    intro n hn
    exact hL0Z n
  have hdegreeZ1 : degreeX L1 ≤ primitiveLaneOneChallengeCap6401 := by
    unfold degreeX
    apply Finset.sup_le
    intro n hn
    exact hL1Z n
  have hraw := bivariate_resultant_natDegree_le
    L0 L1 L0.natDegree L1.natDegree
  change (primitiveLaneResultant6401 W).natDegree ≤ _
  apply hraw.trans
  exact Nat.add_le_add
    (Nat.mul_le_mul hL1X hdegreeZ0)
    (Nat.mul_le_mul hL0X hdegreeZ1)
private theorem resultant_fixed_degree_eq_zero_of_not_isCoprime6401
    {F : Type} [Field F] (A B : F[X]) (m n : Nat)
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n)
    (hsize : 0 < m + n) (hnc : ¬ IsCoprime A B) :
    Polynomial.resultant A B m n = 0 := by
  by_cases hpair : A ≠ 0 ∨ B ≠ 0
  · have hstandard : Polynomial.resultant A B = 0 :=
      (Polynomial.resultant_eq_zero_iff.mpr ⟨hpair, hnc⟩)
    have hm : A.natDegree + (m - A.natDegree) = m :=
      Nat.add_sub_of_le hA
    have hn : B.natDegree + (n - B.natDegree) = n :=
      Nat.add_sub_of_le hB
    rw [← hm, ← hn]
    rw [Polynomial.resultant_add_left_deg]
    · rw [Polynomial.resultant_add_right_deg]
      · simp [hstandard]
      · exact le_rfl
    · exact le_rfl
  · push Not at hpair
    rcases hpair with ⟨rfl, rfl⟩
    rcases m with _ | m <;> rcases n with _ | n <;> simp_all
theorem eval_primitiveLaneResultant_eq_zero_of_not_isCoprime6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hpositive : 0 <
      (primitiveBivariateFailureLaneZero6401 W).natDegree +
      (primitiveBivariateFailureLaneOne6401 W).natDegree)
    (z : F)
    (hnc : ¬ IsCoprime
      (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
      (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) :
    Polynomial.eval z (primitiveLaneResultant6401 W) = 0 := by
  rw [primitiveLaneResultant6401,
    bivariate_resultant_eval_fixed_original_degrees]
  exact resultant_fixed_degree_eq_zero_of_not_isCoprime6401
    _ _ _ _ Polynomial.natDegree_map_le Polynomial.natDegree_map_le
      hpositive hnc
theorem noncoprimePrimitiveOwners_card_le_resultantCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F)
    (hpositive : 0 <
      (primitiveBivariateFailureLaneZero6401 W).natDegree +
      (primitiveBivariateFailureLaneOne6401 W).natDegree)
    (hresultant : primitiveLaneResultant6401 W ≠ 0) :
    (noncoprimePrimitiveOwners6401 W T).card ≤
      primitiveLaneResultantChallengeCap6401 := by
  classical
  let roots := T.filter fun z =>
    Polynomial.eval z (primitiveLaneResultant6401 W) = 0
  have hsubset : noncoprimePrimitiveOwners6401 W T ⊆ roots := by
    intro z hz
    have hz' := hz
    rw [noncoprimePrimitiveOwners6401] at hz'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz').1,
      eval_primitiveLaneResultant_eq_zero_of_not_isCoprime6401
        W hpositive z (Finset.mem_filter.mp hz').2⟩
  calc
    (noncoprimePrimitiveOwners6401 W T).card ≤ roots.card :=
      Finset.card_le_card hsubset
    _ ≤ (primitiveLaneResultant6401 W).natDegree := by
      exact card_filter_eval_eq_zero_le_natDegree
        T (primitiveLaneResultant6401 W) hresultant
    _ ≤ primitiveLaneResultantChallengeCap6401 :=
      primitiveLaneResultant_natDegree_le6401 W
theorem exists_fractionCommonFactor_of_primitiveLaneResultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hresultant : primitiveLaneResultant6401 W = 0) :
    ∃ G : Polynomial (FractionRing F[X]),
      0 < G.natDegree ∧ G.natDegree ≤ 22507 ∧
      G ∣ (primitiveBivariateFailureLaneZero6401 W).map
        (algebraMap F[X] (FractionRing F[X])) ∧
      G ∣ (primitiveBivariateFailureLaneOne6401 W).map
        (algebraMap F[X] (FractionRing F[X])) := by
  classical
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  let L0 := primitiveBivariateFailureLaneZero6401 W
  let L1 := primitiveBivariateFailureLaneOne6401 W
  let K0 : Polynomial (FractionRing F[X]) := L0.map f
  let K1 : Polynomial (FractionRing F[X]) := L1.map f
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hdeg0 : K0.natDegree = L0.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf L0
  have hdeg1 : K1.natDegree = L1.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf L1
  have hfixed : Polynomial.resultant K0 K1
      L0.natDegree L1.natDegree = 0 := by
    rw [Polynomial.resultant_map_map]
    simpa [L0, L1, primitiveLaneResultant6401] using
      congrArg f hresultant
  have hresK : Polynomial.resultant K0 K1 = 0 := by
    simpa only [hdeg0, hdeg1] using hfixed
  have hcriterion := Polynomial.resultant_eq_zero_iff.mp hresK
  have hpair : K0 ≠ 0 ∨ K1 ≠ 0 := hcriterion.1
  have hnotcoprime : ¬ IsCoprime K0 K1 := hcriterion.2
  let G : Polynomial (FractionRing F[X]) := EuclideanDomain.gcd K0 K1
  have hGdiv0 : G ∣ K0 := EuclideanDomain.gcd_dvd_left K0 K1
  have hGdiv1 : G ∣ K1 := EuclideanDomain.gcd_dvd_right K0 K1
  have hGnotUnit : ¬ IsUnit G := by
    intro hunit
    exact hnotcoprime
      (EuclideanDomain.gcd_isUnit_iff.mp hunit)
  have hGne : G ≠ 0 := by
    intro hzero
    rcases hpair with h0 | h1
    · apply h0
      simpa [hzero] using hGdiv0
    · apply h1
      simpa [hzero] using hGdiv1
  have hGdegreeNe : G.degree ≠ 0 := by
    intro hdegree
    exact hGnotUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree)
  have hGnatDegreeNe : G.natDegree ≠ 0 := by
    intro hdegree
    apply hGdegreeNe
    rw [Polynomial.degree_eq_natDegree hGne, hdegree]
    simp
  have hGpositive : 0 < G.natDegree := Nat.pos_of_ne_zero hGnatDegreeNe
  rcases primitiveBivariateFailureLanes_natDegree_le_22507_6401 W with
    ⟨hL0, hL1⟩
  have hGdegree : G.natDegree ≤ 22507 := by
    rcases hpair with h0 | h1
    · calc
        G.natDegree ≤ K0.natDegree :=
          Polynomial.natDegree_le_of_dvd hGdiv0 h0
        _ = L0.natDegree := hdeg0
        _ ≤ 22507 := hL0
    · calc
        G.natDegree ≤ K1.natDegree :=
          Polynomial.natDegree_le_of_dvd hGdiv1 h1
        _ = L1.natDegree := hdeg1
        _ ≤ 22507 := hL1
  exact ⟨G, hGpositive, hGdegree, hGdiv0, hGdiv1⟩
theorem exists_integralPrimitiveCommonFactor_of_primitiveLaneResultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hresultant : primitiveLaneResultant6401 W = 0) :
    ∃ H : F[X][X],
      H.IsPrimitive ∧ 0 < H.natDegree ∧ H.natDegree ≤ 22507 ∧
      H ∣ primitiveBivariateFailureLaneZero6401 W ∧
      H ∣ primitiveBivariateFailureLaneOne6401 W := by
  classical
  obtain ⟨G, hGpositive, hGdegree, hGdiv0, hGdiv1⟩ :=
    exists_fractionCommonFactor_of_primitiveLaneResultant_eq_zero6401
      W hresultant
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  let q : F[X][X] := IsLocalization.integerNormalization
    (nonZeroDivisors F[X]) G
  let H : F[X][X] := q.primPart
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hGne : G ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hGpositive
    omega
  have hqne : q ≠ 0 := by
    intro hzero
    apply hGne
    exact IsFractionRing.integerNormalization_eq_zero_iff.mp hzero
  have hcontentNe : q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  obtain ⟨b, hbmem, hqmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors F[X]) G
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hfbne : f b ≠ 0 := fun hzero =>
    hbne (hf (by simpa using hzero))
  have hfcne : f q.content ≠ 0 := fun hzero =>
    hcontentNe (hf (by simpa using hzero))
  have hproduct :
      Polynomial.C (f q.content) * H.map f = Polynomial.C (f b) * G := by
    calc
      Polynomial.C (f q.content) * H.map f = q.map f := by
        dsimp only [H]
        rw [← Polynomial.map_C, ← Polynomial.map_mul]
        exact congrArg (Polynomial.map f)
          q.eq_C_content_mul_primPart.symm
      _ = b • G := hqmap
      _ = Polynomial.C (f b) * G := by
        rw [Algebra.smul_def]
        rfl
  let c : FractionRing F[X] := f b / f q.content
  have hcne : c ≠ 0 := div_ne_zero hfbne hfcne
  have hscale : H.map f = Polynomial.C c * G := by
    apply mul_left_cancel₀
      (show Polynomial.C (f q.content) ≠ 0 by simpa using hfcne)
    rw [hproduct]
    have hfc : f q.content * c = f b := by
      dsimp [c]
      exact mul_div_cancel₀ _ hfcne
    calc
      Polynomial.C (f b) * G =
          Polynomial.C (f q.content * c) * G := by rw [hfc]
      _ = Polynomial.C (f q.content) *
          (Polynomial.C c * G) := by rw [Polynomial.C_mul, mul_assoc]
  have hHprimitive : H.IsPrimitive := q.isPrimitive_primPart
  have hHdegree : H.natDegree = G.natDegree := by
    calc
      H.natDegree = (H.map f).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hf H).symm
      _ = (Polynomial.C c * G).natDegree := congrArg _ hscale
      _ = G.natDegree := Polynomial.natDegree_C_mul hcne
  have hHmapDiv0 : H.map f ∣
      (primitiveBivariateFailureLaneZero6401 W).map f := by
    rcases hGdiv0 with ⟨Q, hQ⟩
    refine ⟨Polynomial.C c⁻¹ * Q, ?_⟩
    calc
      (primitiveBivariateFailureLaneZero6401 W).map f = G * Q := hQ
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * Q) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * Q) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * Q) := by ring
          _ = G * Q := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = H.map f * (Polynomial.C c⁻¹ * Q) := by rw [hscale]
  have hHmapDiv1 : H.map f ∣
      (primitiveBivariateFailureLaneOne6401 W).map f := by
    rcases hGdiv1 with ⟨Q, hQ⟩
    refine ⟨Polynomial.C c⁻¹ * Q, ?_⟩
    calc
      (primitiveBivariateFailureLaneOne6401 W).map f = G * Q := hQ
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * Q) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * Q) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * Q) := by ring
          _ = G * Q := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = H.map f * (Polynomial.C c⁻¹ * Q) := by rw [hscale]
  have hHdiv0 : H ∣ primitiveBivariateFailureLaneZero6401 W :=
    hHprimitive.dvd_of_fraction_map_dvd_fraction_map hHmapDiv0
  have hHdiv1 : H ∣ primitiveBivariateFailureLaneOne6401 W :=
    hHprimitive.dvd_of_fraction_map_dvd_fraction_map hHmapDiv1
  exact ⟨H, hHprimitive, hHdegree ▸ hGpositive,
    hHdegree ▸ hGdegree, hHdiv0, hHdiv1⟩
theorem primitiveLaneResultant_or_fractionCommonFactor6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) :
    ((primitiveBivariateFailureLaneZero6401 W).natDegree = 0 ∧
      (primitiveBivariateFailureLaneOne6401 W).natDegree = 0) ∨
    (primitiveLaneResultant6401 W = 0 ∧
      ∃ H : F[X][X],
        H.IsPrimitive ∧ 0 < H.natDegree ∧ H.natDegree ≤ 22507 ∧
        H ∣ primitiveBivariateFailureLaneZero6401 W ∧
        H ∣ primitiveBivariateFailureLaneOne6401 W) ∨
    (primitiveLaneResultant6401 W ≠ 0 ∧
      (noncoprimePrimitiveOwners6401 W T).card ≤
        primitiveLaneResultantChallengeCap6401) := by
  by_cases hpositive : 0 <
      (primitiveBivariateFailureLaneZero6401 W).natDegree +
      (primitiveBivariateFailureLaneOne6401 W).natDegree
  · by_cases hresultant : primitiveLaneResultant6401 W = 0
    · exact Or.inr (Or.inl ⟨hresultant,
        exists_integralPrimitiveCommonFactor_of_primitiveLaneResultant_eq_zero6401
          W hresultant⟩)
    · exact Or.inr (Or.inr ⟨hresultant,
        noncoprimePrimitiveOwners_card_le_resultantCap6401
          W T hpositive hresultant⟩)
  · left
    omega
theorem primitiveLaneResultant_or_integralCommonFactor6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) :
    ((primitiveBivariateFailureLaneZero6401 W).natDegree = 0 ∧
      (primitiveBivariateFailureLaneOne6401 W).natDegree = 0) ∨
    (primitiveLaneResultant6401 W = 0 ∧
      ∃ H : F[X][X],
        H.IsPrimitive ∧ 0 < H.natDegree ∧ H.natDegree ≤ 22507 ∧
        H ∣ primitiveBivariateFailureLaneZero6401 W ∧
        H ∣ primitiveBivariateFailureLaneOne6401 W) ∨
    (primitiveLaneResultant6401 W ≠ 0 ∧
      (noncoprimePrimitiveOwners6401 W T).card ≤
        primitiveLaneResultantChallengeCap6401) :=
  primitiveLaneResultant_or_fractionCommonFactor6401 W T
end BCHKSExtremePrimitiveLaneResultantFork6401
end ProximityPrize.SubmissionLower
