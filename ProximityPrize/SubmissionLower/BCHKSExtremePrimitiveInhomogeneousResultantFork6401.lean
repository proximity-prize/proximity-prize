import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveLaneFactorDescent6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveInhomogeneousResultantFork6401
open Polynomial
open Polynomial.Bivariate
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSExtremeThreeRectangleProducer6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveLaneCommonFactorSource6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSFrobeniusGraphInjectivity6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
def primitiveInhomogeneousChallengeCap6401 : Nat :=
  extremeDepth6401 2 - 1
theorem primitiveInhomogeneousChallengeCap_exact6401 :
    primitiveInhomogeneousChallengeCap6401 = 47957940448247 := by
  native_decide
theorem primitiveInhomogeneousLane_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    (W.sourcePuncture.frame.reduced 0).natDegree ≤ 153578 := by
  simpa [primitiveThreeShiftXCap6401] using
    W.sourcePuncture.reduced_caps 0
theorem primitiveInhomogeneousLane_coeffDegreeLE6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    BivariateCoeffDegreeLE (W.sourcePuncture.frame.reduced 0)
      primitiveInhomogeneousChallengeCap6401 := by
  intro n
  apply (coeff_natDegree_le_swap_natDegree
    (W.sourcePuncture.frame.reduced 0) n).trans
  apply (reduced_swap_natDegree_le_thirdRow6401 W 0).trans
  rw [W.rows_eq_selected]
  simpa [primitiveInhomogeneousChallengeCap6401,
    selectedExtremeRow6401] using
    extremeCoefficientRowMap_zero_inner_natDegree_le6401 2
      (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
noncomputable def primitiveInhomogeneousFactorResultant6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W) : F[X] :=
  Polynomial.resultant C.factor (W.sourcePuncture.frame.reduced 0)
theorem exists_integralPrimitiveInhomogeneousCommonFactor_of_resultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (hresultant : primitiveInhomogeneousFactorResultant6401 C = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧
      K ∣ C.factor ∧ K ∣ W.sourcePuncture.frame.reduced 0 := by
  classical
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  let H := C.factor
  let Q := W.sourcePuncture.frame.reduced 0
  let KH : Polynomial (FractionRing F[X]) := H.map f
  let KQ : Polynomial (FractionRing F[X]) := Q.map f
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hHdegree : KH.natDegree = H.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf H
  have hQdegree : KQ.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have hfixed : Polynomial.resultant KH KQ H.natDegree Q.natDegree = 0 := by
    rw [Polynomial.resultant_map_map]
    simpa [H, Q, primitiveInhomogeneousFactorResultant6401] using
      congrArg f hresultant
  have hresK : Polynomial.resultant KH KQ = 0 := by
    simpa only [hHdegree, hQdegree] using hfixed
  have hcriterion := Polynomial.resultant_eq_zero_iff.mp hresK
  have hpair : KH ≠ 0 ∨ KQ ≠ 0 := hcriterion.1
  have hnotcoprime : ¬ IsCoprime KH KQ := hcriterion.2
  let G : Polynomial (FractionRing F[X]) := EuclideanDomain.gcd KH KQ
  have hGdivH : G ∣ KH := EuclideanDomain.gcd_dvd_left KH KQ
  have hGdivQ : G ∣ KQ := EuclideanDomain.gcd_dvd_right KH KQ
  have hGnotUnit : ¬ IsUnit G := by
    intro hunit
    exact hnotcoprime (EuclideanDomain.gcd_isUnit_iff.mp hunit)
  have hGne : G ≠ 0 := by
    intro hzero
    rcases hpair with hHne | hQne
    · apply hHne
      simpa [hzero] using hGdivH
    · apply hQne
      simpa [hzero] using hGdivQ
  have hGdegreeNe : G.degree ≠ 0 := by
    intro hdegree
    exact hGnotUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree)
  have hGnatDegreeNe : G.natDegree ≠ 0 := by
    intro hdegree
    apply hGdegreeNe
    rw [Polynomial.degree_eq_natDegree hGne, hdegree]
    simp
  have hGpositive : 0 < G.natDegree := Nat.pos_of_ne_zero hGnatDegreeNe
  let q : F[X][X] := IsLocalization.integerNormalization
    (nonZeroDivisors F[X]) G
  let K : F[X][X] := q.primPart
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
      Polynomial.C (f q.content) * K.map f = Polynomial.C (f b) * G := by
    calc
      Polynomial.C (f q.content) * K.map f = q.map f := by
        dsimp only [K]
        rw [← Polynomial.map_C, ← Polynomial.map_mul]
        exact congrArg (Polynomial.map f)
          q.eq_C_content_mul_primPart.symm
      _ = b • G := hqmap
      _ = Polynomial.C (f b) * G := by
        rw [Algebra.smul_def]
        rfl
  let c : FractionRing F[X] := f b / f q.content
  have hcne : c ≠ 0 := div_ne_zero hfbne hfcne
  have hscale : K.map f = Polynomial.C c * G := by
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
  have hKprimitive : K.IsPrimitive := q.isPrimitive_primPart
  have hKdegree : K.natDegree = G.natDegree := by
    calc
      K.natDegree = (K.map f).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hf K).symm
      _ = (Polynomial.C c * G).natDegree := congrArg _ hscale
      _ = G.natDegree := Polynomial.natDegree_C_mul hcne
  have hKmapDivH : K.map f ∣ H.map f := by
    rcases hGdivH with ⟨D, hD⟩
    refine ⟨Polynomial.C c⁻¹ * D, ?_⟩
    calc
      H.map f = G * D := hD
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * D) := by ring
          _ = G * D := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = K.map f * (Polynomial.C c⁻¹ * D) := by rw [hscale]
  have hKmapDivQ : K.map f ∣ Q.map f := by
    rcases hGdivQ with ⟨D, hD⟩
    refine ⟨Polynomial.C c⁻¹ * D, ?_⟩
    calc
      Q.map f = G * D := hD
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * D) := by ring
          _ = G * D := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = K.map f * (Polynomial.C c⁻¹ * D) := by rw [hscale]
  have hKdivH : K ∣ H :=
    hKprimitive.dvd_of_fraction_map_dvd_fraction_map hKmapDivH
  have hKdivQ : K ∣ Q :=
    hKprimitive.dvd_of_fraction_map_dvd_fraction_map hKmapDivQ
  exact ⟨K, hKprimitive, hKdegree ▸ hGpositive,
    by simpa [H] using hKdivH, by simpa [Q] using hKdivQ⟩
noncomputable def primitiveInhomogeneousFactorOwnerCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W) : Nat :=
  (W.sourcePuncture.frame.reduced 0).natDegree *
      (Polynomial.Bivariate.swap C.factor).natDegree +
    C.factor.natDegree * primitiveInhomogeneousChallengeCap6401 +
    (Polynomial.Bivariate.swap C.factor).natDegree
def primitiveInhomogeneousFactorUniformOwnerCap6401 : Nat :=
  153578 * primitiveLaneFactorDescentExceptionCap6401 +
    22507 * primitiveInhomogeneousChallengeCap6401 +
    primitiveLaneFactorDescentExceptionCap6401
theorem primitiveInhomogeneousFactorUniformOwnerCap_exact6401 :
    primitiveInhomogeneousFactorUniformOwnerCap6401 =
      8444721901769867663 := by
  native_decide
theorem primitiveInhomogeneousFactorResultant_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W) :
    (primitiveInhomogeneousFactorResultant6401 C).natDegree ≤
      (W.sourcePuncture.frame.reduced 0).natDegree *
          (Polynomial.Bivariate.swap C.factor).natDegree +
        C.factor.natDegree * primitiveInhomogeneousChallengeCap6401 := by
  let H := C.factor
  let Q0 := W.sourcePuncture.frame.reduced 0
  have hraw := bivariate_resultant_natDegree_le
    H Q0 H.natDegree Q0.natDegree
  change (primitiveInhomogeneousFactorResultant6401 C).natDegree ≤ _
  apply hraw.trans
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left Q0.natDegree
      (by
        unfold degreeX
        apply Finset.sup_le
        intro n hn
        exact coeff_natDegree_le_swap_natDegree H n)
  · exact Nat.mul_le_mul_left H.natDegree
      (by
        unfold degreeX
        apply Finset.sup_le
        intro n hn
        exact primitiveInhomogeneousLane_coeffDegreeLE6401 W n)
private theorem resultant_fixed_degree_eq_zero_of_left_exact6401
    {F : Type} [Field F] (H Q : F[X]) (h n : Nat)
    (hHdegree : H.natDegree = h) (hQdegree : Q.natDegree ≤ n)
    (hpositive : 0 < h) (hnc : ¬ IsCoprime H Q) :
    Polynomial.resultant H Q h n = 0 := by
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hHdegree
    omega
  have hstandard : Polynomial.resultant H Q = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hHne, hnc⟩
  have hn : Q.natDegree + (n - Q.natDegree) = n :=
    Nat.add_sub_of_le hQdegree
  rw [← hHdegree, ← hn, Polynomial.resultant_add_right_deg]
  · simp [hstandard]
  · exact le_rfl
theorem eval_primitiveInhomogeneousFactorResultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (hlead : Polynomial.eval z C.factor.leadingCoeff ≠ 0) :
    Polynomial.eval z (primitiveInhomogeneousFactorResultant6401 C) = 0 := by
  let Hz := specializeCoeffZ z C.factor
  let Qz := specializeRow z W.sourcePuncture.frame.reduced 0
  have hHzdegree : Hz.natDegree = C.factor.natDegree := by
    exact Polynomial.natDegree_map_eq_iff.mpr (Or.inl hlead)
  have hHzpositive : 0 < Hz.natDegree := by
    rw [hHzdegree]
    exact C.positiveLocatorDegree
  have hdiv : Hz ∣ Qz := C.specializes_dvd_ownerRow z hz 0
  have hnc : ¬ IsCoprime Hz Qz := by
    intro hcoprime
    exact (Polynomial.not_isUnit_of_natDegree_pos Hz hHzpositive)
      (hcoprime.isUnit_of_dvd hdiv)
  rw [primitiveInhomogeneousFactorResultant6401,
    bivariate_resultant_eval_fixed_original_degrees]
  exact resultant_fixed_degree_eq_zero_of_left_exact6401
    Hz Qz C.factor.natDegree
      (W.sourcePuncture.frame.reduced 0).natDegree
        hHzdegree Polynomial.natDegree_map_le C.positiveLocatorDegree hnc
theorem goodOwners_card_le_inhomogeneousFactorCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (hresultant : primitiveInhomogeneousFactorResultant6401 C ≠ 0) :
    (rowTwoGoodChallenges6401 W.commonDirection S).card ≤
      primitiveInhomogeneousFactorOwnerCap6401 C := by
  classical
  let G := rowTwoGoodChallenges6401 W.commonDirection S
  let bad := G.filter fun z => Polynomial.eval z C.factor.leadingCoeff = 0
  let stable := G.filter fun z => Polynomial.eval z C.factor.leadingCoeff ≠ 0
  have hfactorNe : C.factor ≠ 0 := C.primitive.ne_zero
  have hleadNe : C.factor.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hfactorNe
  have hbadCard : bad.card ≤
      (Polynomial.Bivariate.swap C.factor).natDegree := by
    apply (card_filter_eval_eq_zero_le_natDegree G _ hleadNe).trans
    change (C.factor.coeff C.factor.natDegree).natDegree ≤ _
    exact coeff_natDegree_le_swap_natDegree C.factor C.factor.natDegree
  have hstableRoots : ∀ z ∈ stable,
      Polynomial.eval z (primitiveInhomogeneousFactorResultant6401 C) = 0 := by
    intro z hz
    exact eval_primitiveInhomogeneousFactorResultant_eq_zero6401 C z
      (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  have hstableCard : stable.card ≤
      (primitiveInhomogeneousFactorResultant6401 C).natDegree := by
    let roots := G.filter fun z =>
      Polynomial.eval z (primitiveInhomogeneousFactorResultant6401 C) = 0
    have hsubset : stable ⊆ roots := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨( Finset.mem_filter.mp hz).1,
        hstableRoots z hz⟩
    exact (Finset.card_le_card hsubset).trans
      (card_filter_eval_eq_zero_le_natDegree G _ hresultant)
  have hsplit : bad.card + stable.card = G.card := by
    change
      (G.filter fun z => Polynomial.eval z C.factor.leadingCoeff = 0).card +
        (G.filter fun z => ¬
          Polynomial.eval z C.factor.leadingCoeff = 0).card = G.card
    exact Finset.card_filter_add_card_filter_not
      (s := G) (fun z => Polynomial.eval z C.factor.leadingCoeff = 0)
  have hresdegree := primitiveInhomogeneousFactorResultant_natDegree_le6401 C
  change G.card ≤ _
  rw [← hsplit]
  dsimp [primitiveInhomogeneousFactorOwnerCap6401]
  have hsum := Nat.add_le_add hbadCard (hstableCard.trans hresdegree)
  omega
theorem goodOwners_card_le_inhomogeneousFactorUniformCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (hresultant : primitiveInhomogeneousFactorResultant6401 C ≠ 0) :
    (rowTwoGoodChallenges6401 W.commonDirection S).card ≤
      primitiveInhomogeneousFactorUniformOwnerCap6401 := by
  apply (goodOwners_card_le_inhomogeneousFactorCap6401 C hresultant).trans
  dsimp [primitiveInhomogeneousFactorOwnerCap6401,
    primitiveInhomogeneousFactorUniformOwnerCap6401]
  have hQ0 := primitiveInhomogeneousLane_natDegree_le6401 W
  have hHX := C.locatorDegree_le
  have hHZ := commonHomogeneousFactor_swap_natDegree_le6401
    W C.factor C.primitive.ne_zero
      (by
        exact dvd_neg.mp C.dividesLaneOne)
      (by simpa [primitiveBivariateFailureLaneZero6401] using
        C.dividesLaneZero)
  have hfirst := Nat.mul_le_mul hQ0 hHZ
  have hsecond := Nat.mul_le_mul_right
    primitiveInhomogeneousChallengeCap6401 hHX
  exact Nat.add_le_add (Nat.add_le_add hfirst hsecond) hHZ
theorem exists_globalCommonSubfactorDescent_of_inhomogeneousResultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (hresultant : primitiveInhomogeneousFactorResultant6401 C = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ C.factor ∧
      (∀ j, K ∣ W.sourcePuncture.frame.reduced j) ∧
      Nonempty (PrimitiveLaneFactorDescent6401 W) := by
  obtain ⟨K, hKprimitive, hKpositive, hKfactor, hKzero⟩ :=
    exists_integralPrimitiveInhomogeneousCommonFactor_of_resultant_eq_zero6401
      C hresultant
  have hKone : K ∣ W.sourcePuncture.frame.reduced 1 :=
    hKfactor.trans (dvd_neg.mp C.dividesLaneOne)
  have hKtwo : K ∣ W.sourcePuncture.frame.reduced 2 :=
    hKfactor.trans C.dividesLaneZero
  have hKall : ∀ j, K ∣ W.sourcePuncture.frame.reduced j := by
    intro j
    fin_cases j
    · exact hKzero
    · exact hKone
    · exact hKtwo
  exact ⟨K, hKprimitive, hKpositive, hKfactor, hKall,
    exists_primitiveLaneFactorDescent6401 W K hKpositive hKall⟩
theorem globalCommonSubfactorDescent_or_ownerCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W) :
    (∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ C.factor ∧
      (∀ j, K ∣ W.sourcePuncture.frame.reduced j) ∧
      Nonempty (PrimitiveLaneFactorDescent6401 W)) ∨
    (primitiveInhomogeneousFactorResultant6401 C ≠ 0 ∧
      (rowTwoGoodChallenges6401 W.commonDirection S).card ≤
        primitiveInhomogeneousFactorOwnerCap6401 C) := by
  by_cases hresultant : primitiveInhomogeneousFactorResultant6401 C = 0
  · exact Or.inl
      (exists_globalCommonSubfactorDescent_of_inhomogeneousResultant_eq_zero6401
        C hresultant)
  · exact Or.inr ⟨hresultant,
      goodOwners_card_le_inhomogeneousFactorCap6401 C hresultant⟩
theorem inhomogeneousDivides_or_zeroResultant_or_ownerCap6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W) :
    (C.factor ∣ W.sourcePuncture.frame.reduced 0 ∧
      Nonempty (PrimitiveLaneFactorDescent6401 W)) ∨
    (¬ (C.factor ∣ W.sourcePuncture.frame.reduced 0) ∧
      primitiveInhomogeneousFactorResultant6401 C = 0) ∨
    (primitiveInhomogeneousFactorResultant6401 C ≠ 0 ∧
      (rowTwoGoodChallenges6401 W.commonDirection S).card ≤
        primitiveInhomogeneousFactorOwnerCap6401 C) := by
  by_cases hdiv : C.factor ∣ W.sourcePuncture.frame.reduced 0
  · exact Or.inl ⟨hdiv,
      PrimitiveLaneCommonFactorSource6401.descend_of_dvd_inhomogeneous6401
        C hdiv⟩
  · by_cases hres : primitiveInhomogeneousFactorResultant6401 C = 0
    · exact Or.inr (Or.inl ⟨hdiv, hres⟩)
    · exact Or.inr (Or.inr ⟨hres,
        goodOwners_card_le_inhomogeneousFactorCap6401 C hres⟩)
end BCHKSExtremePrimitiveInhomogeneousResultantFork6401
end ProximityPrize.SubmissionLower
