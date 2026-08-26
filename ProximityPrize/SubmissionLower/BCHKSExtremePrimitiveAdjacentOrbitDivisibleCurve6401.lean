import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitFixedSecant6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAdjacentOrbitDivisibleCurve6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSSubfieldFrobenius6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedGRS6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedSecant6401
open BCHKSFrobeniusFixedOrbitDivisibility6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section EmptyPuncture
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem twoRowSourceBadCoordinates_eq_empty_of_rightLane_degree_eq_22507_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hBdegree : B.natDegree = homogeneousDirectionCap6401) :
    twoRowSourceBadCoordinates6401 W = ∅ := by
  have hcap :=
    (twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G A B hG hA hB hzero hone).2
  have hlocator := twoRowSourcePunctureLocator_ne_zero6401 W
  have hproductDegree :
      (twoRowSourcePunctureLocator6401 W * B).natDegree =
        (twoRowSourcePunctureLocator6401 W).natDegree + B.natDegree :=
    Polynomial.natDegree_mul hlocator hB
  rw [hproductDegree, hBdegree,
    twoRowSourcePunctureLocator_natDegree6401] at hcap
  have hcard : (twoRowSourceBadCoordinates6401 W).card = 0 := by
    norm_num [homogeneousDirectionCap6401] at hcap ⊢
    omega
  exact Finset.card_eq_zero.mp hcard
end EmptyPuncture
section NormEvaluation
variable {F : Type*} [Field F]
theorem scalarFrobeniusNormSix_ne_zero6401
    (sigma : F →+* F) (b : F) (hb : b ≠ 0) :
    scalarFrobeniusNormSix sigma b ≠ 0 := by
  have h1 : sigma b ≠ 0 :=
    fun hz ↦ hb (sigma.injective (by simpa using hz))
  have h2 : sigma (sigma b) ≠ 0 :=
    fun hz ↦ h1 (sigma.injective (by simpa using hz))
  have h3 : sigma (sigma (sigma b)) ≠ 0 :=
    fun hz ↦ h2 (sigma.injective (by simpa using hz))
  have h4 : sigma (sigma (sigma (sigma b))) ≠ 0 :=
    fun hz ↦ h3 (sigma.injective (by simpa using hz))
  have h5 : sigma (sigma (sigma (sigma (sigma b)))) ≠ 0 :=
    fun hz ↦ h4 (sigma.injective (by simpa using hz))
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb h1) h2) h3)
      h4) h5
theorem polynomialFrobeniusNormSix_eval_ne_zero_of_fixed6401
    (sigma : F →+* F) (B : F[X]) (x : F)
    (hx : sigma x = x) (hB : B.eval x ≠ 0) :
    (polynomialFrobeniusNormSix sigma B).eval x ≠ 0 := by
  rw [polynomialFrobeniusNormSix_eval_of_fixed sigma B x hx]
  exact scalarFrobeniusNormSix_ne_zero6401 sigma (B.eval x) hB
end NormEvaluation
section PairClosure
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem pairAgreement_inter_card_ge_108564_6401
    (Az Aw : Finset (Fin n6401))
    (hz : a6401 ≤ Az.card) (hw : a6401 ≤ Aw.card) :
    108564 ≤ (Az ∩ Aw).card := by
  have hunion : (Az ∪ Aw).card ≤ n6401 := by
    calc
      (Az ∪ Aw).card ≤ (Finset.univ : Finset (Fin n6401)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n6401 := by simp
  have hcount := Finset.card_union_add_card_inter Az Aw
  norm_num [a6401, n6401] at hz hw hunion ⊢
  omega
theorem recursiveAdjacentOrbit_fixedSecant_eq_zero_of_direction_dvd6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B Q1 : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hBdegree : B.natDegree = homogeneousDirectionCap6401)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hAgreementCard : ∀ z ∈ S, a6401 ≤ (Aset z).card)
    (hAgreement : ∀ z ∈ S, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i)
    (hQdegree : Q1.natDegree ≤
      adjacentOrbitShortenedTargetDegree6401)
    (hQeval : ∀ i : TwoRowGoodIndex6401 W,
      Q1.eval (twoRowGoodAlpha6401 W i) =
        adjacentOrbitShortenedReceivedDirection6401 W B i)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z w : F) (hzS : z ∈ S) (hwS : w ∈ S)
    (hz : z ∈ R.goodChallenges6401)
    (hw : w ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) (hGw : G.eval w ≠ 0)
    (hzw : z ≠ w)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B)
    (hdivQ : B ∣ Q1) :
    adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w) = 0 := by
  let H := adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w)
  have hbad : twoRowSourceBadCoordinates6401 W = ∅ :=
    twoRowSourceBadCoordinates_eq_empty_of_rightLane_degree_eq_22507_6401
      W R G A B hG hA hB hzero hone hBdegree
  have hHdegree : H.natDegree ≤ 153578 := by
    have hbound := adjacentOrbitFixedSecant_natDegree_le6401
      B Q1 z w (Owner z) (Owner w)
        adjacentOrbitShortenedTargetDegree6401 hBdegree.le hQdegree
        (hOwnerDegree z hzS) (hOwnerDegree w hwS) le_rfl
    simpa [H, adjacentOrbitShortenedTargetDegree6401,
      homogeneousDirectionCap6401, ownerDegreeCap6401] using hbound
  have hHfixed : H.map sigma = H := by
    exact recursiveAdjacentOrbit_fixedSecant_map_eq_self6401
      W R G A B Q1 hG hA hB hcoprime hadjacent hzero hone hBdegree.le
        hOwnerDegree hQdegree hQeval hsigma hfixed z w hzS hwS hz hw
          hGz hGw
  have hB22507 : B.natDegree = 22507 := by
    simpa [homogeneousDirectionCap6401] using hBdegree
  obtain ⟨U, hfactor, hUdegree⟩ :=
    exists_adjacentOrbitFixedSecant_normResidual6401
      sigma B Q1 z w (Owner z) (Owner w) hzw hB hB22507 hHdegree
        hHfixed horbit hdivQ
  let I : Finset (Fin n6401) := Aset z ∩ Aset w
  have hIcard : 108564 ≤ I.card := by
    exact pairAgreement_inter_card_ge_108564_6401
      (Aset z) (Aset w) (hAgreementCard z hzS) (hAgreementCard w hwS)
  have hUeval : ∀ i ∈ I, U.eval (alpha i) = 0 := by
    intro i hi
    have hiz : i ∈ Aset z := (Finset.mem_inter.mp hi).1
    have hiw : i ∈ Aset w := (Finset.mem_inter.mp hi).2
    have higood : i ∉ twoRowSourceBadCoordinates6401 W := by
      rw [hbad]
      simp
    let igood : TwoRowGoodIndex6401 W := ⟨i, higood⟩
    have hQi := hQeval igood
    change Q1.eval (alpha i) = B.eval (alpha i) * u1 i at hQi
    have hHeval : H.eval (alpha i) = 0 := by
      dsimp only [H, adjacentOrbitFixedSecant6401]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      rw [hQi, hAgreement z hzS i hiz, hAgreement w hwS i hiw]
      ring
    have hBvalue : B.eval (alpha i) ≠ 0 :=
      adjacentOrbit_rightEval_ne_zero_of_isCoprime6401
        sigma (alpha i) A B (hfixed i) hadjacent hcoprime
    have hnormValue :
        (polynomialFrobeniusNormSix sigma B).eval (alpha i) ≠ 0 :=
      polynomialFrobeniusNormSix_eval_ne_zero_of_fixed6401
        sigma B (alpha i) (hfixed i) hBvalue
    have hproduct :
        (polynomialFrobeniusNormSix sigma B).eval (alpha i) *
            U.eval (alpha i) = 0 := by
      rw [← Polynomial.eval_mul, ← hfactor]
      exact hHeval
    exact (mul_eq_zero.mp hproduct).resolve_left hnormValue
  have hUzero : U = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      U (I.map alpha)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact hUeval i hi
    · rw [Finset.card_map]
      omega
  rw [hfactor, hUzero, mul_zero]
end PairClosure
section CurveClosure
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem polynomialAffineCurveWitness_of_adjacentOrbitDirection_dvd6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B Q1 : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hBdegree : B.natDegree = homogeneousDirectionCap6401)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hAgreementCard : ∀ z ∈ S, a6401 ≤ (Aset z).card)
    (hAgreement : ∀ z ∈ S, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i)
    (hQdegree : Q1.natDegree ≤
      adjacentOrbitShortenedTargetDegree6401)
    (hQeval : ∀ i : TwoRowGoodIndex6401 W,
      Q1.eval (twoRowGoodAlpha6401 W i) =
        adjacentOrbitShortenedReceivedDirection6401 W B i)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (T : Finset F) (hT : T ⊆ R.goodChallenges6401)
    (hTS : T ⊆ S)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hlarge : q6401 < T.card)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B)
    (hdivQ : B ∣ Q1) :
    PolynomialAffineCurveWitness6401 S Owner := by
  obtain ⟨V, hQV⟩ := hdivQ
  have hVdegree : V.natDegree ≤ ownerDegreeCap6401 := by
    by_cases hV : V = 0
    · simp [hV]
    · have hQ : Q1 ≠ 0 := by
        rw [hQV]
        exact mul_ne_zero hB hV
      have hdegree : B.natDegree + V.natDegree = Q1.natDegree := by
        rw [hQV, Polynomial.natDegree_mul hB hV]
      norm_num [homogeneousDirectionCap6401,
        adjacentOrbitShortenedTargetDegree6401,
        ownerDegreeCap6401] at hBdegree hQdegree ⊢
      omega
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hrT⟩ := hTnonempty
  let p0 : F[X] := Owner r - Polynomial.C r * V
  have hCVdegree : (Polynomial.C r * V).natDegree ≤
      ownerDegreeCap6401 := by
    calc
      (Polynomial.C r * V).natDegree ≤
          (Polynomial.C r).natDegree + V.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + ownerDegreeCap6401 := by
        exact Nat.add_le_add (by simp) hVdegree
      _ = ownerDegreeCap6401 := Nat.zero_add _
  have hp0degree : p0.natDegree ≤ ownerDegreeCap6401 := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hOwnerDegree r (hTS hrT)) hCVdegree)
  refine ⟨p0, V, hp0degree, hVdegree, T, hTS, ?_, ?_⟩
  · have hout : weakCurveOutput6401 ≤ q6401 := by native_decide
    omega
  · intro z hzT
    by_cases hzr : z = r
    · subst z
      simp [p0]
    · have hsecant :=
        recursiveAdjacentOrbit_fixedSecant_eq_zero_of_direction_dvd6401
          W R G A B Q1 hG hA hB hcoprime hadjacent hzero hone hBdegree
            hOwnerDegree hAgreementCard hAgreement hQdegree hQeval hsigma
            hfixed z r (hTS hzT) (hTS hrT) (hT hzT) (hT hrT)
              (hTG z hzT) (hTG r hrT) hzr horbit ⟨V, hQV⟩
      have hinner :
          Owner z - Owner r - Polynomial.C (z - r) * V = 0 := by
        apply mul_left_cancel₀ hB
        rw [mul_zero]
        rw [adjacentOrbitFixedSecant6401, hQV] at hsecant
        calc
          B * (Owner z - Owner r - Polynomial.C (z - r) * V) =
              B * (Owner z - Owner r) -
                Polynomial.C (z - r) * (B * V) := by ring
          _ = 0 := hsecant
      dsimp only [p0]
      rw [map_sub] at hinner
      linear_combination hinner
theorem exists_adjacentOrbitDirection_not_dvd_or_curve6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A B : F[X])
    (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hadjacent : A = B.map sigma)
    (hzero : R.laneZero6401 =
      Polynomial.C G * A.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B.map Polynomial.C)
    (hBdegree : B.natDegree = homogeneousDirectionCap6401)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
    (hAgreementCard : ∀ z ∈ S, a6401 ≤ (Aset z).card)
    (hAgreement : ∀ z ∈ S, ∀ i ∈ Aset z,
      (Owner z).eval (alpha i) = u0 i + z * u1 i)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (T : Finset F) (hT : T ⊆ R.goodChallenges6401)
    (hTS : T ⊆ S)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hlarge : q6401 < T.card)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B) :
    (∃ Q1 : F[X],
        Q1.natDegree ≤ adjacentOrbitShortenedTargetDegree6401 ∧
        (∀ i : TwoRowGoodIndex6401 W,
          Q1.eval (twoRowGoodAlpha6401 W i) =
            adjacentOrbitShortenedReceivedDirection6401 W B i) ∧
        ¬ B ∣ Q1) ∨
      PolynomialAffineCurveWitness6401 S Owner := by
  obtain ⟨Q1, hQdegree, hQeval⟩ :=
    exists_adjacentOrbitShortenedDirectionPolynomial6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hBdegree.le
        hOwnerDegree hsigma hfixed hfixedCard T hT hTS hTG hlarge
  by_cases hdivQ : B ∣ Q1
  · right
    exact polynomialAffineCurveWitness_of_adjacentOrbitDirection_dvd6401
      W R G A B Q1 hG hA hB hcoprime hadjacent hzero hone hBdegree
        hOwnerDegree hAgreementCard hAgreement hQdegree hQeval hsigma
          hfixed T hT hTS hTG hlarge horbit hdivQ
  · exact Or.inl ⟨Q1, hQdegree, hQeval, hdivQ⟩
end CurveClosure
end BCHKSExtremePrimitiveAdjacentOrbitDivisibleCurve6401
end ProximityPrize.SubmissionLower
