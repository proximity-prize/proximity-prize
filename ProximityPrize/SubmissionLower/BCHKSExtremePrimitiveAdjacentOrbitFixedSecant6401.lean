import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAdjacentOrbitShortenedGRS6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusFixedOrbitDivisibility6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAdjacentOrbitFixedSecant6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSSubfieldFrobenius6401
open BCHKSFrobeniusFixedOrbitDivisibility6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveAdjacentOrbitFixedError6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedSyndrome6401
open BCHKSExtremePrimitiveAdjacentOrbitShortenedGRS6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
section Algebra
variable {F : Type*} [Field F]
noncomputable def adjacentOrbitFixedSecant6401
    (B Q1 : F[X]) (z w : F) (Pz Pw : F[X]) : F[X] :=
  B * (Pz - Pw) - Polynomial.C (z - w) * Q1
noncomputable def adjacentOrbitClearedOwner6401
    (B Q1 : F[X]) (z : F) (Pz : F[X]) : F[X] :=
  B * Pz - Polynomial.C z * Q1
theorem adjacentOrbitClearedOwner_sub6401
    (B Q1 : F[X]) (z w : F) (Pz Pw : F[X]) :
    adjacentOrbitClearedOwner6401 B Q1 z Pz -
        adjacentOrbitClearedOwner6401 B Q1 w Pw =
      adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw := by
  simp only [adjacentOrbitClearedOwner6401, adjacentOrbitFixedSecant6401,
    map_sub]
  ring
theorem adjacentOrbitFixedSecant_natDegree_le6401
    (B Q1 : F[X]) (z w : F) (Pz Pw : F[X]) (D : Nat)
    (hB : B.natDegree ≤ homogeneousDirectionCap6401)
    (hQ : Q1.natDegree ≤ D)
    (hPz : Pz.natDegree ≤ ownerDegreeCap6401)
    (hPw : Pw.natDegree ≤ ownerDegreeCap6401)
    (hD : homogeneousDirectionCap6401 + ownerDegreeCap6401 ≤ D) :
    (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).natDegree ≤ D := by
  unfold adjacentOrbitFixedSecant6401
  refine (Polynomial.natDegree_sub_le
    (B * (Pz - Pw)) (Polynomial.C (z - w) * Q1)).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_mul_le).trans ?_
    exact (Nat.add_le_add hB
      ((Polynomial.natDegree_sub_le Pz Pw).trans (max_le hPz hPw))).trans hD
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have hC : (Polynomial.C (z - w) : F[X]).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_C]
    simpa using Nat.add_le_add hC hQ
theorem dvd_adjacentOrbitFixedSecant_iff_dvd_direction6401
    (B Q1 : F[X]) (z w : F) (Pz Pw : F[X]) (hzw : z ≠ w) :
    B ∣ adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw ↔ B ∣ Q1 := by
  have hsub : z - w ≠ 0 := sub_ne_zero.mpr hzw
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨Polynomial.C ((z - w)⁻¹) * (Pz - Pw - K), ?_⟩
    calc
      Q1 = Polynomial.C ((z - w)⁻¹) *
          (Polynomial.C (z - w) * Q1) := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hsub,
          Polynomial.C_1, one_mul]
      _ = Polynomial.C ((z - w)⁻¹) *
          (B * (Pz - Pw) - adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw) := by
        simp only [adjacentOrbitFixedSecant6401]
        ring
      _ = Polynomial.C ((z - w)⁻¹) *
          (B * (Pz - Pw) - B * K) := by rw [hK]
      _ = B * (Polynomial.C ((z - w)⁻¹) * (Pz - Pw - K)) := by
        ring
  · rintro ⟨V, hV⟩
    refine ⟨Pz - Pw - Polynomial.C (z - w) * V, ?_⟩
    rw [adjacentOrbitFixedSecant6401, hV]
    ring
end Algebra
section SourceFixedness
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem adjacentOrbitFixedSecant_eval_eq_error_sub6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (B Q1 : F[X])
    (hQeval : ∀ i : TwoRowGoodIndex6401 W,
      Q1.eval (twoRowGoodAlpha6401 W i) =
        adjacentOrbitShortenedReceivedDirection6401 W B i)
    (z w : F) (i : TwoRowGoodIndex6401 W) :
    (adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w)).eval
        (twoRowGoodAlpha6401 W i) =
      adjacentOrbitWeightedFullError6401 W B z i.1 -
        adjacentOrbitWeightedFullError6401 W B w i.1 := by
  have hQi := hQeval i
  change Q1.eval (alpha i.1) = B.eval (alpha i.1) * u1 i.1 at hQi
  change (adjacentOrbitFixedSecant6401 B Q1 z w
      (Owner z) (Owner w)).eval (alpha i.1) = _
  simp only [adjacentOrbitFixedSecant6401, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C,
    adjacentOrbitWeightedFullError6401, fullOwnerError6401,
    twoRowGoodAlpha6401]
  rw [hQi]
  ring
theorem recursiveAdjacentOrbit_fixedSecant_map_eq_self6401
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
    (hBdegree : B.natDegree ≤ homogeneousDirectionCap6401)
    (hOwnerDegree : ∀ z ∈ S,
      (Owner z).natDegree ≤ ownerDegreeCap6401)
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
    (hGz : G.eval z ≠ 0) (hGw : G.eval w ≠ 0) :
    (adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w)).map sigma =
      adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w) := by
  let H := adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w)
  have hbad := twoRowSourceBadCoordinates_card_le_22507_of_terminalLanes6401
    W R G A B hG hA hB hzero hone
  have hledger := adjacentOrbitShortened_window_ledger6401 W (by
    simpa [homogeneousDirectionCap6401] using hbad)
  have hHdegree : H.natDegree ≤
      adjacentOrbitShortenedTargetDegree6401 := by
    exact adjacentOrbitFixedSecant_natDegree_le6401
      B Q1 z w (Owner z) (Owner w)
        adjacentOrbitShortenedTargetDegree6401 hBdegree hQdegree
        (hOwnerDegree z hzS) (hOwnerDegree w hwS) le_rfl
  have hHmapDegree : (H.map sigma).natDegree ≤
      adjacentOrbitShortenedTargetDegree6401 :=
    Polynomial.natDegree_map_le.trans hHdegree
  have hzfixed :=
    recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        z hz hGz
  have hwfixed :=
    recursiveAdjacentOrbit_weightedError_fixed_off_twoRowPuncture6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hsigma hfixed
        w hw hGw
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (H.map sigma) H (twoRowGoodAlpha6401 W).injective
  · intro i
    rw [eval_map_eq_map_eval_of_fixed sigma H
      (twoRowGoodAlpha6401 W i) (twoRowGoodAlpha_fixed6401 W hfixed i)]
    have hHeval := adjacentOrbitFixedSecant_eval_eq_error_sub6401
      W B Q1 hQeval z w i
    rw [hHeval, map_sub, hzfixed.2.1 i.1 i.2,
      hwfixed.2.1 i.1 i.2]
  · have htarget := adjacentOrbitShortened_parameters_exact6401.1
    have hcard := hledger.1
    exact max_lt (hHmapDegree.trans_lt (by omega))
      (hHdegree.trans_lt (by omega))
end SourceFixedness
section NormFork
variable {F : Type} [Field F]
theorem adjacentOrbitFixedSecant_normResidual_or_obstruction6401
    (sigma : F →+* F) (B Q1 : F[X]) (z w : F) (Pz Pw : F[X])
    (hzw : z ≠ w) (hB : B ≠ 0)
    (hBdegree : B.natDegree = 22507)
    (hHdegree :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).natDegree ≤ 153578)
    (hfixed :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).map sigma =
        adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B) :
    (B ∣ Q1 ∧
        (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw = 0 ∨
          ∃ T : F[X], T ≠ 0 ∧
            adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw =
              polynomialFrobeniusNormSix sigma B * T ∧
            T.natDegree ≤ 18536)) ∨
      (¬ B ∣ Q1 ∧
        ¬ B ∣ adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw) := by
  by_cases hdiv : B ∣ Q1
  · left
    refine ⟨hdiv, ?_⟩
    let H := adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw
    by_cases hH : H = 0
    · exact Or.inl hH
    · right
      have hBdiv : B ∣ H :=
        (dvd_adjacentOrbitFixedSecant_iff_dvd_direction6401
          B Q1 z w Pz Pw hzw).2 hdiv
      exact benchmark_fixedOrbitResidual_degree_le_18536_6401
        sigma B H hB hH hBdegree hHdegree hfixed hBdiv horbit
  · right
    exact ⟨hdiv, fun hBdiv ↦ hdiv <|
      (dvd_adjacentOrbitFixedSecant_iff_dvd_direction6401
        B Q1 z w Pz Pw hzw).1 hBdiv⟩
theorem exists_adjacentOrbitFixedSecant_normResidual6401
    (sigma : F →+* F) (B Q1 : F[X]) (z w : F) (Pz Pw : F[X])
    (hzw : z ≠ w) (hB : B ≠ 0)
    (hBdegree : B.natDegree = 22507)
    (hHdegree :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).natDegree ≤ 153578)
    (hfixed :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).map sigma =
        adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B)
    (hdivQ : B ∣ Q1) :
    ∃ U : F[X],
      adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw =
        polynomialFrobeniusNormSix sigma B * U ∧
      U.natDegree ≤ 18536 := by
  let H := adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw
  by_cases hH : H = 0
  · refine ⟨0, ?_, by simp⟩
    simpa [H, hH]
  · have hdivH : B ∣ H :=
      (dvd_adjacentOrbitFixedSecant_iff_dvd_direction6401
        B Q1 z w Pz Pw hzw).2 hdivQ
    obtain ⟨U, _hU, hfactor, hdegree⟩ :=
      benchmark_fixedOrbitResidual_degree_le_18536_6401
        sigma B H hB hH hBdegree hHdegree hfixed hdivH horbit
    exact ⟨U, hfactor, hdegree⟩
theorem exists_adjacentOrbitClearedOwner_anchoredResidual6401
    (sigma : F →+* F) (B Q1 : F[X]) (z w : F) (Pz Pw : F[X])
    (hzw : z ≠ w) (hB : B ≠ 0)
    (hBdegree : B.natDegree = 22507)
    (hHdegree :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).natDegree ≤ 153578)
    (hfixed :
      (adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw).map sigma =
        adjacentOrbitFixedSecant6401 B Q1 z w Pz Pw)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B)
    (hdivQ : B ∣ Q1) :
    ∃ U : F[X],
      adjacentOrbitClearedOwner6401 B Q1 z Pz =
        adjacentOrbitClearedOwner6401 B Q1 w Pw +
          polynomialFrobeniusNormSix sigma B * U ∧
      U.natDegree ≤ 18536 := by
  obtain ⟨U, hfactor, hdegree⟩ :=
    exists_adjacentOrbitFixedSecant_normResidual6401
      sigma B Q1 z w Pz Pw hzw hB hBdegree hHdegree hfixed horbit hdivQ
  refine ⟨U, ?_, hdegree⟩
  have hsub := adjacentOrbitClearedOwner_sub6401 B Q1 z w Pz Pw
  rw [hfactor] at hsub
  linear_combination hsub
end NormFork
section ComposedSourceFork
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem exists_adjacentOrbitDirection_with_fixedSecantNormFork6401
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
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (T : Finset F) (hT : T ⊆ R.goodChallenges6401)
    (hTS : T ⊆ S)
    (hTG : ∀ z ∈ T, G.eval z ≠ 0)
    (hlarge : q6401 < T.card)
    (horbit : SuccessivelyCoprimeSixOrbit6401 sigma B) :
    ∃ Q1 : F[X],
      Q1.natDegree ≤ adjacentOrbitShortenedTargetDegree6401 ∧
      (∀ i : TwoRowGoodIndex6401 W,
        Q1.eval (twoRowGoodAlpha6401 W i) =
          adjacentOrbitShortenedReceivedDirection6401 W B i) ∧
      ∀ z ∈ T, ∀ w ∈ T, z ≠ w →
        let H := adjacentOrbitFixedSecant6401 B Q1 z w (Owner z) (Owner w)
        H.map sigma = H ∧
          ((B ∣ Q1 ∧
              (H = 0 ∨ ∃ U : F[X], U ≠ 0 ∧
                H = polynomialFrobeniusNormSix sigma B * U ∧
                U.natDegree ≤ 18536)) ∨
            (¬ B ∣ Q1 ∧ ¬ B ∣ H)) := by
  obtain ⟨Q1, hQdegree, hQeval⟩ :=
    exists_adjacentOrbitShortenedDirectionPolynomial6401
      W R G A B hG hA hB hcoprime hadjacent hzero hone hBdegree.le
        hOwnerDegree hsigma hfixed hfixedCard T hT hTS hTG hlarge
  refine ⟨Q1, hQdegree, hQeval, ?_⟩
  intro z hz w hw hzw
  dsimp only
  have hHfixed := recursiveAdjacentOrbit_fixedSecant_map_eq_self6401
    W R G A B Q1 hG hA hB hcoprime hadjacent hzero hone hBdegree.le
      hOwnerDegree hQdegree hQeval hsigma hfixed z w
        (hTS hz) (hTS hw) (hT hz) (hT hw) (hTG z hz) (hTG w hw)
  refine ⟨hHfixed, ?_⟩
  have hHdegree :
      (adjacentOrbitFixedSecant6401 B Q1 z w
        (Owner z) (Owner w)).natDegree ≤ 153578 := by
    have hbound := adjacentOrbitFixedSecant_natDegree_le6401
      B Q1 z w (Owner z) (Owner w)
        adjacentOrbitShortenedTargetDegree6401 hBdegree.le hQdegree
        (hOwnerDegree z (hTS hz)) (hOwnerDegree w (hTS hw)) le_rfl
    simpa [adjacentOrbitShortenedTargetDegree6401,
      homogeneousDirectionCap6401, ownerDegreeCap6401] using hbound
  have hB22507 : B.natDegree = 22507 := by
    simpa [homogeneousDirectionCap6401] using hBdegree
  exact adjacentOrbitFixedSecant_normResidual_or_obstruction6401
    sigma B Q1 z w (Owner z) (Owner w) hzw hB hB22507 hHdegree
      hHfixed horbit
end ComposedSourceFork
end BCHKSExtremePrimitiveAdjacentOrbitFixedSecant6401
end ProximityPrize.SubmissionLower
