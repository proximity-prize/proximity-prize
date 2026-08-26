import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAllSeedsGcdSupport6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveLaneResultantFork6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTwoAxisMultiplicity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAllSeedsResultantMultiplicity6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
open BCHKSExtremePrimitiveLaneResultantFork6401
open BCHKSExtremePrimitiveTwoAxisMultiplicity6401
open BCHKSFrobeniusResultantMultiplicity6401
open BCHKSExtremePrimitiveAllSeedsGcdSupport6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
noncomputable def fullyPaddedCommonFactorSyzygyMap6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    Polynomial.degreeLT F d.natDegree →ₗ[F]
      Polynomial.degreeLT F m × Polynomial.degreeLT F n where
  toFun T :=
    ⟨⟨T.1 * a, by
        rw [Polynomial.mem_degreeLT]
        by_cases hT : T.1 = 0
        · simp [hT]
        · apply (Polynomial.natDegree_lt_iff_degree_lt
            (mul_ne_zero hT ha)).1
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hT).2 hTmem
          apply lt_of_lt_of_le _ hfm
          rw [hfa, Polynomial.natDegree_mul hd ha,
            Polynomial.natDegree_mul hT ha]
          omega⟩,
      ⟨-(T.1 * b), by
        rw [Polynomial.mem_degreeLT]
        by_cases hTb : T.1 * b = 0
        · simp [hTb]
        · rw [Polynomial.degree_neg]
          apply (Polynomial.natDegree_lt_iff_degree_lt hTb).1
          have hTne : T.1 ≠ 0 := fun hzero ↦ hTb (by simp [hzero])
          have hb : b ≠ 0 := fun hzero ↦ hTb (by simp [hzero])
          have hTmem := T.2
          rw [Polynomial.mem_degreeLT] at hTmem
          have hTdegree : T.1.natDegree < d.natDegree :=
            (Polynomial.natDegree_lt_iff_degree_lt hTne).2 hTmem
          apply lt_of_lt_of_le _ hgn
          rw [hgb, Polynomial.natDegree_mul hd hb,
            Polynomial.natDegree_mul hTne hb]
          omega⟩⟩
  map_add' T U := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  map_smul' c T := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> simp
theorem fullyPaddedCommonFactorSyzygyMap_injective6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    Function.Injective
      (fullyPaddedCommonFactorSyzygyMap6401
        f g d a b m n hd ha hfa hgb hfm hgn) := by
  intro T U hTU
  apply Subtype.ext
  have hfirst := congrArg (fun p ↦ p.1.1) hTU
  dsimp [fullyPaddedCommonFactorSyzygyMap6401] at hfirst
  exact mul_right_cancel₀ ha hfirst
theorem fullyPaddedCommonFactorSyzygyMap_mem_kernel6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n)
    (T : Polynomial.degreeLT F d.natDegree) :
    Polynomial.sylvesterMap f g hfm hgn
      (fullyPaddedCommonFactorSyzygyMap6401
        f g d a b m n hd ha hfa hgb hfm hgn T) = 0 := by
  apply Subtype.ext
  dsimp [Polynomial.sylvesterMap, fullyPaddedCommonFactorSyzygyMap6401]
  rw [hfa, hgb]
  ring
theorem fullyPaddedSylvester_rank_le_add_sub_commonFactorDegree6401
    {F : Type*} [Field F]
    (f g d a b : F[X]) (m n : Nat)
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hfa : f = d * a) (hgb : g = d * b)
    (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) :
    (Polynomial.sylvester f g m n).rank ≤ m + n - d.natDegree := by
  let L := fullyPaddedCommonFactorSyzygyMap6401
    f g d a b m n hd ha hfa hgb hfm hgn
  let S := Polynomial.sylvesterMap f g hfm hgn
  let LK : Polynomial.degreeLT F d.natDegree →ₗ[F]
      LinearMap.ker S := {
    toFun T := ⟨L T, by
      rw [LinearMap.mem_ker]
      exact fullyPaddedCommonFactorSyzygyMap_mem_kernel6401
        f g d a b m n hd ha hfa hgb hfm hgn T⟩
    map_add' T U := by
      apply Subtype.ext
      exact L.map_add T U
    map_smul' c T := by
      apply Subtype.ext
      exact L.map_smul c T
    }
  have hLKinj : Function.Injective LK := by
    intro T U hTU
    apply fullyPaddedCommonFactorSyzygyMap_injective6401
      f g d a b m n hd ha hfa hgb hfm hgn
    exact congrArg Subtype.val hTU
  have hsource : Module.finrank F
      (Polynomial.degreeLT F d.natDegree) = d.natDegree := by
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis F d.natDegree)]
    simp
  have hker : d.natDegree ≤ Module.finrank F (LinearMap.ker S) := by
    rw [← hsource]
    exact LinearMap.finrank_le_finrank_of_injective hLKinj
  have hdomain : Module.finrank F
      (Polynomial.degreeLT F m × Polynomial.degreeLT F n) = m + n := by
    rw [Module.finrank_prod,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F m),
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F n)]
    simp
  have hranknull := LinearMap.finrank_range_add_finrank_ker S
  have hrange : Module.finrank F (LinearMap.range S) ≤
      m + n - d.natDegree := by
    rw [hdomain] at hranknull
    omega
  let bin :=
    ((Polynomial.degreeLT.basis F m).prod
      (Polynomial.degreeLT.basis F n)).reindex finSumFinEquiv
  let bout := Polynomial.degreeLT.basis F (m + n)
  have hmatrix : Matrix.toLin bin bout
      (Polynomial.sylvester f g m n) = S := by
    rw [← Polynomial.toMatrix_sylvesterMap' f g hfm hgn]
    exact Matrix.toLin_toMatrix _ _ _
  rw [Matrix.rank_eq_finrank_range_toLin
    (Polynomial.sylvester f g m n) bout bin, hmatrix]
  exact hrange
theorem X_sub_C_pow_commonFactorDegree_dvd_resultant_fullyPadded6401
    {F : Type*} [Field F]
    (B Q : F[X][X]) (m n : Nat) (z : F)
    (d a b : F[X])
    (hd : d ≠ 0) (ha : a ≠ 0)
    (hBfactor : B.map (Polynomial.evalRingHom z) = d * a)
    (hQfactor : Q.map (Polynomial.evalRingHom z) = d * b)
    (hBdegree : (B.map (Polynomial.evalRingHom z)).natDegree ≤ m)
    (hQdegree : (Q.map (Polynomial.evalRingHom z)).natDegree ≤ n) :
    (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      Polynomial.resultant B Q m n := by
  let f := B.map (Polynomial.evalRingHom z)
  let g := Q.map (Polynomial.evalRingHom z)
  have hfdegree : f.natDegree ≤ m := by simpa [f] using hBdegree
  have hgdegree : g.natDegree ≤ n := by simpa [g] using hQdegree
  have hrank : (Polynomial.sylvester f g m n).rank ≤
      m + n - d.natDegree :=
    fullyPaddedSylvester_rank_le_add_sub_commonFactorDegree6401
      f g d a b m n hd ha hBfactor hQfactor hfdegree hgdegree
  have hdle : d.natDegree ≤ m := by
    have hffactor : f = d * a := by simpa [f] using hBfactor
    calc
      d.natDegree ≤ f.natDegree := by
        rw [hffactor, Polynomial.natDegree_mul hd ha]
        omega
      _ ≤ m := hfdegree
  let M := Polynomial.sylvester B Q m n
  have hmap : M.map (Polynomial.evalRingHom z) =
      Polynomial.sylvester f g m n := by
    simpa [M, f, g] using
      (Polynomial.sylvester_map_map B Q m n
        (Polynomial.evalRingHom z)).symm
  have hcorank : d.natDegree ≤
      Fintype.card (Fin (m + n)) -
        (M.map (Polynomial.evalRingHom z)).rank := by
    rw [hmap]
    simp only [Fintype.card_fin]
    omega
  have hdet := X_sub_C_pow_corank_dvd_det6401 M z
  have hsmall : (Polynomial.X - Polynomial.C z) ^ d.natDegree ∣
      (Polynomial.X - Polynomial.C z) ^
        (Fintype.card (Fin (m + n)) -
          (M.map (Polynomial.evalRingHom z)).rank) :=
    pow_dvd_pow _ hcorank
  exact hsmall.trans (by simpa [M, Polynomial.resultant] using hdet)
theorem errorSupportPower_dvd_primitiveLaneResultant_of_allGraphSeedsZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (hlane : primitiveFailureLaneZero6401 W z ≠ 0 ∨
      primitiveFailureLaneOne6401 W z ≠ 0) :
    (Polynomial.X - Polynomial.C z) ^
        (puncturedErrorSupport6401 W z).card ∣
      primitiveLaneResultant6401 W := by
  classical
  let L0 := primitiveBivariateFailureLaneZero6401 W
  let L1 := primitiveBivariateFailureLaneOne6401 W
  let f := L0.map (Polynomial.evalRingHom z)
  let g := L1.map (Polynomial.evalRingHom z)
  let d := EuclideanDomain.gcd f g
  have hf : f = primitiveFailureLaneZero6401 W z := by
    exact primitiveBivariateFailureLaneZero_specialize6401 W z
  have hg : g = primitiveFailureLaneOne6401 W z := by
    exact primitiveBivariateFailureLaneOne_specialize6401 W z
  have hd : d ≠ 0 := by
    intro hzero
    have hboth := EuclideanDomain.gcd_eq_zero_iff.mp hzero
    exact hlane.elim (fun h ↦ h (hf ▸ hboth.1))
      (fun h ↦ h (hg ▸ hboth.2))
  obtain ⟨a, haFactor⟩ := EuclideanDomain.gcd_dvd_left f g
  obtain ⟨b, hbFactor⟩ := EuclideanDomain.gcd_dvd_right f g
  have hsupport : (puncturedErrorSupport6401 W z).card ≤ d.natDegree := by
    have hraw :=
      (puncturedErrorSupport_card_le_laneGcdDegree_le_22507_of_allGraphSeedsZero6401
        W hsigma hfixed hsix hall z hz hlane).1
    simpa [primitiveFailureLaneGcd6401, d, f, g, hf, hg] using hraw
  have hsmall : (Polynomial.X - Polynomial.C z) ^
      (puncturedErrorSupport6401 W z).card ∣
        (Polynomial.X - Polynomial.C z) ^ d.natDegree :=
    pow_dvd_pow _ hsupport
  rcases hlane with h0 | h1
  · have hfne : f ≠ 0 := by simpa [hf] using h0
    have hane : a ≠ 0 := by
      intro hzero
      apply hfne
      rw [haFactor, hzero, mul_zero]
    have hraw :=
      X_sub_C_pow_commonFactorDegree_dvd_resultant_fullyPadded6401
        L0 L1 L0.natDegree L1.natDegree z d a b hd hane
        haFactor hbFactor Polynomial.natDegree_map_le
        Polynomial.natDegree_map_le
    exact hsmall.trans (by
      simpa [primitiveLaneResultant6401, L0, L1] using hraw)
  · have hgne : g ≠ 0 := by simpa [hg] using h1
    have hbne : b ≠ 0 := by
      intro hzero
      apply hgne
      rw [hbFactor, hzero, mul_zero]
    have hraw :=
      X_sub_C_pow_commonFactorDegree_dvd_resultant_fullyPadded6401
        L1 L0 L1.natDegree L0.natDegree z d b a hd hbne
        hbFactor haFactor Polynomial.natDegree_map_le
        Polynomial.natDegree_map_le
    apply hsmall.trans
    rw [primitiveLaneResultant6401, Polynomial.resultant_comm]
    exact dvd_mul_of_dvd_right (by simpa [L0, L1] using hraw) _
noncomputable def bothPrimitiveLanesZeroOwners6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset P)
    (T : Finset F) : Finset F :=
  T.filter fun z ↦
    primitiveFailureLaneZero6401 W z = 0 ∧
      primitiveFailureLaneOne6401 W z = 0
theorem bothPrimitiveLanesZeroOwners_card_le_47957940448246_6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {Aset : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset P)
    (T : Finset F) :
    (bothPrimitiveLanesZeroOwners6401 W T).card ≤ 47957940448246 := by
  classical
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · have hLaneNe : primitiveBivariateFailureLaneOne6401 W ≠ 0 := by
      rw [primitiveBivariateFailureLaneOne6401]
      exact neg_ne_zero.mpr (hpivot ▸ W.sourcePuncture.frame.pivot_ne_zero)
    obtain ⟨a, _ha, hcard⟩ := card_zero_specializations_le_coefficient_degree
      T (primitiveBivariateFailureLaneOne6401 W) hLaneNe
    have hsub : bothPrimitiveLanesZeroOwners6401 W T ⊆
        T.filter fun z ↦
          specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W) = 0 := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨hz'.1, ?_⟩
      rw [primitiveBivariateFailureLaneOne_specialize6401 W z]
      exact hz'.2.2
    calc
      (bothPrimitiveLanesZeroOwners6401 W T).card ≤
          (T.filter fun z ↦
            specializeCoeffZ z
              (primitiveBivariateFailureLaneOne6401 W) = 0).card :=
        Finset.card_le_card hsub
      _ ≤ ((primitiveBivariateFailureLaneOne6401 W).coeff a).natDegree :=
        hcard
      _ ≤ primitiveLaneOneChallengeCap6401 :=
        (primitiveBivariateFailureLanes_coeffDegreeLE6401 W).2 a
      _ ≤ 47957940448246 := by native_decide
  · have hLaneNe : primitiveBivariateFailureLaneZero6401 W ≠ 0 := by
      rw [primitiveBivariateFailureLaneZero6401]
      exact hpivot ▸ W.sourcePuncture.frame.pivot_ne_zero
    obtain ⟨a, _ha, hcard⟩ := card_zero_specializations_le_coefficient_degree
      T (primitiveBivariateFailureLaneZero6401 W) hLaneNe
    have hsub : bothPrimitiveLanesZeroOwners6401 W T ⊆
        T.filter fun z ↦
          specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W) = 0 := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨hz'.1, ?_⟩
      rw [primitiveBivariateFailureLaneZero_specialize6401 W z]
      exact hz'.2.1
    calc
      (bothPrimitiveLanesZeroOwners6401 W T).card ≤
          (T.filter fun z ↦
            specializeCoeffZ z
              (primitiveBivariateFailureLaneZero6401 W) = 0).card :=
        Finset.card_le_card hsub
      _ ≤ ((primitiveBivariateFailureLaneZero6401 W).coeff a).natDegree :=
        hcard
      _ ≤ primitiveLaneZeroChallengeCap6401 :=
        (primitiveBivariateFailureLanes_coeffDegreeLE6401 W).1 a
      _ ≤ 47957940448246 := by native_decide
end BCHKSExtremePrimitiveAllSeedsResultantMultiplicity6401
end ProximityPrize.SubmissionLower
