import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusFullRankOneClassification6401
import ProximityPrize.SubmissionLower.BCHKSSphericalL3Radius76855Audit6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusWeakCurveSeed6401
open Polynomial
open ProximityPrize.Benchmark
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoLedger6401
open BCHKSTwoFrobeniusPrimitiveFrame6401
open BCHKSTwoFrobeniusTripleLight6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusFullRankOne6401
open BCHKSTwoFrobeniusFullRankOneClassification6401
open BCHKSSphericalL3Radius76855Audit6401
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
def weakCurveSeedInput6401 : Nat :=
  BCHKSFinalConditional6401.mcaNumerator6401 + 1 -
    n6401 * wideListBound
def weakCurveSeedCap6401 : Nat := weakCurveSeedInput6401 - 1
def weakCurveOutput6401 : Nat := targetSeedOutput
theorem weakCurveSeed_exactParameters6401 :
    weakCurveSeedInput6401 = 273591199342811068 /\
      weakCurveSeedCap6401 = 273591199342811067 /\
      weakCurveOutput6401 = 1183 /\
      n6401 * wideListBound + weakCurveSeedInput6401 =
        BCHKSFinalConditional6401.mcaNumerator6401 + 1 := by
  norm_num [weakCurveSeedInput6401, weakCurveSeedCap6401,
    weakCurveOutput6401, targetSeedOutput, n6401, wideListBound,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401]
def AffineLineCurveSeedBound
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (errors input output : Nat) : Prop :=
  ∀ (U : Fin 2 → ι → F) (f : F → ι → F),
    (∀ z, f z ∈ C) →
    input ≤ (Finset.univ.filter fun z =>
      hammingDist (fun i => U 0 i + z * U 1 i) (f z) ≤ errors).card →
    ∃ c : Fin 2 → ι → F,
      (∀ j, c j ∈ C) ∧
      output ≤ (Finset.univ.filter fun z =>
        hammingDist (fun i => U 0 i + z * U 1 i) (f z) ≤ errors ∧
          f z = fun i => c 0 i + z * c 1 i).card
def WeakAffineLineCurveSeed6401 : Prop :=
  AffineLineCurveSeedBound IRSProfile.baseCode bchksErrors6401
    weakCurveSeedInput6401 weakCurveOutput6401
def PolynomialAffineCurveWitness6401
    {F : Type*} [Field F]
    (S : Finset F) (P : F -> Polynomial F) : Prop :=
  exists p0 p1 : Polynomial F,
    p0.natDegree <= ownerDegreeCap6401 /\
      p1.natDegree <= ownerDegreeCap6401 /\
      exists T : Finset F, T ⊆ S /\
        weakCurveOutput6401 <= T.card /\
        forall z, z ∈ T -> P z = p0 + Polynomial.C z * p1
def PolynomialOwnerWeakCurveSeed6401
    {F : Type} [Field F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F) : Prop :=
  ∀ (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F),
    weakCurveSeedInput6401 ≤ S.card →
    (∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401) →
    (∀ z ∈ S, a6401 ≤ (A z).card) →
    (∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) →
    PolynomialAffineCurveWitness6401 S P
theorem affineLineCurveSeedBound_of_polynomialOwner6401
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (alpha : Fin n6401 ↪ F)
    (hpoly : PolynomialOwnerWeakCurveSeed6401 alpha) :
    AffineLineCurveSeedBound
      (ReedSolomon.code alpha (ownerDegreeCap6401 + 1))
      bchksErrors6401 weakCurveSeedInput6401 weakCurveOutput6401 := by
  classical
  intro U f hf hclose
  let S : Finset F := Finset.univ.filter fun z =>
    hammingDist (fun i => U 0 i + z * U 1 i) (f z) ≤ bchksErrors6401
  have hSlarge : weakCurveSeedInput6401 ≤ S.card := by
    simpa [S] using hclose
  have hw : ∀ z : F, ∃ p : Polynomial F,
      p.natDegree ≤ ownerDegreeCap6401 ∧
        f z = ReedSolomon.evalOnPoints alpha p := by
    intro z
    have hzcode := hf z
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hzcode
    obtain ⟨p, hpdeg, hp⟩ := hzcode
    refine ⟨p, ?_, hp⟩
    by_cases hp0 : p = 0
    · simp [hp0]
    · have hnat : p.natDegree < ownerDegreeCap6401 + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
      omega
  let P : F → Polynomial F := fun z => Classical.choose (hw z)
  have hPdegree : ∀ z : F,
      (P z).natDegree ≤ ownerDegreeCap6401 :=
    fun z => (Classical.choose_spec (hw z)).1
  have hfP : ∀ z : F,
      f z = ReedSolomon.evalOnPoints alpha (P z) :=
    fun z => (Classical.choose_spec (hw z)).2
  let A : F → Finset (Fin n6401) := fun z =>
    Finset.univ.filter fun i =>
      U 0 i + z * U 1 i = Polynomial.eval (alpha i) (P z)
  have hrow : ∀ z ∈ S, a6401 ≤ (A z).card := by
    intro z hz
    have hdist :
        hammingDist (fun i => U 0 i + z * U 1 i) (f z) ≤
          bchksErrors6401 := (Finset.mem_filter.mp hz).2
    have hsum := Code.agree_add_hammingDist
      (u := fun i => U 0 i + z * U 1 i) (v := f z)
    have hAeq : (A z).card =
        Code.agree (fun i => U 0 i + z * U 1 i) (f z) := by
      unfold Code.agree
      apply congrArg Finset.card
      ext i
      simp [A, hfP z, ReedSolomon.evalOnPoints]
    rw [← hAeq] at hsum
    norm_num [n6401, a6401, bchksErrors6401] at hdist hsum ⊢
    omega
  have howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = U 0 i + z * U 1 i := by
    intro z hz i hi
    exact (Finset.mem_filter.mp hi).2.symm
  obtain ⟨p0, p1, hp0, hp1, T, hTS, hTcard, hline⟩ :=
    hpoly (U 0) (U 1) S A P hSlarge
      (fun z _ => hPdegree z) hrow howner
  let c : Fin 2 → Fin n6401 → F := ![
    ReedSolomon.evalOnPoints alpha p0,
    ReedSolomon.evalOnPoints alpha p1]
  refine ⟨c, ?_, ?_⟩
  · intro j
    fin_cases j
    · apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p0
      · omega
      · intro i
        rfl
    · apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p1
      · omega
      · intro i
        rfl
  · exact hTcard.trans <| Finset.card_le_card <| by
      intro z hzT
      have hzS := hTS hzT
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z, (Finset.mem_filter.mp hzS).2, ?_⟩
      funext i
      have hpolyline := congrArg (Polynomial.eval (alpha i)) (hline z hzT)
      rw [hfP z]
      simpa [c, ReedSolomon.evalOnPoints] using hpolyline
theorem weakAffineLineCurveSeed6401_of_polynomialOwner
    (hpoly : PolynomialOwnerWeakCurveSeed6401 IRSProfile.domain) :
    WeakAffineLineCurveSeed6401 :=
  affineLineCurveSeedBound_of_polynomialOwner6401 IRSProfile.domain hpoly
theorem affineFamily_card_le_1182_of_no_curveWitness6401
    {F : Type*} [Field F]
    (S T : Finset F) (P : F -> Polynomial F)
    (p0 p1 : Polynomial F)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P)
    (hp0 : p0.natDegree <= ownerDegreeCap6401)
    (hp1 : p1.natDegree <= ownerDegreeCap6401)
    (hTS : T ⊆ S)
    (halign : forall z, z ∈ T ->
      P z = p0 + Polynomial.C z * p1) :
    T.card <= 1182 := by
  by_contra hnot
  have hout : weakCurveOutput6401 <= T.card := by
    norm_num [weakCurveOutput6401, targetSeedOutput] at hnot ⊢
    omega
  exact hfail ⟨p0, p1, hp0, hp1, T, hTS, hout, halign⟩
theorem weakCurve_rankCaps_fit6401 :
    rankThreeDetZCap6401 < weakCurveSeedCap6401 /\
      rankTwoIncidenceOwnerCap6401 < weakCurveSeedCap6401 /\
      tripleLightTotalCap6401 < weakCurveSeedCap6401 := by
  norm_num [weakCurveSeedInput6401, weakCurveSeedCap6401,
    BCHKSFinalConditional6401.mcaNumerator6401,
    BCHKSList6401.maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    BCHKSList6401.listBound6401, n6401, wideListBound,
    rankThreeDetZCap6401, rankTwoIncidenceOwnerCap6401,
    rankTwoMismatchZCap6401, tripleLightTotalCap6401,
    tripleLightHeavyCap6401, tripleLightLineCap6401,
    tripleLightThreshold6401, rankTwoDenomZCap6401,
    balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
    a1XSlots6401, q6401]
theorem lightChallenges_card_le_lineCap_of_no_curveWitness6401
    {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (u0 u1 : ι → F)
    (I : Finset ι) (S : Finset F) (P : F → Polynomial F)
    (p0 p1 : Polynomial F)
    (hp0 : p0.natDegree ≤ ownerDegreeCap6401)
    (hp1 : p1.natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P)
    (halign : ∀ z ∈ lightChallenges D alpha
      (rationalIdentityCoordinates D N alpha u0 u1 I) S
        tripleLightThreshold6401,
      P z = p0 + Polynomial.C z * p1) :
    (lightChallenges D alpha
      (rationalIdentityCoordinates D N alpha u0 u1 I) S
        tripleLightThreshold6401).card ≤ tripleLightLineCap6401 := by
  let L := lightChallenges D alpha
    (rationalIdentityCoordinates D N alpha u0 u1 I) S
      tripleLightThreshold6401
  have hLS : L ⊆ S := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have h1182 : L.card ≤ 1182 :=
    affineFamily_card_le_1182_of_no_curveWitness6401
      S L P p0 p1 hfail hp0 hp1 hLS (by simpa [L] using halign)
  exact h1182.trans (by norm_num [tripleLightLineCap6401])
theorem coefficientRows_owner_card_le_weakSeedCap_or_curve6401
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F]
    (sigma : F →+* F)
    (c d : SymbolicCoefficients F) (alpha : ι ↪ F)
    (u0 u1 : ι → F)
    (S : Finset F) (A : F → Finset ι) (P : F → Polynomial F)
    (hcardι : Fintype.card ι = n6401)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c) (coefficientRowMap d) ≠ 0)
    (hPdegree : ∀ z ∈ S,
      (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hc : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap c))
        (P z) = 0)
    (hd : ∀ z ∈ S,
      symbolicRelation sigma (specializeRow z (coefficientRowMap d))
        (P z) = 0)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    S.card ≤ weakCurveSeedCap6401 ∨
      PolynomialAffineCurveWitness6401 S P := by
  classical
  by_cases hcurve : PolynomialAffineCurveWitness6401 S P
  · exact Or.inr hcurve
  · left
    let D := symbolicRankTwoDenominator
      (coefficientRowMap c) (coefficientRowMap d)
    let N := symbolicRankTwoNumerator
      (coefficientRowMap c) (coefficientRowMap d)
    let R := primitiveRationalFrame D N alpha Finset.univ
      (by simpa [D] using hden)
    have hDswap : (Polynomial.Bivariate.swap D).natDegree ≤
        rankTwoDenomZCap6401 := by
      simpa [D] using swap_coefficientRowMap_denominator_natDegree_le c d
    have hNswap : (Polynomial.Bivariate.swap N).natDegree ≤
        rankTwoMismatchZCap6401 := by
      simpa [N] using swap_coefficientRowMap_numerator_natDegree_le c d
    have hbranch : ∀ z ∈ S,
        specializeCoeffZ z R.denominator * P z =
          -specializeCoeffZ z R.numerator := by
      intro z hz
      apply R.cancel_specialized_owner z (P z)
      exact specialized_rankTwo_owner_identity sigma z
        (coefficientRowMap c) (coefficientRowMap d) (P z)
          (hc z hz) (hd z hz)
    have hmismatchDegree : ∀ i : ι,
        (rationalCoordinateMismatch R.denominator R.numerator
          (alpha i) (u0 i) (u1 i)).natDegree ≤
            rankTwoMismatchZCap6401 := by
      intro i
      have h := R.rationalCoordinateMismatch_natDegree_le
        (alpha i) (u0 i) (u1 i)
          rankTwoDenomZCap6401 rankTwoMismatchZCap6401 hDswap hNswap
      simpa [rankTwoDenomZCap6401, rankTwoMismatchZCap6401,
        balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
        a1XSlots6401, q6401] using h
    by_cases hsmall :
        (rationalIdentityCoordinates R.denominator R.numerator
          alpha u0 u1 Finset.univ).card ≤
            rankTwoIdentityIncidenceCutoff6401
    · have hcap := rational_owner_card_le_rankTwoIncidenceOwnerCap6401
        R.denominator R.numerator alpha u0 u1 S A P hcardι hsmall
          hrow hbranch howner hmismatchDegree
      exact hcap.trans (Nat.le_of_lt weakCurve_rankCaps_fit6401.2.1)
    · have hlarge : 185295 ≤
          (rationalIdentityCoordinates R.denominator R.numerator
            alpha u0 u1 Finset.univ).card := by
        norm_num [rankTwoIdentityIncidenceCutoff6401] at hsmall ⊢
        omega
      have hactive : ∀ i ∈
          rationalIdentityCoordinates R.denominator R.numerator
            alpha u0 u1 Finset.univ,
          evalOuterAt (alpha i) R.denominator ≠ 0 := by
        intro i hi hDzero
        have hmismatch : rationalCoordinateMismatch R.denominator R.numerator
            (alpha i) (u0 i) (u1 i) = 0 := by
          simpa [rationalIdentityCoordinates] using hi
        unfold rationalCoordinateMismatch at hmismatch
        rw [hDzero, zero_mul, zero_add] at hmismatch
        exact R.primitive_at_coordinates i (Finset.mem_univ i)
          ⟨hDzero, hmismatch⟩
      have hlargeCap := ownerFamily_card_le_tripleLightTotalCap6401
        R.denominator R.numerator alpha u0 u1 Finset.univ S P
        (by rw [hcardι]) hlarge hactive
        (by
          intro i hi
          exact R.evalOuterAt_denominator_natDegree_le
            (alpha i) rankTwoDenomZCap6401 hDswap)
        hPdegree hbranch
        (by
          intro p0 p1 hp0 hp1 halign
          exact lightChallenges_card_le_lineCap_of_no_curveWitness6401
            R.denominator R.numerator alpha u0 u1 Finset.univ S P
              p0 p1 hp0 hp1 hcurve halign)
      exact hlargeCap.trans
        (Nat.le_of_lt weakCurve_rankCaps_fit6401.2.2)
def FullRankOneWeakCurveSeedResidual6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (P : F → Polynomial F) : Prop :=
  FullSymbolicKernelRankOneResidual6401 sigma alpha u0 u1 ∧
    weakCurveSeedInput6401 ≤ S.card ∧
    ¬ PolynomialAffineCurveWitness6401 S P
theorem symbolicKernel_owner_card_le_weakSeedCap_or_curve_or_fullRankOne6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S,
      (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    S.card ≤ weakCurveSeedCap6401 ∨
      PolynomialAffineCurveWitness6401 S P ∨
      FullSymbolicKernelRankOneResidual6401 sigma alpha u0 u1 := by
  classical
  obtain ⟨q, hqIndependent⟩ :=
    exists_three_independent_symbolicKernel_coefficients sigma alpha u0 u1
  by_cases hdet : symbolicDeterminant
      (fun i => coefficientRowMap (q i).1) ≠ 0
  · left
    have hcard := kernelTriple_owner_card_le_rankThreeDetZCap6401
      sigma alpha u0 u1 hsigma hfixed q S A P hdet
        hPdegree hrow howner
    exact hcard.trans (Nat.le_of_lt weakCurve_rankCaps_fit6401.1)
  · by_cases hpair : ∃ c d : SymbolicKernel sigma alpha u0 u1,
        symbolicRankTwoDenominator
          (coefficientRowMap c.1) (coefficientRowMap d.1) ≠ 0
    · obtain ⟨c, d, hden⟩ := hpair
      rcases coefficientRows_owner_card_le_weakSeedCap_or_curve6401
          sigma c.1 d.1 alpha u0 u1 S A P (Fintype.card_fin _)
            hden hPdegree hrow
            (by
              intro z hz
              exact kernel_symbolicRelation_eq_zero_of_owner
                sigma alpha u0 u1 hsigma hfixed c z (A z) (P z)
                  (hPdegree z hz) (howner z hz) (hrow z hz))
            (by
              intro z hz
              exact kernel_symbolicRelation_eq_zero_of_owner
                sigma alpha u0 u1 hsigma hfixed d z (A z) (P z)
                  (hPdegree z hz) (howner z hz) (hrow z hz))
            howner with hcap | hcurve
      · exact Or.inl hcap
      · exact Or.inr (Or.inl hcurve)
    · right
      right
      have hprojected :
          SymbolicA1A2RankOneResidual6401 sigma alpha u0 u1 := by
        intro c d
        exact not_ne_iff.mp (fun hne => hpair ⟨c, d, hne⟩)
      exact A1A2RankOneResidual_implies_fullSymbolicRankOne6401
        sigma alpha alpha.injective u0 u1 hprojected
theorem symbolicKernel_weakSeed_or_exact_fullRankOneResidual6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hPdegree : ∀ z ∈ S,
      (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    S.card ≤ weakCurveSeedCap6401 ∨
      PolynomialAffineCurveWitness6401 S P ∨
      FullRankOneWeakCurveSeedResidual6401 sigma alpha u0 u1 S P := by
  rcases symbolicKernel_owner_card_le_weakSeedCap_or_curve_or_fullRankOne6401
      sigma alpha u0 u1 hsigma hfixed S A P hPdegree hrow howner with
    hcap | hcurve | hfull
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hcurve)
  · by_cases hlarge : weakCurveSeedInput6401 ≤ S.card
    · by_cases hcurve : PolynomialAffineCurveWitness6401 S P
      · exact Or.inr (Or.inl hcurve)
      · exact Or.inr (Or.inr ⟨hfull, hlarge, hcurve⟩)
    · left
      have hlt : S.card < weakCurveSeedInput6401 := Nat.lt_of_not_ge hlarge
      have hcapEq : weakCurveSeedCap6401 + 1 = weakCurveSeedInput6401 := by
        norm_num [weakCurveSeedCap6401, weakCurveSeedInput6401,
          BCHKSFinalConditional6401.mcaNumerator6401,
          BCHKSList6401.maxMCANumeratorAfterList6401,
          BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
          BCHKSList6401.listBound6401, n6401, wideListBound]
      omega
def FullRankOneWeakCurveSeedClosure6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F) : Prop :=
  ∀ (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F),
    (∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401) →
    (∀ z ∈ S, a6401 ≤ (A z).card) →
    (∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) →
    FullSymbolicKernelRankOneResidual6401 sigma alpha u0 u1 →
    weakCurveSeedInput6401 ≤ S.card →
    PolynomialAffineCurveWitness6401 S P
theorem polynomialOwnerWeakCurveSeed_of_fullRankOneClosure6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hclosure : FullRankOneWeakCurveSeedClosure6401 sigma alpha) :
    PolynomialOwnerWeakCurveSeed6401 alpha := by
  intro u0 u1 S A P hlarge hPdegree hrow howner
  rcases symbolicKernel_owner_card_le_weakSeedCap_or_curve_or_fullRankOne6401
      sigma alpha u0 u1 hsigma hfixed S A P hPdegree hrow howner with
    hcap | hcurve | hfull
  · have hcapEq : weakCurveSeedCap6401 + 1 = weakCurveSeedInput6401 := by
      norm_num [weakCurveSeedCap6401, weakCurveSeedInput6401,
        BCHKSFinalConditional6401.mcaNumerator6401,
        BCHKSList6401.maxMCANumeratorAfterList6401,
        BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
        BCHKSList6401.listBound6401, n6401, wideListBound]
    omega
  · exact hcurve
  · exact hclosure u0 u1 S A P hPdegree hrow howner hfull hlarge
end BCHKSTwoFrobeniusWeakCurveSeed6401
end ProximityPrize.SubmissionLower
