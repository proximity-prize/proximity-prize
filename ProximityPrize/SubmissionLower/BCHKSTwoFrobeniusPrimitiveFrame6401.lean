import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankTwoLedger6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusPrimitiveFrame6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
noncomputable def commonCoordinateMultiplicity
    {F : Type*} [Field F] (D N : XOverZ F) (a : F) : ℕ := by
  classical
  exact if N = 0 then D.rootMultiplicity (Polynomial.C a)
    else min (D.rootMultiplicity (Polynomial.C a))
      (N.rootMultiplicity (Polynomial.C a))
theorem commonCoordinateMultiplicity_le_denominator
    {F : Type*} [Field F] (D N : XOverZ F) (a : F) :
    commonCoordinateMultiplicity D N a ≤
      D.rootMultiplicity (Polynomial.C a) := by
  unfold commonCoordinateMultiplicity
  split_ifs <;> simp
theorem commonCoordinateMultiplicity_le_numerator
    {F : Type*} [Field F] (D N : XOverZ F) (a : F)
    (hN : N ≠ 0) :
    commonCoordinateMultiplicity D N a ≤
      N.rootMultiplicity (Polynomial.C a) := by
  simp [commonCoordinateMultiplicity, hN]
noncomputable def primitiveCoordinateFactor
    {F ι : Type*} [Field F]
    (D N : XOverZ F) (alpha : ι → F) (I : Finset ι) : XOverZ F :=
  ∏ i ∈ I, (Polynomial.X - Polynomial.C (Polynomial.C (alpha i))) ^
    commonCoordinateMultiplicity D N (alpha i)
theorem primitiveCoordinateFactor_monic
    {F ι : Type*} [Field F]
    (D N : XOverZ F) (alpha : ι → F) (I : Finset ι) :
    (primitiveCoordinateFactor D N alpha I).Monic := by
  classical
  unfold primitiveCoordinateFactor
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _
private theorem powered_coordinate_factors_pairwise_coprime
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (I : Finset ι) :
    (↑I : Set ι).Pairwise (Function.onFun IsCoprime fun i =>
      (Polynomial.X - Polynomial.C (Polynomial.C (alpha i))) ^
        commonCoordinateMultiplicity D N (alpha i)) := by
  intro i hi j hj hij
  have hne : alpha i ≠ alpha j := fun h => hij (alpha.injective h)
  have hunit : IsUnit
      ((Polynomial.C (alpha i) : Polynomial F) -
        Polynomial.C (alpha j)) := by
    rw [← Polynomial.C_sub]
    exact Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hne).isUnit
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit).pow
theorem primitiveCoordinateFactor_dvd_denominator
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (I : Finset ι)
    (hD : D ≠ 0) :
    primitiveCoordinateFactor D N alpha I ∣ D := by
  classical
  unfold primitiveCoordinateFactor
  apply Finset.prod_dvd_of_coprime
    (powered_coordinate_factors_pairwise_coprime D N alpha I)
  intro i hi
  rw [← Polynomial.le_rootMultiplicity_iff hD]
  exact commonCoordinateMultiplicity_le_denominator D N (alpha i)
theorem primitiveCoordinateFactor_dvd_numerator
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (I : Finset ι) :
    primitiveCoordinateFactor D N alpha I ∣ N := by
  classical
  by_cases hN : N = 0
  · simp [hN]
  · unfold primitiveCoordinateFactor
    apply Finset.prod_dvd_of_coprime
      (powered_coordinate_factors_pairwise_coprime D N alpha I)
    intro i hi
    rw [← Polynomial.le_rootMultiplicity_iff hN]
    exact commonCoordinateMultiplicity_le_numerator D N (alpha i) hN
structure PrimitiveRationalFrame
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (I : Finset ι) where
  commonFactor : XOverZ F
  denominator : XOverZ F
  numerator : XOverZ F
  commonFactor_monic : commonFactor.Monic
  denominator_factor : D = commonFactor * denominator
  numerator_factor : N = commonFactor * numerator
  denominator_ne_zero : denominator ≠ 0
  primitive_at_coordinates : ∀ i ∈ I,
    ¬ (evalOuterAt (alpha i) denominator = 0 ∧
      evalOuterAt (alpha i) numerator = 0)
noncomputable def primitiveRationalFrame
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha : ι ↪ F) (I : Finset ι)
    (hD : D ≠ 0) : PrimitiveRationalFrame D N alpha I := by
  classical
  let G := primitiveCoordinateFactor D N alpha I
  let Dred := D /ₘ G
  let Nred := N /ₘ G
  have hGmonic : G.Monic := primitiveCoordinateFactor_monic D N alpha I
  have hGne : G ≠ 0 := hGmonic.ne_zero
  have hGdvdD : G ∣ D :=
    primitiveCoordinateFactor_dvd_denominator D N alpha I hD
  have hGdvdN : G ∣ N :=
    primitiveCoordinateFactor_dvd_numerator D N alpha I
  have hDfac : D = G * Dred := by
    have hmod : D %ₘ G = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hGmonic).2 hGdvdD
    have hdiv := Polynomial.modByMonic_add_div D G
    rw [hmod, zero_add] at hdiv
    exact hdiv.symm
  have hNfac : N = G * Nred := by
    have hmod : N %ₘ G = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hGmonic).2 hGdvdN
    have hdiv := Polynomial.modByMonic_add_div N G
    rw [hmod, zero_add] at hdiv
    exact hdiv.symm
  have hDred : Dred ≠ 0 := by
    intro hzero
    apply hD
    rw [hDfac, hzero, mul_zero]
  refine
    { commonFactor := G
      denominator := Dred
      numerator := Nred
      commonFactor_monic := hGmonic
      denominator_factor := hDfac
      numerator_factor := hNfac
      denominator_ne_zero := hDred
      primitive_at_coordinates := ?_ }
  intro i hi hboth
  let L : XOverZ F :=
    Polynomial.X - Polynomial.C (Polynomial.C (alpha i))
  let e := commonCoordinateMultiplicity D N (alpha i)
  have hpowG : L ^ e ∣ G := by
    exact Finset.dvd_prod_of_mem
      (fun j =>
        (Polynomial.X - Polynomial.C (Polynomial.C (alpha j))) ^
          commonCoordinateMultiplicity D N (alpha j)) hi
  have hLDred : L ∣ Dred := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hboth.1
  have hpowD : L ^ (e + 1) ∣ D := by
    rw [pow_succ, hDfac]
    exact mul_dvd_mul hpowG hLDred
  have heD : e + 1 ≤ D.rootMultiplicity (Polynomial.C (alpha i)) := by
    exact (Polynomial.le_rootMultiplicity_iff hD).2 hpowD
  by_cases hN : N = 0
  · simp [e, commonCoordinateMultiplicity, hN] at heD
  · have hLNred : L ∣ Nred := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hboth.2
    have hpowN : L ^ (e + 1) ∣ N := by
      rw [pow_succ, hNfac]
      exact mul_dvd_mul hpowG hLNred
    have heN : e + 1 ≤ N.rootMultiplicity (Polynomial.C (alpha i)) :=
      (Polynomial.le_rootMultiplicity_iff hN).2 hpowN
    simp [e, commonCoordinateMultiplicity, hN] at heD heN
    omega
theorem PrimitiveRationalFrame.specialize_commonFactor_ne_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) (z : F) :
    specializeCoeffZ z R.commonFactor ≠ 0 :=
  (R.commonFactor_monic.map (Polynomial.evalRingHom z)).ne_zero
theorem PrimitiveRationalFrame.cancel_specialized_owner
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) (z : F)
    (P : Polynomial F)
    (hbranch : specializeCoeffZ z D * P = -specializeCoeffZ z N) :
    specializeCoeffZ z R.denominator * P =
      -specializeCoeffZ z R.numerator := by
  have hG := R.specialize_commonFactor_ne_zero z
  have hDspec : specializeCoeffZ z D =
      specializeCoeffZ z R.commonFactor *
        specializeCoeffZ z R.denominator := by
    simpa only [map_mul] using
      congrArg (specializeCoeffZ z) R.denominator_factor
  have hNspec : specializeCoeffZ z N =
      specializeCoeffZ z R.commonFactor *
        specializeCoeffZ z R.numerator := by
    simpa only [map_mul] using
      congrArg (specializeCoeffZ z) R.numerator_factor
  rw [hDspec, hNspec] at hbranch
  apply mul_left_cancel₀ hG
  simpa [mul_assoc] using hbranch
theorem PrimitiveRationalFrame.swap_denominator_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) :
    (Polynomial.Bivariate.swap R.denominator).natDegree ≤
      (Polynomial.Bivariate.swap D).natDegree := by
  have hG : Polynomial.Bivariate.swap R.commonFactor ≠ 0 :=
    (map_ne_zero_iff Polynomial.Bivariate.swap
      Polynomial.Bivariate.swap.injective).2 R.commonFactor_monic.ne_zero
  have hDred : Polynomial.Bivariate.swap R.denominator ≠ 0 :=
    (map_ne_zero_iff Polynomial.Bivariate.swap
      Polynomial.Bivariate.swap.injective).2 R.denominator_ne_zero
  have hfactor := congrArg Polynomial.Bivariate.swap R.denominator_factor
  simp only [map_mul] at hfactor
  rw [hfactor, Polynomial.natDegree_mul hG hDred]
  exact Nat.le_add_left _ _
theorem PrimitiveRationalFrame.swap_numerator_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) :
    (Polynomial.Bivariate.swap R.numerator).natDegree ≤
      (Polynomial.Bivariate.swap N).natDegree := by
  by_cases hNred : R.numerator = 0
  · simp [hNred]
  · have hG : Polynomial.Bivariate.swap R.commonFactor ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 R.commonFactor_monic.ne_zero
    have hNred' : Polynomial.Bivariate.swap R.numerator ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hNred
    have hfactor := congrArg Polynomial.Bivariate.swap R.numerator_factor
    simp only [map_mul] at hfactor
    rw [hfactor, Polynomial.natDegree_mul hG hNred']
    exact Nat.le_add_left _ _
theorem PrimitiveRationalFrame.evalOuterAt_denominator_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) (x : F) (degreeCap : ℕ)
    (hdegree : (Polynomial.Bivariate.swap D).natDegree ≤ degreeCap) :
    (evalOuterAt x R.denominator).natDegree ≤ degreeCap := by
  exact (evalOuterAt_natDegree_le_swap_natDegree x R.denominator).trans
    (R.swap_denominator_natDegree_le.trans hdegree)
theorem PrimitiveRationalFrame.evalOuterAt_numerator_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) (x : F) (degreeCap : ℕ)
    (hdegree : (Polynomial.Bivariate.swap N).natDegree ≤ degreeCap) :
    (evalOuterAt x R.numerator).natDegree ≤ degreeCap := by
  exact (evalOuterAt_natDegree_le_swap_natDegree x R.numerator).trans
    (R.swap_numerator_natDegree_le.trans hdegree)
noncomputable def rationalCoordinateMismatch
    {F : Type*} [Field F] (D N : XOverZ F) (x u₀ u₁ : F) : Polynomial F :=
  evalOuterAt x D * affineValuePolynomial u₀ u₁ + evalOuterAt x N
theorem PrimitiveRationalFrame.rationalCoordinateMismatch_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveRationalFrame D N alpha I) (x u₀ u₁ : F)
    (denominatorCap numeratorCap : ℕ)
    (hDdegree : (Polynomial.Bivariate.swap D).natDegree ≤ denominatorCap)
    (hNdegree : (Polynomial.Bivariate.swap N).natDegree ≤ numeratorCap) :
    (rationalCoordinateMismatch R.denominator R.numerator x u₀ u₁).natDegree ≤
      max (denominatorCap + 1) numeratorCap := by
  unfold rationalCoordinateMismatch
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add
        (R.evalOuterAt_denominator_natDegree_le x denominatorCap hDdegree)
        (affineValuePolynomial_natDegree_le_one u₀ u₁))).trans
          (le_max_left _ _)
  · exact (R.evalOuterAt_numerator_natDegree_le x numeratorCap hNdegree).trans
      (le_max_right _ _)
noncomputable def rationalIdentityCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    Finset ι := by
  classical
  exact I.filter fun i =>
    rationalCoordinateMismatch D N (alpha i) (u₀ i) (u₁ i) = 0
noncomputable def rationalActiveIdentityCoordinates
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D N : XOverZ F) (alpha u₀ u₁ : ι → F) (I : Finset ι) :
    Finset ι := by
  classical
  exact (rationalIdentityCoordinates D N alpha u₀ u₁ I).filter fun i =>
    evalOuterAt (alpha i) D ≠ 0
theorem PrimitiveRationalFrame.identityCoordinates_eq_active
    {F ι : Type*} [Field F] [DecidableEq ι]
    {D N : XOverZ F} {alpha : ι ↪ F} {u₀ u₁ : ι → F}
    {I : Finset ι} (R : PrimitiveRationalFrame D N alpha I) :
    rationalIdentityCoordinates R.denominator R.numerator alpha u₀ u₁ I =
      rationalActiveIdentityCoordinates R.denominator R.numerator
        alpha u₀ u₁ I := by
  classical
  ext i
  simp only [rationalActiveIdentityCoordinates, Finset.mem_filter]
  constructor
  · intro hi
    refine ⟨hi, ?_⟩
    intro hDzero
    have hi' := Finset.mem_filter.mp hi
    have hmismatch := hi'.2
    unfold rationalCoordinateMismatch at hmismatch
    rw [hDzero, zero_mul, zero_add] at hmismatch
    exact R.primitive_at_coordinates i hi'.1 ⟨hDzero, hmismatch⟩
  · exact fun hi => hi.1
end BCHKSTwoFrobeniusPrimitiveFrame6401
end ProximityPrize.SubmissionLower
