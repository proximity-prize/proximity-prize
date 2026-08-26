import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusFullRankOneClassification6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusThreeShiftPrimitive6401
open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusSymbolicKernel6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
def primitiveThreeShiftXCap6401 : Fin 3 → ℕ := ![153578, 22507, 22507]
theorem primitiveThreeShift_gap_exact6401 :
    primitiveThreeShiftXCap6401 0 = 153578 ∧
      primitiveThreeShiftXCap6401 1 = 22507 ∧
      primitiveThreeShiftXCap6401 2 = 22507 ∧
      primitiveThreeShiftXCap6401 0 -
          primitiveThreeShiftXCap6401 1 = ownerDegreeCap6401 ∧
      primitiveThreeShiftXCap6401 0 -
          primitiveThreeShiftXCap6401 2 = ownerDegreeCap6401 := by
  decide
def threeShiftRowXCap6401 : Fin 3 → Fin 3 → ℕ := ![
  ![153578, 54282, 54282],
  ![185353, 22507, 54282],
  ![185353, 54282, 22507]]
theorem threeShift_intersection_caps_exact6401 :
    threeShiftRowXCap6401 0 0 = primitiveThreeShiftXCap6401 0 ∧
      threeShiftRowXCap6401 1 1 = primitiveThreeShiftXCap6401 1 ∧
      threeShiftRowXCap6401 2 2 = primitiveThreeShiftXCap6401 2 := by
  decide
structure ThreeShiftCommonDirection
    {F : Type*} [Field F] where
  rows : Fin 3 → SymbolicRow F
  direction : SymbolicRow F
  multiplier : Fin 3 → XOverZ F
  multiplier_ne_zero : ∀ s, multiplier s ≠ 0
  row_factor : ∀ s j, rows s j = multiplier s * direction j
  row_caps : ∀ s j, (rows s j).natDegree ≤ threeShiftRowXCap6401 s j
  direction_nonzero : direction ≠ 0
theorem ThreeShiftCommonDirection.direction_caps
    {F : Type*} [Field F] (D : ThreeShiftCommonDirection (F := F)) :
    ∀ j, (D.direction j).natDegree ≤ primitiveThreeShiftXCap6401 j := by
  intro j
  fin_cases j
  · by_cases hzero : D.direction 0 = 0
    · simp [hzero, primitiveThreeShiftXCap6401]
    · have hfactor := D.row_factor 0 0
      have hdegree := D.row_caps 0 0
      rw [hfactor, Polynomial.natDegree_mul (D.multiplier_ne_zero 0) hzero]
        at hdegree
      exact (Nat.le_add_left _ _).trans hdegree
  · by_cases hzero : D.direction 1 = 0
    · simp [hzero, primitiveThreeShiftXCap6401]
    · have hfactor := D.row_factor 1 1
      have hdegree := D.row_caps 1 1
      rw [hfactor, Polynomial.natDegree_mul (D.multiplier_ne_zero 1) hzero]
        at hdegree
      exact (Nat.le_add_left _ _).trans hdegree
  · by_cases hzero : D.direction 2 = 0
    · simp [hzero, primitiveThreeShiftXCap6401]
    · have hfactor := D.row_factor 2 2
      have hdegree := D.row_caps 2 2
      rw [hfactor, Polynomial.natDegree_mul (D.multiplier_ne_zero 2) hzero]
        at hdegree
      exact (Nat.le_add_left _ _).trans hdegree
theorem ThreeShiftCommonDirection.exists_nonzero_component
    {F : Type*} [Field F] (D : ThreeShiftCommonDirection (F := F)) :
    ∃ pivot : Fin 3, D.direction pivot ≠ 0 := by
  by_contra h
  apply D.direction_nonzero
  funext j
  by_contra hj
  exact h ⟨j, hj⟩
noncomputable def guardedCoordinateMultiplicity
    {F : Type*} [Field F] (P pivot : XOverZ F) (a : F) : ℕ := by
  classical
  exact if P = 0 then pivot.rootMultiplicity (Polynomial.C a)
    else P.rootMultiplicity (Polynomial.C a)
noncomputable def tripleCommonCoordinateMultiplicity
    {F : Type*} [Field F] (B : SymbolicRow F) (pivot : Fin 3) (a : F) : ℕ :=
  min (guardedCoordinateMultiplicity (B 0) (B pivot) a)
    (min (guardedCoordinateMultiplicity (B 1) (B pivot) a)
      (guardedCoordinateMultiplicity (B 2) (B pivot) a))
theorem tripleCommonCoordinateMultiplicity_le_component
    {F : Type*} [Field F] (B : SymbolicRow F) (pivot j : Fin 3) (a : F)
    (hj : B j ≠ 0) :
    tripleCommonCoordinateMultiplicity B pivot a ≤
      (B j).rootMultiplicity (Polynomial.C a) := by
  fin_cases j
  · change B 0 ≠ 0 at hj
    calc
      tripleCommonCoordinateMultiplicity B pivot a ≤
          guardedCoordinateMultiplicity (B 0) (B pivot) a := min_le_left _ _
      _ = (B 0).rootMultiplicity (Polynomial.C a) := by
        simp [guardedCoordinateMultiplicity, hj]
  · change B 1 ≠ 0 at hj
    calc
      tripleCommonCoordinateMultiplicity B pivot a ≤
          min (guardedCoordinateMultiplicity (B 1) (B pivot) a)
            (guardedCoordinateMultiplicity (B 2) (B pivot) a) :=
        min_le_right _ _
      _ ≤ guardedCoordinateMultiplicity (B 1) (B pivot) a := min_le_left _ _
      _ = (B 1).rootMultiplicity (Polynomial.C a) := by
        simp [guardedCoordinateMultiplicity, hj]
  · change B 2 ≠ 0 at hj
    calc
      tripleCommonCoordinateMultiplicity B pivot a ≤
          min (guardedCoordinateMultiplicity (B 1) (B pivot) a)
            (guardedCoordinateMultiplicity (B 2) (B pivot) a) :=
        min_le_right _ _
      _ ≤ guardedCoordinateMultiplicity (B 2) (B pivot) a := min_le_right _ _
      _ = (B 2).rootMultiplicity (Polynomial.C a) := by
        simp [guardedCoordinateMultiplicity, hj]
noncomputable def triplePrimitiveCoordinateFactor
    {F ι : Type*} [Field F]
    (B : SymbolicRow F) (pivot : Fin 3)
    (alpha : ι → F) (I : Finset ι) : XOverZ F :=
  ∏ i ∈ I, (Polynomial.X - Polynomial.C (Polynomial.C (alpha i))) ^
    tripleCommonCoordinateMultiplicity B pivot (alpha i)
theorem triplePrimitiveCoordinateFactor_monic
    {F ι : Type*} [Field F]
    (B : SymbolicRow F) (pivot : Fin 3)
    (alpha : ι → F) (I : Finset ι) :
    (triplePrimitiveCoordinateFactor B pivot alpha I).Monic := by
  classical
  unfold triplePrimitiveCoordinateFactor
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _
private theorem triple_powered_coordinate_factors_pairwise_coprime
    {F ι : Type*} [Field F] [DecidableEq ι]
    (B : SymbolicRow F) (pivot : Fin 3)
    (alpha : ι ↪ F) (I : Finset ι) :
    (↑I : Set ι).Pairwise (Function.onFun IsCoprime fun i =>
      (Polynomial.X - Polynomial.C (Polynomial.C (alpha i))) ^
        tripleCommonCoordinateMultiplicity B pivot (alpha i)) := by
  intro i hi j hj hij
  have hne : alpha i ≠ alpha j := fun h => hij (alpha.injective h)
  have hunit : IsUnit
      ((Polynomial.C (alpha i) : Polynomial F) -
        Polynomial.C (alpha j)) := by
    rw [← Polynomial.C_sub]
    exact Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hne).isUnit
  exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit).pow
theorem triplePrimitiveCoordinateFactor_dvd_component
    {F ι : Type*} [Field F] [DecidableEq ι]
    (B : SymbolicRow F) (pivot j : Fin 3)
    (alpha : ι ↪ F) (I : Finset ι) :
    triplePrimitiveCoordinateFactor B pivot alpha I ∣ B j := by
  classical
  by_cases hj : B j = 0
  · simp [hj]
  · unfold triplePrimitiveCoordinateFactor
    apply Finset.prod_dvd_of_coprime
      (triple_powered_coordinate_factors_pairwise_coprime
        B pivot alpha I)
    intro i hi
    rw [← Polynomial.le_rootMultiplicity_iff hj]
    exact tripleCommonCoordinateMultiplicity_le_component
      B pivot j (alpha i) hj
structure PrimitiveThreeShiftFrame
    {F ι : Type*} [Field F] [DecidableEq ι]
    (B : SymbolicRow F) (pivot : Fin 3)
    (alpha : ι ↪ F) (I : Finset ι) where
  commonFactor : XOverZ F
  reduced : SymbolicRow F
  commonFactor_monic : commonFactor.Monic
  component_factor : ∀ j, B j = commonFactor * reduced j
  pivot_ne_zero : reduced pivot ≠ 0
  primitive_at_coordinates : ∀ i ∈ I,
    ¬ (∀ j, evalOuterAt (alpha i) (reduced j) = 0)
noncomputable def primitiveThreeShiftFrame
    {F ι : Type*} [Field F] [DecidableEq ι]
    (B : SymbolicRow F) (pivot : Fin 3)
    (alpha : ι ↪ F) (I : Finset ι)
    (hpivot : B pivot ≠ 0) :
    PrimitiveThreeShiftFrame B pivot alpha I := by
  classical
  let G := triplePrimitiveCoordinateFactor B pivot alpha I
  let R : SymbolicRow F := fun j => B j /ₘ G
  have hGmonic : G.Monic :=
    triplePrimitiveCoordinateFactor_monic B pivot alpha I
  have hGdvd : ∀ j, G ∣ B j := fun j =>
    triplePrimitiveCoordinateFactor_dvd_component B pivot j alpha I
  have hfactor : ∀ j, B j = G * R j := by
    intro j
    have hmod : B j %ₘ G = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hGmonic).2 (hGdvd j)
    have hdiv := Polynomial.modByMonic_add_div (B j) G
    rw [hmod, zero_add] at hdiv
    exact hdiv.symm
  have hpivotRed : R pivot ≠ 0 := by
    intro hzero
    apply hpivot
    rw [hfactor pivot, hzero, mul_zero]
  refine
    { commonFactor := G
      reduced := R
      commonFactor_monic := hGmonic
      component_factor := hfactor
      pivot_ne_zero := hpivotRed
      primitive_at_coordinates := ?_ }
  intro i hi hall
  let L : XOverZ F :=
    Polynomial.X - Polynomial.C (Polynomial.C (alpha i))
  let e := tripleCommonCoordinateMultiplicity B pivot (alpha i)
  have hpowG : L ^ e ∣ G := by
    exact Finset.dvd_prod_of_mem
      (fun j =>
        (Polynomial.X - Polynomial.C (Polynomial.C (alpha j))) ^
          tripleCommonCoordinateMultiplicity B pivot (alpha j)) hi
  have hroot (j : Fin 3) : L ∣ R j := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hall j
  have hmult (j : Fin 3) (hj : B j ≠ 0) :
      e + 1 ≤ (B j).rootMultiplicity (Polynomial.C (alpha i)) := by
    have hpow : L ^ (e + 1) ∣ B j := by
      rw [pow_succ, hfactor j]
      exact mul_dvd_mul hpowG (hroot j)
    exact (Polynomial.le_rootMultiplicity_iff hj).2 hpow
  have hpivotMult : e + 1 ≤
      (B pivot).rootMultiplicity (Polynomial.C (alpha i)) :=
    hmult pivot hpivot
  have hguard (j : Fin 3) : e + 1 ≤
      guardedCoordinateMultiplicity (B j) (B pivot) (alpha i) := by
    by_cases hj : B j = 0
    · simp [guardedCoordinateMultiplicity, hj, hpivotMult]
    · simpa [guardedCoordinateMultiplicity, hj] using hmult j hj
  have h0 := hguard 0
  have h1 := hguard 1
  have h2 := hguard 2
  simp [e, tripleCommonCoordinateMultiplicity] at h0 h1 h2
  omega
theorem PrimitiveThreeShiftFrame.specialize_commonFactor_ne_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I) (z : F) :
    specializeCoeffZ z R.commonFactor ≠ 0 :=
  (R.commonFactor_monic.map (Polynomial.evalRingHom z)).ne_zero
theorem PrimitiveThreeShiftFrame.specialize_component_factor
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I) (z : F) (j : Fin 3) :
    specializeRow z B j =
      specializeCoeffZ z R.commonFactor * specializeRow z R.reduced j := by
  simpa [specializeRow] using
    congrArg (specializeCoeffZ z) (R.component_factor j)
theorem PrimitiveThreeShiftFrame.cancel_specialized_relation
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (z : F) (P : Polynomial F)
    (hrel : symbolicRelation sigma (specializeRow z B) P = 0) :
    symbolicRelation sigma (specializeRow z R.reduced) P = 0 := by
  have hG := R.specialize_commonFactor_ne_zero z
  have h0 := R.specialize_component_factor z 0
  have h1 := R.specialize_component_factor z 1
  have h2 := R.specialize_component_factor z 2
  unfold symbolicRelation at hrel ⊢
  rw [h0, h1, h2] at hrel
  apply mul_left_cancel₀ hG
  linear_combination hrel
theorem PrimitiveThreeShiftFrame.reduced_natDegree_le
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I) (j : Fin 3) :
    (R.reduced j).natDegree ≤ (B j).natDegree := by
  by_cases hj : R.reduced j = 0
  · simp [hj]
  · have hG := R.commonFactor_monic.ne_zero
    rw [R.component_factor j, Polynomial.natDegree_mul hG hj]
    exact Nat.le_add_left _ _
theorem PrimitiveThreeShiftFrame.reduced_threeShift_caps
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (hcap : ∀ j, (B j).natDegree ≤ primitiveThreeShiftXCap6401 j) :
    ∀ j, (R.reduced j).natDegree ≤ primitiveThreeShiftXCap6401 j :=
  fun j => (R.reduced_natDegree_le j).trans (hcap j)
structure PrimitiveNormalizedThreeShiftDirection
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : ThreeShiftCommonDirection (F := F))
    (alpha : ι ↪ F) (I : Finset ι) where
  pivot : Fin 3
  source_pivot_ne_zero : D.direction pivot ≠ 0
  frame : PrimitiveThreeShiftFrame D.direction pivot alpha I
  reduced_caps : ∀ j,
    (frame.reduced j).natDegree ≤ primitiveThreeShiftXCap6401 j
noncomputable def ThreeShiftCommonDirection.primitiveNormalization
    {F ι : Type*} [Field F] [DecidableEq ι]
    (D : ThreeShiftCommonDirection (F := F))
    (alpha : ι ↪ F) (I : Finset ι) :
    PrimitiveNormalizedThreeShiftDirection D alpha I := by
  classical
  let pivot := Classical.choose D.exists_nonzero_component
  have hpivot : D.direction pivot ≠ 0 :=
    Classical.choose_spec D.exists_nonzero_component
  let R := primitiveThreeShiftFrame D.direction pivot alpha I hpivot
  exact
    { pivot := pivot
      source_pivot_ne_zero := hpivot
      frame := R
      reduced_caps := R.reduced_threeShift_caps D.direction_caps }
theorem PrimitiveThreeShiftFrame.cancel_coordinate_relation
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (x u₀ u₁ : F)
    (hfactor : evalOuterAt x R.commonFactor ≠ 0)
    (hsource : symbolicCoordinateRelation sigma x u₀ u₁ B = 0) :
    symbolicCoordinateRelation sigma x u₀ u₁ R.reduced = 0 := by
  have h0 := congrArg (evalOuterAt x) (R.component_factor 0)
  have h1 := congrArg (evalOuterAt x) (R.component_factor 1)
  have h2 := congrArg (evalOuterAt x) (R.component_factor 2)
  simp only [evalOuterAt, Polynomial.eval_mul] at h0 h1 h2
  unfold symbolicCoordinateRelation at hsource ⊢
  change Polynomial.eval (Polynomial.C x) (B 0) +
      Polynomial.eval (Polynomial.C x) (B 1) * receivedZ u₀ u₁ +
      Polynomial.eval (Polynomial.C x) (B 2) *
        receivedFrobeniusZ sigma u₀ u₁ = 0 at hsource
  change Polynomial.eval (Polynomial.C x) (R.reduced 0) +
      Polynomial.eval (Polynomial.C x) (R.reduced 1) * receivedZ u₀ u₁ +
      Polynomial.eval (Polynomial.C x) (R.reduced 2) *
        receivedFrobeniusZ sigma u₀ u₁ = 0
  rw [h0, h1, h2] at hsource
  apply mul_left_cancel₀ (by simpa [evalOuterAt] using hfactor)
  linear_combination hsource
def RemovedCoordinateRelationRecovery6401
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (u₀ u₁ : ι → F) : Prop :=
  ∀ i ∈ I, evalOuterAt (alpha i) R.commonFactor = 0 →
    symbolicCoordinateRelation sigma (alpha i) (u₀ i) (u₁ i)
      R.reduced = 0
theorem receivedZ_derivative
    {F : Type*} [Field F] (u₀ u₁ : F) :
    (receivedZ u₀ u₁).derivative = Polynomial.C u₁ := by
  simp [receivedZ, Polynomial.derivative_mul]
theorem receivedFrobeniusZ_derivative_eq_zero
    {F : Type*} [Field F] (sigma : F →+* F) (u₀ u₁ : F)
    (hq : (q6401 : F) = 0) :
    (receivedFrobeniusZ sigma u₀ u₁).derivative = 0 := by
  simp [receivedFrobeniusZ, Polynomial.derivative_monomial, hq]
theorem ordinaryHasseZ_quotient_identity
    {F : Type*} [Field F] (sigma : F →+* F)
    (A₀ A₁ A₂ : Polynomial F) (u₀ u₁ : F)
    (hq : (q6401 : F) = 0)
    (hrel : A₀ + A₁ * receivedZ u₀ u₁ +
      A₂ * receivedFrobeniusZ sigma u₀ u₁ = 0) :
    A₁ * Polynomial.C u₁ =
      -(A₀.derivative + A₁.derivative * receivedZ u₀ u₁ +
        A₂.derivative * receivedFrobeniusZ sigma u₀ u₁) := by
  have hder := congrArg Polynomial.derivative hrel
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_zero] at hder
  rw [receivedZ_derivative,
    receivedFrobeniusZ_derivative_eq_zero sigma u₀ u₁ hq,
    mul_zero, add_zero] at hder
  linear_combination hder
theorem PrimitiveThreeShiftFrame.coordinate_ordinaryHasseZ_identity
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (i : ι) (u₀ u₁ : ι → F)
    (hq : (q6401 : F) = 0)
    (hrel : evalOuterAt (alpha i) (R.reduced 0) +
      evalOuterAt (alpha i) (R.reduced 1) * receivedZ (u₀ i) (u₁ i) +
      evalOuterAt (alpha i) (R.reduced 2) *
        receivedFrobeniusZ sigma (u₀ i) (u₁ i) = 0) :
    evalOuterAt (alpha i) (R.reduced 1) * Polynomial.C (u₁ i) =
      -((evalOuterAt (alpha i) (R.reduced 0)).derivative +
        (evalOuterAt (alpha i) (R.reduced 1)).derivative *
          receivedZ (u₀ i) (u₁ i) +
        (evalOuterAt (alpha i) (R.reduced 2)).derivative *
          receivedFrobeniusZ sigma (u₀ i) (u₁ i)) :=
  ordinaryHasseZ_quotient_identity sigma _ _ _ _ _ hq hrel
def OrdinarySlopeDivisibilityZeroFill6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (R : SymbolicRow F) (u₀ u₁ : Fin n6401 → F) : Prop :=
  ∀ (z : F) (A : Finset (Fin n6401)) (P : Polynomial F),
    P.natDegree ≤ ownerDegreeCap6401 →
    a6401 ≤ A.card →
    (∀ i ∈ A, Polynomial.eval (alpha i) P = u₀ i + z * u₁ i) →
    (∀ i ∈ A,
      evalOuterAt (alpha i) (R 1) * Polynomial.C (u₁ i) =
        -((evalOuterAt (alpha i) (R 0)).derivative +
          (evalOuterAt (alpha i) (R 1)).derivative *
            receivedZ (u₀ i) (u₁ i) +
          (evalOuterAt (alpha i) (R 2)).derivative *
            receivedFrobeniusZ sigma (u₀ i) (u₁ i))) →
    ∃ p₁ : Polynomial F,
      p₁.natDegree ≤ ownerDegreeCap6401 ∧
      ∀ i ∈ A, Polynomial.eval (alpha i) p₁ = u₁ i
end BCHKSTwoFrobeniusThreeShiftPrimitive6401
end ProximityPrize.SubmissionLower
