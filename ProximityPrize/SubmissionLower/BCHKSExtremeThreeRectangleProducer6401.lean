import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusExtremeKernelCounter6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusWeakCurveSeed6401
import ProximityPrize.SubmissionLower.BCHKSFiniteRankOnePrincipalization6401
import ProximityPrize.SubmissionLower.BCHKSExtremePairConsumer6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremeThreeRectangleProducer6401
open Polynomial
open scoped BigOperators
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
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFiniteRankOnePrincipalization6401
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
abbrev ExtremeSymbolicCoefficients6401
    (F : Type*) [Field F] (s : Fin 3) :=
  (Fin (extremeSlots6401 s 0) × Fin (extremeDepth6401 s) → F) ×
    (Fin (extremeSlots6401 s 1) × Fin (extremeDepth6401 s - 1) → F) ×
    (Fin (extremeSlots6401 s 2) ×
      Fin (extremeDepth6401 s - q6401) → F)
noncomputable def extremeCoefficientRowMap6401
    {F : Type*} [Field F] (s : Fin 3) :
    ExtremeSymbolicCoefficients6401 F s →ₗ[F] SymbolicRow F where
  toFun c := ![
    boxPolynomialMap (extremeSlots6401 s 0) (extremeDepth6401 s) c.1,
    boxPolynomialMap (extremeSlots6401 s 1) (extremeDepth6401 s - 1) c.2.1,
    boxPolynomialMap (extremeSlots6401 s 2)
      (extremeDepth6401 s - q6401) c.2.2]
  map_add' c d := by
    funext j
    fin_cases j <;> simp
  map_smul' a c := by
    funext j
    fin_cases j <;> simp
@[simp] theorem extremeCoefficientRowMap_zero_apply6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    extremeCoefficientRowMap6401 s c 0 =
      boxPolynomialMap (extremeSlots6401 s 0) (extremeDepth6401 s) c.1 := rfl
@[simp] theorem extremeCoefficientRowMap_one_apply6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    extremeCoefficientRowMap6401 s c 1 =
      boxPolynomialMap (extremeSlots6401 s 1)
        (extremeDepth6401 s - 1) c.2.1 := rfl
@[simp] theorem extremeCoefficientRowMap_two_apply6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    extremeCoefficientRowMap6401 s c 2 =
      boxPolynomialMap (extremeSlots6401 s 2)
        (extremeDepth6401 s - q6401) c.2.2 := rfl
theorem extremeCoefficientRowMap_injective6401
    {F : Type*} [Field F] (s : Fin 3) :
    Function.Injective (extremeCoefficientRowMap6401 (F := F) s) := by
  intro c d hcd
  apply Prod.ext
  · apply boxPolynomialMap_injective
    have h := congrFun hcd (0 : Fin 3)
    simpa [extremeCoefficientRowMap6401] using h
  · apply Prod.ext
    · apply boxPolynomialMap_injective
      have h := congrFun hcd (1 : Fin 3)
      simpa [extremeCoefficientRowMap6401] using h
    · apply boxPolynomialMap_injective
      have h := congrFun hcd (2 : Fin 3)
      simpa [extremeCoefficientRowMap6401] using h
theorem extremeDepth_room6401 (s : Fin 3) :
    2 ≤ extremeDepth6401 s ∧ q6401 + 1 ≤ extremeDepth6401 s := by
  fin_cases s <;> native_decide
theorem threeShiftRowXCap_eq_extremeSlots_sub_one6401 :
    threeShiftRowXCap6401 =
      fun s j ↦ extremeSlots6401 s j - 1 := by
  native_decide
theorem extremeCoefficientRowMap_natDegree_le6401
    {F : Type*} [Field F] (s j : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    (extremeCoefficientRowMap6401 s c j).natDegree ≤
      threeShiftRowXCap6401 s j := by
  rw [congrFun (congrFun
    threeShiftRowXCap_eq_extremeSlots_sub_one6401 s) j]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · rw [extremeCoefficientRowMap_zero_apply6401]
    exact boxPolynomialMap_natDegree_le _ _ _
  · rw [extremeCoefficientRowMap_one_apply6401]
    exact boxPolynomialMap_natDegree_le _ _ _
  · rw [extremeCoefficientRowMap_two_apply6401]
    exact boxPolynomialMap_natDegree_le _ _ _
theorem extremeCoefficientRowMap_zero_inner_natDegree_le6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    (Polynomial.Bivariate.swap
      (extremeCoefficientRowMap6401 s c 0)).natDegree ≤
        extremeDepth6401 s - 1 := by
  rw [extremeCoefficientRowMap_zero_apply6401]
  exact swap_boxPolynomialMap_natDegree_le _ _ _
theorem extremeCoefficientRowMap_one_inner_natDegree_le6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    (Polynomial.Bivariate.swap
      (extremeCoefficientRowMap6401 s c 1)).natDegree ≤
        (extremeDepth6401 s - 1) - 1 := by
  rw [extremeCoefficientRowMap_one_apply6401]
  exact swap_boxPolynomialMap_natDegree_le _ _ _
theorem extremeCoefficientRowMap_two_inner_natDegree_le6401
    {F : Type*} [Field F] (s : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    (Polynomial.Bivariate.swap
      (extremeCoefficientRowMap6401 s c 2)).natDegree ≤
        (extremeDepth6401 s - q6401) - 1 := by
  rw [extremeCoefficientRowMap_two_apply6401]
  exact swap_boxPolynomialMap_natDegree_le _ _ _
noncomputable def extremeSymbolicConstraintMap6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) :
    ExtremeSymbolicCoefficients6401 F s →ₗ[F]
      (Fin n6401 × Fin (extremeDepth6401 s) → F) :=
  LinearMap.pi fun id ↦
    (Polynomial.lcoeff F (id.2 : ℕ)).comp <|
      (symbolicCoordinateRelationMap sigma (alpha id.1)
        (u0 id.1) (u1 id.1)).comp (extremeCoefficientRowMap6401 s)
noncomputable abbrev ExtremeSymbolicKernel6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) :=
  LinearMap.ker (extremeSymbolicConstraintMap6401 s sigma alpha u0 u1)
theorem extremeSymbolicKernel_ne_bot6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) :
    ExtremeSymbolicKernel6401 s sigma alpha u0 u1 ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin]
  have hexact := extreme_rectangles_exact6401.2.2.2.1 s
  simp only [extremeVariables6401, extremeConstraints6401] at hexact
  omega
noncomputable def selectedExtremeKernelCoefficient6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) :
    ExtremeSymbolicKernel6401 s sigma alpha u0 u1 :=
  ⟨Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot
      (extremeSymbolicKernel_ne_bot6401 s sigma alpha u0 u1)),
    (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
      (extremeSymbolicKernel_ne_bot6401 s sigma alpha u0 u1))).1⟩
theorem selectedExtremeKernelCoefficient_ne_zero6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) :
    selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1 ≠ 0 := by
  intro hzero
  have hvalue :
      (selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1).1 = 0 :=
    congrArg Subtype.val hzero
  exact (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (extremeSymbolicKernel_ne_bot6401 s sigma alpha u0 u1))).2 (by
      simpa [selectedExtremeKernelCoefficient6401] using hvalue)
noncomputable def selectedExtremeRow6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) (s : Fin 3) : SymbolicRow F :=
  extremeCoefficientRowMap6401 s
    (selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1).1
theorem selectedExtremeRow_ne_zero6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) (s : Fin 3) :
    selectedExtremeRow6401 sigma alpha u0 u1 s ≠ 0 := by
  intro hzero
  have hcoeff :
      (selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1).1 = 0 :=
    extremeCoefficientRowMap_injective6401 s (by
      simpa [selectedExtremeRow6401] using hzero)
  apply selectedExtremeKernelCoefficient_ne_zero6401 s sigma alpha u0 u1
  exact Subtype.ext hcoeff
theorem selectedExtremeRow_natDegree_le6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) (s j : Fin 3) :
    (selectedExtremeRow6401 sigma alpha u0 u1 s j).natDegree ≤
      threeShiftRowXCap6401 s j :=
  extremeCoefficientRowMap_natDegree_le6401 s j _
theorem extremeSymbolicCoordinateRelation_natDegree_lt6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (x u0 u1 : F)
    (c : ExtremeSymbolicCoefficients6401 F s) :
    (symbolicCoordinateRelation sigma x u0 u1
      (extremeCoefficientRowMap6401 s c)).natDegree <
        extremeDepth6401 s := by
  have h0 :
      (evalOuterAt x (extremeCoefficientRowMap6401 s c 0)).natDegree ≤
        extremeDepth6401 s - 1 := by
    rw [extremeCoefficientRowMap_zero_apply6401]
    exact evalOuterAt_boxPolynomialMap_natDegree_le _ _ _ _
  have h1 :
      (evalOuterAt x (extremeCoefficientRowMap6401 s c 1)).natDegree ≤
        (extremeDepth6401 s - 1) - 1 := by
    rw [extremeCoefficientRowMap_one_apply6401]
    exact evalOuterAt_boxPolynomialMap_natDegree_le _ _ _ _
  have h2 :
      (evalOuterAt x (extremeCoefficientRowMap6401 s c 2)).natDegree ≤
        (extremeDepth6401 s - q6401) - 1 := by
    rw [extremeCoefficientRowMap_two_apply6401]
    exact evalOuterAt_boxPolynomialMap_natDegree_le _ _ _ _
  have hZ : (receivedZ u0 u1).natDegree ≤ 1 := by
    simpa [receivedZ, affineValuePolynomial] using
      affineValuePolynomial_natDegree_le_one u0 u1
  have hF := receivedFrobeniusZ_natDegree_le sigma u0 u1
  have hroom := extremeDepth_room6401 s
  have hterm1 :
      (evalOuterAt x (extremeCoefficientRowMap6401 s c 1) *
        receivedZ u0 u1).natDegree ≤ extremeDepth6401 s - 1 := by
    exact Polynomial.natDegree_mul_le.trans <| by omega
  have hterm2 :
      (evalOuterAt x (extremeCoefficientRowMap6401 s c 2) *
        receivedFrobeniusZ sigma u0 u1).natDegree ≤
          extremeDepth6401 s - 1 := by
    exact Polynomial.natDegree_mul_le.trans <| by omega
  unfold symbolicCoordinateRelation
  have hall :
      ((evalOuterAt x (extremeCoefficientRowMap6401 s c 0) +
          evalOuterAt x (extremeCoefficientRowMap6401 s c 1) *
            receivedZ u0 u1) +
        evalOuterAt x (extremeCoefficientRowMap6401 s c 2) *
          receivedFrobeniusZ sigma u0 u1).natDegree ≤
            extremeDepth6401 s - 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le
      ((Polynomial.natDegree_add_le _ _).trans (max_le h0 hterm1)) hterm2
  omega
theorem extremeKernel_coordinate_relation_eq_zero6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (i : Fin n6401) :
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
      (extremeCoefficientRowMap6401 s c.1) = 0 := by
  let R := symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
    (extremeCoefficientRowMap6401 s c.1)
  have hdegree : R.natDegree < extremeDepth6401 s :=
    extremeSymbolicCoordinateRelation_natDegree_lt6401
      s sigma (alpha i) (u0 i) (u1 i) c.1
  apply Polynomial.ext
  intro n
  by_cases hn : n < extremeDepth6401 s
  · let nf : Fin (extremeDepth6401 s) := ⟨n, hn⟩
    have hc := LinearMap.mem_ker.mp c.property
    have hfun := congrFun hc (i, nf)
    simpa [R, nf, extremeSymbolicConstraintMap6401] using hfun
  · rw [Polynomial.coeff_zero]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact hdegree.trans_le (Nat.le_of_not_gt hn)
theorem extremeKernel_specialized_value_relation6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (z : F) (i : Fin n6401) :
    Polynomial.eval (alpha i)
        (specializeRow z (extremeCoefficientRowMap6401 s c.1) 0) +
      Polynomial.eval (alpha i)
          (specializeRow z (extremeCoefficientRowMap6401 s c.1) 1) *
        (u0 i + z * u1 i) +
      Polynomial.eval (alpha i)
          (specializeRow z (extremeCoefficientRowMap6401 s c.1) 2) *
        sigma (u0 i + z * u1 i) = 0 := by
  have hzero := extremeKernel_coordinate_relation_eq_zero6401
    s sigma alpha u0 u1 c i
  have heval := congrArg (Polynomial.eval z) hzero
  simp only [Polynomial.eval_zero] at heval
  unfold symbolicCoordinateRelation at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at heval
  rw [← eval_specializeCoeffZ_comm z (alpha i)
      (extremeCoefficientRowMap6401 s c.1 0),
    ← eval_specializeCoeffZ_comm z (alpha i)
      (extremeCoefficientRowMap6401 s c.1 1),
    ← eval_specializeCoeffZ_comm z (alpha i)
      (extremeCoefficientRowMap6401 s c.1 2)] at heval
  have hZ : Polynomial.eval z (receivedZ (u0 i) (u1 i)) =
      u0 i + z * u1 i := by
    simp [receivedZ]
    ring
  rw [hZ, eval_receivedFrobeniusZ sigma z (u0 i) (u1 i) (hsigma z)] at heval
  exact heval
theorem extremeSpecializedSymbolicRelation_natDegree_le6401
    {F : Type*} [Field F]
    (s : Fin 3) (sigma : F →+* F)
    (c : ExtremeSymbolicCoefficients6401 F s)
    (z : F) (P : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401) :
    (symbolicRelation sigma
      (specializeRow z (extremeCoefficientRowMap6401 s c)) P).natDegree ≤
        185353 := by
  have h0 :
      (specializeRow z (extremeCoefficientRowMap6401 s c) 0).natDegree ≤
        threeShiftRowXCap6401 s 0 := by
    exact Polynomial.natDegree_map_le.trans
      (extremeCoefficientRowMap_natDegree_le6401 s 0 c)
  have h1c :
      (specializeRow z (extremeCoefficientRowMap6401 s c) 1).natDegree ≤
        threeShiftRowXCap6401 s 1 := by
    exact Polynomial.natDegree_map_le.trans
      (extremeCoefficientRowMap_natDegree_le6401 s 1 c)
  have h2c :
      (specializeRow z (extremeCoefficientRowMap6401 s c) 2).natDegree ≤
        threeShiftRowXCap6401 s 2 := by
    exact Polynomial.natDegree_map_le.trans
      (extremeCoefficientRowMap_natDegree_le6401 s 2 c)
  have hPmap : (P.map sigma).natDegree ≤ ownerDegreeCap6401 :=
    Polynomial.natDegree_map_le.trans hP
  have hcaps :
      threeShiftRowXCap6401 s 0 ≤ 185353 ∧
      threeShiftRowXCap6401 s 1 + ownerDegreeCap6401 ≤ 185353 ∧
      threeShiftRowXCap6401 s 2 + ownerDegreeCap6401 ≤ 185353 := by
    fin_cases s <;> native_decide
  have h1 :
      (specializeRow z (extremeCoefficientRowMap6401 s c) 1 * P).natDegree ≤
        185353 :=
    Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add h1c hP).trans hcaps.2.1)
  have h2 :
      (specializeRow z (extremeCoefficientRowMap6401 s c) 2 *
        P.map sigma).natDegree ≤ 185353 :=
    Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add h2c hPmap).trans hcaps.2.2)
  unfold symbolicRelation
  exact (Polynomial.natDegree_add_le _ _).trans <| max_le
    ((Polynomial.natDegree_add_le _ _).trans
      (max_le (h0.trans hcaps.1) h1)) h2
theorem extremeKernel_symbolicRelation_eq_zero_of_owner6401
    {F : Type*} [Field F] [DecidableEq F]
    (s : Fin 3) (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (z : F) (A : Finset (Fin n6401)) (P : Polynomial F)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (howner : ∀ i ∈ A,
      Polynomial.eval (alpha i) P = u0 i + z * u1 i)
    (hcard : a6401 ≤ A.card) :
    symbolicRelation sigma
      (specializeRow z (extremeCoefficientRowMap6401 s c.1)) P = 0 := by
  classical
  let roots : Finset F := A.map alpha
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (symbolicRelation sigma
      (specializeRow z (extremeCoefficientRowMap6401 s c.1)) P) roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hvalue := extremeKernel_specialized_value_relation6401
      s sigma alpha u0 u1 hsigma c z i
    have hown := howner i hi
    have htwist := eval_twist_of_fixed sigma (alpha i) (hfixed i) P
    unfold symbolicRelation
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hown, show Polynomial.eval (alpha i) (P.map sigma) =
        sigma (Polynomial.eval (alpha i) P) by
          simpa [twist] using htwist,
      hown]
    exact hvalue
  · rw [Finset.card_map]
    have hdeg := extremeSpecializedSymbolicRelation_natDegree_le6401
      s sigma c.1 z P hP
    norm_num [a6401] at hcard
    omega
theorem extremePair_denominator_inner_natDegree_le6401
    {F : Type*} [Field F] (s t : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s)
    (d : ExtremeSymbolicCoefficients6401 F t) :
    (Polynomial.Bivariate.swap
      (symbolicRankTwoDenominator
        (extremeCoefficientRowMap6401 s c)
        (extremeCoefficientRowMap6401 t d))).natDegree ≤
          extremePairDenominatorCap6401 s t := by
  have hc1 := extremeCoefficientRowMap_one_inner_natDegree_le6401 s c
  have hd1 := extremeCoefficientRowMap_one_inner_natDegree_le6401 t d
  have hc2 := extremeCoefficientRowMap_two_inner_natDegree_le6401 s c
  have hd2 := extremeCoefficientRowMap_two_inner_natDegree_le6401 t d
  rw [symbolicRankTwoDenominator, map_sub, map_mul, map_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hc1 hd2) |>.trans (by
        fin_cases s <;> fin_cases t <;> native_decide)
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hd1 hc2) |>.trans (by
        fin_cases s <;> fin_cases t <;> native_decide)
theorem extremePair_numerator_inner_natDegree_le6401
    {F : Type*} [Field F] (s t : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s)
    (d : ExtremeSymbolicCoefficients6401 F t) :
    (Polynomial.Bivariate.swap
      (symbolicRankTwoNumerator
        (extremeCoefficientRowMap6401 s c)
        (extremeCoefficientRowMap6401 t d))).natDegree ≤
          extremePairMismatchCap6401 s t := by
  have hc0 := extremeCoefficientRowMap_zero_inner_natDegree_le6401 s c
  have hd0 := extremeCoefficientRowMap_zero_inner_natDegree_le6401 t d
  have hc2 := extremeCoefficientRowMap_two_inner_natDegree_le6401 s c
  have hd2 := extremeCoefficientRowMap_two_inner_natDegree_le6401 t d
  rw [symbolicRankTwoNumerator, map_sub, map_mul, map_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hc0 hd2) |>.trans (by
        fin_cases s <;> fin_cases t <;> native_decide)
  · exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hd0 hc2) |>.trans (by
        fin_cases s <;> fin_cases t <;> native_decide)
theorem extremeKernel_pair_denominator_eq_zero_of_weakSeed_noCurve6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (s t : Fin 3) (hst : s ≠ t)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (d : ExtremeSymbolicKernel6401 t sigma alpha u0 u1)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    symbolicRankTwoDenominator
      (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0 := by
  classical
  let qrow := extremeCoefficientRowMap6401 s c.1
  let rrow := extremeCoefficientRowMap6401 t d.1
  let D := symbolicRankTwoDenominator qrow rrow
  let N := symbolicRankTwoNumerator qrow rrow
  by_contra hDzero
  let R := primitiveRationalFrame (F := F) (ι := Fin n6401)
    D N alpha Finset.univ
    (by simpa [D] using hDzero)
  have hDswap : (Polynomial.Bivariate.swap D).natDegree ≤
      extremePairDenominatorCap6401 s t := by
    simpa [D, qrow, rrow] using
      extremePair_denominator_inner_natDegree_le6401 s t c.1 d.1
  have hNswap : (Polynomial.Bivariate.swap N).natDegree ≤
      extremePairMismatchCap6401 s t := by
    simpa [N, qrow, rrow] using
      extremePair_numerator_inner_natDegree_le6401 s t c.1 d.1
  have hbranch : ∀ z ∈ S,
      specializeCoeffZ z R.denominator * P z =
        -specializeCoeffZ z R.numerator := by
    intro z hz
    apply R.cancel_specialized_owner z (P z)
    exact specialized_rankTwo_owner_identity sigma z qrow rrow (P z)
      (by
        simpa [qrow] using
          extremeKernel_symbolicRelation_eq_zero_of_owner6401
            s sigma alpha u0 u1 hsigma hfixed c z (A z) (P z)
              (hPdegree z hz) (howner z hz) (hrow z hz))
      (by
        simpa [rrow] using
          extremeKernel_symbolicRelation_eq_zero_of_owner6401
            t sigma alpha u0 u1 hsigma hfixed d z (A z) (P z)
              (hPdegree z hz) (howner z hz) (hrow z hz))
  have hcap := primitiveExtremePair_owner_card_lt_weakSeed6401
    alpha u0 u1 s t hst R S A P hDswap hNswap hPdegree hrow
      hbranch howner hfail
  exact (Nat.not_lt_of_ge hSlarge) hcap
theorem extremePair_minor01_outer_natDegree_lt_n6401
    {F : Type*} [Field F] (s t : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s)
    (d : ExtremeSymbolicCoefficients6401 F t) :
    (symbolicMinor01 (extremeCoefficientRowMap6401 s c)
      (extremeCoefficientRowMap6401 t d)).natDegree < n6401 := by
  have hc0 := extremeCoefficientRowMap_natDegree_le6401 s 0 c
  have hd0 := extremeCoefficientRowMap_natDegree_le6401 t 0 d
  have hc1 := extremeCoefficientRowMap_natDegree_le6401 s 1 c
  have hd1 := extremeCoefficientRowMap_natDegree_le6401 t 1 d
  unfold symbolicMinor01
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  apply (max_le_max
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd1))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc1))).trans_lt
  fin_cases s <;> fin_cases t <;> native_decide
theorem extremePair_numerator_outer_natDegree_lt_n6401
    {F : Type*} [Field F] (s t : Fin 3)
    (c : ExtremeSymbolicCoefficients6401 F s)
    (d : ExtremeSymbolicCoefficients6401 F t) :
    (symbolicRankTwoNumerator (extremeCoefficientRowMap6401 s c)
      (extremeCoefficientRowMap6401 t d)).natDegree < n6401 := by
  have hc0 := extremeCoefficientRowMap_natDegree_le6401 s 0 c
  have hd0 := extremeCoefficientRowMap_natDegree_le6401 t 0 d
  have hc2 := extremeCoefficientRowMap_natDegree_le6401 s 2 c
  have hd2 := extremeCoefficientRowMap_natDegree_le6401 t 2 d
  unfold symbolicRankTwoNumerator
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  apply (max_le_max
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd2))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc2))).trans_lt
  fin_cases s <;> fin_cases t <;> native_decide
theorem extreme_eval_minor01_eq_zero_of_kernel_and_denominator6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (d : ExtremeSymbolicKernel6401 t sigma alpha u0 u1)
    (hden : symbolicRankTwoDenominator
      (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0)
    (i : Fin n6401) :
    evalOuterAt (alpha i)
      (symbolicMinor01 (extremeCoefficientRowMap6401 s c.1)
        (extremeCoefficientRowMap6401 t d.1)) = 0 := by
  have hc := extremeKernel_coordinate_relation_eq_zero6401
    s sigma alpha u0 u1 c i
  have hd := extremeKernel_coordinate_relation_eq_zero6401
    t sigma alpha u0 u1 d i
  have hdenEval := congrArg (evalOuterAt (alpha i)) hden
  rw [evalOuterAt_symbolicRankTwoDenominator] at hdenEval
  simp only [evalOuterAt, Polynomial.eval_zero] at hdenEval
  unfold symbolicCoordinateRelation at hc hd
  simp only [symbolicMinor01, evalOuterAt, Polynomial.eval_sub,
    Polynomial.eval_mul] at *
  linear_combination
    (Polynomial.eval (Polynomial.C (alpha i))
      (extremeCoefficientRowMap6401 t d.1 1)) * hc -
    (Polynomial.eval (Polynomial.C (alpha i))
      (extremeCoefficientRowMap6401 s c.1 1)) * hd +
    (receivedFrobeniusZ sigma (u0 i) (u1 i)) * hdenEval
theorem extreme_eval_numerator_eq_zero_of_kernel_and_denominator6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (d : ExtremeSymbolicKernel6401 t sigma alpha u0 u1)
    (hden : symbolicRankTwoDenominator
      (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0)
    (i : Fin n6401) :
    evalOuterAt (alpha i)
      (symbolicRankTwoNumerator (extremeCoefficientRowMap6401 s c.1)
        (extremeCoefficientRowMap6401 t d.1)) = 0 := by
  have hc := extremeKernel_coordinate_relation_eq_zero6401
    s sigma alpha u0 u1 c i
  have hd := extremeKernel_coordinate_relation_eq_zero6401
    t sigma alpha u0 u1 d i
  have hdenEval := congrArg (evalOuterAt (alpha i)) hden
  rw [evalOuterAt_symbolicRankTwoDenominator] at hdenEval
  simp only [evalOuterAt, Polynomial.eval_zero] at hdenEval
  unfold symbolicCoordinateRelation at hc hd
  simp only [symbolicRankTwoNumerator, evalOuterAt, Polynomial.eval_sub,
    Polynomial.eval_mul] at *
  linear_combination
    (Polynomial.eval (Polynomial.C (alpha i))
      (extremeCoefficientRowMap6401 t d.1 2)) * hc -
    (Polynomial.eval (Polynomial.C (alpha i))
      (extremeCoefficientRowMap6401 s c.1 2)) * hd -
    (receivedZ (u0 i) (u1 i)) * hdenEval
theorem extreme_minor01_eq_zero_of_kernel_and_denominator6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (d : ExtremeSymbolicKernel6401 t sigma alpha u0 u1)
    (hden : symbolicRankTwoDenominator
      (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0) :
    symbolicMinor01 (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0 := by
  let roots : Finset (Polynomial F) := Finset.univ.map
    ⟨fun i : Fin n6401 ↦ Polynomial.C (alpha i),
      Polynomial.C_injective.comp alpha.injective⟩
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact extreme_eval_minor01_eq_zero_of_kernel_and_denominator6401
      sigma alpha u0 u1 s t c d hden i
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact extremePair_minor01_outer_natDegree_lt_n6401 s t c.1 d.1
theorem extreme_numerator_eq_zero_of_kernel_and_denominator6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F) (s t : Fin 3)
    (c : ExtremeSymbolicKernel6401 s sigma alpha u0 u1)
    (d : ExtremeSymbolicKernel6401 t sigma alpha u0 u1)
    (hden : symbolicRankTwoDenominator
      (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0) :
    symbolicRankTwoNumerator (extremeCoefficientRowMap6401 s c.1)
      (extremeCoefficientRowMap6401 t d.1) = 0 := by
  let roots : Finset (Polynomial F) := Finset.univ.map
    ⟨fun i : Fin n6401 ↦ Polynomial.C (alpha i),
      Polynomial.C_injective.comp alpha.injective⟩
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact extreme_eval_numerator_eq_zero_of_kernel_and_denominator6401
      sigma alpha u0 u1 s t c d hden i
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact extremePair_numerator_outer_natDegree_lt_n6401 s t c.1 d.1
theorem selectedExtremeRows_pairwiseRankOne6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    ∀ s t, ¬ SymbolicRowPairIndependent
      (selectedExtremeRow6401 sigma alpha u0 u1 s)
      (selectedExtremeRow6401 sigma alpha u0 u1 t) := by
  intro s t
  by_cases hst : s = t
  · subst t
    simp [SymbolicRowPairIndependent, symbolicMinor01,
      symbolicRankTwoNumerator, symbolicRankTwoDenominator]
  · let c := selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1
    let d := selectedExtremeKernelCoefficient6401 t sigma alpha u0 u1
    have hden : symbolicRankTwoDenominator
        (extremeCoefficientRowMap6401 s c.1)
        (extremeCoefficientRowMap6401 t d.1) = 0 :=
      extremeKernel_pair_denominator_eq_zero_of_weakSeed_noCurve6401
        sigma alpha u0 u1 hsigma hfixed s t hst c d S A P hSlarge
          hPdegree hrow howner hfail
    have h01 := extreme_minor01_eq_zero_of_kernel_and_denominator6401
      sigma alpha u0 u1 s t c d hden
    have h02 := extreme_numerator_eq_zero_of_kernel_and_denominator6401
      sigma alpha u0 u1 s t c d hden
    rintro (hind | hind | hind)
    · exact hind (by simpa [selectedExtremeRow6401, c, d] using h01)
    · exact hind (by simpa [selectedExtremeRow6401, c, d] using h02)
    · exact hind (by simpa [selectedExtremeRow6401, c, d] using hden)
theorem exists_sourceFaithfulThreeShiftCommonDirection6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    ∃ D : ThreeShiftCommonDirection (F := F),
      D.rows = selectedExtremeRow6401 sigma alpha u0 u1 ∧
      (∀ s z, z ∈ S →
        symbolicRelation sigma (specializeRow z (D.rows s)) (P z) = 0) ∧
      Nonempty (PrimitiveNormalizedThreeShiftDirection D alpha Finset.univ) := by
  classical
  let rows : Fin 3 → SymbolicRow F :=
    selectedExtremeRow6401 sigma alpha u0 u1
  have hrows : ∀ s, rows s ≠ 0 := by
    intro s
    exact selectedExtremeRow_ne_zero6401 sigma alpha u0 u1 s
  have hcaps : ∀ s j,
      (rows s j).natDegree ≤ threeShiftRowXCap6401 s j := by
    intro s j
    exact selectedExtremeRow_natDegree_le6401 sigma alpha u0 u1 s j
  have hrank : ∀ s t,
      ¬ SymbolicRowPairIndependent (rows s) (rows t) :=
    selectedExtremeRows_pairwiseRankOne6401 sigma alpha u0 u1 hsigma hfixed
      S A P hSlarge hPdegree hrow howner hfail
  obtain ⟨direction, multiplier, hdirection, hmultiplier, hfactor⟩ :=
    exists_commonPolynomialDirection_of_pairwiseRankOne rows hrows hrank
  let D : ThreeShiftCommonDirection (F := F) :=
    { rows := rows
      direction := direction
      multiplier := multiplier
      multiplier_ne_zero := hmultiplier
      row_factor := hfactor
      row_caps := hcaps
      direction_nonzero := hdirection }
  refine ⟨D, rfl, ?_, ⟨D.primitiveNormalization alpha Finset.univ⟩⟩
  intro s z hz
  exact extremeKernel_symbolicRelation_eq_zero_of_owner6401
    s sigma alpha u0 u1 hsigma hfixed
      (selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1)
      z (A z) (P z) (hPdegree z hz) (howner z hz) (hrow z hz)
end BCHKSExtremeThreeRectangleProducer6401
end ProximityPrize.SubmissionLower
