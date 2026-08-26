import ProximityPrize.SubmissionLower.BCHKSFiniteRankOnePrincipalization6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSThreeShiftSourceWindow6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
def homogeneousDirectionCap6401 : Nat := 22507
def primitiveSourceWindow6401 : Nat :=
  a6401 - homogeneousDirectionCap6401
theorem primitiveSourceWindow_exact6401 :
    primitiveSourceWindow6401 = 162847 ∧
      ownerDegreeCap6401 + 31776 = primitiveSourceWindow6401 ∧
      homogeneousDirectionCap6401 + ownerDegreeCap6401 + 9269 =
        primitiveSourceWindow6401 := by
  norm_num [primitiveSourceWindow6401, homogeneousDirectionCap6401,
    a6401, ownerDegreeCap6401]
theorem card_filter_evalOuterAt_eq_zero_le_natDegree
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (alpha : ι ↪ F) (A : Finset ι) (M : XOverZ F) (hM : M ≠ 0) :
    (A.filter fun i => evalOuterAt (alpha i) M = 0).card ≤ M.natDegree := by
  let Q : XOverZ F := Polynomial.Bivariate.swap M
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hM
    have := congrArg Polynomial.Bivariate.swap hzero
    simpa [Q, Polynomial.Bivariate.swap_swap_apply] using this
  obtain ⟨b, _hb, hcard⟩ :=
    card_zero_specializations_le_coefficient_degree (A.map alpha) Q hQ
  have heval (x : F) : specializeCoeffZ x Q = evalOuterAt x M := by
    dsimp [Q]
    unfold evalOuterAt
    simpa [Polynomial.aeval_def] using
      (Polynomial.Bivariate.aveal_eq_map_swap (R := F) x M).symm
  have hfilter :
      ((A.filter fun i => evalOuterAt (alpha i) M = 0).map alpha) =
        (A.map alpha).filter fun x => specializeCoeffZ x Q = 0 := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨hiA, hizero⟩, rfl⟩
      exact ⟨⟨i, hiA, rfl⟩, by simpa [heval] using hizero⟩
    · rintro ⟨⟨i, hiA, hix⟩, hxzero⟩
      subst x
      exact ⟨i, ⟨hiA, by simpa [heval] using hxzero⟩, rfl⟩
  rw [← hfilter, Finset.card_map] at hcard
  exact hcard.trans <| (coeff_natDegree_le_swap_natDegree Q b).trans <| by
    dsimp [Q]
    rw [Polynomial.Bivariate.swap_swap_apply]
theorem cancel_sourceRelation_of_commonDirection
    {F : Type*} [Field F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (x u0 u1 : F) (s : Fin 3)
    (hmultiplier : evalOuterAt x (D.multiplier s) ≠ 0)
    (hrow : symbolicCoordinateRelation sigma x u0 u1 (D.rows s) = 0) :
    symbolicCoordinateRelation sigma x u0 u1 D.direction = 0 := by
  have h0 : evalOuterAt x (D.rows s 0) =
      evalOuterAt x (D.multiplier s) * evalOuterAt x (D.direction 0) := by
    simpa [evalOuterAt] using congrArg (evalOuterAt x) (D.row_factor s 0)
  have h1 : evalOuterAt x (D.rows s 1) =
      evalOuterAt x (D.multiplier s) * evalOuterAt x (D.direction 1) := by
    simpa [evalOuterAt] using congrArg (evalOuterAt x) (D.row_factor s 1)
  have h2 : evalOuterAt x (D.rows s 2) =
      evalOuterAt x (D.multiplier s) * evalOuterAt x (D.direction 2) := by
    simpa [evalOuterAt] using congrArg (evalOuterAt x) (D.row_factor s 2)
  unfold symbolicCoordinateRelation at hrow ⊢
  rw [h0, h1, h2] at hrow
  apply mul_left_cancel₀ hmultiplier
  linear_combination hrow
theorem primitive_homogeneous_evaluations_not_both_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (i : ι) (hi : i ∈ I) (u0 u1 : F)
    (hsource : symbolicCoordinateRelation sigma (alpha i) u0 u1
      R.reduced = 0) :
    evalOuterAt (alpha i) (R.reduced 1) ≠ 0 ∨
      evalOuterAt (alpha i) (R.reduced 2) ≠ 0 := by
  by_contra hhomogeneous
  push Not at hhomogeneous
  have hzero : ∀ j,
      evalOuterAt (alpha i) (R.reduced j) = 0 := by
    intro j
    fin_cases j
    · unfold symbolicCoordinateRelation at hsource
      rw [hhomogeneous.1, hhomogeneous.2] at hsource
      simpa using hsource
    · exact hhomogeneous.1
    · exact hhomogeneous.2
  exact R.primitive_at_coordinates i hi hzero
theorem primitive_first_homogeneous_evaluation_ne_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    {B : SymbolicRow F} {pivot : Fin 3}
    {alpha : ι ↪ F} {I : Finset ι}
    (R : PrimitiveThreeShiftFrame B pivot alpha I)
    (sigma : F →+* F) (i : ι) (hi : i ∈ I) (u0 u1 : F)
    (hsource : symbolicCoordinateRelation sigma (alpha i) u0 u1
      R.reduced = 0)
    (hconjugateZero : evalOuterAt (alpha i) (R.reduced 1) = 0 →
      evalOuterAt (alpha i) (R.reduced 2) = 0) :
    evalOuterAt (alpha i) (R.reduced 1) ≠ 0 := by
  intro hzero
  rcases primitive_homogeneous_evaluations_not_both_zero
      R sigma i hi u0 u1 hsource with hfirst | hsecond
  · exact hfirst hzero
  · exact hsecond (hconjugateZero hzero)
theorem homogeneous_ne_zero_of_sourceRelations
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsource : ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0) :
    D.direction 1 ≠ 0 ∨ D.direction 2 ≠ 0 := by
  by_contra hhom
  push Not at hhom
  have hdir0 : D.direction 0 ≠ 0 := by
    intro hzero
    apply D.direction_nonzero
    funext j
    fin_cases j
    · exact hzero
    · exact hhom.1
    · exact hhom.2
  have hrow0 : D.rows 0 0 ≠ 0 := by
    rw [D.row_factor 0 0]
    exact mul_ne_zero (D.multiplier_ne_zero 0) hdir0
  have hvanish : ∀ i,
      evalOuterAt (alpha i) (D.rows 0 0) = 0 := by
    intro i
    have hs := hsource 0 i
    have hrow1 : D.rows 0 1 = 0 := by
      rw [D.row_factor 0 1, hhom.1, mul_zero]
    have hrow2 : D.rows 0 2 = 0 := by
      rw [D.row_factor 0 2, hhom.2, mul_zero]
    unfold symbolicCoordinateRelation at hs
    rw [hrow1, hrow2] at hs
    simpa [evalOuterAt] using hs
  have hbad := card_filter_evalOuterAt_eq_zero_le_natDegree
    alpha Finset.univ (D.rows 0 0) hrow0
  have hfilter :
      (Finset.univ.filter fun i : Fin n6401 =>
        evalOuterAt (alpha i) (D.rows 0 0) = 0) = Finset.univ :=
    Finset.filter_eq_self.mpr (by simpa using hvanish)
  rw [hfilter, Finset.card_univ, Fintype.card_fin] at hbad
  have hdegree := D.row_caps 0 0
  have hcap : threeShiftRowXCap6401 0 0 = 153578 := by decide
  rw [hcap] at hdegree
  norm_num [n6401] at hbad
  omega
theorem exists_homogeneous_diagonal_multiplier
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsource : ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0) :
    ∃ s : Fin 3,
      (s = 1 ∨ s = 2) ∧ D.direction s ≠ 0 ∧
        (D.multiplier s).natDegree ≤ homogeneousDirectionCap6401 := by
  rcases homogeneous_ne_zero_of_sourceRelations D sigma alpha u0 u1 hsource
      with h1 | h2
  · refine ⟨1, Or.inl rfl, h1, ?_⟩
    have hdegree := D.row_caps 1 1
    rw [D.row_factor 1 1,
      Polynomial.natDegree_mul (D.multiplier_ne_zero 1) h1] at hdegree
    simpa [homogeneousDirectionCap6401, threeShiftRowXCap6401] using
      (Nat.le_add_right (D.multiplier 1).natDegree
        (D.direction 1).natDegree |>.trans hdegree)
  · refine ⟨2, Or.inr rfl, h2, ?_⟩
    have hdegree := D.row_caps 2 2
    rw [D.row_factor 2 2,
      Polynomial.natDegree_mul (D.multiplier_ne_zero 2) h2] at hdegree
    simpa [homogeneousDirectionCap6401, threeShiftRowXCap6401] using
      (Nat.le_add_right (D.multiplier 2).natDegree
        (D.direction 2).natDegree |>.trans hdegree)
theorem exists_commonDirection_sourceWindow6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsource : ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0)
    (A : Finset (Fin n6401)) :
    ∃ s : Fin 3,
      (s = 1 ∨ s = 2) ∧ D.direction s ≠ 0 ∧
      (D.multiplier s).natDegree ≤ homogeneousDirectionCap6401 ∧
      (A.filter fun i =>
        evalOuterAt (alpha i) (D.multiplier s) = 0).card ≤
          homogeneousDirectionCap6401 ∧
      ∀ i ∈ A,
        evalOuterAt (alpha i) (D.multiplier s) ≠ 0 →
          symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
            D.direction = 0 := by
  obtain ⟨s, hs, hdirection, hdegree⟩ :=
    exists_homogeneous_diagonal_multiplier D sigma alpha u0 u1 hsource
  refine ⟨s, hs, hdirection, hdegree, ?_, ?_⟩
  · exact (card_filter_evalOuterAt_eq_zero_le_natDegree alpha A
      (D.multiplier s) (D.multiplier_ne_zero s)).trans hdegree
  · intro i _hi hmultiplier
    exact cancel_sourceRelation_of_commonDirection D sigma
      (alpha i) (u0 i) (u1 i) s
      hmultiplier (hsource s i)
theorem exists_primitive_sourceWindow6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsource : ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0)
    (A : Finset (Fin n6401)) (hA : a6401 ≤ A.card) :
    ∃ (s : Fin 3)
      (R : PrimitiveThreeShiftFrame D.direction s alpha Finset.univ),
      (s = 1 ∨ s = 2) ∧
      primitiveSourceWindow6401 ≤
        (A.filter fun i =>
          evalOuterAt (alpha i) (D.multiplier s) ≠ 0 ∧
          evalOuterAt (alpha i) R.commonFactor ≠ 0).card ∧
      ∀ i ∈ A,
        evalOuterAt (alpha i) (D.multiplier s) ≠ 0 →
        evalOuterAt (alpha i) R.commonFactor ≠ 0 →
          symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
            R.reduced = 0 := by
  obtain ⟨s, hs, hdirection, hmultiplierDegree, hbadMultiplier,
      hdirectionSource⟩ :=
    exists_commonDirection_sourceWindow6401 D sigma alpha u0 u1 hsource A
  let R : PrimitiveThreeShiftFrame D.direction s alpha Finset.univ :=
    primitiveThreeShiftFrame D.direction s alpha Finset.univ hdirection
  let combinedFactor : XOverZ F := D.multiplier s * R.commonFactor
  have hcombinedNe : combinedFactor ≠ 0 :=
    mul_ne_zero (D.multiplier_ne_zero s) R.commonFactor_monic.ne_zero
  have hrowFactor :
      D.rows s s = combinedFactor * R.reduced s := by
    calc
      D.rows s s = D.multiplier s * D.direction s := D.row_factor s s
      _ = D.multiplier s * (R.commonFactor * R.reduced s) := by
        rw [R.component_factor s]
      _ = combinedFactor * R.reduced s := by
        simp [combinedFactor, mul_assoc]
  have hcombinedDegree : combinedFactor.natDegree ≤
      homogeneousDirectionCap6401 := by
    have hdegree := D.row_caps s s
    rw [hrowFactor,
      Polynomial.natDegree_mul hcombinedNe R.pivot_ne_zero] at hdegree
    have hcap : threeShiftRowXCap6401 s s =
        homogeneousDirectionCap6401 := by
      rcases hs with rfl | rfl <;> decide
    rw [hcap] at hdegree
    exact (Nat.le_add_right combinedFactor.natDegree
      (R.reduced s).natDegree).trans hdegree
  let Bad : Finset (Fin n6401) := A.filter fun i =>
    evalOuterAt (alpha i) combinedFactor = 0
  have hbad : Bad.card ≤ homogeneousDirectionCap6401 := by
    exact (card_filter_evalOuterAt_eq_zero_le_natDegree alpha A
      combinedFactor hcombinedNe).trans hcombinedDegree
  let Good : Finset (Fin n6401) := A.filter fun i =>
    evalOuterAt (alpha i) combinedFactor ≠ 0
  have hcover : A ⊆ Good ∪ Bad := by
    intro i hi
    by_cases hzero : evalOuterAt (alpha i) combinedFactor = 0
    · simp [Bad, hi, hzero]
    · simp [Good, hi, hzero]
  have hcardCover : A.card ≤ Good.card + Bad.card := by
    calc
      A.card ≤ (Good ∪ Bad).card := Finset.card_le_card hcover
      _ ≤ Good.card + Bad.card := Finset.card_union_le _ _
  have hgood : primitiveSourceWindow6401 ≤ Good.card := by
    dsimp [Good, Bad] at hcardCover hbad ⊢
    norm_num [primitiveSourceWindow6401, homogeneousDirectionCap6401,
      a6401] at hA hbad ⊢
    omega
  refine ⟨s, R, hs, ?_, ?_⟩
  · have hGoodEq : Good = A.filter fun i =>
        evalOuterAt (alpha i) (D.multiplier s) ≠ 0 ∧
          evalOuterAt (alpha i) R.commonFactor ≠ 0 := by
      ext i
      simp [Good, combinedFactor, evalOuterAt]
    rw [← hGoodEq]
    exact hgood
  · intro i hi hmultiplier hfactor
    exact R.cancel_coordinate_relation sigma (alpha i) (u0 i) (u1 i)
      hfactor (hdirectionSource i hi hmultiplier)
end BCHKSThreeShiftSourceWindow6401
end ProximityPrize.SubmissionLower
