import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsRfree

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open RCN002 RCN136 RCN243 RCN264 RCN267 RCN265
open RCN081 RCN095 RCN156 RCN234 RCN275 LocatorDerivativeChain LocatorLowQuotient

noncomputable section

variable {K E : Type} [Field K] [Field E]

abbrev FoldComponent (φ : Polynomial K →+* E) (F : ExceptionPoly K)
    (G : MvPolynomial (Fin 3) E) :=
  RegularComponent E G (surfaceMap φ (dR 1 F)) (surfaceMap φ (dR (chainLength F) F))

theorem fold_component_exists_shifted_carrier
    (φ : Polynomial K →+* E) (F : ExceptionPoly K) (G : MvPolynomial (Fin 3) E)
    (hdiv : G ∣ surfaceMap φ F) (C : FoldComponent φ F G) :
    ∃ j : ℕ, 1 ≤ j ∧ j + 1 ≤ chainLength F ∧
      surfaceMap φ (dR j F) ∈ C.1 ∧ surfaceMap φ (dR (j + 1) F) ∉ C.1 ∧
      (∀ k ≤ j, surfaceMap φ (dR k F) ∈ C.1) ∧
      (wt residualSWeights (dR j F) + 1 ≤ wt residualSWeights F ∧
       wt residualYSWeights (dR j F) + 1 ≤ wt residualYSWeights F ∧
       wt residualTotalWeights (dR j F) + 1 ≤ wt residualTotalWeights F) ∧
      (wt residualSWeights (dR (j + 1) F) + 2 ≤ wt residualSWeights F ∧
       wt residualYSWeights (dR (j + 1) F) + 2 ≤ wt residualYSWeights F ∧
       wt residualTotalWeights (dR (j + 1) F) + 2 ≤ wt residualTotalWeights F) := by
  have hG : G ∈ C.1 := regularComponent_G_mem E _ _ _ C
  have hF : surfaceMap φ F ∈ C.1 := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ]
    exact C.1.mul_mem_right Q hG
  exact fold_exists_first_proper_cut (surfaceMap φ) C.1 F hF
    (regularComponent_T_mem E _ _ _ C) (regularComponent_H_not_mem E _ _ _ C)

variable [IsAlgClosed E] in

theorem fold_component_y_or_z_transcendental
    (φ : Polynomial K →+* E) (F : ExceptionPoly K) (G : MvPolynomial (Fin 3) E)
    (hdiv : G ∣ surfaceMap φ F) (C : FoldComponent φ F G) :
    Transcendental E (coordinate E C.1 0) ∨ Transcendental E (coordinate E C.1 2) := by
  obtain ⟨j, _, _, hj, hnext, _⟩ := fold_component_exists_shifted_carrier φ F G hdiv C
  apply y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap φ (dR j F)) hj
  · rwa [surfaceMap_pderiv_R, ← dR_succ]
  · exact regularComponent_ne_point E _ _ _ C

def shiftedSupport (P : ResidualSupportParameters) (hs : 2 ≤ P.s) (hy : 3 ≤ P.ys) :
    ResidualSupportParameters where
  s := P.s - 1
  ys := P.ys - 1
  total := P.total - 1
  one_le_s := by omega
  s_le_ys := Nat.sub_le_sub_right P.s_le_ys 1
  ys_le_total := Nat.sub_le_sub_right P.ys_le_total 1
  two_le_ys := by omega

def decreasedFlag (P : ResidualSupportParameters) (n : ℕ) : FlagDegree :=
  RCN130.flagFromCaps (P.total - n) (P.ys - n) (P.s - n)

theorem decreasedFlag_cumulative (P : ResidualSupportParameters) (n : ℕ) :
    (decreasedFlag P n).all = P.s - n ∧
      (decreasedFlag P n).yz + (decreasedFlag P n).all = P.ys - n ∧
      (decreasedFlag P n).zOnly + (decreasedFlag P n).yz + (decreasedFlag P n).all =
        P.total - n :=
  RCN130.flagFromCaps_cumulative _ _ _ (Nat.sub_le_sub_right P.s_le_ys n)
    (Nat.sub_le_sub_right P.ys_le_total n)

theorem fold_shifted_support_data (P : ResidualSupportParameters)
    (hs : 2 ≤ P.s) (hy : 3 ≤ P.ys) {F : ExceptionPoly K}
    (hF : ResidualSupportData P F) {j : ℕ} (hj : 1 ≤ j)
    (hsep : dR (j + 1) F ≠ 0) :
    ResidualSupportData (shiftedSupport P hs hy) (dR j F) := by
  have hcarrier : dR j F ≠ 0 := by
    intro hz
    exact hsep (by rw [dR_succ, hz, map_zero])
  obtain ⟨hR, hYR, hAll⟩ := dR_cumulative_drop F j hcarrier
  have hs₀ := hF.s_weight
  have hy₀ := hF.ys_weight
  have ht₀ := hF.total_weight
  constructor <;> change _ ≤ _ - 1 <;> omega

theorem derivative_in_decreasedFlag (φ : Polynomial K →+* E)
    (P : ResidualSupportParameters) {F : ExceptionPoly K}
    (hF : ResidualSupportData P F) (j n : ℕ) (hn : n ≤ j)
    (hderiv : dR j F ≠ 0) :
    PolynomialInFlag (decreasedFlag P n) (surfaceMap φ (dR j F)) := by
  let D := surfaceMap φ (dR j F)
  obtain ⟨hDropS, hDropYS, hDropAll⟩ := dR_cumulative_drop F j hderiv
  obtain ⟨hS, hYS, hAll⟩ := RCN130.surfaceMap_nested_weights_le φ (dR j F)
  have hs₀ := hF.s_weight
  have hy₀ := hF.ys_weight
  have ht₀ := hF.total_weight
  intro d hd
  have hmem := RCN130.polynomialIn_surfaceCumulativeFlag D d hd
  obtain ⟨hs, hy, ht⟩ := RCN130.surfaceCumulativeFlag_cumulative D
  obtain ⟨hs', hy', ht'⟩ := decreasedFlag_cumulative P n
  rw [InFlag, ht, hy, hs] at hmem
  rw [InFlag, ht', hy', hs']
  change MvPolynomial.weightedTotalDegree RCN125.sWeight D ≤ _ at hS
  change MvPolynomial.weightedTotalDegree RCN125.ysWeight D ≤ _ at hYS
  change MvPolynomial.weightedTotalDegree RCN125.totalWeight D ≤ _ at hAll
  exact ⟨Nat.le_sub_of_add_le ((Nat.add_le_add (hmem.1.trans hS) hn).trans (hDropS.trans hs₀)),
    Nat.le_sub_of_add_le ((Nat.add_le_add (hmem.2.1.trans hYS) hn).trans (hDropYS.trans hy₀)),
    Nat.le_sub_of_add_le ((Nat.add_le_add (hmem.2.2.trans hAll) hn).trans (hDropAll.trans ht₀))⟩

theorem fold_separant_in_decreasedFlag (φ : Polynomial K →+* E)
    (P : ResidualSupportParameters) {F : ExceptionPoly K}
    (hF : ResidualSupportData P F) {j : ℕ} (hj : 1 ≤ j)
    (hsep : dR (j + 1) F ≠ 0) :
    PolynomialInFlag (decreasedFlag P 2) (surfaceMap φ (dR (j + 1) F)) :=
  derivative_in_decreasedFlag φ P hF (j + 1) 2 (by omega) hsep

end

end ProximityPrize.SubmissionLower.Koala6831Moving
