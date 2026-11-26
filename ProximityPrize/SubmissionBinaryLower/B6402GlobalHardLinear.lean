import ProximityPrize.SubmissionBinaryLower.B6402CleanFamily
import ProximityPrize.SubmissionBinaryLower.B6402LinearSplit
namespace ProximityPrize.SubmissionBinaryLower.B6402GlobalHardLinear
open Polynomial B6401ContactKerD B6401QuotInterp B6401KerDOrders B6401ResLineOrd B6401ResultantOrd
open B6401Params hiding A
open B6402HybridP64 (A BadOn6402 linePow eval_linePow card_le_of_biPoly_pow arklibBoundPowQ)
open B6402Table4Common B6402Table4NonK B6402Table4K B6402SpecialRouting B6402HardFactor B6402CleanFamily
open B6402BucketBudget B6402LinearSplit B6402FrobeniusCase B6402PointSurplus
open B6401ListAndMCA B6401SmallAlg
open B6401FactorBound (G_val std5Slot wdegBiDom_coeff_le_of_wdeg wdegBiDom_ge_natDegree_mul wdegBiDom_le_of_wdeg_coeff
  resultant_54_ne_zero card_evalZBiPoly_natDegree_lt_le card_evalZ_poly_eq_zero_le degZ_prod_poly_le degZ_mul_poly_le
  degZ_PjZ_le degZ_CjZ_le degZ_BjZ_le PjZ CjZ BjZ makeEscapeUZ makeEscapeUZ_ne_zero makeEscapeUZ_natDegree_le
  makeEscapeUZ_degZ_le triEval_makeEscapeUZ)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
lemma map_PjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (PjZ f_coord j).map (Polynomial.evalRingHom z) = D.Pj j := by
  subst hWF
  unfold PjZ KerD45Data.Pj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

lemma map_CjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (CjZ f_coord j).map (Polynomial.evalRingHom z) = D.Cj j := by
  subst hWF
  unfold CjZ KerD45Data.Cj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

lemma map_BjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (BjZ f_coord j).map (Polynomial.evalRingHom z) = D.Bj j := by
  subst hWF
  unfold BjZ KerD45Data.Bj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

private lemma syzygy_prop_of_minor_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    {P1 C1 B1 P2 C2 B2 p1 c1 b1 p2 c2 b2 : R}
    (h11 : p1 * P1 + c1 * C1 + b1 * B1 = 0) (h12 : p1 * P2 + c1 * C2 + b1 * B2 = 0)
    (h21 : p2 * P1 + c2 * C1 + b2 * B1 = 0) (h22 : p2 * P2 + c2 * C2 + b2 * B2 = 0)
    (hΔ : C1 * B2 + C2 * B1 ≠ 0) :
    p1 * c2 = p2 * c1 ∧ p1 * b2 = p2 * b1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  have hc1 : c1 * (C1 * B2 + C2 * B1) = p1 * (P1 * B2 + P2 * B1) := by
    linear_combination B2 * h11 + B1 * h12 - (p1 * (P1 * B2 + P2 * B1) + b1 * B1 * B2) * h2
  have hc2 : c2 * (C1 * B2 + C2 * B1) = p2 * (P1 * B2 + P2 * B1) := by
    linear_combination B2 * h21 + B1 * h22 - (p2 * (P1 * B2 + P2 * B1) + b2 * B1 * B2) * h2
  have hb1 : b1 * (C1 * B2 + C2 * B1) = p1 * (P1 * C2 + P2 * C1) := by
    linear_combination C2 * h11 + C1 * h12 - (p1 * (P1 * C2 + P2 * C1) + c1 * C1 * C2) * h2
  have hb2 : b2 * (C1 * B2 + C2 * B1) = p2 * (P1 * C2 + P2 * C1) := by
    linear_combination C2 * h21 + C1 * h22 - (p2 * (P1 * C2 + P2 * C1) + c2 * C1 * C2) * h2
  constructor
  · apply mul_right_cancel₀ hΔ
    calc p1 * c2 * (C1 * B2 + C2 * B1) = p1 * (c2 * (C1 * B2 + C2 * B1)) := by ring
      _ = p1 * (p2 * (P1 * B2 + P2 * B1)) := by rw [hc2]
      _ = p2 * (p1 * (P1 * B2 + P2 * B1)) := by ring
      _ = p2 * (c1 * (C1 * B2 + C2 * B1)) := by rw [← hc1]
      _ = p2 * c1 * (C1 * B2 + C2 * B1) := by ring
  · apply mul_right_cancel₀ hΔ
    calc p1 * b2 * (C1 * B2 + C2 * B1) = p1 * (b2 * (C1 * B2 + C2 * B1)) := by ring
      _ = p1 * (p2 * (P1 * C2 + P2 * C1)) := by rw [hb2]
      _ = p2 * (p1 * (P1 * C2 + P2 * C1)) := by ring
      _ = p2 * (b1 * (C1 * B2 + C2 * B1)) := by rw [← hb1]
      _ = p2 * b1 * (C1 * B2 + C2 * B1) := by ring

/-- In char 2, if a `3 × 3` matrix has determinant `0`, then the cofactor vector of any two rows `(r1, r2)`
annihilates all 3 rows! -/
private lemma char2_det3_cofactor_syzygy {R : Type*} [CommRing R] [CharP R 2]
    (P0 P1 P2 C0 C1 C2 B0 B1 B2 : R)
    (hdet : P0 * C1 * B2 + C0 * B1 * P2 + B0 * P1 * C2 + P2 * C1 * B0 + C2 * B1 * P0 + B2 * P1 * C0 = 0) :
    let P : Fin 3 → R := ![P0, P1, P2]
    let C : Fin 3 → R := ![C0, C1, C2]
    let B : Fin 3 → R := ![B0, B1, B2]
    ∀ r1 r2 j : Fin 3,
      (C r1 * B r2 + C r2 * B r1) * P j +
      (P r1 * B r2 + P r2 * B r1) * C j +
      (P r1 * C r2 + P r2 * C r1) * B j = 0 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  intro P C B r1 r2 j
  by_cases h12 : r1 = r2
  · subst h12; simp only [CharTwo.add_self_eq_zero, zero_mul, add_zero]
  · by_cases hj1 : j = r1
    · rw [hj1]
      linear_combination (P r1 * C r1 * B r2 + P r1 * C r2 * B r1 + P r2 * C r1 * B r1) * h2
    · by_cases hj2 : j = r2
      · rw [hj2]
        linear_combination (P r2 * C r1 * B r2 + P r2 * C r2 * B r1 + P r1 * C r2 * B r2) * h2
      · fin_cases r1 <;> fin_cases r2 <;> fin_cases j <;>
          try (exfalso; first | exact h12 rfl | exact hj1 rfl | exact hj2 rfl)
        all_goals (dsimp [P, C, B]; linear_combination hdet)

private lemma char2_det3_eq_sum {R : Type*} [CommRing R] [CharP R 2] (M : Matrix (Fin 3) (Fin 3) R) :
    M.det =
      M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 +
      M 2 0 * M 1 1 * M 0 2 + M 2 1 * M 1 2 * M 0 0 + M 2 2 * M 1 0 * M 0 1 := by
  rw [Matrix.det_fin_three]
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination -(M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 + M 0 2 * M 1 1 * M 2 0) * h2

/-- Convert `p(Z, T), c(Z, T), b(Z, T) ∈ Fld[Z][T]` into the linear-in-`Y` trivariate
`U_Z(Z, X, Y) = (b(Z, X^2) + X * c(Z, X^2)) + p(Z, X^2) * Y : BiPoly (Polynomial Fld)`! -/

theorem hard_labels (bank : Bank)
    (u₀ u₁ : Idx → Fld) {W_F D_ZF q₀ : ℕ} (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hq2_cond : q₀ = 2 → (W_F : ℚ) / (wY : ℚ) < 13 ∧ D_ZF ≤ 1811)
    (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (sourceInvariant : contactDeriv (∑ e : KerDIdx wY W_F 1,cC (f_coord e)*kerDBasisPoly e.1)=0)
    (irr : Irreducible (∑ e : KerDIdx wY W_F 1,cC (f_coord e)*kerDBasisPoly e.1))
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).natDegree = 1)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ q₀ (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z)) (hDZ : D_ZF≤1811)
    (case4 : let f := ∑ e : KerDIdx wY W_F 1,cC (f_coord e)*kerDBasisPoly e.1
             (f.coeff 1).natDegree=4 ∧ (f.coeff 0).natDegree≤5 ∧ (W_F:ℚ)/wY<28/5) :
    (S.card:ℚ)≤linearPrice q₀ := by
  classical
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := fun h0 => hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  have hf1_ne : Fpoly.coeff 1 ≠ 0 := by
    rw [← hFdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hWF_lo : 1 * (wY - 1) ≤ W_F := by
    have h1 := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne; omega
  have hZ_F : ∀ k' j' i', (((Fpoly.coeff k').coeff j').coeff i').natDegree ≤ D_ZF :=
    natDegree_Z_le_of_wYZ hf_wYZ
  have hfc_deg : ∀ e : KerDIdx wY W_F 1, (f_coord e).natDegree ≤ D_ZF := by
    intro e
    by_cases he : f_coord e = 0
    · simp [he]
    · have h1 := coord_wYZ_le_of_wYZ_ne (by norm_num [wY]) f_coord hf_wYZ e he
      omega
  -- Global exact local orders `k i` (independent of `z`!)
  let Loc (i : Idx) : LocalPoly (Polynomial Fld) :=
    ∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) e.1
  have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
    localShift_ne_zero (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) f_coord hFne
  let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
  have hk_exact : ∀ i : Idx, twOrdGE (Loc i) (k i) ∧ (∀ m, k i < m → ∃ p q, p + q = k i ∧ twCoeff (Loc i) p q ≠ 0) :=
    fun i => ⟨twOrdGE_exactTwOrd (hLoc_ne i), fun _ _ => exists_twCoeff_exactTwOrd (hLoc_ne i)⟩
  have hvan_z : ∀ (z : Fld) (i : Idx),
      twOrdGE (∑ e : KerDIdx wY W_F 1,
        locC ((f_coord e).eval z) * kerDLocalPoly (BinaryIRSProfile.domain i) (u₀ i + z ^ q₀ * u₁ i) e.1) (k i) := by
    intro z i
    have h1 := twOrdGE_evalZLocal_sum (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) f_coord z (hk_exact i).1
    simpa only [eval_linePow] using h1
  let f0 := Fpoly.coeff 0
  let f1 := Fpoly.coeff 1
  have hf0_degZ : ∀ j a, ((f0.coeff j).coeff a).natDegree ≤ D_ZF := fun j a => hZ_F 0 j a
  have hf1_degZ : ∀ j a, ((f1.coeff j).coeff a).natDegree ≤ D_ZF := fun j a => hZ_F 1 j a
  have hd0_le25 : f0.natDegree ≤ 25 := by
    by_cases h0 : f0 = 0
    · simp [h0]
    · have hw0 : wdegBiDom wY f0 ≤ W_F := by
        simpa only [Nat.zero_mul, Nat.sub_zero] using wdegBiDom_le_of_wdeg_coeff (le_of_eq hFwdeg) 0
      have h1 := wdegBiDom_ge_natDegree_mul wY f0 h0
      have hwY : wY = 1048575 := rfl
      have hWF_25 : 2 * W_F ≤ 51 * wY := by
        have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
        have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
        exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
      rw [hwY] at hw0 h1 hWF_25
      omega
  have hd1_le25 : f1.natDegree ≤ 25 := by
    have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
      simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
    have hwY : wY = 1048575 := rfl
    have hWF_25 : 2 * W_F ≤ 51 * wY := by
      have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
      have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
      exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
    rw [hwY] at hw1 h1 hWF_25
    omega
  -- Split into Table 4 vs Table 1 globally based on `(f1.natDegree, f0.natDegree, W_F/wY)`!
  change f1.natDegree=4 ∧ f0.natDegree≤5 ∧ (W_F:ℚ)/wY<28/5 at case4
  obtain ⟨hd1_4, hd0_5, hWF_28⟩ := case4
  have ⟨hf0_ne, _, hres_d04⟩ := resY_f0_f1_ne_zero_of_irred_deg1 Fpoly hirr hFdeg (by change 1 ≤ f1.natDegree; omega)
  rw [hd1_4] at hres_d04
  let R54 := Polynomial.resultant f0 f1 5 4
  have hR54_ne : R54 ≠ 0 := resultant_54_ne_zero hd0_5 hd1_4 hf1_ne hres_d04
  have hR54_degZ : ∀ a, (R54.coeff a).natDegree ≤ 9 * D_ZF := fun a => by
    have h9 : (5 + 4) * D_ZF = 9 * D_ZF := by ring
    rw [← h9]
    exact degZ_resultant_biPoly_le f0 f1 5 4 D_ZF hf0_degZ hf1_degZ a
  have hWF_5lo : 5 * wY ≤ W_F + 1 := by
    have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
      simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
    rw [hd1_4] at h1
    have hw : 1 ≤ wY := by norm_num [wY]
    omega
  have hWF_6hi : W_F + 1 < 6 * wY := by
    have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
    have hmul : (W_F : ℚ) * 5 < 28 * (wY : ℚ) := by
      have := (div_lt_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 5)).mp hWF_28; linarith
    have hnat : W_F * 5 < 28 * wY := by exact_mod_cast hmul
    have hw : wY = 1048575 := rfl; omega
  -- Peel off `S_deg`: `f1_z.natDegree ≠ 4` or `R54(z) = 0` (at most `10 * D_ZF` points!)
  let S_bad1 := S.filter fun z => (evalZBiPoly f1 z).natDegree ≠ 4
  let S_bad2 := S.filter fun z => R54.map (Polynomial.evalRingHom z) = 0
  let S_t4 := S.filter fun z => (evalZBiPoly f1 z).natDegree = 4 ∧ R54.map (Polynomial.evalRingHom z) ≠ 0
  have hbad1_card : S_bad1.card ≤ D_ZF := by
    simpa [S_bad1, hd1_4] using card_evalZBiPoly_natDegree_lt_le f1 hf1_ne hf1_degZ S
  have hbad2_card : S_bad2.card ≤ 9 * D_ZF := card_evalZ_poly_eq_zero_le R54 hR54_ne hR54_degZ S
  have hS_split : S.card ≤ S_t4.card + 10 * D_ZF := by
    have hsub : S ⊆ S_t4 ∪ (S_bad1 ∪ S_bad2) := by
      intro z hz; simp only [Finset.mem_union, S_t4, S_bad1, S_bad2, Finset.mem_filter]
      by_cases h1 : (evalZBiPoly f1 z).natDegree = 4
      · by_cases h2 : R54.map (Polynomial.evalRingHom z) = 0
        · exact Or.inr (Or.inr ⟨hz, h2⟩)
        · exact Or.inl ⟨hz, h1, h2⟩
      · exact Or.inr (Or.inl ⟨hz, h1⟩)
    calc S.card ≤ (S_t4 ∪ (S_bad1 ∪ S_bad2)).card := Finset.card_le_card hsub
      _ ≤ S_t4.card + (S_bad1 ∪ S_bad2).card := Finset.card_union_le _ _
      _ ≤ S_t4.card + (S_bad1.card + S_bad2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ S_t4.card + 10 * D_ZF := by omega
  -- Constructor for `KerD45Data` at any `z ∈ S_t4`!
  let mkD (z : Fld) (hz : z ∈ S_t4) : KerD45Data :=
    have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
    have hdeg4 : (evalZBiPoly f1 z).natDegree = 4 := (Finset.mem_filter.mp hz).2.1
    have hRne : R54.map (Polynomial.evalRingHom z) ≠ 0 := (Finset.mem_filter.mp hz).2.2
    have hFz_eq : evalZContact Fpoly z = ∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1 :=
      evalZContact_sum_kerD f_coord z
    have hf1z_eq : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z := by
      rw [← hFz_eq]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
    have hf0z_eq : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z := by
      rw [← hFz_eq]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
    { W_F := W_F
      hWF_lo := hWF_5lo
      hWF_hi := hWF_6hi
      f_coord := fun e => (f_coord e).eval z
      y := fun i => u₀ i + z ^ q₀ * u₁ i
      k := k
      hvan := hvan_z z
      P := P z
      hPdeg := hP z hzS
      Az := Az z
      hAz_card := hcard z hzS
      hagree := fun i hi => (hmatch z hzS i).mp hi
      hFvan := by rw [← hFz_eq]; exact hFvan z hzS
      hf1_deg := by rw [hf1z_eq]; exact hdeg4
      hRes_ne := by
        rw [hf0z_eq, hf1z_eq]
        have hm := Polynomial.resultant_map_map f0 f1 5 4 (Polynomial.mapRingHom (Polynomial.evalRingHom z))
        dsimp only [R54] at hRne
        rw [← Polynomial.coe_mapRingHom, ← hm] at hRne
        exact hRne }
  let f : Model u₀ u₁ q₀ := {
    WF := W_F
    fc := f_coord
    F := Fpoly
    eq := rfl
    fw := hFwdeg
    qz := hf_wYZ.trans hDZ
    slope := hFdeg
    invariant := sourceInvariant
    irreducible := irr
    lifted := hirr
    degree := by
      intro j
      rcases j with _|(_|j)
      · exact hd0_5
      · change f1.natDegree≤5; omega
      · have hd : Fpoly.natDegree=1 := hFdeg
        rw [coeff_eq_zero_of_natDegree_lt (by omega : Fpoly.natDegree<j+2),natDegree_zero]
        omega
    quartic := hd1_4
    lower := by simpa using hWF_lo
    k := k
    ord := fun i => (hk_exact i).1
    exactOrd := fun i => exists_twCoeff_exactTwOrd (hLoc_ne i) }
  let total := singleBudget q₀+(∑ r : Fin 5,groupBudget r q₀)+5*(N*1813)
  have room : (total:ℚ)+100000000000000≤linearPrice q₀ := by
    dsimp only [total]; rcases hq₀ with rfl|rfl <;> decide +kernel
  have dz : (D_ZF:ℚ)≤1811 := by exact_mod_cast hDZ
  have hbound_clean : ∀ S_clean : Finset Fld, ∀ inc : S_clean⊆S_t4,
      (∀ z (hz:z∈S_clean),Assigned (mkD z (inc hz)) (std5Slot (G_val W_F k (Az z)))) →
      (S_clean.card:ℚ)≤total := by
    intro U inc take
    have incl (z:Fld) (hz:z∈U) : z∈S := (Finset.mem_filter.mp (inc hz)).1
    have h := B6402CleanFamily.count bank hq₀ f U P Az (fun z h => hP z (incl z h))
      (fun z h => hcard z (incl z h)) (fun z h => hmatch z (incl z h))
      (fun z h => hFvan z (incl z h)) (fun z h => hbad z (incl z h))
      (fun z h => mkD z (inc h)) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) take
    exact_mod_cast h
  -- Now analyze the global `3 × 3` matrix `MZ` over `Fld[Z][T]`!
  let MZ : Matrix (Fin 3) (Fin 3) (Polynomial (Polynomial Fld)) := Matrix.of fun j c =>
    match c with
    | ⟨0, _⟩ => PjZ f_coord j
    | ⟨1, _⟩ => CjZ f_coord j
    | ⟨2, _⟩ => BjZ f_coord j
  have hMZ_map : ∀ z (hz : z ∈ S_t4), MZ.det.map (Polynomial.evalRingHom z) = (mkD z hz).detM := by
    intro z hz
    rw [← Polynomial.coe_mapRingHom, RingHom.map_det (Polynomial.mapRingHom (Polynomial.evalRingHom z)) MZ]
    unfold KerD45Data.detM KerD45Data.coeffMat
    congr 1; apply Matrix.ext; intro j c; fin_cases c
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
      exact map_PjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
      exact map_CjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
      exact map_BjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
  by_cases hdetZ : MZ.det ≠ 0
  · -- Subcase 1: `MZ.det ≠ 0` globally → at most `3 * D_ZF` roots where `detM_z = 0`!
    have hdet_degZ : ∀ a, (MZ.det.coeff a).natDegree ≤ 3 * D_ZF := by
      intro a; rw [Matrix.det_apply, finset_sum_coeff]
      refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
      dsimp only [Function.comp_apply]
      have hsmul : ∀ (u : ℤˣ) (p : Polynomial (Polynomial Fld)),
          ((u • p).coeff a).natDegree ≤ (p.coeff a).natDegree := fun u p => by
        rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
      refine (hsmul _ _).trans ?_
      refine (degZ_prod_poly_le Finset.univ (fun i => MZ (σ i) i) D_ZF (fun i _ b => ?_) a).trans (by simp)
      dsimp only [MZ, Matrix.of_apply]; fin_cases i
      · exact degZ_PjZ_le f_coord hfc_deg _ b
      · exact degZ_CjZ_le f_coord hfc_deg _ b
      · exact degZ_BjZ_le f_coord hfc_deg _ b
    let S_clean := S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) ≠ 0
    have hbad_det : (S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) = 0).card ≤ 3 * D_ZF :=
      card_evalZ_poly_eq_zero_le MZ.det hdetZ hdet_degZ S_t4
    have hsplit_t4 : S_t4.card ≤ S_clean.card + 3 * D_ZF := by
      have hsub : S_t4 ⊆ S_clean ∪ (S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) = 0) := by
        intro z hz; simp only [Finset.mem_union, S_clean, Finset.mem_filter]
        by_cases h0 : MZ.det.map (Polynomial.evalRingHom z) = 0
        · exact Or.inr ⟨hz, h0⟩
        · exact Or.inl ⟨hz, h0⟩
      have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      omega
    have hcl := hbound_clean S_clean (Finset.filter_subset _ _) (fun z hz => by
      have hzt4 : z ∈ S_t4 := (Finset.mem_filter.mp hz).1
      have hne : (mkD z hzt4).detM ≠ 0 := by rw [← hMZ_map z hzt4]; exact (Finset.mem_filter.mp hz).2
      exact t4_point_det_witness (mkD z hzt4) hWF_28.le hne)
    have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 13 * (D_ZF : ℚ) := by
      have : S.card ≤ S_clean.card + 13 * D_ZF := by omega
      exact_mod_cast this
    linarith only [room,hcl,htot,dz]
  · -- Subcase 2: `MZ.det = 0` globally! Check the 3 `(C, B)` minors!
    push Not at hdetZ
    let minorCB (r1 r2 : Fin 3) : Polynomial (Polynomial Fld) :=
      CjZ f_coord r1 * BjZ f_coord r2 + CjZ f_coord r2 * BjZ f_coord r1
    by_cases hmin_ex : ∃ r1 r2 : Fin 3, minorCB r1 r2 ≠ 0
    · -- Subcase 2a: some `(C, B)` minor `pZ := minorCB r1 r2 ≠ 0`!
      obtain ⟨r1, r2, hpZ_ne⟩ := hmin_ex
      let pZ := minorCB r1 r2
      let cZ := PjZ f_coord r1 * BjZ f_coord r2 + PjZ f_coord r2 * BjZ f_coord r1
      let bZ := PjZ f_coord r1 * CjZ f_coord r2 + PjZ f_coord r2 * CjZ f_coord r1
      have hpZ_degZ : ∀ a, (pZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
        dsimp only [pZ, minorCB]; rw [Polynomial.coeff_add]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · simpa [two_mul] using degZ_mul_poly_le (degZ_CjZ_le f_coord hfc_deg r1) (degZ_BjZ_le f_coord hfc_deg r2) a
        · simpa [two_mul] using degZ_mul_poly_le (degZ_CjZ_le f_coord hfc_deg r2) (degZ_BjZ_le f_coord hfc_deg r1) a
      have hcZ_degZ : ∀ a, (cZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
        dsimp only [cZ]; rw [Polynomial.coeff_add]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r1) (degZ_BjZ_le f_coord hfc_deg r2) a
        · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r2) (degZ_BjZ_le f_coord hfc_deg r1) a
      have hbZ_degZ : ∀ a, (bZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
        dsimp only [bZ]; rw [Polynomial.coeff_add]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r1) (degZ_CjZ_le f_coord hfc_deg r2) a
        · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r2) (degZ_CjZ_le f_coord hfc_deg r1) a
      have hsyzZ : ∀ j : Fin 3, pZ * PjZ f_coord j + cZ * CjZ f_coord j + bZ * BjZ f_coord j = 0 := by
        have hdet_sum := char2_det3_eq_sum MZ
        rw [hdetZ] at hdet_sum
        have hcf := char2_det3_cofactor_syzygy
          (PjZ f_coord 0) (PjZ f_coord 1) (PjZ f_coord 2)
          (CjZ f_coord 0) (CjZ f_coord 1) (CjZ f_coord 2)
          (BjZ f_coord 0) (BjZ f_coord 1) (BjZ f_coord 2)
          (by simpa [MZ] using hdet_sum.symm) r1 r2
        intro j
        have hPeq : ∀ i : Fin 3, (![PjZ f_coord 0, PjZ f_coord 1, PjZ f_coord 2] : Fin 3 → _) i = PjZ f_coord i := fun i => by fin_cases i <;> rfl
        have hCeq : ∀ i : Fin 3, (![CjZ f_coord 0, CjZ f_coord 1, CjZ f_coord 2] : Fin 3 → _) i = CjZ f_coord i := fun i => by fin_cases i <;> rfl
        have hBeq : ∀ i : Fin 3, (![BjZ f_coord 0, BjZ f_coord 1, BjZ f_coord 2] : Fin 3 → _) i = BjZ f_coord i := fun i => by fin_cases i <;> rfl
        simpa [pZ, minorCB, cZ, bZ, hPeq, hCeq, hBeq] using hcf j
      let UZ : BiPoly (Polynomial Fld) := makeEscapeUZ pZ cZ bZ
      let S_p0 := S_t4.filter fun z => pZ.map (Polynomial.evalRingHom z) = 0
      let S_esc := S_t4.filter fun z => triEval UZ z (P z) = 0
      let S_clean := S_t4.filter fun z => pZ.map (Polynomial.evalRingHom z) ≠ 0 ∧ triEval UZ z (P z) ≠ 0
      have hp0_card : S_p0.card ≤ 2 * D_ZF := card_evalZ_poly_eq_zero_le pZ hpZ_ne hpZ_degZ S_t4
      have hesc_card : (S_esc.card : ℚ) ≤ max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ q₀ 1 (2 * D_ZF)) :=
        card_le_of_biPoly_pow u₀ u₁ q₀ (by rcases hq₀ with rfl | rfl <;> omega)
          UZ 1 (2 * D_ZF) (makeEscapeUZ_ne_zero hpZ_ne) (makeEscapeUZ_natDegree_le pZ cZ bZ)
          (makeEscapeUZ_degZ_le hpZ_degZ hcZ_degZ hbZ_degZ)
          S_esc P Az
          (fun z hz => hP z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
          (fun z hz => (Finset.mem_filter.mp hz).2)
          (fun z hz => hcard z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
          (fun z hz i hi => (hmatch z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1 i).mp hi)
          (fun z hz => hbad z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
      have hsplit_t4 : S_t4.card ≤ S_clean.card + S_p0.card + S_esc.card := by
        have hsub : S_t4 ⊆ S_clean ∪ (S_p0 ∪ S_esc) := by
          intro z hz; simp only [Finset.mem_union, S_clean, S_p0, S_esc, Finset.mem_filter]
          by_cases h1 : pZ.map (Polynomial.evalRingHom z) = 0
          · exact Or.inr (Or.inl ⟨hz, h1⟩)
          · by_cases h2 : triEval UZ z (P z) = 0
            · exact Or.inr (Or.inr ⟨hz, h2⟩)
            · exact Or.inl ⟨hz, h1, h2⟩
        calc S_t4.card ≤ (S_clean ∪ (S_p0 ∪ S_esc)).card := Finset.card_le_card hsub
          _ ≤ S_clean.card + (S_p0 ∪ S_esc).card := Finset.card_union_le _ _
          _ ≤ S_clean.card + (S_p0.card + S_esc.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
          _ = S_clean.card + S_p0.card + S_esc.card := by omega
      -- On `S_clean`, `EscapeUZero` is IMPOSSIBLE by `syzygy_prop_of_minor_ne_zero`!
      have hcl := hbound_clean S_clean (Finset.filter_subset _ _) (fun z hz => by
        have hzt4 : z ∈ S_t4 := (Finset.mem_filter.mp hz).1
        have hpz_ne : pZ.map (Polynomial.evalRingHom z) ≠ 0 := (Finset.mem_filter.mp hz).2.1
        have hUz_ne : triEval UZ z (P z) ≠ 0 := (Finset.mem_filter.mp hz).2.2
        rcases t4_point_dichotomy (mkD z hzt4) hWF_28.le with ⟨pz, cz, bz, hpz0, _, hsyz_z, hUP0⟩ | hw
        · exfalso; apply hUz_ne
          rw [triEval_makeEscapeUZ]
          have hm_syz : ∀ j : Fin 3,
              pZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Pj j +
              cZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Cj j +
              bZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Bj j = 0 := fun j => by
            have h := congrArg (Polynomial.map (Polynomial.evalRingHom z)) (hsyzZ j)
            simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_zero,
              map_PjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl),
              map_CjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl),
              map_BjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl)] at h
            exact h
          have hΔ_ne : (mkD z hzt4).Cj r1 * (mkD z hzt4).Bj r2 + (mkD z hzt4).Cj r2 * (mkD z hzt4).Bj r1 ≠ 0 := by
            have h := hpz_ne
            dsimp only [pZ, minorCB] at h
            simpa only [Polynomial.map_add, Polynomial.map_mul,
              map_CjZ f_coord _ z (mkD z hzt4) rfl (fun _ => rfl),
              map_BjZ f_coord _ z (mkD z hzt4) rfl (fun _ => rfl)] using h
          have ⟨hprop_c, hprop_b⟩ := syzygy_prop_of_minor_ne_zero
            (hm_syz r1) (hm_syz r2) (hsyz_z r1) (hsyz_z r2) hΔ_ne
          have hpz_sq_ne : pz.comp (X ^ 2) ≠ 0 := fun h0 => hpz0 ((comp_X_sq_eq_zero_iff pz).mp h0)
          apply mul_left_cancel₀ hpz_sq_ne
          rw [mul_zero]
          have hpc_sq : (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * cz.comp (X ^ 2) =
              pz.comp (X ^ 2) * (cZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) := by
            rw [← mul_comp, ← mul_comp, hprop_c]
          have hpb_sq : (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * bz.comp (X ^ 2) =
              pz.comp (X ^ 2) * (bZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) := by
            rw [← mul_comp, ← mul_comp, hprop_b]
          have hUP0' : pz.comp (X ^ 2) * P z + bz.comp (X ^ 2) + X * cz.comp (X ^ 2) = 0 := hUP0
          linear_combination (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * hUP0' - hpb_sq - X * hpc_sq
        · exact hw)
      have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 12 * (D_ZF : ℚ) + (S_esc.card : ℚ) := by
        have : S.card ≤ S_clean.card + 12 * D_ZF + S_esc.card := by omega
        exact_mod_cast this
      have esc : (S_esc.card:ℚ)≤1000000000000 := by
        rcases hq₀ with rfl|rfl
        · have h := hesc_card.trans (B6402OrdinaryLinear.card_le_of_biPoly_pow_1_bound D_ZF)
          linarith only [h,dz]
        · exact (hesc_card.trans (B6402OrdinaryLinear.card_le_of_biPoly_pow_2_bound hDZ)).trans (by decide)
      linarith only [room,hcl,htot,dz,esc]
    · -- Subcase 2b: ALL `(C, B)` minors vanish globally → EVERY `z ∈ S_t4` satisfies `T4ABranch.p0Zero`!
      push Not at hmin_ex
      have hcl := hbound_clean S_t4 le_rfl (fun z hz => by
        refine t4_point_p0Zero_witness (mkD z hz) hWF_28.le (fun j => ?_)
        have h := congrArg (Polynomial.map (Polynomial.evalRingHom z)) (hmin_ex j 2)
        dsimp only [minorCB] at h
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_zero,
          map_CjZ f_coord _ z (mkD z hz) rfl (fun _ => rfl),
          map_BjZ f_coord _ z (mkD z hz) rfl (fun _ => rfl)] at h
        linear_combination h)
      have htot : (S.card : ℚ) ≤ (S_t4.card : ℚ) + 10 * (D_ZF : ℚ) := by exact_mod_cast hS_split
      linarith only [room,hcl,htot,dz]

#print axioms hard_labels
end ProximityPrize.SubmissionBinaryLower.B6402GlobalHardLinear
