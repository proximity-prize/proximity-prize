import ProximityPrize.SubmissionBinaryLower.Binary6402PointSurplus
import ProximityPrize.SubmissionBinaryLower.B6402FactorCases
/-! The independent quadratic case uses the retuned exact Tables 2 and 3,
with the algebraic reduction of the published binary 6401 submission. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402QuadraticCase
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd B6401KerDOrders B6401KerD2
open B6401Params hiding A
open B6402HybridP64 B6402FarkasVerifier B6402IntFarkas B6402IntSmallCerts B6402CertsT2 B6402CertsT3
open B6402SmallAlg hiding wdegBiDom
open B6401SmallAlg (wdegBiDom)
open B6401ListAndMCA (evalZBiPoly)
open B6401ResLineOrd B6402QuotBridge B6402PointSurplus B6402FactorCases B6402FactorAssembly
open B6401FactorBound (card_evalZBiPoly_natDegree_lt_le card_evalZBiPoly_good_deg_le degZ_resultant_biPoly_le
  card_evalZ_poly_eq_zero_le wdegBiDom_coeff_le_of_wdeg wdegBiDom_le_of_wdeg_coeff wdegBiDom_ge_natDegree_mul)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators
set_option maxHeartbeats 2500000
local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
lemma checkCapWitness_d2_no_p64 {m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ : ℕ} {w : CapWitness}
    (h : checkCapWitness 2 m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ w = true) :
    w.useP64 = false := by
  cases hu : w.useP64
  · rfl
  · exfalso
    unfold checkCapWitness at h
    by_cases hbad : (m == 0 || s < 2 || cHiDen == 0 || δNum == 0 || δDen == 0 || hiGDen == 0) = true
    · simp only [hbad, ↓reduceIte] at h; cases h
    · simp only [hbad, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      have hs := h.1
      unfold checkSideP64 at hs
      simp at hs

lemma card_le_of_biPoly_pow_deg2_bound {B D_ZF : ℕ} (hB : B ≤ 24) (hDZ : D_ZF ≤ 1811) :
    max (D_ZF : ℚ) (arklibBoundPowQ 1 B D_ZF) ≤ (4000000000000 : ℚ) := by
  have hBQ : (B : ℚ) ≤ 24 := by exact_mod_cast hB
  have hB0 : (0 : ℚ) ≤ (B : ℚ) := Nat.cast_nonneg B
  have hDZQ : (D_ZF : ℚ) ≤ 1811 := by exact_mod_cast hDZ
  have hDZ0 : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
  apply max_le
  · linarith
  · unfold arklibBoundPowQ
    have hsub0 : B - (2 * wY + 1) = 0 := by norm_num [wY]; omega
    rw [hsub0, Nat.cast_zero]
    have hmul : (B : ℚ) * (D_ZF : ℚ) ≤ 24 * 1811 :=
      mul_le_mul hBQ hDZQ hDZ0 (by norm_num)
    norm_num [N, wY, A]
    ring_nf at hmul ⊢
    linarith [hmul, hBQ, hDZ0]

theorem deg2_factor_card_le
    (u₀ u₁ : Idx → Fld) {W_F D_ZF : ℕ}
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hDZ_le : D_ZF ≤ 1811)
    (f_coord : KerDIdx wY W_F 2 → Polynomial Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).natDegree = 2)
    (hf1_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ 1 (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ ((T3_CAP_BOUND + 8000000200200 : ℕ) : ℚ) := by
  classical
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := fun h0 => hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  have hf2_ne : Fpoly.coeff 2 ≠ 0 := by
    rw [← hFdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hWF_lo : 2 * (wY - 1) ≤ W_F := by
    have h1 := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 2 hf2_ne; omega
  have hZ_F : ∀ k' j' i', (((Fpoly.coeff k').coeff j').coeff i').natDegree ≤ D_ZF :=
    natDegree_Z_le_of_wYZ hf_wYZ
  let f0 := Fpoly.coeff 0
  let f1 := Fpoly.coeff 1
  let f2 := Fpoly.coeff 2
  have hWF_25 : 2 * W_F ≤ 51 * wY := by
    have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
    have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
    exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
  have hd0_le25 : f0.natDegree ≤ 25 := by
    by_cases h0 : f0 = 0
    · simp [h0]
    · have hw0 : wdegBiDom wY f0 ≤ W_F := by
        simpa only [Nat.zero_mul, Nat.sub_zero] using wdegBiDom_le_of_wdeg_coeff (le_of_eq hFwdeg) 0
      have h1 := wdegBiDom_ge_natDegree_mul wY f0 h0
      have hwY : wY = 1048575 := rfl
      rw [hwY] at hw0 h1 hWF_25; omega
  have hd1_le24 : f1.natDegree ≤ 24 := by
    have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
      simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
    have hwY : wY = 1048575 := rfl
    rw [hwY] at hw1 h1 hWF_25; omega
  have hd2_le24 : f2.natDegree ≤ 24 := by
    have hw2 : wdegBiDom wY f2 + 2 * (wY - 1) ≤ W_F := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 2 hf2_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f2 hf2_ne
    have hwY : wY = 1048575 := rfl
    rw [hwY] at hw2 h1 hWF_25; omega
  obtain ⟨hf0_ne, t, hht_ne, hres_ne⟩ := exists_t_resY_ne_zero_of_irred_deg2 Fpoly hirr hFdeg hf1_ne hf2_ne hd0_le25
  let ht : BiPoly (Polynomial Fld) := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
  have hht_deg : ht.natDegree ≤ 24 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le hd1_le24 ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans hd2_le24
  have hht_degZ : ∀ j a, ((ht.coeff j).coeff a).natDegree ≤ D_ZF := by
    intro j a
    dsimp only [ht]
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (hZ_F 1 j a) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hZ_F 2 j a)
  let R : Polynomial (Polynomial Fld) := Polynomial.resultant f0 ht f0.natDegree ht.natDegree
  -- Peel off `f1(z, P z) = 0`, `f2(z, P z) = 0`, `f0_z deg drop`, `ht_z deg drop`, `R(z) = 0`!
  let S_f1 := S.filter fun z => triEval f1 z (P z) = 0
  let S_f2 := S.filter fun z => triEval f2 z (P z) = 0
  let S_d0 := S.filter fun z => ¬ (evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree)
  let S_dh := S.filter fun z => ¬ (evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree)
  let S_R := S.filter fun z => R.map (Polynomial.evalRingHom z) = 0
  let S_clean := S.filter fun z =>
    triEval f1 z (P z) ≠ 0 ∧ triEval f2 z (P z) ≠ 0 ∧
    (evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree) ∧
    (evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree) ∧
    R.map (Polynomial.evalRingHom z) ≠ 0
  have hmatch1 : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ 1 * u₁ i := fun z hz i hi => by
    simpa only [pow_one] using (hmatch z hz i).mp hi
  have hSf1_card : (S_f1.card : ℚ) ≤ (4000000000000 : ℚ) :=
    (card_le_of_biPoly_pow u₀ u₁ 1 le_rfl f1 24 D_ZF hf1_ne hd1_le24 (fun j a => hZ_F 1 j a)
      S_f1 P Az (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hcard z (Finset.mem_filter.mp hz).1) (fun z hz => hmatch1 z (Finset.mem_filter.mp hz).1)
      (fun z hz => hbad z (Finset.mem_filter.mp hz).1)).trans (card_le_of_biPoly_pow_deg2_bound le_rfl hDZ_le)
  have hSf2_card : (S_f2.card : ℚ) ≤ (4000000000000 : ℚ) :=
    (card_le_of_biPoly_pow u₀ u₁ 1 le_rfl f2 24 D_ZF hf2_ne hd2_le24 (fun j a => hZ_F 2 j a)
      S_f2 P Az (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hcard z (Finset.mem_filter.mp hz).1) (fun z hz => hmatch1 z (Finset.mem_filter.mp hz).1)
      (fun z hz => hbad z (Finset.mem_filter.mp hz).1)).trans (card_le_of_biPoly_pow_deg2_bound le_rfl hDZ_le)
  have hSd0_card : S_d0.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f0 hf0_ne (fun j a => hZ_F 0 j a) S
  have hSdh_card : S_dh.card ≤ D_ZF := card_evalZBiPoly_good_deg_le ht hht_ne hht_degZ S
  have hSR_card : S_R.card ≤ 49 * D_ZF :=
    (card_evalZ_poly_eq_zero_le R hres_ne
      (B6401FactorBound.degZ_resultant_biPoly_le f0 ht f0.natDegree ht.natDegree D_ZF (fun j a => hZ_F 0 j a) hht_degZ) S).trans
      (Nat.mul_le_mul_right D_ZF (by omega))
  have hS_split : S.card ≤ S_clean.card + S_f1.card + S_f2.card + S_d0.card + S_dh.card + S_R.card := by
    have hsub : S ⊆ S_clean ∪ (S_f1 ∪ (S_f2 ∪ (S_d0 ∪ (S_dh ∪ S_R)))) := by
      intro z hz; simp only [Finset.mem_union, S_clean, S_f1, S_f2, S_d0, S_dh, S_R, Finset.mem_filter]
      by_cases h1 : triEval f1 z (P z) = 0
      · exact Or.inr (Or.inl ⟨hz, h1⟩)
      · by_cases h2 : triEval f2 z (P z) = 0
        · exact Or.inr (Or.inr (Or.inl ⟨hz, h2⟩))
        · by_cases h3 : evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree
          · by_cases h4 : evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree
            · by_cases h5 : R.map (Polynomial.evalRingHom z) = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz, h5⟩))))
              · exact Or.inl ⟨hz, h1, h2, h3, h4, h5⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz, h4⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hz, h3⟩)))
    have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _)) _)) _))
    omega
  -- Global exact local orders `k i`!
  let Loc (i : Idx) : LocalPoly (Polynomial Fld) :=
    ∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ 1 i) e.1
  have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
    localShift_ne_zero (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ 1 i) f_coord hFne
  let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
  have hk_exact : ∀ i : Idx, twOrdGE (Loc i) (k i) ∧ (∀ m, k i < m → ∃ p q, p + q = k i ∧ twCoeff (Loc i) p q ≠ 0) :=
    fun i => ⟨twOrdGE_exactTwOrd (hLoc_ne i), fun _ _ => exists_twCoeff_exactTwOrd (hLoc_ne i)⟩
  have hS_clean_card : (S_clean.card : ℚ) ≤ (T3_CAP_BOUND : ℚ) := by
    by_cases hemp : S_clean.Nonempty
    · obtain ⟨z0, hz0⟩ := hemp
      obtain ⟨hz0S, hf1P, hf2P, ⟨hf0z_ne, hd0z⟩, ⟨hhtz_ne, hdhz⟩, hRz_ne⟩ := Finset.mem_filter.mp hz0
      have hFz0 : evalZContact Fpoly z0 = ∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1 :=
        evalZContact_sum_kerD f_coord z0
      have hf0z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
      have hf1z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
      have hf2z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 2 = evalZBiPoly f2 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f2]
      have hhtz_eq : evalZBiPoly ht z0 = evalZBiPoly f1 z0 + Polynomial.C (Polynomial.C t) * evalZBiPoly f2 z0 := by
        unfold evalZBiPoly ht; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
      have hcop_all : ∀ p : Polynomial (RatFunc Fld),
          p ∣ (evalZBiPoly f0 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          p ∣ (evalZBiPoly f1 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          p ∣ (evalZBiPoly f2 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          IsUnit p := by
        intro p hp0 hp1 hp2
        let ι : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
        have hι : Function.Injective ι := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
        have hp_ht : p ∣ (evalZBiPoly ht z0).map ι := by
          rw [hhtz_eq, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
          exact dvd_add hp1 (dvd_mul_of_dvd_right hp2 _)
        have hres_z : Polynomial.resultant (evalZBiPoly f0 z0) (evalZBiPoly ht z0)
            (evalZBiPoly f0 z0).natDegree (evalZBiPoly ht z0).natDegree ≠ 0 := by
          rw [hd0z, hdhz]
          have hm := Polynomial.resultant_map_map f0 ht f0.natDegree ht.natDegree
            (Polynomial.mapRingHom (Polynomial.evalRingHom z0))
          dsimp only [R] at hRz_ne
          rw [← Polynomial.coe_mapRingHom, ← hm] at hRz_ne
          exact hRz_ne
        have hres_rat : Polynomial.resultant ((evalZBiPoly f0 z0).map ι) ((evalZBiPoly ht z0).map ι)
            ((evalZBiPoly f0 z0).map ι).natDegree ((evalZBiPoly ht z0).map ι).natDegree ≠ 0 := by
          rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
            Polynomial.resultant_map_map]
          exact fun h0 => hres_z (hι (h0.trans (map_zero ι).symm))
        by_contra hnu
        apply hres_rat
        have hf0L_ne : (evalZBiPoly f0 z0).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf0z_ne
        have hhtL_ne : (evalZBiPoly ht z0).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hhtz_ne
        have hp_ne : p ≠ 0 := fun h0 => hf0L_ne (zero_dvd_iff.mp (h0 ▸ hp0))
        have hp_pos : 0 < p.natDegree := Nat.pos_of_ne_zero fun h0 =>
          hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hp_ne, h0]; rfl))
        rcases hp0 with ⟨a, ha⟩
        rcases hp_ht with ⟨b, hb⟩
        have ha_ne : a ≠ 0 := fun h0 => hf0L_ne (by rw [ha, h0, mul_zero])
        have hb_ne : b ≠ 0 := fun h0 => hhtL_ne (by rw [hb, h0, mul_zero])
        have hres_pp : Polynomial.resultant p p p.natDegree p.natDegree = 0 := by
          have h0 := resultant_add_mul_right_deg (0 : Polynomial (RatFunc Fld)) p 1 p.natDegree p.natDegree
            (by simp) (by simp) rfl
          rw [zero_add, one_mul] at h0; rw [h0]
          exact Matrix.det_eq_zero_of_column_eq_zero (Fin.natAdd p.natDegree ⟨0, hp_pos⟩)
            (fun _ => by simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]; split_ifs <;> simp)
        rw [ha, hb, Polynomial.natDegree_mul hp_ne ha_ne, Polynomial.natDegree_mul hp_ne hb_ne,
          Polynomial.resultant_mul_left p a (p * b) (p.natDegree + b.natDegree) (by rw [Polynomial.natDegree_mul hp_ne hb_ne]),
          Polynomial.resultant_mul_right p p b p.natDegree le_rfl, hres_pp, zero_mul, zero_mul]
      have hvan_z0 : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 2,
          locC ((f_coord e).eval z0) * kerDLocalPoly (BinaryIRSProfile.domain i) (u₀ i + z0 * u₁ i) e.1) (k i) := fun i => by
        have h1 := twOrdGE_evalZLocal_sum (BinaryIRSProfile.domain i) (linePow u₀ u₁ 1 i) f_coord z0 (hk_exact i).1
        simpa [eval_linePow] using h1
      have hf1z_ne : evalZBiPoly f1 z0 ≠ 0 := fun h0 => hf1P (by change (evalZBiPoly f1 z0).eval (P z0) = 0; rw [h0, Polynomial.eval_zero])
      have hf2z_ne : evalZBiPoly f2 z0 ≠ 0 := fun h0 => hf2P (by change (evalZBiPoly f2 z0).eval (P z0) = 0; rw [h0, Polynomial.eval_zero])
      obtain ⟨m, s, cHiN, cHiD, δN, δD, w, hm, _, hs, _, hcHiD, hδN, hδD, hcHi, hsurp, hcap, hcap_bd⟩ :=
        t23_surplus_of_point (fun e => (f_coord e).eval z0) (fun i => u₀ i + z0 * u₁ i) k
          hvan_z0 (P z0) (hP z0 hz0S) (Az z0) (hcard z0 hz0S) (fun i hi => (hmatch z0 hz0S i).mp hi)
          (by rw [hf1z]; exact hf1z_ne) (by rw [hf2z]; exact hf2z_ne)
          (by rw [hf1z]; exact hf1P) (by rw [hf2z]; exact hf2P)
          hWF_hi (by simpa only [hf0z, hf1z, hf2z] using hcop_all)
      have hnop64 : w.useP64 = false := checkCapWitness_d2_no_p64 hcap
      have hcard_cl := card_le_of_quotient_surplus u₀ u₁ w hcap (Or.inl rfl) (by omega) hs hm
        hcHiD hδN hδD (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
        (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩) hsurp S_clean P Az
        (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => hFvan z (Finset.mem_filter.mp hz).1)
        (fun z hz => hcard z (Finset.mem_filter.mp hz).1)
        (fun z hz i => by simpa only [pow_one] using hmatch z (Finset.mem_filter.mp hz).1 i)
        (fun z hz => hbad z (Finset.mem_filter.mp hz).1) (fun h => by rw [hnop64] at h; cases h)
      have hDZQ : (D_ZF : ℚ) ≤ 1811 := by exact_mod_cast hDZ_le
      have hle : (w.c1Bkt : ℚ) * 1811 + (w.c0Bkt : ℚ) ≤ (T3_CAP_BOUND : ℚ) := by exact_mod_cast hcap_bd
      nlinarith [Nat.cast_nonneg (α := ℚ) w.c1Bkt]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]; positivity
  have hsplitQ : (S.card : ℚ) ≤ (S_clean.card : ℚ) + (S_f1.card : ℚ) + (S_f2.card : ℚ) +
      (S_d0.card : ℚ) + (S_dh.card : ℚ) + (S_R.card : ℚ) := by exact_mod_cast hS_split
  have hd0Q : (S_d0.card : ℚ) ≤ 1811 := by exact_mod_cast (hSd0_card.trans hDZ_le)
  have hdhQ : (S_dh.card : ℚ) ≤ 1811 := by exact_mod_cast (hSdh_card.trans hDZ_le)
  have hRQ : (S_R.card : ℚ) ≤ 49 * 1811 := by exact_mod_cast (hSR_card.trans (Nat.mul_le_mul_left 49 hDZ_le))
  push_cast; linarith

theorem quadratic : QuadraticCount := by
  intro u₀ u₁ F hirr dF hd hf1 hw hz S P Az hP hmatch onF
  let W := wdeg wY F
  obtain ⟨c,ec,_⟩ := (mem_kerD_iff_exists_unique_coords (wY:=wY) (W:=W) (s:=2) (by decide) F).mp ⟨dF,hd.le,le_rfl⟩
  have hW : (W:ℚ)/(wY:ℚ)≤51/2 := by
    rw [div_le_iff₀ (by decide : (0:ℚ)<wY)]
    have hc : (W:ℚ)≤26689499 := by exact_mod_cast hw
    norm_num [wY]; linarith
  have cost := deg2_factor_card_le u₀ u₁ hW le_rfl c
    (ec ▸ B6401Main.irreducible_liftCRat_of_irred hirr (by omega)) (ec ▸ hd)
    (ec ▸ hf1) (by rw [←ec]) (ec ▸ hz) S P Az (fun z h => (hP z h).1) (ec ▸ onF)
    (fun z h => (hP z h).2.1) hmatch (fun z h => (hP z h).2.2)
  have hbound : (S.card:ℚ)≤2*factorCap := cost.trans (by decide +kernel)
  exact_mod_cast hbound

#print axioms quadratic
end ProximityPrize.SubmissionBinaryLower.B6402QuadraticCase
