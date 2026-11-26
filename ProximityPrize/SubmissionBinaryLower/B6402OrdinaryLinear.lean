import ProximityPrize.SubmissionBinaryLower.Binary6402PointSurplus
import ProximityPrize.SubmissionBinaryLower.B6402FactorCases
/-! The retuned Table 1 handles invariant slope-linear factors outside the hard quartic profile. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402OrdinaryLinear
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd B6401KerDOrders B6401KerD2
open B6401Params hiding A
open B6402HybridP64 B6402FarkasVerifier B6402IntFarkas B6402IntSmallCerts B6402CertsT1 B6402CertsT2 B6402CertsT3
open B6402SmallAlg hiding wdegBiDom
open B6401SmallAlg (wdegBiDom)
open B6401ListAndMCA
open B6401ResLineOrd B6402QuotBridge B6402PointSurplus B6402FactorCases B6402FactorAssembly
open B6401FactorBound (card_evalZBiPoly_natDegree_lt_le card_evalZBiPoly_good_deg_le degZ_resultant_biPoly_le
  card_evalZ_poly_eq_zero_le wdegBiDom_coeff_le_of_wdeg wdegBiDom_le_of_wdeg_coeff wdegBiDom_ge_natDegree_mul)
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators
set_option maxHeartbeats 2500000
local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
theorem certsT1_no_p64 :
    certsT1.all (fun c => !c.cap1.useP64 && !c.cap2.useP64) = true := by decide


lemma card_le_of_biPoly_pow_1_bound (D_ZF : ℕ) :
    max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ 1 1 (2 * D_ZF)) ≤
      (15000000 : ℚ) * (D_ZF : ℚ) + 2000000 := by
  have hDZ : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
  apply max_le
  · push_cast; linarith
  · unfold arklibBoundPowQ
    norm_num [N, wY, A]
    linarith

lemma card_le_of_biPoly_pow_2_bound {D_ZF : ℕ} (hDZ : D_ZF ≤ 1811) :
    max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ 2 1 (2 * D_ZF)) ≤ (80000000000 : ℚ) := by
  have hDZQ : (D_ZF : ℚ) ≤ 1811 := by exact_mod_cast hDZ
  apply max_le
  · push_cast; linarith
  · unfold arklibBoundPowQ
    norm_num [N, wY, A]
    linarith


theorem small_linear
    (u₀ u₁ : Idx → Fld) {W_F D_ZF q₀ : ℕ} (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hq2_cond : q₀ = 2 → (W_F : ℚ) / (wY : ℚ) < 13 ∧ D_ZF ≤ 1811)
    (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).natDegree = 1)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ q₀ (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (outside : let F := ∑ e : KerDIdx wY W_F 1,cC (f_coord e)*kerDBasisPoly e.1
               ¬((F.coeff 1).natDegree=4 ∧ (F.coeff 0).natDegree≤5 ∧ (W_F:ℚ)/wY<28/5)) :
    (S.card : ℚ) ≤
      if q₀ = 1 then ((linearSlopeCap + 15000060 : ℕ) : ℚ) * (D_ZF : ℚ) + ((linearConstantCap + 2000000 : ℕ) : ℚ)
      else ((linearPowerCap + 80000231000 : ℕ) : ℚ) := by
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
  have hT4 : ¬(f1.natDegree=4 ∧ f0.natDegree≤5 ∧ (W_F:ℚ)/wY<28/5) := outside
  let S_clean : Finset Fld :=
    if hd1 : 2 ≤ f1.natDegree then
      S.filter fun z =>
        (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
        (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree) ∧
        (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) ≠ 0
    else
      S.filter fun z =>
        (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
        (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
  have hS_split : S.card ≤ S_clean.card + 52 * D_ZF := by
    dsimp only [S_clean]
    split_ifs with hd1
    · have ⟨hf0_ne, _, hres_ne⟩ := resY_f0_f1_ne_zero_of_irred_deg1 Fpoly hirr hFdeg (by change 1 ≤ f1.natDegree; omega)
      let B0 := S.filter fun z => (evalZBiPoly f0 z).natDegree ≠ f0.natDegree
      let B1 := S.filter fun z => ¬ (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
      let B2 := S.filter fun z => (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) = 0
      have hB0 : B0.card ≤ D_ZF := card_evalZBiPoly_natDegree_lt_le f0 hf0_ne hf0_degZ S
      have hB1 : B1.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f1 hf1_ne hf1_degZ S
      have hB2 : B2.card ≤ (f0.natDegree + f1.natDegree) * D_ZF :=
        card_evalZ_poly_eq_zero_le _ hres_ne (B6401FactorBound.degZ_resultant_biPoly_le f0 f1 f0.natDegree f1.natDegree D_ZF hf0_degZ hf1_degZ) S
      have hsub : S ⊆ (S.filter fun z => (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
          (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree) ∧
          (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) ≠ 0) ∪ (B0 ∪ (B1 ∪ B2)) := by
        intro z hz; simp only [Finset.mem_union, B0, B1, B2, Finset.mem_filter]
        by_cases h0 : (evalZBiPoly f0 z).natDegree = f0.natDegree
        · by_cases h1 : evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree
          · by_cases h2 : (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) = 0
            · exact Or.inr (Or.inr (Or.inr ⟨hz, h2⟩))
            · exact Or.inl ⟨hz, h0, h1, h2⟩
          · exact Or.inr (Or.inr (Or.inl ⟨hz, h1⟩))
        · exact Or.inr (Or.inl ⟨hz, h0⟩)
      have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _))
      have : (f0.natDegree + f1.natDegree) * D_ZF ≤ 50 * D_ZF := Nat.mul_le_mul_right D_ZF (by omega)
      omega
    · let B0 := S.filter fun z => (evalZBiPoly f0 z).natDegree ≠ f0.natDegree
      let B1 := S.filter fun z => ¬ (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
      have hB0 : B0.card ≤ D_ZF := by
        by_cases hf0_ne : f0 = 0
        · dsimp only [B0]; rw [hf0_ne]; simp [evalZBiPoly]
        · exact card_evalZBiPoly_natDegree_lt_le f0 hf0_ne hf0_degZ S
      have hB1 : B1.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f1 hf1_ne hf1_degZ S
      have hsub : S ⊆ (S.filter fun z => (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
          (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)) ∪ (B0 ∪ B1) := by
        intro z hz; simp only [Finset.mem_union, B0, B1, Finset.mem_filter]
        by_cases h0 : (evalZBiPoly f0 z).natDegree = f0.natDegree
        · by_cases h1 : evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree
          · exact Or.inl ⟨hz, h0, h1⟩
          · exact Or.inr (Or.inr ⟨hz, h1⟩)
        · exact Or.inr (Or.inl ⟨hz, h0⟩)
      have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
      omega
  have hS_clean_sub : S_clean ⊆ S := by dsimp only [S_clean]; split_ifs <;> exact Finset.filter_subset _ _
  have hcl : (S_clean.card : ℚ) ≤
      if q₀ = 1 then (linearSlopeCap : ℚ) * (D_ZF : ℚ) + (linearConstantCap : ℚ) else (linearPowerCap : ℚ) := by
    by_cases hemp : S_clean.Nonempty
    · obtain ⟨z0, hz0⟩ := hemp
      have hz0S : z0 ∈ S := hS_clean_sub hz0
      have hFz0 : evalZContact Fpoly z0 = ∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1 :=
        evalZContact_sum_kerD f_coord z0
      have hf0z : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
      have hf1z : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
      have ⟨hd0z, hf1z_ne, hd1z, hresz⟩ :
          (evalZBiPoly f0 z0).natDegree = f0.natDegree ∧
          evalZBiPoly f1 z0 ≠ 0 ∧
          (evalZBiPoly f1 z0).natDegree = f1.natDegree ∧
          (2 ≤ (evalZBiPoly f1 z0).natDegree →
            Polynomial.resultant (evalZBiPoly f0 z0) (evalZBiPoly f1 z0)
              (evalZBiPoly f0 z0).natDegree (evalZBiPoly f1 z0).natDegree ≠ 0) := by
        dsimp only [S_clean] at hz0
        split_ifs at hz0 with hd1
        · obtain ⟨_, h0, ⟨hne1, h1⟩, h2⟩ := Finset.mem_filter.mp hz0
          refine ⟨h0, hne1, h1, fun _ => ?_⟩
          rw [h0, h1]
          have hm := Polynomial.resultant_map_map f0 f1 f0.natDegree f1.natDegree
            (Polynomial.mapRingHom (Polynomial.evalRingHom z0))
          rw [← Polynomial.coe_mapRingHom, ← hm] at h2
          exact h2
        · obtain ⟨_, h0, ⟨hne1, h1⟩⟩ := Finset.mem_filter.mp hz0
          exact ⟨h0, hne1, h1, fun hge => by omega⟩
      obtain ⟨c, hc_mem, _, hmpos, _, _, _, hcHi, hsurp, hcap1, hc1_le, hc0_le, hcap2_fn⟩ :=
        t1_surplus_of_point (fun e => (f_coord e).eval z0) (fun i => u₀ i + z0 ^ q₀ * u₁ i) k
          (hvan_z z0) (P z0) (hP z0 hz0S) (Az z0) (hcard z0 hz0S)
          (fun i hi => (hmatch z0 hz0S i).mp hi) (by rw [← hFz0]; exact hFvan z0 hz0S)
          (by rw [hf1z]; exact hf1z_ne) hWF_hi
          (fun h2 => by rw [hf0z, hf1z]; exact hresz (by rw [← hf1z]; exact h2))
          (by rw [hf0z, hf1z, hd0z, hd1z]; exact hT4)
      have hnop64 := List.all_eq_true.mp certsT1_no_p64 c hc_mem
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnop64
      have hpars : 1 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
        unfold checkCapWitness at hcap1
        by_contra hbadp; push Not at hbadp
        have hif : (c.m == 0 || c.s < 1 || c.cHiDen == 0 || c.δNum == 0 || c.δDen == 0 || (1 : ℕ) == 0) = true := by
          rcases lt_or_ge c.s 1 with h1 | h1
          · simp [h1]
          · rcases Nat.eq_zero_or_pos c.cHiDen with h2 | h2
            · simp [h2]
            · rcases Nat.eq_zero_or_pos c.δNum with h3 | h3
              · simp [h3]
              · have h4 : c.δDen = 0 := by have := hbadp h1 h2 h3; omega
                simp [h4]
        rw [if_pos hif] at hcap1; cases hcap1
      rcases hq₀ with rfl | rfl
      · simp only [↓reduceIte]
        have hcard1 := card_le_of_quotient_surplus u₀ u₁ c.cap1 hcap1 (Or.inl rfl) le_rfl hpars.1 hmpos
          hpars.2.1 hpars.2.2.1 hpars.2.2.2 (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
          (fun i => ⟨(hk_exact i).1, (hk_exact i).2 c.m⟩) hsurp S_clean P Az
          (fun z hz => hP z (hS_clean_sub hz)) (fun z hz => hFvan z (hS_clean_sub hz))
          (fun z hz => hcard z (hS_clean_sub hz)) (fun z hz => hmatch z (hS_clean_sub hz))
          (fun z hz => hbad z (hS_clean_sub hz)) (fun h => by rw [hnop64.1] at h; cases h)
        have h1 : (c.cap1.c1Bkt : ℚ) ≤ (linearSlopeCap : ℚ) := by exact_mod_cast hc1_le
        have h0 : (c.cap1.c0Bkt : ℚ) ≤ (linearConstantCap : ℚ) := by exact_mod_cast hc0_le
        have hmul := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℚ) D_ZF)
        linarith only [hcard1, hmul, h0]
      · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
        obtain ⟨hW13, hDZ1811⟩ := hq2_cond rfl
        obtain ⟨hcap2, hq2_le⟩ := hcap2_fn hW13
        have hcard2 := card_le_of_quotient_surplus u₀ u₁ c.cap2 hcap2 (Or.inr rfl) le_rfl hpars.1 hmpos
          hpars.2.1 hpars.2.2.1 hpars.2.2.2 (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
          (fun i => ⟨(hk_exact i).1, (hk_exact i).2 c.m⟩) hsurp S_clean P Az
          (fun z hz => hP z (hS_clean_sub hz)) (fun z hz => hFvan z (hS_clean_sub hz))
          (fun z hz => hcard z (hS_clean_sub hz)) (fun z hz => hmatch z (hS_clean_sub hz))
          (fun z hz => hbad z (hS_clean_sub hz)) (fun h => by rw [hnop64.2] at h; cases h)
        have hq : (c.cap2.c1Bkt : ℚ) * (D_ZF : ℚ) + (c.cap2.c0Bkt : ℚ) ≤ (linearPowerCap : ℚ) := by
          have hDZQ : (D_ZF : ℚ) ≤ 1811 := by exact_mod_cast hDZ1811
          have hle : (c.cap2.c1Bkt : ℚ) * 1811 + (c.cap2.c0Bkt : ℚ) ≤ (linearPowerCap : ℚ) := by exact_mod_cast hq2_le
          have hmul := mul_le_mul_of_nonneg_left hDZQ (Nat.cast_nonneg (α := ℚ) c.cap2.c1Bkt)
          linarith only [hmul, hle]
        exact hcard2.trans hq
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
      split_ifs <;> positivity
  have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 52 * (D_ZF : ℚ) := by exact_mod_cast hS_split
  rcases hq₀ with rfl | rfl
  · simp only [↓reduceIte] at hcl ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℚ) D_ZF]
  · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hcl ⊢
    have hDZQ : (D_ZF : ℚ) ≤ 1811 := by exact_mod_cast (hq2_cond rfl).2
    push_cast; linarith


#print axioms small_linear
end ProximityPrize.SubmissionBinaryLower.B6402OrdinaryLinear
