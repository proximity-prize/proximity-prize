import ProximityPrize.SubmissionBinaryLower.Native6402Caps
/-! Apply the retuned ArkLib or P64 certificate to original labels. The two
branch implications are adapted from the published 6401 integer verifier. -/
namespace ProximityPrize.SubmissionBinaryLower
namespace B6402CapSound
open B6401Params B6401ContactKerD B6401ResultantOrd B6402FarkasVerifier B6402HybridP64 B6402IntFarkas
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators
set_option maxHeartbeats 1600000
private lemma checkSideP64_card_le
    (u₀ u₁ : Idx → Fld) (d m B H W_Phi DeltaMax q₀ : ℕ) (w : CapWitness)
    (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hside_b : checkSideP64 d m B W_Phi DeltaMax q₀ w = true)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0)
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤ W_Phi)
    (hB : Φ.natDegree ≤ B)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hΦgap : ∀ z ∈ S,
      (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
        (∑ i ∈ Az z, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (B6402HybridP64.A : ℤ)) ≤ (DeltaMax : ℤ)) :
    (S.card : ℚ) ≤
      (((w.Cd + max ((4 * W_Phi) / wY) (4 * B) + B + 1 : ℕ) : ℚ) / (1 : ℕ)) * (H : ℚ) +
      ((((w.Cd + max ((4 * W_Phi) / wY) (4 * B) + B) * q₀ * B + w.Ch * B : ℕ) : ℚ) / (1 : ℕ)) := by
  unfold checkSideP64 at hside_b
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hside_b
  rcases hside_b with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hFΦ⟩, hFaux⟩, hh0⟩, hqaux⟩, hM0pos⟩, hBmul⟩, hC0h⟩, h4Bq⟩,
    hslack⟩, hP0⟩, hM0eq⟩, hMh⟩, hCd_ark⟩, hCd_light⟩, hCd_c7⟩, hCd_c6⟩, hCh_aux⟩, hCh_light⟩,
    hCh_ark⟩, hCh_c7⟩, hCh_c6⟩
  set M_W : ℕ := (4 * W_Phi) / wY
  set M_B : ℕ := max M_W (4 * B)
  set N_eff : ℕ := (B6402HybridP64.A - wY) + DeltaMax
  set tNum : ℕ := N - wY
  set tDen : ℕ := B6402HybridP64.A - wY
  have htDen : 0 < tDen := by norm_num [tDen, B6402HybridP64.A, wY]
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have hM0Q : (0 : ℚ) < (w.M0 : ℚ) := by exact_mod_cast hM0pos
  have hFld : Fintype.card Fld = 2 ^ 192 := BF64.card_ext3
  have hFΦ' : 2 * B * W_Phi < Fintype.card Fld := by
    rw [hFld]; exact lt_trans hFΦ (by norm_num)
  have hFaux' : (4 * W_Phi / wY + B) * (4 * W_Phi) < Fintype.card Fld := by
    rw [hFld]; exact lt_trans hFaux (by norm_num)
  have hP0Z : 8 * (wY : ℤ) * w.slack * (w.h0 + 1 : ℤ) ^ 2 +
      16 * (wY : ℤ) * ((B6402HybridP64.A : ℤ) - wY + 10000) * (w.h0 + 1 : ℤ) + ((wY : ℤ) + 2) ^ 2 ≤
      64 * (wY : ℤ) * w.P0 * (w.h0 + 1 : ℤ) ^ 2 := by
    have hsub : ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY := by norm_num [B6402HybridP64.A, wY]
    have hZ : ((8 * wY * w.slack * (w.h0 + 1) ^ 2 +
        16 * wY * (B6402HybridP64.A - wY + 10000) * (w.h0 + 1) + (wY + 2) ^ 2 : ℕ) : ℤ) ≤
        ((64 * wY * w.P0 * (w.h0 + 1) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hP0
    push_cast [hsub] at hZ; exact hZ
  have hM0Z : (w.M0 : ℤ) + w.P0 = (B6402HybridP64.A : ℤ) - wY := by
    have hsub : ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY := by norm_num [B6402HybridP64.A, wY]
    have hZ : ((w.M0 + w.P0 : ℕ) : ℤ) = ((B6402HybridP64.A - wY : ℕ) : ℤ) := by exact_mod_cast hM0eq
    push_cast [hsub] at hZ; exact hZ
  have hNeffZ : (N_eff : ℤ) = (B6402HybridP64.A : ℤ) - wY + DeltaMax := by
    dsimp only [N_eff]; push_cast [show ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY by norm_num [B6402HybridP64.A, wY]]; rfl
  have hCd_arkQ : (2 * (w.h0 : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((B6402HybridP64.A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ)) ≤ (w.Cd : ℚ) := by
    have h2h : 1 ≤ 2 * w.h0 := by linarith
    have h2w : 1 ≤ 2 * wY := by norm_num [wY]
    have hQ : (((2 * w.h0 - 1) * tDen + tNum * (1 + (2 * wY - 1) * (2 * w.h0 - 1) + 2 * (w.h0 - (2 * wY + 1))) : ℕ) : ℚ) ≤
        (w.Cd : ℚ) * (tDen : ℚ) := by exact_mod_cast hCd_ark
    push_cast [Nat.cast_sub h2h, Nat.cast_sub h2w] at hQ
    change (2 * (w.h0 : ℚ) - 1) + ((tNum : ℚ) / (tDen : ℚ)) * _ ≤ (w.Cd : ℚ)
    have hne : (tDen : ℚ) ≠ 0 := htDenQ.ne'
    rw [show (2 * (w.h0 : ℚ) - 1) + ((tNum : ℚ) / (tDen : ℚ)) *
          (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ)) =
        ((2 * (w.h0 : ℚ) - 1) * (tDen : ℚ) + (tNum : ℚ) *
          (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ))) / (tDen : ℚ) by
      rw [add_div, mul_div_cancel_right₀ _ hne, mul_div_right_comm]]
    rw [div_le_iff₀ htDenQ]; linarith
  have hCd_c7Q : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (w.M0 : ℚ) + (N : ℚ) ≤ (w.Cd : ℚ) := by
    have hQ : ((2 * N_eff * N * 6 + N * w.M0 : ℕ) : ℚ) ≤ (w.Cd : ℚ) * (w.M0 : ℚ) := by exact_mod_cast hCd_c7
    rw [show ((2 * N_eff * N * 6 : ℕ) : ℚ) / (w.M0 : ℚ) + (N : ℚ) =
        (((2 * N_eff * N * 6 : ℕ) : ℚ) + (N : ℚ) * (w.M0 : ℚ)) / (w.M0 : ℚ) by
      rw [add_div, mul_div_cancel_right₀ _ hM0Q.ne']]
    rw [div_le_iff₀ hM0Q]; push_cast at hQ ⊢; linarith
  have hCd_c6Q : ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) ≤ (w.Cd : ℚ) := by
    have hQ : ((16 * N_eff * N + N * 10000 ^ 2 : ℕ) : ℚ) ≤ (w.Cd : ℚ) * (10000 ^ 2 : ℚ) := by exact_mod_cast hCd_c6
    rw [show ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) =
        (((16 * N_eff * N : ℕ) : ℚ) + (N : ℚ) * (10000 ^ 2 : ℚ)) / (10000 ^ 2 : ℚ) by ring]
    rw [div_le_iff₀ (by norm_num)]; push_cast at hQ ⊢; linarith
  have hCh_lightQ : ((120000000000 : ℕ) : ℚ) / ((w.h0 + 1 : ℕ) : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ (by positivity)]; exact_mod_cast hCh_light
  have hCh_arkQ : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((B6402HybridP64.A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ (w.Ch : ℚ) := by
    have hQ : ((q₀ * (tNum + (N - wY - 1) * tDen) : ℕ) : ℚ) ≤ (w.Ch : ℚ) * (tDen : ℚ) := by exact_mod_cast hCh_ark
    change (q₀ : ℚ) * (((tNum : ℚ) / (tDen : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ (w.Ch : ℚ)
    rw [show (q₀ : ℚ) * (((tNum : ℚ) / (tDen : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) =
        ((q₀ : ℚ) * ((tNum : ℚ) + ((N - wY - 1 : ℕ) : ℚ) * (tDen : ℚ))) / (tDen : ℚ) by field_simp [htDenQ.ne']]
    rw [div_le_iff₀ htDenQ]; push_cast at hQ; linarith
  have hCh_c7Q : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (w.M0 : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ hM0Q]; exact_mod_cast hCh_c7
  have hCh_c6Q : ((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast hCh_c6
  have hp64 := hybrid_p64_card_le u₀ u₁ q₀ hq₀ Φ B H W_Phi m DeltaMax hΦ hB hH hWΦ hFΦ' hFaux'
    S P Az hP hcurve hcard hmatch hbad hΦgap
    20 30 496 120000000000 cert208984_6402 count208984_6402 (by norm_num)
    w.h0 w.q_aux w.slack w.P0 w.M0 N_eff hh0 hqaux hM0pos hBmul hC0h h4Bq hslack hP0Z hM0Z hNeffZ hMh
    (w.Cd : ℚ) (w.Ch : ℚ) hCd_arkQ (by exact_mod_cast hCd_light) hCd_c7Q hCd_c6Q
    (by exact_mod_cast hCh_aux) hCh_lightQ hCh_arkQ hCh_c7Q hCh_c6Q
  dsimp only at hp64
  have hrew' : (w.Cd : ℚ) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) +
      ((max (4 * W_Phi / wY : ℕ) (4 * B) : ℕ) + (B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) +
      (w.Ch : ℚ) * (B : ℚ) + (H : ℚ) =
      (((w.Cd + M_B + B + 1 : ℕ) : ℚ) / (1 : ℕ)) * (H : ℚ) +
      ((((w.Cd + M_B + B) * q₀ * B + w.Ch * B : ℕ) : ℚ) / (1 : ℕ)) := by
    dsimp only [M_B, M_W]; push_cast; ring
  rw [hrew'] at hp64
  exact hp64

private lemma arklib_alg (B H q₀ tNum tDen psi c0 : ℚ) (htDen : tDen ≠ 0) :
    (2 * B - 1) * H + (tNum / tDen) * (q₀ * B + H * psi) + q₀ * c0 * B =
    (((2 * B - 1) * tDen + tNum * psi) / tDen) * H +
    ((tNum * q₀ * B + q₀ * c0 * B * tDen) / tDen) := by
  field_simp [htDen]; ring

private lemma arklib_eq_ratio (wY_ N_ A_ B H q₀ : ℕ)
    (hB1 : 1 ≤ B) (h2wY1 : 1 ≤ 2 * wY_) (htDen : 0 < A_ - wY_) :
    let tNum : ℕ := N_ - wY_
    let tDen : ℕ := A_ - wY_
    let psi : ℕ := 1 + (2 * wY_ - 1) * (2 * B - 1) + 2 * (B - (2 * wY_ + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N_ - wY_ - 1) * B * tDen
    (2 * (B : ℚ) - 1) * (H : ℚ) +
      (((tNum : ℕ) : ℚ) / ((tDen : ℕ) : ℚ)) * ((q₀ : ℚ) * (B : ℚ) + (H : ℚ) *
        (1 + (2 * (wY_ : ℚ) - 1) * (2 * (B : ℚ) - 1) + 2 * ((B - (2 * wY_ + 1) : ℕ) : ℚ))) +
      (q₀ : ℚ) * ((N_ - wY_ - 1 : ℕ) : ℚ) * (B : ℚ) =
    (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  intro tNum tDen psi kHNum k0Num
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have h2B1 : 1 ≤ 2 * B := by omega
  have hpsiQ : 1 + (2 * (wY_ : ℚ) - 1) * (2 * (B : ℚ) - 1) + 2 * ((B - (2 * wY_ + 1) : ℕ) : ℚ) = (psi : ℚ) := by
    dsimp only [psi]
    push_cast [Nat.cast_sub h2wY1, Nat.cast_sub h2B1]
    ring
  have hkH_cast : (kHNum : ℚ) = (2 * (B : ℚ) - 1) * (tDen : ℚ) + (tNum : ℚ) * (psi : ℚ) := by
    dsimp only [kHNum]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2B1, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hk0_cast : (k0Num : ℚ) =
      (tNum : ℚ) * (q₀ : ℚ) * (B : ℚ) + (q₀ : ℚ) * ((N_ - wY_ - 1 : ℕ) : ℚ) * (B : ℚ) * (tDen : ℚ) := by
    dsimp only [k0Num]
    simp only [Nat.cast_add, Nat.cast_mul]
  rw [hpsiQ, hkH_cast, hk0_cast]
  exact arklib_alg (B : ℚ) (H : ℚ) (q₀ : ℚ) (tNum : ℚ) (tDen : ℚ) (psi : ℚ) ((N_ - wY_ - 1 : ℕ) : ℚ) htDenQ.ne'

private lemma arklib_H_le_ratio (wY_ N_ A_ B H q₀ : ℕ)
    (hB1 : 1 ≤ B) (htDen : 0 < A_ - wY_) :
    let tNum : ℕ := N_ - wY_
    let tDen : ℕ := A_ - wY_
    let psi : ℕ := 1 + (2 * wY_ - 1) * (2 * B - 1) + 2 * (B - (2 * wY_ + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N_ - wY_ - 1) * B * tDen
    (H : ℚ) ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  intro tNum tDen psi kHNum k0Num
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have h1 : (1 : ℚ) ≤ ((kHNum : ℕ) : ℚ) / (tDen : ℚ) := by
    rw [le_div_iff₀ htDenQ, one_mul]
    have h2B_ge : 1 ≤ 2 * B - 1 := by omega
    have : tDen ≤ kHNum := Nat.le_trans (Nat.le_mul_of_pos_left tDen h2B_ge) (Nat.le_add_right _ _)
    exact_mod_cast this
  have h2 : (0 : ℚ) ≤ ((k0Num : ℕ) : ℚ) / (tDen : ℚ) := by positivity
  have hH0 : (0 : ℚ) ≤ (H : ℚ) := by positivity
  calc (H : ℚ) = 1 * (H : ℚ) + 0 := by ring
    _ ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hH0) h2

private lemma checkArklib_card_le
    (u₀ u₁ : Idx → Fld) (B H q₀ : ℕ) (hq₀pos : 1 ≤ q₀) (hB1 : 1 ≤ B)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B) (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z)) :
    let tNum : ℕ := N - wY
    let tDen : ℕ := B6402HybridP64.A - wY
    let psi : ℕ := 1 + (2 * wY - 1) * (2 * B - 1) + 2 * (B - (2 * wY + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N - wY - 1) * B * tDen
    (S.card : ℚ) ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  have hark := card_le_of_biPoly_pow u₀ u₁ q₀ hq₀pos Φ B H hΦ hB hH S P Az
    hP hcurve hcard (fun z hz i hi => (hmatch z hz i).mp hi) hbad
  have htDen : 0 < B6402HybridP64.A - wY := by norm_num [B6402HybridP64.A, wY]
  have h2wY1 : 1 ≤ 2 * wY := by norm_num [wY]
  have hark_eq : arklibBoundPowQ q₀ B H = _ := arklib_eq_ratio wY N B6402HybridP64.A B H q₀ hB1 h2wY1 htDen
  rw [hark_eq] at hark
  exact hark.trans (max_le (arklib_H_le_ratio wY N B6402HybridP64.A B H q₀ hB1 htDen) le_rfl)


theorem priced_labels
    (u₀ u₁ : Idx → Fld) (m B H W_Phi DeltaMax q₀ cap : ℕ) (w : CapWitness)
    (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (checked : Binary6402NativeCaps.allowance m B W_Phi DeltaMax q₀ H cap w=true)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0)
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤ W_Phi)
    (hB : Φ.natDegree ≤ B)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hΦgap : ∀ z ∈ S,
      (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
        (∑ i ∈ Az z, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (B6402HybridP64.A : ℤ)) ≤ (DeltaMax : ℤ)) :
    (S.card : ℚ) ≤ (cap : ℚ) := by
  by_cases hh : w.useP64=true
  · simp only [Binary6402NativeCaps.allowance,hh,if_true,Bool.and_eq_true,decide_eq_true_eq] at checked
    have hside := checkSideP64_card_le u₀ u₁ 1 m B H W_Phi DeltaMax q₀ w hq₀ checked.1 Φ hΦ hWΦ hB hH S P Az hP hcurve hcard hmatch hbad hΦgap
    simp only [Nat.cast_one,div_one] at hside
    apply hside.trans
    have hbudget := checked.2
    rw [Nat.add_assoc] at hbudget
    exact_mod_cast hbudget
  · simp only [Binary6402NativeCaps.allowance,if_neg hh,decide_eq_true_eq] at checked
    have hq : 1≤q₀ := by omega
    have hark := checkArklib_card_le u₀ u₁ B H q₀ hq checked.1 Φ hΦ hB hH S P Az hP hcurve hcard hmatch hbad
    apply hark.trans
    let den := B6402HybridP64.A-wY
    let num := N-wY
    let psi := 1+(2*wY-1)*(2*B-1)+2*(B-(2*wY+1))
    let k := (2*B-1)*den+num*psi
    let c := num*q₀*B+q₀*(N-wY-1)*B*den
    change ((k:ℚ)/(den:ℚ))*(H:ℚ)+(c:ℚ)/(den:ℚ)≤(cap:ℚ)
    rw [div_mul_eq_mul_div,←add_div]
    apply (div_le_iff₀ (by decide : (0:ℚ)<(den:ℚ))).mpr
    have hprice : k*H+c≤cap*den := by
      simpa only [k,c,den,num,psi,N,wY,B6402HybridP64.A,Nat.add_assoc] using checked.2
    exact_mod_cast hprice

#print axioms priced_labels
end B6402CapSound
end ProximityPrize.SubmissionBinaryLower
