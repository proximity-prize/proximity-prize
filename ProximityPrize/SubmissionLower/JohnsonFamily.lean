import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.JohnsonBasic
set_option synthInstance.maxHeartbeats 100000
theorem hammingDist_comp_equiv {ι ι' α : Type*} [Fintype ι] [Fintype ι'] [DecidableEq α]
    (e : ι' ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  unfold hammingDist
  apply Finset.card_nbij' (fun i' => e i') (fun i => e.symm i)
  · intro i' hi'
    simpa using hi'
  · intro i hi
    simpa using hi
  · intro i' hi'
    simp
  · intro i hi
    simp
namespace JohnsonBound
open Real
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ := J q (((ℓ - 1) / ℓ) * δ)
lemma Jqℓ_eq_J (q ℓ δ : ℚ) : Jqℓ q ℓ δ = J q (((ℓ - 1) / ℓ) * δ) := rfl
lemma Jqℓ_eq_mul_one_sub_sqrt {q : ℚ} (hq : q ≠ 0) (ℓ δ : ℚ) :
    Jqℓ q ℓ δ =
      ((1 - 1 / q : ℚ) : ℝ) * (1 - √((1 - q / (q - 1) * ((ℓ - 1) / ℓ) * δ : ℚ))) := by
  have h1 : (1 / (q / (q - 1)) : ℚ) = 1 - 1 / q := by
    rcases eq_or_ne q 1 with rfl | hq1
    · norm_num
    · field_simp
  have hcast : ((1 - 1 / q : ℚ) : ℝ) = 1 / ((q / (q - 1) : ℚ) : ℝ) := by
    rw [← h1]; push_cast; ring
  rw [Jqℓ_eq_J, J, hcast]
  congr 2
  push_cast
  ring_nf
end JohnsonBound
namespace CodingTheory
open scoped NNReal
open Code JohnsonBound
open Real Finset Fintype
set_option maxHeartbeats 1000000 in
lemma johnson_card_le_ell {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (v : Fin n → α) (ℓ : ℕ) (mDist : ℕ)
    (hℓ2 : 2 ≤ ℓ) (hn_pos : 0 < n) (hα2 : 2 ≤ Fintype.card α) (hmDist1 : 1 ≤ mDist)
    (e_fact : (JohnsonBound.e B v : ℝ) ≤ Jqℓ (Fintype.card α) ℓ (mDist / n) * n)
    (d_fact : (mDist : ℚ) ≤ JohnsonBound.d B)
    (hradicand : ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n) ≤ 1) :
    B.card ≤ ℓ := by
  set q : ℚ := (Fintype.card α : ℚ) with hq_def
  set δ_min : ℚ := (mDist : ℚ) / n with hδ_def0
  set radius : ℝ := Jqℓ q ℓ δ_min with hradius
  have hq2 : (2 : ℚ) ≤ q := by rw [hq_def]; exact_mod_cast hα2
  have hfrac : (q / (q - 1) : ℚ) = q / (q - 1) := rfl
  set frac : ℚ := q / (q - 1) with hfrac_def
  have hq1_pos : (0 : ℚ) < q - 1 := by linarith
  have hq_pos : (0 : ℚ) < q := by linarith
  have hfrac_pos : (0 : ℚ) < frac := div_pos hq_pos hq1_pos
  have hfrac_ge1 : (1 : ℚ) ≤ frac := by
    rw [hfrac_def, le_div_iff₀ hq1_pos]; linarith
  have hminDist1 : 1 ≤ mDist := hmDist1
  have hδmin_pos : (0 : ℚ) < δ_min := by
    rw [show δ_min = (mDist:ℚ) / n from rfl]
    apply div_pos <;> [exact_mod_cast hminDist1; exact_mod_cast hn_pos]
  set lFac : ℚ := ((ℓ : ℚ) - 1) / (ℓ : ℚ) with hlFac_def
  have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1_pos : (0 : ℚ) < (ℓ : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ2
    linarith
  have hlFac_pos : (0 : ℚ) < lFac := div_pos hℓ1_pos hℓpos
  have hlFac_lt1 : lFac < 1 := by
    rw [hlFac_def, div_lt_one hℓpos]; linarith
  set x : ℚ := frac * lFac * δ_min with hx_def
  have hx_pos : (0 : ℚ) < x := by positivity
  have hx_le1 : x ≤ 1 := by
    rw [hx_def, hfrac_def, hlFac_def, show δ_min = (mDist:ℚ) / n from rfl]
    convert hradicand using 2
  have hradius_eq : radius = (1 / (frac:ℝ)) * (1 - √(1 - (x:ℝ))) := by
    rw [hradius, Jqℓ_eq_J, JohnsonBound.J, hx_def, hlFac_def, hfrac_def]
    push_cast
    congr 2
    ring_nf
  have h1x_nonneg : (0 : ℝ) ≤ 1 - (x : ℝ) := by
    have : (x : ℝ) ≤ 1 := by exact_mod_cast hx_le1
    linarith
  have hsqrt_nonneg : (0 : ℝ) ≤ √(1 - (x:ℝ)) := Real.sqrt_nonneg _
  have hsqrt_le1 : √(1 - (x:ℝ)) ≤ 1 := by
    have hx0 : (0:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx_pos.le
    calc √(1 - (x:ℝ)) ≤ √1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hfrac_radius : (frac : ℝ) * radius = 1 - √(1 - (x:ℝ)) := by
    rw [hradius_eq]
    have : (frac : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hfrac_pos)
    field_simp
  set eB : ℚ := JohnsonBound.e B v with heB
  set dB : ℚ := JohnsonBound.d B with hdB
  have hcardq : (card α : ℚ) = q := rfl
  have hed_le : (frac:ℝ) * ((eB:ℝ)/n) ≤ 1 - √(1 - (x:ℝ)) := by
    have he_le : (eB:ℝ)/n ≤ radius := by
      rw [div_le_iff₀ (by exact_mod_cast hn_pos)]
      calc (eB:ℝ) = (JohnsonBound.e B v : ℝ) := by rw [heB]
        _ ≤ radius * n := e_fact
    calc (frac:ℝ) * ((eB:ℝ)/n) ≤ (frac:ℝ) * radius :=
          mul_le_mul_of_nonneg_left he_le (by exact_mod_cast hfrac_pos.le)
      _ = 1 - √(1 - (x:ℝ)) := hfrac_radius
  have heB_nonneg : (0:ℚ) ≤ eB := by
    rw [heB]; simp only [JohnsonBound.e]
    apply mul_nonneg (by positivity)
    exact_mod_cast Nat.zero_le _
  have hed_nonneg : (0:ℝ) ≤ (frac:ℝ) * ((eB:ℝ)/n) := by
    apply mul_nonneg (by exact_mod_cast hfrac_pos.le)
    apply div_nonneg _ (by exact_mod_cast hn_pos.le)
    exact_mod_cast heB_nonneg
  have hsq_ge : (1 - (x:ℝ)) ≤ (1 - (frac:ℝ) * ((eB:ℝ)/n))^2 := by
    have h1med : √(1 - (x:ℝ)) ≤ 1 - (frac:ℝ) * ((eB:ℝ)/n) := by linarith
    have hnn : (0:ℝ) ≤ 1 - (frac:ℝ) * ((eB:ℝ)/n) := le_trans hsqrt_nonneg h1med
    nlinarith [Real.sq_sqrt h1x_nonneg, Real.sqrt_nonneg (1 - (x:ℝ)), h1med, hnn]
  have hdd_ge : (frac:ℝ) * (δ_min:ℝ) ≤ (frac:ℝ) * ((dB:ℝ)/n) := by
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hfrac_pos.le)
    rw [le_div_iff₀ (by exact_mod_cast hn_pos)]
    have hdge : (δ_min:ℝ) * n ≤ (dB : ℝ) := by
      have hd1 : (δ_min : ℝ) * n = (mDist : ℝ) := by
        rw [show δ_min = (mDist:ℚ) / n from rfl]; push_cast; field_simp
      rw [hd1, hdB]; exact_mod_cast d_fact
    linarith [hdge]
  have hx_lt_fracδ : (x:ℝ) < (frac:ℝ) * (δ_min:ℝ) := by
    have hxeq : (x:ℝ) = (frac:ℝ) * (lFac:ℝ) * (δ_min:ℝ) := by rw [hx_def]; push_cast; ring
    rw [hxeq]
    have hlFacR : (lFac:ℝ) < 1 := by exact_mod_cast hlFac_lt1
    have hpos : (0:ℝ) < (frac:ℝ) * (δ_min:ℝ) := by
      apply mul_pos (by exact_mod_cast hfrac_pos) (by exact_mod_cast hδmin_pos)
    nlinarith [hpos, hlFacR, (by exact_mod_cast hlFac_pos.le : (0:ℝ) ≤ (lFac:ℝ))]
  have hreal : (1 - (frac:ℝ) * ((dB:ℝ)/n)) < (1 - (frac:ℝ) * ((eB:ℝ)/n))^2 := by
    have hxlt : (x:ℝ) < (frac:ℝ) * ((dB:ℝ)/n) := lt_of_lt_of_le hx_lt_fracδ hdd_ge
    linarith [hsq_ge, hxlt]
  have hstrong : JohnsonConditionStrong B v := by
    rw [johnson_condition_strong_iff_johnson_denom_pos, johnson_denominator_def]
    have hQ : (1 - frac * (dB / n) : ℚ) < (1 - frac * (eB / n) : ℚ) ^ 2 := by
      have hcast : ((1 - frac * (dB / n) : ℚ) : ℝ) < (((1 - frac * (eB / n) : ℚ) : ℝ)) ^ 2 := by
        push_cast; convert hreal using 2
      exact_mod_cast hcast
    have hpos0 : (1 - (card α : ℚ) / ((card α:ℚ) - 1) * (eB / n)) ^ 2
         - (1 - (card α:ℚ) / ((card α:ℚ) - 1) * (dB / n)) > 0 := by
      rw [show (card α:ℚ) = q from rfl, ← hfrac_def]; linarith [hQ]
    convert hpos0 using 2
  have hjb := johnson_bound hstrong
  simp only at hjb
  set ed : ℚ := frac * eB / n with hed_def
  set dd : ℚ := frac * dB / n with hdd_def
  have hDenom : JohnsonDenominator B v = (1 - ed)^2 - (1 - dd) := by
    rw [johnson_denominator_def]
    rw [show (card α : ℚ) = q from rfl, ← hfrac_def]
    rw [hed_def, hdd_def]; ring
  set t : ℚ := 1 - (1 - ed)^2 with ht_def
  have hDenom2 : JohnsonDenominator B v = dd - t := by rw [hDenom, ht_def]; ring
  have ht_nonneg : (0:ℚ) ≤ t := by
    rw [ht_def]
    have : (1 - ed)^2 ≤ 1 := by
      have hed_nn : (0:ℚ) ≤ ed := by
        rw [hed_def]; apply div_nonneg (mul_nonneg hfrac_pos.le _) (by exact_mod_cast hn_pos.le)
        rw [heB]; simp only [JohnsonBound.e]
        exact mul_nonneg (by positivity) (by exact_mod_cast Nat.zero_le _)
      have hed_le1 : ed ≤ 1 := by
        have : (ed : ℝ) ≤ 1 - √(1-(x:ℝ)) := by
          rw [hed_def]; push_cast; rw [mul_div_assoc]; exact hed_le
        have : (ed : ℝ) ≤ 1 := le_trans this (by linarith [hsqrt_nonneg])
        exact_mod_cast this
      nlinarith [hed_nn, hed_le1]
    linarith
  have ht_le_x : t ≤ x := by
    rw [ht_def]
    have hsqQ : (1 - x) ≤ (1 - ed)^2 := by
      have : ((1 - x : ℚ) : ℝ) ≤ ((1 - ed : ℚ) : ℝ)^2 := by
        push_cast
        rw [hed_def]; push_cast
        convert hsq_ge using 2
        ring
      exact_mod_cast this
    linarith
  set b : ℚ := frac * δ_min with hb_def
  have hδ_le_dd_raw : δ_min ≤ dB / n := by
    rw [show δ_min = (mDist:ℚ) / n from rfl, hdB]
    exact div_le_div_of_nonneg_right d_fact (by exact_mod_cast hn_pos.le)
  have hb_le_dd : b ≤ dd := by
    rw [hb_def, hdd_def, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hδ_le_dd_raw hfrac_pos.le
  have hx_lt_b : x < b := by rw [hb_def]; exact_mod_cast hx_lt_fracδ
  have hb_pos : (0:ℚ) < b := by rw [hb_def]; exact mul_pos hfrac_pos hδmin_pos
  have hbx_eq_ℓ : b / (b - x) = (ℓ:ℚ) := by
    rw [hb_def, hx_def, hlFac_def]
    have hl1 : (0:ℚ) < (ℓ:ℚ) - 1 := hℓ1_pos
    field_simp
    ring
  have hDenom_pos : (0:ℚ) < JohnsonDenominator B v :=
    johnson_condition_strong_iff_johnson_denom_pos.1 hstrong
  have hDenom_eq_pos : (0:ℚ) < dd - t := by rw [← hDenom2]; exact hDenom_pos
  have hcard_le : (B.card : ℚ) ≤ (ℓ:ℚ) := by
    calc (B.card : ℚ)
        ≤ (frac * dB / n) / JohnsonDenominator B v := by
          convert hjb using 2
          try rw [show (card α : ℚ) = q from rfl, ← hfrac_def]
      _ = dd / (dd - t) := by rw [hDenom2, hdd_def]
      _ ≤ b / (b - t) := by
          have hat : (0:ℚ) < dd - t := hDenom_eq_pos
          have hbt : (0:ℚ) < b - t := by linarith [ht_le_x, hx_lt_b]
          rw [div_le_div_iff₀ hat hbt]
          nlinarith [ht_nonneg, hb_le_dd]
      _ ≤ b / (b - x) := by
          have hbx : (0:ℚ) < b - x := by linarith [hx_lt_b]
          apply div_le_div_of_nonneg_left hb_pos.le hbx
          linarith [ht_nonneg]
      _ = (ℓ:ℚ) := hbx_eq_ℓ
  exact_mod_cast hcard_le
lemma plotkin_card_le_ell {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (ℓ : ℕ) (mDist : ℕ)
    (hℓ2 : 2 ≤ ℓ) (hn_pos : 0 < n) (hα2 : 2 ≤ Fintype.card α) (hB2 : 2 ≤ B.card)
    (d_fact : (mDist : ℚ) ≤ JohnsonBound.d B)
    (hguard : 1 < ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((mDist : ℚ) / n)) :
    B.card ≤ ℓ := by
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hjb := JohnsonBound.johnson_bound_lemma (B := B) (v := fun _ => a) hn_pos hB2 hα2
  have hq2 : (2 : ℚ) ≤ (Fintype.card α : ℚ) := by exact_mod_cast hα2
  have hq1_pos : (0 : ℚ) < (Fintype.card α : ℚ) - 1 := by linarith
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
  have hℓQ : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ2
  have hℓQ_pos : (0 : ℚ) < (ℓ : ℚ) := by linarith
  set frac : ℚ := (Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1) with hfrac_def
  have hfrac_pos : (0 : ℚ) < frac := div_pos (by linarith) hq1_pos
  set D : ℚ := frac * (JohnsonBound.d B / n) with hD_def
  have hmain : (B.card : ℚ) * (D - 1) ≤ D := by
    have hsq : (0 : ℚ) ≤ (B.card : ℚ) *
        (1 - frac * (JohnsonBound.e B (fun _ => a) / n)) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hD_eq : frac * JohnsonBound.d B / n = D := by rw [hD_def]; ring
    rw [hD_eq] at hjb
    nlinarith [hjb, hsq]
  have hDgt : (ℓ : ℚ) < D * ((ℓ : ℚ) - 1) := by
    have hmd : ((mDist : ℚ) / n) ≤ JohnsonBound.d B / n := by gcongr
    have h1 : 1 < frac * (((ℓ : ℚ) - 1) / ℓ) * (JohnsonBound.d B / n) :=
      lt_of_lt_of_le hguard (mul_le_mul_of_nonneg_left hmd
        (mul_nonneg hfrac_pos.le (div_nonneg (by linarith) (by linarith))))
    calc (ℓ : ℚ) = 1 * ℓ := (one_mul _).symm
      _ < frac * (((ℓ : ℚ) - 1) / ℓ) * (JohnsonBound.d B / n) * ℓ :=
          mul_lt_mul_of_pos_right h1 hℓQ_pos
      _ = D * ((ℓ : ℚ) - 1) := by rw [hD_def]; field_simp
  have hD1 : (1 : ℚ) < D := by nlinarith [hDgt, hℓQ]
  have hfinal : (B.card : ℚ) < (ℓ : ℚ) := by nlinarith [hmain, hDgt, hD1]
  exact_mod_cast hfinal.le
private lemma johnson_lambda_le_ell_of_radicand
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (hℓ_ge : 2 ≤ ℓ)
    (h_radicand :
        ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
            * (((ℓ : ℚ) - 1) / (ℓ : ℚ))
            * ((Code.minDist C : ℚ) / Fintype.card ι) ≤ 1) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  intro q δ_min
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  set radius : ℝ := Jqℓ q ℓ δ_min with hradius
  refine iSup_le fun f => ?_
  set S : Set (ι → α) := closeCodewordsRel C f radius with hS
  have hSfin : S.Finite := Set.toFinite _
  rw [← hSfin.cast_ncard_eq, Set.ncard_eq_toFinset_card S hSfin]
  set B0 : Finset (ι → α) := hSfin.toFinset with hB0
  classical
  have hmem : ∀ x ∈ B0, x ∈ C ∧ ((hammingDist f x : ℝ) / n ≤ radius) := by
    intro x hx
    rw [hB0, Set.Finite.mem_toFinset, hS] at hx
    simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_setOf_eq] at hx
    refine ⟨hx.1, ?_⟩
    have h2 := hx.2
    unfold Code.relHammingDist at h2
    push_cast at h2
    rw [hn_def]
    exact le_of_eq_of_le (by congr!) h2
  suffices hcard : B0.card ≤ ℓ by exact_mod_cast hcard
  rcases le_or_gt B0.card 1 with hle1 | hgt1
  · omega
  ·
    set e : ι ≃ Fin n := (Fintype.equivFin ι) with he
    set reIdx : (ι → α) → (Fin n → α) := fun x => x ∘ e.symm with hreIdx
    have hreIdx_inj : Function.Injective reIdx := by
      intro x y h
      funext i
      have := congrFun h (e i)
      simpa [hreIdx] using this
    set B : Finset (Fin n → α) := B0.image reIdx with hB
    set v : Fin n → α := reIdx f with hv
    have hBcard : B.card = B0.card := Finset.card_image_of_injective B0 hreIdx_inj
    have hB2 : 2 ≤ B.card := by rw [hBcard]; exact hgt1
    have hα2 : 2 ≤ Fintype.card α := by
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hgt1
      obtain ⟨i, hi⟩ := Function.ne_iff.mp huw
      exact Fintype.one_lt_card_iff.mpr ⟨u i, w i, hi⟩
    have hcardF : card α = card α := rfl
    have hBcard_pos : (0 : ℝ) < B.card := by
      rw [hBcard]; exact_mod_cast (by omega : 0 < B0.card)
    have hdist_le : ∀ x ∈ B, (Δ₀(v, x) : ℝ) ≤ radius * n := by
      intro x hx
      rw [hB, Finset.mem_image] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have hdist : hammingDist v (reIdx c) = hammingDist f c := by
        rw [hv, hreIdx]
        exact hammingDist_comp_equiv e.symm f c
      have hle := (hmem c hc).2
      rw [div_le_iff₀ (by exact_mod_cast hn_pos)] at hle
      calc (Δ₀(v, reIdx c) : ℝ) = (hammingDist f c : ℝ) := by rw [hdist]
        _ ≤ radius * n := hle
    have e_fact : (JohnsonBound.e B v : ℝ) ≤ radius * n := by
      simp only [JohnsonBound.e]
      push_cast
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hBcard_pos]
      calc (∑ x ∈ B, (Δ₀(v, x) : ℝ))
          ≤ ∑ x ∈ B, (radius * n) := Finset.sum_le_sum hdist_le
        _ = B.card * (radius * n) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = radius * ↑n * ↑B.card := by ring
    have d_fact : (Code.minDist C : ℚ) ≤ JohnsonBound.d B := by
      have hmin_le : sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d }
          ≤ JohnsonBound.d B :=
        min_dist_le_d hB2
      have hminDist_lb : Code.minDist C ≤
          sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } := by
        apply le_csInf
        · obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
          exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
        · rintro m ⟨u, hu, w, hw, huw, rfl⟩
          rw [hB, Finset.mem_image] at hu hw
          obtain ⟨c1, hc1, rfl⟩ := hu
          obtain ⟨c2, hc2, rfl⟩ := hw
          have hc12 : c1 ≠ c2 := fun h => huw (by rw [h])
          have hd : hammingDist (reIdx c1) (reIdx c2) = hammingDist c1 c2 := by
            rw [hreIdx]; exact hammingDist_comp_equiv e.symm c1 c2
          rw [hd]
          apply Nat.sInf_le
          exact ⟨c1, (hmem c1 hc1).1, c2, (hmem c2 hc2).1, hc12, rfl⟩
      calc (Code.minDist C : ℚ)
          ≤ ((sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } : ℕ) : ℚ) := by
            exact_mod_cast hminDist_lb
        _ ≤ JohnsonBound.d B := hmin_le
    have hminDist1 : 1 ≤ Code.minDist C := by
      obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hgt1
      rw [Code.minDist]
      apply le_csInf
      · exact ⟨hammingDist u w, u, (hmem u hu).1, w, (hmem w hw).1, huw, rfl⟩
      · rintro m ⟨a, _, b, _, hab, rfl⟩
        exact hammingDist_pos.mpr hab
    have hrad : ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
        * (((ℓ : ℚ) - 1) / (ℓ : ℚ)) * ((Code.minDist C : ℚ) / n) ≤ 1 := by
      rw [hn_def]; exact h_radicand
    have hcard_le : B.card ≤ ℓ :=
      johnson_card_le_ell B v ℓ (Code.minDist C) hℓ_ge hn_pos hα2 hminDist1
        e_fact d_fact hrad
    rw [← hBcard]; exact_mod_cast hcard_le
theorem johnson_bound_lambda_le_ell
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (hℓ_ge : 1 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  intro q δ_min
  classical
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  rcases (show ℓ = 1 ∨ 2 ≤ ℓ by omega) with rfl | hℓ2
  ·
    have h0 : Jqℓ q 1 δ_min = 0 := by
      norm_num [Jqℓ, JohnsonBound.J]
    refine iSup_le fun f => ?_
    have hsub : closeCodewordsRel C f (Jqℓ q ((1 : ℕ) : ℚ) δ_min) ⊆ {f} := by
      intro c hc
      have h2 := hc.2
      simp only [Code.relHammingBall, Set.mem_setOf_eq] at h2
      rw [show Jqℓ q ((1 : ℕ) : ℚ) δ_min = 0 by exact_mod_cast h0] at h2
      have h3 := le_antisymm h2 (by positivity)
      have h3' := NNRat.cast_eq_zero.mp h3
      unfold Code.relHammingDist at h3'
      rw [div_eq_zero_iff] at h3'
      rcases h3' with h | h
      · refine Set.mem_singleton_iff.mpr (hammingDist_eq_zero.mp ?_).symm
        have h' := Nat.cast_eq_zero.mp h
        convert h' using 2
      · exact absurd h (by exact_mod_cast (Fintype.card_pos (α := ι)).ne')
    calc (closeCodewordsRel C f (Jqℓ q ((1 : ℕ) : ℚ) δ_min)).encard
        ≤ ({f} : Set (ι → α)).encard := Set.encard_mono hsub
      _ = 1 := Set.encard_singleton f
      _ ≤ (((1 : ℕ) : ℕ∞)) := by simp
  rcases le_or_gt ((q / (q - 1)) * (((ℓ:ℚ) - 1) / ℓ) * δ_min) 1 with hrad | hguard
  · exact johnson_lambda_le_ell_of_radicand C ℓ hℓ2 hrad
  ·
    have hCfin : C.Finite := Set.toFinite _
    refine le_trans (Lambda_le_ncard _ hCfin) ?_
    rcases le_or_gt C.ncard 1 with hle1 | hgt1
    · exact_mod_cast le_trans hle1 (by omega : 1 ≤ ℓ)
    · set eqv : ι ≃ Fin n := Fintype.equivFin ι with heqv
      set reIdx : (ι → α) → (Fin n → α) := fun x => x ∘ eqv.symm with hreIdx
      have hreIdx_inj : Function.Injective reIdx := by
        intro x y h; funext i; simpa [hreIdx] using congrFun h (eqv i)
      set B : Finset (Fin n → α) := hCfin.toFinset.image reIdx with hB
      have hBcard : B.card = C.ncard := by
        rw [hB, Finset.card_image_of_injective _ hreIdx_inj, Set.ncard_eq_toFinset_card _ hCfin]
      have hB2 : 2 ≤ B.card := by omega
      have hα2 : 2 ≤ Fintype.card α := by
        obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
        obtain ⟨i, hi⟩ := Function.ne_iff.mp huw
        exact Fintype.one_lt_card_iff.mpr ⟨u i, w i, hi⟩
      have d_fact : (Code.minDist C : ℚ) ≤ JohnsonBound.d B := by
        have hmin_le : sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d }
            ≤ JohnsonBound.d B := min_dist_le_d hB2
        have hminDist_lb : Code.minDist C ≤
            sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } := by
          apply le_csInf
          · obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
            exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
          · rintro m ⟨u, hu, w, hw, huw, rfl⟩
            rw [hB, Finset.mem_image] at hu hw
            obtain ⟨c1, hc1, rfl⟩ := hu
            obtain ⟨c2, hc2, rfl⟩ := hw
            have hc12 : c1 ≠ c2 := fun h => huw (by rw [h])
            rw [show hammingDist (reIdx c1) (reIdx c2) = hammingDist c1 c2 from
              hammingDist_comp_equiv eqv.symm c1 c2]
            exact Nat.sInf_le ⟨c1, hCfin.mem_toFinset.mp hc1, c2, hCfin.mem_toFinset.mp hc2,
              hc12, rfl⟩
        calc (Code.minDist C : ℚ)
            ≤ ((sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } : ℕ) : ℚ) := by
              exact_mod_cast hminDist_lb
          _ ≤ JohnsonBound.d B := hmin_le
      have hcard_le : B.card ≤ ℓ :=
        plotkin_card_le_ell B ℓ (Code.minDist C) hℓ2 hn_pos hα2 hB2 d_fact (by
          simpa [q, δ_min, hn_def] using hguard)
      rw [← hBcard]; exact_mod_cast hcard_le
private lemma domination_core (s η : ℝ) (ℓ : ℕ) (n : ℕ)
    (hs0 : 0 < s) (hη : 0 < η)
    (hℓ2 : 2 ≤ ℓ) (hn1 : 1 ≤ n)
    (hρ : (s ^ 2 : ℝ) ≤ 1)
    (h2ηρ : 2 * η * s ^ 2 ≤ 1 / 2)
    (hℓ_ge : (1 : ℝ) / (2 * η * s ^ 2) - 1 ≤ ℓ) :
    1 - (1 - 1 / (ℓ:ℝ)) * (1 - s ^ 2 + 1 / n) ≤ (s + η)^2 := by
  have hℓR : (2:ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  have hℓpos : (0:ℝ) < ℓ := by linarith
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0:ℝ) < n := by linarith
  have hρpos : (0:ℝ) < s ^ 2 := by positivity
  have h2ηρpos : (0:ℝ) < 2 * η * s ^ 2 := by positivity
  have h1m2ηρ : (0:ℝ) < 1 - 2 * η * s ^ 2 := by linarith
  have hinvℓ : (1:ℝ) / ℓ ≤ (2 * η * s ^ 2)/(1-2 * η * s ^ 2) := by
    rw [div_le_div_iff₀ hℓpos h1m2ηρ]
    have hden_pos : (0:ℝ) < 1/(2 * η * s ^ 2) - 1 := by
      rw [sub_pos, lt_div_iff₀ h2ηρpos]; linarith
    have hkey : (1:ℝ)/(2 * η * s ^ 2) - 1 = (1 - 2 * η * s ^ 2)/(2 * η * s ^ 2) := by field_simp
    rw [hkey] at hℓ_ge
    rw [div_le_iff₀ h2ηρpos] at hℓ_ge
    nlinarith [hℓ_ge]
  have hLHS : 1 - (1 - 1 / (ℓ:ℝ)) * (1 - s ^ 2 + 1 / n) ≤ s ^ 2 + (1 / ℓ) * (1 - s ^ 2) := by
    have h1n : (0:ℝ) < 1 / n := by positivity
    have hfac : (0:ℝ) ≤ (1 - 1 / (ℓ:ℝ)) := by
      rw [sub_nonneg, div_le_one hℓpos]; linarith
    nlinarith [hfac, h1n, mul_nonneg (le_of_lt (by positivity : (0:ℝ) < 1 / (ℓ:ℝ))) h1n.le]
  have hbound : (1 / (ℓ:ℝ)) * (1 - s ^ 2) ≤ 2 * η * s + η^2 := by
    have h1ρ : (0:ℝ) ≤ 1 - s ^ 2 := by linarith
    calc (1 / (ℓ:ℝ)) * (1 - s ^ 2) ≤ ((2 * η * s ^ 2)/(1-2 * η * s ^ 2))*(1-s ^ 2) :=
          mul_le_mul_of_nonneg_right hinvℓ h1ρ
      _ ≤ 2 * η * s := by
          rw [div_mul_eq_mul_div, div_le_iff₀ h1m2ηρ]
          nlinarith [sq_nonneg (2*s-1), sq_nonneg (s-1), mul_nonneg hs0.le h1ρ, h2ηρ, hη, hs0,
                     mul_pos hη hs0]
      _ ≤ 2 * η * s + η^2 := by nlinarith [sq_nonneg η]
  linarith [hLHS, hbound]
theorem mds_johnson_lambda_le_of_rate_distance
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {α : Type*} [Finite α] [DecidableEq α]
    (C : Set (ι → α)) (ρ η : ℝ)
    (hρ_pos : 0 < ρ) (hρ_le_one : ρ ≤ 1) (hη_pos : 0 < η)
    (h_rate_distance : (Code.minDist C : ℝ) / Fintype.card ι =
      1 - ρ + 1 / Fintype.card ι) :
    (Lambda C (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  letI : Fintype α := Fintype.ofFinite α
  set n : ℕ := Fintype.card ι with hn_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_posR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hC_nontrivial : C.Nontrivial := by
    by_contra hnot
    have hsub : C.Subsingleton := Set.not_nontrivial_iff.mp hnot
    letI : Subsingleton C :=
      ⟨fun x y => Subtype.ext (hsub x.property y.property)⟩
    have hmin0 : Code.minDist C = 0 := by
      rw [← Code.dist_eq_minDist]
      exact Code.dist_subsingleton
    rw [hmin0] at h_rate_distance
    norm_num at h_rate_distance
    have hinv_pos : (0 : ℝ) < 1 / n := one_div_pos.mpr hn_posR
    have hrhs_pos : (0 : ℝ) < 1 - ρ + 1 / n :=
      add_pos_of_nonneg_of_pos (sub_nonneg.mpr hρ_le_one) hinv_pos
    exact (ne_of_gt hrhs_pos) (by simpa [one_div] using h_rate_distance.symm)
  set s : ℝ := √ρ with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hρ_pos
  have hs_le1 : s ≤ 1 := by
    rw [hs_def]; calc √ρ ≤ √1 := Real.sqrt_le_sqrt hρ_le_one
      _ = 1 := Real.sqrt_one
  have hs_sq : s^2 = ρ := by rw [hs_def, Real.sq_sqrt hρ_pos.le]
  set ℓ : ℕ := ⌊1 / (2 * η * ρ)⌋₊ with hℓ_def
  have hηρ_pos : 0 < 2 * η * ρ := by positivity
  have hℓ_le : (ℓ : ℝ) ≤ 1 / (2 * η * ρ) := Nat.floor_le (by positivity)
  rcases le_or_gt ℓ 1 with hℓ1 | hℓ2
  ·
    have hηρ_gt : 1 / 2 < 2 * η * ρ := by
      have hval_lt : 1 / (2 * η * ρ) < 2 := by
        rw [hℓ_def] at hℓ1
        have := Nat.lt_of_floor_lt (n := 2) (by omega : ⌊1 / (2 * η * ρ)⌋₊ < 2)
        exact_mod_cast this
      rw [div_lt_iff₀ hηρ_pos] at hval_lt
      linarith
    have hη_gt : 1 / (4 * ρ) < η := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hηρ_gt, hρ_pos]
    have hradius_neg : 1 - s - η < 0 := by
      have hcorner : 1 - s - 1/(4*s^2) < 0 := by
        have h4 : 0 < 4 * s^2 := by positivity
        rw [sub_neg, lt_div_iff₀ h4]
        nlinarith [sq_nonneg (2*s - 1), sq_nonneg (s-1), hs_pos, hs_le1, sq_nonneg s]
      have h4ρ : 1/(4*ρ) = 1/(4*s^2) := by rw [hs_sq]
      rw [h4ρ] at hη_gt
      linarith
    have hLambda0 : Lambda C (1 - s - η) = 0 := by
      rw [Lambda]
      apply le_antisymm
      · refine iSup_le fun f => ?_
        have hempty : closeCodewordsRel C f (1 - s - η) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro c hc
          have hmem := hc.2
          simp only [Code.relHammingBall, Set.mem_setOf_eq] at hmem
          have hcombine : (0:ℝ) ≤ 1 - s - η := le_trans (by positivity) hmem
          linarith [hcombine, hradius_neg]
        rw [hempty]; simp
      · exact bot_le
    have : Lambda C (1 - √ρ - η) = 0 := by rw [← hs_def]; exact hLambda0
    rw [this]; simp
  ·
    have hq2 : 2 ≤ Fintype.card α := by
      obtain ⟨u, huC, v, hvC, huv⟩ := hC_nontrivial
      obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
      exact Fintype.one_lt_card_iff.mpr ⟨u i, v i, hi⟩
    set q : ℚ := (Fintype.card α : ℚ) with hq_def
    have hqR2 : (2:ℚ) ≤ q := by rw [hq_def]; exact_mod_cast hq2
    set δ_minQ : ℚ := (Code.minDist C : ℚ) / n with hδ_def
    have hℓQ2 : (2:ℚ) ≤ (ℓ:ℚ) := by exact_mod_cast hℓ2
    have hℓRpos : (0:ℝ) < (ℓ:ℝ) := by positivity
    set lFacR : ℝ := ((ℓ:ℝ) - 1) / ℓ with hlFacR_def
    have hδR : (δ_minQ : ℝ) = 1 - ρ + 1/n := by
      rw [hδ_def]; push_cast; rw [← h_rate_distance]
    have hstep3 : (ℓ : ENNReal) ≤ ENNReal.ofReal (1 / (2 * η * ρ)) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hℓ_le
    have hn1 : 1 ≤ n := hn_pos
    have h2ηρ_le : 2 * η * ρ ≤ 1/2 := by
      have hval_ge : (2:ℝ) ≤ 1/(2*η*ρ) := by
        have : (2:ℕ) ≤ ⌊1 / (2 * η * ρ)⌋₊ := by rw [← hℓ_def]; exact hℓ2
        calc (2:ℝ) ≤ (⌊1/(2*η*ρ)⌋₊ : ℝ) := by exact_mod_cast this
          _ ≤ 1/(2*η*ρ) := Nat.floor_le (by positivity)
      rw [le_div_iff₀ hηρ_pos] at hval_ge; linarith
    rcases le_or_gt ((q / (q - 1)) * (((ℓ:ℚ) - 1) / ℓ) * δ_minQ) 1 with hradicand | hguard
    ·
      have hT32 := johnson_bound_lambda_le_ell C ℓ hℓ2.le
      have hdom : 1 - √ρ - η ≤ Jqℓ q ℓ δ_minQ := by
        rw [Jqℓ_eq_J]
        set δJ : ℚ := (((ℓ:ℚ)-1)/ℓ) * δ_minQ with hδJ_def
        have hδJ_nonneg : (0:ℚ) ≤ δJ := by
          rw [hδJ_def]; apply mul_nonneg
          · apply div_nonneg (by linarith [hℓQ2]) (by linarith [hℓQ2])
          · rw [hδ_def]; positivity
        have hδJ_le1 : δJ ≤ 1 := by
          have hfrac_ge1 : (1:ℚ) ≤ q/(q-1) := by
            rw [le_div_iff₀ (by linarith [hqR2])]; linarith [hqR2]
          calc δJ ≤ (q/(q-1)) * δJ := by nlinarith [hδJ_nonneg, hfrac_ge1]
            _ = (q / (q - 1)) * (((ℓ:ℚ) - 1) / ℓ) * δ_minQ := by rw [hδJ_def]; ring
            _ ≤ 1 := hradicand
        have hguardJ : q/(q-1) * δJ ≤ 1 := by
          rw [hδJ_def]
          calc q/(q-1) * ((((ℓ:ℚ)-1)/ℓ) * δ_minQ)
              = (q / (q - 1)) * (((ℓ:ℚ) - 1) / ℓ) * δ_minQ := by ring
            _ ≤ 1 := hradicand
        have hsj : 1 - √(1 - (δJ : ℝ)) ≤ JohnsonBound.J q δJ :=
          JohnsonBound.sqrt_le_J (q := q) (δ := δJ)
            (by exact_mod_cast (by linarith [hqR2] : (1:ℚ) < q)) hδJ_nonneg hδJ_le1 hguardJ
        refine le_trans ?_ hsj
        have hrhs_nn : (0:ℝ) ≤ s + η := by linarith [hs_pos, hη_pos]
        have hδJR : (δJ:ℝ) = (((ℓ:ℝ)-1)/ℓ) * (δ_minQ:ℝ) := by rw [hδJ_def]; push_cast; ring
        have hsq_le : 1 - (δJ:ℝ) ≤ (s + η)^2 := by
          rw [hδJR, hδR, ← hs_sq]
          rw [show (((ℓ:ℝ)-1)/ℓ) = 1 - 1/(ℓ:ℝ) from by field_simp]
          have hℓ_ge : (1:ℝ)/(2*η*(s^2)) - 1 ≤ ℓ := by
            rw [hs_sq]
            have h1 : (1:ℝ)/(2*η*ρ) - 1 ≤ ⌊1/(2*η*ρ)⌋₊ := by
              have := Nat.sub_one_lt_floor (1/(2*η*ρ))
              linarith [this]
            rw [← hℓ_def] at h1; exact h1
          have h2ηρs : 2 * η * s^2 ≤ 1/2 := by rw [hs_sq]; exact h2ηρ_le
          have hρle1 : (s^2:ℝ) ≤ 1 := by rw [hs_sq]; exact hρ_le_one
          have hn1R : (1:ℕ) ≤ n := hn1
          exact domination_core s η ℓ n hs_pos hη_pos hℓ2 hn1R hρle1 h2ηρs hℓ_ge
        have hsuff : √(1 - (δJ:ℝ)) ≤ s + η := by
          rw [show s + η = √((s+η)^2) from by rw [Real.sqrt_sq hrhs_nn]]
          exact Real.sqrt_le_sqrt hsq_le
        rw [hs_def] at hsuff; linarith [hsuff]
      have hstep1 : Lambda C (1 - √ρ - η)
          ≤ Lambda C (Jqℓ q ℓ δ_minQ) := Lambda_mono hdom
      calc (Lambda C (1 - √ρ - η) : ENNReal)
          ≤ (Lambda C (Jqℓ q ℓ δ_minQ) : ENNReal) := by exact_mod_cast hstep1
        _ ≤ ((ℓ : ℕ∞) : ENNReal) := by exact_mod_cast hT32
        _ = (ℓ : ENNReal) := by simp
        _ ≤ ENNReal.ofReal (1 / (2 * η * ρ)) := hstep3
    ·
      classical
      obtain ⟨u0, hu0C, v0, hv0C, huv0⟩ := hC_nontrivial
      set eqv : ι ≃ Fin n := Fintype.equivFin ι with heqv
      set reIdx : (ι → α) → (Fin n → α) := fun x => x ∘ eqv.symm with hreIdx
      have hreIdx_inj : Function.Injective reIdx := by
        intro x y h
        funext i
        simpa [hreIdx] using congrFun h (eqv i)
      have hCfin : C.Finite := Set.toFinite _
      set B : Finset (Fin n → α) := hCfin.toFinset.image reIdx with hB
      have hBcard : B.card = C.ncard := by
        rw [hB, Finset.card_image_of_injective _ hreIdx_inj,
          Set.ncard_eq_toFinset_card _ hCfin]
      have hB2 : 2 ≤ B.card := by
        refine Finset.one_lt_card.mpr
          ⟨reIdx u0, ?_, reIdx v0, ?_, fun h => huv0 (hreIdx_inj h)⟩
        · exact Finset.mem_image_of_mem _ (hCfin.mem_toFinset.mpr hu0C)
        · exact Finset.mem_image_of_mem _ (hCfin.mem_toFinset.mpr hv0C)
      have d_fact : (Code.minDist C : ℚ) ≤ JohnsonBound.d B := by
        have hmin_le : sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d }
            ≤ JohnsonBound.d B := min_dist_le_d hB2
        have hminDist_lb : Code.minDist C ≤
            sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } := by
          apply le_csInf
          · obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB2
            exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
          · rintro m ⟨u, hu, w, hw, huw, rfl⟩
            rw [hB, Finset.mem_image] at hu hw
            obtain ⟨c1, hc1, rfl⟩ := hu
            obtain ⟨c2, hc2, rfl⟩ := hw
            have hc12 : c1 ≠ c2 := fun h => huw (by rw [h])
            rw [show hammingDist (reIdx c1) (reIdx c2) = hammingDist c1 c2 from
              hammingDist_comp_equiv eqv.symm c1 c2]
            apply Nat.sInf_le
            exact ⟨c1, hCfin.mem_toFinset.mp hc1, c2, hCfin.mem_toFinset.mp hc2, hc12, rfl⟩
        calc (Code.minDist C : ℚ)
            ≤ ((sInf { d | ∃ u ∈ B, ∃ w ∈ B, u ≠ w ∧ hammingDist u w = d } : ℕ) : ℚ) := by
              exact_mod_cast hminDist_lb
          _ ≤ JohnsonBound.d B := hmin_le
      have hcard_le : B.card ≤ ℓ := by
        refine plotkin_card_le_ell B ℓ (Code.minDist C)
          hℓ2 hn_pos hq2 hB2 d_fact ?_
        rw [hq_def, hδ_def] at hguard
        exact hguard
      calc (Lambda C (1 - √ρ - η) : ENNReal)
          ≤ ((C.ncard : ℕ∞) : ENNReal) := by
            exact_mod_cast Lambda_le_ncard _ hCfin
        _ ≤ (ℓ : ENNReal) := by
            rw [← hBcard]
            exact_mod_cast hcard_le
        _ ≤ ENNReal.ofReal (1 / (2 * η * ρ)) := hstep3
theorem mds_johnson_lambda_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Finite F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (hη_pos : 0 < η)
    (h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  intro ρ
  letI : Fintype F := Fintype.ofFinite F
  set n : ℕ := Fintype.card ι with hn_def
  set k : ℕ := Module.finrank F C with hk_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_le : k ≤ n := by
    rw [hk_def, hn_def]
    have := Submodule.finrank_le (R := F) (M := ι → F) C
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hbridge := (LinearCode.IsMDS_iff_rate_distance C).mp h_mds
  rw [← hn_def, ← hk_def] at hbridge
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      have hd_le : Code.minDist (C : Set (ι → F)) ≤ n := by
        have h1 : Code.dist (C : Set (ι → F)) = Code.minDist (C : Set (ι → F)) :=
          Code.dist_eq_minDist _
        have h2 : Code.dist (C : Set (ι → F)) ≤ Fintype.card ι := Code.dist_le_card _
        rw [h1] at h2
        rw [hn_def]
        exact h2
      have heq : (Code.minDist (C : Set (ι → F)) : ℝ) = n + 1 := by
        have h := hbridge
        rw [hk0] at h
        push_cast at h
        rw [div_eq_iff (show (n : ℝ) ≠ 0 from by exact_mod_cast hn_pos.ne')] at h
        rw [h]
        field_simp
        ring
      have hcast : (Code.minDist (C : Set (ι → F)) : ℝ) ≤ n := by exact_mod_cast hd_le
      rw [heq] at hcast
      linarith
    · exact hkpos
  have hρ_pos : 0 < ρ := by
    change 0 < (k : ℝ) / n
    positivity
  have hρ_le1 : ρ ≤ 1 := by
    change (k : ℝ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast hn_pos : (0 : ℝ) < n)]
    exact_mod_cast hk_le
  exact mds_johnson_lambda_le_of_rate_distance (C : Set (ι → F)) ρ η
    hρ_pos hρ_le1 hη_pos hbridge
end CodingTheory
