import ProximityPrize.SubmissionBinaryLower.P64Aux

/-!
# S_t-good factors (class 3) and Corollary S3 (class 4), PROOF.md 4.5 and 4.6

`StGood R t q` is (3.2) with `1 ≤ t ≤ 4`, `tw ≥ A`, `t·h ≤ q` and `q + n ≤ 4·DZ`. The extra
conditions only shrink the range of `q`: `t·h ≤ q` keeps every line multiplicity inside the
kernel box, and `q + n ≤ 4·DZ` gives `q + j_t ≤ 4·DZ`, hence the class-3 row
`h(4·DZ - 1) + j_t·d` (`card_le_of_stGood`).

Corollary S3: a cubic that is not `S_1`-good has `Σ_2 ≥ M(w - A)`, hence at least 89952 full
lines, and then at most `89952·d + 2172022111004` slopes by Lemma U and A2. The choice
`q = 3 + ⌊j_1Σ_2/(M - Σ_2)⌋` replaces PROOF.md's real estimates: it is at most `45n + 3` when
`j_1 ≤ 15`, and at most `j_1 + 3` when `j_1 ≥ 16`, because then `M ≥ 2Σ_2`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64S3

open Polynomial BCHKSSubstitutionVanish P64LineOrder P64Cofactor P64Light P64Aux

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yzd" => P64Caps.YZ.yzSupportDegree

/-- (3.2) at `(t, q)`, with the box conditions. -/
def StGood (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) (R : Tri) (t q : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ 4 ∧ 1482911 ≤ t * wd R 1048575 ∧ t * R.natDegree ≤ q ∧
    q + 2097152 ≤ 4 * 58589180686 ∧
    (q + (t * wd R 1048575 - 1482911) / 1048575) * con ω u₀ u₁ R t <
      q * P64Surf.Mbox (t * wd R 1048575 - 1482911)

/-- **Class 3.** -/
theorem card_le_of_stGood (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F)
    {R : Tri} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    {Vs : Finset F} {P : F → F[X]} {Az : F → Finset (Fin 2097152)}
    (hd : BadData ω u₀ u₁ R Vs P Az)
    (hdang : ∀ z ∈ Vs, Dangerous ω (lineOf u₀ u₁) 1048575 1482911 R (Az z))
    (hw : wd R 1048575 ≤ 249292 * 1482911 - 1) (hF : 2 ^ 128 ≤ Fintype.card F)
    {t q : ℕ} (hg : StGood ω u₀ u₁ R t q) :
    Vs.card ≤ R.natDegree * (4 * 58589180686 - 1) +
      (t * wd R 1048575 - 1482911) / 1048575 * yzd R 1 := by
  obtain ⟨ht1, ht4, hA, hth, hq, hcrit⟩ := hg
  have htw : t * wd R 1048575 ≤ 4 * wd R 1048575 := Nat.mul_le_mul_right _ ht4
  have hJ : (t * wd R 1048575 - 1482911) / 1048575 ≤ 2097152 :=
    Nat.div_le_of_le_mul (by omega)
  have hhw : 1048575 * R.natDegree ≤ wd R 1048575 :=
    natDegree_mul_le_weightedSupportDegree R hirr.ne_zero _
  have hφ : ∀ i, t * mu ω u₀ u₁ R i - 1 ≤ q + (t * wd R 1048575 - 1482911) / 1048575 := by
    intro i
    have hμ := lineOrd_le_natDegree_of_irreducible hirr hpos (ω i) (lineOf u₀ u₁ i)
    have : t * mu ω u₀ u₁ R i ≤ t * R.natDegree := Nat.mul_le_mul_left _ hμ
    omega
  have hF' : ((t * wd R 1048575 - 1482911) / 1048575 + R.natDegree) * (t * wd R 1048575) <
      Fintype.card F := by
    have h1 : (t * wd R 1048575 - 1482911) / 1048575 + R.natDegree ≤ 2 ^ 22 := by omega
    have h2 : t * wd R 1048575 ≤ 2 ^ 42 := by omega
    calc _ ≤ 2 ^ 22 * 2 ^ 42 := Nat.mul_le_mul h1 h2
      _ < 2 ^ 128 := by norm_num
      _ ≤ _ := hF
  have hth1 : 1 ≤ t * R.natDegree := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h := card_dangerous_le ω u₀ u₁ hirr hpos hd hdang t q (by omega) hA hφ hcrit hF'
  have h3 : R.natDegree * (q + (t * wd R 1048575 - 1482911) / 1048575 - 1) ≤
      R.natDegree * (4 * 58589180686 - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- `M(W) ≥ (W + 1) + (W - D + 1)` for `W ≥ D`. -/
lemma mbox_ge_two (W : ℕ) (hW : 1048575 ≤ W) :
    2 * W + 2 - 1048575 ≤ P64Surf.Mbox W := by
  unfold P64Surf.Mbox
  have hJ : 1 ≤ W / 1048575 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hsub : Finset.range 2 ⊆ Finset.range (W / 1048575 + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have h1 := Finset.sum_le_sum_of_subset (f := fun j => W - 1048575 * j + 1) hsub
  have h2 : ∑ j ∈ Finset.range 2, (W - 1048575 * j + 1) = (W + 1) + (W - 1048575 + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    omega
  omega

/-- `2·M(W) ≥ (j + 1)(W + 2)` with `j = ⌊W/D⌋`. -/
lemma two_mbox_ge (W : ℕ) :
    (W / 1048575 + 1) * (W + 2) ≤ 2 * P64Surf.Mbox W := by
  unfold P64Surf.Mbox
  set J := W / 1048575
  have hJ : J * 1048575 ≤ W := Nat.div_mul_le_self W 1048575
  have hrefl : ∑ j ∈ Finset.range (J + 1), (W - 1048575 * (J + 1 - 1 - j) + 1) =
      ∑ j ∈ Finset.range (J + 1), (W - 1048575 * j + 1) :=
    Finset.sum_range_reflect (fun j => W - 1048575 * j + 1) (J + 1)
  calc (J + 1) * (W + 2) = ∑ _j ∈ Finset.range (J + 1), (W + 2) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          ((W - 1048575 * j + 1) + (W - 1048575 * (J + 1 - 1 - j) + 1)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        omega
    _ = 2 * ∑ j ∈ Finset.range (J + 1), (W - 1048575 * j + 1) := by
        rw [Finset.sum_add_distrib, hrefl, two_mul]

/-- `Σ_2 = Con_1 ≤ 3n` for a cubic. -/
lemma con_one_le (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) {R : Tri}
    (hirr : Irreducible R) (h3 : R.natDegree = 3) :
    con ω u₀ u₁ R 1 ≤ 2097152 + 2 * (full ω u₀ u₁ R).card ∧ con ω u₀ u₁ R 1 ≤ 3 * 2097152 := by
  classical
  have hterm : ∀ i, (1 * mu ω u₀ u₁ R i - 1) * (1 * mu ω u₀ u₁ R i - 1 + 1) / 2 ≤
      1 + if i ∈ full ω u₀ u₁ R then 2 else 0 := by
    intro i
    have hμ := lineOrd_le_natDegree_of_irreducible hirr (by omega) (ω i) (lineOf u₀ u₁ i)
    rw [h3] at hμ
    have hfull : i ∈ full ω u₀ u₁ R ↔ mu ω u₀ u₁ R i = 3 := by
      simp only [full, Finset.mem_filter, Finset.mem_univ, true_and, h3, mu]
    change lineOrd R (ω i) (lineOf u₀ u₁ i) ≤ 3 at hμ
    change (1 * lineOrd R (ω i) (lineOf u₀ u₁ i) - 1) *
      (1 * lineOrd R (ω i) (lineOf u₀ u₁ i) - 1 + 1) / 2 ≤ _
    change i ∈ full ω u₀ u₁ R ↔ lineOrd R (ω i) (lineOf u₀ u₁ i) = 3 at hfull
    generalize lineOrd R (ω i) (lineOf u₀ u₁ i) = k at hμ hfull ⊢
    interval_cases k <;> simp [hfull]
  have hterm' : ∀ i, (1 * mu ω u₀ u₁ R i - 1) * (1 * mu ω u₀ u₁ R i - 1 + 1) / 2 ≤ 3 := by
    intro i
    have := hterm i
    split_ifs at this <;> omega
  constructor
  · calc con ω u₀ u₁ R 1 ≤ ∑ i : Fin 2097152, (1 + if i ∈ full ω u₀ u₁ R then 2 else 0) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2097152 + 2 * (full ω u₀ u₁ R).card := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
          simp [mul_comm]
  · calc con ω u₀ u₁ R 1 ≤ ∑ _i : Fin 2097152, 3 := Finset.sum_le_sum fun i _ => hterm' i
      _ = 3 * 2097152 := by simp [mul_comm]

/-- **Corollary S3**, first part: a cubic is `S_1`-good or has at least 89952 full lines. -/
theorem stGood_or_full (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) {R : Tri}
    (hirr : Irreducible R) (h3 : R.natDegree = 3) (hw : wd R 1048575 ≤ 249292 * 1482911 - 1) :
    (∃ q, StGood ω u₀ u₁ R 1 q) ∨ 89952 ≤ (full ω u₀ u₁ R).card := by
  classical
  have hhw : 1048575 * R.natDegree ≤ wd R 1048575 :=
    natDegree_mul_le_weightedSupportDegree R hirr.ne_zero _
  rw [h3] at hhw
  obtain ⟨hSfull, hS3⟩ := con_one_le ω u₀ u₁ hirr h3
  obtain ⟨W, hW⟩ : ∃ W, W = wd R 1048575 - 1482911 := ⟨_, rfl⟩
  have hM2 := mbox_ge_two W (by omega)
  have h2M := two_mbox_ge W
  have hJW : W / 1048575 * 1048575 ≤ W := Nat.div_mul_le_self _ _
  obtain ⟨J, hJ⟩ : ∃ J, J = W / 1048575 := ⟨_, rfl⟩
  rw [← hJ] at h2M hJW
  obtain ⟨M, hM⟩ : ∃ M, M = P64Surf.Mbox W := ⟨_, rfl⟩
  rw [← hM] at hM2 h2M
  obtain ⟨S, hS⟩ : ∃ S, S = con ω u₀ u₁ R 1 := ⟨_, rfl⟩
  rw [← hS] at hSfull hS3
  by_cases hlt : S < M
  · left
    obtain ⟨kq, hkq⟩ : ∃ k, k = M - S := ⟨_, rfl⟩
    have hK : 0 < kq := by omega
    obtain ⟨xq, hxq⟩ : ∃ x, x = J * S / kq := ⟨_, rfl⟩
    have hX : J * S < kq * (xq + 1) := hxq ▸ Nat.lt_mul_div_succ _ hK
    have hXb : xq ≤ 15 * (3 * 2097152) + 2097152 := by
      by_cases hJ16 : J ≤ 15
      · have h1 : J * S ≤ 15 * (3 * 2097152) := Nat.mul_le_mul hJ16 hS3
        have h2 : xq ≤ J * S := hxq ▸ Nat.div_le_self _ _
        omega
      · have hJW' : 17 * (W + 2) ≤ (J + 1) * (W + 2) := Nat.mul_le_mul_right _ (by omega)
        have hSK : S ≤ kq := by omega
        rcases Nat.eq_zero_or_pos S with hS0 | hSpos
        · rw [hxq, hS0, mul_zero, Nat.zero_div]; omega
        · have h1 : xq ≤ J := by
            rw [hxq]
            calc J * S / kq ≤ J * S / S := Nat.div_le_div_left hSK hSpos
              _ = J := Nat.mul_div_cancel J hSpos
          omega
    refine ⟨3 + xq, le_rfl, by norm_num, by omega, by rw [h3]; omega, by omega, ?_⟩
    simp only [one_mul]
    rw [← hW, ← hJ, ← hM, ← hS]
    have hMK : M = kq + S := by omega
    rw [hMK]
    have h1 : kq * (xq + 1) ≤ kq * (3 + xq) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · right
    omega

/-- **Corollary S3.** -/
theorem card_le_of_cubic (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F)
    {R : Tri} (hirr : Irreducible R) (h3 : R.natDegree = 3)
    {Vs : Finset F} {P : F → F[X]} {Az : F → Finset (Fin 2097152)}
    (hd : BadData ω u₀ u₁ R Vs P Az) (hfull : 89952 ≤ (full ω u₀ u₁ R).card) :
    Vs.card ≤ 89952 * yzd R 1 + 2172022111004 := by
  classical
  obtain ⟨Λs, hΛsub, hΛcard⟩ := Finset.exists_subset_card_eq hfull
  have h1 := card_le_of_full_subset ω u₀ u₁ hirr (by omega) hd Λs hΛsub
  have h2 := P64Shorten.card_filter_subset_le_89952 ω (by simp) u₀ u₁ Λs hΛcard Vs P Az hd.deg
    hd.card (fun z hz i hi => (hd.agree z hz i).mp hi) hd.bad
  rw [hΛcard] at h1
  omega

end P64S3
end ProximityPrize.SubmissionBinaryLower
