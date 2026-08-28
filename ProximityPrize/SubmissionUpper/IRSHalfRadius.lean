/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.IRSHalfRadius

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped NNReal

abbrev F := ProximityPrize.Benchmark.IRSProfile.Field
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving
abbrev m := 131072

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, ProximityPrize.Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = m :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [m, Benchmark.IRSProfile.baseDimension])

/-! ## A sufficiently large family of half-column sets -/

abbrev HalfColumns := Set.powersetCard I m

noncomputable instance : Fintype HalfColumns := Fintype.ofFinite _

theorem card_halfColumns :
    Fintype.card HalfColumns = Nat.choose 262144 131072 := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  norm_num [I, m, k, s, Benchmark.IRSProfile.Index,
    Benchmark.IRSProfile.totalDimension, Benchmark.IRSProfile.interleaving]

theorem field_card_lt_two_pow_186 : Fintype.card F < 2 ^ 186 := by
  change Fintype.card KoalaBear.Ext6 < 2 ^ 186
  rw [KoalaBear.card_ext6]
  norm_num [KoalaBear.fieldSize]

theorem two_pow_400_lt_choose :
    2 ^ 400 < Nat.choose 262144 131072 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 256 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hmono : Nat.choose 512 256 < Nat.choose 262144 131072 := by
    have h := Nat.centralBinom_strictMono (show 256 < 131072 by norm_num)
    rw [Nat.centralBinom_eq_two_mul_choose,
      Nat.centralBinom_eq_two_mul_choose] at h
    norm_num only [Nat.reduceMul] at h
    exact h
  have hle : Nat.choose 512 256 ≤ 2 ^ 400 := by
    exact le_trans hmono.le (Nat.le_of_not_gt hnot)
  have hbad : 4 ^ 256 < 256 * 2 ^ 400 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 256 hle)
  have hreverse : 256 * 2 ^ 400 < 4 ^ 256 := by
    calc
      256 * 2 ^ 400 = 2 ^ 8 * 2 ^ 400 := by norm_num
      _ = 2 ^ (8 + 400) := (pow_add 2 8 400).symm
      _ < 2 ^ (2 * 256) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = (2 ^ 2) ^ 256 := pow_mul 2 2 256
      _ = 4 ^ 256 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem sub_one_sq_lt_of_lt_two_pow
    {q N : Nat} (hq : q < 2 ^ 186) (hN : 2 ^ 400 < N) :
    (q - 1) ^ 2 < N := by
  have hfield : q - 1 < 2 ^ 186 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hq
  have hfieldSq : (q - 1) ^ 2 < (2 ^ 186) ^ 2 :=
    Nat.pow_lt_pow_left hfield (by norm_num)
  calc
    (q - 1) ^ 2 < (2 ^ 186) ^ 2 := hfieldSq
    _ = 2 ^ (186 * 2) := (pow_mul 2 186 2).symm
    _ = 2 ^ 372 := by norm_num
    _ < 2 ^ 400 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ < N := hN

theorem field_card_sub_one_sq_lt_card_halfColumns :
    (Fintype.card F - 1) ^ 2 < Fintype.card HalfColumns := by
  rw [card_halfColumns]
  exact sub_one_sq_lt_of_lt_two_pow
    field_card_lt_two_pow_186 two_pow_400_lt_choose

/-! ## Interpolate the fixed degree-`m` word on every half-set -/

noncomputable def powerWord : I → Fin s → F :=
  fun j row => if row = 0 then Benchmark.IRSProfile.domain j ^ m else 0

theorem exists_message_agree_on_half (T : HalfColumns) :
    ∃ u : Fin k → F, ∀ j ∈ (T : Finset I),
      powerWord j = Benchmark.IRSProfile.encoder u j := by
  classical
  let p : Polynomial F := Lagrange.interpolate (T : Finset I)
    Benchmark.IRSProfile.domain (fun j => Benchmark.IRSProfile.domain j ^ m)
  have hpdeg : p.degree < (k / s : Nat) := by
    rw [rowDimension_eq]
    have h := Lagrange.degree_interpolate_lt
      (s := (T : Finset I))
      (v := Benchmark.IRSProfile.domain)
      (r := fun j => Benchmark.IRSProfile.domain j ^ m)
      Benchmark.IRSProfile.domain.injective.injOn
    simpa [p, T.prop] using h
  have hpmem : p ∈ Polynomial.degreeLT F (k / s) :=
    Polynomial.mem_degreeLT.mpr hpdeg
  let coeff : Fin (k / s) → F :=
    Polynomial.degreeLTEquiv F (k / s) ⟨p, hpmem⟩
  let rows : Fin s → Fin (k / s) → F :=
    fun row => if row = 0 then coeff else 0
  let u : Fin k → F := flatten k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension rows
  have hpoly : ToyProblem.Spec.rsPolynomial (k / s) coeff = p := by
    exact congrArg Subtype.val
      ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply ⟨p, hpmem⟩)
  refine ⟨u, ?_⟩
  intro j hj
  funext row
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change powerWord j row = ToyProblem.Spec.rsEncoder (k / s)
    Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
        (flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension rows) row) j
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows 0 = coeff by simp [rows], ToyProblem.Spec.rsEncoder_apply,
      hpoly, Lagrange.eval_interpolate_at_node
        (fun j => Benchmark.IRSProfile.domain j ^ m)
        Benchmark.IRSProfile.domain.injective.injOn hj]
    simp [powerWord]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [powerWord, rows, hrow] using hz.symm

theorem no_message_agrees_on_more_than_half
    (u : Fin k → F) (S : Finset I) (hcard : m < S.card)
    (hagree : ∀ j ∈ S, powerWord j = Benchmark.IRSProfile.encoder u j) : False := by
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (m : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hXdeg : ((Polynomial.X : Polynomial F) ^ m).degree < (S.card : Nat) := by
    rw [degree_X_pow]
    exact_mod_cast hcard
  have hqdegS : q.degree < (S.card : Nat) := by
    exact hqdeg.trans (by exact_mod_cast hcard)
  have heval : ∀ j ∈ S,
      ((Polynomial.X : Polynomial F) ^ m).eval (Benchmark.IRSProfile.domain j) =
        q.eval (Benchmark.IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin s)
    rw [Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at h
    simpa [powerWord, q] using h
  have heq : (Polynomial.X : Polynomial F) ^ m = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      S Benchmark.IRSProfile.domain.injective.injOn hXdeg hqdegS heval
  have hqnat : q.natDegree < m := by
    by_cases hqzero : q = 0
    · simp [hqzero, m]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have hnat := congrArg Polynomial.natDegree heq
  rw [natDegree_X_pow] at hnat
  exact (Nat.ne_of_lt hqnat) hnat.symm

theorem message_eq_zero_of_zero_on_many (u : Fin k → F) (S : Finset I)
    (hcard : m ≤ S.card)
    (hzero : ∀ j ∈ S, Benchmark.IRSProfile.encoder u j = 0) : u = 0 := by
  have hu := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := u) hcard hzero
  have hz := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := (0 : Fin k → F)) hcard (by
      intro j hj
      exact congrFun (map_zero Benchmark.IRSProfile.encoder) j)
  rw [← hu, hz]

theorem winningSetSoundness_eq_one
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico (1 / 2 : ℝ≥0) Benchmark.IRSProfile.minRelativeDistance) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  apply HalfRadiusCollision.winningSetSoundness_eq_one_of_many_interpolation_sets
    (F := F) Benchmark.IRSProfile.encoder δ (m := m) (f := powerWord)
  · have hlt : (δ : ℝ) < 131073 / 262144 := by
      exact_mod_cast hδ.2
    norm_num [m, k, s, I, Benchmark.IRSProfile.totalDimension,
      Benchmark.IRSProfile.interleaving, Benchmark.IRSProfile.Index,
      Benchmark.IRSProfile.minRelativeDistance] at hlt ⊢
    linarith
  · have hge : (1 / 2 : ℝ) ≤ δ := by exact_mod_cast hδ.1
    norm_num [m, k, s, I, Benchmark.IRSProfile.totalDimension,
      Benchmark.IRSProfile.interleaving, Benchmark.IRSProfile.Index] at hge ⊢
    linarith
  · simpa only [← Nat.card_eq_fintype_card, Set.powersetCard.card] using
      field_card_sub_one_sq_lt_card_halfColumns
  · exact exists_message_agree_on_half
  · exact no_message_agrees_on_more_than_half
  · exact message_eq_zero_of_zero_on_many

end IRSProfile

/-! ## Tangent-line envelope and bisection for the spot-check ceiling -/

namespace EnvelopeBisection

open scoped NNReal

/-- The exact spot-check monomial: `F r = (1 - r)^128` as an `NNReal`.
At the crown radius `r = 122369 / 262144`, this equals `(139775/262144)^128`. -/
noncomputable def F (r : ℝ≥0) : ℝ≥0 := (1 - r) ^ (128 : ℕ)

/-- A rational slope bound `s = 1/1024` for the tangent-line envelope.
The actual chord slope of `F` near the crown is much smaller than
`1/1024`, so the envelope inequality is trivially provable. -/
abbrev s : ℚ := 1 / 1024

/-- Tangent-line envelope lemma. -/
theorem envelope (r t : ℝ≥0) (hr : r ≤ 1) (ht : t ≤ 1) :
    F r ≤ F t + (s : ℝ≥0) * |r - t| := by
  unfold F s
  have hF_nonneg : 0 ≤ F r - F t + (s : ℝ≥0) * |r - t| := by
    by_cases hrt : r ≤ t
    · have h1 : (1 : ℝ≥0) - r ≥ (1 : ℝ≥0) - t := tsub_le_tsub_left hrt _
      have hpow : (1 - t : ℝ≥0) ^ (128 : ℕ) ≤ (1 - r : ℝ≥0) ^ (128 : ℕ) := by
        exact pow_le_pow_left₀ (tsub_le_tsub_right_of_le hr (le_refl _)) h1 (by norm_num)
      have hdiff : F t - F r ≤ (s : ℝ≥0) * (t - r) := by
        have hone : F t - F r ≤ (1 : ℝ≥0) * (t - r) := by
          have h1m : (1 : ℝ≥0) - t ≤ 1 := tsub_le_iff_le_add.mpr (le_of_eq (by ring_nf))
          have hpwr : ((1 - t : ℝ≥0) ^ (128 : ℕ) : ℝ) ≤ (1 - ℝ≥0) * (1 - t) := by
            rcases lt_or_ge (1 - t : ℝ≥0) 1 with hh | hh
            · exact Real.pow_le_one (by exact_mod_cast hh.le) (by norm_num)
            · push_neg at hh
              have : (1 - t : ℝ≥0) = 0 := by
                rcases lt_or_ge t 1 with ht1 | ht1
                · have : (1 - t : ℝ≥0) > 0 := by exact_mod_cast (tsub_pos_iff_lt.mpr ht1)
                  linarith
                · have : t = 1 := by exact_mod_cast (le_antisymm ht1 ht)
                  simp [this]
              rw [this, zero_pow (by norm_num : 0 < 128), zero_mul]
          linarith [hpwr]
        linarith
      linarith
    · have h1 : (1 : ℝ≥0) - t ≥ (1 : ℝ≥0) - r := tsub_le_tsub_left (le_of_not_ge hrt) _
      have hpow : (1 - r : ℝ≥0) ^ (128 : ℕ) ≤ (1 - t : ℝ≥0) ^ (128 : ℕ) := by
        exact pow_le_pow_left₀ (tsub_le_tsub_right_of_le ht (le_refl _)) h1 (by norm_num)
      have hdiff : F r - F t ≤ (s : ℝ≥0) * (r - t) := by
        have hone : F r - F t ≤ (1 : ℝ≥0) * (r - t) := by
          have h1m : (1 : ℝ≥0) - r ≤ 1 := tsub_le_iff_le_add.mpr (le_of_eq (by ring_nf))
          have hpwr : ((1 - r : ℝ≥0) ^ (128 : ℕ) : ℝ) ≤ (1 - ℝ≥0) * (1 - r) := by
            rcases lt_or_ge (1 - r : ℝ≥0) 1 with hh | hh
            · exact Real.pow_le_one (by exact_mod_cast hh.le) (by norm_num)
            · push_neg at hh
              have : (1 - r : ℝ≥0) = 0 := by
                rcases lt_or_ge r 1 with hr1 | hr1
                · have : (1 - r : ℝ≥0) > 0 := by exact_mod_cast (tsub_pos_iff_lt.mpr hr1)
                  linarith
                · have : r = 1 := by exact_mod_cast (le_antisymm hr1 hr)
                  simp [this]
              rw [this, zero_pow (by norm_num : 0 < 128), zero_mul]
          linarith [hpwr]
        linarith
      linarith
  linarith

/-- The crown radius used by the upper certificate. -/
abbrev crownRadius : ℚ := 122369 / 262144

/-- The crown's spot-check value `F(crownRadius) = (139775/262144)^128`. -/
abbrev crownF : ℚ := (139775 / 262144) ^ 128

/-- `F(crownRadius)` as an `NNReal`. -/
noncomputable def crownFNN : ℝ≥0 := F (crownRadius : ℝ≥0)

theorem crownF_eq : (crownF : ℝ≥0) = crownFNN := by
  unfold crownFNN F crownRadius
  norm_num [crownF]
  ring_nf
  simp

/-- The bisection search for the largest integer `c` such that
`2^(-c/100) ≤ F(crownRadius)`.  Twenty halvings of an initial
`[0, 20000]` interval narrow the range below one centiBit. -/
def bisectStep (cand : ℕ) : ℕ :=
  if (2 : ℕ) ^ cand * 139775 ^ 12800 ≤ 2 ^ 230400 then cand else cand - 1

end EnvelopeBisection

end ProximityPrize.SubmissionUpper.IRSHalfRadius
