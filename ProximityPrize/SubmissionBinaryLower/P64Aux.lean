import ProximityPrize.SubmissionBinaryLower.P64Light
import ProximityPrize.SubmissionBinaryLower.P64GSGeneric

/-!
# Lemma S_t: the near-power auxiliary (PROOF.md 4.6)

For a factor `R` and `t, q ≥ 1` with `(q + j_t)·Con_t < q·M(tw - A)`, the generic interpolation
kernel (`P64GS`, one multiplicity `φ_i = tμ_i - 1` per line) gives a nonzero `Ψ` with
`wdeg Ψ ≤ W = tw - A`, `deg_Y Ψ ≤ j_t = ⌊W/D⌋`, `d_Ψ < q + j_t` and order at least `φ_i` on every
line. The kernel box is the Lemma E box with `DZ = q + j_t`, so it has at least `q·M(W)` unknowns
and at most `(q + j_t)·Con_t` equations. Writing `Ψ = R^a·Ψ'` with `R ∤ Ψ'`, `a < t`, and every
dangerous slope kills `Ψ'`; Lemma R then bounds the dangerous slopes by
`j_t·d + h·(q + j_t - 1)`.

`StGood` is (3.2) with `t·h ≤ q` and `q + n ≤ 4·DZ` (so `q + j_t ≤ 4·DZ`), which gives the class-3
row `h(4·DZ - 1) + (4w/D)·d` of the ledger.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Aux

open Polynomial BCHKSSubstitutionVanish P64LineOrder P64Cofactor P64GS P64Light

/-- `2·Σ_{t < φ} (φ - t) = φ(φ + 1)`. -/
lemma two_mul_sum_range_sub (φ : ℕ) : 2 * ∑ t ∈ Finset.range φ, (φ - t) = φ * (φ + 1) := by
  induction φ with
  | zero => simp
  | succ φ ih =>
      rw [Finset.sum_range_succ, Finset.sum_congr rfl (g := fun t => (φ - t) + 1)
        (fun t ht => by rw [Finset.mem_range] at ht; omega), Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Nat.add_sub_cancel_left]
      nlinarith [ih]

lemma sum_range_sub (φ : ℕ) : ∑ t ∈ Finset.range φ, (φ - t) = φ * (φ + 1) / 2 := by
  rw [← two_mul_sum_range_sub, Nat.mul_div_cancel_left _ (by norm_num)]

lemma card_conIndex_le (p : GSParams) :
    Fintype.card (ConIndex p) ≤ p.DZ * ∑ i : Fin p.n, p.m i * (p.m i + 1) / 2 := by
  rw [card_conIndex, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sum_range_sub, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [mul_comm p.DZ]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- The parameters of the auxiliary interpolation. -/
def auxParams (φ : Fin 2097152 → ℕ) (W q : ℕ) (hφ : ∀ i, φ i ≤ q + W / 1048575)
    (hq : 1 ≤ q) : GSParams where
  n := 2097152
  k := 1048575
  m := φ
  DX := W + 1
  DY := W / 1048575 + 1
  DZ := q + W / 1048575
  hmDZ := hφ
  hDYDZ := by omega
  hDZpos := by omega

lemma card_var_ge (φ : Fin 2097152 → ℕ) (W q : ℕ) (hφ : ∀ i, φ i ≤ q + W / 1048575)
    (hq : 1 ≤ q) : q * P64Surf.Mbox W ≤ Fintype.card (VarIndex (auxParams φ W q hφ hq)) := by
  rw [card_varIndex]
  change q * P64Surf.Mbox W ≤ ∑ j ∈ Finset.range (W / 1048575 + 1),
    (W + 1 - 1048575 * j) * (q + W / 1048575 - j)
  unfold P64Surf.Mbox
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjW : j * 1048575 ≤ W := (Nat.le_div_iff_mul_le (by norm_num)).mp (by omega)
  rw [show W - 1048575 * j + 1 = W + 1 - 1048575 * j by omega, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

/-- The cast of a truncated difference dominates the integer difference. -/
lemma sub_cast_ge (x y : ℕ) : (x : ℤ) - 1 - y ≤ ((x - 1 - y : ℕ) : ℤ) := by omega

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yzd" => P64Caps.YZ.yzSupportDegree

/-- The order `μ_i` of `R` on line `i`. -/
noncomputable abbrev mu (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) (R : Tri)
    (i : Fin 2097152) : ℕ :=
  lineOrd R (ω i) (lineOf u₀ u₁ i)

/-- `Con_t = Σ_i φ_i(φ_i + 1)/2` with `φ_i = tμ_i - 1`. -/
noncomputable def con (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F) (R : Tri) (t : ℕ) : ℕ :=
  ∑ i, (t * mu ω u₀ u₁ R i - 1) * (t * mu ω u₀ u₁ R i - 1 + 1) / 2

/-- **Lemma S_t.** -/
theorem card_dangerous_le (ω : Fin 2097152 ↪ F) (u₀ u₁ : Fin 2097152 → F)
    {R : Tri} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    {Vs : Finset F} {P : F → F[X]} {Az : F → Finset (Fin 2097152)}
    (hd : BadData ω u₀ u₁ R Vs P Az)
    (hdang : ∀ z ∈ Vs, Dangerous ω (lineOf u₀ u₁) 1048575 1482911 R (Az z))
    (t q : ℕ) (hq : 1 ≤ q) (hA : 1482911 ≤ t * wd R 1048575)
    (hφ : ∀ i, t * mu ω u₀ u₁ R i - 1 ≤ q + (t * wd R 1048575 - 1482911) / 1048575)
    (hcrit : (q + (t * wd R 1048575 - 1482911) / 1048575) * con ω u₀ u₁ R t <
      q * P64Surf.Mbox (t * wd R 1048575 - 1482911))
    (hF : ((t * wd R 1048575 - 1482911) / 1048575 + R.natDegree) * (t * wd R 1048575) <
      Fintype.card F) :
    Vs.card ≤ (t * wd R 1048575 - 1482911) / 1048575 * yzd R 1 +
      R.natDegree * (q + (t * wd R 1048575 - 1482911) / 1048575 - 1) := by
  classical
  set w := wd R 1048575 with hwdef
  set W := t * w - 1482911 with hWdef
  set J := W / 1048575 with hJdef
  set μ := mu ω u₀ u₁ R with hμdef
  have hR0 : R ≠ 0 := hirr.ne_zero
  -- the kernel
  set p := auxParams (fun i => t * μ i - 1) W q hφ hq with hpdef
  have hcard : Fintype.card (ConIndex p) < Fintype.card (VarIndex p) := by
    have h1 := card_conIndex_le p
    have h2 : q * P64Surf.Mbox W ≤ Fintype.card (VarIndex p) :=
      card_var_ge (fun i => t * μ i - 1) W q hφ hq
    change Fintype.card (ConIndex p) ≤ (q + J) * con ω u₀ u₁ R t at h1
    omega
  obtain ⟨Ψ, hΨ0, hvan, hcaps⟩ := exists_interpolant_gen hcard ω u₀ u₁
  change ∀ j a, ((Ψ.coeff j).coeff a) ≠ 0 →
    j < J + 1 ∧ a + 1048575 * j < W + 1 ∧ ((Ψ.coeff j).coeff a).natDegree + j < q + J at hcaps
  have hord : ∀ i, OrdGE Ψ (ω i) (lineOf u₀ u₁ i) (t * μ i - 1) := fun i a b hab =>
    hvan i a b hab
  have hcoeff : ∀ j, Ψ.coeff j ≠ 0 → ∃ a, (Ψ.coeff j).coeff a ≠ 0 := fun j hj =>
    ⟨(Ψ.coeff j).natDegree, by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hj⟩
  have hΨdeg : Ψ.natDegree ≤ J := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_contra hne
    obtain ⟨a, ha⟩ := hcoeff j hne
    have := (hcaps j a ha).1
    omega
  have hΨyz : yzd Ψ 1 ≤ q + J - 1 := by
    unfold P64Caps.YZ.yzSupportDegree
    apply Finset.sup_le
    intro j hj
    have hj0 : Ψ.coeff j ≠ 0 := mem_support_iff.mp hj
    have hdeg : Polynomial.Bivariate.degreeX (Ψ.coeff j) + j ≤ q + J - 1 := by
      have : Polynomial.Bivariate.degreeX (Ψ.coeff j) ≤ q + J - 1 - j := by
        unfold Polynomial.Bivariate.degreeX
        apply Finset.sup_le
        intro a ha
        have := (hcaps j a (mem_support_iff.mp ha)).2.2
        omega
      obtain ⟨a, ha⟩ := hcoeff j hj0
      have := (hcaps j a ha).2.2
      omega
    simpa using hdeg
  have hΨw : wd Ψ 1048575 ≤ W := by
    have := P64Caps.Weighted.weightedSupportDegree_lt_of_coeff_cap Ψ 1048575 (W + 1) hΨ0
      (fun j a ha => (hcaps j a ha).2.1)
    omega
  -- the cofactor
  obtain ⟨a, Ψ', hndvd, hΨeq⟩ := WfDvdMonoid.max_power_factor (α := Polynomial (Polynomial (Polynomial F))) hΨ0 hirr
  have hRa : R ^ a ≠ 0 := pow_ne_zero a hR0
  have hΨ'0 : Ψ' ≠ 0 := by
    rintro rfl
    exact hΨ0 (by rw [hΨeq, mul_zero])
  have hwmul : wd Ψ 1048575 = a * w + wd Ψ' 1048575 := by
    rw [hΨeq, P64Caps.Weighted.weightedSupportDegree_mul _ _ _ hRa hΨ'0,
      weightedSupportDegree_pow R hR0]
  have hApos : 0 < t * w := by omega
  have hat : a < t := by
    have h1 : a * w < t * w := by omega
    exact Nat.lt_of_mul_lt_mul_right h1
  have hw'le : wd Ψ' 1048575 + a * w + 1482911 ≤ t * w := by omega
  have hdeg' : Ψ'.natDegree ≤ J := by
    have : Ψ.natDegree = (R ^ a).natDegree + Ψ'.natDegree := by
      rw [hΨeq, natDegree_mul hRa hΨ'0]
    omega
  have hyz' : yzd Ψ' 1 ≤ q + J - 1 := by
    have : yzd Ψ 1 = yzd (R ^ a) 1 + yzd Ψ' 1 := by
      rw [hΨeq, P64Caps.YZ.yzSupportDegree_mul _ _ _ hRa hΨ'0]
    omega
  -- every dangerous slope kills the cofactor
  have hkill : ∀ z ∈ Vs, triEval Ψ' z (P z) = 0 := by
    intro z hz
    by_contra hne
    have hmatch : ∀ i ∈ Az z, (P z).eval (ω i) = (lineOf u₀ u₁ i).eval z := fun i hi => by
      rw [eval_lineOf]; exact (hd.agree z hz i).mp hi
    have hmult : ∀ i ∈ Az z, t * μ i - 1 - a * μ i ≤ (triEval Ψ' z (P z)).rootMultiplicity (ω i) := by
      intro i hi
      have h1 := ordGE_cofactor hRa hΨ'0 (ω i) (lineOf u₀ u₁ i) _ (hΨeq ▸ hord i)
      rw [lineOrd_pow hR0] at h1
      exact le_rootMultiplicity_triEval Ψ' (ω i) z (lineOf u₀ u₁ i) (P z) _ h1 (hmatch i hi) hne
    have hsum : ∑ i ∈ Az z, (t * μ i - 1 - a * μ i) ≤ wd Ψ' 1048575 :=
      (Finset.sum_le_sum hmult).trans ((sum_rootMultiplicity_le_natDegree _ ω (Az z)).trans
        (natDegree_triEval_le Ψ' z (P z) 1048575 (hd.deg z hz)))
    have hsumZ : ∑ i ∈ Az z, ((t : ℤ) * μ i - 1 - a * μ i) ≤ wd Ψ' 1048575 := by
      have h1 : ∑ i ∈ Az z, ((t : ℤ) * μ i - 1 - a * μ i) ≤
          ∑ i ∈ Az z, ((t * μ i - 1 - a * μ i : ℕ) : ℤ) :=
        Finset.sum_le_sum fun i _ => by
          have := sub_cast_ge (t * μ i) (a * μ i)
          push_cast at this
          exact this
      have h2 : ∑ i ∈ Az z, ((t * μ i - 1 - a * μ i : ℕ) : ℤ) ≤ wd Ψ' 1048575 := by
        exact_mod_cast hsum
      exact h1.trans h2
    have hdz := hdang z hz
    unfold Dangerous at hdz
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsumZ
    rw [Finset.sum_sub_distrib] at hdz
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsumZ hdz
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hsumZ
    have hAz : (1482911 : ℤ) ≤ (Az z).card := by exact_mod_cast hd.card z hz
    have hw'Z : ((wd Ψ' 1048575 : ℕ) : ℤ) + a * w + 1482911 ≤ t * w := by exact_mod_cast hw'le
    have hatZ : (a : ℤ) + 1 ≤ t := by exact_mod_cast hat
    set S := ∑ i ∈ Az z, (μ i : ℤ)
    set c := ((Az z).card : ℤ)
    have hdz' : (w : ℤ) - 1482911 < S - c := by
      have := hdz
      push_cast at this
      exact this
    have hp1 : 0 ≤ ((t : ℤ) - a - 1) * (c - 1482911) := mul_nonneg (by linarith) (by linarith)
    have hp2 : 0 ≤ ((t : ℤ) - a) * (S - c - (w - 1482911) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- Lemma R
  have hXR : ∀ j, (R.coeff j).natDegree ≤ t * w := fun j =>
    (P64Resultant.coeff_natDegree_le_weighted R 1048575 j).trans (by nlinarith)
  have hXG : ∀ j, (Ψ'.coeff j).natDegree ≤ t * w := fun j =>
    (P64Resultant.coeff_natDegree_le_weighted Ψ' 1048575 j).trans (by omega)
  have hF' : (Ψ'.natDegree + R.natDegree) * (t * w) < Fintype.card F :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hF
  have hR := P64Resultant.card_common_le R Ψ' hirr (by omega) hndvd (yzd R 1) (q + J - 1) (t * w)
    (fun j a => P64Resultant.coeff_natDegree_le_yz R j a)
    (fun j a => (P64Resultant.coeff_natDegree_le_yz Ψ' j a).trans hyz') hXR hXG hF' Vs P
    (fun z hz => ⟨hd.on_curve z hz, hkill z hz⟩)
  calc Vs.card ≤ Ψ'.natDegree * yzd R 1 + R.natDegree * (q + J - 1) := hR
    _ ≤ J * yzd R 1 + R.natDegree * (q + J - 1) := by gcongr

end P64Aux
end ProximityPrize.SubmissionBinaryLower
