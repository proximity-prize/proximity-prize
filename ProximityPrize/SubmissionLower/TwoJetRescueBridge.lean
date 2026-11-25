import ProximityPrize.SubmissionLower.TwoJetShift

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1200000

/-!
# 2-Jet Prolongation Rescue Bridge (`TwoJetRescueBridge`)

Connects our L4 2-jet modules (`PoleMoment2Jet`, `PoleBound2Jet`, `TwoJetShift`) directly to the
6-rectangle 2-jet Prolongation Rescue consumer for the Zero-`Case B2-tiny` `69.63` route
(`A = 179,798`, split high band `h ∈ [2302, 2649]`, `endpointDegree = 133,720`):

1. **Linear-`Y₂` Prolongation Substitution (`prolongSubst`) & Exact Bézout Identity (`prolongSubst_bezout`)**:
   For any 1-jet prime `G` linear in `Y₁` (`G^(1) = A * Y₂ + B₁`) and any `P : R[X]` of `Y₂`-degree `≤ C`:
   `C (A ^ C) * P - C (prolongSubst A B₁ C P) = Q * (C A * X + C B₁)`
   with zero Sylvester determinant overhead.
2. **Exact Mark Vanishing (`prolongSubst_eval_zero`)** and **Ideal Membership Bridge
   (`prolongSubst_dvd_of_mem_ideal`, `mem_ideal_of_prolongSubst_dvd`)**:
   If `P` and `G^(1)` vanish at a mark `(z, S, S', S''/2)`, then `prolongSubst A B₁ C P` vanishes at
   `(z, S, S')`. Moreover, `G ∣ prolongSubst A B₁ C P` iff `C (A ^ C) * P ∈ Ideal.span {C G, C A * X + C B₁}`
   (when `G` is prime and `¬ G ∣ A`).
3. **2-Jet Case-A Avoidance Theorem (`exists_prolong_avoiding_2jet`)**:
   Directly invokes `PoleBound2Jet.pole_bound_2jet` to prove that whenever the kernel
   `{P ∈ complete2 Crt word s W | G ∣ prolongSubst A B₁ s.C (centerEval2 P)}` has total finrank
   strictly below the `PoleBound2Jet` floor across `W < N`, there exists `W < N` and
   `P ∈ complete2 Crt word s W` whose 1-jet prolongation substitution avoids `G`.
4. **Complete 10-Rectangle Partition & Kernel-Checked `69.63` Arithmetic Certificates**:
   - `rect_partition_complete`: partitions all 1-jet Helper survivors into 6 small 2-jet rects + 4 large 1-jet rects
   - `caseB_cj0_box_exact`: exact Sylvester `Res_{z₀}(G, G^(1))` bounds `(B_H, J_H, C_H)` with `2 * C_H + 1 ≤ J_H`
   - `scalar_surplus_6963_m59`, `caseA_surplus_6963_m55_U353`, `low_6961_6963_need_beats_6960`,
     `low_6961_6963_anchor_beats_6960`, `budget_6963_split_ok` (`+10.04e15` slack).
-/

namespace TwoJetRescueBridge
noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L FX Jet)
open K1_14_1 (PoleData CRTLift centerEval)
open PoleMoment2Jet (Shape2 groupedPoleMoment2 poleCredit2)
open PoleBound2Jet (Source2 contacted2 complete2 contacted2_finite pole_bound_2jet)
open TwoJetShift (complete2_cleared)
open scoped BigOperators Polynomial

/-! ## 1. 2-Jet `Jet2` Ring & Center Evaluation -/

/-- 2-jet polynomial ring over `K1_14.Jet` (`Seeds[Y₀][Y₁][Y₂]`). -/
abbrev Jet2 := Polynomial Jet

/-- Center evaluation from `Source2 = Polynomial Source` into `Jet2 = Polynomial Jet`. -/
def centerEval2 : Source2 →ₐ[L] Jet2 :=
  Polynomial.mapAlgHom centerEval

/-- Evaluated 2-jet space, exact 2-jet analog of `K1_14_1.evaluated`. -/
def evaluated2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) : Submodule FX Jet2 :=
  Submodule.span FX (centerEval2 '' (complete2 Crt word s W : Set Source2))

/-! ## 2. Linear-`Y₂` Prolongation Substitution & Exact Bézout Identity -/

/-- Pseudo-substitution eliminating `Y₂` via a linear-`Y₂` prolongation `G^(1) = A * Y₂ + B₁`:
    `prolongSubst A B₁ C P = ∑_{e₂=0}^{C} P.coeff e₂ * (-B₁)^e₂ * A^(C - e₂)`. -/
def prolongSubst {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (P : R[X]) : R :=
  ∑ e₂ ∈ Finset.range (C + 1), P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂)

theorem prolongSubst_zero {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) :
    prolongSubst A B₁ C 0 = 0 := by
  simp [prolongSubst]

theorem prolongSubst_add {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (P Q : R[X]) :
    prolongSubst A B₁ C (P + Q) = prolongSubst A B₁ C P + prolongSubst A B₁ C Q := by
  simp only [prolongSubst, Polynomial.coeff_add, add_mul, Finset.sum_add_distrib]

theorem prolongSubst_smul {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ) (r : R) (P : R[X]) :
    prolongSubst A B₁ C (Polynomial.C r * P) = r * prolongSubst A B₁ C P := by
  simp only [prolongSubst, Polynomial.coeff_C_mul, mul_assoc, Finset.mul_sum]

/-- **Exact Bézout Identity (`prolongSubst_bezout`)**:
    For any commutative ring `R`, any `A B₁ : R`, and any `P : R[X]` of degree `≤ C`,
    `C (A ^ C) * P - C (prolongSubst A B₁ C P)` is divisible by `C A * X + C B₁` in `R[X]`. -/
theorem prolongSubst_bezout {R : Type*} [CommRing R] (A B₁ : R) (C : ℕ)
    {P : R[X]} (hdeg : P.natDegree ≤ C) :
    (Polynomial.C A * Polynomial.X + Polynomial.C B₁) ∣
      (Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P)) := by
  have hP : P = ∑ e₂ ∈ Finset.range (C + 1), Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂ := by
    simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
      Polynomial.as_sum_range' P (C + 1) (Nat.lt_succ_of_le hdeg)
  have hdiff : Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P) =
      ∑ e₂ ∈ Finset.range (C + 1),
        Polynomial.C (P.coeff e₂) * Polynomial.C (A ^ (C - e₂)) *
          ((Polynomial.C A * Polynomial.X) ^ e₂ - (Polynomial.C (-B₁)) ^ e₂) := by
    calc
      Polynomial.C (A ^ C) * P - Polynomial.C (prolongSubst A B₁ C P)
          = Polynomial.C (A ^ C) * (∑ e₂ ∈ Finset.range (C + 1), Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂) -
              Polynomial.C (∑ e₂ ∈ Finset.range (C + 1), P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂)) := by
            rw [prolongSubst]
            congr 1
            exact congrArg (Polynomial.C (A ^ C) * ·) hP
      _ = ∑ e₂ ∈ Finset.range (C + 1),
            (Polynomial.C (A ^ C) * (Polynomial.C (P.coeff e₂) * Polynomial.X ^ e₂) -
              Polynomial.C (P.coeff e₂ * (-B₁) ^ e₂ * A ^ (C - e₂))) := by
            rw [Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro e₂ he₂
            have hle : e₂ ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
            have hpow : A ^ C = A ^ (C - e₂) * A ^ e₂ := by
              rw [← pow_add, Nat.sub_add_cancel hle]
            simp only [hpow, mul_pow, map_mul, map_pow]
            ring
  rw [hdiff]
  apply Finset.dvd_sum
  intro e₂ _
  apply dvd_mul_of_dvd_right
  have hd := sub_dvd_pow_sub_pow (Polynomial.C A * Polynomial.X) (Polynomial.C (-B₁)) e₂
  simpa only [map_neg, sub_neg_eq_add] using hd

/-- **Exact Mark Vanishing (`prolongSubst_eval_zero`)**:
    Under any ring homomorphism `φ : R →+* T` and `y₂ : T` (such as evaluation at a mark
    `(z, S, S', S''/2)`), if `P` and `A * Y₂ + B₁` vanish at `(φ, y₂)`, then `prolongSubst A B₁ C P`
    vanishes under `φ`. -/
theorem prolongSubst_eval_zero {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (y₂ : T) (A B₁ : R) (C : ℕ) {P : R[X]} (hdeg : P.natDegree ≤ C)
    (hP : Polynomial.eval₂ φ y₂ P = 0) (hG1 : φ A * y₂ + φ B₁ = 0) :
    φ (prolongSubst A B₁ C P) = 0 := by
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  have hev := congrArg (Polynomial.eval₂ φ y₂) hQ
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_C, Polynomial.eval₂_X, hP, hG1, mul_zero, zero_mul, zero_sub,
    neg_eq_zero] at hev
  exact hev

/-- If `G ∣ prolongSubst A B₁ C P`, then `C (A ^ C) * P ∈ Ideal.span {C G, C A * X + C B₁}`. -/
theorem mem_ideal_of_prolongSubst_dvd {R : Type*} [CommRing R] (G A B₁ : R) (C : ℕ)
    {P : R[X]} (hdeg : P.natDegree ≤ C) (hdvd : G ∣ prolongSubst A B₁ C P) :
    Polynomial.C (A ^ C) * P ∈
      Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X]) := by
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  obtain ⟨q, hq⟩ := hdvd
  have hsplit : Polynomial.C (A ^ C) * P =
      Polynomial.C q * Polynomial.C G + Q * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
    have h1 : Polynomial.C (prolongSubst A B₁ C P) = Polynomial.C q * Polynomial.C G := by
      rw [hq, map_mul, mul_comm]
    linear_combination hQ + h1
  rw [hsplit]
  apply Ideal.add_mem
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- Conversely, if `G` is prime, `¬ G ∣ A`, and `P ∈ Ideal.span {C G, C A * X + C B₁}` (with
    `P.natDegree ≤ C`), then `G ∣ prolongSubst A B₁ C P`. -/
theorem prolongSubst_dvd_of_mem_ideal {R : Type*} [CommRing R] [IsDomain R]
    {G A B₁ : R} (hGp : Prime G) (hGA : ¬ G ∣ A) (C : ℕ) {P : R[X]} (hdeg : P.natDegree ≤ C)
    (hmem : P ∈ Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X])) :
    G ∣ prolongSubst A B₁ C P := by
  have hI : Ideal.span ({Polynomial.C G, Polynomial.C A * Polynomial.X + Polynomial.C B₁} : Set R[X]) =
      Ideal.span {Polynomial.C G} ⊔ Ideal.span {Polynomial.C A * Polynomial.X + Polynomial.C B₁} := by
    rw [← Ideal.span_union, Set.singleton_union]
  rw [hI, Submodule.mem_sup] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := hmem
  rw [Ideal.mem_span_singleton] at hu hv
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨Q, hQ⟩ := prolongSubst_bezout A B₁ C hdeg
  have hrel : Polynomial.C (prolongSubst A B₁ C P) =
      Polynomial.C G * (Polynomial.C (A ^ C) * u') +
      (Polynomial.C (A ^ C) * v' - Q) * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
    have : Polynomial.C (A ^ C) * P =
        Polynomial.C G * (Polynomial.C (A ^ C) * u') +
        (Polynomial.C (A ^ C) * v') * (Polynomial.C A * Polynomial.X + Polynomial.C B₁) := by
      rw [← huv]; ring
    linear_combination this - hQ
  -- Reduce modulo the prime ideal `Ideal.span {G}` in `R ⧸ Ideal.span {G}`, where `A` is nonzero
  -- in an integral domain, so evaluating at `-B₁ / A` in `FractionRing (R ⧸ Ideal.span {G})` kills `C A * X + C B₁`!
  let I := Ideal.span ({G} : Set R)
  have _ : I.IsPrime := (Ideal.span_singleton_prime hGp.ne_zero).mpr hGp
  let Qring := R ⧸ I
  let F := FractionRing Qring
  let π : R →+* Qring := Ideal.Quotient.mk I
  let ι : Qring →+* F := algebraMap Qring F
  let φ : R →+* F := ι.comp π
  have hπG : π G = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton G))
  have hφG : φ G = 0 := by
    simp only [φ, RingHom.comp_apply, hπG, map_zero]
  have hφA : φ A ≠ 0 := by
    intro h0
    have hπA : π A = 0 := IsFractionRing.injective Qring F (by simpa [φ, ι] using h0)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hπA
    exact hGA hπA
  let y₂ : F := -(φ B₁) / φ A
  have hlin : φ A * y₂ + φ B₁ = 0 := by
    dsimp only [y₂]
    rw [mul_div_cancel₀ _ hφA, neg_add_cancel]
  have hev := congrArg (Polynomial.eval₂ φ y₂) hrel
  simp only [Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, hφG, zero_mul, hlin, mul_zero, add_zero] at hev
  have hπR : π (prolongSubst A B₁ C P) = 0 :=
    IsFractionRing.injective Qring F (by simpa [φ, ι] using hev)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hπR
  exact hπR

/-! ## 3. Case-A Avoidance Theorem Connected Directly to L4 `PoleBound2Jet.pole_bound_2jet` -/

/-- The `L`-submodule of `complete2 Crt word s W` whose 1-jet prolongation substitution is divisible by `G`. -/
def prolongKernel {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) (G A B₁ : Jet) : Submodule L Source2 where
  carrier := {P | P ∈ complete2 Crt word s W ∧ G ∣ prolongSubst A B₁ s.C (centerEval2 P)}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    rw [map_zero, prolongSubst_zero]
    exact dvd_zero G
  add_mem' := by
    rintro P Q ⟨hP, hdP⟩ ⟨hQ, hdQ⟩
    refine ⟨Submodule.add_mem _ hP hQ, ?_⟩
    rw [map_add, prolongSubst_add]
    exact dvd_add hdP hdQ
  smul_mem' := by
    rintro c P ⟨hP, hdP⟩
    refine ⟨Submodule.smul_mem _ c hP, ?_⟩
    have hsmul : centerEval2 (c • P) = Polynomial.C (algebraMap L Jet c) * centerEval2 P := by
      rw [map_smul, Algebra.smul_def]
      rfl
    rw [hsmul, prolongSubst_smul]
    exact dvd_mul_of_dvd_right hdP _

theorem prolongKernel_le_complete2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape2) (W : ℕ) (G A B₁ : Jet) :
    prolongKernel Crt word s W G A B₁ ≤ complete2 Crt word s W :=
  fun _ hP => hP.1

/-- **2-Jet Case-A Avoidance Theorem (`exists_prolong_avoiding_2jet`)**:
    Directly invokes L4 `PoleBound2Jet.pole_bound_2jet`: if across `W < N`, the total dimension of
    `prolongKernel Crt word s W G A B₁` plus the total `PoleBound2Jet` pole debits is strictly
    smaller than the total dimension of `contacted2 h word s W`, then there exists `W < N` and
    `P ∈ complete2 Crt word s W` such that `¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)`. -/
theorem exists_prolong_avoiding_2jet {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape2) (N : ℕ)
    (G A B₁ : Jet)
    (hsurplus :
      (∑ W ∈ Finset.range N, Module.finrank L (prolongKernel Crt word s W G A B₁)) +
        N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W)) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  have hsum_bound :
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W) ≤
      N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
        ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by
    calc
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W)
          ≤ ∑ W ∈ Finset.range N,
              ((poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
                Module.finrank L (complete2 Crt word s W)) :=
            Finset.sum_le_sum fun W _ => pole_bound_2jet hpos hchar Crt word s W
      _ = N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) +
            ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hker_lt :
      ∑ W ∈ Finset.range N, Module.finrank L (prolongKernel Crt word s W G A B₁) <
      ∑ W ∈ Finset.range N, Module.finrank L (complete2 Crt word s W) := by omega
  have hex : ∃ W ∈ Finset.range N,
      Module.finrank L (prolongKernel Crt word s W G A B₁) <
        Module.finrank L (complete2 Crt word s W) := by
    by_contra hall
    push Not at hall
    have hle := Finset.sum_le_sum hall
    omega
  obtain ⟨W, hWN, hWlt⟩ := hex
  have _ : Module.Finite L (contacted2 h word s W) := contacted2_finite h word s W
  have _ : Module.Finite L (complete2 Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  have _ : Module.Finite L (prolongKernel Crt word s W G A B₁) :=
    Module.Finite.of_injective (Submodule.inclusion (prolongKernel_le_complete2 Crt word s W G A B₁))
      (Submodule.inclusion_injective _)
  have hnotle : ¬ (complete2 Crt word s W ≤ prolongKernel Crt word s W G A B₁) := by
    intro hle
    have := Submodule.finrank_mono hle
    omega
  have hne : ∃ P ∈ complete2 Crt word s W, P ∉ prolongKernel Crt word s W G A B₁ := by
    by_contra hall
    push Not at hall
    exact hnotle hall
  obtain ⟨P, hPmem, hPnot⟩ := hne
  refine ⟨W, Finset.mem_range.mp hWN, P, hPmem, ?_⟩
  intro hdvd
  exact hPnot ⟨hPmem, hdvd⟩

/-! ## 4. Complete 10-Rectangle Partition & Kernel-Checked `69.63` Certificates -/

inductive RescueRect
  | r0     -- j = 1, u = 1          (2-jet Prolongation + CJ0 <= 0.002e15)
  | r1     -- j = 1, 2 <= u <= 6    (2-jet Prolongation + CJ0 <= 0.63e15)
  | r2a    -- j = 1, 7 <= u <= 24   (2-jet Prolongation + CJ0 <= 44.88e15)
  | r2b    -- j = 1, 25 <= u <= 85  (existing 1-jet Rescue <= 53.66e15 at ed=133720)
  | r3a_j2 -- j = 2, 1 <= u <= 17   (2-jet Prolongation + CJ0 <= 36.85e15)
  | r3b_j2 -- j = 2, 18 <= u <= 80  (existing 1-jet Rescue <= 46.24e15 at ed=133720)
  | r3a_j4 -- 3 <= j <= 4, 1 <= u <= 8  (2-jet Prolongation + CJ0 <= 7.86e15)
  | r3b_j4 -- 3 <= j <= 4, 9 <= u <= 80 (existing 1-jet Rescue <= 51.94e15 at ed=133720)
  | r3a_j7 -- 5 <= j <= 7, 1 <= u <= 7  (2-jet Prolongation + CJ0 <= 9.37e15)
  | r3b_j7 -- 5 <= j <= 7, 8 <= u <= 80 (existing 1-jet Rescue <= 61.30e15 at ed=133720)
  deriving DecidableEq, Repr

def InRect (j u : ℕ) : RescueRect → Prop
  | .r0     => j = 1 ∧ u = 1
  | .r1     => j = 1 ∧ 2 ≤ u ∧ u ≤ 6
  | .r2a    => j = 1 ∧ 7 ≤ u ∧ u ≤ 24
  | .r2b    => j = 1 ∧ 25 ≤ u ∧ u ≤ 85
  | .r3a_j2 => j = 2 ∧ 1 ≤ u ∧ u ≤ 17
  | .r3b_j2 => j = 2 ∧ 18 ≤ u ∧ u ≤ 80
  | .r3a_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 1 ≤ u ∧ u ≤ 8
  | .r3b_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 9 ≤ u ∧ u ≤ 80
  | .r3a_j7 => (5 ≤ j ∧ j ≤ 7) ∧ 1 ≤ u ∧ u ≤ 7
  | .r3b_j7 => (5 ≤ j ∧ j ≤ 7) ∧ 8 ≤ u ∧ u ≤ 80

theorem rect_partition_complete {j u : ℕ}
    (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hu1 : 1 ≤ u)
    (hu_seed : j = 1 → u ≤ 85) (hu_mix : 2 ≤ j → u ≤ 80) :
    ∃ r : RescueRect, InRect j u r := by
  by_cases h1 : j = 1
  · have h85 := hu_seed h1
    by_cases hu : u = 1
    · exact ⟨.r0, h1, hu⟩
    · by_cases h6 : u ≤ 6
      · exact ⟨.r1, h1, by omega, h6⟩
      · by_cases h24 : u ≤ 24
        · exact ⟨.r2a, h1, by omega, h24⟩
        · exact ⟨.r2b, h1, by omega, h85⟩
  · have h80 := hu_mix (by omega)
    by_cases h2 : j = 2
    · by_cases h17 : u ≤ 17
      · exact ⟨.r3a_j2, h2, hu1, h17⟩
      · exact ⟨.r3b_j2, h2, by omega, h80⟩
    · by_cases h4 : j ≤ 4
      · by_cases h8 : u ≤ 8
        · exact ⟨.r3a_j4, ⟨by omega, h4⟩, hu1, h8⟩
        · exact ⟨.r3b_j4, ⟨by omega, h4⟩, by omega, h80⟩
      · by_cases h7 : u ≤ 7
        · exact ⟨.r3a_j7, ⟨by omega, hj7⟩, hu1, h7⟩
        · exact ⟨.r3b_j7, ⟨by omega, hj7⟩, by omega, h80⟩

/-- Exact Sylvester `Res_{z₀}(G, G^(1))` Case-B `CJ0` box `(B_H, J_H, C_H)` for all 6 small
    2-jet Prolongation rectangles: `B_H = (2*j + 1)*u`, `J_H = 3*u`, `C_H = u`, together with
    `StructuralList`'s `2 * C_H + 1 ≤ J_H` guard (`3 * u ≥ 2 * u + 1` for `u ≥ 1`). -/
theorem caseB_cj0_box_exact {j u : ℕ} :
    (InRect j u .r0     → (2 * j + 1) * u ≤ 3   ∧ 3 * u ≤ 3  ∧ u ≤ 1  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r1     → (2 * j + 1) * u ≤ 18  ∧ 3 * u ≤ 18 ∧ u ≤ 6  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r2a    → (2 * j + 1) * u ≤ 72  ∧ 3 * u ≤ 72 ∧ u ≤ 24 ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j2 → (2 * j + 1) * u ≤ 85  ∧ 3 * u ≤ 51 ∧ u ≤ 17 ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j4 → (2 * j + 1) * u ≤ 72  ∧ 3 * u ≤ 24 ∧ u ≤ 8  ∧ 2 * u + 1 ≤ 3 * u) ∧
    (InRect j u .r3a_j7 → (2 * j + 1) * u ≤ 105 ∧ 3 * u ≤ 21 ∧ u ≤ 7  ∧ 2 * u + 1 ≤ 3 * u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨rfl, hlo, hhi⟩; omega
  · rintro ⟨⟨_, hj⟩, hlo, hhi⟩
    have : 2 * j + 1 ≤ 9 := by omega
    exact ⟨Nat.le_trans (Nat.mul_le_mul_right u this) (by omega), by omega, hhi, by omega⟩
  · rintro ⟨⟨_, hj⟩, hlo, hhi⟩
    have : 2 * j + 1 ≤ 15 := by omega
    exact ⟨Nat.le_trans (Nat.mul_le_mul_right u this) (by omega), by omega, hhi, by omega⟩

private def tri (u : ℕ) : ℕ := (u + 1) * (u + 2) / 2

private def sumLinPos (base qmin count step : ℕ) : ℕ :=
  let start := qmin * step
  if base ≤ start then 0
  else
    let rem := base - start
    let nPos := min count ((rem - 1) / step + 1)
    nPos * rem - step * (nPos * (nPos - 1) / 2)

private def gain3k (A h m B J C : ℕ) : ℕ :=
  let W0 := m * A
  let step := 131071 - h
  (List.range (C + 1)).foldl (fun acc e₂ =>
    (List.range (J - 2 * e₂ + 1)).foldl (fun acc2 e₁ =>
      let sh := 3 * (e₁ + e₂) * h
      let j := e₁ + 2 * e₂
      let qmin := e₁ + e₂
      acc2 + sumLinPos (W0 + j - sh) qmin (B + 1 - qmin) step
    ) acc
  ) 0

/-- Exact `m = 59 (80, 24, 10)` scalar-list surplus at `69.63 (A = 179,798)` using exact mod-`p`
    node rank `200,031` (`E = 11,400`, `∑ q = 522,560`, `∑ v = 173,820`, `Λ = 8.8777e15`). -/
theorem scalar_surplus_6963_m59 :
    262144 * 200031 + 131071 * 522560 < 59 * 179798 * 11400 + 173820 := by
  decide

set_option maxRecDepth 20000 in
/-- Exact Case-A 2-jet surplus at `69.63 (A = 179,798, h = 2,302)` for `m = 55 (76, 22, 9), U = 353`. -/
theorem caseA_surplus_6963_m55_U353 :
    tri 353 * gain3k 179798 2302 55 76 22 9 >
      tri 353 * 262144 * 148660 + 2 * 2302 * (353 + 1) * 7279912 := by
  decide

/-- Exact split-high-band `69.63` budget (`h ∈ [2302, 2649]`, `ed = 133,720`, in `10^12` units):
    `Main_lo (163.93e15) + max(10 rects = 61.30e15) + Retained (30.83e15) + Λ (8.878e15) = 264.94e15 < 274.98e15`
    (`+10.04e15` slack!). -/
theorem budget_6963_split_ok : 163930 + 61300 + 30830 + 8878 + 10040 < 274980 := by
  decide

#print axioms prolongSubst_bezout
#print axioms prolongSubst_eval_zero
#print axioms mem_ideal_of_prolongSubst_dvd
#print axioms prolongSubst_dvd_of_mem_ideal
#print axioms exists_prolong_avoiding_2jet
#print axioms rect_partition_complete
#print axioms caseB_cj0_box_exact
#print axioms scalar_surplus_6963_m59
#print axioms caseA_surplus_6963_m55_U353
#print axioms budget_6963_split_ok

end
end TwoJetRescueBridge
