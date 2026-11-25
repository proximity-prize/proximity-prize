import ProximityPrize.SubmissionLower.TwoJetCaseAFXCore

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1200000

/-!
# 2-Jet Case-A Kernel Finrank Bound & Jacobian Power Collapse (`TwoJetCaseAKernel`)

Closes the algebraic gap between our L4 modules (`PoleBound2Jet`, `TwoJetShift`,
`TwoJetRescueBridge`) for Case A (`det M ≠ 0`) on the 6 small Rescue rectangles at `69.63`:

1. **2-Variable Jacobian Inversion & Seed-Word Power Collapse (`pow_collapse_of_wordVanishes`)**:
   Over any field `E` of characteristic `K1.p` with two derivations `d₀, d₁ : E → E` (holding
   `X, Y₀` constant) and any `(α₁, α₂) : E × E` with nonzero `2 × 2` Jacobian determinant
   `detM = d₀ α₁ * d₁ α₂ - d₁ α₁ * d₀ α₂ ≠ 0`, Cramer's rule inverts `(d₀, d₁)` to coordinate
   derivations `(δ₁, δ₂)` satisfying `δᵢ(αⱼ) = δ_{ij}`. Consequently, vanishing of all seed-word
   derivatives of length `≤ s` (`s < K1.p`) at `(α₁, α₂)` forces every bivariate Taylor
   coefficient `P(a, b)` with `a + b ≤ s` to vanish (`P ∈ (Y₁ - α₁, Y₂ - α₂)^{s + 1}`).

2. **Exact Shift Automorphism (`shift2 α₁ α₂`)**:
   Constructs `shift2 α₁ α₂ : E[Y₁][Y₂] →+* E[Y₁][Y₂]` sending `Y₁ ↦ Y₁ + α₁`, `Y₂ ↦ Y₂ + α₂`,
   proves its two-sided inverse is `shift2 (-α₁) (-α₂)` (hence injective), and proves it preserves
   total `(Y₁, Y₂)`-degree (`shift2_deg_le`). Thus any polynomial of `(Y₁, Y₂)`-degree `≤ s` that
   vanishes to order `> s` at `(α₁, α₂)` is identically zero (`zero_of_deg_le_and_order_gt`).

3. **Exact Kernel Finrank Upper Bound (`finrank_vanishOrder_le`)**:
   For any injective coefficient homomorphism `evalCoeff : SeedPoly[X][Y₀] →+* E` and any
   `L`-submodule `V ≤ ambient2 h s W` whose elements vanish to order `> k` at `(α₁, α₂)`, the
   coordinate projection onto eligible monomials with `k < e₁ + e₂` is injective on `V`, yielding:
     `Module.finrank L V ≤ (HighCoords h s W k).card`.

4. **End-to-End Case-A Avoidance Theorem (`caseA_avoidance_of_wordVanishes`)**:
   Plugs `finrank_vanishOrder_le` directly into L4 `TwoJetRescueBridge.exists_prolong_avoiding_2jet`
   (and L4 `PoleBound2Jet.pole_bound_2jet`) to produce `W < N` and `P ∈ complete2 Crt word s W`
   such that `¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)`.
-/

namespace TwoJetCaseAKernel
noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L Jet)
open K1_14_1 (SeedPoly seedWeight PoleData CRTLift)
open PoleMoment2Jet (Shape2 jetIdx groupedPoleMoment2 poleCredit2 sourceCoeff2)
open PoleBound2Jet (Source2 coeffAt2 trueEligible2 ambient2 contacted2 complete2)
open TwoJetRescueBridge (centerEval2 prolongSubst prolongKernel prolongKernel_le_complete2
  exists_prolong_avoiding_2jet)
open scoped BigOperators Polynomial Classical

/-! ## 1. 2-Variable Jacobian Inversion & Seed-Word Power Collapse -/

/-- A pair of commuting-free derivations on a field `E` (only additivity + Leibniz rule needed). -/
structure FieldDerivs (E : Type*) [Field E] where
  d₀ : E → E
  d₁ : E → E
  d₀_add : ∀ x y, d₀ (x + y) = d₀ x + d₀ y
  d₁_add : ∀ x y, d₁ (x + y) = d₁ x + d₁ y
  d₀_mul : ∀ x y, d₀ (x * y) = d₀ x * y + x * d₀ y
  d₁_mul : ∀ x y, d₁ (x * y) = d₁ x * y + x * d₁ y

theorem FieldDerivs.d₀_zero {E : Type*} [Field E] (D : FieldDerivs E) : D.d₀ 0 = 0 := by
  have h := D.d₀_add 0 0
  rw [add_zero] at h
  exact add_left_cancel (a := D.d₀ 0) (by rw [add_zero]; exact h.symm)

theorem FieldDerivs.d₁_zero {E : Type*} [Field E] (D : FieldDerivs E) : D.d₁ 0 = 0 := by
  have h := D.d₁_add 0 0
  rw [add_zero] at h
  exact add_left_cancel (a := D.d₁ 0) (by rw [add_zero]; exact h.symm)

theorem FieldDerivs.d₀_neg {E : Type*} [Field E] (D : FieldDerivs E) (x : E) :
    D.d₀ (-x) = -(D.d₀ x) := by
  have h := D.d₀_add x (-x)
  rw [add_neg_cancel, D.d₀_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem FieldDerivs.d₁_neg {E : Type*} [Field E] (D : FieldDerivs E) (x : E) :
    D.d₁ (-x) = -(D.d₁ x) := by
  have h := D.d₁_add x (-x)
  rw [add_neg_cancel, D.d₁_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Bivariate coefficient grid representing `∑_{a, b} P a b * (Y₁ - α₁)^a * (Y₂ - α₂)^b`. -/
abbrev Bivar (E : Type*) := ℕ → ℕ → E

/-- Action of a derivation `d : E → E` (holding `Y₁, Y₂` constant) on a shifted expansion
    around `(α₁, α₂)`: `d(u₁) = -d(α₁)`, `d(u₂) = -d(α₂)`. -/
def liftD {E : Type*} [Field E] (d : E → E) (α₁ α₂ : E) (P : Bivar E) : Bivar E :=
  fun a b => d (P a b) - ((a + 1 : ℕ) : E) * d α₁ * P (a + 1) b - ((b + 1 : ℕ) : E) * d α₂ * P a (b + 1)

def bivarAdd {E : Type*} [Field E] (P Q : Bivar E) : Bivar E := fun a b => P a b + Q a b
def bivarSmul {E : Type*} [Field E] (c : E) (P : Bivar E) : Bivar E := fun a b => c * P a b

theorem liftD_add {E : Type*} [Field E] {d : E → E} (hadd : ∀ x y, d (x + y) = d x + d y)
    (α₁ α₂ : E) (P Q : Bivar E) :
    liftD d α₁ α₂ (bivarAdd P Q) = bivarAdd (liftD d α₁ α₂ P) (liftD d α₁ α₂ Q) := by
  funext a b
  simp only [liftD, bivarAdd, hadd]
  ring

theorem liftD_smul {E : Type*} [Field E] {d : E → E} (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (α₁ α₂ c : E) (P : Bivar E) :
    liftD d α₁ α₂ (bivarSmul c P) = bivarAdd (bivarSmul (d c) P) (bivarSmul c (liftD d α₁ α₂ P)) := by
  funext a b
  simp only [liftD, bivarAdd, bivarSmul, hmul]
  ring

/-- Iterated action of a word `w : List (Fin 2)` of `(liftD d₀, liftD d₁)`. -/
def applyWord {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) : List (Fin 2) → Bivar E → Bivar E
  | [], P => P
  | i :: ws, P =>
    let step := if i = 0 then liftD D.d₀ α₁ α₂ P else liftD D.d₁ α₁ α₂ P
    applyWord D α₁ α₂ ws step

/-- All seed-word derivatives of length `≤ s` vanish at `(0, 0)` (i.e. at `(α₁, α₂)`). -/
def WordVanishes {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) (s : ℕ) (P : Bivar E) : Prop :=
  ∀ w : List (Fin 2), w.length ≤ s → applyWord D α₁ α₂ w P 0 0 = 0

theorem wordVanishes_weaken {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E)
    {s t : ℕ} (hst : t ≤ s) {P : Bivar E} (h : WordVanishes D α₁ α₂ s P) :
    WordVanishes D α₁ α₂ t P :=
  fun w hw => h w (hw.trans hst)

theorem wordVanishes_step0 {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E)
    {s : ℕ} {P : Bivar E} (h : WordVanishes D α₁ α₂ (s + 1) P) :
    WordVanishes D α₁ α₂ s (liftD D.d₀ α₁ α₂ P) := by
  intro w hw
  have := h (0 :: w) (by simp; omega)
  simpa [applyWord] using this

theorem wordVanishes_step1 {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E)
    {s : ℕ} {P : Bivar E} (h : WordVanishes D α₁ α₂ (s + 1) P) :
    WordVanishes D α₁ α₂ s (liftD D.d₁ α₁ α₂ P) := by
  intro w hw
  have := h (1 :: w) (by simp; omega)
  simpa [applyWord] using this

theorem wordVanishes_add {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) :
    ∀ {s : ℕ} {P Q : Bivar E},
      WordVanishes D α₁ α₂ s P → WordVanishes D α₁ α₂ s Q →
      WordVanishes D α₁ α₂ s (bivarAdd P Q)
  | 0, P, Q, hP, hQ => by
    intro w hw
    cases w with
    | nil =>
      have hp0 := hP [] le_rfl
      have hq0 := hQ [] le_rfl
      simp only [applyWord, bivarAdd] at hp0 hq0 ⊢
      rw [hp0, hq0, add_zero]
    | cons _ _ => simp at hw
  | s + 1, P, Q, hP, hQ => by
    intro w hw
    cases w with
    | nil =>
      have hp0 := hP [] (Nat.zero_le _)
      have hq0 := hQ [] (Nat.zero_le _)
      simp only [applyWord, bivarAdd] at hp0 hq0 ⊢
      rw [hp0, hq0, add_zero]
    | cons i ws =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hw
      simp only [applyWord]
      split_ifs
      · rw [liftD_add D.d₀_add]
        exact wordVanishes_add D α₁ α₂
          (wordVanishes_step0 D α₁ α₂ hP) (wordVanishes_step0 D α₁ α₂ hQ) ws hw
      · rw [liftD_add D.d₁_add]
        exact wordVanishes_add D α₁ α₂
          (wordVanishes_step1 D α₁ α₂ hP) (wordVanishes_step1 D α₁ α₂ hQ) ws hw

theorem wordVanishes_smul {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) :
    ∀ {s : ℕ} (c : E) {P : Bivar E},
      WordVanishes D α₁ α₂ s P → WordVanishes D α₁ α₂ s (bivarSmul c P)
  | 0, c, P, hP => by
    intro w hw
    cases w with
    | nil =>
      have hp0 := hP [] le_rfl
      simp only [applyWord, bivarSmul] at hp0 ⊢
      rw [hp0, mul_zero]
    | cons _ _ => simp at hw
  | s + 1, c, P, hP => by
    intro w hw
    cases w with
    | nil =>
      have hp0 := hP [] (Nat.zero_le _)
      simp only [applyWord, bivarSmul] at hp0 ⊢
      rw [hp0, mul_zero]
    | cons i ws =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hw
      simp only [applyWord]
      have hP' := wordVanishes_weaken D α₁ α₂ (Nat.le_succ s) hP
      split_ifs
      · rw [liftD_smul D.d₀_mul]
        exact wordVanishes_add D α₁ α₂
          (wordVanishes_smul D α₁ α₂ (D.d₀ c) hP')
          (wordVanishes_smul D α₁ α₂ c (wordVanishes_step0 D α₁ α₂ hP)) ws hw
      · rw [liftD_smul D.d₁_mul]
        exact wordVanishes_add D α₁ α₂
          (wordVanishes_smul D α₁ α₂ (D.d₁ c) hP')
          (wordVanishes_smul D α₁ α₂ c (wordVanishes_step1 D α₁ α₂ hP)) ws hw

/-- `2 × 2` seed Jacobian determinant `det ∂(α₁, α₂)/∂(z₀, z₁)`. -/
def jacDet {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) : E :=
  D.d₀ α₁ * D.d₁ α₂ - D.d₁ α₁ * D.d₀ α₂

/-- Cramer-inverted coordinate derivations on `E`: `δ₁(α₁) = 1, δ₁(α₂) = 0`, `δ₂(α₁) = 0, δ₂(α₂) = 1`. -/
def cramerD₁ {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) (x : E) : E :=
  (jacDet D α₁ α₂)⁻¹ * (D.d₁ α₂ * D.d₀ x - D.d₀ α₂ * D.d₁ x)

def cramerD₂ {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) (x : E) : E :=
  (jacDet D α₁ α₂)⁻¹ * (-(D.d₁ α₁) * D.d₀ x + D.d₀ α₁ * D.d₁ x)

def delta1 {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) (P : Bivar E) : Bivar E :=
  fun a b => cramerD₁ D α₁ α₂ (P a b) - ((a + 1 : ℕ) : E) * P (a + 1) b

def delta2 {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) (P : Bivar E) : Bivar E :=
  fun a b => cramerD₂ D α₁ α₂ (P a b) - ((b + 1 : ℕ) : E) * P a (b + 1)

/-- **Cramer Identity on `Bivar E` (`cramer_delta1`, `cramer_delta2`)**:
    When `jacDet D α₁ α₂ ≠ 0`, `delta1` and `delta2` are exact `E`-linear combinations of
    `liftD D.d₀` and `liftD D.d₁`. -/
theorem cramer_delta1 {E : Type*} [Field E] (D : FieldDerivs E) {α₁ α₂ : E}
    (hdet : jacDet D α₁ α₂ ≠ 0) (P : Bivar E) :
    delta1 D α₁ α₂ P =
      bivarAdd
        (bivarSmul ((jacDet D α₁ α₂)⁻¹ * D.d₁ α₂) (liftD D.d₀ α₁ α₂ P))
        (bivarSmul (-((jacDet D α₁ α₂)⁻¹ * D.d₀ α₂)) (liftD D.d₁ α₁ α₂ P)) := by
  funext a b
  have hinv : (jacDet D α₁ α₂)⁻¹ * (D.d₀ α₁ * D.d₁ α₂ - D.d₁ α₁ * D.d₀ α₂) = 1 :=
    inv_mul_cancel₀ hdet
  simp only [delta1, cramerD₁, bivarAdd, bivarSmul, liftD]
  linear_combination (((a + 1 : ℕ) : E) * P (a + 1) b) * hinv

theorem cramer_delta2 {E : Type*} [Field E] (D : FieldDerivs E) {α₁ α₂ : E}
    (hdet : jacDet D α₁ α₂ ≠ 0) (P : Bivar E) :
    delta2 D α₁ α₂ P =
      bivarAdd
        (bivarSmul (-((jacDet D α₁ α₂)⁻¹ * D.d₁ α₁)) (liftD D.d₀ α₁ α₂ P))
        (bivarSmul ((jacDet D α₁ α₂)⁻¹ * D.d₀ α₁) (liftD D.d₁ α₁ α₂ P)) := by
  funext a b
  have hinv : (jacDet D α₁ α₂)⁻¹ * (D.d₀ α₁ * D.d₁ α₂ - D.d₁ α₁ * D.d₀ α₂) = 1 :=
    inv_mul_cancel₀ hdet
  simp only [delta2, cramerD₂, bivarAdd, bivarSmul, liftD]
  linear_combination (((b + 1 : ℕ) : E) * P a (b + 1)) * hinv

theorem cramerD₁_zero {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) :
    cramerD₁ D α₁ α₂ 0 = 0 := by
  simp [cramerD₁, D.d₀_zero, D.d₁_zero]

theorem cramerD₂_zero {E : Type*} [Field E] (D : FieldDerivs E) (α₁ α₂ : E) :
    cramerD₂ D α₁ α₂ 0 = 0 := by
  simp [cramerD₂, D.d₀_zero, D.d₁_zero]

/-- **2-Variable Jacobian Power Collapse (`pow_collapse_of_wordVanishes`)**:
    In Case A (`jacDet D α₁ α₂ ≠ 0`) over any field `E` of characteristic `K1.p`,
    if all seed-word derivatives of `P` of length `≤ s` (`s < K1.p`) vanish at `(0, 0)`,
    then `P a b = 0` for all `a + b ≤ s` (`P ∈ (Y₁ - α₁, Y₂ - α₂)^{s + 1}`). -/
theorem pow_collapse_of_wordVanishes {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) {α₁ α₂ : E} (hdet : jacDet D α₁ α₂ ≠ 0) :
    ∀ (s : ℕ), s < K1.p → ∀ {P : Bivar E}, WordVanishes D α₁ α₂ s P →
      ∀ a b, a + b ≤ s → P a b = 0
  | 0, _, P, hP => by
    intro a b hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    exact hP [] le_rfl
  | s + 1, hs, P, hP => by
    have ihP := pow_collapse_of_wordVanishes D hdet s (by omega)
      (wordVanishes_weaken D α₁ α₂ (Nat.le_succ s) hP)
    have hD1 : WordVanishes D α₁ α₂ s (delta1 D α₁ α₂ P) := by
      rw [cramer_delta1 D hdet]
      exact wordVanishes_add D α₁ α₂
        (wordVanishes_smul D α₁ α₂ _ (wordVanishes_step0 D α₁ α₂ hP))
        (wordVanishes_smul D α₁ α₂ _ (wordVanishes_step1 D α₁ α₂ hP))
    have hD2 : WordVanishes D α₁ α₂ s (delta2 D α₁ α₂ P) := by
      rw [cramer_delta2 D hdet]
      exact wordVanishes_add D α₁ α₂
        (wordVanishes_smul D α₁ α₂ _ (wordVanishes_step0 D α₁ α₂ hP))
        (wordVanishes_smul D α₁ α₂ _ (wordVanishes_step1 D α₁ α₂ hP))
    have ih1 := pow_collapse_of_wordVanishes D hdet s (by omega) hD1
    have ih2 := pow_collapse_of_wordVanishes D hdet s (by omega) hD2
    intro a b hab
    by_cases hlt : a + b ≤ s
    · exact ihP a b hlt
    · have heq : a + b = s + 1 := by omega
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b' =>
          have h2 := ih2 0 b' (by omega)
          have h0 := ihP 0 b' (by omega)
          simp only [delta2, h0, cramerD₂_zero, zero_sub, neg_eq_zero] at h2
          have hnz : ((b' + 1 : ℕ) : E) ≠ 0 := by
            intro hcast
            have hdvd : K1.p ∣ (b' + 1) := (CharP.cast_eq_zero_iff E K1.p (b' + 1)).mp hcast
            have hle := Nat.le_of_dvd (Nat.succ_pos b') hdvd
            omega
          exact (mul_eq_zero.mp h2).resolve_left hnz
      | succ a' =>
        have h1 := ih1 a' b (by omega)
        have h0 := ihP a' b (by omega)
        simp only [delta1, h0, cramerD₁_zero, zero_sub, neg_eq_zero] at h1
        have hnz : ((a' + 1 : ℕ) : E) ≠ 0 := by
          intro hcast
          have hdvd : K1.p ∣ (a' + 1) := (CharP.cast_eq_zero_iff E K1.p (a' + 1)).mp hcast
          have hle := Nat.le_of_dvd (Nat.succ_pos a') hdvd
          omega
        exact (mul_eq_zero.mp h1).resolve_left hnz

/-! ## 2. Exact Bivariate Shift Automorphism `shift2 α₁ α₂` -/

/-- Univariate shift `Y ↦ Y + α` on `E[Y]`. -/
def shift1 {E : Type*} [CommRing E] (α : E) : Polynomial E →+* Polynomial E :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C α)

theorem shift1_C {E : Type*} [CommRing E] (α c : E) :
    shift1 α (Polynomial.C c) = Polynomial.C c := by
  simp [shift1]

theorem shift1_X {E : Type*} [CommRing E] (α : E) :
    shift1 α Polynomial.X = Polynomial.X + Polynomial.C α := by
  simp [shift1]

theorem shift1_comp_neg {E : Type*} [CommRing E] (α : E) :
    (shift1 (-α)).comp (shift1 α) = RingHom.id (Polynomial E) := by
  apply Polynomial.ringHom_ext
  · intro c; simp [shift1]
  · simp [shift1]

/-- Bivariate shift `(Y₁, Y₂) ↦ (Y₁ + α₁, Y₂ + α₂)` on `E[Y₁][Y₂]`. -/
def shift2 {E : Type*} [CommRing E] (α₁ α₂ : E) :
    Polynomial (Polynomial E) →+* Polynomial (Polynomial E) :=
  Polynomial.eval₂RingHom
    (Polynomial.C.comp (shift1 α₁))
    (Polynomial.X + Polynomial.C (Polynomial.C α₂))

theorem shift2_comp_neg {E : Type*} [CommRing E] (α₁ α₂ : E) :
    (shift2 (-α₁) (-α₂)).comp (shift2 α₁ α₂) = RingHom.id (Polynomial (Polynomial E)) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c; simp [shift2, shift1]
    · simp [shift2, shift1]
  · simp [shift2, shift1]

theorem shift2_injective {E : Type*} [CommRing E] (α₁ α₂ : E) :
    Function.Injective (shift2 α₁ α₂) := by
  intro P Q hPQ
  have h := congrArg (shift2 (-α₁) (-α₂)) hPQ
  change ((shift2 (-α₁) (-α₂)).comp (shift2 α₁ α₂)) P =
    ((shift2 (-α₁) (-α₂)).comp (shift2 α₁ α₂)) Q at h
  rwa [shift2_comp_neg] at h

/-- Bivariate coefficient view of `P : E[Y₁][Y₂]` (`a = deg Y₁, b = deg Y₂`). -/
def polyBivar {E : Type*} [CommRing E] (P : Polynomial (Polynomial E)) : Bivar E :=
  fun a b => (P.coeff b).coeff a

theorem polyBivar_zero_iff {E : Type*} [CommRing E] (P : Polynomial (Polynomial E)) :
    (∀ a b, polyBivar P a b = 0) ↔ P = 0 := by
  constructor
  · intro h
    ext b a
    exact h a b
  · rintro rfl a b
    simp [polyBivar]

theorem shift1_natDegree_le {E : Type*} [CommRing E] (α : E) (p : Polynomial E) :
    (shift1 α p).natDegree ≤ p.natDegree := by
  have h1 : (Polynomial.X + Polynomial.C α : Polynomial E).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp [Polynomial.natDegree_X_le])
  unfold shift1
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  exact (Nat.mul_le_mul_left i h1).trans (by omega)

/-- `shift2 α₁ α₂` preserves total `(Y₁, Y₂)`-degree bounds: if `P` has total degree `≤ k`,
    then `shift2 α₁ α₂ P` also has total degree `≤ k`. -/
theorem shift2_totalDeg_le {E : Type*} [CommRing E] (α₁ α₂ : E) {k : ℕ}
    {P : Polynomial (Polynomial E)}
    (hdeg : ∀ a b, k < a + b → polyBivar P a b = 0) :
    ∀ a b, k < a + b → polyBivar (shift2 α₁ α₂ P) a b = 0 := by
  have hterm : ∀ i, ∀ a b, k < a + b →
      polyBivar (Polynomial.C (shift1 α₁ (P.coeff i)) *
        (Polynomial.X + Polynomial.C (Polynomial.C α₂)) ^ i) a b = 0 := by
    intro i a b hab
    by_cases hbi : i < b
    · have hnd : (Polynomial.C (shift1 α₁ (P.coeff i)) *
          (Polynomial.X + Polynomial.C (Polynomial.C α₂)) ^ i).natDegree ≤ i := by
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        refine (Polynomial.natDegree_pow_le).trans ?_
        have hlin : (Polynomial.X + Polynomial.C (Polynomial.C α₂) : Polynomial (Polynomial E)).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (by simp [Polynomial.natDegree_X_le])
        exact (Nat.mul_le_mul_left i hlin).trans (by omega)
      simp only [polyBivar, Polynomial.coeff_eq_zero_of_natDegree_lt (hnd.trans_lt hbi),
        Polynomial.coeff_zero]
    · have hle : b ≤ i := Nat.le_of_not_lt hbi
      by_cases hik : k < i
      · have hpi0 : P.coeff i = 0 := by
          ext j
          exact hdeg j i (by omega)
        simp [polyBivar, hpi0]
      · have hndp : (P.coeff i).natDegree ≤ k - i := by
          rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
          intro j hj
          exact hdeg j i (by omega)
        have hnds : (shift1 α₁ (P.coeff i)).natDegree ≤ k - i :=
          (shift1_natDegree_le α₁ (P.coeff i)).trans hndp
        have hpow : ((Polynomial.X + Polynomial.C (Polynomial.C α₂)) ^ i).coeff b =
            Polynomial.C ((i.choose b : E) * α₂ ^ (i - b)) := by
          rw [add_pow, ← Polynomial.lcoeff_apply, map_sum]
          rw [Finset.sum_eq_single b]
          · simp only [Polynomial.lcoeff_apply]
            have hmul : Polynomial.X ^ b * Polynomial.C (Polynomial.C α₂) ^ (i - b) *
                (i.choose b : Polynomial (Polynomial E)) =
                Polynomial.C (Polynomial.C ((i.choose b : E) * α₂ ^ (i - b))) * Polynomial.X ^ b := by
              simp only [map_mul, map_pow, map_natCast]
              ring
            rw [hmul, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl]
          · intro m _ hmb
            simp only [Polynomial.lcoeff_apply]
            have hmul : Polynomial.X ^ m * Polynomial.C (Polynomial.C α₂) ^ (i - m) *
                (i.choose m : Polynomial (Polynomial E)) =
                Polynomial.C (Polynomial.C ((i.choose m : E) * α₂ ^ (i - m))) * Polynomial.X ^ m := by
              simp only [map_mul, map_pow, map_natCast]
              ring
            rw [hmul, Polynomial.coeff_C_mul_X_pow, ite_eq_right hmb.symm]
          · intro hb'
            exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) hb'
        simp only [polyBivar, Polynomial.coeff_C_mul, hpow, Polynomial.coeff_mul_C]
        have ha : (shift1 α₁ (P.coeff i)).natDegree < a := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt ha, zero_mul]
  intro a b hab
  unfold shift2
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  simp only [polyBivar, RingHom.comp_apply]
  rw [← Polynomial.lcoeff_apply (R := Polynomial E) b, map_sum,
    ← Polynomial.lcoeff_apply (R := E) a, map_sum]
  exact Finset.sum_eq_zero fun i _ => hterm i a b hab

/-- **Degree + Vanishing Order Rigidity (`zero_of_deg_le_and_order_gt`)**:
    If `P : E[Y₁][Y₂]` has total `(Y₁, Y₂)`-degree `≤ k` AND its shifted expansion
    `shift2 α₁ α₂ P` vanishes at all `(a, b)` with `a + b ≤ k`, then `P = 0`. -/
theorem zero_of_deg_le_and_order_gt {E : Type*} [CommRing E] (α₁ α₂ : E) {k : ℕ}
    {P : Polynomial (Polynomial E)}
    (hdeg : ∀ a b, k < a + b → polyBivar P a b = 0)
    (hord : ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ P) a b = 0) :
    P = 0 := by
  apply shift2_injective α₁ α₂
  rw [map_zero, ← polyBivar_zero_iff]
  intro a b
  by_cases h : a + b ≤ k
  · exact hord a b h
  · exact shift2_totalDeg_le α₁ α₂ hdeg a b (Nat.lt_of_not_ge h)

/-! ## 3. Exact Kernel Finrank Upper Bound (`finrank_vanishOrder_le`) -/

/-- Coefficient embedding `Source2 = SeedPoly[X][Y₀][Y₁][Y₂] →+* E[Y₁][Y₂]` induced by an
    injective base homomorphism `φ : SeedPoly[X][Y₀] →+* E`. -/
def embed2 {E : Type*} [CommRing E] (φ : Polynomial (Polynomial SeedPoly) →+* E) :
    Source2 →+* Polynomial (Polynomial E) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

theorem embed2_injective {E : Type*} [CommRing E]
    {φ : Polynomial (Polynomial SeedPoly) →+* E} (hφ : Function.Injective φ) :
    Function.Injective (embed2 φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ hφ)

theorem embed2_deg_le {E : Type*} [CommRing E]
    (φ : Polynomial (Polynomial SeedPoly) →+* E) {k : ℕ} {P : Source2}
    (hP : ∀ e₂ e₁ e₀ a e, k < e₁ + e₂ → coeffAt2 P e₂ e₁ e₀ a e = 0) :
    ∀ a b, k < a + b → polyBivar (embed2 φ P) a b = 0 := by
  intro a b hab
  simp only [polyBivar, embed2, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  have hzero : (P.coeff b).coeff a = 0 := by
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro c
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
    exact hP b a e₀ c e hab
  rw [hzero, map_zero]

/-- Explicit finite box indexing all eligible coordinates of `ambient2 h s W`. -/
abbrev CoeffBox2 (B M U : ℕ) :=
  Fin (B + 1) × Fin (B + 1) × Fin (B + 1) × Fin (M + 1) × (Fin 2 → Fin (U + 1))

def boxExp {U : ℕ} (f : Fin 2 → Fin (U + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (f k).val)

def eligibleCoords (h : ℕ) (s : Shape2) (W : ℕ) :
    Finset (CoeffBox2 s.B (W + (s.B + s.J) * (2 * h) + s.J) s.U) :=
  Finset.univ.filter fun u =>
    trueEligible2 h s W u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val (boxExp u.2.2.2.2)

def lowCoords (h : ℕ) (s : Shape2) (W k : ℕ) :
    Finset (CoeffBox2 s.B (W + (s.B + s.J) * (2 * h) + s.J) s.U) :=
  (eligibleCoords h s W).filter fun u => u.2.1.val + u.1.val ≤ k

def highCoords (h : ℕ) (s : Shape2) (W k : ℕ) :
    Finset (CoeffBox2 s.B (W + (s.B + s.J) * (2 * h) + s.J) s.U) :=
  Finset.univ.filter fun u =>
    k < u.2.1.val + u.1.val ∧
      trueEligible2 h s W u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val (boxExp u.2.2.2.2)

theorem eligibleCoords_card_eq_add (h : ℕ) (s : Shape2) (W k : ℕ) :
    (lowCoords h s W k).card + (highCoords h s W k).card = (eligibleCoords h s W).card := by
  have hdisj : Disjoint (lowCoords h s W k) (highCoords h s W k) := by
    rw [Finset.disjoint_left]
    intro u hlo hhi
    have h1 := (Finset.mem_filter.mp hlo).2
    have h2 := (Finset.mem_filter.mp hhi).2.1
    omega
  have hunion : lowCoords h s W k ∪ highCoords h s W k = eligibleCoords h s W := by
    ext u
    simp only [Finset.mem_union, lowCoords, highCoords, eligibleCoords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hel, _⟩ | ⟨_, hel⟩) <;> exact hel
    · intro hel
      by_cases hle : u.2.1.val + u.1.val ≤ k
      · exact Or.inl ⟨hel, hle⟩
      · exact Or.inr ⟨Nat.lt_of_not_ge hle, hel⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private def basisMonomial {B M U : ℕ} (u : CoeffBox2 B M U) : Source2 :=
  Polynomial.monomial u.1.val
    (Polynomial.monomial u.2.1.val
      (Polynomial.monomial u.2.2.1.val
        (Polynomial.monomial u.2.2.2.1.val
          (MvPolynomial.monomial (boxExp u.2.2.2.2) (1 : L)))))

private theorem boxExp_injective {U : ℕ} : Function.Injective (@boxExp U) := by
  intro f g hfg
  funext j
  apply Fin.ext
  have := DFunLike.congr_fun hfg j
  simpa [boxExp] using this

private theorem coeffAt2_basisMonomial {B M U : ℕ} (u v : CoeffBox2 B M U) :
    coeffAt2 (basisMonomial u) v.1.val v.2.1.val v.2.2.1.val v.2.2.2.1.val (boxExp v.2.2.2.2) =
      if u = v then 1 else 0 := by
  unfold coeffAt2 sourceCoeff2 basisMonomial
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
  by_cases h1 : u.1.val = v.1.val
  · simp only [h1, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
    by_cases h2 : u.2.1.val = v.2.1.val
    · simp only [h2, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
      by_cases h3 : u.2.2.1.val = v.2.2.1.val
      · simp only [h3, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
        by_cases h4 : u.2.2.2.1.val = v.2.2.2.1.val
        · simp only [h4, ↓reduceIte, MvPolynomial.coeff_monomial]
          by_cases h5 : boxExp u.2.2.2.2 = boxExp v.2.2.2.2
          · have heq : u = v := by
              rcases u with ⟨u1, u2, u3, u4, u5⟩
              rcases v with ⟨v1, v2, v3, v4, v5⟩
              simp only [Prod.mk.injEq]
              exact ⟨Fin.ext h1, Fin.ext h2, Fin.ext h3, Fin.ext h4, boxExp_injective h5⟩
            simp [h5, heq]
          · have hne : u ≠ v := fun h => h5 (by rw [h])
            simp [h5, hne]
        · have hne : u ≠ v := fun h => h4 (by rw [h])
          simp [h4, hne]
      · have hne : u ≠ v := fun h => h3 (by rw [h])
        simp [h3, hne]
    · have hne : u ≠ v := fun h => h2 (by rw [h])
      simp [h2, hne]
  · have hne : u ≠ v := fun h => h1 (by rw [h])
    simp [h1, hne]

private theorem basisMonomial_mem_ambient2 {h : ℕ} {s : Shape2} {W : ℕ}
    {u : CoeffBox2 s.B (W + (s.B + s.J) * (2 * h) + s.J) s.U}
    (hu : u ∈ eligibleCoords h s W) :
    basisMonomial u ∈ ambient2 h s W := by
  intro e₂ e₁ e₀ a e hne
  unfold coeffAt2 sourceCoeff2 basisMonomial
  simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
  by_cases h1 : u.1.val = e₂
  · simp only [h1, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
    by_cases h2 : u.2.1.val = e₁
    · simp only [h2, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
      by_cases h3 : u.2.2.1.val = e₀
      · simp only [h3, ↓reduceIte, Polynomial.coeff_monomial, Finsupp.single_apply]
        by_cases h4 : u.2.2.2.1.val = a
        · simp only [h4, ↓reduceIte, MvPolynomial.coeff_monomial]
          by_cases h5 : boxExp u.2.2.2.2 = e
          · exfalso
            have hel := (Finset.mem_filter.mp hu).2
            rw [h1, h2, h3, h4, h5] at hel
            exact hne hel
          · simp [h5]
        · simp [h4]
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- Exact dimension of `ambient2 h s W`: equals `(eligibleCoords h s W).card`. -/
theorem finrank_ambient2_eq (h : ℕ) (s : Shape2) (W : ℕ) :
    Module.finrank L (ambient2 h s W) = (eligibleCoords h s W).card := by
  let E := eligibleCoords h s W
  let toFun : ambient2 h s W →ₗ[L] (E → L) :=
    LinearMap.pi fun u =>
      { toFun := fun P =>
          coeffAt2 P.1 u.1.1.val u.1.2.1.val u.1.2.2.1.val u.1.2.2.2.1.val (boxExp u.1.2.2.2.2)
        map_add' := fun P Q => by simp [coeffAt2, sourceCoeff2]
        map_smul' := fun c P => by simp [coeffAt2, sourceCoeff2] }
  have hinj : Function.Injective toFun := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    apply Subtype.ext
    change P.1 = 0
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    apply MvPolynomial.ext; intro e
    simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
    change coeffAt2 P.1 e₂ e₁ e₀ a e = 0
    by_cases hel : trueEligible2 h s W e₂ e₁ e₀ a e
    · have ⟨hB, hJ, _, hU, hW⟩ := hel
      let M := W + (s.B + s.J) * (2 * h) + s.J
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (j : Fin 2) : e j ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      let u : CoeffBox2 s.B M s.U :=
        (⟨e₂, by omega⟩, ⟨e₁, by omega⟩, ⟨e₀, by omega⟩, ⟨a, by omega⟩,
          fun j => ⟨e j, by have := hU' j; omega⟩)
      have heq_e : boxExp u.2.2.2.2 = e := by ext j; simp [boxExp, u]
      have huE : u ∈ E := by
        dsimp only [E, eligibleCoords]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa only [u, heq_e] using hel⟩
      have hz : coeffAt2 P.1 u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val (boxExp u.2.2.2.2) = 0 :=
        congrFun hP ⟨u, huE⟩
      simpa only [u, heq_e] using hz
    · exact P.2 e₂ e₁ e₀ a e hel
  have hsurj : Function.Surjective toFun := by
    intro f
    refine ⟨⟨∑ u : E, f u • basisMonomial u.1,
      Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (basisMonomial_mem_ambient2 u.2)⟩, ?_⟩
    funext v
    change coeffAt2 (∑ u : E, f u • basisMonomial u.1)
      v.1.1.val v.1.2.1.val v.1.2.2.1.val v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) = f v
    have hcoeff_sum : ∀ (S : Finset E) (g : E → Source2),
        coeffAt2 (∑ u ∈ S, g u) v.1.1.val v.1.2.1.val v.1.2.2.1.val v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) =
        ∑ u ∈ S, coeffAt2 (g u) v.1.1.val v.1.2.1.val v.1.2.2.1.val v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) := by
      intro S g
      induction S using Finset.cons_induction with
      | empty => simp [coeffAt2, sourceCoeff2]
      | cons a S ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, ← ih]
        simp [coeffAt2, sourceCoeff2]
    rw [hcoeff_sum]
    rw [Finset.sum_eq_single v]
    · have hsm : coeffAt2 (f v • basisMonomial v.1) v.1.1.val v.1.2.1.val v.1.2.2.1.val
          v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) =
          f v * coeffAt2 (basisMonomial v.1) v.1.1.val v.1.2.1.val v.1.2.2.1.val
            v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) := by
        simp [coeffAt2, sourceCoeff2]
      rw [hsm, coeffAt2_basisMonomial, ite_eq_left rfl, mul_one]
    · intro u _ huv
      have hsm : coeffAt2 (f u • basisMonomial u.1) v.1.1.val v.1.2.1.val v.1.2.2.1.val
          v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) =
          f u * coeffAt2 (basisMonomial u.1) v.1.1.val v.1.2.1.val v.1.2.2.1.val
            v.1.2.2.2.1.val (boxExp v.1.2.2.2.2) := by
        simp [coeffAt2, sourceCoeff2]
      rw [hsm, coeffAt2_basisMonomial, ite_eq_right (fun h => huv (Subtype.ext h)), mul_zero]
    · intro hv; exact absurd (Finset.mem_univ v) hv
  have heq := LinearEquiv.ofBijective toFun ⟨hinj, hsurj⟩
  rw [heq.finrank_eq, Module.finrank_pi, Fintype.card_coe]

/-- **Exact Kernel Finrank Upper Bound (`finrank_vanishOrder_le`)**:
    If `φ : SeedPoly[X][Y₀] →+* E` is injective and every `P ∈ V` (`V ≤ ambient2 h s W`)
    vanishes to order `> k` at `(α₁, α₂)` under `shift2 α₁ α₂ ∘ embed2 φ`, then
    `Module.finrank L V ≤ (highCoords h s W k).card`. -/
theorem finrank_vanishOrder_le {E : Type*} [CommRing E]
    (φ : Polynomial (Polynomial SeedPoly) →+* E) (hφ : Function.Injective φ)
    (α₁ α₂ : E) {h : ℕ} {s : Shape2} {W k : ℕ}
    (V : Submodule L Source2) (hV : V ≤ ambient2 h s W)
    (hord : ∀ P ∈ V, ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ (embed2 φ P)) a b = 0) :
    Module.finrank L V ≤ (highCoords h s W k).card := by
  classical
  let H := highCoords h s W k
  let π : V →ₗ[L] (H → L) :=
    LinearMap.pi fun u =>
      { toFun := fun P =>
          coeffAt2 P.1 u.1.1.val u.1.2.1.val u.1.2.2.1.val u.1.2.2.2.1.val (boxExp u.1.2.2.2.2)
        map_add' := fun P Q => by simp [coeffAt2, sourceCoeff2]
        map_smul' := fun c P => by simp [coeffAt2, sourceCoeff2] }
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    apply Subtype.ext
    change P.1 = 0
    have hlow : ∀ e₂ e₁ e₀ a e, k < e₁ + e₂ → coeffAt2 P.1 e₂ e₁ e₀ a e = 0 := by
      intro e₂ e₁ e₀ a e hgt
      by_cases hel : trueEligible2 h s W e₂ e₁ e₀ a e
      · have ⟨hB, hJ, _, hU, hW⟩ := hel
        let M := W + (s.B + s.J) * (2 * h) + s.J
        have hM : a ≤ M := by dsimp [M]; omega
        have hU' (j : Fin 2) : e j ≤ s.U := by
          apply le_trans _ hU
          rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        let u : CoeffBox2 s.B M s.U :=
          (⟨e₂, by omega⟩, ⟨e₁, by omega⟩, ⟨e₀, by omega⟩, ⟨a, by omega⟩,
            fun j => ⟨e j, by have := hU' j; omega⟩)
        have heq_e : boxExp u.2.2.2.2 = e := by
          ext j; simp [boxExp, u]
        have huH : u ∈ H := by
          dsimp only [H, highCoords]
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, hgt, ?_⟩
          simpa only [u, heq_e] using hel
        have hzero : coeffAt2 P.1 u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val (boxExp u.2.2.2.2) = 0 :=
          congrFun hP ⟨u, huH⟩
        simpa only [u, heq_e] using hzero
      · exact hV P.2 e₂ e₁ e₀ a e hel
    apply embed2_injective hφ
    rw [map_zero]
    exact zero_of_deg_le_and_order_gt α₁ α₂ (embed2_deg_le φ hlow) (hord P.1 P.2)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi, Fintype.card_coe] using hle

/-! ## 4. End-to-End Case-A Avoidance Theorem (`caseA_avoidance_of_wordVanishes`) -/

/-- **End-to-End 2-Jet Case-A Avoidance Theorem (`caseA_avoidance_of_wordVanishes`)**:
    Connects `pow_collapse_of_wordVanishes` (Case A Jacobian `det M ≠ 0`),
    `finrank_vanishOrder_le`, L4 `TwoJetRescueBridge.exists_prolong_avoiding_2jet`, and
    L4 `PoleBound2Jet.pole_bound_2jet`:

    If for each `W < N`, every `P ∈ prolongKernel Crt word s W G A B₁` vanishes along all
    seed-derivative words of length `≤ k W` (`k W < K1.p`) at `(α₁, α₂)` (obtained via L4
    `TwoJetShift.complete2_cleared`), and the high-coordinate count plus `PoleBound2Jet` debits
    is strictly below the `contacted2` total dimension, then there exists `W < N` and
    `P ∈ complete2 Crt word s W` such that `¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)`. -/
theorem caseA_avoidance_of_wordVanishes {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : Polynomial (Polynomial SeedPoly) →+* E) (hφ : Function.Injective φ)
    {α₁ α₂ : E} (hdet : jacDet D α₁ α₂ ≠ 0)
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N : ℕ)
    (G A B₁ : Jet) (k : ℕ → ℕ)
    (hk : ∀ W < N, k W < K1.p)
    (hvan : ∀ W < N, ∀ P ∈ prolongKernel Crt word s W G A B₁,
      WordVanishes D α₁ α₂ (k W) (polyBivar (shift2 α₁ α₂ (embed2 φ P))))
    (hsurplus :
      (∑ W ∈ Finset.range N, (highCoords h s W (k W)).card) +
        N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, Module.finrank L (contacted2 h word s W)) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  apply exists_prolong_avoiding_2jet hpos hchar Crt word s N G A B₁
  have hker_le :
      ∑ W ∈ Finset.range N, Module.finrank L (prolongKernel Crt word s W G A B₁) ≤
      ∑ W ∈ Finset.range N, (highCoords h s W (k W)).card := by
    apply Finset.sum_le_sum
    intro W hWN
    have hWN' : W < N := Finset.mem_range.mp hWN
    apply finrank_vanishOrder_le φ hφ α₁ α₂ _ (fun P hP => (prolongKernel_le_complete2 Crt word s W G A B₁ hP).1.1)
    intro P hP
    exact pow_collapse_of_wordVanishes D hdet (k W) (hk W hWN') (hvan W hWN' P hP)
  omega

/-- **Low-Coordinate Surplus Form of Case-A Avoidance (`caseA_avoidance_of_lowCoords_surplus`)**:
    Combines `finrank_ambient2_eq`, `eligibleCoords_card_eq_add`, `caseA_avoidance_of_wordVanishes`,
    and a physical contact rank upper bound `physRank` (`finrank ambient2 ≤ physRank + finrank contacted2`)
    so that the avoidance condition reduces directly to the `lowCoords` (= `tri U * gain3k`)
    surplus inequality:
      `N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <`
        `∑ W ∈ range N, (lowCoords h s W (k W)).card`. -/
theorem caseA_avoidance_of_lowCoords_surplus {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : Polynomial (Polynomial SeedPoly) →+* E) (hφ : Function.Injective φ)
    {α₁ α₂ : E} (hdet : jacDet D α₁ α₂ ≠ 0)
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N physRank : ℕ)
    (G A B₁ : Jet) (k : ℕ → ℕ)
    (hk : ∀ W < N, k W < K1.p)
    (hphys : ∀ W < N, Module.finrank L (ambient2 h s W) ≤
      physRank + Module.finrank L (contacted2 h word s W))
    (hvan : ∀ W < N, ∀ P ∈ prolongKernel Crt word s W G A B₁,
      WordVanishes D α₁ α₂ (k W) (polyBivar (shift2 α₁ α₂ (embed2 φ P))))
    (hlow :
      N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, (lowCoords h s W (k W)).card) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  apply caseA_avoidance_of_wordVanishes D φ hφ hdet hpos hchar Crt word s N G A B₁ k hk hvan
  have hstep : ∀ W ∈ Finset.range N,
      (lowCoords h s W (k W)).card + (highCoords h s W (k W)).card ≤
        physRank + Module.finrank L (contacted2 h word s W) := by
    intro W hW
    rw [eligibleCoords_card_eq_add, ← finrank_ambient2_eq]
    exact hphys W (Finset.mem_range.mp hW)
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hsum
  have hmul : N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) =
      N * physRank + N * (poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) := by ring
  omega

#print axioms pow_collapse_of_wordVanishes
#print axioms shift2_injective
#print axioms shift2_totalDeg_le
#print axioms zero_of_deg_le_and_order_gt
#print axioms finrank_ambient2_eq
#print axioms finrank_vanishOrder_le
#print axioms caseA_avoidance_of_wordVanishes
#print axioms caseA_avoidance_of_lowCoords_surplus

end
end TwoJetCaseAKernel
