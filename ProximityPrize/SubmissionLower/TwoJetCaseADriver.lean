import ProximityPrize.SubmissionLower.TwoJetCaseAKernel
import ProximityPrize.SubmissionLower.TwoJetCaseBResultant

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

/-!
# 2-Jet Case-A Driver (`TwoJetShift.complete2_cleared` → `TwoJetCaseAKernel`) & Hybrid 6-Rect Rescue (`TwoJetCaseADriver`)

Closes the final algebraic link between L4 `TwoJetShift.complete2_cleared` and L4
`TwoJetCaseAKernel.caseA_avoidance_of_wordVanishes`, and packages both Case A (`det M ≠ 0`) and
Case B (`det M = 0`) for the 6 small Rescue rectangles at `69.63` (`A = 179,798`):

1. **Seed-Derivative Base Ring & Explicit `FieldDerivs (FractionRing BaseRing)`**:
   Proves that `K1_14_1_3.seedCoeff i 1` is an `L`-derivation on `SeedPoly`, lifts it to
   `baseDeriv i` on `BaseRing = SeedPoly[X][Y₀]`, and explicitly constructs
   `fractionRingFieldDerivs : FieldDerivs (FractionRing BaseRing)` via the quotient rule,
   witnessing `BaseDerivCompat` non-vacuously.
2. **Exact Intertwining of `sourceHasse2 i 1` with `liftD`**:
   For any `BaseDerivCompat φ D` and any `(α₁, α₂) : E × E`, proves the exact coefficient identity
     `polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) =`
       `liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))`.
3. **Iterated Cleared-Shift Words (`applyClearedWord`)**:
   Uses L4 `TwoJetShift.complete2_cleared` to show that if every `Q ∈ complete2 Crt word s W'`
   (`W' < N`) vanishes at `(α₁, α₂)`, then every `P ∈ complete2 Crt word s W` automatically obeys
   `WordVanishes D α₁ α₂ k (polyBivar (shift2 α₁ α₂ (embed2 φ P)))` whenever
   `W + k * (boundedShiftExp s 1 * h) < N`.
4. **End-to-End Case-A Avoidance Without `hvan` (`caseA_avoidance_from_complete2_cleared`)**:
   Eliminates the `hvan` hypothesis from `TwoJetCaseAKernel.caseA_avoidance_of_lowCoords_surplus`
   via `TwoJetShift.complete2_cleared` and `TwoJetRescueBridge.prolongSubst_bezout`.
5. **Unified Hybrid 6-Small-Rect Rescue Theorem (`small_rect_hybrid_rescue_6963`)**:
   Packages Case A (2-jet prolongation avoidance) and Case B (L4 `TwoJetCaseBResultant`,
   `T.card ≤ smallRectCap6963 r ≤ 44.89e15 < 61.30e15`) across all 6 small Rescue rectangles.
-/

namespace TwoJetCaseADriver

noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L)
open K1_14_1 (SeedPoly PoleData CRTLift)
open K1_14_1_3 (translation seedCoeff mapCoeffs mapCoeffs_coeff sourceX)
open PoleMoment2Jet (Shape2 groupedPoleMoment2 poleCredit2 jetConstant2)
open PoleBound2Jet (Source2 coeffAt2 ambient2 contacted2 complete2)
open TwoJetShift (boundedShiftExp sourceHasse2 cleared2Shift complete2_cleared)
open TwoJetRescueBridge (Jet2 centerEval2 prolongSubst prolongSubst_bezout prolongKernel
  RescueRect InRect)
open TwoJetCaseAKernel (FieldDerivs Bivar liftD bivarAdd bivarSmul applyWord WordVanishes
  jacDet shift1 shift2 polyBivar embed2 lowCoords highCoords
  caseA_avoidance_of_lowCoords_surplus)
open TwoJetCaseBResultant (IsSmallRect smallRectCap6963 caseB_small_rects_card_le_6963)
open scoped BigOperators Polynomial

abbrev BaseRing := Polynomial (Polynomial SeedPoly)

/-! ## 1. Generic Coefficientwise Derivation Lifting on Polynomials -/

def mapDeriv {R : Type*} [CommRing R] (d : R → R) (p : Polynomial R) : Polynomial R :=
  p.sum fun n a => Polynomial.monomial n (d a)

theorem mapDeriv_coeff {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (p : Polynomial R) (n : ℕ) : (mapDeriv d p).coeff n = d (p.coeff n) := by
  classical
  change (p.sum fun j a => Polynomial.monomial j (d a)).coeff n = d (p.coeff n)
  simp only [Polynomial.sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finsupp.single_apply, Finset.sum_ite_eq']
  split
  · rfl
  next h => rw [Polynomial.notMem_support_iff.mp h, h0]

theorem mapDeriv_zero {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) :
    mapDeriv d (0 : Polynomial R) = 0 := by
  ext n; simp [mapDeriv_coeff h0, h0]

theorem mapDeriv_add {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (p q : Polynomial R) :
    mapDeriv d (p + q) = mapDeriv d p + mapDeriv d q := by
  ext n; simp [mapDeriv_coeff h0, hadd]

theorem mapDeriv_C {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) (c : R) :
    mapDeriv d (Polynomial.C c) = Polynomial.C (d c) := by
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_C, Polynomial.coeff_C]
  split <;> simp [h0]

theorem mapDeriv_X {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0) (h1 : d 1 = 0) :
    mapDeriv d (Polynomial.X : Polynomial R) = 0 := by
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_X, Polynomial.coeff_zero]
  split <;> simp [h0, h1]

theorem mapDeriv_mul {R : Type*} [CommRing R] {d : R → R} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (p q : Polynomial R) :
    mapDeriv d (p * q) = mapDeriv d p * q + p * mapDeriv d q := by
  have hd_sum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → R),
      d (∑ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
    intro s f
    classical
    induction s using Finset.induction with
    | empty => simp [h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  ext n
  rw [mapDeriv_coeff h0, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
    Polynomial.coeff_mul, hd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [hmul, mapDeriv_coeff h0, mapDeriv_coeff h0]

theorem fieldDerivs_d₀_one {E : Type*} [Field E] (D : FieldDerivs E) : D.d₀ 1 = 0 := by
  have h := D.d₀_mul 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (a := D.d₀ 1) (by rw [add_zero]; exact h.symm)

theorem fieldDerivs_d₁_one {E : Type*} [Field E] (D : FieldDerivs E) : D.d₁ 1 = 0 := by
  have h := D.d₁_mul 1 1
  simp only [one_mul, mul_one] at h
  exact add_left_cancel (a := D.d₁ 1) (by rw [add_zero]; exact h.symm)

/-! ## 2. `seedCoeff i 1`, `baseDeriv`, and Explicit `FieldDerivs (FractionRing BaseRing)` -/

theorem translation_coeff_zero (i : Fin 2) (p : SeedPoly) :
    (translation i p).coeff 0 = p := by
  have h : (Polynomial.evalRingHom 0).comp (translation i).toRingHom = RingHom.id SeedPoly := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translation]
    · intro j
      by_cases hj : j = i <;> simp [translation, hj]
  have hp := RingHom.congr_fun h p
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.coe_evalRingHom, RingHom.id_apply] at hp
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact hp

theorem seedCoeff_one_mul (i : Fin 2) (p q : SeedPoly) :
    seedCoeff i 1 (p * q) = seedCoeff i 1 p * q + p * seedCoeff i 1 q := by
  change (translation i (p * q)).coeff 1 =
    (translation i p).coeff 1 * q + p * (translation i q).coeff 1
  rw [map_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, translation_coeff_zero]
  ring

theorem seedCoeff_one_C (i : Fin 2) (a : L) :
    seedCoeff i 1 (MvPolynomial.C a) = 0 := by
  change (translation i (MvPolynomial.C a)).coeff 1 = 0
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  change (Polynomial.C (MvPolynomial.C a)).coeff 1 = 0
  simp

def baseDeriv (i : Fin 2) : BaseRing →ₗ[L] BaseRing :=
  mapCoeffs (mapCoeffs (seedCoeff i 1))

theorem baseDeriv_coeff (i : Fin 2) (r : BaseRing) (b a : ℕ) :
    ((baseDeriv i r).coeff b).coeff a = seedCoeff i 1 ((r.coeff b).coeff a) := by
  simp [baseDeriv]

theorem baseDeriv_mul (i : Fin 2) (r₁ r₂ : BaseRing) :
    baseDeriv i (r₁ * r₂) = baseDeriv i r₁ * r₂ + r₁ * baseDeriv i r₂ := by
  have h1 : ∀ p q : Polynomial SeedPoly,
      mapCoeffs (seedCoeff i 1) (p * q) =
        mapCoeffs (seedCoeff i 1) p * q + p * mapCoeffs (seedCoeff i 1) q := by
    intro p q
    have heq : ∀ x : Polynomial SeedPoly, mapCoeffs (seedCoeff i 1) x = mapDeriv (seedCoeff i 1) x := by
      intro x; ext n; rw [mapCoeffs_coeff, mapDeriv_coeff (map_zero _)]
    simp only [heq]
    exact mapDeriv_mul (map_zero _) (map_add _) (seedCoeff_one_mul i) p q
  have heq2 : ∀ x : BaseRing,
      baseDeriv i x = mapDeriv (mapCoeffs (seedCoeff i 1)) x := by
    intro x; ext b; rw [baseDeriv, mapCoeffs_coeff, mapDeriv_coeff (map_zero _)]
  simp only [heq2]
  exact mapDeriv_mul (map_zero _) (map_add _) h1 r₁ r₂

theorem baseDeriv_sourceX (i : Fin 2) (p : Polynomial L) :
    baseDeriv i (Polynomial.C (sourceX p)) = 0 := by
  ext b a
  rw [baseDeriv_coeff]
  simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  by_cases hb : b = 0
  · subst hb
    simp [sourceX, seedCoeff_one_C]
  · simp [Polynomial.coeff_C, hb]

/-- Quotient-rule extension of any ring derivation `d : R → R` on an integral domain `R`
    to `FractionRing R`. -/
def fracDeriv {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y) :
    FractionRing R → FractionRing R :=
  fun x => Localization.liftOn x
    (fun (a : R) (s : nonZeroDivisors R) =>
      algebraMap R (FractionRing R) (d a * s - a * d s) /
        algebraMap R (FractionRing R) (s * s : R))
    (by
      intro a₁ a₂ s₁ s₂ h
      rw [Localization.r_iff_exists] at h
      obtain ⟨c, hc⟩ := h
      have hc0 : (c : R) ≠ 0 := nonZeroDivisors.ne_zero c.2
      have h1 : a₁ * s₂ = a₂ * s₁ := mul_left_cancel₀ hc0 (by
        have h' : (c : R) * (a₁ * s₂) = (c : R) * (a₂ * s₁) := by
          linear_combination (by simpa [mul_assoc, mul_comm, mul_left_comm] using hc :
            (c : R) * (s₂ * a₁) = (c : R) * (s₁ * a₂))
        exact h')
      have hd : d a₁ * s₂ + a₁ * d s₂ = d a₂ * s₁ + a₂ * d s₁ := by
        have h' := congrArg d h1
        rwa [hmul, hmul] at h'
      have hs1 : algebraMap R (FractionRing R) (s₁ * s₁ : R) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2)
          (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2)
      have hs2 : algebraMap R (FractionRing R) (s₂ * s₂ : R) ≠ 0 := by
        rw [map_mul]
        exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2)
          (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2)
      rw [div_eq_div_iff hs1 hs2]
      rw [← map_mul, ← map_mul]
      congr 1
      have hcross : (d a₁ * s₁ - a₁ * d s₁) * (s₂ * s₂) - (d a₂ * s₂ - a₂ * d s₂) * (s₁ * s₁) =
          (s₁ * s₂) * ((d a₁ * s₂ + a₁ * d s₂) - (d a₂ * s₁ + a₂ * d s₁)) -
          (d s₁ * s₂ + s₁ * d s₂) * (a₁ * s₂ - a₂ * s₁) := by ring
      linear_combination hcross + (s₁ * s₂) * hd - (d s₁ * s₂ + s₁ * d s₂) * h1)

private theorem fracDeriv_mk {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (a : R) (s : nonZeroDivisors R) :
    fracDeriv d hadd hmul (Localization.mk a s) =
      algebraMap R (FractionRing R) (d a * s - a * d s) /
        algebraMap R (FractionRing R) (s * s : R) := by
  unfold fracDeriv
  simp only [Localization.liftOn_mk]

theorem fracDeriv_algebraMap {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y) (a : R) :
    fracDeriv d hadd hmul (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (d a) := by
  have hd1 : d 1 = 0 := by
    have h := hmul 1 1; simp only [one_mul, mul_one] at h
    exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h.symm)
  rw [← Localization.mk_one_eq_algebraMap, fracDeriv_mk]
  simp [hd1]

theorem fracDeriv_add {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (x y : FractionRing R) :
    fracDeriv d hadd hmul (x + y) = fracDeriv d hadd hmul x + fracDeriv d hadd hmul y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a, s⟩
      rcases q with ⟨b, t⟩
      rw [Localization.add_mk, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
      have hs : algebraMap R (FractionRing R) (s : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have ht : algebraMap R (FractionRing R) (t : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
      simp only [Submonoid.coe_mul, hadd, hmul, map_add, map_sub, map_mul]
      field_simp [hs, ht]
      ring

theorem fracDeriv_mul {R : Type*} [CommRing R] [IsDomain R] (d : R → R)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (x y : FractionRing R) :
    fracDeriv d hadd hmul (x * y) =
      fracDeriv d hadd hmul x * y + x * fracDeriv d hadd hmul y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a, s⟩
      rcases q with ⟨b, t⟩
      rw [Localization.mk_mul, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
      have hs : algebraMap R (FractionRing R) (s : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      have ht : algebraMap R (FractionRing R) (t : R) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
      have hmk_eq : ∀ (c : R) (u : nonZeroDivisors R),
          Localization.mk c u = algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) (u : R) := by
        intro c u
        have hu : algebraMap R (FractionRing R) (u : R) ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors u.2
        rw [eq_div_iff hu, ← Localization.mk_one_eq_algebraMap (u : R), Localization.mk_mul, mul_one,
          ← Localization.mk_one_eq_algebraMap c, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        refine ⟨1, by simp [mul_comm]⟩
      rw [hmk_eq a s, hmk_eq b t]
      simp only [Submonoid.coe_mul, hmul, map_add, map_sub, map_mul]
      field_simp [hs, ht]
      ring

/-- Compatibility of a `FieldDerivs E` and base embedding `φ : BaseRing →+* E` with `baseDeriv`. -/
structure BaseDerivCompat {E : Type*} [Field E] (φ : BaseRing →+* E) (D : FieldDerivs E) : Prop where
  compat0 : ∀ r : BaseRing, D.d₀ (φ r) = φ (baseDeriv 0 r)
  compat1 : ∀ r : BaseRing, D.d₁ (φ r) = φ (baseDeriv 1 r)

private theorem baseDeriv_add (i : Fin 2) (x y : BaseRing) :
    baseDeriv i (x + y) = baseDeriv i x + baseDeriv i y :=
  (baseDeriv i).map_add x y

/-- Explicit `FieldDerivs` on `FractionRing BaseRing` extending `baseDeriv 0, baseDeriv 1`. -/
def fractionRingFieldDerivs : FieldDerivs (FractionRing BaseRing) where
  d₀ := fracDeriv (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁ := fracDeriv (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)
  d₀_add := fracDeriv_add (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁_add := fracDeriv_add (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)
  d₀_mul := fracDeriv_mul (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  d₁_mul := fracDeriv_mul (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)

theorem fractionRingFieldDerivs_compat :
    BaseDerivCompat (algebraMap BaseRing (FractionRing BaseRing)) fractionRingFieldDerivs where
  compat0 := fracDeriv_algebraMap (baseDeriv 0) (baseDeriv_add 0) (baseDeriv_mul 0)
  compat1 := fracDeriv_algebraMap (baseDeriv 1) (baseDeriv_add 1) (baseDeriv_mul 1)

/-! ## 3. Exact Intertwining of `sourceHasse2 i 1` with `liftD` -/

private def mapDeriv2 {E : Type*} [Field E] (d : E → E) (P : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv (mapDeriv d) P

private theorem mapDeriv2_coeff {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (P : Polynomial (Polynomial E)) (b a : ℕ) :
    ((mapDeriv2 d P).coeff b).coeff a = d ((P.coeff b).coeff a) := by
  rw [mapDeriv2, mapDeriv_coeff (mapDeriv_zero h0), mapDeriv_coeff h0]

private theorem mapDeriv2_add {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (P Q : Polynomial (Polynomial E)) :
    mapDeriv2 d (P + Q) = mapDeriv2 d P + mapDeriv2 d Q :=
  mapDeriv_add (mapDeriv_zero h0) (mapDeriv_add h0 hadd) P Q

private theorem mapDeriv2_mul {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (P Q : Polynomial (Polynomial E)) :
    mapDeriv2 d (P * Q) = mapDeriv2 d P * Q + P * mapDeriv2 d Q :=
  mapDeriv_mul (mapDeriv_zero h0) (mapDeriv_add h0 hadd) (mapDeriv_mul h0 hadd hmul) P Q

private def derivY1 {E : Type*} [CommRing E] (Q : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv (fun p : Polynomial E => p.derivative) Q

private theorem derivY1_coeff {E : Type*} [CommRing E] (Q : Polynomial (Polynomial E)) (b : ℕ) :
    (derivY1 Q).coeff b = (Q.coeff b).derivative :=
  mapDeriv_coeff (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero Q b

private theorem derivY1_add {E : Type*} [CommRing E] (P Q : Polynomial (Polynomial E)) :
    derivY1 (P + Q) = derivY1 P + derivY1 Q :=
  mapDeriv_add (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero
    (fun x y => Polynomial.derivative_add) P Q

private theorem derivY1_mul {E : Type*} [CommRing E] (P Q : Polynomial (Polynomial E)) :
    derivY1 (P * Q) = derivY1 P * Q + P * derivY1 Q :=
  mapDeriv_mul (d := fun p : Polynomial E => p.derivative) Polynomial.derivative_zero
    (fun x y => Polynomial.derivative_add) (fun x y => Polynomial.derivative_mul) P Q

private def liftPoly {E : Type*} [Field E] (d : E → E) (α₁ α₂ : E) (Q : Polynomial (Polynomial E)) :
    Polynomial (Polynomial E) :=
  mapDeriv2 d Q - Polynomial.C (Polynomial.C (d α₁)) * derivY1 Q -
    Polynomial.C (Polynomial.C (d α₂)) * Q.derivative

private theorem polyBivar_liftPoly {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (α₁ α₂ : E) (Q : Polynomial (Polynomial E)) :
    polyBivar (liftPoly d α₁ α₂ Q) = liftD d α₁ α₂ (polyBivar Q) := by
  funext a b
  simp only [polyBivar, liftPoly, liftD, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    mapDeriv2_coeff h0, derivY1_coeff, Polynomial.coeff_derivative]
  have hcast : ((Q.coeff (b + 1) * ((b : Polynomial E) + 1)).coeff a : E) =
      (Q.coeff (b + 1)).coeff a * ((b + 1 : ℕ) : E) := by
    have h1 : ((b : Polynomial E) + 1) = Polynomial.C ((b + 1 : ℕ) : E) := by simp
    rw [h1, Polynomial.coeff_mul_C]
  rw [hcast]
  push_cast
  ring

private theorem liftPoly_add {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (α₁ α₂ : E) (P Q : Polynomial (Polynomial E)) :
    liftPoly d α₁ α₂ (P + Q) = liftPoly d α₁ α₂ P + liftPoly d α₁ α₂ Q := by
  simp only [liftPoly, mapDeriv2_add h0 hadd, derivY1_add, Polynomial.derivative_add]
  ring

private theorem liftPoly_mul {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (α₁ α₂ : E) (P Q : Polynomial (Polynomial E)) :
    liftPoly d α₁ α₂ (P * Q) = liftPoly d α₁ α₂ P * Q + P * liftPoly d α₁ α₂ Q := by
  simp only [liftPoly, mapDeriv2_mul h0 hadd hmul, derivY1_mul, Polynomial.derivative_mul]
  ring

private theorem shift2_mapDeriv2 {E : Type*} [Field E] {d : E → E} (h0 : d 0 = 0) (h1 : d 1 = 0)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = d x * y + x * d y)
    (α₁ α₂ : E) (P : Polynomial (Polynomial E)) :
    shift2 α₁ α₂ (mapDeriv2 d P) = liftPoly d α₁ α₂ (shift2 α₁ α₂ P) := by
  have hd0 : (fun p : Polynomial E => p.derivative) 0 = 0 := Polynomial.derivative_zero
  have hd1 : (fun p : Polynomial E => p.derivative) 1 = 0 := Polynomial.derivative_one
  have hC : ∀ p : Polynomial E,
      shift2 α₁ α₂ (mapDeriv2 d (Polynomial.C p)) =
        liftPoly d α₁ α₂ (shift2 α₁ α₂ (Polynomial.C p)) := by
    intro p
    induction p using Polynomial.induction_on with
    | C c =>
      have hl : mapDeriv2 d (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C (d c)) := by
        rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_C h0]
      have hs : shift2 α₁ α₂ (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C c) := by
        simp [shift2, shift1]
      have hs' : shift2 α₁ α₂ (Polynomial.C (Polynomial.C (d c))) = Polynomial.C (Polynomial.C (d c)) := by
        simp [shift2, shift1]
      rw [hl, hs, hs']
      have hdy : derivY1 (Polynomial.C (Polynomial.C c)) = 0 := by
        rw [derivY1, mapDeriv_C hd0, Polynomial.derivative_C, map_zero]
      rw [liftPoly, hl, hdy, mul_zero, sub_zero, Polynomial.derivative_C, mul_zero, sub_zero]
    | add p q ihp ihq =>
      rw [map_add, mapDeriv2_add h0 hadd, map_add, map_add, liftPoly_add h0 hadd, ihp, ihq]
    | monomial n c ih =>
      have hsplit : Polynomial.C (Polynomial.C c * Polynomial.X ^ (n + 1)) =
          Polynomial.C (Polynomial.C c * Polynomial.X ^ n) * Polynomial.C Polynomial.X := by
        rw [← map_mul, pow_succ, mul_assoc]
      have hX : shift2 α₁ α₂ (mapDeriv2 d (Polynomial.C Polynomial.X)) =
          liftPoly d α₁ α₂ (shift2 α₁ α₂ (Polynomial.C Polynomial.X)) := by
        have hl : mapDeriv2 d (Polynomial.C Polynomial.X) = 0 := by
          rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_X h0 h1, map_zero]
        have hs : shift2 α₁ α₂ (Polynomial.C Polynomial.X) =
            Polynomial.C (Polynomial.X + Polynomial.C α₁) := by
          simp [shift2, shift1]
        rw [hl, map_zero, hs]
        have hdy : derivY1 (Polynomial.C (Polynomial.X + Polynomial.C α₁)) = 1 := by
          rw [derivY1, mapDeriv_C hd0, Polynomial.derivative_add, Polynomial.derivative_X,
            Polynomial.derivative_C, add_zero, map_one]
        rw [liftPoly, mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_add h0 hadd,
          mapDeriv_X h0 h1, mapDeriv_C h0, zero_add, hdy, mul_one, Polynomial.derivative_C,
          mul_zero, sub_zero, sub_self]
      rw [hsplit, mapDeriv2_mul h0 hadd hmul, map_add]
      rw [map_mul (shift2 α₁ α₂), map_mul (shift2 α₁ α₂), map_mul (shift2 α₁ α₂),
        liftPoly_mul h0 hadd hmul, ih, hX]
  induction P using Polynomial.induction_on with
  | C p => exact hC p
  | add P Q ihP ihQ =>
    rw [mapDeriv2_add h0 hadd, map_add, map_add, liftPoly_add h0 hadd, ihP, ihQ]
  | monomial n p ih =>
    have hsplit : Polynomial.C p * Polynomial.X ^ (n + 1) =
        (Polynomial.C p * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    have hX : shift2 α₁ α₂ (mapDeriv2 d Polynomial.X) =
        liftPoly d α₁ α₂ (shift2 α₁ α₂ Polynomial.X) := by
      have hl : mapDeriv2 d (Polynomial.X : Polynomial (Polynomial E)) = 0 := by
        apply mapDeriv_X (mapDeriv_zero h0)
        rw [show (1 : Polynomial E) = Polynomial.C 1 from rfl, mapDeriv_C h0, h1, map_zero]
      have hs : shift2 α₁ α₂ Polynomial.X = Polynomial.X + Polynomial.C (Polynomial.C α₂) := by
        simp [shift2]
      rw [hl, map_zero, hs]
      have hm1 : mapDeriv2 d (Polynomial.X : Polynomial (Polynomial E)) = 0 := by
        apply mapDeriv_X (mapDeriv_zero h0)
        rw [show (1 : Polynomial E) = Polynomial.C 1 from rfl, mapDeriv_C h0, h1, map_zero]
      have hm2 : mapDeriv2 d (Polynomial.C (Polynomial.C α₂)) = Polynomial.C (Polynomial.C (d α₂)) := by
        rw [mapDeriv2, mapDeriv_C (mapDeriv_zero h0), mapDeriv_C h0]
      have hdy : derivY1 (Polynomial.X + Polynomial.C (Polynomial.C α₂) : Polynomial (Polynomial E)) = 0 := by
        rw [derivY1_add, derivY1, mapDeriv_X hd0 hd1,
          derivY1, mapDeriv_C hd0, Polynomial.derivative_C, map_zero, add_zero]
      simp only [liftPoly, mapDeriv2_add h0 hadd, hm1, hm2, zero_add, hdy, mul_zero, sub_zero,
        Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
        mul_one, sub_self]
    rw [hsplit, mapDeriv2_mul h0 hadd hmul, map_add]
    conv_lhs => rw [map_mul, map_mul]
    conv_rhs => rw [map_mul, liftPoly_mul h0 hadd hmul]
    rw [ih, hX]

private theorem embed2_sourceHasse2 {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (i : Fin 2) (P : Source2) :
    embed2 φ (sourceHasse2 i 1 P) =
      mapDeriv2 (if i = 0 then D.d₀ else D.d₁) (embed2 φ P) := by
  have hd0 : (if i = 0 then D.d₀ else D.d₁) 0 = 0 := by
    split_ifs <;> [exact D.d₀_zero; exact D.d₁_zero]
  ext b a
  rw [mapDeriv2_coeff hd0]
  simp only [embed2, Polynomial.coe_mapRingHom, Polynomial.coeff_map, sourceHasse2,
    mapCoeffs_coeff]
  change φ (baseDeriv i ((P.coeff b).coeff a)) =
    (if i = 0 then D.d₀ else D.d₁) (φ ((P.coeff b).coeff a))
  fin_cases i
  · simp [hcompat.compat0]
  · simp [hcompat.compat1]

/-- **Exact Intertwining Identity**: `sourceHasse2 i 1` acts on the shifted bivariate expansion
    `polyBivar (shift2 α₁ α₂ (embed2 φ P))` identically as `liftD D.dᵢ α₁ α₂`. -/
theorem sourceHasse2_shift2 {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (i : Fin 2) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) =
      liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P))) := by
  rw [embed2_sourceHasse2 hcompat i P]
  fin_cases i
  · simp only [Fin.zero_eta, ↓reduceIte]
    rw [shift2_mapDeriv2 D.d₀_zero (fieldDerivs_d₀_one D) D.d₀_add D.d₀_mul,
      polyBivar_liftPoly D.d₀_zero]
  · simp only [Fin.mk_one, Fin.one_eq_zero_iff]
    rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1)]
    rw [shift2_mapDeriv2 D.d₁_zero (fieldDerivs_d₁_one D) D.d₁_add D.d₁_mul,
      polyBivar_liftPoly D.d₁_zero]

/-! ## 4. Iterated Cleared-Shift Words & `WordVanishes` From `TwoJetShift.complete2_cleared` -/

def clearedFactor {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [CommRing E]
    (φ : BaseRing →+* E) (i : Fin 2) : E :=
  φ (Polynomial.C (sourceX (Dpole.block i ^ boundedShiftExp s 1)))

theorem clearedFactor_ne_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} (hφ : Function.Injective φ) (i : Fin 2) :
    clearedFactor Dpole s φ i ≠ 0 := by
  intro hz
  have hzero : Polynomial.C (sourceX (Dpole.block i ^ boundedShiftExp s 1)) = (0 : BaseRing) :=
    hφ (hz.trans (map_zero φ).symm)
  have hpow_ne : Dpole.block i ^ boundedShiftExp s 1 ≠ 0 :=
    ((Dpole.monic i).pow _).ne_zero
  have hsx : sourceX (Dpole.block i ^ boundedShiftExp s 1) = 0 :=
    Polynomial.C_eq_zero.mp hzero
  apply hpow_ne
  ext n
  have hn := congrArg (fun p : Polynomial SeedPoly => (p.coeff n).coeff 0) hsx
  rw [sourceX, Polynomial.coeff_map, MvPolynomial.coeff_C, ite_eq_left rfl, Polynomial.coeff_zero,
    MvPolynomial.coeff_zero] at hn
  exact hn

theorem clearedFactor_deriv_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} {D : FieldDerivs E} (hcompat : BaseDerivCompat φ D) (i : Fin 2) :
    D.d₀ (clearedFactor Dpole s φ i) = 0 ∧ D.d₁ (clearedFactor Dpole s φ i) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [clearedFactor, hcompat.compat0, baseDeriv_sourceX, map_zero]
  · rw [clearedFactor, hcompat.compat1, baseDeriv_sourceX, map_zero]

private theorem applyWord_bivarSmul_of_const {E : Type*} [Field E] (D : FieldDerivs E)
    (α₁ α₂ c : E) (hc0 : D.d₀ c = 0) (hc1 : D.d₁ c = 0) (w : List (Fin 2)) (P : Bivar E) :
    applyWord D α₁ α₂ w (bivarSmul c P) = bivarSmul c (applyWord D α₁ α₂ w P) := by
  induction w generalizing P with
  | nil => rfl
  | cons i ws ih =>
    simp only [applyWord]
    have hstep : (if i = 0 then liftD D.d₀ α₁ α₂ (bivarSmul c P)
        else liftD D.d₁ α₁ α₂ (bivarSmul c P)) =
        bivarSmul c (if i = 0 then liftD D.d₀ α₁ α₂ P else liftD D.d₁ α₁ α₂ P) := by
      split_ifs
      · funext a b
        simp only [liftD, bivarSmul, D.d₀_mul, hc0, zero_mul, zero_add]
        ring
      · funext a b
        simp only [liftD, bivarSmul, D.d₁_mul, hc1, zero_mul, zero_add]
        ring
    rw [hstep, ih]

def applyClearedWord {h : ℕ} (Dpole : PoleData h) (s : Shape2) :
    List (Fin 2) → Source2 → Source2
  | [], P => P
  | i :: ws, P => applyClearedWord Dpole s ws (cleared2Shift Dpole s i 1 P)

def wordFactor {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [CommRing E]
    (φ : BaseRing →+* E) : List (Fin 2) → E
  | [] => 1
  | i :: ws => wordFactor Dpole s φ ws * clearedFactor Dpole s φ i

theorem wordFactor_ne_zero {h : ℕ} (Dpole : PoleData h) (s : Shape2) {E : Type*} [Field E]
    {φ : BaseRing →+* E} (hφ : Function.Injective φ) (w : List (Fin 2)) :
    wordFactor Dpole s φ w ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons i ws ih =>
    exact mul_ne_zero ih (clearedFactor_ne_zero Dpole s hφ i)

theorem applyClearedWord_mem_complete2 {h : ℕ} {Dpole : PoleData h} (Crt : CRTLift Dpole)
    (word : I → L) {s : Shape2} {W : ℕ} {P : Source2}
    (hP : P ∈ complete2 Crt word s W) (w : List (Fin 2)) :
    applyClearedWord Dpole s w P ∈
      complete2 Crt word s (W + w.length * (boundedShiftExp s 1 * h)) := by
  induction w generalizing W P with
  | nil => simpa [applyClearedWord] using hP
  | cons i ws ih =>
    have h1 := complete2_cleared Crt word hP i 1
    have h2 := ih h1
    have hlen : W + boundedShiftExp s 1 * h + ws.length * (boundedShiftExp s 1 * h) =
        W + (i :: ws).length * (boundedShiftExp s 1 * h) := by
      simp only [List.length_cons]
      ring
    simpa only [applyClearedWord, hlen] using h2

private theorem cleared2Shift_shift2 {h : ℕ} (Dpole : PoleData h) (s : Shape2)
    {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (i : Fin 2) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (cleared2Shift Dpole s i 1 P))) =
      bivarSmul (clearedFactor Dpole s φ i)
        (liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
  have hc : shift2 α₁ α₂ (embed2 φ (jetConstant2 (sourceX (Dpole.block i ^ boundedShiftExp s 1)))) =
      Polynomial.C (Polynomial.C (clearedFactor Dpole s φ i)) := by
    simp [jetConstant2, embed2, shift2, shift1, clearedFactor]
  have hmul : shift2 α₁ α₂ (embed2 φ (cleared2Shift Dpole s i 1 P)) =
      Polynomial.C (Polynomial.C (clearedFactor Dpole s φ i)) *
        shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P)) := by
    rw [cleared2Shift, map_mul, map_mul, hc]
  funext a b
  rw [hmul, polyBivar, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  have hs := congrFun (congrFun (sourceHasse2_shift2 hcompat α₁ α₂ i P) a) b
  change clearedFactor Dpole s φ i * polyBivar (shift2 α₁ α₂ (embed2 φ (sourceHasse2 i 1 P))) a b =
    bivarSmul (clearedFactor Dpole s φ i)
      (liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) a b
  rw [hs]
  rfl

theorem applyClearedWord_shift2 {h : ℕ} (Dpole : PoleData h) (s : Shape2)
    {E : Type*} [Field E] {φ : BaseRing →+* E} {D : FieldDerivs E}
    (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E) (w : List (Fin 2)) (P : Source2) :
    polyBivar (shift2 α₁ α₂ (embed2 φ (applyClearedWord Dpole s w P))) =
      bivarSmul (wordFactor Dpole s φ w)
        (applyWord D α₁ α₂ w (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
  induction w generalizing P with
  | nil =>
    funext a b
    simp [applyClearedWord, wordFactor, applyWord, bivarSmul]
  | cons i ws ih =>
    rw [applyClearedWord, ih, cleared2Shift_shift2 Dpole s hcompat α₁ α₂ i P]
    obtain ⟨hc0, hc1⟩ := clearedFactor_deriv_zero Dpole s hcompat i
    rw [applyWord_bivarSmul_of_const D α₁ α₂ _ hc0 hc1]
    have hif : liftD (if i = 0 then D.d₀ else D.d₁) α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P))) =
        (if i = 0 then liftD D.d₀ α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))
         else liftD D.d₁ α₁ α₂ (polyBivar (shift2 α₁ α₂ (embed2 φ P)))) := by
      split_ifs <;> rfl
    rw [hif]
    funext a b
    simp only [wordFactor, applyWord, bivarSmul]
    ring

/-- **Automatic `WordVanishes` from `TwoJetShift.complete2_cleared`**:
    If every `Q ∈ complete2 Crt word s W'` with `W' < N` vanishes at `(α₁, α₂)`, then every
    `P ∈ complete2 Crt word s W` satisfies `WordVanishes D α₁ α₂ k` whenever
    `W + k * (boundedShiftExp s 1 * h) < N`. -/
theorem wordVanishes_of_all_complete2_eval_zero {h : ℕ} {Dpole : PoleData h} (Crt : CRTLift Dpole)
    (word : I → L) (s : Shape2) (N : ℕ)
    {E : Type*} [Field E] {φ : BaseRing →+* E} (hφ : Function.Injective φ)
    {D : FieldDerivs E} (hcompat : BaseDerivCompat φ D) (α₁ α₂ : E)
    (hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0)
    {W k : ℕ} (hWk : W + k * (boundedShiftExp s 1 * h) < N)
    {P : Source2} (hP : P ∈ complete2 Crt word s W) :
    WordVanishes D α₁ α₂ k (polyBivar (shift2 α₁ α₂ (embed2 φ P))) := by
  intro w hw
  have hW' : W + w.length * (boundedShiftExp s 1 * h) < N :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hw) W).trans_lt hWk
  have hmem := applyClearedWord_mem_complete2 Crt word hP w
  have hz := hall _ hW' _ hmem
  have hsc := congrFun (congrFun (applyClearedWord_shift2 Dpole s hcompat α₁ α₂ w P) 0) 0
  rw [hsc] at hz
  exact (mul_eq_zero.mp hz).resolve_left (wordFactor_ne_zero Dpole s hφ w)

/-! ## 5. Bézout Evaluation Bridge (`prolongSubst_bezout` → `(α₁, α₂)` Vanishing) -/

theorem polyBivar_shift2_zero_zero {E : Type*} [CommRing E] (α₁ α₂ : E)
    (P : Polynomial (Polynomial E)) :
    polyBivar (shift2 α₁ α₂ P) 0 0 =
      Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ P := by
  have h : (Polynomial.evalRingHom 0).comp
      ((Polynomial.evalRingHom (0 : Polynomial E)).comp (shift2 α₁ α₂)) =
      Polynomial.eval₂RingHom (Polynomial.evalRingHom α₁) α₂ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro c; simp [shift2, shift1]
      · simp [shift2, shift1]
    · simp [shift2]
  have hp := RingHom.congr_fun h P
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_eval₂RingHom] at hp
  rw [polyBivar, Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero]
  exact hp

theorem natDegree_le_of_mem_ambient2 {h : ℕ} {s : Shape2} {W : ℕ} {Q : Source2}
    (hQ : Q ∈ ambient2 h s W) : Q.natDegree ≤ s.C := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro e₂ he₂
  ext e₁ e₀ a e
  simp only [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  exact hQ e₂ e₁ e₀ a e (fun hel => (not_le_of_gt he₂) hel.2.2.1)

/-- If `evJet : K1_14.Jet →+* E` evaluates the 1-jet prime `G` to `0`, `A` to a nonzero element,
    `A * Y₂ + B₁` at `α₂` to `0`, and intertwines `centerEval2` with `embed2 φ` at `(α₁, α₂)`,
    then `G ∣ prolongSubst A B₁ s.C (centerEval2 Q)` implies `Q` vanishes at `(α₁, α₂)`. -/
theorem eval_zero_of_prolongSubst_dvd {E : Type*} [Field E]
    (φ : BaseRing →+* E) (evJet : K1_14.Jet →+* E) (α₁ α₂ : E)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} {s : Shape2} {W : ℕ} {G A B₁ : K1_14.Jet}
    (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    {Q : Source2} (hQ : Q ∈ ambient2 h s W)
    (hdvd : G ∣ prolongSubst A B₁ s.C (centerEval2 Q)) :
    polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0 := by
  have hdeg : (centerEval2 Q).natDegree ≤ s.C :=
    (Polynomial.natDegree_map_le).trans (natDegree_le_of_mem_ambient2 hQ)
  obtain ⟨R, hR⟩ := prolongSubst_bezout A B₁ s.C hdeg
  obtain ⟨q, hq⟩ := hdvd
  have hps0 : evJet (prolongSubst A B₁ s.C (centerEval2 Q)) = 0 := by
    rw [hq, map_mul, hG0, zero_mul]
  have hev := congrArg (Polynomial.eval₂ evJet α₂) hR
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, hps0, hG1, map_pow,
    sub_zero, mul_zero, zero_mul] at hev
  have h0 : Polynomial.eval₂ evJet α₂ (centerEval2 Q) = 0 :=
    (mul_eq_zero.mp hev).resolve_left (pow_ne_zero s.C hAne)
  rw [polyBivar_shift2_zero_zero, ← hcomm Q]
  exact h0

/-! ## 5B. Automatic Non-Vanishing of Case-B Resultant (`Res_{z₀}(G, G^(1)) ≠ 0`) -/

private theorem pderiv_eq_zero_of_jetDegree_zero {P : PolynomialDifferential.DifferentialPolynomial CJ0.K 2}
    (h0 : PolynomialDifferential.jetDegree P (Fin.last 2) = 0) :
    MvPolynomial.pderiv (some (Fin.last 2)) P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero]
  by_cases hmem : m + Finsupp.single (some (Fin.last 2)) 1 ∈ P.support
  · exfalso
    have hle := MvPolynomial.degreeOf_le_iff.mp h0.le (m + Finsupp.single (some (Fin.last 2)) 1) hmem
    have hpos : (m + Finsupp.single (some (Fin.last 2)) 1 : Option (Fin 3) →₀ ℕ) (some (Fin.last 2)) =
        m (some (Fin.last 2)) + 1 := by simp
    omega
  · rw [MvPolynomial.notMem_support_iff.mp hmem, zero_mul]
    rfl

/-- **Linear-`Y₂` Coprimality (`not_dvd_linear_Y2`)**:
    If `Gd`, `A_poly`, `B_poly` are `Y₂`-free (`jetDegree _ (Fin.last 2) = 0`) and `¬ Gd ∣ A_poly`,
    then `Gd` cannot divide the prolongation `G₁d = A_poly * C (X (some (Fin.last 2))) + B_poly`. -/
theorem not_dvd_linear_Y2
    (Gd A_poly B_poly : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hG_top : ∀ i, PolynomialDifferential.jetDegree (Gd.coeff i) (Fin.last 2) = 0)
    (hA_top : ∀ i, PolynomialDifferential.jetDegree (A_poly.coeff i) (Fin.last 2) = 0)
    (hB_top : ∀ i, PolynomialDifferential.jetDegree (B_poly.coeff i) (Fin.last 2) = 0)
    (hndiv : ¬ Gd ∣ A_poly) :
    ¬ Gd ∣ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly) := by
  let dY2 : PolynomialDifferential.DifferentialPolynomial CJ0.K 2 →
      PolynomialDifferential.DifferentialPolynomial CJ0.K 2 :=
    fun p => MvPolynomial.pderiv (some (Fin.last 2)) p
  have hd0 : dY2 0 = 0 := map_zero _
  have hdadd : ∀ x y, dY2 (x + y) = dY2 x + dY2 y := fun x y => map_add _ x y
  have hdmul : ∀ x y, dY2 (x * y) = dY2 x * y + x * dY2 y := fun x y => by
    simp only [dY2, MvPolynomial.pderiv_mul]
  have hkill : ∀ P : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2),
      (∀ i, PolynomialDifferential.jetDegree (P.coeff i) (Fin.last 2) = 0) →
      mapDeriv dY2 P = 0 := by
    intro P hP
    apply Polynomial.ext
    intro i
    rw [mapDeriv_coeff hd0, Polynomial.coeff_zero]
    exact pderiv_eq_zero_of_jetDegree_zero (hP i)
  rintro ⟨Q, hQ⟩
  have hL := congrArg (mapDeriv dY2) hQ
  rw [mapDeriv_add hd0 hdadd, mapDeriv_mul hd0 hdadd hdmul, mapDeriv_mul hd0 hdadd hdmul,
    hkill Gd hG_top, hkill A_poly hA_top, hkill B_poly hB_top,
    zero_mul, zero_mul, zero_add, zero_add, add_zero,
    mapDeriv_C hd0] at hL
  have hX1 : dY2 (MvPolynomial.X (some (Fin.last 2))) = 1 := by simp [dY2]
  rw [hX1, map_one, mul_one] at hL
  exact hndiv ⟨mapDeriv dY2 Q, hL⟩

/-- **Automatic Resultant Non-Vanishing (`resultant_ne_zero_of_irreducible_not_dvd`)**:
    For any irreducible `Gd` of positive `z₀`-degree and any `G₁d` not divisible by `Gd`,
    the Sylvester resultant `Gd.resultant G₁d Gd.natDegree G₁d.natDegree` is nonzero. -/
theorem resultant_ne_zero_of_irreducible_not_dvd
    (Gd G₁d : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hIrr : Irreducible Gd) (hpos : 0 < Gd.natDegree) (hndiv : ¬ Gd ∣ G₁d) :
    Gd.resultant G₁d Gd.natDegree G₁d.natDegree ≠ 0 := by
  let R := PolynomialDifferential.DifferentialPolynomial CJ0.K 2
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hp : Gd.IsPrimitive := hIrr.isPrimitive hpos.ne'
  have him : Irreducible (Gd.map φ) := hp.irreducible_iff_irreducible_map_fraction_map.mp hIrr
  have hcop : IsCoprime (Gd.map φ) (G₁d.map φ) := by
    apply him.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨a, ha⟩ := hp.dvd_of_fraction_map_dvd_fraction_map hd
    exact hndiv ⟨a, ha⟩
  have hn := Polynomial.resultant_ne_zero (Gd.map φ) (G₁d.map φ) hcop
  intro hz
  apply hn
  rw [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.resultant_map_map]
  change φ (Gd.resultant G₁d Gd.natDegree G₁d.natDegree) = 0
  rw [hz, map_zero]

/-! ## 6. End-to-End Case-A Avoidance Without `hvan` & Unified Hybrid 6-Rect Rescue -/

/-- **End-to-End 2-Jet Case-A Avoidance Theorem (`caseA_avoidance_from_complete2_cleared`)**:
    Removes the `hvan` assumption completely by combining L4 `TwoJetShift.complete2_cleared`,
    L4 `TwoJetRescueBridge.prolongSubst_bezout`, and L4
    `TwoJetCaseAKernel.caseA_avoidance_of_lowCoords_surplus`. -/
theorem caseA_avoidance_from_complete2_cleared {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : BaseRing →+* E) (hφ : Function.Injective φ)
    (hcompat : BaseDerivCompat φ D)
    (evJet : K1_14.Jet →+* E) {α₁ α₂ : E} (hdet : jacDet D α₁ α₂ ≠ 0)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N physRank : ℕ)
    (G A B₁ : K1_14.Jet) (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    (k : ℕ → ℕ)
    (hk : ∀ W < N, k W < K1.p)
    (hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N)
    (hphys : ∀ W < N, Module.finrank L (ambient2 h s W) ≤
      physRank + Module.finrank L (contacted2 h word s W))
    (hlow :
      N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, (lowCoords h s W (k W)).card) :
    ∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P) := by
  by_contra hnone
  push_neg at hnone
  have hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 α₁ α₂ (embed2 φ Q)) 0 0 = 0 := fun W' hW' Q hQ =>
    eval_zero_of_prolongSubst_dvd φ evJet α₁ α₂ hcomm hG0 hAne hG1 hQ.1.1 (hnone W' hW' Q hQ)
  have hvan : ∀ W < N, ∀ P ∈ prolongKernel Crt word s W G A B₁,
      WordVanishes D α₁ α₂ (k W) (polyBivar (shift2 α₁ α₂ (embed2 φ P))) :=
    fun W hW P hP => wordVanishes_of_all_complete2_eval_zero Crt word s N hφ hcompat α₁ α₂ hall
      (hWk W hW) hP.1
  obtain ⟨W, hW, P, hP, havoid⟩ :=
    caseA_avoidance_of_lowCoords_surplus D φ hφ hdet hpos hchar Crt word s N physRank G A B₁
      k hk hphys hvan hlow
  exact havoid (hnone W hW P hP)

/-- **Unified 6-Small-Rectangle Hybrid Rescue Dichotomy at `69.63` (`A = 179,798`)**:
    Packages both branches of the 2-jet Prolongation Rescue for every small rectangle
    `r ∈ {.r0, .r1, .r2a, .r3a_j2, .r3a_j4, .r3a_j7}`:
    - **Case A (`jacDet D α₁ α₂ ≠ 0`)**: produces `W < N` and `P ∈ complete2 Crt word s W`
      whose prolongation substitution `prolongSubst A B₁ s.C (centerEval2 P)` avoids `G`
      (zero `hvan` assumption, directly from L4 `TwoJetShift.complete2_cleared` + L4
      `PoleBound2Jet.pole_bound_2jet`).
    - **Case B (`jacDet D α₁ α₂ = 0`, nonzero Sylvester resultant `Res_{z₀}(G, G^(1))`)**:
      proves `T.card ≤ smallRectCap6963 r ≤ 44_890_000_000_000_000` (`44.89e15 < 61.30e15`)
      for any finite `T ⊆ closeHigh 179798 w` of degree-`< 133,721` polynomials on `(G, G^(1))`. -/
theorem small_rect_hybrid_rescue_6963 {E : Type*} [Field E] [CharP E K1.p]
    (D : FieldDerivs E) (φ : BaseRing →+* E) (hφ : Function.Injective φ)
    (hcompat : BaseDerivCompat φ D) (evJet : K1_14.Jet →+* E) (α₁ α₂ : E)
    (hcomm : ∀ Q : Source2,
      Polynomial.eval₂ evJet α₂ (centerEval2 Q) =
        Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 φ Q))
    {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {Dpole : PoleData h} (Crt : CRTLift Dpole) (word : I → L) (s : Shape2) (N physRank : ℕ)
    (G A B₁ : K1_14.Jet) (hG0 : evJet G = 0) (hAne : evJet A ≠ 0) (hG1 : evJet A * α₂ + evJet B₁ = 0)
    (k : ℕ → ℕ) (hk : ∀ W < N, k W < K1.p)
    (hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N)
    (hphys : ∀ W < N, Module.finrank L (ambient2 h s W) ≤
      physRank + Module.finrank L (contacted2 h word s W))
    (hlow :
      N * (physRank + poleCredit2 h s + 2 * h * (s.U + 1) * groupedPoleMoment2 s) <
      ∑ W ∈ Finset.range N, (lowCoords h s W (k W)).card)
    {r : RescueRect} (hr : IsSmallRect r) {j u : ℕ} (hin : InRect j u r)
    (Gd A_poly B_poly : Polynomial (PolynomialDifferential.DifferentialPolynomial CJ0.K 2))
    (hIrr : Irreducible Gd) (hposG : 0 < Gd.natDegree)
    (hG_u : Gd.natDegree ≤ u)
    (hG₁_u : (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree ≤ u)
    (hG_top_all : ∀ i, PolynomialDifferential.jetDegree (Gd.coeff i) (Fin.last 2) = 0)
    (hA_top_all : ∀ i, PolynomialDifferential.jetDegree (A_poly.coeff i) (Fin.last 2) = 0)
    (hB_top_all : ∀ i, PolynomialDifferential.jetDegree (B_poly.coeff i) (Fin.last 2) = 0)
    (hndivA : ¬ Gd ∣ A_poly)
    (hG_tot : ∀ i ≤ Gd.natDegree, PolynomialDifferential.jetTotalDegree (Gd.coeff i) ≤ j)
    (hG_idx : ∀ i ≤ Gd.natDegree, (Gd.coeff i).weightedTotalDegree CJ0.indexWeight ≤ 1)
    (hG₁_tot : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      PolynomialDifferential.jetTotalDegree
        ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i) ≤ j + 1)
    (hG₁_idx : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i).weightedTotalDegree
        CJ0.indexWeight ≤ 2)
    (hG₁_top : ∀ i ≤ (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).natDegree,
      PolynomialDifferential.jetDegree
        ((A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).coeff i) (Fin.last 2) ≤ 1)
    (w : CJ0.Node → CJ0.K) (T : Finset (Polynomial CJ0.K))
    (hT : (T : Set (Polynomial CJ0.K)) ⊆ CJ0High133721.closeHigh 179798 w)
    (hcommon : ∀ f ∈ T, ∃ z₀ : Polynomial CJ0.K,
      Gd.eval₂ (PolynomialDifferential.differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0 ∧
      (A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly).eval₂
        (PolynomialDifferential.differentialSpecializationHom (d := 2) f).toRingHom z₀ = 0) :
    (∃ W < N, ∃ P ∈ complete2 Crt word s W, ¬ G ∣ prolongSubst A B₁ s.C (centerEval2 P)) ∨
    (T.card ≤ smallRectCap6963 r ∧ T.card ≤ 44_890_000_000_000_000) := by
  by_cases hdet : jacDet D α₁ α₂ ≠ 0
  · exact Or.inl (caseA_avoidance_from_complete2_cleared D φ hφ hcompat evJet hdet hcomm
      hpos hchar Crt word s N physRank G A B₁ hG0 hAne hG1 k hk hWk hphys hlow)
  · let G₁d := A_poly * Polynomial.C (MvPolynomial.X (some (Fin.last 2))) + B_poly
    have hndiv : ¬ Gd ∣ G₁d := not_dvd_linear_Y2 Gd A_poly B_poly hG_top_all hA_top_all hB_top_all hndivA
    have hne : Gd.resultant G₁d Gd.natDegree G₁d.natDegree ≠ 0 :=
      resultant_ne_zero_of_irreducible_not_dvd Gd G₁d hIrr hposG hndiv
    exact Or.inr (caseB_small_rects_card_le_6963 hr hin Gd G₁d hG_u hG₁_u le_rfl le_rfl
      (Or.inl hposG.ne') hne hG_tot hG_idx (fun i _ => hG_top_all i)
      hG₁_tot hG₁_idx hG₁_top w T hT hcommon)

end

end TwoJetCaseADriver

#print axioms TwoJetCaseADriver.fractionRingFieldDerivs_compat
#print axioms TwoJetCaseADriver.sourceHasse2_shift2
#print axioms TwoJetCaseADriver.applyClearedWord_mem_complete2
#print axioms TwoJetCaseADriver.applyClearedWord_shift2
#print axioms TwoJetCaseADriver.wordVanishes_of_all_complete2_eval_zero
#print axioms TwoJetCaseADriver.eval_zero_of_prolongSubst_dvd
#print axioms TwoJetCaseADriver.not_dvd_linear_Y2
#print axioms TwoJetCaseADriver.resultant_ne_zero_of_irreducible_not_dvd
#print axioms TwoJetCaseADriver.caseA_avoidance_from_complete2_cleared
#print axioms TwoJetCaseADriver.small_rect_hybrid_rescue_6963
