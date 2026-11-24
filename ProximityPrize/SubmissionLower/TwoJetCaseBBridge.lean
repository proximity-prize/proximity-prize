import ProximityPrize.SubmissionLower.TwoJetCaseAFXContact
import ProximityPrize.SubmissionLower.TwoJetCaseBResultant
import ProximityPrize.SubmissionLower.R6960ThirdPole

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 800000

/-!
# End-to-End Case-B Algebraic Descent & 6-Small-Rect Cardinality Cap at `69.61` (`TwoJetCaseBBridge`)

Closes the Case-B (`jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0`) branch for all 6
small Rescue rectangles at `69.61` (`A = 179,818`, `h ∈ [2327, 2449]`, `deg ≤ 133,520 < 133,721`):

1. **Seed-Variable Elimination & Leading-Coefficient Descent (`caseB_seedFree_annihilator`)**:
   Given an irreducible linear-in-`Y₁` prime `G : K1_14.Jet` (`G.natDegree = 1`, `UsesSeed G`,
   `RowCaps G ⟨0, j, 1, u⟩`, `1 ≤ j ≤ 7`, `1 ≤ u ≤ 22`) with `jacDet = 0`:
   - Picks `i : Fin 2` with `deg_{z_i}(G) ≥ 1` (using `UsesSeed G`).
   - Forms the Sylvester resultant `R = Res_{z_i}(G, G^(1)) ∈ (FX[Y₀, Y₁, Y₂])[z_{1-i}]` and
     proves `R ≠ 0` (`not_dvd_linear_Y2` + `resultant_ne_zero`) and `deg_{z_{1-i}}(R) ≤ 2*u² < p`.
   - Proves `d_i(α₁) ≠ 0` from `IsRelPrime (G.coeff 1) (G.coeff 0)` and `u < p`.
   - Applies the `FX[Y₀]`-derivation `δ = d_{1-i}(α₁) d_i - d_i(α₁) d_{1-i}` (`δ(α₁) = δ(α₂) = 0`,
     `δ(z_{1-i}) = -d_i(α₁) ≠ 0`) iteratively `d = deg_{z_{1-i}}(R)` times to `R(z_{1-i}, α₁, α₂) = 0`,
     yielding `d! * R.leadingCoeff(α₁, α₂) = 0`, hence `R.leadingCoeff(α₁, α₂) = 0` (`d < p`)!
   - Clears the finite `L[X]`-denominators of `R.leadingCoeff` and applies a `K`-linear functional
     `λ : L →ₗ[K] K` to produce a nonzero `Q ∈ DifferentialPolynomial K 2` with
     `OrderTwoHigh ⟨(2*j + 1)*u, 3*u, u⟩ Q` that vanishes on every mark `(z, S)` with
     `jetAt G z S = 0` and `jetAt (prolongA G) z S ≠ 0`.
2. **`A = 0` Exception Bound (`caseB_leading_zero_card_le`)**:
   Marks with `jetAt G z S = 0` and `jetAt (prolongA G) z S = 0` vanish on both `G.coeff 1` and
   `G.coeff 0`, hence contribute at most `(2*j - 1)*u * (p + 1) ≤ 143 * (p + 1)` labels via
   `Lower6960.ThirdPole.count_common` / `K1_10.frobenius_coefficient_exception_count`.
3. **6-Small-Rect `69.61` Cardinality Cap (`caseB_small_rect_card_le_6961`)**:
   Instantiates L4 `CJ0High133721.order_two_card_le_high133721` on `T_good.image F.scalar`
   (using `F.distinct`), proving `(Γ.filter (jetAt G ... = 0)).card ≤ caseBCap6961 r ≤ 37_710_000_000_000_000`.
-/

namespace TwoJetCaseBBridge
noncomputable section

open Polynomial Finset MvPolynomial PolynomialDifferential
open K1 (I K p)
open K1_14 (L FX Seeds Equation Jet liftPoly atX graphEval jetAt seedEmbedding)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open TwoJetCaseADriver (BaseRing mapDeriv mapDeriv_coeff mapDeriv_zero mapDeriv_add mapDeriv_mul
  fracDeriv_algebraMap fractionRingFieldDerivs fractionRingFieldDerivs_compat)
open TwoJetCaseAKernel (FieldDerivs jacDet)
open TwoJetCaseAFX (EField seedsToE seedsY0ToE seedsY0ToE_injective prolongA prolongB1
  prolongA_rowCaps prolongB1_rowCaps prolong_vanish_at_mark alpha1 evJetAt alpha2)
open CJ0High133721 (BoxShape BoxOK OrderTwoHigh AgreementOKHigh closeHigh tariffHigh kHigh NHigh
  order_two_card_le_high133721)
open scoped BigOperators Polynomial

/-! ## 1. 6 Small-Rectangle Box Shapes & Kernel-Checked `tariffHigh 179818` Bounds -/

inductive SmallRect61
  | r0     -- j = 1, u = 1
  | r1     -- j = 1, 2 ≤ u ≤ 6
  | r2a    -- j = 1, 7 ≤ u ≤ 22
  | r3a_j2 -- j = 2, 1 ≤ u ≤ 17
  | r3a_j4 -- 3 ≤ j ≤ 4, 1 ≤ u ≤ 13
  | r3a_j7 -- 5 ≤ j ≤ 7, 1 ≤ u ≤ 11
  deriving DecidableEq, Repr

def SmallRect61.In (j u : ℕ) : SmallRect61 → Prop
  | .r0     => j = 1 ∧ u = 1
  | .r1     => j = 1 ∧ 2 ≤ u ∧ u ≤ 6
  | .r2a    => j = 1 ∧ 7 ≤ u ∧ u ≤ 22
  | .r3a_j2 => j = 2 ∧ 1 ≤ u ∧ u ≤ 17
  | .r3a_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 1 ≤ u ∧ u ≤ 13
  | .r3a_j7 => (5 ≤ j ∧ j ≤ 7) ∧ 1 ≤ u ∧ u ≤ 11

def SmallRect61.box : SmallRect61 → BoxShape
  | .r0     => ⟨3, 3, 1⟩
  | .r1     => ⟨18, 18, 6⟩
  | .r2a    => ⟨66, 66, 22⟩
  | .r3a_j2 => ⟨85, 51, 17⟩
  | .r3a_j4 => ⟨117, 39, 13⟩
  | .r3a_j7 => ⟨165, 33, 11⟩

def SmallRect61.cap : SmallRect61 → ℕ
  | .r0     => 2_000_000_000_000
  | .r1     => 640_000_000_000_000
  | .r2a    => 34_450_000_000_000_000
  | .r3a_j2 => 36_830_000_000_000_000
  | .r3a_j4 => 34_900_000_000_000_000
  | .r3a_j7 => 37_710_000_000_000_000

theorem agreementOK_6961 : AgreementOKHigh 179818 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem smallRect61_boxOK (r : SmallRect61) : BoxOK r.box := by
  cases r <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem smallRect61_tariff_le (r : SmallRect61) :
    tariffHigh 179818 r.box + 143 * (p + 1) ≤ r.cap := by
  cases r <;> decide +kernel

theorem smallRect61_cap_le (r : SmallRect61) : r.cap ≤ 37_710_000_000_000_000 := by
  cases r <;> decide

theorem smallRect61_bounds {j u : ℕ} {r : SmallRect61} (hin : r.In j u) :
    1 ≤ j ∧ j ≤ 7 ∧ 1 ≤ u ∧ u ≤ 22 ∧
    (2 * j + 1) * u ≤ r.box.B ∧ 3 * u ≤ r.box.J ∧ u ≤ r.box.C ∧ (2 * j - 1) * u ≤ 143 := by
  cases r with
  | r0 => rcases hin with ⟨rfl, rfl⟩; dsimp [SmallRect61.box]; omega
  | r1 => rcases hin with ⟨rfl, h1, h2⟩; dsimp [SmallRect61.box]; omega
  | r2a => rcases hin with ⟨rfl, h1, h2⟩; dsimp [SmallRect61.box]; omega
  | r3a_j2 => rcases hin with ⟨rfl, h1, h2⟩; dsimp [SmallRect61.box]; omega
  | r3a_j4 =>
    rcases hin with ⟨⟨hj1, hj2⟩, h1, h2⟩
    dsimp [SmallRect61.box]
    have hmul : (2 * j + 1) * u ≤ 9 * 13 := Nat.mul_le_mul (by omega) h2
    have hmul2 : (2 * j - 1) * u ≤ 7 * 13 := Nat.mul_le_mul (by omega) h2
    omega
  | r3a_j7 =>
    rcases hin with ⟨⟨hj1, hj2⟩, h1, h2⟩
    dsimp [SmallRect61.box]
    have hmul : (2 * j + 1) * u ≤ 15 * 11 := Nat.mul_le_mul (by omega) h2
    have hmul2 : (2 * j - 1) * u ≤ 13 * 11 := Nat.mul_le_mul (by omega) h2
    omega

/-! ## 2. `FX`-Jet Ring & Re-indexing by Seed Variables `(z_i, z_{1-i})` -/

open scoped Classical

private theorem charP_EField : CharP EField p := by
  have hφ : Function.Injective (algebraMap BaseRing EField) := IsFractionRing.injective BaseRing EField
  refine ⟨fun n => ?_⟩
  have hcast : (n : EField) =
      algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.C (n : L)))) := by simp
  rw [hcast, show (0 : EField) = algebraMap BaseRing EField 0 from (map_zero _).symm, hφ.eq_iff,
    Polynomial.C_eq_zero, Polynomial.C_eq_zero, MvPolynomial.C_eq_zero]
  exact CharP.cast_eq_zero_iff L p n

/-- Order-2 differential polynomials over `FX` (`MvPolynomial (Fin 3) FX`, variables `Y₀, Y₁, Y₂`). -/
abbrev FXJet2 := MvPolynomial (Fin 3) FX

private def fxJet2Weight_tot : Fin 3 → ℕ := fun _ => 1
private def fxJet2Weight_idx : Fin 3 → ℕ := fun k => k.val
private def fxJet2Weight_top : Fin 3 → ℕ := Pi.single (Fin.last 2) 1

private def otherSeed (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

private theorem otherSeed_ne (i : Fin 2) : otherSeed i ≠ i := by
  fin_cases i <;> decide

private theorem otherSeed_other (i : Fin 2) : otherSeed (otherSeed i) = i := by
  fin_cases i <;> decide

/-- Ring isomorphism `Seeds[Y₀][Y₁][Y₂] →+* ((FXJet2)[z_{1-i}])[z_i]` viewing a 2-jet polynomial
    over `FX[z₀, z₁]` as a univariate polynomial in `z_i` over `(FX[Y₀, Y₁, Y₂])[z_{1-i}]`. -/
private def seedView (i : Fin 2) :
    Polynomial Jet →+* Polynomial (Polynomial FXJet2) :=
  let cFX : FX →+* Polynomial (Polynomial FXJet2) :=
    Polynomial.C.comp (Polynomial.C.comp MvPolynomial.C)
  let cSeed : Seeds →+* Polynomial (Polynomial FXJet2) :=
    MvPolynomial.eval₂Hom cFX (fun k => if k = i then Polynomial.X else Polynomial.C Polynomial.X)
  let cY0 : Equation →+* Polynomial (Polynomial FXJet2) :=
    Polynomial.eval₂RingHom cSeed (Polynomial.C (Polynomial.C (MvPolynomial.X 0)))
  let cY1 : Jet →+* Polynomial (Polynomial FXJet2) :=
    Polynomial.eval₂RingHom cY0 (Polynomial.C (Polynomial.C (MvPolynomial.X 1)))
  Polynomial.eval₂RingHom cY1 (Polynomial.C (Polynomial.C (MvPolynomial.X 2)))

/-- Inverse of `seedView i` on `Polynomial (Polynomial FXJet2) →+* Polynomial Jet`. -/
private def seedUnview (i : Fin 2) :
    Polynomial (Polynomial FXJet2) →+* Polynomial Jet :=
  let cFX : FX →+* Polynomial Jet :=
    Polynomial.C.comp (Polynomial.C.comp (Polynomial.C.comp MvPolynomial.C))
  let cJet : FXJet2 →+* Polynomial Jet :=
    MvPolynomial.eval₂Hom cFX (fun k =>
      match k with
      | ⟨0, _⟩ => Polynomial.C (Polynomial.C Polynomial.X)
      | ⟨1, _⟩ => Polynomial.C Polynomial.X
      | ⟨2, _⟩ => Polynomial.X)
  let cOther : Polynomial FXJet2 →+* Polynomial Jet :=
    Polynomial.eval₂RingHom cJet (Polynomial.C (Polynomial.C (Polynomial.C (MvPolynomial.X (otherSeed i)))))
  Polynomial.eval₂RingHom cOther (Polynomial.C (Polynomial.C (Polynomial.C (MvPolynomial.X i))))

private theorem seedUnview_comp_seedView (i : Fin 2) :
    (seedUnview i).comp (seedView i) = RingHom.id (Polynomial Jet) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply MvPolynomial.ringHom_ext
        · intro a; simp [seedView, seedUnview]
        · intro k
          by_cases hk : k = i
          · subst hk; simp [seedView, seedUnview]
          · have hko : k = otherSeed i := by fin_cases i <;> fin_cases k <;> simp_all [otherSeed]
            subst hko
            simp [seedView, seedUnview, otherSeed_ne i]
      · simp [seedView, seedUnview]
    · simp [seedView, seedUnview]
  · simp [seedView, seedUnview]

private theorem seedView_comp_seedUnview (i : Fin 2) :
    (seedView i).comp (seedUnview i) = RingHom.id (Polynomial (Polynomial FXJet2)) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro a; simp [seedView, seedUnview]
      · intro k; fin_cases k <;> simp [seedView, seedUnview]
    · simp [seedView, seedUnview, otherSeed_ne i]
  · simp [seedView, seedUnview]

private def seedViewEquiv (i : Fin 2) : Polynomial Jet ≃+* Polynomial (Polynomial FXJet2) where
  toFun := seedView i
  invFun := seedUnview i
  left_inv x := RingHom.congr_fun (seedUnview_comp_seedView i) x
  right_inv y := RingHom.congr_fun (seedView_comp_seedUnview i) y
  map_mul' := (seedView i).map_mul
  map_add' := (seedView i).map_add

private theorem seedView_C_natDegree_pos {G : Jet} {i : Fin 2}
    (hpos : ∃ j k, 0 < ((G.coeff j).coeff k).degreeOf i) :
    0 < (seedView i (Polynomial.C G)).natDegree := by
  obtain ⟨j, k, hdeg⟩ := hpos
  have hne : (seedView i (Polynomial.C G)).natDegree ≠ 0 := by
    intro h0
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero h0
    let c := (seedView i (Polynomial.C G)).coeff 0
    have hG : Polynomial.C G = seedUnview i (Polynomial.C c) := by
      have h1 := congrArg (seedUnview i) hconst
      have h2 := RingHom.congr_fun (seedUnview_comp_seedView i) (Polynomial.C G)
      simpa [RingHom.comp_apply, c] using h2.symm.trans h1
    -- Every coefficient of `seedUnview i (Polynomial.C c)` has `degreeOf i = 0`!
    have hzero_deg : ∀ q : Polynomial FXJet2,
        ∀ e₂ e₁ e₀, ((((seedUnview i (Polynomial.C q)).coeff e₂).coeff e₁).coeff e₀).degreeOf i = 0 := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p₁ p₂ ih₁ ih₂ =>
        intro e₂ e₁ e₀
        rw [Polynomial.C_add, map_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
        exact Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans (by simp [ih₁, ih₂]))
      | monomial m f =>
        induction f using MvPolynomial.induction_on with
        | C a =>
          intro e₂ e₁ e₀
          have hmon : seedUnview i (Polynomial.C (Polynomial.monomial m (MvPolynomial.C a))) =
              Polynomial.C (Polynomial.C (Polynomial.C
                (MvPolynomial.C a * MvPolynomial.X (otherSeed i) ^ m))) := by
            rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
            simp [seedUnview, Polynomial.C_mul, Polynomial.C_pow]
          rw [hmon, Polynomial.coeff_C]; split_ifs with h2
          · rw [Polynomial.coeff_C]; split_ifs with h1
            · rw [Polynomial.coeff_C]; split_ifs with h0
              · apply Nat.eq_zero_of_le_zero
                refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
                rw [MvPolynomial.degreeOf_C, zero_add]
                refine (MvPolynomial.degreeOf_pow_le _ _ _).trans ?_
                rw [MvPolynomial.degreeOf_X, if_neg (otherSeed_ne i).symm, mul_zero]
              · simp
            · simp
          · simp
        | add f₁ f₂ ih₁ ih₂ =>
          intro e₂ e₁ e₀
          rw [map_add, Polynomial.C_add, map_add, Polynomial.coeff_add,
            Polynomial.coeff_add, Polynomial.coeff_add]
          exact Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans (by simp [ih₁, ih₂]))
        | mul_X f v ih =>
          intro e₂ e₁ e₀
          have hmul : seedUnview i (Polynomial.C (Polynomial.monomial m (f * MvPolynomial.X v))) =
              seedUnview i (Polynomial.C (Polynomial.monomial m f)) *
                seedUnview i (Polynomial.C (Polynomial.C (MvPolynomial.X v))) := by
            rw [← map_mul, ← Polynomial.C_mul, Polynomial.monomial_mul_C]
          rw [hmul]
          fin_cases v <;> dsimp only
          · have hX : seedUnview i (Polynomial.C (Polynomial.C (MvPolynomial.X (⟨0, by decide⟩ : Fin 3)))) =
                Polynomial.C (Polynomial.C Polynomial.X) := by simp [seedUnview]
            rw [hX, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C]
            cases e₀ with
            | zero => simp
            | succ e₀ => rw [Polynomial.coeff_mul_X]; exact ih e₂ e₁ e₀
          · have hX : seedUnview i (Polynomial.C (Polynomial.C (MvPolynomial.X (⟨1, by decide⟩ : Fin 3)))) =
                Polynomial.C Polynomial.X := by simp [seedUnview]
            rw [hX, Polynomial.coeff_mul_C]
            cases e₁ with
            | zero => simp
            | succ e₁ => rw [Polynomial.coeff_mul_X]; exact ih e₂ e₁ e₀
          · have hX : seedUnview i (Polynomial.C (Polynomial.C (MvPolynomial.X (⟨2, by decide⟩ : Fin 3)))) =
                Polynomial.X := by simp [seedUnview]
            rw [hX]
            cases e₂ with
            | zero => simp
            | succ e₂ => rw [Polynomial.coeff_mul_X]; exact ih e₂ e₁ e₀
    have hz := hzero_deg c 0 j k
    rw [← hG, Polynomial.coeff_C_zero] at hz
    omega
  exact Nat.pos_of_ne_zero hne

private theorem seedView_C_irreducible {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    (i : Fin 2) :
    Irreducible (seedView i (Polynomial.C G)) := by
  have hIrr2 : Irreducible (Polynomial.C G : Polynomial Jet) := by
    have hnu : ¬ IsUnit (Polynomial.C G : Polynomial Jet) := by
      intro hu
      exact hIrr.not_isUnit (Polynomial.isUnit_C.mp hu)
    refine ⟨hnu, fun a b hab => ?_⟩
    have hdeg0 : a.natDegree + b.natDegree = 0 := by
      have ha : a ≠ 0 := fun hz => hIrr.ne_zero (by rw [hz, zero_mul] at hab; exact Polynomial.C_eq_zero.mp hab)
      have hb : b ≠ 0 := fun hz => hIrr.ne_zero (by rw [hz, mul_zero] at hab; exact Polynomial.C_eq_zero.mp hab)
      rw [← Polynomial.natDegree_mul ha hb, ← hab, Polynomial.natDegree_C]
    have ha0 := Polynomial.eq_C_of_natDegree_eq_zero (by omega : a.natDegree = 0)
    have hb0 := Polynomial.eq_C_of_natDegree_eq_zero (by omega : b.natDegree = 0)
    rw [ha0, hb0, ← Polynomial.C_mul] at hab
    have hGab := Polynomial.C_injective hab
    rcases hIrr.isUnit_or_isUnit hGab with hua | hub
    · exact Or.inl (ha0.symm ▸ hua.map Polynomial.C)
    · exact Or.inr (hb0.symm ▸ hub.map Polynomial.C)
  simpa [seedViewEquiv] using (MulEquiv.irreducible_iff (seedViewEquiv i).toMulEquiv).mpr hIrr2

/-! ## 3. Non-Vanishing of `Res_{z_i}(G, G^(1))` & Box Degree Bounds -/

private def prolongPoly (G : Jet) : Polynomial Jet :=
  Polynomial.C (prolongA G) * Polynomial.X + Polynomial.C (prolongB1 G)

private theorem seedView_not_dvd_prolong {G : Jet} (hdegG : G.natDegree = 1) (i : Fin 2) :
    ¬ seedView i (Polynomial.C G) ∣ seedView i (prolongPoly G) := by
  intro ⟨Q, hQ⟩
  have hQ' := congrArg (seedUnview i) hQ
  have hl := RingHom.congr_fun (seedUnview_comp_seedView i) (prolongPoly G)
  have hr := RingHom.congr_fun (seedUnview_comp_seedView i) (Polynomial.C G)
  rw [map_mul] at hQ'
  simp only [RingHom.comp_apply, RingHom.id_apply] at hl hr
  rw [hl, hr] at hQ'
  -- Take `Y₂`-coefficient `1` on both sides: `prolongA G = G * (seedUnview i Q).coeff 1`!
  have h1 := congrArg (fun P : Polynomial Jet => P.coeff 1) hQ'
  simp only [prolongPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X] at h1
  simp only [↓reduceIte, one_ne_zero, add_zero, mul_one] at h1
  -- Compare `Y₁`-degrees: `prolongA G = 2 * C (G.coeff 1)` has `natDegree = 0`, while `G` has `natDegree = 1`!
  have hAne : prolongA G ≠ 0 := by
    have hA1 : G.coeff 1 ≠ 0 := by
      rw [← hdegG, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
    intro hz
    have h20 : (2 : Equation) * G.coeff 1 = 0 := by
      have := congrArg (fun P : Jet => P.coeff 0) hz
      simpa [prolongA, show (2 : Jet) = Polynomial.C (2 : Equation) from (map_ofNat Polynomial.C 2).symm] using this
    have h2ne : (2 : Equation) ≠ 0 := by
      intro h2
      have h2fx : (2 : FX) = 0 := by
        have := congrArg (fun p : Equation => (p.coeff 0).coeff 0) h2
        simpa using this
      have h2L : (2 : L) = 0 := by
        have h1 : (2 : FX) = algebraMap (Polynomial L) FX (Polynomial.C 2) := by simp only [map_ofNat]
        rw [h1] at h2fx
        exact Polynomial.C_eq_zero.mp (IsFractionRing.injective (Polynomial L) FX (h2fx.trans (map_zero _).symm))
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff L p 2).mp (by simpa using h2L)
      have hle := Nat.le_of_dvd (by decide) hdvd
      change 2130706433 ≤ 2 at hle; omega
    exact hA1 ((mul_eq_zero.mp h20).resolve_left h2ne)
  have hQne : (seedUnview i Q).coeff 1 ≠ 0 := fun hz => hAne (by rw [h1, hz, mul_zero])
  have hGne : G ≠ 0 := fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega
  have hdegA : (prolongA G).natDegree = 0 := by
    rw [show prolongA G = Polynomial.C (2 * G.coeff 1) by simp [prolongA, map_ofNat]]
    exact Polynomial.natDegree_C _
  have hdegMul := Polynomial.natDegree_mul hGne hQne
  rw [← h1, hdegA, hdegG] at hdegMul
  omega

private theorem resultant_seedView_ne_zero {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    {i : Fin 2} (hpos : ∃ j k, 0 < ((G.coeff j).coeff k).degreeOf i) :
    let Gv := seedView i (Polynomial.C G)
    let G1v := seedView i (prolongPoly G)
    Gv.resultant G1v Gv.natDegree G1v.natDegree ≠ 0 := by
  intro Gv G1v
  have hIrrV : Irreducible Gv := seedView_C_irreducible hIrr hdegG i
  have hposV : 0 < Gv.natDegree := seedView_C_natDegree_pos hpos
  have hndiv : ¬ Gv ∣ G1v := seedView_not_dvd_prolong hdegG i
  let R := Polynomial FXJet2
  let φ := algebraMap R (FractionRing R)
  have hinj : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hp : Gv.IsPrimitive := hIrrV.isPrimitive hposV.ne'
  have him : Irreducible (Gv.map φ) := hp.irreducible_iff_irreducible_map_fraction_map.mp hIrrV
  have hcop : IsCoprime (Gv.map φ) (G1v.map φ) := by
    apply him.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨a, ha⟩ := hp.dvd_of_fraction_map_dvd_fraction_map hd
    exact hndiv ⟨a, ha⟩
  have hn := Polynomial.resultant_ne_zero (Gv.map φ) (G1v.map φ) hcop
  intro hz
  apply hn
  rw [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.resultant_map_map]
  change φ (Gv.resultant G1v Gv.natDegree G1v.natDegree) = 0
  rw [hz, map_zero]

/-! ## 4. Degree Bounds on `seedView` & Sylvester Resultant `R` -/

private theorem seedView_bounds_of_rowCaps (i : Fin 2) {P : Jet} {B J U : ℕ}
    (hP : RowCaps P ⟨0, B, J, U⟩) :
    let Pv := seedView i (Polynomial.C P)
    Pv.natDegree ≤ U ∧
    (∀ a, (Pv.coeff a).natDegree ≤ U) ∧
    (∀ a b, ((Pv.coeff a).coeff b).weightedTotalDegree fxJet2Weight_tot ≤ B) ∧
    (∀ a b, ((Pv.coeff a).coeff b).weightedTotalDegree fxJet2Weight_idx ≤ J) ∧
    (∀ a b, ((Pv.coeff a).coeff b).weightedTotalDegree fxJet2Weight_top = 0) := by
  intro Pv
  -- Express `Pv` explicitly by summing over the monomials of `P`!
  have hmon (e₁ e₀ : ℕ) (m : Fin 2 →₀ ℕ) (c : FX)
      (hB : e₀ + e₁ ≤ B) (hJ : e₁ ≤ J) (hU : m 0 + m 1 ≤ U) :
      let T : Polynomial (Polynomial FXJet2) :=
        Polynomial.monomial (m i) (Polynomial.monomial (m (otherSeed i))
          (MvPolynomial.monomial (Finsupp.single 0 e₀ + Finsupp.single 1 e₁) c))
      T.natDegree ≤ U ∧
      (∀ a, (T.coeff a).natDegree ≤ U) ∧
      (∀ a b, ((T.coeff a).coeff b).weightedTotalDegree fxJet2Weight_tot ≤ B) ∧
      (∀ a b, ((T.coeff a).coeff b).weightedTotalDegree fxJet2Weight_idx ≤ J) ∧
      (∀ a b, ((T.coeff a).coeff b).weightedTotalDegree fxJet2Weight_top = 0) := by
    intro T
    have wtd_mon : ∀ (w : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) (c' : FX),
        (MvPolynomial.monomial d c').weightedTotalDegree w ≤ Finsupp.weight w d := by
      intro w d c'
      change (MvPolynomial.monomial d c').support.sup (Finsupp.weight w) ≤ Finsupp.weight w d
      refine Finset.sup_le fun m' hm' => ?_
      have h : m' = d := by
        by_contra hne
        exact (MvPolynomial.mem_support_iff.mp hm') (by simp [MvPolynomial.coeff_monomial, Ne.symm hne])
      subst h; exact le_rfl
    have hmi : m i ≤ U := by
      fin_cases i
      · change m 0 ≤ U; omega
      · change m 1 ≤ U; omega
    have hmo : m (otherSeed i) ≤ U := by fin_cases i <;> simp [otherSeed] <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Polynomial.natDegree_monomial_le _ |>.trans hmi
    · intro a; dsimp only [T]; rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
      · exact Polynomial.natDegree_monomial_le _ |>.trans hmo
      · simp
    · intro a b; dsimp only [T]; rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
      · rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
        · refine (wtd_mon _ _ _).trans ?_
          rw [map_add, Finsupp.weight_apply, Finsupp.weight_apply,
            Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
          simp [fxJet2Weight_tot]; omega
        · simp [MvPolynomial.weightedTotalDegree]
      · simp [MvPolynomial.weightedTotalDegree]
    · intro a b; dsimp only [T]; rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
      · rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
        · refine (wtd_mon _ _ _).trans ?_
          rw [map_add, Finsupp.weight_apply, Finsupp.weight_apply,
            Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
          simp [fxJet2Weight_idx]; omega
        · simp [MvPolynomial.weightedTotalDegree]
      · simp [MvPolynomial.weightedTotalDegree]
    · intro a b; dsimp only [T]; rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
      · rw [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs
        · apply Nat.eq_zero_of_le_zero
          refine (wtd_mon _ _ _).trans ?_
          rw [map_add, Finsupp.weight_apply, Finsupp.weight_apply,
            Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
          simp [fxJet2Weight_top, Pi.single_apply, show (0 : Fin 3) ≠ Fin.last 2 by decide,
            show (1 : Fin 3) ≠ Fin.last 2 by decide]
        · simp [MvPolynomial.weightedTotalDegree]
      · simp [MvPolynomial.weightedTotalDegree]
  have hPv_sum : Pv =
      ∑ e₁ ∈ P.support, ∑ e₀ ∈ (P.coeff e₁).support, ∑ m ∈ ((P.coeff e₁).coeff e₀).support,
        Polynomial.monomial (m i) (Polynomial.monomial (m (otherSeed i))
          (MvPolynomial.monomial (Finsupp.single 0 e₀ + Finsupp.single 1 e₁)
            (((P.coeff e₁).coeff e₀).coeff m))) := by
    dsimp only [Pv]
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow, map_sum, map_sum]
    apply Finset.sum_congr rfl; intro e₁ _
    rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
    conv_lhs => rw [(P.coeff e₁).as_sum_support_C_mul_X_pow, map_sum, map_sum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro e₀ _
    rw [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
    conv_lhs => rw [((P.coeff e₁).coeff e₀).as_sum, map_sum, map_sum, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _
    have hms : MvPolynomial.monomial m (((P.coeff e₁).coeff e₀).coeff m) =
        MvPolynomial.C (((P.coeff e₁).coeff e₀).coeff m) *
          MvPolynomial.X i ^ m i * MvPolynomial.X (otherSeed i) ^ m (otherSeed i) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      fin_cases i
      · simp [otherSeed, mul_assoc]
      · simp [otherSeed]; ring
    rw [hms]
    simp only [map_mul, map_pow, seedView, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.eval₂_X, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', ↓reduceIte,
      otherSeed_ne i, RingHom.comp_apply]
    have hmon3 : MvPolynomial.monomial (Finsupp.single (0 : Fin 3) e₀ + Finsupp.single 1 e₁)
        (((P.coeff e₁).coeff e₀).coeff m) =
        MvPolynomial.C (((P.coeff e₁).coeff e₀).coeff m) *
          (MvPolynomial.X (0 : Fin 3) : FXJet2) ^ e₀ * (MvPolynomial.X (1 : Fin 3) : FXJet2) ^ e₁ := by
      simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial]
    rw [hmon3]
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow]
    ring
  have hsum_prop : ∀ {α : Type} (S : Finset α) (f : α → Polynomial (Polynomial FXJet2)),
      (∀ x ∈ S, (f x).natDegree ≤ U ∧ (∀ a, ((f x).coeff a).natDegree ≤ U) ∧
        (∀ a b, (((f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_tot ≤ B) ∧
        (∀ a b, (((f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_idx ≤ J) ∧
        (∀ a b, (((f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_top = 0)) →
      (∑ x ∈ S, f x).natDegree ≤ U ∧ (∀ a, ((∑ x ∈ S, f x).coeff a).natDegree ≤ U) ∧
        (∀ a b, (((∑ x ∈ S, f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_tot ≤ B) ∧
        (∀ a b, (((∑ x ∈ S, f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_idx ≤ J) ∧
        (∀ a b, (((∑ x ∈ S, f x).coeff a).coeff b).weightedTotalDegree fxJet2Weight_top = 0) := by
    intro α S f hf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Polynomial.natDegree_sum_le_of_forall_le S f fun x hx => (hf x hx).1
    · intro a; rw [Polynomial.finsetSum_coeff]
      exact Polynomial.natDegree_sum_le_of_forall_le S _ fun x hx => (hf x hx).2.1 a
    · intro a b; rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
      exact AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun x hx => (hf x hx).2.2.1 a b)
    · intro a b; rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
      exact AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun x hx => (hf x hx).2.2.2.1 a b)
    · intro a b; rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
      exact Nat.eq_zero_of_le_zero (AddMonoidAlgebra.supDegree_sum_le.trans
        (Finset.sup_le fun x hx => (hf x hx).2.2.2.2 a b |>.le))
  rw [hPv_sum]
  apply hsum_prop; intro e₁ _
  apply hsum_prop; intro e₀ he₀
  apply hsum_prop; intro m hm
  have hne : (P.coeff e₁).coeff e₀ ≠ 0 := Polynomial.mem_support_iff.mp he₀
  have ⟨hB, hJ, hU⟩ := hP e₁ e₀ hne
  have hmU : m 0 + m 1 ≤ U := by
    have hle := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hle
    exact hle.trans hU
  exact hmon e₁ e₀ m (((P.coeff e₁).coeff e₀).coeff m) hB hJ hmU

private theorem wtd_zero (w : Fin 3 → ℕ) : (0 : FXJet2).weightedTotalDegree w = 0 := by
  simp [MvPolynomial.weightedTotalDegree]

private theorem wtd_monomial_le (w : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) (c : FX) :
    (MvPolynomial.monomial d c).weightedTotalDegree w ≤ Finsupp.weight w d := by
  change (MvPolynomial.monomial d c).support.sup (Finsupp.weight w) ≤ Finsupp.weight w d
  refine Finset.sup_le fun m hm => ?_
  have h : m = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (by simp [MvPolynomial.coeff_monomial, Ne.symm hne])
  subst h; exact le_rfl

private theorem wtd_add_le (w : Fin 3 → ℕ) (p q : FXJet2) :
    (p + q).weightedTotalDegree w ≤ max (p.weightedTotalDegree w) (q.weightedTotalDegree w) :=
  AddMonoidAlgebra.supDegree_add_le

private theorem wtd_sum_le {ι : Type} (w : Fin 3 → ℕ) (S : Finset ι) (f : ι → FXJet2) :
    (∑ x ∈ S, f x).weightedTotalDegree w ≤ S.sup fun x => (f x).weightedTotalDegree w :=
  AddMonoidAlgebra.supDegree_sum_le

private theorem wtd_mul_le (w : Fin 3 → ℕ) (p q : FXJet2) :
    (p * q).weightedTotalDegree w ≤ p.weightedTotalDegree w + q.weightedTotalDegree w := by
  by_cases hp : p = 0
  · subst hp; rw [zero_mul, wtd_zero]; omega
  · by_cases hq : q = 0
    · subst hq; rw [mul_zero, wtd_zero]; omega
    · exact (MvPolynomial.weightedTotalDegree_mul w p q hp hq).le

private theorem wtd_neg (w : Fin 3 → ℕ) (p : FXJet2) :
    (-p).weightedTotalDegree w = p.weightedTotalDegree w := by
  simp [MvPolynomial.weightedTotalDegree, MvPolynomial.support_neg]

private theorem seedView_prolong_bounds (i : Fin 2) {G : Jet} {j u : ℕ}
    (hj : 1 ≤ j) (hG : RowCaps G ⟨0, j, 1, u⟩) :
    let G1v := seedView i (prolongPoly G)
    G1v.natDegree ≤ u ∧
    (∀ a, (G1v.coeff a).natDegree ≤ u) ∧
    (∀ a b, ((G1v.coeff a).coeff b).weightedTotalDegree fxJet2Weight_tot ≤ j) ∧
    (∀ a b, ((G1v.coeff a).coeff b).weightedTotalDegree fxJet2Weight_idx ≤ 2) ∧
    (∀ a b, ((G1v.coeff a).coeff b).weightedTotalDegree fxJet2Weight_top ≤ 1) := by
  intro G1v
  have hA := seedView_bounds_of_rowCaps i (prolongA_rowCaps hj hG)
  have hB1 := seedView_bounds_of_rowCaps i (prolongB1_rowCaps hG)
  have heq : G1v = seedView i (Polynomial.C (prolongA G)) *
      Polynomial.C (Polynomial.C (MvPolynomial.X 2)) + seedView i (Polynomial.C (prolongB1 G)) := by
    simp [G1v, prolongPoly, seedView]
  rw [heq]
  have hX2_eq : (MvPolynomial.X (2 : Fin 3) : FXJet2) = MvPolynomial.monomial (Finsupp.single 2 1) 1 := rfl
  have hX2_tot : (MvPolynomial.X (2 : Fin 3) : FXJet2).weightedTotalDegree fxJet2Weight_tot ≤ 1 := by
    rw [hX2_eq]; exact (wtd_monomial_le _ _ _).trans (by simp [Finsupp.weight_apply, fxJet2Weight_tot])
  have hX2_idx : (MvPolynomial.X (2 : Fin 3) : FXJet2).weightedTotalDegree fxJet2Weight_idx ≤ 2 := by
    rw [hX2_eq]; exact (wtd_monomial_le _ _ _).trans (by simp [Finsupp.weight_apply, fxJet2Weight_idx])
  have hX2_top : (MvPolynomial.X (2 : Fin 3) : FXJet2).weightedTotalDegree fxJet2Weight_top ≤ 1 := by
    rw [hX2_eq]; exact (wtd_monomial_le _ _ _).trans (by simp [Finsupp.weight_apply, fxJet2Weight_top])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_mul_C_le _ _).trans hA.1) hB1.1)
  · intro a
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_mul_C_le _ _).trans (hA.2.1 a)) (hB1.2.1 a))
  · intro a b
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_mul_C]
    refine (wtd_add_le _ _ _).trans (max_le ?_ (hB1.2.2.1 a b))
    refine (wtd_mul_le _ _ _).trans ?_
    have := hA.2.2.1 a b; omega
  · intro a b
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_mul_C]
    refine (wtd_add_le _ _ _).trans (max_le ?_ (hB1.2.2.2.1 a b))
    refine (wtd_mul_le _ _ _).trans ?_
    have := hA.2.2.2.1 a b; omega
  · intro a b
    rw [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_mul_C]
    refine (wtd_add_le _ _ _).trans (max_le ?_ (by rw [hB1.2.2.2.2 a b]; omega))
    refine (wtd_mul_le _ _ _).trans ?_
    rw [hA.2.2.2.2 a b, zero_add]; exact hX2_top

private theorem sylvester_poly_weighted_le (w : Fin 3 → ℕ)
    (P Q : Polynomial (Polynomial FXJet2)) (m n B D : ℕ)
    (hP : ∀ a ≤ m, ∀ b, ((P.coeff a).coeff b).weightedTotalDegree w ≤ B)
    (hQ : ∀ a ≤ n, ∀ b, ((Q.coeff a).coeff b).weightedTotalDegree w ≤ D) (k : ℕ) :
    ((P.resultant Q m n).coeff k).weightedTotalDegree w ≤ n * B + m * D := by
  classical
  have hmul_le : ∀ {d₁ d₂ : ℕ} {f g : Polynomial FXJet2},
      (∀ b, (f.coeff b).weightedTotalDegree w ≤ d₁) →
      (∀ b, (g.coeff b).weightedTotalDegree w ≤ d₂) →
      ∀ b, ((f * g).coeff b).weightedTotalDegree w ≤ d₁ + d₂ := by
    intro d₁ d₂ f g hf hg b
    rw [Polynomial.coeff_mul]
    refine (wtd_sum_le w _ _).trans (Finset.sup_le fun xy _ => ?_)
    exact (wtd_mul_le w _ _).trans (Nat.add_le_add (hf xy.1) (hg xy.2))
  have hprod_le : ∀ {ι : Type} (S : Finset ι) (f : ι → Polynomial FXJet2) (d : ι → ℕ),
      (∀ x ∈ S, ∀ b, ((f x).coeff b).weightedTotalDegree w ≤ d x) →
      ∀ b, ((∏ x ∈ S, f x).coeff b).weightedTotalDegree w ≤ ∑ x ∈ S, d x := by
    intro ι S f d hf
    induction S using Finset.induction with
    | empty =>
      intro b; simp only [Finset.prod_empty, Finset.sum_empty, Polynomial.coeff_one]
      split_ifs
      · rw [← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
      · exact (wtd_zero w).le
    | insert a S ha ih =>
      intro b
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact hmul_le (hf a (Finset.mem_insert_self a S))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)) b
  let M := Polynomial.sylvester P Q m n
  let W : Fin (m + n) → ℕ := Fin.addCases (fun _ : Fin m => D) (fun _ : Fin n => B)
  have hW : ∑ x, W x = n * B + m * D := by
    simp only [W, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  change (M.det.coeff k).weightedTotalDegree w ≤ n * B + m * D
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine (wtd_sum_le w _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hprod : ((∏ x, M (σ x) x).coeff k).weightedTotalDegree w ≤ n * B + m * D := by
    rw [← hW]
    apply hprod_le Finset.univ (fun x => M (σ x) x) W
    intro x _ b
    cases x using Fin.addCases with
    | left j' =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, W]
      split_ifs with h
      · exact hQ _ (by have := h.2; omega) b
      · simp [wtd_zero]
    | right j' =>
      simp only [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, W]
      split_ifs with h
      · exact hP _ (by have := h.2; omega) b
      · simp [wtd_zero]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul, Polynomial.coeff_neg, wtd_neg]
    exact hprod

/-! ## 5. The 15-Line Derivative Descent (`δ = d_{1-i}(α₁) d_i - d_i(α₁) d_{1-i}`) -/

private def fxToE' : FX →+* EField := seedsToE.comp MvPolynomial.C

private theorem fxToE'_algebraMap (p : Polynomial L) :
    fxToE' (algebraMap (Polynomial L) FX p) =
      algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p)) := by
  let ev : Polynomial K1_14_1.SeedPoly →ₐ[L] Seeds :=
    Polynomial.eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
      (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
      (fun _ => Commute.all _ _)
  have hev : ev (K1_14_1_3.sourceX p) = MvPolynomial.C (algebraMap (Polynomial L) FX p) := by
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ =>
      simp only [K1_14_1_3.sourceX, Polynomial.map_add, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [K1_14_1_3.sourceX, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X, map_mul, map_pow]
      have hC : ev (Polynomial.C (MvPolynomial.C a)) =
          MvPolynomial.C (algebraMap (Polynomial L) FX (Polynomial.C a)) := by
        simp only [ev, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C]
        exact MvPolynomial.map_C _ _
      have hX : ev Polynomial.X = MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X) := by
        simp [ev, Polynomial.eval₂AlgHom_apply]
      rw [hC, hX]
  let Q : PoleBound2Jet.Source2 := Polynomial.C (Polynomial.C (Polynomial.C (K1_14_1_3.sourceX p)))
  have h := congrArg (fun R : Polynomial (Polynomial EField) => (R.coeff 0).coeff 0)
    (TwoJetCaseAFX.jet2ToE_centerEval2 Q)
  have hrhs : (((TwoJetCaseAKernel.embed2 (algebraMap BaseRing EField) Q).coeff 0).coeff 0) =
      algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p)) := by
    simp [Q, TwoJetCaseAKernel.embed2]
  have hlhs : (((TwoJetCaseAFX.jet2ToE (TwoJetRescueBridge.centerEval2 Q)).coeff 0).coeff 0) =
      fxToE' (algebraMap (Polynomial L) FX p) := by
    have hce : TwoJetRescueBridge.centerEval2 Q =
        Polynomial.C (Polynomial.C (Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX p)))) := by
      change Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom ev.toRingHom))
        (Polynomial.C (Polynomial.C (Polynomial.C (K1_14_1_3.sourceX p)))) = _
      simp only [Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact congrArg (Polynomial.C ∘ Polynomial.C ∘ Polynomial.C) hev
    rw [hce]
    simp [TwoJetCaseAFX.jet2ToE, seedsY0ToE, fxToE']
  exact hlhs.symm.trans (h.trans hrhs)

private theorem seedCoeff_one_X (j k : Fin 2) :
    K1_14_1_3.seedCoeff j 1 (MvPolynomial.X k : K1_14_1.SeedPoly) = if j = k then 1 else 0 := by
  change (K1_14_1_3.translation j (MvPolynomial.X k : K1_14_1.SeedPoly)).coeff 1 = _
  by_cases h : j = k
  · subst h; simp [K1_14_1_3.translation]
  · have h' : k ≠ j := Ne.symm h; simp [K1_14_1_3.translation, h, h']

private theorem baseDeriv_Y0 (j : Fin 2) : TwoJetCaseADriver.baseDeriv j Polynomial.X = 0 := by
  apply Polynomial.ext; intro b; apply Polynomial.ext; intro a
  rw [TwoJetCaseADriver.baseDeriv_coeff, Polynomial.coeff_X, Polynomial.coeff_zero, Polynomial.coeff_zero]
  split_ifs
  · simp only [Polynomial.coeff_one]; split_ifs
    · simpa using TwoJetCaseADriver.seedCoeff_one_C j (1 : L)
    · simp
  · simp

private theorem baseDeriv_seedX (j k : Fin 2) :
    TwoJetCaseADriver.baseDeriv j (Polynomial.C (Polynomial.C (MvPolynomial.X k))) =
      if j = k then 1 else 0 := by
  apply Polynomial.ext; intro b; apply Polynomial.ext; intro a
  rw [TwoJetCaseADriver.baseDeriv_coeff]
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 0
    · subst ha
      simp only [Polynomial.coeff_C_zero, seedCoeff_one_X]
      split_ifs <;> simp
    · simp only [Polynomial.coeff_C_zero, Polynomial.coeff_C, ha, ↓reduceIte, map_zero]
      split_ifs <;> simp [Polynomial.coeff_one, ha]
  · simp only [Polynomial.coeff_C, hb, ↓reduceIte, Polynomial.coeff_zero, map_zero]
    split_ifs <;> simp [Polynomial.coeff_one, hb]

private theorem deriv_seed_nonzero {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    {u : ℕ} (hu : u ≤ 22) (hU : ∀ j k, ((G.coeff j).coeff k).totalDegree ≤ u)
    {i : Fin 2} (hpos : ∃ j k, 0 < ((G.coeff j).coeff k).degreeOf i) :
    (if i = 0 then fractionRingFieldDerivs.d₀ else fractionRingFieldDerivs.d₁) (alpha1 G) ≠ 0 := by
  let D := fractionRingFieldDerivs
  let di : EField → EField := if i = 0 then D.d₀ else D.d₁
  have hdi_add : ∀ x y, di (x + y) = di x + di y := by
    fin_cases i <;> [exact D.d₀_add; exact D.d₁_add]
  have hdi_mul : ∀ x y, di (x * y) = di x * y + x * di y := by
    fin_cases i <;> [exact D.d₀_mul; exact D.d₁_mul]
  have hdi_sub : ∀ x y, di (x - y) = di x - di y := by
    intro x y
    have h := hdi_add (x - y) y
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hdi_neg : ∀ x, di (-x) = -di x := by
    fin_cases i <;> [exact D.d₀_neg; exact D.d₁_neg]
  have hdi_zero : di 0 = 0 := by
    fin_cases i <;> [exact D.d₀_zero; exact D.d₁_zero]
  -- Define `eqDeriv : Equation → Equation` = `mapDeriv (MvPolynomial.pderiv i)`!
  let eqDeriv : Equation → Equation := mapDeriv (fun p : Seeds => MvPolynomial.pderiv i p)
  have heq_comm : ∀ q : Equation, di (seedsY0ToE q) = seedsY0ToE (eqDeriv q) := by
    have hfx0 : ∀ c : FX, di (TwoJetCaseAFX.seedsToE (MvPolynomial.C c)) = 0 := by
      intro c
      have hsub : ∀ p : Polynomial L, di (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
        intro p
        have h0 : D.d₀ (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
          rw [fractionRingFieldDerivs_compat.compat0, TwoJetCaseADriver.baseDeriv_sourceX, map_zero]
        have h1 : D.d₁ (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
          rw [fractionRingFieldDerivs_compat.compat1, TwoJetCaseADriver.baseDeriv_sourceX, map_zero]
        fin_cases i
        · simpa [di] using h0
        · simpa [di] using h1
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial L)) c
      have hce : TwoJetCaseAFX.seedsToE (MvPolynomial.C c) *
          algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX d.1)) =
          algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX n)) := by
        have h2 := congrArg fxToE' hnd
        rw [map_mul, fxToE'_algebraMap, fxToE'_algebraMap] at h2
        exact h2
      have hd_ne : algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX d.1)) ≠ 0 := by
        intro hz
        have h0 := IsFractionRing.injective BaseRing EField (hz.trans (map_zero _).symm)
        have h1 := Polynomial.C_eq_zero.mp h0
        have hd0 : d.1 = 0 := by
          ext a
          have := congrArg (fun r : Polynomial K1_14_1.SeedPoly => (r.coeff a).coeff 0) h1
          simpa [K1_14_1_3.sourceX, Polynomial.coeff_map, MvPolynomial.coeff_C] using this
        exact nonZeroDivisors.ne_zero d.2 hd0
      have hder := congrArg di hce
      rw [hdi_mul, hsub d.1, hsub n, mul_zero, add_zero] at hder
      exact (mul_eq_zero.mp hder).resolve_right hd_ne
    have hseed_comm : ∀ s : Seeds, di (seedsToE s) = seedsToE (MvPolynomial.pderiv i s) := by
      intro s
      induction s using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.pderiv_C, map_zero]; exact hfx0 c
      | add s₁ s₂ ih₁ ih₂ => rw [map_add, hdi_add, map_add, map_add, ih₁, ih₂]
      | mul_X s k ih =>
        rw [map_mul, hdi_mul, ih, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul, map_mul]
        congr 1
        have hXk : di (seedsToE (MvPolynomial.X k)) = seedsToE ((Pi.single i (1 : Seeds) : Fin 2 → Seeds) k) := by
          simp only [seedsToE, MvPolynomial.eval₂Hom_X']
          fin_cases i <;> fin_cases k
          · change D.d₀ (algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X 0)))) = _
            rw [fractionRingFieldDerivs_compat.compat0, baseDeriv_seedX]; simp
          · change D.d₀ (algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X 1)))) = _
            rw [fractionRingFieldDerivs_compat.compat0, baseDeriv_seedX]; simp
          · change D.d₁ (algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X 0)))) = _
            rw [fractionRingFieldDerivs_compat.compat1, baseDeriv_seedX]; simp
          · change D.d₁ (algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X 1)))) = _
            rw [fractionRingFieldDerivs_compat.compat1, baseDeriv_seedX]; simp
        rw [hXk]
    have hY0 : di (algebraMap BaseRing EField Polynomial.X) = 0 := by
      have h0 : D.d₀ (algebraMap BaseRing EField Polynomial.X) = 0 := by
        rw [fractionRingFieldDerivs_compat.compat0, baseDeriv_Y0, map_zero]
      have h1 : D.d₁ (algebraMap BaseRing EField Polynomial.X) = 0 := by
        rw [fractionRingFieldDerivs_compat.compat1, baseDeriv_Y0, map_zero]
      fin_cases i
      · simp [di, h0]
      · simp [di, h1]
    intro q
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ ih₁ ih₂ =>
      dsimp only [eqDeriv]
      rw [map_add, hdi_add, mapDeriv_add (map_zero _) (fun x y => map_add _ x y), map_add, ih₁, ih₂]
    | monomial n s =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hdi_mul]
      have hpow0 : ∀ m : ℕ, di (seedsY0ToE Polynomial.X ^ m) = 0 := by
        intro m; induction m with
        | zero =>
          rw [pow_zero]
          fin_cases i <;> [exact TwoJetCaseADriver.fieldDerivs_d₀_one D; exact TwoJetCaseADriver.fieldDerivs_d₁_one D]
        | succ m ihm =>
          rw [pow_succ, hdi_mul, ihm, zero_mul, zero_add]
          have : seedsY0ToE Polynomial.X = algebraMap BaseRing EField Polynomial.X := by simp [seedsY0ToE]
          rw [this, hY0, mul_zero]
      rw [hpow0 n, mul_zero, add_zero]
      have hmd : eqDeriv (Polynomial.C s * Polynomial.X ^ n) =
          Polynomial.C (MvPolynomial.pderiv i s) * Polynomial.X ^ n := by
        ext k; rw [mapDeriv_coeff (map_zero _), Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
        split_ifs <;> simp
      rw [hmd, map_mul, map_pow]
      simp only [seedsY0ToE, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hseed_comm]
  -- Now assume `di (alpha1 G) = 0` and derive a contradiction!
  intro h0
  change di (alpha1 G) = 0 at h0
  let A := G.coeff 1
  let B := G.coeff 0
  have hAne : A ≠ 0 := by
    rw [show A = G.coeff G.natDegree by rw [hdegG], Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
  have hAe_ne : seedsY0ToE A ≠ 0 := fun hz => hAne (seedsY0ToE_injective (hz.trans (map_zero _).symm))
  have hrel : seedsY0ToE A * alpha1 G + seedsY0ToE B = 0 := by
    dsimp only [alpha1, A, B]; rw [mul_div_cancel₀ _ hAe_ne, neg_add_cancel]
  have hdrel := congrArg di hrel
  rw [hdi_add, hdi_mul, h0, mul_zero, add_zero, hdi_zero, heq_comm A, heq_comm B] at hdrel
  -- Multiply by `seedsY0ToE A` to clear `alpha1 G = -B / A`:
  have hcross : seedsY0ToE (eqDeriv B * A - B * eqDeriv A) = 0 := by
    have hmul := congrArg (· * seedsY0ToE A) hdrel
    simp only [add_mul, zero_mul] at hmul
    have hα : alpha1 G * seedsY0ToE A = -seedsY0ToE B := by
      dsimp only [alpha1, A, B]; rw [div_mul_cancel₀ _ hAe_ne]
    rw [mul_assoc, hα] at hmul
    rw [map_sub, map_mul, map_mul]
    linear_combination hmul
  have hEq : eqDeriv B * A = B * eqDeriv A := sub_eq_zero.mp (seedsY0ToE_injective (hcross.trans (map_zero _).symm))
  -- Since `G = C A * X + C B` is irreducible, `IsRelPrime A B` in the UFD `Equation`!
  have hcop : IsRelPrime A B := by
    intro d hdA hdB
    have hdG : Polynomial.C d ∣ G := by
      have hlin : G = Polynomial.C B + Polynomial.C A * Polynomial.X := by
        ext n; cases n with
        | zero => simp [B]
        | succ n => cases n with
          | zero => simp [A]
          | succ n =>
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
            simp
      rw [hlin]
      exact dvd_add (_root_.map_dvd Polynomial.C hdB) (dvd_mul_of_dvd_left (_root_.map_dvd Polynomial.C hdA) _)
    obtain ⟨Q, hQ⟩ := hdG
    rcases hIrr.isUnit_or_isUnit hQ with hu | hu
    · exact Polynomial.isUnit_C.mp hu
    · exfalso
      have hQdeg : Q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hGdeg : G.natDegree = 0 := by
        rw [hQ]
        exact Nat.eq_zero_of_le_zero ((Polynomial.natDegree_C_mul_le d Q).trans_eq hQdeg)
      omega
  have hAdvd : A ∣ eqDeriv A := hcop.dvd_of_dvd_mul_left ⟨eqDeriv B, by linear_combination -hEq⟩
  have hBdvd : B ∣ eqDeriv B := hcop.symm.dvd_of_dvd_mul_left ⟨eqDeriv A, by linear_combination hEq⟩
  -- For any `f : Equation` with all coeffs having `totalDegree ≤ u ≤ 22 < p`, `f ∣ eqDeriv f → ∀ k, (f.coeff k).degreeOf i = 0`!
  have hdeg_zero : ∀ f : Equation, (∀ k, (f.coeff k).totalDegree ≤ u) → f ∣ eqDeriv f →
      ∀ k, (f.coeff k).degreeOf i = 0 := by
    intro f hf hdvd k
    -- Map `Equation` into `Polynomial (Polynomial (Polynomial FX))` with outer variable `z_i`!
    let viewEq : Equation →+* Polynomial (Polynomial (Polynomial FX)) :=
      Polynomial.eval₂RingHom
        (MvPolynomial.eval₂Hom (Polynomial.C.comp (Polynomial.C.comp Polynomial.C))
          (fun j => if j = i then Polynomial.X else Polynomial.C (Polynomial.C Polynomial.X)))
        (Polynomial.C Polynomial.X)
    have hview_deriv : ∀ q : Equation, viewEq (eqDeriv q) = (viewEq q).derivative := by
      intro q
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ ih₁ ih₂ =>
        dsimp only [eqDeriv]
        rw [mapDeriv_add (map_zero _) (fun x y => map_add _ x y), map_add, map_add,
          Polynomial.derivative_add, ih₁, ih₂]
      | monomial n s =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        have hmd : eqDeriv (Polynomial.C s * Polynomial.X ^ n) =
            Polynomial.C (MvPolynomial.pderiv i s) * Polynomial.X ^ n := by
          ext m; rw [mapDeriv_coeff (map_zero _), Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
          split_ifs <;> simp
        rw [hmd, map_mul, map_pow, map_mul, map_pow, Polynomial.derivative_mul]
        have hXn : (viewEq Polynomial.X ^ n).derivative = 0 := by
          rw [show viewEq Polynomial.X = Polynomial.C Polynomial.X by simp [viewEq],
            ← Polynomial.C_pow, Polynomial.derivative_C]
        rw [hXn, mul_zero, add_zero]
        refine congrArg (· * viewEq Polynomial.X ^ n) ?_
        clear hmd hXn
        simp only [viewEq, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        induction s using MvPolynomial.induction_on with
        | C c => simp
        | add s₁ s₂ ih₁ ih₂ => rw [map_add, map_add, map_add, Polynomial.derivative_add, ih₁, ih₂]
        | mul_X s j ih =>
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul, map_mul,
            map_mul, Polynomial.derivative_mul, ih]
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
    have hdv := _root_.map_dvd viewEq hdvd
    rw [hview_deriv] at hdv
    have hvf_deg : (viewEq f).natDegree ≤ u := by
      rw [f.as_sum_support_C_mul_X_pow, map_sum]
      apply Polynomial.natDegree_sum_le_of_forall_le; intro n _
      rw [map_mul, map_pow]
      have hXn : (viewEq Polynomial.X ^ n).natDegree = 0 := by
        rw [show viewEq Polynomial.X = Polynomial.C Polynomial.X by simp [viewEq],
          ← Polynomial.C_pow, Polynomial.natDegree_C]
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [hXn, add_zero]
      let φs : Seeds →+* Polynomial (Polynomial (Polynomial FX)) :=
        MvPolynomial.eval₂Hom (Polynomial.C.comp (Polynomial.C.comp Polynomial.C))
          (fun j => if j = i then Polynomial.X else Polynomial.C (Polynomial.C Polynomial.X))
      simp only [viewEq, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change (φs (f.coeff n)).natDegree ≤ u
      rw [(f.coeff n).as_sum, map_sum]
      apply Polynomial.natDegree_sum_le_of_forall_le; intro m hm
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two,
        map_mul, map_mul, map_pow, map_pow]
      have hmU : m 0 + m 1 ≤ u := by
        have hle := MvPolynomial.le_totalDegree hm
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hle
        exact hle.trans (hf n)
      have hC0 : (φs (MvPolynomial.C ((f.coeff n).coeff m))).natDegree = 0 := by
        simp [φs]
      have hX_deg : ∀ j : Fin 2, (φs (MvPolynomial.X j) ^ m j).natDegree ≤ m j := by
        intro j
        by_cases hj : j = i
        · simp [φs, hj]
        · rw [show φs (MvPolynomial.X j) = Polynomial.C (Polynomial.C Polynomial.X) by simp [φs, hj],
            ← Polynomial.C_pow, Polynomial.natDegree_C]
          exact Nat.zero_le _
      have h1 : (φs (MvPolynomial.X 0) ^ m 0 * φs (MvPolynomial.X 1) ^ m 1).natDegree ≤ m 0 + m 1 :=
        (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hX_deg 0) (hX_deg 1))
      exact (Polynomial.natDegree_mul_le).trans (by rw [hC0, zero_add]; exact h1.trans hmU)
    have hder0 : (viewEq f).derivative = 0 := by
      by_contra hne
      have hfne : viewEq f ≠ 0 := fun hz => hne (by rw [hz, Polynomial.derivative_zero])
      have hle := Polynomial.natDegree_le_of_dvd hdv hne
      have hlt : (viewEq f).derivative.natDegree < (viewEq f).natDegree :=
        Polynomial.natDegree_derivative_lt (fun h0 => hne (by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]))
      omega
    -- Since `(viewEq f).natDegree ≤ u ≤ 22 < p`, `derivative = 0` forces `(viewEq f).natDegree = 0`!
    have hdeg0 : (viewEq f).natDegree = 0 := by
      by_contra hpos'
      have hne : (viewEq f).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (fun hz => hpos' (by simp [hz]))
      have hc := congrArg (fun P => P.coeff ((viewEq f).natDegree - 1)) hder0
      rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_add_one,
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hpos'), Polynomial.coeff_natDegree] at hc
      have hcast : (((viewEq f).natDegree : ℕ) : Polynomial (Polynomial FX)) ≠ 0 := by
        intro hz
        have hfx0 : (((viewEq f).natDegree : ℕ) : FX) = 0 := by
          have := congrArg (fun q : Polynomial (Polynomial FX) => (q.coeff 0).coeff 0) hz
          simpa using this
        have hL0 : (((viewEq f).natDegree : ℕ) : L) = 0 := by
          have h1 : (((viewEq f).natDegree : ℕ) : FX) =
              algebraMap (Polynomial L) FX (Polynomial.C ((viewEq f).natDegree : L)) := by simp
          rw [h1] at hfx0
          exact Polynomial.C_eq_zero.mp (IsFractionRing.injective (Polynomial L) FX (hfx0.trans (map_zero _).symm))
        have hdvd_p : p ∣ (viewEq f).natDegree := (CharP.cast_eq_zero_iff L p _).mp hL0
        have hle_p := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos') hdvd_p
        change 2130706433 ≤ _ at hle_p; omega
      exact hne ((mul_eq_zero.mp hc).resolve_right hcast)
    -- Therefore `eqDeriv f = 0`, which means `MvPolynomial.pderiv i (f.coeff k) = 0`, hence `(f.coeff k).degreeOf i = 0`!
    have heq0 : eqDeriv f = 0 := by
      have hv0 : viewEq (eqDeriv f) = 0 := by rw [hview_deriv, hder0]
      -- `viewEq` is injective!
      have hvinj : Function.Injective viewEq := by
        let unviewEq : Polynomial (Polynomial (Polynomial FX)) →+* Equation :=
          Polynomial.eval₂RingHom
            (Polynomial.eval₂RingHom
              (Polynomial.eval₂RingHom (Polynomial.C.comp MvPolynomial.C)
                (Polynomial.C (MvPolynomial.X (otherSeed i))))
              Polynomial.X)
            (Polynomial.C (MvPolynomial.X i))
        have hleft : unviewEq.comp viewEq = RingHom.id Equation := by
          apply Polynomial.ringHom_ext'
          · apply MvPolynomial.ringHom_ext
            · intro a; simp [viewEq, unviewEq]
            · intro j
              by_cases hj : j = i
              · subst hj; simp [viewEq, unviewEq]
              · have hjo : j = otherSeed i := by fin_cases i <;> fin_cases j <;> simp_all [otherSeed]
                subst hjo; simp [viewEq, unviewEq, otherSeed_ne i]
          · simp [viewEq, unviewEq]
        exact Function.LeftInverse.injective (g := unviewEq) (fun x => RingHom.congr_fun hleft x)
      exact hvinj (hv0.trans (map_zero _).symm)
    have hpd0 : MvPolynomial.pderiv i (f.coeff k) = 0 := by
      have := congrArg (fun q : Equation => q.coeff k) heq0
      simpa [eqDeriv, mapDeriv_coeff (map_zero _)] using this
    by_contra hdk
    let d := (f.coeff k).degreeOf i
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hdk
    have hd_le : d ≤ u := (MvPolynomial.degreeOf_le_totalDegree (f.coeff k) i).trans (hf k)
    -- Pick a monomial `m ∈ (f.coeff k).support` with `m i = d`!
    have hex_m : ∃ m ∈ (f.coeff k).support, m i = d := by
      have hne_f : f.coeff k ≠ 0 := fun hz => hdk (by simp [hz])
      have hne_sup : (f.coeff k).support.Nonempty := MvPolynomial.support_nonempty.mpr hne_f
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (f.coeff k).support (fun m => m i) hne_sup
      refine ⟨m, hm, le_antisymm (MvPolynomial.degreeOf_le_iff.mp le_rfl m hm) ?_⟩
      dsimp only [d]
      rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.sup_le fun m' hm' => hmax m' hm'
    obtain ⟨m, hm, hmi⟩ := hex_m
    let m' : Fin 2 →₀ ℕ := m - Finsupp.single i 1
    have hadd : m' + Finsupp.single i 1 = m := by
      ext j; by_cases hj : j = i
      · subst hj; simp [m', hmi]; omega
      · simp [m', hj]
    have hcoeff0 := congrArg (fun s : Seeds => s.coeff m') hpd0
    rw [MvPolynomial.coeff_pderiv, hadd, MvPolynomial.coeff_zero] at hcoeff0
    have hd_ne : ((m' i + 1 : ℕ) : FX) ≠ 0 := by
      intro hz
      have hL0 : ((m' i + 1 : ℕ) : L) = 0 := by
        have h1 : ((m' i + 1 : ℕ) : FX) = algebraMap (Polynomial L) FX (Polynomial.C ((m' i + 1 : ℕ) : L)) := by simp
        rw [h1] at hz
        exact Polynomial.C_eq_zero.mp (IsFractionRing.injective (Polynomial L) FX (hz.trans (map_zero _).symm))
      have hdvd_p : p ∣ (m' i + 1) := (CharP.cast_eq_zero_iff L p _).mp hL0
      have hle_p := Nat.le_of_dvd (Nat.succ_pos _) hdvd_p
      have hm' : m' i + 1 = d := by
        have := DFunLike.congr_fun hadd i; simp at this; omega
      change 2130706433 ≤ _ at hle_p; omega
    exact MvPolynomial.mem_support_iff.mp hm ((mul_eq_zero.mp hcoeff0).resolve_right (by simpa using hd_ne))
  obtain ⟨j, k, hjpos⟩ := hpos
  have hj1 : j = 0 ∨ j = 1 := by
    by_contra hgt
    have h0 : (G.coeff j) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < j)
    rw [h0, Polynomial.coeff_zero] at hjpos
    simp at hjpos
  rcases hj1 with rfl | rfl
  · have h := hdeg_zero B (fun k' => hU 0 k') hBdvd k; dsimp only [B] at h; omega
  · have h := hdeg_zero A (fun k' => hU 1 k') hAdvd k; dsimp only [A] at h; omega

/-- **15-Line Derivative Descent (`caseB_leadingCoeff_vanishes`)**:
    When `jacDet = 0`, the leading `z_{1-i}`-coefficient `c_d ∈ FXJet2` of `Res_{z_i}(G, G^(1))`
    is NONZERO, lies in box `((2j+1)u, 3u, u)`, and vanishes at `(Y₀, α₁, α₂)` in `EField`! -/
private theorem caseB_leadingCoeff_vanishes {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    {j u : ℕ} (hj : 1 ≤ j) (hu : u ≤ 22) (hG : RowCaps G ⟨0, j, 1, u⟩)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0)
    {i : Fin 2} (hpos : ∃ a b, 0 < ((G.coeff a).coeff b).degreeOf i) :
    ∃ Q : FXJet2, Q ≠ 0 ∧
      Q.weightedTotalDegree fxJet2Weight_tot ≤ (2 * j + 1) * u ∧
      Q.weightedTotalDegree fxJet2Weight_idx ≤ 3 * u ∧
      Q.weightedTotalDegree fxJet2Weight_top ≤ u ∧
      MvPolynomial.eval₂ fxToE'
        (fun k => match k with | ⟨0, _⟩ => algebraMap BaseRing EField Polynomial.X
                               | ⟨1, _⟩ => alpha1 G
                               | ⟨2, _⟩ => alpha2 G) Q = 0 := by
  let Gv := seedView i (Polynomial.C G)
  let G1v := seedView i (prolongPoly G)
  let R : Polynomial FXJet2 := Gv.resultant G1v Gv.natDegree G1v.natDegree
  have hRne : R ≠ 0 := resultant_seedView_ne_zero hIrr hdegG hpos
  have hGb := seedView_bounds_of_rowCaps i hG
  have hG1b := seedView_prolong_bounds i hj hG
  -- Bound `R.natDegree ≤ 2 * u^2`!
  have hRdeg : R.natDegree ≤ 2 * u * u := by
    have hbd := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Gv G1v Gv.natDegree G1v.natDegree
      u u (fun a => hGb.2.1 a) (fun a => hG1b.2.1 a)
    have h1 : G1v.natDegree * u + Gv.natDegree * u ≤ u * u + u * u :=
      Nat.add_le_add (Nat.mul_le_mul_right u hG1b.1) (Nat.mul_le_mul_right u hGb.1)
    exact hbd.trans (h1.trans_eq (by ring))
  -- Evaluation homomorphism `evJ : FXJet2 →+* EField` sending `FX ↦ FX, Y₀ ↦ Y₀, Y₁ ↦ α₁, Y₂ ↦ α₂`!
  let evJ : FXJet2 →+* EField :=
    MvPolynomial.eval₂Hom fxToE'
      (fun k => match k with | ⟨0, _⟩ => algebraMap BaseRing EField Polynomial.X
                             | ⟨1, _⟩ => alpha1 G
                             | ⟨2, _⟩ => alpha2 G)
  let zi : EField := algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X i)))
  let zo : EField := algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X (otherSeed i))))
  let evPoly : Polynomial FXJet2 →+* EField := Polynomial.eval₂RingHom evJ zo
  -- Check that `evPoly` sends `Gv` and `G1v` to polynomials in `EField[z_i]` with common root `zi`!
  have hcomm_eval : ∀ P : Polynomial Jet,
      (seedView i P).eval₂ evPoly zi = Polynomial.eval₂ (evJetAt G) (alpha2 G) P := by
    have hcomp : (Polynomial.eval₂RingHom evPoly zi).comp (seedView i) =
        Polynomial.eval₂RingHom (evJetAt G) (alpha2 G) := by
      apply Polynomial.ringHom_ext'
      · apply Polynomial.ringHom_ext'
        · apply Polynomial.ringHom_ext'
          · apply MvPolynomial.ringHom_ext
            · intro c; simp [seedView, evPoly, evJ, evJetAt, seedsY0ToE, fxToE']
            · intro k
              by_cases hk : k = i
              · subst hk; simp [seedView, evPoly, evJ, evJetAt, seedsY0ToE, seedsToE, zi]
              · have hko : k = otherSeed i := by fin_cases i <;> fin_cases k <;> simp_all [otherSeed]
                subst hko; simp [seedView, evPoly, evJ, evJetAt, seedsY0ToE, seedsToE, zo, otherSeed_ne i]
          · simp [seedView, evPoly, evJ, evJetAt, seedsY0ToE]
        · simp [seedView, evPoly, evJ, evJetAt]
      · simp [seedView, evPoly, evJ, evJetAt]
    exact fun P => RingHom.congr_fun hcomp P
  -- Verify `evJetAt G G = 0` and `evJetAt G (prolongA G) * alpha2 G + evJetAt G (prolongB1 G) = 0`!
  have hA1_ne : G.coeff 1 ≠ 0 := by
    rw [← hdegG, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
  have hAe_ne : seedsY0ToE (G.coeff 1) ≠ 0 := fun hz => hA1_ne (seedsY0ToE_injective (hz.trans (map_zero _).symm))
  have h2_ne : (2 : EField) ≠ 0 := by
    intro h2
    haveI : CharP EField p := charP_EField
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff EField p 2).mp (by simpa using h2)
    have hle := Nat.le_of_dvd (by decide) hdvd
    change 2130706433 ≤ 2 at hle; omega
  have hG0 : evJetAt G G = 0 := by
    have hlin : G = Polynomial.C (G.coeff 0) + Polynomial.C (G.coeff 1) * Polynomial.X := by
      ext n; cases n with
      | zero => simp
      | succ n => cases n with
        | zero => simp
        | succ n =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
          simp [Polynomial.coeff_C, Polynomial.coeff_X]
    conv_lhs => arg 2; rw [hlin]
    rw [map_add, map_mul]
    simp only [evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, alpha1]
    rw [mul_div_cancel₀ _ hAe_ne, add_neg_cancel]
  have hAne : evJetAt G (prolongA G) ≠ 0 := by
    simp only [prolongA, map_mul, map_ofNat, evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact mul_ne_zero h2_ne hAe_ne
  have hG10 : evJetAt G (prolongA G) * alpha2 G + evJetAt G (prolongB1 G) = 0 := by
    dsimp only [alpha2]; rw [mul_div_cancel₀ _ hAne, neg_add_cancel]
  -- Hence `evPoly R = 0` by `Sol1.C40Primitives.map_resultant_eq_zero_of_common_root`!
  have hR0 : evPoly R = 0 := by
    have hposV : Gv.natDegree ≠ 0 := (seedView_C_natDegree_pos hpos).ne'
    have hz1 : Gv.eval₂ evPoly zi = 0 := by
      rw [hcomm_eval (Polynomial.C G), Polynomial.eval₂_C, hG0]
    have hz2 : G1v.eval₂ evPoly zi = 0 := by
      rw [hcomm_eval (prolongPoly G), prolongPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X, hG10]
    exact Sol1.C40Primitives.map_resultant_eq_zero_of_common_root evPoly Gv G1v
      Gv.natDegree G1v.natDegree le_rfl le_rfl (Or.inl hposV) zi hz1 hz2
  -- Define `δ = d_{1-i}(α₁) * d_i - d_i(α₁) * d_{1-i}`!
  let D := fractionRingFieldDerivs
  let di : EField → EField := if i = 0 then D.d₀ else D.d₁
  let do_ : EField → EField := if i = 0 then D.d₁ else D.d₀
  let δ : EField → EField := fun x => do_ (alpha1 G) * di x - di (alpha1 G) * do_ x
  have hdi_add : ∀ x y, di (x + y) = di x + di y := by fin_cases i <;> [exact D.d₀_add; exact D.d₁_add]
  have hdo_add : ∀ x y, do_ (x + y) = do_ x + do_ y := by fin_cases i <;> [exact D.d₁_add; exact D.d₀_add]
  have hdi_mul : ∀ x y, di (x * y) = di x * y + x * di y := by fin_cases i <;> [exact D.d₀_mul; exact D.d₁_mul]
  have hdo_mul : ∀ x y, do_ (x * y) = do_ x * y + x * do_ y := by fin_cases i <;> [exact D.d₁_mul; exact D.d₀_mul]
  have hδ_add : ∀ x y, δ (x + y) = δ x + δ y := fun x y => by simp only [δ, hdi_add, hdo_add]; ring
  have hδ_mul : ∀ x y, δ (x * y) = δ x * y + x * δ y := fun x y => by simp only [δ, hdi_mul, hdo_mul]; ring
  have hδ_zero : δ 0 = 0 := by
    have h := hδ_add 0 0; rw [add_zero] at h
    exact add_left_cancel (a := δ 0) (by rw [add_zero]; exact h.symm)
  have hδ_one : δ 1 = 0 := by
    have h := hδ_mul 1 1; simp only [one_mul, mul_one] at h
    exact add_left_cancel (a := δ 1) (by rw [add_zero]; exact h.symm)
  -- `δ` vanishes on `evJ c` for EVERY `c : FXJet2`!
  have hδ_evJ : ∀ c : FXJet2, δ (evJ c) = 0 := by
    have hδ_α1 : δ (alpha1 G) = 0 := by dsimp only [δ]; ring
    have hδ_α2 : δ (alpha2 G) = 0 := by
      dsimp only [δ, di, do_, D]
      unfold jacDet at hdet
      fin_cases i
      · simp only [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, ↓reduceIte]; linear_combination -hdet
      · simp only [show (⟨1, by decide⟩ : Fin 2) ≠ 0 by decide, ↓reduceIte]; linear_combination hdet
    have hδ_Y0 : δ (algebraMap BaseRing EField Polynomial.X) = 0 := by
      have h0 : D.d₀ (algebraMap BaseRing EField Polynomial.X) = 0 := by
        rw [fractionRingFieldDerivs_compat.compat0, baseDeriv_Y0, map_zero]
      have h1 : D.d₁ (algebraMap BaseRing EField Polynomial.X) = 0 := by
        rw [fractionRingFieldDerivs_compat.compat1, baseDeriv_Y0, map_zero]
      fin_cases i <;> simp [δ, di, do_, h0, h1]
    have hδ_FX : ∀ a : FX, δ (fxToE' a) = 0 := by
      intro a
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial L)) a
      have hsub : ∀ p : Polynomial L, δ (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
        intro p
        have h0 : D.d₀ (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
          rw [fractionRingFieldDerivs_compat.compat0, TwoJetCaseADriver.baseDeriv_sourceX, map_zero]
        have h1 : D.d₁ (algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX p))) = 0 := by
          rw [fractionRingFieldDerivs_compat.compat1, TwoJetCaseADriver.baseDeriv_sourceX, map_zero]
        fin_cases i <;> simp [δ, di, do_, h0, h1]
      have hce : fxToE' a *
          algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX d.1)) =
          algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX n)) := by
        have h2 := congrArg fxToE' hnd
        rw [map_mul, fxToE'_algebraMap, fxToE'_algebraMap] at h2
        exact h2
      have hd_ne : algebraMap BaseRing EField (Polynomial.C (K1_14_1_3.sourceX d.1)) ≠ 0 := by
        intro hz
        have h0 := IsFractionRing.injective BaseRing EField (hz.trans (map_zero _).symm)
        have h1 := Polynomial.C_eq_zero.mp h0
        have hd0 : d.1 = 0 := by
          ext k; have := congrArg (fun r : Polynomial K1_14_1.SeedPoly => (r.coeff k).coeff 0) h1
          simpa [K1_14_1_3.sourceX, Polynomial.coeff_map, MvPolynomial.coeff_C] using this
        exact nonZeroDivisors.ne_zero d.2 hd0
      have hder := congrArg δ hce
      rw [hδ_mul, hsub d.1, hsub n, mul_zero, add_zero] at hder
      exact (mul_eq_zero.mp hder).resolve_right hd_ne
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => simpa [evJ] using hδ_FX a
    | add c₁ c₂ ih₁ ih₂ => rw [map_add, hδ_add, ih₁, ih₂, add_zero]
    | mul_X c k ih =>
      rw [map_mul, hδ_mul, ih, zero_mul, zero_add]
      fin_cases k
      · simp [evJ, hδ_Y0]
      · simp [evJ, hδ_α1]
      · simp [evJ, hδ_α2]
  -- And `δ(zo) = -di (alpha1 G) ≠ 0`!
  have hδ_zo : δ zo = -di (alpha1 G) := by
    have h0 : D.d₀ zo = algebraMap BaseRing EField (if (0 : Fin 2) = otherSeed i then 1 else 0) := by
      dsimp only [zo]; rw [fractionRingFieldDerivs_compat.compat0, baseDeriv_seedX]
    have h1 : D.d₁ zo = algebraMap BaseRing EField (if (1 : Fin 2) = otherSeed i then 1 else 0) := by
      dsimp only [zo]; rw [fractionRingFieldDerivs_compat.compat1, baseDeriv_seedX]
    fin_cases i <;> simp [δ, di, do_, otherSeed, h0, h1]
  have hU_all : ∀ a b, ((G.coeff a).coeff b).totalDegree ≤ u := by
    intro a b
    by_cases hz : (G.coeff a).coeff b = 0
    · simp [hz]
    · exact (hG a b hz).2.2
  have hδ_zo_ne : δ zo ≠ 0 := by
    rw [hδ_zo, neg_ne_zero]
    exact deriv_seed_nonzero hIrr hdegG hu hU_all hpos
  -- Chain rule: `δ (evPoly P) = evPoly P.derivative * δ zo`!
  have hchain : ∀ P : Polynomial FXJet2, δ (evPoly P) = evPoly P.derivative * δ zo := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P₁ P₂ ih₁ ih₂ =>
      rw [map_add, hδ_add, Polynomial.derivative_add, map_add, add_mul, ih₁, ih₂]
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hδ_mul]
      have hCc : δ (evPoly (Polynomial.C c)) = 0 := by
        simpa [evPoly] using hδ_evJ c
      rw [hCc, zero_mul, zero_add]
      have hdpow : ∀ m : ℕ, δ (zo ^ m) = (m : EField) * zo ^ (m - 1) * δ zo := by
        intro m; induction m with
        | zero => rw [pow_zero, hδ_one]; simp
        | succ m ihm =>
          rw [pow_succ, hδ_mul, ihm]
          cases m with
          | zero => simp
          | succ m =>
            have : m + 1 - 1 = m := by omega
            rw [this, pow_succ]; push_cast; ring
      have hX : evPoly Polynomial.X = zo := by simp [evPoly]
      rw [hX, hdpow n, Polynomial.derivative_C_mul_X_pow]
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel, map_mul, map_pow, map_natCast, evPoly,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
        ring
  -- Induction on `m`: `evPoly (Polynomial.derivative^[m] R) = 0` for all `m`!
  have hiter : ∀ m : ℕ, evPoly (Polynomial.derivative^[m] R) = 0 := by
    intro m; induction m with
    | zero => exact hR0
    | succ m ihm =>
      rw [Function.iterate_succ_apply']
      have h := congrArg δ ihm
      rw [hchain, hδ_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hδ_zo_ne
  -- At `m = R.natDegree`, `derivative^[d] R = C (d! • R.leadingCoeff)`!
  have htop := hiter R.natDegree
  have htop_eq : Polynomial.derivative^[R.natDegree] R =
      Polynomial.C (R.natDegree.factorial • R.leadingCoeff) := by
    apply Polynomial.ext; intro k
    rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk
      rw [zero_add, Nat.descFactorial_self, Polynomial.coeff_natDegree]
    · have hgt : R.natDegree < k + R.natDegree := by omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
  rw [htop_eq] at htop
  simp only [evPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, nsmul_eq_mul, map_mul,
    map_natCast] at htop
  have hfac_ne : ((R.natDegree.factorial : ℕ) : EField) ≠ 0 := by
    intro h0
    haveI : CharP EField p := charP_EField
    have hdvd : p ∣ R.natDegree.factorial := (CharP.cast_eq_zero_iff EField p _).mp h0
    have hle : p ≤ R.natDegree := (KoalaBear.is_prime.dvd_factorial).mp hdvd
    change 2130706433 ≤ R.natDegree at hle
    have h968 : R.natDegree ≤ 968 := hRdeg.trans (by nlinarith)
    omega
  have hlead0 : evJ R.leadingCoeff = 0 := (mul_eq_zero.mp htop).resolve_left hfac_ne
  -- Package `Q := R.leadingCoeff` with exact Sylvester weighted degree bounds!
  refine ⟨R.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hRne, ?_, ?_, ?_, hlead0⟩
  · have h := sylvester_poly_weighted_le fxJet2Weight_tot Gv G1v Gv.natDegree G1v.natDegree j j
      (fun a _ b => hGb.2.2.1 a b) (fun a _ b => hG1b.2.2.1 a b) R.natDegree
    have h1 : G1v.natDegree * j + Gv.natDegree * j ≤ (2 * j + 1) * u := by
      have ha := Nat.mul_le_mul_right j hG1b.1
      have hb := Nat.mul_le_mul_right j hGb.1
      have : u * j + u * j = 2 * j * u := by ring
      nlinarith
    exact h.trans h1
  · have h := sylvester_poly_weighted_le fxJet2Weight_idx Gv G1v Gv.natDegree G1v.natDegree 1 2
      (fun a _ b => hGb.2.2.2.1 a b) (fun a _ b => hG1b.2.2.2.1 a b) R.natDegree
    have h1 : G1v.natDegree * 1 + Gv.natDegree * 2 ≤ 3 * u := by
      have ha : G1v.natDegree ≤ u := hG1b.1
      have hb : Gv.natDegree ≤ u := hGb.1
      omega
    exact h.trans h1
  · have h := sylvester_poly_weighted_le fxJet2Weight_top Gv G1v Gv.natDegree G1v.natDegree 0 1
      (fun a _ b => (hGb.2.2.2.2 a b).le) (fun a _ b => hG1b.2.2.2.2 a b) R.natDegree
    have h1 : G1v.natDegree * 0 + Gv.natDegree * 1 ≤ u := by
      have hb : Gv.natDegree ≤ u := hGb.1
      omega
    exact h.trans h1

/-! ## 6. Denominator Clearing, `K`-Linear Descent, and `OrderTwoHigh` Witness -/

/-- Clears `L[X]`-denominators of `Q ∈ FXJet2` and projects `L →ₗ[K] K` to produce a nonzero
    `Q_K ∈ DifferentialPolynomial K 2` vanishing on every mark `(z, S)` with `jetAt G z S = 0`
    and `jetAt (prolongA G) z S ≠ 0`. -/
theorem caseB_diffPoly_witness {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    (hseed : UsesSeed G) {j u : ℕ} (hj : 1 ≤ j) (hu : u ≤ 22) (hG : RowCaps G ⟨0, j, 1, u⟩)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0)
    {box : BoxShape} (hB : (2 * j + 1) * u ≤ box.B) (hJ : 3 * u ≤ box.J) (hC : u ≤ box.C) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwoHigh box Q ∧
      ∀ (z : K) (S : Polynomial K),
        jetAt G z S = 0 → jetAt (prolongA G) z S ≠ 0 →
        differentialSpecialization Q S = 0 := by
  -- Step 1: Pick `i : Fin 2` with `deg_{z_i}(G) ≥ 1` from `UsesSeed G`!
  have hpos : ∃ i : Fin 2, ∃ a b, 0 < ((G.coeff a).coeff b).degreeOf i := by
    obtain ⟨a, b, htot⟩ := hseed
    have hne : (G.coeff a).coeff b ≠ 0 := fun hz => by simp [hz] at htot
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image ((G.coeff a).coeff b).support
      (fun m => m 0 + m 1) (MvPolynomial.support_nonempty.mpr hne)
    have hsum : 0 < m 0 + m 1 := by
      have hle : ((G.coeff a).coeff b).totalDegree ≤ m 0 + m 1 := by
        rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
        intro m' hm'
        rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
        exact hmax m' hm'
      omega
    have h01 : 0 < m 0 ∨ 0 < m 1 := by omega
    rcases h01 with h0 | h1
    · exact ⟨0, a, b, h0.trans_le (MvPolynomial.degreeOf_le_iff.mp le_rfl m hm)⟩
    · exact ⟨1, a, b, h1.trans_le (MvPolynomial.degreeOf_le_iff.mp le_rfl m hm)⟩
  obtain ⟨i, hpos_i⟩ := hpos
  obtain ⟨Qfx, hQfx_ne, hQtot, hQidx, hQtop, hQeval⟩ :=
    caseB_leadingCoeff_vanishes hIrr hdegG hj hu hG hdet hpos_i
  -- Step 2: Clear `L[X]`-denominators of `Qfx : MvPolynomial (Fin 3) FX` to `QL : MvPolynomial (Fin 3) (Polynomial L)`!
  have hclear : ∀ m, ∃ d : Polynomial L, d ≠ 0 ∧ ∃ n : Polynomial L,
      algebraMap (Polynomial L) FX d * Qfx.coeff m = algebraMap (Polynomial L) FX n := by
    intro m
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial L)) (Qfx.coeff m)
    exact ⟨d.1, nonZeroDivisors.ne_zero d.2, n, by simpa [mul_comm] using hnd⟩
  choose den hden_ne num hnum using fun m : Qfx.support => hclear m.1
  let D : Polynomial L := ∏ m : Qfx.support, den m
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hden_ne m
  have hD_fx : algebraMap (Polynomial L) FX D ≠ 0 := fun hz =>
    hD_ne (IsFractionRing.injective (Polynomial L) FX (hz.trans (map_zero _).symm))
  have hcoeff_clear : ∀ m, ∃ p : Polynomial L,
      algebraMap (Polynomial L) FX D * Qfx.coeff m = algebraMap (Polynomial L) FX p := by
    intro m
    by_cases hm : m ∈ Qfx.support
    · let mc : Qfx.support := ⟨m, hm⟩
      let D' := ∏ m' ∈ Finset.univ.erase mc, den m'
      have hD_sp : D = D' * den mc := Finset.prod_erase_mul _ _ (Finset.mem_univ mc) |>.symm
      refine ⟨D' * num mc, ?_⟩
      rw [hD_sp, map_mul, map_mul, mul_assoc, hnum mc]
    · exact ⟨0, by rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero, map_zero]⟩
  choose cpoly hcpoly using hcoeff_clear
  let QL : MvPolynomial (Fin 3) (Polynomial L) :=
    ∑ m ∈ Qfx.support, MvPolynomial.monomial m (cpoly m)
  have hQL_map : MvPolynomial.map (algebraMap (Polynomial L) FX) QL =
      MvPolynomial.C (algebraMap (Polynomial L) FX D) * Qfx := by
    ext m
    simp only [QL, map_sum, MvPolynomial.map_monomial, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, Finset.sum_ite_eq', MvPolynomial.coeff_C_mul]
    split_ifs with hm
    · exact (hcpoly m).symm
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
  have hQL_ne : QL ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hQL_map
    exact hQfx_ne ((mul_eq_zero.mp hQL_map.symm).resolve_left (by
      intro hC; exact hD_fx (MvPolynomial.C_eq_zero.mp hC)))
  -- Step 3: Pick a nonzero `(m*, a*)` coefficient `c* ∈ L` of `QL` and a `K`-linear map `λ : L →ₗ[K] K` with `λ c* = 1`!
  obtain ⟨mstar, hmstar⟩ : ∃ m, QL.coeff m ≠ 0 := by
    by_contra! hall; exact hQL_ne (MvPolynomial.ext _ _ fun m => by simpa using hall m)
  obtain ⟨astar, hastar⟩ : ∃ a, (QL.coeff mstar).coeff a ≠ 0 := by
    by_contra! hall; exact hmstar (Polynomial.ext fun a => by simpa using hall a)
  let cstar : L := (QL.coeff mstar).coeff astar
  let B := Module.Basis.ofVectorSpace K L
  obtain ⟨b, hb⟩ : ∃ b, B.repr cstar b ≠ 0 := by
    by_contra! hall
    exact hastar (B.repr.injective (by apply Finsupp.ext; intro b; simpa using hall b))
  let φK : L →ₗ[K] K := (B.repr cstar b)⁻¹ • B.coord b
  have hφK_star : φK cstar = 1 := by simp [φK, inv_mul_cancel₀ hb]
  -- Define `Q ∈ DifferentialPolynomial K 2` by applying `φK` coefficientwise to `QL`!
  let polyToDiff (p : Polynomial L) : DifferentialPolynomial K 2 :=
    ∑ a ∈ p.support, MvPolynomial.monomial (Finsupp.single none a) (φK (p.coeff a))
  let Q : DifferentialPolynomial K 2 :=
    ∑ m ∈ QL.support, polyToDiff (QL.coeff m) *
      (MvPolynomial.X (some 0) ^ m 0 * MvPolynomial.X (some 1) ^ m 1 * MvPolynomial.X (some 2) ^ m 2)
  -- Express `Q` coefficients explicitly: `Q.coeff (single none a + mapDomain some m) = φK ((QL.coeff m).coeff a)`!
  let liftExp (a : ℕ) (m : Fin 3 →₀ ℕ) : Option (Fin 3) →₀ ℕ :=
    Finsupp.single none a + Finsupp.single (some 0) (m 0) +
      Finsupp.single (some 1) (m 1) + Finsupp.single (some 2) (m 2)
  have hQ_coeff : ∀ a m, Q.coeff (liftExp a m) = φK ((QL.coeff m).coeff a) := by
    intro a m
    have hmon (m' : Fin 3 →₀ ℕ) (a' : ℕ) :
        MvPolynomial.monomial (Finsupp.single none a') (φK ((QL.coeff m').coeff a')) *
          (MvPolynomial.X (some 0) ^ m' 0 * MvPolynomial.X (some 1) ^ m' 1 * MvPolynomial.X (some 2) ^ m' 2) =
        MvPolynomial.monomial (liftExp a' m') (φK ((QL.coeff m').coeff a')) := by
      simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one, liftExp, add_assoc]
    have hQeq : Q = ∑ m' ∈ QL.support, ∑ a' ∈ (QL.coeff m').support,
        MvPolynomial.monomial (liftExp a' m') (φK ((QL.coeff m').coeff a')) := by
      dsimp only [Q, polyToDiff]
      apply Finset.sum_congr rfl; intro m' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a' _
      exact hmon m' a'
    rw [hQeq, MvPolynomial.coeff_sum]
    have hinj_exp : ∀ a' m', liftExp a' m' = liftExp a m ↔ a' = a ∧ m' = m := by
      intro a' m'
      constructor
      · intro he
        refine ⟨?_, ?_⟩
        · have := DFunLike.congr_fun he none; simpa [liftExp] using this
        · ext k; fin_cases k
          · have := DFunLike.congr_fun he (some 0); simpa [liftExp] using this
          · have := DFunLike.congr_fun he (some 1); simpa [liftExp] using this
          · have := DFunLike.congr_fun he (some 2); simpa [liftExp] using this
      · rintro ⟨rfl, rfl⟩; rfl
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hinj_exp]
    by_cases hm : m ∈ QL.support
    · rw [Finset.sum_eq_single m]
      · by_cases ha : a ∈ (QL.coeff m).support
        · rw [Finset.sum_eq_single a]
          · simp
          · intro a' _ hne; simp [hne]
          · intro ha'; exact absurd ha ha'
        · rw [Finset.sum_eq_zero]
          · rw [Polynomial.notMem_support_iff.mp ha, map_zero]
          · intro a' ha'; have hne : a' ≠ a := fun h => ha (h ▸ ha'); simp [hne]
      · intro m' _ hne
        apply Finset.sum_eq_zero; intro a' _; simp [hne]
      · intro hm'; exact absurd hm hm'
    · rw [Finset.sum_eq_zero]
      · rw [MvPolynomial.notMem_support_iff.mp hm, Polynomial.coeff_zero, map_zero]
      · intro m' hm'; apply Finset.sum_eq_zero; intro a' _
        have hne : m' ≠ m := fun h => hm (h ▸ hm'); simp [hne]
  have hQ_ne : Q ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : DifferentialPolynomial K 2 => P.coeff (liftExp astar mstar)) hz
    rw [hQ_coeff, MvPolynomial.coeff_zero] at hc
    exact one_ne_zero (hφK_star.symm.trans hc)
  -- Check `OrderTwoHigh box Q`!
  have hQL_supp : ∀ m ∈ QL.support, m ∈ Qfx.support := by
    intro m hm
    by_contra hnot
    have h0 : QL.coeff m = 0 := by
      dsimp only [QL]
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero; intro m' hm'
      rw [MvPolynomial.coeff_monomial, if_neg (fun h : m' = m => hnot (h ▸ hm'))]
    exact MvPolynomial.mem_support_iff.mp hm h0
  have hQ_supp : ∀ u' ∈ Q.support, ∃ m ∈ Qfx.support, ∃ a, u' = liftExp a m := by
    intro u' hu'
    have hQeq : Q = ∑ m' ∈ QL.support, ∑ a' ∈ (QL.coeff m').support,
        MvPolynomial.monomial (liftExp a' m') (φK ((QL.coeff m').coeff a')) := by
      dsimp only [Q, polyToDiff]
      apply Finset.sum_congr rfl; intro m' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a' _
      simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one, liftExp, add_assoc]
    have hne : Q.coeff u' ≠ 0 := MvPolynomial.mem_support_iff.mp hu'
    rw [hQeq, MvPolynomial.coeff_sum] at hne
    obtain ⟨m', hm', hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [MvPolynomial.coeff_sum] at hne1
    obtain ⟨a', _, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
    rw [MvPolynomial.coeff_monomial] at hne2
    split_ifs at hne2 with heq
    · exact ⟨m', hQL_supp m' hm', a', heq.symm⟩
    · exact absurd rfl hne2
  have hOrder : OrderTwoHigh box Q := by
    refine ⟨hQ_ne, ?_, ?_, ?_⟩
    · apply (jetTotalDegree_le_iff Q box.B).mpr
      intro u' hu'
      obtain ⟨m, hm, a, rfl⟩ := hQ_supp u' hu'
      have hm_le : m 0 + m 1 + m 2 ≤ (2 * j + 1) * u := by
        have h := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => Finsupp.weight fxJet2Weight_tot m) hm
        have h' := h.trans hQtot
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_three] at h'
        simp only [fxJet2Weight_tot, smul_eq_mul, mul_one] at h'
        omega
      have heq : totalJetDegree (liftExp a m) = m 0 + m 1 + m 2 := by
        dsimp only [liftExp]
        rw [totalJetDegree, map_add, map_add, map_add, Finsupp.weight_apply,
          Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply,
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simp [jetDegreeWeight]
      rw [heq]; exact hm_le.trans hB
    · apply Finset.sup_le; intro u' hu'
      obtain ⟨m, hm, a, rfl⟩ := hQ_supp u' hu'
      have hm_le : m 1 + 2 * m 2 ≤ 3 * u := by
        have h := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => Finsupp.weight fxJet2Weight_idx m) hm
        have h' := h.trans hQidx
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_three] at h'
        simp only [fxJet2Weight_idx, smul_eq_mul, mul_zero, zero_add, mul_one] at h'
        omega
      have heq : Finsupp.weight CJ0.indexWeight (liftExp a m) = m 1 + 2 * m 2 := by
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fintype.sum_option,
          Fin.sum_univ_three]
        simp [CJ0.indexWeight, liftExp, smul_eq_mul]; ring
      rw [heq]; exact hm_le.trans hJ
    · apply MvPolynomial.degreeOf_le_iff.mpr; intro u' hu'
      obtain ⟨m, hm, a, rfl⟩ := hQ_supp u' hu'
      have hm_le : m 2 ≤ u := by
        have h := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => Finsupp.weight fxJet2Weight_top m) hm
        have h' := h.trans hQtop
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_three] at h'
        simp only [fxJet2Weight_top, Pi.single_apply, smul_eq_mul,
          show (0 : Fin 3) ≠ Fin.last 2 by decide, show (1 : Fin 3) ≠ Fin.last 2 by decide,
          show (2 : Fin 3) = Fin.last 2 from rfl, ↓reduceIte, mul_zero, zero_add, mul_one] at h'
        exact h'
      have heq : liftExp a m (some (Fin.last 2)) = m 2 := by simp [liftExp, Fin.last]
      rw [heq]; exact hm_le.trans hC
  -- Step 4: Show `differentialSpecialization Q S = 0` for every mark `(z, S)` on `G` with `jetAt (prolongA G) z S ≠ 0`!
  refine ⟨Q, hOrder, fun z S hGz hAz => ?_⟩
  -- First prove `MvPolynomial.eval ![atX S, atX S.derivative, atX (hasseDeriv 2 S)] (QL.map (algebraMap (Polynomial L) FX)) = 0`!
  -- Because `QL.map algebraMap = C (algebraMap D) * Qfx`, and `Qfx` vanishes at `(Y₀, α₁, α₂)` in `EField`!
  -- Clear `α₁ = -B/A` and `α₂ = -B₁(α₁)/(2A)` inside `Equation = Polynomial Seeds`!
  have hSpec_QL : MvPolynomial.eval₂ (algebraMap (Polynomial L) FX)
      ![atX S, atX S.derivative, atX (hasseDeriv 2 S)] QL = 0 := by
    -- Define the `L`-hom `evalMark : Polynomial Seeds →+* FX` sending `z₀ ↦ z, z₁ ↦ z^p, Y₀ ↦ atX S`!
    let evEq : Equation →+* FX := Polynomial.eval₂RingHom (graphEval z) (atX S)
    let evJ_mark : Jet →+* FX := Polynomial.eval₂RingHom evEq (atX S.derivative)
    have hA_val : evEq (G.coeff 1) ≠ 0 := by
      intro hz; apply hAz
      change evJ_mark (prolongA G) = 0
      simp [prolongA, evJ_mark, hz]
    have h2fx : (2 : FX) ≠ 0 := by
      intro h2
      have hL0 : (2 : L) = 0 := by
        have h1 : (2 : FX) = algebraMap (Polynomial L) FX (Polynomial.C 2) := by simp only [map_ofNat]
        rw [h1] at h2
        exact Polynomial.C_eq_zero.mp (IsFractionRing.injective (Polynomial L) FX (h2.trans (map_zero _).symm))
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff L p 2).mp (by simpa using hL0)
      have hle := Nat.le_of_dvd (by decide) hdvd
      change 2130706433 ≤ 2 at hle; omega
    -- Compute `S' = -evEq B / evEq A` and `hasseDeriv 2 S = -evJ_mark B₁ / (2 * evEq A)` in `FX`!
    have hS1 : atX S.derivative = -(evEq (G.coeff 0)) / evEq (G.coeff 1) := by
      have hlin : G = Polynomial.C (G.coeff 0) + Polynomial.C (G.coeff 1) * Polynomial.X := by
        ext n; cases n with
        | zero => simp
        | succ n => cases n with
          | zero => simp
          | succ n =>
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
            simp
      have hg0 : evEq (G.coeff 0) + evEq (G.coeff 1) * atX S.derivative = 0 := by
        have h := hGz
        change evJ_mark G = 0 at h
        rw [hlin, map_add, map_mul] at h
        simpa [evJ_mark] using h
      exact eq_div_of_mul_eq hA_val (by linear_combination hg0)
    have hS2 : atX (hasseDeriv 2 S) = -(evJ_mark (prolongB1 G)) / (2 * evEq (G.coeff 1)) := by
      have hp0 := prolong_vanish_at_mark hdegG z S hGz
      have hAeq : jetAt (prolongA G) z S = 2 * evEq (G.coeff 1) := by
        change evJ_mark (prolongA G) = _; simp [prolongA, evJ_mark]
      have hB1eq : jetAt (prolongB1 G) z S = evJ_mark (prolongB1 G) := rfl
      rw [hAeq, hB1eq] at hp0
      exact eq_div_of_mul_eq (mul_ne_zero h2fx hA_val) (by linear_combination hp0)
    -- In `Equation`, define the cleared numerators `N₁ = -B` and `N₂ = -(A² * B₁.coeff 0 - A * B * B₁.coeff 1 + B² * B₁.coeff 2)`
    -- so that `α₁ = N₁ / A` and `α₂ = N₂ / (2 * A³)` in BOTH `EField` and `FX`!
    let A := G.coeff 1
    let B := G.coeff 0
    let B1 := prolongB1 G
    let N2 : Equation := -(B1.coeff 0 * A ^ 2 - B1.coeff 1 * B * A + B1.coeff 2 * B ^ 2)
    have hB1_deg : B1.natDegree ≤ 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      apply Polynomial.ext; intro i; rw [Polynomial.coeff_zero]
      by_contra hne
      have h := (prolongB1_rowCaps hG k i hne).2.1
      dsimp only at h
      omega
    have hB1_split : B1 = Polynomial.C (B1.coeff 0) + Polynomial.C (B1.coeff 1) * Polynomial.X +
        Polynomial.C (B1.coeff 2) * Polynomial.X ^ 2 := by
      ext k; cases k with
      | zero => simp
      | succ k => cases k with
        | zero => simp
        | succ k => cases k with
          | zero => simp
          | succ k =>
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : B1.natDegree < k + 3)]
            simp [Polynomial.coeff_X_pow]
    have hα2_eq : alpha2 G = seedsY0ToE N2 / (2 * seedsY0ToE A ^ 3) := by
      have hAe_ne : seedsY0ToE A ≠ 0 := fun hz => by
        have hA1 : A ≠ 0 := by
          dsimp only [A]; rw [← hdegG, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hdegG; omega)
        exact hA1 (seedsY0ToE_injective (hz.trans (map_zero _).symm))
      have h2E : (2 : EField) ≠ 0 := by
        intro h2
        haveI : CharP EField p := charP_EField
        have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff EField p 2).mp (by simpa using h2)
        have hle := Nat.le_of_dvd (by decide) hdvd
        change 2130706433 ≤ 2 at hle; omega
      have hα1 : alpha1 G = -(seedsY0ToE B) / seedsY0ToE A := rfl
      have hevB1 : evJetAt G B1 = -(seedsY0ToE N2) / seedsY0ToE A ^ 2 := by
        rw [hB1_split]
        simp only [evJetAt, map_add, map_mul, map_pow, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, Polynomial.eval₂_X, hα1, N2, map_neg, map_sub]
        field_simp [hAe_ne]
        ring
      dsimp only [alpha2]
      have hAp : evJetAt G (prolongA G) = 2 * seedsY0ToE A := by
        simp [prolongA, evJetAt, A]
      rw [hAp, hevB1]
      field_simp [hAe_ne, h2E]
    have hS2_eq : atX (hasseDeriv 2 S) = evEq N2 / (2 * evEq A ^ 3) := by
      have hA_val' : evEq A ≠ 0 := hA_val
      have hS1' : atX S.derivative = -(evEq B) / evEq A := hS1
      have hevB1 : evJ_mark B1 = -(evEq N2) / evEq A ^ 2 := by
        rw [hB1_split]
        simp only [evJ_mark, map_add, map_mul, map_pow, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C, Polynomial.eval₂_X, hS1', N2, map_neg, map_sub]
        field_simp [hA_val']
        ring
      rw [hS2, hevB1]
      change -( -(evEq N2) / evEq A ^ 2) / (2 * evEq A) = evEq N2 / (2 * evEq A ^ 3)
      field_simp [hA_val', h2fx]
    -- Form the cleared polynomial `Qcleared ∈ Equation` = `∑ m, (C (algebraMap D * Qfx.coeff m)) * Y₀^{m 0} * (-B)^{m 1} * N2^{m 2} * 2^{u - m 2} * A^{4*u - (m 1 + 3 * m 2)}`!
    let Qcleared : Equation :=
      ∑ m ∈ Qfx.support, Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX (cpoly m))) *
        Polynomial.X ^ m 0 * (-B) ^ m 1 * N2 ^ m 2 *
        (2 : Equation) ^ (u - m 2) * A ^ (4 * u - (m 1 + 3 * m 2))
    have hm_bds : ∀ m ∈ Qfx.support, m 2 ≤ u ∧ m 1 + 3 * m 2 ≤ 4 * u := by
      intro m hm
      have h1 : m 2 ≤ u := by
        have h := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => Finsupp.weight fxJet2Weight_top m) hm
        have h' := h.trans hQtop
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_three] at h'
        simp only [fxJet2Weight_top, Pi.single_apply, smul_eq_mul,
          show (0 : Fin 3) ≠ Fin.last 2 by decide, show (1 : Fin 3) ≠ Fin.last 2 by decide,
          show (2 : Fin 3) = Fin.last 2 from rfl, ↓reduceIte, mul_zero, zero_add, mul_one] at h'
        exact h'
      have h2 : m 1 + 2 * m 2 ≤ 3 * u := by
        have h := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => Finsupp.weight fxJet2Weight_idx m) hm
        have h' := h.trans hQidx
        rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Fin.sum_univ_three] at h'
        simp only [fxJet2Weight_idx, smul_eq_mul, mul_zero, zero_add, mul_one] at h'
        omega
      exact ⟨h1, by omega⟩
    have hcancel : ∀ {F : Type} [Field F] (a b c d x y : F) (_ : (2 : F) ≠ 0) (_ : a ≠ 0)
        (m0 m1 m2 u : ℕ) (_ : m2 ≤ u) (_ : m1 + 3 * m2 ≤ 4 * u),
        (d * c) * x ^ m0 * (-b) ^ m1 * y ^ m2 * (2 : F) ^ (u - m2) * a ^ (4 * u - (m1 + 3 * m2)) =
        (2 : F) ^ u * a ^ (4 * u) * d * (c * (x ^ m0 * (-b / a) ^ m1 * (y / (2 * a ^ 3)) ^ m2)) := by
      intro F _ a b c d x y h2 hA m0 m1 m2 u hm2 hm13
      have hpow2 : (2 : F) ^ u = (2 : F) ^ (u - m2) * (2 : F) ^ m2 := by
        rw [← pow_add, Nat.sub_add_cancel hm2]
      have hpowA : a ^ (4 * u) = a ^ (4 * u - (m1 + 3 * m2)) * (a ^ m1 * (a ^ 3) ^ m2) := by
        rw [← pow_mul, ← pow_add, ← pow_add, Nat.sub_add_cancel hm13]
      simp only [div_pow, mul_pow]
      rw [hpow2, hpowA]
      field_simp [h2, hA]
    -- Evaluate `Qcleared` in `EField`: equals `2^u * A^(4u) * D * Qfx(Y₀, α₁, α₂) = 0`!
    have hQc_E : seedsY0ToE Qcleared = 0 := by
      have hAe_ne : seedsY0ToE A ≠ 0 := fun hz => by
        have hA1 : A ≠ 0 := by
          dsimp only [A]; rw [← hdegG, Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => by rw [h, Polynomial.natDegree_zero] at hdegG; omega)
        exact hA1 (seedsY0ToE_injective (hz.trans (map_zero _).symm))
      have h2E : (2 : EField) ≠ 0 := by
        intro h2
        have : CharP EField p := charP_EField
        have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff EField p 2).mp (by simpa using h2)
        have hle := Nat.le_of_dvd (by decide) hdvd
        change 2130706433 ≤ 2 at hle; omega
      have hC_s : ∀ x : FX, seedsY0ToE (Polynomial.C (MvPolynomial.C x)) = fxToE' x := fun x => by
        simp [seedsY0ToE, fxToE']
      have hX_s : seedsY0ToE Polynomial.X = algebraMap BaseRing EField Polynomial.X := by
        simp [seedsY0ToE]
      have hval : seedsY0ToE Qcleared =
          (2 : EField) ^ u * seedsY0ToE A ^ (4 * u) *
            fxToE' (algebraMap (Polynomial L) FX D) *
            MvPolynomial.eval₂ fxToE'
              (fun k => match k with | ⟨0, _⟩ => algebraMap BaseRing EField Polynomial.X
                                     | ⟨1, _⟩ => alpha1 G
                                     | ⟨2, _⟩ => alpha2 G) Qfx := by
        rw [MvPolynomial.eval₂_eq', Finset.mul_sum]
        dsimp only [Qcleared]
        rw [map_sum]
        apply Finset.sum_congr rfl; intro m hm
        obtain ⟨hm2, hm13⟩ := hm_bds m hm
        rw [Fin.prod_univ_three]
        simp only [map_mul, map_pow, map_neg, map_ofNat, hC_s, hX_s]
        rw [← hcpoly m, map_mul]
        have hα1 : alpha1 G = -(seedsY0ToE B) / seedsY0ToE A := rfl
        rw [hα1, hα2_eq]
        exact hcancel (seedsY0ToE A) (seedsY0ToE B) (fxToE' (Qfx.coeff m))
          (fxToE' (algebraMap (Polynomial L) FX D)) (algebraMap BaseRing EField Polynomial.X)
          (seedsY0ToE N2) h2E hAe_ne (m 0) (m 1) (m 2) u hm2 hm13
      rw [hval, hQeval, mul_zero]
    have hQc_zero : Qcleared = 0 := seedsY0ToE_injective (hQc_E.trans (map_zero _).symm)
    -- Now evaluate `Qcleared = 0` under `evEq : Equation →+* FX`!
    have hQc_FX : evEq Qcleared = 0 := by rw [hQc_zero, map_zero]
    have hC_e : ∀ x : FX, evEq (Polynomial.C (MvPolynomial.C x)) = x := fun x => by
      simp [evEq, graphEval]
    have hX_e : evEq Polynomial.X = atX S := by simp [evEq]
    have hA_val' : evEq A ≠ 0 := hA_val
    have hS1' : atX S.derivative = -(evEq B) / evEq A := hS1
    have hval_FX : evEq Qcleared =
        (2 : FX) ^ u * evEq A ^ (4 * u) *
          MvPolynomial.eval₂ (algebraMap (Polynomial L) FX)
            ![atX S, atX S.derivative, atX (hasseDeriv 2 S)] QL := by
      change evEq Qcleared = (2 : FX) ^ u * evEq A ^ (4 * u) *
        MvPolynomial.eval₂Hom (algebraMap (Polynomial L) FX)
          ![atX S, atX S.derivative, atX (hasseDeriv 2 S)] QL
      dsimp only [Qcleared]
      rw [map_sum]
      conv_rhs => rw [show QL = ∑ m ∈ Qfx.support, MvPolynomial.monomial m (cpoly m) from rfl, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro m hm
      obtain ⟨hm2, hm13⟩ := hm_bds m hm
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
      simp only [map_mul, map_pow, map_neg, map_ofNat, hC_e, hX_e,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hS1', hS2_eq]
      have hc := hcancel (evEq A) (evEq B) (algebraMap (Polynomial L) FX (cpoly m)) (1 : FX)
        (atX S) (evEq N2) h2fx hA_val' (m 0) (m 1) (m 2) u hm2 hm13
      simpa only [one_mul, mul_one] using hc
    rw [hval_FX] at hQc_FX
    exact (mul_eq_zero.mp hQc_FX).resolve_left
      (mul_ne_zero (pow_ne_zero u h2fx) (pow_ne_zero (4 * u) hA_val))
  -- Pull back `hSpec_QL = 0` from `FX` to `Polynomial L`, then apply `φK : L →ₗ[K] K` coefficientwise!
  have hSpec_L : MvPolynomial.eval₂ (RingHom.id (Polynomial L))
      ![liftPoly S, liftPoly S.derivative, liftPoly (hasseDeriv 2 S)] QL = 0 := by
    apply IsFractionRing.injective (Polynomial L) FX
    rw [map_zero, ← hSpec_QL]
    have hcomp : (algebraMap (Polynomial L) FX).comp (MvPolynomial.eval₂Hom (RingHom.id (Polynomial L))
        ![liftPoly S, liftPoly S.derivative, liftPoly (hasseDeriv 2 S)]) =
        MvPolynomial.eval₂Hom (algebraMap (Polynomial L) FX)
          ![atX S, atX S.derivative, atX (hasseDeriv 2 S)] := by
      apply MvPolynomial.ringHom_ext
      · intro p; simp
      · intro k; fin_cases k <;> simp [atX]
    exact RingHom.congr_fun hcomp QL
  -- Apply `mapCoeffs φK : Polynomial L →ₗ[K] Polynomial K` to `hSpec_L = 0`!
  let projPoly : Polynomial L →ₗ[K] Polynomial K :=
    { toFun := fun p => p.sum fun n a => Polynomial.monomial n (φK a)
      map_add' := fun p q => by
        apply Polynomial.ext; intro n
        simp only [Polynomial.sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
          Finsupp.single_apply, Polynomial.coeff_add]
        have h1 : ∀ r : Polynomial L, (∑ i ∈ r.support, if i = n then φK (r.coeff i) else 0) =
            φK (r.coeff n) := by
          intro r; rw [Finset.sum_ite_eq']; split_ifs with hn
          · rfl
          · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
        have h2 : (∑ i ∈ (p + q).support, if i = n then φK (p.coeff i + q.coeff i) else 0) =
            φK (p.coeff n + q.coeff n) := by
          simpa only [Polynomial.coeff_add] using h1 (p + q)
        rw [h2, h1 p, h1 q, map_add]
      map_smul' := fun c p => by
        apply Polynomial.ext; intro n
        simp only [Polynomial.sum, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
          Finsupp.single_apply, Polynomial.coeff_smul, RingHom.id_apply]
        have h1 : ∀ r : Polynomial L, (∑ i ∈ r.support, if i = n then φK (r.coeff i) else 0) =
            φK (r.coeff n) := by
          intro r; rw [Finset.sum_ite_eq']; split_ifs with hn
          · rfl
          · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
        have h2 : (∑ i ∈ (c • p).support, if i = n then φK (c • p.coeff i) else 0) =
            φK (c • p.coeff n) := by
          simpa only [Polynomial.coeff_smul] using h1 (c • p)
        rw [h2, h1 p, map_smul] }
  have hproj_coeff (p : Polynomial L) (n : ℕ) : (projPoly p).coeff n = φK (p.coeff n) := by
    simp only [projPoly, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.sum, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
  have hproj_mul_lift (p : Polynomial L) (q : Polynomial K) :
      projPoly (p * liftPoly q) = projPoly p * q := by
    apply Polynomial.ext; intro n
    rw [hproj_coeff, Polynomial.coeff_mul, Polynomial.coeff_mul]
    have hsum : ∀ (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → L), φK (∑ x ∈ S, f x) = ∑ x ∈ S, φK (f x) :=
      fun S f => map_sum φK f S
    rw [hsum]
    apply Finset.sum_congr rfl; rintro ⟨a, b⟩ _
    rw [liftPoly, Polynomial.coeff_map, hproj_coeff, mul_comm (p.coeff a), ← Algebra.smul_def,
      map_smul, smul_eq_mul, mul_comm]
  have hproj_spec : projPoly (MvPolynomial.eval₂ (RingHom.id (Polynomial L))
      ![liftPoly S, liftPoly S.derivative, liftPoly (hasseDeriv 2 S)] QL) =
      differentialSpecialization Q S := by
    dsimp only [Q, polyToDiff]
    rw [MvPolynomial.eval₂_eq', map_sum]
    unfold differentialSpecialization
    rw [map_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Fin.prod_univ_three]
    simp only [RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have hpow : liftPoly S ^ m 0 * liftPoly S.derivative ^ m 1 * liftPoly (hasseDeriv 2 S) ^ m 2 =
        liftPoly (S ^ m 0 * S.derivative ^ m 1 * hasseDeriv 2 S ^ m 2) := by
      simp [liftPoly, Polynomial.map_mul, Polynomial.map_pow]
    rw [hpow, hproj_mul_lift]
    have hX0 : differentialSpecializationHom (d := 2) S (MvPolynomial.X (some 0)) = S := by
      simp [differentialSpecializationHom]
    have hX1 : differentialSpecializationHom (d := 2) S (MvPolynomial.X (some 1)) = S.derivative := by
      simp [differentialSpecializationHom]
    have hX2 : differentialSpecializationHom (d := 2) S (MvPolynomial.X (some 2)) = hasseDeriv 2 S := by
      simp [differentialSpecializationHom]
    simp only [map_mul, map_pow, map_sum, hX0, hX1, hX2]
    congr 1
    apply Polynomial.ext; intro n
    rw [hproj_coeff, Polynomial.finsetSum_coeff]
    have hterm : ∀ a ∈ (QL.coeff m).support,
        (differentialSpecializationHom (d := 2) S
          (MvPolynomial.monomial (Finsupp.single none a) (φK ((QL.coeff m).coeff a)))).coeff n =
        if a = n then φK ((QL.coeff m).coeff a) else 0 := by
      intro a _
      rw [show MvPolynomial.monomial (Finsupp.single none a) (φK ((QL.coeff m).coeff a)) =
        MvPolynomial.C (φK ((QL.coeff m).coeff a)) * MvPolynomial.X none ^ a by
          simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial],
        map_mul, map_pow]
      have hC : differentialSpecializationHom (d := 2) S (MvPolynomial.C (φK ((QL.coeff m).coeff a))) =
          Polynomial.C (φK ((QL.coeff m).coeff a)) := by simp [differentialSpecializationHom]
      have hX : differentialSpecializationHom (d := 2) S (MvPolynomial.X none) = Polynomial.X := by
        simp [differentialSpecializationHom]
      rw [hC, hX, Polynomial.coeff_C_mul_X_pow]
      by_cases h : a = n
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
  rw [← hproj_spec, hSpec_L, map_zero]

/-! ## 7. `A = 0` Exception Bound & End-to-End 6-Small-Rect Case-B Theorem -/

/-- Marks on `G` where the leading `Y₁`-coefficient `prolongA G` also vanishes contribute at most
    `(2*j - 1) * u * (p + 1)` labels via `Lower6960.ThirdPole.count_common` /
    `K1_10.frobenius_coefficient_exception_count`. -/
theorem caseB_leading_zero_card_le {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1)
    {j u : ℕ} (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (hu : u ≤ 22) (hG : RowCaps G ⟨0, j, 1, u⟩)
    (Γ : Finset K) (label : K → K) (hlabel : Function.Injective label) (scalar : K → Polynomial K) :
    (Γ.filter fun γ => jetAt G (label γ) (scalar γ) = 0 ∧
      jetAt (prolongA G) (label γ) (scalar γ) = 0).card ≤ (2 * j - 1) * u * (p + 1) := by
  classical
  let Bad := Γ.filter fun γ => jetAt G (label γ) (scalar γ) = 0 ∧
    jetAt (prolongA G) (label γ) (scalar γ) = 0
  let coord (γ : K) : FX := seedEmbedding (label γ)
  have hcard_im : (Bad.image coord).card = Bad.card :=
    Finset.card_image_of_injOn fun x _ y _ h => hlabel (seedEmbedding.injective h)
  let A := G.coeff 1
  let B := G.coeff 0
  have hAne : A ≠ 0 := by
    dsimp only [A]; rw [← hdegG, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
  have h2fx : (2 : FX) ≠ 0 := by
    intro h2
    have hL0 : (2 : L) = 0 := by
      have h1 : (2 : FX) = algebraMap (Polynomial L) FX (Polynomial.C 2) := by simp only [map_ofNat]
      rw [h1] at h2
      exact Polynomial.C_eq_zero.mp (IsFractionRing.injective (Polynomial L) FX (h2.trans (map_zero _).symm))
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff L p 2).mp (by simpa using hL0)
    have hle := Nat.le_of_dvd (by decide) hdvd
    change 2130706433 ≤ 2 at hle; omega
  have hA_deg : A.natDegree ≤ j - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk; by_contra hne
    have h := (hG 1 k hne).1; dsimp only at h; omega
  have hB_deg : B.natDegree ≤ j := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk; by_contra hne
    have h := (hG 0 k hne).1; dsimp only at h; omega
  have hA_axis : ∀ k, (A.coeff k).degreeOf 0 ≤ u ∧ (A.coeff k).degreeOf 1 ≤ u := by
    intro k
    by_cases hz : A.coeff k = 0
    · simp [hz]
    · have hu' := (hG 1 k hz).2.2
      exact ⟨(MvPolynomial.degreeOf_le_totalDegree _ 0).trans hu',
        (MvPolynomial.degreeOf_le_totalDegree _ 1).trans hu'⟩
  have hB_axis : ∀ k, (B.coeff k).degreeOf 0 ≤ u ∧ (B.coeff k).degreeOf 1 ≤ u := by
    intro k
    by_cases hz : B.coeff k = 0
    · simp [hz]
    · have hu' := (hG 0 k hz).2.2
      exact ⟨(MvPolynomial.degreeOf_le_totalDegree _ 0).trans hu',
        (MvPolynomial.degreeOf_le_totalDegree _ 1).trans hu'⟩
  have hboth : ∀ γ ∈ Bad,
      (A.map (graphEval (label γ))).eval (atX (scalar γ)) = 0 ∧
      (B.map (graphEval (label γ))).eval (atX (scalar γ)) = 0 := by
    intro γ hγ
    obtain ⟨_, hGz, hAz⟩ := Finset.mem_filter.mp hγ
    have hA0 : A.eval₂ (graphEval (label γ)) (atX (scalar γ)) = 0 := by
      have h1 : jetAt (prolongA G) (label γ) (scalar γ) =
          2 * A.eval₂ (graphEval (label γ)) (atX (scalar γ)) := by
        simp [jetAt, prolongA, A]
      rw [h1] at hAz
      exact (mul_eq_zero.mp hAz).resolve_left h2fx
    have hB0 : B.eval₂ (graphEval (label γ)) (atX (scalar γ)) = 0 := by
      have hlin : G = Polynomial.C B + Polynomial.C A * Polynomial.X := by
        ext n; cases n with
        | zero => simp [B]
        | succ n => cases n with
          | zero => simp [A]
          | succ n =>
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
            simp [Polynomial.coeff_C, Polynomial.coeff_X]
      have h1 := hGz
      unfold jetAt at h1
      rw [hlin, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, Polynomial.eval₂_X] at h1
      change B.eval₂ (graphEval (label γ)) (atX (scalar γ)) +
        A.eval₂ (graphEval (label γ)) (atX (scalar γ)) * atX (scalar γ).derivative = 0 at h1
      rw [hA0, zero_mul, add_zero] at h1
      exact h1
    simpa [Polynomial.eval_map] using ⟨hA0, hB0⟩
  by_cases hposAB : A.natDegree ≠ 0 ∨ B.natDegree ≠ 0
  · -- `A.resultant B ≠ 0` since `G` is irreducible of `Y₁`-degree `1` ⇒ `IsRelPrime A B` in `Seeds[Y₀]`!
    have hcop : IsRelPrime A B := by
      intro d hdA hdB
      have hdG : Polynomial.C d ∣ G := by
        have hlin : G = Polynomial.C B + Polynomial.C A * Polynomial.X := by
          ext n; cases n with
          | zero => simp [B]
          | succ n => cases n with
            | zero => simp [A]
            | succ n =>
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
              simp [Polynomial.coeff_C, Polynomial.coeff_X]
        rw [hlin]
        exact dvd_add (_root_.map_dvd Polynomial.C hdB) (dvd_mul_of_dvd_left (_root_.map_dvd Polynomial.C hdA) _)
      obtain ⟨Q, hQ⟩ := hdG
      rcases hIrr.isUnit_or_isUnit hQ with hu' | hu'
      · exact Polynomial.isUnit_C.mp hu'
      · exfalso
        have hQdeg : Q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu'
        have hGdeg : G.natDegree = 0 := by
          rw [hQ]; exact Nat.eq_zero_of_le_zero ((Polynomial.natDegree_C_mul_le d Q).trans_eq hQdeg)
        omega
    have hres_ne : A.resultant B ≠ 0 := by
      let φ := algebraMap Seeds (FractionRing Seeds)
      have hinj : Function.Injective φ := IsFractionRing.injective Seeds (FractionRing Seeds)
      letI : NormalizedGCDMonoid Seeds := Classical.arbitrary _
      have hcopF : IsCoprime (A.map φ) (B.map φ) := by
        -- In `FractionRing Seeds [Y₀]`, if a prime `q` divided both, clearing denominators contradicts `IsRelPrime A B`!
        rw [EuclideanDomain.gcd_isUnit_iff.symm]
        by_contra hnu
        let g := EuclideanDomain.gcd (A.map φ) (B.map φ)
        have hg_ne : g ≠ 0 := fun hz => by
          have hA0 : A.map φ = 0 := zero_dvd_iff.mp (hz ▸ EuclideanDomain.gcd_dvd_left _ _)
          exact hAne ((Polynomial.map_eq_zero_iff hinj).mp hA0)
        have hg_pos : 0 < g.natDegree := by
          by_contra h0
          have h0' : g.natDegree = 0 := by omega
          exact hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr
            (Polynomial.degree_eq_natDegree hg_ne ▸ congrArg WithBot.some h0'))
        -- Take an irreducible factor `q` of `g` in `(FractionRing Seeds)[Y₀]`, lift to primitive `q₀ ∈ Seeds[Y₀]`!
        obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hg_ne
        have hqA : q ∣ A.map φ := hq_dvd.trans (EuclideanDomain.gcd_dvd_left _ _)
        have hqB : q ∣ B.map φ := hq_dvd.trans (EuclideanDomain.gcd_dvd_right _ _)
        -- Clear denominators of `q` to get `q₁ ∈ Seeds[Y₀]` with `q₁.map φ = C s * q`, then take `primPart q₁`!
        obtain ⟨s, hs_ne, q₁, hq₁⟩ : ∃ s : Seeds, s ≠ 0 ∧ ∃ q₁ : Equation,
            q₁.map φ = Polynomial.C (φ s) * q := by
          choose x hx using fun k : q.support =>
            IsLocalization.surj (nonZeroDivisors Seeds) (q.coeff k)
          let den := fun k : q.support => (x k).2
          let num := fun k : q.support => (x k).1
          have hnum : ∀ k : q.support, q.coeff k * φ (den k).1 = φ (num k) := hx
          let S : Seeds := ∏ k : q.support, (den k).1
          have hS : S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => nonZeroDivisors.ne_zero (den k).2
          have hc : ∀ k, ∃ p : Seeds, φ S * q.coeff k = φ p := by
            intro k
            by_cases hk : k ∈ q.support
            · let kc : q.support := ⟨k, hk⟩
              let S' := ∏ k' ∈ Finset.univ.erase kc, (den k').1
              have hS_sp : S = S' * (den kc).1 := Finset.prod_erase_mul _ _ (Finset.mem_univ kc) |>.symm
              refine ⟨S' * num kc, ?_⟩
              rw [hS_sp, map_mul, map_mul, mul_assoc, mul_comm (φ (den kc).1), hnum kc]
            · exact ⟨0, by rw [Polynomial.notMem_support_iff.mp hk, mul_zero, map_zero]⟩
          choose cp hcp using hc
          let q₁ : Equation := ∑ k ∈ q.support, Polynomial.monomial k (cp k)
          refine ⟨S, hS, q₁, ?_⟩
          apply Polynomial.ext; intro k
          simp only [q₁, Polynomial.map_sum, Polynomial.map_monomial, Polynomial.finsetSum_coeff,
            Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Polynomial.coeff_C_mul]
          split_ifs with hk
          · exact (hcp k).symm
          · rw [Polynomial.notMem_support_iff.mp hk, mul_zero]
        have hq₁_ne : q₁ ≠ 0 := fun hz => by
          rw [hz, Polynomial.map_zero] at hq₁
          exact hq_irr.ne_zero ((mul_eq_zero.mp hq₁.symm).resolve_left (by
            intro hC; exact hs_ne (hinj ((Polynomial.C_eq_zero.mp hC).trans (map_zero _).symm))))
        let q₀ := q₁.primPart
        have hq₀_prim : q₀.IsPrimitive := q₁.isPrimitive_primPart
        have hfac : q₁ = Polynomial.C q₁.content * q₀ := q₁.eq_C_content_mul_primPart
        have hq₀_map : Polynomial.C (φ q₁.content) * q₀.map φ = Polynomial.C (φ s) * q := by
          rw [← Polynomial.map_C, ← Polynomial.map_mul, ← hfac, hq₁]
        have hcont_ne : q₁.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hq₁_ne
        have hu_c : IsUnit (Polynomial.C (φ q₁.content)) :=
          Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun hz => hcont_ne (hinj (hz.trans (map_zero _).symm))))
        have hu_s : IsUnit (Polynomial.C (φ s)) :=
          Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun hz => hs_ne (hinj (hz.trans (map_zero _).symm))))
        have hassoc : Associated (q₀.map φ) q := by
          refine ⟨(hu_c.unit * hu_s.unit⁻¹ : (Polynomial (FractionRing Seeds))ˣ), ?_⟩
          have h := congrArg (hu_s.unit⁻¹.val * ·) hq₀_map
          have hinv : hu_s.unit⁻¹.val * Polynomial.C (φ s) = 1 := by
            simpa only [hu_s.unit_spec] using Units.inv_mul hu_s.unit
          rw [← mul_assoc (hu_s.unit⁻¹.val) (Polynomial.C (φ s)), hinv, one_mul] at h
          calc
            q₀.map φ * (hu_c.unit * hu_s.unit⁻¹ : (Polynomial (FractionRing Seeds))ˣ)
              = q₀.map φ * (Polynomial.C (φ q₁.content) * hu_s.unit⁻¹.val) := by
                  rw [Units.val_mul, hu_c.unit_spec]
            _ = hu_s.unit⁻¹.val * (Polynomial.C (φ q₁.content) * q₀.map φ) := by ring
            _ = q := h
        have hq₀_dvd_A : q₀ ∣ A := by
          apply hq₀_prim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing Seeds)
          exact hassoc.dvd_iff_dvd_left.mpr hqA
        have hq₀_dvd_B : q₀ ∣ B := by
          apply hq₀_prim.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing Seeds)
          exact hassoc.dvd_iff_dvd_left.mpr hqB
        have hu_q₀ : IsUnit q₀ := hcop hq₀_dvd_A hq₀_dvd_B
        have hq₀_deg : q₀.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_q₀
        have hq_deg : q.natDegree = 0 := by
          have hdeg_eq := congrArg Polynomial.natDegree hq₀_map
          have hcont_ne' : φ q₁.content ≠ 0 := fun hz => hcont_ne (hinj (hz.trans (map_zero _).symm))
          have hs_ne' : φ s ≠ 0 := fun hz => hs_ne (hinj (hz.trans (map_zero _).symm))
          rw [Polynomial.natDegree_C_mul hcont_ne', Polynomial.natDegree_C_mul hs_ne',
            Polynomial.natDegree_map_eq_of_injective hinj, hq₀_deg] at hdeg_eq
          exact hdeg_eq.symm
        exact hq_irr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr
          (Polynomial.degree_eq_natDegree hq_irr.ne_zero ▸ congrArg WithBot.some hq_deg))
      have hn := Polynomial.resultant_ne_zero (A.map φ) (B.map φ) hcopF
      intro hz
      apply hn
      rw [Polynomial.natDegree_map_eq_of_injective hinj,
        Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.resultant_map_map]
      change φ (A.resultant B) = 0
      rw [hz, map_zero]
    have hdeg_sum : B.natDegree * u + A.natDegree * u ≤ (2 * j - 1) * u := by
      have : B.natDegree + A.natDegree ≤ 2 * j - 1 := by omega
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right u this
    have hsmall : B.natDegree * u + A.natDegree * u < p :=
      hdeg_sum.trans_lt (by
        have h1 : (2 * j - 1) * u ≤ 13 * 22 := Nat.mul_le_mul (by omega) hu
        change _ < 2130706433; omega)
    have hcnt := Lower6960.ThirdPole.count_common p (by decide) A B u u u u
      hA_axis hB_axis hposAB hres_ne hsmall (Bad.image coord) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hA0, hB0⟩ := hboth γ hγ
        refine ⟨atX (scalar γ), ?_, ?_⟩
        · simpa [coord, graphEval] using hA0
        · simpa [coord, graphEval] using hB0)
    rw [hcard_im] at hcnt
    calc
      Bad.card ≤ (B.natDegree * u + A.natDegree * u) + p * (B.natDegree * u + A.natDegree * u) := hcnt
      _ ≤ (2 * j - 1) * u + p * ((2 * j - 1) * u) :=
          Nat.add_le_add hdeg_sum (Nat.mul_le_mul_left p hdeg_sum)
      _ = (2 * j - 1) * u * (p + 1) := by ring
  · -- Both `A` and `B` have `Y₀`-degree `0`, so `A = C c` with `c ≠ 0` and `graphEval (label γ) c = 0`!
    push_neg at hposAB
    obtain ⟨hA0, _⟩ := hposAB
    have hAc : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hA0
    have hc_ne : A.coeff 0 ≠ 0 := fun hz => hAne (by rw [hAc, hz, map_zero])
    have hsmall : u < p := by change u < 2130706433; omega
    have hcnt := K1_10.frobenius_coefficient_exception_count p u u (by decide) (A.coeff 0) hc_ne
      (hA_axis 0).1 hsmall (hA_axis 0).2 (Bad.image coord) (by
        intro z hz
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
        have h := (hboth γ hγ).1
        rw [hAc, Polynomial.map_C, Polynomial.eval_C] at h
        simpa [coord, graphEval] using h)
    rw [hcard_im] at hcnt
    have hle : 1 ≤ 2 * j - 1 := by omega
    have hmul : u ≤ (2 * j - 1) * u := Nat.le_mul_of_pos_left u hle
    calc
      Bad.card ≤ u + p * u := hcnt
      _ = u * (p + 1) := by ring
      _ ≤ (2 * j - 1) * u * (p + 1) := Nat.mul_le_mul_right (p + 1) hmul

/-- **End-to-End Case-B Cardinality Cap for All 6 Small Rescue Rectangles at `69.61` (`caseB_small_rect_card_le_6961`)**:
    In Case B (`jacDet = 0`), for ANY small rectangle `r : SmallRect61`, any irreducible `G` with
    `G.natDegree = 1`, `UsesSeed G`, `RowCaps G ⟨0, j, 1, u⟩`, `r.In j u`, and any family `Γ`
    with `F : P1.FamilyAt 179818 M Γ` and `M.overhead.toNat ≤ 2449`:
      `(Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ) = 0)).card ≤ r.cap ≤ 37_710_000_000_000_000`. -/
theorem caseB_small_rect_card_le_6961 {uM : P1.Words} {deleted : Finset I}
    {M : P1.ModelAt 33579 uM deleted} {Γ : Finset K} (F : P1.FamilyAt 179818 M Γ)
    (hhi : M.overhead.toNat ≤ 2449)
    {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1) (hseed : UsesSeed G)
    {r : SmallRect61} {j u : ℕ} (hin : r.In j u) (hG : RowCaps G ⟨0, j, 1, u⟩)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0) :
    (Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0).card ≤ r.cap ∧
    (Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0).card ≤ 37_710_000_000_000_000 := by
  classical
  obtain ⟨hj1, hj7, _, hu22, hB, hJ, hC, h143⟩ := smallRect61_bounds hin
  obtain ⟨Q, hOrder, hVanish⟩ :=
    caseB_diffPoly_witness hIrr hdegG hseed hj1 hu22 hG hdet hB hJ hC
  let ΓG := Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0
  let Bad := Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0 ∧
    jetAt (prolongA G) (M.label γ) (F.scalar γ) = 0
  let Good := ΓG \ Bad
  have hBad_sub : Bad ⊆ ΓG := fun γ hγ => by
    obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hγ
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  have hsplit : Good.card + Bad.card = ΓG.card := Finset.card_sdiff_add_card_eq_card hBad_sub
  -- Bound `Bad.card ≤ 143 * (p + 1)`!
  have hBad_le : Bad.card ≤ 143 * (p + 1) := by
    have h1 := caseB_leading_zero_card_le hIrr hdegG hj1 hj7 hu22 hG Γ M.label
      (fun _ _ h => sub_left_inj.mp h) F.scalar
    exact h1.trans (Nat.mul_le_mul_right (p + 1) h143)
  -- Bound `Good.card ≤ tariffHigh 179818 r.box` via `F.distinct` + `order_two_card_le_high133721`!
  let Sgood := Good.image F.scalar
  have hGood_sub : Good ⊆ Γ := (Finset.sdiff_subset).trans (Finset.filter_subset _ _)
  have hSgood_card : Sgood.card = Good.card :=
    Finset.card_image_of_injOn (F.distinct.mono hGood_sub)
  have hSgood_close : (Sgood : Set (Polynomial K)) ⊆ closeHigh 179818 M.word := by
    intro f hf
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hf)
    have hγΓ : γ ∈ Γ := hGood_sub hγ
    let B := F.mark γ hγΓ
    refine ⟨?_, ?_⟩
    · rcases B.scalar_degree with h0 | hdeg
      · rw [h0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
      · by_cases hz : F.scalar γ = 0
        · rw [hz, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
        · rw [Polynomial.degree_eq_natDegree hz]
          change ((F.scalar γ).natDegree : WithBot ℕ) < (kHigh : WithBot ℕ)
          exact WithBot.coe_lt_coe.mpr (by
            change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hdeg
            have : M.overhead ≤ 2449 := by omega
            change (F.scalar γ).natDegree < 133721
            omega)
    · refine B.bad.agreement.trans (Finset.card_le_card fun i hi => ?_)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, B.scalar_hits i hi⟩
  have hSgood_roots : ∀ f ∈ Sgood, differentialSpecialization Q f = 0 := by
    intro f hf
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hγG, hnotBad⟩ := Finset.mem_sdiff.mp hγ
    obtain ⟨hγΓ, hGz⟩ := Finset.mem_filter.mp hγG
    have hAz : jetAt (prolongA G) (M.label γ) (F.scalar γ) ≠ 0 :=
      fun h0 => hnotBad (Finset.mem_filter.mpr ⟨hγΓ, hGz, h0⟩)
    exact hVanish (M.label γ) (F.scalar γ) hGz hAz
  have hGood_le : Good.card ≤ tariffHigh 179818 r.box := by
    rw [← hSgood_card]
    exact order_two_card_le_high133721 agreementOK_6961 (by decide) (smallRect61_boxOK r)
      hOrder Sgood hSgood_close hSgood_roots
  have hcap : ΓG.card ≤ r.cap := by
    have htot := smallRect61_tariff_le r
    omega
  exact ⟨hcap, hcap.trans (smallRect61_cap_le r)⟩

#print axioms caseB_diffPoly_witness
#print axioms caseB_leading_zero_card_le
#print axioms caseB_small_rect_card_le_6961

end
end TwoJetCaseBBridge
