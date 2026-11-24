import ProximityPrize.SubmissionLower.TwoJetCaseAFXRank
import ProximityPrize.SubmissionLower.TwoJetCaseADriver

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

/-!
# End-to-End 2-Jet Case-A Prolongation Avoidance at `69.61` (`TwoJetCaseAFX`)

Combines:
- `TwoJetCaseAFXCore` (`telescope2`, `leading_bound_2jet`)
- `TwoJetCaseAFXRank` (`physRank2_m59`)
- `PoleBound2Jet` (`pole_bound_2jet`)
- `TwoJetCaseADriver` (`fractionRingFieldDerivs`, `wordVanishes_of_all_complete2_eval_zero`,
  `eval_zero_of_prolongSubst_dvd`)
- `TwoJetCaseAKernel` (`pow_collapse_of_wordVanishes`, `zero_of_deg_le_and_order_gt`)

to prove `caseA_avoidance_6961`: for every `h ∈ [2327, 2449]` and every linear-in-`Y₁` prime
`G : K1_14.Jet` (`G.natDegree = 1`) with Case-A nonzero seed Jacobian determinant
`jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) ≠ 0`, there exist `W < 59 * 179818` and
`P₀ ∈ complete2 Crt word (shape2_m59 399) W` such that
  `¬ G ∣ prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀)`.
-/

namespace TwoJetCaseAFX

section FastNat61

private def natSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => natSum n f + f n

private def natSumBlock (start : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => natSumBlock start n f + f (start + n)

private theorem natSumBlock_add (a b c : ℕ) (f : ℕ → ℕ) :
    natSumBlock a (b + c) f = natSumBlock a b f + natSumBlock (a + b) c f := by
  induction c with
  | zero => simp [natSumBlock]
  | succ c ih =>
    rw [← Nat.add_assoc, natSumBlock, natSumBlock, ih, Nat.add_assoc, Nat.add_assoc]

private theorem natSum_eq_block (n : ℕ) (f : ℕ → ℕ) : natSum n f = natSumBlock 0 n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natSum, natSumBlock, ih]

private def gradeCount61 (q : ℕ) : ℕ :=
  natSum 11 fun e₂ => if e₂ ≤ q then min (q - e₂) (24 - 2 * e₂) + 1 else 0

private def colCount61 (t q : ℕ) : ℕ :=
  natSum 11 fun e₂ =>
    if e₂ ≤ q ∧ t + 2 * e₂ ≤ 127 then
      min (min (q - e₂) (24 - 2 * e₂)) (127 - t - 2 * e₂) + 1 - (24 - t - 2 * e₂)
    else 0

private def pivCount61 (t q : ℕ) : ℕ :=
  natSum 11 fun e₂ =>
    if e₂ ≤ q ∧ t + q + 2 * e₂ ≤ 127 then
      min (min (q - e₂) (24 - 2 * e₂)) (127 - t - q - 2 * e₂) + 1 - (24 - t - 2 * e₂)
    else 0

private def optK61 (t : ℕ) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
    43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
    62, 63, 64, 65, 66, 67, 68, 69, 69, 70, 71, 72, 72, 73, 74, 74, 75, 75, 76,
    76, 77, 77, 77, 77, 77, 78, 78, 78, 78, 78, 78, 78, 78, 78, 79, 79, 79, 79,
    79, 79, 79, 79, 79, 79, 79, 79]).getD t 0

private def offsetUpper61 (t : ℕ) : ℕ :=
  let R := natSum 81 (pivCount61 t)
  let k := optK61 t
  R * k + natSum 81 (fun q => (q - k) * colCount61 t q) - natSum 81 (fun q => q * pivCount61 t q)

private theorem optK61_lt_81 : ∀ t : Fin 128, optK61 t.val < 81 := by decide +kernel
private theorem poleRows2_nat_val : natSum 81 (fun q => (104 - q) * gradeCount61 q) = 662695 := by decide +kernel
private theorem box_card_val : natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => 81 - e₁ - e₂)) = 11385 := by decide +kernel
private theorem box_q_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ =>
      (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂))) = 521345 := by decide +kernel
private theorem box_v_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => (81 - e₁ - e₂) * (e₁ + 2 * e₂))) = 173635 := by decide +kernel
private theorem box_12_val :
    natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ => (81 - e₁ - e₂) * (e₁ + e₂))) = 131890 := by decide +kernel
private theorem offsetUpper_val : natSum 128 offsetUpper61 = 9858694 := by decide +kernel

end FastNat61

noncomputable section

open Polynomial Finset
open K1 (I)
open K1_14 (L FX Seeds Equation Jet triangle)
open K1_14_1 (SeedPoly seedWeight PoleData CRTLift)
open K1_14_1_3 (sourceX)
open K1_14_2_2 (RowCaps)
open PoleMoment2Jet (Shape2 jetIdx poleRows2 poleCredit2 groupedPoleMoment2)
open PoleBound2Jet (Source2 coeffAt2 trueEligible2 ambient2 contacted2 complete2 pole_bound_2jet)
open TwoJetShift (boundedShiftExp)
open TwoJetRescueBridge (Jet2 centerEval2 evaluated2 prolongSubst)
open TwoJetCaseAKernel (FieldDerivs jacDet shift2 polyBivar embed2 zero_of_deg_le_and_order_gt
  pow_collapse_of_wordVanishes)
open TwoJetCaseADriver (BaseRing mapDeriv mapDeriv_coeff mapDeriv_zero mapDeriv_add mapDeriv_mul
  fracDeriv fracDeriv_algebraMap fracDeriv_add fracDeriv_mul fractionRingFieldDerivs
  fractionRingFieldDerivs_compat wordVanishes_of_all_complete2_eval_zero
  eval_zero_of_prolongSubst_dvd)
open scoped BigOperators Polynomial Classical

/-! ## 1. Field Embedding `Equation →+* FractionRing BaseRing` & `Jet2 →+* E[Y₁][Y₂]` -/

abbrev EField := FractionRing BaseRing

private def sourceXHom : Polynomial L →+* Polynomial SeedPoly :=
  Polynomial.mapRingHom MvPolynomial.C

private theorem sourceXHom_eq (p : Polynomial L) : sourceXHom p = sourceX p := rfl

private theorem sourceX_injective : Function.Injective sourceXHom := by
  intro p q hpq
  ext a
  have h := congrArg (fun r : Polynomial SeedPoly => (r.coeff a).coeff 0) hpq
  simpa [sourceXHom, Polynomial.coeff_map, MvPolynomial.coeff_C] using h

private def fxToE : FX →+* EField :=
  IsFractionRing.lift
    (g := (algebraMap BaseRing EField).comp (Polynomial.C.comp sourceXHom))
    ((IsFractionRing.injective BaseRing EField).comp
      (Polynomial.C_injective.comp sourceX_injective))

private theorem fxToE_algebraMap (p : Polynomial L) :
    fxToE (algebraMap (Polynomial L) FX p) =
      algebraMap BaseRing EField (Polynomial.C (sourceX p)) :=
  IsFractionRing.lift_algebraMap _ p

def seedsToE : Seeds →+* EField :=
  MvPolynomial.eval₂Hom fxToE
    (fun i => algebraMap BaseRing EField (Polynomial.C (Polynomial.C (MvPolynomial.X i))))

def seedsY0ToE : Equation →+* EField :=
  Polynomial.eval₂RingHom seedsToE (algebraMap BaseRing EField Polynomial.X)

def jet2ToE : Jet2 →+* Polynomial (Polynomial EField) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom seedsY0ToE)

private def centerBaseY0 : BaseRing →+* Equation :=
  Polynomial.mapRingHom (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
    (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X)))

private theorem seedsY0ToE_comp_centerBaseY0 :
    seedsY0ToE.comp centerBaseY0 = algebraMap BaseRing EField := by
  apply Polynomial.ringHom_ext
  · intro q
    simp only [RingHom.comp_apply, centerBaseY0, Polynomial.coe_mapRingHom, Polynomial.map_C,
      seedsY0ToE, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ =>
      rw [Polynomial.eval₂_add, map_add, Polynomial.C_add, map_add, ih₁, ih₂]
    | monomial n s =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, map_mul, map_pow,
        Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      simp only [seedsToE, MvPolynomial.eval₂Hom_C, fxToE_algebraMap, Polynomial.map_pow,
        sourceX, Polynomial.map_X]
      congr 1
      induction s using MvPolynomial.induction_on with
      | C c =>
        have hC : MvPolynomial.map (algebraMap L FX) (MvPolynomial.C c : SeedPoly) =
            MvPolynomial.C (algebraMap (Polynomial L) FX (Polynomial.C c)) := by
          rw [MvPolynomial.map_C]; rfl
        rw [hC, MvPolynomial.eval₂Hom_C, fxToE_algebraMap]
        simp [sourceX]
      | add p₁ p₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
      | mul_X p i ih =>
        rw [map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.eval₂Hom_X', ih]
        rw [Polynomial.C_mul, Polynomial.C_mul, map_mul]
  · simp [centerBaseY0, seedsY0ToE]

private theorem fxToE_mul_denom (a : FX) :
    ∃ d : Polynomial L, d ≠ 0 ∧ ∃ n : Polynomial L,
      algebraMap (Polynomial L) FX d * a = algebraMap (Polynomial L) FX n := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial L)) a
  refine ⟨d.1, nonZeroDivisors.ne_zero d.2, n, ?_⟩
  simpa [mul_comm] using hnd

theorem seedsY0ToE_injective : Function.Injective seedsY0ToE := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  -- Clear denominators of all FX-coefficients in `q : Polynomial Seeds`
  let coeffs : Finset FX :=
    q.support.biUnion fun i => (q.coeff i).support.image fun m => (q.coeff i).coeff m
  have hex : ∀ c ∈ coeffs, ∃ d : Polynomial L, d ≠ 0 ∧
      ∃ n : Polynomial L, algebraMap (Polynomial L) FX d * c = algebraMap (Polynomial L) FX n :=
    fun c _ => fxToE_mul_denom c
  choose den hden_ne num hnum using fun c : coeffs => fxToE_mul_denom c.1
  let D : Polynomial L := ∏ c : coeffs, den c
  have hD_ne : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hden_ne c
  -- Every coefficient of `D • q` lies in `algebraMap (Polynomial L) FX`
  have hclear : ∀ i m, ∃ p : Polynomial L,
      algebraMap (Polynomial L) FX D * ((q.coeff i).coeff m) = algebraMap (Polynomial L) FX p := by
    intro i m
    by_cases h0 : (q.coeff i).coeff m = 0
    · exact ⟨0, by simp [h0]⟩
    · have hmem : (q.coeff i).coeff m ∈ coeffs := by
        refine Finset.mem_biUnion.mpr ⟨i, Polynomial.mem_support_iff.mpr (fun hz => h0 (by simp [hz])),
          Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr h0, rfl⟩⟩
      let c : coeffs := ⟨(q.coeff i).coeff m, hmem⟩
      let D' : Polynomial L := ∏ c' ∈ Finset.univ.erase c, den c'
      have hD_split : D = D' * den c := by
        dsimp only [D, D']
        rw [Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      refine ⟨D' * num c, ?_⟩
      rw [hD_split, map_mul, map_mul, mul_assoc, hnum c]
  -- Lift `D • q` to `r : BaseRing` with `centerBaseY0 r = C (MvPolynomial.C (algebraMap D)) * q`
  choose poly hpoly using hclear
  let mkSeedPoly (i : ℕ) : Polynomial SeedPoly :=
    ∑ m ∈ (q.coeff i).support, (poly i m).map MvPolynomial.C * Polynomial.C (MvPolynomial.monomial m 1)
  let r : BaseRing := ∑ i ∈ q.support, Polynomial.monomial i (mkSeedPoly i)
  have hr_eq : centerBaseY0 r = Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX D)) * q := by
    have hcoeff_r : ∀ i, (centerBaseY0 r).coeff i =
        MvPolynomial.C (algebraMap (Polynomial L) FX D) * q.coeff i := by
      intro i
      rw [centerBaseY0, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      have hri : r.coeff i = if i ∈ q.support then mkSeedPoly i else 0 := by
        simp only [r, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply,
          Finset.sum_ite_eq']
      rw [hri]
      split_ifs with hi
      · apply MvPolynomial.ext; intro m
        simp only [mkSeedPoly, map_sum, map_mul, MvPolynomial.coeff_sum]
        have hterm (m' : Fin 2 →₀ ℕ) :
            (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              ((poly i m').map MvPolynomial.C) *
            Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              (Polynomial.C (MvPolynomial.monomial m' 1))) =
            MvPolynomial.monomial m' (algebraMap (Polynomial L) FX (poly i m')) := by
          have hev : Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap L FX))
              (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
              ((poly i m').map (MvPolynomial.C : L →+* SeedPoly)) =
              MvPolynomial.C (algebraMap (Polynomial L) FX (poly i m')) := by
            induction poly i m' using Polynomial.induction_on' with
            | add p₁ p₂ ih₁ ih₂ => simp only [Polynomial.map_add, map_add, ih₁, ih₂]
            | monomial n c =>
              simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
                Polynomial.map_C, Polynomial.map_X, map_mul, map_pow, Polynomial.coe_eval₂RingHom,
                Polynomial.eval₂_C, Polynomial.eval₂_X, MvPolynomial.map_C]
              rfl
          rw [hev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.map_monomial,
            map_one, MvPolynomial.C_mul_monomial, mul_one]
        simp_rw [hterm, MvPolynomial.coeff_monomial]
        rw [Finset.sum_ite_eq', MvPolynomial.coeff_C_mul]
        split_ifs with hm
        · exact (hpoly i m).symm
        · have h0 : (q.coeff i).coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
          rw [h0, mul_zero]
      · rw [map_zero, Polynomial.notMem_support_iff.mp hi, mul_zero]
    ext i; rw [hcoeff_r i, Polynomial.coeff_C_mul]
  have hr0 : algebraMap BaseRing EField r = 0 := by
    rw [← seedsY0ToE_comp_centerBaseY0, RingHom.comp_apply, hr_eq, map_mul, hq, mul_zero]
  have hr_zero : r = 0 := IsFractionRing.injective BaseRing EField (hr0.trans (map_zero _).symm)
  rw [hr_zero, map_zero] at hr_eq
  have hD_ne' : Polynomial.C (MvPolynomial.C (algebraMap (Polynomial L) FX D)) ≠ (0 : Equation) := by
    intro hz
    have h1 : algebraMap (Polynomial L) FX D = 0 :=
      MvPolynomial.C_eq_zero.mp (Polynomial.C_eq_zero.mp hz)
    exact hD_ne (IsFractionRing.injective (Polynomial L) FX (h1.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hr_eq.symm).resolve_left hD_ne'

theorem jet2ToE_centerEval2 (Q : Source2) :
    jet2ToE (centerEval2 Q) = embed2 (algebraMap BaseRing EField) Q := by
  have hbase_eq :
      (Polynomial.mapRingHom
        (Polynomial.eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
          (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
          (fun _ => Commute.all _ _)).toRingHom) = centerBaseY0 := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply MvPolynomial.ringHom_ext
        · intro a; simp [centerBaseY0]
        · intro i; simp [centerBaseY0]
      · simp [centerBaseY0]
    · simp [centerBaseY0]
  have hcomp : (jet2ToE.comp centerEval2.toRingHom) = embed2 (algebraMap BaseRing EField) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext; intro q
        have hq := RingHom.congr_fun seedsY0ToE_comp_centerBaseY0 q
        have hq' : seedsY0ToE
            (Polynomial.map
              (Polynomial.eval₂AlgHom (MvPolynomial.mapAlgHom (Algebra.ofId L FX))
                (MvPolynomial.C (algebraMap (Polynomial L) FX Polynomial.X))
                (fun _ => Commute.all _ _)).toRingHom q) =
            algebraMap BaseRing EField q := by
          have := congrArg (fun f : BaseRing →+* Equation => seedsY0ToE (f q)) hbase_eq
          exact this.trans hq
        simpa [jet2ToE, centerEval2, K1_14_1.centerEval, embed2] using congrArg (Polynomial.C ∘ Polynomial.C) hq'
      · simp [jet2ToE, centerEval2, K1_14_1.centerEval, embed2]
    · simp [jet2ToE, centerEval2, K1_14_1.centerEval, embed2]
  exact RingHom.congr_fun hcomp Q

theorem jet2ToE_smul (c : FX) (P : Jet2) :
    jet2ToE (c • P) = Polynomial.C (Polynomial.C (fxToE c)) * jet2ToE P := by
  ext e₂ e₁
  simp only [jet2ToE, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C_mul]
  have hsmul : ((c • P).coeff e₂).coeff e₁ = Polynomial.C (MvPolynomial.C c) * ((P.coeff e₂).coeff e₁) := by
    rw [Algebra.smul_def]
    simp [MvPolynomial.algebraMap_eq]
  rw [hsmul, map_mul]
  congr 1
  simp [seedsY0ToE, seedsToE]

theorem jet2ToE_eval₂_comm (α₁ α₂ : EField) (Q : Source2) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom seedsY0ToE α₁) α₂ (centerEval2 Q) =
      Polynomial.eval₂ (Polynomial.evalRingHom α₁) α₂ (embed2 (algebraMap BaseRing EField) Q) := by
  rw [← jet2ToE_centerEval2 Q]
  have h : (Polynomial.eval₂RingHom (Polynomial.evalRingHom α₁) α₂).comp jet2ToE =
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom seedsY0ToE α₁) α₂ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext; intro c; simp [jet2ToE]
      · simp [jet2ToE]
    · simp [jet2ToE]
  exact (RingHom.congr_fun h (centerEval2 Q)).symm

/-! ## 2. 1-Jet Prolongation `G^(1) = prolongA G * Y₂ + prolongB1 G` & `RowCaps` -/

def derivFX : FX → FX :=
  fracDeriv (fun p : Polynomial L => p.derivative)
    (fun _ _ => Polynomial.derivative_add)
    (fun _ _ => Polynomial.derivative_mul)

theorem derivFX_zero : derivFX 0 = 0 := by
  have h := fracDeriv_algebraMap (fun p : Polynomial L => p.derivative)
    (fun _ _ => Polynomial.derivative_add) (fun _ _ => Polynomial.derivative_mul) 0
  rw [map_zero, Polynomial.derivative_zero, map_zero] at h
  exact h

theorem derivFX_add (x y : FX) : derivFX (x + y) = derivFX x + derivFX y :=
  fracDeriv_add _ _ _ x y

theorem derivFX_mul (x y : FX) : derivFX (x * y) = derivFX x * y + x * derivFX y :=
  fracDeriv_mul _ _ _ x y

theorem derivFX_algebraMap (p : Polynomial L) :
    derivFX (algebraMap (Polynomial L) FX p) = algebraMap (Polynomial L) FX p.derivative :=
  fracDeriv_algebraMap _ _ _ p

def derivSeedsX (p : Seeds) : Seeds :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (derivFX (p.coeff m))

theorem derivSeedsX_coeff (p : Seeds) (m : Fin 2 →₀ ℕ) :
    (derivSeedsX p).coeff m = derivFX (p.coeff m) := by
  classical
  dsimp only [derivSeedsX]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, derivFX_zero]

theorem derivSeedsX_zero : derivSeedsX 0 = 0 := by
  ext m; simp [derivSeedsX_coeff, derivFX_zero]

theorem derivSeedsX_add (p q : Seeds) : derivSeedsX (p + q) = derivSeedsX p + derivSeedsX q := by
  ext m; simp [derivSeedsX_coeff, derivFX_add]

theorem derivSeedsX_mul (p q : Seeds) :
    derivSeedsX (p * q) = derivSeedsX p * q + p * derivSeedsX q := by
  classical
  have hd_sum : ∀ (s : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) (f : _ → FX),
      derivFX (∑ i ∈ s, f i) = ∑ i ∈ s, derivFX (f i) := by
    intro s f
    induction s using Finset.induction with
    | empty => simp [derivFX_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, derivFX_add, ih]
  ext m
  rw [derivSeedsX_coeff, MvPolynomial.coeff_add, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul, hd_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [derivFX_mul, derivSeedsX_coeff, derivSeedsX_coeff]

theorem derivSeedsX_totalDegree_le (p : Seeds) : (derivSeedsX p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hne : p.coeff m ≠ 0 := by
    intro hz
    have h0 := MvPolynomial.mem_support_iff.mp hm
    rw [derivSeedsX_coeff, hz, derivFX_zero] at h0
    exact h0 rfl
  exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

def jetDerivX (G : Jet) : Jet :=
  mapDeriv (mapDeriv derivSeedsX) G

def jetDerivY0 (G : Jet) : Jet :=
  mapDeriv Polynomial.derivative G

def prolongA (G : Jet) : Jet :=
  2 * Polynomial.C (G.coeff 1)

def prolongB1 (G : Jet) : Jet :=
  jetDerivX G + jetDerivY0 G * Polynomial.X

theorem jetDerivX_coeff (G : Jet) (j i : ℕ) :
    ((jetDerivX G).coeff j).coeff i = derivSeedsX ((G.coeff j).coeff i) := by
  rw [jetDerivX, mapDeriv_coeff (mapDeriv_zero derivSeedsX_zero), mapDeriv_coeff derivSeedsX_zero]

theorem jetDerivY0_coeff (G : Jet) (j i : ℕ) :
    ((jetDerivY0 G).coeff j).coeff i = ((G.coeff j).coeff (i + 1)) * ((i + 1 : ℕ) : Seeds) := by
  rw [jetDerivY0, mapDeriv_coeff Polynomial.derivative_zero, Polynomial.coeff_derivative]
  push_cast; rfl

theorem rowCaps_add {P Q : Jet} {s : K1_14.Shape} (hP : RowCaps P s) (hQ : RowCaps Q s) :
    RowCaps (P + Q) s := by
  intro j i hne
  simp only [Polynomial.coeff_add] at hne ⊢
  by_cases hp : (P.coeff j).coeff i = 0
  · rw [hp, zero_add] at hne ⊢; exact hQ j i hne
  · by_cases hq : (Q.coeff j).coeff i = 0
    · rw [hq, add_zero]; exact hP j i hp
    · have h1 := hP j i hp
      have h2 := hQ j i hq
      exact ⟨h1.1, h1.2.1, (MvPolynomial.totalDegree_add _ _).trans (max_le h1.2.2 h2.2.2)⟩

theorem rowCaps_neg {P : Jet} {s : K1_14.Shape} (hP : RowCaps P s) : RowCaps (-P) s := by
  intro j i hne
  simp only [Polynomial.coeff_neg, neg_ne_zero] at hne
  have h := hP j i hne
  refine ⟨h.1, h.2.1, ?_⟩
  simp only [Polynomial.coeff_neg, MvPolynomial.totalDegree, MvPolynomial.support_neg]
  exact h.2.2

theorem rowCaps_mul {P Q : Jet} {s t : K1_14.Shape} (hP : RowCaps P s) (hQ : RowCaps Q t) :
    RowCaps (P * Q) ⟨0, s.B + t.B, s.J + t.J, s.U + t.U⟩ := by
  intro j i hne
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff] at hne
  obtain ⟨⟨j₁, j₂⟩, hj, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Polynomial.coeff_mul] at hne1
  obtain ⟨⟨i₁, i₂⟩, hi, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
  have h1 := hP j₁ i₁ (left_ne_zero_of_mul hne2)
  have h2 := hQ j₂ i₂ (right_ne_zero_of_mul hne2)
  have hje := Finset.mem_antidiagonal.mp hj
  have hie := Finset.mem_antidiagonal.mp hi
  dsimp only
  refine ⟨by omega, by omega, ?_⟩
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  refine MvPolynomial.totalDegree_finsetSum_le fun ⟨a₁, a₂⟩ _ => ?_
  rw [Polynomial.coeff_mul]
  refine MvPolynomial.totalDegree_finsetSum_le fun ⟨b₁, b₂⟩ _ => ?_
  by_cases hz : ((P.coeff a₁).coeff b₁) * ((Q.coeff a₂).coeff b₂) = 0
  · simp [hz]
  · have ha1 := hP a₁ b₁ (left_ne_zero_of_mul hz)
    have ha2 := hQ a₂ b₂ (right_ne_zero_of_mul hz)
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha1.2.2 ha2.2.2)

theorem rowCaps_pow {P : Jet} {s : K1_14.Shape} (hP : RowCaps P s) (n : ℕ) :
    RowCaps (P ^ n) ⟨0, n * s.B, n * s.J, n * s.U⟩ := by
  induction n with
  | zero =>
    intro j i hne
    rw [pow_zero] at hne
    by_cases hj : j = 0
    · subst hj
      by_cases hi : i = 0
      · subst hi; simp
      · simp [Polynomial.coeff_one, hi] at hne
    · simp [Polynomial.coeff_one, hj] at hne
  | succ n ih =>
    rw [pow_succ]
    have hm := rowCaps_mul ih hP
    intro j i hne
    have ⟨h1, h2, h3⟩ := hm j i hne
    exact ⟨by simp only [Nat.succ_mul]; omega, by simp only [Nat.succ_mul]; omega,
      by simp only [Nat.succ_mul]; omega⟩

theorem rowCaps_mono {P : Jet} {s t : K1_14.Shape} (hP : RowCaps P s)
    (hB : s.B ≤ t.B) (hJ : s.J ≤ t.J) (hU : s.U ≤ t.U) : RowCaps P t := by
  intro j i hne
  have ⟨h1, h2, h3⟩ := hP j i hne
  exact ⟨h1.trans hB, h2.trans hJ, h3.trans hU⟩

theorem prolongA_rowCaps {G : Jet} {j u : ℕ} (hj : 1 ≤ j) (hG : RowCaps G ⟨0, j, 1, u⟩) :
    RowCaps (prolongA G) ⟨0, j - 1, 0, u⟩ := by
  intro k i hne
  have h2 : prolongA G = Polynomial.C (2 * G.coeff 1) := by
    simp [prolongA, map_ofNat]
  rw [h2, Polynomial.coeff_C] at hne ⊢
  split_ifs at hne ⊢ with hk
  · subst hk
    rw [show (2 : Equation) = Polynomial.C (2 : Seeds) from (map_ofNat Polynomial.C 2).symm,
      Polynomial.coeff_C_mul] at hne ⊢
    have hc := hG 1 i (right_ne_zero_of_mul hne)
    dsimp only at hc ⊢
    refine ⟨by omega, le_rfl, ?_⟩
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      have h2d : (2 : Seeds).totalDegree = 0 := by
        rw [show (2 : Seeds) = MvPolynomial.C (2 : FX) from (map_ofNat MvPolynomial.C 2).symm,
          MvPolynomial.totalDegree_C]
      rw [h2d, zero_add]; exact hc.2.2)
  · simp at hne

theorem prolongB1_rowCaps {G : Jet} {j u : ℕ} (hG : RowCaps G ⟨0, j, 1, u⟩) :
    RowCaps (prolongB1 G) ⟨0, j, 2, u⟩ := by
  apply rowCaps_add
  · intro k i hne
    rw [jetDerivX_coeff] at hne ⊢
    have hc : (G.coeff k).coeff i ≠ 0 := fun hz => hne (by rw [hz, derivSeedsX_zero])
    have ⟨h1, h2, h3⟩ := hG k i hc
    dsimp only at h1 h2 h3 ⊢
    exact ⟨h1, by omega, (derivSeedsX_totalDegree_le _).trans h3⟩
  · intro k i hne
    cases k with
    | zero => simp at hne
    | succ k' =>
      rw [Polynomial.coeff_mul_X, jetDerivY0_coeff] at hne ⊢
      have hc : (G.coeff k').coeff (i + 1) ≠ 0 := left_ne_zero_of_mul hne
      have ⟨h1, h2, h3⟩ := hG k' (i + 1) hc
      dsimp only at h1 h2 h3 ⊢
      refine ⟨by omega, by omega, ?_⟩
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        have hnd : ((i + 1 : ℕ) : Seeds).totalDegree = 0 := by
          rw [← MvPolynomial.C_eq_natCast, MvPolynomial.totalDegree_C]
        rw [hnd, add_zero]; exact h3)

/-- Exact `RowCaps` of `prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀)` for
    `P₀ ∈ ambient2 h (shape2_m59 399) W`: `⟨0, 80 + 10*(j - 1), 24, 399 + 10*u⟩`! -/
theorem prolongSubst_rowCaps {h W j u : ℕ} (hj : 1 ≤ j) {G : Jet} (hG : RowCaps G ⟨0, j, 1, u⟩)
    {P₀ : Source2} (hP : P₀ ∈ ambient2 h (shape2_m59 399) W) :
    RowCaps (prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀))
      ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩ := by
  unfold prolongSubst
  have hsum : ∀ (S : Finset ℕ) (f : ℕ → Jet),
      (∀ e₂ ∈ S, RowCaps (f e₂) ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩) →
      RowCaps (∑ e₂ ∈ S, f e₂) ⟨0, 80 + 10 * (j - 1), 24, 399 + 10 * u⟩ := by
    intro S f hf
    induction S using Finset.induction with
    | empty => intro k i hne; simp at hne
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact rowCaps_add (hf a (Finset.mem_insert_self a S))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
  apply hsum
  intro e₂ he₂
  have he₂_le : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  have hPcoeff : RowCaps ((centerEval2 P₀).coeff e₂) ⟨0, 80 - e₂, 24 - 2 * e₂, 399⟩ := by
    intro e₁ e₀ hne
    rw [centerEval2_eq_tripleMap, tripleMap_coeff] at hne
    have hcoeff_ne : (((P₀.coeff e₂).coeff e₁).coeff e₀) ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    obtain ⟨a, ha⟩ : ∃ a, ((((P₀.coeff e₂).coeff e₁).coeff e₀).coeff a) ≠ 0 := by
      by_contra! hall; exact hcoeff_ne (Polynomial.ext fun a => by simpa using hall a)
    obtain ⟨e, he⟩ : ∃ e, coeffAt2 P₀ e₂ e₁ e₀ a e ≠ 0 := by
      by_contra! hall
      exact ha (MvPolynomial.ext _ _ fun e => by simpa [coeffAt2, PoleMoment2Jet.sourceCoeff2] using hall e)
    have hel : trueEligible2 h (shape2_m59 399) W e₂ e₁ e₀ a e := by
      by_contra hnot; exact he (hP e₂ e₁ e₀ a e hnot)
    obtain ⟨hB, hJ, _, _, _⟩ := hel
    dsimp only [shape2_m59, jetIdx] at hB hJ ⊢
    refine ⟨by omega, by omega, ?_⟩
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    intro m hm
    by_contra hbig
    have h0 : ((((centerEval2 P₀).coeff e₂).coeff e₁).coeff e₀).coeff m = 0 := by
      change jetCoords2 (centerEval2 P₀) (e₂, e₁, e₀, m) = 0
      rw [coords2_center]
      have hsc0 : sourceCoord2 P₀ (e₂, e₁, e₀, m) = 0 := by
        apply Polynomial.ext; intro c
        rw [sourceCoord2_coeff, Polynomial.coeff_zero]
        exact hP e₂ e₁ e₀ c m (fun hel' => hbig hel'.2.2.2.1)
      rw [hsc0, map_zero]
    exact (MvPolynomial.mem_support_iff.mp hm) h0
  have hB1 := rowCaps_pow (rowCaps_neg (prolongB1_rowCaps hG)) e₂
  have hA := rowCaps_pow (prolongA_rowCaps hj hG) (10 - e₂)
  have hmul := rowCaps_mul (rowCaps_mul hPcoeff hB1) hA
  apply rowCaps_mono hmul
  · have h1 : e₂ * j + (10 - e₂) * (j - 1) = e₂ + 10 * (j - 1) := by
      zify [hj, he₂_le]; ring
    dsimp only; omega
  · dsimp only; omega
  · have h2 : e₂ * u + (10 - e₂) * u = 10 * u := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' he₂_le]
    dsimp only; omega

/-! ## 3. Graded `FX`-Kernel Finrank Bound & Exact Linear-in-`h` Surplus -/

def boxPos2 : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range 11) ×ˢ ((Finset.range 25) ×ˢ (Finset.range 81))).filter fun m =>
    m.2.2 + m.2.1 + m.1 ≤ 80 ∧ jetIdx m.2.1 m.1 ≤ 24 ∧ m.1 ≤ 10

def highPos2 (h W k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  boxPos2.filter fun m =>
    (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧ k < m.2.1 + m.1

theorem mem_boxPos2 {m : ℕ × ℕ × ℕ} :
    m ∈ boxPos2 ↔ m.2.2 + m.2.1 + m.1 ≤ 80 ∧ jetIdx m.2.1 m.1 ≤ 24 ∧ m.1 ≤ 10 := by
  rcases m with ⟨e₂, e₁, e₀⟩
  simp only [boxPos2, Finset.mem_filter, Finset.mem_product, Finset.mem_range, jetIdx]
  constructor
  · intro h; exact h.2
  · intro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega, by omega⟩, h1, h2, h3⟩

private def seedExpsU (U : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)
    |>.image (fun p => Finsupp.single 0 p.1 + Finsupp.single 1 p.2)

private theorem mem_seedExpsU {U : ℕ} {e : Fin 2 →₀ ℕ} :
    e ∈ seedExpsU U ↔ seedWeight e ≤ U := by
  simp only [seedExpsU, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨_, _⟩, hab⟩, rfl⟩
    rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    simpa using hab
  · intro hle
    have hsum : e 0 + e 1 ≤ U := by
      rw [seedWeight, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hle
      exact hle
    refine ⟨(e 0, e 1), ⟨⟨by omega, by omega⟩, hsum⟩, ?_⟩
    ext j; fin_cases j <;> simp

private theorem card_seedExpsU (U : ℕ) : (seedExpsU U).card = triangle U := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => Finsupp.single (0 : Fin 2) p.1 + Finsupp.single 1 p.2)
      (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
    exact Prod.ext (by simpa using h0) (by simpa using h1)
  rw [seedExpsU, Finset.card_image_of_injOn hinj]
  have hfib : (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)).card =
      ∑ a ∈ Finset.range (U + 1), (U + 1 - a) := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro a ha
    have ha' : a ≤ U := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [← Finset.card_filter]
    have heq : (Finset.range (U + 1)).filter (fun b => a + b ≤ U) = Finset.range (U + 1 - a) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [heq, Finset.card_range]
  rw [hfib]
  clear hinj hfib
  induction U with
  | zero => decide
  | succ U ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    have hshift : ∑ k ∈ Finset.range (U + 1), (U + 1 + 1 - (k + 1)) =
        ∑ k ∈ Finset.range (U + 1), (U + 1 - k) := by
      apply Finset.sum_congr rfl; intro k _; omega
    rw [hshift, ih]
    unfold triangle
    have h2 : 2 * ((U + 1) * (U + 2) / 2) = (U + 1) * (U + 2) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self (U + 1)).two_dvd
    have h2' : 2 * ((U + 1 + 1) * (U + 1 + 2) / 2) = (U + 1 + 1) * (U + 1 + 2) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self (U + 1 + 1)).two_dvd
    have hring : (U + 1 + 1) * (U + 1 + 2) = (U + 1) * (U + 2) + 2 * (U + 2) := by ring
    omega

private theorem evaluated2_mem_box {h U W : ℕ} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {P : Jet2} (hP : P ∈ evaluated2 Crt word (shape2_m59 U) W) :
    ∀ e₂ e₁ e₀ e, ((((P.coeff e₂).coeff e₁).coeff e₀).coeff e ≠ 0) →
      (e₂, e₁, e₀) ∈ boxPos2 ∧ seedWeight e ≤ U := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Q, hQ, rfl⟩ := hP
    intro e₂ e₁ e₀ e hne
    rw [show ((((centerEval2 Q).coeff e₂).coeff e₁).coeff e₀).coeff e =
        algebraMap (Polynomial L) FX (sourceCoord2 Q (e₂, e₁, e₀, e)) from
        coords2_center Q (e₂, e₁, e₀, e)] at hne
    have hsc_ne : sourceCoord2 Q (e₂, e₁, e₀, e) ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    obtain ⟨a, ha⟩ : ∃ a, (sourceCoord2 Q (e₂, e₁, e₀, e)).coeff a ≠ 0 := by
      by_contra! hall; exact hsc_ne (Polynomial.ext fun a => by simpa using hall a)
    rw [sourceCoord2_coeff] at ha
    have hel : trueEligible2 h (shape2_m59 U) W e₂ e₁ e₀ a e := by
      by_contra hnot; exact ha (hQ.1.1 e₂ e₁ e₀ a e hnot)
    exact ⟨mem_boxPos2.mpr ⟨hel.1, hel.2.1, hel.2.2.1⟩, hel.2.2.2.1⟩
  | zero => intro e₂ e₁ e₀ e hne; simp at hne
  | add P₁ P₂ _ _ ih₁ ih₂ =>
    intro e₂ e₁ e₀ e hne
    simp only [Polynomial.coeff_add, MvPolynomial.coeff_add] at hne
    by_cases h1 : (((P₁.coeff e₂).coeff e₁).coeff e₀).coeff e = 0
    · rw [h1, zero_add] at hne; exact ih₂ e₂ e₁ e₀ e hne
    · exact ih₁ e₂ e₁ e₀ e h1
  | smul c P _ ih =>
    intro e₂ e₁ e₀ e hne
    have hmul : ((((c • P).coeff e₂).coeff e₁).coeff e₀).coeff e =
        c * (((P.coeff e₂).coeff e₁).coeff e₀).coeff e := by
      change jetCoords2 (c • P) (e₂, e₁, e₀, e) = c * jetCoords2 P (e₂, e₁, e₀, e)
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hmul] at hne
    exact ih e₂ e₁ e₀ e (right_ne_zero_of_mul hne)

/-- **Graded 2-Jet `FX`-Kernel Finrank Bound (`finrank_FX_vanishOrder_le`)**:
    If every `Q ∈ complete2 Crt word (shape2_m59 U) W` vanishes to order `> k` at `(α₁, α₂)` under
    `shift2 α₁ α₂ ∘ embed2 (algebraMap BaseRing EField)`, then
      `Module.finrank FX (evaluated2 Crt word (shape2_m59 U) W) ≤ triangle U * (highPos2 h W k).card`. -/
theorem finrank_FX_vanishOrder_le {h U W k : ℕ} (hpos : 0 < h) (hh : h ≤ 131069)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (α₁ α₂ : EField)
    (hord : ∀ Q ∈ complete2 Crt word (shape2_m59 U) W,
      ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ (embed2 (algebraMap BaseRing EField) Q)) a b = 0) :
    Module.finrank FX (evaluated2 Crt word (shape2_m59 U) W) ≤
      triangle U * (highPos2 h W k).card := by
  classical
  let s := shape2_m59 U
  -- Step 1: Every `P ∈ evaluated2 Crt word s W` also vanishes to order `> k` under `shift2 α₁ α₂ ∘ jet2ToE`!
  have hordP : ∀ P ∈ evaluated2 Crt word s W,
      ∀ a b, a + b ≤ k → polyBivar (shift2 α₁ α₂ (jet2ToE P)) a b = 0 := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨Q, hQ, rfl⟩ := hP
      rw [jet2ToE_centerEval2]
      exact hord Q hQ
    | zero => intro a b _; simp [polyBivar]
    | add P₁ P₂ _ _ ih₁ ih₂ =>
      intro a b hab
      simp only [map_add, polyBivar, Polynomial.coeff_add]
      unfold polyBivar at ih₁ ih₂
      rw [ih₁ a b hab, ih₂ a b hab, add_zero]
    | smul c P _ ih =>
      intro a b hab
      rw [jet2ToE_smul, map_mul]
      have hC : shift2 α₁ α₂ (Polynomial.C (Polynomial.C (fxToE c))) =
          Polynomial.C (Polynomial.C (fxToE c)) := by
        simp [TwoJetCaseAKernel.shift2, TwoJetCaseAKernel.shift1]
      rw [hC, polyBivar, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      change fxToE c * polyBivar (shift2 α₁ α₂ (jet2ToE P)) a b = 0
      rw [ih a b hab, mul_zero]
  -- Step 2: Project `evaluated2 Crt word s W` onto `(highPos2 h W k × seedExpsU U → FX)`!
  let H := highPos2 h W k
  let SE := seedExpsU U
  let π : evaluated2 Crt word s W →ₗ[FX] (H × SE → FX) :=
    LinearMap.pi fun u =>
      { toFun := fun P => jetCoords2 P.1 (u.1.1.1, u.1.1.2.1, u.1.1.2.2, u.2.1)
        map_add' := fun P Q => by simp
        map_smul' := fun c P => by simp }
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    apply Subtype.ext
    change P.1 = 0
    by_contra hnz
    -- Take the graded-maximal nonzero monomial `m* = (e₂*, e₁*, e₀*)` of `P.1`!
    obtain ⟨m, hm, hmax⟩ := exists_graded_max hnz
    have hbd := leading_bound_2jet hpos hh Crt word s W P.2 hm hmax
    have hm_ne : (((P.1.coeff m.1).coeff m.2.1).coeff m.2.2) ≠ 0 := (mem_support3 P.1 m).mp hm
    obtain ⟨e, he⟩ : ∃ e, ((((P.1.coeff m.1).coeff m.2.1).coeff m.2.2).coeff e) ≠ 0 := by
      by_contra! hall; exact hm_ne (MvPolynomial.ext _ _ fun e => by simpa using hall e)
    obtain ⟨hm_box, heU⟩ := evaluated2_mem_box P.2 m.1 m.2.1 m.2.2 e he
    -- Cannot have `k < m.2.1 + m.1`, because then `(m, e) ∈ H × SE` and `π P = 0` contradicts `he`!
    have hle_k : m.2.1 + m.1 ≤ k := by
      by_contra hgt
      have hmH : m ∈ H := Finset.mem_filter.mpr ⟨hm_box, hbd, Nat.lt_of_not_ge hgt⟩
      have heSE : e ∈ SE := mem_seedExpsU.mpr heU
      have h0 : jetCoords2 P.1 (m.1, m.2.1, m.2.2, e) = 0 := congrFun hP (⟨m, hmH⟩, ⟨e, heSE⟩)
      exact he h0
    -- Since `m` is maximal under `(e₁ + e₂, e₂, e₀)`, EVERY nonzero `(e₂, e₁)` of `P.1` has `e₁ + e₂ ≤ k`!
    have hdeg_le : ∀ a b, k < a + b → polyBivar (jet2ToE P.1) a b = 0 := by
      intro a b hab
      simp only [polyBivar, jet2ToE, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      have hzero : (P.1.coeff b).coeff a = 0 := by
        apply Polynomial.ext; intro e₀
        simp only [Polynomial.coeff_zero]
        by_contra hne₀
        have hmem' : (b, a, e₀) ∈ support3 P.1 := (mem_support3 P.1 _).mpr hne₀
        have hle := hmax (b, a, e₀) hmem'
        rcases hle with hlt | heq
        · unfold gradedLt at hlt
          dsimp only at hlt
          omega
        · subst heq
          dsimp only at hle_k
          omega
      rw [hzero, map_zero]
    -- Apply `zero_of_deg_le_and_order_gt` to `jet2ToE P.1`!
    have hj0 : jet2ToE P.1 = 0 := zero_of_deg_le_and_order_gt α₁ α₂ hdeg_le (hordP P.1 P.2)
    have hP0 : P.1 = 0 :=
      (Polynomial.map_injective _ (Polynomial.map_injective _ seedsY0ToE_injective))
        (hj0.trans (Polynomial.map_zero _).symm)
    exact hnz hP0
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_seedExpsU] at hle
  simpa only [mul_comm] using hle

/-! ## 4. Exact Combinatorial Receipts & Linear-in-`h` Surplus for `69.61` -/

private theorem finset_sum_range_eq_natSum (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range n, f i = natSum n f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih]; rfl

private theorem card_range_filter_Icc (N lo hi : ℕ) (hhi : hi < N) :
    ((Finset.range N).filter fun x => lo ≤ x ∧ x ≤ hi).card = hi + 1 - lo := by
  by_cases h : lo ≤ hi
  · have heq : (Finset.range N).filter (fun x => lo ≤ x ∧ x ≤ hi) = Finset.Icc lo hi := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    rw [heq, Nat.card_Icc]
  · have heq : (Finset.range N).filter (fun x => lo ≤ x ∧ x ≤ hi) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
    rw [heq, Finset.card_empty]; omega

private theorem gradeSlots2_card_61 (q : ℕ) :
    (PoleMoment2Jet.gradeSlots2 (shape2_m59 399) q).card = gradeCount61 q := by
  rw [PoleMoment2Jet.gradeSlots2, Finset.card_filter, Finset.sum_product_right, gradeCount61,
    ← finset_sum_range_eq_natSum]
  dsimp only [shape2_m59]
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hq
  · have heq : (Finset.range 25).filter (fun e₁ => e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) =
        (Finset.range 25).filter (fun e₁ => 0 ≤ e₁ ∧ e₁ ≤ min (q - e₂) (24 - 2 * e₂)) := by
      ext e₁; simp only [Finset.mem_filter, Finset.mem_range, jetIdx]; omega
    rw [heq, card_range_filter_Icc 25 0 (min (q - e₂) (24 - 2 * e₂)) (by omega)]
    omega
  · have heq : (Finset.range 25).filter (fun e₁ => e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) = ∅ := by
      ext e₁; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, jetIdx]; omega
    rw [heq, Finset.card_empty]

private theorem columnCount2_61 (t q : ℕ) :
    PoleMoment2Jet.columnCount2 (shape2_m59 399) t q = colCount61 t q := by
  rw [PoleMoment2Jet.columnCount2, PoleMoment2Jet.colSlots2, PoleMoment2Jet.gradeSlots2,
    Finset.filter_filter, Finset.card_filter, Finset.sum_product_right, colCount61,
    ← finset_sum_range_eq_natSum]
  change ∑ e₂ ∈ Finset.range 11,
      (∑ e₁ ∈ Finset.range 25,
        if (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂ then 1 else 0) = _
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hcond
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂) =
        (Finset.range 25).filter (fun e₁ =>
          (24 - t - 2 * e₂) ≤ e₁ ∧ e₁ ≤ min (min (q - e₂) (24 - 2 * e₂)) (127 - t - 2 * e₂)) := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, PoleMoment2Jet.IsCol, shape2_m59, jetIdx]
      omega
    rw [heq, card_range_filter_Icc 25 _ _ (by omega)]
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsCol (shape2_m59 399) t q e₁ e₂) = ∅ := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        PoleMoment2Jet.IsCol, shape2_m59, jetIdx]
      omega
    rw [heq, Finset.card_empty]

private theorem pivotCount2_61 (t q : ℕ) :
    PoleMoment2Jet.pivotCount2 (shape2_m59 399) t q = pivCount61 t q := by
  rw [PoleMoment2Jet.pivotCount2, PoleMoment2Jet.pivotSlots2, PoleMoment2Jet.gradeSlots2,
    Finset.filter_filter, Finset.card_filter, Finset.sum_product_right, pivCount61,
    ← finset_sum_range_eq_natSum]
  change ∑ e₂ ∈ Finset.range 11,
      (∑ e₁ ∈ Finset.range 25,
        if (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂ then 1 else 0) = _
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [← Finset.card_filter]
  split_ifs with hcond
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂) =
        (Finset.range 25).filter (fun e₁ =>
          (24 - t - 2 * e₂) ≤ e₁ ∧ e₁ ≤ min (min (q - e₂) (24 - 2 * e₂)) (127 - t - q - 2 * e₂)) := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, PoleMoment2Jet.IsPivot,
        PoleMoment2Jet.IsCol, PoleMoment2Jet.IsRow, shape2_m59, jetIdx]
      omega
    rw [heq, card_range_filter_Icc 25 _ _ (by omega)]
  · have heq :
        (Finset.range 25).filter (fun e₁ =>
          (e₁ + e₂ ≤ q ∧ e₂ ≤ 10 ∧ jetIdx e₁ e₂ ≤ 24) ∧
            PoleMoment2Jet.IsPivot (shape2_m59 399) t q e₁ e₂) = ∅ := by
      ext e₁
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        PoleMoment2Jet.IsPivot, PoleMoment2Jet.IsCol, PoleMoment2Jet.IsRow, shape2_m59, jetIdx]
      omega
    rw [heq, Finset.card_empty]

theorem groupedPoleMoment2_m59_le : groupedPoleMoment2 (shape2_m59 399) ≤ 9858694 := by
  have hsum_le : groupedPoleMoment2 (shape2_m59 399) ≤ ∑ t ∈ Finset.range 128, offsetUpper61 t := by
    rw [groupedPoleMoment2]
    change ∑ t ∈ Finset.range 128, PoleMoment2Jet.offsetMoment2 (shape2_m59 399) t ≤ _
    apply Finset.sum_le_sum
    intro t ht
    rw [PoleMoment2Jet.offsetMoment2, PoleMoment2Jet.largestGradeSum2]
    have hmem : optK61 t ∈ Finset.range ((shape2_m59 399).B + 1) :=
      Finset.mem_range.mpr (optK61_lt_81 ⟨t, Finset.mem_range.mp ht⟩)
    refine (Nat.sub_le_sub_right (Finset.inf'_le _ hmem) _).trans ?_
    simp_rw [columnCount2_61, pivotCount2_61]
    change (∑ q ∈ Finset.range 81, pivCount61 t q) * optK61 t +
        ∑ q ∈ Finset.range 81, (q - optK61 t) * colCount61 t q -
        ∑ q ∈ Finset.range 81, q * pivCount61 t q ≤ offsetUpper61 t
    simp only [finset_sum_range_eq_natSum, offsetUpper61]
    exact le_rfl
  refine hsum_le.trans ?_
  rw [finset_sum_range_eq_natSum, offsetUpper_val]

theorem poleRows2_m59 : poleRows2 (shape2_m59 399) = 662695 := by
  rw [poleRows2]
  simp_rw [gradeSlots2_card_61]
  dsimp only [shape2_m59]
  rw [finset_sum_range_eq_natSum]
  exact poleRows2_nat_val

private theorem sum_boxPos2_eq (f : ℕ × ℕ × ℕ → ℕ) :
    ∑ m ∈ boxPos2, f m =
      ∑ e₂ ∈ Finset.range 11, ∑ e₁ ∈ Finset.range (25 - 2 * e₂),
        ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), f (e₂, e₁, e₀) := by
  rw [boxPos2, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro e₂ he₂
  have he₂' : e₂ ≤ 10 := Nat.lt_succ_iff.mp (Finset.mem_range.mp he₂)
  rw [Finset.sum_product]
  have h1 : ∀ e₁ ∈ Finset.range 25,
      (∑ e₀ ∈ Finset.range 81, if e₀ + e₁ + e₂ ≤ 80 ∧ jetIdx e₁ e₂ ≤ 24 ∧ e₂ ≤ 10 then f (e₂, e₁, e₀) else 0) =
      if e₁ < 25 - 2 * e₂ then ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), f (e₂, e₁, e₀) else 0 := by
    intro e₁ he₁
    split_ifs with hlt
    · rw [← Finset.sum_filter]
      have heq : (Finset.range 81).filter (fun e₀ => e₀ + e₁ + e₂ ≤ 80 ∧ jetIdx e₁ e₂ ≤ 24 ∧ e₂ ≤ 10) =
          Finset.range (81 - e₁ - e₂) := by
        ext e₀; simp only [Finset.mem_filter, Finset.mem_range, jetIdx]; omega
      rw [heq]
    · apply Finset.sum_eq_zero; intro e₀ _
      rw [ite_eq_right_iff]; intro hc; exfalso; simp only [jetIdx] at hc; omega
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have heq : (Finset.range 25).filter (fun e₁ => e₁ < 25 - 2 * e₂) = Finset.range (25 - 2 * e₂) := by
    ext e₁; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [heq]

private theorem boxPos2_moments :
    boxPos2.card = 11385 ∧
    (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = 521345 ∧
    (∑ m ∈ boxPos2, jetIdx m.2.1 m.1) = 173635 ∧
    (∑ m ∈ boxPos2, (m.2.1 + m.1)) = 131890 ∧
    (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) = 662695 := by
  have hcard : boxPos2.card = 11385 := by
    rw [Finset.card_eq_sum_ones, sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, finset_sum_range_eq_natSum]
    exact box_card_val
  have hq : (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = 521345 := by
    rw [sum_boxPos2_eq]
    have hinner : ∀ e₂ ∈ Finset.range 11, ∀ e₁ ∈ Finset.range (25 - 2 * e₂),
        (∑ e₀ ∈ Finset.range (81 - e₁ - e₂), (e₀ + e₁ + e₂)) =
        (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂) := by
      intro e₂ _ e₁ _
      have : ∀ e₀, e₀ + e₁ + e₂ = e₀ + (e₁ + e₂) := fun _ => Nat.add_assoc _ _ _
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hsum : (∑ e₂ ∈ Finset.range 11, ∑ e₁ ∈ Finset.range (25 - 2 * e₂),
          ∑ e₀ ∈ Finset.range (81 - e₁ - e₂), (e₀ + e₁ + e₂)) =
        natSum 11 (fun e₂ => natSum (25 - 2 * e₂) (fun e₁ =>
          (81 - e₁ - e₂) * (81 - e₁ - e₂ - 1) / 2 + (81 - e₁ - e₂) * (e₁ + e₂))) := by
      rw [← finset_sum_range_eq_natSum]
      apply Finset.sum_congr rfl; intro e₂ he₂
      rw [← finset_sum_range_eq_natSum]
      exact Finset.sum_congr rfl (hinner e₂ he₂)
    rw [hsum]; exact box_q_val
  have hv : (∑ m ∈ boxPos2, jetIdx m.2.1 m.1) = 173635 := by
    rw [sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, jetIdx, finset_sum_range_eq_natSum]
    exact box_v_val
  have h12 : (∑ m ∈ boxPos2, (m.2.1 + m.1)) = 131890 := by
    rw [sum_boxPos2_eq]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, finset_sum_range_eq_natSum]
    exact box_12_val
  have hp : (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) = 662695 := by
    have hadd : (∑ m ∈ boxPos2, (80 + 24 - (m.2.2 + m.2.1 + m.1))) +
        (∑ m ∈ boxPos2, (m.2.2 + m.2.1 + m.1)) = ∑ _m ∈ boxPos2, (80 + 24) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro m hm
      have hbox := mem_boxPos2.mp hm
      omega
    rw [Finset.sum_const, smul_eq_mul, hcard, hq] at hadd
    have hsub : ∀ x : ℕ, x + 521345 = 11385 * (80 + 24) → x = 662695 := by omega
    exact hsub _ hadd
  exact ⟨hcard, hq, hv, h12, hp⟩

private theorem finrank_ambient2_m59_ge (h : ℕ) (hlo : 2327 ≤ h) (hhi : h ≤ 2449) :
    let N := 59 * 179818
    triangle 399 * (N * 11385 + 173635 - (131071 - h) * 521345) + poleCredit2 h (shape2_m59 399) ≤
      Module.finrank L (ambient2 h (shape2_m59 399) (N - 1)) := by
  intro N
  rw [TwoJetCaseAKernel.finrank_ambient2_eq]
  -- Count `eligibleCoords h (shape2_m59 399) (N - 1)` by fibering over `(m ∈ boxPos2, e ∈ seedExpsU 399, a ≤ bound)`!
  let s := shape2_m59 399
  let M := (N - 1) + (s.B + s.J) * (2 * h) + s.J
  let width (m : ℕ × ℕ × ℕ) : ℕ :=
    N + (s.B + s.J) * (2 * h) + jetIdx m.2.1 m.1 - (m.2.2 + m.2.1 + m.1) * (131071 + h)
  -- Build explicit injection from `(m : boxPos2) × (e : seedExpsU 399) × Fin (width m.1)` into `eligibleCoords`!
  let f : (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) →
      TwoJetCaseAKernel.CoeffBox2 s.B M s.U := fun ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩ =>
    have hbox := mem_boxPos2.mp hm
    have hse := mem_seedExpsU.mp he
    have haM : a ≤ M := by
      dsimp only [width, M, s, shape2_m59, jetIdx] at ha hbox ⊢; omega
    have hej (j : Fin 2) : e j ≤ 399 := by
      apply le_trans _ hse
      rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    (⟨e₂, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨e₁, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨e₀, by dsimp only [s, shape2_m59] at hbox ⊢; omega⟩,
     ⟨a, by omega⟩,
     fun j => ⟨e j, by have := hej j; dsimp only [s, shape2_m59]; omega⟩)
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩ ⟨⟨⟨e₂', e₁', e₀'⟩, hm'⟩, ⟨e', he'⟩, ⟨a', ha'⟩⟩ hfeq
    simp only [f, Prod.mk.injEq, Fin.ext_iff] at hfeq
    obtain ⟨rfl, rfl, rfl, rfl, heeq⟩ := hfeq
    have he_eq : e = e' := by
      ext j
      have := congrFun heeq j
      simpa [Fin.ext_iff] using this
    subst he_eq
    rfl
  have hf_mem : ∀ x, f x ∈ TwoJetCaseAKernel.eligibleCoords h s (N - 1) := by
    rintro ⟨⟨⟨e₂, e₁, e₀⟩, hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩
    rw [TwoJetCaseAKernel.eligibleCoords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hbox := mem_boxPos2.mp hm
    have hse := mem_seedExpsU.mp he
    have hbox_e : TwoJetCaseAKernel.boxExp (f ⟨⟨(e₂, e₁, e₀), hm⟩, ⟨e, he⟩, ⟨a, ha⟩⟩).2.2.2.2 = e := by
      ext j; simp [TwoJetCaseAKernel.boxExp, f]
    rw [hbox_e]
    refine ⟨hbox.1, hbox.2.1, hbox.2.2, hse, ?_⟩
    have hpos_w : (e₀ + e₁ + e₂) * (131071 + h) ≤ N + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂ := by
      dsimp only [N, s, shape2_m59, jetIdx] at hbox ⊢
      have hmul_le : (e₀ + e₁ + e₂) * (131071 + h) ≤ 80 * (131071 + h) := Nat.mul_le_mul_right _ hbox.1
      omega
    dsimp only [f, width] at ha ⊢
    omega
  have hcard_le : Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) ≤
      (TwoJetCaseAKernel.eligibleCoords h s (N - 1)).card := by
    have := Fintype.card_le_of_injective
      (fun x => (⟨f x, hf_mem x⟩ : TwoJetCaseAKernel.eligibleCoords h s (N - 1)))
      (fun x y hxy => hf_inj (congrArg Subtype.val hxy))
    simpa only [Fintype.card_coe] using this
  -- Evaluate `Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1))`!
  have hcard_eq : Fintype.card (Σ m : boxPos2, seedExpsU 399 × Fin (width m.1)) =
      triangle 399 * ∑ m ∈ boxPos2, width m := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_coe, card_seedExpsU, Fintype.card_fin]
    rw [← Finset.mul_sum, Finset.sum_coe_sort]
  have hsum_width : ∑ m ∈ boxPos2, width m =
      (N * 11385 + 173635 - (131071 - h) * 521345) + 2 * h * 662695 := by
    have hterm (m : ℕ × ℕ × ℕ) (hm : m ∈ boxPos2) :
        width m + (m.2.2 + m.2.1 + m.1) * (131071 - h) =
          N + jetIdx m.2.1 m.1 + 2 * h * (80 + 24 - (m.2.2 + m.2.1 + m.1)) := by
      have hbox := mem_boxPos2.mp hm
      dsimp only [width, s, shape2_m59, N, jetIdx] at hbox ⊢
      have hmul : (m.2.2 + m.2.1 + m.1) * (131071 + h) =
          (m.2.2 + m.2.1 + m.1) * (131071 - h) + 2 * h * (m.2.2 + m.2.1 + m.1) := by
        have h1 : 131071 + h = (131071 - h) + 2 * h := by omega
        rw [h1, Nat.mul_add]; ring
      have h2 : 2 * h * (80 + 24 - (m.2.2 + m.2.1 + m.1)) + 2 * h * (m.2.2 + m.2.1 + m.1) =
          (80 + 24) * (2 * h) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : m.2.2 + m.2.1 + m.1 ≤ 80 + 24), mul_comm]
      have hmul_le : (m.2.2 + m.2.1 + m.1) * (131071 + h) ≤ 80 * (131071 + h) :=
        Nat.mul_le_mul_right _ hbox.1
      omega
    have hsum := Finset.sum_congr rfl hterm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
    obtain ⟨hc, hq, hv, _, hp⟩ := boxPos2_moments
    rw [hc, hq, hv, ← Finset.mul_sum, hp] at hsum
    have hcomm : 521345 * (131071 - h) = (131071 - h) * 521345 := mul_comm _ _
    have hN : 11385 * N = N * 11385 := mul_comm _ _
    omega
  rw [hcard_eq, hsum_width, Nat.mul_add] at hcard_le
  have hpc : poleCredit2 h (shape2_m59 399) = triangle 399 * (2 * h * 662695) := by
    rw [poleCredit2, poleRows2_m59, mul_assoc]; rfl
  rw [hpc]
  exact hcard_le

private theorem sum_highPos2_card_le (h : ℕ) (hlo : 2327 ≤ h) (hhi : h ≤ 2449) :
    let N := 59 * 179818
    (∑ W ∈ Finset.range N, (highPos2 h W ((N - 1 - W) / (3 * h))).card) +
      (N * 11385 + 173635 - 131071 * 521345 + h * 125675) ≤
      N * 11385 + 173635 - (131071 - h) * 521345 := by
  intro N
  -- Swap sum over `W ∈ range N` and `m ∈ boxPos2`!
  have hswap : ∑ W ∈ Finset.range N, (highPos2 h W ((N - 1 - W) / (3 * h))).card =
      ∑ m ∈ boxPos2, ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1).card := by
    simp only [highPos2, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- For each `m ∈ boxPos2`, the inner count is at most `3 * h * (m.2.1 + m.1)`!
  have hper (m : ℕ × ℕ × ℕ) (hm : m ∈ boxPos2) :
      ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1).card ≤
      3 * h * (m.2.1 + m.1) := by
    have hsub : ((Finset.range N).filter fun W =>
        (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
        (N - 1 - W) / (3 * h) < m.2.1 + m.1) ⊆
      (Finset.range (3 * h * (m.2.1 + m.1))).image (fun t => N - 1 - t) := by
      intro W hW
      obtain ⟨hWN, _, hdiv⟩ := Finset.mem_filter.mp hW
      have hWN' : W < N := Finset.mem_range.mp hWN
      have h3h : 0 < 3 * h := by omega
      have hlt : N - 1 - W < 3 * h * (m.2.1 + m.1) := by
        by_contra hge
        push_neg at hge
        have hq : m.2.1 + m.1 ≤ (N - 1 - W) / (3 * h) :=
          (Nat.le_div_iff_mul_le h3h).mpr (by simpa [mul_comm] using hge)
        omega
      exact Finset.mem_image.mpr ⟨N - 1 - W, Finset.mem_range.mpr hlt, by omega⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hsum_le : ∑ m ∈ boxPos2, ((Finset.range N).filter fun W =>
      (m.2.2 + m.2.1 + m.1) * (131071 - h) ≤ W + jetIdx m.2.1 m.1 ∧
      (N - 1 - W) / (3 * h) < m.2.1 + m.1).card ≤ 3 * h * 131890 := by
    calc
      _ ≤ ∑ m ∈ boxPos2, 3 * h * (m.2.1 + m.1) := Finset.sum_le_sum hper
      _ = 3 * h * ∑ m ∈ boxPos2, (m.2.1 + m.1) := (Finset.mul_sum _ _ _).symm
      _ = 3 * h * 131890 := by rw [boxPos2_moments.2.2.2.1]
  have hNval : N = 10609262 := rfl
  have hsub1 : (131071 - h) * 521345 + h * 521345 = 131071 * 521345 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  omega

/-! ## 5. End-to-End Case-A Avoidance Theorem at `69.61` (`caseA_avoidance_6961`) -/

def alpha1 (G : Jet) : EField :=
  -(seedsY0ToE (G.coeff 0)) / seedsY0ToE (G.coeff 1)

def evJetAt (G : Jet) : Jet →+* EField :=
  Polynomial.eval₂RingHom seedsY0ToE (alpha1 G)

def alpha2 (G : Jet) : EField :=
  -(evJetAt G (prolongB1 G)) / evJetAt G (prolongA G)

theorem caseA_avoidance_6961 {h : ℕ} (hlo : 2327 ≤ h) (hhi : h ≤ 2449)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {G : Jet} (hdegG : G.natDegree = 1)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) ≠ 0) :
    ∃ W < 59 * 179818, ∃ P₀ ∈ complete2 Crt word (shape2_m59 399) W,
      ¬ G ∣ prolongSubst (prolongA G) (prolongB1 G) 10 (centerEval2 P₀) := by
  let s := shape2_m59 399
  let N := 59 * 179818
  let φ : BaseRing →+* EField := algebraMap BaseRing EField
  have hφ : Function.Injective φ := IsFractionRing.injective BaseRing EField
  have hcharE : CharP EField K1.p := by
    have h2 : ∀ n : ℕ, (n : EField) = 0 ↔ K1.p ∣ n := by
      intro n
      have hcast : (n : EField) = φ (Polynomial.C (Polynomial.C (MvPolynomial.C (n : L)))) := by
        simp [φ]
      rw [hcast, show (0 : EField) = φ 0 from (map_zero φ).symm, hφ.eq_iff,
        Polynomial.C_eq_zero, Polynomial.C_eq_zero, MvPolynomial.C_eq_zero]
      exact CharP.cast_eq_zero_iff L K1.p n
    exact ⟨h2⟩
  have hA1_ne : G.coeff 1 ≠ 0 := by
    rw [← hdegG, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by rw [hz, Polynomial.natDegree_zero] at hdegG; omega)
  have hA_ne : seedsY0ToE (G.coeff 1) ≠ 0 := fun hz =>
    hA1_ne (seedsY0ToE_injective (hz.trans (map_zero _).symm))
  have h2_ne : (2 : EField) ≠ 0 := by
    intro h2
    have hdvd : K1.p ∣ 2 := (CharP.cast_eq_zero_iff EField K1.p 2).mp (by simpa using h2)
    have hle := Nat.le_of_dvd (by decide) hdvd
    change 2130706433 ≤ 2 at hle
    omega
  have hG0 : evJetAt G G = 0 := by
    have hlin : G = Polynomial.C (G.coeff 0) + Polynomial.C (G.coeff 1) * Polynomial.X := by
      ext n
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2)]
          simp [Polynomial.coeff_C, Polynomial.coeff_X]
    conv_lhs => arg 2; rw [hlin]
    rw [map_add, map_mul]
    simp only [evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, alpha1]
    rw [mul_div_cancel₀ _ hA_ne, add_neg_cancel]
  have hAne : evJetAt G (prolongA G) ≠ 0 := by
    simp only [prolongA, map_mul, map_ofNat, evJetAt, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact mul_ne_zero h2_ne hA_ne
  have hG1 : evJetAt G (prolongA G) * alpha2 G + evJetAt G (prolongB1 G) = 0 := by
    dsimp only [alpha2]
    rw [mul_div_cancel₀ _ hAne, neg_add_cancel]
  by_contra hnone
  push_neg at hnone
  -- Every `Q ∈ complete2 Crt word s W'` (`W' < N`) vanishes at `(alpha1 G, alpha2 G)`!
  have hall : ∀ W' < N, ∀ Q ∈ complete2 Crt word s W',
      polyBivar (shift2 (alpha1 G) (alpha2 G) (embed2 φ Q)) 0 0 = 0 := fun W' hW' Q hQ =>
    eval_zero_of_prolongSubst_dvd φ (evJetAt G) (alpha1 G) (alpha2 G)
      (jet2ToE_eval₂_comm (alpha1 G) (alpha2 G)) hG0 hAne hG1 hQ.1.1 (hnone W' hW' Q hQ)
  -- For each `W < N`, let `k W = (N - 1 - W) / (3 * h)`. Then `boundedShiftExp s 1 = 3`!
  have hbse : boundedShiftExp s 1 = 3 := by decide
  let k (W : ℕ) : ℕ := (N - 1 - W) / (3 * h)
  have hWk : ∀ W < N, W + k W * (boundedShiftExp s 1 * h) < N := by
    intro W hW
    rw [hbse]
    have hmul : k W * (3 * h) ≤ N - 1 - W := by
      rw [mul_comm]
      exact Nat.mul_div_le (N - 1 - W) (3 * h)
    omega
  have hk : ∀ W < N, k W < K1.p := by
    intro W hW
    have hle : k W ≤ N - 1 - W := Nat.div_le_self _ _
    change k W < 2130706433
    dsimp only [N] at hle
    omega
  -- Hence every `Q ∈ complete2 Crt word s W` vanishes to order `> k W` at `(alpha1 G, alpha2 G)`!
  have hord : ∀ W < N, ∀ Q ∈ complete2 Crt word s W,
      ∀ a b, a + b ≤ k W → polyBivar (shift2 (alpha1 G) (alpha2 G) (embed2 φ Q)) a b = 0 := by
    intro W hW Q hQ
    have hvan := wordVanishes_of_all_complete2_eval_zero Crt word s N hφ
      fractionRingFieldDerivs_compat (alpha1 G) (alpha2 G) hall (hWk W hW) hQ
    exact pow_collapse_of_wordVanishes fractionRingFieldDerivs hdet (k W) (hk W hW) hvan
  -- Chain `finrank_ambient2_m59_ge` ≤ `physRank2_m59` ≤ `pole_bound_2jet` ≤ `telescope2` ≤ `finrank_FX_vanishOrder_le`!
  have hamb := finrank_ambient2_m59_ge h hlo hhi
  have hphys := physRank2_m59 h 399 (N - 1) word
  have hpole := pole_bound_2jet (by omega : 0 < h) (by change h < 2130706433; omega) Crt word s (N - 1)
  have htele := telescope2 (by omega : 0 < h) (by omega : h ≤ 131068) Crt word s (N - 1)
  have hN_eq : (N - 1) + 1 = N := rfl
  rw [hN_eq] at htele
  have hsum_fx : ∑ W ∈ Finset.range N, Module.finrank FX (evaluated2 Crt word s W) ≤
      triangle 399 * ∑ W ∈ Finset.range N, (highPos2 h W (k W)).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro W hW
    exact finrank_FX_vanishOrder_le (by omega) (by omega) Crt word (alpha1 G) (alpha2 G)
      (hord W (Finset.mem_range.mp hW))
  have hhigh := sum_highPos2_card_le h hlo hhi
  have hhigh_mul := Nat.mul_le_mul_left (triangle 399) hhigh
  rw [Nat.mul_add] at hhigh_mul
  have hgpm : groupedPoleMoment2 s ≤ 9858694 := groupedPoleMoment2_m59_le
  have htri : triangle 399 = 80200 := by decide
  -- Pure linear arithmetic in `h ∈ [2327, 2449]` gives contradiction!
  dsimp only [s, N] at hamb hphys hpole htele hsum_fx hhigh_mul hgpm
  have hmul_gpm : 2 * h * ((shape2_m59 399).U + 1) * groupedPoleMoment2 (shape2_m59 399) ≤
      2 * h * 400 * 9858694 := by
    dsimp only [shape2_m59]
    exact Nat.mul_le_mul_left _ hgpm
  rw [htri] at hamb hphys hsum_fx hhigh_mul
  dsimp only [k, N] at hsum_fx
  omega

#print axioms seedsY0ToE_injective
#print axioms prolongSubst_rowCaps
#print axioms finrank_FX_vanishOrder_le
#print axioms caseA_avoidance_6961

end
end TwoJetCaseAFX
