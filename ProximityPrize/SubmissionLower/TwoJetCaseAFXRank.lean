import ProximityPrize.SubmissionLower.TwoJetCaseAFXCore
import ProximityPrize.SubmissionLower.TwoJetCaseAKernel
import ProximityPrize.SubmissionLower.Front6963ListRank
import ProximityPrize.SubmissionLower.Front6963List
import ProximityPrize.SubmissionLower.ListProofA

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

/-!
# Exact Mod-`p` Physical Contact Rank Bound for 2-Jet `m = 59 (80, 24, 10)` (`TwoJetCaseAFXRank`)

Proves the physical contact rank bound for `shape2_m59 U = ⟨59, 80, 24, 10, U⟩`:
  `Module.finrank L (ambient2 h (shape2_m59 U) W) ≤`
    `K1_14.triangle U * 262144 * 200031 + Module.finrank L (contacted2 h word (shape2_m59 U) W)`

by:
1. Slicing `Source2` by each seed exponent `e : Fin 2 →₀ ℕ` (`seedWeight e ≤ U`), showing that
   `atPhysical2 x r` commutes with seed slicing and matches `unscaledLocalSubstitution 2 x r`
   under `η ↦ t * E` (`a + 3*b = (a + b) + 2*b < 59`).
2. Translating `(x, r)` to `(0, 0)` over `L` via `Sol1.C42.coordinates_translation` (mirroring
   `ListProofA.CJ0_2.point_rank_le_origin` over any field `F`).
3. Base-changing from `ZMod p` to `L` via `Matrix.rank_map_le`, then applying L4 `CJ0_1.proof`
   and L4 `Front6963ListBank.prefix_bound` (`≤ 200031`).
-/

namespace TwoJetCaseAFX
noncomputable section

open Polynomial Finset PolynomialDifferential ReedSolomon.HiddenDerivative
open K1 (I)
open K1_14 (L triangle)
open K1_14_1 (SeedPoly seedWeight nodeL)
open PoleMoment2Jet (Shape2 jetIdx poleRows2 poleCredit2 groupedPoleMoment2)
open PoleBound2Jet (Source2 coeffAt2 trueEligible2 ambient2 atPhysical2 physical2 contacted2)
open scoped BigOperators Polynomial Classical

def shape2_m59 (U : ℕ) : Shape2 := ⟨59, 80, 24, 10, U⟩

/-! ## 1. Seed Slicing & Exact Match Between `atPhysical2` and `unscaledLocalSubstitution 2` -/

abbrev PlainJet2 := Polynomial (Polynomial (Polynomial (Polynomial L)))

private def sliceSeedPoly (e : Fin 2 →₀ ℕ) : Source2 →ₗ[L] PlainJet2 :=
  K1_14_1_3.mapCoeffs (K1_14_1_3.mapCoeffs (K1_14_1_3.mapCoeffs
    (K1_14_1_3.mapCoeffs (MvPolynomial.lcoeff L e))))

private theorem sliceSeedPoly_coeff (e : Fin 2 →₀ ℕ) (P : Source2) (e₂ e₁ e₀ a : ℕ) :
    ((((sliceSeedPoly e P).coeff e₂).coeff e₁).coeff e₀).coeff a = coeffAt2 P e₂ e₁ e₀ a e := by
  simp [sliceSeedPoly, K1_14_1_3.mapCoeffs_coeff, coeffAt2, PoleMoment2Jet.sourceCoeff2]

private def atPhysical2L (x r : L) : PlainJet2 →ₐ[L] PlainJet2 :=
  let c : Polynomial L →+* PlainJet2 := PoleMoment2Jet.jetConstant2
  let base : Polynomial L →ₐ[L] Polynomial L :=
    Polynomial.aeval (Polynomial.X + Polynomial.C x)
  let y0 : PlainJet2 := C (C (Polynomial.X (R := Polynomial L)))
  let y1 : PlainJet2 := C (Polynomial.X (R := Polynomial (Polynomial L)))
  let y2 : PlainJet2 := Polynomial.X
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom
    ((IsScalarTower.toAlgHom L (Polynomial L) PlainJet2).comp base)
    (c (Polynomial.C r) + c Polynomial.X * y1 - c (Polynomial.X ^ 2) * y2 + y0)
    (fun _ => Commute.all _ _))
    y1 (fun _ => Commute.all _ _))
    y2 (fun _ => Commute.all _ _)

private theorem atPhysical2L_CCC (x r : L) (q : Polynomial L) :
    atPhysical2L x r (C (C (C q))) = C (C (C (Polynomial.aeval (Polynomial.X + Polynomial.C x) q))) := by
  unfold atPhysical2L
  dsimp only
  rw [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    IsScalarTower.algebraMap_apply (Polynomial L) (Polynomial (Polynomial L)) PlainJet2,
    IsScalarTower.algebraMap_apply (Polynomial (Polynomial L)) (Polynomial (Polynomial (Polynomial L))) PlainJet2]
  simp only [Polynomial.algebraMap_eq]

private theorem atPhysical2L_CCX (x r : L) :
    atPhysical2L x r (C (C Polynomial.X)) =
      PoleMoment2Jet.jetConstant2 (Polynomial.C r) +
        PoleMoment2Jet.jetConstant2 Polynomial.X * C Polynomial.X -
        PoleMoment2Jet.jetConstant2 (Polynomial.X ^ 2) * Polynomial.X +
        C (C Polynomial.X) := by
  unfold atPhysical2L
  dsimp only
  rw [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]

private theorem atPhysical2L_CX (x r : L) : atPhysical2L x r (C Polynomial.X) = C Polynomial.X := by
  unfold atPhysical2L
  dsimp only
  rw [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C,
    AlgHom.coe_toRingHom, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]

private theorem atPhysical2L_X (x r : L) : atPhysical2L x r Polynomial.X = Polynomial.X := by
  unfold atPhysical2L
  dsimp only
  rw [Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]

private theorem atPhysical2_X (x r : L) : atPhysical2 x r Polynomial.X = Polynomial.X :=
  (RingHom.congr_fun (PoleBound2Jet.atPhysical2_as_substitute x r) Polynomial.X).trans
    (PoleMoment2Jet.substitute2_y2 _ _ _ _)

private theorem atPhysical2_CX (x r : L) : atPhysical2 x r (C Polynomial.X) = C Polynomial.X :=
  (RingHom.congr_fun (PoleBound2Jet.atPhysical2_as_substitute x r) (C Polynomial.X)).trans
    (PoleMoment2Jet.substitute2_y1 _ _ _ _)

private theorem atPhysical2_CCX (x r : L) :
    atPhysical2 x r (C (C Polynomial.X)) =
      PoleMoment2Jet.jetConstant2 (Polynomial.C (MvPolynomial.C r)) +
        PoleMoment2Jet.jetConstant2 (Polynomial.X (R := SeedPoly)) * C (Polynomial.X (R := Polynomial (Polynomial SeedPoly))) -
        PoleMoment2Jet.jetConstant2 ((Polynomial.X (R := SeedPoly)) ^ 2) * Polynomial.X +
        C (C (Polynomial.X (R := Polynomial SeedPoly))) :=
  (RingHom.congr_fun (PoleBound2Jet.atPhysical2_as_substitute x r) (C (C Polynomial.X))).trans
    (PoleMoment2Jet.substitute2_y0 _ _ _ _)

private theorem atPhysical2_CCC (x r : L) (q : Polynomial SeedPoly) :
    atPhysical2 x r (C (C (C q))) =
      PoleMoment2Jet.jetConstant2
        (eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C (MvPolynomial.C x)) q) :=
  (RingHom.congr_fun (PoleBound2Jet.atPhysical2_as_substitute x r) (C (C (C q)))).trans
    (PoleMoment2Jet.substitute2_base _ _ _ _ q)

private theorem sliceSeedPoly_atPhysical2 (e : Fin 2 →₀ ℕ) (x r : L) (P : Source2) :
    sliceSeedPoly e (atPhysical2 x r P) = atPhysical2L x r (sliceSeedPoly e P) := by
  -- Both sides are L-linear; check on a basis monomial of Source2.
  -- Since `atPhysical2 x r` acts as identity on `SeedPoly` and uses only `L`-scalars in `X, Y₀, Y₁, Y₂`,
  -- prove by induction on `P` via `Polynomial.induction_on'` at each layer.
  have hbase_comm : ∀ q : Polynomial SeedPoly,
      K1_14_1_3.mapCoeffs (MvPolynomial.lcoeff L e)
        (eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C (MvPolynomial.C x)) q) =
      Polynomial.aeval (Polynomial.X + Polynomial.C x)
        (K1_14_1_3.mapCoeffs (MvPolynomial.lcoeff L e) q) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | monomial n s =>
      conv_lhs =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
      conv_rhs =>
        rw [K1_14_1_3.mapCoeffs_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
          map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      ext a
      rw [K1_14_1_3.mapCoeffs_coeff]
      simp only [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul, MvPolynomial.lcoeff_apply]
      have hpow : ∀ k : ℕ, ((Polynomial.X + Polynomial.C (MvPolynomial.C x) : Polynomial SeedPoly) ^ k) =
          ((Polynomial.X + Polynomial.C x : Polynomial L) ^ k).map MvPolynomial.C := by
        intro k
        rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
      rw [hpow n, Polynomial.coeff_map, mul_comm s, MvPolynomial.coeff_C_mul]
      ring
  have hmul_const : ∀ (p : PlainJet2) (Q : Source2),
      sliceSeedPoly e ((PoleBound2Jet.jetMap2 MvPolynomial.C p) * Q) = p * sliceSeedPoly e Q := by
    intro p Q
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    rw [sliceSeedPoly_coeff, coeffAt2, PoleMoment2Jet.sourceCoeff2]
    simp only [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl; rintro ⟨p₂, q₂⟩ _
    simp only [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl; rintro ⟨p₁, q₁⟩ _
    simp only [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl; rintro ⟨p₀, q₀⟩ _
    simp only [Polynomial.coeff_mul, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl; rintro ⟨pa, qa⟩ _
    simp only [PoleBound2Jet.jetMap2, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      MvPolynomial.coeff_C_mul, sliceSeedPoly_coeff, coeffAt2, PoleMoment2Jet.sourceCoeff2]
  have hy0_eq :
      PoleMoment2Jet.jetConstant2 (Polynomial.C (MvPolynomial.C r)) +
        PoleMoment2Jet.jetConstant2 (Polynomial.X (R := SeedPoly)) * C (Polynomial.X (R := Polynomial (Polynomial SeedPoly))) -
        PoleMoment2Jet.jetConstant2 ((Polynomial.X (R := SeedPoly)) ^ 2) * Polynomial.X +
        C (C (Polynomial.X (R := Polynomial SeedPoly))) =
      PoleBound2Jet.jetMap2 MvPolynomial.C
        (PoleMoment2Jet.jetConstant2 (Polynomial.C r) +
          PoleMoment2Jet.jetConstant2 Polynomial.X * C Polynomial.X -
          PoleMoment2Jet.jetConstant2 (Polynomial.X ^ 2) * Polynomial.X +
          C (C Polynomial.X)) := by
    simp [PoleBound2Jet.jetMap2, PoleMoment2Jet.jetConstant2]
  have hy1_eq : (C (Polynomial.X (R := Polynomial (Polynomial SeedPoly))) : Source2) =
      PoleBound2Jet.jetMap2 MvPolynomial.C (C Polynomial.X) := by
    simp [PoleBound2Jet.jetMap2]
  have hy2_eq : (Polynomial.X : Source2) = PoleBound2Jet.jetMap2 MvPolynomial.C Polynomial.X := by
    simp [PoleBound2Jet.jetMap2]
  have hjetC : ∀ q : Polynomial SeedPoly,
      sliceSeedPoly e (PoleMoment2Jet.jetConstant2 q) =
        PoleMoment2Jet.jetConstant2 (K1_14_1_3.mapCoeffs (MvPolynomial.lcoeff L e) q) := by
    intro q
    apply Polynomial.ext; intro e₂
    apply Polynomial.ext; intro e₁
    apply Polynomial.ext; intro e₀
    apply Polynomial.ext; intro a
    rw [sliceSeedPoly_coeff, coeffAt2, PoleMoment2Jet.sourceCoeff2]
    cases e₂ <;> cases e₁ <;> cases e₀ <;>
      simp [PoleMoment2Jet.jetConstant2, K1_14_1_3.mapCoeffs_coeff]
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | monomial e₂ P₁ =>
    conv_lhs => rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    conv_rhs =>
      rw [sliceSeedPoly, K1_14_1_3.mapCoeffs_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
        map_mul, map_pow]
    rw [atPhysical2_X, atPhysical2L_X, hy2_eq, ← map_pow, mul_comm (atPhysical2 x r (C P₁)),
      hmul_const, mul_comm]
    congr 1
    induction P₁ using Polynomial.induction_on' with
    | add Q₁ Q₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | monomial e₁ P₀ =>
      conv_lhs =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
          map_mul, map_pow]
      conv_rhs =>
        rw [K1_14_1_3.mapCoeffs_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      rw [atPhysical2_CX, atPhysical2L_CX, hy1_eq, ← map_pow,
        mul_comm (atPhysical2 x r (C (C P₀))), hmul_const, mul_comm]
      congr 1
      induction P₀ using Polynomial.induction_on' with
      | add R₁ R₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
      | monomial e₀ q =>
        conv_lhs =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
            Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
        conv_rhs =>
          rw [K1_14_1_3.mapCoeffs_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
            Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_mul, Polynomial.C_pow,
            map_mul, map_pow]
        rw [atPhysical2_CCX, atPhysical2L_CCX, hy0_eq, ← map_pow,
          mul_comm (atPhysical2 x r (C (C (C q)))), hmul_const, mul_comm]
        congr 1
        rw [atPhysical2_CCC, atPhysical2L_CCC, hjetC, hbase_comm]
        rfl

private def plainToDiff : PlainJet2 →ₐ[L] DifferentialPolynomial L 2 :=
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom
    (Polynomial.aeval (MvPolynomial.X none))
    (MvPolynomial.X (some 0)) (fun _ => Commute.all _ _))
    (MvPolynomial.X (some 1)) (fun _ => Commute.all _ _))
    (MvPolynomial.X (some 2)) (fun _ => Commute.all _ _)

private def ηToTE : PlainJet2 →ₐ[L] LocalPolynomial L 2 :=
  eval₂AlgHom (eval₂AlgHom (eval₂AlgHom
    (Polynomial.aeval (MvPolynomial.X (localT 2)))
    (MvPolynomial.X (localT 2) * MvPolynomial.X (localE 2)) (fun _ => Commute.all _ _))
    (MvPolynomial.X (localY (0 : Fin 2))) (fun _ => Commute.all _ _))
    (MvPolynomial.X (localY (1 : Fin 2))) (fun _ => Commute.all _ _)

private theorem plainToDiff_CCC (q : Polynomial L) :
    plainToDiff (C (C (C q))) = Polynomial.aeval (MvPolynomial.X none) q := by
  simp only [plainToDiff, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C]

private theorem plainToDiff_CCX : plainToDiff (C (C Polynomial.X)) = MvPolynomial.X (some 0) := by
  simp only [plainToDiff, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private theorem plainToDiff_CX : plainToDiff (C Polynomial.X) = MvPolynomial.X (some 1) := by
  simp only [plainToDiff, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private theorem plainToDiff_X : plainToDiff Polynomial.X = MvPolynomial.X (some 2) := by
  simp only [plainToDiff, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]

private theorem ηToTE_CCC (q : Polynomial L) :
    ηToTE (C (C (C q))) = Polynomial.aeval (MvPolynomial.X (localT 2)) q := by
  simp only [ηToTE, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C]

private theorem ηToTE_CCX : ηToTE (C (C Polynomial.X)) = MvPolynomial.X (localT 2) * MvPolynomial.X (localE 2) := by
  simp only [ηToTE, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private theorem ηToTE_CX : ηToTE (C Polynomial.X) = MvPolynomial.X (localY (0 : Fin 2)) := by
  simp only [ηToTE, Polynomial.eval₂AlgHom_apply, AlgHom.coe_toRingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private theorem ηToTE_X : ηToTE Polynomial.X = MvPolynomial.X (localY (1 : Fin 2)) := by
  simp only [ηToTE, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_X]

private theorem ηToTE_comp_atPhysical2L (x r : L) :
    ηToTE.comp (atPhysical2L x r) = (unscaledLocalSubstitution 2 x r).comp plainToDiff := by
  have hcomp : unscaledLocalSubstitution 2 x r =
      (unscaledLocalSubstitution 2 (0 : L) 0).comp (globalPointTranslation x r) := by
    rw [unscaledLocalSubstitution_comp_globalPointTranslation]
    simp
  have hY0 : unscaledLocalSubstitution 2 x r (MvPolynomial.X (some 0)) =
      MvPolynomial.C r + MvPolynomial.X (localT 2) * MvPolynomial.X (localY (0 : Fin 2)) -
        MvPolynomial.X (localT 2) ^ 2 * MvPolynomial.X (localY (1 : Fin 2)) +
        MvPolynomial.X (localT 2) * MvPolynomial.X (localE 2) := by
    rw [hcomp, AlgHom.comp_apply, globalPointTranslation_Y_zero, map_add, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq]
    have h0 : unscaledLocalSubstitution 2 (0 : L) 0 (MvPolynomial.X (some 0)) =
        MvPolynomial.X (localT 2) * MvPolynomial.X (localE 2) +
          (MvPolynomial.X (localT 2) * MvPolynomial.X (localY (0 : Fin 2)) -
            MvPolynomial.X (localT 2) ^ 2 * MvPolynomial.X (localY (1 : Fin 2))) := by
      simp [localCorrection, Fin.sum_univ_two, sub_eq_add_neg]
      ring
    rw [h0]; ring
  apply AlgHom.toRingHom_injective
  apply PoleMoment2Jet.jetHom2_ext
  · intro q
    change ηToTE (atPhysical2L x r (C (C (C q)))) =
      unscaledLocalSubstitution 2 x r (plainToDiff (C (C (C q))))
    rw [atPhysical2L_CCC, ηToTE_CCC, plainToDiff_CCC]
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | monomial n c =>
      simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_add,
        Polynomial.aeval_C, Polynomial.aeval_X, AlgHom.commutes, MvPolynomial.algHom_C,
        unscaledLocalSubstitution_X, MvPolynomial.algebraMap_eq]
      ring
  · change ηToTE (atPhysical2L x r (C (C Polynomial.X))) =
      unscaledLocalSubstitution 2 x r (plainToDiff (C (C Polynomial.X)))
    rw [atPhysical2L_CCX, plainToDiff_CCX, hY0]
    have hjet : ∀ q : Polynomial L, ηToTE (PoleMoment2Jet.jetConstant2 q) =
        Polynomial.aeval (MvPolynomial.X (localT 2)) q := fun q => ηToTE_CCC q
    simp only [map_add, map_sub, map_mul, hjet, ηToTE_CCX, ηToTE_CX, ηToTE_X,
      Polynomial.aeval_C, Polynomial.aeval_X, map_pow, MvPolynomial.algebraMap_eq]
  · change ηToTE (atPhysical2L x r (C Polynomial.X)) =
      unscaledLocalSubstitution 2 x r (plainToDiff (C Polynomial.X))
    rw [atPhysical2L_CX, ηToTE_CX, plainToDiff_CX]
    exact (unscaledLocalSubstitution_Y_succ (R := L) (d := 2) x r 0).symm
  · change ηToTE (atPhysical2L x r Polynomial.X) =
      unscaledLocalSubstitution 2 x r (plainToDiff Polynomial.X)
    rw [atPhysical2L_X, ηToTE_X, plainToDiff_X]
    exact (unscaledLocalSubstitution_Y_succ (R := L) (d := 2) x r 1).symm

private def localExp (t h b c : ℕ) : LocalVariable 2 →₀ ℕ :=
  Finsupp.single (localT 2) t + Finsupp.single (localE 2) h +
    Finsupp.single (localY (0 : Fin 2)) b + Finsupp.single (localY (1 : Fin 2)) c

private theorem localExp_eq_iff {t₁ h₁ b₁ c₁ t₂ h₂ b₂ c₂ : ℕ} :
    localExp t₁ h₁ b₁ c₁ = localExp t₂ h₂ b₂ c₂ ↔
      t₁ = t₂ ∧ h₁ = h₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  constructor
  · intro he
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := DFunLike.congr_fun he (localT 2); simpa [localExp, localT, localE, localY, localAux] using this
    · have := DFunLike.congr_fun he (localE 2); simpa [localExp, localT, localE, localY, localAux] using this
    · have := DFunLike.congr_fun he (localY (0 : Fin 2)); simpa [localExp, localT, localE, localY, localAux] using this
    · have := DFunLike.congr_fun he (localY (1 : Fin 2)); simpa [localExp, localT, localE, localY, localAux] using this
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

private theorem ηToTE_coeff (Q : PlainJet2) (e₂ e₁ b a : ℕ) :
    (ηToTE Q).coeff (localExp (a + b) b e₁ e₂) = (((Q.coeff e₂).coeff e₁).coeff b).coeff a := by
  induction Q using Polynomial.induction_on' with
  | add P₁ P₂ ih₁ ih₂ => simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂]
  | monomial n₂ P₁ =>
    induction P₁ using Polynomial.induction_on' with
    | add Q₁ Q₂ ih₁ ih₂ =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂]
    | monomial n₁ P₀ =>
      induction P₀ using Polynomial.induction_on' with
      | add R₁ R₂ ih₁ ih₂ =>
        simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂]
      | monomial n₀ q =>
        induction q using Polynomial.induction_on' with
        | add q₁ q₂ ih₁ ih₂ =>
          simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂]
        | monomial na c =>
          have hmon : ηToTE (Polynomial.monomial n₂ (Polynomial.monomial n₁
              (Polynomial.monomial n₀ (Polynomial.monomial na c)))) =
              MvPolynomial.monomial (localExp (na + n₀) n₀ n₁ n₂) c := by
            simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
              ηToTE_CCC, ηToTE_CCX, ηToTE_CX, ηToTE_X,
              Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq,
              MvPolynomial.C_apply, MvPolynomial.X, MvPolynomial.monomial_pow,
              MvPolynomial.monomial_mul, one_pow, mul_one, localExp]
            simp only [smul_add, Finsupp.smul_single, smul_eq_mul, mul_one, zero_add, add_zero]
            congr 1
            rw [Finsupp.single_add]
            abel
          rw [hmon, MvPolynomial.coeff_monomial]
          simp only [localExp_eq_iff, Polynomial.coeff_monomial]
          by_cases h2 : n₂ = e₂
          · subst h2; simp only [↓reduceIte]
            by_cases h1 : n₁ = e₁
            · subst h1; simp only [↓reduceIte]
              by_cases h0 : n₀ = b
              · subst h0; simp only [↓reduceIte]
                by_cases ha : na = a
                · subst ha; simp
                · have hne : ¬ (na + n₀ = a + n₀ ∧ n₀ = n₀ ∧ n₁ = n₁ ∧ n₂ = n₂) := by omega
                  simp [ha, hne]
              · have hne : ¬ (na + n₀ = a + b ∧ n₀ = b ∧ n₁ = n₁ ∧ n₂ = n₂) := by omega
                simp [h0, hne]
            · have hne : ¬ (na + n₀ = a + b ∧ n₀ = b ∧ n₁ = e₁ ∧ n₂ = n₂) := by omega
              simp [h1, hne]
          · have hne : ¬ (na + n₀ = a + b ∧ n₀ = b ∧ n₁ = e₁ ∧ n₂ = e₂) := by omega
            simp [h2, hne]

private def extractSeed2 (e : Fin 2 →₀ ℕ) : Source2 →ₗ[L] DifferentialPolynomial L 2 :=
  plainToDiff.toLinearMap.comp (sliceSeedPoly e)

private theorem coeffAt2_atPhysical2_eq_local (e : Fin 2 →₀ ℕ) (x r : L) (P : Source2)
    (e₂ e₁ b a : ℕ) :
    coeffAt2 (atPhysical2 x r P) e₂ e₁ b a e =
      (unscaledLocalSubstitution 2 x r (extractSeed2 e P)).coeff (localExp (a + b) b e₁ e₂) := by
  rw [← sliceSeedPoly_coeff, sliceSeedPoly_atPhysical2, ← ηToTE_coeff]
  have h := AlgHom.congr_fun (ηToTE_comp_atPhysical2L x r) (sliceSeedPoly e P)
  exact congrArg (fun f : LocalPolynomial L 2 => f.coeff (localExp (a + b) b e₁ e₂)) h

/-! ## 2. Translation to Origin Over `L` & Base-Change From `ZMod p` -/

private def sourceSpanL (A : ℕ) (s : CJ0.Source) : Submodule L (DifferentialPolynomial L 2) :=
  Submodule.span L (Set.range fun i : CJ0.ColumnIndex A s => (CJ0.column A s i).polynomial)

private theorem lower_mem_L {s : CJ0.Source} (hs : CJ0.ShapeOK s) {c b a : ℕ}
    (h : (⟨c, b, a⟩ : CJ0.Jet) ∈ s.E) {a' : ℕ} (ha : a' ≤ a) :
    (⟨c, b, a'⟩ : CJ0.Jet) ∈ s.E := by
  induction a with
  | zero => rw [Nat.eq_zero_of_le_zero ha]; exact h
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le ha with rfl | hlt
    · exact h
    · exact ih (hs.lower _ h (Nat.succ_pos a)) (Nat.le_of_lt_succ hlt)

private theorem translated_column_mem_L {A : ℕ} {s : CJ0.Source} (hs : CJ0.ShapeOK s)
    (center received : L) (i : CJ0.ColumnIndex A s) :
    globalPointTranslation center received (CJ0.column A s i).polynomial ∈ sourceSpanL A s := by
  classical
  let col := CJ0.column A s i
  change globalPointTranslation center received col.polynomial ∈ sourceSpanL A s
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  simp only [sourceMonomial, map_mul, map_pow, map_prod, globalPointTranslation_X,
    globalPointTranslation_Y_zero, globalPointTranslation_Y_succ]
  rw [add_comm (MvPolynomial.C center), add_comm (MvPolynomial.C received), add_pow, add_pow,
    Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem; intro x hx
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem; intro a ha
  have hx' : x ≤ i.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have ha' : a ≤ i.1.val.a := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  let j : CJ0.Jet := ⟨i.1.val.c, i.1.val.b, a⟩
  have hj : j ∈ s.E := by
    rcases i with ⟨⟨⟨c, b, a₀⟩, hi⟩, i⟩
    exact lower_mem_L hs hi ha'
  have hq : j.q ≤ i.1.val.q := Nat.add_le_add_right (Nat.add_le_add_right ha' _) _
  have hwidth : CJ0.width A s i.1.val ≤ CJ0.width A s j :=
    Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_left CJ0.N hq) _) _
  let l : CJ0.ColumnIndex A s := ⟨⟨j, hj⟩, ⟨x, (hx'.trans_lt i.2.isLt).trans_le hwidth⟩⟩
  let coeff : L := center ^ (col.x - x) * (col.x.choose x : L) *
    received ^ (col.y₀ - a) * (col.y₀.choose a : L)
  have hterm :
      (MvPolynomial.X none ^ x * MvPolynomial.C center ^ (col.x - x) * (col.x.choose x : DifferentialPolynomial L 2) *
        (MvPolynomial.X (some 0) ^ a * MvPolynomial.C received ^ (col.y₀ - a) *
          (col.y₀.choose a : DifferentialPolynomial L 2))) *
        (∏ j, MvPolynomial.X (some j.succ) ^ col.higher j) =
      coeff • (CJ0.column A s l).polynomial := by
    rw [MvPolynomial.smul_eq_C_mul, SourceColumn.polynomial_eq_sourceMonomial]
    change _ = MvPolynomial.C coeff * sourceMonomial x a col.higher
    simp only [coeff, sourceMonomial, map_mul, map_pow, map_natCast]
    ac_rfl
  rw [hterm]
  exact (sourceSpanL A s).smul_mem coeff (Submodule.subset_span (Set.mem_range_self l))

private def pointMatrixL (A : ℕ) (s : CJ0.Source) (center received : L) :
    Matrix (LowContactIndex 2 s.m) (CJ0.ColumnIndex A s) L :=
  fun row i => localConstraintCoordinatesAt s.m center received (CJ0.column A s i).polynomial row

private theorem point_rank_le_origin_L {A : ℕ} {s : CJ0.Source} (hs : CJ0.ShapeOK s)
    (center received : L) :
    (pointMatrixL A s center received).rank ≤ (pointMatrixL A s 0 0).rank := by
  classical
  let loc := localConstraintCoordinatesAt (R := L) (d := 2) s.m 0 0
  have hmap : (sourceSpanL A s).map loc =
      Submodule.span L (Set.range (pointMatrixL A s 0 0).col) := by
    rw [sourceSpanL, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span L (Set.range (pointMatrixL A s center received).col) ≤
      Submodule.span L (Set.range (pointMatrixL A s 0 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hmap]
    exact ⟨globalPointTranslation center received (CJ0.column A s i).polynomial,
      translated_column_mem_L hs center received i,
      (Sol1.C42.coordinates_translation s.m center received (CJ0.column A s i).polynomial).symm⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  letI := FiniteDimensional.span_of_finite (K := L)
    (Set.finite_range (pointMatrixL A s 0 0).col)
  exact Submodule.finrank_mono hspan

private theorem origin_rank_le_native_L (A : ℕ) (s : CJ0.Source) :
    (pointMatrixL A s 0 0).rank ≤ CJ0.originRank A s := by
  let φ : ZMod CJ0.p →+* L := ZMod.castHom dvd_rfl L
  let P := localConstraintMatrix s.m
    (fun _ : Unit => (0 : ZMod CJ0.p)) (fun _ => 0) (CJ0.column A s)
  let row : LowContactIndex 2 s.m → Unit × LowContactIndex 2 s.m := fun r => ((), r)
  have hmap : P.map φ =
      localConstraintMatrix s.m (fun _ : Unit => (0 : L)) (fun _ => 0) (CJ0.column A s) := by
    ext r j
    simp only [Matrix.map_apply, localConstraintMatrix_apply, P]
    rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
    simp [SourceColumn.polynomial, map_zero]
  calc
    (pointMatrixL A s 0 0).rank
        = ((P.map φ).submatrix row id).rank := by rw [hmap]; rfl
    _ ≤ (P.map φ).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ P.rank := Matrix.rank_map_le φ P
    _ = CJ0.originRank A s := rfl

private theorem point_rank_m59_le (A : ℕ) (hA : 59 ≤ 59 * A - CJ0.N * 80) (x r : L) :
    (pointMatrixL A Front6963ListBank.source x r).rank ≤ 200031 := by
  have tail : CJ0.SilentTail Front6963ListBank.source 81 := by
    intro j hj hcut
    have hq : j.q ≤ 80 := (Front6963ListBank.native_shape.support j hj).1
    omega
  calc
    (pointMatrixL A Front6963ListBank.source x r).rank
        ≤ (pointMatrixL A Front6963ListBank.source 0 0).rank :=
          point_rank_le_origin_L Front6963ListBank.native_shape x r
    _ ≤ CJ0.originRank A Front6963ListBank.source :=
          origin_rank_le_native_L A Front6963ListBank.source
    _ ≤ CJ0.prefixRank Front6963ListBank.source 81 :=
          CJ0_1.proof A Front6963ListBank.source 81 Front6963ListBank.native_shape hA le_rfl tail
    _ ≤ 200031 := Front6963ListBank.prefix_bound

/-! ## 3. Global 2-Jet Physical Contact Rank Bound (`physRank2_m59`) -/

private def seedExps (U : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)
    |>.image (fun p => Finsupp.single 0 p.1 + Finsupp.single 1 p.2)

private theorem mem_seedExps {U : ℕ} {e : Fin 2 →₀ ℕ} :
    e ∈ seedExps U ↔ seedWeight e ≤ U := by
  simp only [seedExps, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
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

private theorem card_seedExps (U : ℕ) : (seedExps U).card = triangle U := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => Finsupp.single (0 : Fin 2) p.1 + Finsupp.single 1 p.2)
      (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U) : Set (ℕ × ℕ)) := by
    intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
    exact Prod.ext (by simpa using h0) (by simpa using h1)
  rw [seedExps, Finset.card_image_of_injOn hinj]
  have hfib : (((Finset.range (U + 1)) ×ˢ (Finset.range (U + 1))).filter (fun p => p.1 + p.2 ≤ U)).card =
      ∑ a ∈ Finset.range (U + 1), (U + 1 - a) := by
    induction U with
    | zero => decide
    | succ U ih =>
      have hcard : (((Finset.range (U + 2)) ×ˢ (Finset.range (U + 2))).filter (fun p => p.1 + p.2 ≤ U + 1)).card =
          ∑ a ∈ Finset.range (U + 2), (((Finset.range (U + 2)).filter (fun b => a + b ≤ U + 1)).card) := by
        rw [Finset.card_filter, Finset.sum_product]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.card_filter]
      rw [hcard]
      apply Finset.sum_congr rfl; intro a ha
      have ha' : a ≤ U + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have heq : (Finset.range (U + 2)).filter (fun b => a + b ≤ U + 1) = Finset.range (U + 2 - a) := by
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

private theorem extractSeed2_mem_sourceSpan (h U W : ℕ) (e : Fin 2 →₀ ℕ)
    {P : Source2} (hP : P ∈ ambient2 h (shape2_m59 U) W) :
    extractSeed2 e P ∈ sourceSpanL (W + 104 * (2 * h) + 25 + CJ0.N * 80 + 59) Front6963ListBank.source := by
  let A' := W + 104 * (2 * h) + 25 + CJ0.N * 80 + 59
  let Q := sliceSeedPoly e P
  change plainToDiff Q ∈ sourceSpanL A' Front6963ListBank.source
  rw [Q.as_sum_support_C_mul_X_pow, map_sum]
  apply Submodule.sum_mem; intro e₂ _
  rw [map_mul, map_pow, (Q.coeff e₂).as_sum_support_C_mul_X_pow, map_sum, map_sum, Finset.sum_mul]
  apply Submodule.sum_mem; intro e₁ _
  rw [map_mul, map_pow, map_mul, map_pow, ((Q.coeff e₂).coeff e₁).as_sum_support_C_mul_X_pow,
    map_sum, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem; intro e₀ _
  rw [map_mul, map_pow, map_mul, map_pow, map_mul, map_pow,
    (((Q.coeff e₂).coeff e₁).coeff e₀).as_sum_support_C_mul_X_pow,
    map_sum, map_sum, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem; intro a ha
  have hne : coeffAt2 P e₂ e₁ e₀ a e ≠ 0 := by
    rw [← sliceSeedPoly_coeff]
    exact Polynomial.mem_support_iff.mp ha
  have hel : trueEligible2 h (shape2_m59 U) W e₂ e₁ e₀ a e := by
    by_contra hnot
    exact hne (hP e₂ e₁ e₀ a e hnot)
  obtain ⟨hB, hJ, hC, _, hW⟩ := hel
  have hjmem : (⟨e₂, e₁, e₀⟩ : CJ0.Jet) ∈ Front6963ListBank.source.E := by
    change (⟨e₂, e₁, e₀⟩ : CJ0.Jet) ∈ CJ0.fullBox 80 24 10
    rw [CJ0.mem_fullBox (by decide) (by decide)]
    exact ⟨hB, hJ, hC⟩
  have hwidth : a < CJ0.width A' Front6963ListBank.source ⟨e₂, e₁, e₀⟩ := by
    unfold CJ0.width Front6963ListBank.source CJ0.Jet.q CJ0.Jet.v CJ0.Jet.a CJ0.Jet.b CJ0.Jet.c
    dsimp only [A', shape2_m59, PoleMoment2Jet.jetIdx] at hB hJ hW ⊢
    have hq_le : CJ0.N * (e₀ + e₁ + e₂) ≤ CJ0.N * 80 := Nat.mul_le_mul_left CJ0.N hB
    omega
  let colIdx : CJ0.ColumnIndex A' Front6963ListBank.source := ⟨⟨⟨e₂, e₁, e₀⟩, hjmem⟩, ⟨a, hwidth⟩⟩
  have hterm :
      plainToDiff (C (C (C (C ((((Q.coeff e₂).coeff e₁).coeff e₀).coeff a) * Polynomial.X ^ a)))) *
        plainToDiff (C (C Polynomial.X)) ^ e₀ *
        plainToDiff (C Polynomial.X) ^ e₁ *
        plainToDiff Polynomial.X ^ e₂ =
      ((((Q.coeff e₂).coeff e₁).coeff e₀).coeff a) •
        (CJ0.column A' Front6963ListBank.source colIdx).polynomial := by
    rw [MvPolynomial.smul_eq_C_mul, SourceColumn.polynomial_eq_sourceMonomial]
    simp only [plainToDiff_CCC, plainToDiff_CCX, plainToDiff_CX, plainToDiff_X,
      map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq,
      sourceMonomial, CJ0.column, colIdx,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [CJ0.Jet.a, CJ0.Jet.b, CJ0.Jet.c]
    rw [show (Fin.succ (0 : Fin 2) : Fin 3) = 1 from rfl,
      show (Fin.succ (1 : Fin 2) : Fin 3) = 2 from rfl]
    ring
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self colIdx))

/-- **Exact Mod-`p` Physical Contact Rank Bound for `shape2_m59 U` (`physRank2_m59`)**:
    `finrank L (ambient2 h (shape2_m59 U) W) ≤ triangle U * 262144 * 200031 + finrank L (contacted2 h word (shape2_m59 U) W)`. -/
theorem physRank2_m59 (h U W : ℕ) (word : I → L) :
    Module.finrank L (ambient2 h (shape2_m59 U) W) ≤
      triangle U * 262144 * 200031 + Module.finrank L (contacted2 h word (shape2_m59 U) W) := by
  classical
  let s := shape2_m59 U
  let A' := W + 104 * (2 * h) + 25 + CJ0.N * 80 + 59
  let SE := seedExps U
  let Φ_pt (i : I) (e : SE) : ambient2 h s W →ₗ[L] (LowContactIndex 2 59 → L) :=
    (localConstraintCoordinatesAt (R := L) (d := 2) 59 (nodeL i) (word i)).comp
      ((extractSeed2 e.1).comp (ambient2 h s W).subtype)
  let Φ : ambient2 h s W →ₗ[L] (I × SE → LowContactIndex 2 59 → L) :=
    LinearMap.pi fun p => Φ_pt p.1 p.2
  -- Step 1: Every `P ∈ ker Φ` lies in `contacted2 h word s W`!
  have hker_mem : ∀ P : LinearMap.ker Φ, (P.1 : Source2) ∈ contacted2 h word s W := by
    intro P
    refine ⟨P.1.2, ?_⟩
    intro i a b e₁ e₂ e hlt
    by_cases he : seedWeight e ≤ U
    · have heSE : e ∈ SE := mem_seedExps.mpr he
      have hord : localContactOrder 2 (localExp (a + b) b e₁ e₂) < 59 := by
        rw [localContactOrder_eq]
        have hT : localExp (a + b) b e₁ e₂ (localT 2) = a + b := by
          simp [localExp, localT, localE, localY, localAux]
        have hE : localExp (a + b) b e₁ e₂ (localE 2) = b := by
          simp [localExp, localT, localE, localY, localAux]
        rw [hT, hE]
        change a + b + 2 * b < 59
        dsimp only [s, shape2_m59] at hlt
        omega
      let row : LowContactIndex 2 59 := ⟨localExp (a + b) b e₁ e₂, hord⟩
      have h0 : Φ P.1 (i, ⟨e, heSE⟩) row = 0 := by
        have hker := LinearMap.mem_ker.mp P.2
        exact congrFun (congrFun hker (i, ⟨e, heSE⟩)) row
      rw [coeffAt2_atPhysical2_eq_local]
      exact h0
    · -- `e` has `seedWeight e > U`, so `sliceSeedPoly e P = 0`!
      have hslice0 : sliceSeedPoly e P.1.1 = 0 := by
        apply Polynomial.ext; intro c₂
        apply Polynomial.ext; intro c₁
        apply Polynomial.ext; intro c₀
        apply Polynomial.ext; intro ca
        rw [sliceSeedPoly_coeff]
        simp only [Polynomial.coeff_zero]
        exact P.1.2 c₂ c₁ c₀ ca e (fun hel => he hel.2.2.2.1)
      rw [← sliceSeedPoly_coeff, sliceSeedPoly_atPhysical2, hslice0, map_zero]
      simp
  -- Step 2: `finrank (ker Φ) ≤ finrank (contacted2 h word s W)`
  have hfin_amb : Module.Finite L (ambient2 h s W) := by
    let M := W + (s.B + s.J) * (2 * h) + s.J
    let f : ambient2 h s W →ₗ[L] (TwoJetCaseAKernel.CoeffBox2 s.B M s.U → L) :=
      LinearMap.pi fun u =>
        { toFun := fun P =>
            coeffAt2 P.1 u.1.val u.2.1.val u.2.2.1.val u.2.2.2.1.val
              (TwoJetCaseAKernel.boxExp u.2.2.2.2)
          map_add' := fun P Q => by simp [coeffAt2, PoleMoment2Jet.sourceCoeff2]
          map_smul' := fun c P => by simp [coeffAt2, PoleMoment2Jet.sourceCoeff2] }
    apply Module.Finite.of_injective f
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
      have hM : a ≤ M := by dsimp [M]; omega
      have hU' (j : Fin 2) : e j ≤ s.U := by
        apply le_trans _ hU
        rw [seedWeight, Finsupp.sum_fintype _ _ (by simp)]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      let u : TwoJetCaseAKernel.CoeffBox2 s.B M s.U :=
        (⟨e₂, by omega⟩, ⟨e₁, by omega⟩, ⟨e₀, by omega⟩, ⟨a, by omega⟩,
          fun j => ⟨e j, by have := hU' j; omega⟩)
      have heq_e : TwoJetCaseAKernel.boxExp u.2.2.2.2 = e := by
        ext j; simp [TwoJetCaseAKernel.boxExp, u]
      have hz : f P u = 0 := congrFun hP u
      simpa only [f, LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk, u, heq_e] using hz
    · exact P.2 e₂ e₁ e₀ a e hel
  letI := hfin_amb
  letI := PoleBound2Jet.contacted2_finite h word s W
  let incl : LinearMap.ker Φ →ₗ[L] contacted2 h word s W :=
    { toFun := fun P => ⟨P.1.1, hker_mem P⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj_incl : Function.Injective incl := by
    intro P Q hPQ
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun x : contacted2 h word s W => x.1) hPQ
  have hker_le : Module.finrank L (LinearMap.ker Φ) ≤ Module.finrank L (contacted2 h word s W) :=
    LinearMap.finrank_le_finrank_of_injective hinj_incl
  -- Step 3: For each `(i, e)`, `finrank (range (Φ_pt i e)) ≤ 200031`!
  have hpt_le (i : I) (e : SE) : Module.finrank L (LinearMap.range (Φ_pt i e)) ≤ 200031 := by
    have hsub : LinearMap.range (Φ_pt i e) ≤
        Submodule.span L (Set.range (pointMatrixL A' Front6963ListBank.source (nodeL i) (word i)).col) := by
      rintro _ ⟨P, rfl⟩
      have hmem := extractSeed2_mem_sourceSpan h U W e.1 P.2
      have hmap : (sourceSpanL A' Front6963ListBank.source).map
          (localConstraintCoordinatesAt (R := L) (d := 2) 59 (nodeL i) (word i)) =
          Submodule.span L (Set.range (pointMatrixL A' Front6963ListBank.source (nodeL i) (word i)).col) := by
        rw [sourceSpanL, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [← hmap]
      exact ⟨extractSeed2 e.1 P.1, hmem, rfl⟩
    have hfin_span : Module.Finite L
        (Submodule.span L (Set.range (pointMatrixL A' Front6963ListBank.source (nodeL i) (word i)).col)) :=
      FiniteDimensional.span_of_finite (K := L)
        (Set.finite_range (pointMatrixL A' Front6963ListBank.source (nodeL i) (word i)).col)
    have hle : Module.finrank L (LinearMap.range (Φ_pt i e)) ≤
        Module.finrank L (Submodule.span L (Set.range (pointMatrixL A' Front6963ListBank.source (nodeL i) (word i)).col)) :=
      @Submodule.finrank_mono L (LowContactIndex 2 59 → L) _ _ _ _ _ _ hfin_span hsub
    rw [← Matrix.rank_eq_finrank_span_cols] at hle
    have hA' : 59 ≤ 59 * A' - CJ0.N * 80 := by dsimp [A', CJ0.N]; omega
    exact hle.trans (point_rank_m59_le A' hA' (nodeL i) (word i))
  -- Step 4: Subadditivity of `finrank (range Φ) ≤ ∑ (i, e), finrank (range (Φ_pt i e))`
  let prodSub : Submodule L (I × SE → LowContactIndex 2 59 → L) :=
    Submodule.pi Set.univ fun p => LinearMap.range (Φ_pt p.1 p.2)
  have hrange_le : LinearMap.range Φ ≤ prodSub := by
    rintro _ ⟨P, rfl⟩ p _
    exact ⟨P, rfl⟩
  have hfin_pt (p : I × SE) : Module.Finite L (LinearMap.range (Φ_pt p.1 p.2)) :=
    Module.Finite.range (Φ_pt p.1 p.2)
  let eqv : prodSub ≃ₗ[L] (∀ p : I × SE, LinearMap.range (Φ_pt p.1 p.2)) :=
    { toFun := fun f p => ⟨f.1 p, f.2 p trivial⟩
      invFun := fun g => ⟨fun p => (g p).1, fun p _ => (g p).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin_prod : Module.Finite L prodSub :=
    Module.Finite.equiv eqv.symm
  have hrange_fin : Module.finrank L (LinearMap.range Φ) ≤
      ∑ p : I × SE, Module.finrank L (LinearMap.range (Φ_pt p.1 p.2)) := by
    calc
      Module.finrank L (LinearMap.range Φ)
          ≤ Module.finrank L prodSub := Submodule.finrank_mono hrange_le
      _ = Module.finrank L (∀ p : I × SE, LinearMap.range (Φ_pt p.1 p.2)) := eqv.finrank_eq
      _ = ∑ p : I × SE, Module.finrank L (LinearMap.range (Φ_pt p.1 p.2)) := Module.finrank_pi_fintype L
  have hsum_le : ∑ p : I × SE, Module.finrank L (LinearMap.range (Φ_pt p.1 p.2)) ≤
      triangle U * 262144 * 200031 := by
    calc
      ∑ p : I × SE, Module.finrank L (LinearMap.range (Φ_pt p.1 p.2))
          ≤ ∑ _p : I × SE, 200031 := Finset.sum_le_sum fun p _ => hpt_le p.1 p.2
      _ = Fintype.card (I × SE) * 200031 := by simp
      _ = (Fintype.card I * Fintype.card SE) * 200031 := by rw [Fintype.card_prod]
      _ = triangle U * 262144 * 200031 := by
            rw [ProximityPrize.Benchmark.IRSProfile.card_index, Fintype.card_coe, card_seedExps]
            ring
  have hrank_null := Φ.finrank_range_add_finrank_ker
  dsimp only [s] at hrank_null hker_le
  omega

#print axioms physRank2_m59

end
end TwoJetCaseAFX
