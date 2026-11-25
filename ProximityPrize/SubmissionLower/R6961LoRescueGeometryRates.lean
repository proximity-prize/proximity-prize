import ProximityPrize.SubmissionLower.TwoJetCaseAFX
import ProximityPrize.SubmissionLower.R6960ThirdPole
import ProximityPrize.SubmissionLower.R6961LoRescueSource6961
import ProximityPrize.SubmissionLower.R6961LoHelperSource
import ProximityPrize.SubmissionLower.R6961ExceptionalStage
import ProximityPrize.SubmissionLower.R6961Front6961PoleChart
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option Elab.async false

-- merged module TwoJetCaseAFXContact
section Merged_TwoJetCaseAFXContact

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

/-!
# 2-Jet Contact Vanishing & Prolongation Mark Vanishing (`TwoJetCaseAFXContact`)

Proves the 2-jet root-count vanishing theorem for `P₀ ∈ complete2 Crt word s W` (`W < s.m * A`):
1. `composed2`: evaluates `Source2` at `(t, X, S, S', hasseDeriv 2 S)`.
2. `composed2_degree`: `(composed2 t S P₀).natDegree ≤ W + (s.B + s.J) * (2 * h)`.
3. `composed2_contact`: `(X - C (nodeL k)) ^ s.m ∣ composed2 t S P₀` via the exact 3rd-order
   Taylor remainder `(X - C x)^3 ∣ S - C r - (X - C x)*S' + (X - C x)^2 * hasseDeriv 2 S`.
4. `specialized_poles_2jet`: `poleProduct D ^ (s.B + s.J) ∣ composed2 (seedPair z) (liftPoly S) P₀`.
5. `contact_vanish_2jet`: `composed2 (seedPair z) (liftPoly S) P₀ = 0` whenever `W < s.m * A`.
6. `prolong_vanish_at_mark` & `prolongSubst_vanish_at_mark`:
   if `jetAt G z S = 0`, then `jetAt (prolongSubst (prolongA G) (prolongB1 G) s.C (centerEval2 P₀)) z S = 0`!
-/

namespace TwoJetCaseAFX
noncomputable section

open Polynomial Finset
open K1 (I K node)
open K1_14 (L FX Seeds Equation Jet liftPoly atX graphEval jetAt seedEmbedding)
open K1_14_1 (SeedPoly SeedField PoleData CRTLift poleProduct rawBlock crtPolynomial seedPair
  MarkResidues nodeL residueAt otherBlock seedInField)
open K1_14_1_2 (markedLift markedLift_residue)
open PoleMoment2Jet (Shape2 jetIdx jetConstant2 forward2 forward2_as_substitute
  substitute2 substitute2_base substitute2_y0 substitute2_y1 substitute2_y2)
open PoleBound2Jet (Source2 RawSource2 coeffAt2 trueEligible2 ambient2 atPhysical2 physical2
  poleSpace2 contacted2 complete2)
open TwoJetRescueBridge (Jet2 centerEval2 prolongSubst prolongSubst_eval_zero)
open TwoJetCaseADriver (mapDeriv mapDeriv_coeff mapDeriv_zero mapDeriv_add)
open scoped BigOperators Polynomial Classical

/-! ## 1. 2-Jet Composed Evaluation & Degree Bound -/

def evalFour {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v w : R) : Polynomial (Polynomial (Polynomial (Polynomial A))) →+* R :=
  eval₂RingHom (eval₂RingHom (eval₂RingHom (eval₂RingHom f x) y) v) w

def composed2 (t : Fin 2 → L) (S : Polynomial L) : Source2 →+* Polynomial L :=
  evalFour (C.comp (MvPolynomial.eval t)) Polynomial.X S S.derivative (hasseDeriv 2 S)

private theorem evalFour_ext {A R : Type*} [CommSemiring A] [CommSemiring R]
    {f g : Polynomial (Polynomial (Polynomial (Polynomial A))) →+* R}
    (hc : ∀ a : A, f (C (C (C (C a)))) = g (C (C (C (C a)))))
    (hx : f (C (C (C Polynomial.X))) = g (C (C (C Polynomial.X))))
    (hy : f (C (C Polynomial.X)) = g (C (C Polynomial.X)))
    (hv : f (C Polynomial.X) = g (C Polynomial.X))
    (hw : f Polynomial.X = g Polynomial.X) : f = g := by
  apply Polynomial.ringHom_ext _ hw
  have h1 : ((f.comp C).comp C).comp C = ((g.comp C).comp C).comp C :=
    Polynomial.ringHom_ext hc hx
  have h2 : (f.comp C).comp C = (g.comp C).comp C :=
    Polynomial.ringHom_ext (DFunLike.congr_fun h1) hy
  have h3 : f.comp C = g.comp C :=
    Polynomial.ringHom_ext (DFunLike.congr_fun h2) hv
  exact DFunLike.congr_fun h3

private theorem evalFour_sum {A R : Type*} [CommSemiring A] [CommSemiring R]
    (f : A →+* R) (x y v w : R) (P : Polynomial (Polynomial (Polynomial (Polynomial A)))) :
    evalFour f x y v w P =
      ∑ e₂ ∈ P.support, (∑ e₁ ∈ (P.coeff e₂).support,
        (∑ e₀ ∈ ((P.coeff e₂).coeff e₁).support,
          (∑ a ∈ (((P.coeff e₂).coeff e₁).coeff e₀).support,
            f ((((P.coeff e₂).coeff e₁).coeff e₀).coeff a) * x ^ a) * y ^ e₀) * v ^ e₁) * w ^ e₂ := by
  simp only [evalFour, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]

private theorem natDegree_hasseDeriv2_le {R : Type*} [CommSemiring R] (p : Polynomial R) :
    (hasseDeriv 2 p).natDegree ≤ p.natDegree - 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [Polynomial.hasseDeriv_coeff]
  have hgt : p.natDegree < n + 2 := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, mul_zero]

theorem composed2_degree {h : ℕ} {s : Shape2} {W : ℕ} {P : Source2}
    (hP : P ∈ ambient2 h s W) (t : Fin 2 → L) (S : Polynomial L)
    (hd : S.natDegree ≤ 131071 + h) :
    (composed2 t S P).natDegree ≤ W + (s.B + s.J) * (2 * h) := by
  let d := 131071 + h
  have hd1 : S.derivative.natDegree ≤ d - 1 :=
    (natDegree_derivative_le S).trans (Nat.sub_le_sub_right hd 1)
  have hd2 : (hasseDeriv 2 S).natDegree ≤ d - 2 :=
    (natDegree_hasseDeriv2_le S).trans (Nat.sub_le_sub_right hd 2)
  rw [composed2, evalFour_sum]
  apply natDegree_sum_le_of_forall_le; intro e₂ _
  rw [Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le; intro e₁ _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le; intro e₀ _
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply natDegree_sum_le_of_forall_le; intro a ha
  have hne : (((P.coeff e₂).coeff e₁).coeff e₀).coeff a ≠ 0 := mem_support_iff.mp ha
  have hw : a + (e₀ + e₁ + e₂) * d ≤ W + (s.B + s.J) * (2 * h) + jetIdx e₁ e₂ := by
    by_contra hn
    apply hne
    ext e
    exact hP e₂ e₁ e₀ a e (fun he => hn he.2.2.2.2)
  refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (by simp : (C _ : Polynomial L).natDegree ≤ 0)
      (by simp : (Polynomial.X ^ a : Polynomial L).natDegree ≤ a))
    (natDegree_pow_le_of_le e₀ hd)) (natDegree_pow_le_of_le e₁ hd1))
    (natDegree_pow_le_of_le e₂ hd2)).trans ?_
  have h1 : e₁ * (d - 1) + e₁ = e₁ * d := by
    have : d - 1 + 1 = d := by dsimp [d]; omega
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, this]
  have h2 : e₂ * (d - 2) + 2 * e₂ = e₂ * d := by
    have : d - 2 + 2 = d := by dsimp [d]; omega
    calc
      e₂ * (d - 2) + 2 * e₂ = e₂ * (d - 2 + 2) := by ring
      _ = e₂ * d := by rw [this]
  unfold jetIdx at hw
  have htot : (e₀ + e₁ + e₂) * d = e₀ * d + e₁ * d + e₂ * d := by ring
  dsimp only [d] at h1 h2 htot hw ⊢
  omega

/-! ## 2. 3rd-Order Taylor Remainder & Contact Divisibility -/

private theorem hasseDeriv2_mul {R : Type*} [CommRing R] (p q : Polynomial R) :
    hasseDeriv 2 (p * q) =
      hasseDeriv 2 p * q + p.derivative * q.derivative + p * hasseDeriv 2 q := by
  rw [Polynomial.hasseDeriv_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  change (hasseDeriv 0 p * hasseDeriv 2 q) + (hasseDeriv 1 p * hasseDeriv 1 q + hasseDeriv 2 p * hasseDeriv 0 q) = _
  simp only [hasseDeriv_zero, hasseDeriv_one, LinearMap.id_apply]
  ring

private theorem derivative_derivative_eq_two_hasseDeriv2 {R : Type*} [CommRing R] (p : Polynomial R) :
    p.derivative.derivative = 2 * hasseDeriv 2 p := by
  ext n
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative,
    show (2 : Polynomial R) = Polynomial.C (2 : R) from (map_ofNat Polynomial.C 2).symm,
    Polynomial.coeff_C_mul, Polynomial.hasseDeriv_coeff]
  have hch : 2 * (n + 2).choose 2 = (n + 2) * (n + 1) := by
    rw [Nat.choose_two_right]
    have heven : Even ((n + 2) * (n + 1)) := by
      rw [mul_comm]; exact Nat.even_mul_succ_self (n + 1)
    have hsub : n + 2 - 1 = n + 1 := by omega
    rw [hsub]
    exact Nat.mul_div_cancel' heven.two_dvd
  have hcast : (2 : R) * ((n + 2).choose 2 : R) = ((n + 2 : ℕ) : R) * ((n + 1 : ℕ) : R) := by
    have := congrArg (Nat.cast (R := R)) hch
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using this
  push_cast at hcast ⊢
  linear_combination p.coeff (n + 2) * hcast.symm

private theorem remainder_order_three (S : Polynomial L) (x r : L) (hx : S.eval x = r) :
    (Polynomial.X - C x) ^ 3 ∣
      S - C r - (Polynomial.X - C x) * S.derivative + (Polynomial.X - C x) ^ 2 * hasseDeriv 2 S := by
  let δ : Polynomial L := Polynomial.X - C x
  have hδ0 : δ.eval x = 0 := by simp [δ]
  have hδ1 : δ.derivative = 1 := by simp [δ]
  have hδ2 : hasseDeriv 2 δ = 0 := by
    ext n
    rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_zero]
    have hlt : δ.natDegree < n + 2 := by
      have : δ.natDegree ≤ 1 := by
        dsimp [δ]; exact (Polynomial.natDegree_sub_le _ _).trans (by simp [Polynomial.natDegree_X_le])
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
  have hδsq0 : (δ ^ 2).eval x = 0 := by simp [hδ0]
  have hδsq1 : (δ ^ 2).derivative = 2 * δ := by
    rw [pow_two, Polynomial.derivative_mul, hδ1]; ring
  have hδsq2 : hasseDeriv 2 (δ ^ 2) = 1 := by
    rw [pow_two, hasseDeriv2_mul, hδ2, hδ1]; ring
  rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  intro k hk
  have he : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases he with rfl | rfl | rfl
  · simp [hasseDeriv_zero, hx]
  · change (hasseDeriv 1 (S - C r - δ * S.derivative + δ ^ 2 * hasseDeriv 2 S)).eval x = 0
    rw [hasseDeriv_one, map_add, map_sub, map_sub, Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_mul, hδ1, hδsq1,
      derivative_derivative_eq_two_hasseDeriv2]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_zero, hδ0, hδsq0]
    ring
  · change (hasseDeriv 2 (S - C r - δ * S.derivative + δ ^ 2 * hasseDeriv 2 S)).eval x = 0
    have hC2 : hasseDeriv 2 (C r : Polynomial L) = 0 := by
      ext n; rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_C]; simp
    rw [map_add, map_sub, map_sub, hC2, hasseDeriv2_mul, hasseDeriv2_mul, hδ2, hδ1, hδsq2, hδsq1,
      derivative_derivative_eq_two_hasseDeriv2]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_zero, hδ0, hδsq0]
    ring

private theorem physical2_substitute (t : Fin 2 → L) (S : Polynomial L) (x r : L) :
    (evalFour (C.comp (MvPolynomial.eval t)) (Polynomial.X - C x)
      (S - C r - (Polynomial.X - C x) * S.derivative + (Polynomial.X - C x) ^ 2 * hasseDeriv 2 S)
      S.derivative (hasseDeriv 2 S)).comp (atPhysical2 x r).toRingHom =
      composed2 t S := by
  let δ : Polynomial L := Polynomial.X - C x
  let η : Polynomial L := S - C r - δ * S.derivative + δ ^ 2 * hasseDeriv 2 S
  let E := evalFour (C.comp (MvPolynomial.eval t)) δ η S.derivative (hasseDeriv 2 S)
  change E.comp (atPhysical2 x r).toRingHom = composed2 t S
  rw [PoleBound2Jet.atPhysical2_as_substitute]
  apply evalFour_ext
  · intro g
    simp [E, composed2, evalFour, substitute2, jetConstant2, RingHom.comp_apply]
  · simp [E, composed2, evalFour, substitute2, jetConstant2, δ, RingHom.comp_apply]
  · simp [E, composed2, evalFour, substitute2, jetConstant2, δ, η, RingHom.comp_apply,
      Polynomial.eval₂_pow, map_pow]
  · simp [E, composed2, evalFour, substitute2, RingHom.comp_apply]
  · simp [E, composed2, evalFour, substitute2, RingHom.comp_apply]

theorem composed2_contact {word : I → L} {s : Shape2} {P : Source2}
    (hP : P ∈ physical2 word s) (t : Fin 2 → L) (S : Polynomial L)
    (k : I) (hk : S.eval (nodeL k) = word k) :
    (Polynomial.X - C (nodeL k)) ^ s.m ∣ composed2 t S P := by
  let x := nodeL k
  let r := word k
  let δ : Polynomial L := Polynomial.X - C x
  let η : Polynomial L := S - C r - δ * S.derivative + δ ^ 2 * hasseDeriv 2 S
  let E := evalFour (C.comp (MvPolynomial.eval t)) δ η S.derivative (hasseDeriv 2 S)
  let Q := atPhysical2 x r P
  change δ ^ s.m ∣ composed2 t S P
  have he : E Q = composed2 t S P := DFunLike.congr_fun (physical2_substitute t S x r) P
  rw [← he]
  dsimp only [E]
  rw [evalFour_sum]
  apply Finset.dvd_sum; intro e₂ _
  apply Dvd.dvd.mul_right
  apply Finset.dvd_sum; intro e₁ _
  apply Dvd.dvd.mul_right
  apply Finset.dvd_sum; intro b _
  rw [Finset.sum_mul]
  apply Finset.dvd_sum; intro a ha
  have hw : s.m ≤ a + 3 * b := by
    by_contra hn
    apply mem_support_iff.mp ha
    ext e
    exact hP k a b e₁ e₂ e (by omega)
  have hη : δ ^ 3 ∣ η := remainder_order_three S x r hk
  have hpow : δ ^ (a + 3 * b) ∣ δ ^ a * η ^ b := by
    rw [pow_add, pow_mul]
    exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hη b)
  exact (pow_dvd_pow _ hw).trans (by simpa only [mul_assoc] using hpow.mul_left _)

/-! ## 3. 2-Jet Pole Specialization & Root-Count Vanishing (`contact_vanish_2jet`) -/

private def regularSeeds2 (t : Fin 2 → L) : Submonoid SeedPoly where
  carrier := {a | MvPolynomial.eval t a ≠ 0}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change MvPolynomial.eval t (a * b) ≠ 0
    rw [map_mul]; exact mul_ne_zero ha hb

private abbrev RegRing2 (t : Fin 2 → L) := Localization (regularSeeds2 t)

private def specReg2 (t : Fin 2 → L) : RegRing2 t →+* L :=
  IsLocalization.lift (g := MvPolynomial.eval t)
    (fun a : regularSeeds2 t => isUnit_iff_ne_zero.mpr a.property)

private def inclGen2 (t : Fin 2 → L) : RegRing2 t →+* SeedField :=
  IsLocalization.lift (g := algebraMap SeedPoly SeedField)
    (fun a : regularSeeds2 t => isUnit_iff_ne_zero.mpr (fun he => a.property (by
      have hz := IsFractionRing.injective SeedPoly SeedField (he.trans (map_zero _).symm)
      simp [hz])))

private theorem inclGen2_injective (t : Fin 2 → L) : Function.Injective (inclGen2 t) := by
  unfold inclGen2
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  have h : regularSeeds2 t ≤ nonZeroDivisors SeedPoly := fun x hx =>
    mem_nonZeroDivisors_iff_ne_zero.mpr (fun he => hx (by simp [he]))
  rw [(IsLocalization.injective (RegRing2 t) h).eq_iff,
    (IsFractionRing.injective SeedPoly SeedField).eq_iff]

private def seedPoly2 (i : Fin 2) : Polynomial L →+* SeedPoly :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X i)

private def localLift2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) : Polynomial (RegRing2 t) :=
  ∑ i, C (IsLocalization.mk' (RegRing2 t) 1
      (⟨seedPoly2 i (Crt.denominator i), by
        have he : (MvPolynomial.eval t).comp (seedPoly2 i) = evalRingHom (t i) := by
          apply Polynomial.ringHom_ext <;> simp [seedPoly2, RingHom.comp_apply]
        change (MvPolynomial.eval t).comp (seedPoly2 i) (Crt.denominator i) ≠ 0
        rw [he]; exact hd i⟩ : regularSeeds2 t)) *
    (Crt.numerator i).map ((algebraMap SeedPoly (RegRing2 t)).comp (seedPoly2 i))

private theorem map_localLift2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift2 Crt t hd).map (inclGen2 t) = crtPolynomial Crt := by
  rw [localLift2, crtPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro i _
  have hm : (algebraMap SeedPoly SeedField).comp (seedPoly2 i) = (seedInField i).toRingHom := by
    apply Polynomial.ringHom_ext <;>
      simp [seedPoly2, seedInField, aeval_def, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply L SeedPoly SeedField]
  have he : algebraMap SeedPoly SeedField (seedPoly2 i (Crt.denominator i)) =
      seedInField i (Crt.denominator i) := RingHom.congr_fun hm (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, inclGen2,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, hm,
    smul_eq_C_mul, map_one, Units.val_inv_eq_inv_val, one_mul,
    IsUnit.liftRight_apply, IsUnit.unit_spec, MonoidHom.domRestrict_apply]
  change C ((algebraMap SeedPoly SeedField (seedPoly2 i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]; rfl

private theorem spec_localLift2 {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (t : Fin 2 → L)
    (hd : ∀ i, (Crt.denominator i).eval (t i) ≠ 0) :
    (localLift2 Crt t hd).map (specReg2 t) = markedLift Crt t := by
  rw [localLift2, markedLift, Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro i _
  have hm : (MvPolynomial.eval t).comp (seedPoly2 i) = evalRingHom (t i) := by
    apply Polynomial.ringHom_ext <;> simp [seedPoly2, RingHom.comp_apply]
  have he : MvPolynomial.eval t (seedPoly2 i (Crt.denominator i)) =
      (Crt.denominator i).eval (t i) := RingHom.congr_fun hm (Crt.denominator i)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, specReg2,
    IsLocalization.lift_mk', IsLocalization.lift_comp, ← RingHom.comp_assoc, hm,
    map_one, Units.val_inv_eq_inv_val, one_mul, IsUnit.liftRight_apply, IsUnit.unit_spec,
    MonoidHom.domRestrict_apply]
  change C ((MvPolynomial.eval t (seedPoly2 i (Crt.denominator i)))⁻¹) * _ = _
  rw [he]

theorem specialized_poles_2jet {h : ℕ} {D : PoleData h} (Crt : CRTLift D)
    {z : K} {S : Polynomial K} (hres : MarkResidues D z S)
    {s : Shape2} {P : Source2} (hp : P ∈ poleSpace2 Crt s) :
    poleProduct D ^ (s.B + s.J) ∣ composed2 (seedPair z) (liftPoly S) P := by
  let t := seedPair z
  have hd (i : Fin 2) : (Crt.denominator i).eval (t i) ≠ 0 := Crt.regular i (t i) (hres i).1
  obtain ⟨U, hU⟩ := markedLift_residue Crt hres
  have hS : liftPoly S = poleProduct D * U + markedLift Crt t := eq_add_of_sub_eq hU
  let T : Polynomial SeedField := U.map (algebraMap L SeedField)
  let H := rawBlock D
  let lift := crtPolynomial Crt
  -- Evaluate `forward2 (poleProduct D) lift P` at `(T, T', hasseDeriv 2 T)`!
  let rawEv : RawSource2 →+* Polynomial SeedField :=
    eval₂RingHom (eval₂RingHom (eval₂RingHom (RingHom.id _) T) T.derivative) (hasseDeriv 2 T)
  have hfwd_ev : rawEv (forward2 (poleProduct D) lift P) =
      evalFour (C.comp (algebraMap SeedPoly SeedField)) Polynomial.X
        (H * T + lift)
        (H * T.derivative + H.derivative * T + lift.derivative)
        (H * hasseDeriv 2 T + H.derivative * T.derivative + hasseDeriv 2 H * T + hasseDeriv 2 lift) P := by
    have hcomp : rawEv.comp (forward2 (poleProduct D) lift).toRingHom =
        evalFour (C.comp (algebraMap SeedPoly SeedField)) Polynomial.X
          (H * T + lift)
          (H * T.derivative + H.derivative * T + lift.derivative)
          (H * hasseDeriv 2 T + H.derivative * T.derivative + hasseDeriv 2 H * T + hasseDeriv 2 lift) := by
      have hHdef : (poleProduct D).map (algebraMap L SeedField) = H := rfl
      have hH1 : (poleProduct D).derivative.map (algebraMap L SeedField) = H.derivative := by
        rw [← Polynomial.derivative_map, hHdef]
      have hH2 : (hasseDeriv 2 (poleProduct D)).map (algebraMap L SeedField) = hasseDeriv 2 H := by
        rw [← Polynomial.hasseDeriv_map, hHdef]
      rw [forward2_as_substitute]
      apply evalFour_ext
      · intro a; simp [rawEv, evalFour, substitute2, jetConstant2, RingHom.comp_apply]
      · simp [rawEv, evalFour, substitute2, jetConstant2, RingHom.comp_apply]
      · simp [rawEv, evalFour, substitute2, jetConstant2, hHdef, lift, RingHom.comp_apply]
      · simp [rawEv, evalFour, substitute2, jetConstant2, hHdef, hH1, lift, RingHom.comp_apply]
      · simp [rawEv, evalFour, substitute2, jetConstant2, hHdef, hH1, hH2, lift, RingHom.comp_apply]
    exact DFunLike.congr_fun hcomp P
  -- From `hp : H^(B+J) ∣ forward2 P`, get `H^(B+J) ∣ rawEv (forward2 P)`!
  obtain ⟨Q, hQ⟩ := hp
  have hdvd_gen : H ^ (s.B + s.J) ∣ rawEv (forward2 (poleProduct D) lift P) := by
    refine ⟨rawEv Q, ?_⟩
    have h := congrArg rawEv hQ
    rw [map_mul] at h
    have hc : rawEv (jetConstant2 (H ^ (s.B + s.J))) = H ^ (s.B + s.J) := by
      rw [map_pow, map_pow]
      simp [rawEv, jetConstant2]
    change rawEv (forward2 (poleProduct D) lift P) = rawEv (jetConstant2 (H ^ (s.B + s.J))) * rawEv Q at h
    rwa [hc] at h
  -- Lift `rawEv (forward2 P)` to `Polynomial (RegRing2 t)` via `localLift2`!
  let Tloc : Polynomial (RegRing2 t) := U.map ((algebraMap SeedPoly (RegRing2 t)).comp MvPolynomial.C)
  let Hloc : Polynomial (RegRing2 t) := (poleProduct D).map ((algebraMap SeedPoly (RegRing2 t)).comp MvPolynomial.C)
  let liftLoc : Polynomial (RegRing2 t) := localLift2 Crt t hd
  let evLoc : Source2 →+* Polynomial (RegRing2 t) :=
    evalFour (C.comp (algebraMap SeedPoly (RegRing2 t))) Polynomial.X
      (Hloc * Tloc + liftLoc)
      (Hloc * Tloc.derivative + Hloc.derivative * Tloc + liftLoc.derivative)
      (Hloc * hasseDeriv 2 Tloc + Hloc.derivative * Tloc.derivative + hasseDeriv 2 Hloc * Tloc + hasseDeriv 2 liftLoc)
  have hH_gen : Hloc.map (inclGen2 t) = H := by
    simp [Hloc, H, rawBlock, Polynomial.map_map]
    congr 1; ext a; simp [inclGen2, IsScalarTower.algebraMap_apply L SeedPoly SeedField]
  have hT_gen : Tloc.map (inclGen2 t) = T := by
    simp [Tloc, T, Polynomial.map_map]
    congr 1; ext a; simp [inclGen2, IsScalarTower.algebraMap_apply L SeedPoly SeedField]
  have hL_gen : liftLoc.map (inclGen2 t) = lift := map_localLift2 Crt t hd
  have hev_gen : (evLoc P).map (inclGen2 t) = rawEv (forward2 (poleProduct D) lift P) := by
    rw [hfwd_ev]
    have hcomp : (Polynomial.mapRingHom (inclGen2 t)).comp evLoc =
        evalFour (C.comp (algebraMap SeedPoly SeedField)) Polynomial.X
          (H * T + lift)
          (H * T.derivative + H.derivative * T + lift.derivative)
          (H * hasseDeriv 2 T + H.derivative * T.derivative + hasseDeriv 2 H * T + hasseDeriv 2 lift) := by
      apply evalFour_ext
      · intro a
        simp [evLoc, evalFour, inclGen2, RingHom.comp_apply]
      · simp [evLoc, evalFour, RingHom.comp_apply]
      · simp [evLoc, evalFour, RingHom.comp_apply, hH_gen, hT_gen, hL_gen]
      · simp [evLoc, evalFour, RingHom.comp_apply, ← Polynomial.derivative_map, hH_gen, hT_gen, hL_gen]
      · simp [evLoc, evalFour, RingHom.comp_apply, ← Polynomial.derivative_map,
          ← Polynomial.hasseDeriv_map, hH_gen, hT_gen, hL_gen]
    exact DFunLike.congr_fun hcomp P
  have hH_spec : Hloc.map (specReg2 t) = poleProduct D := by
    simp [Hloc, Polynomial.map_map]
    have hid : (specReg2 t).comp ((algebraMap SeedPoly (RegRing2 t)).comp MvPolynomial.C) = RingHom.id L := by
      ext a; simp [specReg2]
    rw [hid, Polynomial.map_id]
  have hev_spec : (evLoc P).map (specReg2 t) = composed2 t (liftPoly S) P := by
    have hT : Tloc.map (specReg2 t) = U := by
      simp [Tloc, Polynomial.map_map]
      have hid : (specReg2 t).comp ((algebraMap SeedPoly (RegRing2 t)).comp MvPolynomial.C) = RingHom.id L := by
        ext a; simp [specReg2]
      rw [hid, Polynomial.map_id]
    have hL : liftLoc.map (specReg2 t) = markedLift Crt t := spec_localLift2 Crt t hd
    have hS1 : (liftPoly S).derivative = poleProduct D * U.derivative + (poleProduct D).derivative * U +
        (markedLift Crt t).derivative := by
      rw [hS, Polynomial.derivative_add, Polynomial.derivative_mul]; ring
    have hS2 : hasseDeriv 2 (liftPoly S) = poleProduct D * hasseDeriv 2 U +
        (poleProduct D).derivative * U.derivative + hasseDeriv 2 (poleProduct D) * U +
        hasseDeriv 2 (markedLift Crt t) := by
      rw [hS, map_add, hasseDeriv2_mul]; ring
    have hcomp : (Polynomial.mapRingHom (specReg2 t)).comp evLoc = composed2 t (liftPoly S) := by
      apply evalFour_ext
      · intro a; simp [evLoc, composed2, evalFour, specReg2, RingHom.comp_apply]
      · simp [evLoc, composed2, evalFour, RingHom.comp_apply]
      · simp [evLoc, composed2, evalFour, RingHom.comp_apply, hH_spec, hT, hL, hS]
      · simp [evLoc, composed2, evalFour, RingHom.comp_apply, ← Polynomial.derivative_map,
          hH_spec, hT, hL, hS1]
      · simp [evLoc, composed2, evalFour, RingHom.comp_apply, ← Polynomial.derivative_map,
          ← Polynomial.hasseDeriv_map, hH_spec, hT, hL, hS2]
    exact DFunLike.congr_fun hcomp P
  -- Since `Hloc ^ (s.B + s.J)` is monic, `(evLoc P) %ₘ Hloc^(s.B+s.J) = 0` follows from injectivity of `inclGen2 t`!
  have hmonic : (Hloc ^ (s.B + s.J)).Monic :=
    (((D.monic 0).mul (D.monic 1)).map _).pow _
  have hmod_zero : evLoc P %ₘ (Hloc ^ (s.B + s.J)) = 0 := by
    apply (Polynomial.map_eq_zero_iff (inclGen2_injective t)).mp
    rw [Polynomial.map_modByMonic (inclGen2 t) hmonic, hev_gen]
    have hHpow : (Hloc ^ (s.B + s.J)).map (inclGen2 t) = H ^ (s.B + s.J) := by
      rw [Polynomial.map_pow, hH_gen]
    have hHmonic : (H ^ (s.B + s.J)).Monic :=
      (((D.monic 0).mul (D.monic 1)).map _).pow _
    rw [hHpow, Polynomial.modByMonic_eq_zero_iff_dvd hHmonic]
    exact hdvd_gen
  have hdvd_loc : Hloc ^ (s.B + s.J) ∣ evLoc P :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mp hmod_zero
  have hdvd_spec := map_dvd (Polynomial.mapRingHom (specReg2 t)) hdvd_loc
  rw [Polynomial.coe_mapRingHom, hev_spec, Polynomial.map_pow, hH_spec] at hdvd_spec
  exact hdvd_spec

/-- **2-Jet Root-Count Vanishing (`contact_vanish_2jet`)**:
    Any `P₀ ∈ complete2 Crt word s W` with `W < s.m * A` vanishes identically under
    `composed2 (seedPair z) (liftPoly S)` at every mark `(z, S)` with `≥ A` hits and
    `(liftPoly S).natDegree ≤ 131071 + h`. -/
theorem contact_vanish_2jet {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    (z : K) (S : Polynomial K) (hres : MarkResidues D z S)
    (hdeg : (liftPoly S).natDegree ≤ 131071 + h)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hhits : ∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k)
    {s : Shape2} {W : ℕ} (hW : W < s.m * A) {P₀ : Source2}
    (hP : P₀ ∈ complete2 Crt word s W) :
    composed2 (seedPair z) (liftPoly S) P₀ = 0 := by
  let Q := composed2 (seedPair z) (liftPoly S) P₀
  have hQdeg : Q.natDegree ≤ W + (s.B + s.J) * (2 * h) :=
    composed2_degree hP.1.1 (seedPair z) (liftPoly S) hdeg
  have hQpole : poleProduct D ^ (s.B + s.J) ∣ Q :=
    specialized_poles_2jet Crt hres hP.2
  have hQhit : ∀ k ∈ hits, (Polynomial.X - C (nodeL k)) ^ s.m ∣ Q :=
    fun k hk => composed2_contact hP.1.2 (seedPair z) (liftPoly S) k (hhits k hk)
  by_contra hne
  obtain ⟨T, hT⟩ := hQpole
  have hTne : T ≠ 0 := fun hz => hne (by change Q = 0; rw [hT, hz, mul_zero])
  have hmonic : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
  have hDdeg : (poleProduct D).natDegree = 2 * h := by
    rw [poleProduct, natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hTdeg : T.natDegree ≤ W := by
    rw [hT, natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne, natDegree_pow, hDdeg] at hQdeg
    omega
  have hroot (k : I) : IsCoprime (Polynomial.X - C (nodeL k)) (poleProduct D) := by
    refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    simpa [IsRoot, poleProduct] using mul_ne_zero (hnode 0 k) (hnode 1 k)
  have hcontacts (k : I) (hk : k ∈ hits) : (Polynomial.X - C (nodeL k)) ^ s.m ∣ T :=
    (hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hQhit k hk)
  have hinj : Function.Injective nodeL := (algebraMap K L).injective.comp node.injective
  exact hTne (K1_11.eq_zero_of_many_contacts hits nodeL hinj s.m T hcontacts
    (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard))))

/-! ## 4. Prolongation Vanishing at Marks (`prolongSubst_vanish_at_mark`) -/

private def jetMarkEval (z : K) (S : Polynomial K) : Jet →+* FX :=
  eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)

private theorem jetMarkEval_eq (z : K) (S : Polynomial K) (P : Jet) :
    jetMarkEval z S P = jetAt P z S := rfl

private theorem composed2_center (z : K) (S : Polynomial K) (P₀ : Source2) :
    Polynomial.eval₂ (jetMarkEval z S) (atX (hasseDeriv 2 S)) (centerEval2 P₀) =
      algebraMap (Polynomial L) FX (composed2 (seedPair z) (liftPoly S) P₀) := by
  let f := algebraMap (Polynomial L) FX
  have hcomp :
      (Polynomial.eval₂RingHom (jetMarkEval z S) (atX (hasseDeriv 2 S))).comp centerEval2.toRingHom =
        f.comp (composed2 (seedPair z) (liftPoly S)) := by
    apply evalFour_ext
    · intro g
      have he : (graphEval z).comp (MvPolynomial.map (algebraMap L FX)) =
          (f.comp C).comp (MvPolynomial.eval (seedPair z)) := by
        apply MvPolynomial.ringHom_ext
        · intro a; simp [graphEval, RingHom.comp_apply, f]; rfl
        · intro i; fin_cases i <;> simp [graphEval, seedPair, seedEmbedding, f]
      simpa [RingHom.comp_apply, centerEval2, K1_14_1.centerEval, jetMarkEval, composed2, evalFour]
        using DFunLike.congr_fun he g
    · simp [RingHom.comp_apply, centerEval2, K1_14_1.centerEval, jetMarkEval, composed2, evalFour,
        graphEval, f]
    · simp [RingHom.comp_apply, centerEval2, K1_14_1.centerEval, jetMarkEval, composed2, evalFour,
        f, atX]
    · simp [RingHom.comp_apply, centerEval2, K1_14_1.centerEval, jetMarkEval, composed2, evalFour,
        f, atX, liftPoly, Polynomial.derivative_map]
    · simp [RingHom.comp_apply, centerEval2, K1_14_1.centerEval, jetMarkEval, composed2, evalFour,
        f, atX, liftPoly, Polynomial.hasseDeriv_map]
  exact DFunLike.congr_fun hcomp P₀

private theorem derivFX_seedEmbedding (z : K) : derivFX (seedEmbedding z) = 0 := by
  have h : seedEmbedding z = algebraMap (Polynomial L) FX (Polynomial.C (algebraMap K L z)) := rfl
  rw [h, derivFX_algebraMap, Polynomial.derivative_C, map_zero]

private theorem derivFX_graphEval (z : K) (p : Seeds) :
    derivFX (graphEval z p) = graphEval z (derivSeedsX p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have h1 : derivSeedsX (MvPolynomial.C c) = MvPolynomial.C (derivFX c) := by
      ext m; rw [derivSeedsX_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
      split_ifs <;> simp [derivFX_zero]
    rw [h1]; simp [graphEval]
  | add p q ihp ihq => rw [map_add, derivFX_add, derivSeedsX_add, map_add, ihp, ihq]
  | mul_X p i ih =>
    have hX : derivSeedsX (MvPolynomial.X i : Seeds) = 0 := by
      ext m; rw [derivSeedsX_coeff, MvPolynomial.coeff_X']
      split_ifs
      · change derivFX 1 = 0
        have h1 : (1 : FX) = algebraMap (Polynomial L) FX 1 := (map_one _).symm
        rw [h1, derivFX_algebraMap, Polynomial.derivative_one, map_zero]
      · exact derivFX_zero
    rw [map_mul, derivFX_mul, derivSeedsX_mul, hX, mul_zero, add_zero, map_mul, ih]
    have hgi : derivFX (graphEval z (MvPolynomial.X i)) = 0 := by
      fin_cases i
      · simpa [graphEval] using derivFX_seedEmbedding z
      · have hdpow : ∀ n : ℕ, derivFX ((seedEmbedding z) ^ n) = 0 := by
          intro n; induction n with
          | zero =>
            have h1 : (1 : FX) = algebraMap (Polynomial L) FX 1 := (map_one _).symm
            rw [pow_zero, h1, derivFX_algebraMap, Polynomial.derivative_one, map_zero]
          | succ n ihn =>
            rw [pow_succ, derivFX_mul, ihn, derivFX_seedEmbedding, zero_mul, mul_zero, add_zero]
        simpa [graphEval] using hdpow K1.p
    rw [hgi, mul_zero, add_zero]

private theorem derivFX_atX (S : Polynomial K) : derivFX (atX S) = atX S.derivative := by
  change derivFX (algebraMap (Polynomial L) FX (liftPoly S)) =
    algebraMap (Polynomial L) FX (liftPoly S.derivative)
  rw [derivFX_algebraMap, liftPoly, liftPoly, Polynomial.derivative_map]

private theorem derivFX_eval_eq (z : K) (S : Polynomial K) (p : Equation) :
    derivFX (p.eval₂ (graphEval z) (atX S)) =
      (mapDeriv derivSeedsX p).eval₂ (graphEval z) (atX S) +
      p.derivative.eval₂ (graphEval z) (atX S) * atX S.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [Polynomial.eval₂_add, derivFX_add, mapDeriv_add derivSeedsX_zero derivSeedsX_add,
      Polynomial.derivative_add, Polynomial.eval₂_add, Polynomial.eval₂_add, ihp, ihq]
    ring
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    have hmd : mapDeriv derivSeedsX (Polynomial.C c * Polynomial.X ^ n) =
        Polynomial.C (derivSeedsX c) * Polynomial.X ^ n := by
      ext k
      rw [mapDeriv_coeff derivSeedsX_zero, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
      split_ifs <;> simp [derivSeedsX_zero]
    rw [hmd, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      derivFX_mul, derivFX_graphEval, Polynomial.derivative_C_mul_X_pow]
    have hdpow : ∀ m : ℕ, derivFX (atX S ^ m) = (m : FX) * atX S ^ (m - 1) * atX S.derivative := by
      intro m; induction m with
      | zero =>
        have h1 : (1 : FX) = algebraMap (Polynomial L) FX 1 := (map_one _).symm
        rw [pow_zero, h1, derivFX_algebraMap, Polynomial.derivative_one, map_zero]; simp
      | succ m ihm =>
        rw [pow_succ, derivFX_mul, ihm, derivFX_atX]
        cases m with
        | zero => simp
        | succ m =>
          have h1 : m + 1 - 1 = m := rfl
          have h2 : m + 1 + 1 - 1 = m + 1 := rfl
          rw [h1, h2]
          conv_rhs => rw [pow_succ]
          push_cast; ring
    rw [hdpow n]
    cases n with
    | zero =>
      simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_mul, map_zero,
        Polynomial.eval₂_zero, add_zero]
    | succ n =>
      have hsub : n + 1 - 1 = n := rfl
      rw [hsub, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_mul, map_natCast,
        Polynomial.eval₂_pow, Polynomial.eval₂_X]
      ring

/-- **Prolongation Vanishing at Any Mark (`prolong_vanish_at_mark`)**:
    If `G.natDegree = 1` and `jetAt G z S = 0`, then
      `jetAt (prolongA G) z S * atX (hasseDeriv 2 S) + jetAt (prolongB1 G) z S = 0`. -/
theorem prolong_vanish_at_mark {G : Jet} (hdegG : G.natDegree = 1) (z : K) (S : Polynomial K)
    (hG : jetAt G z S = 0) :
    jetAt (prolongA G) z S * atX (hasseDeriv 2 S) + jetAt (prolongB1 G) z S = 0 := by
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
  have hd0 : derivFX (jetAt G z S) = 0 := by rw [hG, derivFX_zero]
  rw [← jetMarkEval_eq, hlin] at hd0
  simp only [map_add, map_mul, jetMarkEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, derivFX_add, derivFX_mul, derivFX_eval_eq, derivFX_atX] at hd0
  have h2 : atX S.derivative.derivative = (2 : FX) * atX (hasseDeriv 2 S) := by
    rw [derivative_derivative_eq_two_hasseDeriv2]
    change algebraMap (Polynomial L) FX (liftPoly (2 * hasseDeriv 2 S)) = _
    rw [liftPoly, Polynomial.map_mul, Polynomial.map_ofNat, map_mul, map_ofNat]; rfl
  rw [h2] at hd0
  have hB1 : jetAt (prolongB1 G) z S =
      (mapDeriv derivSeedsX (G.coeff 0)).eval₂ (graphEval z) (atX S) +
      (mapDeriv derivSeedsX (G.coeff 1)).eval₂ (graphEval z) (atX S) * atX S.derivative +
      ((G.coeff 0).derivative.eval₂ (graphEval z) (atX S) +
        (G.coeff 1).derivative.eval₂ (graphEval z) (atX S) * atX S.derivative) * atX S.derivative := by
    unfold prolongB1
    rw [← jetMarkEval_eq, map_add, map_mul]
    have hX : jetMarkEval z S Polynomial.X = atX S.derivative := by simp [jetMarkEval]
    have hjX : jetDerivX G =
        Polynomial.C (mapDeriv derivSeedsX (G.coeff 0)) +
        Polynomial.C (mapDeriv derivSeedsX (G.coeff 1)) * Polynomial.X := by
      ext n
      rw [jetDerivX, mapDeriv_coeff (mapDeriv_zero derivSeedsX_zero)]
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2),
            mapDeriv_zero derivSeedsX_zero]
          simp [Polynomial.coeff_C, Polynomial.coeff_X]
    have hjY : jetDerivY0 G =
        Polynomial.C (G.coeff 0).derivative +
        Polynomial.C (G.coeff 1).derivative * Polynomial.X := by
      ext n
      rw [jetDerivY0, mapDeriv_coeff Polynomial.derivative_zero]
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < n + 2),
            Polynomial.derivative_zero]
          simp [Polynomial.coeff_C, Polynomial.coeff_X]
    rw [hjX, hjY, hX]
    simp only [map_add, map_mul, jetMarkEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
  have hA : jetAt (prolongA G) z S = 2 * (G.coeff 1).eval₂ (graphEval z) (atX S) := by
    rw [← jetMarkEval_eq, prolongA, map_mul, map_ofNat]
    simp [jetMarkEval]
  rw [hA, hB1]
  linear_combination hd0

/-- **Prolongation Substitution Vanishes at Every Mark on `G` (`prolongSubst_vanish_at_mark`)**:
    For any `P₀ ∈ complete2 Crt word s W` (`W < s.m * A`) and any mark `(z, S)` on `G` with
    `≥ A` hits and `(liftPoly S).natDegree ≤ 131071 + h`, `Q₀ = prolongSubst (prolongA G) (prolongB1 G) s.C (centerEval2 P₀)`
    satisfies `jetAt Q₀ z S = 0`! -/
theorem prolongSubst_vanish_at_mark {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    (z : K) (S : Polynomial K) (hres : MarkResidues D z S)
    (hdeg : (liftPoly S).natDegree ≤ 131071 + h)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hhits : ∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k)
    {s : Shape2} {W : ℕ} (hW : W < s.m * A) {P₀ : Source2}
    (hP : P₀ ∈ complete2 Crt word s W)
    {G : Jet} (hdegG : G.natDegree = 1) (hG : jetAt G z S = 0) :
    jetAt (prolongSubst (prolongA G) (prolongB1 G) s.C (centerEval2 P₀)) z S = 0 := by
  have hPdeg : (centerEval2 P₀).natDegree ≤ s.C :=
    (Polynomial.natDegree_map_le).trans (TwoJetCaseADriver.natDegree_le_of_mem_ambient2 hP.1.1)
  have hP0 : Polynomial.eval₂ (jetMarkEval z S) (atX (hasseDeriv 2 S)) (centerEval2 P₀) = 0 := by
    rw [composed2_center, contact_vanish_2jet Crt word hnode z S hres hdeg hits hcard hhits hW hP,
      map_zero]
  exact prolongSubst_eval_zero (jetMarkEval z S) (atX (hasseDeriv 2 S))
    (prolongA G) (prolongB1 G) s.C hPdeg hP0 (prolong_vanish_at_mark hdegG z S hG)

#print axioms contact_vanish_2jet
#print axioms prolong_vanish_at_mark
#print axioms prolongSubst_vanish_at_mark

end
end TwoJetCaseAFX

end Merged_TwoJetCaseAFXContact

-- merged module TwoJetCaseBBridge
section Merged_TwoJetCaseBBridge

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxRecDepth 16000
set_option maxHeartbeats 800000

/-!
# End-to-End Case-B Algebraic Descent & 6-Small-Rect Cardinality Cap at `69.61` (`TwoJetCaseBBridge`)

Closes the Case-B (`jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0`) branch for all 6
small Rescue rectangles at `69.61` (`A = 179,818`, `h ∈ [2368, 2401]`, `deg ≤ 133,520 < 133,721`):

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
   (using `F.distinct`), proving `(Γ.filter (jetAt G ... = 0)).card ≤ caseBCap6961 r ≤ 34_917_696_728_717_810`.
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

/-! ## 1. 6 Small-Rectangle Box Shapes & Kernel-Checked `tariffHigh 179798` Bounds -/

inductive SmallRect61
  | r0 -- j = 1, u = 1
  | r1 -- j = 1, 2 ≤ u ≤ 6
  | r2a -- j = 1, 7 ≤ u ≤ 22
  | r3a_j2 -- j = 2, 1 ≤ u ≤ 16
  | r3a_j4 -- 3 ≤ j ≤ 4, 1 ≤ u ≤ 13
  | r3a_j5 -- 5 ≤ j ≤ 6, 1 ≤ u ≤ 11
  | r3a_j7 -- j = 7, 1 ≤ u ≤ 10
  deriving DecidableEq, Repr

def SmallRect61.In (j u : ℕ) : SmallRect61 → Prop
  | .r0 => j = 1 ∧ u = 1
  | .r1 => j = 1 ∧ 2 ≤ u ∧ u ≤ 6
  | .r2a => j = 1 ∧ 7 ≤ u ∧ u ≤ 22
  | .r3a_j2 => j = 2 ∧ 1 ≤ u ∧ u ≤ 16
  | .r3a_j4 => (3 ≤ j ∧ j ≤ 4) ∧ 1 ≤ u ∧ u ≤ 13
  | .r3a_j5 => (5 ≤ j ∧ j ≤ 6) ∧ 1 ≤ u ∧ u ≤ 11
  | .r3a_j7 => j = 7 ∧ 1 ≤ u ∧ u ≤ 10

def SmallRect61.box : SmallRect61 → BoxShape
  | .r0 => ⟨3, 3, 1⟩
  | .r1 => ⟨18, 18, 6⟩
  | .r2a => ⟨66, 66, 22⟩
  | .r3a_j2 => ⟨80, 48, 16⟩
  | .r3a_j4 => ⟨117, 39, 13⟩
  | .r3a_j5 => ⟨143, 33, 11⟩
  | .r3a_j7 => ⟨150, 30, 10⟩

def SmallRect61.cap : SmallRect61 → ℕ
  | .r0 => 1_516_012_482_196
  | .r1 => 633_736_945_130_922
  | .r2a => 34_467_853_581_469_594
  | .r3a_j2 => 30_643_127_015_445_009
  | .r3a_j4 => 34_917_696_728_717_810
  | .r3a_j5 => 32_136_762_722_344_834
  | .r3a_j7 => 28_167_821_374_198_251

theorem agreementOK_6961 : AgreementOKHigh 179798 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem smallRect61_boxOK (r : SmallRect61) : BoxOK r.box := by
  cases r <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem smallRect61_tariff_le (r : SmallRect61) :
    tariffHigh 179798 r.box + 143 * (p + 1) ≤ r.cap := by
  cases r <;> decide +kernel

theorem smallRect61_cap_le (r : SmallRect61) : r.cap ≤ 34_917_696_728_717_810 := by
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
  | r3a_j5 =>
    rcases hin with ⟨⟨hj1, hj2⟩, h1, h2⟩
    dsimp [SmallRect61.box]
    have hmul : (2 * j + 1) * u ≤ 13 * 11 := Nat.mul_le_mul (by omega) h2
    have hmul2 : (2 * j - 1) * u ≤ 11 * 11 := Nat.mul_le_mul (by omega) h2
    omega
  | r3a_j7 => rcases hin with ⟨rfl, h1, h2⟩; dsimp [SmallRect61.box]; omega

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
    with `F : P1.FamilyAt 179798 M Γ` and `M.overhead.toNat ≤ 2401`:
      `(Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ) = 0)).card ≤ r.cap ≤ 34_917_696_728_717_810`. -/
theorem caseB_small_rect_card_le_6961 {uM : P1.Words} {deleted : Finset I}
    {M : P1.ModelAt 33619 uM deleted} {Γ : Finset K} (F : P1.FamilyAt 179798 M Γ)
    (hhi : M.overhead.toNat ≤ 2401)
    {G : Jet} (hIrr : Irreducible G) (hdegG : G.natDegree = 1) (hseed : UsesSeed G)
    {r : SmallRect61} {j u : ℕ} (hin : r.In j u) (hG : RowCaps G ⟨0, j, 1, u⟩)
    (hdet : jacDet fractionRingFieldDerivs (alpha1 G) (alpha2 G) = 0) :
    (Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0).card ≤ r.cap ∧
    (Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0).card ≤ 34_917_696_728_717_810 := by
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
  -- Bound `Good.card ≤ tariffHigh 179798 r.box` via `F.distinct` + `order_two_card_le_high133721`!
  let Sgood := Good.image F.scalar
  have hGood_sub : Good ⊆ Γ := (Finset.sdiff_subset).trans (Finset.filter_subset _ _)
  have hSgood_card : Sgood.card = Good.card :=
    Finset.card_image_of_injOn (F.distinct.mono hGood_sub)
  have hSgood_close : (Sgood : Set (Polynomial K)) ⊆ closeHigh 179798 M.word := by
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
            have : M.overhead ≤ 2401 := by omega
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
  have hGood_le : Good.card ≤ tariffHigh 179798 r.box := by
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

end Merged_TwoJetCaseBBridge

-- merged module R6961LoRescueSourceException
section Merged_R6961LoRescueSourceException

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (helperBank helperCutoff helper_common_caps)
open TwoJetCaseBBridge (SmallRect61)

def jetCap (rect : Fin 13) : ℕ := ([1,1,1,2,4,6,7,1,1,2,4,6,7] : List ℕ).get ⟨rect.val,rect.isLt⟩
def seedCap (rect : Fin 13) : ℕ := ([1,6,22,16,13,11,10,40,85,80,80,80,80] : List ℕ).get ⟨rect.val,rect.isLt⟩

def smallRectOf (rect : Fin 13) : SmallRect61 :=
  match rect.val with
  | 0 => .r0
  | 1 => .r1
  | 2 => .r2a
  | 3 => .r3a_j2
  | 4 => .r3a_j4
  | 5 => .r3a_j5
  | _ => .r3a_j7

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤80) :
    ∃ rect : Fin 13, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect ∧
      (rect.val < 7 → (smallRectOf rect).In j u) := by
  by_cases hj1 : j = 1
  · by_cases hu1 : u ≤ 1
    · refine ⟨0, by change 1≤j; omega, by change j≤1; omega, by change 1≤u; omega, by change u≤1; omega, ?_⟩
      intro _; simp [smallRectOf, SmallRect61.In]; omega
    · by_cases hu6 : u ≤ 6
      · refine ⟨1, by change 1≤j; omega, by change j≤1; omega, by change 2≤u; omega, by change u≤6; omega, ?_⟩
        intro _; simp [smallRectOf, SmallRect61.In]; omega
      · by_cases hu22 : u ≤ 22
        · refine ⟨2, by change 1≤j; omega, by change j≤1; omega, by change 7≤u; omega, by change u≤22; omega, ?_⟩
          intro _; simp [smallRectOf, SmallRect61.In]; omega
        · by_cases hu40 : u ≤ 40
          · refine ⟨7, by change 1≤j; omega, by change j≤1; omega, by change 23≤u; omega, by change u≤40; omega, ?_⟩
            intro h; omega
          · refine ⟨8, by change 1≤j; omega, by change j≤1; omega, by change 41≤u; omega, by change u≤85; omega, ?_⟩
            intro h; omega
  · have hu80 : u ≤ 80 := mixed (by omega)
    by_cases hj2 : j = 2
    · by_cases hu16 : u ≤ 16
      · refine ⟨3, by change 2≤j; omega, by change j≤2; omega, by change 1≤u; omega, by change u≤16; omega, ?_⟩
        intro _; simp [smallRectOf, SmallRect61.In]; omega
      · refine ⟨9, by change 2≤j; omega, by change j≤2; omega, by change 17≤u; omega, by change u≤80; omega, ?_⟩
        intro h; omega
    · by_cases hj4 : j ≤ 4
      · by_cases hu13 : u ≤ 13
        · refine ⟨4, by change 3≤j; omega, by change j≤4; omega, by change 1≤u; omega, by change u≤13; omega, ?_⟩
          intro _; simp [smallRectOf, SmallRect61.In]; omega
        · refine ⟨10, by change 3≤j; omega, by change j≤4; omega, by change 14≤u; omega, by change u≤80; omega, ?_⟩
          intro h; omega
      · by_cases hj6 : j ≤ 6
        · by_cases hu11 : u ≤ 11
          · refine ⟨5, by change 5≤j; omega, by change j≤6; omega, by change 1≤u; omega, by change u≤11; omega, ?_⟩
            intro _; simp [smallRectOf, SmallRect61.In]; omega
          · refine ⟨11, by change 5≤j; omega, by change j≤6; omega, by change 12≤u; omega, by change u≤80; omega, ?_⟩
            intro h; omega
        · by_cases hu10 : u ≤ 10
          · refine ⟨6, by change 7≤j; omega, by change j≤7; omega, by change 1≤u; omega, by change u≤10; omega, ?_⟩
            intro _; simp [smallRectOf, SmallRect61.In]; omega
          · refine ⟨12, by change 7≤j; omega, by change j≤7; omega, by change 11≤u; omega, by change u≤80; omega, ?_⟩
            intro h; omega

theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2368≤h) (hi : h≤2401) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣P) :
    ∃ rect : Fin 13, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      (rect.val < 7 → (smallRectOf rect).In (jetDegree G) (seedDegree G)) ∧
      ∀ (i : Fin 17), (7 ≤ rect.val ∨ i ≠ 0) →
        ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU,hsmall⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,hsmall,fun i hok => ?_⟩
  exact rescue_row Crt word lo hi rect i hok irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

end Lower6961.Lo.RescueSource

end Merged_R6961LoRescueSourceException

-- merged module R6961LoRescueGeometry
section Merged_R6961LoRescueGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open RescueSource (bank reserve cutoff jetCap seedCap)
open Lower6960.DifferentialContact (Native)
open Lower6961.RescueGeometry (Model Family word OnMark label_injective contact_at_mark zero_of_contact OnSurface)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)


def primeShape (rect : Fin 13) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩

def initialCap (rect : Fin 13) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape

theorem prime_shape_fit (rect : Fin 13) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide

theorem initial_small (rect : Fin 13) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel

theorem reserve_small (i : Fin 17) : reserve i<K1.p := by
  fin_cases i <;> decide +kernel


/-- The exceptional initial pair feeds the native section bound and retains
both row memberships on every component. -/
private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩

/-- Initial books and projective parents for the marks that lie on the
exceptional prime. The rank exit and dual parents share the original cap. -/
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 13) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ

private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 13} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))

theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 13} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 13} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

#print axioms initial_cover
#print axioms Initial.rank_ode

end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometry

-- merged module R6961LoRescueGeometryHistory
section Merged_R6961LoRescueGeometryHistory

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open RescueSource (bank reserve cutoff jetCap seedCap)
open Lower6960.DifferentialContact (Native)
open Lower6961.RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open scoped Classical

theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 13} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 17→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (bank rect i).shape)
    (contact : ∀ (i : Fin 17), i ≠ 0 → ∀ γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (Q i)) ∧
      (∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
        (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c) ∧
      ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (RescueSource.shape_guards rect i).2.1 init.parents on (reserve i) (reserve_small i)
  let selected (i : Fin 17) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : reserve 0=0 := by decide
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (reserve 0+1) (Q 0) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 17) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (reserve i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 17) (c : Fin 4) :
      (reserve i+1)*mass (selected i) c≤pairCap (primeShape rect) (bank rect i).shape c := by
    by_cases zi : i = 0
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 17,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 17,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = 0 := Fin.ext (by omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ 0 := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i nz γ hγ)⟩

structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 13
  row : Fin 17→Jet
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 17,∀ n,i.val<n → ∀ J∈kept n,Native J (reserve i+1) (row i)
  cap : ∀ i : Fin 17,∀ n,i.val<n → ∀ c : Fin 4,
    (reserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (bank rect i).shape c
  cut : ∀ i : Fin 17,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (bank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0

/-- Build a `Run` from any Stage-0 avoiding row `Q₀` (either 2-jet prolongation or 1-jet)
and the 16 1-jet rows at stages `1..16`. -/
theorem prepare_with_Q0 {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2368≤M.overhead.toNat) (hi : M.overhead.toNat≤2401)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (irr : Irreducible G) (rect : Fin 13)
    (capsG : RowCaps G (primeShape rect))
    (Q₀ : Jet) (avoid0 : ¬ G ∣ Q₀) (capsQ0 : RowCaps Q₀ (bank rect 0).shape)
    (zero0 : ∀ γ∈Γ, jetAt Q₀ (M.label γ) (F.scalar γ) = 0)
    (rows_later : ∀ (i : Fin 17), i ≠ 0 →
      ∃ Q ∈ evaluated Crt (word M) (bank rect i).shape (cutoff M.overhead.toNat rect i), ¬ G∣Q) :
    Nonempty (Run F Crt G) := by
  let pickLater (i : Fin 17) : Jet :=
    if h0 : i = 0 then Q₀ else Classical.choose (rows_later i h0)
  have hQ0 : pickLater 0 = Q₀ := by simp [pickLater]
  have avoid (i : Fin 17) : ¬ G ∣ pickLater i := by
    by_cases h0 : i = 0
    · subst h0; rwa [hQ0]
    · simp only [pickLater, dif_neg h0]
      exact (Classical.choose_spec (rows_later i h0)).2
  have caps (i : Fin 17) : RowCaps (pickLater i) (bank rect i).shape := by
    by_cases h0 : i = 0
    · subst h0; rwa [hQ0]
    · simp only [pickLater, dif_neg h0]
      exact evaluated_shape Crt (word M) (Classical.choose_spec (rows_later i h0)).1
  have contact (i : Fin 17) (h0 : i ≠ 0) (γ : K) (hγ : γ ∈ Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (pickLater i) := by
    simp only [pickLater, dif_neg h0]
    exact contact_at_mark F Crt noPole residues (Classical.choose_spec (rows_later i h0)).1
      (RescueSource.cutoff_fit lo hi rect i (Or.inr h0)) γ hγ
  obtain ⟨ini⟩ := initial_cover F irr (avoid 0) capsG (caps 0) (by simpa [hQ0] using zero0)
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial irr capsG pickLater ini avoid caps contact
  exact ⟨⟨rect,pickLater,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩⟩

theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)

end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometryHistory

-- merged module R6961LoRescueGeometryCuts
section Merged_R6961LoRescueGeometryCuts

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt atX seedEmbedding)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom eval_toJet CoordinateRing)
open K1_14_2_2 (RowCaps Active dual mass sectionDegree CutCover weight dot emptyCut joinCuts
  joinCuts_cost sum_dot)
open K1_14_2_2_3 K1_14_2_2_7
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open RescueSource (bank reserve)
open Lower6961.RescueGeometry (Model Family word OnMark label_injective contact_at_mark zero_of_contact OnSurface)
open scoped Classical
open HighCore82258_3 (envelope_caps)
open K1_14_2_2_7 (seed_value_eq)

/-- The common depth-4500 terminal is tested at the full 69.60 cutoff. -/
def terminalShape : Shape := ⟨4500,6285,1329,1126356⟩

def terminalCutoff : ℕ := terminalShape.m*179798-1

def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ P∈evaluated Crt w terminalShape terminalCutoff,toJet P∈J

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) :=
  (R.kept 17).filter (TerminalPass Crt (word M))

def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  if n<17 then R.kept (n+1) else R.final

def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) :=
  R.live n \ R.live (n+1)

theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<17
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]
    exact R.antitone (by omega)
  · have eq : i+1=17 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]
    exact filter_subset _ _

theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem
  exact (R.parent_geom mem).1

theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<17)]
  exact R.intro_pass

def rescueStage (rect : Fin 13) (i : Fin 17) : P1_7.Stage :=
  ⟨reserve i,⟨Lower6960.HelperPrefix.timesShape (reserve i+1) (primeShape rect),0,0⟩,bank rect i⟩

def cutShape (rect : Fin 13) (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (rect : Fin 13) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (RescueSource.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=17 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass =>
      lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    unfold TerminalPass at hf
    push Not at hf
    obtain ⟨C,inside,proper⟩ := hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,evaluated_shape Crt (word M) inside,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside (by simp only [Nat.mul_zero,Nat.add_zero]; decide +kernel) γ hγ

private theorem mark_on_cut {J : Ideal Ambient} {P : Jet} {z : K} {S : (Polynomial K)}
    (on : OnJet J z S) (zero : jetAt P z S=0) :
    ∃ Q∈cutComponents J P,OnJet Q z S := by
  let e := jetMarkHom z S
  have incl : J ⊔ Ideal.span {toJet P} ≤ RingHom.ker e :=
    sup_le on ((Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans zero)))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q,minimal,mark⟩ := Ideal.exists_minimalPrimes_le incl
  exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr minimal,mark⟩

theorem proper_cut {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (s : Shape) {J : Ideal Ambient} {P : Jet} (sl : s.J≤s.B) (act : Active J)
    (cap : RowCaps P s) (proper : toJet P∉J) (zero : ∀ γ∈Γ,jetAt P (M.label γ) (F.scalar γ)=0) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight s fee) (sectionDegree J)) ∧
      ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnMark F Q)
  let direct := (constantComponents J P).biUnion marked
  have card : direct.card≤(constantComponents J P).card := by
    have single (Q : Ideal Ambient) (mem : Q∈constantComponents J P) : (marked Q).card≤1 := by
      obtain ⟨comp,seed⟩ := mem_filter.mp mem
      let _ : Q.IsPrime := (cutComponent_curve act proper comp).1
      apply card_le_one.mpr
      intro γ hγ δ hδ
      apply label_injective M
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq seed (mem_filter.mp hγ).2).trans (seed_value_eq seed (mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q∈constantComponents J P,(marked Q).card := card_biUnion_le
      _ ≤ ∑ _∈constantComponents J P,1 := sum_le_sum single
      _ = _ := by simp
  let C : CutCover := ⟨direct,movingComponents J P,by
    intro Q hQ
    obtain ⟨comp,moving⟩ := mem_filter.mp hQ
    obtain ⟨prime,dim⟩ := cutComponent_curve act proper comp
    exact ⟨prime,dim,K1_14_2_2_7_1.proof Q prime dim moving⟩⟩
  refine ⟨C,?_,?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s J P sl act cap proper
    · exact P0_10R.Bridge.cut_ordinate_mass s J P sl act cap proper
    · exact card.trans (P0_10R.Bridge.cut_constant_count s J P sl act cap proper)
  · intro γ hγ on
    obtain ⟨Q,comp,mark⟩ := mark_on_cut on (zero γ hγ)
    by_cases c : ConstantSeed Q
    · exact Or.inl (mem_biUnion.mpr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mem_filter.mpr ⟨hγ,mark⟩⟩)
    · exact Or.inr ⟨Q,mem_filter.mpr ⟨comp,c⟩,mark⟩

/-- Every lost bin of the concrete rescue process is paid by the native
constant-component and moving-curve cut data at the schedule's envelope. -/
theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<17,J∈R.lost i := by
  by_cases h : ∃ i<17,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤17,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 17 le_rfl)


def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal

/-- Convert the actual retained ideals to the surfaces used by the common
terminal test and the projected-product construction. -/
theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

#print axioms Run.cutCover
#print axioms Run.retained_or_lost
#print axioms Run.terminal_surfaces

end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometryCuts

-- merged module R6961LoRescueGeometryBills
section Merged_R6961LoRescueGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open RescueSource (bank reserve)
open Lower6961.RescueGeometry (Model Family word OnMark label_injective OnSurface)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical

def initialMass (rect : Fin 13) : Mass := fun k => initialCap rect k

def history (rect : Fin 13) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<17 then
      let i : Fin 17 := ⟨n+1,hn⟩
      min (history rect n k)
        ((pairCap (primeShape rect) (bank rect i).shape k : ℚ)/(reserve i+1))
    else history rect n k

theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by
    simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))

theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<17) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 17 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (bank R.rect j).shape k : ℚ) / (reserve j+1)
    have pos : (0 : ℚ)<reserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound
    unfold massQ
    exact_mod_cast bound

theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]
  exact R.history_cap hi (Nat.lt_succ_self _) k

theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]
  exact R.initial_cap _ k

def cutWeight (rect : Fin 13) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k

def seedLimit (rect : Fin 13) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)

def pointLimit (rect : Fin 13) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)

def initialSeedLimit (rect : Fin 13) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3

theorem seed_limit_small (rect : Fin 13) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel

theorem point_limit_bound (rect : Fin 13) : pointLimit rect ≤ 107740799081 := by
  fin_cases rect <;> decide +kernel

def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 13} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))

def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 13} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 13} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)

theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 13} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ

theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)

def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i

private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i

private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := bill_bound 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    simpa only [beforeCuts,Run.jointLost,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k

/-- The source receipts, geometric inventory, and cut charges from a given Stage-0 row `Q₀`. -/
theorem inventory_with_Q0 {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2368≤M.overhead.toNat) (hi : M.overhead.toNat≤2401)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (irr : Irreducible G) (rect : Fin 13)
    (capsG : K1_14_2_2.RowCaps G (primeShape rect))
    (Q₀ : Jet) (avoid0 : ¬ G ∣ Q₀) (capsQ0 : K1_14_2_2.RowCaps Q₀ (bank rect 0).shape)
    (zero0 : ∀ γ∈Γ, jetAt Q₀ (M.label γ) (F.scalar γ) = 0)
    (rows_later : ∀ (i : Fin 17), i ≠ 0 →
      ∃ Q ∈ K1_14_1.evaluated Crt (word M) (bank rect i).shape (RescueSource.cutoff M.overhead.toNat rect i), ¬ G∣Q) :
    ∃ (R : Run F Crt G) (C : CutBooks R) (S : Finset Surface),
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
        γ∈R.initial.seedMarks ∨ γ∈R.initial.ordinateMarks ∨
        (∃ J∈R.initial.rankExit,OnMark F J γ) ∨ γ∈C.pointMarks ∨
        (∃ i<17,∃ Q∈(C.cover i).curves,OnMark F Q γ) ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare_with_Q0 F Crt lo hi noPole residues irr rect capsG Q₀ avoid0 capsQ0 zero0 rows_later
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨R,C,S,geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_filter.mpr ⟨hγ,seed⟩)
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pass γ hγ ⟨J,final,on⟩)))))
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | curve
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,curve⟩))))

end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometryBills

-- merged module R6961LoRescueGeometryTariffs
section Merged_R6961LoRescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open Lower6961.RescueGeometry (Model Family label_injective)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179798
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 133472

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133472) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179798 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 133472 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 133472) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2401) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤133472
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2401) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133472)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 133472) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2401) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound

#print axioms curve_tariff
#print axioms fixed_count

end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometryTariffs

-- merged module R6961LoRescueGeometryRates
section Merged_R6961LoRescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (K p)
open Lower6961.RescueGeometry (Model Family OnMark)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

#print axioms rated_curve_count
end Lower6961.Lo.RescueGeometry

end
end Merged_R6961LoRescueGeometryRates
