import ProximityPrize.SubmissionLower.TwoJetCaseAFX

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
