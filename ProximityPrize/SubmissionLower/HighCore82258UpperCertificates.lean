import ProximityPrize.SubmissionLower.SilverBase
import ProximityPrize.SubmissionLower.HighCore82258UpperGeometry

namespace HighCore82258GeometryGoals
def c1 : Prop := HighCore82258Upper_3_1.c2
def c2 : Prop := HighCore82258Upper_3_2.c4
end HighCore82258GeometryGoals

set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation)
open HighCore82258Upper (Input ResidueLift Factors)
open HighCore82258Upper_3 (JetRing ordinate openFactor graphIdeal tangentEquation le_saturate
  proper_mem_graph)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative)
open HighCore82258Upper_3_1_2
open Polynomial (C)
open TrivSqZeroExt
open scoped BigOperators Ring
open private flow flow_mul flow_C flow_sep flow_tangentEquation coeffDiff_one
  coeff_coeffDiff dx_nat from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
theorem cancel_unit {R : Type*} [CommRing R] {a b c : R}
    (ha : IsUnit a) (h : a*b = a*c) : b = c := by
  simpa only [Ring.inverse_mul_cancel_left _ _ ha] using congrArg (fun x => a⁻¹ʳ * x) h
theorem finite_zero (J : Input) (B : ResidueLift J) (D : Factors J B)
    {N : JetRing} (h : N ∈ graphIdeal J B D) : finite J B D N = 0 := by
  simp only [finite, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
theorem overlap_unit (J : Input) (B : ResidueLift J) (D : Factors J B) :
    IsUnit (finite J B D (ordinate * openFactor J B)) :=
  IsLocalization.Away.algebraMap_isUnit (overlapFactor J B D)
theorem separant_unit (J : Input) (B : ResidueLift J) (D : Factors J B) :
    IsUnit (finite J B D (jetSeparant J.f)) := by
  apply isUnit_of_dvd_unit _ (overlap_unit J B D)
  refine map_dvd (finite J B D) ⟨ordinate * HighCore82258Upper_3.residueInJet B, ?_⟩
  change ordinate * (HighCore82258Upper_3.residueInJet B * jetSeparant J.f) = _
  ring
private def firstJet {R : Type*} [CommRing R] (f : Equation) (ev : JetRing →+* R) :
    JetRing →+* TrivSqZeroExt R R where
  toFun N := ⟨ev N, ev (flow f N)⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one ev
    · change ev (flow f 1) = 0
      rw [← Polynomial.C_1, flow_C, coeffDiff_one, Polynomial.derivative_one]
      simp
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' N M := by
    apply TrivSqZeroExt.ext
    · exact map_add ev N M
    · change ev (flow f (N+M)) = ev (flow f N) + ev (flow f M)
      rw [map_add, map_add]
  map_mul' N M := by
    apply TrivSqZeroExt.ext
    · exact map_mul ev N M
    · change ev (flow f (N*M)) = ev N * ev (flow f M) + ev (flow f N) * ev M
      rw [flow_mul, map_add, map_mul, map_mul]
private theorem kills_saturation {R : Type*} [CommRing R] (ev : JetRing →+* R)
    {I : Ideal JetRing} {g : JetRing} (hg : IsUnit (ev g)) (hI : I ≤ RingHom.ker ev)
    {N : JetRing} (hN : N ∈ HighCore82258Upper_3.saturate I g) : ev N = 0 := by
  obtain ⟨n, hn⟩ := hN
  have h : ev (g^n * N) = 0 := hI hn
  rw [map_mul, map_pow, ← mul_zero ((ev g)^n)] at h
  exact cancel_unit (hg.pow n) h
theorem finite_root (J : Input) (B : ResidueLift J) (D : Factors J B) :
    finite J B D (C J.f) = 0 := by
  rw [D.product, map_mul, map_mul, finite_zero J B D (proper_mem_graph J B D), zero_mul]
private theorem firstJet_graph {R : Type*} [CommRing R]
    (J : Input) (B : ResidueLift J) (D : Factors J B) (ev : JetRing →+* R)
    (hP : ev (C D.proper) = 0) (hT : ev (tangentEquation J.f) = 0)
    (hc : IsUnit (ev (jetSeparant J.f))) (hg : IsUnit (ev (openFactor J B))) :
    ∀ N ∈ graphIdeal J B D, firstJet J.f ev N = 0 := by
  let H : Equation := ∏ j, D.flat j
  have hf : J.f = D.proper * H := D.product
  have hC : ev (jetSeparant J.f) = ev (C D.proper.derivative) * ev (C H) := by
    change ev (C J.f.derivative) = _
    rw [hf, Polynomial.derivative_mul]
    simp only [map_add, map_mul, hP, zero_mul, add_zero]
  have hH : IsUnit (ev (C H)) := isUnit_of_dvd_unit
    ⟨ev (C D.proper.derivative), hC.trans (mul_comm _ _)⟩ hc
  have hs : ev (flow J.f (C J.f)) = 0 := by
    rw [flow_C]
    change ev (jetSeparant J.f * tangentEquation J.f) = 0
    rw [map_mul, hT, mul_zero]
  have hflow : flow J.f (C J.f) =
      flow J.f (C D.proper * C H) := by rw [← map_mul, ← hf]
  rw [hflow, flow_mul, map_add, map_mul, map_mul, hP, zero_mul, zero_add, mul_comm,
    ← mul_zero (ev (C H))] at hs
  have hp : ev (flow J.f (C D.proper)) = 0 := cancel_unit hH hs
  intro N hN
  apply kills_saturation (firstJet J.f ev)
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hg) _ hN
  apply Ideal.span_le.mpr
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact TrivSqZeroExt.ext hP hp
  · apply TrivSqZeroExt.ext
    · exact hT
    · change ev (flow J.f (tangentEquation J.f)) = 0
      rw [flow_tangentEquation, map_zero]
set_option backward.isDefEq.respectTransparency false in
private def derivationOfJet {R : Type*} [CommRing R]
    (j : R →+* TrivSqZeroExt R R) (hj : ∀ x, (j x).fst = x) (a : R) :
    ChartDerivation R := by
  let d : R →+ R :=
    { toFun := fun x => a * (j x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  refine Derivation.mk' d.toIntLinearMap (fun x y => ?_)
  change a * (j (x*y)).snd = x * (a * (j y).snd) + y * (a * (j x).snd)
  simp only [map_mul, snd_mul, op_smul_eq_smul, smul_eq_mul, hj]
  ring
theorem coeffDiff_X : coefficientDerivative (Polynomial.X : Equation) = 0 := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have h1 : K1_14_6_1.Dx 1 = 0 := by simpa only [Nat.cast_one] using dx_nat 1
  by_cases hi : 1 = i <;> by_cases hm : (0 : Fin 2 →₀ ℕ) = m <;>
    simp [coeff_coeffDiff, Polynomial.coeff_X, MvPolynomial.coeff_one, hi, hm, h1]
private theorem extendJet {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (g : A) [IsLocalization.Away g R] (H : A →+* TrivSqZeroExt R R)
    (hH : ∀ n, (H n).fst = algebraMap A R n) {c : R} (hc : IsUnit c) :
    ∃ δ : ChartDerivation R, ∀ n, c * δ (algebraMap A R n) = (H n).snd := by
  have hU : IsUnit (H g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hH]
    exact IsLocalization.Away.algebraMap_isUnit g
  let j : R →+* TrivSqZeroExt R R := IsLocalization.Away.lift g hU
  let fst' : TrivSqZeroExt R R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom
  have hproj : fst'.comp j = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro n
    change (j (algebraMap A R n)).fst = algebraMap A R n
    rw [IsLocalization.Away.lift_eq g hU, hH]
  refine ⟨derivationOfJet j (RingHom.congr_fun hproj) (Ring.inverse c), fun n => ?_⟩
  change c * (Ring.inverse c * (j (algebraMap A R n)).snd) = (H n).snd
  rw [Ring.mul_inverse_cancel_left _ _ hc, IsLocalization.Away.lift_eq g hU]
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
theorem finite_flow : HighCore82258Upper_3_1_2.c1 := by
  intro J B D
  let ev := finite J B D
  have hg : IsUnit (ev (openFactor J B)) :=
    isUnit_of_dvd_unit (map_dvd ev ⟨ordinate, mul_comm _ _⟩) (overlap_unit J B D)
  have ht : ev (tangentEquation J.f) = 0 :=
    finite_zero J B D (le_saturate _ _ (Ideal.subset_span (by simp)))
  have hc := separant_unit J B D
  let H := Ideal.Quotient.lift (graphIdeal J B D) (firstJet J.f ev)
    (firstJet_graph J B D ev (finite_zero J B D (proper_mem_graph J B D)) ht hc hg)
  have hH (n : Graph J B D) : (H n).fst = algebraMap (Graph J B D) (Overlap J B D) n := by
    obtain ⟨N, rfl⟩ := Ideal.Quotient.mk_surjective n
    rfl
  obtain ⟨δ, hδ⟩ := extendJet (overlapFactor J B D) H hH hc
  have hd (N : JetRing) : ev (jetSeparant J.f) * δ (ev N) = ev (flow J.f N) :=
    hδ (Ideal.Quotient.mk _ N)
  refine ⟨δ, ⟨?_, ?_, hd⟩⟩
  · apply cancel_unit hc
    rw [hd]
    change ev (flow J.f (C Polynomial.X)) = _
    simp only [flow_C, Polynomial.derivative_X, coeffDiff_X, map_zero, zero_add, map_one,
      mul_one, map_mul]
    rfl
  · apply cancel_unit hc
    rw [hd, flow_sep, map_mul]
    rfl
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_1
noncomputable section
open K1_14 (Equation Seeds)
open HighCore82258Upper_3 (JetRing ordinate)
open HighCore82258Upper_3_1 (velocity jetSeparant coefficientDerivative secondAlongVelocity)
open HighCore82258Upper_3_1_2
open Polynomial (C eval₂RingHom)
open private flow flow_mul flow_C flow_X coeffDiff_add coeffDiff_mul coeff_coeffDiff
  coeffDiff_derivative from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
open private eval_coefficient from ProximityPrize.SubmissionLower.HighCore82258UpperGeometry
private theorem coeffDiff_C (s : Seeds) :
    coefficientDerivative (C s) = C (HighCore82258Upper_4.coeffDx s) := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  cases n <;> simp [coeff_coeffDiff, HighCore82258Upper_4.coeff_coeffDx]
private theorem deriv_mul {R : Type*} [CommRing R] (δ : ChartDerivation R) (x y : R) :
    δ (x*y) = x*δ y + δ x*y := by
  rw [δ.leibniz, smul_eq_mul, smul_eq_mul, mul_comm y]
private theorem root_chain {R : Type*} [CommRing R] (δ : ChartDerivation R)
    (E : Equation →+* R)
    (hs : ∀ s : Seeds, δ (E (C s)) = E (C (HighCore82258Upper_4.coeffDx s))) (N : Equation) :
    δ (E N) = E (coefficientDerivative N) + δ (E Polynomial.X) * E N.derivative := by
  have hstep (p q : Equation)
      (hp : δ (E p) = E (coefficientDerivative p) + δ (E Polynomial.X) * E p.derivative)
      (hq : δ (E q) = E (coefficientDerivative q) + δ (E Polynomial.X) * E q.derivative) :
      δ (E (p*q)) = E (coefficientDerivative (p*q)) + δ (E Polynomial.X) * E (p*q).derivative := by
    simp only [map_mul, deriv_mul, hp, hq, coeffDiff_mul, Polynomial.derivative_mul, map_add]
    ring
  have hx : δ (E Polynomial.X) =
      E (coefficientDerivative Polynomial.X) + δ (E Polynomial.X) * E Polynomial.X.derivative := by
    simp only [coeffDiff_X, Polynomial.derivative_X, map_zero, zero_add, map_one, mul_one]
  induction N using Polynomial.induction_on with
  | C s => simp only [hs, coeffDiff_C, Polynomial.derivative_C, map_zero, mul_zero, add_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, coeffDiff_add, mul_add]
    ring
  | monomial n s ih =>
    rw [pow_succ, ← mul_assoc]
    exact hstep _ _ ih hx
private theorem jet_chain {R : Type*} [CommRing R] (δ : ChartDerivation R)
    (ev : JetRing →+* R) (f : Equation)
    (hC : ∀ q : Equation, δ (ev (C q)) =
      ev (C (coefficientDerivative q)) + ev velocity * ev (C q.derivative))
    (hX : ev (jetSeparant f) * δ (ev velocity) = -ev (secondAlongVelocity f))
    (N : JetRing) : ev (jetSeparant f) * δ (ev N) = ev (flow f N) := by
  have hstep (p q : JetRing)
      (hp : ev (jetSeparant f) * δ (ev p) = ev (flow f p))
      (hq : ev (jetSeparant f) * δ (ev q) = ev (flow f q)) :
      ev (jetSeparant f) * δ (ev (p*q)) = ev (flow f (p*q)) := by
    simp only [flow_mul, map_add, map_mul, deriv_mul]
    linear_combination ev p * hq + ev q * hp
  have hx : ev (jetSeparant f) * δ (ev velocity) = ev (flow f velocity) := by
    simpa only [flow_X, map_neg] using hX
  induction N using Polynomial.induction_on with
  | C s => rw [hC, flow_C, map_mul, map_add, map_mul]
  | add p q hp hq => simp only [map_add, mul_add, hp, hq]
  | monomial n s ih =>
    rw [pow_succ, ← mul_assoc]
    exact hstep _ _ ih hx
private theorem ordinate_deriv {R : Type*} [CommRing R] (δ : ChartDerivation R)
    {y z v : R} (hy : y*z = 1) (hv : δ y = v) : δ z = -(v*z^2) := by
  have h := congrArg (fun t => δ t) hy
  rw [deriv_mul, Derivation.map_one_eq_zero, hv] at h
  linear_combination z * h - δ z * hy
private theorem reverse_euler (f : Equation) (e : ℕ) (hf : f.natDegree ≤ e) :
    (Polynomial.X * f.derivative).reflect e + Polynomial.X * (f.reflect e).derivative =
      C (e : Seeds) * f.reflect e := by
  have hcoeff (g : Equation) (n : ℕ) : (Polynomial.X*g.derivative).coeff n = g.coeff n * (n : Seeds) := by
    cases n with
    | zero => simp
    | succ n => simp only [Polynomial.coeff_X_mul,
        Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_reflect, hcoeff, Polynomial.coeff_C_mul]
  by_cases hn : n ≤ e
  · rw [Polynomial.revAt_le hn, ← mul_add, ← Nat.cast_add, Nat.sub_add_cancel hn, mul_comm]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hf.trans_lt (Nat.lt_of_not_ge hn))]
    simp
private theorem reverse_chart {R : Type*} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hy : φ ordinate * z = 1) (f : Equation) {e : ℕ}
    (hf : f.natDegree ≤ e) (he : 2 ≤ e) (hroot : φ (C f) = 0) :
    inverseEval φ z (C (f.reflect e)) = 0 ∧
      inverseEval φ z (jetSeparant (f.reflect e)) = -(z^(e-2) * φ (jetSeparant f)) := by
  let y := φ ordinate
  let i := seedMap φ
  let E := eval₂RingHom i z
  have hzy : z*y = 1 := (mul_comm _ _).trans hy
  let : Invertible y := ⟨z, hzy, hy⟩
  have href (p : Equation) (hp : p.natDegree ≤ e) : E (p.reflect e) = z^e * φ (C p) := by
    have h := Polynomial.eval₂_reflect_mul_pow i y e p hp
    rw [eval_coefficient]
    change E (p.reflect e) * y^e = p.eval₂ i y at h
    rw [← h, ← mul_assoc, mul_comm (z^e) (E _), mul_assoc, ← mul_pow, hzy, one_pow, mul_one]
  have hE (q : Equation) : inverseEval φ z (C q) = E q := by
    simp [inverseEval, Polynomial.coe_eval₂RingHom, E, i]
  have hF : E (f.reflect e) = 0 := by rw [href f hf, hroot, mul_zero]
  refine ⟨(hE _).trans hF, ?_⟩
  have hD : (Polynomial.X*f.derivative).natDegree ≤ e := by
    have hm := Polynomial.natDegree_mul_le (p := (Polynomial.X : Equation)) (q := f.derivative)
    rw [Polynomial.natDegree_X] at hm
    have hd := Polynomial.natDegree_derivative_le f
    omega
  have h := congrArg (fun q => E q) (reverse_euler f e hf)
  simp only [map_add, map_mul, hF, mul_zero] at h
  rw [href _ hD, map_mul, map_mul] at h
  rw [show jetSeparant (f.reflect e) = C (f.reflect e).derivative from rfl, hE]
  have hX : E Polynomial.X = z := Polynomial.eval₂_X _ _
  have hpow : z^e * y = z * z^(e-2) := by
    calc
      z^e * y = z^(e-2+1) * (z*y) := by
        rw [← mul_assoc, ← pow_succ, show e-2+1+1 = e by omega]
      _ = z * z^(e-2) := by rw [hzy, mul_one, pow_succ']
  change E (f.reflect e).derivative = -(z^(e-2) * φ (C f.derivative))
  apply cancel_unit (IsUnit.of_mul_eq_one y hzy)
  rw [hX, ← mul_assoc] at h
  change (z^e * y) * φ (C f.derivative) + z * E (f.reflect e).derivative = 0 at h
  rw [hpow] at h
  linear_combination h
private theorem transport {R : Type*} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hy : φ ordinate * z = 1) (f : Equation) {e : ℕ} (hf : f.natDegree ≤ e)
    (he : 2 ≤ e) (hroot : φ (C f) = 0) (hc : IsUnit (φ (jetSeparant f)))
    (δ : ChartDerivation R) (h : ChartFlow f φ δ) :
    ChartFlow (f.reflect e) (inverseEval φ z) δ ∧
      inverseEval φ z (jetSeparant (f.reflect e)) = -(z^(e-2) * φ (jetSeparant f)) := by
  let ψ := inverseEval φ z
  let F := f.reflect e
  let E := ψ.comp (C : Equation →+* JetRing)
  obtain ⟨hF, hsep⟩ := reverse_chart φ z hy f hf he hroot
  have hseed (s : Seeds) : E (C s) = φ (C (C s)) := by
    simp [E, ψ, inverseEval, seedMap, Polynomial.coe_eval₂RingHom]
  have hs (s : Seeds) : δ (E (C s)) = E (C (HighCore82258Upper_4.coeffDx s)) := by
    rw [hseed, hseed]
    apply cancel_unit hc
    have ha := h.action (C (C s))
    change φ (jetSeparant f) * δ (φ (C (C s))) = φ (flow f (C (C s))) at ha
    rw [ha, flow_C, coeffDiff_C]
    simp
  have hz : E Polynomial.X = z := by simp [E, ψ, inverseEval, Polynomial.coe_eval₂RingHom]
  have hw : ψ velocity = -(φ velocity*z^2) := by
    simp [ψ, inverseEval, velocity, Polynomial.coe_eval₂RingHom]
  have hδz : δ (E Polynomial.X) = ψ velocity := by
    rw [hz, hw]
    exact ordinate_deriv δ hy h.root
  have hC (q : Equation) :
      δ (E q) = E (coefficientDerivative q) + ψ velocity * E q.derivative := by
    rw [root_chain δ E hs, hδz]
  have hT : E (coefficientDerivative F) + ψ velocity * E F.derivative = 0 := by
    have ht := congrArg (fun t => δ t) hF
    change δ (E F) = δ 0 at ht
    rw [hC, map_zero] at ht
    exact ht
  have hV : ψ (jetSeparant F) * δ (ψ velocity) = -ψ (secondAlongVelocity F) := by
    have ht := congrArg (fun t => δ t) hT
    rw [map_zero, map_add, deriv_mul, hC (coefficientDerivative F), hC F.derivative,
      ← coeffDiff_derivative] at ht
    change E F.derivative * δ (ψ velocity) = _
    simp only [secondAlongVelocity, map_add, map_mul, map_ofNat, map_pow]
    change E F.derivative * δ (ψ velocity) =
      -(E (coefficientDerivative (coefficientDerivative F)) +
        2 * ψ velocity * E (coefficientDerivative F.derivative) +
        (ψ velocity)^2 * E F.derivative.derivative)
    linear_combination ht
  have hsepFlow : δ (ψ (jetSeparant F)) = ψ (sepAlong F) := by
    rw [sepAlong, map_add, map_mul]
    change δ (E F.derivative) =
      E (coefficientDerivative F.derivative) + ψ velocity * E F.derivative.derivative
    exact hC F.derivative
  exact ⟨⟨hδz, hsepFlow, jet_chain δ ψ F hC hV⟩, hsep⟩
private theorem inverse_flow : HighCore82258Upper_3_1_2.c2 := by
  intro J B D δ h
  exact transport (finite J B D) (reciprocal J B D) (mul_reciprocal J B D)
    J.f le_rfl (Nat.le_of_succ_le J.sheets) (finite_root J B D) (separant_unit J B D) δ h
theorem proof : HighCore82258GeometryGoals.c1 :=
  HighCore82258Upper_3_1_2.of_children finite_flow inverse_flow
end
end HighCore82258GeometryCert_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2
def c1 : Prop := HighCore82258Upper_3_2_4.c1
def c2 : Prop := HighCore82258Upper_3_2_4.c2
theorem of_children (h1 : c1) (h2 : c2) : HighCore82258GeometryGoals.c2 :=
  HighCore82258Upper_3_2_4.of_children h1 h2
end HighCore82258GeometryCert_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_1
noncomputable section
open K1_14 (FX)
open HighCore82258Upper_3 HighCore82258Upper_3_2_4 MvPolynomial
open scoped BigOperators MonomialOrder
private def finiteDegLex (α : Type) [Fintype α] : MonomialOrder α := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' _ (Fintype.equivFin α).injective
  have : WellFoundedGT α := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
private def termOrder : MonomialOrder CoxVar := finiteDegLex CoxVar
private def leading (L : Layer) (d : Degree) : Set Exponent :=
  {m | ∃ p : Cox, p ∈ L d ∧ p ≠ 0 ∧ termOrder.degree p = m}
private def initial (L : Layer) : Set Exponent :=
  {m | m ∈ leading L (Finsupp.weight coxWeight m)}
private theorem leading_weight {L : Layer} {d : Degree} (hL : Stable L)
    {m : Exponent} (hm : m ∈ leading L d) : Finsupp.weight coxWeight m = d := by
  obtain ⟨p, hp, hp0, rfl⟩ := hm
  have hp' : p.IsWeightedHomogeneous coxWeight d := hL.1 d hp
  exact hp' (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0)
private theorem initial_upper {L : Layer} (hL : Stable L) : IsUpperSet (initial L) := by
  classical
  intro m n hmn hm
  obtain ⟨p, hp, hp0, hd⟩ := hm
  let q : Cox := monomial (n - m) 1
  have hq : q ∈ homogeneous (Finsupp.weight coxWeight (n - m)) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  have hq0 : q ≠ 0 := by simp [q]
  have he : Finsupp.weight coxWeight (n - m) + Finsupp.weight coxWeight m =
      Finsupp.weight coxWeight n := by
    rw [← map_add, tsub_add_cancel_of_le hmn]
  refine ⟨q * p, ?_, mul_ne_zero hq0 hp0, ?_⟩
  · rw [← he]
    exact hL.2 _ _ hq hp
  · rw [termOrder.degree_mul hq0 hp0, hd]
    simp only [q, termOrder.degree_monomial, one_ne_zero, ite_false, tsub_add_cancel_of_le hmn]
private theorem leading_finite {L : Layer} (hL : Stable L) (d : Degree) :
    (leading L d).Finite :=
  (finite_weight d).subset fun _ hm => leading_weight hL hm
private theorem mem_leading_iff {L : Layer} (hL : Stable L) {d : Degree} {m : Exponent} :
    m ∈ leading L d ↔ m ∈ initial L ∧ Finsupp.weight coxWeight m = d := by
  constructor
  · intro hm
    have hw := leading_weight hL hm
    exact ⟨show m ∈ leading L (Finsupp.weight coxWeight m) from hw.symm ▸ hm, hw⟩
  · rintro ⟨hm, hw⟩
    exact hw ▸ (show m ∈ leading L (Finsupp.weight coxWeight m) from hm)
private theorem independent_of_leading {σ K ι : Type} [Field K] [Fintype ι]
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0)
    (hd : Function.Injective fun i => m.degree (p i)) : LinearIndependent K p := by
  classical
  refine (Fintype.linearIndependent_iff (v := p)).mpr ?_
  intro w hw j
  by_contra hj
  let active : Finset ι := Finset.univ.filter fun i => w i ≠ 0
  obtain ⟨i, hi, hmax⟩ := active.exists_max_image (fun a => m.toSyn (m.degree (p a)))
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hwi := (Finset.mem_filter.mp hi).2
  let e := m.degree (p i)
  have hz := congrArg (lcoeff K e) hw
  simp only [map_sum, map_smul, map_zero] at hz
  change ∑ a : ι, w a * (p a).coeff e = 0 at hz
  rw [Finset.sum_eq_single i] at hz
  · exact (mul_ne_zero hwi (MonomialOrder.coeff_degree_ne_zero_iff.mpr (hp i))) hz
  · intro a _ hai
    by_cases ha : w a = 0
    · rw [ha, zero_mul]
    · have hle := hmax a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      have hlt := lt_of_le_of_ne hle (fun he => hai (hd (m.toSyn.injective he)))
      rw [m.coeff_eq_zero_of_lt hlt, mul_zero]
  · simp
private theorem rank_leading {L : Layer} (hL : Stable L) (d : Degree) :
    Module.finrank FX (L d) = (leading L d).ncard := by
  classical
  let : Fintype (leading L d) := (leading_finite hL d).fintype
  let coeffs : L d →ₗ[FX] (leading L d → FX) :=
    LinearMap.pi fun i => (lcoeff FX i.val).comp (L d).subtype
  have hinj : Function.Injective coeffs := by
    intro u v huv
    apply sub_eq_zero.mp
    let p := u - v
    change p = 0
    have hz : coeffs p = 0 := (coeffs.map_sub u v).trans (sub_eq_zero.mpr huv)
    apply Subtype.ext
    by_contra hp
    have hp0 : (p : Cox) ≠ 0 := hp
    let i : leading L d := ⟨termOrder.degree (p : Cox), p, p.property, hp0, rfl⟩
    have hc : (p : Cox).coeff (termOrder.degree (p : Cox)) = 0 :=
      congrFun hz i
    exact (MonomialOrder.coeff_degree_ne_zero_iff.mpr hp0) hc
  have : Module.Finite FX (L d) := Module.Finite.of_injective coeffs hinj
  choose p hp hp0 hd using (fun i : leading L d => i.property)
  let v : leading L d → L d := fun i => ⟨p i, hp i⟩
  have he : Function.Injective (fun i => termOrder.degree (p i)) := by
    intro i j hij
    exact Subtype.ext ((hd i).symm.trans (hij.trans (hd j)))
  have hind : LinearIndependent FX v := by
    exact LinearIndependent.of_comp (v := v) (L d).subtype
      (independent_of_leading termOrder p hp0 he)
  rw [← Set.fintypeCard_eq_ncard]
  refine le_antisymm ?_ hind.fintype_card_le_finrank
  rw [← Module.finrank_pi FX]
  exact LinearMap.finrank_le_finrank_of_injective (f := coeffs) hinj
theorem proof : HighCore82258GeometryCert_2.c1 := by
  change HighCore82258Upper_3_2_4.c1
  intro A B hA hB hab
  have hsub (d : Degree) : leading A d ⊆ leading B d := by
    rintro m ⟨p, hp, hp0, hd⟩
    exact ⟨p, hab d hp, hp0, hd⟩
  refine ⟨initial A, initial B, initial_upper hA, initial_upper hB,
    fun m hm => hsub (Finsupp.weight coxWeight m) hm, fun d => ?_⟩
  have he : {m | m ∈ initial B \ initial A ∧ Finsupp.weight coxWeight m = d} =
      leading B d \ leading A d := by
    ext m
    change (m ∈ initial B ∧ m ∉ initial A) ∧ Finsupp.weight coxWeight m = d ↔
      m ∈ leading B d ∧ m ∉ leading A d
    rw [mem_leading_iff hA, mem_leading_iff hB]
    tauto
  rw [rank_leading hA, rank_leading hB, exponentCount, he, add_comm]
  exact Set.ncard_sdiff_add_ncard_of_subset (hsub d) (leading_finite hB d)
end
end HighCore82258GeometryCert_2_1
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2_4
def rootFree (B : Block) : Finset (Fin 2) :=
  Finset.univ.filter fun i => Sum.inl i ∈ B.free
def seedFree (B : Block) : Finset (Fin 3) :=
  Finset.univ.filter fun i => tᵢ i ∈ B.free
def rv {R : Type} [Semiring R] (r : ℕ) (a b : Prop) [Decidable a] [Decidable b]
    (T H HT HT₂ : R) : R :=
  if r = 0 then 0
  else if a then
    if b then T * (if r = 1 then 1 else HT)
    else if r = 1 then 1 else HT₂
  else if b then if r = 1 then 1 else H
  else 0
def seeds {R : Type} [Semiring R] (r : ℕ) (S S₂ Q : R) : R :=
  if r = 1 then 1 else if r = 2 then S else if r = 3 then Q * S * S₂ else 0
private def velocities (B : Block) (b : ℕ) : Finset ℕ :=
  if v₀ ∈ B.free then (if v₁ ∈ B.free then Finset.range (b+1) else {b})
  else if v₁ ∈ B.free then {0} else ∅
private theorem mem_velocities (B : Block) {b j : ℕ} (hb : 0 < b) :
    j ∈ velocities B b ↔ j ≤ b ∧ (v₀ ∉ B.free → j = 0) ∧
      (v₁ ∉ B.free → b-j = 0) := by
  by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [velocities, h₀', h₁'] <;> omega
private theorem mem_comp {n d : ℕ} {F : Finset (Fin n)} {f : Fin n →₀ ℕ} :
    f ∈ F.finsuppAntidiag d ↔ (∑ i, f i) = d ∧ ∀ i ∉ F, f i = 0 := by
  rw [Finset.mem_finsuppAntidiag', Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun h i hi => Finsupp.notMem_support_iff.mp (fun hm => hi (h hm))
  · intro h i hi
    by_contra hf
    exact (Finsupp.mem_support_iff.mp hi) (h i hf)
private def project {n : ℕ} (m : Exponent) (f : Fin n → CoxVar) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (f i))
private def pack (r : Fin 2 →₀ ℕ) (j b : ℕ) (z : Fin 3 →₀ ℕ) : Exponent :=
  Finsupp.equivFunOnFinite.symm (Sum.elim r (Sum.elim ![j,b-j] z))
private abbrev Increments (B : Block) (d : Degree) :=
  {m : Exponent // (∀ i ∉ B.free, m i = 0) ∧ Finsupp.weight coxWeight m = d}
private def enum (B : Block) (a b c : ℕ) (hb : 0 < b) :
    Increments B (nefDegree a b c) ≃
      (Σ j : velocities B b, (rootFree B).finsuppAntidiag (a+2*j.val)) ×
        (seedFree B).finsuppAntidiag c where
  toFun m := by
    have hz := m.prop.1
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have ha := congrArg Prod.fst hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    have hc := congrArg (fun d : Degree => d.2.2) hw
    change m.val h₀ + m.val h₁ + 2*m.val v₁ = a+2*b at ha
    change m.val v₀ + m.val v₁ = b at hv
    change m.val (tᵢ 0) + m.val (tᵢ 1) + m.val (tᵢ 2) = c at hc
    refine ⟨⟨⟨m.val v₀, (mem_velocities B hb).mpr ⟨by omega, hz _, ?_⟩⟩,
      ⟨project m.val Sum.inl, mem_comp.mpr ⟨?_, ?_⟩⟩⟩,
      ⟨project m.val tᵢ, mem_comp.mpr ⟨?_, ?_⟩⟩⟩
    · intro h
      have := hz v₁ h
      omega
    · rw [Fin.sum_univ_two]
      change m.val h₀ + m.val h₁ = a+2*m.val v₀
      omega
    · exact fun i hi => hz (Sum.inl i) (by simpa [rootFree] using hi)
    · rw [Fin.sum_univ_three]
      exact hc
    · exact fun i hi => hz (tᵢ i) (by simpa [seedFree] using hi)
  invFun p := by
    rcases p with ⟨⟨j, r⟩, z⟩
    have hj := ((mem_velocities B hb).mp j.prop).1
    have hj₀ := ((mem_velocities B hb).mp j.prop).2.1
    have hj₁ := ((mem_velocities B hb).mp j.prop).2.2
    have hr := (mem_comp.mp r.prop).1
    have hrz := (mem_comp.mp r.prop).2
    have hs := (mem_comp.mp z.prop).1
    have hsz := (mem_comp.mp z.prop).2
    rw [Fin.sum_univ_two] at hr
    rw [Fin.sum_univ_three] at hs
    refine ⟨pack r.val j.val b z.val, ?_, ?_⟩
    · intro i hi
      rcases i with i | (i | i)
      · exact hrz i (by simpa [rootFree] using hi)
      · fin_cases i
        · exact hj₀ hi
        · exact hj₁ hi
      · apply hsz i
        intro hz
        unfold seedFree at hz
        exact hi (Finset.mem_filter.mp hz).2
    · rw [weight_coordinates]
      change (r.val 0 + r.val 1 + 2*(b-j.val), j.val+(b-j.val),
        z.val 0+z.val 1+z.val 2) = (a+2*b,b,c)
      rw [hr, hs]
      congr 1
      · omega
      · congr 1
        omega
  left_inv m := by
    have hw := m.prop.2
    rw [weight_coordinates] at hw
    have hv := congrArg (fun d : Degree => d.2.1) hw
    change m.val v₀ + m.val v₁ = b at hv
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rcases i with i | (i | i)
    · rfl
    · fin_cases i
      · rfl
      · change b-m.val v₀ = m.val v₁
        omega
    · rfl
  right_inv p := by
    rcases p with ⟨⟨j,r⟩,z⟩
    apply Prod.ext
    · exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext (Finsupp.ext fun _ => rfl)))
    · exact Subtype.ext (Finsupp.ext fun _ => rfl)
private def shift (B : Block) (d e : Degree) (hw : Finsupp.weight coxWeight B.base + d = e) :
    Increments B d ≃ {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} :=
  Equiv.ofBijective (fun m => ⟨B.base + m.val, ⟨m.val, m.prop.1, rfl⟩, by
    rw [map_add, m.prop.2, hw]⟩) (by
      constructor
      · intro m n h
        exact Subtype.ext (add_left_cancel (congrArg Subtype.val h))
      · rintro ⟨_, ⟨m, hm, rfl⟩, h⟩
        rw [map_add, ← hw] at h
        exact ⟨⟨m, hm, add_left_cancel h⟩, rfl⟩)
private theorem comp_card {ι : Type} [DecidableEq ι] (F : Finset ι)
    {n : ℕ} (hn : 0 < n) (hF : F.card ≤ 3) :
    (F.finsuppAntidiag n).card =
      if F.card = 0 then 0 else if F.card = 1 then 1
      else if F.card = 2 then n+1 else (n+2).choose 2 := by
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  interval_cases h : F.card
  · simp [Nat.choose_eq_zero_of_lt (show n-1 < n by omega)]
  · simp [show 1+n-1 = n by omega]
  · rw [show 2+n-1 = n+1 by omega, Nat.choose_symm_of_eq_add (a := n) (b := 1) rfl]
    simp
  · rw [show 3+n-1 = n+2 by omega, Nat.choose_symm_of_eq_add (a := n) (b := 2) rfl]
    simp
private theorem sum_widths (a b : ℕ) :
    (∑ j ∈ Finset.range (b+1), (a+2*j+1)) = (b+1)*(a+b+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    ring
private theorem root_velocity_card (B : Block) {a b : ℕ} (ha : 0 < a) :
    (∑ j ∈ velocities B b, ((rootFree B).finsuppAntidiag (a+2*j)).card) =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) := by
  have hR : (rootFree B).card ≤ 2 := (Finset.card_le_univ _).trans (by simp)
  have hc (j : ℕ) := comp_card (rootFree B) (n := a+2*j) (by omega) (hR.trans (by decide))
  simp_rw [hc]
  interval_cases h : (rootFree B).card <;>
    by_cases h₀' : v₀ ∈ B.free <;> by_cases h₁' : v₁ ∈ B.free <;>
    simp [rv, velocities, h₀', h₁', sum_widths]
theorem fibre_card (B : Block) {a b c : ℕ} {e : Degree}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw : Finsupp.weight coxWeight B.base + nefDegree a b c = e) :
    exponentCount B.exponents e =
      rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
        (b+1) (a+1) (a+b+1) (a+2*b+1) *
      (if (seedFree B).card = 0 then 0 else if (seedFree B).card = 1 then 1
        else if (seedFree B).card = 2 then c+1 else (c+2).choose 2) := by
  classical
  change Nat.card {m : Exponent // m ∈ B.exponents ∧ Finsupp.weight coxWeight m = e} = _
  rw [Nat.card_congr ((shift B _ _ hw).symm.trans (enum B a b c hb)),
    Nat.card_prod, Nat.card_sigma]
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  change (∑ j ∈ (velocities B b).attach, ((rootFree B).finsuppAntidiag (a+2*j.val)).card) * _ = _
  have hS : (seedFree B).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
  rw [Finset.sum_attach (velocities B b) (fun j : ℕ => ((rootFree B).finsuppAntidiag (a+2*j)).card),
    root_velocity_card B ha, comp_card (seedFree B) hc hS]
end
end HighCore82258GeometryCert_2_2
end
section
set_option autoImplicit false
namespace HighCore82258GeometryCert_2_2
noncomputable section
open HighCore82258Upper_3 HighCore82258Upper_3_2 HighCore82258Upper_3_2_4 MvPolynomial
private abbrev Exp := Fin 3 →₀ ℕ
private theorem coeff_add_apply (p q : HilbertPoly) (m : Exp) :
    (p+q).coeff m = p.coeff m + q.coeff m := by simp
private theorem coeff_nonneg {p : HilbertPoly} (hp : NonnegativeTop p)
    {m : Exp} (hm : p.totalDegree ≤ m.degree) : 0 ≤ p.coeff m := by
  rcases lt_or_eq_of_le hm with h | h
  · rw [coeff_eq_zero_of_totalDegree_lt h]
  · exact hp m h.symm
private theorem top_add_right {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) (hq' : q ≠ 0) (h : p.totalDegree ≤ q.totalDegree) :
    NonnegativeTop (p+q) := by
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup q.support (support_nonempty.mpr hq')
    (fun m => m.degree)
  change q.totalDegree = m.degree at hd
  have hpos : 0 < q.coeff m :=
    lt_of_le_of_ne (hq m hd.symm) (ne_comm.mp (MvPolynomial.mem_support_iff.mp hm))
  have hm' : m ∈ (p+q).support := by
    rw [MvPolynomial.mem_support_iff, coeff_add_apply]
    exact (add_pos_of_nonneg_of_pos (coeff_nonneg hp (h.trans_eq hd)) hpos).ne'
  have hd' : (p+q).totalDegree = q.totalDegree :=
    le_antisymm ((totalDegree_add _ _).trans (max_eq_right h).le)
      (hd.trans_le (le_totalDegree hm'))
  intro n hn
  change n.degree = (p+q).totalDegree at hn
  rw [coeff_add_apply]
  exact add_nonneg (coeff_nonneg hp (h.trans_eq (hn.trans hd').symm)) (hq n (hn.trans hd'))
private theorem top_add {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p+q) := by
  by_cases hp' : p = 0
  · simpa [hp'] using hq
  by_cases hq' : q = 0
  · simpa [hq'] using hp
  rcases le_total p.totalDegree q.totalDegree with h | h
  · exact top_add_right hp hq hq' h
  · rw [add_comm]
    exact top_add_right hq hp hp' h
private theorem top_zero : NonnegativeTop (0 : HilbertPoly) := by
  intro m _
  simp
private theorem top_mul {p q : HilbertPoly} (hp : NonnegativeTop p)
    (hq : NonnegativeTop q) : NonnegativeTop (p*q) := by
  classical
  by_cases hp' : p = 0
  · simpa [hp'] using top_zero
  by_cases hq' : q = 0
  · simpa [hq'] using top_zero
  intro m hm
  change m.degree = (p*q).totalDegree at hm
  rw [totalDegree_mul_of_isDomain hp' hq'] at hm
  rw [coeff_mul]
  apply Finset.sum_nonneg
  rintro ⟨a,b⟩ hab
  have he : a+b = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hd : a.degree+b.degree = m.degree := by rw [← map_add, he]
  by_cases ha : p.totalDegree < a.degree
  · simp [coeff_eq_zero_of_totalDegree_lt ha]
  by_cases hb : q.totalDegree < b.degree
  · simp [coeff_eq_zero_of_totalDegree_lt hb]
  exact mul_nonneg (hp a (by change a.degree = p.totalDegree; omega))
    (hq b (by change b.degree = q.totalDegree; omega))
private theorem top_C (r : ℚ) (hr : 0 ≤ r) : NonnegativeTop (C r : HilbertPoly) := by
  intro m _
  rw [coeff_C]
  split_ifs
  · exact hr
  · exact le_rfl
private theorem top_one : NonnegativeTop (1 : HilbertPoly) := by
  simpa only [map_one] using top_C 1 zero_le_one
private def affine (i j : Fin 3) (r b : ℚ) : HilbertPoly :=
  MvPolynomial.X i + C r * MvPolynomial.X j + C b
private theorem top_affine (i j : Fin 3) {r : ℚ} (hr : 0 ≤ r) (b : ℚ) :
    NonnegativeTop (affine i j r b) := by
  classical
  have hX (k : Fin 3) (m : Exp) : 0 ≤ (MvPolynomial.X k : HilbertPoly).coeff m := by
    rw [coeff_X]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  let p : HilbertPoly := MvPolynomial.X i + C r * MvPolynomial.X j
  have hp (m : Exp) : 0 ≤ p.coeff m := by
    change 0 ≤ (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff m
    rw [coeff_add_apply, coeff_C_mul]
    exact add_nonneg (hX i m) (mul_nonneg hr (hX j m))
  have hm : Finsupp.single i 1 ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    change (MvPolynomial.X i + C r * MvPolynomial.X j : HilbertPoly).coeff (Finsupp.single i 1) ≠ 0
    rw [coeff_add_apply, coeff_C_mul, show (MvPolynomial.X i : HilbertPoly).coeff (Finsupp.single i 1) = 1 by
      simp [coeff_X]]
    exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hX j _))).ne'
  have hd := le_totalDegree hm
  change (Finsupp.single i 1).degree ≤ p.totalDegree at hd
  rw [Finsupp.degree_single] at hd
  intro m hm
  change m.degree = (p + C b).totalDegree at hm
  have hd' : (C b : HilbertPoly).totalDegree < p.totalDegree := by
    rw [totalDegree_C]
    omega
  rw [totalDegree_add_eq_left_of_totalDegree_lt hd'] at hm
  change 0 ≤ (p + C b).coeff m
  have hm' : (C b : HilbertPoly).totalDegree < m.degree := by rwa [hm]
  rw [coeff_add_apply, coeff_eq_zero_of_totalDegree_lt hm', add_zero]
  exact hp m
private def baseDegree (B : Block) : Degree := Finsupp.weight coxWeight B.base
private def profile (B : Block) : HilbertPoly :=
  let (u,v,w) := baseDegree B
  rv (rootFree B).card (v₀ ∈ B.free) (v₁ ∈ B.free)
    (affine 1 1 0 (1-v)) (affine 0 0 0 (1+2*v-u))
    (affine 0 1 1 (1+v-u)) (affine 0 1 2 (1-u)) *
  seeds (seedFree B).card
    (affine 2 2 0 (1-w)) (affine 2 2 0 (2-w)) (C (1/2))
private theorem profile_top (B : Block) : NonnegativeTop (profile B) := by
  change NonnegativeTop (rv _ _ _ _ _ _ _ * seeds _ _ _ _)
  apply top_mul
  · unfold rv
    split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _
      | exact top_mul (top_affine _ _ (by norm_num) _) top_one
      | exact top_mul (top_affine _ _ (by norm_num) _) (top_affine _ _ (by norm_num) _)
  · unfold seeds
    split_ifs <;> first
      | exact top_zero
      | exact top_one
      | exact top_affine _ _ (by norm_num) _
      | exact top_mul (top_mul (top_C _ (by norm_num)) (top_affine _ _ (by norm_num) _))
          (top_affine _ _ (by norm_num) _)
private def threshold (B : Block) : ℕ :=
  let (u,v,w) := baseDegree B
  u+v+w+1
private theorem profile_eval (B : Block) (h t s : ℕ)
    (hh : threshold B ≤ h) (ht : threshold B ≤ t) (hs : threshold B ≤ s) :
    (exponentCount B.exponents (nefDegree h t s) : ℚ) = evalHilbert (profile B) h t s := by
  rcases hbase : baseDegree B with ⟨u,v,w⟩
  have hw : Finsupp.weight coxWeight B.base = (u,v,w) := hbase
  simp only [threshold, hbase] at hh ht hs
  let a := h+2*v-u
  let b := t-v
  let c := s-w
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hweight : Finsupp.weight coxWeight B.base + nefDegree a b c = nefDegree h t s := by
    rw [hw]
    change (u+(a+2*b), v+b, w+c) = (h+2*t,t,s)
    dsimp [a,b,c]
    congr 1
    · omega
    · congr 1 <;> omega
  rw [fibre_card B ha hb hc hweight, Nat.cast_mul]
  let E := MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s : ℚ)]
  unfold evalHilbert profile
  rw [hbase]
  change _ = E (_ * _)
  rw [map_mul]
  congr 1
  · unfold rv
    split_ifs <;> simp [E, affine, a, b, Nat.cast_sub (show u ≤ h+2*v by omega),
      Nat.cast_sub (show v ≤ t by omega)] <;> ring
  · have hS : (seedFree B).card ≤ 3 := (Finset.card_le_univ _).trans (by simp)
    interval_cases (seedFree B).card <;>
      simp [E, seeds, affine, c, Nat.cast_choose_two,
        Nat.cast_sub (show w ≤ s by omega)] <;> ring
private theorem sum_top (blocks : Finset Block) : NonnegativeTop (∑ B ∈ blocks, profile B) := by
  classical
  induction blocks using Finset.induction_on with
  | empty => simpa using top_zero
  | insert B _ hB ih => rw [Finset.sum_insert hB]; exact top_add (profile_top B) ih
theorem proof : HighCore82258GeometryCert_2.c2 := by
  change HighCore82258Upper_3_2_4.c2
  intro blocks
  let N := ∑ B ∈ blocks, threshold B
  refine ⟨∑ B ∈ blocks, profile B, sum_top blocks, N, fun h t s hh ht hs => ?_⟩
  change ((∑ B ∈ blocks, exponentCount B.exponents (nefDegree h t s) : ℕ) : ℚ) =
    MvPolynomial.eval ![(h : ℚ),(t : ℚ),(s : ℚ)] (∑ B ∈ blocks, profile B)
  rw [Nat.cast_sum, map_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hN : threshold B ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hB
  exact profile_eval B h t s (hN.trans hh) (hN.trans ht) (hN.trans hs)
end
end HighCore82258GeometryCert_2_2
end
