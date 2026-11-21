import ProximityPrize.SubmissionLower.Rect51TangentJets

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace Rect51Tangent
noncomputable section
open HighCore82706Tangent (Input ResidueLift Factors)
open HighCore82706Tangent_3 (JetRing ordinate graphIdeal)
open HighCore82706Tangent_3_1 (velocity jetSeparant velocityNumerator pureDen pureOrdinate pureDegree)
open HighCore82706Tangent_3_1_2 (inverseEval seedMap reverseEquation reciprocalNumerator
  finite reciprocal mul_reciprocal clear_overlap)
open K1_14 (Equation FX)
open scoped BigOperators
open private numerator_bound from ProximityPrize.SubmissionLower.Rect51TangentJets
open private inverseOrdinate factorialScalar coord_transition scale_velocity eval_coefficient
  from ProximityPrize.SubmissionLower.HighCore82706TangentDeps
open HighCore82706_5_1 (finite_flow)
open private inverse_flow from ProximityPrize.SubmissionLower.HighCore82706Tangent

def baseDegree (J : Input) (r : ℕ) : ℕ := 1+(J.e-3)*r

private theorem inverse_polynomial {R : Type*} [CommRing R] (φ : JetRing →+* R)
    (z : R) (hz : φ ordinate * z = 1) {P : JetRing} {a b : ℕ} {v : Axes}
    (hP : Bounded P b v) :
    ∃ n : ℕ, ∃ G : JetRing,
      Bounded G b v ∧ Weighted G (a+n) ∧
      φ G = (φ ordinate)^(a+n) * inverseEval φ z P := by
  classical
  let y := φ ordinate
  let : Invertible y := ⟨z, by rw [mul_comm]; exact hz, hz⟩
  let n := 2*b + P.support.sup (fun j => (P.coeff j).natDegree)
  let N (j : ℕ) := a+n-2*j
  have hj (j : ℕ) (hm : j ∈ P.support) : j ≤ b :=
    (Polynomial.le_natDegree_of_mem_supp j hm).trans hP.1
  have hN (j : ℕ) (hm : j ∈ P.support) : (P.coeff j).natDegree ≤ N j := by
    have d : (P.coeff j).natDegree ≤ P.support.sup (fun j => (P.coeff j).natDegree) :=
      Finset.le_sup (f := fun j => (P.coeff j).natDegree) hm
    have b' := hj j hm
    dsimp only [n,N]
    omega
  have rN (j : ℕ) (hm : j ∈ P.support) : ((P.coeff j).reflect (N j)).natDegree ≤ N j :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl (hN j hm))
  let E (j : ℕ) : JetRing :=
    algebraMap FX JetRing ((-1:FX)^j) * Polynomial.monomial j ((P.coeff j).reflect (N j))
  refine ⟨n, ∑ j ∈ P.support, E j, Bounded.sum ?_, Weighted.sum ?_, ?_⟩
  · intro j hm
    have hc := Bounded.monomial ((hP.2 j).reflect (N j)) j
    have h := (Bounded.scalar ((-1:FX)^j)).mul hc
    simpa only [Nat.zero_add, zero_add] using
      h.mono (by simpa using hj j hm) (by intro i; simp)
  · intro j hm
    have hb := hj j hm
    have hmul : N j+2*j = a+n := by dsimp only [N,n]; omega
    have hw : Weighted (Polynomial.monomial j ((P.coeff j).reflect (N j))) (a+n) :=
      Weighted.monomial ((Nat.add_le_add_right (rN j hm) _).trans_eq hmul)
    simpa only [Nat.zero_add] using (Weighted.scalar ((-1:FX)^j)).mul hw
  · rw [map_sum]
    conv_rhs => rw [← P.sum_monomial_eq, Polynomial.sum_def, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hm
    have hv : 2*j ≤ a+n := by have h := hj j hm; dsimp only [n]; omega
    rw [show E j = algebraMap FX JetRing ((-1:FX)^j) *
      (Polynomial.C ((P.coeff j).reflect (N j)) * velocity^j) by
        rw [Polynomial.C_mul_X_pow_eq_monomial]]
    simp only [map_mul, map_pow, map_neg, map_one, eval_coefficient φ]
    rw [show inverseEval φ z (Polynomial.monomial j (P.coeff j)) =
        (P.coeff j).eval₂ (seedMap φ) z * (-(φ velocity * z^2))^j by
      rw [inverseEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        Polynomial.coe_eval₂RingHom]]
    rw [scale_velocity y z (φ velocity) ((P.coeff j).eval₂ (seedMap φ) z) hz hv]
    have hm' := Polynomial.eval₂_reflect_mul_pow (seedMap φ) y (N j)
      ((P.coeff j).reflect (N j)) (rN j hm)
    simp only [Polynomial.reflect_reflect] at hm'
    change (P.coeff j).eval₂ (seedMap φ) z * y^(N j) =
      ((P.coeff j).reflect (N j)).eval₂ (seedMap φ) y at hm'
    rw [hm']
    ring

private theorem pure_bound (J : Input) {v : Axes} (hf : SeedBound J.f v) {r k : ℕ}
    (hk : k+1 ≤ r) : Bounded (pureOrdinate J r (k+1)) r (r • v) := by
  have h := (Bounded.scalar (factorialScalar k)).mul
    (((Bounded.C hf.derivative).pow (r-1-k)).mul (numerator_bound hf k))
  apply h.mono
  · simpa only [Nat.mul_zero, Nat.zero_add] using hk
  · have e : (r-1-k) • v + k • v = (r-1) • v := by
      rw [← add_nsmul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
    rw [zero_add, e]
    intro i
    exact Nat.mul_le_mul_right (v i) (Nat.sub_le r 1)

private theorem reciprocal_pure_bound (J : Input) {v : Axes} (hf : SeedBound J.f v) {r k : ℕ}
    (hk : k+1 ≤ r) : Bounded (inverseOrdinate J r k) r (r • v) := by
  have hr : SeedBound (reverseEquation J) v := hf.reflect J.e
  have h := (Bounded.scalar ((-1:FX)^(r-1)*factorialScalar k)).mul
    (((Bounded.ordinate.pow (J.e-2+(r-1-k))).mul
      (((Bounded.C hr.derivative).pow (r-1-k)).mul (reciprocal_bound hr k))))
  apply h.mono
  · simpa only [Nat.mul_zero, Nat.zero_add] using hk
  · have e : (r-1-k) • v + k • v = (r-1) • v := by
      rw [← add_nsmul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
    simp only [smul_zero, zero_add, e]
    intro i
    exact Nat.mul_le_mul_right (v i) (Nat.sub_le r 1)

theorem represent_ordinate_succ (J : Input) (B : ResidueLift J) (D : Factors J B)
    {v : Axes} (hf : SeedBound J.f v) {r k : ℕ} (hk : k+1 ≤ r) :
    Represented (graphIdeal J B D) (baseDegree J r) r (r • v) (pureOrdinate J r (k+1)) := by
  obtain ⟨δ, hd⟩ := finite_flow J B D
  obtain ⟨hi, hc⟩ := inverse_flow J B D δ hd
  let φ := finite J B D
  let z := reciprocal J B D
  have hy := mul_reciprocal J B D
  let a := baseDegree J r+2*r
  obtain ⟨n,I,hb,hw,evalI⟩ :=
    inverse_polynomial φ z hy (a := a) (reciprocal_pure_bound J hf hk)
  have ht := coord_transition J hk φ z hd hi hy hc
  change φ (pureOrdinate J r (k+1)) = (φ ordinate)^a * inverseEval φ z (inverseOrdinate J r k) at ht
  have hz : φ (ordinate^n*pureOrdinate J r (k+1)-I) = 0 := by
    rw [map_sub,map_mul,map_pow,ht,evalI, ← mul_assoc, ← pow_add, Nat.add_comm n a, sub_self]
  obtain ⟨m,hm⟩ := clear_overlap J B D hz
  have hB : Bounded (ordinate^m*I) r (r • v) := by
    simpa only [Nat.mul_zero,zero_nsmul,smul_zero,Nat.zero_add,zero_add] using (Bounded.ordinate.pow m).mul hb
  have hW : Weighted (ordinate^m*I) (baseDegree J r+2*r+(n+m)) := by
    exact ((Weighted.ordinate.pow m).mul hw).mono (by dsimp only [a]; omega)
  have hg : ordinate^(n+m)*pureOrdinate J r (k+1)-ordinate^m*I ∈ graphIdeal J B D := by
    rw [pow_add]
    convert hm using 1
    ring
  exact Represented.of_inverse (pure_bound J hf hk) hB hW hg

#print axioms represent_ordinate_succ
end
end Rect51Tangent
