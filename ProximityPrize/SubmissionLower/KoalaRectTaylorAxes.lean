import ProximityPrize.SubmissionLower.KoalaRectJetCoords

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace KoalaRectTaylor
noncomputable section

open K1_14 (FX Equation Seeds)
open HighCore82219Upper (Input)
open HighCore82219Upper_3 (JetRing ordinate)
open HighCore82219Upper_3_1 (coefficientDerivative jetCoeffDerivative jetSeparant
  pureDen pureOrdinate secondAlongVelocity velocity velocityNumerator)
open HighCore82219Upper_3_1_2 (clearedAction reciprocalNumerator reverseEquation sepAlong)
open private HighCore82219Upper_3_1_1.coeff_coeffDiff HighCore82219Upper_3_1_1.coeff_lift
  HighCore82219Upper_3_1.coefficientDerivative_zero HighCore82219Upper_3_1_2.inverseOrdinate
  from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry
open HighCore82219Upper_3_1_1 (coeff_coeffDiff coeff_lift)
open HighCore82219Upper_3_1 (coefficientDerivative_zero)
open HighCore82219Upper_3_1_2 (inverseOrdinate)
open MvPolynomial (degreeOf degreeOf_le_iff degreeOf_add_le degreeOf_mul_le
  degreeOf_sum_le)

def EquationAxis (z : Fin 2) (q : Equation) (s : ℕ) : Prop :=
  ∀ i, (q.coeff i).degreeOf z ≤ s

def JetAxis (z : Fin 2) (q : JetRing) (s : ℕ) : Prop :=
  ∀ i, EquationAxis z (q.coeff i) s

namespace EquationAxis

variable {z : Fin 2} {q p : Equation} {s t : ℕ}

theorem zero : EquationAxis z 0 s := by
  intro i
  simp

theorem C {p : Seeds} (hp : p.degreeOf z ≤ s) : EquationAxis z (Polynomial.C p) s := by
  intro i
  cases i with
  | zero => simpa using hp
  | succ i => simp

theorem scalar (c : FX) : EquationAxis z (Polynomial.C (MvPolynomial.C c)) 0 :=
  C (by simp)

theorem variableX : EquationAxis z Polynomial.X 0 := by
  intro i
  by_cases h : i = 1
  · subst i
    simp
  · simp [Polynomial.coeff_X_of_ne_one h]

theorem add (hp : EquationAxis z p s) (hq : EquationAxis z q s) :
    EquationAxis z (p + q) s := by
  intro i
  rw [Polynomial.coeff_add]
  exact (degreeOf_add_le _ _ _).trans (max_le (hp i) (hq i))

theorem mul (hp : EquationAxis z p s) (hq : EquationAxis z q t) :
    EquationAxis z (p * q) (s + t) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ =>
    (degreeOf_mul_le _ _ _).trans (Nat.add_le_add (hp k.1) (hq k.2)))

theorem nat_add_one (i : ℕ) : (↑i + 1 : Seeds) =
    MvPolynomial.C ((i : FX) + 1) := by
  simp only [map_add, map_one, map_natCast]

theorem derivative (hq : EquationAxis z q s) : EquationAxis z q.derivative s := by
  intro i
  rw [Polynomial.coeff_derivative, nat_add_one]
  exact (degreeOf_mul_le _ _ _).trans (by
    simpa only [MvPolynomial.degreeOf_C, Nat.add_zero] using hq (i+1))

theorem coeffDiff (hq : EquationAxis z q s) :
    EquationAxis z (coefficientDerivative q) s := by
  intro i
  apply degreeOf_le_iff.mpr
  intro m hm
  apply degreeOf_le_iff.mp (hq i) m
  rw [MvPolynomial.mem_support_iff, coeff_coeffDiff] at hm
  rw [MvPolynomial.mem_support_iff]
  intro hz
  simp [hz] at hm

theorem reflect (hq : EquationAxis z q s) (n : ℕ) : EquationAxis z (q.reflect n) s := by
  intro i
  rw [Polynomial.coeff_reflect]
  exact hq _

end EquationAxis

namespace JetAxis

variable {z : Fin 2} {p q : JetRing} {s t : ℕ}

theorem mono (hp : JetAxis z p s) (h : s ≤ t) : JetAxis z p t :=
  fun i j => (hp i j).trans h

theorem C {q : Equation} (hq : EquationAxis z q s) :
    JetAxis z (Polynomial.C q) s := by
  intro i
  cases i with
  | zero => simpa using hq
  | succ i => simpa using (EquationAxis.zero : EquationAxis z 0 s)

theorem scalar (c : FX) : JetAxis z (algebraMap FX JetRing c) 0 :=
  C (EquationAxis.scalar c)

theorem nat (n : ℕ) : JetAxis z (n : JetRing) 0 := by
  rw [← map_natCast (algebraMap FX JetRing)]
  exact scalar _

theorem one : JetAxis z 1 0 := by simpa only [Nat.cast_one] using (nat (z := z) 1)

theorem ordinate : JetAxis z ordinate 0 := C EquationAxis.variableX

theorem velocity : JetAxis z velocity 0 := by
  intro i
  by_cases h : i = 1
  · subst i
    simpa using (EquationAxis.scalar (z := z) 1)
  · rw [Polynomial.coeff_X_of_ne_one h]
    exact EquationAxis.zero

theorem add (hp : JetAxis z p s) (hq : JetAxis z q s) : JetAxis z (p + q) s := by
  intro i
  rw [Polynomial.coeff_add]
  exact (hp i).add (hq i)

theorem mul (hp : JetAxis z p s) (hq : JetAxis z q t) : JetAxis z (p * q) (s + t) := by
  intro i j
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  exact (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ =>
    (hp k.1).mul (hq k.2) j)

theorem neg (hp : JetAxis z p s) : JetAxis z (-p) s := by
  simpa only [map_neg,map_one,neg_one_mul,Nat.zero_add] using (scalar (-1 : FX)).mul hp

theorem sub (hp : JetAxis z p s) (hq : JetAxis z q s) : JetAxis z (p - q) s := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

theorem pow (hp : JetAxis z p s) (n : ℕ) : JetAxis z (p ^ n) (n*s) := by
  induction n with
  | zero => simpa using (one : JetAxis z 1 0)
  | succ n ih => simpa [pow_succ, Nat.succ_mul, Nat.add_comm] using ih.mul hp

theorem derivative (hp : JetAxis z p s) : JetAxis z p.derivative s := by
  intro i
  rw [Polynomial.coeff_derivative]
  rw [← map_natCast (Polynomial.C : Seeds →+* Equation), ← map_natCast (MvPolynomial.C : FX →+* Seeds)]
  simpa only [Nat.add_zero,map_add,map_one] using (hp (i+1)).mul (EquationAxis.scalar (i+1))

theorem coeffDiff (hp : JetAxis z p s) {δ : Equation → Equation} (h0 : δ 0 = 0)
    (hδ : ∀ q, EquationAxis z q s → EquationAxis z (δ q) s) :
    JetAxis z (jetCoeffDerivative δ p) s := by
  intro i
  rw [coeff_lift h0]
  exact hδ _ (hp i)

end JetAxis

variable {z : Fin 2} {f : Equation} {s : ℕ}

theorem separant_axis (hf : EquationAxis z f s) : JetAxis z (jetSeparant f) s :=
  JetAxis.C hf.derivative

theorem second_axis (hf : EquationAxis z f s) :
    JetAxis z (secondAlongVelocity f) s := by
  have h1 := JetAxis.C hf.coeffDiff.coeffDiff
  have h2 := ((JetAxis.nat (z := z) 2).mul JetAxis.velocity).mul (JetAxis.C hf.derivative.coeffDiff)
  have h3 := (JetAxis.velocity.pow 2).mul (JetAxis.C hf.derivative.derivative)
  exact (h1.add (by simpa using h2)).add (by simpa using h3)

theorem along_axis (hf : EquationAxis z f s) : JetAxis z (sepAlong f) s := by
  exact (JetAxis.C hf.derivative.coeffDiff).add
    (by simpa using (JetAxis.velocity (z := z)).mul (JetAxis.C hf.derivative.derivative))

theorem action_axis (hf : EquationAxis z f s) {p : JetRing} {t : ℕ}
    (hp : JetAxis z p t) : JetAxis z (clearedAction f p) (s+t) := by
  have hx := hp.coeffDiff coefficientDerivative_zero (fun _ h => h.coeffDiff)
  have hy := hp.coeffDiff Polynomial.derivative_zero (fun _ h => h.derivative)
  have hs := hx.add (by simpa using (JetAxis.velocity (z := z)).mul hy)
  exact ((separant_axis hf).mul hs).sub ((second_axis hf).mul hp.derivative)

theorem velocity_axis (hf : EquationAxis z f s) (k : ℕ) :
    JetAxis z (velocityNumerator f k) (k*s) := by
  induction k with
  | zero => simpa [velocityNumerator] using (JetAxis.velocity (z := z))
  | succ k ih =>
    have h1 := action_axis hf ih
    have h2 := ((JetAxis.nat (z := z) k).mul (along_axis hf)).mul ih
    change JetAxis z (clearedAction f (velocityNumerator f k) -
      (k : JetRing) * sepAlong f * velocityNumerator f k) _
    simpa [Nat.succ_mul, Nat.add_comm] using h1.sub (by simpa using h2)

theorem reciprocal_axis (hf : EquationAxis z f s) (k : ℕ) :
    JetAxis z (reciprocalNumerator f k) (k*s) := by
  induction k with
  | zero => simpa [reciprocalNumerator] using (JetAxis.velocity (z := z)).neg
  | succ k ih =>
    have h1 := action_axis hf ih
    have h2 := ((JetAxis.nat (z := z) k).mul (along_axis hf)).mul ih
    have h3 := (((JetAxis.nat (z := z) (k+2)).mul (separant_axis hf)).mul JetAxis.velocity).mul ih
    have hleft := (JetAxis.ordinate (z := z)).mul (h1.sub (by simpa only [Nat.zero_add] using h2))
    rw [reciprocalNumerator, Nat.succ_mul, Nat.add_comm (k*s)]
    apply JetAxis.sub
    · simpa only [Nat.zero_add] using hleft
    · simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_add] using h3

theorem pureDen_axis (J : Input) (hf : EquationAxis z J.f s) (r : ℕ) :
    JetAxis z (pureDen J r) ((r-1)*s) :=
  (separant_axis hf).pow _

theorem pureOrdinate_axis (J : Input) (hf : EquationAxis z J.f s) {r i : ℕ} (hi : i ≤ r) :
    JetAxis z (pureOrdinate J r i) (r*s) := by
  have hr := Nat.mul_le_mul_right s (Nat.sub_le r 1)
  cases i with
  | zero =>
    exact (by simpa [pureOrdinate] using (pureDen_axis J hf r).mul JetAxis.ordinate :
      JetAxis z (pureOrdinate J r 0) ((r-1)*s)).mono hr
  | succ k =>
    have ht : (r-1-k)*s + k*s = (r-1)*s := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
    have hu := ((separant_axis hf).pow (r-1-k)).mul (velocity_axis hf k)
    rw [ht] at hu
    have hv := (JetAxis.scalar (z := z) (((k+1).factorial : FX)⁻¹)).mul hu
    exact (by simpa [pureOrdinate] using hv : JetAxis z (pureOrdinate J r (k+1)) ((r-1)*s)).mono hr

theorem inverseOrdinate_axis (J : Input) (hf : EquationAxis z J.f s) {r k : ℕ} (hk : k+1 ≤ r) :
    JetAxis z (inverseOrdinate J r k) (r*s) := by
  have hrev : EquationAxis z (reverseEquation J) s := hf.reflect J.e
  have ht : (r-1-k)*s + k*s = (r-1)*s := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : k ≤ r-1)]
  have hu := ((separant_axis hrev).pow (r-1-k)).mul (reciprocal_axis hrev k)
  rw [ht] at hu
  have hv := ((JetAxis.ordinate (z := z)).pow (J.e-2+(r-1-k))).mul hu
  have hw := (JetAxis.scalar (z := z) ((-1 : FX)^(r-1) * (((k+1).factorial : FX)⁻¹))).mul hv
  exact (by simpa [inverseOrdinate] using hw : JetAxis z (inverseOrdinate J r k) ((r-1)*s)).mono
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

end
end KoalaRectTaylor

