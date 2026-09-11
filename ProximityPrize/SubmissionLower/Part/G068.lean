import ProximityPrize.SubmissionLower.Part.G067


section Compact_SecondJetWeightedSupport
/-! Signed linear support bounds for the weighted second-jet kernel family. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def weight (w : Fin 5 → ℤ) (e : Fin 5 →₀ ℕ) : ℤ := ∑ j, (e j : ℤ)*w j

def LinearBound (w : Fin 5 → ℤ) (b : ℤ) (P : Poly (K := K)) : Prop :=
  ∀ e ∈ P.support, weight w e ≤ b

theorem weight_add (w : Fin 5 → ℤ) (e f : Fin 5 →₀ ℕ) :
    weight w (e+f) = weight w e+weight w f := by
  simp [weight, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem LinearBound.mono {w : Fin 5 → ℤ} {b c : ℤ} {P : Poly (K := K)}
    (h : LinearBound w b P) (hbc : b ≤ c) : LinearBound w c P :=
  fun e he => (h e he).trans hbc

theorem LinearBound.mul {w : Fin 5 → ℤ} {b c : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w c Q) : LinearBound w (b+c) (P*Q) := by
  intro e he
  obtain ⟨f,hf,g,hg,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  rw [weight_add]
  exact add_le_add (hP f hf) (hQ g hg)

theorem LinearBound.add {w : Fin 5 → ℤ} {b : ℤ} {P Q : Poly (K := K)}
    (hP : LinearBound w b P) (hQ : LinearBound w b Q) : LinearBound w b (P+Q) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hP e h
  · exact hQ e h

theorem LinearBound.neg {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) : LinearBound w b (-P) := by
  simpa only [LinearBound, MvPolynomial.support_neg] using hP

theorem linear_one (w : Fin 5 → ℤ) : LinearBound w 0 (1 : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_one, Finset.mem_singleton] at he
  subst e
  simp [weight]

theorem LinearBound.pow {w : Fin 5 → ℤ} {b : ℤ} {P : Poly (K := K)}
    (hP : LinearBound w b P) (n : ℕ) : LinearBound w ((n : ℤ)*b) (P^n) := by
  induction n with
  | zero => simpa using linear_one (K := K) w
  | succ n ih => simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hP

theorem linear_X (w : Fin 5 → ℤ) (j : Fin 5) :
    LinearBound w (w j) (MvPolynomial.X j : Poly (K := K)) := by
  intro e he
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at he
  subst e
  simp [weight, Finsupp.single_apply]

def weightedVector (r h a b i j z l : ℕ) : Poly (K := K) :=
  MvPolynomial.X 0^r * MvPolynomial.X 1^h *
    (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1)^(a-l) *
    (MvPolynomial.X 3*(MvPolynomial.X 2-MvPolynomial.X 3)+
      MvPolynomial.X 0*MvPolynomial.X 2*MvPolynomial.X 1)^l *
    (MvPolynomial.X 2-MvPolynomial.X 3)^b *
    MvPolynomial.X 2^i * MvPolynomial.X 3^(j-l) * MvPolynomial.X 4^z

theorem weightedVector_bound (w : Fin 5 → ℤ) (r h a b i j z l : ℕ) :
    LinearBound w ((r : ℤ)*w 0+(h : ℤ)*w 1+
      ((a-l : ℕ) : ℤ)*max (max (w 2) (w 3)) (w 0+w 1)+
      (l : ℤ)*max (w 3+max (w 2) (w 3)) (w 0+w 2+w 1)+
      (b : ℤ)*max (w 2) (w 3)+(i : ℤ)*w 2+((j-l : ℕ) : ℤ)*w 3+(z : ℤ)*w 4)
      (weightedVector (K := K) r h a b i j z l) := by
  have hE := linear_X (K := K) w 0
  have hS := linear_X (K := K) w 1
  have hA := linear_X (K := K) w 2
  have hR := linear_X (K := K) w 3
  have hZ := linear_X (K := K) w 4
  have hV : LinearBound w (max (w 2) (w 3))
      (MvPolynomial.X 2-MvPolynomial.X 3 : Poly (K := K)) := by
    rw [sub_eq_add_neg]
    exact (hA.mono (le_max_left _ _)).add (hR.neg.mono (le_max_right _ _))
  have hU := (hV.mono (le_max_left _ (w 0+w 1))).add
    ((hE.mul hS).mono (le_max_right _ _))
  have hJ := ((hR.mul hV).mono (le_max_left _ (w 0+w 2+w 1))).add
    (((hE.mul hA).mul hS).mono (le_max_right _ _))
  exact (((((((hE.pow r).mul (hS.pow h)).mul (hU.pow (a-l))).mul (hJ.pow l)).mul
    (hV.pow b)).mul (hA.pow i)).mul (hR.pow (j-l))).mul (hZ.pow z)

theorem weightedVector_support (r h a b i j z l : ℕ) (hla : l ≤ a) (hlj : l ≤ j)
    (e : Fin 5 →₀ ℕ) (he : e ∈ (weightedVector (K := K) r h a b i j z l).support) :
    r ≤ e 0 ∧ e 2 ≤ i+a+b ∧ e 3 ≤ j+a+b ∧ h ≤ e 1 ∧ e 1 ≤ h+a ∧
      e 1+e 2+e 3 ≤ i+j+h+a+b ∧ e 1+e 2+e 3+e 4 ≤ i+j+h+a+b+z ∧
      2*e 1+e 3 ≤ 2*h+2*a+b+j-l := by
  have h0 := weightedVector_bound (K := K) ![-1,0,0,0,0] r h a b i j z l e he
  have hA := weightedVector_bound (K := K) ![0,0,1,0,0] r h a b i j z l e he
  have hR := weightedVector_bound (K := K) ![0,0,0,1,0] r h a b i j z l e he
  have hSlo := weightedVector_bound (K := K) ![0,-1,0,0,0] r h a b i j z l e he
  have hShi := weightedVector_bound (K := K) ![0,1,0,0,0] r h a b i j z l e he
  have hM := weightedVector_bound (K := K) ![0,1,1,1,0] r h a b i j z l e he
  have hT := weightedVector_bound (K := K) ![0,1,1,1,1] r h a b i j z l e he
  have hB := weightedVector_bound (K := K) ![0,2,0,1,0] r h a b i j z l e he
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at h0 hA hR hSlo hShi hM hT hB
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedSupport

end Compact_SecondJetWeightedSupport
