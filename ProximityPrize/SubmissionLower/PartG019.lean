import ProximityPrize.SubmissionLower.PartG018


section Compact_SecondJetFacetSupport
/-! A shared R/S degree bound for the second-jet kernel family. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def RSBound (b : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, d 1+d 3 ≤ b

theorem RSBound.mono {b c : ℕ} {P : Poly (K := K)}
    (h : RSBound b P) (hbc : b ≤ c) : RSBound c P :=
  fun d hd => (h d hd).trans hbc

theorem RSBound.mul {b c : ℕ} {P Q : Poly (K := K)}
    (hP : RSBound b P) (hQ : RSBound c Q) : RSBound (b+c) (P*Q) := by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP u hu
  have hq := hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem RSBound.add {b : ℕ} {P Q : Poly (K := K)}
    (hP : RSBound b P) (hQ : RSBound b Q) : RSBound b (P+Q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem RSBound.neg {b : ℕ} {P : Poly (K := K)} (hP : RSBound b P) : RSBound b (-P) := by
  simpa only [RSBound, MvPolynomial.support_neg] using hP

theorem rs_one : RSBound 0 (1 : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_one, Finset.mem_singleton] at hd
  subst d
  simp

theorem RSBound.pow {b : ℕ} {P : Poly (K := K)}
    (hP : RSBound b P) (n : ℕ) : RSBound (n*b) (P^n) := by
  induction n with
  | zero => simpa using (rs_one (K := K))
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

theorem rs_X (j : Fin 5) :
    RSBound (if j=1 ∨ j=3 then 1 else 0) (MvPolynomial.X j : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> norm_num [Finsupp.single_apply, Fin.ext_iff]

theorem vector_rs (r h a b i j z : ℕ) :
    RSBound (j+h+a+b) (vector (K := K) r h a b i j z) := by
  have hE : RSBound 0 (MvPolynomial.X 0 : Poly (K := K)) := by simpa using rs_X (K := K) 0
  have hS : RSBound 1 (MvPolynomial.X 1 : Poly (K := K)) := by simpa using rs_X (K := K) 1
  have hA : RSBound 0 (MvPolynomial.X 2 : Poly (K := K)) := by simpa using rs_X (K := K) 2
  have hR : RSBound 1 (MvPolynomial.X 3 : Poly (K := K)) := by simpa using rs_X (K := K) 3
  have hZ : RSBound 0 (MvPolynomial.X 4 : Poly (K := K)) := by simpa using rs_X (K := K) 4
  have hV : RSBound 1 (MvPolynomial.X 2-MvPolynomial.X 3 : Poly (K := K)) := by
    rw [sub_eq_add_neg]
    exact (hA.mono (by omega)).add hR.neg
  have hU : RSBound 1
      (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1 : Poly (K := K)) :=
    hV.add ((hE.mul hS).mono (by omega))
  have hh := ((((((hE.pow r).mul (hS.pow h)).mul (hU.pow a)).mul (hV.pow b)).mul
    (hA.pow i)).mul (hR.pow j)).mul (hZ.pow z)
  simpa [vector, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

theorem RSBound.truncFlat {b : ℕ} {P : Poly (K := K)} (hP : RSBound b P) (m : ℕ) :
    RSBound b (truncFlat (K := K) m P) :=
  fun d hd => hP d (support_truncFlat m P d hd).2

end
end ProximityPrize.SubmissionLower.SecondJetFacetSupport

end Compact_SecondJetFacetSupport
