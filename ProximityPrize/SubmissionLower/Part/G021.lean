import ProximityPrize.SubmissionLower.Part.G020


section Compact_SecondJetGlobalSupport
/-! Global-to-local substitution preserving the shared derivative cap.
Global variables are X, S, Y, R, Z; local variables epsilon, S, A, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalSupport
open scoped BigOperators Pointwise
open MvPolynomial SecondJetSupport SecondJetBasis
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def LocalBound (B s L : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, d 2 ≤ d 0 ∧ d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3+d 4 ≤ L

theorem LocalBound.mono {B s L B' s' L' : ℕ} {P : Poly (K := K)}
    (h : LocalBound B s L P) (hB : B ≤ B') (hs : s ≤ s') (hL : L ≤ L') :
    LocalBound B' s' L' P := by
  intro d hd
  have hh := h d hd
  exact ⟨hh.1,hh.2.1.trans hB,hh.2.2.1.trans hs,hh.2.2.2.trans hL⟩

theorem LocalBound.mul {B s L B' s' L' : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B' s' L' Q) :
    LocalBound (B+B') (s+s') (L+L') (P*Q) := by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  have hp := hP u hu
  have hq := hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem LocalBound.add {B s L : ℕ} {P Q : Poly (K := K)}
    (hP : LocalBound B s L P) (hQ : LocalBound B s L Q) : LocalBound B s L (P+Q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem local_C (c : K) : LocalBound 0 0 0 (MvPolynomial.C c : Poly (K := K)) := by
  intro d hd
  have hd0 : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_C_subset hd)
  subst d
  simp

theorem LocalBound.pow {B s L : ℕ} {P : Poly (K := K)}
    (hP : LocalBound B s L P) (n : ℕ) : LocalBound (n*B) (n*s) (n*L) (P^n) := by
  induction n with
  | zero => simpa using (local_C (K := K) 1)
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

def localize (x u0 u1 : K) : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4+
      MvPolynomial.X 0*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem local_X (j : Fin 5) (hj : j ≠ 2) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (MvPolynomial.X j : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> norm_num [Finsupp.single_apply, Fin.ext_iff] at *

theorem local_epsilon_A : LocalBound 0 0 1
    (MvPolynomial.X 0*MvPolynomial.X 2 : Poly (K := K)) := by
  intro d hd
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul] at hd
  have hd' := MvPolynomial.support_monomial_subset hd
  have hd0 := Finset.mem_singleton.mp hd'
  subst d
  norm_num [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff]

theorem localize_X (x u0 u1 : K) (j : Fin 5) :
    LocalBound (if j=1 ∨ j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (localize x u0 u1 (MvPolynomial.X j)) := by
  have hE : LocalBound 0 0 0 (MvPolynomial.X 0 : Poly (K := K)) := by
    simpa using local_X (K := K) 0 (by decide)
  have hZ : LocalBound 0 0 1 (MvPolynomial.X 4 : Poly (K := K)) := by
    simpa using local_X (K := K) 4 (by decide)
  fin_cases j
  · simpa [localize] using (local_C x).add hE
  · simpa [localize] using local_X (K := K) 1 (by decide)
  · have hU : LocalBound 0 0 1 (MvPolynomial.C u0+MvPolynomial.C u1*MvPolynomial.X 4 : Poly (K := K)) :=
      ((local_C u0).mono (by omega) (by omega) (by omega)).add
        ((local_C u1).mul hZ)
    simpa [localize] using hU.add (local_epsilon_A (K := K))
  · simpa [localize] using local_X (K := K) 3 (by decide)
  · simpa [localize] using hZ

theorem localize_monomial (x u0 u1 : K) (d : Fin 5 →₀ ℕ) (c : K) :
    LocalBound (d 1+d 3) (d 1) (d 1+d 2+d 3+d 4)
      (localize x u0 u1 (MvPolynomial.monomial d c)) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow,
      map_C]
    have h0 := (localize_X x u0 u1 0).pow (d 0)
    have h1 := (localize_X x u0 u1 1).pow (d 1)
    have h2 := (localize_X x u0 u1 2).pow (d 2)
    have h3 := (localize_X x u0 u1 3).pow (d 3)
    have h4 := (localize_X x u0 u1 4).pow (d 4)
    simpa [Nat.add_assoc] using (local_C c).mul (h0.mul (h1.mul (h2.mul (h3.mul h4))))
  · intro i
    simp

theorem truncated_local_monomial_mem (x u0 u1 : K) (m L B s : ℕ)
    (d : Fin 5 →₀ ℕ) (c : K) (hB : d 1+d 3 ≤ B) (hs : d 1 ≤ s)
    (hL : d 1+d 2+d 3+d 4 ≤ L) :
    truncateOuter (K := K) m (flatEquiv (K := K)
      (localize x u0 u1 (MvPolynomial.monomial d c))) ∈
        SecondJetFacetSpace.source (K := K) m L B s := by
  rw [← flatEquiv_truncFlat, SecondJetFacetSpace.mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro e he
  obtain ⟨hm,he'⟩ := support_truncFlat m _ e he
  have hh := ((localize_monomial x u0 u1 d c).mono hB hs hL) e he'
  exact ⟨⟨hm,hh.1,by omega,hh.2.2.1,hh.2.2.2⟩,hh.2.1⟩

end
end ProximityPrize.SubmissionLower.SecondJetGlobalSupport

end Compact_SecondJetGlobalSupport
