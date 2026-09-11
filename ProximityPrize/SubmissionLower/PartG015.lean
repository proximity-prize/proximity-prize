import ProximityPrize.SubmissionLower.PartG014


section Compact_SecondJetSupport
/-! Support bounds for the explicit second-jet kernel family. Variables are
ordered epsilon, S, A, R, Z, matching two successive `finSuccEquiv`s. -/
namespace ProximityPrize.SubmissionLower.SecondJetSupport
open scoped BigOperators Pointwise
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]
abbrev Poly := MvPolynomial (Fin 5) K

def Box (lo a r s t : ℕ) (P : Poly (K := K)) : Prop :=
  ∀ d ∈ P.support, lo ≤ d 0 ∧ d 2 ≤ a ∧ d 3 ≤ r ∧ d 1 ≤ s ∧
    d 1+d 2+d 3+d 4 ≤ t

theorem Box.mono {lo a r s t lo' a' r' s' t' : ℕ} {P : Poly (K := K)}
    (h : Box lo a r s t P) (hl : lo' ≤ lo) (ha : a ≤ a')
    (hr : r ≤ r') (hs : s ≤ s') (ht : t ≤ t') : Box lo' a' r' s' t' P := by
  intro d hd
  obtain ⟨h0,h2,h3,h1,h4⟩ := h d hd
  exact ⟨hl.trans h0,h2.trans ha,h3.trans hr,h1.trans hs,h4.trans ht⟩

theorem Box.mul {lo a r s t lo' a' r' s' t' : ℕ} {P Q : Poly (K := K)}
    (hP : Box lo a r s t P) (hQ : Box lo' a' r' s' t' Q) :
    Box (lo+lo') (a+a') (r+r') (s+s') (t+t') (P*Q) := by
  intro d hd
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  obtain ⟨hu0,hu2,hu3,hu1,hu4⟩ := hP u hu
  obtain ⟨hv0,hv2,hv3,hv1,hv4⟩ := hQ v hv
  simp only [Finsupp.add_apply]
  omega

theorem Box.add {lo a r s t : ℕ} {P Q : Poly (K := K)}
    (hP : Box lo a r s t P) (hQ : Box lo a r s t Q) : Box lo a r s t (P+Q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h
  · exact hQ d h

theorem Box.neg {lo a r s t : ℕ} {P : Poly (K := K)}
    (hP : Box lo a r s t P) : Box lo a r s t (-P) := by
  simpa only [Box, MvPolynomial.support_neg] using hP

theorem box_one : Box 0 0 0 0 0 (1 : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_one, Finset.mem_singleton] at hd
  subst d
  simp

theorem Box.pow {lo a r s t : ℕ} {P : Poly (K := K)}
    (hP : Box lo a r s t P) (n : ℕ) : Box (n*lo) (n*a) (n*r) (n*s) (n*t) (P^n) := by
  induction n with
  | zero => simpa using (box_one (K := K))
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

theorem box_X (j : Fin 5) :
    Box (if j=0 then 1 else 0) (if j=2 then 1 else 0)
      (if j=3 then 1 else 0) (if j=1 then 1 else 0)
      (if j=0 then 0 else 1) (MvPolynomial.X j : Poly (K := K)) := by
  intro d hd
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases j <;> norm_num [Finsupp.single_apply, Fin.ext_iff]

def vector (r h a b i j z : ℕ) : Poly (K := K) :=
  MvPolynomial.X 0^r * MvPolynomial.X 1^h *
    (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1)^a *
    (MvPolynomial.X 2-MvPolynomial.X 3)^b *
    MvPolynomial.X 2^i * MvPolynomial.X 3^j * MvPolynomial.X 4^z

theorem vector_box (r h a b i j z : ℕ) :
    Box r (i+a+b) (j+a+b) (h+a) (i+j+h+a+b+z) (vector (K := K) r h a b i j z) := by
  have hE : Box 1 0 0 0 0 (MvPolynomial.X 0 : Poly (K := K)) := by simpa using box_X (K := K) 0
  have hS : Box 0 0 0 1 1 (MvPolynomial.X 1 : Poly (K := K)) := by simpa using box_X (K := K) 1
  have hA : Box 0 1 0 0 1 (MvPolynomial.X 2 : Poly (K := K)) := by simpa using box_X (K := K) 2
  have hR : Box 0 0 1 0 1 (MvPolynomial.X 3 : Poly (K := K)) := by simpa using box_X (K := K) 3
  have hZ : Box 0 0 0 0 1 (MvPolynomial.X 4 : Poly (K := K)) := by simpa using box_X (K := K) 4
  have hV : Box 0 1 1 0 1 (MvPolynomial.X 2-MvPolynomial.X 3 : Poly (K := K)) := by
    rw [sub_eq_add_neg]
    exact (hA.mono (by omega) (by omega) (by omega) (by omega) (by omega)).add
      (hR.neg.mono (by omega) (by omega) (by omega) (by omega) (by omega))
  have hU : Box 0 1 1 1 1
      (MvPolynomial.X 2-MvPolynomial.X 3+MvPolynomial.X 0*MvPolynomial.X 1 : Poly (K := K)) :=
    (hV.mono (by omega) (by omega) (by omega) (by omega) (by omega)).add
      ((hE.mul hS).mono (by omega) (by omega) (by omega) (by omega) (by omega))
  have hh := ((((((hE.pow r).mul (hS.pow h)).mul (hU.pow a)).mul (hV.pow b)).mul
    (hA.pow i)).mul (hR.pow j)).mul (hZ.pow z)
  simpa [vector, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh


def flatEquiv : Poly (K := K) ≃ₐ[K] SecondJetBasis.Jet (MvPolynomial (Fin 3) K) :=
  (MvPolynomial.finSuccEquiv K 4).trans (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv K 3))

theorem flatEquiv_X (j : Fin 5) :
    flatEquiv (K := K) (MvPolynomial.X j) =
      ![Polynomial.X, Polynomial.C Polynomial.X,
        Polynomial.C (Polynomial.C (MvPolynomial.X 0)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 1)),
        Polynomial.C (Polynomial.C (MvPolynomial.X 2))] j := by
  have h0 : flatEquiv (K := K) (MvPolynomial.X 0) = Polynomial.X := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0)) = _
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
  have hs (i : Fin 4) : flatEquiv (K := K) (MvPolynomial.X i.succ) =
      Polynomial.C ((MvPolynomial.finSuccEquiv K 3) (MvPolynomial.X i)) := by
    change Polynomial.map _ ((MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X i.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    rfl
  fin_cases j
  · exact h0
  · change flatEquiv (K := K) (MvPolynomial.X (0 : Fin 4).succ) = Polynomial.C Polynomial.X
    rw [hs, MvPolynomial.finSuccEquiv_X_zero]
  · change flatEquiv (K := K) (MvPolynomial.X ((0 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((1 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl
  · change flatEquiv (K := K) (MvPolynomial.X ((2 : Fin 3).succ).succ) = _
    rw [hs, MvPolynomial.finSuccEquiv_X_succ]
    rfl

theorem flatEquiv_vector (r h a b i j z : ℕ) :
    flatEquiv (K := K) (vector (K := K) r h a b i j z) =
      SecondJetBasis.term (K := K) (MvPolynomial.X 0-MvPolynomial.X 1) r h a b
        (MvPolynomial.X 0^i*MvPolynomial.X 1^j*MvPolynomial.X 2^z) := by
  simp only [vector, map_mul, map_pow, map_add, map_sub, flatEquiv_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four,
    SecondJetBasis.term_apply, SecondJetBasis.factor]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  ring

theorem flatEquiv_coeff (P : Poly (K := K)) (r h : ℕ) (d : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff d (((flatEquiv (K := K) P).coeff r).coeff h) =
      MvPolynomial.coeff ((d.cons h).cons r) P := by
  simp only [flatEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv, Polynomial.coeff_map]
  change MvPolynomial.coeff d (((MvPolynomial.finSuccEquiv K 3)
    (((MvPolynomial.finSuccEquiv K 4) P).coeff r)).coeff h) = _
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.finSuccEquiv_coeff_coeff]


def truncFlat (m : ℕ) : Poly (K := K) →ₗ[K] Poly (K := K) :=
  (flatEquiv (K := K)).symm.toLinearMap.comp
    ((SecondJetBasis.truncateOuter (K := K) m).comp (flatEquiv (K := K)).toLinearMap)

theorem flatEquiv_truncFlat (m : ℕ) (P : Poly (K := K)) :
    flatEquiv (K := K) (truncFlat (K := K) m P) =
      SecondJetBasis.truncateOuter (K := K) m (flatEquiv (K := K) P) := by
  simp [truncFlat]

theorem coeff_truncFlat_cons (m r h : ℕ) (d : Fin 3 →₀ ℕ) (P : Poly (K := K)) :
    MvPolynomial.coeff ((d.cons h).cons r) (truncFlat (K := K) m P) =
      if r < m then MvPolynomial.coeff ((d.cons h).cons r) P else 0 := by
  rw [← flatEquiv_coeff, flatEquiv_truncFlat]
  by_cases hr : r < m
  · rw [if_pos hr, SecondJetBasis.truncateOuter_coeff m _ r hr, flatEquiv_coeff]
  · rw [if_neg hr, SecondJetBasis.truncateOuter_coeff_high m _ r (by omega)]
    simp

theorem support_truncFlat (m : ℕ) (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (truncFlat (K := K) m P).support) : d 0 < m ∧ d ∈ P.support := by
  have heq : ((d.tail.tail).cons (d.tail 0)).cons (d 0) = d := by
    rw [Finsupp.cons_tail, Finsupp.cons_tail]
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [← heq, coeff_truncFlat_cons] at hne
  split_ifs at hne with h
  · refine ⟨h, MvPolynomial.mem_support_iff.mpr ?_⟩
    simpa only [heq] using hne
  · exact False.elim (hne rfl)

def Allowed (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) : Prop :=
  d 0 < m ∧ d 2 ≤ d 0 ∧ d 3 ≤ s1 ∧ d 1 ≤ s2 ∧ d 1+d 2+d 3+d 4 ≤ L

theorem vector_allowed (m L s1 s2 r h a b i j z : ℕ)
    (hi : i+a+b ≤ r) (hj : j+a+b ≤ s1) (hh : h+a ≤ s2)
    (hL : i+j+h+a+b+z ≤ L) :
    ∀ d ∈ (truncFlat (K := K) m (vector (K := K) r h a b i j z)).support,
      Allowed m L s1 s2 d := by
  intro d hd
  obtain ⟨htr,hmem⟩ := support_truncFlat m _ d hd
  obtain ⟨h0,h2,h3,h1,h4⟩ := vector_box (K := K) r h a b i j z d hmem
  exact ⟨htr, h2.trans (hi.trans h0), h3.trans hj, h1.trans hh, h4.trans hL⟩

end
end ProximityPrize.SubmissionLower.SecondJetSupport

end Compact_SecondJetSupport
