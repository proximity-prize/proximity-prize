import ProximityPrize.SubmissionLower.HighCore82706Tangent

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000

namespace Rect51Tangent
noncomputable section

open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3 (JetRing ordinate)
open HighCore82706Tangent_3_1 (velocity coefficientDerivative jetCoeffDerivative)
open K1_14_6_1 (flatten partialX coeff_partialX Dx)
open MvPolynomial (degreeOf degreeOf_le_iff degreeOf_mul_le degreeOf_add_le degreeOf_sum_le degreeOf_C)
open scoped BigOperators

abbrev Axes := Fin 2 → ℕ

/-- Bound the degree of each seed independently in every ordinate coefficient. -/
def SeedBound (P : Equation) (v : Axes) : Prop :=
  ∀ k i, degreeOf i (P.coeff k) ≤ v i

namespace SeedBound
theorem mono {P : Equation} {v w : Axes} (h : SeedBound P v) (hw : ∀ i, v i ≤ w i) :
    SeedBound P w := fun k i => (h k i).trans (hw i)

theorem zero (v : Axes) : SeedBound 0 v := by intro k i; simp

theorem scalar (a : FX) : SeedBound (Polynomial.C (MvPolynomial.C a)) 0 := by
  intro k i
  by_cases hk : k = 0
  · simp [hk]
  · simp [Polynomial.coeff_C_of_ne_zero hk]

theorem add {P Q : Equation} {v : Axes} (hP : SeedBound P v) (hQ : SeedBound Q v) :
    SeedBound (P+Q) v := by
  intro k i
  rw [Polynomial.coeff_add]
  exact (degreeOf_add_le _ _ _).trans (max_le (hP k i) (hQ k i))

theorem neg {P : Equation} {v : Axes} (hP : SeedBound P v) : SeedBound (-P) v := by
  intro k i
  rw [Polynomial.coeff_neg]
  simpa using hP k i

theorem sub {P Q : Equation} {v : Axes} (hP : SeedBound P v) (hQ : SeedBound Q v) :
    SeedBound (P-Q) v := by
  intro k i
  rw [Polynomial.coeff_sub, sub_eq_add_neg]
  exact (degreeOf_add_le _ _ _).trans (max_le (hP k i) (by simpa using hQ k i))

theorem mul {P Q : Equation} {v w : Axes} (hP : SeedBound P v) (hQ : SeedBound Q w) :
    SeedBound (P*Q) (v+w) := by
  intro k i
  rw [Polynomial.coeff_mul]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  exact (degreeOf_mul_le _ _ _).trans (Nat.add_le_add (hP j.1 i) (hQ j.2 i))

theorem derivative {P : Equation} {v : Axes} (hP : SeedBound P v) :
    SeedBound P.derivative v := by
  intro k i
  rw [Polynomial.coeff_derivative]
  have he : (↑k+1 : Seeds) = MvPolynomial.C ((k : FX)+1) := by simp
  rw [he]
  exact (MvPolynomial.degreeOf_mul_C_le _ _ _).trans (hP (k+1) i)

theorem reflect {P : Equation} {v : Axes} (hP : SeedBound P v) (n : ℕ) :
    SeedBound (P.reflect n) v := by
  intro k i
  rw [Polynomial.coeff_reflect]
  exact hP _ i

theorem coeffDiff {P : Equation} {v : Axes} (hP : SeedBound P v) :
    SeedBound (coefficientDerivative P) v := by
  intro j i
  apply degreeOf_le_iff.mpr
  intro m hm
  have h := MvPolynomial.optionEquivLeft_coeff_coeff FX (partialX (flatten P)) j m
  have h' := MvPolynomial.optionEquivLeft_coeff_coeff FX (flatten P) j m
  have hn : ((P.coeff j).coeff m) ≠ 0 := by
    intro he
    rw [MvPolynomial.mem_support_iff] at hm
    apply hm
    change ((MvPolynomial.optionEquivLeft FX (Fin 2) (partialX (flatten P))).coeff j).coeff m = 0
    rw [h, coeff_partialX, ← h', AlgEquiv.apply_symm_apply, he, map_zero]
  exact degreeOf_le_iff.mp (hP j i) m (MvPolynomial.mem_support_iff.mpr hn)

theorem flatten_iff (P : Equation) (v : Axes) :
    SeedBound P v ↔ ∀ i, degreeOf (some i) (flatten P) ≤ v i := by
  constructor
  · intro h i
    apply degreeOf_le_iff.mpr
    intro m hm
    have hc := MvPolynomial.optionEquivLeft_coeff_coeff FX (flatten P) (m none) m.some
    rw [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at hc
    have hs : m.some ∈ (P.coeff (m none)).support :=
      MvPolynomial.mem_support_iff.mpr (hc ▸ MvPolynomial.mem_support_iff.mp hm)
    exact degreeOf_le_iff.mp (h (m none) i) m.some hs
  · intro h k i
    apply degreeOf_le_iff.mpr
    intro m hm
    have hc := MvPolynomial.optionEquivLeft_coeff_coeff FX (flatten P) k m
    rw [AlgEquiv.apply_symm_apply] at hc
    have hs : m.optionElim k ∈ (flatten P).support :=
      MvPolynomial.mem_support_iff.mpr (hc ▸ MvPolynomial.mem_support_iff.mp hm)
    simpa only [Finsupp.optionElim_apply_some] using degreeOf_le_iff.mp (h i) _ hs

end SeedBound

/-- A polynomial in velocity with separate coefficient bounds on its seeds. -/
def Bounded (P : JetRing) (t : ℕ) (v : Axes) : Prop :=
  P.natDegree ≤ t ∧ ∀ j, SeedBound (P.coeff j) v

namespace Bounded
theorem mono {P : JetRing} {t t' : ℕ} {v v' : Axes}
    (h : Bounded P t v) (ht : t ≤ t') (hv : ∀ i, v i ≤ v' i) : Bounded P t' v' :=
  ⟨h.1.trans ht, fun j => (h.2 j).mono hv⟩

theorem zero (t : ℕ) (v : Axes) : Bounded 0 t v := by
  refine ⟨by simp, fun j => ?_⟩
  rw [Polynomial.coeff_zero]
  exact SeedBound.zero v

theorem C {P : Equation} {v : Axes} (hP : SeedBound P v) : Bounded (Polynomial.C P) 0 v := by
  refine ⟨(Polynomial.natDegree_C _).le, fun j => ?_⟩
  by_cases hj : j = 0
  · simpa [hj] using hP
  · rw [Polynomial.coeff_C_of_ne_zero hj]
    exact SeedBound.zero v

theorem monomial {P : Equation} {v : Axes} (hP : SeedBound P v) (n : ℕ) :
    Bounded (Polynomial.monomial n P) n v := by
  refine ⟨Polynomial.natDegree_monomial_le _, fun j => ?_⟩
  by_cases hj : j = n
  · subst j
    rwa [Polynomial.coeff_monomial_same]
  · rw [Polynomial.coeff_monomial_of_ne _ hj]
    exact SeedBound.zero v

theorem scalar (x : FX) : Bounded (algebraMap FX JetRing x) 0 0 := C (SeedBound.scalar x)

theorem nat (k : ℕ) : Bounded (k : JetRing) 0 0 := by
  rw [← map_natCast (algebraMap FX JetRing)]
  exact scalar (k : FX)

theorem velocity : Bounded velocity 1 0 := by
  refine ⟨Polynomial.natDegree_X.le, fun j => ?_⟩
  by_cases hj : j = 1
  · subst j
    rw [Polynomial.coeff_X_one]
    simpa only [map_one] using SeedBound.scalar (1 : FX)
  · rw [Polynomial.coeff_X_of_ne_one hj]
    exact SeedBound.zero 0

theorem ordinate : Bounded ordinate 0 0 := by
  apply C
  intro k i
  by_cases hk : k = 1
  · simp [hk]
  · simp [Polynomial.coeff_X_of_ne_one hk]

theorem add {P Q : JetRing} {t : ℕ} {v : Axes}
    (hP : Bounded P t v) (hQ : Bounded Q t v) : Bounded (P+Q) t v := by
  refine ⟨by simpa only [max_self] using Polynomial.natDegree_add_le_of_le hP.1 hQ.1, fun j => ?_⟩
  rw [Polynomial.coeff_add]
  exact (hP.2 j).add (hQ.2 j)

theorem mul {P Q : JetRing} {t u : ℕ} {v w : Axes}
    (hP : Bounded P t v) (hQ : Bounded Q u w) : Bounded (P*Q) (t+u) (v+w) := by
  refine ⟨Polynomial.natDegree_mul_le_of_le hP.1 hQ.1, fun j k i => ?_⟩
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro a _
  exact ((hP.2 a.1).mul (hQ.2 a.2)) k i

theorem neg {P : JetRing} {t : ℕ} {v : Axes} (hP : Bounded P t v) :
    Bounded (-P) t v := by
  simpa only [map_neg, map_one, neg_one_mul, Nat.zero_add, zero_add] using
    (Bounded.scalar (-1 : FX)).mul hP

theorem sub {P Q : JetRing} {t : ℕ} {v : Axes}
    (hP : Bounded P t v) (hQ : Bounded Q t v) : Bounded (P-Q) t v := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg

theorem pow {P : JetRing} {t : ℕ} {v : Axes} (hP : Bounded P t v) (n : ℕ) :
    Bounded (P^n) (n*t) (n • v) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul, zero_nsmul, Nat.cast_one] using nat 1
  | succ n ih => simpa only [pow_succ, Nat.succ_mul, succ_nsmul] using ih.mul hP

theorem derivative {P : JetRing} {t : ℕ} {v : Axes} (hP : Bounded P t v) :
    Bounded P.derivative (t-1) v := by
  refine ⟨(Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hP.1 _), fun j => ?_⟩
  rw [Polynomial.coeff_derivative]
  rw [← map_natCast (Polynomial.C : Seeds →+* Equation), ← map_natCast (MvPolynomial.C : FX →+* Seeds)]
  simpa only [add_zero, map_add, map_one] using (hP.2 (j+1)).mul (SeedBound.scalar (j+1))

theorem coeffDiff {P : JetRing} {t : ℕ} {v : Axes} (hP : Bounded P t v)
    {δ : Equation → Equation} (h0 : δ 0 = 0) (hδ : ∀ A, SeedBound A v → SeedBound (δ A) v) :
    Bounded (jetCoeffDerivative δ P) t v := by
  have hc (k : ℕ) : (jetCoeffDerivative δ P).coeff k = δ (P.coeff k) := by
    rw [jetCoeffDerivative, Polynomial.sum_def, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · exact Polynomial.coeff_monomial_same _ _
    · exact fun j _ hj => Polynomial.coeff_monomial_of_ne _ hj.symm
    · intro hk
      rw [Polynomial.notMem_support_iff.mp hk, h0, Polynomial.monomial_zero_right, Polynomial.coeff_zero]
  refine ⟨Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_), fun k => ?_⟩
  · rw [hc, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.1.trans_lt hk), h0]
  · rw [hc]
    exact hδ _ (hP.2 k)

theorem sum {ι : Type*} {t : ℕ} {v : Axes} {s : Finset ι} {f : ι → JetRing}
    (hf : ∀ i ∈ s, Bounded (f i) t v) : Bounded (∑ i ∈ s, f i) t v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero _ _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Bounded

end
end Rect51Tangent
