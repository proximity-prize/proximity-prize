import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN313
open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

def atAxis (i : Fin 4) : Polynomial K →+* Carrier K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)

theorem atAxis_degree (i j : Fin 4) (P : Polynomial K) :
    (atAxis i P).degreeOf j ≤ if j=i then P.natDegree else 0 := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [map_sum]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro n hn
  change (atAxis i (Polynomial.C (P.coeff n) * Polynomial.X^n)).degreeOf j ≤ _
  have coeff : atAxis i (Polynomial.C (P.coeff n)) = MvPolynomial.C (P.coeff n) :=
    Polynomial.eval₂_C _ _
  have axis : atAxis i (Polynomial.X : Polynomial K) = MvPolynomial.X i :=
    Polynomial.eval₂_X (MvPolynomial.C : K →+* Carrier K) (MvPolynomial.X i)
  rw [map_mul, map_pow, coeff, axis]
  have hm := MvPolynomial.degreeOf_C_mul_le ((MvPolynomial.X i : Carrier K) ^ n) j (P.coeff n)
  refine hm.trans ((MvPolynomial.degreeOf_pow_le j (MvPolynomial.X i) n).trans ?_)
  rw [MvPolynomial.degreeOf_X]
  split_ifs with he
  · simpa using Polynomial.le_natDegree_of_mem_supp n hn
  · simp

theorem graphSpecialize_atAxis (P Q : Polynomial K) (g h : K) (i : Fin 4) :
    graphSpecialize P g h (atAxis i Q) = Q.eval₂ Polynomial.C (![Polynomial.X,P,Polynomial.C g,Polynomial.C h] i) := by
  induction Q using Polynomial.induction_on' with
  | add A B hA hB =>
    simp only [map_add, hA, hB, Polynomial.eval₂_add]
  | monomial n a =>
    simp [atAxis, Polynomial.eval₂_monomial, graphSpecialize]

def axesProduct (A B C : Polynomial K) : Carrier K :=
  atAxis 0 A * atAxis 2 B * atAxis 3 C

theorem axesProduct_degree (A B C : Polynomial K) (i : Fin 4) :
    (axesProduct A B C).degreeOf i ≤ ![A.natDegree,0,B.natDegree,C.natDegree] i := by
  have h := degree_mul_bound i (degree_mul_bound i (atAxis_degree 0 i A) (atAxis_degree 2 i B))
    (atAxis_degree 3 i C)
  fin_cases i <;> simpa [axesProduct] using h

theorem graphSpecialize_axesProduct (P A B C : Polynomial K) (g h : K) :
    graphSpecialize P g h (axesProduct A B C) = Polynomial.C (B.eval g * C.eval h) * A := by
  simp only [axesProduct, map_mul, graphSpecialize_atAxis, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.cons_val_three, Polynomial.eval₂_C_X]
  have hB : B.eval₂ Polynomial.C (Polynomial.C g) = Polynomial.C (B.eval g) :=
    Polynomial.eval₂_at_apply _ _
  have hC : C.eval₂ Polynomial.C (Polynomial.C h) = Polynomial.C (C.eval h) :=
    Polynomial.eval₂_at_apply _ _
  change A * B.eval₂ Polynomial.C (Polynomial.C g) * C.eval₂ Polynomial.C (Polynomial.C h) = _
  rw [hB, hC]
  ring

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
