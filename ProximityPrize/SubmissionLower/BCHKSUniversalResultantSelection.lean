import ProximityPrize.SubmissionLower.BCHKSResultantDegree
import ProximityPrize.SubmissionLower.BCHKSConcreteNumerators

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

/-- Monicity is unnecessary for resultant descent: irreducibility and positive
`Y`-degree make the right polynomial primitive over `F[Z]`. -/
theorem irreducible_dvd_of_resultant_eq_zero_nonmonic
    (B H : F[X][Y]) (hHirreducible : Irreducible H)
    (hHpos : 0 < H.natDegree)
    (hres : Polynomial.resultant B H = 0) : H ∣ B := by
  classical
  let K := FractionRing F[X]
  let f : F[X] →+* K := algebraMap F[X] K
  have hf : Function.Injective f := IsFractionRing.injective F[X] K
  have hBdeg : (B.map f).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf B
  have hHdeg : (H.map f).natDegree = H.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf H
  have hresFixed :
      Polynomial.resultant (B.map f) (H.map f) B.natDegree H.natDegree = 0 := by
    rw [Polynomial.resultant_map_map, hres]
    exact map_zero f
  have hresK : Polynomial.resultant (B.map f) (H.map f) = 0 := by
    simpa only [hBdeg, hHdeg] using hresFixed
  have hnotCoprime : ¬ IsCoprime (B.map f) (H.map f) :=
    (Polynomial.resultant_eq_zero_iff.mp hresK).2
  have hprimitive : H.IsPrimitive :=
    hHirreducible.isPrimitive (ne_of_gt hHpos)
  have hHirreducibleK : Irreducible (H.map f) := by
    exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hHirreducible
  have hdvdK : H.map f ∣ B.map f :=
    (Irreducible.dvd_iff_not_isCoprime hHirreducibleK).2 fun hc =>
      hnotCoprime hc.symm
  exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdvdK

/-- Root-counting wrapper without a monicity assumption on the irreducible
factor. Fixed-degree padding handles degree drops after specialization. -/
theorem irreducible_dvd_of_many_bivariate_common_roots_nonmonic
    (B H : F[X][Y]) (n m : ℕ) (S : Finset F) (t : F → F)
    (hBY : B.natDegree = n) (hHY : H.natDegree = m)
    (hHirreducible : Irreducible H) (hHpos : 0 < H.natDegree)
    (hmany : m * degreeX B + n * degreeX H < S.card)
    (hroots : ∀ z ∈ S,
      (B.map (Polynomial.evalRingHom z)).eval (t z) = 0 ∧
      (H.map (Polynomial.evalRingHom z)).eval (t z) = 0) :
    H ∣ B := by
  let R : F[X] := Polynomial.resultant B H n m
  have hsize : 0 < n + m := by
    rw [← hBY, ← hHY]
    exact Nat.add_pos_right _ hHpos
  have hReval : ∀ z ∈ S, R.eval z = 0 := by
    intro z hz
    exact bivariate_resultant_eval_eq_zero_of_common_root B H n m z (t z)
      (Polynomial.natDegree_map_le.trans hBY.le)
      (Polynomial.natDegree_map_le.trans hHY.le) hsize
      (hroots z hz).1 (hroots z hz).2
  have hRdeg : R.natDegree ≤ m * degreeX B + n * degreeX H :=
    bivariate_resultant_natDegree_le B H n m
  have hRzero : R = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R S hReval
      (hRdeg.trans_lt hmany)
  apply irreducible_dvd_of_resultant_eq_zero_nonmonic B H hHirreducible hHpos
  simpa only [R, hBY, hHY] using hRzero

/-- The generic function-field coordinate `T/W` is a root of `H`. -/
theorem eval₂_lift_initialValue_self_eq_zero
    (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) H = 0 := by
  let d := H.natDegree
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  have hd : 0 < d := Fact.out
  have hW : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hdeg : H.natDegree ≤ (d - 1) + 1 := by
    simp [d, Nat.sub_add_cancel hd]
  have hscale := leadingCoeff_pow_mul_eval₂_div_eq_sum
    (H := H) (P := H) (k := d - 1) hdeg
  have hmono : liftBivariate (H := H) (monicize H) = 0 := by
    unfold liftBivariate
    change Ideal.Quotient.mk (Ideal.span {monicizeRatFunc H})
        ((monicize H).map ToRatFunc.univPolyHom) = 0
    rw [map_monicize_eq_monicizeRatFunc]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  have hrhs :
      (∑ i ∈ Finset.range ((d - 1) + 1),
          liftToFunctionField (H := H) (H.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (d - 1 - i))) +
        (liftToFunctionField (H := H) (H.coeff ((d - 1) + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ ((d - 1) + 1) =
        liftBivariate (H := H) (monicize H) := by
    rw [show (d - 1) + 1 = d by omega]
    unfold monicize
    rw [if_neg (Nat.ne_of_gt hd)]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C,
      liftBivariate_X, Polynomial.coeff_natDegree]
    change (∑ i ∈ Finset.range d,
        liftToFunctionField (H := H) (H.coeff i) *
          (functionFieldT (H := H) ^ i * W ^ (d - 1 - i))) +
      liftToFunctionField (H := H) (H.coeff d) / W *
          functionFieldT (H := H) ^ d = _
    rw [show H.coeff d = H.leadingCoeff by simp [d], show
      liftToFunctionField (H := H) H.leadingCoeff = W by rfl, div_self hW]
    have hsum :
        (∑ i ∈ Finset.range d,
          liftToFunctionField (H := H) (H.coeff i) *
            (functionFieldT (H := H) ^ i * W ^ (d - 1 - i))) =
        (∑ i ∈ Finset.range H.natDegree,
          liftToFunctionField (H := H) (H.coeff i) *
            W ^ (H.natDegree - 1 - i) * functionFieldT (H := H) ^ i) := by
      apply Finset.sum_congr (by simp [d])
      intro i hi
      dsimp [d]
      ring
    rw [hsum]
    ring
  rw [initialValue]
  change Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) /
        liftToFunctionField (H := H) H.leadingCoeff) H = 0
  have hs : W ^ (d - 1) *
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (functionFieldT (H := H) /
          liftToFunctionField (H := H) H.leadingCoeff) H = 0 := by
    rw [hscale, hrhs, hmono]
  exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ hW)

/-- Any multiple of `H` vanishes at the generic function-field root. -/
theorem eval₂_lift_initialValue_eq_zero_of_dvd
    (B H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hdiv : H ∣ B) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) B = 0 := by
  obtain ⟨C, rfl⟩ := hdiv
  rw [Polynomial.eval₂_mul, eval₂_lift_initialValue_self_eq_zero H, zero_mul]

end ProximityPrize.SubmissionLower
