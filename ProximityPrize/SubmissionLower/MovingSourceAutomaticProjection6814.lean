import ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
namespace ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN046 RCN093 RCN095 RCN116 RCN264 RCN341
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814 MovingSourcePoleBudget6814

theorem separable_of_finrank_lt_char
    {K E : Type} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (c : ℕ) [CharP K c] (h : Module.finrank K E<c) : Algebra.IsSeparable K E := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq E := Classical.decEq E
  refine ⟨fun x => ?_⟩
  exact (RCN364.integral_and_separable_of_small_annihilator c (minpoly K x) x
    (minpoly.ne_zero (IsIntegral.of_finite K x)) (minpoly.aeval K x)
    ((minpoly.natDegree_le x).trans_lt h)).2

theorem prime_projection_gate
    {K : Type} [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (axis : Axis) (lam mu nu : K)
    (ht : Transcendental K (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : B∈P) (hHmem : H∈P)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP K c] (hsmall : flagMixed p q axis.flag<c) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P)
      (flagEvaluation K P lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra
  have hfamily := finite_sum_prime_fields K axis lam mu nu (fun _ : Unit => P)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => ht)
    B H hB hH hrel (fun _ => hBmem) (fun _ => hHmem) p q hp hq
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) := hfamily.1 ()
  have hdegree : Module.finrank (RatFunc K) (CoordinateField K P)≤flagMixed p q axis.flag := by
    simpa only [Fintype.sum_unique] using hfamily.2
  exact ⟨inferInstance,separable_of_finrank_lt_char c (hdegree.trans_lt hsmall)⟩

end
end ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
