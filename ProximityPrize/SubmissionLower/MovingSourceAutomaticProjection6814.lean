import ProximityPrize.SubmissionLower.MovingSourceZSupplier6814

/-! The new pair itself supplies finite/separable projections on the WHOLE
carrier family. The carrier need not be irreducible, and its flag is not
charged separately for each geometric factor. -/
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

/-- A reducible old carrier receives one projection budget from the actual
coprime pair. Only the pair's two mixed bounds are compared with the
characteristic; no degree gate or irreducibility of the carrier is used. -/
theorem exists_whole_projection_family
    {K : Type} [Field K] [IsAlgClosed K]
    (G M R B H : MvPolynomial (Fin 3) K)
    (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ C : RegularComponent K G M R, B∈C.1)
    (hHmem : ∀ C : RegularComponent K G M R, H∈C.1)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP K c]
    (hZsmall : flagMixed p q unitZFlag<c) (hYsmall : flagMixed p q unitYZFlag<c)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0) :
    ∃ base : ∀ C : RegularComponent K G M R, SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base p q) := by
  have hY (C : RegularComponent K G M R) : LiteralProjectionGate C 0 := by
    intro ht
    have ht' : Transcendental K (flagEvaluation K C.1 0 0 0 (MvPolynomial.X (Axis.u.order 0))) := by
      simpa [Axis.order,RCN125.uOrder,affineU] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.uOrder,affineU])
    have hh := prime_projection_gate C.1 .u 0 0 0 ht' B H hB hH hrel (hBmem C) (hHmem C)
      p q hp hq c hYsmall
    rw [he] at hh
    exact hh
  have hZ (C : RegularComponent K G M R) : LiteralProjectionGate C 2 := by
    intro ht
    have ht' : Transcendental K (flagEvaluation K C.1 0 0 0 (MvPolynomial.X (Axis.z.order 0))) := by
      simpa [Axis.order,RCN125.zOrder] using ht
    have he := elementEmbedding_congr ht' ht (by simp [Axis.order,RCN125.zOrder])
    have hh := prime_projection_gate C.1 .z 0 0 0 ht' B H hB hH hrel (hBmem C) (hHmem C)
      p q hp hq c hZsmall
    rw [he] at hh
    exact hh
  let base (C : RegularComponent K G M R) : SeparableLiteralCoordinate C.1 :=
    Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
      (regularComponent_ne_point K G M R C) (hY C) (hZ C))
  obtain ⟨D⟩ := exists_adaptiveNestedProjectionData base hY hZ hderiv
  exact ⟨base,⟨projectionFamily_of_coprime_pair base hY hZ hderiv D
    B H hB hH hrel hBmem hHmem p q hp hq⟩⟩

#print axioms separable_of_finrank_lt_char
#print axioms exists_whole_projection_family
end
end ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
