import ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
namespace ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN022 RCN037 RCN042 RCN046 RCN093 RCN095 RCN114 RCN116 RCN237 RCN264 RCN341 RCN344
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814

theorem sum_coordinateOfGate_le
    (K : Type) [Field K] [IsAlgClosed K] (axis : Axis) (lam mu nu : K)
    {I : Type} [Fintype I]
    (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P)
    (hgate : ∀ i, ∀ ht : Transcendental K
        (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))),
      (letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
        (elementEmbedding K (CoordinateField K (P i))
          (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (CoordinateField K (P i))) ∧
      (letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
        (elementEmbedding K (CoordinateField K (P i))
          (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0))) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))))
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ i, B∈P i) (hHmem : ∀ i, H∈P i)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    (∑ i, coordinateDegree K (CoordinateField K (P i))
      (coordinateOfGate (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))
        (hgate i))) ≤ flagMixed p q axis.flag := by
  classical
  rw [sum_coordinateOfGate_degree_eq]
  exact (finite_sum_prime_fields K axis lam mu nu
    (fun i : {i // Transcendental K
      (flagEvaluation K (P i) lam mu nu (MvPolynomial.X (axis.order 0)))} => P i.1)
    (fun i j hij => Subtype.ext (hinj hij)) (fun i => i.2)
    B H hB hH hrel (fun i => hBmem i.1) (fun i => hHmem i.1) p q hp hq).2

variable {K : Type} [Field K] [IsAlgClosed K]
    {G T R : MvPolynomial (Fin 3) K}

def projectionFamily_of_coprime_pair
    (base : ∀ C : RegularComponent K G T R, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent K G T R, LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (D : AdaptiveNestedProjectionData base hY hZ hderiv)
    (B H : MvPolynomial (Fin 3) K) (hB : B≠0) (hH : H≠0) (hrel : IsRelPrime B H)
    (hBmem : ∀ C : RegularComponent K G T R, B∈C.1)
    (hHmem : ∀ C : RegularComponent K G T R, H∈C.1)
    (p q : FlagDegree) (hp : PolynomialInFlag p B) (hq : PolynomialInFlag q H) :
    AdaptiveUnitProjectionFamily base p q := by
  classical
  let x (axis : Axis) (C : RegularComponent K G T R) :=
    flagEvaluation K C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0))
  have gate (axis : Axis) (C : RegularComponent K G T R)
      (ht : Transcendental K (x axis C)) :
      (letI : Algebra (RatFunc K) (CoordinateField K C.1) :=
        (elementEmbedding K (CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) (CoordinateField K C.1)) ∧
      (letI : Algebra (RatFunc K) (CoordinateField K C.1) :=
        (elementEmbedding K (CoordinateField K C.1) (x axis C) ht).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1)) := by
    cases axis with
    | z =>
      have hz : Transcendental K (coordinate K C.1 2) := by
        simpa only [x,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,flagEvaluation_X_two] using ht
      have he := elementEmbedding_congr ht hz (by
        simp only [x,Axis.order,RCN125.zOrder,Equiv.swap_apply_left,flagEvaluation_X_two])
      rw [he]
      exact hZ C hz
    | u =>
      have hu : Transcendental K (affineU K C.1 D.lam) := by
        simpa only [x,Axis.order,RCN125.uOrder,Equiv.refl_apply,flagEvaluation_X_zero] using ht
      have he := elementEmbedding_congr ht hu (by
        simp only [x,Axis.order,RCN125.uOrder,Equiv.refl_apply,flagEvaluation_X_zero])
      rw [he]
      exact D.uGate C hu
    | v =>
      have he := elementEmbedding_congr ht (D.allAffineTranscendental C) (by
        simp only [x,Axis.order,RCN125.vOrder,Equiv.swap_apply_left,flagEvaluation_X_one])
      rw [he]
      exact ⟨D.allFinite C,D.allSeparable C⟩
  let projection (axis : Axis) (C : RegularComponent K G T R) :=
    coordinateOfGate (x axis C) (gate axis C)
  have hsum (axis : Axis) :
      (∑ C : RegularComponent K G T R,
        coordinateDegree K (CoordinateField K C.1) (projection axis C)) ≤ flagMixed p q axis.flag :=
    sum_coordinateOfGate_le K axis D.lam D.mu (D.mu*D.lam)
      (fun C : RegularComponent K G T R => C.1)
      (fun _ _ h => Subtype.ext h) (gate axis) B H hB hH hrel hBmem hHmem p q hp hq
  have hz (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .z C)=coordinate K C.1 2 := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.zOrder,
      Equiv.swap_apply_left,flagEvaluation_X_two]
  have hu (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .u C)=affineU K C.1 D.lam := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.uOrder,
      Equiv.refl_apply,flagEvaluation_X_zero]
  have hv (C : RegularComponent K G T R) :
      coordinateValue K (CoordinateField K C.1) (projection .v C)=affineV K C.1 D.mu (D.mu*D.lam) := by
    simp only [projection,coordinateOfGate_value,x,Axis.order,RCN125.vOrder,
      Equiv.swap_apply_left,flagEvaluation_X_one]
  refine {
    zProjection := projection .z
    yzProjection := projection .u
    allProjection := projection .v
    zValue := hz
    allTranscendental := ?_
    zPole_eq := ?_
    yzPole_eq := ?_
    allPole_eq := ?_
    sum_zDegree_le := hsum .z
    sum_yzDegree_le := hsum .u
    sum_allDegree_le := hsum .v }
  · intro C
    rw [hv C]
    exact D.allAffineTranscendental C
  · intro C v
    rw [exponentSetPoleWeight_unitZ]
    change _=RCN187.poleOrder v.val _
    rw [hz C]
  · intro C v
    rw [exponentSetPoleWeight_unitYZ]
    change _=RCN187.poleOrder v.val _
    rw [hu C,←D.uValue C]
    exact (D.uPole C v).symm
  · intro C v
    rw [exponentSetPoleWeight_unitAll]
    change _=RCN187.poleOrder v.val _
    rw [hv C,←D.allValue C]
    exact (D.allPole C v).symm

end
end ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
