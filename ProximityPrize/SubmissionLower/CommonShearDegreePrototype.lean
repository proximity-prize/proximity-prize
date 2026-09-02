import ProximityPrize.SubmissionLower.Y7
import ProximityPrize.SubmissionLower.R7

namespace ProximityPrize.SubmissionLower.RCN988

open scoped Classical BigOperators
open RCN001 RCN002 RCN005 RCN008 RCN009 RCN011 RCN013 RCN021 RCN022 RCN093 RCN125 RCN351
  RCN371 RCN372

noncomputable section

variable {K : Type} [Field K]

private def familyFiniteSummary {I : Type} [Fintype I]
    (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)))
    (bound : ℕ) : Prop :=
  letI := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ bound

private theorem elementEmbedding_congr_local
    {L : Type} [Field L] [Algebra K L] {s t : L}
    (hs : Transcendental K s) (ht : Transcendental K t) (h : s = t) :
    elementEmbedding K L s hs = elementEmbedding K L t ht := by
  subst t
  rfl

theorem flagAlgHom_zero_zero_eq_shearAlgHom (a : K) :
    RCN125.flagAlgHom (0 : K) 0 a = RCN372.shearAlgHom a := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [RCN125.flagImage, RCN125.flagAlgHom,
      RCN372.shearImage, RCN372.shearAlgHom]

theorem flag_shear_degreeOf_zero_le (a : K)
    (F : MvPolynomial (Fin 3) K) :
    (RCN125.flagAlgHom (0 : K) 0 a F).degreeOf 0 ≤ F.degreeOf 0 := by
  rw [flagAlgHom_zero_zero_eq_shearAlgHom]
  exact RCN372.shear_degreeOf_zero_le a F

theorem flag_shear_degreeOf_two_le (a : K)
    (F : MvPolynomial (Fin 3) K) :
    (RCN125.flagAlgHom (0 : K) 0 a F).degreeOf 2 ≤
      F.degreeOf 2 + F.degreeOf 1 := by
  rw [flagAlgHom_zero_zero_eq_shearAlgHom]
  exact RCN372.shear_degreeOf_two_le a F

theorem coordinateMixedDegree_flag_shear_one_le (a : K)
    (G T : MvPolynomial (Fin 3) K) :
    RCN001.coordinateMixedDegree K
        (RCN125.flagAlgHom (0 : K) 0 a G)
        (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤
      RCN001.coordinateMixedDegree K G T 1 +
        RCN001.coordinateMixedDegree K G T 2 := by
  rw [RCN001.coordinateMixedDegree_one,
    RCN001.coordinateMixedDegree_one,
    RCN001.coordinateMixedDegree_two]
  have hG0 := flag_shear_degreeOf_zero_le a G
  have hG2 := flag_shear_degreeOf_two_le a G
  have hT0 := flag_shear_degreeOf_zero_le a T
  have hT2 := flag_shear_degreeOf_two_le a T
  calc
    _ ≤ T.degreeOf 0 * (G.degreeOf 2 + G.degreeOf 1) +
        G.degreeOf 0 * (T.degreeOf 2 + T.degreeOf 1) :=
      Nat.add_le_add (Nat.mul_le_mul hT0 hG2)
        (Nat.mul_le_mul hG0 hT2)
    _ = T.degreeOf 0 * G.degreeOf 2 + G.degreeOf 0 * T.degreeOf 2 +
        (T.degreeOf 0 * G.degreeOf 1 + G.degreeOf 0 * T.degreeOf 1) := by
      simp only [Nat.mul_add]
      omega

section Family

variable {I : Type} [Fintype I]
  (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]

theorem exists_common_component_shear
    [IsAlgClosed K]
    (hZ : ∀ i, Transcendental K (coordinate K (Q i) 2))
    (hfiniteZ : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 (hZ i)
      FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))
    (hsepZ : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 (hZ i)
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) :
    ∃ a : K, a ≠ 0 ∧ ∀ i,
      ∃ hS : Transcendental K
          (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) := by
  let embeddingZ : ∀ i, RatFunc K →ₐ[K] CoordinateField K (Q i) :=
    fun i => rationalBaseEmbedding K (Q i) 2 (hZ i)
  have hvalueZ : ∀ i, embeddingZ i
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        coordinate K (Q i) 2 := by
    intro i
    dsimp only [embeddingZ]
    rw [rationalBaseEmbedding_polynomial, Polynomial.aeval_X]
  exact RCN351.exists_common_finite_separable_shear K
    (fun i => CoordinateField K (Q i))
    (fun i => coordinate K (Q i) 1)
    (fun i => coordinate K (Q i) 2)
    embeddingZ hvalueZ hfiniteZ hsepZ

/-- Once one common shear makes `R + a Z` transcendental on a finite family,
the separability-free family resultant bounds the *sum* of all resulting
extension degrees by the old `R` and `Z` mixed-degree budgets together.  This
is the aggregate substitute for the unavailable componentwise inequality
`[L : K(R+Z)] ≤ [L : K(R)] + [L : K(Z)]`. -/
theorem finite_sum_flag_shear_finrank_le_two_budgets_of_order
    (order : Fin 3 ≃ Fin 3)
    (horder : order = Equiv.swap 0 1 ∨
      order = RCN013.swapOtherOrder (Equiv.swap 0 1))
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (RCN093.affineV K (Q i) 0 a))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (hpositive : 0 <
      (planeMap K order
        (RCN125.flagAlgHom (0 : K) 0 a G)).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i => (elementEmbedding K (CoordinateField K (Q i))
        (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        RCN001.coordinateMixedDegree K G T 1 +
          RCN001.coordinateMixedDegree K G T 2 := by
  let e : ∀ i, MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i) :=
    fun i => RCN093.flagEvaluation K (Q i) 0 0 a
  have hbase : order 0 = 1 := by
    rcases horder with hsame | hswap
    · subst order
      decide
    · subst order
      simp
  have ht : ∀ i, Transcendental K (e i (MvPolynomial.X (order 0))) := by
    intro i
    simpa [e, hbase] using hS i
  have hemb (i : I) :
      elementEmbedding K (CoordinateField K (Q i))
          (e i (MvPolynomial.X (order 0))) (ht i) =
        elementEmbedding K (CoordinateField K (Q i))
          (RCN093.affineV K (Q i) 0 a) (hS i) :=
    elementEmbedding_congr_local (ht i) (hS i)
      (by simp [e, hbase])
  have hgen : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        (elementEmbedding K (CoordinateField K (Q i))
          (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)), e i (MvPolynomial.X (order 1))} :
          Set (CoordinateField K (Q i))) = ⊤ := by
    intro i
    rw [hemb i]
    rcases horder with hsame | hswap
    · subst order
      simpa [e, Equiv.swap_apply_def] using
        (RCN093.flag_generators_v K (Q i) 0 0 a (hS i))
    · subst order
      simpa [e, RCN013.swapOtherOrder, Equiv.swap_apply_def, Set.pair_comm]
        using (RCN093.flag_generators_v K (Q i) 0 0 a (hS i))
  have hGroot : ∀ i, e i (RCN125.flagAlgHom (0 : K) 0 a G) = 0 := by
    intro i
    rw [show e i (RCN125.flagAlgHom (0 : K) 0 a G) =
        coordinateEvaluation K (Q i) G from
      RCN093.flagEvaluation_flag K (Q i) 0 0 a G]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hTroot : ∀ i, e i (RCN125.flagAlgHom (0 : K) 0 a T) = 0 := by
    intro i
    rw [show e i (RCN125.flagAlgHom (0 : K) 0 a T) =
        coordinateEvaluation K (Q i) T from
      RCN093.flagEvaluation_flag K (Q i) 0 0 a T]
    change T ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hTmem i
  have hresult := RCN021.finite_sum_finrank_bound K order
    (fun i => CoordinateField K (Q i)) e ht hgen
    (RCN093.flagEvaluation_kernel_family_injective K Q hinj 0 0 a)
    (RCN125.flagAlgHom (0 : K) 0 a G)
    (RCN125.flagAlgHom (0 : K) 0 a T)
    ((RCN125.flag_irreducible_iff 0 0 a G).mpr hG)
    hGroot hTroot (by simpa only [RCN125.flag_dvd_iff] using hproper)
    hpositive
  have htransformed : RCN013.originalMixedDegree K order
      (RCN125.flagAlgHom (0 : K) 0 a G)
      (RCN125.flagAlgHom (0 : K) 0 a T) ≤
      RCN001.coordinateMixedDegree K G T 1 +
        RCN001.coordinateMixedDegree K G T 2 := by
    rcases horder with hsame | hswap
    · subst order
      change RCN001.coordinateMixedDegree K
          (RCN125.flagAlgHom (0 : K) 0 a G)
          (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤ _
      exact coordinateMixedDegree_flag_shear_one_le a G T
    · subst order
      rw [RCN013.originalMixedDegree_swap]
      change RCN001.coordinateMixedDegree K
          (RCN125.flagAlgHom (0 : K) 0 a G)
          (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤ _
      exact coordinateMixedDegree_flag_shear_one_le a G T
  have hbound := hresult.2 |>.trans
    (RCN008.plane_budget_le_original K order
      (RCN125.flagAlgHom (0 : K) 0 a G)
      (RCN125.flagAlgHom (0 : K) 0 a T)) |>.trans htransformed
  have hpack := And.intro hresult.1 hbound
  let A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
    fun i => (elementEmbedding K (CoordinateField K (Q i))
      (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
  let B : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
    fun i => (elementEmbedding K (CoordinateField K (Q i))
      (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
  have hAB : A = B := by
    funext i
    exact congrArg (fun f => f.toRingHom.toAlgebra) (hemb i)
  change familyFiniteSummary Q A
    (RCN001.coordinateMixedDegree K G T 1 +
      RCN001.coordinateMixedDegree K G T 2) at hpack
  change familyFiniteSummary Q B
    (RCN001.coordinateMixedDegree K G T 1 +
      RCN001.coordinateMixedDegree K G T 2)
  rw [← hAB]
  exact hpack

/-- The outer-variable positivity required by the planar resultant is not an
extra source hypothesis: on a nonempty component family irreducibility chooses
one of the two non-base variables.  Swapping those two variables preserves the
mixed-degree budget.  The empty family is immediate. -/
theorem finite_sum_flag_shear_finrank_le_two_budgets_auto
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (RCN093.affineV K (Q i) 0 a))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i => (elementEmbedding K (CoordinateField K (Q i))
        (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        RCN001.coordinateMixedDegree K G T 1 +
          RCN001.coordinateMixedDegree K G T 2 := by
  classical
  by_cases hI : Nonempty I
  · let i0 : I := Classical.choice hI
    let order0 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
    let e0 : MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i0) :=
      RCN093.flagEvaluation K (Q i0) 0 0 a
    have ht0 : Transcendental K (e0 (MvPolynomial.X (order0 0))) := by
      simpa [e0, order0, Equiv.swap_apply_def] using hS i0
    have hGroot0 : e0 (RCN125.flagAlgHom (0 : K) 0 a G) = 0 := by
      rw [show e0 (RCN125.flagAlgHom (0 : K) 0 a G) =
          coordinateEvaluation K (Q i0) G from
        RCN093.flagEvaluation_flag K (Q i0) 0 0 a G]
      change G ∈ RingHom.ker (coordinateEvaluation K (Q i0)).toRingHom
      rw [coordinateEvaluation_ker]
      exact hGmem i0
    have hirr := RCN021.rationalMap_irreducible_of_evaluation K
      (CoordinateField K (Q i0)) order0 e0
      (RCN125.flagAlgHom (0 : K) 0 a G)
      ((RCN125.flag_irreducible_iff 0 0 a G).mpr hG) hGroot0 ht0
    rcases RCN013.positive_degree_of_irreducible
        (rationalMap K order0 (RCN125.flagAlgHom (0 : K) 0 a G)) hirr with
      houter | hinner
    · apply finite_sum_flag_shear_finrank_le_two_budgets_of_order Q
        order0 (Or.inl rfl) hinj a hS G T hG hGmem hTmem hproper
      change 0 < (bivariateEquiv (RatFunc K)
        (rationalMap K order0
          (RCN125.flagAlgHom (0 : K) 0 a G))).natDegree
      rwa [bivariateEquiv_natDegree]
    · apply finite_sum_flag_shear_finrank_le_two_budgets_of_order Q
        (RCN013.swapOtherOrder order0) (Or.inr rfl)
        hinj a hS G T hG hGmem hTmem hproper
      rwa [RCN013.swapped_outer_degree]
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

/-- Choose the coefficient using only the `Z`-transcendental components, but
charge *every* component on which the resulting `R + a Z` is transcendental
in one resultant family.  This includes the `Z`-algebraic/`R`-transcendental
case and is the form needed for the algebraic-`Z` fiber split. -/
theorem exists_common_shear_with_full_transcendental_sum_bound
    [IsAlgClosed K]
    (hinj : Function.Injective Q)
    (hfiniteZ : ∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 hZ
      FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))
    (hsepZ : ∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 hZ
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T) :
    ∃ a : K, a ≠ 0 ∧
      (∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
        ∃ hS : Transcendental K
            (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
          (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
              (elementEmbedding K (CoordinateField K (Q i))
                (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
                hS).toRingHom.toAlgebra;
            FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
          (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
              (elementEmbedding K (CoordinateField K (Q i))
                (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
                hS).toRingHom.toAlgebra;
            Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)))) ∧
      (let sS : Set I := {i | Transcendental K
          (RCN093.affineV K (Q i) 0 a)}
       let hS : ∀ i : sS,
          Transcendental K (RCN093.affineV K (Q i) 0 a) := fun i => i.2
       letI : ∀ i : sS,
          Algebra (RatFunc K) (CoordinateField K (Q i)) :=
         fun i => (elementEmbedding K (CoordinateField K (Q i))
           (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
       (∀ i : sS,
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
         (∑ i : sS,
            Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
           RCN001.coordinateMixedDegree K G T 1 +
             RCN001.coordinateMixedDegree K G T 2) := by
  classical
  let sZ : Set I := {i | Transcendental K (coordinate K (Q i) 2)}
  obtain ⟨a, ha0, hzdata⟩ := exists_common_component_shear
    (Q := fun i : sZ => Q i)
    (fun i => i.2)
    (fun i => hfiniteZ i.1 i.2)
    (fun i => hsepZ i.1 i.2)
  have hzdata' : ∀ i (hZi : Transcendental K (coordinate K (Q i) 2)),
      ∃ hS : Transcendental K
          (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) := by
    intro i hZi
    exact hzdata ⟨i, hZi⟩
  refine ⟨a, ha0, hzdata', ?_⟩
  let sS : Set I := {i | Transcendental K
    (RCN093.affineV K (Q i) 0 a)}
  let hS : ∀ i : sS,
      Transcendental K (RCN093.affineV K (Q i) 0 a) := fun i => i.2
  exact finite_sum_flag_shear_finrank_le_two_budgets_auto
    (Q := fun i : sS => Q i) (fun _ _ h => Subtype.ext (hinj h))
    a hS G T hG (fun i => hGmem i) (fun i => hTmem i) hproper

end Family

end

end ProximityPrize.SubmissionLower.RCN988
