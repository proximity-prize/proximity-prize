import ProximityPrize.SubmissionLower.Koala6831IntrinsicH2
import ProximityPrize.SubmissionLower.Koala6831IntrinsicPoleProjection
import ProximityPrize.SubmissionLower.Koala6831IntrinsicShear


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial RCN002 RCN009 RCN011 RCN022 RCN093 RCN113 RCN117 RCN120 RCN125 RCN344 RCN371

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K : Type} [Field K] [IsAlgClosed K]

private theorem transcendental_of_not_mem_powerField {E : Type} [Field E] [Algebra K E]
    (p : ℕ) [ExpChar E p] [PerfectRing K p] (u : E) (hu : u ∉ powerField E p) :
    Transcendental K u := by
  intro halg
  obtain ⟨c, he⟩ := RCN370.eq_algebraMap_of_isAlgebraic K E u halg
  exact hu (he ▸ algebraMap_mem_powerField p c)

theorem flagAffinePair_value (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] (a : K) :
    flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 0)) =
      coordinate K P 1 + algebraMap K (CoordinateField K P) a * coordinate K P 0 := by
  simp [seedZeroOrder_base, affineV, Algebra.smul_def]

private theorem affine_directional_bad_subsingleton (G : MvPolynomial (Fin 3) K)
    (hd : MvPolynomial.pderiv (0 : Fin 3) G ≠ 0) :
    {a : K | MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G = 0}.Subsingleton := by
  by_cases h : MvPolynomial.pderiv (1 : Fin 3) G = 0
  · intro a ha b _
    exact (hd (by simpa only [Set.mem_setOf_eq, h, mul_zero, sub_zero] using ha)).elim
  · exact fun _ ha _ hb => RCN096.directional_bad_coefficient_subsingleton G h ha hb

private theorem affine_outer_positive (a : K) (G : MvPolynomial (Fin 3) K)
    (ha : MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G ≠ 0) :
    0 < (planeMap K seedZeroOrder (flagAlgHom (0 : K) a 0 G)).natDegree := by
  apply planeMap_natDegree_pos_of_pderiv_ne_zero seedZeroOrder
  rw [show seedZeroOrder 1 = 0 by decide]
  have h := pderiv_zero_flagAlgHom_nested (0 : K) a G
  rw [mul_zero] at h
  rw [h]
  exact (flagEquiv (0 : K) a 0).injective.ne ha

theorem exists_separating_affine_pair {I : Type} [Fintype I]
    (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]
    (hinj : Function.Injective Q) (G T : MvPolynomial (Fin 3) K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T) (hderiv : MvPolynomial.pderiv (0 : Fin 3) G ≠ 0)
    (p : ℕ) [ExpChar K p] [PerfectRing K p] [∀ i, ExpChar (CoordinateField K (Q i)) p]
    (hp : p.Prime)
    (hactive : ∀ i, coordinate K (Q i) 1 ∉ powerField (CoordinateField K (Q i)) p ∨
      coordinate K (Q i) 0 ∉ powerField (CoordinateField K (Q i)) p)
    (seed : ∀ i, SeparableCoordinate K (CoordinateField K (Q i)))
    (W : ∀ i, Finset (Place K (CoordinateField K (Q i))))
    (tg tt zg zt : ℕ)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ tg) (hTt : ∀ d ∈ T.support, d 0 + d 1 ≤ tt)
    (hGz : G.degreeOf 2 ≤ zg) (hTz : T.degreeOf 2 ≤ zt) :
    ∃ a : K,
      0 < (flagPlaneMap K 0 a 0 seedZeroOrder G).natDegree ∧
      ∃ ht : ∀ i, Transcendental K
          (flagEvaluation K (Q i) 0 a 0 (MvPolynomial.X (seedZeroOrder 0))),
        (∀ i, letI := flagBaseAlgebra K (Q i) 0 a 0 seedZeroOrder (ht i)
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
        (∀ i, letI := flagBaseAlgebra K (Q i) 0 a 0 seedZeroOrder (ht i)
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) ∧
        (∀ i v, v ∈ W i →
          RCN187.poleOrder v.val
            (flagEvaluation K (Q i) 0 a 0 (MvPolynomial.X (seedZeroOrder 0))) =
            max (RCN187.poleOrder v.val (coordinate K (Q i) 1))
              (RCN187.poleOrder v.val (coordinate K (Q i) 0))) := by
  classical
  let bad : Unit ⊕ (I ⊕ Σ i, {v // v ∈ W i}) → Set K
    | .inl _ => {a | MvPolynomial.pderiv (0 : Fin 3) G -
      MvPolynomial.C a * MvPolynomial.pderiv (1 : Fin 3) G = 0}
    | .inr (.inl i) => {a | coordinate K (Q i) 1 +
      algebraMap K (CoordinateField K (Q i)) a * coordinate K (Q i) 0 ∈ powerField _ p}
    | .inr (.inr ⟨i, v⟩) => {a | v.1.val (coordinate K (Q i) 1 +
      algebraMap K (CoordinateField K (Q i)) a * coordinate K (Q i) 0) <
        max (v.1.val (coordinate K (Q i) 1)) (v.1.val (coordinate K (Q i) 0))}
  have hbad : ∀ j, (bad j).Subsingleton := by
    intro j
    rcases j with _ | i | ⟨i, v⟩
    · exact affine_directional_bad_subsingleton G hderiv
    · exact power_affine_parameters_subsingleton p _ _ (hactive i)
    · letI := v.1.property.2
      exact affineProjection_valuation_bad_subsingleton v.1.val _ _
  obtain ⟨a, ha⟩ := exists_avoiding_finite_subsingleton_parameters bad hbad
  have hpos := affine_outer_positive a G (ha (.inl ()))
  have hn (i : I) : flagEvaluation K (Q i) 0 a 0 (MvPolynomial.X (seedZeroOrder 0)) ∉
      powerField (CoordinateField K (Q i)) p := by
    rw [flagAffinePair_value]
    exact ha (.inr (.inl i))
  have ht (i : I) := transcendental_of_not_mem_powerField (K := K) p _ (hn i)
  have hfin := (affine_pair_family_finite_rank Q hinj a G T
    hG hGmem hTmem hproper hpos ht tg tt zg zt hGt hTt hGz hTz).1
  refine ⟨a, hpos, ht, hfin, ?_, ?_⟩
  · intro i
    let s := (seed i).embedding (RatFunc.X : RatFunc K)
    have hs : Transcendental K s := by
      intro h
      exact RatFunc.transcendental_X (K := K)
        ((isAlgebraic_algHom_iff (seed i).embedding (seed i).embedding.injective).mp h)
    have he : elementEmbedding K (CoordinateField K (Q i)) s hs = (seed i).embedding := by
      apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
      ext
      change elementEmbedding K (CoordinateField K (Q i)) s hs
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        (seed i).embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
      rw [elementEmbedding_variable, RatFunc.algebraMap_X]
    have hsep : letI := (elementEmbedding K _ s hs).toRingHom.toAlgebra
        Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)) := by
      change @Algebra.IsSeparable _ _ _ _ (elementEmbedding K _ s hs).toRingHom.toAlgebra
      rw [he]
      exact (seed i).separable
    exact separable_affine_projection_from_seed p hp s _ hs (ht i) (hn i) hsep (hfin i)
  · intro i v hv
    letI := v.property.2
    rw [flagAffinePair_value]
    exact affineProjection_poleOrder_eq v.val _ _ a (ha (.inr (.inr ⟨i, ⟨v, hv⟩⟩)))

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
