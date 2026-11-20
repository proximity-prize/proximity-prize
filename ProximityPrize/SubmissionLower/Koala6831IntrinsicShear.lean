import ProximityPrize.SubmissionLower.Koala6831IntrinsicSeedProjections


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open MvPolynomial RCN002 RCN009 RCN011 RCN093 RCN125 RCN371

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K : Type} [Field K]

private theorem monomial_shear_bound (a : K) (l : Fin 3) (d : Fin 3 →₀ ℕ)
    (c : K) (bound : Fin 3 → ℕ)
    (hs : ∀ i, (flagAlgHom (0 : K) a 0 (MvPolynomial.X i)).degreeOf l ≤ bound i) :
    (flagAlgHom (0 : K) a 0 (MvPolynomial.monomial d c)).degreeOf l ≤
      ∑ i : Fin 3, d i * bound i := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    map_mul, map_prod]
  have hC : (flagAlgHom (0 : K) a 0 (MvPolynomial.C c)).degreeOf l = 0 := by simp [flagAlgHom]
  refine (MvPolynomial.degreeOf_mul_le l _ _).trans ?_
  rw [hC, Nat.zero_add]
  refine (MvPolynomial.degreeOf_prod_le l Finset.univ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [map_pow]
  exact (MvPolynomial.degreeOf_pow_le l _ _).trans (Nat.mul_le_mul_left _ (hs i))

private theorem shear_bound (a : K) (l : Fin 3) (F : MvPolynomial (Fin 3) K)
    (bound : Fin 3 → ℕ) (cap : ℕ)
    (hs : ∀ i, (flagAlgHom (0 : K) a 0 (MvPolynomial.X i)).degreeOf l ≤ bound i)
    (hcap : ∀ d ∈ F.support, (∑ i : Fin 3, d i * bound i) ≤ cap) :
    (flagAlgHom (0 : K) a 0 F).degreeOf l ≤ cap := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum]
  apply (MvPolynomial.degreeOf_sum_le l _ _).trans
  apply Finset.sup_le
  intro d hd
  exact (monomial_shear_bound a l d (F.coeff d) bound hs).trans (hcap d hd)

private theorem shear_X1 (a : K) :
    flagAlgHom (0 : K) a 0 (MvPolynomial.X (1 : Fin 3)) =
      MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 0 := by
  simp [flagAlgHom, flagImage]

private theorem shear_X1_ydegree (a : K) :
    (flagAlgHom (0 : K) a 0 (MvPolynomial.X (1 : Fin 3))).degreeOf 0 ≤ 1 := by
  rw [shear_X1]
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  apply max_le
  · simp [MvPolynomial.degreeOf_X_of_ne (by decide : (0 : Fin 3) ≠ 1)]
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp)

private theorem shear_X1_zdegree (a : K) :
    (flagAlgHom (0 : K) a 0 (MvPolynomial.X (1 : Fin 3))).degreeOf 2 ≤ 0 := by
  rw [shear_X1]
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  apply max_le
  · simp [MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by
      simp [MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 3) ≠ 0)])

theorem affine_pair_fiber_degree (a : K) (F : MvPolynomial (Fin 3) K) (t z : ℕ)
    (ht : ∀ d ∈ F.support, d 0 + d 1 ≤ t) (hz : F.degreeOf 2 ≤ z) :
    (flagAlgHom (0 : K) a 0 F).degreeOf 0 ≤ t ∧
      (flagAlgHom (0 : K) a 0 F).degreeOf 2 ≤ z := by
  constructor
  · apply shear_bound a 0 F (![1, 1, 0] : Fin 3 → ℕ) t
    · intro i
      fin_cases i
      · simp [flagAlgHom, flagImage]
      · exact shear_X1_ydegree a
      · simp [flagAlgHom, flagImage, MvPolynomial.degreeOf_X_of_ne (by decide : (0 : Fin 3) ≠ 2)]
    · intro d hd
      simpa [Fin.sum_univ_succ] using ht d hd
  · apply shear_bound a 2 F (![0, 0, 1] : Fin 3 → ℕ) z
    · intro i
      fin_cases i
      · simp [flagAlgHom, flagImage, MvPolynomial.degreeOf_X_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      · exact shear_X1_zdegree a
      · simp [flagAlgHom, flagImage]
    · intro d hd
      simpa [Fin.sum_univ_succ] using (MvPolynomial.monomial_le_degreeOf (2 : Fin 3) hd).trans hz

theorem affine_pair_resultant_degree (a : K) (G T : MvPolynomial (Fin 3) K)
    (tg tt zg zt : ℕ)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ tg)
    (hTt : ∀ d ∈ T.support, d 0 + d 1 ≤ tt)
    (hGz : G.degreeOf 2 ≤ zg) (hTz : T.degreeOf 2 ≤ zt) :
    (Polynomial.resultant (planeMap K seedZeroOrder (flagAlgHom (0 : K) a 0 G))
      (planeMap K seedZeroOrder (flagAlgHom (0 : K) a 0 T))).natDegree ≤ tt * zg + tg * zt := by
  obtain ⟨hG₀, hG₂⟩ := affine_pair_fiber_degree a G tg zg hGt hGz
  obtain ⟨hT₀, hT₂⟩ := affine_pair_fiber_degree a T tt zt hTt hTz
  exact seedZero_resultant_degree _ _ tg tt zg zt hG₀ hT₀ hG₂ hT₂

theorem affine_pair_generators (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] (a : K)
    (ht : Transcendental K
      (flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 0)))) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (RCN022.elementEmbedding K (CoordinateField K P)
        (flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 0))) ht).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 2)),
        flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 1))} :
        Set (CoordinateField K P)) = ⊤ := by
  have hv : Transcendental K (affineV K P a 0) := by
    simpa only [seedZeroOrder_base, flagEvaluation_X_one] using ht
  have hh := flag_generators_v K P 0 a 0 hv
  have hcongr (x y : CoordinateField K P) (hx : Transcendental K x)
      (hy : Transcendental K y) (hxy : x = y) :
      RCN022.elementEmbedding K (CoordinateField K P) x hx =
        RCN022.elementEmbedding K (CoordinateField K P) y hy := by
    subst y
    rfl
  have he := hcongr (flagEvaluation K P 0 a 0 (MvPolynomial.X (seedZeroOrder 0))) (affineV K P a 0)
    ht hv (by simp only [seedZeroOrder_base, flagEvaluation_X_one])
  rw [he]
  simpa only [show seedZeroOrder 1 = 0 by decide, show seedZeroOrder 2 = 2 by decide,
    flagEvaluation_X_zero, flagEvaluation_X_two] using hh

theorem affine_pair_family_finite_rank {I : Type} [Fintype I]
    (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]
    (hinj : Function.Injective Q) (a : K) (G T : MvPolynomial (Fin 3) K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (hpositive : 0 < (planeMap K seedZeroOrder (flagAlgHom (0 : K) a 0 G)).natDegree)
    (ht : ∀ i, Transcendental K
      (flagEvaluation K (Q i) 0 a 0 (MvPolynomial.X (seedZeroOrder 0))))
    (tg tt zg zt : ℕ)
    (hGt : ∀ d ∈ G.support, d 0 + d 1 ≤ tg)
    (hTt : ∀ d ∈ T.support, d 0 + d 1 ≤ tt)
    (hGz : G.degreeOf 2 ≤ zg) (hTz : T.degreeOf 2 ≤ zt) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i => (RCN022.elementEmbedding K (CoordinateField K (Q i))
        (flagEvaluation K (Q i) 0 a 0 (MvPolynomial.X (seedZeroOrder 0))) (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ tt * zg + tg * zt := by
  let e (i : I) := flagEvaluation K (Q i) 0 a 0
  have hgen (i : I) :
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        (RCN022.elementEmbedding K (CoordinateField K (Q i))
          (e i (MvPolynomial.X (seedZeroOrder 0))) (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (seedZeroOrder 2)), e i (MvPolynomial.X (seedZeroOrder 1))} :
        Set (CoordinateField K (Q i))) = ⊤ :=
    affine_pair_generators (Q i) a (ht i)
  have hGroot (i : I) : e i (flagAlgHom (0 : K) a 0 G) = 0 := by
    dsimp only [e]
    rw [flagEvaluation_flag]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hTroot (i : I) : e i (flagAlgHom (0 : K) a 0 T) = 0 := by
    dsimp only [e]
    rw [flagEvaluation_flag]
    change T ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hTmem i
  have hsum := RCN021.finite_sum_finrank_bound K seedZeroOrder
    (fun i => CoordinateField K (Q i)) e ht hgen
    (flagEvaluation_kernel_family_injective K Q hinj 0 a 0)
    (flagAlgHom (0 : K) a 0 G) (flagAlgHom (0 : K) a 0 T)
    ((flag_irreducible_iff 0 a 0 G).mpr hG)
    hGroot hTroot (by simpa only [flag_dvd_iff] using hproper) hpositive
  obtain ⟨hG₀, hG₂⟩ := affine_pair_fiber_degree a G tg zg hGt hGz
  obtain ⟨hT₀, hT₂⟩ := affine_pair_fiber_degree a T tt zt hTt hTz
  have houter (F : MvPolynomial (Fin 3) K) :
      (planeMap K seedZeroOrder F).natDegree ≤ F.degreeOf 0 := by
    simpa only [show seedZeroOrder 1 = 0 by decide] using planeMap_natDegree_le K seedZeroOrder F
  have hinner (F : MvPolynomial (Fin 3) K) :
      Polynomial.Bivariate.degreeX (planeMap K seedZeroOrder F) ≤ F.degreeOf 2 := by
    simpa only [show seedZeroOrder 2 = 2 by decide] using planeMap_degreeX_le K seedZeroOrder F
  exact ⟨hsum.1, hsum.2.trans
    (Nat.add_le_add
      (Nat.mul_le_mul ((houter _).trans hT₀) ((hinner _).trans hG₂))
      (Nat.mul_le_mul ((houter _).trans hG₀) ((hinner _).trans hT₂)))⟩

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
