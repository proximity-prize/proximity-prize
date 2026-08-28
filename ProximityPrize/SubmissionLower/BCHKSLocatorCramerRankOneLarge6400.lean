import ProximityPrize.SubmissionLower.BCHKSLocatorCramerRankTwoAssembly6400

/-!
# Large-nullity rank-one locator kernels

If a subspace of degree-capped polynomial pairs has alternating rank one,
then the presence of any nonzero second component makes projection to that
component injective.  Its dimension is consequently at most the second
degree cap.  For the production locator kernel this means that rational rank
one and nullity above `22489` force the entire Frobenius block to vanish.

The second half of the file turns one nonzero ordinary-only polynomial
kernel vector into a challenge-root obstruction.  At a retained bad slope
the corresponding ordinary multiplier would have at least `76771` genuine
error roots despite degree below `54292`, so the polynomial vector must
specialize to zero.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- In an alternating-rank-one polynomial-pair space, a nonzero second
component makes second projection injective.  Hence a space whose dimension
exceeds the second degree cap has identically zero second component. -/
theorem second_component_eq_zero_of_pairwise_pairDet_eq_zero
    {F : Type} [Field F] (c h : ℕ)
    (V : Submodule F (PolynomialPairSpace F c h))
    (hlarge : h < Module.finrank F V)
    (hrankOne : ∀ u v : V, polynomialPairDet u.1 v.1 = 0) :
    ∀ u : V, u.1.2.1 = 0 := by
  intro u
  by_contra hu
  let second : V →ₗ[F] Polynomial.degreeLT F h :=
    { toFun := fun v => v.1.2
      map_add' := by
        intro v w
        rfl
      map_smul' := by
        intro a v
        rfl }
  have hsecond : Function.Injective second := by
    intro v w hvw
    change v.1.2 = w.1.2 at hvw
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hdet := hrankOne u (v - w)
      have hsecondZero : (v - w).1.2.1 = 0 := by
        have hvwPoly := congrArg Subtype.val hvw
        simpa only [second, Submodule.coe_sub, Prod.snd_sub,
          Submodule.coe_sub, sub_eq_zero] using hvwPoly
      have hproduct : u.1.2.1 * (v - w).1.1.1 = 0 := by
        simpa only [polynomialPairDet, hsecondZero, mul_zero,
          zero_sub, neg_eq_zero, mul_comm] using hdet
      have hfirstZero : (v - w).1.1.1 = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left hu
      simpa only [Submodule.coe_sub, Prod.fst_sub, Submodule.coe_sub,
        sub_eq_zero] using hfirstZero
    · exact hvw
  have hle := LinearMap.finrank_le_finrank_of_injective hsecond
  have htarget : Module.finrank F (Polynomial.degreeLT F h) = h := by
    rw [(Polynomial.degreeLTEquiv F h).finrank_eq, Module.finrank_fin_fun]
  rw [htarget] at hle
  omega

/-- Vanishing of every Frobenius-block coordinate is exactly vanishing of
the Frobenius multiplier polynomial. -/
theorem score6400LocatorRelationPair_snd_eq_zero_of_inr_eq_zero
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : ∀ i : Fin locatorFrobeniusRows6400, q (Sum.inr i) = 0) :
    (score6400LocatorRelationPair q).2.1 = 0 := by
  apply Polynomial.ext
  intro n
  by_cases hn : n < locatorFrobeniusRows6400
  · let i : Fin locatorFrobeniusRows6400 := ⟨n, hn⟩
    have hcoeff := score6400LocatorRelationPair_inr_coeff q i
    rw [degreeLTEquiv_apply_eq_coeff] at hcoeff
    simpa only [i, Polynomial.coeff_zero] using hcoeff.trans (hq i)
  · have hnle : locatorFrobeniusRows6400 ≤ n := Nat.le_of_not_gt hn
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      ((Polynomial.mem_degreeLT.mp
        (score6400LocatorRelationPair q).2.2).trans_le
          (WithBot.coe_le_coe.mpr hnle)), Polynomial.coeff_zero]

/-- A retained score-64 bad slope cannot support a nonzero ordinary-only
production relation: its ordinary multiplier would have more distinct error
roots than its degree. -/
theorem score6400_ordinaryOnly_locatorKernel_relation_eq_zero
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field)
    (hq : q ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).mulVecLin)
    (hqinr : ∀ i : Fin locatorFrobeniusRows6400,
      q (Sum.inr i) = 0)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    (score6400LocatorRelationPair q).1.1 = 0 := by
  classical
  obtain ⟨A, P, E, hAcard, hPdegree, hagreement, _hunexplained,
      hE, hEcard, _hEupper⟩ :=
    exists_score6400_large_error_witness f₀ f₁ z hbad hnotOld
  let ordinary := (score6400LocatorRelationPair q).1.1
  have hfrobenius : (score6400LocatorRelationPair q).2.1 = 0 :=
    score6400LocatorRelationPair_snd_eq_zero_of_inr_eq_zero q hqinr
  have hroot : ∀ i ∈ E,
      ordinary.eval (IRSProfile.domain i) = 0 := by
    intro i hi
    have hiError : (f₀ i + z * f₁ i) -
        P.eval (IRSProfile.domain i) ≠ 0 := by
      have hi' := (Finset.mem_filter.mp (by simpa only [hE] using hi)).2
      exact hi'
    have hrelation := score6400_locatorKernel_error_relation_of_agreement
      f₀ f₁ z q hq A P hAcard hPdegree hagreement i
    rw [hfrobenius, Polynomial.eval_zero, zero_mul, add_zero] at hrelation
    exact (mul_eq_zero.mp hrelation).resolve_right hiError
  by_cases hzero : ordinary = 0
  · exact hzero
  have hdegree : ordinary.natDegree < locatorOrdinaryRows6400 := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hzero]
    exact Polynomial.mem_degreeLT.mp
      (score6400LocatorRelationPair q).1.2
  have hdegreeE : ordinary.natDegree < E.card := by
    norm_num [locatorOrdinaryRows6400] at hdegree
    omega
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    ordinary (f := fun i : E => IRSProfile.domain i.1)
  · intro i j hij
    apply Subtype.ext
    exact IRSProfile.domain.injective hij
  · intro i
    exact hroot i.1 i.2
  · simpa only [Fintype.card_coe] using hdegreeE

/-- A single polynomial production-kernel vector supported only on the
ordinary block controls all retained bad slopes by any one of its nonzero
ordinary coordinate polynomials. -/
theorem score6400_ordinaryOnly_polynomialKernel_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (hqinr : ∀ i : Fin locatorFrobeniusRows6400,
      q (Sum.inr i) = 0)
    (i₀ : Fin locatorOrdinaryRows6400)
    (hi₀ : q (Sum.inl i₀) ≠ 0)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ (q (Sum.inl i₀)).natDegree := by
  classical
  let g := q (Sum.inl i₀)
  have hroot : ∀ z ∈ T, g.eval z = 0 := by
    intro z hz
    let qz : Score6400LocatorMinorIndex → IRSProfile.Field :=
      fun n => (q n).eval z
    have hqz : qz ∈ LinearMap.ker
        (twoBlockSpecialization
          (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
          z (z ^ 2130706433)).mulVecLin := by
      exact score6400_eval_mem_locatorKernel_of_polynomial_mem_ker
        f₀ f₁ q hq z
    have hqzinr : ∀ i : Fin locatorFrobeniusRows6400,
        qz (Sum.inr i) = 0 := by
      intro i
      simp only [qz, hqinr i, Polynomial.eval_zero]
    have hordinary := score6400_ordinaryOnly_locatorKernel_relation_eq_zero
      f₀ f₁ z qz hqz hqzinr (hbad z hz) (hnotOld z hz)
    have hcoeff := score6400LocatorRelationPair_inl_coeff qz i₀
    rw [degreeLTEquiv_apply_eq_coeff, hordinary,
      Polynomial.coeff_zero] at hcoeff
    simpa only [g, qz] using hcoeff.symm
  have hsub : T ⊆ g.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (by simpa [g] using hi₀)]
    exact hroot z hz
  calc
    T.card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ g.roots.card := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ = (q (Sum.inl i₀)).natDegree := rfl

/-- Rational rank one above the Frobenius-block dimension forces an
ordinary-only Cramer vector.  One nonzero coordinate of that vector bounds
all retained score-64 bad slopes. -/
theorem score6400_largeNullity_rankOne_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlarge : 22490 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ score6400KernelBasisTotalDegree := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  obtain ⟨r, rows, cols, hrows, hcols, hrank, hcomplement, hminor,
      hpolynomialKer, hdegree, hspan⟩ :=
    exists_score6400_spanning_bounded_locatorCramerFamily
      f₀ f₁ L hkernelRank
  let coordinateFamily : SelectedColumnComplement cols →
      Score6400LocatorMinorIndex → K :=
    mappedSelectedPolynomialCramerKernelVector ι M rows cols hcols
  let A := score6400SelectedLocatorCramerOrdinary
    f₀ f₁ rows cols hcols
  let B := score6400SelectedLocatorCramerFrobenius
    f₀ f₁ rows cols hcols
  have hA : ∀ j, A j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorOrdinaryRows6400 :=
    score6400SelectedLocatorCramerOrdinary_mem_degreeLT
      f₀ f₁ rows cols hcols
  have hB : ∀ j, B j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorFrobeniusRows6400 :=
    score6400SelectedLocatorCramerFrobenius_mem_degreeLT
      f₀ f₁ rows cols hcols
  let pairFamily : SelectedColumnComplement cols →
      PolynomialPairSpace K locatorOrdinaryRows6400
        locatorFrobeniusRows6400 :=
    locatorPairFamilyFraction
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 A B hA hB
  have hfamily : ∀ j, pairFamily j = e.symm (coordinateFamily j) := by
    intro j
    simpa only [pairFamily, A, B, coordinateFamily, K, ι, M,
      locatorPairFamilyFraction,
      score6400SelectedLocatorCramerOrdinary,
      score6400SelectedLocatorCramerFrobenius,
      score6400SelectedLocatorCramerVector,
      mappedSelectedPolynomialCramerKernelVector, e] using
        score6400_locatorFractionRelationPair_eq_coordinatePair
          (score6400SelectedLocatorCramerVector
            f₀ f₁ rows cols hcols j)
  have hpairLI : LinearIndependent K pairFamily := by
    simpa only [K, pairFamily, A, B] using
      linearIndependent_score6400SelectedLocatorCramerFractionPairs
        f₀ f₁ rows cols hcols hminor
  let V := Submodule.span K (Set.range pairFamily)
  have hVrank : Module.finrank K V = L := by
    calc
      Module.finrank K V =
          Fintype.card (SelectedColumnComplement cols) := by
        simpa only [V] using finrank_span_eq_card hpairLI
      _ = Nat.card (SelectedColumnComplement cols) := by
        rw [Nat.card_eq_fintype_card]
      _ = L := hcomplement
  have hfamilyMem : ∀ j,
      pairFamily j ∈ score6400LocatorRationalPairKernel f₀ f₁ := by
    intro j
    change e (pairFamily j) ∈ LinearMap.ker (M.map ι).mulVecLin
    rw [hfamily j, e.apply_symm_apply]
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hVle : V ≤ score6400LocatorRationalPairKernel f₀ f₁ := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hfamilyMem j
  have hrankOneV : ∀ u v : V, polynomialPairDet u.1 v.1 = 0 := by
    intro u v
    exact hrankOne ⟨u.1, hVle u.2⟩ ⟨v.1, hVle v.2⟩
  have hVlarge : locatorFrobeniusRows6400 < Module.finrank K V := by
    rw [hVrank]
    norm_num [locatorFrobeniusRows6400]
    omega
  have hsecond : ∀ u : V, u.1.2.1 = 0 :=
    second_component_eq_zero_of_pairwise_pairDet_eq_zero
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 V hVlarge hrankOneV
  have hJcard : Fintype.card (SelectedColumnComplement cols) = L := by
    rw [← Nat.card_eq_fintype_card]
    exact hcomplement
  have hJpos : 0 < Fintype.card (SelectedColumnComplement cols) := by
    rw [hJcard]
    omega
  let j₀ : SelectedColumnComplement cols :=
    Classical.choice (Fintype.card_pos_iff.mp hJpos)
  have hpairMemV : pairFamily j₀ ∈ V :=
    Submodule.subset_span (Set.mem_range_self j₀)
  have hsecondj : (pairFamily j₀).2.1 = 0 :=
    hsecond ⟨pairFamily j₀, hpairMemV⟩
  have hBzero : B j₀ = 0 := by
    apply Polynomial.map_injective ι
      (IsFractionRing.injective IRSProfile.Field[X] K)
    have hmap : (B j₀).map ι = 0 := by
      simpa only [pairFamily, locatorPairFamilyFraction,
        locatorFractionDegreeLT, B, K, ι] using hsecondj
    simpa only [Polynomial.map_zero] using hmap
  let q := score6400SelectedLocatorCramerVector
    f₀ f₁ rows cols hcols j₀
  have hqinr : ∀ i : Fin locatorFrobeniusRows6400,
      q (Sum.inr i) = 0 := by
    intro i
    have hcoeff := score6400PolynomialLocatorRelationPair_inr_coeff q i
    rw [degreeLTEquiv_apply_eq_coeff] at hcoeff
    have hBform : (score6400PolynomialLocatorRelationPair q).2.1 = B j₀ := rfl
    rw [hBform, hBzero, Polynomial.coeff_zero] at hcoeff
    exact hcoeff.symm
  have hpivotNe :
      (selectedPolynomialPivotBlock
        (score6400LocatorPolynomialMatrix f₀ f₁) rows cols).det ≠ 0 := by
    intro hzero
    exact hminor (by rw [hzero, map_zero])
  have hfree : q j₀.1 =
      (selectedPolynomialPivotBlock
        (score6400LocatorPolynomialMatrix f₀ f₁) rows cols).det := by
    have hfreeRaw := selectedPolynomialCramerKernelVector_apply_free
      (score6400LocatorPolynomialMatrix f₀ f₁) rows cols hcols j₀ j₀
    rw [if_pos rfl] at hfreeRaw
    simpa only [q, score6400SelectedLocatorCramerVector] using hfreeRaw
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin locatorOrdinaryRows6400,
      q (Sum.inl i₀) ≠ 0 := by
    cases hj : j₀.1 with
    | inl i =>
        refine ⟨i, ?_⟩
        rw [← hj, hfree]
        exact hpivotNe
    | inr i =>
        exfalso
        have hz := hqinr i
        rw [← hj, hfree] at hz
        exact hpivotNe hz
  have hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin := by
    simpa only [q, score6400SelectedLocatorCramerVector] using
      hpolynomialKer j₀
  have hcard := score6400_ordinaryOnly_polynomialKernel_badSlopeSet_card_le
    f₀ f₁ q hqker hqinr i₀ hi₀ T hbad hnotOld
  calc
    T.card ≤ (q (Sum.inl i₀)).natDegree := hcard
    _ ≤ r * 2130706433 := hdegree j₀ (Sum.inl i₀)
    _ ≤ score6400KernelBasisTotalDegree := by
      have hrle : r ≤ 76781 := by
        have hcardN : Fintype.card Score6400LocatorMinorIndex = 76781 := by
          norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
            locatorFrobeniusRows6400]
        rw [hcardN] at hrank
        omega
      simpa only [score6400KernelBasisTotalDegree] using
        Nat.mul_le_mul_right 2130706433 hrle

end ProximityPrize.SubmissionLower
