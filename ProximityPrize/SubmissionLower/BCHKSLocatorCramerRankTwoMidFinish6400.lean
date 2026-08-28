import ProximityPrize.SubmissionLower.BCHKSLocatorCramerRankTwoAssembly6400
import ProximityPrize.SubmissionLower.BCHKSLocatorContainerAlignment6400
import ProximityPrize.SubmissionLower.BCHKSUniversalConcreteShiftCaps

/-!
# Exact-incidence finish for locator rank two at nullity two through ten

The rooted Cramer obstruction is evaluated at every Reed--Solomon domain
coordinate, leaving a univariate polynomial in the challenge.  Exact
incidence produces a fixed set of at least `49634` identically vanishing
coordinates.  This file then prepares the fixed container and residual root
sets consumed by the checked affine-alignment finish, through outer degree
`76780`.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

/-- Evaluate the outer variable of a bivariate Cramer obstruction at one
Reed--Solomon domain coordinate. -/
noncomputable def score6400CramerCoordinateObstruction
    (Δ : IRSProfile.Field[X][X]) (i : IRSProfile.Index) :
    IRSProfile.Field[X] :=
  Δ.eval (Polynomial.C (IRSProfile.domain i))

/-- Challenge evaluation of the coordinate obstruction agrees with first
specializing the bivariate coefficient variable. -/
theorem score6400CramerCoordinateObstruction_eval
    (Δ : IRSProfile.Field[X][X]) (i : IRSProfile.Index)
    (z : IRSProfile.Field) :
    (score6400CramerCoordinateObstruction Δ i).eval z =
      (Δ.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) := by
  exact (eval_map_eval_eq_eval_eval_C
    Δ (IRSProfile.domain i) z).symm

/-- A uniform cap on all coefficient degrees bounds the first-variable degree
of a bivariate polynomial. -/
theorem bivariate_degreeX_le_of_coeff_natDegree_le
    {F : Type} [Field F] (P : F[X][X]) (S : ℕ)
    (hcoeff : ∀ n, (P.coeff n).natDegree ≤ S) :
    Polynomial.Bivariate.degreeX P ≤ S := by
  unfold Polynomial.Bivariate.degreeX
  exact Finset.sup_le fun n hn ↦ hcoeff n

theorem score6400CramerCoordinateObstruction_natDegree_le
    (Δ : IRSProfile.Field[X][X]) (S : ℕ)
    (hcoeff : ∀ n, (Δ.coeff n).natDegree ≤ S)
    (i : IRSProfile.Index) :
    (score6400CramerCoordinateObstruction Δ i).natDegree ≤ S := by
  exact (UniversalNumerator.natDegree_eval_C_le_degreeX
      Δ (IRSProfile.domain i)).trans
    (bivariate_degreeX_le_of_coeff_natDegree_le Δ S hcoeff)

/-- The doubled candidate cap still has ample exact-incidence room. -/
theorem score6400_twenty_kernelBasis_budgets_incidence
    (tcard : ℕ) (ht : 174972148031419760 < tcard) :
    262144 * (20 * score6400KernelBasisTotalDegree) <
      (76771 - 49633) * tcard := by
  norm_num [score6400KernelBasisTotalDegree] at ht ⊢
  nlinarith

/-- Common rooted specializations of a nonzero bivariate obstruction produce
a fixed container.  Its upper bound follows by root counting over the
coefficient domain `F[z]`, not by assuming the container consists of errors. -/
theorem exists_score6400_fixed_container_of_rooted_obstruction
    (Δ : IRSProfile.Field[X][X]) (hΔne : Δ ≠ 0)
    (hΔcoeff : ∀ n, (Δ.coeff n).natDegree ≤
      20 * score6400KernelBasisTotalDegree)
    (T : Finset IRSProfile.Field)
    (hT : 174972148031419760 < T.card)
    (E : IRSProfile.Field → Finset IRSProfile.Index)
    (hEcard : ∀ z ∈ T, 76771 ≤ (E z).card)
    (hroot : ∀ z ∈ T, ∀ i ∈ E z,
      (Δ.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0) :
    ∃ Container : Finset IRSProfile.Index,
      Container = Finset.univ.filter (fun i =>
        score6400CramerCoordinateObstruction Δ i = 0) ∧
      49634 ≤ Container.card ∧ Container.card ≤ Δ.natDegree := by
  classical
  let G : IRSProfile.Index → IRSProfile.Field[X] :=
    score6400CramerCoordinateObstruction Δ
  let Container : Finset IRSProfile.Index :=
    Finset.univ.filter fun i => G i = 0
  have hGdegree : ∀ i,
      (G i).natDegree ≤ 20 * score6400KernelBasisTotalDegree := by
    intro i
    exact score6400CramerCoordinateObstruction_natDegree_le
      Δ (20 * score6400KernelBasisTotalDegree) hΔcoeff i
  have hGroot : ∀ z ∈ T, ∀ i ∈ E z, (G i).eval z = 0 := by
    intro z hz i hi
    rw [show G i = score6400CramerCoordinateObstruction Δ i by rfl,
      score6400CramerCoordinateObstruction_eval]
    exact hroot z hz i hi
  have hContainerLower : 49634 ≤ Container.card := by
    obtain ⟨z, hzT, hzlarge⟩ :=
      exists_many_zero_obstruction_agreements
        T E G 262144 76771 49633
          (20 * score6400KernelBasisTotalDegree)
        (by norm_num [IRSProfile.Index]) hEcard
        (fun z hz i hi ↦ Or.inr (hGroot z hz i hi)) hGdegree
        (score6400_twenty_kernelBasis_budgets_incidence T.card hT)
    have hsub : (E z).filter (fun i ↦ G i = 0) ⊆
        Finset.univ.filter (fun i : IRSProfile.Index ↦ G i = 0) := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    simpa only [Container] using hzlarge.trans (Finset.card_le_card hsub)
  have hContainerUpper : Container.card ≤ Δ.natDegree := by
    by_contra hlarge
    have hdegree : Δ.natDegree < Container.card := by omega
    let domainC : IRSProfile.Index ↪ IRSProfile.Field[X] :=
      ⟨fun i ↦ Polynomial.C (IRSProfile.domain i), by
        intro i j hij
        apply IRSProfile.domain.injective
        exact Polynomial.C_injective hij⟩
    let Roots : Finset IRSProfile.Field[X] := Container.map domainC
    apply hΔne
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Δ Roots
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      have hiZero : G i = 0 := (Finset.mem_filter.mp hi).2
      change Δ.eval (Polynomial.C (IRSProfile.domain i)) = 0
      simpa only [G, score6400CramerCoordinateObstruction] using hiZero
    · simpa only [Roots, Finset.card_map] using hdegree
  exact ⟨Container, rfl, hContainerLower, hContainerUpper⟩

/-- Removing the roots of a nonzero challenge polynomial costs at most its
degree.  This local form keeps the mid-nullity finish independent of the
older Frobenius branch. -/
theorem card_le_filter_polynomial_eval_ne_zero_add_natDegree
    {F : Type} [Field F] [DecidableEq F]
    (T : Finset F) (P : F[X]) (hP : P ≠ 0) :
    T.card ≤ (T.filter (fun z ↦ P.eval z ≠ 0)).card + P.natDegree := by
  have hzero :
      (T.filter (fun z ↦ P.eval z = 0)).card ≤ P.natDegree := by
    have hsubset : T.filter (fun z ↦ P.eval z = 0) ⊆
        P.roots.toFinset := by
      intro z hz
      have hzZero := (Finset.mem_filter.mp hz).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hzZero
    exact (Finset.card_le_card hsubset).trans
      (Multiset.toFinset_card_le P.roots |>.trans
        (Polynomial.card_roots' P))
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun z ↦ P.eval z ≠ 0) (s := T)
  have hzero' :
      (T.filter (fun z ↦ ¬P.eval z ≠ 0)).card ≤ P.natDegree := by
    simpa only [not_ne_iff] using hzero
  omega

/-- A nonvanishing evaluated coefficient witnesses that coefficientwise
specialization of the outer polynomial is nonzero. -/
theorem polynomial_map_ne_zero_of_coeff_eval_ne_zero
    {F : Type} [Field F] (P : F[X][X]) (n : ℕ) (z : F)
    (hcoeff : (P.coeff n).eval z ≠ 0) :
    P.map (Polynomial.evalRingHom z) ≠ 0 := by
  intro hzero
  have hcoeffZero := congrArg (fun Q : F[X] ↦ Q.coeff n) hzero
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hcoeffZero
  change (P.coeff n).eval z = 0 at hcoeffZero
  exact hcoeff hcoeffZero

/-- A nonzero univariate polynomial has at most its degree many roots among
the injective Reed--Solomon evaluation coordinates. -/
theorem score6400_domain_rootSet_card_le_natDegree
    (P : IRSProfile.Field[X]) (hP : P ≠ 0) :
    (Finset.univ.filter (fun i : IRSProfile.Index ↦
      P.eval (IRSProfile.domain i) = 0)).card ≤ P.natDegree := by
  classical
  by_contra hlarge
  let S : Finset IRSProfile.Index := Finset.univ.filter fun i ↦
    P.eval (IRSProfile.domain i) = 0
  let Roots : Finset IRSProfile.Field := S.map IRSProfile.domain
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Roots
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact (Finset.mem_filter.mp hi).2
  · have hdegree : P.natDegree < S.card := by
      simpa only [S] using Nat.lt_of_not_ge hlarge
    simpa only [Roots, Finset.card_map] using hdegree

/-- The natural-degree form used by the score-64 Reed--Solomon encoder. -/
theorem score6400_degree_lt_baseDimension_of_natDegree_lt
    {P : IRSProfile.Field[X]} (hP : P.natDegree < 131072) :
    P.degree < (IRSProfile.baseDimension : WithBot ℕ) := by
  by_cases hzero : P = 0
  · simp [hzero]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hzero]
    norm_num [IRSProfile.baseDimension] at hP ⊢
    exact hP

/-- Any nonzero rooted Cramer obstruction with outer degree at most `76780`
closes its entire new score-64 bad-slope set.  The proof keeps only the
specializations where the leading outer coefficient survives, extracts the
fixed coordinate container, and applies affine Reed--Solomon alignment to
the residual roots. -/
theorem score6400_rootedCramerObstruction_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Δ : IRSProfile.Field[X][X]) (hΔne : Δ ≠ 0)
    (hΔdegree : Δ.natDegree < 76781)
    (hΔcoeff : ∀ n, (Δ.coeff n).natDegree ≤
      20 * score6400KernelBasisTotalDegree)
    (hΔroots : ∀ z : IRSProfile.Field,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z →
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z →
      Nonempty (Score6400RootedCramerObstructionData f₀ f₁ z Δ))
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ 174972148031419760 := by
  classical
  by_contra hTsmall
  have hTlarge : 174972148031419760 < T.card := by omega
  let data : (z : {z // z ∈ T}) →
      Score6400RootedCramerObstructionData f₀ f₁ z.1 Δ :=
    fun z ↦ Classical.choice
      (hΔroots z.1 (hbad z.1 z.2) (hnotOld z.1 z.2))
  let E : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    if hz : z ∈ T then (data ⟨z, hz⟩).errorSet else ∅
  have hEcard : ∀ z ∈ T, 76771 ≤ (E z).card := by
    intro z hz
    rw [show E z = (data ⟨z, hz⟩).errorSet by simp [E, hz]]
    exact (data ⟨z, hz⟩).errorSet_large
  have hEroot : ∀ z ∈ T, ∀ i ∈ E z,
      (Δ.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0 := by
    intro z hz i hi
    rw [show E z = (data ⟨z, hz⟩).errorSet by simp [E, hz]] at hi
    exact (data ⟨z, hz⟩).obstruction_roots i hi
  obtain ⟨C, hCeq, hClower, hCupper⟩ :=
    exists_score6400_fixed_container_of_rooted_obstruction
      Δ hΔne hΔcoeff T hTlarge E hEcard hEroot
  have hCupper' : C.card ≤ 76780 := hCupper.trans (by omega)
  let a : IRSProfile.Field[X] := Δ.coeff Δ.natDegree
  have ha : a ≠ 0 := by
    dsimp only [a]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hΔne
  let Good : Finset IRSProfile.Field :=
    T.filter fun z ↦ a.eval z ≠ 0
  have hGoodT : Good ⊆ T := Finset.filter_subset _ _
  have hGoodCount :=
    card_le_filter_polynomial_eval_ne_zero_add_natDegree T a ha
  change T.card ≤ Good.card + a.natDegree at hGoodCount
  have hadegree : a.natDegree ≤
      20 * score6400KernelBasisTotalDegree := by
    simpa only [a] using hΔcoeff Δ.natDegree
  have hGoodLarge : 76781 < Good.card := by
    norm_num [score6400KernelBasisTotalDegree] at hadegree
    omega
  have hspecialNe : ∀ z ∈ Good,
      Δ.map (Polynomial.evalRingHom z) ≠ 0 := by
    intro z hz
    apply polynomial_map_ne_zero_of_coeff_eval_ne_zero
      Δ Δ.natDegree z
    have hzGood := (Finset.mem_filter.mp hz).2
    simpa only [a] using hzGood
  let goodData : (z : {z // z ∈ Good}) →
      Score6400RootedCramerObstructionData f₀ f₁ z.1 Δ :=
    fun z ↦ data ⟨z.1, hGoodT z.2⟩
  let RootSet : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    Finset.univ.filter fun i ↦
      (Δ.map (Polynomial.evalRingHom z)).eval
        (IRSProfile.domain i) = 0
  let R : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    RootSet z \ C
  let A : IRSProfile.Field → Finset IRSProfile.Index := fun z ↦
    if hz : z ∈ Good then (goodData ⟨z, hz⟩).agreementSet else ∅
  let P : IRSProfile.Field → IRSProfile.Field[X] := fun z ↦
    if hz : z ∈ Good then (goodData ⟨z, hz⟩).polynomial else 0
  have hCroot : ∀ z, C ⊆ RootSet z := by
    intro z i hi
    rw [hCeq] at hi
    have hiCoordinate := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    rw [← score6400CramerCoordinateObstruction_eval Δ i z,
      hiCoordinate, Polynomial.eval_zero]
  have hRootCard : ∀ z ∈ Good,
      (RootSet z).card ≤ Δ.natDegree := by
    intro z hz
    calc
      (RootSet z).card ≤
          (Δ.map (Polynomial.evalRingHom z)).natDegree := by
        simpa only [RootSet] using
          score6400_domain_rootSet_card_le_natDegree
            (Δ.map (Polynomial.evalRingHom z)) (hspecialNe z hz)
      _ ≤ Δ.natDegree := Polynomial.natDegree_map_le
  have hRcard : ∀ z ∈ Good, (R z).card ≤ 76780 - C.card := by
    intro z hz
    have hpartition := Finset.card_sdiff_add_card_eq_card (hCroot z)
    have hcap := hRootCard z hz
    change (RootSet z \ C).card ≤ 76780 - C.card
    omega
  have hAeq : ∀ z (hz : z ∈ Good),
      A z = (goodData ⟨z, hz⟩).agreementSet := by
    intro z hz
    simp only [A, dif_pos hz]
  have hPeq : ∀ z (hz : z ∈ Good),
      P z = (goodData ⟨z, hz⟩).polynomial := by
    intro z hz
    simp only [P, dif_pos hz]
  have hAcard : ∀ z ∈ Good,
      Fintype.card IRSProfile.Index - 76780 ≤ (A z).card := by
    intro z hz
    rw [hAeq z hz]
    norm_num [IRSProfile.Index]
    exact (goodData ⟨z, hz⟩).agreementSet_large
  have hPdegree : ∀ z ∈ Good, (P z).natDegree < 131072 := by
    intro z hz
    rw [hPeq z hz]
    exact (goodData ⟨z, hz⟩).polynomial_degree.trans_lt (by norm_num)
  have hPagree : ∀ z ∈ Good, ∀ i ∈ A z,
      (P z).eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro z hz i hi
    rw [hAeq z hz] at hi
    rw [hPeq z hz]
    exact (goodData ⟨z, hz⟩).agreement i hi
  have houtside : ∀ z ∈ Good, ∀ i, i ∉ C → i ∉ R z →
      (P z).eval (IRSProfile.domain i) = f₀ i + z * f₁ i := by
    intro z hz i hiC hiR
    rw [hPeq z hz]
    let d := goodData ⟨z, hz⟩
    have hiNotError : i ∉ d.errorSet := by
      intro hiError
      apply hiR
      refine Finset.mem_sdiff.mpr ⟨?_, hiC⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      exact d.obstruction_roots i hiError
    have hnot : ¬((f₀ i + z * f₁ i) -
        d.polynomial.eval (IRSProfile.domain i) ≠ 0) := by
      rw [d.errorSet_eq] at hiNotError
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hiNotError
    have heq : (f₀ i + z * f₁ i) -
        d.polynomial.eval (IRSProfile.domain i) = 0 := not_ne_iff.mp hnot
    exact (sub_eq_zero.mp heq).symm
  have htwo : 1 < Good.card := by omega
  obtain ⟨z₀, hz₀, z₁, hz₁, hzne⟩ := Finset.one_lt_card.mp htwo
  have hroom : 131072 + C.card + 3 * (76780 - C.card) ≤
      Fintype.card IRSProfile.Index := by
    norm_num [IRSProfile.Index]
    omega
  obtain ⟨p₀, p₁, hp₀, hp₁, z, hz, hcommon⟩ :=
    exists_common_pair_agreement_of_fixed_error_container
      IRSProfile.domain Good A P f₀ f₁ C R
        131072 (76780 - C.card) 76780 z₀ z₁ hz₀ hz₁ hzne
        (by simpa using hGoodLarge) hAcard hPdegree hPagree hRcard
        houtside hroom
  let d := goodData ⟨z, hz⟩
  have hAz : A z = d.agreementSet := by
    simpa only [d] using hAeq z hz
  apply d.unexplainedPair
  refine ⟨ReedSolomon.evalOnPoints IRSProfile.domain p₀, ?_,
    ReedSolomon.evalOnPoints IRSProfile.domain p₁, ?_, ?_, ?_⟩
  · change ReedSolomon.evalOnPoints IRSProfile.domain p₀ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact score6400_degree_lt_baseDimension_of_natDegree_lt hp₀
  · change ReedSolomon.evalOnPoints IRSProfile.domain p₁ ∈
      ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension
    apply ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    exact score6400_degree_lt_baseDimension_of_natDegree_lt hp₁
  · intro i hi
    change p₀.eval (IRSProfile.domain i) = f₀ i
    exact (hcommon i (hAz.symm ▸ hi)).1.symm
  · intro i hi
    change p₁.eval (IRSProfile.domain i) = f₁ i
    exact (hcommon i (hAz.symm ▸ hi)).2.symm

/-- The exact-incidence `2 ≤ L ≤ 10` rational-rank-two branch is therefore
completely bounded by the new score-64 slope budget. -/
theorem score6400_midNullity_rankTwo_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlower : 2 ≤ L) (hLupper : L ≤ 10)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ 174972148031419760 := by
  obtain ⟨Δ, hΔne, hΔdegree, hΔcoeff, hΔroots⟩ :=
    exists_score6400_midNullity_rankTwo_obstruction
      f₀ f₁ L hkernelRank hLlower hLupper hrankTwo
  exact score6400_rootedCramerObstruction_badSlopeSet_card_le
    f₀ f₁ Δ hΔne hΔdegree hΔcoeff hΔroots T hbad hnotOld

/-- Consolidated rational-rank-two endpoint for every possible generic
nullity at least two. -/
theorem score6400_rankTwo_badSlopeSet_card_le
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : ℕ)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlower : 2 ≤ L) (hLupper : L ≤ 76781)
    (hrankTwo : ∃ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 ≠ 0)
    (T : Finset IRSProfile.Field)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    T.card ≤ 174972148031419760 := by
  by_cases hmid : L ≤ 10
  · exact score6400_midNullity_rankTwo_badSlopeSet_card_le
      f₀ f₁ L hkernelRank hLlower hmid hrankTwo T hbad hnotOld
  · have hlarge : 11 ≤ L := by omega
    have hbound := score6400_largeNullity_rankTwo_badSlopeSet_card_le
      f₀ f₁ L hkernelRank hlarge hLupper hrankTwo T hbad hnotOld
    calc
      T.card ≤ 20 * score6400KernelBasisTotalDegree := hbound
      _ ≤ 174972148031419760 := by
        norm_num [score6400KernelBasisTotalDegree]

end ProximityPrize.SubmissionLower
