import ProximityPrize.SubmissionBinaryLower.BCHKSSingleFactorGood
import ProximityPrize.SubmissionBinaryLower.BCHKSPrimitiveEffectiveResultant
import ProximityPrize.SubmissionBinaryLower.BCHKSFactorXDegree
import ProximityPrize.SubmissionBinaryLower.BCHKSPairSetup
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalPairFiberBridge6399
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalSelectedPairCore
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalNumeratorFunctionField
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalConcreteObstruction
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalGlobalCapacity
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalFactorSums
import ProximityPrize.SubmissionBinaryLower.BCHKSUniversalResultantSelection

/-!
# Single-factor alignment through the universal numerator ledger

For one separable irreducible factor `R` at Frobenius level `q`, choose a good
specialization `x₀` and charge every positive factor `H` of `R(x₀, Y, Z)` with
the degree of the ordinary resultant of `H` against the universal affine
obstruction.  These resultant degrees add up to at most `2 E d D` over all `H`,
so the per-factor capacity is linear in `d = deg_Y R` with the fused incidence
coefficient `uC`.  The selected pair then aligns through the universal
function-field core, with no split on the degree of `R`.
-/

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark Polynomial Polynomial.Bivariate
open RationalFunctions RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open UniversalOuterCover6399 UniversalPairFiberBridge6399 UniversalNumerator

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- The universal-numerator exponent `2k - 1`. -/
def uE : ℕ := 2097149
/-- `Z`-degree cap of a selected factor. -/
def uDZ : ℕ := 21907324
/-- `n - k`. -/
def uNK : ℕ := 1048577
/-- `n - e - k`. -/
def uGap : ℕ := 434335
/-- Fused incidence coefficient: `(n - k) * 2E ≤ (n - e - k) * uC`. -/
def uC : ℕ := 10125927

theorem uE_eq : uE = FiniteHenselWeight.denominatorExponent 1048575 := by
  norm_num [uE, FiniteHenselWeight.denominatorExponent]

theorem u_fused : uNK * (2 * uE) ≤ uGap * uC := by
  norm_num [uNK, uE, uGap, uC]

/-- Capacity of a separable factor of `Y`-degree `d` in the universal ledger. -/
def sfCapU (d : ℕ) : ℕ :=
  uC * uDZ * d + (bchksErrors + 1) * d + 2 * d * uDZ

theorem sfCapU_mono {a b : ℕ} (h : a ≤ b) : sfCapU a ≤ sfCapU b := by
  unfold sfCapU
  have h3 : 2 * a * uDZ ≤ 2 * b * uDZ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
  have h4 : (bchksErrors + 1) * a ≤ (bchksErrors + 1) * b := Nat.mul_le_mul_left _ h
  have h5 : uC * uDZ * a ≤ uC * uDZ * b := Nat.mul_le_mul_left _ h
  omega

theorem u_fused_mul (d : ℕ) :
    uNK * (2 * uE * d * uDZ) ≤ uGap * (uC * uDZ * d) := by
  calc
    uNK * (2 * uE * d * uDZ) = (uNK * (2 * uE)) * (d * uDZ) := by ring
    _ ≤ (uGap * uC) * (d * uDZ) := Nat.mul_le_mul_right _ u_fused
    _ = uGap * (uC * uDZ * d) := by ring

/-- Pair setup for one irreducible factor, without an ambient interpolant. -/
theorem setup_selected_pair_single
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hRirr : Irreducible R)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hRdeg : R.natDegree ≤ 6902)
    (hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 21907324)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible H ∧
    H ∣ triSpecializeX R x₀ ∧ H.natDegree ≤ 6902 ∧
    Polynomial.Bivariate.totalDegree H ≤ 21907324 ∧
    RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hHR).irreducible
  have hHd : H ∣ triSpecializeX R x₀ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hHR
  have hRXeq : triSpecializeX R x₀ =
      Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  have hRX0 : triSpecializeX R x₀ ≠ 0 := by
    rw [hRXeq]
    exact hprim.ne_zero
  have hHdeg : H.natDegree ≤ 6902 :=
    (Polynomial.natDegree_le_of_dvd hHd hRX0).trans
      ((triSpecializeX_natDegree_le R x₀).trans hRdeg)
  have hRXtotal : Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 21907324 :=
    totalDegree_triSpecializeX_le R x₀ 21907324 hRYZ
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0) (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul hA hC]
    exact Nat.le_add_right _ _
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hHtotal : Polynomial.Bivariate.totalDegree H ≤ 21907324 :=
    (totalDegree_le_of_dvd hH0 hRX0 hHd).trans hRXtotal
  have hHyp : RationalFunctions.HenselNumerators.Hypotheses x₀ R H := by
    refine ⟨?_, hprim.ne_zero, ?_⟩
    · simpa [hRXeq] using hHd
    · intro Q hfac hQdeg
      let q₀ : Polynomial F := Q.coeff 0
      have hQC : Q = Polynomial.C q₀ :=
        Polynomial.eq_C_of_natDegree_le_zero hQdeg.le
      have hCdvd : Polynomial.C q₀ ∣
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R := by
        refine ⟨H, ?_⟩
        calc
          Polynomial.Bivariate.evalX (Polynomial.C x₀) R = H * Q := hfac
          _ = H * Polynomial.C q₀ := by rw [hQC]
          _ = Polynomial.C q₀ * H := mul_comm _ _
      exact (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprim) q₀ hCdvd
  exact ⟨hHirr, hHd, hHdeg, hHtotal, hHyp⟩

/-- Single-factor alignment for a separable irreducible factor at level `q`,
through the universal numerator ledger. -/
theorem single_factor_alignment_univ
    (q : ℕ) (hq1 : 1 ≤ q) (hqE : q ≤ uE)
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (P : BinaryIRSProfile.Field → BinaryIRSProfile.Field[X])
    (Arow : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (R : Polynomial (Polynomial (Polynomial BinaryIRSProfile.Field)))
    (S : Finset BinaryIRSProfile.Field)
    (hRi : Irreducible R) (hRpos : 0 < R.natDegree) (hRd : R.natDegree ≤ 6901)
    (hsep : R.derivative ≠ 0)
    (hYZs : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + q * j < 21907324)
    (hW : ∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + 1048575 * j < 7236927760)
    (hPdeg : ∀ z ∈ S, (P z).natDegree ≤ 1048575)
    (hvan : ∀ z ∈ S, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ S, 1482910 ≤ (Arow z).card) →
    (hagree : ∀ z ∈ S, ∀ i ∈ Arow z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z ^ q * U 1 i)
    (hcard : sfCapU R.natDegree < S.card) :
    ∃ T : Finset BinaryIRSProfile.Field, T ⊆ S ∧ bchksErrors + 1 < T.card ∧
      ∃ p₀ p₁ : BinaryIRSProfile.Field[X], p₀.natDegree ≤ 1048575 ∧
        p₁.natDegree ≤ 1048575 ∧ ∀ z ∈ T, P z = p₀ + Polynomial.C (z ^ q) * p₁ := by
  classical
  have hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 21907324 := by
    intro j a ha
    have := hYZs j a ha
    nlinarith
  have hYZ : YZCap R uDZ := by
    intro j a ha
    have := hRYZ j a ha
    norm_num [uDZ]
    omega
  -- The primitive-specialization certificate for `R`.
  have hZ : ∀ j, (Polynomial.Bivariate.swap (R.coeff j)).natDegree ≤
      BCHKSConcreteGS.DZ := by
    intro j
    rw [show (Polynomial.Bivariate.swap (R.coeff j)).natDegree =
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap (R.coeff j)) from rfl,
      Polynomial.Bivariate.natDegreeY_swap]
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have hne : ((R.coeff j).coeff a) ≠ 0 := Polynomial.mem_support_iff.mp ha
    have := hRYZ j a hne
    norm_num [BCHKSConcreteGS.DZ] at *
    omega
  have hX : ∀ j, Polynomial.Bivariate.degreeX
      (Polynomial.Bivariate.swap (R.coeff j)) ≤ BCHKSConcreteGS.DX := by
    intro j
    rw [Polynomial.Bivariate.degreeX_swap]
    change (R.coeff j).natDegree ≤ BCHKSConcreteGS.DX
    by_cases hz : R.coeff j = 0
    · simp [hz]
    · have hl := Polynomial.leadingCoeff_ne_zero.mpr hz
      have hw := hW j (R.coeff j).natDegree (by
        rw [Polynomial.coeff_natDegree]
        exact hl)
      norm_num [BCHKSConcreteGS.DX] at *
      omega
  obtain ⟨w, hwdeg⟩ := effectivePrimitiveObstruction_of_irreducible R hRi hRpos hZ hX
  have hfx : (factorXObstruction R).natDegree ≤
      (2 * R.natDegree + 2) * BCHKSConcreteGS.DX := by
    apply factorXObstruction_natDegree_le R BCHKSConcreteGS.DX
    · unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro j hj
      simp only [mapZToRatFunc, Polynomial.coeff_map]
      exact Polynomial.natDegree_map_le.trans (by
        by_cases hz : R.coeff j = 0
        · simp [hz]
        · have := hW j (R.coeff j).natDegree (by
            rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hz)
          norm_num [BCHKSConcreteGS.DX] at *
          omega)
    · by_cases hz : R.leadingCoeff = 0
      · simp [hz]
      · have := hW R.natDegree R.leadingCoeff.natDegree (by
          rw [Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr hz)
        norm_num [BCHKSConcreteGS.DX] at *
        omega
  have hcertDegree : w.obstruction.natDegree + (factorXObstruction R).natDegree <
      Fintype.card BinaryIRSProfile.Field := by
    calc
      w.obstruction.natDegree + (factorXObstruction R).natDegree ≤
          2 * (BCHKSConcreteGS.DZ + 1) * BCHKSConcreteGS.DX +
            (2 * 6902 + 2) * BCHKSConcreteGS.DX := by
        exact Nat.add_le_add hwdeg
          (hfx.trans (Nat.mul_le_mul_right BCHKSConcreteGS.DX (by omega)))
      _ < Fintype.card BinaryIRSProfile.Field := by
        rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ)
          from BF64.card_ext3]
        norm_num [BCHKSConcreteGS.DZ, BCHKSConcreteGS.DX]
  have hevalCap : ∀ x : BinaryIRSProfile.Field,
      ∀ p : Polynomial (Polynomial BinaryIRSProfile.Field),
      Polynomial.Bivariate.degreeX p ≤ 21907324 →
      (Polynomial.eval (Polynomial.C x) p).natDegree ≤ 21907324 := by
    intro x p hpdeg
    have heq : (Polynomial.Bivariate.swap p).map
        (Polynomial.evalRingHom x) = Polynomial.eval (Polynomial.C x) p := by
      rw [← Polynomial.Bivariate.evalX_eq_map]
      exact (Polynomial.Bivariate.evalY_eq_evalX_swap x p).symm
    rw [← heq]
    exact Polynomial.natDegree_map_le.trans (by
      rw [show (Polynomial.Bivariate.swap p).natDegree =
        Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap p) from rfl,
        Polynomial.Bivariate.natDegreeY_swap]
      exact hpdeg)
  have hcoeffCap : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤ 21907324 := by
    intro j
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro a ha
    have := hRYZ j a (Polynomial.mem_support_iff.mp ha)
    omega
  have hBZ : ∀ x : BinaryIRSProfile.Field,
      Polynomial.Bivariate.degreeX (triSpecializeX R x) ≤ 21907324 := by
    intro x
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro j hj
    simp only [triSpecializeX, Polynomial.coeff_map]
    exact hevalCap x (R.coeff j) (hcoeffCap j)
  have hfactorXDegree : ∀ x : BinaryIRSProfile.Field,
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 21907324 := by
    intro x
    apply factorXObstruction_eval_natDegree_le R x R.natDegree 21907324 hRpos (le_refl _)
    · exact hBZ x
    · exact hevalCap x R.leadingCoeff (by
        rw [← Polynomial.coeff_natDegree]
        exact hcoeffCap R.natDegree)
  obtain ⟨x₀, Bad, hBad, hdegEq, hRX0, hprim, hsimple, hobs⟩ :=
    exists_single_factor_good_effective R hRi hRpos hsep w R.natDegree 21907324
      hcertDegree hfactorXDegree
  -- Second stage: the universal resultant ledger over the factors of `R(x₀, Y, Z)`.
  let d := R.natDegree
  let Uset := S \ Bad
  have hUcard : uC * uDZ * d + (bchksErrors + 1) * d < Uset.card := by
    have hc : (Bad ∩ S).card ≤ 2 * d * uDZ :=
      (Finset.card_le_card Finset.inter_subset_left).trans hBad
    have hcap : uC * uDZ * d + (bchksErrors + 1) * d + 2 * d * uDZ < S.card := hcard
    rw [Finset.card_sdiff]
    generalize uC * uDZ * d + (bchksErrors + 1) * d = cA at hcap ⊢
    generalize 2 * d * uDZ = cB at hcap hc
    omega
  let Hs := (UniqueFactorizationMonoid.normalizedFactors
    (triSpecializeX R x₀)).toFinset.filter fun H => 0 < H.natDegree
  let Rel : BinaryIRSProfile.Field → BiPoly → Prop := fun z H => pairRel P x₀ z (R, H)
  have hcover : ∀ z ∈ Uset, ∃ H ∈ Hs, Rel z H := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hzBad : z ∉ Bad := (Finset.mem_sdiff.mp hz).2
    have hpoint : biEval (triSpecializeX R x₀) (Polynomial.eval x₀ (P z)) z = 0 := by
      rw [← eval_triEval_eq_biEval_triSpecializeX, hvan z hzS]
      simp
    have hsec : biSpecializeZ (triSpecializeX R x₀) z ≠ 0 := by
      intro heq
      have hs := hsimple z hzBad 0
      have hder : triSpecializeX R.derivative x₀ =
          (triSpecializeX R x₀).derivative := by
        simp [triSpecializeX, Polynomial.derivative_map]
      have hd : biSpecializeZ (triSpecializeX R.derivative x₀) z = 0 := by
        rw [hder]
        simpa [biSpecializeZ, Polynomial.derivative_map] using
          congrArg Polynomial.derivative heq
      exact (hs (by rw [heq]; simp)) (by rw [hd]; simp)
    obtain ⟨H, hHR, hHpos, hHzero⟩ :=
      exists_positive_normalizedFactor_biEval_eq_zero
        (triSpecializeX R x₀) z (Polynomial.eval x₀ (P z)) hsec hpoint
    exact ⟨H, by simp [Hs, hHR, hHpos], hvan z hzS, hHzero, hobs z hzBad, hsec⟩
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le
    (triSpecializeX R x₀) hRX0
  have hHsum : (∑ H ∈ Hs, H.natDegree) ≤ d :=
    hsums.1.trans (triSpecializeX_natDegree_le R x₀)
  have hHZsum : (∑ H ∈ Hs, Polynomial.Bivariate.degreeX H) ≤ uDZ :=
    hsums.2.trans (hBZ x₀)
  have hHcard : Hs.card ≤ d := by
    calc
      Hs.card = ∑ H ∈ Hs, 1 := by simp
      _ ≤ ∑ H ∈ Hs, H.natDegree := by
        exact Finset.sum_le_sum fun H hH => (Finset.mem_filter.mp hH).2
      _ ≤ d := hHsum
  let rdeg : BiPoly → ℕ := fun H =>
    H.natDegree * (uE * uDZ) + (uE * d) * Polynomial.Bivariate.degreeX H
  have hresult : (∑ H ∈ Hs, rdeg H) ≤ 2 * uE * d * uDZ := by
    calc
      (∑ H ∈ Hs, rdeg H) = (∑ H ∈ Hs, H.natDegree) * (uE * uDZ) +
          (uE * d) * (∑ H ∈ Hs, Polynomial.Bivariate.degreeX H) := by
        simp [rdeg, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ ≤ d * (uE * uDZ) + (uE * d) * uDZ := by gcongr
      _ = 2 * uE * d * uDZ := by ring
  have hsumcap := sum_scaled_pair_capacities_le_of_fused Hs rdeg uNK uGap
    bchksErrors (2 * uE * d * uDZ) d (uC * uDZ * d) hresult hHcard (u_fused_mul d)
  obtain ⟨H, hHs, hHfib⟩ :=
    exists_rel_fiber_gt_capacity Uset Hs Rel
      (fun H => (uNK * rdeg H) / uGap + (bchksErrors + 1)) hcover
      (hsumcap.trans_lt hUcard)
  let T := Uset.filter fun z => Rel z H
  have hbounds := scaled_pair_capacity_implies_incidence uNK uGap (rdeg H)
    bchksErrors T.card (by norm_num [uGap]) hHfib
  have hTS : T ⊆ S := fun z hz => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hrel : ∀ z ∈ T, Rel z H := fun z hz => (Finset.mem_filter.mp hz).2
  have hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) := by
    simpa [Hs] using (Finset.mem_filter.mp hHs).1
  have hHpos : 0 < H.natDegree := (Finset.mem_filter.mp hHs).2
  have hprim' : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive := by
    rw [Polynomial.Bivariate.evalX_eq_map]
    exact hprim
  obtain ⟨hHirr, hHd, -, -, hHyp⟩ :=
    setup_selected_pair_single R H x₀ hRi hHR hHpos (hRd.trans (by norm_num)) hRYZ hprim'
  -- Coordinates whose fibers beat the resultant degree.
  let Coord : Finset BinaryIRSProfile.Index := Finset.univ.filter fun i =>
    rdeg H < (T.filter fun z => i ∈ Arow z).card
  have hCoord : 1048576 ≤ Coord.card := by
    have h := many_large_fibers T Arow 2097152 614242 1048575 (rdeg H)
      BinaryIRSProfile.card_index
      (fun z hz => by have := hrow z (hTS hz); norm_num; exact this)
      (by
        have h1 := hbounds.1
        simp only [uNK, uGap] at h1
        norm_num
        linarith)
    simpa [Coord] using h
  let G : BinaryIRSProfile.Index → BiPoly := fun i =>
    concreteUniversalAffineObstruction x₀ R uE 1048575
      (BinaryIRSProfile.domain i - x₀) (U 0 i) (U 1 i) q
  have hGcaps : ∀ i, (G i).natDegree ≤ uE * d ∧
      Polynomial.Bivariate.degreeX (G i) ≤ uE * uDZ := by
    intro i
    exact concreteUniversalAffineObstruction_degree_bounds x₀ R uE 1048575 d uDZ
      (BinaryIRSProfile.domain i - x₀) (U 0 i) (U 1 i) q hqE uE_eq
      (by norm_num) hRpos (by norm_num [uDZ]) hRpos le_rfl hYZ
  let Res : BinaryIRSProfile.Index → BinaryIRSProfile.Field[X] := fun i =>
    Polynomial.resultant (G i) H (G i).natDegree H.natDegree
  have hResdeg : ∀ i, (Res i).natDegree ≤ rdeg H := by
    intro i
    have hg := hGcaps i
    calc
      (Res i).natDegree ≤
          H.natDegree * Polynomial.Bivariate.degreeX (G i) +
            (G i).natDegree * Polynomial.Bivariate.degreeX H :=
        bivariate_resultant_natDegree_le (G i) H (G i).natDegree H.natDegree
      _ ≤ H.natDegree * (uE * uDZ) +
          (uE * d) * Polynomial.Bivariate.degreeX H := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left H.natDegree hg.2)
          (Nat.mul_le_mul_right (Polynomial.Bivariate.degreeX H) hg.1)
  have hsimpleSlope : ∀ z ∈ T, FiniteHensel.ySlope
      (triSpecializeZ R z) x₀ ((P z).eval x₀) ≠ 0 := by
    intro z hz
    exact simple_slope_of_pairRel P x₀ z R H (hrel z hz) hdegEq hRpos
  have hResroot : ∀ i, ∀ z ∈ T, i ∈ Arow z → (Res i).eval z = 0 := by
    intro i z hzT hiz
    have hpair := hrel z hzT
    have hGroot : biEval (G i) (Polynomial.eval x₀ (P z)) z = 0 := by
      apply biEval_concreteUniversalAffineObstruction_eq_zero
        x₀ z (Polynomial.eval x₀ (P z)) R (P z) uE 1048575
        (BinaryIRSProfile.domain i - x₀) (U 0 i) (U 1 i) q uE_eq hRpos rfl
        (hPdeg z (hTS hzT)) hpair.1 (hsimpleSlope z hzT)
      simpa using hagree z (hTS hzT) i hiz
    exact bivariate_resultant_eval_eq_zero_of_common_root
      (G i) H (G i).natDegree H.natDegree z (Polynomial.eval x₀ (P z))
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le
      (Nat.add_pos_right _ hHpos) hGroot hpair.2.1
  have hdiv : ∀ i ∈ Coord, H ∣ G i := by
    intro i hi
    have hlarge := (Finset.mem_filter.mp hi).2
    have hzero : Res i = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        (Res i) (T.filter fun z => i ∈ Arow z)
      · intro z hz
        exact hResroot i z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
      · exact (hResdeg i).trans_lt hlarge
    exact irreducible_dvd_of_resultant_eq_zero_nonmonic (G i) H hHirr hHpos
      (by simpa only [Res] using hzero)
  -- The selected pair aligns through the universal function-field core.
  haveI : Fact (Irreducible H) := ⟨hHirr⟩
  haveI : Fact (0 < H.natDegree) := ⟨hHpos⟩
  let PT : T → BinaryIRSProfile.Field[X] := fun z => P z
  have hPTdeg : ∀ z : T, (PT z).natDegree ≤ 1048575 :=
    fun z => hPdeg z (hTS z.property)
  have hExact : ∀ z : T, (triSpecializeZ R (z : BinaryIRSProfile.Field)).eval (PT z) = 0 :=
    fun z => (hrel z z.property).1
  have hfactor : ∀ z : T,
      Polynomial.evalEval (z : BinaryIRSProfile.Field) ((PT z).eval x₀) H = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C H ((PT z).eval x₀)
      (z : BinaryIRSProfile.Field)).symm.trans (hrel z z.property).2.1
  have hWz : ∀ z : T, H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0 := by
    intro z
    have hparts := obstruction_seed_parts x₀ (z : BinaryIRSProfile.Field) R
      (hrel z z.property).2.2.1
    exact inner_leadingCoeff_eval_ne_zero x₀ (z : BinaryIRSProfile.Field)
      R H hdegEq hHd hparts.1
  let root : ∀ z : T, rationalRoot (monicize H) (z : BinaryIRSProfile.Field) :=
    fun z => rationalRootOfPair H hHpos (z : BinaryIRSProfile.Field)
      ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : T, GoodAt (z : BinaryIRSProfile.Field) (root z)
      (fieldTo𝕃 (H := H) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H := H) (z : BinaryIRSProfile.Field) (root z) x₀
  have hy : ∀ z : T, GoodAt (z : BinaryIRSProfile.Field) (root z)
      (initialValue (H := H)) ((PT z).eval x₀) := by
    intro z
    have hTval : GoodAt (z : BinaryIRSProfile.Field) (root z)
        (functionFieldT (H := H))
        (H.leadingCoeff.eval (z : BinaryIRSProfile.Field) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair H hHpos (z : BinaryIRSProfile.Field)
            ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H := H)
      (z : BinaryIRSProfile.Field) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (hWz z)] using
      GoodAt.div hTval hWgood (hWz z)
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by have := hbounds.2; omega)
  let z₀ : T := ⟨Classical.choose hTnonempty, Classical.choose_spec hTnonempty⟩
  have hzeta : zeta R x₀ H ≠ 0 :=
    zeta_ne_zero_of_selected_slope x₀ R (z₀ : BinaryIRSProfile.Field)
      (root z₀) x₀ ((PT z₀).eval x₀) (hx z₀) (hy z₀)
      (hsimpleSlope z₀ z₀.property)
  have hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp
      (z : BinaryIRSProfile.Field) (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ R hHyp hzeta (z : BinaryIRSProfile.Field)
      (root z) x₀ ((PT z).eval x₀) (hx z) (hy z) (hWz z)
      (hsimpleSlope z z.property)
  have hsimpleAt : ∀ z : T, FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R (z : BinaryIRSProfile.Field)) x₀ ((PT z).eval x₀) := by
    intro z
    refine ⟨?_, hsimpleSlope z z.property⟩
    have hz := congrArg (Polynomial.eval x₀) (hExact z)
    calc
      (triSpecializeZ R (z : BinaryIRSProfile.Field)).eval₂
          (Polynomial.evalRingHom x₀) ((PT z).eval x₀) =
          (Polynomial.evalRingHom x₀)
            ((triSpecializeZ R (z : BinaryIRSProfile.Field)).eval (PT z)) := by
        exact (Polynomial.hom_eval₂
          (triSpecializeZ R (z : BinaryIRSProfile.Field)) (RingHom.id _)
          (Polynomial.evalRingHom x₀) (PT z)).symm
      _ = 0 := by simpa using hz
  let Sel : UniversalSelectedHenselData x₀ R H hHyp hzeta
      uDZ d 1048575 1048576 T PT := {
    root := root
    hx := hx
    hy := hy
    hsL := (hNP z₀).hsL
    hsimple := hsimpleAt
    hExact := hExact
    hslope := fun z => (hNP z).hslope
    hW := hWz
    hxi := fun z => (hNP z).hxi }
  let Afield : Finset BinaryIRSProfile.Field := Coord.image BinaryIRSProfile.domain
  have hAfield : 1048575 + 1 ≤ Afield.card := by
    have hc : Afield.card = Coord.card :=
      Finset.card_image_iff.mpr fun a _ b _ hab => BinaryIRSProfile.domain.injective hab
    rw [hc]
    exact hCoord
  let idx : Afield → BinaryIRSProfile.Index := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Afield) : idx x ∈ Coord ∧
      BinaryIRSProfile.domain (idx x) = (x : BinaryIRSProfile.Field) := by
    exact Classical.choose_spec (Finset.mem_image.mp x.property)
  let U₀ : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hxA : x ∈ Afield then U 0 (idx ⟨x, hxA⟩) else 0
  let U₁ : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hxA : x ∈ Afield then U 1 (idx ⟨x, hxA⟩) else 0
  have hs : Polynomial.eval₂ (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) = zeta R x₀ H := by
    change evalUniversal (liftToFunctionField (H := H))
      (initialValue (H := H)) (universalSlope x₀ R) = _
    rw [universalSlope_evalUniversal]
    simpa [liftedR, fieldTo𝕃] using
      (ySlope_liftedR_eq_zeta (R := R) (H := H) x₀)
  have hnum : ∀ i, i ≤ 1048575 →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (universalRootedNumerators x₀ R i) =
        finiteAlpha (R := R) (H := H) x₀ 1048576 i *
          zeta R x₀ H ^ FiniteHenselWeight.denominatorExponent i := by
    intro i hi
    exact eval₂_universalRootedNumerators_eq_finiteAlpha_mul_zeta_pow
      x₀ R hHyp hzeta 1048576 i (by omega)
  have hzero : ∀ x ∈ Afield,
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H))
          (universalAffineObstruction (universalRootedNumerators x₀ R)
            (universalSlope x₀ R) uE 1048575
            (x - x₀) (U₀ x) (U₁ x) q) = 0 := by
    intro x hxA
    let xx : Afield := ⟨x, hxA⟩
    have hdvd := hdiv (idx xx) (hidx xx).1
    have heval := eval₂_lift_initialValue_eq_zero_of_dvd _ H hdvd
    have hxeq : BinaryIRSProfile.domain (idx xx) = x := (hidx xx).2
    simpa [G, concreteUniversalAffineObstruction, U₀, U₁, hxA, xx, hxeq]
      using heval
  obtain ⟨p₀, p₁, hp₀, hp₁, halign⟩ :=
    universal_selected_pair_alignment_core_light x₀ R hHyp hzeta
      uDZ d 1048575 1048576 (by norm_num)
      T PT Sel hNP hPTdeg (by
        rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ)
          from BF64.card_ext3]
        norm_num) Afield hAfield
      U₀ U₁ q (universalRootedNumerators x₀ R)
      (universalSlope x₀ R) uE uE_eq hs hnum hzero
  refine ⟨T, hTS, hbounds.2, p₀, p₁, hp₀, hp₁, ?_⟩
  intro z hz
  simpa [PT] using halign ⟨z, hz⟩

end ProximityPrize.SubmissionBinaryLower
