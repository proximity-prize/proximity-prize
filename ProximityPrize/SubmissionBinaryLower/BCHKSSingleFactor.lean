import ProximityPrize.SubmissionBinaryLower.BCHKSSingleFactorGood
import ProximityPrize.SubmissionBinaryLower.BCHKSPrimitiveEffectiveResultant
import ProximityPrize.SubmissionBinaryLower.BCHKSFactorXDegree
import ProximityPrize.SubmissionBinaryLower.BCHKSPairSetup
import ProximityPrize.SubmissionBinaryLower.BCHKSDegreeTwoSelectedFinal
import ProximityPrize.SubmissionBinaryLower.BCHKSLinearProtocolAdapter

/-!
# Single-factor alignment at Frobenius level `q`

The staged BCHKS selection first picks one irreducible factor `R` of the
interpolant and only then chooses a specialization point `x₀` and a factor `H`
of `R(x₀, Y, Z)`.  This file isolates the second half as a statement about one
irreducible `R`, with the affine data `U₀ + z^q U₁`.  The exponent `q` is a
power of two: in characteristic two an inseparable factor is untwisted by a
Frobenius square root, which turns the line `U₀ + z U₁` into `U₀ + t^q U₁`
with `z = t^q`.

Here the factor is assumed separable (`R.derivative ≠ 0`); the inseparable
cases are reduced to this one in `BCHKSInseparable`.
-/

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark Polynomial
open RationalFunctions RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- First-stage capacity of a factor of `Y`-degree `d`: the second-stage
pair budget, the error term, and the bad-specialization reserve. -/
def sfCap (d : ℕ) : ℕ :=
  5059283 * 1288 * 1180364 * d + (bchksErrors + 1) * d + 2 * d * 1180364

theorem sfCap_mono {a b : ℕ} (h : a ≤ b) : sfCap a ≤ sfCap b := by
  unfold sfCap
  have h3 : 2 * a * 1180364 ≤ 2 * b * 1180364 := by omega
  have h4 : (bchksErrors + 1) * a ≤ (bchksErrors + 1) * b := Nat.mul_le_mul_left _ h
  have h5 : 5059283 * 1288 * 1180364 * a ≤ 5059283 * 1288 * 1180364 * b :=
    Nat.mul_le_mul_left _ h
  omega

/-- Pair setup for one irreducible factor, without an ambient interpolant. -/
theorem setup_selected_pair_single
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (R : Polynomial (Polynomial (Polynomial F)))
    (H : Polynomial (Polynomial F)) (x₀ : F)
    (hRirr : Irreducible R)
    (hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀))
    (hHpos : 0 < H.natDegree)
    (hRdeg : R.natDegree ≤ 1289)
    (hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 1180364)
    (hprim : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    Irreducible H ∧
    H ∣ triSpecializeX R x₀ ∧ H.natDegree ≤ 1289 ∧
    Polynomial.Bivariate.totalDegree H ≤ 1180364 ∧
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
  have hHdeg : H.natDegree ≤ 1289 :=
    (Polynomial.natDegree_le_of_dvd hHd hRX0).trans
      ((triSpecializeX_natDegree_le R x₀).trans hRdeg)
  have hRXtotal : Polynomial.Bivariate.totalDegree (triSpecializeX R x₀) ≤ 1180364 :=
    totalDegree_triSpecializeX_le R x₀ 1180364 hRYZ
  have totalDegree_le_of_dvd
      {A B : Polynomial (Polynomial F)} (hA : A ≠ 0) (hB : B ≠ 0) (hd : A ∣ B) :
      Polynomial.Bivariate.totalDegree A ≤ Polynomial.Bivariate.totalDegree B := by
    obtain ⟨C, rfl⟩ := hd
    have hC : C ≠ 0 := fun hc => hB (by simp [hc])
    rw [Polynomial.Bivariate.totalDegree_mul hA hC]
    exact Nat.le_add_right _ _
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hHtotal : Polynomial.Bivariate.totalDegree H ≤ 1180364 :=
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

/-- Single-factor alignment for a separable irreducible factor at level `q`. -/
theorem single_factor_alignment_sep
    (q : ℕ) (hq1 : 1 ≤ q) (hqD : q ≤ 1180364)
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (P : BinaryIRSProfile.Field → BinaryIRSProfile.Field[X])
    (Arow : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (R : Polynomial (Polynomial (Polynomial BinaryIRSProfile.Field)))
    (S : Finset BinaryIRSProfile.Field)
    (hRi : Irreducible R) (hRpos : 0 < R.natDegree) (hRd : R.natDegree ≤ 1288)
    (hsep : R.derivative ≠ 0)
    (hYZs : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + q * j < 1180364)
    (hW : ∀ j a, ((R.coeff j).coeff a) ≠ 0 → a + 1048575 * j < 1351219797)
    (hPdeg : ∀ z ∈ S, (P z).natDegree ≤ 1048575)
    (hvan : ∀ z ∈ S, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ S, 1483227 ≤ (Arow z).card)
    (hagree : ∀ z ∈ S, ∀ i ∈ Arow z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z ^ q * U 1 i)
    (hcard : sfCap R.natDegree < S.card) :
    ∃ T : Finset BinaryIRSProfile.Field, T ⊆ S ∧ bchksErrors + 1 < T.card ∧
      ∃ p₀ p₁ : BinaryIRSProfile.Field[X], p₀.natDegree ≤ 1048575 ∧
        p₁.natDegree ≤ 1048575 ∧ ∀ z ∈ T, P z = p₀ + Polynomial.C (z ^ q) * p₁ := by
  classical
  have hYZq : YZCapQ R q 1180364 := by
    intro i a ha
    have := hYZs i a ha
    omega
  have hYZ : YZCap R 1180364 := hYZq.toYZCap hq1
  have hRYZ : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      ((R.coeff j).coeff a).natDegree + j < 1180364 := by
    intro j a ha
    have := hYZs j a ha
    nlinarith
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
            (2 * 1289 + 2) * BCHKSConcreteGS.DX := by
        exact Nat.add_le_add hwdeg
          (hfx.trans (Nat.mul_le_mul_right BCHKSConcreteGS.DX (by omega)))
      _ < Fintype.card BinaryIRSProfile.Field := by
        rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ)
          from BF64.card_ext3]
        norm_num [BCHKSConcreteGS.DZ, BCHKSConcreteGS.DX]
  have hfactorXDegree : ∀ x : BinaryIRSProfile.Field,
      (Polynomial.eval (Polynomial.C x) (factorXObstruction R)).natDegree ≤
        2 * R.natDegree * 1180364 := by
    intro x
    have hcoeffCap : ∀ j, Polynomial.Bivariate.degreeX (R.coeff j) ≤ 1180364 := by
      intro j
      unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro a ha
      have := hRYZ j a (Polynomial.mem_support_iff.mp ha)
      omega
    have hevalCap : ∀ p : Polynomial (Polynomial BinaryIRSProfile.Field),
        Polynomial.Bivariate.degreeX p ≤ 1180364 →
        (Polynomial.eval (Polynomial.C x) p).natDegree ≤ 1180364 := by
      intro p hpdeg
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
    apply factorXObstruction_eval_natDegree_le R x R.natDegree 1180364 hRpos (le_refl _)
    · unfold Polynomial.Bivariate.degreeX
      apply Finset.sup_le
      intro j hj
      simp only [triSpecializeX, Polynomial.coeff_map]
      exact hevalCap (R.coeff j) (hcoeffCap j)
    · exact hevalCap R.leadingCoeff (by
        rw [← Polynomial.coeff_natDegree]
        exact hcoeffCap R.natDegree)
  obtain ⟨x₀, Bad, hBad, -, hRX0, hprim, hsimple⟩ :=
    exists_single_factor_good_effective R hRi hRpos hsep w R.natDegree 1180364
      hcertDegree hfactorXDegree
  -- Second stage: choose a factor `H` of `R(x₀, Y, Z)`.
  let d := R.natDegree
  let A := 5059283 * 1288 * 1180364
  let e' := bchksErrors + 1
  let Uset := S \ Bad
  have hUcard : A * d + e' * d < Uset.card := by
    have hc : (Bad ∩ S).card ≤ 2 * d * 1180364 :=
      (Finset.card_le_card Finset.inter_subset_left).trans hBad
    have hcap : A * d + e' * d + 2 * d * 1180364 < S.card := hcard
    rw [Finset.card_sdiff]
    generalize A * d + e' * d = cA at hcap ⊢
    generalize 2 * d * 1180364 = cB at hcap hc
    omega
  let Hs := (UniqueFactorizationMonoid.normalizedFactors
    (triSpecializeX R x₀)).toFinset.filter fun H => 0 < H.natDegree
  have hcover : ∀ z ∈ Uset, ∃ H ∈ Hs,
      biEval H (Polynomial.eval x₀ (P z)) z = 0 := by
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
    exact ⟨H, by simp [Hs, hHR, hHpos], hHzero⟩
  have hHsum : (∑ H ∈ Hs, H.natDegree) ≤ d := by
    calc
      (∑ H ∈ Hs, H.natDegree) ≤
          ∑ H ∈ (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX R x₀)).toFinset, H.natDegree := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
      _ ≤ (triSpecializeX R x₀).natDegree :=
        normalizedFactors_toFinset_sum_natDegree_le _ hRX0
      _ ≤ R.natDegree := triSpecializeX_natDegree_le R x₀
  have hHcard : Hs.card ≤ d := by
    calc
      Hs.card = ∑ H ∈ Hs, 1 := by simp
      _ ≤ ∑ H ∈ Hs, H.natDegree := by
        exact Finset.sum_le_sum fun H hH => (Finset.mem_filter.mp hH).2
      _ ≤ d := hHsum
  let capH : Polynomial (Polynomial BinaryIRSProfile.Field) → ℕ :=
    fun H => A * H.natDegree + e'
  have hcapHsum : (∑ H ∈ Hs, capH H) ≤ A * d + e' * d := by
    dsimp [capH]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      A * (∑ H ∈ Hs, H.natDegree) + Hs.card * e' ≤ A * d + d * e' :=
        Nat.add_le_add (Nat.mul_le_mul_left A hHsum) (Nat.mul_le_mul_right e' hHcard)
      _ = A * d + e' * d := by ring
  obtain ⟨H, hHs, hHfib⟩ :=
    exists_rel_fiber_gt_capacity Uset Hs
      (fun z H => biEval H (Polynomial.eval x₀ (P z)) z = 0) capH hcover
      (hcapHsum.trans_lt hUcard)
  let T := Uset.filter fun z => biEval H (Polynomial.eval x₀ (P z)) z = 0
  have hHR : H ∈ UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀) := by
    simpa [Hs] using (Finset.mem_filter.mp hHs).1
  have hHpos : 0 < H.natDegree := (Finset.mem_filter.mp hHs).2
  have hprim' : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive := by
    rw [Polynomial.Bivariate.evalX_eq_map]
    exact hprim
  obtain ⟨hHirr, -, -, hHtot, hHyp⟩ :=
    setup_selected_pair_single R H x₀ hRi hHR hHpos (hRd.trans (by norm_num)) hRYZ hprim'
  have hTS : T ⊆ S := fun z hz => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hTbad : ∀ z ∈ T, z ∉ Bad :=
    fun z hz => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
  have hvanT : ∀ z ∈ T, triEval R z (P z) = 0 ∧
      biEval H (Polynomial.eval x₀ (P z)) z = 0 :=
    fun z hz => ⟨hvan z (hTS hz), (Finset.mem_filter.mp hz).2⟩
  have hmargin : A * H.natDegree + e' < T.card := hHfib
  by_cases hdeg1 : R.natDegree = 1
  · have hTmargin : (613925 + 1) + 2 * 1351219797 * 1180364 < T.card := by
      have hm : 2 * 1351219797 * 1180364 ≤ A * H.natDegree := by
        dsimp [A]
        nlinarith
      dsimp [e', bchksErrors] at hmargin
      omega
    obtain ⟨Tg, hTgT, hTgcard, p₀, p₁, hp₀, hp₁, hline⟩ :=
      bchksLinearProtocolAdapter U P Arow R T q hq1
        (fun z hz => hPdeg z (hTS hz)) (fun z hz => hvan z (hTS hz))
        (fun z hz => hrow z (hTS hz)) (fun z hz => hagree z (hTS hz))
        hRi hYZq hW hdeg1 hTmargin
    exact ⟨Tg, hTgT.trans hTS, by simpa [bchksErrors] using hTgcard,
      p₀, p₁, hp₀, hp₁, hline⟩
  · have hdeg2 : 2 ≤ R.natDegree := by omega
    obtain ⟨Tg, hTgT, hTgcard, p₀, p₁, hp₀, hp₁, hline⟩ :=
      degree_two_selected_final U P Arow R H T x₀ Bad q hqD
        (fun z hz => hPdeg z (hTS hz)) hvanT hTbad hmargin hRd
        hRi hHirr hHpos hHyp hHtot hYZ hsimple
        (fun z hz => by have := hrow z (hTS hz); norm_num; exact this)
        (fun z hz => hagree z (hTS hz)) hdeg2
    exact ⟨Tg, hTgT.trans hTS, hTgcard, p₀, p₁, hp₀, hp₁, hline⟩

end ProximityPrize.SubmissionBinaryLower
