import ProximityPrize.SubmissionLower.BCHKSResidualNearFullProfile6400
import ProximityPrize.SubmissionLower.BCHKSDegreeCodimCoverage6400
import ProximityPrize.SubmissionLower.BCHKSHeterogeneousUniversalLedger6400
import ProximityPrize.SubmissionLower.BCHKSFullCoreOwnerBridge6400
import ProximityPrize.SubmissionLower.BCHKSGaoPositiveCharacteristicCore6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSNearFullDirectCoreBudget6400
open BCHKSResidualNearFullProfile6400
open BCHKSDegreeCodimCoverage6400
open BCHKSHeterogeneousUniversalLedger6400
open BCHKSFullCoreOwnerBridge6400
open BCHKSBranchwiseHybridAudit6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSTopEdgeSplitJetCap6400
open BCHKSGaoPositiveCharacteristicCore6400
open Polynomial
theorem nearFull_agreements_supply_globalCore_matches
    {I Challenge K : Type*} [DecidableEq I]
    (D : Finset I) (A : Challenge -> Finset I)
    (S : Finset Challenge)
    (order : I -> Nat) (value received : Challenge -> I -> K)
    (d a c : Nat)
    (hAsub : ∀ z ∈ S, A z ⊆ D)
    (hAcard : ∀ z ∈ S, (A z).card = a)
    (horder : ∀ i ∈ D, order i <= d)
    (hFullCard : (D.filter fun i => order i = d).card = c)
    (hca : c <= a)
    (hdefect : ∀ z ∈ S,
      (A z).sum (fun i => d - order i) <= a - c)
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z,
      value z i = received z i) :
    ∀ z ∈ S, ∀ i ∈ D.filter (fun i => order i = d),
      value z i = received z i := by
  intro z hz i hi
  apply hmatch z hz i
  have hrigid := nearFull_profile_rigid
    D (A z) order d a c (hAsub z hz) (hAcard z hz) horder
      hFullCard hca (hdefect z hz)
  exact hrigid.1 hi
theorem exists_bounded_coreQuotient_family_of_nearFull_agreements
    {F : Type*} [Field F] [DecidableEq F]
    (D S : Finset F) (A : F -> Finset F) (order : F -> Nat)
    (P : F -> F[X]) (U0 U1 : F -> F)
    (d a c s : Nat)
    (hAsub : ∀ z ∈ S, A z ⊆ D)
    (hAcard : ∀ z ∈ S, (A z).card = a)
    (horder : ∀ x ∈ D, order x <= d)
    (hFullCard : (D.filter fun x => order x = d).card = c)
    (hca : c <= a)
    (hdefect : ∀ z ∈ S,
      (A z).sum (fun x => d - order x) <= a - c)
    (hmatch : ∀ z ∈ S, ∀ x ∈ A z,
      Polynomial.eval x (P z) = U0 x + z * U1 x)
    (hcard : (D.filter fun x => order x = d).card + s = 131071)
    (hPdegree : ∀ z ∈ S, (P z).natDegree <= 131071) :
    ∃ B0 B1 : F[X], ∃ Q : F -> F[X],
      B0.natDegree <= 131071 ∧ B1.natDegree <= 131071 ∧
      (∀ x ∈ D.filter (fun x => order x = d), B0.eval x = U0 x) ∧
      (∀ x ∈ D.filter (fun x => order x = d), B1.eval x = U1 x) ∧
      (∀ z ∈ S, (Q z).natDegree <= s) ∧
      (∀ z ∈ S,
        P z = B0 + Polynomial.C z * B1 +
          BCHKSFullCoreLineArrangement6400.coreLocator
            (D.filter fun x => order x = d) * Q z) := by
  have hcoreMatch : ∀ z ∈ S,
      ∀ x ∈ D.filter (fun x => order x = d),
        Polynomial.eval x (P z) = U0 x + z * U1 x :=
    nearFull_agreements_supply_globalCore_matches
      D A S order (fun z x => Polynomial.eval x (P z))
        (fun z x => U0 x + z * U1 x) d a c hAsub hAcard horder
        hFullCard hca hdefect hmatch
  exact exists_bounded_coreQuotient_family
    (D.filter fun x => order x = d) S P U0 U1 131071 s
      hcard hPdegree hcoreMatch
def nearFullDirectRaisedSplitTotal6400 (d s : Nat) : Nat :=
  quotientRawCoefficient6400 d s * bchksHybridZMass6400 +
    raisedSplitFixedCover6400
lemma degree129_core389_directSplit_exact6400 :
    quotientRawCoefficient6400 129 130682 = 162792316 /\
      quotientEffectiveCoefficient6400 129 130682 -
          quotientRawCoefficient6400 129 130682 = 389 /\
      nearFullDirectRaisedSplitTotal6400 129 130682 =
        274980556317431259 /\
      nearFullDirectRaisedSplitTotal6400 129 130682 <
        bchksResidualNumerator6400 /\
      bchksResidualNumerator6400 -
          nearFullDirectRaisedSplitTotal6400 129 130682 =
        143682568741 := by
  norm_num [quotientRawCoefficient6400, quotientEffectiveCoefficient6400,
    quotientExponent6400, nearFullDirectRaisedSplitTotal6400,
    raisedSplitFixedCover6400, branchwiseSplitLowYCoefficient6400,
    bchksHybridYMass6400, bchksHybridPairCardCover6400,
    bchksHybridQBadCover6400, bchksHybridZMass6400,
    bchksResidualNumerator6400, bchksErrors6400]
def nearFullDirectAllUniversalTotal6400 (d s : Nat) : Nat :=
  quotientRawCoefficient6400 d s * bchksHybridZMass6400 +
    bchksHybridPairCardCover6400 + bchksHybridQBadCover6400
lemma degree129_directAllUniversal_endpoint6400 :
    quotientRawCoefficient6400 129 130695 = 162808510 /\
      nearFullDirectAllUniversalTotal6400 129 130695 =
        274979581044477775 /\
      bchksResidualNumerator6400 -
          nearFullDirectAllUniversalTotal6400 129 130695 =
        1118955522225 /\
      quotientRawCoefficient6400 129 130696 = 162809756 /\
      nearFullDirectAllUniversalTotal6400 129 130696 =
        274981685507861063 /\
      nearFullDirectAllUniversalTotal6400 129 130696 -
          bchksResidualNumerator6400 = 985507861063 := by
  norm_num [quotientRawCoefficient6400, quotientExponent6400,
    nearFullDirectAllUniversalTotal6400, bchksHybridZMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksResidualNumerator6400, bchksErrors6400]
def nearFullWeightedSupportCap6400 : Nat := 185364 * (129 - 1) + 389 - 1
def nearFullFirstDerivativeRoots6400 : Nat :=
  389 * (129 - 1) + (185364 - 389) * (129 - 2)
lemma degree129_core389_firstDerivative_slack6400 :
    nearFullWeightedSupportCap6400 = 23726980 /\
      nearFullFirstDerivativeRoots6400 = 23541617 /\
      nearFullWeightedSupportCap6400 - 131071 = 23595909 /\
      nearFullFirstDerivativeRoots6400 + 54292 =
        nearFullWeightedSupportCap6400 - 131071 /\
      54292 = 185364 - 131071 - 1 := by
  norm_num [nearFullWeightedSupportCap6400,
    nearFullFirstDerivativeRoots6400]
def nearFullOrder128Delta6400 : Nat := 128 * 127 / 2
def nearFullNewtonInterior6400 (c : Nat) : Nat :=
  1954881344 + 128 * c
lemma nearFull_order128_delta_exact6400 :
    nearFullOrder128Delta6400 = 8128 := by
  norm_num [nearFullOrder128Delta6400]
theorem globalHighStratum_card_le_240511_of_deltaLedger6400
    (highCard coreCard : Nat)
    (hdelta : highCard * nearFullOrder128Delta6400 + coreCard * 128 <=
      nearFullNewtonInterior6400 coreCard) :
    highCard <= 240511 := by
  norm_num [nearFullOrder128Delta6400,
    nearFullNewtonInterior6400] at hdelta ⊢
  omega
lemma globalHighStratum_sparseGenus_endpoint6400 (c : Nat) :
    240511 * nearFullOrder128Delta6400 + c * 128 + 7936 =
        nearFullNewtonInterior6400 c /\
      nearFullNewtonInterior6400 c + 192 =
        240512 * nearFullOrder128Delta6400 + c * 128 /\
      239657 * nearFullOrder128Delta6400 + c * 128 + 6949248 =
        nearFullNewtonInterior6400 c := by
  norm_num [nearFullOrder128Delta6400,
    nearFullNewtonInterior6400]
  omega
lemma globalHighStratum_extraDelta_requirement6400 :
    6949248 + 1 = 6949249 /\
      239657 * 28 = 6710396 /\
      6949249 - 239657 * 28 = 238853 /\
      239657 * 29 = 6950053 /\
      239657 * 29 - 6949249 = 804 := by
  norm_num
lemma core375_rationalTangent_degree_window6400 :
    128 * 185366 + 118 = 185364 * 128 + 375 - 1 /\
      185366 - 131071 = 54295 /\
      185366 + 54295 = 239661 /\
      239657 < 239661 /\
      185364 * 128 + 375 - 1 < 129 * 185366 := by
  norm_num
theorem core375_rationalTangent_crossDegree_le6400
    {K : Type*} [Field K] (A1 A2 B1 B2 : Polynomial K)
    (hA1 : A1.natDegree <= 185366) (hA2 : A2.natDegree <= 185366)
    (hB1 : B1.natDegree <= 54295) (hB2 : B2.natDegree <= 54295) :
    (A1 * B2 - A2 * B1).natDegree <= 239661 := by
  calc
    (A1 * B2 - A2 * B1).natDegree <=
        max (A1 * B2).natDegree (A2 * B1).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ <= 239661 := by
      apply max_le
      · exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hA1 hB2))
      · exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hA2 hB1))
lemma core375_rationalTangent_requiredCancellation6400 :
    239661 - 4 = 239657 /\
      239661 - 5 = 239656 /\
      239656 < 239657 := by
  norm_num
theorem natDegree_det_add_potentialGap_le
    {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (M : Matrix I I R[X]) (rowCap rowPotential colPotential : I -> Nat)
    (gap : Nat)
    (hgap : gap + ∑ i, rowPotential i = ∑ i, colPotential i)
    (hbudget : gap <= ∑ i, rowCap i)
    (hentry : ∀ i j, M i j ≠ 0 ->
      (M i j).natDegree + colPotential j <=
        rowCap i + rowPotential i) :
    M.det.natDegree + gap <= ∑ i, rowCap i := by
  classical
  have hterm (sigma : Equiv.Perm I) :
      (∏ i : I, M (sigma i) i).natDegree + gap <= ∑ i, rowCap i := by
    by_cases hzero : ∃ i : I, M (sigma i) i = 0
    · rcases hzero with ⟨i, hi⟩
      have hprod : (∏ i : I, M (sigma i) i) = 0 :=
        Finset.prod_eq_zero (s := Finset.univ) (by simp) hi
      simpa [hprod] using hbudget
    · have hselected (i : I) : M (sigma i) i ≠ 0 := by
        intro hi
        exact hzero ⟨i, hi⟩
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        hentry (sigma i) i (hselected i))
      have hpermCap : (∑ i : I, rowCap (sigma i)) =
          ∑ i : I, rowCap i := by
        simpa using Equiv.sum_comp sigma rowCap
      have hpermPotential : (∑ i : I, rowPotential (sigma i)) =
          ∑ i : I, rowPotential i := by
        simpa using Equiv.sum_comp sigma rowPotential
      have hprodDegree :
          (∏ i : I, M (sigma i) i).natDegree <=
            ∑ i : I, (M (sigma i) i).natDegree := by
        simpa using Polynomial.natDegree_prod_le
          (s := Finset.univ) (f := fun i : I => M (sigma i) i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hpermCap, hpermPotential] at hsum
      omega
  rw [Matrix.det_apply]
  have hsumDegree :
      (∑ sigma : Equiv.Perm I,
        Equiv.Perm.sign sigma • ∏ i : I, M (sigma i) i).natDegree <=
          (∑ i, rowCap i) - gap := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro sigma _
    have hsmul := Polynomial.natDegree_smul_le
      (Equiv.Perm.sign sigma) (∏ i : I, M (sigma i) i)
    have ht := hterm sigma
    omega
  omega
theorem coefficientDegree_det_add_potentialGap_le
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I (Polynomial (Polynomial K)))
    (rowCap rowPotential colPotential : I -> Nat) (gap : Nat)
    (hgap : gap + ∑ i, rowPotential i = ∑ i, colPotential i)
    (hbudget : gap <= ∑ i, rowCap i)
    (hentry : ∀ i j, M i j ≠ 0 ->
      Polynomial.Bivariate.degreeX (M i j) + colPotential j <=
        rowCap i + rowPotential i) :
    Polynomial.Bivariate.degreeX M.det + gap <= ∑ i, rowCap i := by
  rw [← Polynomial.Bivariate.natDegreeY_swap]
  change (Polynomial.Bivariate.swap M.det).natDegree + gap <= _
  rw [show Polynomial.Bivariate.swap M.det =
      ((Polynomial.Bivariate.swap.toRingEquiv.toRingHom).mapMatrix M).det by
    simpa using RingHom.map_det
      Polynomial.Bivariate.swap.toRingEquiv.toRingHom M]
  apply natDegree_det_add_potentialGap_le _ rowCap rowPotential
    colPotential gap hgap hbudget
  intro i j hij
  have horiginal : M i j ≠ 0 := by
    intro hz
    apply hij
    simp [hz]
  change (Polynomial.Bivariate.swap (M i j)).natDegree + colPotential j <=
    rowCap i + rowPotential i
  rw [show (Polynomial.Bivariate.swap (M i j)).natDegree =
      Polynomial.Bivariate.degreeX (M i j) by
    simpa only [Polynomial.Bivariate.natDegreeY] using
      Polynomial.Bivariate.natDegreeY_swap (M i j)]
  exact hentry i j horiginal
theorem pow_dvd_det_of_permExponentSum
    {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (uniformizer : R) (M : Matrix I I R) (exponent : I -> I -> Nat)
    (N : Nat)
    (hentry : ∀ i j, uniformizer ^ exponent i j ∣ M i j)
    (hperm : ∀ sigma : Equiv.Perm I,
      (∀ i, M (sigma i) i ≠ 0) ->
        N <= ∑ i, exponent (sigma i) i) :
    uniformizer ^ N ∣ M.det := by
  classical
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro sigma _
  suffices hproductDvd : uniformizer ^ N ∣ ∏ i : I, M (sigma i) i by
    rcases hproductDvd with ⟨C, hC⟩
    refine ⟨Equiv.Perm.sign sigma • C, ?_⟩
    rw [hC, mul_smul_comm]
  by_cases hzero : ∃ i : I, M (sigma i) i = 0
  · rcases hzero with ⟨i, hi⟩
    have hprod : (∏ i : I, M (sigma i) i) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ) (by simp) hi
    simp [hprod]
  · have hselected (i : I) : M (sigma i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    have hlargePower : uniformizer ^ N ∣
        uniformizer ^ (∑ i, exponent (sigma i) i) :=
      pow_dvd_pow uniformizer (hperm sigma hselected)
    have hproductPower :
        (∏ i : I, uniformizer ^ exponent (sigma i) i) ∣
          ∏ i : I, M (sigma i) i :=
      Finset.prod_dvd_prod_of_dvd _ _
        (fun i (_ : i ∈ Finset.univ) => hentry (sigma i) i)
    rw [Finset.prod_pow_eq_pow_sum] at hproductPower
    exact hlargePower.trans hproductPower
theorem permExponentSum_ge_of_potentials
    {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (M : Matrix I I R) (exponent : I -> I -> Nat)
    (rowFloor rowPotential colPotential bonus : I -> Nat)
    (gap N : Nat)
    (hgap : gap + ∑ i, rowPotential i = ∑ i, colPotential i)
    (hthreshold : N + gap <=
      (∑ i, rowFloor i) + ∑ i, bonus i)
    (hentry : ∀ i j, M i j ≠ 0 ->
      rowFloor i + rowPotential i + bonus j <=
        exponent i j + colPotential j)
    (sigma : Equiv.Perm I) (hselected : ∀ i, M (sigma i) i ≠ 0) :
    N <= ∑ i, exponent (sigma i) i := by
  classical
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    hentry (sigma i) i (hselected i))
  have hpermFloor : (∑ i : I, rowFloor (sigma i)) =
      ∑ i : I, rowFloor i := by
    simpa using Equiv.sum_comp sigma rowFloor
  have hpermPotential : (∑ i : I, rowPotential (sigma i)) =
      ∑ i : I, rowPotential i := by
    simpa using Equiv.sum_comp sigma rowPotential
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hpermFloor, hpermPotential] at hsum
  omega
theorem coefficientDegree_resultant_add_slantGap_le
    {K : Type*} [Field K]
    (f g : Polynomial (Polynomial (Polynomial K)))
    (m n k Bf Bg : Nat)
    (hf : ∀ i, Polynomial.Bivariate.degreeX (f.coeff i) + k * i <= Bf)
    (hg : ∀ i, Polynomial.Bivariate.degreeX (g.coeff i) + k * i <= Bg)
    (hbudget : k * m * n <= m * Bg + n * Bf) :
    coefficientDegree (resultant f g m n) + k * m * n <=
      m * Bg + n * Bf := by
  classical
  rw [coefficientDegree_eq_degreeX]
  unfold resultant
  rw [← Matrix.det_transpose]
  let M : Matrix (Fin (m + n)) (Fin (m + n))
      (Polynomial (Polynomial K)) :=
    Matrix.transpose (sylvester f g m n)
  let rowCap : Fin (m + n) -> Nat :=
    Fin.addCases (fun _ : Fin m => Bg) (fun _ : Fin n => Bf)
  let rowPotential : Fin (m + n) -> Nat :=
    Fin.addCases (fun j : Fin m => k * (j : Nat))
      (fun j : Fin n => k * (j : Nat))
  let colPotential : Fin (m + n) -> Nat := fun i => k * (i : Nat)
  change Polynomial.Bivariate.degreeX M.det + k * m * n <=
    m * Bg + n * Bf
  have hrowCapSum : (∑ j, rowCap j) = m * Bg + n * Bf := by
    rw [Fin.sum_univ_add]
    simp [rowCap]
  rw [← hrowCapSum]
  apply coefficientDegree_det_add_potentialGap_le M rowCap rowPotential
    colPotential (k * m * n)
  · simp only [rowPotential, colPotential]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_add
      (fun i : Fin (m + n) => k * (i : Nat))]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    change k * m * n +
        ((∑ j : Fin m, k * (j : Nat)) +
          ∑ j : Fin n, k * (j : Nat)) =
        (∑ i : Fin m, k * (i : Nat)) +
          ∑ i : Fin n, k * (m + (i : Nat))
    simp_rw [Nat.mul_add]
    rw [Finset.sum_add_distrib]
    simp
    ring
  · simpa [hrowCapSum] using hbudget
  · intro j i hji
    exact Fin.addCases
      (fun (j : Fin m) (hji : M (Fin.castAdd n j) i ≠ 0) => by
        have hentry : M (Fin.castAdd n j) i =
            if (i : Nat) ∈ Set.Icc (j : Nat) ((j : Nat) + n) then
              g.coeff ((i : Nat) - (j : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        by_cases hmem : (i : Nat) ∈ Set.Icc (j : Nat) ((j : Nat) + n)
        · rw [hentry, if_pos hmem]
          simp only [colPotential, rowCap, rowPotential,
            Fin.addCases_left]
          change Polynomial.Bivariate.degreeX
              (g.coeff ((i : Nat) - (j : Nat))) + k * (i : Nat) <=
            Bg + k * (j : Nat)
          have hle : (j : Nat) <= (i : Nat) := (Set.mem_Icc.mp hmem).1
          have hsplit : (i : Nat) - (j : Nat) + (j : Nat) = (i : Nat) := by
            omega
          have hcoeff := hg ((i : Nat) - (j : Nat))
          have hmul : k * (i : Nat) =
              k * ((i : Nat) - (j : Nat)) + k * (j : Nat) := by
            rw [← Nat.mul_add, hsplit]
          rw [hmul, ← Nat.add_assoc]
          exact Nat.add_le_add_right hcoeff _
        · exact (hji (by rw [hentry, if_neg hmem])).elim)
      (fun (j : Fin n) (hji : M (Fin.natAdd m j) i ≠ 0) => by
        have hentry : M (Fin.natAdd m j) i =
            if (i : Nat) ∈ Set.Icc (j : Nat) ((j : Nat) + m) then
              f.coeff ((i : Nat) - (j : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        by_cases hmem : (i : Nat) ∈ Set.Icc (j : Nat) ((j : Nat) + m)
        · rw [hentry, if_pos hmem]
          simp only [colPotential, rowCap, rowPotential,
            Fin.addCases_right]
          change Polynomial.Bivariate.degreeX
              (f.coeff ((i : Nat) - (j : Nat))) + k * (i : Nat) <=
            Bf + k * (j : Nat)
          have hle : (j : Nat) <= (i : Nat) := (Set.mem_Icc.mp hmem).1
          have hsplit : (i : Nat) - (j : Nat) + (j : Nat) = (i : Nat) := by
            omega
          have hcoeff := hf ((i : Nat) - (j : Nat))
          have hmul : k * (i : Nat) =
              k * ((i : Nat) - (j : Nat)) + k * (j : Nat) := by
            rw [← Nat.mul_add, hsplit]
          rw [hmul, ← Nat.add_assoc]
          exact Nat.add_le_add_right hcoeff _
        · exact (hji (by rw [hentry, if_neg hmem])).elim)
      j hji
def localSylvesterExponent6400 (m n nu : Nat)
    (row col : Fin (m + n)) : Nat :=
  Fin.addCases
    (fun r : Fin m => (nu - 1) - ((col : Nat) - (r : Nat)))
    (fun r : Fin n => nu - ((col : Nat) - (r : Nat))) row
theorem pow_dvd_resultant_of_localJets_and_permBound
    {R : Type*} [CommRing R]
    (uniformizer : R) (f q : Polynomial R)
    (m n nu N : Nat)
    (hf : ∀ i, uniformizer ^ (nu - i) ∣ f.coeff i)
    (hq : ∀ i, uniformizer ^ ((nu - 1) - i) ∣ q.coeff i)
    (hperm : ∀ sigma : Equiv.Perm (Fin (m + n)),
      (∀ i, (Matrix.transpose (sylvester f q m n)) (sigma i) i ≠ 0) ->
      N <= ∑ i, localSylvesterExponent6400 m n nu (sigma i) i) :
    uniformizer ^ N ∣ resultant f q m n := by
  classical
  unfold resultant
  rw [← Matrix.det_transpose]
  apply pow_dvd_det_of_permExponentSum uniformizer
    (Matrix.transpose (sylvester f q m n))
    (localSylvesterExponent6400 m n nu) N
  · intro row col
    exact Fin.addCases
      (fun r : Fin m => by
        have hentry :
            (Matrix.transpose (sylvester f q m n)) (Fin.castAdd n r) col =
              if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + n) then
                q.coeff ((col : Nat) - (r : Nat))
              else 0 := by
          simp [Polynomial.sylvester]
        by_cases hmem :
            (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + n)
        · rw [hentry, if_pos hmem]
          simpa [localSylvesterExponent6400] using
            hq ((col : Nat) - (r : Nat))
        · rw [hentry, if_neg hmem]
          simp)
      (fun r : Fin n => by
        have hentry :
            (Matrix.transpose (sylvester f q m n)) (Fin.natAdd m r) col =
              if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + m) then
                f.coeff ((col : Nat) - (r : Nat))
              else 0 := by
          simp [Polynomial.sylvester]
        by_cases hmem :
            (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + m)
        · rw [hentry, if_pos hmem]
          simpa [localSylvesterExponent6400] using
            hf ((col : Nat) - (r : Nat))
        · rw [hentry, if_neg hmem]
          simp)
      row
  · exact hperm
theorem localSylvesterExponent_core_permBound
    {R : Type*} [CommRing R]
    (f q : Polynomial R) (d : Nat) (sigma : Equiv.Perm (Fin (d + (d - 1))))
    (hselected : ∀ i,
      (Matrix.transpose (sylvester f q d (d - 1))) (sigma i) i ≠ 0) :
    d * (d - 1) <=
      ∑ i, localSylvesterExponent6400 d (d - 1) d (sigma i) i := by
  classical
  let M : Matrix (Fin (d + (d - 1))) (Fin (d + (d - 1))) R :=
    Matrix.transpose (sylvester f q d (d - 1))
  let rowFloor : Fin (d + (d - 1)) -> Nat :=
    Fin.addCases (fun _ : Fin d => d - 1) (fun _ : Fin (d - 1) => d)
  let rowPotential : Fin (d + (d - 1)) -> Nat :=
    Fin.addCases (fun r : Fin d => (r : Nat))
      (fun r : Fin (d - 1) => (r : Nat))
  let colPotential : Fin (d + (d - 1)) -> Nat := fun i => (i : Nat)
  let bonus : Fin (d + (d - 1)) -> Nat := fun _ => 0
  apply permExponentSum_ge_of_potentials M
    (localSylvesterExponent6400 d (d - 1) d)
    rowFloor rowPotential colPotential bonus (d * (d - 1))
    (d * (d - 1))
  · simp only [rowPotential, colPotential]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_add
      (fun i : Fin (d + (d - 1)) => (i : Nat))]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    rw [Finset.sum_add_distrib]
    simp
    ring
  · simp [rowFloor, bonus, Fin.sum_univ_add]
    ring_nf
    exact le_rfl
  · intro row col hne
    exact Fin.addCases
      (fun (r : Fin d) (hne : M (Fin.castAdd (d - 1) r) col ≠ 0) => by
        have hentry : M (Fin.castAdd (d - 1) r) col =
            if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + (d - 1)) then
              q.coeff ((col : Nat) - (r : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        have hmem :
            (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + (d - 1)) := by
          by_contra hnot
          exact hne (by rw [hentry, if_neg hnot])
        simp only [rowFloor, rowPotential, colPotential, bonus,
          Fin.addCases_left, localSylvesterExponent6400]
        have hlo := (Set.mem_Icc.mp hmem).1
        have hhi := (Set.mem_Icc.mp hmem).2
        omega)
      (fun (r : Fin (d - 1)) (hne : M (Fin.natAdd d r) col ≠ 0) => by
        have hentry : M (Fin.natAdd d r) col =
            if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + d) then
              f.coeff ((col : Nat) - (r : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        have hmem : (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + d) := by
          by_contra hnot
          exact hne (by rw [hentry, if_neg hnot])
        simp only [rowFloor, rowPotential, colPotential, bonus,
          Fin.addCases_right, localSylvesterExponent6400]
        have hlo := (Set.mem_Icc.mp hmem).1
        have hhi := (Set.mem_Icc.mp hmem).2
        omega)
      row hne
  · exact hselected
theorem localSylvesterExponent_offCore_permBound
    {R : Type*} [CommRing R]
    (f q : Polynomial R) (d : Nat) (hd : 2 <= d)
    (sigma : Equiv.Perm (Fin (d + (d - 1))))
    (hselected : ∀ i,
      (Matrix.transpose (sylvester f q d (d - 1))) (sigma i) i ≠ 0) :
    (d - 1) * (d - 2) <=
      ∑ i, localSylvesterExponent6400 d (d - 1) (d - 1) (sigma i) i := by
  classical
  have hlastlt : 2 * d - 2 < d + (d - 1) := by omega
  let last : Fin (d + (d - 1)) := ⟨2 * d - 2, hlastlt⟩
  have hlastval : (last : Nat) = 2 * d - 2 := rfl
  let M : Matrix (Fin (d + (d - 1))) (Fin (d + (d - 1))) R :=
    Matrix.transpose (sylvester f q d (d - 1))
  let rowFloor : Fin (d + (d - 1)) -> Nat :=
    Fin.addCases (fun _ : Fin d => d - 2)
      (fun _ : Fin (d - 1) => d - 1)
  let rowPotential : Fin (d + (d - 1)) -> Nat :=
    Fin.addCases (fun r : Fin d => (r : Nat))
      (fun r : Fin (d - 1) => (r : Nat))
  let colPotential : Fin (d + (d - 1)) -> Nat := fun i => (i : Nat)
  let bonus : Fin (d + (d - 1)) -> Nat :=
    fun i => if i = last then 1 else 0
  apply permExponentSum_ge_of_potentials M
    (localSylvesterExponent6400 d (d - 1) (d - 1))
    rowFloor rowPotential colPotential bonus (d * (d - 1))
    ((d - 1) * (d - 2))
  · simp only [rowPotential, colPotential]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_add
      (fun i : Fin (d + (d - 1)) => (i : Nat))]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    rw [Finset.sum_add_distrib]
    simp
    ring
  · have hbonus : (∑ i, bonus i) = 1 := by
      simp [bonus]
    rw [hbonus]
    simp [rowFloor, Fin.sum_univ_add]
    let t := d - 2
    have h2 : d - 2 = t := rfl
    have h1 : d - 1 = t + 1 := by
      dsimp [t]
      omega
    have h0 : d = t + 2 := by
      dsimp [t]
      omega
    rw [h2, h1, h0]
    ring_nf
    exact le_rfl
  · intro row col hne
    exact Fin.addCases
      (fun (r : Fin d) (hne : M (Fin.castAdd (d - 1) r) col ≠ 0) => by
        have hentry : M (Fin.castAdd (d - 1) r) col =
            if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + (d - 1)) then
              q.coeff ((col : Nat) - (r : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        have hmem :
            (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + (d - 1)) := by
          by_contra hnot
          exact hne (by rw [hentry, if_neg hnot])
        simp only [rowFloor, rowPotential, colPotential,
          Fin.addCases_left, localSylvesterExponent6400]
        have hlo := (Set.mem_Icc.mp hmem).1
        have hhi := (Set.mem_Icc.mp hmem).2
        by_cases hcol : col = last
        · subst col
          simp [bonus, last] at ⊢
          have hr : (r : Nat) = d - 1 := by omega
          omega
        · simp [bonus, hcol]
          omega)
      (fun (r : Fin (d - 1)) (hne : M (Fin.natAdd d r) col ≠ 0) => by
        have hentry : M (Fin.natAdd d r) col =
            if (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + d) then
              f.coeff ((col : Nat) - (r : Nat))
            else 0 := by
          simp [M, Polynomial.sylvester]
        have hmem : (col : Nat) ∈ Set.Icc (r : Nat) ((r : Nat) + d) := by
          by_contra hnot
          exact hne (by rw [hentry, if_neg hnot])
        simp only [rowFloor, rowPotential, colPotential,
          Fin.addCases_right, localSylvesterExponent6400]
        have hlo := (Set.mem_Icc.mp hmem).1
        have hhi := (Set.mem_Icc.mp hmem).2
        by_cases hcol : col = last
        · subst col
          simp [bonus, last] at ⊢
          have hr : (r : Nat) = d - 2 := by omega
          omega
        · simp [bonus, hcol]
          omega)
      row hne
  · exact hselected
theorem pow_dvd_resultant_of_coreLocalJets
    {R : Type*} [CommRing R]
    (uniformizer : R) (f q : Polynomial R) (d : Nat)
    (hf : ∀ i, uniformizer ^ (d - i) ∣ f.coeff i)
    (hq : ∀ i, uniformizer ^ ((d - 1) - i) ∣ q.coeff i) :
    uniformizer ^ (d * (d - 1)) ∣ resultant f q d (d - 1) := by
  apply pow_dvd_resultant_of_localJets_and_permBound
    uniformizer f q d (d - 1) d (d * (d - 1)) hf hq
  intro sigma hselected
  exact localSylvesterExponent_core_permBound f q d sigma hselected
theorem pow_dvd_resultant_of_offCoreLocalJets
    {R : Type*} [CommRing R]
    (uniformizer : R) (f q : Polynomial R) (d : Nat) (hd : 2 <= d)
    (hf : ∀ i, uniformizer ^ ((d - 1) - i) ∣ f.coeff i)
    (hq : ∀ i, uniformizer ^ ((d - 2) - i) ∣ q.coeff i) :
    uniformizer ^ ((d - 1) * (d - 2)) ∣
      resultant f q d (d - 1) := by
  apply pow_dvd_resultant_of_localJets_and_permBound
    uniformizer f q d (d - 1) (d - 1) ((d - 1) * (d - 2)) hf hq
  intro sigma hselected
  exact localSylvesterExponent_offCore_permBound
    f q d hd sigma hselected
theorem pow_dvd_derivative_coeff_of_localJets
    {R : Type*} [CommRing R]
    (uniformizer : R) (f : Polynomial R) (nu : Nat)
    (hf : ∀ i, uniformizer ^ (nu - i) ∣ f.coeff i) :
    ∀ i, uniformizer ^ ((nu - 1) - i) ∣ f.derivative.coeff i := by
  intro i
  rw [Polynomial.coeff_derivative]
  have hbase := hf (i + 1)
  have hexponent : nu - (i + 1) = (nu - 1) - i := by omega
  rw [← hexponent]
  exact dvd_mul_of_dvd_left hbase _
theorem pow_dvd_affineDerivative_sub_coeff_of_localJets
    {R : Type*} [CommRing R]
    (uniformizer A : R) (f H : Polynomial R) (nu : Nat)
    (hf : ∀ i, uniformizer ^ (nu - i) ∣ f.coeff i)
    (hH : ∀ i, uniformizer ^ ((nu - 1) - i) ∣ H.coeff i) :
    ∀ i, uniformizer ^ ((nu - 1) - i) ∣
      (Polynomial.C A * f.derivative - H).coeff i := by
  intro i
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  apply dvd_sub
  · exact dvd_mul_of_dvd_right
      (pow_dvd_derivative_coeff_of_localJets uniformizer f nu hf i) A
  · exact hH i
theorem pow_dvd_symmetricGaoResultant_of_coreJets
    {R : Type*} [CommRing R]
    (uniformizer A : R) (f H : Polynomial R) (d : Nat)
    (hf : ∀ i, uniformizer ^ (d - i) ∣ f.coeff i)
    (hH : ∀ i, uniformizer ^ ((d - 1) - i) ∣ H.coeff i) :
    uniformizer ^ (d * (d - 1)) ∣
      resultant f (Polynomial.C A * f.derivative - H) d (d - 1) := by
  apply pow_dvd_resultant_of_coreLocalJets uniformizer f
    (Polynomial.C A * f.derivative - H) d hf
  exact pow_dvd_affineDerivative_sub_coeff_of_localJets
    uniformizer A f H d hf hH
theorem pow_dvd_symmetricGaoResultant_of_offCoreJets
    {R : Type*} [CommRing R]
    (uniformizer A : R) (f H : Polynomial R) (d : Nat) (hd : 2 <= d)
    (hf : ∀ i, uniformizer ^ ((d - 1) - i) ∣ f.coeff i)
    (hH : ∀ i, uniformizer ^ ((d - 2) - i) ∣ H.coeff i) :
    uniformizer ^ ((d - 1) * (d - 2)) ∣
      resultant f (Polynomial.C A * f.derivative - H) d (d - 1) := by
  apply pow_dvd_resultant_of_offCoreLocalJets uniformizer f
    (Polynomial.C A * f.derivative - H) d hd hf
  have hderiv := pow_dvd_derivative_coeff_of_localJets
    uniformizer f (d - 1) hf
  intro i
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  apply dvd_sub
  · have hexponent : ((d - 1) - 1) - i = (d - 2) - i := by omega
    rw [← hexponent]
    exact dvd_mul_of_dvd_right (hderiv i) A
  · exact hH i
theorem coefficientFiberProduct_dvd_of_pairwiseLocalFactors
    {K I : Type*} [Field K] [DecidableEq I]
    (T : Polynomial (Polynomial K)) (S : Finset I)
    (x : I -> K) (nu : I -> Nat)
    (hinj : Set.InjOn x S)
    (hlocal : ∀ i ∈ S,
      Polynomial.C ((Polynomial.X - Polynomial.C (x i)) ^ nu i) ∣ T) :
    Polynomial.C
      (∏ i ∈ S, (Polynomial.X - Polynomial.C (x i)) ^ nu i) ∣ T := by
  classical
  let factor : I -> Polynomial (Polynomial K) := fun i =>
    Polynomial.C ((Polynomial.X - Polynomial.C (x i)) ^ nu i)
  have hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
      IsCoprime (factor i) (factor j) := by
    intro i hi j hj hij
    have hx : x i ≠ x j := fun h => hij (hinj hi hj h)
    have hunit : IsUnit (x i - x j) := (sub_ne_zero.mpr hx).isUnit
    have hbase : IsCoprime
        ((Polynomial.X - Polynomial.C (x i)) ^ nu i)
        ((Polynomial.X - Polynomial.C (x j)) ^ nu j) :=
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit).pow
    exact hbase.map (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K))
  have hprod : ∏ i ∈ S, factor i ∣ T :=
    Finset.prod_dvd_of_coprime hcop (fun i hi => hlocal i hi)
  simpa [factor] using hprod
theorem coefficientFiberProduct_natDegree
    {K I : Type*} [Field K] [DecidableEq I]
    (S : Finset I) (x : I -> K) (nu : I -> Nat) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (x i)) ^ nu i).natDegree =
      ∑ i ∈ S, nu i := by
  classical
  rw [Polynomial.natDegree_prod_of_monic]
  · apply Finset.sum_congr rfl
    intro i hi
    simp
  · intro i hi
    exact (Polynomial.monic_X_sub_C _).pow _
theorem exists_nonzero_residual_of_pairwiseLocalFactors
    {K I : Type*} [Field K] [DecidableEq I]
    (T : Polynomial (Polynomial K)) (S : Finset I)
    (x : I -> K) (nu : I -> Nat)
    (hinj : Set.InjOn x S) (hT : T ≠ 0)
    (hlocal : ∀ i ∈ S,
      Polynomial.C ((Polynomial.X - Polynomial.C (x i)) ^ nu i) ∣ T) :
    ∃ residual : Polynomial (Polynomial K),
      T = Polynomial.C
          (∏ i ∈ S, (Polynomial.X - Polynomial.C (x i)) ^ nu i) *
            residual ∧
      residual ≠ 0 := by
  obtain ⟨residual, hfactor⟩ :=
    coefficientFiberProduct_dvd_of_pairwiseLocalFactors
      T S x nu hinj hlocal
  refine ⟨residual, hfactor, ?_⟩
  intro hz
  apply hT
  rw [hfactor, hz, mul_zero]
def nearFullGaoWeight6400 (c : Nat) : Nat :=
  185364 * 128 + c - 1
def nearFullGaoTriangularRaw6400 (c : Nat) : Nat :=
  (2 * 129 - 1) * nearFullGaoWeight6400 c - 129 -
    131071 * 129 * 128
def nearFullGaoSingularMass6400 (c : Nat) : Nat :=
  c * 129 * 128 + (185364 - c) * 128 * 127
def nearFullGaoCorrectedDegree6400 (c : Nat) : Nat :=
  nearFullGaoTriangularRaw6400 c - nearFullGaoSingularMass6400 c
lemma degree129_core375_correctedGao_exact6400 :
    nearFullGaoWeight6400 375 = 23726966 /\
      nearFullGaoTriangularRaw6400 375 = 3933585781 /\
      nearFullGaoSingularMass6400 375 = 3013373184 /\
      nearFullGaoCorrectedDegree6400 375 = 920212597 /\
      nearFullGaoCorrectedDegree6400 375 < 2130706433 /\
      2130706433 - nearFullGaoCorrectedDegree6400 375 =
        1210493836 := by
  norm_num [nearFullGaoWeight6400, nearFullGaoTriangularRaw6400,
    nearFullGaoSingularMass6400, nearFullGaoCorrectedDegree6400]
theorem degree129_correctedGao_lt_characteristic_of_core_le3756400
    (c : Nat) (hc : c <= 375) :
    nearFullGaoCorrectedDegree6400 c <= 920212597 /\
      nearFullGaoCorrectedDegree6400 c < 2130706433 := by
  norm_num [nearFullGaoCorrectedDegree6400,
    nearFullGaoTriangularRaw6400, nearFullGaoWeight6400,
    nearFullGaoSingularMass6400] at ⊢
  omega
def nearFullGaoCorrectedClosedForm6400 (d c : Nat) : Nat :=
  (d - 1) * (d * 54293 + 185364) + c + 1 - 3 * d
theorem nearFullGaoCorrectedClosedForm_lt_characteristic_of_degree_le1966400
    (d c : Nat) (hd : d <= 196) (hc : c <= 185364) :
    nearFullGaoCorrectedClosedForm6400 d c <= 2111409805 /\
      nearFullGaoCorrectedClosedForm6400 d c < 2130706433 := by
  have hdm : d - 1 <= 195 := by omega
  have hinner : d * 54293 + 185364 <= 196 * 54293 + 185364 := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right 54293 hd) 185364
  have hproduct :
      (d - 1) * (d * 54293 + 185364) <=
        195 * (196 * 54293 + 185364) :=
    Nat.mul_le_mul hdm hinner
  have hbound : nearFullGaoCorrectedClosedForm6400 d c <= 2111409805 := by
    unfold nearFullGaoCorrectedClosedForm6400
    calc
      (d - 1) * (d * 54293 + 185364) + c + 1 - 3 * d <=
          (d - 1) * (d * 54293 + 185364) + c + 1 := Nat.sub_le _ _
      _ <= 195 * (196 * 54293 + 185364) + 185364 + 1 := by
        exact Nat.add_le_add_right (Nat.add_le_add hproduct hc) 1
      _ = 2111409805 := by norm_num
  exact ⟨hbound, hbound.trans_lt (by norm_num)⟩
lemma nearFullGaoCorrectedClosedForm_degree197_firstMiss6400 :
    nearFullGaoCorrectedClosedForm6400 197 0 = 2132692070 /\
      2130706433 < nearFullGaoCorrectedClosedForm6400 197 0 /\
      nearFullGaoCorrectedClosedForm6400 197 0 - 2130706433 =
        1985637 := by
  norm_num [nearFullGaoCorrectedClosedForm6400]
def nearFullSymmetricGaoWeight6400 (d c : Nat) : Nat :=
  185364 * (d - 1) + c - 1
def nearFullSymmetricGaoRaw6400 (d c : Nat) : Nat :=
  (2 * d - 1) * nearFullSymmetricGaoWeight6400 d c -
    131071 * d * d
def nearFullSymmetricGaoSingularMass6400 (d c : Nat) : Nat :=
  c * d * (d - 1) + (185364 - c) * (d - 1) * (d - 2)
def nearFullSymmetricGaoCorrected6400 (d c : Nat) : Nat :=
  nearFullSymmetricGaoRaw6400 d c -
    nearFullSymmetricGaoSingularMass6400 d c
def nearFullSymmetricGaoClosedForm6400 (d c : Nat) : Nat :=
  (54293 * d * d + c + 1) - (185364 + 2 * d)
lemma degree129_core375_symmetricCorrectedGao_exact6400 :
    nearFullSymmetricGaoWeight6400 129 375 = 23726966 /\
      nearFullSymmetricGaoRaw6400 129 375 = 3916677751 /\
      nearFullSymmetricGaoSingularMass6400 129 375 = 3013373184 /\
      nearFullSymmetricGaoCorrected6400 129 375 = 903304567 /\
      nearFullSymmetricGaoClosedForm6400 129 375 = 903304567 /\
      2130706433 - nearFullSymmetricGaoCorrected6400 129 375 =
        1227401866 := by
  norm_num [nearFullSymmetricGaoWeight6400,
    nearFullSymmetricGaoRaw6400, nearFullSymmetricGaoSingularMass6400,
    nearFullSymmetricGaoCorrected6400,
    nearFullSymmetricGaoClosedForm6400]
theorem nearFullSymmetricGaoClosedForm_lt_characteristic_of_degree_le1986400
    (d c : Nat) (hd : d <= 198) (hc : c <= 185364) :
    nearFullSymmetricGaoClosedForm6400 d c <= 2128688137 /\
      nearFullSymmetricGaoClosedForm6400 d c < 2130706433 := by
  have hd2 : d * d <= 198 * 198 := Nat.mul_le_mul hd hd
  have hscaled : 54293 * (d * d) <= 54293 * (198 * 198) :=
    Nat.mul_le_mul_left 54293 hd2
  have hpre : 54293 * d * d + c + 1 <= 2128688137 := by
    calc
      54293 * d * d + c + 1 = 54293 * (d * d) + c + 1 := by ring
      _ <= 54293 * (198 * 198) + 185364 + 1 := by omega
      _ = 2128688137 := by norm_num
  have hbound : nearFullSymmetricGaoClosedForm6400 d c <= 2128688137 := by
    exact (Nat.sub_le _ _).trans hpre
  exact ⟨hbound, hbound.trans_lt (by norm_num)⟩
lemma nearFullSymmetricGao_degree198_endpoint6400 :
    nearFullSymmetricGaoRaw6400 198 185364 = 9358810561 /\
      nearFullSymmetricGaoSingularMass6400 198 185364 = 7230308184 /\
      nearFullSymmetricGaoCorrected6400 198 185364 = 2128502377 /\
      nearFullSymmetricGaoClosedForm6400 198 185364 = 2128502377 /\
      2130706433 - nearFullSymmetricGaoCorrected6400 198 185364 =
        2204056 := by
  norm_num [nearFullSymmetricGaoWeight6400,
    nearFullSymmetricGaoRaw6400, nearFullSymmetricGaoSingularMass6400,
    nearFullSymmetricGaoCorrected6400,
    nearFullSymmetricGaoClosedForm6400]
lemma nearFullSymmetricGao_degree199_firstMiss6400 :
    nearFullSymmetricGaoCorrected6400 199 0 = 2149871332 /\
      nearFullSymmetricGaoClosedForm6400 199 0 = 2149871332 /\
      nearFullSymmetricGaoCorrected6400 199 0 - 2130706433 =
        19164899 := by
  norm_num [nearFullSymmetricGaoWeight6400,
    nearFullSymmetricGaoRaw6400, nearFullSymmetricGaoSingularMass6400,
    nearFullSymmetricGaoCorrected6400,
    nearFullSymmetricGaoClosedForm6400]
theorem frobeniusPower_derivative_eq_zero6400
    {K : Type*} [CommRing K] {p : Nat} [CharP K p] :
    (Polynomial.X ^ p : Polynomial K).derivative = 0 := by
  rw [Polynomial.derivative_pow, CharP.cast_eq_zero K p]
  simp
private theorem degreeX_C_eq_natDegree6400
    {K : Type*} [Semiring K] (q : Polynomial K) :
    Polynomial.Bivariate.degreeX
      (Polynomial.C q : Polynomial (Polynomial K)) = q.natDegree := by
  unfold Polynomial.Bivariate.degreeX
  by_cases hq : q = 0
  · subst q
    simp
  · rw [Polynomial.support_C hq]
    simp
theorem coefficientDegree_coefficientFactor_mul
    {K : Type*} [Field K]
    (singular : Polynomial K) (M : Polynomial (Polynomial K))
    (hsingular : singular ≠ 0) (hM : M ≠ 0) :
    coefficientDegree (Polynomial.C singular * M) =
      singular.natDegree + coefficientDegree M := by
  rw [coefficientDegree_eq_degreeX, coefficientDegree_eq_degreeX,
    Polynomial.Bivariate.degreeX_mul _ _
      (Polynomial.C_ne_zero.mpr hsingular) hM,
    degreeX_C_eq_natDegree6400]
theorem coefficientDegree_residual_add_mass_le_of_coefficientFactor
    {K : Type*} [Field K]
    (whole residual : Polynomial (Polynomial K))
    (singular : Polynomial K) (raw mass : Nat)
    (hfactor : whole = Polynomial.C singular * residual)
    (hsingular : singular ≠ 0) (hresidual : residual ≠ 0)
    (hwhole : coefficientDegree whole <= raw)
    (hmass : mass <= singular.natDegree) :
    coefficientDegree residual + mass <= raw := by
  have heq : coefficientDegree whole =
      singular.natDegree + coefficientDegree residual := by
    rw [hfactor,
      coefficientDegree_coefficientFactor_mul singular residual
        hsingular hresidual]
  omega
theorem irreducible_dvd_residual_of_dvd_coefficientFactor_mul
    {K : Type*} [Field K]
    (T M : Polynomial (Polynomial K)) (singular : Polynomial K)
    (hTirreducible : Irreducible T) (hTpos : 0 < T.natDegree)
    (hsingular : singular ≠ 0)
    (hdiv : T ∣ Polynomial.C singular * M) :
    T ∣ M := by
  rcases hTirreducible.prime.dvd_mul.mp hdiv with hcoeff | hM
  · have hCzero : Polynomial.C singular ≠ 0 :=
      Polynomial.C_ne_zero.mpr hsingular
    have hdegree : (Polynomial.C singular).natDegree < T.natDegree := by
      rw [Polynomial.natDegree_C]
      exact hTpos
    exact (Polynomial.not_dvd_of_natDegree_lt hCzero hdegree hcoeff).elim
  · exact hM
theorem exists_constantPolynomial_of_correctedResidual
    {K : Type*} [Field K] {p : Nat} [CharP K p]
    (T M : Polynomial (Polynomial K)) (singular : Polynomial K)
    (hp : p ≠ 0)
    (hTirreducible : Irreducible T) (hTpos : 0 < T.natDegree)
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hsingular : singular ≠ 0) (hM : M ≠ 0)
    (hdiv : T ∣ Polynomial.C singular * M)
    (hdegree : coefficientDegree M < p) :
    ∃ t : Polynomial K, t.map Polynomial.C = T := by
  apply exists_constantPolynomial_of_derivatives_eq_zero_of_dvd_degree_lt_char
    hp T M hderiv hM
  · exact irreducible_dvd_residual_of_dvd_coefficientFactor_mul
      T M singular hTirreducible hTpos hsingular hdiv
  · exact hdegree
theorem exists_constantPolynomial_of_rawResultant_after_singularDivision
    {K : Type*} [Field K] {p : Nat} [CharP K p]
    (T whole residual : Polynomial (Polynomial K))
    (singular : Polynomial K) (raw mass : Nat)
    (hp : p ≠ 0)
    (hTirreducible : Irreducible T) (hTpos : 0 < T.natDegree)
    (hderiv : ∀ i, (T.coeff i).derivative = 0)
    (hfactor : whole = Polynomial.C singular * residual)
    (hsingular : singular ≠ 0) (hresidual : residual ≠ 0)
    (hTdivWhole : T ∣ whole)
    (hwholeDegree : coefficientDegree whole <= raw)
    (hmass : mass <= singular.natDegree)
    (hcorrected : raw - mass < p) :
    ∃ t : Polynomial K, t.map Polynomial.C = T := by
  have hresidualDegreeAdd : coefficientDegree residual + mass <= raw :=
    coefficientDegree_residual_add_mass_le_of_coefficientFactor
      whole residual singular raw mass hfactor hsingular hresidual
        hwholeDegree hmass
  have hresidualDegree : coefficientDegree residual <= raw - mass := by
    omega
  have hdiv : T ∣ Polynomial.C singular * residual := by
    rw [← hfactor]
    exact hTdivWhole
  exact exists_constantPolynomial_of_correctedResidual
    T residual singular hp hTirreducible hTpos hderiv hsingular hresidual
      hdiv (hresidualDegree.trans_lt hcorrected)
end BCHKSNearFullDirectCoreBudget6400
end ProximityPrize.SubmissionLower
