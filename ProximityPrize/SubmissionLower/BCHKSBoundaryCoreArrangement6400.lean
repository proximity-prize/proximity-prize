import ProximityPrize.SubmissionLower.BCHKSHybridHighDegreeAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSBoundaryCoreArrangement6400
open Polynomial
def bchksBoundaryOffCore6400 : ℕ := 131073
def bchksBoundaryDeficiency6400 : ℕ := 54293
def bchksBoundaryErrors6400 : ℕ := 76780
def bchksBoundaryPairArrangementCap6400 : ℕ := 311778
def bchksBoundaryDirectIncidenceCap6400 : ℕ := 185360
theorem maxWeight_forces_exact_deficiency_and_core
    (d w total deficiency full : ℕ)
    (hweight : w + bchksBoundaryDeficiency6400 + 1 = d * 185364)
    (hcofactor : w < total)
    (htotal : total + deficiency ≤ d * 185364)
    (hprofile : 185364 ≤ full + deficiency)
    (hnonalignment : full ≤ 131071) :
    deficiency = bchksBoundaryDeficiency6400 ∧
      full = 131071 ∧ total = w + 1 := by
  dsimp [bchksBoundaryDeficiency6400] at hweight ⊢
  omega
noncomputable def coreLocator6400
    {F I : Type*} [Field F] [DecidableEq I]
    (core : Finset I) (omega : I → F) : F[X] :=
  ∏ i ∈ core, (Polynomial.X - Polynomial.C (omega i))
theorem exists_coreLocator_quotient
    {F I : Type*} [Field F] [DecidableEq I]
    (core : Finset I) (omega : I → F) (D : F[X]) (s : ℕ)
    (homega : Function.Injective omega)
    (hroot : ∀ i ∈ core, Polynomial.eval (omega i) D = 0)
    (hdegree : D.natDegree ≤ core.card + s) :
    ∃ C : F[X],
      D = coreLocator6400 core omega * C ∧ C.natDegree ≤ s := by
  classical
  have hdiv : coreLocator6400 core omega ∣ D := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact pairwise_coprime_X_sub_C homega hij
    · intro i hi
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
      exact hroot i hi
  obtain ⟨C, hfactor⟩ := hdiv
  refine ⟨C, hfactor, ?_⟩
  by_cases hC : C = 0
  · simp [hC]
  have hGmonic : (coreLocator6400 core omega).Monic := by
    exact Polynomial.monic_prod_X_sub_C omega core
  have hG : coreLocator6400 core omega ≠ 0 := hGmonic.ne_zero
  have hGdegree : (coreLocator6400 core omega).natDegree = core.card := by
    exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card core omega
  have hmulDegree :
      (coreLocator6400 core omega).natDegree + C.natDegree = D.natDegree := by
    rw [hfactor, Polynomial.natDegree_mul hG hC]
  omega
theorem eq_of_eval_eq_on_core
    {F I : Type*} [Field F] [DecidableEq I]
    (core : Finset I) (omega : I → F) (P Q : F[X]) (s : ℕ)
    (homega : Function.Injective omega)
    (hP : P.natDegree ≤ s) (hQ : Q.natDegree ≤ s)
    (hcore : s < core.card)
    (heval : ∀ i ∈ core,
      Polynomial.eval (omega i) P = Polynomial.eval (omega i) Q) :
    P = Q := by
  classical
  let points : Finset F := core.image omega
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P Q points
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact heval i hi
  · have hcard : points.card = core.card := by
      exact Finset.card_image_iff.mpr fun i _ j _ hij ↦ homega hij
    rw [hcard]
    exact (max_le hP hQ).trans_lt hcore
def fallingFactorial6400 (n t : ℕ) : ℕ :=
  ∏ i ∈ Finset.range t, (n - i)
theorem card_le_tupleCapacity
    (L N r t e : ℕ)
    (hpos : 0 < fallingFactorial6400 r t)
    (hcount : L * fallingFactorial6400 r t ≤
      e * fallingFactorial6400 N t) :
    L ≤ (e * fallingFactorial6400 N t) /
      fallingFactorial6400 r t := by
  rw [Nat.le_div_iff_mul_le hpos]
  exact hcount
lemma bchksBoundary_pairArrangement_exact6400 :
    (bchksBoundaryOffCore6400 * (bchksBoundaryOffCore6400 - 1) / 2) /
          (bchksBoundaryDeficiency6400 - 1) +
        (bchksBoundaryOffCore6400 / bchksBoundaryDeficiency6400) *
          bchksBoundaryErrors6400 =
      bchksBoundaryPairArrangementCap6400 := by
  norm_num [bchksBoundaryOffCore6400, bchksBoundaryDeficiency6400,
    bchksBoundaryErrors6400, bchksBoundaryPairArrangementCap6400]
lemma bchksBoundary_directIncidence_exact6400 :
    (bchksBoundaryOffCore6400 * bchksBoundaryErrors6400) /
        bchksBoundaryDeficiency6400 =
      bchksBoundaryDirectIncidenceCap6400 ∧
    bchksBoundaryDirectIncidenceCap6400 <
      bchksBoundaryPairArrangementCap6400 := by
  norm_num [bchksBoundaryOffCore6400, bchksBoundaryDeficiency6400,
    bchksBoundaryErrors6400, bchksBoundaryDirectIncidenceCap6400,
    bchksBoundaryPairArrangementCap6400]
theorem aggregate_ownerCard_le_of_minDegree
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree ownerCard : R → ℕ)
    (dMin degreeMass ownerCap : ℕ)
    (hdpos : 0 < dMin)
    (hdegree : ∀ r ∈ Rs, dMin ≤ degree r)
    (hmass : (∑ r ∈ Rs, degree r) ≤ degreeMass)
    (howner : ∀ r ∈ Rs, ownerCard r ≤ ownerCap) :
    (∑ r ∈ Rs, ownerCard r) ≤
      (degreeMass / dMin) * ownerCap := by
  have hcardMul : Rs.card * dMin ≤ degreeMass := by
    calc
      Rs.card * dMin = ∑ _r ∈ Rs, dMin := by simp
      _ ≤ ∑ r ∈ Rs, degree r := by
        apply Finset.sum_le_sum
        intro r hr
        exact hdegree r hr
      _ ≤ degreeMass := hmass
  have hcard : Rs.card ≤ degreeMass / dMin := by
    rw [Nat.le_div_iff_mul_le hdpos]
    exact hcardMul
  calc
    (∑ r ∈ Rs, ownerCard r) ≤ ∑ _r ∈ Rs, ownerCap :=
      Finset.sum_le_sum howner
    _ = Rs.card * ownerCap := by simp
    _ ≤ (degreeMass / dMin) * ownerCap :=
      Nat.mul_le_mul_right ownerCap hcard
def bchksBoundaryHighFactorCount6400 : ℕ := 655
def bchksBoundaryExactCoreAllHighCap6400 : ℕ := 121410800
lemma bchksBoundary_exactCore_highFactorAggregate6400 :
    bchksBoundaryHighFactorCount6400 = 84607 / 129 ∧
      bchksBoundaryExactCoreAllHighCap6400 =
        bchksBoundaryHighFactorCount6400 *
          bchksBoundaryDirectIncidenceCap6400 ∧
      bchksBoundaryExactCoreAllHighCap6400 < bchksWeightedNumerator6400 := by
  norm_num [bchksBoundaryHighFactorCount6400,
    bchksBoundaryExactCoreAllHighCap6400,
    bchksBoundaryDirectIncidenceCap6400, bchksWeightedNumerator6400]
def bchksBoundaryCoreCodimension6400 : ℕ := 24
def bchksBoundaryTupleSize6400 : ℕ := 25
def bchksBoundaryTupleAmbient6400 : ℕ := 131097
def bchksBoundaryTupleIncidences6400 : ℕ := 54317
def bchksBoundaryCodim24PerFactorCap6400 : ℕ := 283842678462903
def bchksBoundaryCodim24AllHighCap6400 : ℕ := 185916954393201465
lemma bchksBoundary_codim24_parameters6400 :
    bchksBoundaryTupleSize6400 = bchksBoundaryCoreCodimension6400 + 1 ∧
      bchksBoundaryTupleAmbient6400 =
        bchksBoundaryOffCore6400 + bchksBoundaryCoreCodimension6400 ∧
      bchksBoundaryTupleIncidences6400 =
        bchksBoundaryDeficiency6400 + bchksBoundaryCoreCodimension6400 := by
  norm_num [bchksBoundaryTupleSize6400, bchksBoundaryCoreCodimension6400,
    bchksBoundaryTupleAmbient6400, bchksBoundaryOffCore6400,
    bchksBoundaryTupleIncidences6400, bchksBoundaryDeficiency6400]
lemma bchksBoundary_codim24_tupleCapacity6400 :
    (bchksBoundaryErrors6400 *
        fallingFactorial6400 bchksBoundaryTupleAmbient6400
          bchksBoundaryTupleSize6400) /
        fallingFactorial6400 bchksBoundaryTupleIncidences6400
          bchksBoundaryTupleSize6400 =
      bchksBoundaryCodim24PerFactorCap6400 := by
  norm_num [bchksBoundaryErrors6400, fallingFactorial6400,
    bchksBoundaryTupleAmbient6400, bchksBoundaryTupleSize6400,
    bchksBoundaryTupleIncidences6400, bchksBoundaryCodim24PerFactorCap6400,
    Finset.prod_range_succ]
lemma bchksBoundary_codim24_highFactorAggregate6400 :
    bchksBoundaryCodim24AllHighCap6400 =
        bchksBoundaryHighFactorCount6400 *
          bchksBoundaryCodim24PerFactorCap6400 ∧
      bchksBoundaryCodim24AllHighCap6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksBoundaryCodim24AllHighCap6400 =
        89062045606798535 := by
  norm_num [bchksBoundaryCodim24AllHighCap6400,
    bchksBoundaryHighFactorCount6400,
    bchksBoundaryCodim24PerFactorCap6400, bchksWeightedNumerator6400]
end BCHKSBoundaryCoreArrangement6400
end ProximityPrize.SubmissionLower
