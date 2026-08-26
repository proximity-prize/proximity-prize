import ProximityPrize.SubmissionLower.BCHKSHybridHighDegreeAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSBoundaryCoreArrangement6400

open Polynomial

/-!
Arithmetic and abstract counting audit for the full-core line-arrangement
escape from the degree-129 hybrid boundary.

At exact maximum nonalignment weight

`w = d*185364 - 54293 - 1`,

the margin-one cofactor inequality and the nonalignment deficiency dichotomy
force deficiency exactly `54293`.  Hence there are exactly `k=131071`
full-order received coordinates.  Interpolating the two received rows on
this core gives `P0,P1`, and every owner polynomial has the form

`P_z = P0 + z*P1 + c_z*G_core`.

Every one of the remaining `54293` agreements puts `(z,c_z)` on one of the
`131073=n-k` fixed affine lines indexed by the off-core coordinates.  In a
no-alignment family, each indexed line contains at most `e=76780` challenge
points.  Plain incidence double counting therefore gives the sharper bound

`floor(131073*76780/54293) = 185360`

per exact-core owner factor.  The earlier pair-intersection argument gives
the valid but weaker `311778` bound, also recorded below.

More generally, if the common full core has codimension `s`, write

`P_z = P0 + z*P1 + G_core*C_z`,  `deg C_z <= s`.

Any `s+1` distinct off-core agreement coordinates determine `C_z`
affinely in `z` by a Vandermonde system.  Thus, in a no-alignment family,
each coordinate tuple can occur for at most `e` challenges.  The abstract
double-count interface below yields

`L * (g+s)_(s+1) <= e * (n-k+s)_(s+1)`,

where `(a)_t` is a falling factorial.  Through `s=24`, even summing over all
possible degree-at-least-129 factors costs less than the challenge
numerator.  Formalizing the polynomial representation and Vandermonde tuple
fibre bound is still required; this file does not assume it silently.
-/

def bchksBoundaryOffCore6400 : ℕ := 131073
def bchksBoundaryDeficiency6400 : ℕ := 54293
def bchksBoundaryErrors6400 : ℕ := 76780
def bchksBoundaryPairArrangementCap6400 : ℕ := 311778
def bchksBoundaryDirectIncidenceCap6400 : ℕ := 185360

/-- Division-free numerical bridge from maximum nonalignment weight to an
exact full core.  In the application, `w<total` is the margin-one cofactor
conclusion and `total≤d*a-deficiency` comes from the local-order profile. -/
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

/-! ## Polynomial core representation -/

/-- Locator of a fixed coordinate core. -/
noncomputable def coreLocator6400
    {F I : Type*} [Field F] [DecidableEq I]
    (core : Finset I) (omega : I → F) : F[X] :=
  ∏ i ∈ core, (Polynomial.X - Polynomial.C (omega i))

/-- Vanishing on an injectively located core gives a locator quotient, with
the exact codimension degree bound.  This is the algebraic representation
behind `P_z=P0+zP1+G_core*C_z`; it is unconditional and does not invoke the
still-missing owner/full-order bridge. -/
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

/-- `s+1` injectively located evaluations determine a polynomial of degree at
most `s`.  This is the Vandermonde uniqueness fact needed after interpolation
constructs the two affine coefficient polynomials. -/
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

/-- Falling factorial `(n)_t`. -/
def fallingFactorial6400 (n t : ℕ) : ℕ :=
  ∏ i ∈ Finset.range t, (n - i)

/-- The division-free abstract end of the tuple double count. -/
theorem card_le_tupleCapacity
    (L N r t e : ℕ)
    (hpos : 0 < fallingFactorial6400 r t)
    (hcount : L * fallingFactorial6400 r t ≤
      e * fallingFactorial6400 N t) :
    L ≤ (e * fallingFactorial6400 N t) /
      fallingFactorial6400 r t := by
  rw [Nat.le_div_iff_mul_le hpos]
  exact hcount

/-- Exact arithmetic of the original light-pair/heavy-line estimate. -/
lemma bchksBoundary_pairArrangement_exact6400 :
    (bchksBoundaryOffCore6400 * (bchksBoundaryOffCore6400 - 1) / 2) /
          (bchksBoundaryDeficiency6400 - 1) +
        (bchksBoundaryOffCore6400 / bchksBoundaryDeficiency6400) *
          bchksBoundaryErrors6400 =
      bchksBoundaryPairArrangementCap6400 := by
  norm_num [bchksBoundaryOffCore6400, bchksBoundaryDeficiency6400,
    bchksBoundaryErrors6400, bchksBoundaryPairArrangementCap6400]

/-- Direct indexed-line incidence counting is stronger at exact core size. -/
lemma bchksBoundary_directIncidence_exact6400 :
    (bchksBoundaryOffCore6400 * bchksBoundaryErrors6400) /
        bchksBoundaryDeficiency6400 =
      bchksBoundaryDirectIncidenceCap6400 ∧
    bchksBoundaryDirectIncidenceCap6400 <
      bchksBoundaryPairArrangementCap6400 := by
  norm_num [bchksBoundaryOffCore6400, bchksBoundaryDeficiency6400,
    bchksBoundaryErrors6400, bchksBoundaryDirectIncidenceCap6400,
    bchksBoundaryPairArrangementCap6400]

/-- Generic aggregation over factors of minimum degree `dMin`. -/
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

/-! ## Core-codimension 24 endpoint -/

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

/-- Exact falling-factorial quotient at core codimension 24. -/
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
