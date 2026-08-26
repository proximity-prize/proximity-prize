import ProximityPrize.SubmissionLower.BCHKSFrobeniusGlobalMaxRankFork6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusProjectiveAffineLine6401

/-!
# Projective-section incidence for the degree-one defect branch

This file isolates the finite-geometry and Möbius algebra needed by a
possible degree-one closure.  It deliberately does not assert that the
benchmark's ownerwise primitive pairs supply the projective fibres appearing
in the interface.

* In projective dimension two, a regular point--line double count gives a
  line containing `37664452` selected owner points at the rank-defect mass.
  Taking one point from each owner fibre makes higher fibre weights harmless.
* In projective dimension three, if every owner fibre has vector dimension
  at least two, pairwise-disjointness makes them projective lines.  Every pair
  of skew lines has `(q+1)^2` transversals.  The resulting pair-incidence
  identity gives one line meeting at least `37664453` owner fibres.
* On either extracted non-fibre line the challenge is fractional-linear.
  A message identity affine after multiplication by its denominator converts
  exactly back to an affine owner line in the original challenge.

The rank-four theorem below takes the standard transversal pair-count
identity as an explicit hypothesis.  This is the smallest honest interface:
deriving that identity from concrete subspaces belongs to a finite-projective
geometry bridge, while deriving the subspaces from the h=1 syndrome branch
remains the coding-theoretic gap.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusProjectiveSectionLine6401

open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGlobalMaxRankFork6401
open BCHKSTwoFrobeniusModuleAudit6401

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

def projectivePlaneDenseLineFloor6401 : Nat := 37664452
def projectiveThreeSpaceDenseTransversalFloor6401 : Nat := 37664453

/-- The slightly weaker floor obtained after first classifying a rank-four
linear set as an `F_{q^2}`-subline and then averaging over its `F_q`-sublines. -/
def projectiveFq2SublineDenseFloor6401 : Nat := 37664452

/-! The unsplit positive-rank branch retains substantially more owner mass
than the later exact-support/rank strata.  These constants isolate the rich
line arithmetic needed by a degree-two h=1 pencil argument. -/

def positiveRankOwnerFloor6401 : Nat := 173591179194623459

def positiveRankDenseLineFloor6401 : Nat := 81471186

def positiveRankDenseTransversalFloor6401 : Nat := 81471187

/-- Prospective per-fibre spherical cap in the quadratic-pencil ledger. -/
def quadraticPencilFibreCap6401 : Nat := 17594603

/-- Number of projective lines in `PG(2,q)`. -/
def projectivePlaneLineCount6401 : Nat := q6401 ^ 2 + q6401 + 1

/-- Number of projective lines in `PG(3,q)`, namely the Gaussian binomial
coefficient `[4 choose 2]_q`. -/
def projectiveThreeSpaceLineCount6401 : Nat :=
  (q6401 ^ 2 + 1) * (q6401 ^ 2 + q6401 + 1)

/-- Number of points of `PG(1,q^2)`. -/
def projectiveFq2SublinePointCount6401 : Nat := q6401 ^ 2 + 1

/-- Number of `F_q`-sublines in `PG(1,q^2)`.  Equivalently this is
`|PGL(2,q^2)| / |PGL(2,q)| = q(q^2+1)`. -/
def projectiveFqSublineCount6401 : Nat :=
  q6401 * (q6401 ^ 2 + 1)

/-- Number of `F_q`-sublines of `PG(1,q^2)` through one point. -/
def projectiveFqSublineReplication6401 : Nat :=
  q6401 * (q6401 + 1)

/-- Elementary averaging for point incidences.  `count l` is the number of
selected points on line `l`; the caller supplies the already-double-counted
total incidence. -/
theorem exists_count_ge_of_sum_count
    {Line : Type*} [Fintype Line]
    (count : Line → Nat) (total threshold : Nat)
    (hsum : ∑ l, count l = total)
    (haverage : Fintype.card Line * (threshold - 1) < total) :
    ∃ l, threshold ≤ count l := by
  classical
  by_contra h
  push_neg at h
  have hpoint : ∀ l : Line, count l ≤ threshold - 1 := by
    intro l
    have hl := h l
    omega
  have hsumle : (∑ l, count l) ≤
      ∑ _l : Line, (threshold - 1) :=
    Finset.sum_le_sum fun l _ => hpoint l
  rw [hsum] at hsumle
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumle
  exact (Nat.not_lt_of_ge hsumle) haverage

/-- Pair-incidence averaging.  If `count l` owner fibres meet a projective
line `l`, the left side counts unordered pairs of owners through `l`. -/
theorem exists_count_ge_of_sum_choose_two
    {Line : Type*} [Fintype Line]
    (count : Line → Nat) (totalPairs threshold : Nat)
    (hsum : ∑ l, Nat.choose (count l) 2 = totalPairs)
    (haverage : Fintype.card Line * Nat.choose (threshold - 1) 2 <
      totalPairs) :
    ∃ l, threshold ≤ count l := by
  classical
  by_contra h
  push_neg at h
  have hpoint : ∀ l : Line,
      Nat.choose (count l) 2 ≤ Nat.choose (threshold - 1) 2 := by
    intro l
    apply Nat.choose_le_choose 2
    have hl := h l
    omega
  have hsumle : (∑ l, Nat.choose (count l) 2) ≤
      ∑ _l : Line, Nat.choose (threshold - 1) 2 :=
    Finset.sum_le_sum fun l _ => hpoint l
  rw [hsum] at hsumle
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumle
  exact (Nat.not_lt_of_ge hsumle) haverage

/-- Exact benchmark arithmetic for the projective-plane line average at the
global rank-defect owner floor. -/
theorem projectivePlane_denseLine_inequality6401 :
    projectivePlaneLineCount6401 *
        (projectivePlaneDenseLineFloor6401 - 1) <
      defectOwnerFloor6401 * (q6401 + 1) := by
  native_decide

/-- Abstract `PG(2,q)` endpoint.  The finite-geometry bridge only needs to
identify `Line` with the projective lines and prove the displayed incidence
sum. -/
theorem projectivePlane_exists_denseLine6401
    {Line : Type*} [Fintype Line]
    (count : Line → Nat)
    (hlineCount : Fintype.card Line = projectivePlaneLineCount6401)
    (hsum : ∑ l, count l = defectOwnerFloor6401 * (q6401 + 1)) :
    ∃ l, projectivePlaneDenseLineFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_count count
    (defectOwnerFloor6401 * (q6401 + 1))
    projectivePlaneDenseLineFloor6401 hsum
  rw [hlineCount]
  exact projectivePlane_denseLine_inequality6401

/-- Exact benchmark arithmetic for skew-line transversals in `PG(3,q)`.
The right side counts every unordered owner pair through all of its
`(q+1)^2` transversals. -/
theorem projectiveThreeSpace_denseTransversal_inequality6401 :
    projectiveThreeSpaceLineCount6401 *
        Nat.choose (projectiveThreeSpaceDenseTransversalFloor6401 - 1) 2 <
      Nat.choose defectOwnerFloor6401 2 * (q6401 + 1) ^ 2 := by
  native_decide

/-- Abstract rank-four transversal endpoint. -/
theorem projectiveThreeSpace_exists_denseTransversal6401
    {Line : Type*} [Fintype Line]
    (count : Line → Nat)
    (hlineCount : Fintype.card Line = projectiveThreeSpaceLineCount6401)
    (hpairCount : ∑ l, Nat.choose (count l) 2 =
      Nat.choose defectOwnerFloor6401 2 * (q6401 + 1) ^ 2) :
    ∃ l, projectiveThreeSpaceDenseTransversalFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_choose_two count
    (Nat.choose defectOwnerFloor6401 2 * (q6401 + 1) ^ 2)
    projectiveThreeSpaceDenseTransversalFloor6401 hpairCount
  rw [hlineCount]
  exact projectiveThreeSpace_denseTransversal_inequality6401

/-! ## Optional rank-four classification route

For a rank-four `F_q`-linear set in `PG(1,q^t)`, `4 ≤ t`, the number of
points of weight at least two is one of `1, 2, q+1, q^2+1`.  In the last
case every point has weight two, `t` is even, and the linear set is an
`F_{q^2}`-subline.  The next theorem isolates the only numerical use of that
classification in this benchmark.  The classification itself can instead be
proved elementarily by putting two weight-two fibres on the coordinate axes:
the remaining slopes are a coset of the scalar stabilizer of a two-dimensional
`F_q`-space, and that stabilizer with zero adjoined is `F_q` or `F_{q^2}`.
-/

theorem defectOwnerFloor_gt_projectiveLine6401 :
    q6401 + 1 < defectOwnerFloor6401 := by
  native_decide

/-- Abstract numerical endpoint of the rank-four weight classification. -/
theorem rankFour_heavyPointCount_eq_fq2Subline6401
    (heavyPointCount : Nat)
    (howners : defectOwnerFloor6401 ≤ heavyPointCount)
    (hclassification : heavyPointCount = 1 ∨
      heavyPointCount = 2 ∨
      heavyPointCount = q6401 + 1 ∨
      heavyPointCount = q6401 ^ 2 + 1) :
    heavyPointCount = q6401 ^ 2 + 1 := by
  rcases hclassification with h | h | h | h
  · subst heavyPointCount
    norm_num [defectOwnerFloor6401] at howners
  · subst heavyPointCount
    norm_num [defectOwnerFloor6401] at howners
  · subst heavyPointCount
    exfalso
    exact (Nat.not_lt_of_ge howners) defectOwnerFloor_gt_projectiveLine6401
  · exact h

/-- Exact benchmark arithmetic for averaging the owner subset over all
`F_q`-sublines of the classified `PG(1,q^2)`. -/
theorem projectiveFq2Subline_dense_inequality6401 :
    projectiveFqSublineCount6401 *
        (projectiveFq2SublineDenseFloor6401 - 1) <
      defectOwnerFloor6401 * projectiveFqSublineReplication6401 := by
  native_decide

/-- Abstract `F_{q^2}`-subline endpoint.  The incidence sum uses that every
point of `PG(1,q^2)` lies on `q(q+1)` of its `F_q`-sublines. -/
theorem projectiveFq2Subline_exists_denseFqSubline6401
    {FqSubline : Type*} [Fintype FqSubline]
    (count : FqSubline → Nat)
    (hsublineCount : Fintype.card FqSubline =
      projectiveFqSublineCount6401)
    (hsum : ∑ l, count l =
      defectOwnerFloor6401 * projectiveFqSublineReplication6401) :
    ∃ l, projectiveFq2SublineDenseFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_count count
    (defectOwnerFloor6401 * projectiveFqSublineReplication6401)
    projectiveFq2SublineDenseFloor6401 hsum
  rw [hsublineCount]
  exact projectiveFq2Subline_dense_inequality6401

/-! ## Unsplit positive-rank rich-line arithmetic -/

theorem positiveRank_projectivePlane_denseLine_inequality6401 :
    projectivePlaneLineCount6401 *
        (positiveRankDenseLineFloor6401 - 1) <
      positiveRankOwnerFloor6401 * (q6401 + 1) := by
  native_decide

theorem positiveRank_projectiveFq2Subline_dense_inequality6401 :
    projectiveFqSublineCount6401 *
        (positiveRankDenseLineFloor6401 - 1) <
      positiveRankOwnerFloor6401 * projectiveFqSublineReplication6401 := by
  native_decide

theorem positiveRank_projectiveThreeSpace_denseTransversal_inequality6401 :
    projectiveThreeSpaceLineCount6401 *
        Nat.choose (positiveRankDenseTransversalFloor6401 - 1) 2 <
      Nat.choose positiveRankOwnerFloor6401 2 * (q6401 + 1) ^ 2 := by
  native_decide

/-- The quadratic no-affine-curve fibre budget closes at four fibres, but
not at five; the two inequalities record the exact narrow margin. -/
theorem positiveRank_quadraticPencil_fourFibre_margin6401 :
    4 * quadraticPencilFibreCap6401 < positiveRankDenseLineFloor6401 := by
  native_decide

theorem positiveRank_quadraticPencil_fiveFibre_noMargin6401 :
    positiveRankDenseLineFloor6401 ≤
      5 * quadraticPencilFibreCap6401 := by
  native_decide

theorem positiveRank_projectivePlane_exists_denseLine6401
    {Line : Type*} [Fintype Line]
    (count : Line → Nat)
    (hlineCount : Fintype.card Line = projectivePlaneLineCount6401)
    (hsum : ∑ l, count l = positiveRankOwnerFloor6401 * (q6401 + 1)) :
    ∃ l, positiveRankDenseLineFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_count count
    (positiveRankOwnerFloor6401 * (q6401 + 1))
    positiveRankDenseLineFloor6401 hsum
  rw [hlineCount]
  exact positiveRank_projectivePlane_denseLine_inequality6401

theorem positiveRank_projectiveFq2Subline_exists_denseFqSubline6401
    {FqSubline : Type*} [Fintype FqSubline]
    (count : FqSubline → Nat)
    (hsublineCount : Fintype.card FqSubline =
      projectiveFqSublineCount6401)
    (hsum : ∑ l, count l =
      positiveRankOwnerFloor6401 * projectiveFqSublineReplication6401) :
    ∃ l, positiveRankDenseLineFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_count count
    (positiveRankOwnerFloor6401 * projectiveFqSublineReplication6401)
    positiveRankDenseLineFloor6401 hsum
  rw [hsublineCount]
  exact positiveRank_projectiveFq2Subline_dense_inequality6401

theorem positiveRank_projectiveThreeSpace_exists_denseTransversal6401
    {Line : Type*} [Fintype Line]
    (count : Line → Nat)
    (hlineCount : Fintype.card Line = projectiveThreeSpaceLineCount6401)
    (hpairCount : ∑ l, Nat.choose (count l) 2 =
      Nat.choose positiveRankOwnerFloor6401 2 * (q6401 + 1) ^ 2) :
    ∃ l, positiveRankDenseTransversalFloor6401 ≤ count l := by
  apply exists_count_ge_of_sum_choose_two count
    (Nat.choose positiveRankOwnerFloor6401 2 * (q6401 + 1) ^ 2)
    positiveRankDenseTransversalFloor6401 hpairCount
  rw [hlineCount]
  exact positiveRank_projectiveThreeSpace_denseTransversal_inequality6401

/-- If every fibre has dimension at least two and every pair fits disjointly
inside a four-dimensional ambient space, then the presence of another fibre
forces every fibre to have dimension exactly two. -/
theorem fibreDimension_eq_two_of_rank_four
    {Owner : Type*} (dimension : Owner → Nat)
    (hlower : ∀ z, 2 ≤ dimension z)
    (hbudget : ∀ z w, z ≠ w → dimension z + dimension w ≤ 4)
    (hanother : ∀ z : Owner, ∃ w : Owner, w ≠ z) :
    ∀ z, dimension z = 2 := by
  intro z
  obtain ⟨w, hw⟩ := hanother z
  have hsum := hbudget z w hw.symm
  have hwlower := hlower w
  have hzlower := hlower z
  omega

/-! ## Fractional-linear reparametrization of an owner line -/

/-- Polynomial intercept after undoing a fractional-linear parameter. -/
noncomputable def mobiusOwnerIntercept
    {F : Type*} [Field F] (a0 a1 b0 b1 : F)
    (Q0 Q1 : F[X]) : F[X] :=
  Polynomial.C ((a0 * b1 - a1 * b0)⁻¹) *
    (Polynomial.C a0 * Q1 - Polynomial.C a1 * Q0)

/-- Polynomial slope after undoing a fractional-linear parameter. -/
noncomputable def mobiusOwnerSlope
    {F : Type*} [Field F] (a0 a1 b0 b1 : F)
    (Q0 Q1 : F[X]) : F[X] :=
  Polynomial.C ((a0 * b1 - a1 * b0)⁻¹) *
    (Polynomial.C b0 * Q1 - Polynomial.C b1 * Q0)

/-- An affine identity after multiplication by the Möbius denominator is
exactly an affine owner identity in the original challenge. -/
theorem owner_eq_affine_of_mobius_scaled
    {F : Type*} [Field F]
    (a0 a1 b0 b1 t z : F) (P Q0 Q1 : F[X])
    (hdet : a0 * b1 - a1 * b0 ≠ 0)
    (hden : b0 + t * b1 ≠ 0)
    (hz : z = -(a0 + t * a1) / (b0 + t * b1))
    (hscaled : Polynomial.C (b0 + t * b1) * P =
      Q0 + Polynomial.C t * Q1) :
    P = mobiusOwnerIntercept a0 a1 b0 b1 Q0 Q1 +
      Polynomial.C z * mobiusOwnerSlope a0 a1 b0 b1 Q0 Q1 := by
  let d := a0 * b1 - a1 * b0
  let p0 := mobiusOwnerIntercept a0 a1 b0 b1 Q0 Q1
  let p1 := mobiusOwnerSlope a0 a1 b0 b1 Q0 Q1
  have hd : d ≠ 0 := by simpa [d] using hdet
  have hconst :
      Polynomial.C b0 * p0 - Polynomial.C a0 * p1 = Q0 := by
    calc
      Polynomial.C b0 * p0 - Polynomial.C a0 * p1 =
          Polynomial.C (d⁻¹ * d) * Q0 := by
            simp only [p0, p1, mobiusOwnerIntercept, mobiusOwnerSlope,
              d, map_mul, map_sub]
            ring
      _ = Q0 := by rw [inv_mul_cancel₀ hd]; simp
  have hslope :
      Polynomial.C b1 * p0 - Polynomial.C a1 * p1 = Q1 := by
    calc
      Polynomial.C b1 * p0 - Polynomial.C a1 * p1 =
          Polynomial.C (d⁻¹ * d) * Q1 := by
            simp only [p0, p1, mobiusOwnerIntercept, mobiusOwnerSlope,
              d, map_mul, map_sub]
            ring
      _ = Q1 := by rw [inv_mul_cancel₀ hd]; simp
  have hbz : (b0 + t * b1) * z = -(a0 + t * a1) := by
    rw [hz]
    field_simp [hden]
  have hlinear :
      Polynomial.C (b0 + t * b1) * (p0 + Polynomial.C z * p1) =
        Q0 + Polynomial.C t * Q1 := by
    calc
      Polynomial.C (b0 + t * b1) *
          (p0 + Polynomial.C z * p1) =
          Polynomial.C (b0 + t * b1) * p0 +
            Polynomial.C ((b0 + t * b1) * z) * p1 := by
              simp only [map_mul]
              ring
      _ = Polynomial.C (b0 + t * b1) * p0 -
            Polynomial.C (a0 + t * a1) * p1 := by
              rw [hbz]
              simp
              ring
      _ = (Polynomial.C b0 * p0 - Polynomial.C a0 * p1) +
            Polynomial.C t *
              (Polynomial.C b1 * p0 - Polynomial.C a1 * p1) := by
                simp only [map_add, map_mul]
                ring
      _ = Q0 + Polynomial.C t * Q1 := by rw [hconst, hslope]
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hden)
  rw [hscaled, hlinear]

/-- The Möbius conversion preserves a common polynomial degree cap. -/
theorem mobiusOwner_degreeCaps
    {F : Type*} [Field F]
    (a0 a1 b0 b1 : F) (Q0 Q1 : F[X]) (D : Nat)
    (hQ0 : Q0.natDegree ≤ D) (hQ1 : Q1.natDegree ≤ D) :
    (mobiusOwnerIntercept a0 a1 b0 b1 Q0 Q1).natDegree ≤ D ∧
      (mobiusOwnerSlope a0 a1 b0 b1 Q0 Q1).natDegree ≤ D := by
  have hlinear : ∀ c0 c1 : F,
      (Polynomial.C c0 * Q1 - Polynomial.C c1 * Q0).natDegree ≤ D := by
    intro c0 c1
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by simpa using hQ1)
    · exact Polynomial.natDegree_mul_le.trans (by simpa using hQ0)
  constructor
  · unfold mobiusOwnerIntercept
    exact Polynomial.natDegree_mul_le.trans
      (by simpa using hlinear a0 a1)
  · unfold mobiusOwnerSlope
    exact Polynomial.natDegree_mul_le.trans
      (by simpa using hlinear b0 b1)

end BCHKSFrobeniusProjectiveSectionLine6401
end ProximityPrize.SubmissionLower
