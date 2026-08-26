import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower
namespace BCHKSGaoSpecializationCore6400

open Polynomial

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
# Specialization core for the degree-53 Gao lane

This file proves only the finite-matrix algebra surrounding a prospective
application of Gao's PDE factorization theorem.  In particular, it does **not**
assert Gao's theorem or manufacture the generic-rank hypothesis needed by the
benchmark.

For a matrix over `K[Z]`, a selected square minor is a polynomial in `Z`.
Evaluation commutes with both selection and determinant.  If the specialized
full matrix acquires more kernel dimension than its generic corank, the fixed
maximal minor vanishes.  Finally, its `Z`-degree is bounded by the sum of the
individual row caps, rather than by `number of rows * maximum cap`.
-/

section Specialization

variable {R S : Type*} [CommRing R] [CommRing S]
variable {Rows Cols I J : Type*}

/-- Mapping entries and then selecting rows and columns is definitionally the
same as selecting first and mapping afterward. -/
theorem mapMatrix_submatrix (phi : R →+* S) (M : Matrix Rows Cols R)
    (rows : I → Rows) (cols : J → Cols) :
    (M.submatrix rows cols).map phi =
      (M.map phi).submatrix rows cols := by
  rfl

/-- A ring specialization commutes with the determinant of a fixed submatrix. -/
theorem map_submatrix_det [Fintype I] [DecidableEq I]
    (phi : R →+* S) (M : Matrix Rows Cols R)
    (rows : I → Rows) (cols : I → Cols) :
    phi (M.submatrix rows cols).det =
      ((M.map phi).submatrix rows cols).det := by
  rw [RingHom.map_det]
  rfl

/-- Polynomial evaluation is the specialization used in the bad-fiber count. -/
theorem eval_submatrix_det
    {K : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    (z : K) (M : Matrix Rows Cols K[X])
    (rows : I → Rows) (cols : I → Cols) :
    Polynomial.eval z (M.submatrix rows cols).det =
      ((M.map (Polynomial.evalRingHom z)).submatrix rows cols).det := by
  exact map_submatrix_det (Polynomial.evalRingHom z) M rows cols

end Specialization

section Degree

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- Row-sensitive determinant degree.  This is the exact form needed for the
mixed-Hermite ledger: every determinant term uses one entry from each row, so
the degree cost is the sum of the row caps. -/
theorem natDegree_det_le_sum_rowCaps
    (M : Matrix I I K[X]) (rowCap : I → ℕ)
    (hentry : ∀ i j, (M i j).natDegree ≤ rowCap i) :
    M.det.natDegree ≤ ∑ i, rowCap i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro sigma _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simpa using hentry i (sigma i)

/-- Uniform-cap corollary, retained only for comparison with the sharper
row-sensitive ledger. -/
theorem natDegree_det_le_card_mul
    (M : Matrix I I K[X]) (cap : ℕ)
    (hentry : ∀ i j, (M i j).natDegree ≤ cap) :
    M.det.natDegree ≤ Fintype.card I * cap := by
  calc
    M.det.natDegree ≤ ∑ _i : I, cap :=
      natDegree_det_le_sum_rowCaps M (fun _ ↦ cap) hentry
    _ = Fintype.card I * cap := by simp

end Degree

section KernelJump

variable {K Rows Cols : Type*} [Field K]
variable [Fintype Cols]

/-- Rank-nullity for a matrix, stated in the orientation used below. -/
theorem rank_add_finrank_ker_mulVecLin
    (A : Matrix Rows Cols K) :
    A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) =
      Fintype.card Cols := by
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    A.mulVecLin.finrank_range_add_finrank_ker

/-- If a `q` by `q` selected minor is nonsingular, the full matrix has rank at
least `q`.  No injectivity assumptions on the selection maps are needed: a
nonsingular minor forces them automatically. -/
theorem rank_ge_of_submatrix_det_ne_zero
    (A : Matrix Rows Cols K) (q : ℕ)
    (rows : Fin q → Rows) (cols : Fin q → Cols)
    (hminor : (A.submatrix rows cols).det ≠ 0) :
    q ≤ A.rank := by
  classical
  have hli : LinearIndependent K (fun i ↦ (A.submatrix rows cols) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hminor
  have hrank : (A.submatrix rows cols).rank = q := by
    simpa only [Fintype.card_fin] using
      (LinearIndependent.rank_matrix
        (M := A.submatrix rows cols) hli)
  rw [← hrank]
  exact Matrix.rank_submatrix_le A rows cols

/-- A kernel jump past the generic corank forces every fixed `q`-minor to
vanish.  This is the linear-algebra implication used when the factor count (and
hence the Gao kernel dimension) rises after specialization. -/
theorem submatrix_det_eq_zero_of_finrank_ker_gt_corank
    (A : Matrix Rows Cols K) (q : ℕ)
    (rows : Fin q → Rows) (cols : Fin q → Cols)
    (hq : q ≤ Fintype.card Cols)
    (hjump : Fintype.card Cols - q <
      Module.finrank K (LinearMap.ker A.mulVecLin)) :
    (A.submatrix rows cols).det = 0 := by
  classical
  by_contra hminor
  have hqrank : q ≤ A.rank :=
    rank_ge_of_submatrix_det_ne_zero A q rows cols hminor
  have hrankNull := rank_add_finrank_ker_mulVecLin A
  omega

/-- The fixed-minor bad-fiber lemma over `K[Z]`.  The first conclusion records
that the selected polynomial really is a nonzero generic minor; the second is
the specialization vanishing forced by a kernel jump.

The generic nonvanishing is deliberately an input.  Constructing such a minor
from Gao's PDE theorem is the first missing benchmark-specific theorem. -/
theorem fixed_nonzero_minor_vanishes_of_specialized_kernel_jump
    (M : Matrix Rows Cols K[X]) (q : ℕ)
    (rows : Fin q → Rows) (cols : Fin q → Cols)
    (z : K)
    (hgeneric : (M.submatrix rows cols).det ≠ 0)
    (hq : q ≤ Fintype.card Cols)
    (hjump : Fintype.card Cols - q <
      Module.finrank K
        (LinearMap.ker (M.map (Polynomial.evalRingHom z)).mulVecLin)) :
    (M.submatrix rows cols).det ≠ 0 ∧
      Polynomial.eval z (M.submatrix rows cols).det = 0 := by
  refine ⟨hgeneric, ?_⟩
  rw [eval_submatrix_det]
  exact submatrix_det_eq_zero_of_finrank_ker_gt_corank
    (M.map (Polynomial.evalRingHom z)) q rows cols hq hjump

/-- Root-count form of the specialization argument.  On any finite candidate
set, the number of fibers whose kernel dimension exceeds the generic corank is
at most the sum of the selected minor's row degree caps. -/
theorem card_kernelJumpFibers_le_sum_rowCaps
    (M : Matrix Rows Cols K[X]) (q : ℕ)
    (rows : Fin q → Rows) (cols : Fin q → Cols)
    (rowCap : Fin q → ℕ)
    (hentry : ∀ i j,
      (M (rows i) (cols j)).natDegree ≤ rowCap i)
    (T : Finset K)
    (hgeneric : (M.submatrix rows cols).det ≠ 0)
    (hq : q ≤ Fintype.card Cols) :
    (T.filter fun z ↦ Fintype.card Cols - q <
      Module.finrank K
        (LinearMap.ker (M.map (Polynomial.evalRingHom z)).mulVecLin)).card ≤
      ∑ i, rowCap i := by
  classical
  let D : K[X] := (M.submatrix rows cols).det
  have hdeg : D.natDegree ≤ ∑ i, rowCap i := by
    apply natDegree_det_le_sum_rowCaps
    intro i j
    exact hentry i j
  calc
    (T.filter fun z ↦ Fintype.card Cols - q <
        Module.finrank K
          (LinearMap.ker (M.map (Polynomial.evalRingHom z)).mulVecLin)).card
        ≤ D.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      have hjump := (Finset.mem_filter.mp
        (show z ∈ T.filter fun z ↦ Fintype.card Cols - q <
          Module.finrank K
            (LinearMap.ker
              (M.map (Polynomial.evalRingHom z)).mulVecLin) from hz)).2
      apply (Polynomial.mem_roots hgeneric).2
      rw [Polynomial.IsRoot.def]
      exact (fixed_nonzero_minor_vanishes_of_specialized_kernel_jump
        M q rows cols z hgeneric hq hjump).2
    _ ≤ ∑ i, rowCap i := hdeg

end KernelJump

/-!
## Exact interface still missing from the degree-53 route

Gao, *Factoring Multivariate Polynomials via Partial Differential Equations*,
Math. Comp. 72 (2003), Theorem 2.3, assumes:

* a field of characteristic `p`;
* `f ∈ F[x,y]` of exact bidegree `(m,n)`;
* `gcd(f, ∂f/∂x) = 1`;
* `r` distinct irreducible factors of `f` over an algebraic closure;
* characteristic zero or `p > (2*m-1)*n`.

The PDE unknowns obey `deg g ≤ (m-1,n)` and
`deg h ≤ (m,n-1)`, and satisfy

`f * (∂g/∂y - ∂h/∂x) + h * ∂f/∂x - g * ∂f/∂y = 0`.

The conclusion is that the solution space projected to `g` has dimension `r`
both over the ground field and over its algebraic closure; over the closure its
elements are the linear combinations of
`E_i = (f/f_i) * ∂f_i/∂x`.

The definitions below transcribe those hypotheses and conclusions.  In
particular, `gaoTheorem23FormalizationTarget` is merely a `Prop`; this file does
not contain a theorem inhabiting it.
-/

abbrev BiPoly (K : Type*) [Semiring K] := Polynomial (Polynomial K)

/-- Coefficientwise `X` derivative for the representation `K[X][Y]`. -/
noncomputable def partialX
    {K : Type*} [CommRing K] (f : BiPoly K) : BiPoly K :=
  f.sum fun j a ↦ Polynomial.monomial j a.derivative

/-- Outer-variable (`Y`) derivative. -/
noncomputable def partialY
    {K : Type*} [CommRing K] (f : BiPoly K) : BiPoly K :=
  f.derivative

/-- Gao's cleared PDE, equation (5) in the paper. -/
def SatisfiesGaoPDE
    {K : Type*} [CommRing K] (f g h : BiPoly K) : Prop :=
  f * (partialY g - partialX h) +
      h * partialX f - g * partialY f = 0

/-- The paper's convention that a negative degree cap forces the polynomial to
be zero, encoded without integer-valued polynomial degrees. -/
def degreeXAtMostPred
    {K : Type*} [CommRing K] (m : ℕ) (g : BiPoly K) : Prop :=
  match m with
  | 0 => g = 0
  | m + 1 => Polynomial.Bivariate.degreeX g ≤ m

/-- The analogous predecessor cap in the outer (`Y`) variable. -/
def degreeYAtMostPred
    {K : Type*} [CommRing K] (n : ℕ) (h : BiPoly K) : Prop :=
  match n with
  | 0 => h = 0
  | n + 1 => h.natDegree ≤ n

/-- Degree box (4) of Gao's paper:
`deg g ≤ (m-1,n)` and `deg h ≤ (m,n-1)`. -/
def GaoDegreeBox
    {K : Type*} [CommRing K] (m n : ℕ) (g h : BiPoly K) : Prop :=
  degreeXAtMostPred m g ∧ g.natDegree ≤ n ∧
    Polynomial.Bivariate.degreeX h ≤ m ∧ degreeYAtMostPred n h

/-- Projection of the bounded PDE-pair space onto its `g` coordinate.  Under
`IsCoprime f (∂f/∂x)`, the accompanying `h` is unique. -/
def GaoProjectedSolution
    {K : Type*} [Field K] (f : BiPoly K) (m n : ℕ)
    (g : BiPoly K) : Prop :=
  ∃ h : BiPoly K, GaoDegreeBox m n g h ∧ SatisfiesGaoPDE f g h

/-- Extend both coefficient layers of a bivariate polynomial. -/
noncomputable def mapBivariate
    {K L : Type*} [Field K] [Field L]
    (phi : K →+* L) (f : BiPoly K) : BiPoly L :=
  f.map (Polynomial.mapRingHom phi)

/-- A chosen factorization over an algebraic closure into pairwise
nonassociated irreducibles.  The scalar records the unit suppressed by the
paper's product notation. -/
structure GaoAbsoluteFactorization
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f : BiPoly K) (r : ℕ) where
  factors : Fin r → BiPoly L
  scalar : Lˣ
  irreducible : ∀ i, Irreducible (factors i)
  pairwiseNonassociated :
    ∀ i j, i ≠ j → ¬ Associated (factors i) (factors j)
  product_eq :
    mapBivariate (algebraMap K L) f =
      Polynomial.C (Polynomial.C (scalar : L)) * ∏ i, factors i

/-- `E_i = (f/f_i) * ∂f_i/∂x`, including the scalar unit in the
chosen absolute factorization. -/
noncomputable def GaoAbsoluteFactorization.logarithmicX
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : BiPoly K} {r : ℕ}
    (fac : GaoAbsoluteFactorization K L f r) (i : Fin r) : BiPoly L :=
  (Polynomial.C (Polynomial.C (fac.scalar : L)) *
      ∏ j ∈ Finset.univ.erase i, fac.factors j) *
    partialX (fac.factors i)

/-- Exact hypotheses of Gao Theorem 2.3, with an explicit chosen algebraic
closure and absolute factorization. -/
structure GaoTheorem23Hypotheses
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : BiPoly K) (m n r : ℕ) where
  bidegreeX : Polynomial.Bivariate.degreeX f = m
  bidegreeY : f.natDegree = n
  coprimeX : IsCoprime f (partialX f)
  absoluteFactorization : GaoAbsoluteFactorization K L f r
  characteristicBound :
    ringChar K = 0 ∨ (2 * m - 1) * n < ringChar K

/-- Exact conclusion of Gao Theorem 2.3.  The submodules are explicit fields
because constructing them from the PDE predicate is itself part of the future
formalization.  The final equality encodes equation (9), not merely its easy
one-sided containment. -/
structure GaoTheorem23Conclusion
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : BiPoly K) (m n r : ℕ)
    (fac : GaoAbsoluteFactorization K L f r) where
  groundSolutions : Submodule K (BiPoly K)
  groundSolutions_spec :
    ∀ g, g ∈ groundSolutions ↔ GaoProjectedSolution f m n g
  groundDimension : Module.finrank K groundSolutions = r
  closureSolutions : Submodule L (BiPoly L)
  closureSolutions_spec :
    ∀ g, g ∈ closureSolutions ↔
      GaoProjectedSolution (mapBivariate (algebraMap K L) f) m n g
  closureDimension : Module.finrank L closureSolutions = r
  closure_eq_span_logarithmicX :
    closureSolutions =
      Submodule.span L (Set.range fac.logarithmicX)

/-- Precise, unproved formalization target for Gao Theorem 2.3.  Having this
definition in scope creates no assumption: downstream code must provide an
actual proof before it may use the conclusion. -/
def gaoTheorem23FormalizationTarget
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : BiPoly K) (m n r : ℕ) : Prop :=
  ∀ h : GaoTheorem23Hypotheses K L f m n r,
    Nonempty (GaoTheorem23Conclusion K L f m n r h.absoluteFactorization)

/-- The degree-53 endpoint satisfies Gao's strict characteristic hypothesis
with `m = 53` and `n = 9,769,998`. -/
lemma bchksDegree53GaoCharacteristicBound6400 :
    (2 * 53 - 1) * 9769998 < 2130706433 := by
  norm_num

/-!
For the benchmark, Gao's theorem must additionally be connected to the concrete
sparse coefficient matrix and to its unrestricted top-edge column set.  The
following structure is the honest, minimal matrix-level interface for that last
step.  It is a proposition to be proved at the call site, not a declaration of
the missing result.
-/

/-- Matrix-level output required from a future formalization of Gao Theorem 2.3.
`genericKernelDim` is the number of absolute factors.  The equality fixes the
kernel dimension of the concrete PDE matrix; `existsMaximalMinor` selects the
minor used by the specialization lemmas above. -/
structure GaoKernelRankInterface
    (K : Type*) [Field K]
    (Rows Cols : Type*) [Fintype Rows] [Fintype Cols]
    (M : Matrix Rows Cols K) (genericKernelDim : ℕ) : Prop where
  kernelDimension :
    Module.finrank K (LinearMap.ker M.mulVecLin) = genericKernelDim
  kernelDim_le_columns : genericKernelDim ≤ Fintype.card Cols
  existsMaximalMinor :
    ∃ (rows : Fin (Fintype.card Cols - genericKernelDim) → Rows)
      (cols : Fin (Fintype.card Cols - genericKernelDim) → Cols),
      (M.submatrix rows cols).det ≠ 0

end BCHKSGaoSpecializationCore6400
end ProximityPrize.SubmissionLower
