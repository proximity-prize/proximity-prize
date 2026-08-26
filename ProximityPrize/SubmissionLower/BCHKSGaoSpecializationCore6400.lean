import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower
namespace BCHKSGaoSpecializationCore6400
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section Specialization
variable {R S : Type*} [CommRing R] [CommRing S]
variable {Rows Cols I J : Type*}
theorem mapMatrix_submatrix (phi : R →+* S) (M : Matrix Rows Cols R)
    (rows : I → Rows) (cols : J → Cols) :
    (M.submatrix rows cols).map phi =
      (M.map phi).submatrix rows cols := by
  rfl
theorem map_submatrix_det [Fintype I] [DecidableEq I]
    (phi : R →+* S) (M : Matrix Rows Cols R)
    (rows : I → Rows) (cols : I → Cols) :
    phi (M.submatrix rows cols).det =
      ((M.map phi).submatrix rows cols).det := by
  rw [RingHom.map_det]
  rfl
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
theorem rank_add_finrank_ker_mulVecLin
    (A : Matrix Rows Cols K) :
    A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) =
      Fintype.card Cols := by
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
    A.mulVecLin.finrank_range_add_finrank_ker
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
abbrev BiPoly (K : Type*) [Semiring K] := Polynomial (Polynomial K)
noncomputable def partialX
    {K : Type*} [CommRing K] (f : BiPoly K) : BiPoly K :=
  f.sum fun j a ↦ Polynomial.monomial j a.derivative
noncomputable def partialY
    {K : Type*} [CommRing K] (f : BiPoly K) : BiPoly K :=
  f.derivative
def SatisfiesGaoPDE
    {K : Type*} [CommRing K] (f g h : BiPoly K) : Prop :=
  f * (partialY g - partialX h) +
      h * partialX f - g * partialY f = 0
def degreeXAtMostPred
    {K : Type*} [CommRing K] (m : ℕ) (g : BiPoly K) : Prop :=
  match m with
  | 0 => g = 0
  | m + 1 => Polynomial.Bivariate.degreeX g ≤ m
def degreeYAtMostPred
    {K : Type*} [CommRing K] (n : ℕ) (h : BiPoly K) : Prop :=
  match n with
  | 0 => h = 0
  | n + 1 => h.natDegree ≤ n
def GaoDegreeBox
    {K : Type*} [CommRing K] (m n : ℕ) (g h : BiPoly K) : Prop :=
  degreeXAtMostPred m g ∧ g.natDegree ≤ n ∧
    Polynomial.Bivariate.degreeX h ≤ m ∧ degreeYAtMostPred n h
def GaoProjectedSolution
    {K : Type*} [Field K] (f : BiPoly K) (m n : ℕ)
    (g : BiPoly K) : Prop :=
  ∃ h : BiPoly K, GaoDegreeBox m n g h ∧ SatisfiesGaoPDE f g h
noncomputable def mapBivariate
    {K L : Type*} [Field K] [Field L]
    (phi : K →+* L) (f : BiPoly K) : BiPoly L :=
  f.map (Polynomial.mapRingHom phi)
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
noncomputable def GaoAbsoluteFactorization.logarithmicX
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : BiPoly K} {r : ℕ}
    (fac : GaoAbsoluteFactorization K L f r) (i : Fin r) : BiPoly L :=
  (Polynomial.C (Polynomial.C (fac.scalar : L)) *
      ∏ j ∈ Finset.univ.erase i, fac.factors j) *
    partialX (fac.factors i)
structure GaoTheorem23Hypotheses
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : BiPoly K) (m n r : ℕ) where
  bidegreeX : Polynomial.Bivariate.degreeX f = m
  bidegreeY : f.natDegree = n
  coprimeX : IsCoprime f (partialX f)
  absoluteFactorization : GaoAbsoluteFactorization K L f r
  characteristicBound :
    ringChar K = 0 ∨ (2 * m - 1) * n < ringChar K
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
def gaoTheorem23FormalizationTarget
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (f : BiPoly K) (m n r : ℕ) : Prop :=
  ∀ h : GaoTheorem23Hypotheses K L f m n r,
    Nonempty (GaoTheorem23Conclusion K L f m n r h.absoluteFactorization)
lemma bchksDegree53GaoCharacteristicBound6400 :
    (2 * 53 - 1) * 9769998 < 2130706433 := by
  norm_num
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
