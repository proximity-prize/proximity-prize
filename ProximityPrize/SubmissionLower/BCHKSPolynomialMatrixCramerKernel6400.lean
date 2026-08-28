import ProximityPrize.SubmissionLower.BCHKSLocatorCramerSelection6400

/-!
# Explicit polynomial kernel vectors from a nonsingular minor

For a block row matrix `[A | B]` with square pivot block `A`, each free
column of `B` gives the denominator-cleared Cramer relation

`(-cramer A B_j, det(A) e_j)`.

This module packages that construction, proves its kernel and degree bounds,
and will be used to avoid invoking a full minimal-polynomial-kernel-basis
theorem in the score-64 locator argument.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open scoped Matrix

set_option autoImplicit false

/-- The denominator-cleared Cramer relation belonging to one free column. -/
noncomputable def polynomialCramerKernelVector
    {R I J : Type} [CommRing R]
    [Fintype I] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I R) (B : Matrix I J R) (j : J) : I ⊕ J → R
  | Sum.inl i => -Matrix.cramer A (fun row => B row j) i
  | Sum.inr k => if k = j then A.det else 0

/-- The rectangular block row matrix `[A | B]`. -/
def polynomialBlockTopMatrix
    {R I J : Type} [CommRing R]
    (A : Matrix I I R) (B : Matrix I J R) : Matrix I (I ⊕ J) R
  | row, Sum.inl i => A row i
  | row, Sum.inr j => B row j

/-- The Cramer relation annihilates the pivot rows over the original ring. -/
theorem blockTop_mulVec_polynomialCramerKernelVector
    {R I J : Type} [CommRing R]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I R) (B : Matrix I J R) (j : J) :
    (polynomialBlockTopMatrix A B) *ᵥ
        polynomialCramerKernelVector A B j = 0 := by
  funext row
  rw [show ((polynomialBlockTopMatrix A B) *ᵥ
        polynomialCramerKernelVector A B j) row =
      ∑ col : I ⊕ J, polynomialBlockTopMatrix A B row col *
          polynomialCramerKernelVector A B j col by
    rfl]
  rw [Fintype.sum_sum_type]
  simp only [polynomialCramerKernelVector, mul_neg, Finset.sum_neg_distrib,
    polynomialBlockTopMatrix]
  rw [show ∑ i : I, A row i * Matrix.cramer A (fun r => B r j) i =
      (A *ᵥ Matrix.cramer A (fun r => B r j)) row by rfl,
    Matrix.mulVec_cramer]
  simp [Pi.smul_apply, smul_eq_mul] <;> ring

/-- Every coordinate of an explicit Cramer kernel vector has the determinant
degree bound `#pivot * S`. -/
theorem polynomialCramerKernelVector_natDegree_le_card_mul
    {F I J : Type} [Field F]
    [Fintype I] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I F[X]) (B : Matrix I J F[X]) (S : ℕ)
    (hA : ∀ i k, (A i k).natDegree ≤ S)
    (hB : ∀ i j, (B i j).natDegree ≤ S)
    (j : J) (col : I ⊕ J) :
    (polynomialCramerKernelVector A B j col).natDegree ≤
      Fintype.card I * S := by
  cases col with
  | inl i =>
      simpa [polynomialCramerKernelVector] using
        polynomialMatrix_cramer_natDegree_le_card_mul A
          (fun row => B row j) S hA (fun row => hB row j) i
  | inr k =>
      by_cases hkj : k = j
      · subst k
        simpa [polynomialCramerKernelVector] using
          polynomialMatrix_det_natDegree_le_card_mul A S hA
      · simp [polynomialCramerKernelVector, hkj]

/-- Map an explicit Cramer relation into a field. -/
noncomputable def mappedPolynomialCramerKernelVector
    {R K I J : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [DecidableEq J]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R) (j : J) :
    I ⊕ J → K :=
  f ∘ polynomialCramerKernelVector A B j

/-- A nonzero mapped pivot determinant makes the free-column Cramer
relations linearly independent. -/
theorem linearIndependent_mappedPolynomialCramerKernelVector
    {R K I J : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R)
    (hdet : f A.det ≠ 0) :
    LinearIndependent K
      (mappedPolynomialCramerKernelVector f A B) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hj := congrFun hc (Sum.inr j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mappedPolynomialCramerKernelVector, Function.comp_apply,
    polynomialCramerKernelVector, Pi.zero_apply] at hj
  have hsum :
      (∑ x, c x * f (if j = x then A.det else 0)) =
        c j * f A.det := by
    calc
      (∑ x, c x * f (if j = x then A.det else 0)) =
          ∑ x, if x = j then c x * f A.det else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxj : x = j
        · subst x
          simp
        · simp [hxj, Ne.symm hxj]
      _ = c j * f A.det := by simp
  have hj' : c j * f A.det = 0 := by
    rw [← hsum]
    exact hj
  exact (mul_eq_zero.mp hj').resolve_right hdet

/-- Each mapped Cramer relation lies in the kernel of the mapped pivot-row
matrix. -/
theorem mappedPolynomialCramerKernelVector_mem_blockTop_ker
    {R K I J : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R) (j : J) :
    mappedPolynomialCramerKernelVector f A B j ∈
      LinearMap.ker ((polynomialBlockTopMatrix A B).map f).mulVecLin := by
  rw [LinearMap.mem_ker]
  funext row
  change (((polynomialBlockTopMatrix A B).map f) *ᵥ
      (f ∘ polynomialCramerKernelVector A B j)) row = 0
  rw [← RingHom.map_mulVec]
  rw [blockTop_mulVec_polynomialCramerKernelVector]
  simpa using f.map_zero

/-- The free-column Cramer relations form a basis of the rational kernel of
the pivot-row block matrix.  This is the exact spanning fact needed later;
no minimal-index theorem is involved. -/
theorem span_mappedPolynomialCramerKernelVector_eq_blockTop_ker
    {R K I J : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R)
    (hdet : f A.det ≠ 0) :
    Submodule.span K
        (Set.range (mappedPolynomialCramerKernelVector f A B)) =
      LinearMap.ker ((polynomialBlockTopMatrix A B).map f).mulVecLin := by
  let T : (I ⊕ J → K) →ₗ[K] (I → K) :=
    ((polynomialBlockTopMatrix A B).map f).mulVecLin
  have hlinearIndependent : LinearIndependent K
      (mappedPolynomialCramerKernelVector f A B) :=
    linearIndependent_mappedPolynomialCramerKernelVector f A B hdet
  have hle : Submodule.span K
      (Set.range (mappedPolynomialCramerKernelVector f A B)) ≤
      LinearMap.ker T := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact mappedPolynomialCramerKernelVector_mem_blockTop_ker f A B j
  have hspanRank : Module.finrank K
      (Submodule.span K
        (Set.range (mappedPolynomialCramerKernelVector f A B))) =
      Fintype.card J := by
    exact finrank_span_eq_card hlinearIndependent
  have hmapA : f.mapMatrix A = A.map f := by
    ext i j
    rfl
  have hAdet : ((A.map f).det) ≠ 0 := by
    rw [← hmapA, ← f.map_det]
    exact hdet
  have hAunit : IsUnit (A.map f) :=
    (Matrix.isUnit_iff_isUnit_det (A.map f)).mpr
      (isUnit_iff_ne_zero.mpr hAdet)
  have hAsurjective : Function.Surjective (A.map f).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hAunit
  have hTsurjective : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hAsurjective y
    let z : I ⊕ J → K := Sum.elim x (fun _ => 0)
    refine ⟨z, ?_⟩
    funext row
    have hxrow := congrFun hx row
    change (((polynomialBlockTopMatrix A B).map f) *ᵥ z) row = y row
    rw [show (((polynomialBlockTopMatrix A B).map f) *ᵥ z) row =
        ∑ col : I ⊕ J,
          ((polynomialBlockTopMatrix A B).map f) row col * z col by
      rfl]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.map_apply, polynomialBlockTopMatrix, z, Sum.elim_inl,
      Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
    exact hxrow
  have hrangeRank : Module.finrank K (LinearMap.range T) =
      Fintype.card I := by
    rw [LinearMap.range_eq_top.mpr hTsurjective, finrank_top]
    simp
  have hdomainRank : Module.finrank K (I ⊕ J → K) =
      Fintype.card I + Fintype.card J := by
    simp
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (K := K) (V := (I ⊕ J → K)) T
  have hkerRank : Module.finrank K (LinearMap.ker T) =
      Fintype.card J := by
    rw [hrangeRank, hdomainRank] at hrankNullity
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle
    (hspanRank.trans hkerRank.symm)

/-- A full block matrix whose first block row is `[A | B]`. -/
def polynomialBlockMatrix
    {R I J H : Type} [CommRing R]
    (A : Matrix I I R) (B : Matrix I J R)
    (C : Matrix H I R) (D : Matrix H J R) :
    Matrix (I ⊕ H) (I ⊕ J) R
  | Sum.inl row, Sum.inl col => A row col
  | Sum.inl row, Sum.inr col => B row col
  | Sum.inr row, Sum.inl col => C row col
  | Sum.inr row, Sum.inr col => D row col

/-- The kernel of the full block matrix is contained in the kernel of its
pivot rows. -/
theorem polynomialBlockMatrix_ker_le_blockTop_ker
    {R K I J H : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype H]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R)
    (C : Matrix H I R) (D : Matrix H J R) :
    LinearMap.ker ((polynomialBlockMatrix A B C D).map f).mulVecLin ≤
      LinearMap.ker ((polynomialBlockTopMatrix A B).map f).mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  funext row
  have hrow := congrFun hx (Sum.inl row)
  change (((polynomialBlockTopMatrix A B).map f) *ᵥ x) row = 0
  change (((polynomialBlockMatrix A B C D).map f) *ᵥ x)
    (Sum.inl row) = 0 at hrow
  simpa [Matrix.mulVec, dotProduct, polynomialBlockMatrix,
    polynomialBlockTopMatrix] using hrow

/-- If the full mapped kernel has the expected free-column dimension, the
explicit Cramer family spans it.  A maximal nonsingular minor will supply
this dimension hypothesis. -/
theorem span_mappedPolynomialCramerKernelVector_eq_full_ker_of_finrank
    {R K I J H : Type} [CommRing R] [Field K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype H]
    (f : R →+* K) (A : Matrix I I R) (B : Matrix I J R)
    (C : Matrix H I R) (D : Matrix H J R)
    (hdet : f A.det ≠ 0)
    (hfullRank : Module.finrank K
      (LinearMap.ker ((polynomialBlockMatrix A B C D).map f).mulVecLin) =
        Fintype.card J) :
    Submodule.span K
        (Set.range (mappedPolynomialCramerKernelVector f A B)) =
      LinearMap.ker ((polynomialBlockMatrix A B C D).map f).mulVecLin := by
  let fullKer :=
    LinearMap.ker ((polynomialBlockMatrix A B C D).map f).mulVecLin
  let topKer :=
    LinearMap.ker ((polynomialBlockTopMatrix A B).map f).mulVecLin
  have hspanTop : Submodule.span K
      (Set.range (mappedPolynomialCramerKernelVector f A B)) = topKer := by
    exact span_mappedPolynomialCramerKernelVector_eq_blockTop_ker
      f A B hdet
  have htopRank : Module.finrank K topKer = Fintype.card J := by
    rw [← hspanTop]
    exact finrank_span_eq_card
      (linearIndependent_mappedPolynomialCramerKernelVector f A B hdet)
  have hfullLeTop : fullKer ≤ topKer := by
    exact polynomialBlockMatrix_ker_le_blockTop_ker f A B C D
  have hfullTop : fullKer = topKer := by
    apply Submodule.eq_of_le_of_finrank_eq hfullLeTop
    exact hfullRank.trans htopRank.symm
  exact hspanTop.trans hfullTop.symm

/-- A square matrix over a field admits a nonsingular minor whose size is its
rank.  We select the columns from a basis of the column space and then select
coordinates detecting that basis.  The complement size is the kernel
dimension by rank-nullity. -/
theorem exists_maximal_minor_of_kernel_finrank
    {K N : Type} [Field K] [Fintype N] [DecidableEq N]
    (M : Matrix N N K) (L : ℕ)
    (hkernelRank : Module.finrank K (LinearMap.ker M.mulVecLin) = L) :
    ∃ r : ℕ, ∃ rows cols : Fin r → N,
      r + L = Fintype.card N ∧
      Function.Injective rows ∧ Function.Injective cols ∧
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  let W : Submodule K (N → K) :=
    Submodule.span K (Set.range M.col)
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (K := K) (V := (N → K)) M.mulVecLin
  have hrankSum : Module.finrank K W + L = Fintype.card N := by
    rw [Matrix.range_mulVecLin, hkernelRank] at hrankNullity
    simpa [W] using hrankNullity
  obtain ⟨g, hgcol, hgspan, hgindependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.col)
  have hexistsCols : ∀ i, ∃ col : N, M.col col = g i := by
    intro i
    simpa only [Set.mem_range] using hgcol i
  choose cols hcols using hexistsCols
  have hcolsInjective : Function.Injective cols := by
    intro i j hij
    apply hgindependent.injective
    rw [← hcols i, ← hcols j, hij]
  let eN : N ≃ Fin (Fintype.card N) := Fintype.equivFin N
  let P : (N → K) ≃ₗ[K] (Fin (Fintype.card N) → K) :=
    LinearEquiv.funCongrLeft K K eN.symm
  let gFin : Fin (Module.finrank K W) →
      (Fin (Fintype.card N) → K) := fun i => P (g i)
  have hgFinIndependent : LinearIndependent K gFin := by
    have hmap := hgindependent.map' P.toLinearMap
      (LinearMap.ker_eq_bot.mpr P.injective)
    simpa [gFin, Function.comp_def] using hmap
  obtain ⟨rowsFin, hminorFin⟩ :=
    exists_coordinate_minor_ne_zero gFin hgFinIndependent
  let rows : Fin (Module.finrank K W) → N :=
    fun i => eN.symm (rowsFin i)
  have hminor :
      (Matrix.of fun i j => g j (rows i)).det ≠ 0 := by
    simpa [gFin, P, rows, eN, LinearEquiv.funCongrLeft_apply] using
      hminorFin
  let A : Matrix (Fin (Module.finrank K W))
      (Fin (Module.finrank K W)) K :=
    Matrix.of fun i j => g j (rows i)
  have hAminor : A.det ≠ 0 := by
    simpa [W, A] using hminor
  have hrowsInjective : Function.Injective rows := by
    have hrowIndependent :=
      Matrix.linearIndependent_rows_of_det_ne_zero hAminor
    intro i j hij
    apply hrowIndependent.injective
    funext k
    simp [A, Matrix.row, hij]
  refine ⟨Module.finrank K W, rows, cols, hrankSum,
    hrowsInjective, hcolsInjective, ?_⟩
  have hmatrix : M.submatrix rows cols = A := by
    ext i j
    change M (rows i) (cols j) = g j (rows i)
    exact congrFun (hcols j) (rows i)
  rw [hmatrix]
  exact hAminor

/-- The columns outside a selected injective pivot family. -/
abbrev SelectedColumnComplement
    {P N : Type} (cols : P → N) :=
  {n : N // n ∉ Set.range cols}

/-- Reindex all columns as selected pivot columns followed by their
complement. -/
noncomputable def selectedColumnEquiv
    {P N : Type} (cols : P → N) (hcols : Function.Injective cols) :
    P ⊕ SelectedColumnComplement cols ≃ N := by
  classical
  exact
    (Equiv.sumCongr (Equiv.ofInjective cols hcols)
        (Equiv.refl (SelectedColumnComplement cols))).trans
      (Equiv.Set.sumCompl (Set.range cols))

@[simp]
theorem selectedColumnEquiv_apply_inl
    {P N : Type} (cols : P → N) (hcols : Function.Injective cols)
    (i : P) :
    selectedColumnEquiv cols hcols (Sum.inl i) = cols i := by
  classical
  simp [selectedColumnEquiv]
  rfl

@[simp]
theorem selectedColumnEquiv_apply_inr
    {P N : Type} (cols : P → N) (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    selectedColumnEquiv cols hcols (Sum.inr j) = j.1 := by
  classical
  simp [selectedColumnEquiv]
  rfl

@[simp]
theorem selectedColumnEquiv_symm_apply_complement
    {P N : Type} (cols : P → N) (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    (selectedColumnEquiv cols hcols).symm j.1 = Sum.inr j := by
  apply (selectedColumnEquiv cols hcols).injective
  rw [(selectedColumnEquiv cols hcols).apply_symm_apply]
  exact (selectedColumnEquiv_apply_inr cols hcols j).symm

/-- The selected pivot block. -/
def selectedPolynomialPivotBlock
    {R P N : Type} [CommRing R]
    (M : Matrix N N R) (rows cols : P → N) : Matrix P P R :=
  M.submatrix rows cols

/-- The selected pivot rows restricted to non-pivot columns. -/
def selectedPolynomialFreeBlock
    {R P N : Type} [CommRing R]
    (M : Matrix N N R) (rows cols : P → N) :
    Matrix P (SelectedColumnComplement cols) R :=
  fun i j => M (rows i) j.1

/-- An explicit Cramer kernel vector in the original column coordinates. -/
noncomputable def selectedPolynomialCramerKernelVector
    {R P N : Type} [CommRing R]
    [Fintype P] [DecidableEq P] [DecidableEq N]
    (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) : N → R := by
  classical
  exact polynomialCramerKernelVector
    (selectedPolynomialPivotBlock M rows cols)
    (selectedPolynomialFreeBlock M rows cols) j ∘
      (selectedColumnEquiv cols hcols).symm

@[simp]
theorem selectedPolynomialCramerKernelVector_apply_free
    {R P N : Type} [CommRing R]
    [Fintype P] [DecidableEq P] [DecidableEq N]
    (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (j k : SelectedColumnComplement cols) :
    selectedPolynomialCramerKernelVector M rows cols hcols j k.1 =
      if k = j then (selectedPolynomialPivotBlock M rows cols).det else 0 := by
  classical
  simp [selectedPolynomialCramerKernelVector]
  rfl

/-- Map a selected polynomial Cramer vector into a field. -/
noncomputable def mappedSelectedPolynomialCramerKernelVector
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) : N → K :=
  f ∘ selectedPolynomialCramerKernelVector M rows cols hcols j

/-- A nonzero selected minor makes the original-coordinate Cramer family
linearly independent after mapping to the field. -/
theorem linearIndependent_mappedSelectedPolynomialCramerKernelVector
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0) :
    LinearIndependent K
      (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols) := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hj := congrFun hc j.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mappedSelectedPolynomialCramerKernelVector, Function.comp_apply,
    selectedPolynomialCramerKernelVector_apply_free, Pi.zero_apply] at hj
  have hsum :
      (∑ x, c x * f
        (if j = x then
          (selectedPolynomialPivotBlock M rows cols).det else 0)) =
        c j * f (selectedPolynomialPivotBlock M rows cols).det := by
    calc
      (∑ x, c x * f
          (if j = x then
            (selectedPolynomialPivotBlock M rows cols).det else 0)) =
          ∑ x, if x = j then
            c x * f (selectedPolynomialPivotBlock M rows cols).det else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxj : x = j
        · subst x
          simp
        · simp [hxj, Ne.symm hxj]
      _ = c j * f (selectedPolynomialPivotBlock M rows cols).det := by
        simp
  have hj' : c j * f (selectedPolynomialPivotBlock M rows cols).det = 0 := by
    rw [← hsum]
    exact hj
  exact (mul_eq_zero.mp hj').resolve_right hdet

/-- The selected-column equivalence gives the expected cardinal split. -/
theorem card_selectedColumnComplement
    {P N : Type} [Fintype P] [Fintype N]
    (cols : P → N) (hcols : Function.Injective cols) :
    Fintype.card P + Nat.card (SelectedColumnComplement cols) =
      Fintype.card N := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  have hcard : Fintype.card
      (P ⊕ SelectedColumnComplement cols) = Fintype.card N :=
    Fintype.card_congr (selectedColumnEquiv cols hcols)
  rw [Fintype.card_sum] at hcard
  rw [Nat.card_eq_fintype_card]
  exact hcard

/-- Selected Cramer vectors annihilate every selected pivot row over the
original coefficient ring. -/
theorem selectedRows_mulVec_selectedPolynomialCramerKernelVector
    {R P N : Type} [CommRing R]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    (M.submatrix rows (Equiv.refl N)) *ᵥ
      selectedPolynomialCramerKernelVector M rows cols hcols j = 0 := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  let e := selectedColumnEquiv cols hcols
  let A := selectedPolynomialPivotBlock M rows cols
  let B := selectedPolynomialFreeBlock M rows cols
  let v := polynomialCramerKernelVector A B j
  have hv := blockTop_mulVec_polynomialCramerKernelVector A B j
  funext row
  have hvrow := congrFun hv row
  change (∑ n : N, M (rows row) n * v (e.symm n)) = 0
  calc
    (∑ n : N, M (rows row) n * v (e.symm n)) =
        ∑ c : P ⊕ SelectedColumnComplement cols,
          M (rows row) (e c) * v c := by
      apply Fintype.sum_equiv e.symm
      intro n
      simp
    _ = ((polynomialBlockTopMatrix A B) *ᵥ v) row := by
      rw [show ((polynomialBlockTopMatrix A B) *ᵥ v) row =
          ∑ c : P ⊕ SelectedColumnComplement cols,
            polynomialBlockTopMatrix A B row c * v c by rfl]
      apply Finset.sum_congr rfl
      intro c hc
      cases c with
      | inl i =>
          change M (rows row) (cols i) * v (Sum.inl i) =
            A row i * v (Sum.inl i)
          rfl
      | inr k =>
          change M (rows row) k.1 * v (Sum.inr k) =
            B row k * v (Sum.inr k)
          rfl
    _ = 0 := hvrow

/-- Mapping coefficients sends each selected Cramer vector into the selected
row kernel. -/
theorem mappedSelectedPolynomialCramerKernelVector_mem_selectedRows_ker
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    mappedSelectedPolynomialCramerKernelVector f M rows cols hcols j ∈
      LinearMap.ker
        (((M.submatrix rows (Equiv.refl N)).map f).mulVecLin) := by
  rw [LinearMap.mem_ker]
  funext row
  change ((((M.submatrix rows (Equiv.refl N)).map f) *ᵥ
      (f ∘ selectedPolynomialCramerKernelVector M rows cols hcols j)) row) = 0
  rw [← RingHom.map_mulVec]
  rw [selectedRows_mulVec_selectedPolynomialCramerKernelVector]
  simpa using f.map_zero

/-- The full mapped kernel is contained in every selected-row kernel. -/
theorem fullMatrix_ker_le_selectedRows_ker
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [Fintype N]
    (f : R →+* K) (M : Matrix N N R) (rows : P → N) :
    LinearMap.ker (M.map f).mulVecLin ≤
      LinearMap.ker
        (((M.submatrix rows (Equiv.refl N)).map f).mulVecLin) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  funext row
  have hrow := congrFun hx (rows row)
  change (((M.map f) *ᵥ x) (rows row) = 0) at hrow
  simpa [Matrix.mulVec, dotProduct] using hrow

/-- A nonzero selected minor makes the selected-row map surjective. -/
theorem selectedRows_mulVecLin_surjective_of_minor_ne_zero
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0) :
    Function.Surjective
      (((M.submatrix rows (Equiv.refl N)).map f).mulVecLin) := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  let e := selectedColumnEquiv cols hcols
  let A := selectedPolynomialPivotBlock M rows cols
  have hmapA : f.mapMatrix A = A.map f := by
    ext i j
    rfl
  have hAdet : (A.map f).det ≠ 0 := by
    rw [← hmapA, ← f.map_det]
    exact hdet
  have hAunit : IsUnit (A.map f) :=
    (Matrix.isUnit_iff_isUnit_det (A.map f)).mpr
      (isUnit_iff_ne_zero.mpr hAdet)
  have hAsurjective : Function.Surjective (A.map f).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hAunit
  intro y
  obtain ⟨xPivot, hxPivot⟩ := hAsurjective y
  let x : N → K :=
    (Sum.elim xPivot (fun _ : SelectedColumnComplement cols => 0)) ∘ e.symm
  refine ⟨x, ?_⟩
  funext row
  have hxrow := congrFun hxPivot row
  change (∑ n : N, f (M (rows row) n) * x n) = y row
  calc
    (∑ n : N, f (M (rows row) n) * x n) =
        ∑ c : P ⊕ SelectedColumnComplement cols,
          f (M (rows row) (e c)) *
            Sum.elim xPivot
              (fun _ : SelectedColumnComplement cols => 0) c := by
      apply Fintype.sum_equiv e.symm
      intro n
      simp [x]
    _ = ∑ i : P, f (M (rows row) (cols i)) * xPivot i := by
      rw [Fintype.sum_sum_type]
      simp [e]
    _ = ((A.map f) *ᵥ xPivot) row := by
      rfl
    _ = y row := hxrow

/-- The selected-row kernel has exactly as many dimensions as there are
non-pivot columns. -/
theorem finrank_selectedRows_ker_eq_card_complement
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0) :
    Module.finrank K
      (LinearMap.ker
        (((M.submatrix rows (Equiv.refl N)).map f).mulVecLin)) =
      Nat.card (SelectedColumnComplement cols) := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  let T : (N → K) →ₗ[K] (P → K) :=
    ((M.submatrix rows (Equiv.refl N)).map f).mulVecLin
  have hsurjective : Function.Surjective T :=
    selectedRows_mulVecLin_surjective_of_minor_ne_zero
      f M rows cols hcols hdet
  have hrangeRank : Module.finrank K (LinearMap.range T) =
      Fintype.card P := by
    rw [LinearMap.range_eq_top.mpr hsurjective, finrank_top]
    simp
  have hdomainRank : Module.finrank K (N → K) = Fintype.card N := by
    simp
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker
    (K := K) (V := (N → K)) T
  have hcard := card_selectedColumnComplement cols hcols
  have hrankEquation :
      Fintype.card P + Module.finrank K (LinearMap.ker T) =
        Fintype.card N := by
    calc
      Fintype.card P + Module.finrank K (LinearMap.ker T) =
          Module.finrank K (LinearMap.range T) +
            Module.finrank K (LinearMap.ker T) := by rw [hrangeRank]
      _ = Module.finrank K (N → K) := hrankNullity
      _ = Fintype.card N := hdomainRank
  change Module.finrank K (LinearMap.ker T) =
    Nat.card (SelectedColumnComplement cols)
  rw [Nat.card_eq_fintype_card] at hcard ⊢
  omega

/-- When the selected minor is maximal, the explicit bounded-degree Cramer
family spans the full mapped kernel. -/
theorem span_mappedSelectedPolynomialCramerKernelVector_eq_full_ker
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0)
    (hfullRank : Module.finrank K (LinearMap.ker (M.map f).mulVecLin) =
      Nat.card (SelectedColumnComplement cols)) :
    Submodule.span K
        (Set.range
          (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols)) =
      LinearMap.ker (M.map f).mulVecLin := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  let fullKer := LinearMap.ker (M.map f).mulVecLin
  let topKer := LinearMap.ker
    (((M.submatrix rows (Equiv.refl N)).map f).mulVecLin)
  have hfullLeTop : fullKer ≤ topKer :=
    fullMatrix_ker_le_selectedRows_ker f M rows
  have htopRank : Module.finrank K topKer =
      Nat.card (SelectedColumnComplement cols) :=
    finrank_selectedRows_ker_eq_card_complement
      f M rows cols hcols hdet
  have hfullTop : fullKer = topKer := by
    apply Submodule.eq_of_le_of_finrank_eq hfullLeTop
    exact hfullRank.trans htopRank.symm
  have hfamilyIndependent : LinearIndependent K
      (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols) :=
    linearIndependent_mappedSelectedPolynomialCramerKernelVector
      f M rows cols hcols hdet
  have hspanRank : Module.finrank K
      (Submodule.span K
        (Set.range
          (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols))) =
      Nat.card (SelectedColumnComplement cols) := by
    rw [Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hfamilyIndependent
  have hspanLeTop : Submodule.span K
      (Set.range
        (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols)) ≤
      topKer := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact mappedSelectedPolynomialCramerKernelVector_mem_selectedRows_ker
      f M rows cols hcols j
  have hspanTop : Submodule.span K
      (Set.range
        (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols)) =
      topKer := by
    apply Submodule.eq_of_le_of_finrank_eq hspanLeTop
    exact hspanRank.trans htopRank.symm
  exact hspanTop.trans hfullTop.symm

/-- If the coefficient map is injective, the selected Cramer vectors already
annihilate the full matrix over the original ring.  The spanning theorem
first puts their mapped images in the full field kernel; injectivity then
returns every row identity before specialization. -/
theorem selectedPolynomialCramerKernelVector_mem_full_ker_of_injective
    {R K P N : Type} [CommRing R] [Field K]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (f : R →+* K) (hf : Function.Injective f)
    (M : Matrix N N R) (rows cols : P → N)
    (hcols : Function.Injective cols)
    (hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0)
    (hfullRank : Module.finrank K (LinearMap.ker (M.map f).mulVecLin) =
      Nat.card (SelectedColumnComplement cols))
    (j : SelectedColumnComplement cols) :
    selectedPolynomialCramerKernelVector M rows cols hcols j ∈
      LinearMap.ker M.mulVecLin := by
  classical
  letI : Fintype (SelectedColumnComplement cols) := Fintype.ofFinite _
  have hspan :=
    span_mappedSelectedPolynomialCramerKernelVector_eq_full_ker
      f M rows cols hcols hdet hfullRank
  have hmapped :
      mappedSelectedPolynomialCramerKernelVector f M rows cols hcols j ∈
        LinearMap.ker (M.map f).mulVecLin := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  rw [LinearMap.mem_ker] at hmapped ⊢
  change ((M.map f) *ᵥ
      (f ∘ selectedPolynomialCramerKernelVector M rows cols hcols j) = 0)
    at hmapped
  funext i
  apply hf
  have hi := congrFun hmapped i
  rw [← RingHom.map_mulVec] at hi
  simpa using hi

/-- Every coordinate of a selected Cramer vector has degree at most the
selected-minor size times the entry cap. -/
theorem selectedPolynomialCramerKernelVector_natDegree_le_card_mul
    {F P N : Type} [Field F]
    [Fintype P] [DecidableEq P] [Fintype N] [DecidableEq N]
    (M : Matrix N N F[X]) (rows cols : P → N)
    (hcols : Function.Injective cols) (S : ℕ)
    (hM : ∀ i k, (M i k).natDegree ≤ S)
    (j : SelectedColumnComplement cols) (n : N) :
    (selectedPolynomialCramerKernelVector M rows cols hcols j n).natDegree ≤
      Fintype.card P * S := by
  classical
  apply polynomialCramerKernelVector_natDegree_le_card_mul
  · intro i k
    exact hM (rows i) (cols k)
  · intro i k
    exact hM (rows i) k.1

/-- A maximal minor gives a complete explicit polynomial Cramer family for
the mapped kernel.  The family has exactly `L` members, spans the rational
kernel, and every polynomial coordinate has degree at most `r * S`, where
`r + L` is the ambient matrix size.  This is the packaged replacement for a
minimal-polynomial-kernel-basis degree theorem. -/
theorem exists_spanning_bounded_polynomialCramerKernelFamily
    {F K N : Type} [Field F] [Field K]
    [Fintype N] [DecidableEq N]
    (f : F[X] →+* K) (M : Matrix N N F[X]) (L S : ℕ)
    (hkernelRank :
      Module.finrank K (LinearMap.ker (M.map f).mulVecLin) = L)
    (hM : ∀ i k, (M i k).natDegree ≤ S) :
    ∃ r : ℕ, ∃ rows cols : Fin r → N,
      ∃ hrows : Function.Injective rows,
      ∃ hcols : Function.Injective cols,
        r + L = Fintype.card N ∧
        Nat.card (SelectedColumnComplement cols) = L ∧
        f (selectedPolynomialPivotBlock M rows cols).det ≠ 0 ∧
        Submodule.span K
            (Set.range
              (mappedSelectedPolynomialCramerKernelVector
                f M rows cols hcols)) =
          LinearMap.ker (M.map f).mulVecLin ∧
        ∀ (j : SelectedColumnComplement cols) (n : N),
          (selectedPolynomialCramerKernelVector
            M rows cols hcols j n).natDegree ≤ r * S := by
  classical
  obtain ⟨r, rows, cols, hrank, hrows, hcols, hminor⟩ :=
    exists_maximal_minor_of_kernel_finrank (M.map f) L hkernelRank
  have hdet : f (selectedPolynomialPivotBlock M rows cols).det ≠ 0 := by
    rw [f.map_det]
    have hmapSub :
        (M.submatrix rows cols).map f =
          (M.map f).submatrix rows cols := by
      ext i j
      rfl
    have hmapMatrix :
        f.mapMatrix (M.submatrix rows cols) =
          (M.submatrix rows cols).map f := by
      ext i j
      rfl
    rw [show selectedPolynomialPivotBlock M rows cols =
        M.submatrix rows cols by rfl, hmapMatrix, hmapSub]
    exact hminor
  have hcomplement : Nat.card (SelectedColumnComplement cols) = L := by
    have hcard := card_selectedColumnComplement cols hcols
    simp only [Fintype.card_fin] at hcard
    omega
  have hspan : Submodule.span K
        (Set.range
          (mappedSelectedPolynomialCramerKernelVector f M rows cols hcols)) =
      LinearMap.ker (M.map f).mulVecLin := by
    apply span_mappedSelectedPolynomialCramerKernelVector_eq_full_ker
      f M rows cols hcols hdet
    exact hkernelRank.trans hcomplement.symm
  refine ⟨r, rows, cols, hrows, hcols, hrank, hcomplement, hdet, hspan, ?_⟩
  intro j n
  simpa using selectedPolynomialCramerKernelVector_natDegree_le_card_mul
    M rows cols hcols S hM j n

end ProximityPrize.SubmissionLower
