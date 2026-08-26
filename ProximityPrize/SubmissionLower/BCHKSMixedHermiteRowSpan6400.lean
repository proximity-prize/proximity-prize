import ProximityPrize.SubmissionLower.BCHKSMixedHermitePivot6400
import ProximityPrize.SubmissionLower.BCHKSGaoSpecializationCore6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedHermiteRowSpan6400

open LinearMap Submodule Matrix
open BCHKSMixedHermitePivot6400
open BCHKSGaoSpecializationCore6400

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 200000

/-!
# From kernel annihilation to controlled Gao row pivots

The first half of this file is field-linear and unconditional.  If every
selected jet kills the kernel of a Gao map, then finite-dimensional duality
puts that jet in the row space.  A linearly independent selected family can
then be extended to a basis of the row space.

The second half avoids rational row operations altogether.  It adjoins
polynomial representatives of the jets to the literal normalized Gao rows,
then uses finite matroid extension to select a full-span independent subset
containing every jet.  The resulting coordinate minor is a literal polynomial
minor of this augmented matrix, with degree bounded by the exact sum of its
selected row caps.

The remaining concrete input is only the normalized sparse matrix model:
polynomial coordinate rows for the selected jets, their entry caps, and the
common-kernel statement after passage to the generic field.  No bounded
polynomial realization of abstract row operations is required here.
-/

section RowSpace

variable {K V W J : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A functional which kills `ker A` belongs to the row space
`range A.dualMap`. -/
theorem mem_range_dualMap_of_ker_le_ker
    (A : V →ₗ[K] W) (ell : Module.Dual K V)
    (hkill : LinearMap.ker A <= LinearMap.ker ell) :
    ell ∈ LinearMap.range A.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [Submodule.mem_dualAnnihilator]
  intro v hv
  exact hkill hv

/-- Pointwise common-kernel form for a selected family. -/
theorem selectedJets_mem_rowSpace
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hkill : forall v, A v = 0 -> forall j, jet j v = 0) :
    forall j, jet j ∈ LinearMap.range A.dualMap := by
  intro j
  apply mem_range_dualMap_of_ker_le_ker A (jet j)
  intro v hv
  exact hkill v hv j

/-- A chosen row-space lift of each selected jet. -/
noncomputable def jetRowSpaceLift
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hmem : forall j, jet j ∈ LinearMap.range A.dualMap) :
    J -> LinearMap.range A.dualMap :=
  fun j => ⟨jet j, hmem j⟩

@[simp]
theorem jetRowSpaceLift_coe
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hmem : forall j, jet j ∈ LinearMap.range A.dualMap) (j : J) :
    (jetRowSpaceLift A jet hmem j : Module.Dual K V) = jet j := rfl

/-- Linear independence survives passage to the row-space subtype. -/
theorem jetRowSpaceLift_linearIndependent
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hmem : forall j, jet j ∈ LinearMap.range A.dualMap)
    (hli : LinearIndependent K jet) :
    LinearIndependent K (jetRowSpaceLift A jet hmem) := by
  apply LinearIndependent.of_comp (LinearMap.range A.dualMap).subtype
  simpa [Function.comp_def] using hli

/-- Every independent family extends to a basis set.  Applied to
`jetRowSpaceLift`, the selected jets occur literally in a basis of the Gao row
space, not merely in its span. -/
theorem linearIndependent_subset_basisSet
    {M : Type*} [AddCommGroup M] [Module K M]
    (v : J -> M) (hli : LinearIndependent K v) :
    exists basisSet : Set M,
      LinearIndepOn K _root_.id basisSet ∧
      Submodule.span K basisSet = ⊤ ∧
      Set.range v ⊆ basisSet := by
  classical
  let selected : Set M := Set.range v
  have hselected : LinearIndepOn K _root_.id selected :=
    hli.linearIndepOn_id
  let basisSet := hselected.extend (Set.subset_univ selected)
  refine ⟨basisSet, ?_, ?_, ?_⟩
  · exact hselected.linearIndepOn_extend (Set.subset_univ selected)
  · have hspan := hselected.span_extend_eq_span
      (Set.subset_univ selected)
    simpa [basisSet] using hspan
  · exact hselected.subset_extend (Set.subset_univ selected)

/-- Kernel annihilation and independence put the selected jets literally
inside a basis set for the Gao row space.  This is the ambient-dual form of
the row-basis extension, avoiding any choice of row operations or
denominators. -/
theorem selectedJets_subset_rowBasisSet
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hkill : forall v, A v = 0 -> forall j, jet j v = 0)
    (hli : LinearIndependent K jet) :
    exists basisSet : Set (Module.Dual K V),
      LinearIndepOn K _root_.id basisSet ∧
      Submodule.span K basisSet = LinearMap.range A.dualMap ∧
      Set.range jet ⊆ basisSet ∧
      basisSet ⊆ LinearMap.range A.dualMap := by
  classical
  let selected : Set (Module.Dual K V) := Set.range jet
  let rowSet : Set (Module.Dual K V) :=
    (LinearMap.range A.dualMap : Set (Module.Dual K V))
  have hselected : LinearIndepOn K _root_.id selected :=
    hli.linearIndepOn_id
  have hsubset : selected ⊆ rowSet := by
    rintro _ ⟨j, rfl⟩
    exact selectedJets_mem_rowSpace A jet hkill j
  let basisSet := hselected.extend hsubset
  refine ⟨basisSet, ?_, ?_, ?_, ?_⟩
  · exact hselected.linearIndepOn_extend hsubset
  · have hspan := hselected.span_extend_eq_span hsubset
    simpa [basisSet, rowSet] using hspan
  · exact hselected.subset_extend hsubset
  · exact hselected.extend_subset hsubset

/-- The selected jet count cannot exceed the Gao row rank. -/
theorem card_selectedJets_le_finrank_rowSpace
    [Fintype J] [FiniteDimensional K V]
    (A : V →ₗ[K] W) (jet : J -> Module.Dual K V)
    (hkill : forall v, A v = 0 -> forall j, jet j v = 0)
    (hli : LinearIndependent K jet) :
    Fintype.card J <=
      Module.finrank K (LinearMap.range A.dualMap) := by
  let hmem := selectedJets_mem_rowSpace A jet hkill
  have hlift := jetRowSpaceLift_linearIndependent A jet hmem hli
  exact hlift.fintype_card_le_finrank

/-- Row-space dimension equals the rank of the original Gao map. -/
theorem finrank_rowSpace_eq_finrank_range
    [FiniteDimensional K V] (A : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range A.dualMap) =
      Module.finrank K (LinearMap.range A) := by
  exact LinearMap.finrank_range_dualMap_eq_finrank_range A

end RowSpace

section MatrixRowSpace

variable {K Rows Cols JetRows : Type*} [Field K]
variable [Fintype Rows] [DecidableEq Rows]
variable [Fintype Cols] [DecidableEq Cols]

/-- Coordinate form of annihilator-to-row-span duality.  A row vector which
kills the kernel of `M.mulVec` lies in the span of the literal rows of `M`. -/
theorem matrixRow_mem_span_of_kernel_annihilation
    (M : Matrix Rows Cols K) (v : Cols -> K)
    (hkill : forall x, M.mulVec x = 0 -> dotProduct v x = 0) :
    v ∈ Submodule.span K (Set.range M.row) := by
  let ell : Module.Dual K (Cols -> K) := dotProductEquiv K Cols v
  have hell : ell ∈ LinearMap.range M.mulVecLin.dualMap := by
    apply mem_range_dualMap_of_ker_le_ker M.mulVecLin ell
    intro x hx
    change dotProduct v x = 0
    exact hkill x hx
  obtain ⟨g, hg⟩ := hell
  let a : Rows -> K := (dotProductEquiv K Rows).symm g
  have ha : dotProductEquiv K Rows a = g := by
    exact (dotProductEquiv K Rows).apply_symm_apply g
  have hv : M.vecMulLinear a = v := by
    apply (dotProductEquiv K Cols).injective
    apply LinearMap.ext
    intro x
    have hx := congrArg
      (fun f : Module.Dual K (Cols -> K) => f x) hg
    calc
      dotProductEquiv K Cols (M.vecMulLinear a) x =
          dotProduct (a ᵥ* M) x := rfl
      _ = dotProduct a (M *ᵥ x) := by rw [dotProduct_mulVec]
      _ = (dotProductEquiv K Rows a) (M *ᵥ x) := rfl
      _ = g (M *ᵥ x) := by rw [ha]
      _ = M.mulVecLin.dualMap g x := rfl
      _ = ell x := hx
      _ = dotProductEquiv K Cols v x := rfl
  rw [← range_vecMulLinear M]
  exact ⟨a, hv⟩

/-- Common-kernel form for a finite selected row family. -/
theorem matrixRows_mem_span_of_kernel_annihilation
    (M : Matrix Rows Cols K) (jet : JetRows -> Cols -> K)
    (hkill : forall x, M.mulVec x = 0 ->
      forall j, dotProduct (jet j) x = 0) :
    forall j, jet j ∈ Submodule.span K (Set.range M.row) := by
  intro j
  exact matrixRow_mem_span_of_kernel_annihilation M (jet j)
    (fun x hx => hkill x hx j)

end MatrixRowSpace

section MixedHermiteRowBasis

variable {K I W : Type*} [Field K] [Fintype I]
variable [AddCommGroup W] [Module K W]

/-- Concrete specialization to the proven tower of mixed-Hermite pivots.
If the selected jets kill the kernel of `A`, they occur literally in a basis
set of its row space. -/
theorem selectedMixedHasseTower_subset_rowBasisSet
    (A : Polynomial (Polynomial K) →ₗ[K] W)
    (omega : I ↪ K) (u : I -> K) (nu : I -> Nat) (s n : Nat)
    (hkill : forall T, A T = 0 ->
      forall j : LayerTower
        (fun b => HermiteIndex I (predecessorLayerCount nu b)) s n,
        layerTowerFamily
          (fun b => HermiteIndex I (predecessorLayerCount nu b))
          (fun b => selectedMixedHasseLayer omega u
            (predecessorLayerCount nu b) b) s n j T = 0) :
    exists basisSet : Set (Module.Dual K (Polynomial (Polynomial K))),
      LinearIndepOn K _root_.id basisSet ∧
      Submodule.span K basisSet = LinearMap.range A.dualMap ∧
      Set.range
        (layerTowerFamily
          (fun b => HermiteIndex I (predecessorLayerCount nu b))
          (fun b => selectedMixedHasseLayer omega u
            (predecessorLayerCount nu b) b) s n) ⊆ basisSet ∧
      basisSet ⊆ LinearMap.range A.dualMap := by
  apply selectedJets_subset_rowBasisSet A _ hkill
  exact selectedMixedHasseTower_linearIndependent omega u nu s n

/-- Degree-53 endpoint form of
`selectedMixedHasseTower_subset_rowBasisSet`. -/
theorem selectedMixedHasseTower_degree53_subset_rowBasisSet
    (A : Polynomial (Polynomial K) →ₗ[K] W)
    (omega : I ↪ K) (u : I -> K) (nu : I -> Nat)
    (hkill : forall T, A T = 0 ->
      forall j : LayerTower
        (fun b => HermiteIndex I (predecessorLayerCount nu b)) 0 52,
        layerTowerFamily
          (fun b => HermiteIndex I (predecessorLayerCount nu b))
          (fun b => selectedMixedHasseLayer omega u
            (predecessorLayerCount nu b) b) 0 52 j T = 0) :
    exists basisSet : Set (Module.Dual K (Polynomial (Polynomial K))),
      LinearIndepOn K _root_.id basisSet ∧
      Submodule.span K basisSet = LinearMap.range A.dualMap ∧
      Set.range
        (layerTowerFamily
          (fun b => HermiteIndex I (predecessorLayerCount nu b))
          (fun b => selectedMixedHasseLayer omega u
            (predecessorLayerCount nu b) b) 0 52) ⊆ basisSet ∧
      basisSet ⊆ LinearMap.range A.dualMap := by
  exact selectedMixedHasseTower_subset_rowBasisSet
    A omega u nu 0 52 hkill

end MixedHermiteRowBasis

section AugmentedRowBasis

variable {K V JetRows OriginalRows : Type*} [Field K]
variable [AddCommGroup V] [Module K V]

/-- Adjoin distinguished jet rows in front of the literal rows of a matrix. -/
def augmentedFamily
    (jet : JetRows -> V) (row : OriginalRows -> V) :
    JetRows ⊕ OriginalRows -> V :=
  Sum.elim jet row

/-- Adding vectors already in the original row span does not change that
span. -/
theorem span_augmentedFamily_eq_original_of_jet_mem_span
    (jet : JetRows -> V) (row : OriginalRows -> V)
    (hmem : forall j, jet j ∈ Submodule.span K (Set.range row)) :
    Submodule.span K (Set.range (augmentedFamily jet row)) =
      Submodule.span K (Set.range row) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨q, rfl⟩
    cases q with
    | inl j => exact hmem j
    | inr r => exact Submodule.subset_span ⟨r, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨r, rfl⟩
    exact ⟨Sum.inr r, rfl⟩

/-- Finite matroid extension in the form needed for the Gao matrix.  Starting
with independent jet rows lying in the span of the original rows, it selects
a basis of that span which contains every jet row and whose remaining members
are literal original rows.  No row-operation coefficients are introduced. -/
theorem exists_augmented_basisFinset
    [Fintype JetRows] [Fintype OriginalRows]
    (jet : JetRows -> V) (row : OriginalRows -> V)
    (hli : LinearIndependent K jet)
    (hmem : forall j, jet j ∈ Submodule.span K (Set.range row)) :
    exists chosen : Finset (JetRows ⊕ OriginalRows),
      (forall j, Sum.inl j ∈ chosen) ∧
      LinearIndependent K
        (fun q : {q // q ∈ chosen} => augmentedFamily jet row q.1) ∧
      Submodule.span K
          (Set.range
            (fun q : {q // q ∈ chosen} => augmentedFamily jet row q.1)) =
        Submodule.span K (Set.range row) := by
  classical
  let aug : JetRows ⊕ OriginalRows -> V := augmentedFamily jet row
  let selected : Set (JetRows ⊕ OriginalRows) := Set.range Sum.inl
  have hselected : LinearIndepOn K aug selected := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    simpa [aug, augmentedFamily, Function.comp_def] using hli
  let chosenSet := hselected.extend (Set.subset_univ selected)
  have hchosenLI : LinearIndepOn K aug chosenSet :=
    hselected.linearIndepOn_extend (Set.subset_univ selected)
  have hfinite : Set.Finite chosenSet := Set.toFinite chosenSet
  let chosen : Finset (JetRows ⊕ OriginalRows) := hfinite.toFinset
  have hcoe : (chosen : Set (JetRows ⊕ OriginalRows)) = chosenSet := by
    exact hfinite.coe_toFinset
  refine ⟨chosen, ?_, ?_, ?_⟩
  · intro j
    have hj : Sum.inl j ∈ chosenSet :=
      hselected.subset_extend (Set.subset_univ selected) ⟨j, rfl⟩
    change Sum.inl j ∈ (chosen : Set (JetRows ⊕ OriginalRows))
    rw [hcoe]
    exact hj
  · rw [← hcoe] at hchosenLI
    change LinearIndependent K
      ((chosen : Set (JetRows ⊕ OriginalRows)).restrict
        (augmentedFamily jet row))
    simpa [aug] using hchosenLI.linearIndependent_restrict
  · have hspan := hselected.span_image_extend_eq_span_image
      (Set.subset_univ selected)
    calc
      Submodule.span K
          (Set.range
            (fun q : {q // q ∈ chosen} => augmentedFamily jet row q.1)) =
          Submodule.span K
            (aug '' (chosen : Set (JetRows ⊕ OriginalRows))) := by
            congr 1
            ext v
            constructor
            · rintro ⟨q, rfl⟩
              exact ⟨q.1, q.2, rfl⟩
            · rintro ⟨q, hq, rfl⟩
              exact ⟨⟨q, hq⟩, rfl⟩
      _ = Submodule.span K (aug '' chosenSet) := by rw [hcoe]
      _ = Submodule.span K (aug '' Set.univ) := hspan
      _ = Submodule.span K (Set.range aug) := by
        congr 1
        ext v
        simp
      _ = Submodule.span K (Set.range row) := by
        exact span_augmentedFamily_eq_original_of_jet_mem_span jet row hmem

end AugmentedRowBasis

section CoordinateMinor

variable {K Rows Cols : Type*} [Field K]
variable [Fintype Rows] [DecidableEq Rows]
variable [Fintype Cols] [DecidableEq Cols]

omit [DecidableEq Rows] [Fintype Cols] [DecidableEq Cols] in
/-- Independent rows span enough coordinate columns to contain a basis. -/
theorem span_columns_eq_top_of_rows_linearIndependent
    (B : Matrix Rows Cols K)
    (hli : LinearIndependent K B.row) :
    Submodule.span K (Set.range (flip B)) = ⊤ := by
  exact (span_flip_eq_top_iff_linearIndependent).2 hli

omit [Fintype Cols] [DecidableEq Cols] in
/-- Any finite independent row family admits a square nonzero coordinate
minor.  The row family need not be a literal subset of a larger matrix; this
is the form used after replacing Gao rows by a row-space basis containing the
Hermite pivots. -/
theorem exists_columns_det_ne_zero_of_rows_linearIndependent
    (B : Matrix Rows Cols K)
    (hli : LinearIndependent K B.row) :
    exists cols : Rows -> Cols,
      (B.submatrix _root_.id cols).det ≠ 0 := by
  classical
  let columns : Cols -> (Rows -> K) := flip B
  have hspan : Submodule.span K (Set.range columns) = ⊤ := by
    exact span_columns_eq_top_of_rows_linearIndependent B hli
  let htop : (⊤ : Submodule K (Rows -> K)) <=
      Submodule.span K (Set.range columns) := by
    rw [hspan]
  let Idx := (linearIndepOn_empty K _root_.id).extend
    (Set.empty_subset (Set.range columns))
  let b : Module.Basis Idx K (Rows -> K) :=
    Module.Basis.ofSpan htop
  letI : Finite Idx := b.linearIndependent.finite
  letI : Fintype Idx := Fintype.ofFinite Idx
  have hcard : Fintype.card Rows = Fintype.card Idx := by
    rw [← Module.finrank_fintype_fun_eq_card K,
      Module.finrank_eq_card_basis b]
  let e : Rows ≃ Idx := Fintype.equivOfCardEq hcard
  have hbmem (r : Rows) : b (e r) ∈ Set.range columns := by
    have hrange : Set.range b ⊆ Set.range columns :=
      Module.Basis.extendLe_subset
        (linearIndepOn_empty K _root_.id)
        (Set.empty_subset (Set.range columns)) htop
    exact hrange ⟨e r, rfl⟩
  choose cols hcols using hbmem
  refine ⟨cols, ?_⟩
  have hcol : forall r,
      (B.submatrix _root_.id cols).col r = b (e r) := by
    intro r
    funext i
    have hr := congrFun (hcols r).symm i
    change B i (cols r) = b (e r) i
    exact hr.symm
  have hliCols : LinearIndependent K
      (B.submatrix _root_.id cols).col := by
    have hb : LinearIndependent K (fun r => b (e r)) :=
      b.linearIndependent.comp e e.injective
    rw [show (B.submatrix _root_.id cols).col =
      (fun r => b (e r)) from funext hcol]
    exact hb
  have hunit : IsUnit (B.submatrix _root_.id cols) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hliCols
  exact ((B.submatrix _root_.id cols).isUnit_iff_isUnit_det.mp hunit).ne_zero

/-- Matrix of a dual row family in a chosen finite basis. -/
noncomputable def functionalCoordinateMatrix
    {V : Type*} [AddCommGroup V] [Module K V]
    (bV : Module.Basis Cols K V)
    (row : Rows -> Module.Dual K V) : Matrix Rows Cols K :=
  fun i c => row i (bV c)

/-- A square row basis always yields a nonzero maximal coordinate minor. -/
theorem rowBasis_exists_nonzero_coordinateMinor
    {V : Type*} [AddCommGroup V] [Module K V]
    (bV : Module.Basis Cols K V)
    (row : Rows -> Module.Dual K V)
    (hli : LinearIndependent K row) :
    exists cols : Rows -> Cols,
      ((functionalCoordinateMatrix bV row).submatrix
        _root_.id cols).det ≠ 0 := by
  let B : Matrix Rows Cols K := functionalCoordinateMatrix bV row
  exact exists_columns_det_ne_zero_of_rows_linearIndependent B (by
    have hmapped := hli.map' bV.dualBasis.equivFun.toLinearMap
      (LinearMap.ker_eq_bot_of_injective
        bV.dualBasis.equivFun.injective)
    have heq : (fun i => bV.dualBasis.equivFun (row i)) = B.row := by
      funext i c
      simp [B, functionalCoordinateMatrix,
        Module.Basis.dualBasis_equivFun]
    rw [← heq]
    exact hmapped)

end CoordinateMinor

section ControlledAugmentedLift

variable {F L JetRows OriginalRows Cols : Type*}
variable [Field F] [Field L]
variable [Fintype JetRows] [Fintype OriginalRows]

/-- Polynomial matrix obtained by adjoining the distinguished jet rows to
the literal rows of the normalized Gao matrix. -/
def augmentedPolynomialMatrix
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F)) :
    Matrix (JetRows ⊕ OriginalRows) Cols (Polynomial F) :=
  fun q => Sum.elim jetRows originalRows q

omit [Fintype JetRows] [Fintype OriginalRows] in
@[simp]
theorem augmentedPolynomialMatrix_inl
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F))
    (j : JetRows) (c : Cols) :
    augmentedPolynomialMatrix jetRows originalRows (Sum.inl j) c =
      jetRows j c := rfl

omit [Fintype JetRows] [Fintype OriginalRows] in
@[simp]
theorem augmentedPolynomialMatrix_inr
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F))
    (r : OriginalRows) (c : Cols) :
    augmentedPolynomialMatrix jetRows originalRows (Sum.inr r) c =
      originalRows r c := rfl

/-- The selected augmented row basis, nonzero polynomial coordinate minor,
and exact row-cap certificate delivered by the denominator-free construction. -/
def AugmentedRowBasisMinorCertificate
    [DecidableEq JetRows] [DecidableEq OriginalRows]
    (phi : Polynomial F →+* L)
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F))
    (rowCap : JetRows ⊕ OriginalRows -> Nat) : Prop :=
  exists chosen : Finset (JetRows ⊕ OriginalRows),
    exists cols : {q // q ∈ chosen} -> Cols,
      (forall j, Sum.inl j ∈ chosen) ∧
      LinearIndependent L
        (fun q : {q // q ∈ chosen} =>
          ((augmentedPolynomialMatrix jetRows originalRows).map phi).row
            q.1) ∧
      Submodule.span L
          (Set.range
            (fun q : {q // q ∈ chosen} =>
              ((augmentedPolynomialMatrix jetRows originalRows).map phi).row
                q.1)) =
        Submodule.span L (Set.range (originalRows.map phi).row) ∧
      ((augmentedPolynomialMatrix jetRows originalRows).submatrix
        Subtype.val cols).det ≠ 0 ∧
      ((augmentedPolynomialMatrix jetRows originalRows).submatrix
        Subtype.val cols).det.natDegree <=
        ∑ q : {q // q ∈ chosen}, rowCap q.1

/-- Denominator-free controlled-minor interface.  Over the generic field,
assume the polynomial jet rows are independent and lie in the span of the
literal Gao rows.  A finite row basis can then be selected from the augmented
matrix, containing every jet row.  Its nonzero coordinate minor is already a
minor of the polynomial augmented matrix, so its degree is bounded by the
exact sum of the selected row caps; no rational row operations need to be
cleared. -/
theorem controlledAugmentedRowBasis_exists_minor
    [DecidableEq JetRows] [DecidableEq OriginalRows]
    (phi : Polynomial F →+* L)
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F))
    (rowCap : JetRows ⊕ OriginalRows -> Nat)
    (hentry : forall q c,
      (augmentedPolynomialMatrix jetRows originalRows q c).natDegree <=
        rowCap q)
    (hjetLI : LinearIndependent L (jetRows.map phi).row)
    (hjetMem : forall j,
      (jetRows.map phi).row j ∈
        Submodule.span L (Set.range (originalRows.map phi).row)) :
    AugmentedRowBasisMinorCertificate
      phi jetRows originalRows rowCap := by
  classical
  unfold AugmentedRowBasisMinorCertificate
  let B := augmentedPolynomialMatrix jetRows originalRows
  obtain ⟨chosen, hinclude, hselectedLI, hspan⟩ :=
    exists_augmented_basisFinset
      (jetRows.map phi).row (originalRows.map phi).row hjetLI hjetMem
  have hselectedLI' : LinearIndependent L
      (fun q : {q // q ∈ chosen} => (B.map phi).row q.1) := by
    have hfamily :
        (fun q : {q // q ∈ chosen} => (B.map phi).row q.1) =
          (fun q : {q // q ∈ chosen} =>
            augmentedFamily (jetRows.map phi).row
              (originalRows.map phi).row q.1) := by
      funext q c
      cases q.1 <;> rfl
    rw [hfamily]
    exact hselectedLI
  have hspan' : Submodule.span L
        (Set.range
          (fun q : {q // q ∈ chosen} => (B.map phi).row q.1)) =
      Submodule.span L (Set.range (originalRows.map phi).row) := by
    have hfamily :
        (fun q : {q // q ∈ chosen} => (B.map phi).row q.1) =
          (fun q : {q // q ∈ chosen} =>
            augmentedFamily (jetRows.map phi).row
              (originalRows.map phi).row q.1) := by
      funext q c
      cases q.1 <;> rfl
    rw [hfamily]
    exact hspan
  let selectedMapped : Matrix {q // q ∈ chosen} Cols L :=
    (B.map phi).submatrix Subtype.val _root_.id
  have hselectedMatrixLI : LinearIndependent L selectedMapped.row := by
    change LinearIndependent L
      (fun q : {q // q ∈ chosen} => fun c => (B.map phi) q.1 c)
    exact hselectedLI'
  obtain ⟨cols, hminorMapped⟩ :=
    exists_columns_det_ne_zero_of_rows_linearIndependent
      selectedMapped hselectedMatrixLI
  refine ⟨chosen, cols, hinclude, hselectedLI', hspan', ?_, ?_⟩
  · intro hzero
    apply hminorMapped
    have hmapped := BCHKSGaoSpecializationCore6400.map_submatrix_det
      phi B (Subtype.val : {q // q ∈ chosen} ->
        JetRows ⊕ OriginalRows) cols
    rw [hzero, map_zero] at hmapped
    simpa [selectedMapped] using hmapped.symm
  · apply BCHKSGaoSpecializationCore6400.natDegree_det_le_sum_rowCaps
    intro q q'
    exact hentry q.1 (cols q')

/-- Kernel-containment version of the denominator-free construction.  The
coordinate annihilator theorem supplies generic row-span membership, after
which `controlledAugmentedRowBasis_exists_minor` selects only literal rows of
the augmented polynomial matrix. -/
theorem controlledAugmentedRowBasis_exists_minor_of_kernel_annihilation
    [Fintype Cols] [DecidableEq Cols]
    [DecidableEq JetRows] [DecidableEq OriginalRows]
    (phi : Polynomial F →+* L)
    (jetRows : Matrix JetRows Cols (Polynomial F))
    (originalRows : Matrix OriginalRows Cols (Polynomial F))
    (rowCap : JetRows ⊕ OriginalRows -> Nat)
    (hentry : forall q c,
      (augmentedPolynomialMatrix jetRows originalRows q c).natDegree <=
        rowCap q)
    (hjetLI : LinearIndependent L (jetRows.map phi).row)
    (hkill : forall x, (originalRows.map phi).mulVec x = 0 ->
      forall j, dotProduct ((jetRows.map phi).row j) x = 0) :
    AugmentedRowBasisMinorCertificate
      phi jetRows originalRows rowCap := by
  apply controlledAugmentedRowBasis_exists_minor
    phi jetRows originalRows rowCap hentry hjetLI
  exact matrixRows_mem_span_of_kernel_annihilation
    (originalRows.map phi) (jetRows.map phi).row hkill

end ControlledAugmentedLift

section ControlledPolynomialLift

variable {K L Q Cols : Type*} [Field K] [Field L]
variable [Fintype Q] [DecidableEq Q]
variable [Fintype Cols] [DecidableEq Cols]

omit [Fintype Cols] [DecidableEq Cols] in
/-- Generic fallback: any already-provided bounded polynomial independent row
family has a nonzero maximal minor retaining the exact sum of row degree caps.
The augmented construction above is stronger for Gao because it does not ask
for polynomial representatives of abstract row operations. -/
theorem controlledPolynomialRowBasis_exists_minor
    (phi : Polynomial K →+* L)
    (B : Matrix Q Cols (Polynomial K))
    (rowCap : Q -> Nat)
    (hentry : forall i c, (B i c).natDegree <= rowCap i)
    (hli : LinearIndependent L (B.map phi).row) :
    exists cols : Q -> Cols,
      (B.submatrix _root_.id cols).det ≠ 0 ∧
      (B.submatrix _root_.id cols).det.natDegree <= ∑ i, rowCap i := by
  classical
  obtain ⟨cols, hminorMapped⟩ :=
    exists_columns_det_ne_zero_of_rows_linearIndependent
      (B.map phi) hli
  refine ⟨cols, ?_, ?_⟩
  · intro hzero
    apply hminorMapped
    have hmapped := BCHKSGaoSpecializationCore6400.map_submatrix_det
      phi B (_root_.id : Q -> Q) cols
    rw [hzero, map_zero] at hmapped
    simpa using hmapped.symm
  · apply BCHKSGaoSpecializationCore6400.natDegree_det_le_sum_rowCaps
    intro i j
    exact hentry i (cols j)

end ControlledPolynomialLift

/-!
`selectedJets_subset_rowBasisSet` closes abstract annihilator-to-row-space
duality.  More concretely,
`controlledAugmentedRowBasis_exists_minor_of_kernel_annihilation` converts
common-kernel annihilation and jet independence directly into a full-span
augmented row selection and a nonzero polynomial minor with row-sensitive
degree accounting.

The remaining benchmark-specific hypothesis is therefore narrow: define the
normalized sparse Gao polynomial rows and the polynomial coordinate rows for
the mixed-Hermite jets, prove their advertised entry caps, and prove the
common-kernel statement over the generic field.  The abstract construction
then introduces no denominators.  Nothing in this file asserts Gao's missing
generic kernel-dimension theorem.
-/

end BCHKSMixedHermiteRowSpan6400
end ProximityPrize.SubmissionLower
