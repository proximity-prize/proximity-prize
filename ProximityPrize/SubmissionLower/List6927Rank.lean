import ProximityPrize.SubmissionLower.List6927Source

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

namespace List6927Rank

noncomputable section
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative List6927Source
open Sol1.C42 (localBalance fin_interval_card)
open Sol1.C52 (row_jet_formula row_balance_formula rank_le_col_representatives
  rank_le_row_representatives rank_le_sum_min_dependent)
open scoped BigOperators Matrix

def columnCount (s : ℕ) (g : ℤ) : ℕ :=
  ∑ e ∈ Finset.range (min s 9 + 1),
    ((min (min ((s : ℤ) - e) (20 - 2 * (e : ℤ))) (48 - g - 2 * e)) -
      max 0 (-g - 2 * e) + 1).toNat
def rowCountEnvelope (s : ℕ) (g : ℤ) : ℕ :=
  ∑ b : Fin (s + 1),
    (min ((s : ℤ) - b.val) (49 - g - s - 1 - 2 * b.val) -
      max 0 (max 0 (-g) - s + b.val) + 1).toNat

def envelopeUpper : ℕ := ∑ s : Fin 68, ∑ gi : Fin 69,
  min (columnCount s.val ((gi.val : ℤ) - 20))
    (rowCountEnvelope s.val ((gi.val : ℤ) - 20))


def gradeUpper (s : ℕ) : ℕ := ∑ gi : Fin 69,
  min (columnCount s ((gi.val : ℤ) - 20)) (rowCountEnvelope s ((gi.val : ℤ) - 20))

private def gradeTable : Fin 68 → ℕ := ![49, 144, 282, 460, 675, 924, 1204, 1512, 1845, 2200, 2535, 2850, 3108, 3312, 3465, 3570, 3630, 3648, 3627, 3570, 3480, 3360, 3240, 3120, 3000, 2880, 2760, 2640, 2520, 2400, 2281, 2163, 2047, 1933, 1822, 1712, 1604, 1500, 1400, 1300, 1205, 1115, 1025, 941, 860, 782, 710, 639, 575, 511, 455, 399, 350, 302, 260, 221, 185, 155, 125, 100, 80, 60, 44, 32, 22, 13, 7, 3]


private theorem grade_0 : gradeUpper 0 = 49 := by decide +kernel
private theorem grade_1 : gradeUpper 1 = 144 := by decide +kernel
private theorem grade_2 : gradeUpper 2 = 282 := by decide +kernel
private theorem grade_3 : gradeUpper 3 = 460 := by decide +kernel
private theorem grade_4 : gradeUpper 4 = 675 := by decide +kernel
private theorem grade_5 : gradeUpper 5 = 924 := by decide +kernel
private theorem grade_6 : gradeUpper 6 = 1204 := by decide +kernel
private theorem grade_7 : gradeUpper 7 = 1512 := by decide +kernel
private theorem grade_8 : gradeUpper 8 = 1845 := by decide +kernel
private theorem grade_9 : gradeUpper 9 = 2200 := by decide +kernel
private theorem grade_10 : gradeUpper 10 = 2535 := by decide +kernel
private theorem grade_11 : gradeUpper 11 = 2850 := by decide +kernel
private theorem grade_12 : gradeUpper 12 = 3108 := by decide +kernel
private theorem grade_13 : gradeUpper 13 = 3312 := by decide +kernel
private theorem grade_14 : gradeUpper 14 = 3465 := by decide +kernel
private theorem grade_15 : gradeUpper 15 = 3570 := by decide +kernel
private theorem grade_16 : gradeUpper 16 = 3630 := by decide +kernel
private theorem grade_17 : gradeUpper 17 = 3648 := by decide +kernel
private theorem grade_18 : gradeUpper 18 = 3627 := by decide +kernel
private theorem grade_19 : gradeUpper 19 = 3570 := by decide +kernel
private theorem grade_20 : gradeUpper 20 = 3480 := by decide +kernel
private theorem grade_21 : gradeUpper 21 = 3360 := by decide +kernel
private theorem grade_22 : gradeUpper 22 = 3240 := by decide +kernel
private theorem grade_23 : gradeUpper 23 = 3120 := by decide +kernel
private theorem grade_24 : gradeUpper 24 = 3000 := by decide +kernel
private theorem grade_25 : gradeUpper 25 = 2880 := by decide +kernel
private theorem grade_26 : gradeUpper 26 = 2760 := by decide +kernel
private theorem grade_27 : gradeUpper 27 = 2640 := by decide +kernel
private theorem grade_28 : gradeUpper 28 = 2520 := by decide +kernel
private theorem grade_29 : gradeUpper 29 = 2400 := by decide +kernel
private theorem grade_30 : gradeUpper 30 = 2281 := by decide +kernel
private theorem grade_31 : gradeUpper 31 = 2163 := by decide +kernel
private theorem grade_32 : gradeUpper 32 = 2047 := by decide +kernel
private theorem grade_33 : gradeUpper 33 = 1933 := by decide +kernel
private theorem grade_34 : gradeUpper 34 = 1822 := by decide +kernel
private theorem grade_35 : gradeUpper 35 = 1712 := by decide +kernel
private theorem grade_36 : gradeUpper 36 = 1604 := by decide +kernel
private theorem grade_37 : gradeUpper 37 = 1500 := by decide +kernel
private theorem grade_38 : gradeUpper 38 = 1400 := by decide +kernel
private theorem grade_39 : gradeUpper 39 = 1300 := by decide +kernel
private theorem grade_40 : gradeUpper 40 = 1205 := by decide +kernel
private theorem grade_41 : gradeUpper 41 = 1115 := by decide +kernel
private theorem grade_42 : gradeUpper 42 = 1025 := by decide +kernel
private theorem grade_43 : gradeUpper 43 = 941 := by decide +kernel
private theorem grade_44 : gradeUpper 44 = 860 := by decide +kernel
private theorem grade_45 : gradeUpper 45 = 782 := by decide +kernel
private theorem grade_46 : gradeUpper 46 = 710 := by decide +kernel
private theorem grade_47 : gradeUpper 47 = 639 := by decide +kernel
private theorem grade_48 : gradeUpper 48 = 575 := by decide +kernel
private theorem grade_49 : gradeUpper 49 = 511 := by decide +kernel
private theorem grade_50 : gradeUpper 50 = 455 := by decide +kernel
private theorem grade_51 : gradeUpper 51 = 399 := by decide +kernel
private theorem grade_52 : gradeUpper 52 = 350 := by decide +kernel
private theorem grade_53 : gradeUpper 53 = 302 := by decide +kernel
private theorem grade_54 : gradeUpper 54 = 260 := by decide +kernel
private theorem grade_55 : gradeUpper 55 = 221 := by decide +kernel
private theorem grade_56 : gradeUpper 56 = 185 := by decide +kernel
private theorem grade_57 : gradeUpper 57 = 155 := by decide +kernel
private theorem grade_58 : gradeUpper 58 = 125 := by decide +kernel
private theorem grade_59 : gradeUpper 59 = 100 := by decide +kernel
private theorem grade_60 : gradeUpper 60 = 80 := by decide +kernel
private theorem grade_61 : gradeUpper 61 = 60 := by decide +kernel
private theorem grade_62 : gradeUpper 62 = 44 := by decide +kernel
private theorem grade_63 : gradeUpper 63 = 32 := by decide +kernel
private theorem grade_64 : gradeUpper 64 = 22 := by decide +kernel
private theorem grade_65 : gradeUpper 65 = 13 := by decide +kernel
private theorem grade_66 : gradeUpper 66 = 7 := by decide +kernel
private theorem grade_67 : gradeUpper 67 = 3 := by decide +kernel

private theorem grade_table (s : Fin 68) : gradeUpper s.val = gradeTable s := by
  fin_cases s
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67


def blockUpper : ℕ := 100948

private theorem envelope_upper_eq : envelopeUpper = blockUpper := by
  change (∑ s : Fin 68, gradeUpper s.val) = _
  simp_rw [grade_table]
  decide +kernel

theorem strict_source_surplus : 262144 * blockUpper < Fintype.card SourceIndex := by
  rw [source_card]
  decide

abbrev Block := Fin 68 × Fin 69
def balance (q : Block) : ℤ := (q.2.val : ℤ) - 20
abbrev ColFiber (q : Block) :=
  (e : Fin (min q.1.val 9 + 1)) ×
    {a : Fin (min (q.1.val - e.val) (20 - 2 * e.val) + 1) //
      0 ≤ balance q + a.val + 2 * e.val ∧ balance q + a.val + 2 * e.val < 49}
abbrev Col := (q : Block) × ColFiber q

abbrev RowFiber (q : Block) :=
  (b : Fin (q.1.val + 1)) × {f : Fin (q.1.val - b.val + 1) //
    (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
      balance q + q.1.val + f.val + 2 * b.val < 49}
abbrev Row := (q : Block) × RowFiber q

theorem colFiber_card (q : Block) : Fintype.card (ColFiber q) = columnCount q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  unfold columnCount
  let value (e : ℕ) : ℕ :=
    (min (min ((q.1.val : ℤ)-e) (20-2*(e:ℤ))) (48-balance q-2*e) -
      max 0 (-balance q - 2*e) + 1).toNat
  change _ = ∑ e ∈ Finset.range (min q.1.val 9 + 1), value e
  rw [← Fin.sum_univ_eq_sum_range value]
  apply Finset.sum_congr rfl
  intro e _
  have hf : (Finset.univ.filter fun a : Fin (min (q.1.val-e.val) (20-2*e.val)+1) =>
      0 ≤ balance q + a.val + 2*e.val ∧ balance q + a.val + 2*e.val < 49) =
    (Finset.univ.filter fun a : Fin (min (q.1.val-e.val) (20-2*e.val)+1) =>
      -balance q - 2*e.val ≤ (a.val:ℤ) ∧ (a.val:ℤ) ≤ 48-balance q-2*e.val) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hf, fin_interval_card]
  have he := e.isLt
  have hcast : ((min (q.1.val-e.val) (20-2*e.val)+1 : ℕ) : ℤ)-1 =
      min ((q.1.val:ℤ)-e.val) (20-2*(e.val:ℤ)) := by omega
  rw [hcast]

theorem rowFiber_card (q : Block) : Fintype.card (RowFiber q) =
    rowCountEnvelope q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  unfold rowCountEnvelope
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_subtype]
  have hf : (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
      (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
        balance q + q.1.val + f.val + 2 * b.val < 49) =
      (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
        max 0 (-(balance q)) - q.1.val + b.val ≤ (f.val : ℤ) ∧
          (f.val : ℤ) ≤ 49 - balance q - q.1.val - 1 - 2 * b.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hb := b.isLt
    have hh := f.isLt
    omega
  rw [hf, fin_interval_card]
  have hb := b.isLt
  have hh : ((q.1.val - b.val + 1 : ℕ) : ℤ) - 1 = (q.1.val : ℤ) - b.val := by omega
  rw [hh]

def colOriginal (j : Col) : SourceIndex :=
  let jet : Jet := ⟨j.1.1, j.2.1, j.2.2.1⟩
  ⟨jet, ⟨(balance j.1 + j.2.2.1.val + 2 * j.2.1.val).toNat, by
    have hp := j.2.2.2
    have hw := width_lower jet
    omega⟩⟩

def rowExponent (i : Row) : LocalVariable 2 →₀ ℕ :=
  Finsupp.single (localT 2) (balance i.1 + i.1.1.val + i.2.2.1.val).toNat +
  Finsupp.single (localE 2) i.2.1.val +
  Finsupp.single (localY (0 : Fin 2)) (i.1.1.val - i.2.1.val - i.2.2.1.val) +
  Finsupp.single (localY (1 : Fin 2)) i.2.2.1.val

theorem rowExponent_contact (i : Row) : localContactOrder 2 (rowExponent i) < 49 := by
  have hp := i.2.2.2
  rw [localContactOrder_eq]
  simp [rowExponent, localT, localE, localAux, localY]
  omega

def rowOriginal (i : Row) : LowContactIndex 2 49 := ⟨rowExponent i, rowExponent_contact i⟩

theorem rowExponent_jet (i : Row) :
    (rowExponent i).weight (localJetDegreeWeight 2) = i.1.1.val := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  simp only [rowExponent, map_add, Finsupp.weight_single, localJetDegreeWeight,
    localT, localE, localAux, localY, nsmul_eq_mul, Nat.cast_id, mul_zero, mul_one, zero_add]
  omega

theorem rowExponent_balance (i : Row) : (rowExponent i).weight localBalance = balance i.1 := by
  have hb := i.2.1.isLt
  have hf := i.2.2.1.isLt
  have hp := i.2.2.2
  simp only [rowExponent, map_add, Finsupp.weight_single, localBalance,
    localT, localE, localAux, localY, nsmul_eq_mul]
  omega


theorem colOriginal_grade (j : Col) : (colOriginal j).1.1 = j.1.1 := rfl

theorem colOriginal_balance (j : Col) :
    ((colOriginal j).2.val : ℤ) - e1 (colOriginal j).1 - 2 * e2 (colOriginal j).1 =
      balance j.1 := by
  have hp := j.2.2.2
  simp only [colOriginal, e1, e2]
  omega

theorem low_column_represented (i : SourceIndex) (hx : i.2.val < 49) :
    ∃ j : Col, colOriginal j = i := by
  rcases i with ⟨⟨s,e,a⟩,x⟩
  change x.val < 49 at hx
  have ho := jet_order (⟨s,e,a⟩ : Jet)
  simp only [e1, e2] at ho
  let gi : Fin 69 := ⟨((x.val : ℤ) - a.val - 2 * e.val + 20).toNat, by omega⟩
  let q : Block := ⟨s,gi⟩
  have hgi : balance q = (x.val : ℤ) - a.val - 2 * e.val := by
    dsimp [balance,q,gi]
    omega
  let j : Col := ⟨q,e,⟨a,by rw [hgi]; omega⟩⟩
  refine ⟨j, ?_⟩
  dsimp only [colOriginal, j, q]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Fin.ext
  change (balance q + a.val + 2 * e.val).toNat = x.val
  rw [hgi]
  omega

variable {F : Type*} [Field F]

theorem point_entry_constraint (r : LowContactIndex 2 49) (j : SourceIndex) :
    pointMatrix (F := F) 49 0 0 r j =
      (localConstraintAt 49 0 0 (columns j).polynomial).coeff r.val := by
  change (unscaledLocalSubstitution 2 (0 : F) 0 (columns j).polynomial).coeff r.val = _
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coeff_projectLowContact, ite_eq_left r.property]

theorem high_column_zero (j : SourceIndex) (hx : 49 ≤ j.2.val) :
    (pointMatrix (F := F) 49 0 0).col j = 0 := by
  ext r
  rw [Matrix.col_apply, point_entry_constraint, origin_high_X_zero 49 j hx]
  simp

/-- Every actual nonzero coefficient has a representative in the finite envelope. -/
theorem nonzero_row_represented (r : LowContactIndex 2 49) (j : SourceIndex)
    (hne : pointMatrix (F := F) 49 0 0 r j ≠ 0) :
    ∃ i : Row, rowOriginal i = r := by
  have hx : j.2.val < 49 := by
    by_contra hh
    have hz := high_column_zero (F := F) j (by omega)
    exact hne (congrFun hz r)
  have hs : r.val.weight (localJetDegreeWeight 2) = j.1.1.val := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_jet_ne 49 j r.val hh))
  have hg : r.val.weight localBalance = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_balance_ne 49 j r.val hh))
  have he : r.val (localE 2) ≤ r.val (localT 2) := by
    apply localE_le_localT_of_mem_support (0 : F) 0 (columns j).polynomial
    exact mem_support_iff.mpr hne
  have ht := r.property
  rw [localContactOrder_eq] at ht
  have hsj := row_jet_formula r.val
  have hgj := row_balance_formula r.val
  have ho := jet_order j.1
  let gi : Fin 69 := ⟨((j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 + 20).toNat, by omega⟩
  let q : Block := ⟨j.1.1,gi⟩
  have hq : balance q = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    dsimp [balance,q,gi]
    omega
  let b : Fin (q.1.val + 1) := ⟨r.val (localE 2), by dsimp [q]; omega⟩
  let f : Fin (q.1.val - b.val + 1) := ⟨r.val (localY (1 : Fin 2)), by dsimp [q,b]; omega⟩
  have hT : balance q + q.1.val + f.val = (r.val (localT 2) : ℤ) := by
    change balance q + j.1.1.val + (r.val (localY (1 : Fin 2)) : ℤ) = _
    rw [hq]
    omega
  let i : Row := ⟨q,b,⟨f,by rw [hT]; dsimp [b]; omega⟩⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  ext v
  rcases v with _ | (_ | v)
  · change rowExponent i (localT 2) = r.val (localT 2)
    have heval : rowExponent i (localT 2) =
        (balance q + q.1.val + f.val).toNat := by
      simp [rowExponent, localT, localE, localAux, localY, i]
    rw [heval, hT]
    simp
  · change rowExponent i (localE 2) = r.val (localE 2)
    simp [rowExponent, localT, localE, localAux, localY, i,b]
  · fin_cases v
    · change rowExponent i (localY (0 : Fin 2)) = r.val (localY (0 : Fin 2))
      have heval : rowExponent i (localY (0 : Fin 2)) =
          j.1.1.val - r.val (localE 2) - r.val (localY (1 : Fin 2)) := by
        simp [rowExponent, localT, localE, localAux, localY, i,b,f,q]
      rw [heval]
      omega
    · change rowExponent i (localY (1 : Fin 2)) = r.val (localY (1 : Fin 2))
      simp [rowExponent, localT, localE, localAux, localY, i,b,f]

def finiteMatrix : Matrix Row Col F :=
  (pointMatrix 49 (0 : F) 0).submatrix rowOriginal colOriginal

/-- Actual origin coefficients vanish between different s,g blocks. -/
theorem finiteMatrix_offblock (i : Row) (j : Col) (hne : i.1 ≠ j.1) :
    finiteMatrix (F := F) i j = 0 := by
  rw [finiteMatrix, Matrix.submatrix_apply, point_entry_constraint]
  by_cases hs : i.1.1 = j.1.1
  · apply origin_coefficient_zero_of_balance_ne
    dsimp only [rowOriginal]
    rw [rowExponent_balance, colOriginal_balance]
    intro hbalance
    apply hne
    apply Prod.ext hs
    apply Fin.ext
    unfold balance at hbalance
    omega
  · apply origin_coefficient_zero_of_jet_ne
    dsimp only [rowOriginal]
    rw [rowExponent_jet, colOriginal_grade]
    exact fun h ↦ hs (Fin.ext h)

/-- The finite semantic block matrix has the exact static C42 rank allowance. -/
theorem finiteMatrix_rank : (finiteMatrix (F := F)).rank ≤ blockUpper := by
  classical
  apply (rank_le_sum_min_dependent (finiteMatrix (F := F)) finiteMatrix_offblock).trans
  simp_rw [rowFiber_card, colFiber_card]
  rw [Fintype.sum_prod_type]
  change (∑ s : Fin 68, ∑ gi : Fin 69,
    min (rowCountEnvelope s.val ((gi.val : ℤ) - 20))
      (columnCount s.val ((gi.val : ℤ) - 20))) ≤ blockUpper
  simp_rw [min_comm]
  exact envelope_upper_eq.le

/-- Restrict the actual origin columns to X<49 without increasing the rank. -/
theorem origin_rank_le_low_columns :
    (pointMatrix (F := F) 49 0 0).rank ≤
      ((pointMatrix (F := F) 49 0 0).submatrix id colOriginal).rank := by
  apply rank_le_col_representatives
  intro j
  by_cases hx : j.2.val < 49
  · obtain ⟨c,hc⟩ := low_column_represented j hx
    exact Or.inr ⟨c,by rw [hc]⟩
  · exact Or.inl (high_column_zero j (by omega))

/-- Every nonzero low-column row is represented by the finite target envelope. -/
theorem low_columns_rank_le_finite :
    ((pointMatrix (F := F) 49 0 0).submatrix id colOriginal).rank ≤
      (finiteMatrix (F := F)).rank := by
  classical
  apply rank_le_row_representatives
  intro r
  by_cases hz : ((pointMatrix (F := F) 49 0 0).submatrix id colOriginal) r = 0
  · exact Or.inl hz
  · right
    obtain ⟨c,hc⟩ := Function.ne_iff.mp hz
    have hc' : pointMatrix (F := F) 49 0 0 r (colOriginal c) ≠ 0 := hc
    obtain ⟨i,hi⟩ := nonzero_row_represented r (colOriginal c) hc'
    refine ⟨i, ?_⟩
    exact congrArg (fun r : LowContactIndex 2 49 ↦
      ((pointMatrix (F := F) 49 0 0).submatrix id colOriginal) r) hi.symm

/-- Kernel-checked static origin rank, valid over every coefficient field. -/
theorem origin_rank : (pointMatrix (F := F) 49 0 0).rank ≤ blockUpper :=
  origin_rank_le_low_columns.trans (low_columns_rank_le_finite.trans finiteMatrix_rank)

end
end List6927Rank
