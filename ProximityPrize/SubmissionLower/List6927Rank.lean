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
    ((min (min ((s : ℤ) - e) (derivativeCap e : ℤ)) (49 - g - 2 * e)) -
      max 0 (-g - 2 * e) + 1).toNat
def rowCountEnvelope (s : ℕ) (g : ℤ) : ℕ :=
  ∑ b : Fin (s + 1),
    (min ((s : ℤ) - b.val) (50 - g - s - 1 - 2 * b.val) -
      max 0 (max 0 (-g) - s + b.val) + 1).toNat

def envelopeUpper : ℕ := ∑ s : Fin 69, ∑ gi : Fin 70,
  min (columnCount s.val ((gi.val : ℤ) - 20))
    (rowCountEnvelope s.val ((gi.val : ℤ) - 20))


def gradeUpper (s : ℕ) : ℕ := ∑ gi : Fin 70,
  min (columnCount s ((gi.val : ℤ) - 20)) (rowCountEnvelope s ((gi.val : ℤ) - 20))

private def gradeTable : Fin 69 → ℕ := ![50, 147, 288, 470, 690, 945, 1232, 1548, 1890, 2255, 2600, 2886, 3116, 3330, 3492, 3605, 3672, 3696, 3680, 3627, 3540, 3422, 3304, 3186, 3068, 2950, 2832, 2714, 2596, 2478, 2360, 2243, 2127, 2013, 1901, 1791, 1682, 1576, 1474, 1374, 1276, 1183, 1093, 1005, 923, 842, 766, 694, 625, 561, 499, 443, 389, 340, 294, 252, 215, 179, 149, 121, 96, 76, 58, 42, 30, 21, 13, 7, 3]

private theorem grade_0 : gradeUpper 0 = 50 := by decide +kernel
private theorem grade_1 : gradeUpper 1 = 147 := by decide +kernel
private theorem grade_2 : gradeUpper 2 = 288 := by decide +kernel
private theorem grade_3 : gradeUpper 3 = 470 := by decide +kernel
private theorem grade_4 : gradeUpper 4 = 690 := by decide +kernel
private theorem grade_5 : gradeUpper 5 = 945 := by decide +kernel
private theorem grade_6 : gradeUpper 6 = 1232 := by decide +kernel
private theorem grade_7 : gradeUpper 7 = 1548 := by decide +kernel
private theorem grade_8 : gradeUpper 8 = 1890 := by decide +kernel
private theorem grade_9 : gradeUpper 9 = 2255 := by decide +kernel
private theorem grade_10 : gradeUpper 10 = 2600 := by decide +kernel
private theorem grade_11 : gradeUpper 11 = 2886 := by decide +kernel
private theorem grade_12 : gradeUpper 12 = 3116 := by decide +kernel
private theorem grade_13 : gradeUpper 13 = 3330 := by decide +kernel
private theorem grade_14 : gradeUpper 14 = 3492 := by decide +kernel
private theorem grade_15 : gradeUpper 15 = 3605 := by decide +kernel
private theorem grade_16 : gradeUpper 16 = 3672 := by decide +kernel
private theorem grade_17 : gradeUpper 17 = 3696 := by decide +kernel
private theorem grade_18 : gradeUpper 18 = 3680 := by decide +kernel
private theorem grade_19 : gradeUpper 19 = 3627 := by decide +kernel
private theorem grade_20 : gradeUpper 20 = 3540 := by decide +kernel
private theorem grade_21 : gradeUpper 21 = 3422 := by decide +kernel
private theorem grade_22 : gradeUpper 22 = 3304 := by decide +kernel
private theorem grade_23 : gradeUpper 23 = 3186 := by decide +kernel
private theorem grade_24 : gradeUpper 24 = 3068 := by decide +kernel
private theorem grade_25 : gradeUpper 25 = 2950 := by decide +kernel
private theorem grade_26 : gradeUpper 26 = 2832 := by decide +kernel
private theorem grade_27 : gradeUpper 27 = 2714 := by decide +kernel
private theorem grade_28 : gradeUpper 28 = 2596 := by decide +kernel
private theorem grade_29 : gradeUpper 29 = 2478 := by decide +kernel
private theorem grade_30 : gradeUpper 30 = 2360 := by decide +kernel
private theorem grade_31 : gradeUpper 31 = 2243 := by decide +kernel
private theorem grade_32 : gradeUpper 32 = 2127 := by decide +kernel
private theorem grade_33 : gradeUpper 33 = 2013 := by decide +kernel
private theorem grade_34 : gradeUpper 34 = 1901 := by decide +kernel
private theorem grade_35 : gradeUpper 35 = 1791 := by decide +kernel
private theorem grade_36 : gradeUpper 36 = 1682 := by decide +kernel
private theorem grade_37 : gradeUpper 37 = 1576 := by decide +kernel
private theorem grade_38 : gradeUpper 38 = 1474 := by decide +kernel
private theorem grade_39 : gradeUpper 39 = 1374 := by decide +kernel
private theorem grade_40 : gradeUpper 40 = 1276 := by decide +kernel
private theorem grade_41 : gradeUpper 41 = 1183 := by decide +kernel
private theorem grade_42 : gradeUpper 42 = 1093 := by decide +kernel
private theorem grade_43 : gradeUpper 43 = 1005 := by decide +kernel
private theorem grade_44 : gradeUpper 44 = 923 := by decide +kernel
private theorem grade_45 : gradeUpper 45 = 842 := by decide +kernel
private theorem grade_46 : gradeUpper 46 = 766 := by decide +kernel
private theorem grade_47 : gradeUpper 47 = 694 := by decide +kernel
private theorem grade_48 : gradeUpper 48 = 625 := by decide +kernel
private theorem grade_49 : gradeUpper 49 = 561 := by decide +kernel
private theorem grade_50 : gradeUpper 50 = 499 := by decide +kernel
private theorem grade_51 : gradeUpper 51 = 443 := by decide +kernel
private theorem grade_52 : gradeUpper 52 = 389 := by decide +kernel
private theorem grade_53 : gradeUpper 53 = 340 := by decide +kernel
private theorem grade_54 : gradeUpper 54 = 294 := by decide +kernel
private theorem grade_55 : gradeUpper 55 = 252 := by decide +kernel
private theorem grade_56 : gradeUpper 56 = 215 := by decide +kernel
private theorem grade_57 : gradeUpper 57 = 179 := by decide +kernel
private theorem grade_58 : gradeUpper 58 = 149 := by decide +kernel
private theorem grade_59 : gradeUpper 59 = 121 := by decide +kernel
private theorem grade_60 : gradeUpper 60 = 96 := by decide +kernel
private theorem grade_61 : gradeUpper 61 = 76 := by decide +kernel
private theorem grade_62 : gradeUpper 62 = 58 := by decide +kernel
private theorem grade_63 : gradeUpper 63 = 42 := by decide +kernel
private theorem grade_64 : gradeUpper 64 = 30 := by decide +kernel
private theorem grade_65 : gradeUpper 65 = 21 := by decide +kernel
private theorem grade_66 : gradeUpper 66 = 13 := by decide +kernel
private theorem grade_67 : gradeUpper 67 = 7 := by decide +kernel
private theorem grade_68 : gradeUpper 68 = 3 := by decide +kernel

private theorem grade_table (s : Fin 69) : gradeUpper s.val = gradeTable s := by
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
  · exact grade_68

def blockUpper : ℕ := 104045

private theorem envelope_upper_eq : envelopeUpper = blockUpper := by
  change (∑ s : Fin 69, gradeUpper s.val) = _
  simp_rw [grade_table]
  decide +kernel

theorem strict_source_surplus : 262144 * blockUpper < Fintype.card SourceIndex := by
  rw [source_card]
  decide

abbrev Block := Fin 69 × Fin 70
def balance (q : Block) : ℤ := (q.2.val : ℤ) - 20
abbrev ColFiber (q : Block) :=
  (e : Fin (min q.1.val 9 + 1)) ×
    {a : Fin (min (q.1.val - e.val) (derivativeCap e.val) + 1) //
      0 ≤ balance q + a.val + 2 * e.val ∧ balance q + a.val + 2 * e.val < 50}
abbrev Col := (q : Block) × ColFiber q

abbrev RowFiber (q : Block) :=
  (b : Fin (q.1.val + 1)) × {f : Fin (q.1.val - b.val + 1) //
    (b.val : ℤ) ≤ balance q + q.1.val + f.val ∧
      balance q + q.1.val + f.val + 2 * b.val < 50}
abbrev Row := (q : Block) × RowFiber q

theorem colFiber_card (q : Block) : Fintype.card (ColFiber q) = columnCount q.1.val (balance q) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_subtype]
  unfold columnCount
  let value (e : ℕ) : ℕ :=
    (min (min ((q.1.val : ℤ)-e) (derivativeCap e : ℤ)) (49-balance q-2*e) -
      max 0 (-balance q - 2*e) + 1).toNat
  change _ = ∑ e ∈ Finset.range (min q.1.val 9 + 1), value e
  rw [← Fin.sum_univ_eq_sum_range value]
  apply Finset.sum_congr rfl
  intro e _
  have hf : (Finset.univ.filter fun a : Fin (min (q.1.val-e.val) (derivativeCap e.val)+1) =>
      0 ≤ balance q + a.val + 2*e.val ∧ balance q + a.val + 2*e.val < 50) =
    (Finset.univ.filter fun a : Fin (min (q.1.val-e.val) (derivativeCap e.val)+1) =>
      -balance q - 2*e.val ≤ (a.val:ℤ) ∧ (a.val:ℤ) ≤ 49-balance q-2*e.val) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hf, fin_interval_card]
  have he := e.isLt
  have hcast : ((min (q.1.val-e.val) (derivativeCap e.val)+1 : ℕ) : ℤ)-1 =
      min ((q.1.val:ℤ)-e.val) (derivativeCap e.val : ℤ) := by omega
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
        balance q + q.1.val + f.val + 2 * b.val < 50) =
      (Finset.univ.filter fun f : Fin (q.1.val - b.val + 1) ↦
        max 0 (-(balance q)) - q.1.val + b.val ≤ (f.val : ℤ) ∧
          (f.val : ℤ) ≤ 50 - balance q - q.1.val - 1 - 2 * b.val) := by
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

theorem rowExponent_contact (i : Row) : localContactOrder 2 (rowExponent i) < 50 := by
  have hp := i.2.2.2
  rw [localContactOrder_eq]
  simp [rowExponent, localT, localE, localAux, localY]
  omega

def rowOriginal (i : Row) : LowContactIndex 2 50 := ⟨rowExponent i, rowExponent_contact i⟩

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

theorem low_column_represented (i : SourceIndex) (hx : i.2.val < 50) :
    ∃ j : Col, colOriginal j = i := by
  rcases i with ⟨⟨s,e,a⟩,x⟩
  change x.val < 50 at hx
  have ho := jet_order (⟨s,e,a⟩ : Jet)
  simp only [e1, e2] at ho
  let gi : Fin 70 := ⟨((x.val : ℤ) - a.val - 2 * e.val + 20).toNat, by omega⟩
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

theorem point_entry_constraint (r : LowContactIndex 2 50) (j : SourceIndex) :
    pointMatrix (F := F) 50 0 0 r j =
      (localConstraintAt 50 0 0 (columns j).polynomial).coeff r.val := by
  change (unscaledLocalSubstitution 2 (0 : F) 0 (columns j).polynomial).coeff r.val = _
  simp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    coeff_projectLowContact, ite_eq_left r.property]

theorem high_column_zero (j : SourceIndex) (hx : 50 ≤ j.2.val) :
    (pointMatrix (F := F) 50 0 0).col j = 0 := by
  ext r
  rw [Matrix.col_apply, point_entry_constraint, origin_high_X_zero 50 j hx]
  simp

/-- Every actual nonzero coefficient has a representative in the finite envelope. -/
theorem nonzero_row_represented (r : LowContactIndex 2 50) (j : SourceIndex)
    (hne : pointMatrix (F := F) 50 0 0 r j ≠ 0) :
    ∃ i : Row, rowOriginal i = r := by
  have hx : j.2.val < 50 := by
    by_contra hh
    have hz := high_column_zero (F := F) j (by omega)
    exact hne (congrFun hz r)
  have hs : r.val.weight (localJetDegreeWeight 2) = j.1.1.val := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_jet_ne 50 j r.val hh))
  have hg : r.val.weight localBalance = (j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 := by
    by_contra hh
    exact hne ((point_entry_constraint r j).trans
      (origin_coefficient_zero_of_balance_ne 50 j r.val hh))
  have he : r.val (localE 2) ≤ r.val (localT 2) := by
    apply localE_le_localT_of_mem_support (0 : F) 0 (columns j).polynomial
    exact mem_support_iff.mpr hne
  have ht := r.property
  rw [localContactOrder_eq] at ht
  have hsj := row_jet_formula r.val
  have hgj := row_balance_formula r.val
  have ho := jet_order j.1
  let gi : Fin 70 := ⟨((j.2.val : ℤ) - e1 j.1 - 2 * e2 j.1 + 20).toNat, by omega⟩
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
  (pointMatrix 50 (0 : F) 0).submatrix rowOriginal colOriginal

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
  change (∑ s : Fin 69, ∑ gi : Fin 70,
    min (rowCountEnvelope s.val ((gi.val : ℤ) - 20))
      (columnCount s.val ((gi.val : ℤ) - 20))) ≤ blockUpper
  simp_rw [min_comm]
  exact envelope_upper_eq.le

/-- Restrict the actual origin columns to X<50 without increasing the rank. -/
theorem origin_rank_le_low_columns :
    (pointMatrix (F := F) 50 0 0).rank ≤
      ((pointMatrix (F := F) 50 0 0).submatrix id colOriginal).rank := by
  apply rank_le_col_representatives
  intro j
  by_cases hx : j.2.val < 50
  · obtain ⟨c,hc⟩ := low_column_represented j hx
    exact Or.inr ⟨c,by rw [hc]⟩
  · exact Or.inl (high_column_zero j (by omega))

/-- Every nonzero low-column row is represented by the finite target envelope. -/
theorem low_columns_rank_le_finite :
    ((pointMatrix (F := F) 50 0 0).submatrix id colOriginal).rank ≤
      (finiteMatrix (F := F)).rank := by
  classical
  apply rank_le_row_representatives
  intro r
  by_cases hz : ((pointMatrix (F := F) 50 0 0).submatrix id colOriginal) r = 0
  · exact Or.inl hz
  · right
    obtain ⟨c,hc⟩ := Function.ne_iff.mp hz
    have hc' : pointMatrix (F := F) 50 0 0 r (colOriginal c) ≠ 0 := hc
    obtain ⟨i,hi⟩ := nonzero_row_represented r (colOriginal c) hc'
    refine ⟨i, ?_⟩
    exact congrArg (fun r : LowContactIndex 2 50 ↦
      ((pointMatrix (F := F) 50 0 0).submatrix id colOriginal) r) hi.symm

/-- Kernel-checked static origin rank, valid over every coefficient field. -/
theorem origin_rank : (pointMatrix (F := F) 50 0 0).rank ≤ blockUpper :=
  origin_rank_le_low_columns.trans (low_columns_rank_le_finite.trans finiteMatrix_rank)

end
end List6927Rank
