import ProximityPrize.SubmissionLower.PoleReceipts
import ProximityPrize.SubmissionLower.HighJoint6921Certificate

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

namespace HighJoint6921

open K1_14 Polynomial
open scoped BigOperators

inductive HeightBand
  | first | second | third | fourth
  deriving DecidableEq

def HeightBand.lower : HeightBand → ℕ
  | .first => 2442
  | .second => 3555
  | .third => 8250
  | .fourth => 24000

def HeightBand.upper : HeightBand → ℕ
  | .first => 3554
  | .second => 8249
  | .third => 23999
  | .fourth => 32970

def HeightBand.ordinateCap : HeightBand → ℕ
  | .first => 12
  | .second => 5
  | .third => 3
  | .fourth => 2

def bridgeShape (U : ℕ) : Shape := ⟨2048, 2845, 600, U⟩
def laterShape (U : ℕ) : Shape := ⟨358, 500, 105, U⟩

def HeightBand.fullBank : HeightBand → Shape
  | .first => bridgeShape 75000
  | _ => laterShape 66251

def HeightBand.seedBank : HeightBand → Shape
  | .first => bridgeShape 75000
  | .second => laterShape 6798
  | .third => laterShape 4860
  | .fourth => laterShape 3913

/-- The tested seed ceiling for each positive actual ordinate degree. -/
def HeightBand.seedCap : HeightBand → ℕ → ℕ
  | .first, 1 => 229
  | .first, 2 => 221
  | .first, 3 => 212
  | .first, 4 => 202
  | .first, 5 => 191
  | .first, 6 => 178
  | .first, 7 => 161
  | .first, 8 => 140
  | .first, 9 => 114
  | .first, 10 => 82
  | .first, 11 => 46
  | .first, 12 => 5
  | .second, 1 => 108
  | .second, 2 => 103
  | .second, 3 => 99
  | .second, 4 => 94
  | .second, 5 => 87
  | .third, 1 => 41
  | .third, 2 => 37
  | .third, 3 => 33
  | .fourth, 1 => 28
  | .fourth, 2 => 25
  | _, _ => 0

private theorem bridgeCount (U : ℕ) : columnCount (bridgeShape U) = 1530146 := by
  change (∑ q ∈ Finset.range 2846, (min q 600 + 1)) = _
  exact (range_sum_eq (fun q => min q 600 + 1) 2846).trans (by decide +kernel)

private theorem bridgeGrade (U : ℕ) : gradeMoment (bridgeShape U) = 2397109535 := by
  change (∑ q ∈ Finset.range 2846, q*(min q 600+1)) = _
  exact (range_sum_eq (fun q => q*(min q 600+1)) 2846).trans (by decide +kernel)

private theorem bridgeIndex (U : ℕ) : indexMoment (bridgeShape U) = 440953700 := by
  change (∑ q ∈ Finset.range 2846, (min q 600+1)*min q 600/2) = _
  exact (range_sum_eq (fun q => (min q 600+1)*min q 600/2) 2846).trans (by decide +kernel)

private theorem bridgeNodeSum :
    (∑ q ∈ Finset.range 2846, nodeCostAt (bridgeShape 0) q) = 963929476 :=
  (range_sum_eq (nodeCostAt (bridgeShape 0)) 2846).trans (by decide +kernel)

private theorem bridgeFixed (U : ℕ) :
    fixedDebit (bridgeShape U) = triangle U * 252688328556544 := by
  change triangle U * 262144 *
    (∑ q ∈ Finset.range 2846, nodeCostAt (bridgeShape 0) q) = _
  rw [bridgeNodeSum, Nat.mul_assoc]

private theorem laterCount (U : ℕ) : columnCount (laterShape U) = 47541 := by
  unfold columnCount laterShape
  rw [range_sum_eq]
  rfl

private theorem laterGrade (U : ℕ) : gradeMoment (laterShape U) = 13083580 := by
  change (∑ q ∈ Finset.range 501, q*(min q 105+1)) = _
  exact (range_sum_eq (fun q => q*(min q 105+1)) 501).trans (by decide +kernel)

private theorem laterIndex (U : ℕ) : indexMoment (laterShape U) = 2396660 := by
  change (∑ q ∈ Finset.range 501, (min q 105+1)*min q 105/2) = _
  exact (range_sum_eq (fun q => (min q 105+1)*min q 105/2) 501).trans (by decide +kernel)

private theorem laterNodeSum :
    (∑ q ∈ Finset.range 501, nodeCostAt (laterShape 0) q) = 5210801 :=
  (range_sum_eq (nodeCostAt (laterShape 0)) 501).trans (by decide +kernel)

private theorem laterFixed (U : ℕ) :
    fixedDebit (laterShape U) = triangle U * 1365980217344 := by
  change triangle U * 262144 *
    (∑ q ∈ Finset.range 501, nodeCostAt (laterShape 0) q) = _
  rw [laterNodeSum, Nat.mul_assoc]

private theorem affine_of_moments {s : Shape} {h e step columns grade index nodes pole penalty : ℕ}
    (hc : columnCount s = columns) (hg : gradeMoment s = grade) (hi : indexMoment s = index)
    (hn : fixedDebit s = nodes) (hd : BankDebit.extra s = pole) (hp : seedPenalty s e step = penalty)
    (bound : nodes + h * (2*pole + 2*(triangle s.U*index+penalty)) +
        base h * (triangle s.U*grade) < triangle s.U * (top s*columns+index) ∧
      2*pole + 2*(triangle s.U*index+penalty) ≤ triangle s.U*grade) :
    AffineCertificate s h e step := by
  unfold AffineCertificate affineCost affineSlope affineValue ordinatePenalty linearDebit
  rw [hc, hg, hi, hn, hd, hp]
  exact bound

private theorem penalty_ordinate_first : seedPenalty (bridgeShape 75000) 13 0 = 421239211231755451 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_ordinate_first : AffineCertificate (bridgeShape 75000) 2442 13 0 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_ordinate_first (by decide +kernel)

private theorem penalty_seed_first_1 : seedPenalty (bridgeShape 75000) 1 230 = 450675008267945670 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_1 : AffineCertificate (bridgeShape 75000) 2442 1 230 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_1 (by decide +kernel)

private theorem penalty_seed_first_2 : seedPenalty (bridgeShape 75000) 2 222 = 450355645856901936 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_2 : AffineCertificate (bridgeShape 75000) 2442 2 222 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_2 (by decide +kernel)

private theorem penalty_seed_first_3 : seedPenalty (bridgeShape 75000) 3 213 = 450593890303902488 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_3 : AffineCertificate (bridgeShape 75000) 2442 3 213 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_3 (by decide +kernel)

private theorem penalty_seed_first_4 : seedPenalty (bridgeShape 75000) 4 203 = 450959541134013534 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_4 : AffineCertificate (bridgeShape 75000) 2442 4 203 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_4 (by decide +kernel)

private theorem penalty_seed_first_5 : seedPenalty (bridgeShape 75000) 5 192 = 450764737728211335 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_5 : AffineCertificate (bridgeShape 75000) 2442 5 192 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_5 (by decide +kernel)

private theorem penalty_seed_first_6 : seedPenalty (bridgeShape 75000) 6 179 = 450556564176219083 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_6 : AffineCertificate (bridgeShape 75000) 2442 6 179 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_6 (by decide +kernel)

private theorem penalty_seed_first_7 : seedPenalty (bridgeShape 75000) 7 162 = 451278826247316867 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_7 : AffineCertificate (bridgeShape 75000) 2442 7 162 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_7 (by decide +kernel)

private theorem penalty_seed_first_8 : seedPenalty (bridgeShape 75000) 8 141 = 450895752182956885 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_8 : AffineCertificate (bridgeShape 75000) 2442 8 141 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_8 (by decide +kernel)

private theorem penalty_seed_first_9 : seedPenalty (bridgeShape 75000) 9 115 = 450553566144475648 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_9 : AffineCertificate (bridgeShape 75000) 2442 9 115 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_9 (by decide +kernel)

private theorem penalty_seed_first_10 : seedPenalty (bridgeShape 75000) 10 83 = 451366249117221169 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_10 : AffineCertificate (bridgeShape 75000) 2442 10 83 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_10 (by decide +kernel)

private theorem penalty_seed_first_11 : seedPenalty (bridgeShape 75000) 11 47 = 451183986148834150 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_11 : AffineCertificate (bridgeShape 75000) 2442 11 47 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_11 (by decide +kernel)

private theorem penalty_seed_first_12 : seedPenalty (bridgeShape 75000) 12 6 = 451306100048395745 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_12 : AffineCertificate (bridgeShape 75000) 2442 12 6 :=
  affine_of_moments (bridgeCount 75000) (bridgeGrade 75000) (bridgeIndex 75000)
    (bridgeFixed 75000) PoleReceipts.debit_2845_600_75000 penalty_seed_first_12 (by decide +kernel)

private theorem penalty_ordinate_second : seedPenalty (laterShape 66251) 6 0 = 3865730302121688 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_ordinate_second : AffineCertificate (laterShape 66251) 3555 6 0 :=
  affine_of_moments (laterCount 66251) (laterGrade 66251) (laterIndex 66251)
    (laterFixed 66251) PoleReceipts.debit_500_105_66251 penalty_ordinate_second (by decide +kernel)

private theorem penalty_seed_second_1 : seedPenalty (laterShape 6798) 1 109 = 21510899914254 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_second_1 : AffineCertificate (laterShape 6798) 3555 1 109 :=
  affine_of_moments (laterCount 6798) (laterGrade 6798) (laterIndex 6798)
    (laterFixed 6798) PoleReceipts.debit_500_105_6798 penalty_seed_second_1 (by decide +kernel)

private theorem penalty_seed_second_2 : seedPenalty (laterShape 6798) 2 104 = 21658533861900 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_second_2 : AffineCertificate (laterShape 6798) 3555 2 104 :=
  affine_of_moments (laterCount 6798) (laterGrade 6798) (laterIndex 6798)
    (laterFixed 6798) PoleReceipts.debit_500_105_6798 penalty_seed_second_2 (by decide +kernel)

private theorem penalty_seed_second_3 : seedPenalty (laterShape 6798) 3 100 = 21530138054700 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_second_3 : AffineCertificate (laterShape 6798) 3555 3 100 :=
  affine_of_moments (laterCount 6798) (laterGrade 6798) (laterIndex 6798)
    (laterFixed 6798) PoleReceipts.debit_500_105_6798 penalty_seed_second_3 (by decide +kernel)

private theorem penalty_seed_second_4 : seedPenalty (laterShape 6798) 4 95 = 21489154275120 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_second_4 : AffineCertificate (laterShape 6798) 3555 4 95 :=
  affine_of_moments (laterCount 6798) (laterGrade 6798) (laterIndex 6798)
    (laterFixed 6798) PoleReceipts.debit_500_105_6798 penalty_seed_second_4 (by decide +kernel)

private theorem penalty_seed_second_5 : seedPenalty (laterShape 6798) 5 88 = 21663568858932 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_second_5 : AffineCertificate (laterShape 6798) 3555 5 88 :=
  affine_of_moments (laterCount 6798) (laterGrade 6798) (laterIndex 6798)
    (laterFixed 6798) PoleReceipts.debit_500_105_6798 penalty_seed_second_5 (by decide +kernel)

private theorem penalty_ordinate_third : seedPenalty (laterShape 66251) 4 0 = 5824582858914930 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_ordinate_third : AffineCertificate (laterShape 66251) 8250 4 0 :=
  affine_of_moments (laterCount 66251) (laterGrade 66251) (laterIndex 66251)
    (laterFixed 66251) PoleReceipts.debit_500_105_66251 penalty_ordinate_third (by decide +kernel)

private theorem penalty_seed_third_1 : seedPenalty (laterShape 4860) 1 42 = 19997442624335 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_third_1 : AffineCertificate (laterShape 4860) 8250 1 42 :=
  affine_of_moments (laterCount 4860) (laterGrade 4860) (laterIndex 4860)
    (laterFixed 4860) PoleReceipts.debit_500_105_4860 penalty_seed_third_1 (by decide +kernel)

private theorem penalty_seed_third_2 : seedPenalty (laterShape 4860) 2 38 = 20260748989089 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_third_2 : AffineCertificate (laterShape 4860) 8250 2 38 :=
  affine_of_moments (laterCount 4860) (laterGrade 4860) (laterIndex 4860)
    (laterFixed 4860) PoleReceipts.debit_500_105_4860 penalty_seed_third_2 (by decide +kernel)

private theorem penalty_seed_third_3 : seedPenalty (laterShape 4860) 3 34 = 20093941820832 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_third_3 : AffineCertificate (laterShape 4860) 8250 3 34 :=
  affine_of_moments (laterCount 4860) (laterGrade 4860) (laterIndex 4860)
    (laterFixed 4860) PoleReceipts.debit_500_105_4860 penalty_seed_third_3 (by decide +kernel)

private theorem penalty_ordinate_fourth : seedPenalty (laterShape 66251) 3 0 = 7783455167980074 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_ordinate_fourth : AffineCertificate (laterShape 66251) 24000 3 0 :=
  affine_of_moments (laterCount 66251) (laterGrade 66251) (laterIndex 66251)
    (laterFixed 66251) PoleReceipts.debit_500_105_66251 penalty_ordinate_fourth (by decide +kernel)

private theorem penalty_seed_fourth_1 : seedPenalty (laterShape 3913) 1 29 = 14974109968545 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_fourth_1 : AffineCertificate (laterShape 3913) 24000 1 29 :=
  affine_of_moments (laterCount 3913) (laterGrade 3913) (laterIndex 3913)
    (laterFixed 3913) PoleReceipts.debit_500_105_3913 penalty_seed_fourth_1 (by decide +kernel)

private theorem penalty_seed_fourth_2 : seedPenalty (laterShape 3913) 2 26 = 15030069642775 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_fourth_2 : AffineCertificate (laterShape 3913) 24000 2 26 :=
  affine_of_moments (laterCount 3913) (laterGrade 3913) (laterIndex 3913)
    (laterFixed 3913) PoleReceipts.debit_500_105_3913 penalty_seed_fourth_2 (by decide +kernel)

private theorem ordinate_certificate (b : HeightBand) :
    AffineCertificate b.fullBank b.lower (b.ordinateCap+1) 0 := by
  cases b
  · exact affine_ordinate_first
  · exact affine_ordinate_second
  · exact affine_ordinate_third
  · exact affine_ordinate_fourth

private theorem seed_certificate (b : HeightBand) (e : ℕ)
    (he : 0 < e) (hcap : e ≤ b.ordinateCap) :
    AffineCertificate b.seedBank b.lower e (b.seedCap e + 1) := by
  cases b
  case first =>
    change e ≤ 12 at hcap
    interval_cases e
    · exact affine_seed_first_1
    · exact affine_seed_first_2
    · exact affine_seed_first_3
    · exact affine_seed_first_4
    · exact affine_seed_first_5
    · exact affine_seed_first_6
    · exact affine_seed_first_7
    · exact affine_seed_first_8
    · exact affine_seed_first_9
    · exact affine_seed_first_10
    · exact affine_seed_first_11
    · exact affine_seed_first_12
  case second =>
    change e ≤ 5 at hcap
    interval_cases e
    · exact affine_seed_second_1
    · exact affine_seed_second_2
    · exact affine_seed_second_3
    · exact affine_seed_second_4
    · exact affine_seed_second_5
  case third =>
    change e ≤ 3 at hcap
    interval_cases e
    · exact affine_seed_third_1
    · exact affine_seed_third_2
    · exact affine_seed_third_3
  case fourth =>
    change e ≤ 2 at hcap
    interval_cases e
    · exact affine_seed_fourth_1
    · exact affine_seed_fourth_2

/-- Every high-overhead height belongs to a real band, including both end points. -/
theorem exists_height_band {h : ℕ} (hlo : 2442 ≤ h) (hhi : h ≤ 32970) :
    ∃ b : HeightBand, b.lower ≤ h ∧ h ≤ b.upper := by
  by_cases h₁ : h ≤ 3554
  · exact ⟨.first, hlo, h₁⟩
  by_cases h₂ : h ≤ 8249
  · exact ⟨.second, by change 3555 ≤ h; omega, h₂⟩
  by_cases h₃ : h ≤ 23999
  · exact ⟨.third, by change 8250 ≤ h; omega, h₃⟩
  · exact ⟨.fourth, by change 24000 ≤ h; omega, hhi⟩

private theorem positive_lower (b : HeightBand) : 0 < b.lower := by cases b <;> decide
private theorem upper_lt_degree (b : HeightBand) : b.upper < 131071 := by cases b <;> decide

private theorem full_width (b : HeightBand) :
    b.fullBank.B * base b.lower ≤ top b.fullBank := by cases b <;> decide

private theorem seed_width (b : HeightBand) :
    b.seedBank.B * base b.lower ≤ top b.seedBank := by cases b <;> decide

/-- Uniform ordinate exclusion from the full terminal bank in any one real band. -/
theorem ordinate_bound (b : HeightBand) {h : ℕ} (hlo : b.lower ≤ h) (hhi : h ≤ b.upper)
    {f : Equation} (hf : f ≠ 0) (hm : TerminalMass b.fullBank h f) :
    f.natDegree ≤ b.ordinateCap := by
  have hh := (positive_lower b).trans_le hlo
  have hk := hhi.trans_lt (upper_lt_degree b)
  apply Nat.lt_succ_iff.mp
  exact ordinate_of_strict hf (Nat.sub_pos_of_lt hk) hm
    (strict_of_affine b.fullBank h b.lower (b.ordinateCap+1) 0 hh hlo hk.le
      (Nat.succ_pos _) (full_width b) (ordinate_certificate b))

/-- Uniform seed exclusion with the actual positive ordinate degree as its tariff row. -/
theorem seed_bound (b : HeightBand) {h : ℕ} (hlo : b.lower ≤ h) (hhi : h ≤ b.upper)
    {f : Equation} (hf : f ≠ 0) (he : 0 < f.natDegree) (hcap : f.natDegree ≤ b.ordinateCap)
    (hm : TerminalMass b.seedBank h f) : SeedBound f (b.seedCap f.natDegree) := by
  have hh := (positive_lower b).trans_le hlo
  have hk := hhi.trans_lt (upper_lt_degree b)
  exact seed_of_strict hf (Nat.sub_pos_of_lt hk) le_rfl hm
    (strict_of_affine b.seedBank h b.lower f.natDegree (b.seedCap f.natDegree+1) hh hlo hk.le
      he (seed_width b) (seed_certificate b _ he hcap))

/-- Both terminal bounds from the two nested mass banks, for arbitrary projected equations. -/
theorem terminal_bounds (b : HeightBand) {h : ℕ} (hlo : b.lower ≤ h) (hhi : h ≤ b.upper)
    {f : Equation} (hf : f ≠ 0) (he : 0 < f.natDegree)
    (hfull : TerminalMass b.fullBank h f) (hseed : TerminalMass b.seedBank h f) :
    f.natDegree ≤ b.ordinateCap ∧ SeedBound f (b.seedCap f.natDegree) := by
  have hd := ordinate_bound b hlo hhi hf hfull
  exact ⟨hd, seed_bound b hlo hhi hf he hd hseed⟩

end HighJoint6921
