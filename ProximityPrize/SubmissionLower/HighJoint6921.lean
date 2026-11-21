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
  | .first => 2385
  | .second => 3555
  | .third => 8250
  | .fourth => 24000

def HeightBand.upper : HeightBand → ℕ
  | .first => 3554
  | .second => 8249
  | .third => 23999
  | .fourth => 33068

def HeightBand.ordinateCap : HeightBand → ℕ
  | .first => 14
  | .second => 5
  | .third => 3
  | .fourth => 2

def bridgeShape (U : ℕ) : Shape := ⟨3025, 4200, 890, U⟩
def laterShape (U : ℕ) : Shape := ⟨358, 500, 105, U⟩

def HeightBand.fullBank : HeightBand → Shape
  | .first => bridgeShape 84000
  | _ => laterShape 66251

def HeightBand.seedBank : HeightBand → Shape
  | .first => bridgeShape 84000
  | .second => laterShape 6798
  | .third => laterShape 4860
  | .fourth => laterShape 3913

/-- The tested seed ceiling for each positive actual ordinate degree. -/
def HeightBand.seedCap : HeightBand → ℕ → ℕ
  | .first, 1 => 209
  | .first, 2 => 203
  | .first, 3 => 196
  | .first, 4 => 189
  | .first, 5 => 182
  | .first, 6 => 173
  | .first, 7 => 163
  | .first, 8 => 151
  | .first, 9 => 137
  | .first, 10 => 119
  | .first, 11 => 98
  | .first, 12 => 74
  | .first, 13 => 46
  | .first, 14 => 16
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

private theorem bridgeCount (U : ℕ) : columnCount (bridgeShape U) = 3346596 := by
  change (∑ q ∈ Finset.range 4201, (min q 890 + 1)) = _
  exact (range_sum_eq (fun q => min q 890 + 1) 4201).trans (by decide +kernel)

private theorem bridgeGrade (U : ℕ) : gradeMoment (bridgeShape U) = 7742996415 := by
  change (∑ q ∈ Finset.range 4201, q*(min q 890+1)) = _
  exact (range_sum_eq (fun q => q*(min q 890+1)) 4201).trans (by decide +kernel)

private theorem bridgeIndex (U : ℕ) : indexMoment (bridgeShape U) = 1430289630 := by
  change (∑ q ∈ Finset.range 4201, (min q 890+1)*min q 890/2) = _
  exact (range_sum_eq (fun q => (min q 890+1)*min q 890/2) 4201).trans (by decide +kernel)

private theorem bridgeNodeSum :
    (∑ q ∈ Finset.range 4201, nodeCostAt (bridgeShape 0) q) = 3113939565 :=
  (range_sum_eq (nodeCostAt (bridgeShape 0)) 4201).trans (by decide +kernel)

private theorem bridgeFixed (U : ℕ) :
    fixedDebit (bridgeShape U) = triangle U * 816300573327360 := by
  change triangle U * 262144 *
    (∑ q ∈ Finset.range 4201, nodeCostAt (bridgeShape 0) q) = _
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

private theorem penalty_ordinate_first : seedPenalty (bridgeShape 84000) 15 0 = 1479295531955766480 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_ordinate_first : AffineCertificate (bridgeShape 84000) 2385 15 0 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_ordinate_first (by decide +kernel)

private theorem penalty_seed_first_1 : seedPenalty (bridgeShape 84000) 1 210 = 1526509035415663200 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_1 : AffineCertificate (bridgeShape 84000) 2385 1 210 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_1 (by decide +kernel)

private theorem penalty_seed_first_2 : seedPenalty (bridgeShape 84000) 2 204 = 1525893374906588952 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_2 : AffineCertificate (bridgeShape 84000) 2385 2 204 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_2 (by decide +kernel)

private theorem penalty_seed_first_3 : seedPenalty (bridgeShape 84000) 3 197 = 1529423705341780380 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_3 : AffineCertificate (bridgeShape 84000) 2385 3 197 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_3 (by decide +kernel)

private theorem penalty_seed_first_4 : seedPenalty (bridgeShape 84000) 4 190 = 1529325538877796660 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_4 : AffineCertificate (bridgeShape 84000) 2385 4 190 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_4 (by decide +kernel)

private theorem penalty_seed_first_5 : seedPenalty (bridgeShape 84000) 5 183 = 1524719185548409719 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_5 : AffineCertificate (bridgeShape 84000) 2385 5 183 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_5 (by decide +kernel)

private theorem penalty_seed_first_6 : seedPenalty (bridgeShape 84000) 6 174 = 1527821461399776444 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_6 : AffineCertificate (bridgeShape 84000) 2385 6 174 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_6 (by decide +kernel)

private theorem penalty_seed_first_7 : seedPenalty (bridgeShape 84000) 7 164 = 1528916123523417196 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_7 : AffineCertificate (bridgeShape 84000) 2385 7 164 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_7 (by decide +kernel)

private theorem penalty_seed_first_8 : seedPenalty (bridgeShape 84000) 8 152 = 1529733744686743148 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_8 : AffineCertificate (bridgeShape 84000) 2385 8 152 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_8 (by decide +kernel)

private theorem penalty_seed_first_9 : seedPenalty (bridgeShape 84000) 9 138 = 1525922929793202237 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_9 : AffineCertificate (bridgeShape 84000) 2385 9 138 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_9 (by decide +kernel)

private theorem penalty_seed_first_10 : seedPenalty (bridgeShape 84000) 10 120 = 1526951769775818645 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_10 : AffineCertificate (bridgeShape 84000) 2385 10 120 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_10 (by decide +kernel)

private theorem penalty_seed_first_11 : seedPenalty (bridgeShape 84000) 11 99 = 1526896174731879006 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_11 : AffineCertificate (bridgeShape 84000) 2385 11 99 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_11 (by decide +kernel)

private theorem penalty_seed_first_12 : seedPenalty (bridgeShape 84000) 12 75 = 1526219668780177800 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_12 : AffineCertificate (bridgeShape 84000) 2385 12 75 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_12 (by decide +kernel)

private theorem penalty_seed_first_13 : seedPenalty (bridgeShape 84000) 13 47 = 1529016331329853313 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_13 : AffineCertificate (bridgeShape 84000) 2385 13 47 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_13 (by decide +kernel)

private theorem penalty_seed_first_14 : seedPenalty (bridgeShape 84000) 14 17 = 1528044467398547062 := by
  unfold seedPenalty
  rw [range_sum_eq]
  decide +kernel

private theorem affine_seed_first_14 : AffineCertificate (bridgeShape 84000) 2385 14 17 :=
  affine_of_moments (bridgeCount 84000) (bridgeGrade 84000) (bridgeIndex 84000)
    (bridgeFixed 84000) PoleReceipts.debit_4200_890_84000 penalty_seed_first_14 (by decide +kernel)

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
    change e ≤ 14 at hcap
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
    · exact affine_seed_first_13
    · exact affine_seed_first_14
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
theorem exists_height_band {h : ℕ} (hlo : 2385 ≤ h) (hhi : h ≤ 33068) :
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
