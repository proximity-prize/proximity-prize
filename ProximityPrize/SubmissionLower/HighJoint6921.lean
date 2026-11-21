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
  | .first => 2472
  | .second => 3555
  | .third => 8250
  | .fourth => 24000

def HeightBand.upper : HeightBand → ℕ
  | .first => 3554
  | .second => 8249
  | .third => 23999
  | .fourth => 32950

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
  | .first, 1 => 243
  | .first, 2 => 235
  | .first, 3 => 226
  | .first, 4 => 216
  | .first, 5 => 206
  | .first, 6 => 193
  | .first, 7 => 178
  | .first, 8 => 159
  | .first, 9 => 135
  | .first, 10 => 106
  | .first, 11 => 72
  | .first, 12 => 34
  | .second, 1 => 136
  | .second, 2 => 132
  | .second, 3 => 127
  | .second, 4 => 123
  | .second, 5 => 117
  | .third, 1 => 49
  | .third, 2 => 46
  | .third, 3 => 42
  | .fourth, 1 => 35
  | .fourth, 2 => 32
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

private theorem bridgePoleSum :
    (∑ q ∈ Finset.range 2846, poleCostAt (bridgeShape 0) q) = 4523988852695 :=
  (range_sum_eq (poleCostAt (bridgeShape 0)) 2846).trans (by decide +kernel)

private theorem bridgeFixed (U : ℕ) :
    fixedDebit (bridgeShape U) = triangle U * 252688328556544 := by
  change triangle U * 262144 *
    (∑ q ∈ Finset.range 2846, nodeCostAt (bridgeShape 0) q) = _
  rw [bridgeNodeSum, Nat.mul_assoc]

private theorem bridgeLinear (U : ℕ) :
    linearDebit (bridgeShape U) = (U+1)*9047977705390 := by
  change 2 * (U+1) *
    (∑ q ∈ Finset.range 2846, poleCostAt (bridgeShape 0) q) = _
  rw [bridgePoleSum, Nat.mul_comm 2, Nat.mul_assoc]

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

private theorem laterPoleSum :
    (∑ q ∈ Finset.range 501, poleCostAt (laterShape 0) q) = 4343593800 :=
  (range_sum_eq (poleCostAt (laterShape 0)) 501).trans (by decide +kernel)

private theorem laterFixed (U : ℕ) :
    fixedDebit (laterShape U) = triangle U * 1365980217344 := by
  change triangle U * 262144 *
    (∑ q ∈ Finset.range 501, nodeCostAt (laterShape 0) q) = _
  rw [laterNodeSum, Nat.mul_assoc]

private theorem laterLinear (U : ℕ) :
    linearDebit (laterShape U) = (U+1)*8687187600 := by
  change 2 * (U+1) *
    (∑ q ∈ Finset.range 501, poleCostAt (laterShape 0) q) = _
  rw [laterPoleSum, Nat.mul_comm 2, Nat.mul_assoc]

private theorem ordinate_certificate (b : HeightBand) :
    AffineCertificate b.fullBank b.lower (b.ordinateCap+1) 0 := by
  cases b
  all_goals
    unfold AffineCertificate affineCost affineSlope affineValue ordinatePenalty
    simp only [HeightBand.lower, HeightBand.ordinateCap, HeightBand.fullBank,
      bridgeCount, bridgeGrade, bridgeIndex, bridgeFixed, bridgeLinear,
      laterCount, laterGrade, laterIndex, laterFixed, laterLinear, seedPenalty, range_sum_eq]
    decide +kernel

private theorem seed_certificate (b : HeightBand) (e : ℕ)
    (he : 0 < e) (hcap : e ≤ b.ordinateCap) :
    AffineCertificate b.seedBank b.lower e (b.seedCap e + 1) := by
  cases b <;> simp only [HeightBand.ordinateCap] at hcap <;> interval_cases e
  all_goals
    unfold AffineCertificate affineCost affineSlope affineValue ordinatePenalty
    simp only [HeightBand.lower, HeightBand.seedCap, HeightBand.seedBank,
      bridgeCount, bridgeGrade, bridgeIndex, bridgeFixed, bridgeLinear,
      laterCount, laterGrade, laterIndex, laterFixed, laterLinear, seedPenalty, range_sum_eq]
    decide +kernel

/-- Every high-overhead height belongs to a real band, including both end points. -/
theorem exists_height_band {h : ℕ} (hlo : 2472 ≤ h) (hhi : h ≤ 32950) :
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
