import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

open scoped Classical BigOperators
open RCN095

set_option autoImplicit false

def lengthAverage (n w A : ℚ) : ℚ := n * w / A

def nodeAverage (n w A : ℚ) : ℚ := (n - w) / (A - w)

theorem shortened_product_average (n w A i : ℚ)
    (h0 : 0 ≤ i) (hiw : i ≤ w) (hwA : w < A) (hAn : A ≤ n) :
    (n - i) * (w - i) / (A - i) ≤ lengthAverage n w A := by
  unfold lengthAverage
  have hApos : 0 < A := by linarith
  have hAipos : 0 < A - i := by linarith
  have hn : 0 ≤ n := by linarith
  rw [div_le_div_iff₀ hAipos hApos]
  calc
    (n - i) * (w - i) * A = n * w * (A - i) -
        i * (n * (A - w) + A * (w - i)) := by ring
    _ ≤ _ := sub_le_self _ (mul_nonneg h0 (add_nonneg
      (mul_nonneg hn (sub_nonneg.mpr hwA.le))
      (mul_nonneg hApos.le (sub_nonneg.mpr hiw))))

theorem shortened_node_average (n w A i : ℚ)
    (hiw : i ≤ w) (hwA : w < A) (hAn : A ≤ n) :
    (n - i) / (A - i) ≤ nodeAverage n w A := by
  unfold nodeAverage
  have hAipos : 0 < A - i := by linarith
  have hAwpos : 0 < A - w := by linarith
  rw [div_le_div_iff₀ hAipos hAwpos]
  calc
    (n - i) * (A - w) = (n - w) * (A - i) - (w - i) * (n - A) := by ring
    _ ≤ _ := sub_le_self _ (mul_nonneg (sub_nonneg.mpr hiw) (sub_nonneg.mpr hAn))

theorem shortened_affine_average (n w A i slope center : ℚ)
    (h0 : 0 ≤ i) (hiw : i ≤ w) (hwA : w < A) (hAn : A ≤ n)
    (hslope : 0 ≤ slope) (hcenter : 0 ≤ center) :
    (n - i) * (center + slope * (w - i)) / (A - i) ≤
      slope * lengthAverage n w A + center * nodeAverage n w A := by
  calc
    _ = slope * ((n - i) * (w - i) / (A - i)) + center * ((n - i) / (A - i)) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (shortened_product_average n w A i h0 hiw hwA hAn) hslope)
      (mul_le_mul_of_nonneg_left (shortened_node_average n w A i hiw hwA hAn) hcenter)

theorem incidence_le_shortened_scaled {Seed Node : Type*}
    (relation : Seed → Node → Prop)
    (seeds : Finset Seed) (nodes identities : Finset Node)
    (A w scale slope center : ℕ)
    (hscale : 0 < scale) (hidentities : identities ⊆ nodes)
    (hshort : identities.card ≤ w) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hagreement : ∀ seed ∈ seeds, A ≤ (nodes.filter (relation seed)).card)
    (hfiber : ∀ node ∈ nodes \ identities,
      (seeds.filter (fun seed => relation seed node)).card * scale ≤
        center + slope * (w - identities.card)) :
    (seeds.card : ℚ) * scale ≤
      slope * lengthAverage nodes.card w A + center * nodeAverage nodes.card w A := by
  let cost := center + slope * (w - identities.card)
  have hinc := RCN173.incidence_after_exempt_nodes relation seeds nodes identities A (cost / scale)
    hidentities hagreement (fun node hn => (Nat.le_div_iff_mul_le hscale).mpr (hfiber node hn))
  have hnat : (seeds.card * scale) * (A - identities.card) ≤
      (nodes.card - identities.card) * cost := by
    calc
      _ = (seeds.card * (A - identities.card)) * scale := by ring
      _ ≤ ((nodes.card - identities.card) * (cost / scale)) * scale :=
        Nat.mul_le_mul_right _ hinc
      _ = (nodes.card - identities.card) * (cost / scale * scale) := Nat.mul_assoc _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  have hiA : identities.card ≤ A := hshort.trans hwA.le
  have hin : identities.card ≤ nodes.card := hiA.trans hAn
  have hrat : (seeds.card : ℚ) * scale * ((A : ℚ) - identities.card) ≤
      ((nodes.card : ℚ) - identities.card) *
        (center + slope * ((w : ℚ) - identities.card)) := by
    exact_mod_cast hnat
  have hpos : 0 < (A : ℚ) - identities.card := by
    exact sub_pos.mpr (by exact_mod_cast (hshort.trans_lt hwA))
  refine ((le_div_iff₀ hpos).mpr hrat).trans ?_
  apply shortened_affine_average
  · positivity
  · exact_mod_cast hshort
  · exact_mod_cast hwA
  · exact_mod_cast hAn
  · positivity
  · positivity

def ordinaryFlag (y t : ℕ) : FlagDegree := ⟨0, t - y, y⟩

theorem ordinary_mixed_sum_le {Component : Type*} [Fintype Component]
    (y t : Component → ℕ) (valueCap totalCap : ℕ) (q r : FlagDegree)
    (hyt : ∀ c, y c ≤ t c) (hcap : valueCap ≤ totalCap)
    (hy : (∑ c, y c) ≤ valueCap) (ht : (∑ c, t c) ≤ totalCap) :
    (∑ c, flagMixed (ordinaryFlag (y c) (t c)) q r) ≤ flagMixed (ordinaryFlag valueCap totalCap) q r := by
  have hpoint (c : Component) : t c - y c + y c = t c := Nat.sub_add_cancel (hyt c)
  apply RCN084.sum_flagMixed_le_of_cumulative
  · exact hy
  · simpa only [ordinaryFlag, hpoint, Nat.sub_add_cancel hcap] using ht
  · simpa only [ordinaryFlag, zero_add, hpoint, Nat.sub_add_cancel hcap] using ht

def averageDenominator (w A : ℕ) : ℕ := A * (A - w)

def averagedCutNumerator (n w A degree : ℕ) : ℕ :=
  2 * n * w * (degree - 1) * (A - w) + (n - w) * A

def cutFlag (center length y t : ℕ) : FlagDegree :=
  ordinaryFlag (center + length * (2 * (y - 1))) (center + length * (2 * (t - 1)))

theorem cutFlag_mixed (left right : FlagDegree) (center length y t : ℕ) :
    flagMixed left (cutFlag center length y t) right =
      length * flagMixed left (ordinaryFlag (2 * (y - 1)) (2 * (t - 1))) right +
        center * flagMixed left (ordinaryFlag 1 1) right := by
  have hdiff :
      (center + length * (2 * (t - 1))) - (center + length * (2 * (y - 1))) =
        length * (2 * (t - 1) - 2 * (y - 1)) := by
    rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib length]
  simp only [cutFlag, flagMixed, ordinaryFlag, hdiff]
  ring

theorem mixed_incidence_le_scaled {Seed Node : Type*}
    (relation : Seed → Node → Prop)
    (seeds : Finset Seed) (nodes identities : Finset Node)
    (left right : FlagDegree) (A w y t scale : ℕ)
    (hscale : 0 < scale) (hidentities : identities ⊆ nodes)
    (hshort : identities.card ≤ w) (hwA : w < A) (hAn : A ≤ nodes.card)
    (hagreement : ∀ seed ∈ seeds, A ≤ (nodes.filter (relation seed)).card)
    (hfiber : ∀ node ∈ nodes \ identities,
      (seeds.filter (fun seed => relation seed node)).card * scale ≤
        flagMixed left (cutFlag 1 (w - identities.card) y t) right) :
    seeds.card * scale * averageDenominator w A ≤
      flagMixed left
        (ordinaryFlag (averagedCutNumerator nodes.card w A y)
          (averagedCutNumerator nodes.card w A t)) right := by
  let slope := flagMixed left (ordinaryFlag (2 * (y - 1)) (2 * (t - 1))) right
  let center := flagMixed left (ordinaryFlag 1 1) right
  have h := incidence_le_shortened_scaled relation seeds nodes identities A w scale slope center
    hscale hidentities hshort hwA hAn hagreement (fun node hn => by
      simpa only [cutFlag_mixed, one_mul, Nat.add_comm, Nat.mul_comm, slope, center] using hfiber node hn)
  have hA : (A : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_le w |>.trans_lt hwA))
  have hAw : (A : ℚ) - w ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hwA))
  have hlength :
      lengthAverage nodes.card w A * (averageDenominator w A : ℚ) =
        (↑(nodes.card * w * (A - w)) : ℚ) := by
    unfold lengthAverage averageDenominator
    push_cast [Nat.cast_sub hwA.le]
    field_simp
  have hcenter :
      nodeAverage nodes.card w A * (averageDenominator w A : ℚ) =
        (↑((nodes.card - w) * A) : ℚ) := by
    unfold nodeAverage averageDenominator
    push_cast [Nat.cast_sub hwA.le, Nat.cast_sub (hwA.le.trans hAn)]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_right h (show (0 : ℚ) ≤ averageDenominator w A by positivity)
  rw [add_mul, mul_assoc (slope : ℚ), mul_assoc (center : ℚ), hlength, hcenter] at hscaled
  have hnat : seeds.card * scale * averageDenominator w A ≤
      slope * (nodes.card * w * (A - w)) + center * ((nodes.card - w) * A) := by
    exact_mod_cast hscaled
  have hcap (degree : ℕ) : averagedCutNumerator nodes.card w A degree =
      (nodes.card - w) * A + (nodes.card * w * (A - w)) * (2 * (degree - 1)) := by
    unfold averagedCutNumerator
    ring
  rw [hcap y, hcap t]
  change _ ≤ flagMixed left (cutFlag ((nodes.card - w) * A) (nodes.card * w * (A - w)) y t) right
  rw [cutFlag_mixed]
  simpa only [slope, center, Nat.mul_comm] using hnat

def ordinaryPrice (p n w A e y t : ℕ) : ℕ :=
  let denominator := averageDenominator w A
  let cutY := averagedCutNumerator n w A y
  let cutT := averagedCutNumerator n w A t
  flagMixed (ordinaryFlag y t) (ordinaryFlag cutY cutT)
      (ordinaryFlag cutY (cutT + (e + 1) * denominator)) / denominator ^ 2 +
    p * (2 * y + 2) * t + (e + 1) * (y + t)

def koalaCarrierShape (caseIndex : Fin 9) : ℕ × ℕ :=
  ![(19, 185), (15, 95), (8, 54), (6, 43), (5, 38), (4, 39),
    (4, 41), (4, 44), (2, 31)] caseIndex

theorem koala_ordinary_price_le (caseIndex : Fin 9) :
    ordinaryPrice 2130706433 262144 131071 181078 81066
      (koalaCarrierShape caseIndex).1 (koalaCarrierShape caseIndex).2 +
      10 * 2130706433 * (262144 + 1) ≤ 250000000000000000 := by
  fin_cases caseIndex <;> decide +kernel

end ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
