import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped BigOperators

def resultantCharge (p : ℕ) (f helper : Rectangle) : ℕ :=
  f.value * helper.first + helper.value * f.first +
    p * (f.value * helper.second + helper.value * f.second)

theorem card_biUnion_le_resultantCharge {I S : Type*} [DecidableEq S]
    (p : ℕ) (families : Finset I) (points : I → Finset S)
    (factor : I → Rectangle) (aggregate helper : Rectangle)
    (hcount : ∀ i ∈ families, (points i).card ≤ resultantCharge p (factor i) helper)
    (hy : (∑ i ∈ families, (factor i).value) ≤ aggregate.value)
    (hb : (∑ i ∈ families, (factor i).first) ≤ aggregate.first)
    (hc : (∑ i ∈ families, (factor i).second) ≤ aggregate.second) :
    (families.biUnion points).card ≤ resultantCharge p aggregate helper := by
  calc
    _ ≤ ∑ i ∈ families, (points i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ families, resultantCharge p (factor i) helper := Finset.sum_le_sum hcount
    _ ≤ _ := by
      simp only [resultantCharge, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hy) (Nat.mul_le_mul_left _ hb))
        (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ hy)
          (Nat.mul_le_mul_left _ hc)))

private theorem mixedDegree_linear (f g h : Rectangle) :
    mixedDegree f g h =
      f.value * (g.first*h.second + g.second*h.first) +
      f.first * (g.value*h.second + h.value*g.second) +
      f.second * (g.value*h.first + h.value*g.first) := by
  unfold mixedDegree
  ring

theorem card_biUnion_le_mixedDegree {I S : Type*} [DecidableEq S]
    (families : Finset I) (points : I → Finset S)
    (factor : I → Rectangle) (aggregate tail1 tail2 : Rectangle)
    (hcount : ∀ i ∈ families, (points i).card ≤ mixedDegree (factor i) tail1 tail2)
    (hy : (∑ i ∈ families, (factor i).value) ≤ aggregate.value)
    (hb : (∑ i ∈ families, (factor i).first) ≤ aggregate.first)
    (hc : (∑ i ∈ families, (factor i).second) ≤ aggregate.second) :
    (families.biUnion points).card ≤ mixedDegree aggregate tail1 tail2 := by
  calc
    _ ≤ ∑ i ∈ families, (points i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ families, mixedDegree (factor i) tail1 tail2 := Finset.sum_le_sum hcount
    _ ≤ _ := by
      simp only [mixedDegree_linear, Finset.sum_add_distrib, ← Finset.sum_mul]
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hy) (Nat.mul_le_mul_right _ hb))
        (Nat.mul_le_mul_right _ hc)

def modulus : ℕ := 2130706433

def primaryBox : Rectangle := ⟨179,3800,3800⟩
def roomBox : Rectangle := ⟨1451,32586,32586⟩
def remainingBox : Rectangle := ⟨45,1018,1018⟩
def adaptiveBox : Rectangle := ⟨6975,133094,133094⟩

theorem room_digit_lt_modulus :
    primaryBox.value * roomBox.first + roomBox.value * primaryBox.first < modulus := by
  decide +kernel

theorem adaptive_digit_lt_modulus :
    remainingBox.value * adaptiveBox.first + adaptiveBox.value * remainingBox.first < modulus := by
  decide +kernel

def invariantSurfaceBudget : ℕ := 400000000000000

def excludedBudget : ℕ :=
  (2 * primaryBox.value + 2) *
    (primaryBox.first + modulus * primaryBox.second) + 4 * modulus * (10000 + 1) + 10^14

theorem virtual_total_budget :
    resultantCharge modulus primaryBox roomBox +
    resultantCharge modulus remainingBox adaptiveBox +
    215212585876172700 + invariantSurfaceBudget + excludedBudget = 270779581434104148 := by decide +kernel


theorem virtual_budget_le_retained_budget :
    (270779581434104148 : ℕ) ≤ 274566834571012320 := by decide +kernel


end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
