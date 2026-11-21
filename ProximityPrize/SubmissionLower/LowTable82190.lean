import ProximityPrize.SubmissionLower.LowPhysical82190

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace LowTable82190
open LowCaps82190 (Tier Band start order allowance box)
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open LowPriceData82190 (physicalPrice)

private theorem rectangle {tier : Tier} {k : Band} {a : Shape} {bl jl bh jh th l : ℕ}
    (hlo : bl ≤ a.b) (hj : jl ≤ a.j) (hb : a.b ≤ bh) (hj' : a.j ≤ jh) (ht : a.t ≤ th)
    (hfit : 3*a.t ≤ a.j) (hp : 3*th ≤ jh) (hpos : 0 < l) (horder : l ≤ order k ⟨bl,jl,0⟩)
    (hprice : physicalPrice ⟨bh,jh,th⟩ l ≤ allowance tier k jl) :
    physicalPrice a (order k a) ≤ allowance tier k a.j := by
  have ho := horder.trans (LowCaps82190.order_mono k (x := ⟨bl,jl,0⟩) (y := a) hlo hj)
  exact ((LowPhysical82190.physicalPrice_anti a hpos ho).trans
    (LowPhysical82190.physical_mono (y := ⟨bh,jh,th⟩) ⟨hb,hj',ht⟩ hfit hp l)).trans
    (hprice.trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hj)))

private theorem r0_0_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 3) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_2 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 31) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_4 {a : Shape} (h₁ : 32 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_5 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 3) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_6 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 9) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_7 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 16) (h₄ : a.j ≤ 7) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_8 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 16) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_9 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 31) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 3) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_10 {a : Shape} (h₁ : 32 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 5) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_11 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 10) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_12 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 14) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 11) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_13 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 14) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 21) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_14 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 62) (h₄ : a.j ≤ 25) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 23) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_15 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 20) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 27) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_16 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 25) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 31) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_17 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 26 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 31) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_18 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 26 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 31) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 39) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_19 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 32 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 46) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_20 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 37) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_21 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 43) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 41) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_22 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 45) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_23 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 48) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_24 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 44) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_25 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_26 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 49) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_27 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 49) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_28 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_29 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_0_30 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j :=
  rectangle (l := 51) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price0_0 (a : Shape) (ha : Valid a) (hc : InBox ((start .empty).plus a) (box .small)) :
    physicalPrice a (order .empty a) ≤ allowance .small .empty a.j := by
  change 0 + a.b ≤ 120 ∧ 0 + a.j ≤ 48 ∧ 0 + a.t ≤ 8 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 3
  · apply r0_0_0 <;> omega
  by_cases j1 : a.j ≤ 4
  · by_cases b0 : a.b ≤ 61
    · apply r0_0_1 <;> omega
    apply r0_0_2 <;> omega
  by_cases j2 : a.j ≤ 5
  · by_cases b0 : a.b ≤ 31
    · apply r0_0_3 <;> omega
    by_cases b1 : a.b ≤ 61
    · apply r0_0_4 <;> omega
    apply r0_0_5 <;> omega
  by_cases j3 : a.j ≤ 7
  · by_cases b0 : a.b ≤ 9
    · apply r0_0_6 <;> omega
    by_cases b1 : a.b ≤ 16
    · apply r0_0_7 <;> omega
    by_cases b2 : a.b ≤ 31
    · apply r0_0_9 <;> omega
    by_cases b3 : a.b ≤ 61
    · apply r0_0_10 <;> omega
    apply r0_0_11 <;> omega
  by_cases j4 : a.j ≤ 8
  · by_cases b0 : a.b ≤ 9
    · apply r0_0_6 <;> omega
    by_cases b1 : a.b ≤ 16
    · apply r0_0_8 <;> omega
    by_cases b2 : a.b ≤ 31
    · apply r0_0_9 <;> omega
    by_cases b3 : a.b ≤ 61
    · apply r0_0_10 <;> omega
    apply r0_0_11 <;> omega
  by_cases j5 : a.j ≤ 14
  · by_cases b0 : a.b ≤ 61
    · apply r0_0_12 <;> omega
    apply r0_0_13 <;> omega
  by_cases j6 : a.j ≤ 20
  · by_cases b0 : a.b ≤ 62
    · apply r0_0_14 <;> omega
    apply r0_0_15 <;> omega
  by_cases j7 : a.j ≤ 25
  · by_cases b0 : a.b ≤ 62
    · apply r0_0_14 <;> omega
    apply r0_0_16 <;> omega
  by_cases j8 : a.j ≤ 31
  · by_cases b0 : a.b ≤ 64
    · apply r0_0_17 <;> omega
    apply r0_0_18 <;> omega
  by_cases j9 : a.j ≤ 37
  · by_cases b0 : a.b ≤ 64
    · apply r0_0_17 <;> omega
    apply r0_0_19 <;> omega
  by_cases j10 : a.j ≤ 40
  · by_cases b0 : a.b ≤ 66
    · apply r0_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r0_0_21 <;> omega
    apply r0_0_22 <;> omega
  by_cases j11 : a.j ≤ 43
  · by_cases b0 : a.b ≤ 66
    · apply r0_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r0_0_21 <;> omega
    apply r0_0_23 <;> omega
  by_cases j12 : a.j ≤ 45
  · by_cases b0 : a.b ≤ 66
    · apply r0_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r0_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r0_0_25 <;> omega
    apply r0_0_26 <;> omega
  by_cases j13 : a.j ≤ 46
  · by_cases b0 : a.b ≤ 66
    · apply r0_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r0_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r0_0_25 <;> omega
    apply r0_0_27 <;> omega
  by_cases j14 : a.j ≤ 47
  · by_cases b0 : a.b ≤ 66
    · apply r0_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r0_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r0_0_25 <;> omega
    by_cases b3 : a.b ≤ 114
    · apply r0_0_28 <;> omega
    apply r0_0_29 <;> omega
  by_cases b0 : a.b ≤ 66
  · apply r0_0_20 <;> omega
  by_cases b1 : a.b ≤ 93
  · apply r0_0_24 <;> omega
  by_cases b2 : a.b ≤ 107
  · apply r0_0_25 <;> omega
  by_cases b3 : a.b ≤ 114
  · apply r0_0_28 <;> omega
  apply r0_0_30 <;> omega

private theorem r0_1_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 3) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 60) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_2 {a : Shape} (h₁ : 61 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 4) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_4 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 10) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_5 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 13) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 20) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_6 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 19) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 28) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_7 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 20 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 24) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 32) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_8 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 56) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_9 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 36) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_10 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 40) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 51) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_1_11 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j :=
  rectangle (l := 56) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price0_1 (a : Shape) (ha : Valid a) (hc : InBox ((start .one).plus a) (box .small)) :
    physicalPrice a (order .one a) ≤ allowance .small .one a.j := by
  change 1 + a.b ≤ 120 ∧ 3 + a.j ≤ 48 ∧ 1 + a.t ≤ 8 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 3
  · apply r0_1_0 <;> omega
  by_cases j1 : a.j ≤ 4
  · by_cases b0 : a.b ≤ 60
    · apply r0_1_1 <;> omega
    apply r0_1_2 <;> omega
  by_cases j2 : a.j ≤ 5
  · apply r0_1_3 <;> omega
  by_cases j3 : a.j ≤ 8
  · apply r0_1_4 <;> omega
  by_cases j4 : a.j ≤ 13
  · apply r0_1_5 <;> omega
  by_cases j5 : a.j ≤ 19
  · apply r0_1_6 <;> omega
  by_cases j6 : a.j ≤ 24
  · apply r0_1_7 <;> omega
  by_cases j7 : a.j ≤ 35
  · apply r0_1_8 <;> omega
  by_cases j8 : a.j ≤ 40
  · by_cases b0 : a.b ≤ 65
    · apply r0_1_9 <;> omega
    apply r0_1_10 <;> omega
  by_cases b0 : a.b ≤ 65
  · apply r0_1_9 <;> omega
  apply r0_1_11 <;> omega

private theorem r0_2_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 7) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 23) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_1 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 12) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 29) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_2 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 22) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 65) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_3 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 23 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 32) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 80) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_4 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 42) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 53) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 74) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r0_2_6 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 42) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j :=
  rectangle (l := 83) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price0_2 (a : Shape) (ha : Valid a) (hc : InBox ((start .two).plus a) (box .small)) :
    physicalPrice a (order .two a) ≤ allowance .small .two a.j := by
  change 2 + a.b ≤ 120 ∧ 6 + a.j ≤ 48 ∧ 2 + a.t ≤ 8 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 7
  · apply r0_2_0 <;> omega
  by_cases j1 : a.j ≤ 12
  · apply r0_2_1 <;> omega
  by_cases j2 : a.j ≤ 22
  · apply r0_2_2 <;> omega
  by_cases j3 : a.j ≤ 32
  · apply r0_2_3 <;> omega
  by_cases j4 : a.j ≤ 37
  · by_cases b0 : a.b ≤ 64
    · apply r0_2_4 <;> omega
    apply r0_2_5 <;> omega
  by_cases b0 : a.b ≤ 64
  · apply r0_2_4 <;> omega
  apply r0_2_6 <;> omega

private theorem r1_0_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 3) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_2 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 31) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_4 {a : Shape} (h₁ : 32 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_5 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 3) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_6 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 9) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_7 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 16) (h₄ : a.j ≤ 7) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_8 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 16) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_9 {a : Shape} (h₁ : 17 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 31) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 3) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_10 {a : Shape} (h₁ : 32 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 5) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_11 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 9) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_12 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 14) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 11) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_13 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 14) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 21) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_14 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 62) (h₄ : a.j ≤ 25) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 23) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_15 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 20) (h₅ : a.t ≤ 6) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 26) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_16 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 25) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 30) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_17 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 26 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 31) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_18 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 26 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 31) (h₅ : a.t ≤ 10) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 38) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_19 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 32 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 45) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_20 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 38) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_21 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 43) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 41) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_22 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 44) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_23 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 48) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_24 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 44) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_25 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 46) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 46) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_26 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 49) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_27 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 49) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_28 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 47) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_29 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_30 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 47 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 47) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_0_31 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 48 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 48) (h₅ : a.t ≤ 12) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j :=
  rectangle (l := 51) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price1_0 (a : Shape) (ha : Valid a) (hc : InBox ((start .empty).plus a) (box .large)) :
    physicalPrice a (order .empty a) ≤ allowance .large .empty a.j := by
  change 0 + a.b ≤ 120 ∧ 0 + a.j ≤ 48 ∧ 0 + a.t ≤ 12 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 3
  · apply r1_0_0 <;> omega
  by_cases j1 : a.j ≤ 4
  · by_cases b0 : a.b ≤ 61
    · apply r1_0_1 <;> omega
    apply r1_0_2 <;> omega
  by_cases j2 : a.j ≤ 5
  · by_cases b0 : a.b ≤ 31
    · apply r1_0_3 <;> omega
    by_cases b1 : a.b ≤ 61
    · apply r1_0_4 <;> omega
    apply r1_0_5 <;> omega
  by_cases j3 : a.j ≤ 7
  · by_cases b0 : a.b ≤ 9
    · apply r1_0_6 <;> omega
    by_cases b1 : a.b ≤ 16
    · apply r1_0_7 <;> omega
    by_cases b2 : a.b ≤ 31
    · apply r1_0_9 <;> omega
    by_cases b3 : a.b ≤ 61
    · apply r1_0_10 <;> omega
    apply r1_0_11 <;> omega
  by_cases j4 : a.j ≤ 8
  · by_cases b0 : a.b ≤ 9
    · apply r1_0_6 <;> omega
    by_cases b1 : a.b ≤ 16
    · apply r1_0_8 <;> omega
    by_cases b2 : a.b ≤ 31
    · apply r1_0_9 <;> omega
    by_cases b3 : a.b ≤ 61
    · apply r1_0_10 <;> omega
    apply r1_0_11 <;> omega
  by_cases j5 : a.j ≤ 14
  · by_cases b0 : a.b ≤ 61
    · apply r1_0_12 <;> omega
    apply r1_0_13 <;> omega
  by_cases j6 : a.j ≤ 20
  · by_cases b0 : a.b ≤ 62
    · apply r1_0_14 <;> omega
    apply r1_0_15 <;> omega
  by_cases j7 : a.j ≤ 25
  · by_cases b0 : a.b ≤ 62
    · apply r1_0_14 <;> omega
    apply r1_0_16 <;> omega
  by_cases j8 : a.j ≤ 31
  · by_cases b0 : a.b ≤ 64
    · apply r1_0_17 <;> omega
    apply r1_0_18 <;> omega
  by_cases j9 : a.j ≤ 37
  · by_cases b0 : a.b ≤ 64
    · apply r1_0_17 <;> omega
    apply r1_0_19 <;> omega
  by_cases j10 : a.j ≤ 40
  · by_cases b0 : a.b ≤ 66
    · apply r1_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r1_0_21 <;> omega
    apply r1_0_22 <;> omega
  by_cases j11 : a.j ≤ 43
  · by_cases b0 : a.b ≤ 66
    · apply r1_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r1_0_21 <;> omega
    apply r1_0_23 <;> omega
  by_cases j12 : a.j ≤ 45
  · by_cases b0 : a.b ≤ 66
    · apply r1_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r1_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r1_0_25 <;> omega
    apply r1_0_26 <;> omega
  by_cases j13 : a.j ≤ 46
  · by_cases b0 : a.b ≤ 66
    · apply r1_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r1_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r1_0_25 <;> omega
    apply r1_0_27 <;> omega
  by_cases j14 : a.j ≤ 47
  · by_cases b0 : a.b ≤ 66
    · apply r1_0_20 <;> omega
    by_cases b1 : a.b ≤ 93
    · apply r1_0_24 <;> omega
    by_cases b2 : a.b ≤ 107
    · apply r1_0_28 <;> omega
    by_cases b3 : a.b ≤ 114
    · apply r1_0_29 <;> omega
    apply r1_0_30 <;> omega
  by_cases b0 : a.b ≤ 66
  · apply r1_0_20 <;> omega
  by_cases b1 : a.b ≤ 93
  · apply r1_0_24 <;> omega
  by_cases b2 : a.b ≤ 107
  · apply r1_0_28 <;> omega
  by_cases b3 : a.b ≤ 114
  · apply r1_0_29 <;> omega
  apply r1_0_31 <;> omega

private theorem r1_1_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 3) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 60) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 1) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_2 {a : Shape} (h₁ : 61 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 4) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 2) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 5) (h₅ : a.t ≤ 1) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 3) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_4 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 8) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 10) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_5 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 13) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 19) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_6 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 24) (h₅ : a.t ≤ 8) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 45) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_7 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35) (h₅ : a.t ≤ 11) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 55) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_8 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 11) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 37) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_9 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 40) (h₅ : a.t ≤ 11) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 50) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1_10 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 45) (h₅ : a.t ≤ 11) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j :=
  rectangle (l := 56) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price1_1 (a : Shape) (ha : Valid a) (hc : InBox ((start .one).plus a) (box .large)) :
    physicalPrice a (order .one a) ≤ allowance .large .one a.j := by
  change 1 + a.b ≤ 120 ∧ 3 + a.j ≤ 48 ∧ 1 + a.t ≤ 12 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 3
  · apply r1_1_0 <;> omega
  by_cases j1 : a.j ≤ 4
  · by_cases b0 : a.b ≤ 60
    · apply r1_1_1 <;> omega
    apply r1_1_2 <;> omega
  by_cases j2 : a.j ≤ 5
  · apply r1_1_3 <;> omega
  by_cases j3 : a.j ≤ 8
  · apply r1_1_4 <;> omega
  by_cases j4 : a.j ≤ 13
  · apply r1_1_5 <;> omega
  by_cases j5 : a.j ≤ 24
  · apply r1_1_6 <;> omega
  by_cases j6 : a.j ≤ 35
  · apply r1_1_7 <;> omega
  by_cases j7 : a.j ≤ 40
  · by_cases b0 : a.b ≤ 65
    · apply r1_1_8 <;> omega
    apply r1_1_9 <;> omega
  by_cases b0 : a.b ≤ 65
  · apply r1_1_8 <;> omega
  apply r1_1_10 <;> omega

private theorem r1_2_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 7) (h₅ : a.t ≤ 2) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 22) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_1 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 8 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 12) (h₅ : a.t ≤ 4) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 28) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_2 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 22) (h₅ : a.t ≤ 7) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 62) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_3 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 23 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 32) (h₅ : a.t ≤ 10) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 77) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_4 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 42) (h₅ : a.t ≤ 10) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 53) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 37) (h₅ : a.t ≤ 10) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 72) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2_6 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 42) (h₅ : a.t ≤ 10) (h₆ : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j :=
  rectangle (l := 81) h₁ h₂ h₃ h₄ h₅ h₆ (by decide) (by decide) (by decide +kernel) (by decide +kernel)

private theorem price1_2 (a : Shape) (ha : Valid a) (hc : InBox ((start .two).plus a) (box .large)) :
    physicalPrice a (order .two a) ≤ allowance .large .two a.j := by
  change 2 + a.b ≤ 120 ∧ 6 + a.j ≤ 48 ∧ 2 + a.t ≤ 12 at hc
  obtain ⟨h₁,h₂,h₃⟩ := hc
  obtain ⟨ht,hjt,hjb⟩ := ha
  by_cases j0 : a.j ≤ 7
  · apply r1_2_0 <;> omega
  by_cases j1 : a.j ≤ 12
  · apply r1_2_1 <;> omega
  by_cases j2 : a.j ≤ 22
  · apply r1_2_2 <;> omega
  by_cases j3 : a.j ≤ 32
  · apply r1_2_3 <;> omega
  by_cases j4 : a.j ≤ 37
  · by_cases b0 : a.b ≤ 64
    · apply r1_2_4 <;> omega
    apply r1_2_5 <;> omega
  by_cases b0 : a.b ≤ 64
  · apply r1_2_4 <;> omega
  apply r1_2_6 <;> omega

theorem price (tier : Tier) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (box tier)) :
    physicalPrice a (order k a) ≤ allowance tier k a.j := by
  cases tier <;> cases k
  · exact price0_0 a ha hc
  · exact price0_1 a ha hc
  · exact price0_2 a ha hc
  · exact price1_0 a ha hc
  · exact price1_1 a ha hc
  · exact price1_2 a ha hc
#print axioms price
end LowTable82190
