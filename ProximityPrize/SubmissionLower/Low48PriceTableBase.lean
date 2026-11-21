import ProximityPrize.SubmissionLower.Low48PriceMonotone
import ProximityPrize.SubmissionLower.Low48PriceCaps

set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Low48PriceTableBase
open K1_13 (Shape InBox)
open Low48Price (physicalPrice physicalPriceOld)
open Low48PriceCaps (Band order allowance indexBudget)
open Low48PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

theorem oldRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h₁ : bl ≤ a.b) (h₂ : jl ≤ a.j) (h₃ : a.b ≤ bh) (h₄ : a.j ≤ jh)
    (h₅ : a.t = t) (ha : 3 * a.t ≤ a.j) (hl : 0 < l)
    (hlo : l ≤ order k ⟨bl,jl,0⟩)
    (hbill : physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k jl) :
    physicalPrice a (order k a) ≤ allowance top k a.j := by
  have hu : l ≤ order k a := hlo.trans (Low48PriceCaps.order_mono k h₁ h₂)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨h₃, h₄, h₅.le⟩
  have hallow : allowance top k jl ≤ allowance top k a.j :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ h₂)
  exact ((physicalPrice_anti a hl hu).trans (physicalPrice_le_old a l)).trans
    ((physical_mono hbox ha hi l).trans (hbill.trans hallow))

theorem point {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (hb : a.b = b) (hj : a.j = j) (ht : a.t = t) (hl : 0 < l)
    (hlo : l ≤ order k ⟨b,j,t⟩)
    (hbill : physicalPrice ⟨b,j,t⟩ l ≤ allowance top k j) :
    physicalPrice a (order k a) ≤ allowance top k a.j := by
  cases a
  subst_vars
  exact (physicalPrice_anti _ hl hlo).trans hbill
abbrev RectangleClaim (top : ℕ) (k : Band) (bl jl bh jh t : ℕ) : Prop :=
  ∀ {a : Shape}, bl ≤ a.b → jl ≤ a.j → a.b ≤ bh → a.j ≤ jh → a.t = t → 3 * a.t ≤ a.j →
    physicalPrice a (order k a) ≤ allowance top k a.j

abbrev PointClaim (top : ℕ) (k : Band) (b j t : ℕ) : Prop :=
  ∀ {a : Shape}, b ≤ a.b → j ≤ a.j → a.b ≤ b → a.j ≤ j → a.t = t →
    physicalPrice a (order k a) ≤ allowance top k a.j

/-- Apply a rectangle receipt after checking its closed numerical inequalities. -/
theorem rectangleBound {top : ℕ} {k : Band} {bl jl bh jh t l : ℕ} (hl : 0 < l)
    (hlo : l ≤ order k ⟨bl,jl,0⟩)
    (hbill : physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k jl)
    {a : Shape} (h₁ : bl ≤ a.b) (h₂ : jl ≤ a.j) (h₃ : a.b ≤ bh) (h₄ : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    physicalPrice a (order k a) ≤ allowance top k a.j :=
  oldRectangle h₁ h₂ h₃ h₄ ht ha hl hlo hbill

/-- Apply a singleton receipt with the same endpoint hypotheses as a rectangle. -/
theorem pointBound {top : ℕ} {k : Band} {b j t l : ℕ} (hl : 0 < l)
    (hlo : l ≤ order k ⟨b,j,t⟩)
    (hbill : physicalPrice ⟨b,j,t⟩ l ≤ allowance top k j)
    {a : Shape} (h₁ : b ≤ a.b) (h₂ : j ≤ a.j) (h₃ : a.b ≤ b) (h₄ : a.j ≤ j)
    (ht : a.t = t) :
    physicalPrice a (order k a) ≤ allowance top k a.j :=
  point (Nat.le_antisymm h₃ h₁) (Nat.le_antisymm h₄ h₂) ht hl hlo hbill

end Low48PriceTableBase
