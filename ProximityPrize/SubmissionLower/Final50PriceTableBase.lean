import ProximityPrize.SubmissionLower.Final50PriceMonotone
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option maxHeartbeats 4000000
namespace Final50PriceTableBase
open K1_13 (Shape InBox)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance activeCap)
open Final50PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

abbrev OldReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k jl

abbrev PointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ physicalPrice ⟨b,j,t⟩ l (activeCap k) ≤ allowance top k j

theorem oldRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : OldReceipt top k bl jl bh jh t l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    physicalPrice a (order k a) (activeCap k) ≤ allowance top k a.j := by
  obtain ⟨hl,hlo,hbill⟩ := h
  have hu : l ≤ order k a := hlo.trans (Final50PriceCaps.order_mono k hb hj)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨hb', hj', ht.le⟩
  have hallow : allowance top k jl ≤ allowance top k a.j :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hj)
  exact ((physicalPrice_anti a _ hl hu).trans (physicalPrice_le_old a l _)).trans
    ((physical_mono hbox ha hi l).trans (hbill.trans hallow))

theorem point {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h : PointReceipt top k b j t l) (hb : a.b = b) (hj : a.j = j) (ht : a.t = t)
    (ha : 3 * a.t ≤ a.j) :
    physicalPrice a (order k a) (activeCap k) ≤ allowance top k a.j := by
  obtain ⟨hl, hlo, hbill⟩ := h
  cases a
  subst_vars
  exact (physicalPrice_anti _ _ hl hlo).trans hbill
open Final50SharedPrice (Rate RateFits)

def Covered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  physicalPrice a (order k a) (activeCap k) ≤ allowance top k a.j ∨
  ∃ u l, k = .empty ∧ 0 < l ∧ l ≤ order k a ∧ RateFits a u ∧
    Final50SharedPrice.price a l (activeCap k) u ≤ allowance top k a.j

abbrev SharedReceipt (t b j l : ℕ) (u : Rate) : Prop :=
  0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ RateFits ⟨b,j,t⟩ u ∧
    Final50SharedPrice.price ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty j

theorem sharedPoint {a : Shape} {b j t l : ℕ} {u : Rate}
    (h : SharedReceipt t b j l u) (hb : a.b = b) (hj : a.j = j) (ht : a.t = t) :
    Covered t .empty a := by
  cases a
  subst_vars
  exact Or.inr ⟨u,l,rfl,h⟩

theorem covered_mono {k : Band} {a : Shape} {top next : ℕ}
    (h : Covered top k a) (hm : top ≤ next) (hn : next ≤ 14) : Covered next k a := by
  rcases h with h | ⟨u,l,he,hl,ho,hu,hp⟩
  · exact Or.inl (h.trans (Final50PriceCaps.allowance_mono k hm hn))
  · exact Or.inr ⟨u,l,he,hl,ho,hu,hp.trans (Final50PriceCaps.allowance_mono k hm hn)⟩

theorem coveredPoint {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h : PointReceipt top k b j t l) (hb : a.b=b) (hj : a.j=j) (ht : a.t=t)
    (ha : 3*a.t ≤ a.j) : Covered top k a := Or.inl (point h hb hj ht ha)

theorem coveredRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : OldReceipt top k bl jl bh jh t l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3*a.t ≤ a.j) : Covered top k a :=
  Or.inl (oldRectangle h hb hj hb' hj' ht ha)
end Final50PriceTableBase
