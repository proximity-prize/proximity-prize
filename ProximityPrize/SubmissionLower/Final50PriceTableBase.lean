import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaWeightedRate
import ProximityPrize.SubmissionLower.Final50PriceMonotone
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option maxHeartbeats 4000000
namespace Final50PriceTableBase
open K1_13 (Shape InBox)
open KoalaRetainedCut (contractedPrice)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance activeCap start)
open Final50PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

theorem contracted_le (x h : Shape) (l K : ℕ) :
    contractedPrice x h l K ≤ physicalPrice x l K := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl

abbrev OldReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k bl jl t

abbrev PointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ contractedPrice ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance top k b j t

theorem oldRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : OldReceipt top k bl jl bh jh t l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) := by
  obtain ⟨hl,hlo,hbill⟩ := h
  have hu : l ≤ order k a := hlo.trans (Final50PriceCaps.order_mono k hb hj)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨hb', hj', ht.le⟩
  have hallow : allowance top k bl jl t ≤ allowance top k a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Final50PriceCaps.weight_mono k hb hj ht.ge))
  refine ⟨l,hl,hu,?_⟩
  exact ((contracted_le a (start k) l (activeCap k)).trans (physicalPrice_le_old a l _)).trans
    ((physical_mono hbox ha hi l).trans (hbill.trans hallow))

theorem point {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h : PointReceipt top k b j t l) (hb : a.b = b) (hj : a.j = j) (ht : a.t = t)
    (ha : 3 * a.t ≤ a.j) :
    (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) := by
  obtain ⟨hl, hlo, hbill⟩ := h
  cases a
  subst_vars
  exact ⟨l,hl,hlo,hbill⟩
open Final50SharedPrice (Rate)
open KoalaWeightedRate (Allowed)

def Covered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) ∨
  ∃ u l, k = .empty ∧ 0 < l ∧ l ≤ order k a ∧ Allowed a u ∧
    Final50SharedPrice.price a l (activeCap k) u ≤ allowance top k a.b a.j a.t

abbrev SharedReceipt (t b j l : ℕ) (u : Rate) : Prop :=
  0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ Allowed ⟨b,j,t⟩ u ∧
    Final50SharedPrice.price ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty b j t

theorem sharedPoint {a : Shape} {b j t l : ℕ} {u : Rate}
    (h : SharedReceipt t b j l u) (hb : a.b = b) (hj : a.j = j) (ht : a.t = t) :
    Covered t .empty a := by
  cases a
  subst_vars
  exact Or.inr ⟨u,l,rfl,h⟩

theorem covered_mono {k : Band} {a : Shape} {top next : ℕ}
    (h : Covered top k a) (hm : top ≤ next) (hn : next ≤ 14) : Covered next k a := by
  rcases h with h | ⟨u,l,he,hl,ho,hu,hp⟩
  · obtain ⟨l,hl,ho,hp⟩ := h
    exact Or.inl ⟨l,hl,ho,hp.trans (Final50PriceCaps.allowance_mono k hm hn)⟩
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
