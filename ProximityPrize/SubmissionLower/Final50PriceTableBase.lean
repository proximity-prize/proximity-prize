import ProximityPrize.SubmissionLower.Final50PriceActualOrder
import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaAt2428Rates
import ProximityPrize.SubmissionLower.Final50PriceMonotone
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Final50PriceTableBase
open K1_13 (Shape InBox)
open KoalaRetainedCut (contractedPrice)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance actualAllowance activeCap start Admits)
open Final50PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

theorem contracted_le (x h : Shape) (l K : ℕ) :
    contractedPrice x h l K≤physicalPrice x l K:=by
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
  0 < l ∧ l≤order k ⟨bl,jl,0⟩ ∧ physicalPriceOld ⟨bh,jh,t⟩ l≤allowance top k bl jl t

abbrev PointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l≤order k ⟨b,j,t⟩ ∧ contractedPrice ⟨b,j,t⟩ (start k) l (activeCap k)≤allowance top k b j t

theorem oldRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h:OldReceipt top k bl jl bh jh t l)
    (hb:bl≤a.b) (hj:jl≤a.j) (hb' : a.b≤bh) (hj' : a.j≤jh)
    (ht:a.t=t) (ha:3*a.t≤a.j) :
    (∃ l,0 < l ∧ l≤order k a ∧ contractedPrice a (start k) l (activeCap k)≤allowance top k a.b a.j a.t):=by
  obtain ⟨hl,hlo,hbill⟩:=h
  have hu:l≤order k a:=hlo.trans (Final50PriceCaps.order_mono k hb hj)
  have hi:3*t≤jh:=by omega
  have hbox:InBox a ⟨bh,jh,t⟩:=⟨hb', hj', ht.le⟩
  have hallow : allowance top k bl jl t ≤ allowance top k a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul
      (Nat.sub_le_sub_left (Final50PriceCaps.tileReserve_anti k hb) _)
      (Final50PriceCaps.weight_mono k hb hj ht.ge))
  refine ⟨l,hl,hu,?_⟩
  exact ((contracted_le a (start k) l (activeCap k)).trans (physicalPrice_le_old a l _)).trans
    ((physical_mono hbox ha hi l).trans (hbill.trans hallow))

theorem point {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h:PointReceipt top k b j t l) (hb:a.b=b) (hj:a.j=j) (ht:a.t=t)
    (ha:3*a.t≤a.j) :
    (∃ l,0 < l ∧ l≤order k a ∧ contractedPrice a (start k) l (activeCap k)≤allowance top k a.b a.j a.t):=by
  obtain ⟨hl,hlo,hbill⟩:=h
  cases a
  subst_vars
  exact ⟨l,hl,hlo,hbill⟩
open Final50SharedPrice (Rate)
open KoalaAt2428Rates (Allowed)

open Final50PriceActualOrder (raised raised_pos raised_valid)

def ExactPointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧
    ∀ w : Fin 27, (start k).b ≤ w.val → w.val ≤ Final50PriceCaps.endWidth k → w.val+b ≤ 137 →
      contractedPrice ⟨b,j,t⟩ ⟨w.val,(start k).j,(start k).t⟩ (raised k b j t w.val l) (activeCap k) ≤
        actualAllowance top k w.val b j t

instance (top : ℕ) (k : Band) (b j t l : ℕ) : Decidable (ExactPointReceipt top k b j t l) := by
  unfold ExactPointReceipt
  infer_instance

def ExactCovered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  ∀ r : Shape, Admits k r → r.b+a.b ≤ 137 →
    ∃ m, 0 < m ∧ (m ≤ order k a ∨
      Final50PriceLayer.availableMass r a (m-1) < Final50Price.layerNeed ∨
      KoalaWeightedReceipt2428.WeightedOrder r a m) ∧
    contractedPrice a r m (activeCap k)≤actualAllowance top k r.b a.b a.j a.t

theorem exactPoint {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h:ExactPointReceipt top k b j t l) (hb:a.b=b) (hj:a.j=j) (ht:a.t=t) :
    ExactCovered top k a:=by
  obtain ⟨hl,ho,hcheck⟩:=h
  have ha:(⟨b,j,t⟩:Shape)=a:=by cases a; simp_all
  rw [← ha]
  intro r hr hs
  have hrj:=hr.2.1
  have hrt:=hr.2.2.1
  have hrb:=hr.2.2.2.1
  have hi:r.b < 27:=lt_of_le_of_lt hrb (by cases k <;> decide)
  have h:=hcheck ⟨r.b,hi⟩ hr.1.1 hrb hs
  have he : (⟨r.b,(start k).j,(start k).t⟩ : Shape) = r := by
    rcases r with ⟨rb,rj,rt⟩
    change rj=(start k).j at hrj
    change rt=(start k).t at hrt
    subst rj
    subst rt
    rfl
  rw [he] at h
  have hm:=raised_valid k b j t r.b l
  rw [he] at hm
  exact ⟨_,raised_pos hl,hm.imp (fun hml => hml.trans ho) id,h⟩

def Covered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  (∃ l,0 < l ∧ l≤order k a ∧ contractedPrice a (start k) l (activeCap k)≤allowance top k a.b a.j a.t) ∨
  (∃ u l, 0 < l ∧ l ≤ order k a ∧ Allowed a u ∧
    Final50SharedPrice.price a l 172 u≤allowance top k a.b a.j a.t) ∨ ExactCovered top k a

abbrev SharedReceipt (k : Band) (t b j l : ℕ) (u : Rate) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ Allowed ⟨b,j,t⟩ u ∧
    Final50SharedPrice.price ⟨b,j,t⟩ l 172 u≤allowance ((start k).t+t) k b j t

theorem sharedPoint {a : Shape} {k : Band} {b j t l : ℕ} {u : Rate}
    (h:SharedReceipt k t b j l u) (hb:a.b=b) (hj:a.j=j) (ht:a.t=t) :
    Covered ((start k).t+t) k a:=by
  cases a
  subst_vars
  exact Or.inr (Or.inl ⟨u,l,h⟩)

theorem covered_mono {k : Band} {a : Shape} {top next : ℕ}
    (h:Covered top k a) (hm:top≤next) (hn:next≤14):Covered next k a:=by
  rcases h with h | ⟨u,l,hl,ho,hu,hp⟩ | hp
  · obtain ⟨l,hl,ho,hp⟩ := h
    exact Or.inl ⟨l,hl,ho,hp.trans (Final50PriceCaps.allowance_mono k hm hn)⟩
  · exact Or.inr (Or.inl ⟨u,l,hl,ho,hu,hp.trans (Final50PriceCaps.allowance_mono k hm hn)⟩)
  · right
    right
    intro r hr hw
    obtain ⟨l,hl,ho,hp⟩:=hp r hr hw
    exact ⟨l,hl,ho,hp.trans (Final50PriceCaps.actualAllowance_mono k hm hn)⟩

theorem coveredPoint {top : ℕ} {k : Band} {a : Shape} {b j t l : ℕ}
    (h:PointReceipt top k b j t l) (hb:a.b=b) (hj:a.j=j) (ht:a.t=t)
    (ha:3*a.t≤a.j):Covered top k a:=Or.inl (point h hb hj ht ha)

theorem coveredRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h:OldReceipt top k bl jl bh jh t l)
    (hb:bl≤a.b) (hj:jl≤a.j) (hb' : a.b≤bh) (hj' : a.j≤jh)
    (ht:a.t=t) (ha:3*a.t≤a.j):Covered top k a :=
  Or.inl (oldRectangle h hb hj hb' hj' ht ha)
end Final50PriceTableBase
