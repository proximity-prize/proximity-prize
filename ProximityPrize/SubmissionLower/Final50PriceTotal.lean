import ProximityPrize.SubmissionLower.KoalaWeightedReceipt2428
import ProximityPrize.SubmissionLower.Final50RetainedIndex8
import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaAt2428Rates
import ProximityPrize.SubmissionLower.Compact50PriceTable
import ProximityPrize.SubmissionLower.Final50PriceMass
import ProximityPrize.SubmissionLower.Final50FatReserve

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Final50PriceTotal
open K1_13 (Shape InBox FatEligible)
open KoalaRetainedCut (contractedPrice)
open K1_13_8 (Valid zeroShape)
open Final50PriceLayer (availableMass)
open Final50Price (physicalPrice fatPrice)
open Final50Price (layerNeed LayerBudget fullCap Fits)
open Final50PriceCaps (factorCap Band reserve start pricingWeight pricingDenom Admits activeCap endWidth reserveAt tileReserve actualAllowance)
open Final50RetainedIndex8 (Box)
open Final50PriceMonotone (physicalPrice_anti)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_insert P3_6_8.shapeSum_union
  P3_6_8.shapeSum_mono P3_6_8.inBox_trans P3_6_8.inBox_shapeSum P3_6_8.shapeSum_valid_or_empty
  from ProximityPrize.SubmissionLower.GoldBranch6N8

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i=0)

private theorem chooseBand (r : Shape) (hr : Valid r) (hx : Box r) : ∃ k, Admits k r := by
  obtain ⟨b,j,t⟩:=r
  have ht:1≤t:=hr.1
  have hjt:3*t≤j:=hr.2.1
  have hjb:j≤3*b:=hr.2.2
  have hj:j≤8:=hx.2.1
  have hB : b ≤ Final50FatReserve.degreeCap j := by
    have hj0:3≤j:=by omega
    interval_cases j <;> simp [Box,Final50FatReserve.degreeCap] at hx ⊢ <;> omega
  have hcases : (j = 3 ∧ t = 1) ∨ (j = 4 ∧ t = 1) ∨ (j = 5 ∧ t = 1) ∨
      (j=6 ∧ t=1) ∨ (j=7 ∧ t=1) ∨ (j=6 ∧ t=2) ∨
      (j=7 ∧ t=2) ∨ (j=8 ∧ t=1) ∨ (j=8 ∧ t=2):=by omega
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · by_cases h1 : b ≤ 1
    · exact ⟨.one3,by simp [Admits,start,endWidth,InBox]; omega⟩
    · exact ⟨.one3wide,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · exact ⟨.one4,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · exact ⟨.one5,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · exact ⟨.one6,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · exact ⟨.one7,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · by_cases h3 : b ≤ 3
    · exact ⟨.two6thin,by simp [Admits,start,endWidth,InBox]; omega⟩
    · by_cases h11 : b ≤ 11
      · exact ⟨.two6thinwide,by simp [Admits,start,endWidth,InBox]; omega⟩
      · by_cases h13 : b ≤ 13
        · exact ⟨.two6wide,by simp [Admits,start,endWidth,InBox]; omega⟩
        · by_cases h16 : b ≤ 16
          · exact ⟨.two6wider,by simp [Admits,start,endWidth,InBox] at *; omega⟩
          · exact ⟨.two6last,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · by_cases h6 : b ≤ 6
    · exact ⟨.two7,by simp [Admits,start,endWidth,InBox]; omega⟩
    · by_cases h9 : b ≤ 9
      · exact ⟨.two7wide,by simp [Admits,start,endWidth,InBox] at *; omega⟩
      · exact ⟨.two7last,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩

  · exact ⟨.one8,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩
  · exact ⟨.two8,by simp [Admits,start,endWidth,InBox,Final50FatReserve.degreeCap] at *; omega⟩

private theorem degree_bound {r : Shape} (hr : Valid r) (hx : Box r) :
    r.b≤Final50FatReserve.degreeCap r.j:=by
  have hjl:3≤r.j:=(Nat.mul_le_mul_left 3 hr.1).trans hr.2.1
  have hju:=hx.2.1
  have hj:r.j=3 ∨ r.j=4 ∨ r.j=5 ∨ r.j=6 ∨ r.j=7 ∨ r.j=8:=by omega
  rcases hj with hj | hj | hj | hj | hj | hj <;> rw [hj] <;> simp only [Final50FatReserve.degreeCap]
  · exact hx.1
  · exact hx.2.2.1 (by omega)
  · exact hx.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.1 (by omega)
  · exact hx.2.2.2.2.2.2 (by omega)

private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z:Finset ι} {k:Band} (ha : ∀ i,Valid (a i)) (hr:Valid (P3_6_8.shapeSum a z))
    (hbox:Box (P3_6_8.shapeSum a z)) (hk:Admits k (P3_6_8.shapeSum a z))
    (hfat : ∀ i,FatEligible (a i)→cost i≤fatPrice (a i)) :
    (∑ i ∈ z,cost i)≤reserveAt k (P3_6_8.shapeSum a z).b:=by
  let r:=P3_6_8.shapeSum a z
  let er:=z.equivFin.symm
  let ar:Fin z.card→Shape:=fun i => a (er i).val
  have sums (g : Shape → ℕ) : (∑ i, g (ar i)) = ∑ i ∈ z, g (a i) := by
    rw [← Finset.sum_attach z (fun i => g (a i))]
    exact Fintype.sum_equiv er _ _ fun _ => rfl
  have hj:(∑ i,(ar i).j)≤8:=by rw [sums]; exact hbox.2.1
  have hb : (∑ i, (ar i).b) ≤ Final50FatReserve.degreeCap (∑ i, (ar i).j) := by
    rw [sums,sums]
    exact degree_bound hr hbox
  have hp:=Final50FatReserve.family z.card ar (fun i => ha (er i).val) hj hb
  rw [sums,sums,sums,sums] at hp
  have hp' : (∑ i ∈ z, fatPrice (a i)) ≤
      Final50FatReserve.charge r.b r.j r.t:=hp
  rw [hk.2.1,hk.2.2.1] at hp'
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans hp'
  have h:=P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide),(h.2.1.trans hbox.2.1).trans (by decide)⟩

private theorem positiveStartIndex {k : Band} (nonempty : k ≠ .empty) :
    0 < (start k).j := by
  cases k <;> first | exact (nonempty rfl).elim | decide

/-- Total cost of all factors in the low-height cover. -/
theorem total (top : ℕ) (htop : top ≤ 14) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits:Fits top a) (hlayers:LayerBudget a l)
    (hWeighted:KoalaWeightedLayer2428.WeightedLayerBudget a l)
    (hphys : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) →
      ∀ h:Shape,InBox h (retainedShape a l)→cost i≤contractedPrice (a i) h m (activeCap k))
    (hshared : ∀ i m u, 0 < m → m ≤ l i → KoalaAt2428Rates.Allowed (a i) u →
      cost i≤Final50SharedPrice.price (a i) m 172 u)
    (hfat : ∀ i,FatEligible (a i)→cost i≤fatPrice (a i)) :
    (∑ i,cost i)≤factorCap top:=by
  let z:=Finset.univ.filter (fun i => l i=0)
  let pos:=Finset.univ.filter (fun i => ¬ l i=0)
  let r:=P3_6_8.shapeSum a z
  have ha (i:Fin n):Valid (a i):=hfits.1 i
  have hz (i:Fin n) (hi:i ∈ z):l i=0:=(Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ k : Band, Admits k r ∧
      (∑ i ∈ z,cost i)≤reserveAt k r.b:=by
    rcases Final50RetainedIndex8.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret,htr,_⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨.empty, ?_, ?_⟩
      · rw [hr0]
        simp [Admits,start,zeroShape,InBox]
      · simp [hempty,r,P3_6_8.shapeSum_empty,reserveAt,start,Final50FatReserve.charge,zeroShape]
    · have hr : Valid r := (P3_6_8.shapeSum_valid_or_empty ha z).resolve_left (by
        intro he
        have heq:P3_6_8.shapeSum a z=zeroShape:=he ▸ P3_6_8.shapeSum_empty a
        have hpos:1≤(P3_6_8.shapeSum a z).t:=htr
        rw [heq] at hpos
        exact (by decide : ¬ (1≤zeroShape.t)) hpos)
      obtain ⟨k,hk⟩:=chooseBand r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩:=account
  let q:=start k
  have hqr:InBox q r:=hk.1
  have massKind:q=zeroShape ∨ 0 < q.j:=by cases k <;> decide
  have hreserve : reserveAt k r.b ≤ factorCap top := by
    have h:=Final50PriceCaps.reserveAt_mono k hk.2.2.2.1 le_rfl
    rw [Final50PriceCaps.reserveAt_end] at h
    exact h.trans (by interval_cases top <;> cases k <;> decide)
  have hall:InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top):=hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top):=by
    have hb:=P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _,Nat.add_le_add_right hqr.2.1 _,Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_fee (i : Fin n) (hi : i ∈ pos) :
      cost i≤actualAllowance top k r.b (a i).b (a i).j (a i).t:=by
    have hone : P3_6_8.shapeSum a {i} = a i := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
        P3_6_8.shapeSum_insert a (by simp),P3_6_8.shapeSum_empty]
      cases a i
      simp [zeroShape,Shape.plus]
    have hsingle:({i} : Finset (Fin n)) ⊆ pos:=Finset.singleton_subset_iff.mpr hi
    have hL:0 < l i:=hpos i hi
    have hj0 : 0 < (a i).j := by
      obtain ⟨ht,hj,_⟩:=ha i
      omega
    have hj:0 < q.j+(a i).j:=by omega
    have hmass0 := Final50PriceRetained.mass_le hlayers hz
      (s := {i}) (L:=l i) (by simp) (hdisj hsingle) hqr
    rw [hone] at hmass0
    have hmass:=hmass0.trans (Final50PriceLayer.layerSum_le_available massKind hj)
    have horder : Final50PriceCaps.order k (a i) ≤ l i := by
      rcases Final50PriceMass.order_valid k (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono massKind hj
          (show l i≤Final50PriceCaps.order k (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc:=member_cap hsingle
    rw [hone] at hc
    have hu:=P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ {i}))
    rw [P3_6_8.shapeSum_union a (hdisj hsingle),hone] at hu
    have hw:=(P3_6_8.inBox_trans hu hall).1
    change r.b+(a i).b≤137 at hw
    have hmatch : r.b ≤ min (endWidth k) (137-(a i).b) :=
      le_min hk.2.2.2.1 (by omega)
    have hsmall : reserveAt k r.b ≤ tileReserve k (a i).b :=
      Final50PriceCaps.reserveAt_mono k hmatch (min_le_left _ _)
    have hallow : Final50PriceCaps.allowance top k (a i).b (a i).j (a i).t ≤
        actualAllowance top k r.b (a i).b (a i).j (a i).t :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hsmall _))
    rcases Compact50PriceTable.price top htop k (a i) (ha i) hc with
      ⟨m,hm,hmo,hfee⟩ | ⟨u,m,hm,hmo,hu,hfee⟩ | hwid
    · exact (hphys i m hm (hmo.trans horder) k hk _ hqr).trans (hfee.trans hallow)
    · exact (hshared i m u hm (hmo.trans horder) hu).trans (hfee.trans hallow)
    · obtain ⟨m,hm,hmo,hfee⟩ := hwid r hk hw
      have hrr:InBox r (retainedShape a l):=⟨le_rfl,le_rfl,le_rfl⟩
      have hml : m ≤ l i := by
        rcases hmo with hsmall | hmassLt | hweighted
        · exact hsmall.trans horder
        · have hknd : r = zeroShape ∨ 0 < r.j := by
            by_cases he:k = .empty
            · exact Or.inl (hk.2.2.2.2 he)
            · right
              rw [hk.2.1]
              exact positiveStartIndex he
          have hjr:0 < r.j+(a i).j:=by omega
          by_contra! hn
          have hv := Final50PriceRetained.mass_le hlayers hz
            (s := {i}) (L:=l i) (by simp) (hdisj hsingle) hrr
          rw [hone] at hv
          have hn' : l i≤m-1:=by omega
          exact (not_lt_of_ge ((hv.trans (Final50PriceLayer.layerSum_le_available hknd hjr)).trans
            (Final50PriceLayer.availableMass_mono hknd hjr hn'))) hmassLt
        · have hin : i ∉ z := fun hi =>
            Finset.disjoint_left.mp (hdisj hsingle) hi (by simp)
          exact KoalaWeightedReceipt2428.order (by decide) hWeighted hz hin hrr hweighted
      exact (hphys i m hm hml k hk r hrr).trans hfee
  have hfits_pos:=member_cap (s:=pos) (Finset.Subset.rfl)
  have hwidth : (∑ i ∈ pos, (a i).b) ≤ 137 - q.b := by
    have hh:=hfits_pos.1
    change q.b+(∑ i ∈ pos,(a i).b)≤137 at hh
    omega
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 56 - q.j := by
    have hh:=hfits_pos.2.1
    change q.j+(∑ i ∈ pos,(a i).j)≤56 at hh
    omega
  have hDen:0 < pricingDenom k:=by cases k <;> decide
  have hweights : (∑ i ∈ pos, pricingWeight k (a i).b (a i).j (a i).t) ≤ pricingDenom k := by
    by_cases he:k = .empty
    · subst k
      simpa only [pricingWeight, ↓reduceIte, show pricingDenom .empty = 361 by decide] using
        KoalaAllocationWeight.sum_le htop a hfits pos
    · simpa only [q,pricingWeight,pricingDenom,if_neg he] using hindex
  let C:=factorCap top - reserveAt k r.b
  let M:=pricingDenom k
  have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * pricingWeight k (a i).b (a i).j (a i).t := by
    have hp:cost i≤C*pricingWeight k (a i).b (a i).j (a i).t / M:=positive_fee i hi
    have h:=Nat.mul_le_mul_left M hp
    calc
      _≤M*(C*pricingWeight k (a i).b (a i).j (a i).t / M):=h
      _=(C*pricingWeight k (a i).b (a i).j (a i).t / M)*M:=Nat.mul_comm _ _
      _≤_:=Nat.div_mul_le_self _ _
  have hweighted : M * (∑ i ∈ pos, cost i) ≤ M*C := by
    rw [Finset.mul_sum,mul_comm M C]
    refine (Finset.sum_le_sum fees).trans ?_
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ hweights
  have hp:(∑ i ∈ pos,cost i)≤C:=Nat.le_of_mul_le_mul_left hweighted hDen
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i,cost i)≤factorCap top
  dsimp [C] at hp
  omega

#print axioms total
end Final50PriceTotal
