import ProximityPrize.SubmissionLower.Z6970H2307Cofactor
import ProximityPrize.SubmissionLower.Z6970ExpandedOrderH2307
import ProximityPrize.SubmissionLower.Z6970ExpandedGateBox
import ProximityPrize.SubmissionLower.Z6970H2307BankBase

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000

namespace Height2307Inventory
noncomputable section

open P3 (I K node)
open K1_13 (Geom Row Shape shape extend indexDegree InBox)
open K1_13_2_2 (JetExp gradeWeight oldWeight)
open K1_13_3 (symbolAt)
open Low6969Prices (Messages primaryCutoff symbolCount)
open Low6969RetainedCut (Bank levelOrder)
open Height2307Cofactor (remaining)
open ExpandedColumns6970 (jetColumns jetExponents)
open P0_9_3 (exists_fresh sum_by_layer)
open scoped BigOperators

abbrev layerWidth : ℕ := ExpandedOrderH2307.layerWidth
abbrev layerNeed : ℕ := Low6969Prices.layerNeed
abbrev layerCount : ℕ := 1+primaryCutoff/layerWidth

def LayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤ ∑ k ∈ Finset.range layerCount,
    remaining (∑ i, (k+1-l i)*(a i).b) (∑ i, (k+1-l i)*(a i).j)

private theorem cap_active {P : Row 4} (h : ExpandedPrimary6970.JetsBounded P) :
    Final50Price.ActiveFits P 5192 := by
  intro m hm
  obtain ⟨hB,hJ,hT,hD⟩ := h m hm
  change m.weight gradeWeight ≤ 4024 at hB
  change m 1 + m 2 + m 3 ≤ ExpandedTaper6970.cap (m.weight gradeWeight) at hD
  rw [TaperColumns.sumGrade] at hB hD
  unfold ExpandedTaper6970.cap at hD
  split at hD <;> omega


def bank {w Γ s} (hm : Messages w Γ s) : Bank Γ s where
  row := ExpandedOrderH2307.BankRow w
  bounds := by
    intro T hT P hP
    refine ⟨hP.1,?_,cap_active hP.2.2.1⟩
    intro m hm
    exact (hP.2.1 m hm).trans hT
  order := by
    intro T hT P hP γ hγ
    obtain ⟨S,hS,hval⟩ := hm.hits γ hγ
    exact ExpandedOrderH2307.order_of_contact w P hT hP.2.1 hP.2.2.2
      (Polynomial.natDegree_map_le.trans (hm.degree γ hγ)) hS
      (fun i hi => by rw [Polynomial.eval_map,Polynomial.eval₂_hom,hval i hi])


theorem remaining_anti {b j B J : ℕ} (hb : b≤B) (hj : j≤J) :
    remaining B J ≤ remaining b j := by
  by_cases h : B≤4024 ∧ J≤1679
  · unfold Height2307Cofactor.remaining
    rw [if_pos h, if_pos ⟨hb.trans h.1,hj.trans h.2⟩]
    exact ExpandedGateBox6970.ambCount_mono
      (Nat.sub_le_sub_left hb _) (Nat.sub_le_sub_left hj _) le_rfl
  · simp [Height2307Cofactor.remaining,h]

theorem layer_budget {w Γ s} (hm : Messages w Γ s)
    (hceil : layerWidth*(layerNeed-1) < ExpandedOrderH2307.sourceRank)
    {n : ℕ} (f : Fin n → Row 4)
    (hirr : ∀ i, Irreducible (f i)) (hdiff : ∀ i j, i≠j → ¬ Associated (f i) (f j)) :
    LayerBudget (fun i => shape (f i)) (fun i => (bank hm).availability (f i)) := by
  classical
  let l (i : Fin n) := (bank hm).availability (f i)
  obtain ⟨x,hx,hsup⟩ := exists_fresh f
  obtain ⟨r,hrank,hfamilies⟩ :=
    ExpandedOrderH2307.symbol_families w x (ExpandedOrderH2307.primary_rank w) hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz,MvPolynomial.support_zero,eq_comm,MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) := remaining (∑ i, (k+1-l i)*(shape (f i)).b)
    (∑ i, (k+1-l i)*(shape (f i)).j)
  have hcost (T : ℕ) (hT : T ≤ primaryCutoff) : r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    obtain ⟨e,he,hei⟩ := hfamilies T hT
    let a (i : Fin n) := levelOrder T-l i
    let product := ∏ i, symbolAt x (f i) ^ a i
    have hproduct : product ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hnz i))
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        exact ((hirr j).isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk ((hirr j).associated_of_dvd (hirr k) h))).pow
      · intro j
        exact (bank hm).available (f j) T hT _ (he i)
    have weight_pow (wgt : Fin 4 → ℕ) (i : Fin n) (k : ℕ) :
        MvPolynomial.weightedTotalDegree wgt (symbolAt x (f i) ^ k) =
          k*MvPolynomial.weightedTotalDegree wgt (symbolAt x (f i)) := by
      induction k with
      | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,MvPolynomial.weightedTotalDegree_C]
      | succ k ih =>
        rw [pow_succ,MvPolynomial.weightedTotalDegree_mul _ _ _ (pow_ne_zero _ (hnz i)) (hnz i),
          ih,Nat.succ_mul]
    have wd (wgt : Fin 4 → ℕ) : MvPolynomial.weightedTotalDegree wgt product =
        ∑ i, a i * MvPolynomial.weightedTotalDegree wgt (symbolAt x (f i)) := by
      unfold product
      rw [MvPolynomial.weightedTotalDegree_prod wgt Finset.univ _ (fun i _ => pow_ne_zero _ (hnz i))]
      exact Finset.sum_congr rfl (fun i _ => weight_pow wgt i (a i))
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : MvPolynomial.weightedTotalDegree oldWeight (symbolAt x (f i)) =
        (shape (f i)).j := by
      change MvPolynomial.weightedTotalDegree Fin.val (symbolAt x (f i)) = indexDegree (f i)
      rw [K1_13_1.indexDegree_eq]
      unfold MvPolynomial.weightedTotalDegree
      rw [hsup]
    have hbP : product.totalDegree = ∑ i, a i * (shape (f i)).b := by
      simpa only [MvPolynomial.weightedTotalDegree_one,hb] using wd (1 : Fin 4 → ℕ)
    have hjP : MvPolynomial.weightedTotalDegree oldWeight product =
        ∑ i, a i * (shape (f i)).j := by rw [wd]; simp only [hj]
    have hsupport (i : Fin (r T)) (m : JetExp) (hm : m ∈ (symbolAt x (e i)).support) :
        m ∈ jetExponents := (he i).2.2.1 m (MvPolynomial.support_map_subset _ _ hm)
    have hk := Height2307Cofactor.rank product hproduct hbP hjP (fun i => symbolAt x (e i)) hei
      hsupport (fun i => by simpa only [product,map_prod,map_pow] using map_dvd (symbolAt x) (hdiv i))
    exact hk
  have hsum := hrank.trans ((Finset.sum_le_sum fun T hT =>
    hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
    (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  change layerNeed ≤ ∑ k ∈ Finset.range layerCount, cost k
  by_contra! small
  have cap : (∑ k ∈ Finset.range layerCount,cost k) ≤ layerNeed-1 := by omega
  exact (not_lt_of_ge (hsum.trans (Nat.mul_le_mul_left layerWidth cap))) hceil

def layerTerm (r x : Shape) (L k : ℕ) : ℕ :=
  remaining ((k+1)*r.b+(k+1-L)*x.b) ((k+1)*r.j+(k+1-L)*x.j)

def availableMass (r x : Shape) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (L+1679/(r.j+x.j)), layerTerm r x L k

theorem layerTerm_anti {r r' x x' : Shape} {L L' k : ℕ}
    (hr : InBox r r') (hx : x.b≤x'.b ∧ x.j≤x'.j) (hL : L≤L') :
    layerTerm r' x' L k ≤ layerTerm r x L' k := by
  unfold layerTerm
  have hgap : k+1-L' ≤ k+1-L := Nat.sub_le_sub_left hL _
  exact remaining_anti
    (Nat.add_le_add (Nat.mul_le_mul_left _ hr.1) (Nat.mul_le_mul hgap hx.1))
    (Nat.add_le_add (Nat.mul_le_mul_left _ hr.2.1) (Nat.mul_le_mul hgap hx.2))

private theorem layer_zero {r x : Shape} {L k : ℕ} (hj : 0<r.j+x.j)
    (hk : L+1679/(r.j+x.j)≤k) : layerTerm r x L k = 0 := by
  have hz : 1679/(r.j+x.j) < k+1-L := by omega
  have hj' : 1679 < (k+1-L)*(r.j+x.j) :=
    (Nat.div_lt_iff_lt_mul hj).mp hz
  have hp := Nat.mul_le_mul_right r.j (Nat.sub_le (k+1) L)
  have hindex : 1679 < (k+1)*r.j+(k+1-L)*x.j := by
    rw [Nat.mul_add] at hj'
    omega
  simp [layerTerm,Height2307Cofactor.remaining,not_le.mpr hindex]

theorem availableMass_anti {r r' x x' : Shape} {L L' : ℕ}
    (hr : InBox r r') (hx : x.b≤x'.b ∧ x.j≤x'.j) (hL : L≤L')
    (hj : 0<r.j+x.j) : availableMass r' x' L ≤ availableMass r x L' := by
  have hj' : 0<r'.j+x'.j := by have := hr.2.1; have := hx.2; omega
  let a := L + 1679/(r'.j+x'.j)
  let b := L' + 1679/(r.j+x.j)
  let N := max a b
  have ha : min N a = a := min_eq_right (le_max_left _ _)
  have hb : min N b = b := min_eq_right (le_max_right _ _)
  have ea :
      (∑ k ∈ Finset.range N, layerTerm r' x' L k) = availableMass r' x' L := by
    rw [K1_13_8.sum_range_min N a (fun _ h => layer_zero hj' h), ha]
    rfl
  have eb :
      (∑ k ∈ Finset.range N, layerTerm r x L' k) = availableMass r x L' := by
    rw [K1_13_8.sum_range_min N b (fun _ h => layer_zero hj h), hb]
    rfl
  rw [←ea, ←eb]
  exact Finset.sum_le_sum fun _ _ => layerTerm_anti hr hx hL

theorem availableMass_mono_order {r x : Shape} {L L' : ℕ}
    (hj : 0<r.j+x.j) (hL : L≤L') : availableMass r x L ≤ availableMass r x L' :=
  availableMass_anti ⟨le_rfl, le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ hL hj

theorem availableMass_anti_right {r x x' : Shape} {L : ℕ}
    (hj : 0<r.j+x.j) (hx : x.b≤x'.b ∧ x.j≤x'.j) :
    availableMass r x' L ≤ availableMass r x L :=
  availableMass_anti ⟨le_rfl, le_rfl, le_rfl⟩ hx le_rfl hj

theorem full_le_available {r x : Shape} {L : ℕ} (hj : 0<r.j+x.j) :
    (∑ k ∈ Finset.range layerCount, layerTerm r x L k) ≤ availableMass r x L := by
  rw [K1_13_8.sum_range_min layerCount (L+1679/(r.j+x.j)) (fun _ h => layer_zero hj h)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (min_le_right _ _))

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i∈z, l i=0) (hs : ∀ i∈s, l i≤L)
    (hdisj : Disjoint z s) (hq : InBox q (P3_6_8.shapeSum a z)) :
    layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (P3_6_8.shapeSum a s) L k := by
  refine hlayers.trans (Finset.sum_le_sum fun k _ => remaining_anti ?_ ?_)
  · exact P3_6_8.spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact P3_6_8.spend_le (fun i => (a i).j) hz hs hdisj hq.2.1

end
end Height2307Inventory
