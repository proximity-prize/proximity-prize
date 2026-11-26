import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.DdZ1iXjHc
import ProximityPrize.SubmissionLower.DdZQtCuFa
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_MonoidLocalization_UniqueFactorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RegularLocalRing_Polynomial
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low6966ActiveCycleMixed
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Encoding
import ProximityPrize.SubmissionLower.Low6966FatCount
import ProximityPrize.SubmissionLower.R6960Low6960Gates

section Merged6967_Low6966RetainedCount
set_option Elab.async false





set_option Elab.async false

-- merged module R6960Low6966RetainedBank
section Merged_R6960Low6966RetainedBank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6966RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox atJet extend OrderAt embed indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low6966Prices (Messages SmallFactor ActiveFits primaryBox primaryCutoff layerWidth layerNeed
  TrueWeightLE LayerBudget)
open scoped Polynomial BigOperators
open P0_9_3 (exists_fresh specialization_bounds sum_by_layer)
def levelOrder (T : ℕ) : ℕ := (primaryCutoff-T)/layerWidth+1
structure Bank (Γ : Finset K) (s : K → (Polynomial K)) where
  row : ℕ → Row 4 → Prop
  bounds : ∀ T ≤ primaryCutoff, ∀ P, row T P →
    InBox (shape P) primaryBox ∧ TrueWeightLE P primaryCutoff ∧ ActiveFits P 5164
  order : ∀ T ≤ primaryCutoff, ∀ P, row T P → ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (levelOrder T)
variable {Γ : Finset K} {s : K → (Polynomial K)}
def Bank.Ranked (D : Bank Γ s) : Prop :=
  ∀ x : Geom, (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, layerWidth*(layerNeed-1) < ∑ T ∈ Finset.range (primaryCutoff+1), r T ∧
      ∀ T ≤ primaryCutoff, r T ≤ Low6966Prices.symbolCount ∧ ∃ e : Fin (r T) → Row 4,
        (∀ i, D.row T (e i)) ∧ LinearIndependent Geom (fun i => symbolAt x (e i))
def Bank.Admissible (D : Bank Γ s) (f : Row 4) (l : ℕ) : Prop :=
  ∀ T ≤ primaryCutoff, ∀ P, D.row T P → f^(levelOrder T-l) ∣ P
private theorem some_admissible (D : Bank Γ s) (f : Row 4) : ∃ l, D.Admissible f l := by
  refine ⟨primaryCutoff/layerWidth+1, fun T _ P _ => ?_⟩
  have hle : levelOrder T ≤ primaryCutoff/layerWidth+1 :=
    Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
  rw [Nat.sub_eq_zero_of_le hle,pow_zero]
  exact one_dvd P
def Bank.availability (D : Bank Γ s) (f : Row 4) : ℕ := by
  classical
  exact Nat.find (some_admissible D f)
theorem Bank.available (D : Bank Γ s) (f : Row 4) : D.Admissible f (D.availability f) := by
  classical
  exact Nat.find_spec (some_admissible D f)
theorem Bank.extremal (D : Bank Γ s) (f : Row 4) (hp : 0 < D.availability f) :
    ∃ T ≤ primaryCutoff, ∃ P, D.row T P ∧ D.availability f ≤ levelOrder T ∧
      f^(levelOrder T - D.availability f) ∣ P ∧ ¬ f^(levelOrder T - D.availability f+1) ∣ P := by
  classical
  let l := D.availability f
  have hbad : ¬ D.Admissible f (l-1) := Nat.find_min (some_admissible D f) (by
    change l-1 < l
    dsimp only [l]
    omega)
  dsimp only [Bank.Admissible] at hbad
  push Not at hbad
  obtain ⟨T,hT,P,hP,hn⟩ := hbad
  have hl : l ≤ levelOrder T := by
    by_contra! hh
    have heq : levelOrder T-(l-1)=0 := by omega
    exact hn (by rw [heq,pow_zero]; exact one_dvd P)
  have heq : levelOrder T-(l-1)=levelOrder T-l+1 := by dsimp only [l] at *; omega
  exact ⟨T,hT,P,hP,hl,D.available f T hT P hP,by rwa [heq] at hn⟩
theorem Bank.layer_budget {n : ℕ} (D : Bank Γ s) (ranked : D.Ranked) (f : Fin n → Row 4)
    (hirr : ∀ i, Irreducible (f i)) (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) :
    LayerBudget (fun i => shape (f i)) (fun i => D.availability (f i)) := by
  classical
  let l (i : Fin n) := D.availability (f i)
  obtain ⟨x,hx,hsup⟩ := exists_fresh f
  obtain ⟨r,hrank,hfamilies⟩ := ranked x hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz,MvPolynomial.support_zero,eq_comm,MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) := Low6966Prices.remaining (∑ i, (k+1-l i)*(shape (f i)).b)
    (∑ i, (k+1-l i)*(shape (f i)).j)
  have hcost (T) (hT : T ≤ primaryCutoff) : r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    obtain ⟨hs,e,he,hei⟩ := hfamilies T hT
    let a (i : Fin n) := levelOrder T-l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        exact ((hirr j).isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk ((hirr j).associated_of_dvd (hirr k) h))).pow
      · intro j
        exact D.available (f j) T hT _ (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb,hj⟩ := specialization_bounds x (e i) (D.bounds T hT _ (he i)).1
        exact ⟨hb,hj,by simpa only [map_prod,map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    exact le_min hs (by simpa only [a,levelOrder,hb,hj] using hbound)
  have hsum := hrank.trans_le ((Finset.sum_le_sum fun T hT =>
    hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
    (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  change layerNeed ≤ ∑ k ∈ Finset.range (1+primaryCutoff/layerWidth), cost k
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1+primaryCutoff/layerWidth), cost k) ≤ layerNeed-1 := by omega
  exact (not_le_of_gt hsum) (Nat.mul_le_mul_left layerWidth hpred)
theorem Bank.proper_cut (D : Bank Γ s) {f : Row 4} (hf : SmallFactor f)
    (hchar : f.degreeOf 3 < K1.p) {l : ℕ} (hp : 0 < l) (hl : l ≤ D.availability f) :
    Low6966Prices.ProperCut f Γ s l := by
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal f (hp.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  obtain ⟨Q,hproper,hbQ,hwQ,haQ,hord⟩ := exists_divided_cut (H := 1) (k := levelOrder T) (l := l) hP one_ne_zero
    hf.1 hf.2.1 hchar isRelPrime_one_right (by omega) hb hw ht (by simp) divF exactF
  refine ⟨Q,hproper,⟨hbQ.1.trans (Nat.sub_le _ _),hbQ.2.1.trans (Nat.sub_le _ _),
    hbQ.2.2.trans (Nat.sub_le _ _)⟩,hwQ,haQ,?_⟩
  intro γ hγ
  exact hord _ (by simp [atJet]) (D.order T hT _ hrow γ hγ)
def sumShape {ι : Type*} (z : Finset ι) (x : ι → Shape) : Shape :=
  ⟨∑ i∈z, (x i).b, ∑ i∈z, (x i).j, ∑ i∈z, (x i).t⟩
theorem shape_of_product {ι : Type*} (z : Finset ι) (f : ι → Row 4) (hn : ∀ i∈z, f i ≠ 0) :
    shape (∏ i∈z, f i) = sumShape z (fun i => shape (f i)) := by
  have hb := MvPolynomial.weightedTotalDegree_prod (1 : Fin 4 → ℕ) z f hn
  have hj := MvPolynomial.weightedTotalDegree_prod Fin.val z f hn
  have ht := MvPolynomial.weightedTotalDegree_prod (Pi.single (3 : Fin 4) 1) z f hn
  simp only [MvPolynomial.weightedTotalDegree_one] at hb
  simp only [← K1_13_1.indexDegree_eq] at hj
  simp only [MvPolynomial.weightedTotalDegree_piSingle] at ht
  change Shape.mk _ _ _ = Shape.mk _ _ _
  rw [hb,hj,ht]
  rfl
theorem Bank.companion_price_floor {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    ∀ h : Shape, InBox h (shape (∏ j∈z, f j)) → Δ.card ≤ contractedPrice (shape (f i)) h l active := by
  classical
  obtain ⟨T,hT,P,hrow,hk,divF,exactF⟩ := D.extremal (f i) (hpos.trans_le hl)
  obtain ⟨hb,hw,ht⟩ := D.bounds T hT P hrow
  have hP : P ≠ 0 := fun he => exactF (he ▸ dvd_zero _)
  have hH : (∏ j∈z, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hf j).1.ne_zero
  have divH := retained_power_dvd z f (fun j => (hf j).1) hdiff (k := levelOrder T) (P := P) (by
    intro j hj
    have hd := D.available (f j) T hT P hrow
    simpa only [hz j hj,Nat.sub_zero] using hd)
  exact price_of_witness_floor (hm.mono hsub) (hf i) ha hchar hon hoff hP hH
    (prime_off_product z f (fun j => (hf j).1) hdiff hi) hpos (by omega) hb hw ht
    (fun γ hγ => D.order T hT P hrow γ (hsub hγ)) divH divF exactF
theorem Bank.companion_price {w : I → K} {n : ℕ} (D : Bank Γ s) (hm : Messages w Γ s)
    (f : Fin n → Row 4) (hf : ∀ i, SmallFactor (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (hz : ∀ j∈z, D.availability (f j)=0) {i : Fin n} (hi : i∉z)
    {l active : ℕ} (hpos : 0 < l) (hl : l ≤ D.availability (f i))
    (ha : ActiveFits (f i) active) (hchar : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (hsub : Δ ⊆ Γ) (hon : ∀ γ∈Δ, K1_13.OnFactor (f i) (extend (s γ)))
    (hoff : ∀ γ∈Δ, atJet (∏ j∈z, f j) (extend (s γ)) ≠ 0) :
    Δ.card ≤ contractedPrice (shape (f i)) (shape (∏ j∈z, f j)) l active :=
  D.companion_price_floor hm f hf hdiff z hz hi hpos hl ha hchar Δ hsub hon hoff
    _ ⟨le_rfl,le_rfl,le_rfl⟩
#print axioms Bank.proper_cut
#print axioms shape_of_product
#print axioms Bank.layer_budget
#print axioms Bank.companion_price_floor
#print axioms Bank.companion_price
end
end Low6966RetainedCut

end Merged_R6960Low6966RetainedBank

-- merged module R6960Low6966RetainedCount
section Merged_R6960Low6966RetainedCount
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6966RetainedCut
noncomputable section
open P3 (I K)
open K1_13 (Geom Row Shape shape InBox extend atJet OnFactor)
open Low6966Prices (Messages activeFitsPrice ActiveFits SmallFactor Fits Holds FatEquations
  ProperCut LayerBudget lowerCap fullCap TrueWeightLE anchorCutoff)
open Final50GeoCover (activeDegree)
open K1_13_1 (anchorLead indexDegree_eq)
open LowProfile6966 (factor_small lower_of_anchor)
open KoalaRetainedCut (anchor_factors priority_pieces)
open K1_13_1 (index_bounds)
open MvPolynomial
open scoped Polynomial BigOperators
def GateBank (G : Shape → ℕ) : Prop :=
  ∀ {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {n : ℕ} (D : Bank Γ s) (_ : Messages w Γ s)
    (f : Fin n → Row 4) (_ : ∀ i, SmallFactor (f i))
    (_ : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)) (z : Finset (Fin n))
    (_ : ∀ j ∈ z, D.availability (f j) = 0) {i : Fin n} (_ : i ∉ z)
    {l active : ℕ} (_ : 0 < l) (_ : l ≤ D.availability (f i))
    (_ : ActiveFits (f i) active) (_ : (f i).degreeOf 3 < K1.p)
    (Δ : Finset K) (_ : Δ ⊆ Γ) (_ : ∀ γ ∈ Δ, OnFactor (f i) (extend (s γ)))
    (_ : ∀ γ ∈ Δ, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) (id : ℕ),
    InBox (Low6966Gate.floorShape id) (shape (∏ j ∈ z, f j)) →
    Low6966Gate.Gated id (shape (f i)) → Δ.card ≤ Low6966Gate.gatePrice G (shape (f i)) l
structure AllocationData (Γ : Finset K) (s : K → (Polynomial K)) (E : FatEquations) (top anchorK : ℕ)
    (G : Shape → ℕ) where
  n : ℕ
  f : Fin n → Row 4
  pieces : Fin n → Finset K
  orders : Fin n → ℕ
  zeros : Finset (Fin n)
  zero_iff : ∀ i, i∈zeros ↔ orders i=0
  small : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits top (fun i => shape (f i))
  active_budget : (∑ i, activeDegree (f i)) ≤ anchorK
  layers : LayerBudget (fun i => shape (f i)) orders
  subset : ∀ i, pieces i ⊆ Γ
  on_factor : ∀ i γ, γ ∈ pieces i → OnFactor (f i) (extend (s γ))
  fat : ∀ i γ, γ ∈ pieces i → Holds E (extend (s γ))
  proper : ∀ i, 0 < orders i → ProperCut (f i) Γ s (orders i)
  contracted : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ h, InBox h (sumShape zeros (fun j => shape (f j))) →
      (pieces i).card ≤ contractedPrice (shape (f i)) h l active
  gated : ∀ i ∉ zeros, ∀ l, 0 < l → l ≤ orders i →
    ∀ active, ActiveFits (f i) active →
    ∀ id, InBox (Low6966Gate.floorShape id) (sumShape zeros (fun j => shape (f j))) →
      Low6966Gate.Gated id (shape (f i)) →
      (pieces i).card ≤ Low6966Gate.gatePrice G (shape (f i)) l
def Allocation (budget anchorK : ℕ) (G : Shape → ℕ) : Prop :=
  ∀ {w Γ s}, Messages w Γ s → ∀ top, top ≤ 15 → ∀ E,
    ∀ d : AllocationData Γ s E top anchorK G, lowerCap top + (∑ i, (d.pieces i).card) ≤ budget
theorem count_of_data {budget anchorK : ℕ} {G : Shape → ℕ} (gate : GateBank G)
    (allocate : Allocation budget anchorK G)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    (bank : Bank Γ s) (rank : bank.Ranked) (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) (fullCap 15)) (hw : TrueWeightLE P anchorCutoff)
    (ha : ActiveFits P anchorK) (hz : ∀ γ∈Γ, atJet P (extend (s γ))=0)
    (lower : ∀ top ≤ 15, Low6966Prices.c5 top)
    (book : Finset K) (E : FatEquations) (booked : book.card ≤ 56000)
    (hE : ∀ γ∈Γ, γ∉book → Holds E (extend (s γ))) : Γ.card ≤ 56000+budget := by
  classical
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := anchor_factors hP
  let top := (shape P).t
  have htop : top ≤ 15 := hbox.2.2
  have small (i : Fin n) : SmallFactor (f i) := factor_small hP hbox hw
    (factors i).1 (factors i).2.1 (factors i).2.2
  have fits : Fits top (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(factors i).2.1,index_bounds (f i)⟩,?_,?_,?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP prodDvd
      simp only [weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd Fin.val Finset.univ f hP prodDvd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP prodDvd
      change (∑ i, (f i).degreeOf 3) ≤ P.degreeOf 3
      simpa only [weightedTotalDegree_piSingle] using h
  have active : (∑ i, activeDegree (f i)) ≤ anchorK :=
    (sum_weightedTotalDegree_le_of_prod_dvd (![1,2,2,2] : Fin 4 → ℕ) Finset.univ f hP prodDvd).trans
      ((Final50GeoCover.activeFits_iff P anchorK).mp ha)
  let orders i := bank.availability (f i)
  let z := Finset.univ.filter fun i => orders i=0
  have hzero (i) : i∈z ↔ orders i=0 := by simp [z]
  obtain ⟨low,pieces,lowSub,lowOn,sub,on,off,total⟩ := priority_pieces
    (fun i => (factors i).2.2) s book z (fun γ hγ => covers _ (hz γ hγ))
  have lbound := lower top htop _ _ _ (hm.mono lowSub) _ (lower_of_anchor P hP hbox hw) lowOn
  have hchar (i) : (f i).degreeOf 3 < K1.p := (small i).2.2.1.2.2.trans_lt (by decide : 15<K1.p)
  let data : AllocationData Γ s E top anchorK G := {
    n := n, f := f, pieces := pieces, orders := orders, zeros := z, zero_iff := hzero
    small := small, different := different, fits := fits, active_budget := active
    layers := bank.layer_budget rank f (fun i => (factors i).1) different, subset := sub
    on_factor := fun i γ h => (on i γ h).2
    fat := fun i γ h => hE γ (sub i h) (on i γ h).1
    proper := fun i hp => bank.proper_cut (small i) (hchar i) hp le_rfl
    contracted := by
      intro i hi l hp hl K hK h hfloor
      apply bank.companion_price_floor hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) h
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
    gated := by
      intro i hi l hp hl K hK id hfloor hg
      refine gate bank hm f small different z (fun j hj => (hzero j).mp hj) hi
        hp hl hK (hchar i) (pieces i) (sub i) (fun γ hγ => (on i γ hγ).2) (off i hi) id ?_ hg
      rwa [shape_of_product z f (fun i _ => (factors i).1.ne_zero)]
  }
  have counts := allocate hm top htop E data
  change lowerCap top + (∑ i, (pieces i).card) ≤ budget at counts
  exact total.trans (by omega)
#print axioms count_of_data
end
end Low6966RetainedCut

end Merged_R6960Low6966RetainedCount

end Merged6967_Low6966RetainedCount

section Merged6967_Low6966SharedTallyNew
set_option Elab.async false











set_option Elab.async false





-- merged module R6960Low6966SharedChooseCut
section Merged_R6960Low6966SharedChooseCut
set_option Elab.async false
set_option linter.style.haveILetI false
set_option maxRecDepth 12000

namespace Low6966SharedChooseCut
noncomputable section

open K1_13 (Geom Row Shape shape InBox indexDegree)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height cycleLength_ge_order)
open MvPolynomial
open Low6966SharedPrice (slope coord)

theorem weighted_pow (w : Fin 4 → ℕ) {P : Row 4} (h : P ≠ 0) (a : ℕ) :
    (P^a).weightedTotalDegree w = a * P.weightedTotalDegree w := by
  induction a with
  | zero => rw [pow_zero,zero_mul,← MvPolynomial.C_1,weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ h) h,ih,Nat.succ_mul]

theorem valuation_factorization {f P : Row 4} (hf : f ≠ 0)
    (hpos : 0 < f.totalDegree) (hP : P ≠ 0) :
    ∃ a : ℕ, ∃ G : Row 4, P=f^a*G ∧ G≠0 ∧ ¬ f ∣ G := by
  have hm : FiniteMultiplicity f P := by
    refine ⟨P.totalDegree, ?_⟩
    intro hd
    have hle := weightedTotalDegree_le_of_dvd (1 : Fin 4→ℕ) hd hP
    rw [weighted_pow _ hf,weightedTotalDegree_one,weightedTotalDegree_one] at hle
    have ht := Nat.mul_le_mul_left (P.totalDegree+1) hpos
    simp only [Nat.mul_one] at ht
    omega
  obtain ⟨G,hG,hd⟩ := hm.exists_eq_pow_mul_and_not_dvd
  exact ⟨_,G,hG,fun h0 => hP (by rw [hG,h0,mul_zero]),hd⟩

theorem weight_coord (i : Fin 3) (P : Row 4) :
    coord (shape P) i =
      P.weightedTotalDegree (![fun _ : Fin 4 => 1,Fin.val,Pi.single 3 1] i) := by
  fin_cases i
  · exact (weightedTotalDegree_one P).symm
  · exact K1_13_1.indexDegree_eq P
  · exact (weightedTotalDegree_piSingle (3 : Fin 4) P).symm

theorem shape_product {f Q G : Row 4} (hf : f ≠ 0) (hG : G ≠ 0)
    {a : ℕ} (he : Q=f^a*G) (i : Fin 3) :
    coord (shape Q) i = a*coord (shape f) i+coord (shape G) i := by
  simp only [weight_coord,he,weightedTotalDegree_mul _ _ _ (pow_ne_zero _ hf) hG,weighted_pow _ hf]

private theorem cap_coords {Q : Row 4} {r : ℕ}
    (hQ : ∀ m ∈ Q.support, Low6966ShapeGate.fits r m) (i : Fin 3) :
    coord (shape Q) i ≤ r*coord slope i := by
  rw [weight_coord]
  apply Finset.sup_le
  intro m hm
  have hs := hQ m hm
  fin_cases i
  · exact hs.1
  · exact hs.2.1
  · simpa [Finsupp.weight_eq_sum, Finsupp.sum_fintype, Low6966SharedPrice.coord,
      Low6966SharedPrice.slope, Pi.single_apply] using hs.2.2

theorem minimal_pair {f G : Row 4} {P : Ideal GeoJets} [P.IsPrime]
    (hf : Irreducible f) (hproper : ¬f∣G) (hP : P.height=2)
    (hF : toGeneric f∈P) (hG : toGeneric G∈P) :
    (intersectionIdeal f G).IsMinimalPrime P := by
  have hsub : intersectionIdeal f G ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact hF
    · exact hG
  obtain ⟨P',hmin,hle⟩ := Ideal.exists_minimalPrimes_le hsub
  have hzero := K1_13_6_3_6.toGeneric_ne_zero hf.ne_zero
  have hrel := K1_13_7_1.proper_generic f G hf hproper
  have hht : P'.height=2 := pair_height hzero hrel hmin
  letI : P'.IsPrime := hmin.isPrime
  have heq : P'=P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht,hP] at hs
    exact (by decide : ¬(2:ℕ∞)+1≤2) hs
  exact heq ▸ hmin

theorem mem_of_order {P : Ideal GeoJets} [P.IsPrime] {Q : GeoJets} {n : ℕ}
    (hn : 0<n) (hQ : VanishesTo P Q n) : Q∈P := by
  let L := Localization.AtPrime P
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mp
    ((Ideal.pow_le_self (Nat.ne_of_gt hn)) hQ)

structure SuitableSurface (f : Row 4) (s : ℕ) (P : Ideal GeoJets) : Prop where
  prime : P.IsPrime
  height : P.height = 2
  contains : toGeneric f ∈ P
  low : ¬ @VanishesTo _ _ P prime (toGeneric f) (s+1)

/-- The same independent cut has positive residual order at every selected surface. -/
theorem exists_cut {w Γ s} (hm : Low6966Prices.Messages w Γ s)
    (f : Row 4) (hf : Irreducible f) (hpos : 0<f.totalDegree)
    (multiplicityCap : ℕ) (pivot : Fin 3)
    (hguard : multiplicityCap*coord slope pivot < coord (shape f) pivot)
    (surfaces : Finset (Ideal GeoJets))
    (hp : ∀ P ∈ surfaces, Low6966SharedPersistent.Persistent Γ s P)
    (hh : ∀ P ∈ surfaces, SuitableSurface f multiplicityCap P) :
    ∃ r a : ℕ, 0<r ∧ 0<r-multiplicityCap*a ∧ ∃ G : Row 4, G≠0 ∧ ¬f∣G ∧
      (∀ i, a*coord (shape f) i + coord (shape G) i ≤ r*coord slope i) ∧
      ∀ P ∈ surfaces, ∃ h : (intersectionIdeal f G).IsMinimalPrime P,
        @VanishesTo _ _ P h.isPrime (toGeneric G) (r-multiplicityCap*a) ∧
        ((r-multiplicityCap*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) P h.isPrime := by
  obtain ⟨r,hr,Q,hQ,hs,ho⟩ := Low6966SharedShapeRank.exists_polynomial hm surfaces hp
  obtain ⟨a,G,hfac,hG,hind⟩ := valuation_factorization hf.ne_zero hpos hQ
  have hbound (i : Fin 3) : a*coord (shape f) i+coord (shape G) i ≤ r*coord slope i := by
    rw [← shape_product hf.ne_zero hG hfac i]
    exact cap_coords hs i
  have hres : 0<r-multiplicityCap*a := Shared50ShapeRankBase.residual_order_pos hr hguard
    ((Nat.le_add_right _ _).trans (hbound pivot))
  refine ⟨r,a,hr,hres,G,hG,hind,hbound,?_⟩
  intro P hP
  have hdata := hh P hP
  letI := hdata.prime
  have hmap : toGeneric Q = (toGeneric f)^a*toGeneric G := by
    simp [hfac,toGeneric,map_mul,map_pow]
  have hGo : VanishesTo P (toGeneric G) (r-multiplicityCap*a) := by
    apply Shared50OrderDivision.vanishesTo_of_pow_mul_hasse P hdata.low
    rw [← hmap]
    exact ho P hP
  have hmin := minimal_pair hf hind hdata.height hdata.contains (mem_of_order hres hGo)
  exact ⟨hmin,hGo,cycleLength_ge_order hdata.height hdata.contains hGo⟩

#print axioms exists_cut
end
end Low6966SharedChooseCut

end Merged_R6960Low6966SharedChooseCut

-- merged module R6960Low6966SharedTallyNew
section Merged_R6960Low6966SharedTallyNew

set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Low6966SharedTallyNew
noncomputable section
open P3 (K)
open K1_13 (Row Shape shape InBox chart)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_2_4 (oldEmbedding)
open K1_13_6_1_2 (VanishesTo cycleLength_ge_order pair_height)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966Prices (taylorLength)
open Low6966SharedPrice (Rate RateFits coord slope deficit weights surface surfaceScale)
open Low6966SharedTally (Data)
open MvPolynomial Finset
open scoped Polynomial BigOperators
open Low6966SharedChooseCut (minimal_pair mem_of_order)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def tally (D : Data Γ s f Q l S) (F : Finset (Branch f Q l)) : ℕ :=
  ∑ b∈F,b.weight*(D.points b).card

private theorem scale_limit {x y e : ℕ} (h : ∀ N>0, N*x ≤ N*y+e) : x≤y := by
  by_contra! hh
  have hb := h (e+1) (by omega)
  have hc := Nat.mul_le_mul_left (e+1) (show y+1≤x by omega)
  rw [Nat.mul_add,Nat.mul_one] at hc
  omega

private theorem power_box (G : Row 4) (N : ℕ) :
    InBox (shape (G^N)) ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩ := by
  refine ⟨?_,?_,?_⟩
  · have h := weightedTotalDegree_pow_le (1 : Fin 4→ℕ) G N
    rw [weightedTotalDegree_one,weightedTotalDegree_one] at h
    exact (h.trans (Nat.mul_le_mul_left _ (le_max_left _ _))).trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Fin.val : Fin 4→ℕ) G N
    rw [← K1_13_1.indexDegree_eq,← K1_13_1.indexDegree_eq] at h
    exact h.trans (Nat.le_add_right _ _)
  · have h := weightedTotalDegree_pow_le (Pi.single (3 : Fin 4) 1) G N
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans (Nat.le_add_right _ _)

private theorem power_order {P : Ideal GeoJets} [P.IsPrime] {G : Row 4} {n : ℕ}
    (h : VanishesTo P (toGeneric G) n) (N : ℕ) : VanishesTo P (toGeneric (G^N)) (N*n) := by
  let L := Localization.AtPrime P
  change algebraMap GeoJets L (toGeneric (G^N)) ∈ IsLocalRing.maximalIdeal L^(N*n)
  unfold toGeneric
  rw [map_pow,map_pow,Nat.mul_comm N n,pow_mul]
  exact Ideal.pow_mem_pow h _

private theorem four_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (hv : K1_13_8.Valid (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) n)
    (hrate : surface .ordinary (shape f) (shape G).chamber ≤ 32*amount*n) :
    tally D F ≤ amount := by
  let W := weights .ordinary (shape f)
  have hbase : W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t ≤ 32*amount*n := by
    rw [Low6966SharedPrice.surface_ordinary_eq_weights hv] at hrate
    change _ ≤ _ at hrate
    exact hrate
  have hall (N : ℕ) (hN : 0<N) :
      N*(32*n*tally D F) ≤ N*(32*n*amount)+(W.b*3+W.j*3+W.t) := by
    let q : Shape := ⟨N*(shape G).chamber.b+3,N*(shape G).j+3,N*(shape G).t+1⟩
    have hCh : K1_13_6_2_3.ChamberBox q := by
      have ht := (K1_13_7_1.shape_chamber G).2
      have hj := Nat.mul_le_mul_left N ht
      have hb := Nat.mul_le_mul_left N (le_max_right (shape G).b (shape G).j)
      refine ⟨?_,?_,?_⟩
      · change N*(shape G).j+3 ≤ N*max (shape G).b (shape G).j+3
        exact Nat.add_le_add_right hb _
      · change 3*(N*(shape G).t+1) ≤ N*(shape G).j+3
        rw [show 3*(N*(shape G).t+1)=N*(3*(shape G).t)+3 by ring]
        exact Nat.add_le_add_right hj _
      · dsimp [q]; omega
    have hp' : ¬ f∣G^N := fun h => hproper (input.small.1.prime.dvd_of_dvd_pow h)
    have hdata (b : Branch f Q l) (hb : b∈F) :
        ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime b.surface,
          ((N*n : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f (G^N)) b.surface h.isPrime := by
      obtain ⟨hP,horder⟩ := hcut b hb
      letI := hP.isPrime
      have hheight := pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
        (K1_13_7_1.proper_generic f G input.small.1 hproper) hP
      have hmem : toGeneric f∈b.surface := hP.le (Ideal.subset_span (by simp))
      have ho := power_order horder N
      have hmin := minimal_pair input.small.1 hp' hheight hmem
        (mem_of_order (Nat.mul_pos hN hn) ho)
      exact ⟨hmin,cycleLength_ge_order hheight hmem ho⟩
    have hbound := Low6966SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
      (K1_13_6_2_3_2.of_children
        K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
        K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
      (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
        (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
      f Q (G^N) l input.small hp' q hCh (power_box G N) (fun _ => N*n) F D.points
      (fun b hb => D.four input b (hF hb)) hdata
    have hnum : N*(32*n*tally D F) ≤ surface .ordinary (shape f) q := by
      have h := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp hbound
      apply (Nat.cast_le (α := ℚ)).mp
      simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum,
        mul_comm,mul_left_comm,mul_assoc, surface] using h
    have hlin : surface .ordinary (shape f) q =
        N*(W.b*(shape G).chamber.b+W.j*(shape G).j+W.t*(shape G).t)+(W.b*3+W.j*3+W.t) := by
      rw [Low6966SharedPrice.surface_ordinary_eq_weights hv]
      unfold q W
      ring
    rw [hlin] at hnum
    exact hnum.trans (by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left N hbase) (W.b*3+W.j*3+W.t))
  have hh := scale_limit hall
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<32) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem tilted_count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (n amount : ℕ) (hn : 0<n) (htilt : Low6966Prices.tiltedFits (shape f))
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      (n : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime)
    (hrate : surface .tilted (shape f) (shape G).chamber ≤ 1920*amount*n) :
    tally D F ≤ amount := by
  let p := (shape f).chamber
  let q := (shape G).chamber
  have ht : 1≤p.t := input.small.2.1
  have hq : Low48BentLattice.Chamber (q,0) :=
    ⟨(K1_13_7_1.shape_chamber G).1,(K1_13_7_1.shape_chamber G).2,Nat.zero_le _⟩
  have hfamily := Low6966SharedBentCaps.caps_chamber (K1_13_7_1.shape_chamber f).1 ht htilt.1 hq
  let R := Low48BentCycle.rawFamily (Low6966SharedBentCaps.caps p q)
  let B := Low48BentCycle.capFamily (Low6966SharedBentCaps.caps p q)
  have h := Low6966SharedCycleBound.bound_with_cut (R := R) (B := B)
    Low6966SharedBentCaps.ordinary_doubled f Q G l input.small hproper (fun _ => n)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    F D.points (fun b hb => D.bent input (Low6966SharedBentCaps.chart q ht) b (hF hb)) hcut
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (Low6966SharedBentCaps.ordinary_budget hfamily)
  have hnum : 1920*n*tally D F ≤ surface .tilted (shape f) (shape G).chamber := by
    norm_num only [show (60 : ℚ) * 32 = 1920 by norm_num] at hh
    apply (Nat.cast_le (α := ℚ)).mp
    simpa only [tally,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,← Finset.mul_sum, mul_comm,mul_left_comm,mul_assoc, surface] using hh
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos (by decide : 0<1920) hn)
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hnum.trans hrate

theorem count (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F⊆D.branches) (G : Row 4) (hproper : ¬ f∣G)
    (u : Rate) (hu : RateFits (shape f) u) (r a : ℕ) (hn : 0<r-u.split*a)
    (hv : K1_13_8.Valid (shape f))
    (hbound : ∀ i, a*coord (shape f) i+coord (shape G) i≤r*coord slope i)
    (hcut : ∀ b∈F, ∃ h : (intersectionIdeal f G).IsMinimalPrime b.surface,
      @VanishesTo _ _ b.surface h.isPrime (toGeneric G) (r-u.split*a) ∧
      ((r-u.split*a : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal f G) b.surface h.isPrime) :
    tally D F ≤ u.amount := by
  have hfit i := (Nat.le_add_right _ _).trans (hbound i)
  have hb (i : Fin 3) : coord (shape G) i≤r*coord slope i-a*coord (shape f) i :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hbound i)
  have hbox : InBox (shape G) (deficit r a (shape f)) := ⟨hb 0,hb 1,hb 2⟩
  have hc := Low6966SharedPrice.chamber_bound hu r a hfit (shape G) hbox (K1_13_7_1.shape_chamber G).2
  have hcap : (weights u.kind (shape f)).b*(shape G).chamber.b +
      (weights u.kind (shape f)).j*(shape G).j + (weights u.kind (shape f)).t*(shape G).t ≤
      surfaceScale u.kind*u.amount*(r-u.split*a) :=
    Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc] using hc) (by decide : 0<3)
  cases hkind : u.kind
  · apply four_count D input F hF G hproper _ _ hn hv
    · intro b hb
      obtain ⟨h,ho,_⟩ := hcut b hb
      exact ⟨h,ho⟩
    · rw [Low6966SharedPrice.surface_ordinary_eq_weights hv]
      rw [hkind] at hcap
      exact hcap
  · have ht := hu.1 hkind
    apply tilted_count D input F hF G hproper _ _ hn ht
    · intro b hb
      obtain ⟨h,_,hl⟩ := hcut b hb
      exact ⟨h,hl⟩
    · rw [Low6966SharedPrice.surface_tilted_eq_weights hv ht]
      rw [hkind] at hcap
      exact hcap

#print axioms count
end
end Low6966SharedTallyNew

end Merged_R6960Low6966SharedTallyNew

end Merged6967_Low6966SharedTallyNew

section Merged6967_Low6966Tiles0Top1
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def priceBatch0 : P :=
  ⟨unpack [2197883909, 671158281, 4496364553, 4395703309, 21659657229, 69157141525], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [83958825, 8791466025, 73654435885, 369169469, 151066685, 22247648317], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [335682625, 35117516869, 13909041245, 6174480485, 30922327169, 47800607873], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [23220655257, 31659724973, 51827479753, 35620073721, 34513602813, 22265816329], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [30470012169, 21779553553, 21678961937, 13021990181, 8693472549, 372042021], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [4365016385, 4549567809, 8760505669, 8710242629, 4381723977, 4348171593], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [26745394513, 19717461, 8760648021, 19649881, 36493657, 13122575709], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [8743726429, 2940253, 53202273, 19648865, 2872673, 2940256], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [4364943717, 53201253, 19715429, 2939237, 2940260, 2871657], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [2939240, 2940264, 17618730349, 13172838765, 2871660, 2938220], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [2939244, 2940268, 4381718897, 2870641, 2871664, 2938224], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [2939248, 2940272, 2869621, 2870644, 2871668, 2938228], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [2939252, 2940276, 53199225, 19645817, 2869625, 2870648], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [2871672, 2938232, 2939256, 2940280, 2869628, 2870652], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [2871676, 2938236, 2939260, 2940284, 2868609, 2869632], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [2870656, 2937216, 2938240, 2939264, 2940288, 53272961], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [19719553, 2943360, 4398427525, 4364940677, 2868612, 2869636], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [2870660, 2937220, 2938244, 2939268, 2940292, 2943364], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [36421001, 2867593, 2868616, 2869640, 2870664, 2937224], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [2938248, 2939272, 2940296, 2942344, 2943368, 2867596], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [2868620, 2869644, 2870668, 2937228, 2938252, 2939276], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [2940300, 2942348, 2943372, 2867600, 2868624, 2869648], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [2870672, 2937232, 2938256, 2939280, 2940304, 2941328], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [2942352, 2943376, 2866581, 2867604, 2868628, 2869652], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [2870676, 2937236, 2938260, 2939284, 2940308, 2941332], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [2942356, 2943380, 4465533337, 4381649305, 69973401, 19642777], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [2866584, 2867608, 2868632, 2869656, 2936216, 2937240], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [2938264, 2939288, 2940312, 2941336, 2942360, 2943384], by decide +kernel⟩
private def priceBatch28 : P :=
  ⟨unpack [2866588, 2867612, 2868636, 2869660, 2936220, 2937244], by decide +kernel⟩
private def priceBatch29 : P :=
  ⟨unpack [2938268, 2939292, 2940316, 2941340, 2942364, 2943388], by decide +kernel⟩
private def priceBatch30 : P :=
  ⟨unpack [86749601, 2865569, 2866592, 2867616, 2868640, 2869664], by decide +kernel⟩
private def priceBatch31 : P :=
  ⟨unpack [2936224, 2937248, 2938272, 2939296, 2940320, 2941344], by decide +kernel⟩
private def priceBatch32 : P :=
  ⟨unpack [2942368, 2943392, 2865572, 2866596, 2867620, 2868644], by decide +kernel⟩
private def priceBatch33 : P :=
  ⟨unpack [2869668, 2936228, 2937252, 2938276, 2939300, 2940324], by decide +kernel⟩
private def priceBatch34 : P :=
  ⟨unpack [2941348, 2942372, 2943396, 2865576, 2866600, 2867624], by decide +kernel⟩
private def priceBatch35 : P :=
  ⟨unpack [2868648, 2869672, 2936232, 2937256, 2938280, 2939304], by decide +kernel⟩
private def priceBatch36 : P :=
  ⟨unpack [2940328, 2941352, 2942376, 2943400, 2864557, 2865580], by decide +kernel⟩
private def priceBatch37 : P :=
  ⟨unpack [2866604, 2867628, 2868652, 2869676, 2936236, 2937260], by decide +kernel⟩
private def priceBatch38 : P :=
  ⟨unpack [2938284, 2939308, 2940332, 2941356, 2942380, 2943404], by decide +kernel⟩
private def priceBatch39 : P :=
  ⟨unpack [137079217, 86748593, 2864561, 2865584, 2866608, 2867632], by decide +kernel⟩
private def priceBatch40 : P :=
  ⟨unpack [2868656, 2869680, 2936240, 2937264, 2938288, 2939312], by decide +kernel⟩
private def priceBatch41 : P :=
  ⟨unpack [2940336, 2941360, 2942384, 2943408, 8844382645, 4448755125], by decide +kernel⟩
private def priceBatch42 : P :=
  ⟨unpack [2864564, 2865588, 2866612, 2867636, 2868660, 2935220], by decide +kernel⟩
private def priceBatch43 : P :=
  ⟨unpack [2936244, 2937268, 2938292, 2939316, 2940340, 2941364], by decide +kernel⟩
private def priceBatch44 : P :=
  ⟨unpack [2942388, 2943412, 19640761, 2864568, 2865592, 2866616], by decide +kernel⟩
private def priceBatch45 : P :=
  ⟨unpack [2867640, 2868664, 2935224, 2936248, 2937272, 2938296], by decide +kernel⟩
private def priceBatch46 : P :=
  ⟨unpack [2939320, 2940344, 2941368, 2942392, 2943416, 2864572], by decide +kernel⟩
private def priceBatch47 : P :=
  ⟨unpack [2865596, 2866620, 2867644, 2868668, 2935228, 2936252], by decide +kernel⟩
private def priceBatch48 : P :=
  ⟨unpack [2937276, 2938300, 2939324, 2940348, 2941372, 2942396], by decide +kernel⟩
private def priceBatch49 : P :=
  ⟨unpack [2943420, 2863552, 2864576, 2865600, 2866624, 2867648], by decide +kernel⟩
private def priceBatch50 : P :=
  ⟨unpack [2868672, 2935232, 2936256, 2937280, 2938304, 2939328], by decide +kernel⟩
private def priceBatch51 : P :=
  ⟨unpack [2940352, 2941376, 2942400, 2943424, 137078213, 2863556], by decide +kernel⟩
private def priceBatch52 : P :=
  ⟨unpack [2864580, 2865604, 2866628, 2867652, 2868676, 2935236], by decide +kernel⟩
private def priceBatch53 : P :=
  ⟨unpack [2936260, 2937284, 2938308, 2939332, 2940356, 2941380], by decide +kernel⟩
private def priceBatch54 : P :=
  ⟨unpack [2942404, 2943428, 21896982985, 19639753, 2863560, 2864584], by decide +kernel⟩
private def priceBatch55 : P :=
  ⟨unpack [2865608, 2866632, 2867656, 2934216, 2935240, 2936264], by decide +kernel⟩
private def priceBatch56 : P :=
  ⟨unpack [2937288, 2938312, 2939336, 2940360, 2941384, 2942408], by decide +kernel⟩
private def priceBatch57 : P :=
  ⟨unpack [2943432, 2863564, 2864588, 2865612, 2866636, 2867660], by decide +kernel⟩
private def priceBatch58 : P :=
  ⟨unpack [2934220, 2935244, 2936268, 2937292, 2938316, 2939340], by decide +kernel⟩
private def priceBatch59 : P :=
  ⟨unpack [2940364, 2941388, 2942412, 2943436, 2862545, 2863568], by decide +kernel⟩
private def priceBatch60 : P :=
  ⟨unpack [2864592, 2865616, 2866640, 2867664, 2934224, 2935248], by decide +kernel⟩
private def priceBatch61 : P :=
  ⟨unpack [2936272, 2937296, 2938320, 2939344, 2940368, 2941392], by decide +kernel⟩
private def priceBatch62 : P :=
  ⟨unpack [2942416, 2943440, 36415957, 2862548, 2863572, 2864596], by decide +kernel⟩
private def priceBatch63 : P :=
  ⟨unpack [2865620, 2866644, 2867668, 2934228, 2935252, 2936276], by decide +kernel⟩
private def priceBatch64 : P :=
  ⟨unpack [2937300, 2938324, 2939348, 2940372, 2941396, 2942420], by decide +kernel⟩
private def priceBatch65 : P :=
  ⟨unpack [2943444, 8894712281, 2862552, 2863576, 2864600, 2865624], by decide +kernel⟩
private def priceBatch66 : P :=
  ⟨unpack [2866648, 2867672, 2934232, 2935256, 2936280, 2937304], by decide +kernel⟩
private def priceBatch67 : P :=
  ⟨unpack [2938328, 2939352, 2940376, 2941400, 2942424, 2943448], by decide +kernel⟩
private def priceBatch68 : P :=
  ⟨unpack [4398489053, 2862556, 2863580, 2864604, 2865628, 2866652], by decide +kernel⟩
private def priceBatch69 : P :=
  ⟨unpack [2867676, 2934236, 2935260, 2936284, 2937308, 2938332], by decide +kernel⟩
private def priceBatch70 : P :=
  ⟨unpack [2939356, 2940380, 2941404, 2942428, 2943452, 2861537], by decide +kernel⟩
private def priceBatch71 : P :=
  ⟨unpack [2862560, 2863584, 2864608, 2865632, 2866656, 2933216], by decide +kernel⟩
private def priceBatch72 : P :=
  ⟨unpack [2934240, 2935264, 2936288, 2937312, 2938336, 2939360], by decide +kernel⟩
private def priceBatch73 : P :=
  ⟨unpack [2940384, 2941408, 2942432, 2943456, 2861540, 2862564], by decide +kernel⟩
private def priceBatch74 : P :=
  ⟨unpack [2863588, 2864612, 2865636, 2866660, 2933220, 2934244], by decide +kernel⟩
private def priceBatch75 : P :=
  ⟨unpack [2935268, 2936292, 2937316, 2938340, 2939364, 2940388], by decide +kernel⟩
private def priceBatch76 : P :=
  ⟨unpack [2941412, 2942436, 2943460, 36414953, 2861544, 2862568], by decide +kernel⟩
private def priceBatch77 : P :=
  ⟨unpack [2863592, 2864616, 2865640, 2866664, 2933224, 2934248], by decide +kernel⟩
private def priceBatch78 : P :=
  ⟨unpack [2935272, 2936296, 2937320, 2938344, 2939368, 2940392], by decide +kernel⟩
private def priceBatch79 : P :=
  ⟨unpack [2941416, 2942440, 2943464, 2861548, 2862572, 2863596], by decide +kernel⟩
private def priceBatch80 : P :=
  ⟨unpack [2864620, 2865644, 2866668, 2933228, 2934252, 2935276], by decide +kernel⟩
private def priceBatch81 : P :=
  ⟨unpack [2936300, 2937324, 2938348, 2939372, 2940396, 2941420], by decide +kernel⟩
private def priceBatch82 : P :=
  ⟨unpack [2942444, 2943468, 2861552, 2862576, 2863600, 2864624], by decide +kernel⟩
private def priceBatch83 : P :=
  ⟨unpack [2865648, 2866672, 2933232, 2934256, 2935280, 2936304], by decide +kernel⟩
private def priceBatch84 : P :=
  ⟨unpack [2937328, 2938352, 2939376, 2940400, 2941424, 2942448], by decide +kernel⟩
private def priceBatch85 : P :=
  ⟨unpack [2943472, 4415198709, 2860533, 2861556, 2862580, 2863604], by decide +kernel⟩
private def priceBatch86 : P :=
  ⟨unpack [2864628, 2865652, 2932212, 2933236, 2934260, 2935284], by decide +kernel⟩
private def priceBatch87 : P :=
  ⟨unpack [2936308, 2937332, 2938356, 2939380, 2940404, 2941428], by decide +kernel⟩
private def priceBatch88 : P :=
  ⟨unpack [2942452, 2943476, 120299001, 53191161, 2860537, 2861560], by decide +kernel⟩
private def priceBatch89 : P :=
  ⟨unpack [2862584, 2863608, 2864632, 2865656, 2932216, 2933240], by decide +kernel⟩
private def priceBatch90 : P :=
  ⟨unpack [2934264, 2935288, 2936312, 2937336, 2938360, 2939384], by decide +kernel⟩
private def priceBatch91 : P :=
  ⟨unpack [2940408, 2941432, 2942456, 2943480, 2860540, 2861564], by decide +kernel⟩
private def priceBatch92 : P :=
  ⟨unpack [2862588, 2863612, 2864636, 2865660, 2932220, 2933244], by decide +kernel⟩
private def priceBatch93 : P :=
  ⟨unpack [2934268, 2935292, 2936316, 2937340, 2938364, 2939388], by decide +kernel⟩
private def priceBatch94 : P :=
  ⟨unpack [2940412, 2941436, 2942460, 2943484, 2860544, 2861568], by decide +kernel⟩
private def priceBatch95 : P :=
  ⟨unpack [2862592, 2863616, 2864640, 2865664, 2932224, 2933248], by decide +kernel⟩
private def priceBatch96 : P :=
  ⟨unpack [2934272, 2935296, 2936320, 2937344, 2938368, 2939392], by decide +kernel⟩
private def priceBatch97 : P :=
  ⟨unpack [2940416, 2941440, 2942464, 2943488, 2860548, 2861572], by decide +kernel⟩
private def priceBatch98 : P :=
  ⟨unpack [2862596, 2863620, 2864644, 2865668, 2932228, 2933252], by decide +kernel⟩
private def priceBatch99 : P :=
  ⟨unpack [2934276, 2935300, 2936324, 2937348, 2938372, 2939396], by decide +kernel⟩
private def priceBatch100 : P :=
  ⟨unpack [2940420, 2941444, 2942468, 2943492, 19636745, 2860552], by decide +kernel⟩
private def priceBatch101 : P :=
  ⟨unpack [2861576, 2862600, 2863624, 2864648, 2931208, 2932232], by decide +kernel⟩
private def priceBatch102 : P :=
  ⟨unpack [2933256, 2934280, 2935304, 2936328, 2937352, 2938376], by decide +kernel⟩
private def priceBatch103 : P :=
  ⟨unpack [2939400, 2940424, 2941448, 2942472, 3009032, 2860556], by decide +kernel⟩
private def priceBatch104 : P :=
  ⟨unpack [2861580, 2862604, 2863628, 2864652, 2931212, 2932236], by decide +kernel⟩
private def priceBatch105 : P :=
  ⟨unpack [2933260, 2934284, 2935308, 2936332, 2937356, 2938380], by decide +kernel⟩
private def priceBatch106 : P :=
  ⟨unpack [2939404, 2940428, 2941452, 2942476, 3009036, 2859537], by decide +kernel⟩
private def priceBatch107 : P :=
  ⟨unpack [2860560, 2861584, 2862608, 2863632, 2864656, 2931216], by decide +kernel⟩
private def priceBatch108 : P :=
  ⟨unpack [2932240, 2933264, 2934288, 2935312, 2936336, 2937360], by decide +kernel⟩
private def priceBatch109 : P :=
  ⟨unpack [2938384, 2939408, 2940432, 2941456, 2942480, 3009040], by decide +kernel⟩
private def priceBatch110 : P :=
  ⟨unpack [86052834837, 4398487061, 2859540, 2860564, 2861588, 2862612], by decide +kernel⟩
private def priceBatch111 : P :=
  ⟨unpack [2863636, 2864660, 2931220, 2932244, 2933268, 2934292], by decide +kernel⟩
private def priceBatch112 : P :=
  ⟨unpack [2935316, 2936340, 2937364, 2938388, 2939412, 2940436], by decide +kernel⟩
private def priceBatch113 : P :=
  ⟨unpack [2941460, 2942484, 3009044, 53190169, 2859544, 2860568], by decide +kernel⟩
private def priceBatch114 : P :=
  ⟨unpack [2861592, 2862616, 2863640, 2930200, 2931224, 2932248], by decide +kernel⟩
private def priceBatch115 : P :=
  ⟨unpack [2933272, 2934296, 2935320, 2936344, 2937368, 2938392], by decide +kernel⟩
private def priceBatch116 : P :=
  ⟨unpack [2939416, 2940440, 2941464, 2942488, 3009048, 2859548], by decide +kernel⟩
private def priceBatch117 : P :=
  ⟨unpack [2860572, 2861596, 2862620, 2863644, 2930204, 2931228], by decide +kernel⟩
private def priceBatch118 : P :=
  ⟨unpack [2932252, 2933276, 2934300, 2935324, 2936348, 2937372], by decide +kernel⟩
private def priceBatch119 : P :=
  ⟨unpack [2938396, 2939420, 2940444, 2941468, 2942492, 3009052], by decide +kernel⟩
private def priceBatch120 : P :=
  ⟨unpack [2859552, 2860576, 2861600, 2862624, 2863648, 2930208], by decide +kernel⟩
private def priceBatch121 : P :=
  ⟨unpack [2931232, 2932256, 2933280, 2934304, 2935328, 2936352], by decide +kernel⟩
private def priceBatch122 : P :=
  ⟨unpack [2937376, 2938400, 2939424, 2940448, 2941472, 3008032], by decide +kernel⟩
private def priceBatch123 : P :=
  ⟨unpack [3009056, 12971641381, 2859556, 2860580, 2861604, 2862628], by decide +kernel⟩
private def priceBatch124 : P :=
  ⟨unpack [2863652, 2930212, 2931236, 2932260, 2933284, 2934308], by decide +kernel⟩
private def priceBatch125 : P :=
  ⟨unpack [2935332, 2936356, 2937380, 2938404, 2939428, 2940452], by decide +kernel⟩
private def priceBatch126 : P :=
  ⟨unpack [2941476, 3008036, 3009060, 19635753, 2859560, 2860584], by decide +kernel⟩
private def priceBatch127 : P :=
  ⟨unpack [2861608, 2862632, 2863656, 2930216, 2931240, 2932264], by decide +kernel⟩
private def priceBatch128 : P :=
  ⟨unpack [2933288, 2934312, 2935336, 2936360, 2937384, 2938408], by decide +kernel⟩
private def priceBatch129 : P :=
  ⟨unpack [2939432, 2940456, 2941480, 3008040, 3009064, 2859564], by decide +kernel⟩
private def priceBatch130 : P :=
  ⟨unpack [2860588, 2861612, 2862636, 2929196, 2930220, 2931244], by decide +kernel⟩
private def priceBatch131 : P :=
  ⟨unpack [2932268, 2933292, 2934316, 2935340, 2936364, 2937388], by decide +kernel⟩
private def priceBatch132 : P :=
  ⟨unpack [2938412, 2939436, 2940460, 2941484, 3008044, 3009068], by decide +kernel⟩
private def priceBatch133 : P :=
  ⟨unpack [30101107249, 36411953, 2858544, 2859568, 2860592, 2861616], by decide +kernel⟩
private def priceBatch134 : P :=
  ⟨unpack [2862640, 2929200, 2930224, 2931248, 2932272, 2933296], by decide +kernel⟩
private def priceBatch135 : P :=
  ⟨unpack [2934320, 2935344, 2936368, 2937392, 2938416, 2939440], by decide +kernel⟩
private def priceBatch136 : P :=
  ⟨unpack [2940464, 2941488, 3008048, 3009072, 2858548, 2859572], by decide +kernel⟩
private def priceBatch137 : P :=
  ⟨unpack [2860596, 2861620, 2862644, 2929204, 2930228, 2931252], by decide +kernel⟩
private def priceBatch138 : P :=
  ⟨unpack [2932276, 2933300, 2934324, 2935348, 2936372, 2937396], by decide +kernel⟩
private def priceBatch139 : P :=
  ⟨unpack [2938420, 2939444, 2940468, 3007028, 3008052, 223506888296496781981510198], by decide +kernel⟩
private def priceBatch140 : P :=
  ⟨unpack [2858552, 2859576, 2860600, 2861624, 2862648, 2929208], by decide +kernel⟩
private def priceBatch141 : P :=
  ⟨unpack [2930232, 2931256, 2932280, 2933304, 2934328, 2935352], by decide +kernel⟩
private def priceBatch142 : P :=
  ⟨unpack [2936376, 2937400, 2938424, 2939448, 2940472, 3007032], by decide +kernel⟩
private def priceBatch143 : P :=
  ⟨unpack [3008056, 224548234799561770074499642], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27, priceBatch28, priceBatch29, priceBatch30, priceBatch31, priceBatch32, priceBatch33, priceBatch34, priceBatch35, priceBatch36, priceBatch37, priceBatch38, priceBatch39, priceBatch40, priceBatch41, priceBatch42, priceBatch43, priceBatch44, priceBatch45, priceBatch46, priceBatch47, priceBatch48, priceBatch49, priceBatch50, priceBatch51, priceBatch52, priceBatch53, priceBatch54, priceBatch55, priceBatch56, priceBatch57, priceBatch58, priceBatch59, priceBatch60, priceBatch61, priceBatch62, priceBatch63, priceBatch64, priceBatch65, priceBatch66, priceBatch67, priceBatch68, priceBatch69, priceBatch70, priceBatch71, priceBatch72, priceBatch73, priceBatch74, priceBatch75, priceBatch76, priceBatch77, priceBatch78, priceBatch79, priceBatch80, priceBatch81, priceBatch82, priceBatch83, priceBatch84, priceBatch85, priceBatch86, priceBatch87, priceBatch88, priceBatch89, priceBatch90, priceBatch91, priceBatch92, priceBatch93, priceBatch94, priceBatch95, priceBatch96, priceBatch97, priceBatch98, priceBatch99, priceBatch100, priceBatch101, priceBatch102, priceBatch103, priceBatch104, priceBatch105, priceBatch106, priceBatch107, priceBatch108, priceBatch109, priceBatch110, priceBatch111, priceBatch112, priceBatch113, priceBatch114, priceBatch115, priceBatch116, priceBatch117, priceBatch118, priceBatch119, priceBatch120, priceBatch121, priceBatch122, priceBatch123, priceBatch124, priceBatch125, priceBatch126, priceBatch127, priceBatch128, priceBatch129, priceBatch130, priceBatch131, priceBatch132, priceBatch133, priceBatch134, priceBatch135, priceBatch136, priceBatch137, priceBatch138, priceBatch139, priceBatch140, priceBatch141, priceBatch142, priceBatch143]
private theorem i3 : checks (tilesOf batches) 142 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 142 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 142 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 142 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 142 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 142 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 142 51 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤142) (hj : a.j≤58) :
    Covered orders a ∨ Low6966Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

end Low6966Allocation.Group0

end Merged6967_Low6966Tiles0Top1
