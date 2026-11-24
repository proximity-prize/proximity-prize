import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960Inventory
import ProximityPrize.SubmissionLower.R6960Low6960Monotone
import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal

-- merged module R6960Low6960RetainedBank
section Merged_R6960Low6960RetainedBank
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6960RetainedCut
noncomputable section
open P3 (I K node)
open K1_13 (Row Geom Shape shape InBox atJet extend OrderAt embed indexDegree)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open Low6960Prices (Messages SmallFactor ActiveFits primaryBox primaryCutoff layerWidth layerNeed
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
      ∀ T ≤ primaryCutoff, r T ≤ Low6960Prices.symbolCount ∧ ∃ e : Fin (r T) → Row 4,
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
  let cost (k : ℕ) := Low6960Prices.remaining (∑ i, (k+1-l i)*(shape (f i)).b)
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
    Low6960Prices.ProperCut f Γ s l := by
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
end Low6960RetainedCut

end Merged_R6960Low6960RetainedBank

-- merged module R6960Low6960RetainedCount
section Merged_R6960Low6960RetainedCount
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Low6960RetainedCut
noncomputable section
open P3 (I K)
open K1_13 (Geom Row Shape shape InBox extend atJet OnFactor)
open Low6960Prices (Messages activeFitsPrice ActiveFits SmallFactor Fits Holds FatEquations
  ProperCut LayerBudget lowerCap fullCap TrueWeightLE anchorCutoff)
open Final50GeoCover (activeDegree)
open K1_13_1 (anchorLead indexDegree_eq)
open Lower6960.Low (factor_small lower_of_anchor)
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
    InBox (Low6960Gate.floorShape id) (shape (∏ j ∈ z, f j)) →
    Low6960Gate.Gated id (shape (f i)) → Δ.card ≤ Low6960Gate.gatePrice G (shape (f i)) l
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
    ∀ id, InBox (Low6960Gate.floorShape id) (sumShape zeros (fun j => shape (f j))) →
      Low6960Gate.Gated id (shape (f i)) →
      (pieces i).card ≤ Low6960Gate.gatePrice G (shape (f i)) l
def Allocation (budget anchorK : ℕ) (G : Shape → ℕ) : Prop :=
  ∀ {w Γ s}, Messages w Γ s → ∀ top, top ≤ 14 → ∀ E,
    ∀ d : AllocationData Γ s E top anchorK G, lowerCap top + (∑ i, (d.pieces i).card) ≤ budget
theorem count_of_data {budget anchorK : ℕ} {G : Shape → ℕ} (gate : GateBank G)
    (allocate : Allocation budget anchorK G)
    {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} (hm : Messages w Γ s)
    (bank : Bank Γ s) (rank : bank.Ranked) (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) (fullCap 14)) (hw : TrueWeightLE P anchorCutoff)
    (ha : ActiveFits P anchorK) (hz : ∀ γ∈Γ, atJet P (extend (s γ))=0)
    (lower : ∀ top ≤ 14, Low6960Prices.c5 top)
    (book : Finset K) (E : FatEquations) (booked : book.card ≤ 140000)
    (hE : ∀ γ∈Γ, γ∉book → Holds E (extend (s γ))) : Γ.card ≤ 140000+budget := by
  classical
  obtain ⟨n,f,factors,different,prodDvd,covers⟩ := anchor_factors hP
  let top := (shape P).t
  have htop : top ≤ 14 := hbox.2.2
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
  have hchar (i) : (f i).degreeOf 3 < K1.p := (small i).2.2.1.2.2.trans_lt (by decide : 14<K1.p)
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
end Low6960RetainedCut

end Merged_R6960Low6960RetainedCount
