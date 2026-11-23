import ProximityPrize.SubmissionLower.H2428Weighted87Count
import ProximityPrize.SubmissionLower.KoalaWeightedCofactor
import ProximityPrize.SubmissionLower.KoalaRetainedPrimary
import ProximityPrize.SubmissionLower.FadicCast
import ProximityPrize.SubmissionLower.Final50PriceLayer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

namespace KoalaWeightedLayer2428
noncomputable section

open P3 (I K)
open K1_13 (Row Geom Shape shape InBox embed indexDegree)
open K1_13_3 (Symbol symbolAt symbolIndex cofactor_rank)
open K1_13_2_2 (JetExp gradeWeight oldWeight)
open Final50Price (Messages primaryBox primaryCutoff layerWidth layerNeed)
open KoalaRetainedCut (Bank levelOrder)
open MvPolynomial
open scoped BigOperators Polynomial
open private index_eq_weighted from ProximityPrize.SubmissionLower.Fast070
open private exists_fresh specialization_bounds sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase
open private P3_6_8.spend_le P3_6_8.shapeSum from ProximityPrize.SubmissionLower.GoldBranch6N8

variable {Γ:Finset K} {s:K→K[X]}

abbrev jetWeight : Fin 4 → ℕ := fun i => if i = 0 then 8 else 15
abbrev cap:ℕ:=39656

private theorem weight_eq (m : JetExp) :
    m.weight jetWeight=8*m.weight gradeWeight+7*(m 1+m 2+m 3):=by
  rw [FadicGate.weight_four,FadicGate.w_grade]
  simp [jetWeight]
  omega

/-- Both branches of the published primary taper lie in the linear envelope. -/
theorem exponent_weight {m : JetExp} (hm : m ∈ TaperColumns.jetExponents) :
    m.weight jetWeight≤cap:=by
  change m.weight gradeWeight ≤ 4012 ∧ m.weight oldWeight ≤ 1650 ∧
    m 1+m 2+m 3≤TaperBudget.cap (m.weight gradeWeight) at hm
  obtain ⟨hb,hj,hd⟩:=hm
  rw [FadicGate.w_old] at hj
  rw [weight_eq]
  unfold cap
  by_cases hq:m.weight gradeWeight < 3514
  · omega
  · have hw : 26 * m.weight gradeWeight + 25 * (m 1 + m 2 + m 3) ≤ 131312 := by
      rw [TaperBudget.cap,if_neg hq] at hd
      have h:=(Nat.le_div_iff_mul_le (by decide:0 < 25)).mp hd
      omega
    omega

theorem symbol_weight {P : Row 4} (x : Geom) (h : PrimaryTaper.JetsBounded P) :
    (symbolAt x P).weightedTotalDegree jetWeight≤cap:=by
  rw [weightedTotalDegree,Finset.sup_le_iff]
  exact fun m hm => exponent_weight (h m (MvPolynomial.support_map_subset _ _ hm))

/-- Exact weighted remainder. The rectangular minimum keeps the original
ledger available. The weighted term uses the exact box, before rounding. -/
def remaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then
    min (Final50Price.remaining b j)
      (H2428Weighted87Count.boxCount (4012-b) (1650-j) 550 (cap-8*b)).toNat
  else 0

theorem remaining_anti {b j b' j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') :
    remaining b' j' ≤ remaining b j:=by
  unfold remaining
  by_cases ok:b' ≤ 4012 ∧ j' ≤ 1650
  · rw [if_pos ok, if_pos ⟨hb.trans ok.1,hj.trans ok.2⟩]
    apply min_le_min (Final50PriceLayer.remaining_anti hb hj)
    rw [← H2428Weighted87Count.taperBox_card, ← H2428Weighted87Count.taperBox_card]
    simp only [Int.toNat_natCast]
    apply Finset.card_le_card
    intro m hm
    rw [Set.Finite.mem_toFinset] at hm ⊢
    exact H2428Weighted87Count.taperBox_mono (Nat.sub_le_sub_left hb _) (Nat.sub_le_sub_left hj _)
      le_rfl (Nat.sub_le_sub_left (Nat.mul_le_mul_left 8 hb) _) hm
  · simp [ok]

theorem remaining_zero {b j : ℕ} (h : 1650 < j) : remaining b j = 0 := by
  simp [remaining,not_le_of_gt h]

private theorem count_weighted {r B J Θ : ℕ} (Q : Fin r → Symbol)
    (hi:LinearIndependent Geom Q) (hJ:J≤1650)
    (hb : ∀ i, (Q i).totalDegree ≤ B ∧ symbolIndex (Q i) ≤ J ∧
      (Q i).weightedTotalDegree jetWeight≤Θ) :
    r≤(H2428Weighted87Count.boxCount B J 550 Θ).toNat:=by
  classical
  let E:=(H2428Weighted87Count.taperBox_finite B J 550 Θ).toFinset
  let V:=MvPolynomial.restrictSupport Geom (↑E:Set JetExp)
  have hmem (i : Fin r) : Q i ∈ V := by
    change (↑(Q i).support:Set JetExp) ⊆ (↑E:Set JetExp)
    intro m hm
    change m ∈ E
    rw [Set.Finite.mem_toFinset]
    have h0:=le_weightedTotalDegree (1:Fin 4→ℕ) hm
    rw [weightedTotalDegree_one] at h0
    have hb' : m.weight gradeWeight≤B:=h0.trans (hb i).1
    have h1:=le_weightedTotalDegree Fin.val hm
    rw [← index_eq_weighted] at h1
    have hj' : m.weight oldWeight≤J:=h1.trans (hb i).2.1
    have hw:=(le_weightedTotalDegree jetWeight hm).trans (hb i).2.2
    rw [weight_eq] at hw
    have htop:=hj'.trans hJ
    rw [FadicGate.w_old] at htop
    exact ⟨hb', hj', by omega,hw⟩
  letI:Module.Finite Geom V:=MvPolynomial.restrictSupport_finite E.finite_toSet
  have hlin : LinearIndependent Geom (fun i => (⟨Q i,hmem i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hi
  have hdim:r≤Module.finrank Geom V:=by simpa using hlin.fintype_card_le_finrank
  rw [MvPolynomial.finrank_restrictSupport_finset] at hdim
  rw [← H2428Weighted87Count.taperBox_card]
  simpa using hdim

theorem cofactor_rank_weighted (n : ℕ) (F : Fin n → Symbol) (a : Fin n → ℕ) (hF : ∀ i, F i ≠ 0)
    (r:ℕ) (e:Fin r→Symbol) (hi:LinearIndependent Geom e)
    (hs:r≤Final50Price.symbolCount)
    (hcap : ∀ i, (e i).totalDegree ≤ 4012 ∧ symbolIndex (e i) ≤ 1650 ∧
      (e i).weightedTotalDegree jetWeight≤cap ∧ (∏ j,F j ^ a j) ∣ e i) :
    r≤remaining (∑ j,a j*(F j).totalDegree) (∑ j,a j*symbolIndex (F j)):=by
  by_cases hr:r=0
  · simp [hr]
  let b := ∑ j,a j*(F j).totalDegree
  let j := ∑ i,a i*symbolIndex (F i)
  have hrect := cofactor_rank n F a hF r e hi (fun i =>
    ⟨(hcap i).1,(hcap i).2.1,(hcap i).2.2.2⟩)
  obtain ⟨Q,hQ,hb⟩ := KoalaWeightedCofactor.cofactor_weight jetWeight 8 cap
    (by intro i; unfold jetWeight; split <;> decide) F a hF e hi hcap
  have h0 : b + (Q ⟨0,Nat.pos_of_ne_zero hr⟩).totalDegree ≤ 4012 ∧
      j+symbolIndex (Q ⟨0,Nat.pos_of_ne_zero hr⟩)≤1650:=⟨(hb _).1,(hb _).2.1⟩
  have hB:b≤4012:=by omega
  have hJ:j≤1650:=by omega
  have hweighted : r ≤ (H2428Weighted87Count.boxCount (4012-b) (1650-j) 550 (cap-8*b)).toNat := by
    apply count_weighted Q hQ (Nat.sub_le _ _) 
    intro i
    obtain ⟨hb',hj',hw'⟩:=hb i
    change b+_≤_ at hb'
    change j+_≤_ at hj'
    change 8*b+_≤_ at hw'
    exact ⟨by omega,by omega,by omega⟩
  change r≤remaining b j
  rw [remaining,if_pos ⟨hB,hJ⟩]
  exact le_min (le_min hs hrect) hweighted

def WeightedLayerBudget {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Prop :=
  layerNeed ≤ ∑ k ∈ Finset.range Final50PriceLayer.layerCount,
    remaining (∑ i,(k+1-l i)*(a i).b) (∑ i,(k+1-l i)*(a i).j)

-- The bank and its factor availability are the same as in the ordinary proof.
theorem bank_budget {n : ℕ} (D : Bank Γ s) (ranked : D.Ranked)
    (hjets : ∀ T P,D.row T P→PrimaryTaper.JetsBounded P) (f:Fin n→Row 4)
    (hirr : ∀ i,Irreducible (f i)) (hdiff : ∀ i j,i≠j → ¬ Associated (f i) (f j)) :
    WeightedLayerBudget (fun i => shape (f i)) (fun i => D.availability (f i)):=by
  classical
  let l (i:Fin n):=D.availability (f i)
  obtain ⟨x,hx,hsup⟩:=exists_fresh f
  obtain ⟨r,hrank,hfamilies⟩:=ranked x hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero:=hsup i
    rw [hz,MvPolynomial.support_zero,eq_comm,MvPolynomial.support_eq_empty] at hzero
    exact (hirr i).ne_zero hzero
  let cost (k : ℕ) := remaining (∑ i, (k+1-l i)*(shape (f i)).b)
    (∑ i,(k+1-l i)*(shape (f i)).j)
  have hcost (T) (hT : T ≤ primaryCutoff) : r T ≤ cost ((primaryCutoff-T)/layerWidth) := by
    obtain ⟨hs,e,he,hei⟩:=hfamilies T hT
    let a (i:Fin n):=levelOrder T-l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        exact ((hirr j).isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk ((hirr j).associated_of_dvd (hirr k) h))).pow
      · intro j
        exact D.available (f j) T hT _ (he i)
    have hbound := cofactor_rank_weighted n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei hs (fun i => by
        obtain ⟨hb,hj⟩:=specialization_bounds x (e i) (D.bounds T hT _ (he i)).1
        exact ⟨hb,hj,symbol_weight x (hjets T _ (he i)),by simpa only [map_prod,map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree=(f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i))=indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    simpa only [a,levelOrder,hb,hj] using hbound
  have hsum := hrank.trans_le ((Finset.sum_le_sum fun T hT =>
    hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
    (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  change layerNeed ≤ ∑ k ∈ Finset.range (1+primaryCutoff/layerWidth),cost k
  by_contra! hsmall
  have hpred:(∑ k ∈ Finset.range (1+primaryCutoff/layerWidth),cost k)≤layerNeed-1:=by omega
  exact (not_le_of_gt hsum) (Nat.mul_le_mul_left layerWidth hpred)

theorem of_messages_budget {w : I → K} {Γ : Finset K} {s : K → K[X]}
    (hm:Messages w Γ s) {n:ℕ} (f:Fin n→Row 4)
    (hirr : ∀ i,Irreducible (f i)) (hdiff : ∀ i j,i≠j → ¬ Associated (f i) (f j)) :
    WeightedLayerBudget (fun i => shape (f i))
      (fun i => (Bank.of_messages hm).availability (f i)) :=
  bank_budget (Bank.of_messages hm) (Bank.of_messages_ranked hm)
    (fun T P h => (show Final50OrderProof.BankRow w T P from h).2.2.1) f hirr hdiff

def layerTerm (q y : Shape) (L k : ℕ) : ℕ :=
  remaining ((k+1)*q.b+(k+1-L)*y.b) ((k+1)*q.j+(k+1-L)*y.j)

theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers:WeightedLayerBudget a l) {z:Finset (Fin n)} {i:Fin n} {q y:Shape} {L:ℕ}
    (hz : ∀ j ∈ z,l j=0) (hi:i ∉ z) (hl:l i≤L)
    (hq:InBox q (P3_6_8.shapeSum a z)) (hy:InBox y (a i)) :
    layerNeed ≤ ∑ k ∈ Finset.range Final50PriceLayer.layerCount,layerTerm q y L k:=by
  classical
  have hd:Disjoint z {i} := Finset.disjoint_singleton_right.mpr hi
  have hs : ∀ j ∈ ({i} : Finset (Fin n)), l j ≤ L := by
    intro j hj
    rwa [Finset.mem_singleton.mp hj]
  refine hlayers.trans (Finset.sum_le_sum fun k _ => remaining_anti ?_ ?_)
  · have h := P3_6_8.spend_le (fun i => (a i).b) (d := k+1) hz hs hd hq.1
    simp only [Finset.sum_singleton] at h
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hy.1) _).trans h
  · have h := P3_6_8.spend_le (fun i => (a i).j) (d := k+1) hz hs hd hq.2.1
    simp only [Finset.sum_singleton] at h
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hy.2.1) _).trans h

#print axioms exponent_weight
#print axioms cofactor_rank_weighted
#print axioms of_messages_budget
#print axioms mass_le
end
end KoalaWeightedLayer2428
