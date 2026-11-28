import ProximityPrize.SubmissionLower.R6970RescueRankTransfer

set_option Elab.async false
set_option autoImplicit true

namespace Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient)
open K1_14_2_2 (RowCaps mass)
open P1_7_4 (Mass massQ dotQ weightedBill)
open _root_.Lower6960.Far6969RescueGeometry (Model Family)
open scoped BigOperators Classical

noncomputable section

def reducedWeight (rate : ℚ) (w : Mass) (k : Fin 4) : ℚ :=
  if k = 1 then max 0 (w k - rate) else w k

def transferredCredit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (a u : ℕ) (k : Fin 4) : ℚ :=
  P1_7_4.running (fun i => reducedWeight (rankTransfer plan) (eventLossWeight shape a u i))
    steps k + (if k = 1 then rankTransfer plan else 0)

def transferredLossLimit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) : ℚ :=
  weightedBill steps (fun i => reducedWeight (rankTransfer plan) (eventLossWeight shape a u i))
    capacity + weightedBill steps (eventCut shape 0) capacity + rankBase plan

def transferredFee (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) : ℕ :=
  (transferredLossLimit plan steps shape capacity a u).ceil.toNat +
    (weightedBill steps (eventCut shape 2) (fun _ k => plan.initialCap k)).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)

private theorem round_card {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  have hn : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans hn)

private theorem reduce_dot (rate : ℚ) (w : Mass) (S : Finset (Ideal Ambient)) :
    dotQ w (massQ S) ≤ dotQ (reducedWeight rate w) (massQ S) + rate * massQ S 1 := by
  have bound := mul_le_mul_of_nonneg_right (le_max_right 0 (w 1-rate))
    (P1_7_4.massQ_nonneg S 1)
  simp only [dotQ, Fin.sum_univ_four, reducedWeight] at *
  have h0 : (0 : Fin 4) ≠ 1 := by decide
  have h2 : (2 : Fin 4) ≠ 1 := by decide
  have h3 : (3 : Fin 4) ≠ 1 := by decide
  simp only [h0,h2,h3,ite_false,ite_true] at *
  linarith only [bound]

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable {R : Run F Crt G plan} (B : Book R)

private theorem sum_lost_mass (n : ℕ) (hn : n ≤ B.steps) :
    (∑ i∈range n, massQ (B.lost i) 1) + massQ (B.live n) 1 = massQ (B.live 0) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step := P1_7_4.massQ_split (B.next n (by omega)) (1 : Fin 4)
    rw [sum_range_succ, add_assoc]
    change _ + (massQ (B.live n \ B.live (n+1)) 1 + massQ (B.live (n+1)) 1) = _
    rw [step]
    exact ih (by omega)

theorem transferred_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (small : (2*a-1)*u < p) (hi : M.overhead.toNat ≤ 2313)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    (box : rankJ plan ≤ rankB plan) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ)
    (retained : ∀ k, (credit k : ℚ) ≤ transferredCredit plan B.steps B.shape a u k) :
    (paid B).card + charge B credit ≤ transferredFee plan B.steps B.shape B.capacity a u := by
  let rebate := rankTransfer plan
  let reduced (i : ℕ) := reducedWeight rebate (lossWeight B a u i)
  have cut (i : ℕ) (hi' : i < B.steps) :
      ((regularCutMarks B i).card : ℚ) ≤ dotQ (reduced i) (massQ (B.lost i)) +
        rebate * massQ (B.lost i) 1 :=
    (curve_count B ha hu slope caps hi roots hi').trans (reduce_dot rebate _ _)
  have cuts := sum_le_sum (fun i (mem : i∈range B.steps) => cut i (mem_range.mp mem))
  rw [sum_add_distrib, ← mul_sum] at cuts
  have lossRail : ((lossMarks B).card : ℚ) ≤ (rankMarks R).card +
      ∑ i∈range B.steps, ((regularCutMarks B i).card : ℚ) := by
    exact_mod_cast (show (lossMarks B).card ≤ (rankMarks R).card +
      ∑ i∈range B.steps, ((regularCutMarks B i).card) from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have rank := rank_count_transfer R hi box rankSmall
  have split := sum_lost_mass B B.steps le_rfl
  rw [B.start] at split
  change (∑ i∈range B.steps, massQ (B.lost i) 1) + massQ B.final 1 =
    (mass R.initial.parents 1 : ℚ) at split
  have paidTransfer :
      rebate * (∑ i∈range B.steps, massQ (B.lost i) 1) +
        rebate * massQ B.final 1 = rebate * (mass R.initial.parents 1 : ℚ) := by
    rw [← mul_add,split]
  have creditBill : (charge B credit : ℚ) ≤
      dotQ (P1_7_4.running reduced B.steps) (massQ B.final) + rebate * massQ B.final 1 := by
    have h : (charge B credit : ℚ) ≤
        dotQ (transferredCredit plan B.steps B.shape a u) (massQ B.final) := by
      unfold charge dotQ massQ
      push_cast
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (retained k) (Nat.cast_nonneg _)
    refine h.trans_eq ?_
    unfold dotQ transferredCredit reduced rebate
    simp only [Fin.sum_univ_four]
    have h0 : (0 : Fin 4) ≠ 1 := by decide
    have h2 : (2 : Fin 4) ≠ 1 := by decide
    have h3 : (3 : Fin 4) ≠ 1 := by decide
    simp only [h0,h2,h3,ite_false,ite_true,add_zero]
    change
      P1_7_4.running reduced B.steps 0 * massQ B.final 0 +
      (P1_7_4.running reduced B.steps 1 + rankTransfer plan) * massQ B.final 1 +
      P1_7_4.running reduced B.steps 2 * massQ B.final 2 +
      P1_7_4.running reduced B.steps 3 * massQ B.final 3 = _
    ring
  have bill := P1_7_4.bill_bound_with_final B.steps reduced B.capacity B.live B.lost
    (fun i hi' => B.next i hi') (fun _ _ => subset_rfl) (fun i hi' => B.bound i hi')
  rw [← Book.final] at bill
  have seedNonneg : 0 ≤ seedLimit B :=
    le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (seed_bill B)
  have loss : (lossMarks B).card + charge B credit ≤
      (transferredLossLimit plan B.steps B.shape B.capacity a u).ceil.toNat := by
    apply round_card
    push_cast
    change _ ≤ weightedBill B.steps reduced B.capacity + seedLimit B + rankBase plan
    change _ + rebate * _ ≤ _ at rank
    linarith only [lossRail,cuts,rank,paidTransfer,creditBill,bill,seedNonneg]
  have point := round_card (point_bill B)
  have singular : (singularMarks (M:=M) (F:=F) G).card ≤ (2*a-1)*((p+1)*u) :=
    singular_count F prime slope caps small (fun γ hγ => roots γ (mem_filter.mp hγ).1)
      (fun _ hγ => (mem_filter.mp hγ).2)
  have union₀ := card_union_le ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R))
    (singularMarks (M:=M) (F:=F) G)
  have union₁ := card_union_le (lossMarks B ∪ pointMarks B) (seedMarks R ∪ ordinateMarks R)
  have union₂ := card_union_le (lossMarks B) (pointMarks B)
  have union₃ := card_union_le (seedMarks R) (ordinateMarks R)
  have seed := seed_count R
  have ord := ordinate_count R
  unfold paid
  change _ ≤ (transferredLossLimit plan B.steps B.shape B.capacity a u).ceil.toNat +
    (pointLimit B).ceil.toNat + ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)
  omega

theorem transferred_normal_event (R : Run F Crt G plan) {a u bound : ℕ}
    (ha : 2 ≤ a) (hu : 0 < u) (prime : Prime G) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u)) (small : (2*a-1)*u < p)
    (hi : M.overhead.toNat ≤ 2313)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    (box : rankJ plan ≤ rankB plan) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ)
    (noPole : ∀ j i, (D.block j).eval (K1_14_1.nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, K1_14_1.MarkResidues D (M.label γ) (F.scalar γ))
    (feeFit : transferredFee plan plan.count plan.normalShape plan.history a u ≤ bound)
    (retained : ∀ k, (credit k : ℚ) ≤ transferredCredit plan plan.count plan.normalShape a u k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  refine ⟨B, final, ?_, ?_⟩
  · have h := transferred_count B ha hu prime slope caps small hi roots box rankSmall credit
      (fun k => by rw [steps,shape]; exact retained k)
    rw [steps,shape,capacity] at h
    exact h.trans feeFit
  · intro γ hγ
    rw [← final]
    exact paid_cover B hγ (roots γ hγ)

def realizedCredit (plan : Plan) (a u : ℕ) (credit : Fin 4 → ℕ) (k : Fin 4) : ℕ :=
  min (credit k) ⌊transferredCredit plan plan.count plan.normalShape a u k⌋₊

def creditAdjustment (plan : Plan) (a u : ℕ) (credit : Fin 4 → ℕ) : ℕ :=
  ∑ k, (credit k - realizedCredit plan a u credit k) * ⌊plan.history (plan.count-1) k⌋₊

theorem transferred_normal_event_adjusted (R : Run F Crt G plan) {a u bound : ℕ}
    (ha : 2 ≤ a) (hu : 0 < u) (prime : Prime G) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u)) (small : (2*a-1)*u < p)
    (hi : M.overhead.toNat ≤ 2313)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    (box : rankJ plan ≤ rankB plan) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ)
    (noPole : ∀ j i, (D.block j).eval (K1_14_1.nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, K1_14_1.MarkResidues D (M.label γ) (F.scalar γ))
    (feeFit : transferredFee plan plan.count plan.normalShape plan.history a u +
      creditAdjustment plan a u credit ≤ bound)
    (retained : ∀ k, (realizedCredit plan a u credit k : ℚ) ≤
      transferredCredit plan plan.count plan.normalShape a u k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨event⟩ := transferred_normal_event R ha hu prime slope caps small hi roots box rankSmall
    (realizedCredit plan a u credit) noPole residues le_rfl retained
  have debt : charge event.book credit ≤ charge event.book (realizedCredit plan a u credit) +
      creditAdjustment plan a u credit := by
    unfold charge creditAdjustment
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro k _
    have cap : mass event.book.final k ≤ ⌊plan.history (plan.count-1) k⌋₊ := by
      apply Nat.le_floor
      rw [event.final]
      exact Run.mass_terminal R k
    calc
      _ ≤ (realizedCredit plan a u credit k + (credit k - realizedCredit plan a u credit k)) *
          mass event.book.final k := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := by
        rw [Nat.add_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ cap) _
  refine ⟨event.book,event.final,?_,event.cover⟩
  have paid := event.count
  omega

end
end Research6970.Height2313.Lower6960.Prefix6969Rescue.Invoice
