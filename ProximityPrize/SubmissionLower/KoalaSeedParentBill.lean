import ProximityPrize.SubmissionLower.KoalaSeedParentArithmetic
import ProximityPrize.SubmissionLower.HighCore82258JointRankCharge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace KoalaSeedParent
noncomputable section

open Finset
open HighCore82258 (Band K p AnchorModel AnchoredFamily InBand Source)
open HighCore82258_3 (Process PairedMass laterCount stopIndex rankMass history initialCap initialE)
open HighCore82258JointRank (rankCharge rankRounding rankMarks rank_marks_le)
open HighCore82268JointRank (splice bill_with_exit_terminal)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono)
open P1_7_4 (Mass dotQ massQ running weightedBill)

theorem disjoint_mass {S P Q : Finset (Ideal Ambient)} (hp : P ⊆ S) (hq : Q ⊆ S)
    (hd : Disjoint P Q) (k : Fin 4) : mass P k + mass Q k ≤ mass S k := by
  classical
  apply le_trans _ (mass_mono (Finset.union_subset hp hq) k)
  unfold mass
  rw [Finset.sum_union hd]

def firstCap (b : Band) (d : ℕ) : Mass :=
  fun k => rankMass b k - if k = 2 then (d : ℚ) else 0

private theorem dot_sub_head (w c : Mass) (d : ℚ) :
    dotQ w (fun k => c k - if k = 2 then d else 0) = dotQ w c - w 2*d := by
  simp [dotQ,Fin.sum_univ_succ] <;> ring

theorem first_bill_with (b : Band) (n : ℕ) (rank : Mass) (w hist : ℕ → Mass) (d : ℕ)
    (hpos : ∀ k, 0 ≤ rank k) :
    weightedBill (n+1) (splice 0 rank w) (splice 0 (firstCap b d) hist) =
      weightedBill (n+1) (splice 0 rank w) (splice 0 (rankMass b) hist) -
        rank 2*(d:ℚ) := by
  unfold weightedBill
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have htail :
      (∑ i ∈ range n,
        dotQ (fun k => running (splice 0 rank w) (i+1+1) k -
          running (splice 0 rank w) (i+1) k) (splice 0 (firstCap b d) hist (i+1))) =
      ∑ i ∈ range n,
        dotQ (fun k => running (splice 0 rank w) (i+1+1) k -
          running (splice 0 rank w) (i+1) k) (splice 0 (rankMass b) hist (i+1)) := by
    apply sum_congr rfl
    intro i _
    simp [splice]
  rw [htail]
  have hhead : (fun k => running (splice 0 rank w) (0+1) k -
      running (splice 0 rank w) 0 k) = rank := by
    funext k
    simp [running,splice,max_eq_right (hpos k)]
  rw [hhead]
  have hzero (v : Mass) : splice 0 v hist 0 = v := by simp [splice]
  rw [hzero (firstCap b d), hzero (rankMass b)]
  unfold firstCap
  rw [dot_sub_head]
  ring

theorem first_bill (b : Band) (n : ℕ) (rank : Mass) (w : ℕ → Mass) (d : ℕ)
    (hpos : ∀ k, 0 ≤ rank k) :
    weightedBill (n+1) (splice 0 rank w) (splice 0 (firstCap b d) (history b)) =
      weightedBill (n+1) (splice 0 rank w) (splice 0 (rankMass b) (history b)) -
        rank 2*(d:ℚ) :=
  first_bill_with b n rank w (history b) d hpos

theorem process_bill_with {b : Band} {u del} {M : AnchorModel u del}
    {rows} {pairs : HighCore82258.Pairs b (FrontCore82258.effectiveHeight M).toNat rows}
    (R : Process pairs) (rank : Mass) (w hist : ℕ → Mass)
    (hcap : ∀ i < laterCount b+1, ∀ k, massQ (R.live i) k ≤ hist i k) (d : ℕ)
    (hparent : d+mass R.parents 2 ≤ initialCap b 2) :
    ((∑ i ∈ range (laterCount b+1),dotQ (w i) (massQ (R.lost i))) +
      dotQ rank (massQ R.rankExit)) +
      dotQ (running (splice 0 rank w) (laterCount b+2)) (massQ R.final) ≤
      weightedBill (laterCount b+2) (splice 0 rank w)
        (splice 0 (firstCap b d) hist) := by
  classical
  have hend : R.live (laterCount b+1) = R.final := by simp [Process.live]
  rw [← hend]
  refine bill_with_exit_terminal (laterCount b+1) 0 (Nat.zero_le _) w hist
    rank (firstCap b d) R.live R.lost (R.tested 0) R.rankExit
    (fun _ hi => R.next_sub (Nat.le_of_lt_succ hi))
    (fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)) hcap ?_ ?_ ?_ ?_ ?_
  · rw [Process.live,ite_eq_left (Nat.zero_le _)]
    exact R.kept_sub 0
  · intro I hI
    obtain ⟨hI,hnot⟩ := mem_filter.mp hI
    refine mem_sdiff.mpr ⟨hI,?_⟩
    rw [Process.live,ite_eq_left (Nat.zero_le _)]
    exact fun hkeep => hnot ((mem_filter.mp hkeep).2 le_rfl)
  · intro i hi
    omega
  · intro i hi
    omega
  · intro k
    have hle := P1_7_4.massQ_mono (R.tested_sub 0) k
    have hinit : (mass R.parents k : ℚ) ≤ initialCap b k := by exact_mod_cast R.init_mass k
    unfold firstCap
    by_cases hk : k = 2
    · subst k
      have hp : (d:ℚ)+mass R.parents 2 ≤ initialCap b 2 := by exact_mod_cast hparent
      change massQ (R.tested 0) 2 ≤ (initialCap b 2:ℚ) - (if (2:Fin 4)=2 then (d:ℚ) else 0)
      simp only [if_true]
      change massQ (R.tested 0) 2 ≤ (mass R.parents 2:ℚ) at hle
      linarith only [hp,hle]
    · simp only [hk,if_false,sub_zero]
      change massQ (R.tested 0) k ≤ (initialCap b k:ℚ)
      exact hle.trans hinit

theorem process_bill {b : Band} {u del} {M : AnchorModel u del}
    {Γ} {F : AnchoredFamily M Γ} {rows} {pairs : HighCore82258.Pairs b (FrontCore82258.effectiveHeight M).toNat rows}
    (R : Process pairs) (estimate : PairedMass) (src : Source b M F rows)
    (hw : InBand b (FrontCore82258.effectiveHeight M)) (rank : Mass) (w : ℕ → Mass) (d : ℕ)
    (hparent : d+mass R.parents 2 ≤ initialCap b 2) :
    ((∑ i ∈ range (laterCount b+1),dotQ (w i) (massQ (R.lost i))) +
      dotQ rank (massQ R.rankExit)) +
      dotQ (running (splice 0 rank w) (laterCount b+2)) (massQ R.final) ≤
      weightedBill (laterCount b+2) (splice 0 rank w)
        (splice 0 (firstCap b d) (history b)) :=
  process_bill_with R rank w (history b)
    (fun _ hi => R.cap_live estimate src hw (Nat.le_of_lt_succ hi)) d hparent

theorem joint_rank_and_seed {b : Band} {u del} {M : AnchorModel u del}
    {Γ} (F : AnchoredFamily M Γ) {rows} {pairs : HighCore82258.Pairs b (FrontCore82258.effectiveHeight M).toNat rows}
    (R : Process pairs) (estimate : PairedMass) (src : Source b M F rows)
    (hw : InBand b (FrontCore82258.effectiveHeight M)) (hcount : HighCore82258_3.FixedCount)
    (tau pivot : ℚ) (htau : 0 ≤ tau) (htau' : tau ≤ 1)
    (hcharge : 0 ≤ rankCharge b tau pivot 1)
    (hsmall : (rankMass b 2).floor.toNat+2 < p)
    (hrank : ∀ k, 0 ≤ rankCharge b tau pivot k)
    (hshare : ((p+1:ℕ):ℚ) ≤ rankCharge b tau pivot 2)
    (marks : ℕ → Finset K) (w : ℕ → Mass) (extra : ℕ → ℚ)
    (hloc : ∀ i < laterCount b+1,
      ((marks i).card:ℚ) ≤ dotQ (w i) (massQ (R.lost i))+extra i)
    (d : ℕ) (seed : Finset K) (hparent : d+mass R.parents 2 ≤ initialCap b 2)
    (hseed : seed.card ≤ (p+1)*d+initialE b) :
    let n := laterCount b+1
    ((((range n).biUnion marks ∪ rankMarks F R).card : ℚ)+seed.card) +
      dotQ (running (splice 0 (rankCharge b tau pivot) w) (n+1)) (massQ R.final) ≤
      weightedBill (n+1) (splice 0 (rankCharge b tau pivot) w)
        (splice 0 (rankMass b) (history b)) +
      rankRounding b tau pivot + (∑ i ∈ range n,extra i) + initialE b := by
  classical
  let n := laterCount b+1
  have hsum := sum_le_sum (fun i (hi:i ∈ range n) => hloc i (mem_range.mp hi))
  rw [sum_add_distrib] at hsum
  have hc : (((range n).biUnion marks ∪ rankMarks F R).card:ℚ) ≤
      ∑ i ∈ range n,((marks i).card:ℚ) + (rankMarks F R).card := by
    exact_mod_cast (card_union_le ((range n).biUnion marks) (rankMarks F R)).trans
      (Nat.add_le_add_right card_biUnion_le _)
  have hr := rank_marks_le F R estimate src hw hcount tau pivot htau htau' hcharge hsmall
  have hbill := process_bill R estimate src hw (rankCharge b tau pivot) w d hparent
  rw [first_bill b n _ _ d hrank] at hbill
  have hseed' : (seed.card:ℚ) ≤ ((p+1:ℕ):ℚ)*d+initialE b := by exact_mod_cast hseed
  have hpay := mul_le_mul_of_nonneg_right hshare (show 0 ≤ (d:ℚ) by positivity)
  dsimp only
  linarith only [hsum,hc,hr,hbill,hseed',hpay]

#print axioms disjoint_mass
#print axioms first_bill
#print axioms process_bill
#print axioms joint_rank_and_seed
end
end KoalaSeedParent
