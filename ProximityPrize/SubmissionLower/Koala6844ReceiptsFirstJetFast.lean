import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetIndex
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetRank

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators

private theorem chooseThree_eq_choose (n : Nat) : chooseThree n = n.choose 3 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  simp only [chooseThree, show 3=2+1 by decide, Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.factorial_succ, Nat.factorial_zero, Nat.sub_zero,Nat.mul_one]
  norm_num
  ac_rfl

private theorem chooseThree_sum (n : Nat) : (∑ i ∈ Finset.range n, chooseTwo i) = chooseThree n := by
  induction n with
  | zero => simp [chooseThree]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,chooseThree_eq_choose,chooseThree_eq_choose,
      show chooseTwo n = n.choose 2 by exact (Nat.choose_two_right n).symm]
    rw [Nat.add_comm]
    exact (Nat.choose_succ_succ' n 2).symm

private theorem range_difference (sums f : Nat → Nat)
    (hp : ∀ n, sums n = ∑ i ∈ Finset.range n, f i) (lo len : Nat) :
    (∑ i ∈ Finset.range len, f (lo+i)) = sums (lo+len)-sums lo := by
  rw [hp,hp,Finset.sum_range_add,Nat.add_sub_cancel_left]

def closedFirstJetWindow (cut u lo len : Nat) : Nat × Nat :=
  let hi := lo+len
  let first := chooseTwo hi-chooseTwo lo
  let second := squares hi-squares lo
  let orderTwo := chooseThree hi-chooseThree lo
  ⟨len*((u+1)*cut)+(u+1)*first+degree*orderTwo,
   cut*first+second+len*(degree*chooseTwo (u+1))⟩

theorem firstJetWindow_closed (cut u lo len : Nat) (h : ∀ i < len, lo+i ≤ u) :
    (∑ i ∈ Finset.range len, firstJetAffineRow cut u false (lo+i)) =
      ((closedFirstJetWindow cut u lo len).1 : Int)-(closedFirstJetWindow cut u lo len).2 := by
  let pos r := (u+1)*cut+(u+1)*r+degree*chooseTwo r
  let neg r := cut*r+r^2+degree*chooseTwo (u+1)
  have hPoint (i : Nat) (hi : i < len) :
      firstJetAffineRow cut u false (lo+i) = (pos (lo+i) : Int)-(neg (lo+i) : Int) := by
    have hb := h i hi
    have hc : chooseTwo (lo+i) ≤ chooseTwo (u+1) := by
      simp only [chooseTwo_eq_sum_range]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    simp only [firstJetAffineRow,pos,neg,ite_false,Bool.false_eq_true]
    push_cast [Nat.cast_sub hb,Nat.cast_sub hc]
    ring
  have hwindow :
      (∑ i ∈ Finset.range len, firstJetAffineRow cut u false (lo+i)) =
        ∑ i ∈ Finset.range len, ((pos (lo+i) : Int)-(neg (lo+i) : Int)) :=
    Finset.sum_congr rfl (fun i hi => hPoint i (Finset.mem_range.mp hi))
  have hp : (∑ i ∈ Finset.range len, pos (lo+i)) = (closedFirstJetWindow cut u lo len).1 := by
    unfold pos closedFirstJetWindow
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,←Finset.mul_sum]
    rw [range_difference chooseTwo (fun i => i) chooseTwo_eq_sum_range lo len,
      range_difference chooseThree chooseTwo (fun n => (chooseThree_sum n).symm)]
    rfl
  have hn : (∑ i ∈ Finset.range len, neg (lo+i)) = (closedFirstJetWindow cut u lo len).2 := by
    unfold neg closedFirstJetWindow
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,←Finset.mul_sum]
    rw [range_difference chooseTwo (fun i => i) chooseTwo_eq_sum_range lo len,
      range_difference squares (fun i => i^2) squares_eq_sum_range]
    rfl
  rw [hwindow,Finset.sum_sub_distrib]
  simpa only [Nat.cast_sum] using congrArg₂ (fun a b : Nat => (a : Int)-b) hp hn


def closedLeadingColumns (cut slope : Nat) : Nat :=
  if cut = 0 then 0 else
    let cap := (cut-1)/degree
    let turn := degree-(cut-1)%degree
    let begin := min turn (min (slope+1) (cap+1))
    let finish := min slope (cap+1)+1
    let lo := closedFirstJetWindow cut cap 0 begin
    let hi := closedFirstJetWindow cut (cap+1) turn (finish-turn)
    (lo.1+hi.1)-(lo.2+hi.2)

theorem closedLeadingColumns_eq (cut slope : Nat) (hB : slope < degree) :
    (closedLeadingColumns cut slope : Int) = firstJetAffineColumns cut slope false := by
  by_cases hcut : cut = 0
  · simp [closedLeadingColumns,firstJetAffineColumns,hcut]
  · let cap := (cut-1)/degree
    let turn := degree-(cut-1)%degree
    let begin := min turn (min (slope+1) (cap+1))
    let finish := min slope (cap+1)+1
    let lo := closedFirstJetWindow cut cap 0 begin
    let hi := closedFirstJetWindow cut (cap+1) turn (finish-turn)
    have hl : (∑ i ∈ Finset.range begin, firstJetAffineRow cut cap false i) =
        (lo.1 : Int)-lo.2 := by
      simpa only [lo,Nat.zero_add] using firstJetWindow_closed cut cap 0 begin (by
        intro i hi
        have h0 : begin ≤ cap+1 := (min_le_right _ _).trans (min_le_right _ _)
        omega)
    have hh : (∑ i ∈ Finset.range (finish-turn), firstJetAffineRow cut (cap+1) false (turn+i)) =
        (hi.1 : Int)-hi.2 :=
      firstJetWindow_closed cut (cap+1) turn (finish-turn) (by
        intro i hi
        have h0 : finish ≤ cap+2 := Nat.add_le_add_right (min_le_right _ _) 1
        omega)
    have hexact : firstJetAffineColumns cut slope false = (lo.1 : Int)-lo.2 + ((hi.1 : Int)-hi.2) := by
      rw [firstJetAffineColumns_eq_interval_sum cut slope false hcut]
      change (∑ i ∈ Finset.range begin, firstJetAffineRow cut cap false i) +
        (∑ i ∈ Finset.range (finish-turn), firstJetAffineRow cut (cap+1) false (turn+i)) = _
      rw [hl,hh]
    have hnonneg : 0 ≤ firstJetAffineColumns cut slope false := by
      rw [← auxiliaryFirstJetIndex_card cut slope (slopeColumnCap cut slope) hB le_rfl]
      positivity
    have hcast : (lo.2 : Int)+hi.2 ≤ (lo.1 : Int)+hi.1 := by rw [hexact] at hnonneg; omega
    have hsub : lo.2+hi.2 ≤ lo.1+hi.1 := by exact_mod_cast hcast
    unfold closedLeadingColumns
    rw [ite_eq_right hcut]
    change (((lo.1+hi.1)-(lo.2+hi.2) : Nat) : Int) = _
    rw [Nat.cast_sub hsub,hexact]
    push_cast
    ring

def leadingRankPositive (m s : Nat) : Nat :=
  let k := min s (m/2)
  6*(s+1)*m*(m+1) + 6*(m+2*s+3)*k*(k+1)

def leadingRankNegative (m s : Nat) : Nat :=
  let k := min s (m/2)
  12*(m+1)*(s+1)*k + 4*k*(k+1)*(2*k+1)

def closedLeadingRank (m s : Nat) : Nat := leadingRankPositive m s-leadingRankNegative m s

theorem closedLeadingRank_eq (m s : Nat) :
    (closedLeadingRank m s : Int) = firstJetRankSlopeTwelve m s := by
  let P := leadingRankPositive m s
  let N := leadingRankNegative m s
  have hexact : firstJetRankSlopeTwelve m s = (P : Int)-N := by
    unfold firstJetRankSlopeTwelve firstJetRankTwelve P N leadingRankPositive leadingRankNegative
    push_cast
    ring
  have hnonneg : 0 ≤ firstJetRankSlopeTwelve m s := by
    let src : SourceShape := ⟨m,s,0,m+s,m+s,0,1,0⟩
    have h := auxiliaryFirstJetRankTwelve_eq src 0 rfl (Nat.zero_le _) (Nat.le_refl (m+s))
    change 12*(auxiliaryRankSlice src 0 : Int) = firstJetRankSlopeTwelve m s at h
    rw [← h]
    positivity
  have hsub : N ≤ P := by
    have hcast : (N : Int) ≤ P := by rw [hexact] at hnonneg; omega
    exact_mod_cast hcast
  change ((P-N : Nat) : Int) = _
  rw [Nat.cast_sub hsub,hexact]

def closedAuxContribution (shape : FirstJetShape) (room j : Nat) : Int :=
  let cut := firstJetCutoff shape room
  12*(closedLeadingColumns (cut-(j+1)*(degree+poleWidth)) shape.s : Int) -
    if j+1 < shape.m then (nodes : Int)*(closedLeadingRank (shape.m-(j+1)) shape.s : Int)
    else 0

theorem closedAuxContribution_eq (shape : FirstJetShape) (room j : Nat) (hB : shape.s < degree) :
    closedAuxContribution shape room j = firstJetAuxContribution shape room j := by
  simp only [closedAuxContribution,firstJetAuxContribution,closedLeadingColumns_eq _ _ hB,
    closedLeadingRank_eq]

def closedAuxWindow (shape : FirstJetShape) (room start len : Nat) : Int :=
  ((List.range' start len).map (closedAuxContribution shape room)).sum

theorem closedAuxWindow_eq (shape : FirstJetShape) (room start len : Nat) (hB : shape.s < degree) :
    closedAuxWindow shape room start len = ((List.range' start len).map (firstJetAuxContribution shape room)).sum := by
  unfold closedAuxWindow
  have h : closedAuxContribution shape room = firstJetAuxContribution shape room :=
    funext fun j => closedAuxContribution_eq shape room j hB
  rw [h]

theorem firstJetWindow_of_closed (shape : FirstJetShape) (room start len : Nat)
    (value : Int) (hB : shape.s < degree) (h : closedAuxWindow shape room start len = value) :
    ((List.range' start len).map (firstJetAuxContribution shape room)).sum = value :=
  (closedAuxWindow_eq shape room start len hB).symm.trans h

end ProximityPrize.SubmissionLower.Koala6844Receipts
