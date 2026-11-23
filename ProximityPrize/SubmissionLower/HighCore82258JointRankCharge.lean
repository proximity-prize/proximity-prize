import ProximityPrize.SubmissionLower.HighCore82258JointRank

set_option Elab.async false

open FrontCore82258 (effectiveHeight)

namespace HighCore82258JointRank

open Polynomial Finset
open HighCore82268JointRank (splice fixed_fee_linear)
open HighCore82258 (Band AnchorModel AnchoredFamily InBand K p degreeAt finish gap blockLength agreement)
open HighCore82258_3 (Process rankMass fixedFee OnParent fixed_zero)
open P1_7_4 (Mass massQ dotQ ODEGuard rank_equation)
open K1_14_2_2 (mass ODECaps)
open scoped Classical

noncomputable def rankMarks {b : Band} {h rows} {pairs : HighCore82258.Pairs b h rows}
    {u del} {M:AnchorModel u del} {Γ} (F:AnchoredFamily M Γ) (R:Process pairs):Finset K :=
  Γ.filter fun γ => ∃ I ∈ R.rankExit,OnParent F I γ

private theorem nat_le_floor_of_le {m : ℕ} {q : ℚ} (h : (m : ℚ) ≤ q) :
    m≤q.floor.toNat:=by
  exact Int.toNat_le_toNat (Rat.le_floor_iff.mpr (by exact_mod_cast h))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- Bound the rank marks with a fixed-count theorem valid on this family. -/
theorem rank_marks_le_with {b : Band} {u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) {rows} {pairs : HighCore82258.Pairs b (effectiveHeight M).toNat rows}
    (R : Process pairs) (fare : ℕ → ℕ → ℕ)
    (hcount : ∀ B J, ODEGuard B J → ∀ G : K1_14_2.ODE, ODECaps G B J →
      ∀ T ⊆ Γ, (∀ γ ∈ T, K1_14_2.fixedAt G (F.scalar γ) = 0) → T.card ≤ fare B J)
    (w₁ w₂ offset : ℚ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (linear : ∀ B J, ODEGuard B J → B ≤ capB b → J ≤ capJ b →
      (fare B J : ℚ) ≤ w₁*J + w₂*B + offset)
    (hsmall : (rankMass b 2).floor.toNat+2 < p) :
    ((rankMarks F R).card : ℚ) ≤ dotQ ![0,w₁,w₂,0] (massQ R.rankExit) +
      (w₁+2*w₂+offset):=by
  let S:=R.rankExit
  let B:=max 2 (mass S 2)
  let J:=max 1 (min (mass S 1) B)
  obtain ⟨G, hG, hzero⟩ := rank_equation S (fun _ hI => R.rank_geometry hI)
    (J:=mass S 1) (B:=mass S 2) le_rfl le_rfl
  have hBm:B≤ mass S 2+2:=max_le (by omega) (by omega)
  have hJm:J≤ mass S 1+1:=max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB2:2≤B:=le_max_left _ _
  have hJ1:1≤J:=le_max_left _ _
  have hJB:J≤B:=max_le (by omega) (min_le_right _ _)
  have hB:B≤ capB b:=hBm.trans (Nat.add_le_add_right (nat_le_floor_of_le (R.rank_cap 2)) 2)
  have hJ:J≤ capJ b:=hJm.trans (Nat.add_le_add_right (nat_le_floor_of_le (R.rank_cap 1)) 1)
  have degreeB : G.natDegree ≤ B := by
    have htop : G.coeff G.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hG.1
    have hn : (G.coeff G.natDegree).coeff (G.coeff G.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr htop
    have hp:=hG.2.2 _ _ hn
    exact (Nat.le_add_left _ _).trans (hp.trans (le_max_right _ _))
  have hcaps : ODECaps G B J := ⟨hG.1,
    (le_min hG.2.1 degreeB).trans (le_max_right _ _),
    fun j i hz => (hG.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard:ODEGuard B J:=⟨hB2,hJ1,hJB,hB.trans_lt hsmall⟩
  have count : (rankMarks F R).card ≤ fare B J :=
    hcount B J guard G hcaps _ (filter_subset _ _)
      (fun γ hγ => by
        obtain ⟨I,hI,hm⟩:=(mem_filter.mp hγ).2
        exact fixed_zero hm (hzero I hI))
  have hc := linear B J guard hB hJ
  have hJm' : (J:ℚ)≤(mass S 1:ℚ)+1:=by exact_mod_cast hJm
  have hBm' : (B:ℚ)≤(mass S 2:ℚ)+2:=by exact_mod_cast hBm
  have hjfee:=mul_le_mul_of_nonneg_left hJm' hw₁
  have hbfee:=mul_le_mul_of_nonneg_left hBm' hw₂
  have hdot : dotQ ![0,w₁,w₂,0] (massQ R.rankExit) =
      w₁*(mass S 1 : ℚ)+w₂*(mass S 2 : ℚ) := by
    simp [dotQ,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (hc.trans ?_)
  rw [hdot]
  linarith only [hjfee,hbfee]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- Bound the actual rank-exit marks by the mass charged to the rank bin. -/
theorem rank_marks_le {b : Band} {u del} {M : AnchorModel u del} {Γ}
    (F:AnchoredFamily M Γ) {rows} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows}
    (R:Process pairs) (estimate:HighCore82258_3.PairedMass) (src:HighCore82258.Source b M F rows)
    (hw:InBand b (effectiveHeight M)) (hcount:HighCore82258_3.FixedCount) (tau pivot:ℚ) (htau:0≤tau) (htau' : tau≤1)
    (hcharge:0≤ rankCharge b tau pivot 1)
    (hsmall:(rankMass b 2).floor.toNat+2 < p) :
    ((rankMarks F R).card : ℚ) ≤ dotQ (rankCharge b tau pivot) (massQ R.rankExit) +
      rankRounding b tau pivot:=by
  have hl : 0 ≤ lambdaDegree b := by unfold lambdaDegree; positivity
  have hm : 0 ≤ mu b := by unfold mu; positivity
  have hw₂ : 0 ≤ rankCharge b tau pivot 2 := by
    change 0 ≤ 4*lambdaDegree b*(capJ b:ℚ)*(1-tau)+(capB b:ℚ)
    exact add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr htau')) (Nat.cast_nonneg _)
  have hweight : (![0,rankCharge b tau pivot 1,rankCharge b tau pivot 2,0] : Mass) =
      rankCharge b tau pivot := by
    funext k
    fin_cases k <;> rfl
  simpa only [hweight,rankRounding,add_assoc] using (rank_marks_le_with F R (fixedFee (finish b)) (hcount b u del M Γ F hw)
    (rankCharge b tau pivot 1) (rankCharge b tau pivot 2) (2*lambdaDegree b*pivot^2+1)
    hcharge hw₂ (fun B J guard hB hJ => by
      have hlin := fixed_fee_linear (lambdaDegree b) (mu b) tau pivot hl hm htau htau'
        guard.jb hB hJ
      simpa [fixedFee,rankCharge,lambdaDegree,mu,mul_assoc,add_assoc] using hlin) hsmall)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
/-- Count rank marks and the proper-cut marks with one budget. -/
theorem rank_and_loss_count_terminal {b : Band} {u del} {M : AnchorModel u del}
    {Γ} (F:AnchoredFamily M Γ) {rows}
    {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows}
    (R:Process pairs) (estimate:HighCore82258_3.PairedMass)
    (src:HighCore82258.Source b M F rows) (hw:InBand b (effectiveHeight M))
    (hcount:HighCore82258_3.FixedCount) (tau pivot:ℚ) (htau:0≤tau) (htau' : tau≤1)
    (hcharge:0≤ rankCharge b tau pivot 1)
    (hsmall:(rankMass b 2).floor.toNat+2 < p)
    (marks:ℕ→Finset K) (w:ℕ→Mass) (extra:ℕ→ℚ)
    (hloc : ∀ i < HighCore82258_3.laterCount b+1,
      ((marks i).card:ℚ)≤dotQ (w i) (massQ (R.lost i))+extra i) :
    let n:=HighCore82258_3.laterCount b+1
    let s:=HighCore82258_3.stopIndex b
    (((range n).biUnion marks ∪ rankMarks F R).card : ℚ) +
      dotQ (P1_7_4.running (splice s (rankCharge b tau pivot) w) (n+1)) (massQ R.final) ≤
      P1_7_4.weightedBill (n+1) (splice s (rankCharge b tau pivot) w)
        (splice s (rankMass b) (HighCore82258_3.history b)) +
      rankRounding b tau pivot + ∑ i ∈ range n,extra i:=by
  let n:=HighCore82258_3.laterCount b+1
  have hsum:=sum_le_sum (fun i (hi:i ∈ range n) => hloc i (mem_range.mp hi))
  rw [sum_add_distrib] at hsum
  have hsum_count : (((range n).biUnion marks).card : ℚ) ≤ ∑ i ∈ range n, ((marks i).card : ℚ) := by
    exact_mod_cast (card_biUnion_le : ((range n).biUnion marks).card ≤
      ∑ i ∈ range n,(marks i).card)
  have hrc:=rank_marks_le F R estimate src hw hcount tau pivot htau htau' hcharge hsmall
  have hbill:=process_rank_bill_terminal (F:=F) R estimate src hw (rankCharge b tau pivot) w
  have hc : (((range n).biUnion marks ∪ rankMarks F R).card : ℚ) ≤
      (((range n).biUnion marks).card:ℚ)+((rankMarks F R).card:ℚ):=by
    exact_mod_cast card_union_le ((range n).biUnion marks) (rankMarks F R)
  dsimp only
  linarith only [hsum,hsum_count,hrc,hbill,hc]

#print axioms rank_marks_le
#print axioms rank_and_loss_count_terminal

end HighCore82258JointRank
