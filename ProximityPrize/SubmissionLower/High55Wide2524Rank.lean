import ProximityPrize.SubmissionLower.High55Wide2524PrefixProcess

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace High55Wide2524JointRank

open Polynomial Finset
open High55Wide2524 (Band AnchorModel AnchoredFamily InBand K p degreeAt finish gap blockLength agreement fees)
open High55Wide2524_3 (Process PairedMass rankMass fixedFee OnParent fixed_zero laterCount
  stopIndex stop_eq history FixedCount seedLimit)
open P1_7_4 (Mass massQ massQ_mono massQ_nonneg dotQ dotQ_mono_mass ODEGuard rank_equation
  weightedBill running)
open K1_14_2_2 (mass ODECaps dual)
open High50Nonlinear (remainder bill_after_exit fixed_fee_quadratic charge)
open scoped Classical

noncomputable def rankMarks {b : Band} {h rows} {pairs : High55Wide2524.Pairs b h rows}
    {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) (R : Process pairs) : Finset K :=
  Γ.filter fun γ => ∃ I ∈ R.rankExit, OnParent F I γ

private theorem nat_le_floor_of_le {m : ℕ} {q : ℚ} (h : (m : ℚ) ≤ q) :
    m ≤ q.floor.toNat := by
  exact Int.toNat_le_toNat (Rat.le_floor_iff.mpr (by exact_mod_cast h))

private theorem after_exit {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows} {pairs : High55Wide2524.Pairs b M.overhead.toNat rows}
    (R : Process pairs) (est : PairedMass) (src : High55Wide2524.Source b M F rows)
    (hw : InBand b M.overhead) (w : ℕ → Mass) :
    (∑ i ∈ range (laterCount b+1), dotQ (w i) (massQ (R.lost i))) ≤
      weightedBill (laterCount b+1) w (remainder (stopIndex b) (history b) (rankMass b) (massQ R.rankExit)) := by
  let E := R.tested (stopIndex b)
  let S := R.rankExit
  have hS : S ⊆ E := Finset.filter_subset _ _
  have hlate (i : ℕ) (hs : stopIndex b ≤ i) (hi : i < laterCount b+1) : R.live i ⊆ E \ S := by
    have hsub : R.live i ⊆ R.live (stopIndex b) := by
      induction hs with
      | refl => exact Subset.refl _
      | @step j _ ih => exact (R.next_sub (by omega)).trans (ih (by omega))
    intro I hI
    have hm := hsub hI
    rw [Process.live, ite_eq_left R.sched.stop_le] at hm
    obtain ⟨hE,hdual⟩ := mem_filter.mp hm
    refine mem_sdiff.mpr ⟨hE, ?_⟩
    intro he
    exact (mem_filter.mp he).2 (hdual le_rfl)
  refine bill_after_exit (laterCount b+1) (stopIndex b) w (history b) (rankMass b)
    R.live R.lost E S (fun _ hi => R.next_sub (by omega)) (fun _ hi => R.lost_diff (by omega))
    (fun _ hi k => R.cap_live est src hw (by omega) k) ?_ hlate ?_ hS (R.rank_entry_cap est src hw)
  · intro i hi
    rw [stop_eq] at hi
    obtain rfl : i = 0 := by omega
    exact hS.trans R.rank_enter
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro I hI hs
    by_cases hstop : i < stopIndex b
    · rw [stop_eq] at hstop
      obtain rfl : i = 0 := by omega
      exact (mem_sdiff.mp (R.rank_before_loss hI)).2 (hS hs)
    · have hm := (mem_sdiff.mp (R.lost_diff (by omega) hI)).1
      exact (mem_sdiff.mp (hlate i (by omega) hi hm)).2 hs

private theorem reduce_bill {n stop : ℕ} (w hist : ℕ → Mass) (entry used real : Mass)
    (h : ∀ k, used k ≤ real k) :
    weightedBill n w (remainder stop hist entry real) ≤
      weightedBill n w (remainder stop hist entry used) := by
  unfold weightedBill
  apply sum_le_sum
  intro i _
  apply dotQ_mono_mass (fun k => sub_nonneg.mpr (le_max_left _ _))
  intro k
  unfold remainder
  split
  · exact sub_le_sub_left (h k) _
  · exact min_le_min le_rfl (sub_le_sub_left (h k) _)

/-- Count the rank exit and later cuts using their remaining section masses. -/
theorem rank_and_loss_count {b : Band} {u del} {M : AnchorModel u del} {Γ} {rows}
    {pairs : High55Wide2524.Pairs b M.overhead.toNat rows}
    (F : AnchoredFamily M Γ) (R : Process pairs) (est : PairedMass)
    (src : High55Wide2524.Source b M F rows) (hw : InBand b M.overhead) (hcount : FixedCount)
    (hsmall : capB b < p) (w : ℕ → Mass) (marks : ℕ → Finset K) (extra : ℕ → ℚ)
    (hloc : ∀ i < laterCount b+1,
      ((marks i).card : ℚ) ≤ dotQ (w i) (massQ (R.lost i)) + extra i)
    (hextra : ∑ i ∈ range (laterCount b+1), extra i ≤ seedLimit b)
    (hpay : ∀ B J : ℕ, 2 ≤ B → 1 ≤ J → B ≤ capB b → J ≤ capJ b →
        weightedBill (laterCount b+1) w
          (remainder (stopIndex b) (history b) (rankMass b) ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit b +
        charge (lambdaDegree b) (mu b) 0 0 0 B J ≤ (fees b).loss) :
    (((range (laterCount b+1)).biUnion marks ∪ rankMarks F R).card : ℚ) ≤ (fees b).loss := by
  let S := R.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨G,hG,hzero⟩ := rank_equation S (fun _ hI => R.rank_geometry hI)
    (J := mass S 1) (B := mass S 2) le_rfl le_rfl
  have hBm : B ≤ mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB₂ : 2 ≤ B := le_max_left _ _
  have hJ₁ : 1 ≤ J := le_max_left _ _
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  have hB : B ≤ capB b := hBm.trans (Nat.add_le_add_right (nat_le_floor_of_le (R.rank_cap est src hw 2)) 2)
  have hJ : J ≤ capJ b := hJm.trans (Nat.add_le_add_right (nat_le_floor_of_le (R.rank_cap est src hw 1)) 1)
  have degreeB : G.natDegree ≤ B := by
    have htop : G.coeff G.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hG.1
    have hn : (G.coeff G.natDegree).coeff (G.coeff G.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr htop
    have hp := hG.2.2 _ _ hn
    exact (Nat.le_add_left _ _).trans (hp.trans (le_max_right _ _))
  have hcaps : ODECaps G B J := ⟨hG.1,
    (le_min hG.2.1 degreeB).trans (le_max_right _ _),
    fun j i hz => (hG.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨hB₂,hJ₁,hJB,hB.trans_lt hsmall⟩
  have hcount' : (rankMarks F R).card ≤ fixedFee (finish b) B J :=
    hcount b u del M Γ F hw B J guard G hcaps _ (filter_subset _ _)
      (fun γ hγ => by
        obtain ⟨I,hI,hm⟩ := (mem_filter.mp hγ).2
        exact fixed_zero hm (hzero I hI))
  have hl : 0 ≤ lambdaDegree b := by unfold lambdaDegree; positivity
  have hm : 0 ≤ mu b := by unfold mu; positivity
  have hfee : (fixedFee (finish b) B J : ℚ) ≤ charge (lambdaDegree b) (mu b) 0 0 0 B J := by
    have h := fixed_fee_quadratic (lambdaDegree b) (mu b) hl hm hJB
    have heq : 4*(lambdaDegree b)*B*J + (mu b)*J - 2*(lambdaDegree b)*(J : ℚ)^2 + (B : ℚ)^2+1 =
        charge (lambdaDegree b) (mu b) 0 0 0 B J := by unfold charge; ring
    dsimp only at h
    rw [heq] at h
    simpa only [fixedFee, lambdaDegree, mu, mul_assoc] using h
  have hused : ∀ k : Fin 4, (![0,(J : ℚ)-1,(B : ℚ)-2,0] : Mass) k ≤ massQ S k := by
    intro k
    fin_cases k
    · exact massQ_nonneg _ _
    · change (J : ℚ)-1 ≤ (mass S 1 : ℚ)
      have h : (J : ℚ) ≤ (mass S 1 : ℚ)+1 := by exact_mod_cast hJm
      linarith only [h]
    · change (B : ℚ)-2 ≤ (mass S 2 : ℚ)
      have h : (B : ℚ) ≤ (mass S 2 : ℚ)+2 := by exact_mod_cast hBm
      linarith only [h]
    · exact massQ_nonneg _ _
  let n := laterCount b+1
  have hc : (((range n).biUnion marks ∪ rankMarks F R).card : ℚ) ≤
      ((range n).biUnion marks).card + (rankMarks F R).card := by
    exact_mod_cast card_union_le ((range n).biUnion marks) (rankMarks F R)
  have hsum : (((range n).biUnion marks).card : ℚ) ≤ ∑ i ∈ range n, ((marks i).card : ℚ) := by
    exact_mod_cast (card_biUnion_le : ((range n).biUnion marks).card ≤ ∑ i ∈ range n, (marks i).card)
  have hloc' := sum_le_sum (fun i (hi : i ∈ range n) => hloc i (mem_range.mp hi))
  rw [sum_add_distrib] at hloc'
  have hr := (Nat.cast_le.mpr hcount').trans hfee
  have hbill := (after_exit R est src hw w).trans (reduce_bill w (history b) (rankMass b) _ _ hused)
  have hf := hpay B J hB₂ hJ₁ hB hJ
  linarith only [hc,hsum,hloc',hr,hbill,hextra,hf]

#print axioms rank_and_loss_count
end High55Wide2524JointRank
