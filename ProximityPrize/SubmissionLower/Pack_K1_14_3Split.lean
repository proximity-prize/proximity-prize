import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Numeric2Aux
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) (d b j : ℕ),
    2 ≤ d → d < 180265 → 180265^2 ≤ 262144*d → 2 ≤ b → b < p → 1 ≤ j → j ≤ b →
    (∀ γ ∈ Γ, (F.scalar γ).natDegree ≤ d) →
    ∀ G : JetPlane, G ≠ 0 → JetCaps G b j →
    ∀ T ⊆ Γ, (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ odePrice d b j
def c7 : Prop :=
  ∀ qs : Finset Surface, qs.Nonempty → (∀ q ∈ qs, Parent q) →
    ∃ f : Equation, ProjectedProduct qs f
private theorem pair_membership {w : ℤ} (hw : 3555 ≤ w) (i : Fin 4) {s : Shape}
    (hs : s ∈ [cheapShape i, layeredShape i]) : s ∈ scheduled w := by
  have hn : ¬ w ≤ 3554 := by omega
  simp at hs
  rcases hs with rfl | rfl <;> fin_cases i <;>
    simp [scheduled, hn, cheapShape, layeredShape]
private theorem full_membership {w : ℤ} (hw : 3555 ≤ w) : fullShape ∈ scheduled w := by
  have hn : ¬ w ≤ 3554 := by omega
  simp [scheduled, hn, fullShape]
private theorem buffered_power (h : ℕ) (hl : 3555 ≤ h) (hu : h ≤ 32680)
    (i : Fin 4) (s : Shape) (hs : s ∈ [cheapShape i, layeredShape i]) :
    reserveCutoff h s i < s.m*180265 ∧ contactPower h s (reserveCutoff h s i) = reserve i+1 := by
  simp at hs
  have hfit : 2*h*reserve i ≤ s.m*180265-1 := by
    rcases hs with rfl | rfl <;> fin_cases i <;>
      norm_num [cheapShape, layeredShape, reserve] <;> omega
  have hpos : 0 < s.m := by
    rcases hs with rfl | rfl <;> fin_cases i <;> decide
  have hdiff : s.m*180265-1 - reserveCutoff h s i = 2*h*reserve i := by
    unfold reserveCutoff
    omega
  constructor
  · unfold reserveCutoff
    omega
  · rw [contactPower, hdiff, Nat.mul_div_cancel_left _ (by omega)]
    omega
private theorem terminal_shape_data {w : ℤ} (hw : 3555 ≤ w) :
    terminalShape w ∈ scheduled w ∧ (terminalShape w).m = fullShape.m ∧
      (terminalShape w).B = fullShape.B ∧ (terminalShape w).J = fullShape.J ∧
      (terminalShape w).U ≤ fullShape.U ∧ (band w).yBound = 4 := by
  have hn : ¬ w ≤ 3554 := by omega
  constructor
  · simp [scheduled, hn]
  · unfold terminalShape band fullShape
    simp only [hn, ite_false]
    split_ifs <;> decide
private theorem terminal_power {w : ℤ} (hm : (band w).multiplicity = fullShape.m) (W j : ℕ) :
    forcedPower w W j = contactPower w.toNat fullShape W - j := by
  unfold forcedPower contactPower
  rw [hm]
private theorem paid_complement (ode : c6) {u del}
    {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32680)
    (initial : InitialCover M F) (lost : SeedCover)
    (hd : lost.curve.totalDegree ≤ 54375137) (he : lost.points.card ≤ 26769366519)
    (kept : Finset K)
    (hcover : ∀ γ ∈ Γ, (∃ q ∈ initial.parents, MarkOn M F q γ) →
      γ ∈ kept ∨ lost.Covers (M.label γ)) :
    (Γ \ kept).card ≤ highPrefix M.overhead := by
  classical
  let T := Γ \ kept
  let book : Fin 6 → Finset K :=
    ![T.filter (fun γ => initial.seeds.Covers (M.label γ)),
      T.filter (fun γ => atX (F.scalar γ) ∈ initial.ordinates),
      T.filter (fun γ => fixedAt initial.lowJet (F.scalar γ) = 0),
      T.filter (fun γ => fixedAt initial.fixedCheap (F.scalar γ) = 0),
      T.filter (fun γ => fixedAt initial.fixedLayered (F.scalar γ) = 0),
      T.filter (fun γ => lost.Covers (M.label γ))]
  have hbook : T ⊆ Finset.univ.biUnion book := by
    intro γ hγ
    have hΓ : γ ∈ Γ := (Finset.mem_sdiff.mp hγ).1
    rcases initial.cover γ hΓ with h | h | h | h | h | h
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨3, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨4, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, h⟩⟩
    · have hh := (hcover γ hΓ h).resolve_left (Finset.mem_sdiff.mp hγ).2
      exact Finset.mem_biUnion.mpr ⟨5, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hh⟩⟩
  have hzero : (book 0).card ≤ (p+1)*(381269+812+2907) + 3019828 := by
    apply (seed_count (label_injective M).injOn initial.seeds _
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)).trans
    · exact Nat.add_le_add (Nat.mul_le_mul_left _ initial.seedDegree) initial.seedPoints
    · exact initial.seedDegree.trans_lt (by decide)
  have hconst : (book 1).card ≤ 2891 := by
    refine (Finset.card_le_card_of_injOn (fun γ => atX (F.scalar γ)) ?_ ?_).trans initial.ordinateCount
    · intro γ hγ
      exact (Finset.mem_filter.mp hγ).2
    · intro x hx y hy h
      exact F.distinct (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1 (scalar_atX_injective h)
  let d := 131071 + (band M.overhead).endpoint
  obtain ⟨hw, hlo, hhi⟩ := endpoint_range M.overhead hl hu
  have hdeg : ∀ γ ∈ Γ, (F.scalar γ).natDegree ≤ d := by
    intro γ hγ
    rcases (F.mark γ hγ).scalar_degree with h | h
    · simp [h]
    · dsimp [d]
      omega
  have hode (G : JetPlane) (b j : ℕ) (hb : 2 ≤ b) (hbp : b < p) (hj : 1 ≤ j)
      (hjb : j ≤ b) (hn : G ≠ 0) (hcap : JetCaps G b j) :
      (T.filter (fun γ => fixedAt G (F.scalar γ) = 0)).card ≤ odePrice d b j :=
    ode u del M Γ F d b j (by dsimp [d]; omega) (by dsimp [d]; omega)
      (by dsimp [d]; omega) hb hbp hj hjb hdeg G hn hcap _
      (fun _ hγ => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hγ).1).1)
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hlow : (book 2).card ≤ odePrice d 381269 60998 :=
    hode _ _ _ (by decide) (by decide) (by decide) (by decide)
      initial.lowJet_ne initial.lowJet_caps
  have hcheap : (book 3).card ≤ odePrice d 63 14 :=
    hode _ _ _ (by decide) (by decide) (by decide) (by decide)
      initial.fixedCheap_ne initial.fixedCheap_caps
  have hlayer : (book 4).card ≤ odePrice d 118 24 :=
    hode _ _ _ (by decide) (by decide) (by decide) (by decide)
      initial.fixedLayered_ne initial.fixedLayered_caps
  have hloss : (book 5).card ≤ (p+1)*54375137 + 26769366519 :=
    (seed_count (label_injective M).injOn lost (hd.trans_lt (by decide))
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hd) he)
  calc
    T.card ≤ (Finset.univ.biUnion book).card := Finset.card_le_card hbook
    _ ≤ ∑ i : Fin 6, (book i).card := Finset.card_biUnion_le
    _ ≤ _ := by
      rw [Fin.sum_univ_six]
      dsimp only [d] at hlow hcheap hlayer
      have hf := endpoint_fees M.overhead hl
      change _ ≤ highPrefix M.overhead
      omega
end
end K1_14_3
end
