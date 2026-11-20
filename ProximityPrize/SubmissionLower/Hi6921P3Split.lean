import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3Split
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace H21_3

noncomputable section

open K21 H21 Polynomial
open scoped BigOperators Classical

/-- Choose a nonzero cheap row and a layered row avoiding its moving
positive-V factors at the reserved, rather than the full, cutoff. -/
def c1 : Prop :=
  ∀ (h : ℕ) (rows : Banks) (i : Fin 4), 3555 ≤ h → h ≤ 32872 →
    (∀ s ∈ [cheapShape i, layeredShape i],
      (∀ W, ∀ P ∈ rows s W, RowCaps P s) ∧
      LeadingFilter h rows s ∧ SeedShift h rows s ∧ RankFloor h rows s) →
    Nonempty (BufferedPair h rows i)

/-- From the initial two equations, separate the low projections and retain
height-two parents dominant and separable over both coordinate planes. -/
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) (P Q : Jet),
    P ≠ 0 → Q ≠ 0 → RowCaps P (cheapShape 0) → RowCaps Q (layeredShape 0) →
    NoMovingCommon P Q →
    (∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover M F)

/-- Seed-shift vanishing on a doubly dominant parent implies contact
in both jet variables in each geometric generic-seed fibre. -/
def c3 : Prop :=
  ∀ (h : ℕ) (rows : Banks) (s : Shape) (q : Surface),
    0 < h → s.m*180169 < p → Parent q → SeedShift h rows s → BankVanishes rows s q →
    ∀ W < s.m*180169, ∀ P ∈ rows s W, OrderAt q P (contactPower h s W)

/-- The shared ordinary gcd and the residual local intersection lengths
bound the aggregate masses of a set of parents that pass a paired test. -/
def c4 : Prop :=
  ∀ (h : ℕ) (rows : Banks) (i : Fin 4) (B : BufferedPair h rows i)
    (qs : Finset Surface),
    (∀ q ∈ qs, Parent q ∧ Compatible B.cheap B.layered q ∧
      OrderAt q B.cheap (reserve i + 1) ∧ OrderAt q B.layered (reserve i + 1)) →
    MassCap qs (seedMassCap i) (ordinateMassCap i) (mixedMassCap i)

/-- A first failed test gives a proper curve cut whose moving seed image
and constant seed images have the respective local degree budgets. -/
def c5 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    3555 ≤ M.overhead → M.overhead ≤ 32872 →
    ∀ (rows : Banks), JetSource M F rows →
    ∀ (pairs : ∀ i : Fin 4, BufferedPair M.overhead.toNat rows i)
      (i : Fin 5) (q : Surface), Parent q → ¬ PassStage rows pairs i q →
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree (cutShape i) {q} ∧
      (C.points.card : ℚ) ≤ constantDegree (cutShape i) {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → C.Covers (M.label γ)

/-- Fixed first-order equation tariff for a single common word, including
ordinary factors and the singular V-separant class. -/
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) (d b j : ℕ),
    2 ≤ d → d < 180169 → 180169^2 ≤ 262144*d → 2 ≤ b → b < p → 1 ≤ j → j ≤ b →
    (∀ γ ∈ Γ, (F.scalar γ).natDegree ≤ d) →
    ∀ G : JetPlane, G ≠ 0 → JetCaps G b j →
    ∀ T ⊆ Γ, (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ odePrice d b j

/-- Descend the reduced distinct Y-projection product and transfer contact
to divisibility of the leading V coefficient. -/
def c7 : Prop :=
  ∀ qs : Finset Surface, qs.Nonempty → (∀ q ∈ qs, Parent q) →
    ∃ f : Equation, ProjectedProduct qs f

/-- At the terminal full-bank rank floor, the leading-position restriction
that five distinct Y values would force is impossible. -/
def c8 : Prop :=
  ∀ (h : ℕ) (rows : Banks), 3555 ≤ h → h ≤ 32872 →
    (∀ W, ∀ P ∈ rows fullShape W, RowCaps P fullShape) →
    LeadingFilter h rows fullShape → RankFloor h rows fullShape →
    ∃ W < fullShape.m*180169, ∃ P ∈ rows fullShape W, P ≠ 0 ∧
      P.leadingCoeff.natDegree < 5 * (contactPower h fullShape W - P.natDegree)


private theorem pair_membership {w : ℤ} (hw : 3555 ≤ w) (i : Fin 4) {s : Shape}
    (hs : s ∈ [cheapShape i, layeredShape i]) : s ∈ scheduled w := by
  have hn : ¬ w ≤ 3554 := by omega
  simp at hs
  rcases hs with rfl | rfl <;> fin_cases i <;>
    simp [scheduled, hn, cheapShape, layeredShape]

private theorem full_membership {w : ℤ} (hw : 3555 ≤ w) : fullShape ∈ scheduled w := by
  have hn : ¬ w ≤ 3554 := by omega
  simp [scheduled, hn, fullShape]

private theorem source_data {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (h : JetSource M F rows) {s : Shape}
    (hs : s ∈ scheduled M.overhead) :
    (∀ W, ∀ P ∈ rows s W, RowCaps P s) ∧
    LeadingFilter M.overhead.toNat rows s ∧ SeedShift M.overhead.toNat rows s ∧
    RankFloor M.overhead.toNat rows s :=
  ⟨h.shape s hs, h.leading s hs, h.shift s hs, h.floor_bound s hs⟩

private theorem buffered_power (h : ℕ) (hl : 3555 ≤ h) (hu : h ≤ 32872)
    (i : Fin 4) (s : Shape) (hs : s ∈ [cheapShape i, layeredShape i]) :
    reserveCutoff h s i < s.m*180169 ∧ contactPower h s (reserveCutoff h s i) = reserve i+1 := by
  simp at hs
  have hfit : 2*h*reserve i ≤ s.m*180169-1 := by
    rcases hs with rfl | rfl <;> fin_cases i <;>
      norm_num [cheapShape, layeredShape, reserve] <;> omega
  have hpos : 0 < s.m := by
    rcases hs with rfl | rfl <;> fin_cases i <;> decide
  have hdiff : s.m*180169-1 - reserveCutoff h s i = 2*h*reserve i := by
    unfold reserveCutoff
    omega
  constructor
  · unfold reserveCutoff
    omega
  · rw [contactPower, hdiff, Nat.mul_div_cancel_left _ (by omega)]
    omega

private theorem paired_mass_of_test (contact : c3) (massBound : c4) {u del}
    {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {rows : Banks}
    (hJ : JetSource M F rows) (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32872)
    (pairs : ∀ i : Fin 4, BufferedPair M.overhead.toNat rows i)
    (i : Fin 4) (S : Finset Surface) (hS : ∀ q ∈ S, Parent q)
    (hpass : ∀ q ∈ S, PassStage rows pairs i.castSucc q) :
    MassCap S (seedMassCap i) (ordinateMassCap i) (mixedMassCap i) := by
  apply massBound _ _ i (pairs i) S
  intro q hq
  have hP : BankVanishes rows (cheapShape i) q ∧ BankVanishes rows (layeredShape i) q ∧
      Compatible (pairs i).cheap (pairs i).layered q := by
    simpa only [PassStage, Fin.val_castSucc, dite_eq_left i.isLt] using hpass q hq
  have hcontact (s : Shape) (hs : s ∈ [cheapShape i, layeredShape i])
      (hv : BankVanishes rows s q) (P : Jet)
      (hP : P ∈ rows s (reserveCutoff M.overhead.toNat s i)) : OrderAt q P (reserve i+1) := by
    have hp : s.m*180169 < p := by
      simp at hs
      rcases hs with rfl | rfl <;> fin_cases i <;> decide
    have hw := buffered_power M.overhead.toNat (by omega) (by omega) i s hs
    rw [← hw.2]
    exact contact _ rows s q (by omega) hp (hS q hq)
      (hJ.shift s (pair_membership hl i hs)) hv _ hw.1 P hP
  exact ⟨hS q hq, hP.2.2,
    hcontact _ (by simp) hP.1 _ (pairs i).cheap_mem,
    hcontact _ (by simp) hP.2.1 _ (pairs i).layered_mem⟩

private theorem terminal_shape_data {w : ℤ} (hw : 3555 ≤ w) :
    terminalShape w ∈ scheduled w ∧ (terminalShape w).m = fullShape.m ∧
      (terminalShape w).B = fullShape.B ∧ (terminalShape w).J = fullShape.J ∧
      (terminalShape w).U ≤ fullShape.U ∧ True := by
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
    (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32872)
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

-- Keep the height symbolic while transferring the cutoff and the exponent.
private theorem split_terminal_divisibility {w : ℤ} {rows : Banks} {f : Equation}
    (hm : (band w).multiplicity = fullShape.m)
    (hsub : ∀ W, rows (terminalShape w) W ≤ rows fullShape W)
    (hfull : ∀ W < fullShape.m * 180169, ∀ P ∈ rows fullShape W, P ≠ 0 →
      f ^ (contactPower w.toNat fullShape W - P.natDegree) ∣ P.leadingCoeff) :
    TerminalDivisibility w rows f := by
  intro W hW P hP hn
  rw [hm] at hW
  rw [terminal_power hm]
  exact hfull W hW P (hsub W hP) hn


end
end H21_3
end High_K1_14_3Split
