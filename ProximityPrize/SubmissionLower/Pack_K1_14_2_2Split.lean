import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Numeric5Certificate
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def c1 : Prop :=
  ∀ P s, P ≠ 0 → RowCaps P s → Nonempty (FixedPart P s)
def c2 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) rows
    (B : RowPair M.overhead rows 0) (A : FixedPair B),
    (∀ γ ∈ Γ, jetAt B.cheap (M.label γ) (F.scalar γ) = 0 ∧
      jetAt B.layered (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover M F A.cheap.equation A.layered.equation)
def c3 : Prop :=
  ∀ (h : ℕ) (rows : Banks) (s : Shape) (I : Ideal Ambient),
    0 < h → Active I →
    (∀ W W', W ≤ W' → rows s W ≤ rows s W') →
    K1_14_3.SeedShift h rows s → bankVanishes rows s I →
    ∀ W r P, r < p → W + 2*h*r ≤ fullCutoff s → P ∈ rows s W →
      orderOn I P (r+1)
def c4 : Prop :=
  ∀ w rows (i : Fin 10) (B : RowPair w rows i) (A : FixedPair B)
    (S : Finset (Ideal Ambient)),
    0 < i.val → Fits S (budget (i.val-1)) →
    (∀ I ∈ S, Active I ∧ pairGood A I ∧
      orderOn I B.cheap ((stageAt i).reserve+1) ∧
      orderOn I B.layered ((stageAt i).reserve+1)) →
    (i.val ≤ 4 → Fits S (exitBudget i)) ∧
    Fits (S.filter dual) (budget i.val)
def c5 : Prop :=
  ∀ S : Finset (Ideal Ambient), (∀ I ∈ S, Active I ∧ ¬ dual I) →
    mass S 1 ≤ 93976 → mass S 2 ≤ 507836 →
    ∃ G : ODE, ODECaps G 507836 93976 ∧ ∀ I ∈ S, fixedOn G I
def c6 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) rows,
    M.overhead ≤ 3554 → JetSource M F rows →
    ∀ (pairs : ∀ i : Fin 10, RowPair M.overhead rows i) (n : ℕ) (I : Ideal Ambient),
    n ≤ 10 → ¬ stageTest pairs n I →
    ∃ P : Jet, RowCaps P (cutShape n) ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent M F I γ → jetAt P (M.label γ) (F.scalar γ) = 0
def c7 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ) (s : Shape)
    (I : Ideal Ambient) (P : Jet),
    s.J ≤ s.B → Active I → RowCaps P s → toJet P ∉ I →
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent M F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 →
        C.covers M F γ
theorem selectPair {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (hw : M.overhead ≤ 3554) (hsrc : JetSource M F rows)
    (hbuf : BufferedPairs M.overhead rows) (i : Fin 10) :
    Nonempty (RowPair M.overhead rows i) := by
  obtain ⟨P, hp, Q, hq, hpn, hqn, hnm⟩ := hbuf (stageAt i) (stage_mem i)
  exact ⟨⟨P, Q, hpn, hqn, hp, hq,
    hsrc.shape _ (pair_scheduled hw i (by simp [stagePair])) _ P hp,
    hsrc.shape _ (pair_scheduled hw i (by simp [stagePair])) _ Q hq, hnm⟩⟩
theorem passing_mass (h3 : c3) (h4 : c4)
    {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {rows : Banks}
    (hsrc : JetSource M F rows) (hlo : 2601 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    (i : Fin 10) (hi : 0 < i.val) (B : RowPair M.overhead rows i) (A : FixedPair B)
    (S : Finset (Ideal Ambient)) (hgeom : ∀ I ∈ S, Active I)
    (hcap : Fits S (budget (i.val-1))) :
    let R := S.filter (pairGood A)
    (i.val ≤ 4 → Fits R (exitBudget i)) ∧ Fits (R.filter dual) (budget i.val) := by
  apply h4 _ _ i B A _ hi (fits_mono (Finset.filter_subset _ _) hcap)
  intro I hI
  obtain ⟨hm, hg⟩ := Finset.mem_filter.mp hI
  have hI' := hgeom I hm
  have hcontact (s : Shape) (hs : s ∈ stagePair i) (hv : bankVanishes rows s I)
      (P : Jet) (hp : P ∈ rows s (bufferedAt M.overhead (stageAt i).reserve s)) :
      orderOn I P ((stageAt i).reserve+1) := by
    have hs' := pair_scheduled hhi i hs
    have hres : (stageAt i).reserve < p := by fin_cases i <;> decide
    have hfit := buffered_fits hhi i hs
    have hsum : bufferedAt M.overhead (stageAt i).reserve s +
        2 * M.overhead.toNat * (stageAt i).reserve ≤ fullCutoff s := by
      change fullCutoff s - 2*M.overhead.toNat*(stageAt i).reserve + _ ≤ fullCutoff s
      omega
    exact h3 _ rows s I (by omega) hI'
      (hsrc.nested s hs' s hs' rfl rfl rfl le_rfl)
      (hsrc.shift s hs') hv _ _ P hres hsum hp
  exact ⟨hI', hg, hcontact _ (by simp [stagePair]) hg.1.1 _ B.cheap_mem,
    hcontact _ (by simp [stagePair]) hg.1.2.1 _ B.layered_mem⟩
private def stay {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) (n : ℕ) (I : Ideal Ambient) : Prop :=
  if hn : n < 10 then pairGood (parts ⟨n, hn⟩) I ∧ (n = 4 → dual I)
  else bankVanishes rows full I
theorem cut_shape_valid (n : ℕ) : (cutShape n).J ≤ (cutShape n).B := by
  by_cases hn : n < 10
  · simp only [cutShape, dite_eq_left hn]
    generalize hi : (⟨n, hn⟩ : Fin 10) = i
    fin_cases i <;> decide
  · simp [cutShape, hn, full]
theorem after_four {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) (start : Finset (Ideal Ambient)) :
    ∀ n, 4 ≤ n → ∀ I ∈ timeline start (stay parts) n, dual I := by
  intro n hn I hI
  have h4 := timeline_antitone start (stay parts) hn hI
  change I ∈ (timeline start (stay parts) 3).filter (stay parts 4) at h4
  have hp := (Finset.mem_filter.mp h4).2
  simp only [stay, dite_eq_left (by decide : (4 : ℕ) < 10)] at hp
  exact hp.2 trivial
def equationFor {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) (rank : ODE) : FixedTag → ODE
  | .inl t => if t = 0 then rank else 1
  | .inr (i, false) => (parts i).cheap.equation
  | .inr (i, true) => (parts i).layered.equation
private theorem equation_caps {w rows} {pairs : ∀ i : Fin 10, RowPair w rows i}
    (parts : ∀ i : Fin 10, FixedPair (pairs i)) {rank : ODE}
    (hr : ODECaps rank 507836 93976) (t : FixedTag) :
    ODECaps (equationFor parts rank t) (tagKey t).1 (tagKey t).2 := by
  rcases t with t | ⟨i,b⟩
  · fin_cases t
    · exact hr
    · change ODECaps (1 : ODE) 1164 247
      refine ⟨one_ne_zero, by simp, ?_⟩
      intro j i h
      have hj : j = 0 := by
        by_contra hn
        simp [coeff_one, hn] at h
      subst j
      have hi : i = 0 := by
        by_contra hn
        simp [coeff_one, hn] at h
      omega
  · cases b
    · exact (parts i).cheap.equation_caps
    · exact (parts i).layered.equation_caps
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) : K1_14_2.c2 := by
  classical
  intro u del M Γ F hlo hhi rows hsrc hbuf
  let pairs (i : Fin 10) : RowPair M.overhead rows i :=
    Classical.choice (selectPair hhi hsrc hbuf i)
  let parts (i : Fin 10) : FixedPair (pairs i) :=
    ⟨Classical.choice (h1 _ _ (pairs i).cheap_ne (pairs i).cheap_caps),
     Classical.choice (h1 _ _ (pairs i).layered_ne (pairs i).layered_caps)⟩
  obtain ⟨initial⟩ := h2 u del M Γ F rows (pairs 0) (parts 0) (by
    intro γ hγ
    exact ⟨hsrc.necessary _ (pair_scheduled hhi 0 (by simp [stagePair]))
        _ (buffer_lt 0 (by simp [stagePair]) _) _ (pairs 0).cheap_mem γ hγ,
      hsrc.necessary _ (pair_scheduled hhi 0 (by simp [stagePair]))
        _ (buffer_lt 0 (by simp [stagePair]) _) _ (pairs 0).layered_mem γ hγ⟩)
  let S := timeline initial.parents (stay parts)
  have hsub (n : ℕ) : S (n+1) ⊆ S n := timeline_succ _ _ _
  have hactive (n : ℕ) : ∀ I ∈ S n, Active I :=
    fun I hI => initial.geometric I (timeline_antitone _ _ (Nat.zero_le n) hI)
  have hdual (n : ℕ) (hn : 4 ≤ n) : ∀ I ∈ S n, dual I :=
    after_four parts initial.parents n hn
  have hcap (n : ℕ) (hn : n < 10) : Fits (S n) (budget n) := by
    induction n with
    | zero => exact initial.initial_mass
    | succ n ih =>
      let i : Fin 10 := ⟨n+1, hn⟩
      let R := (S n).filter (pairGood (parts i))
      have hb := passing_mass h3 h4 hsrc hlo hhi i (by simp [i]) (pairs i) (parts i)
        (S n) (hactive n) (ih (by omega))
      have hs (I) (hI : I ∈ S (n+1)) : I ∈ R := by
        change I ∈ (S n).filter (stay parts (n+1)) at hI
        obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hI
        have hp' : pairGood (parts i) I ∧ (n+1 = 4 → dual I) := by
          simpa only [stay, dite_eq_left hn, i] using hp
        exact Finset.mem_filter.mpr ⟨hm, hp'.1⟩
      by_cases hfour : 4 ≤ n+1
      · apply fits_mono (T := R.filter dual) _ hb.2
        exact fun I hI => Finset.mem_filter.mpr ⟨hs I hI, hdual _ hfour I hI⟩
      · have hh := hb.1 (by dsimp [i]; omega)
        have he : exitBudget i = budget (n+1) := by
          simp [exitBudget, i, show n+1 ≠ 4 by omega]
        rw [he] at hh
        exact fits_mono hs hh
  let exitPool := (S 3).filter (pairGood (parts 4))
  let rankOne := exitPool.filter (fun I => ¬ dual I)
  have hexit : Fits exitPool (exitBudget 4) :=
    (passing_mass h3 h4 hsrc hlo hhi 4 (by decide) (pairs 4) (parts 4)
      (S 3) (hactive 3) (hcap 3 (by decide))).1 (by decide)
  have hrank := fits_mono (Finset.filter_subset (fun I => ¬ dual I) exitPool) hexit
  obtain ⟨rank, hrankCaps, hrankOn⟩ := h5 rankOne
    (fun I hI => ⟨hactive 3 I ((Finset.mem_filter.mp ((Finset.mem_filter.mp hI).1)).1),
      (Finset.mem_filter.mp hI).2⟩) (hrank 1) (hrank 2)
  let equation := equationFor parts rank
  let removed (n : ℕ) :=
    (S n \ S (n+1)).filter (fun I => ¬ stageTest pairs (n+1) I)
  have hstep (n : ℕ) (hn : n < 10) : ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight (cutShape (n+1)) fee) (mass (removed n))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ removed n, OnParent M F I γ) → C.covers M F γ := by
    apply combineCuts (removed n) (cutShape (n+1))
    intro I hI
    obtain ⟨hsd, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨P, hP, hproper, hzero⟩ :=
      h6 u del M Γ F rows hhi hsrc pairs (n+1) I (by omega) hf
    obtain ⟨C, hcost, hcover⟩ :=
      h7 u del M Γ F (cutShape (n+1)) I P (cut_shape_valid _)
        (hactive n I (Finset.mem_sdiff.mp hsd).1) hP hproper
    exact ⟨C, hcost, fun γ hγ hmark => hcover γ hγ hmark (hzero γ hγ hmark)⟩
  let stepCuts (n : ℕ) : CutCover := if hn : n < 10 then Classical.choose (hstep n hn) else emptyCut
  have hstepCuts (n : ℕ) (hn : n < 10) :
      (∀ fee, (stepCuts n).cost fee ≤ dot (price fee (n+1)) (mass (removed n))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ removed n, OnParent M F I γ) → (stepCuts n).covers M F γ := by
    simpa only [stepCuts, dite_eq_left hn, price, Nat.succ_ne_zero, ite_false] using
      Classical.choose_spec (hstep n hn)
  let cuts := joinCuts (Finset.range 10) stepCuts
  have hcutCap (fee : Fin 3) : cuts.cost fee ≤ feeCap fee := by
    calc
      _ ≤ ∑ n ∈ Finset.range 10, (stepCuts n).cost fee := joinCuts_cost _ _ _
      _ ≤ ∑ n ∈ Finset.range 10, dot (price fee (n+1)) (mass (S n \ S (n+1))) := by
        apply Finset.sum_le_sum
        intro n hn
        exact ((hstepCuts n (Finset.mem_range.mp hn)).1 fee).trans
          (dot_mono _ _ _ (mass_mono (Finset.filter_subset _ _)))
      _ ≤ ledger fee 10 :=
        (Nat.le_add_right _ _).trans (loss_ledger S fee le_rfl (fun i _ => hsub i) hcap)
      _ ≤ _ := ledger_cap fee
  have hfollow (γ : K) (hγ : γ ∈ Γ) (I : Ideal Ambient)
      (hI : I ∈ initial.parents) (hmark : OnParent M F I γ) (n : ℕ) (hn : n ≤ 10) :
      I ∈ S n ∨ (∃ t, fixedAt (equation t) (F.scalar γ) = 0) ∨ cuts.covers M F γ := by
    induction n with
    | zero => exact Or.inl hI
    | succ n ih =>
      rcases ih (by omega) with hm | hp
      · by_cases hout : I ∈ S (n+1)
        · exact Or.inl hout
        right
        have hfail : ¬ stay parts (n+1) I :=
          fun h => hout (Finset.mem_filter.mpr ⟨hm, h⟩)
        by_cases ht : stageTest pairs (n+1) I
        · by_cases hi : n+1 < 10
          · let i : Fin 10 := ⟨n+1, hi⟩
            have htest : pairTest (pairs i) I := by
              simpa only [stageTest, dite_eq_left hi, i] using ht
            by_cases hcheap : fixedOn (parts i).cheap.equation I
            · exact Or.inl ⟨cheapTag i, fixed_on_mark hmark hcheap⟩
            by_cases hlayer : fixedOn (parts i).layered.equation I
            · exact Or.inl ⟨layeredTag i, fixed_on_mark hmark hlayer⟩
            have hgood : pairGood (parts i) I := ⟨htest, hcheap, hlayer⟩
            have hbad : ¬ (n+1 = 4 → dual I) := by
              intro h
              exact hfail (by simpa only [stay, dite_eq_left hi, i] using And.intro hgood h)
            have he : n+1 = 4 := by
              by_contra hne
              exact hbad (fun h => (hne h).elim)
            have hd : ¬ dual I := fun hd => hbad (fun _ => hd)
            have hnj : n = 3 := by omega
            subst n
            have hp : I ∈ rankOne :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm, hgood⟩, hd⟩
            exact Or.inl ⟨rankTag, fixed_on_mark hmark (hrankOn I hp)⟩
          · exact (hfail (by simpa only [stageTest, stay, dite_eq_right hi] using ht)).elim
        · have hrem : I ∈ removed n :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hm, hout⟩, ht⟩
          exact Or.inr (joinCuts_covers (Finset.mem_range.mpr (by omega))
            ((hstepCuts n (by omega)).2 γ hγ ⟨I, hrem, hmark⟩))
      · exact Or.inr hp
  have hterminal (I : Ideal Ambient) (hI : I ∈ S 10) : bankVanishes rows full I := by
    change I ∈ (S 9).filter (stay parts 10) at hI
    simpa only [stay, dite_eq_right (by decide : ¬ (10 : ℕ) < 10)] using (Finset.mem_filter.mp hI).2
  let parents : RetainedParents rows :=
    ⟨S 10, fun I hI => (hactive 10 I hI).prime,
      fun I hI => (hactive 10 I hI).seed_finite, fun I hI => (hactive 10 I hI).seed_size,
      fun I hI => (hactive 10 I hI).jet_finite,
      fun I hI => ⟨hdual 10 (by decide) I hI, (hactive 10 I hI).jet_lt⟩, hterminal⟩
  let kept := Γ.filter (fun γ => ∃ I ∈ parents.ideals, OnParent M F I γ)
  let lost := Γ.filter (fun γ => ∃ I ∈ cuts.curves, OnParent M F I γ)
  let fixedGroups (k : ℕ × ℕ) :=
    Γ.filter (fun γ => ∃ t, tagKey t = k ∧ fixedAt (equation t) (F.scalar γ) = 0)
  have hfixed (t : FixedTag) (γ : K) (hγ : γ ∈ Γ)
      (hzero : fixedAt (equation t) (F.scalar γ) = 0) :
      ∃ k ∈ fixedKeys, γ ∈ fixedGroups k :=
    ⟨tagKey t, tagKey_mem t, Finset.mem_filter.mpr ⟨hγ, t, rfl, hzero⟩⟩
  refine ⟨{
    direct := initial.direct ∪ cuts.direct
    lost := lost
    kept := kept
    fixedGroups := fixedGroups
    parents := parents
    direct_card := ?_
    fixed_eq := ?_
    lost_subset := Finset.filter_subset _ _
    loss_cover := ?_
    kept_subset := Finset.filter_subset _ _
    kept_cover := fun γ hγ => (Finset.mem_filter.mp hγ).2
    cover := ?_
  }⟩
  · exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add initial.direct_card (hcutCap 2)).trans direct_cap)
  · intro k hk
    obtain ⟨t, rfl⟩ := tagKey_exists hk
    obtain ⟨hne, hj, hb⟩ := equation_caps parts hrankCaps t
    refine ⟨Finset.filter_subset _ _, equation t, hne, hj, hb, ?_⟩
    intro γ hγ
    obtain ⟨t', he, hz⟩ := (Finset.mem_filter.mp hγ).2
    simpa only [tagKey_injective he] using hz
  · exact ⟨cuts.curves, cuts.geometric, hcutCap 0, hcutCap 1,
      fun γ hγ => (Finset.mem_filter.mp hγ).2⟩
  · intro γ hγ
    rcases initial.cover γ hγ with hd | hc | hl | ⟨I, hI, hm⟩
    · exact Or.inl (Finset.mem_union_left _ hd)
    · exact Or.inr (Or.inl (hfixed (cheapTag 0) γ hγ hc))
    · exact Or.inr (Or.inl (hfixed (layeredTag 0) γ hγ hl))
    · rcases hfollow γ hγ I hI hm 10 le_rfl with hk | ⟨t, hf⟩ | hd | ⟨J, hJ, hJm⟩
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hγ, I, hk, hm⟩)))
      · exact Or.inr (Or.inl (hfixed t γ hγ hf))
      · exact Or.inl (Finset.mem_union_right _ hd)
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hγ, J, hJ, hJm⟩)))
end
end K1_14_2_2
end
