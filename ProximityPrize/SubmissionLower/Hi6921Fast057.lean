import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921P21Split
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3RSplit
set_option autoImplicit true
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace H21_3R

noncomputable section

open K21 H21 H21_3 Polynomial
open scoped BigOperators Classical
open private pair_membership from ProximityPrize.SubmissionLower.Hi6921P3Split
open private full_membership from ProximityPrize.SubmissionLower.Hi6921P3Split
open private buffered_power from ProximityPrize.SubmissionLower.Hi6921P3Split
open private paid_complement from ProximityPrize.SubmissionLower.Hi6921P3Split
open private terminal_shape_data from ProximityPrize.SubmissionLower.Hi6921P3Split
open private terminal_power from ProximityPrize.SubmissionLower.Hi6921P3Split

export _root_.K1_14_3R (c1)

export _root_.K1_14_3R (c2)

export _root_.K1_14_3R (c3)

private theorem order_of_source (contact : c1) {u del} {M : AnchorModel u del}
    {Γ} {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    {s : Shape} (hs : s ∈ scheduled M.overhead) (hh : 0 < M.overhead.toNat)
    (hchar : s.m * 180139 < p) {q : Surface} (hq : Parent q)
    (hv : BankVanishes rows s q) (W : ℕ) (hw : W < s.m * 180139)
    (P : Jet) (hP : P ∈ rows s W) : OrderAt q P (contactPower M.overhead.toNat s W) := by
  let h := M.overhead.toNat
  apply contact _ _ _ hq
  · have := Nat.div_le_self (s.m * 180139 - 1 - W) (2*h)
    change 1 + (s.m * 180139 - 1 - W) / (2*h) < p
    omega
  intro a b hab
  change a+b < 1 + (s.m*180139 - 1 - W) / (2*h) at hab
  have hd : 0 < 2*h := by dsimp [h]; omega
  have hl := (Nat.le_div_iff_mul_le hd).mp (show a+b ≤ (s.m*180139 - 1 - W) / (2*h) by omega)
  rw [Nat.mul_comm (a+b), Nat.mul_add] at hl
  have hle : W + 2*h*a + 2*h*b ≤ s.m*180139 - 1 := by omega
  have hA := src.shift s hs W P hP 0 a
  have hB := src.shift s hs _ _ hA 1 b
  exact hv _ (src.nested s hs s hs rfl rfl rfl le_rfl _ _ hle hB)

private theorem paired_mass_of_test (contact : c1) (masses : c2) {u del}
    {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {rows : Banks}
    (src : JetSource M F rows) (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32932)
    (pairs : ∀ i : Fin 4, BufferedPair M.overhead.toNat rows i)
    (i : Fin 4) (S : Finset Surface) (hS : ∀ q ∈ S, Parent q)
    (hpass : ∀ q ∈ S, stagePass rows pairs i.castSucc q) :
    MassCap S (seedMassCap i) (ordinateMassCap i) (mixedMassCap i) := by
  let B := pairs i
  have test (q : Surface) (hq : q ∈ S) :
      BankVanishes rows (cheapShape i) q ∧ BankVanishes rows (layeredShape i) q ∧
        compatible B.cheap B.layered q := by
    simpa only [stagePass, Fin.val_castSucc, dite_eq_left i.isLt] using hpass q hq
  apply masses i B.cheap B.layered B.cheap_ne B.layered_ne B.cheap_caps B.layered_caps B.no_moving
  · intro f hi hd hp hP hQ
    obtain ⟨g, a, ha, hproper, _⟩ := ordinary_graph f hi hd hp
    exact ⟨g, a, ha, hproper, fun q hq hf => (test q hq).2.2 f hi hd hP hQ hf g a ha⟩
  intro q hq
  have ht := test q hq
  have ord (s : Shape) (hs : s ∈ [cheapShape i, layeredShape i]) (hv : BankVanishes rows s q)
      (P : Jet) (hP : P ∈ rows s (reserveCutoff M.overhead.toNat s i)) :
      OrderAt q P (reserve i+1) := by
    have hp : s.m*180139 < p := by
      simp at hs
      rcases hs with rfl | rfl <;> fin_cases i <;> decide
    have hw := buffered_power M.overhead.toNat (by omega) (by omega) i s hs
    rw [← hw.2]
    exact order_of_source contact src (pair_membership hl i hs) (by omega) hp
      (hS q hq) hv _ hw.1 _ hP
  exact ⟨hS q hq, ord _ (by simp) ht.1 _ B.cheap_mem,
    ord _ (by simp) ht.2.1 _ B.layered_mem⟩

open private cheap_caps_le from ProximityPrize.SubmissionLower.Fast057

private theorem cover_failure (loss : c3) {u del} {M : AnchorModel u del}
    {Γ} {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    (hl : 3555 ≤ M.overhead) (pairs : ∀ i : Fin 4, BufferedPair M.overhead.toNat rows i)
    (i : Fin 5) (q : Surface) (hq : Parent q) (hfail : ¬ stagePass rows pairs i q) :
    ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree (cutShape i) {q} ∧
      (C.points.card : ℚ) ≤ constantDegree (cutShape i) {q} ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → C.Covers (M.label γ) := by
  have stagePos (j : Fin 4) : 0 < (cheapShape j).m ∧ 0 < (layeredShape j).m ∧
      1 ≤ (layeredShape j).J := by fin_cases j <;> decide
  have bank (s : Shape) (hs : s ∈ scheduled M.overhead) (hm : 0 < s.m)
      (hn : ¬ BankVanishes rows s q) :
      ∃ P : Jet, P ∉ q.asIdeal ∧ RowCaps P s ∧
        ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
    unfold BankVanishes at hn
    push Not at hn
    obtain ⟨P, hP, hp⟩ := hn
    exact ⟨P, hp, src.shape s hs _ P hP, src.necessary s hs _ (by omega) P hP⟩
  suffices H : ∃ P : Jet, P ∉ q.asIdeal ∧ RowCaps P (cutShape i) ∧
      ∀ γ ∈ Γ, MarkOn M F q γ → jetAt P (M.label γ) (F.scalar γ) = 0 by
    obtain ⟨P, hn, hc, hv⟩ := H
    obtain ⟨C, hd, he, hcov⟩ := loss i q P hq hc hn
    exact ⟨C, hd, he, fun γ hγ hm => hcov _ _ hm (hv γ hγ hm)⟩
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    rw [stagePass, dite_eq_left hi] at hfail
    rw [cutShape, dite_eq_left hi]
    change ¬ (BankVanishes rows (cheapShape j) q ∧ BankVanishes rows (layeredShape j) q ∧
      compatible (pairs j).cheap (pairs j).layered q) at hfail
    by_cases hc : BankVanishes rows (cheapShape j) q
    · by_cases hlayer : BankVanishes rows (layeredShape j) q
      · have hco := fun hc' => hfail ⟨hc, hlayer, hc'⟩
        change ¬ compatible _ _ q at hco
        unfold compatible at hco
        push Not at hco
        obtain ⟨f, _, _, _, hdiv, hf, g, a, hclear, hproper⟩ := hco
        have hcaps := chainCutter_caps_of_dvd (pairs j).layered_ne (pairs j).layered_caps
          (stagePos j).2.2 hdiv hclear
        refine ⟨chainCutter g, hproper, hcaps, ?_⟩
        intro γ _ hmark
        apply chainCutter_zero hclear
        have h := RingHom.mem_ker.mp (hmark hf)
        change jetAt (C f) (M.label γ) (F.scalar γ) = 0 at h
        simpa only [jetAt, eval₂_C, coe_eval₂RingHom, atMark] using h
      · obtain ⟨P, hn, hp, hzero⟩ := bank _ (pair_membership hl j (by simp))
          (stagePos j).2.1 hlayer
        exact ⟨P, hn, hp, fun γ hγ _ => hzero γ hγ⟩
    · obtain ⟨P, hn, hp, hzero⟩ := bank _ (pair_membership hl j (by simp))
        (stagePos j).1 hc
      exact ⟨P, hn, cheap_caps_le j hp, fun γ hγ _ => hzero γ hγ⟩
  · rw [stagePass, dite_eq_right hi] at hfail
    rw [cutShape, dite_eq_right hi]
    obtain ⟨P, hn, hp, hzero⟩ := bank _ (full_membership hl) (by decide) hfail
    exact ⟨P, hn, hp, fun γ hγ _ => hzero γ hγ⟩

theorem of_children (power : H21_2_1.c1) (rankBound : H21_2_1.c2)
    (initialCover : H21_3.c2) (contact : c1) (masses : c2) (loss : c3)
    (ode : H21_3.c6)
    (ordinate : ∀ {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
      (hl : 3555 ≤ M.overhead) (hu : M.overhead ≤ 32932) (rows : Banks)
      (hJ : JetSource M F rows) (f : Equation), f ≠ 0 →
      (∀ W < fullShape.m*180139, ∀ P ∈ rows fullShape W, P ≠ 0 →
        f ^ (contactPower M.overhead.toNat fullShape W - P.natDegree) ∣ P.leadingCoeff) →
      f.natDegree ≤ (band M.overhead).yBound) : H21.c3 := by
  classical
  intro u del M Γ F hl hu _H _chart rows hJ
  let w := M.overhead
  let h := w.toNat
  have hln : 3555 ≤ h := by dsimp [h, w]; omega
  have hun : h ≤ 32932 := by dsimp [h, w]; omega
  let pairs (i : Fin 4) : BufferedPair h rows i :=
    Classical.choice (bufferedPairs power rankBound hJ hl hu i)
  obtain ⟨initial⟩ := initialCover u del M Γ F (pairs 0).cheap (pairs 0).layered
    (pairs 0).cheap_ne (pairs 0).layered_ne (pairs 0).cheap_caps (pairs 0).layered_caps
    (pairs 0).no_moving (by
      intro γ hγ
      exact ⟨hJ.necessary _ (pair_membership hl 0 (by simp))
        _ (buffered_power h hln hun 0 (cheapShape 0) (by simp)).1 _ (pairs 0).cheap_mem γ hγ,
        hJ.necessary _ (pair_membership hl 0 (by simp))
        _ (buffered_power h hln hun 0 (layeredShape 0) (by simp)).1 _ (pairs 0).layered_mem γ hγ⟩)
  let next (i : Fin 5) (S : Finset Surface) := S.filter (stagePass rows pairs i)
  let S₀ := initial.parents
  let S₁ := next 1 S₀
  let S₂ := next 2 S₁
  let S₃ := next 3 S₂
  let S₄ := next 4 S₃
  have s₁ : S₁ ⊆ S₀ := Finset.filter_subset _ _
  have s₂ : S₂ ⊆ S₁ := Finset.filter_subset _ _
  have s₃ : S₃ ⊆ S₂ := Finset.filter_subset _ _
  have s₄ : S₄ ⊆ S₃ := Finset.filter_subset _ _
  have hg₀ : ∀ q ∈ S₀, Parent q := initial.geometric
  have hg₁ : ∀ q ∈ S₁, Parent q := fun q hq => hg₀ q (s₁ hq)
  have hg₂ : ∀ q ∈ S₂, Parent q := fun q hq => hg₁ q (s₂ hq)
  have hg₃ : ∀ q ∈ S₃, Parent q := fun q hq => hg₂ q (s₃ hq)
  have hg₄ : ∀ q ∈ S₄, Parent q := fun q hq => hg₃ q (s₄ hq)
  have m₁ := paired_mass_of_test contact masses hJ hl hu pairs 1 S₁ hg₁
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have m₂ := paired_mass_of_test contact masses hJ hl hu pairs 2 S₂ hg₂
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have m₃ := paired_mass_of_test contact masses hJ hl hu pairs 3 S₃ hg₃
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have step (i : Fin 5) (S : Finset Surface) (hS : ∀ q ∈ S, Parent q) :
      ∃ C : SeedCover, (C.curve.totalDegree : ℚ) ≤ cutDegree (cutShape i) (S \ next i S) ∧
        (C.points.card : ℚ) ≤ constantDegree (cutShape i) (S \ next i S) ∧
        ∀ γ ∈ Γ, (∃ q ∈ S \ next i S, MarkOn M F q γ) → C.Covers (M.label γ) := by
    apply combine_cut_covers
    intro q hq
    obtain ⟨hq₀, hfail⟩ := Finset.mem_sdiff.mp hq
    apply cover_failure loss hJ hl pairs i q (hS q hq₀)
    exact fun pass => hfail (Finset.mem_filter.mpr ⟨hq₀, pass⟩)
  obtain ⟨C₁, d₁, e₁, cov₁⟩ := step 1 S₀ hg₀
  obtain ⟨C₂, d₂, e₂, cov₂⟩ := step 2 S₁ hg₁
  obtain ⟨C₃, d₃, e₃, cov₃⟩ := step 3 S₂ hg₂
  obtain ⟨C₄, d₄, e₄, cov₄⟩ := step 4 S₃ hg₃
  let C : Fin 4 → SeedCover := ![C₁,C₂,C₃,C₄]
  let lost := joinCovers Finset.univ C
  have hd : (lost.curve.totalDegree : ℚ) ≤ 7830019781/144 := by
    have hd' : (lost.curve.totalDegree : ℚ) ≤
        ∑ i : Fin 4, ((C i).curve.totalDegree : ℚ) := by exact_mod_cast joinCovers_degree .univ C
    rw [Fin.sum_univ_four] at hd'
    exact (hd'.trans (add_le_add (add_le_add (add_le_add d₁ d₂) d₃) d₄)).trans
      (moving_loss_bound s₁ s₂ s₃ s₄ initial.masses m₁ m₂ m₃)
  have he : (lost.points.card : ℚ) ≤ 26769366519 := by
    have he' : (lost.points.card : ℚ) ≤
        ∑ i : Fin 4, ((C i).points.card : ℚ) := by exact_mod_cast joinCovers_points .univ C
    rw [Fin.sum_univ_four] at he'
    exact (he'.trans (add_le_add (add_le_add (add_le_add e₁ e₂) e₃) e₄)).trans
      (constant_loss_bound s₁ s₂ s₃ s₄ initial.masses.mixed initial.jetMass)
  let kept := Γ.filter (fun γ => ∃ q ∈ S₄, MarkOn M F q γ)
  have hcover : ∀ γ ∈ Γ, (∃ q ∈ S₀, MarkOn M F q γ) →
      γ ∈ kept ∨ lost.Covers (M.label γ) := by
    rintro γ hγ ⟨q, hq₀, hm⟩
    by_cases hq₁ : q ∈ S₁
    · by_cases hq₂ : q ∈ S₂
      · by_cases hq₃ : q ∈ S₃
        · by_cases hq₄ : q ∈ S₄
          · exact Or.inl (Finset.mem_filter.mpr ⟨hγ,q,hq₄,hm⟩)
          · exact Or.inr (joinCovers_covers (i := (3 : Fin 4)) (Finset.mem_univ _)
              (cov₄ γ hγ ⟨q, Finset.mem_sdiff.mpr ⟨hq₃,hq₄⟩,hm⟩))
        · exact Or.inr (joinCovers_covers (i := (2 : Fin 4)) (Finset.mem_univ _)
            (cov₃ γ hγ ⟨q, Finset.mem_sdiff.mpr ⟨hq₂,hq₃⟩,hm⟩))
      · exact Or.inr (joinCovers_covers (i := (1 : Fin 4)) (Finset.mem_univ _)
          (cov₂ γ hγ ⟨q, Finset.mem_sdiff.mpr ⟨hq₁,hq₂⟩,hm⟩))
    · exact Or.inr (joinCovers_covers (i := (0 : Fin 4)) (Finset.mem_univ _)
        (cov₁ γ hγ ⟨q, Finset.mem_sdiff.mpr ⟨hq₀,hq₁⟩,hm⟩))
  have hdNat : lost.curve.totalDegree ≤ 54375137 := by
    have ht : (lost.curve.totalDegree : ℚ) < (54375138 : ℕ) :=
      hd.trans_lt (by norm_num)
    have hn : lost.curve.totalDegree < 54375138 := by exact_mod_cast ht
    omega
  have heNat : lost.points.card ≤ 26769366519 := by exact_mod_cast he
  have hprefix := paid_complement ode hl hu initial lost hdNat heNat kept hcover
  by_cases hkept : kept.Nonempty
  · have hne : S₄.Nonempty := by
      obtain ⟨γ, hγ⟩ := hkept
      obtain ⟨q, hq, _⟩ := (Finset.mem_filter.mp hγ).2
      exact ⟨q, hq⟩
    obtain ⟨f, hf⟩ := K1_14_3_7.proof S₄ hne hg₄
    have hs := full_membership hl
    have hcontacts (W : ℕ) (hw : W < fullShape.m*180139) (P : Jet)
        (hP : P ∈ rows fullShape W) :
        ∀ q ∈ S₄, OrderAt q P (contactPower h fullShape W) := by
      intro q hq
      have ht : BankVanishes rows fullShape q := by
        have hpass : stagePass rows pairs 4 q := (Finset.mem_filter.mp hq).2
        unfold stagePass at hpass
        split at hpass
        · rename_i hi
          exact ((by decide : ¬ (4 : Fin 5).val < 4) hi).elim
        · exact hpass
      exact order_of_source contact hJ hs (by omega) (by decide) (hg₄ q hq) ht W hw P hP
    have hfour := ordinate M F hl hu rows hJ f (by
      intro he
      simpa only [he, Polynomial.natDegree_zero, lt_self_iff_false] using hf.positive) (by
      intro W hW Q hQ hn
      exact hf.divides_leading Q _ hn (hcontacts W hW Q hQ))
    obtain ⟨ht, hm, hb, hj, hU, hy⟩ := terminal_shape_data hl
    -- Check the terminal divisibility proof at its stated type before packing the witness.
    have hdiv : TerminalDivisibility w rows f := by
      intro W hW P hP hn
      change (band w).multiplicity = fullShape.m at hm
      rw [hm] at hW
      have hp : P ∈ rows fullShape W :=
        hJ.nested _ ht _ hs hm hb hj hU W W le_rfl hP
      change f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff
      rw [terminal_power hm]
      exact hf.divides_leading P _ hn (hcontacts W hW P hp)
    refine Or.inr ⟨kept, Finset.filter_subset _ _, hprefix, f,
      ⟨hf.positive, hfour, hf.primitive, hf.separable⟩, hdiv, ?_⟩
    intro γ hg
    obtain ⟨q, hq, hmark⟩ := (Finset.mem_filter.mp hg).2
    have hz := RingHom.mem_ker.mp (hmark (hf.vanishes q hq))
    simpa [atMark, eval₂RingHom] using hz
  · left
    have hk := Finset.not_nonempty_iff_eq_empty.mp hkept
    simpa only [hk, Finset.sdiff_empty] using hprefix

end
end H21_3R
end High_K1_14_3RSplit
