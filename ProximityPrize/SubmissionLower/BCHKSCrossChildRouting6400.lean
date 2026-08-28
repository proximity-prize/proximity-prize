import ProximityPrize.SubmissionLower.BCHKSUniversalFactorSums
import ProximityPrize.SubmissionLower.BCHKSUniversalResultantSelection

/-!
# Cross-child routing for the centered score-64 recursion

At a repeated agreement section, the section and the selected witness may be
owned by different normalized irreducible children of the same parent.  This
module isolates those mismatches as challenges at which two distinct positive
children have a common specialized root.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The distinct normalized factors of a bivariate parent that have positive
degree in the root variable. -/
noncomputable def positiveChildren (B : F[X][Y]) : Finset (F[X][Y]) :=
  (UniqueFactorizationMonoid.normalizedFactors B).toFinset.filter
    (fun H => 0 < H.natDegree)

omit [Fintype F] in
@[simp]
theorem mem_positiveChildren_iff {B H : F[X][Y]} :
    H ∈ positiveChildren B ↔
      H ∈ UniqueFactorizationMonoid.normalizedFactors B ∧
        0 < H.natDegree := by
  simp [positiveChildren]

omit [Fintype F] in
/-- Distinct positive normalized children have a nonzero ordinary
resultant.  A zero resultant would make one irreducible child divide the
other; normalization would then identify them. -/
theorem resultant_ne_zero_of_distinct_positiveChildren
    (B H₀ H₁ : F[X][Y])
    (h₀ : H₀ ∈ positiveChildren B)
    (h₁ : H₁ ∈ positiveChildren B)
    (hne : H₀ ≠ H₁) :
    Polynomial.resultant H₀ H₁ ≠ 0 := by
  intro hres
  have h₀' := (mem_positiveChildren_iff.mp h₀)
  have h₁' := (mem_positiveChildren_iff.mp h₁)
  have hirr₀ : Irreducible H₀ :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H₀ h₀'.1).irreducible
  have hirr₁ : Irreducible H₁ :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H₁ h₁'.1).irreducible
  have hdvd : H₁ ∣ H₀ :=
    irreducible_dvd_of_resultant_eq_zero_nonmonic H₀ H₁ hirr₁ h₁'.2 hres
  have hassoc : Associated H₁ H₀ :=
    Irreducible.associated_of_dvd hirr₁ hirr₀ hdvd
  have heq : H₁ = H₀ :=
    UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
      h₁'.1 h₀'.1 hassoc
  exact hne heq.symm

omit [Fintype F] in
/-- A specialized common root of two positive children is a root of their
ordinary resultant in the challenge variable. -/
theorem resultant_eval_eq_zero_of_positiveChildren_common_root
    (B H₀ H₁ : F[X][Y]) (z y : F)
    (h₀ : H₀ ∈ positiveChildren B)
    (h₁ : H₁ ∈ positiveChildren B)
    (hroot₀ : (H₀.map (Polynomial.evalRingHom z)).eval y = 0)
    (hroot₁ : (H₁.map (Polynomial.evalRingHom z)).eval y = 0) :
    (Polynomial.resultant H₀ H₁).eval z = 0 := by
  have hpos₀ := (mem_positiveChildren_iff.mp h₀).2
  have hpos₁ := (mem_positiveChildren_iff.mp h₁).2
  exact bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
    H₀ H₁ z y (by omega) hroot₀ hroot₁

/-- Challenges at which two distinct positive normalized children of `B`
share a specialized root. -/
noncomputable def crossChildChallenges (B : F[X][Y]) : Finset F :=
  Finset.univ.filter fun z =>
    ∃ Hsection ∈ positiveChildren B,
    ∃ Hwitness ∈ positiveChildren B,
      Hsection ≠ Hwitness ∧
      ∃ y : F,
        (Hsection.map (Polynomial.evalRingHom z)).eval y = 0 ∧
        (Hwitness.map (Polynomial.evalRingHom z)).eval y = 0

/-- If the section owner and witness owner are not the same child, their
common specialized root places the challenge in the cross-child bad set. -/
theorem same_child_or_mem_crossChildChallenges
    (B Hsection Hwitness : F[X][Y]) (z y : F)
    (hsection : Hsection ∈ positiveChildren B)
    (hwitness : Hwitness ∈ positiveChildren B)
    (hsectionRoot :
      (Hsection.map (Polynomial.evalRingHom z)).eval y = 0)
    (hwitnessRoot :
      (Hwitness.map (Polynomial.evalRingHom z)).eval y = 0) :
    Hsection = Hwitness ∨ z ∈ crossChildChallenges B := by
  by_cases hsame : Hsection = Hwitness
  · exact Or.inl hsame
  · refine Or.inr ?_
    simp only [crossChildChallenges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Hsection, hsection, Hwitness, hwitness, hsame, y,
      hsectionRoot, hwitnessRoot⟩

/-- The unordered pairs of distinct positive normalized children. -/
noncomputable def positiveChildPairs (B : F[X][Y]) :
    Finset (Sym2 F[X][Y]) :=
  (positiveChildren B).sym2.filter fun p => ¬ p.IsDiag

/-- The challenges at which the two children in an unordered pair have a
common specialized root. -/
noncomputable def pairChallenges (p : Sym2 F[X][Y]) : Finset F :=
  Sym2.lift ⟨(fun H₀ H₁ => Finset.univ.filter fun z =>
    ∃ y : F,
      (H₀.map (Polynomial.evalRingHom z)).eval y = 0 ∧
      (H₁.map (Polynomial.evalRingHom z)).eval y = 0), by
        intro H₀ H₁
        apply Finset.ext
        intro z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨y, h₀, h₁⟩
          exact ⟨y, h₁, h₀⟩
        · rintro ⟨y, h₁, h₀⟩
          exact ⟨y, h₀, h₁⟩⟩ p

/-- The degree charge for an unordered pair of children.  It is the standard
bivariate resultant degree bound, symmetrized in the two children. -/
noncomputable def pairWeight (p : Sym2 F[X][Y]) : ℕ :=
  Sym2.lift ⟨(fun H₀ H₁ =>
    H₀.natDegree * degreeX H₁ + H₁.natDegree * degreeX H₀), by
      intro H₀ H₁
      exact Nat.add_comm _ _⟩ p

private noncomputable def unorderedPairWeight {A : Type} (f g : A → ℕ)
    (p : Sym2 A) : ℕ :=
  Sym2.lift ⟨(fun a b => f a * g b + f b * g a), by
    intro a b
    exact Nat.add_comm _ _⟩ p

/-- The total cross mass of all unordered distinct pairs is at most the
product of the two total masses.  Counting each unordered pair once is what
keeps the centered score-64 collision ledger within budget. -/
private theorem sum_unorderedPairWeight_le_mul
    {A : Type} [DecidableEq A] (s : Finset A) (f g : A → ℕ) :
    (∑ p ∈ s.sym2.filter (fun p => ¬ p.IsDiag), unorderedPairWeight f g p) ≤
      (∑ a ∈ s, f a) * (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sym2_insert]
      simp only [Finset.filter_union]
      have hfirst :
          (Finset.image (fun b => s(a, b)) (insert a s)).filter
              (fun p => ¬ p.IsDiag) =
            s.image (fun b => s(a, b)) := by
        ext p
        induction p using Sym2.inductionOn with
        | hf x y =>
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_insert,
              Sym2.mk_isDiag_iff]
            constructor
            · rintro ⟨⟨b, hb, hp⟩, hxy⟩
              have hba : b ≠ a := by
                intro h
                subst b
                apply hxy
                rw [← Sym2.mk_isDiag_iff, ← hp]
                exact Sym2.mk_isDiag_iff.mpr rfl
              refine ⟨b, hb.resolve_left hba, hp⟩
            · rintro ⟨b, hb, hp⟩
              refine ⟨⟨b, Or.inr hb, hp⟩, ?_⟩
              intro hxy
              have hab : a = b := by
                rw [← Sym2.mk_isDiag_iff]
                rw [hp]
                exact hxy
              exact ha (hab ▸ hb)
      rw [hfirst]
      have hdisj : Disjoint (s.image fun b => s(a, b))
          (s.sym2.filter fun p => ¬ p.IsDiag) := by
        rw [Finset.disjoint_left]
        intro p hpnew hpold
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hpnew
        exact ha (Finset.mk_mem_sym2_iff.mp (Finset.mem_filter.mp hpold).1).1
      rw [Finset.sum_union hdisj]
      have hinj : Set.InjOn (fun b => s(a, b)) s := by
        intro b _ c _ h
        exact Sym2.congr_right.mp h
      rw [Finset.sum_image hinj]
      simp only [unorderedPairWeight, Sym2.lift_mk]
      calc
        (∑ b ∈ s, (f a * g b + f b * g a)) +
              ∑ p ∈ s.sym2 with ¬ p.IsDiag, unorderedPairWeight f g p ≤
            (∑ b ∈ s, (f a * g b + f b * g a)) +
              ((∑ b ∈ s, f b) * ∑ b ∈ s, g b) :=
          Nat.add_le_add_left ih _
        _ ≤ (∑ b ∈ insert a s, f b) * ∑ b ∈ insert a s, g b := by
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          rw [Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          simp only [Nat.add_mul, Nat.mul_add]
          omega

theorem crossChildChallenges_subset_pairChallenges (B : F[X][Y]) :
    crossChildChallenges B ⊆
      (positiveChildPairs B).biUnion pairChallenges := by
  classical
  intro z hz
  simp only [crossChildChallenges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hz
  obtain ⟨H₀, hH₀, H₁, hH₁, hne, y, hroot₀, hroot₁⟩ := hz
  rw [Finset.mem_biUnion]
  refine ⟨s(H₀, H₁), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨hH₀, hH₁⟩, ?_⟩
    simpa only [Sym2.mk_isDiag_iff] using hne
  · simp only [pairChallenges, Sym2.lift_mk, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨y, hroot₀, hroot₁⟩

theorem pairChallenges_card_le_weight
    (B : F[X][Y]) (p : Sym2 F[X][Y]) (hp : p ∈ positiveChildPairs B) :
    (pairChallenges p).card ≤ pairWeight p := by
  classical
  induction p using Sym2.inductionOn with
  | hf H₀ H₁ =>
      have hp' :
          (H₀ ∈ positiveChildren B ∧ H₁ ∈ positiveChildren B) ∧
            H₀ ≠ H₁ := by
        simpa [positiveChildPairs, Sym2.mk_isDiag_iff] using hp
      rcases hp' with ⟨⟨hH₀, hH₁⟩, hne⟩
      let R : F[X] := Polynomial.resultant H₀ H₁
      have hR0 : R ≠ 0 := resultant_ne_zero_of_distinct_positiveChildren
        B H₀ H₁ hH₀ hH₁ hne
      have hsub : pairChallenges s(H₀, H₁) ⊆ R.roots.toFinset := by
        intro z hz
        simp only [pairChallenges, Sym2.lift_mk, Finset.mem_filter,
          Finset.mem_univ, true_and] at hz
        obtain ⟨y, hroot₀, hroot₁⟩ := hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hR0]
        exact bivariate_resultant_eval_eq_zero_of_common_root_original_degrees
          H₀ H₁ z y (Nat.add_pos_left (mem_positiveChildren_iff.mp hH₀).2 _)
          hroot₀ hroot₁
      calc
        (pairChallenges s(H₀, H₁)).card ≤ R.roots.toFinset.card :=
          Finset.card_le_card hsub
        _ ≤ R.roots.card := Multiset.toFinset_card_le _
        _ ≤ R.natDegree := Polynomial.card_roots' R
        _ ≤ H₀.natDegree * degreeX H₁ + H₁.natDegree * degreeX H₀ := by
          simpa [R, Nat.add_comm] using
            (bivariate_resultant_natDegree_le H₀ H₁
              H₀.natDegree H₁.natDegree)
        _ = pairWeight s(H₀, H₁) := rfl

theorem crossChildChallenges_card_le_sum_pairWeight (B : F[X][Y]) :
    (crossChildChallenges B).card ≤
      ∑ p ∈ positiveChildPairs B, pairWeight p := by
  classical
  calc
    (crossChildChallenges B).card ≤
        ((positiveChildPairs B).biUnion pairChallenges).card :=
      Finset.card_le_card (crossChildChallenges_subset_pairChallenges B)
    _ ≤ ∑ p ∈ positiveChildPairs B, (pairChallenges p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ positiveChildPairs B, pairWeight p := by
      exact Finset.sum_le_sum fun p hp => pairChallenges_card_le_weight B p hp

omit [Fintype F] in
theorem sum_positiveChildPairs_pairWeight_le_mul_degrees (B : F[X][Y]) :
    (∑ p ∈ positiveChildPairs B, pairWeight p) ≤
      (∑ H ∈ positiveChildren B, H.natDegree) *
        (∑ H ∈ positiveChildren B, degreeX H) := by
  classical
  simpa [positiveChildPairs, pairWeight, unorderedPairWeight] using
    (sum_unorderedPairWeight_le_mul (positiveChildren B)
      (fun H : F[X][Y] => H.natDegree)
      (fun H : F[X][Y] => degreeX H))

/-- All cross-child challenges are charged once to ordinary resultants.  If
the parent has root-variable degree at most `M` and challenge-variable degree
at most `D`, the entire bad set has cardinality at most `M * D`. -/
theorem crossChildChallenges_card_le_mul
    (B : F[X][Y]) (hB : B ≠ 0) (M D : ℕ)
    (hY : B.natDegree ≤ M) (hX : degreeX B ≤ D) :
    (crossChildChallenges B).card ≤ M * D := by
  classical
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
  dsimp only at hsums
  have hsumY : (∑ H ∈ positiveChildren B, H.natDegree) ≤ M := by
    simpa [positiveChildren] using hsums.1.trans hY
  have hsumX : (∑ H ∈ positiveChildren B, degreeX H) ≤ D := by
    simpa [positiveChildren] using hsums.2.trans hX
  calc
    (crossChildChallenges B).card ≤
        ∑ p ∈ positiveChildPairs B, pairWeight p :=
      crossChildChallenges_card_le_sum_pairWeight B
    _ ≤ (∑ H ∈ positiveChildren B, H.natDegree) *
        (∑ H ∈ positiveChildren B, degreeX H) :=
      sum_positiveChildPairs_pairWeight_le_mul_degrees B
    _ ≤ M * D := Nat.mul_le_mul hsumY hsumX

/-- A family of parents pays the cross-child charge only once per parent. -/
theorem biUnion_crossChildChallenges_card_le
    {I : Type} [DecidableEq I] (parents : Finset I)
    (B : I → F[X][Y]) (M D : ℕ)
    (hB : ∀ i ∈ parents, B i ≠ 0)
    (hY : ∀ i ∈ parents, (B i).natDegree ≤ M)
    (hX : ∀ i ∈ parents, degreeX (B i) ≤ D) :
    (parents.biUnion fun i => crossChildChallenges (B i)).card ≤
      parents.card * (M * D) := by
  classical
  calc
    (parents.biUnion fun i => crossChildChallenges (B i)).card ≤
        ∑ i ∈ parents, (crossChildChallenges (B i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ parents, M * D := by
      exact Finset.sum_le_sum fun i hi =>
        crossChildChallenges_card_le_mul (B i) (hB i hi) M D
          (hY i hi) (hX i hi)
    _ = parents.card * (M * D) := by simp

/-- If the recursive family has at most `E` parents, its entire cross-child
charge is at most `E * (M * D)`. -/
theorem biUnion_crossChildChallenges_card_le_of_card
    {I : Type} [DecidableEq I] (parents : Finset I)
    (B : I → F[X][Y]) (E M D : ℕ)
    (hcard : parents.card ≤ E)
    (hB : ∀ i ∈ parents, B i ≠ 0)
    (hY : ∀ i ∈ parents, (B i).natDegree ≤ M)
    (hX : ∀ i ∈ parents, degreeX (B i) ≤ D) :
    (parents.biUnion fun i => crossChildChallenges (B i)).card ≤
      E * (M * D) := by
  calc
    (parents.biUnion fun i => crossChildChallenges (B i)).card ≤
        parents.card * (M * D) :=
      biUnion_crossChildChallenges_card_le parents B M D hB hY hX
    _ ≤ E * (M * D) := Nat.mul_le_mul_right (M * D) hcard

/-- Exact cross-child term in the centered score-64 collision ledger. -/
theorem centered6400_crossChild_numeric :
    262141 * (2654 * 1670075) = 1161908276546050 := by
  norm_num

end ProximityPrize.SubmissionLower
