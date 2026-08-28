import ProximityPrize.SubmissionLower.BCHKSBridge

/-!
# Exact sparsification for the score-64 affine-line search

This file ports the deterministic SP3 reduction into the self-contained lower
submission graph.  It deliberately uses an agreement threshold `a` rather
than a real radius, so the result can be connected to the chosen agreement
sets in `AffineLineGivenSetsBound` without rounding ambiguity.

The theorem is parameter-free: it applies to every finite linear code.  The
score-64 specialization uses `a = 185364`, so a non-column-far received pair
can be translated by two codewords to a pair whose joint support has size at
most `262144 - 185364 = 76780`.
-/

open scoped BigOperators Classical

noncomputable section

namespace ProximityPrize.SubmissionLower.BCHKSExactSparsification6400

set_option autoImplicit false

universe u v

variable {F : Type u} {D : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype D] [DecidableEq D]

local notation "Word" => D → F

/-- A word is explained on `S` if a codeword agrees with it on every
coordinate of `S`. -/
def Explained (C : Submodule F Word) (f : Word) (S : Finset D) : Prop :=
  ∃ c ∈ C, ∀ x ∈ S, c x = f x

/-- Both rows are simultaneously explained on the same support. -/
def ExplainedPair (C : Submodule F Word) (f₀ f₁ : Word) (S : Finset D) : Prop :=
  ∃ c₀ ∈ C, ∃ c₁ ∈ C,
    (∀ x ∈ S, c₀ x = f₀ x) ∧ (∀ x ∈ S, c₁ x = f₁ x)

/-- A slope has a close line word on some large support, but the two source
rows are not simultaneously explained on that support. -/
def MCABad (C : Submodule F Word) (f₀ f₁ : Word) (a : ℕ) (z : F) : Prop :=
  ∃ S : Finset D, a ≤ S.card ∧
    Explained C (fun x => f₀ x + z * f₁ x) S ∧
    ¬ ExplainedPair C f₀ f₁ S

/-- The plain correlated-agreement branch: the line has a large explanation,
while the pair has no large common explanation anywhere. -/
def CABad (C : Submodule F Word) (f₀ f₁ : Word) (a : ℕ) (z : F) : Prop :=
  (∃ S : Finset D, a ≤ S.card ∧
      Explained C (fun x => f₀ x + z * f₁ x) S) ∧
  (∀ T : Finset D, a ≤ T.card → ¬ ExplainedPair C f₀ f₁ T)

/-- A pair is column-far when it is not simultaneously explained on any
support of cardinality at least `a`. -/
def ColumnFar (C : Submodule F Word) (f₀ f₁ : Word) (a : ℕ) : Prop :=
  ∀ S : Finset D, a ≤ S.card → ¬ ExplainedPair C f₀ f₁ S

/-- The finite support of a word. -/
def wordSupport (f : Word) : Finset D :=
  Finset.univ.filter fun x => f x ≠ 0

/-- The union of the two coordinate supports of a received pair. -/
def pairSupport (f₀ f₁ : Word) : Finset D :=
  wordSupport f₀ ∪ wordSupport f₁

/-- The sparse class at agreement `a`. -/
def SparseAt (f₀ f₁ : Word) (a : ℕ) : Prop :=
  (pairSupport f₀ f₁).card ≤ Fintype.card D - a

/-- MCA-bad slopes restricted to a finite challenge set. -/
def restrictedMCABadSlopes (Gamma : Finset F) (C : Submodule F Word)
    (f₀ f₁ : Word) (a : ℕ) : Finset F :=
  Gamma.filter fun z => MCABad C f₀ f₁ a z

/-- CA-bad slopes restricted to a finite challenge set. -/
def restrictedCABadSlopes (Gamma : Finset F) (C : Submodule F Word)
    (f₀ f₁ : Word) (a : ℕ) : Finset F :=
  Gamma.filter fun z => CABad C f₀ f₁ a z

/-- Challenge-restricted MCA numerator. -/
noncomputable def B_MCA_challenge (Gamma : Finset F) (C : Submodule F Word)
    (a : ℕ) : ℕ :=
  Finset.univ.sup fun p : Word × Word =>
    (restrictedMCABadSlopes Gamma C p.1 p.2 a).card

/-- Challenge-restricted CA numerator. -/
noncomputable def B_CA_challenge (Gamma : Finset F) (C : Submodule F Word)
    (a : ℕ) : ℕ :=
  Finset.univ.sup fun p : Word × Word =>
    (restrictedCABadSlopes Gamma C p.1 p.2 a).card

/-- Challenge-restricted sparse mutual numerator. -/
noncomputable def sparseMutualChallenge (Gamma : Finset F)
    (C : Submodule F Word) (a : ℕ) : ℕ :=
  Finset.univ.sup fun p : Word × Word =>
    if SparseAt p.1 p.2 a
    then (restrictedMCABadSlopes Gamma C p.1 p.2 a).card
    else 0

omit [Fintype F] [DecidableEq F] in
/-- The support-wise definition agrees with ArkLib's projected-code
membership predicate. -/
theorem explained_iff_projectedCodeSubmod (C : Submodule F Word)
    (f : Word) (S : Finset D) :
    Explained C f S ↔
      LinearCode.projectedWord f S ∈ LinearCode.projectedCodeSubmod C S := by
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  constructor
  · rintro ⟨c, hc, hagree⟩
    refine ⟨c, hc, ?_⟩
    funext x
    exact (hagree x.1 x.2).symm
  · rintro ⟨c, hc, hproj⟩
    refine ⟨c, hc, ?_⟩
    intro x hx
    exact (congrFun hproj ⟨x, hx⟩).symm

omit [Fintype F] [DecidableEq F] in
/-- Pair explanation is exactly projected membership of both rows. -/
theorem explainedPair_iff_projectedCodeSubmod (C : Submodule F Word)
    (f₀ f₁ : Word) (S : Finset D) :
    ExplainedPair C f₀ f₁ S ↔
      LinearCode.projectedWord f₀ S ∈ LinearCode.projectedCodeSubmod C S ∧
      LinearCode.projectedWord f₁ S ∈ LinearCode.projectedCodeSubmod C S := by
  rw [← explained_iff_projectedCodeSubmod C f₀ S,
    ← explained_iff_projectedCodeSubmod C f₁ S]
  constructor
  · rintro ⟨c₀, hc₀, c₁, hc₁, h₀, h₁⟩
    exact ⟨⟨c₀, hc₀, h₀⟩, ⟨c₁, hc₁, h₁⟩⟩
  · rintro ⟨⟨c₀, hc₀, h₀⟩, ⟨c₁, hc₁, h₁⟩⟩
    exact ⟨c₀, hc₀, c₁, hc₁, h₀, h₁⟩

omit [Fintype F] [DecidableEq F] in
/-- `MCABad` is exactly the chosen-agreement-set witness used by ArkLib's
affine-line MCA predicate, with the real cardinality inequality replaced by
the already-rounded natural threshold `a`. -/
theorem mcaBad_iff_projectedWitness (C : Submodule F Word)
    (U : Fin 2 → Word) (a : ℕ) (z : F) :
    MCABad C (U 0) (U 1) a z ↔
      ∃ S : Finset D, a ≤ S.card ∧
        LinearCode.projectedWord (fun x => U 0 x + z * U 1 x) S ∈
          LinearCode.projectedCodeSubmod C S ∧
        ∃ j : Fin 2,
          LinearCode.projectedWord (U j) S ∉
            LinearCode.projectedCodeSubmod C S := by
  classical
  constructor
  · rintro ⟨S, hS, hline, hpair⟩
    refine ⟨S, hS,
      (explained_iff_projectedCodeSubmod C _ S).mp hline, ?_⟩
    have hnot : ¬ (
        LinearCode.projectedWord (U 0) S ∈
            LinearCode.projectedCodeSubmod C S ∧
        LinearCode.projectedWord (U 1) S ∈
            LinearCode.projectedCodeSubmod C S) := by
      intro hboth
      exact hpair ((explainedPair_iff_projectedCodeSubmod C (U 0) (U 1) S).mpr hboth)
    by_cases h₀ : LinearCode.projectedWord (U 0) S ∈
        LinearCode.projectedCodeSubmod C S
    · refine ⟨1, ?_⟩
      intro h₁
      exact hnot ⟨h₀, h₁⟩
    · exact ⟨0, h₀⟩
  · rintro ⟨S, hS, hline, j, hj⟩
    refine ⟨S, hS,
      (explained_iff_projectedCodeSubmod C _ S).mpr hline, ?_⟩
    intro hpair
    have hboth :=
      (explainedPair_iff_projectedCodeSubmod C (U 0) (U 1) S).mp hpair
    fin_cases j
    · exact hj hboth.1
    · exact hj hboth.2

omit [Fintype F] [DecidableEq F] in
/-- Negating column-farness produces a common explaining support. -/
theorem not_columnFar_iff (C : Submodule F Word) (f₀ f₁ : Word) (a : ℕ) :
    ¬ ColumnFar C f₀ f₁ a ↔
      ∃ S : Finset D, a ≤ S.card ∧ ExplainedPair C f₀ f₁ S := by
  simp [ColumnFar]

omit [Fintype F] [DecidableEq F] in
/-- Translating a word by a codeword preserves explanation on every support. -/
theorem explained_sub_mem_iff (C : Submodule F Word) (f c : Word)
    (hc : c ∈ C) (S : Finset D) :
    Explained C (f - c) S ↔ Explained C f S := by
  constructor
  · rintro ⟨h, hhC, hh⟩
    refine ⟨h + c, C.add_mem hhC hc, ?_⟩
    intro x hx
    change h x + c x = f x
    rw [hh x hx]
    exact sub_add_cancel _ _
  · rintro ⟨h, hhC, hh⟩
    refine ⟨h - c, C.sub_mem hhC hc, ?_⟩
    intro x hx
    change h x - c x = f x - c x
    rw [hh x hx]

omit [Fintype F] [DecidableEq F] in
/-- Translating both coordinates preserves simultaneous explanation. -/
theorem explainedPair_sub_mem_iff (C : Submodule F Word)
    (f₀ f₁ c₀ c₁ : Word) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (S : Finset D) :
    ExplainedPair C (f₀ - c₀) (f₁ - c₁) S ↔
      ExplainedPair C f₀ f₁ S := by
  constructor
  · rintro ⟨h₀, hh₀C, h₁, hh₁C, hh₀, hh₁⟩
    refine ⟨h₀ + c₀, C.add_mem hh₀C hc₀, h₁ + c₁,
      C.add_mem hh₁C hc₁, ?_, ?_⟩
    · intro x hx
      change h₀ x + c₀ x = f₀ x
      rw [hh₀ x hx]
      exact sub_add_cancel _ _
    · intro x hx
      change h₁ x + c₁ x = f₁ x
      rw [hh₁ x hx]
      exact sub_add_cancel _ _
  · rintro ⟨h₀, hh₀C, h₁, hh₁C, hh₀, hh₁⟩
    refine ⟨h₀ - c₀, C.sub_mem hh₀C hc₀, h₁ - c₁,
      C.sub_mem hh₁C hc₁, ?_, ?_⟩
    · intro x hx
      change h₀ x - c₀ x = f₀ x - c₀ x
      rw [hh₀ x hx]
    · intro x hx
      change h₁ x - c₁ x = f₁ x - c₁ x
      rw [hh₁ x hx]

omit [Fintype F] [DecidableEq F] in
/-- Translating a pair preserves line explanation at each slope and support. -/
theorem lineExplained_sub_mem_iff (C : Submodule F Word)
    (f₀ f₁ c₀ c₁ : Word) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (z : F) (S : Finset D) :
    Explained C (fun x => (f₀ - c₀) x + z * (f₁ - c₁) x) S ↔
      Explained C (fun x => f₀ x + z * f₁ x) S := by
  constructor
  · rintro ⟨h, hhC, hh⟩
    refine ⟨h + (c₀ + z • c₁),
      C.add_mem hhC (C.add_mem hc₀ (C.smul_mem z hc₁)), ?_⟩
    intro x hx
    change h x + (c₀ x + z * c₁ x) = f₀ x + z * f₁ x
    have heq := hh x hx
    change h x = (f₀ x - c₀ x) + z * (f₁ x - c₁ x) at heq
    rw [heq]
    ring
  · rintro ⟨h, hhC, hh⟩
    refine ⟨h - (c₀ + z • c₁),
      C.sub_mem hhC (C.add_mem hc₀ (C.smul_mem z hc₁)), ?_⟩
    intro x hx
    change h x - (c₀ x + z * c₁ x) =
      (f₀ x - c₀ x) + z * (f₁ x - c₁ x)
    have heq := hh x hx
    change h x = f₀ x + z * f₁ x at heq
    rw [heq]
    ring

omit [Fintype F] [DecidableEq F] in
/-- Codeword-pair translation preserves the exact MCA-bad predicate. -/
theorem mcaBad_sub_mem_iff (C : Submodule F Word)
    (f₀ f₁ c₀ c₁ : Word) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (a : ℕ) (z : F) :
    MCABad C (f₀ - c₀) (f₁ - c₁) a z ↔ MCABad C f₀ f₁ a z := by
  constructor
  · rintro ⟨S, hS, hline, hpair⟩
    refine ⟨S, hS,
      (lineExplained_sub_mem_iff C f₀ f₁ c₀ c₁ hc₀ hc₁ z S).mp hline, ?_⟩
    intro hp
    exact hpair <| (explainedPair_sub_mem_iff C f₀ f₁ c₀ c₁ hc₀ hc₁ S).mpr hp
  · rintro ⟨S, hS, hline, hpair⟩
    refine ⟨S, hS,
      (lineExplained_sub_mem_iff C f₀ f₁ c₀ c₁ hc₀ hc₁ z S).mpr hline, ?_⟩
    intro hp
    exact hpair <| (explainedPair_sub_mem_iff C f₀ f₁ c₀ c₁ hc₀ hc₁ S).mp hp

omit [Fintype F] in
/-- A common explaining support becomes a sparse pair after translation. -/
theorem sparseAt_sub_mem_of_explained
    (f₀ f₁ c₀ c₁ : Word) (S : Finset D) (a : ℕ)
    (hS : a ≤ S.card) (h₀ : ∀ x ∈ S, c₀ x = f₀ x)
    (h₁ : ∀ x ∈ S, c₁ x = f₁ x) :
    SparseAt (f₀ - c₀) (f₁ - c₁) a := by
  have hsupp : pairSupport (f₀ - c₀) (f₁ - c₁) ⊆ Finset.univ \ S := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxS
    rcases Finset.mem_union.mp hx with hx₀ | hx₁
    · have hne : (f₀ - c₀) x ≠ 0 := (Finset.mem_filter.mp hx₀).2
      apply hne
      change f₀ x - c₀ x = 0
      rw [h₀ x hxS]
      simp
    · have hne : (f₁ - c₁) x ≠ 0 := (Finset.mem_filter.mp hx₁).2
      apply hne
      change f₁ x - c₁ x = 0
      rw [h₁ x hxS]
      simp
  unfold SparseAt
  calc
    (pairSupport (f₀ - c₀) (f₁ - c₁)).card
        ≤ (Finset.univ \ S).card := Finset.card_le_card hsupp
    _ = (Finset.univ : Finset D).card - S.card := by
      rw [Finset.card_sdiff]
      simp
    _ = Fintype.card D - S.card := by simp
    _ ≤ Fintype.card D - a := Nat.sub_le_sub_left hS _

omit [Fintype F] [DecidableEq F] in
/-- On a column-far pair MCA-badness and CA-badness coincide. -/
theorem restrictedMCA_eq_restrictedCA_of_columnFar
    (Gamma : Finset F) (C : Submodule F Word) (f₀ f₁ : Word) (a : ℕ)
    (hfar : ColumnFar C f₀ f₁ a) :
    restrictedMCABadSlopes Gamma C f₀ f₁ a =
      restrictedCABadSlopes Gamma C f₀ f₁ a := by
  ext z
  simp only [restrictedMCABadSlopes, restrictedCABadSlopes, Finset.mem_filter]
  constructor
  · rintro ⟨hz, S, hS, hline, -⟩
    exact ⟨hz, ⟨⟨S, hS, hline⟩, hfar⟩⟩
  · rintro ⟨hz, hca⟩
    rcases hca with ⟨⟨S, hS, hline⟩, hpair⟩
    exact ⟨hz, S, hS, hline, hpair S hS⟩

omit [DecidableEq F] in
theorem B_CA_challenge_le_B_MCA_challenge (Gamma : Finset F)
    (C : Submodule F Word) (a : ℕ) :
    B_CA_challenge Gamma C a ≤ B_MCA_challenge Gamma C a := by
  refine Finset.sup_le ?_
  intro p hp
  calc
    (restrictedCABadSlopes Gamma C p.1 p.2 a).card
        ≤ (restrictedMCABadSlopes Gamma C p.1 p.2 a).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [restrictedCABadSlopes, restrictedMCABadSlopes,
            Finset.mem_filter] at hz ⊢
          rcases hz with ⟨hz, ⟨⟨S, hS, hline⟩, hfar⟩⟩
          exact ⟨hz, S, hS, hline, hfar S hS⟩
    _ ≤ B_MCA_challenge Gamma C a := by
      unfold B_MCA_challenge
      exact Finset.le_sup
        (s := (Finset.univ : Finset (Word × Word)))
        (f := fun q : Word × Word =>
          (restrictedMCABadSlopes Gamma C q.1 q.2 a).card) hp

theorem sparseMutualChallenge_le_B_MCA_challenge (Gamma : Finset F)
    (C : Submodule F Word) (a : ℕ) :
    sparseMutualChallenge Gamma C a ≤ B_MCA_challenge Gamma C a := by
  unfold sparseMutualChallenge
  refine Finset.sup_le ?_
  intro p hp
  by_cases hsparse : SparseAt p.1 p.2 a
  · simp only [hsparse, if_true]
    unfold B_MCA_challenge
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Word × Word)))
      (f := fun q : Word × Word =>
        (restrictedMCABadSlopes Gamma C q.1 q.2 a).card) hp
  · simp [hsparse]

theorem B_MCA_challenge_le_max (Gamma : Finset F)
    (C : Submodule F Word) (a : ℕ) :
    B_MCA_challenge Gamma C a ≤
      max (B_CA_challenge Gamma C a) (sparseMutualChallenge Gamma C a) := by
  refine Finset.sup_le ?_
  intro p hp
  by_cases hfar : ColumnFar C p.1 p.2 a
  · rw [restrictedMCA_eq_restrictedCA_of_columnFar Gamma C p.1 p.2 a hfar]
    have hca : (restrictedCABadSlopes Gamma C p.1 p.2 a).card ≤
        B_CA_challenge Gamma C a := by
      unfold B_CA_challenge
      exact Finset.le_sup
        (s := (Finset.univ : Finset (Word × Word)))
        (f := fun q : Word × Word =>
          (restrictedCABadSlopes Gamma C q.1 q.2 a).card) hp
    exact le_trans hca (Nat.le_max_left _ _)
  · rcases (not_columnFar_iff C p.1 p.2 a).mp hfar with
      ⟨S, hS, c₀, hc₀, c₁, hc₁, h₀, h₁⟩
    let e₀ : Word := p.1 - c₀
    let e₁ : Word := p.2 - c₁
    have hsparse : SparseAt e₀ e₁ a :=
      sparseAt_sub_mem_of_explained p.1 p.2 c₀ c₁ S a hS h₀ h₁
    have hbad : restrictedMCABadSlopes Gamma C e₀ e₁ a =
        restrictedMCABadSlopes Gamma C p.1 p.2 a := by
      ext z
      simp only [restrictedMCABadSlopes, Finset.mem_filter]
      exact and_congr_right fun _ =>
        mcaBad_sub_mem_iff C p.1 p.2 c₀ c₁ hc₀ hc₁ a z
    have hle : (restrictedMCABadSlopes Gamma C e₀ e₁ a).card ≤
        sparseMutualChallenge Gamma C a := by
      have hp' : (e₀, e₁) ∈ (Finset.univ : Finset (Word × Word)) :=
        Finset.mem_univ _
      have hsup := Finset.le_sup
        (s := (Finset.univ : Finset (Word × Word)))
        (f := fun q : Word × Word =>
          if SparseAt q.1 q.2 a
          then (restrictedMCABadSlopes Gamma C q.1 q.2 a).card
          else 0) hp'
      simpa [sparseMutualChallenge, hsparse] using hsup
    rw [← hbad]
    exact le_trans hle (Nat.le_max_right _ _)

/-- Exact challenge-restricted sparsification identity (SP3). -/
theorem exact_sparsification_challenge (Gamma : Finset F)
    (C : Submodule F Word) (a : ℕ) :
    B_MCA_challenge Gamma C a =
      max (B_CA_challenge Gamma C a) (sparseMutualChallenge Gamma C a) := by
  apply le_antisymm
  · exact B_MCA_challenge_le_max Gamma C a
  · exact max_le
      (B_CA_challenge_le_B_MCA_challenge Gamma C a)
      (sparseMutualChallenge_le_B_MCA_challenge Gamma C a)

/-- Concrete arithmetic attached to SP3 at the score-64 endpoint. -/
theorem score6400_sparse_support_cap : 262144 - 185364 = 76780 := by
  norm_num

end ProximityPrize.SubmissionLower.BCHKSExactSparsification6400
