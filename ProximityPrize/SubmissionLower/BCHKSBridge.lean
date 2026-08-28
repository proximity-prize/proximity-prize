import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open scoped NNReal ProbabilityTheory
open CoreDefinitions
open ProximityGap

/-- . -/
def AffineLineGivenSetsBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (δ : ℝ) (a : ℕ) : Prop :=
  ∀ (U : Fin 2 → ι → F) (S : Finset F) (T : F → Finset ι),
    a < S.card →
    (∀ z ∈ S, (T z).card ≥ (Fintype.card ι : ℝ) * (1 - δ)) →
    (∀ z ∈ S,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (T z) ∈
        LinearCode.projectedCodeSubmod C (T z)) →
    ∃ z ∈ S, ∀ j : Fin 2,
      LinearCode.projectedWord (U j) (T z) ∈ LinearCode.projectedCodeSubmod C (T z)

/-- . -/
theorem mcaError_affineLine_le_of_givenSetsBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (δ : ℝ) (a : ℕ)
    (hgiven : AffineLineGivenSetsBound C δ a) :
    mcaError (AffineLineGenerator F) C δ ≤
      ENNReal.ofReal ((a : ℝ) / Fintype.card F) := by
  classical
  unfold mcaError
  refine iSup_le fun U => ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (show
      (Finset.univ.filter (fun z : F =>
        IsMCA (AffineLineGenerator F) C z U δ)).card ≤ a by
      by_contra hnot
      have hlarge : a < (Finset.univ.filter (fun z : F =>
          IsMCA (AffineLineGenerator F) C z U δ)).card := by omega
      let S : Finset F := Finset.univ.filter (fun z : F =>
        IsMCA (AffineLineGenerator F) C z U δ)
      have hmem (z : F) (hz : z ∈ S) :
          IsMCA (AffineLineGenerator F) C z U δ := by
        simpa [S] using hz
      let T : F → Finset ι := fun z =>
        if hz : z ∈ S then Classical.choose (hmem z hz) else ∅
      have hTspec (z : F) (hz : z ∈ S) :
          (T z).card ≥ (Fintype.card ι : ℝ) * (1 - δ) ∧
          LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (T z) ∈
            LinearCode.projectedCodeSubmod C (T z) ∧
          ∃ j : Fin 2, LinearCode.projectedWord (U j) (T z) ∉
            LinearCode.projectedCodeSubmod C (T z) := by
        rcases Classical.choose_spec (hmem z hz) with ⟨hcard, hcomb, hbad⟩
        have hTz : T z = Classical.choose (hmem z hz) := by
          simp only [T, dif_pos hz]
        rw [hTz]
        refine ⟨hcard, ?_, hbad⟩
        simpa [AffineLineGenerator, Fin.sum_univ_two] using hcomb
      obtain ⟨z, hzS, hall⟩ := hgiven U S T (by simpa [S] using hlarge)
        (fun z hz => (hTspec z hz).1) (fun z hz => (hTspec z hz).2.1)
      obtain ⟨j, hj⟩ := (hTspec z hzS).2.2
      exact hj (hall j))
  · positivity


open Finset

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [DecidableEq F]

/-- .
 -/
theorem exists_common_affine_set
    (U p : Fin 2 → ι → F) (T : Finset F) (A : F → Finset ι) (e : ℕ)
    (hT : e + 1 < T.card)
    (hAcard : ∀ z ∈ T, Fintype.card ι - e ≤ (A z).card)
    (hEq : ∀ z ∈ T, ∀ x ∈ A z,
      U 0 x + z * U 1 x = p 0 x + z * p 1 x) :
    ∃ z ∈ T, ∀ x ∈ A z, U 0 x = p 0 x ∧ U 1 x = p 1 x := by
  classical
  let B : Finset ι := Finset.univ.filter fun x =>
    U 0 x ≠ p 0 x ∨ U 1 x ≠ p 1 x
  let R : F → Finset ι := fun z => A z ∩ B
  have hRsub (z : F) : R z ⊆ B := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hRpair : (↑T : Set F).PairwiseDisjoint R := by
    rintro z hz w hw hzw
    change Disjoint (R z) (R w)
    rw [Finset.disjoint_left]
    intro x hxz hxw
    have hxAz : x ∈ A z := (Finset.mem_inter.mp hxz).1
    have hxAw : x ∈ A w := (Finset.mem_inter.mp hxw).1
    have hzEq := hEq z hz x hxAz
    have hwEq := hEq w hw x hxAw
    have hmul : (z - w) * (U 1 x - p 1 x) = 0 := by
      linear_combination hzEq - hwEq
    have hzw0 : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have hrow1 : U 1 x = p 1 x := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzw0)
    have hrow0 : U 0 x = p 0 x := by
      rw [hrow1] at hzEq
      exact add_right_cancel hzEq
    have hxB : x ∈ B := (Finset.mem_inter.mp hxz).2
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
    exact hxB.elim (fun h => h hrow0) (fun h => h hrow1)
  have hRlower (z : F) (hz : z ∈ T) : B.card ≤ (R z).card + e := by
    have hsplit := Finset.card_inter_add_card_sdiff (A z) B
    have hsdiff : (A z \ B).card ≤ Bᶜ.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp hx).2
    rw [Finset.card_compl] at hsdiff
    have ha := hAcard z hz
    have hbcard : B.card ≤ Fintype.card ι := Finset.card_le_univ B
    dsimp only [R]
    omega
  have hB : B.card ≤ e := by
    by_contra hnot
    have heB : e < B.card := Nat.lt_of_not_ge hnot
    have hsumLower : T.card * (B.card - e) ≤ ∑ z ∈ T, (R z).card := by
      calc
        T.card * (B.card - e) = ∑ z ∈ T, (B.card - e) := by
          exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
        _ ≤ ∑ z ∈ T, (R z).card := by
          exact Finset.sum_le_sum fun z hz => by
            have := hRlower z hz
            omega
    have hunionSub : (T.biUnion R).card ≤ B.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨z, hzT, hxR⟩ := Finset.mem_biUnion.mp hx
      exact hRsub z hxR
    have hunionCard : (T.biUnion R).card = ∑ z ∈ T, (R z).card :=
      Finset.card_biUnion hRpair
    rw [hunionCard] at hunionSub
    have hprod : T.card * (B.card - e) ≤ B.card := hsumLower.trans hunionSub
    have hdpos : 0 < B.card - e := Nat.sub_pos_of_lt heB
    have htlo : e + 2 ≤ T.card := by omega
    have he_mul : e ≤ e * (B.card - e) :=
      Nat.le_mul_of_pos_right e hdpos
    have hstrict : B.card < (e + 2) * (B.card - e) := by
      calc
        B.card = e + (B.card - e) := (Nat.add_sub_of_le heB.le).symm
        _ ≤ e * (B.card - e) + (B.card - e) := Nat.add_le_add_right he_mul _
        _ < e * (B.card - e) + 2 * (B.card - e) := by omega
        _ = (e + 2) * (B.card - e) := by ring
    have hprodLower : (e + 2) * (B.card - e) ≤
        T.card * (B.card - e) := Nat.mul_le_mul_right _ htlo
    omega
  by_contra hno
  push Not at hno
  have hRpos : ∀ z ∈ T, 1 ≤ (R z).card := by
    intro z hz
    obtain ⟨x, hxA, hxnot⟩ := hno z hz
    apply Finset.card_pos.mpr
    refine ⟨x, Finset.mem_inter.mpr ⟨hxA, ?_⟩⟩
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h0 : U 0 x = p 0 x
    · exact Or.inr (hxnot h0)
    · exact Or.inl h0
  have hTsum : T.card ≤ ∑ z ∈ T, (R z).card := by
    calc
      T.card = ∑ z ∈ T, 1 := by simp
      _ ≤ ∑ z ∈ T, (R z).card := Finset.sum_le_sum hRpos
  have hunionSub : (T.biUnion R).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨z, hzT, hxR⟩ := Finset.mem_biUnion.mp hx
    exact hRsub z hxR
  rw [Finset.card_biUnion hRpair] at hunionSub
  have hTB : T.card ≤ B.card := hTsum.trans hunionSub
  omega



/-- .
 -/
def AffineLineAlignmentBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (e a : ℕ) : Prop :=
  ∀ (U : Fin 2 → ι → F) (S : Finset F) (A : F → Finset ι),
    a < S.card →
    (∀ z ∈ S, Fintype.card ι - e ≤ (A z).card) →
    (∀ z ∈ S,
      LinearCode.projectedWord (fun i => U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod C (A z)) →
    ∃ p : Fin 2 → ι → F,
      (∀ j, p j ∈ C) ∧
      ∃ T : Finset F, T ⊆ S ∧ e + 1 < T.card ∧
        ∀ z ∈ T, ∀ x ∈ A z,
          U 0 x + z * U 1 x = p 0 x + z * p 1 x

/-- .
 -/
theorem givenSetsBound_of_alignmentBound
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (δ : ℝ) (e a : ℕ)
    (hsize : ∀ A : Finset ι,
      (A.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - δ) →
      Fintype.card ι - e ≤ A.card)
    (halign : AffineLineAlignmentBound C e a) :
    AffineLineGivenSetsBound C δ a := by
  classical
  intro U S A hS hAcard hcomb
  obtain ⟨p, hpC, T, hTS, hTcard, hEq⟩ :=
    halign U S A hS (fun z hz => hsize (A z) (hAcard z hz)) hcomb
  obtain ⟨z, hzT, hz⟩ :=
    exists_common_affine_set U p T A e hTcard
      (fun z hz => hsize (A z) (hAcard z (hTS hz))) hEq
  refine ⟨z, hTS hzT, fun j => ?_⟩
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨p j, hpC j, ?_⟩
  funext x
  simp only [LinearCode.projectedWord]
  rcases hz x.1 x.2 with ⟨h0, h1⟩
  fin_cases j
  · exact h0
  · exact h1

end ProximityPrize.SubmissionLower
