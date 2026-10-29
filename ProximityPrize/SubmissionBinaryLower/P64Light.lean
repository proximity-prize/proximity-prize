import ProximityPrize.SubmissionBinaryLower.P64Shorten

/-!
# Full lines: Lemma AF and Theorem Q2 (PROOF.md 4.4, 4.10.4)

`BadData` packages the facts about the bad slopes on a factor `R` used by the class bounds:
witnesses of degree at most `D` through the curve, full agreement sets of size at least `A`, and
badness of the pair on each agreement set.

- `card_le_of_full_subset`: `L` full lines in every agreement set but `d` per line, so
  `|Vs| ≤ L·d + |B(Λ*)|` (Theorem Q2(b), Corollary S3, Lemma AF(1)).
- `card_le_of_afLight`: Lemma AF(1), (2): at least 208984 full lines, or at most 208983 lines,
  gives `|Vs| ≤ 208984·d + 117013736431`.
- `not_dangerous_of_quadric`: Theorem Q2(a) in the form "fewer than 208984 full lines": a quadric
  then has no dangerous slope.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Light

open Polynomial BCHKSSubstitutionVanish P64LineOrder P64Incidence P64Shorten P64Cofactor

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- The line `Y = u0 i + Z·u1 i`. -/
noncomputable def lineOf (u₀ u₁ : ι → F) (i : ι) : F[X] :=
  (Polynomial.C (u₀ i) : F[X]) + Polynomial.X * Polynomial.C (u₁ i)

lemma lineOf_natDegree_le (u₀ u₁ : ι → F) (i : ι) : (lineOf u₀ u₁ i).natDegree ≤ 1 := by
  unfold lineOf
  refine natDegree_add_le_of_degree_le (by simp) ?_
  exact (natDegree_mul_le).trans (by simp)

lemma eval_lineOf (u₀ u₁ : ι → F) (i : ι) (z : F) :
    (lineOf u₀ u₁ i).eval z = u₀ i + z * u₁ i := by
  simp only [lineOf, eval_add, eval_mul, eval_C, eval_X]

/-- The facts about the bad slopes `Vs` on `R` used by the class bounds. -/
structure BadData (ω : ι ↪ F) (u₀ u₁ : ι → F) (R : Polynomial (Polynomial (Polynomial F)))
    (Vs : Finset F) (P : F → F[X]) (Az : F → Finset ι) : Prop where
  on_curve : ∀ z ∈ Vs, triEval R z (P z) = 0
  deg : ∀ z ∈ Vs, (P z).natDegree ≤ 1048575
  card : ∀ z ∈ Vs, 1482911 ≤ (Az z).card
  agree : ∀ z ∈ Vs, ∀ i, i ∈ Az z ↔ (P z).eval (ω i) = u₀ i + z * u₁ i
  bad : ∀ z ∈ Vs, ¬ ∃ p₀ p₁ : F[X], p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
    ∀ i ∈ Az z, p₀.eval (ω i) = u₀ i ∧ p₁.eval (ω i) = u₁ i

/-- The full lines of `R`. -/
noncomputable def full (ω : ι ↪ F) (u₀ u₁ : ι → F) (R : Polynomial (Polynomial (Polynomial F))) :
    Finset ι :=
  Finset.univ.filter fun i => lineOrd R (ω i) (lineOf u₀ u₁ i) = R.natDegree

/-- `L` full lines: `|Vs| ≤ L·d + |B(Λ*)|`. -/
theorem card_le_of_full_subset (ω : ι ↪ F) (u₀ u₁ : ι → F)
    {R : Polynomial (Polynomial (Polynomial F))} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    {Vs : Finset F} {P : F → F[X]} {Az : F → Finset ι} (hd : BadData ω u₀ u₁ R Vs P Az)
    (Λs : Finset ι) (hΛ : Λs ⊆ full ω u₀ u₁ R) :
    Vs.card ≤ Λs.card * P64Caps.YZ.yzSupportDegree R 1 +
      (Vs.filter fun z => Λs ⊆ Az z).card := by
  classical
  have hcover : Vs ⊆ Λs.biUnion (fun i => Vs.filter fun z => i ∉ Az z) ∪
      Vs.filter fun z => Λs ⊆ Az z := by
    intro z hz
    by_cases hsub : Λs ⊆ Az z
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hsub⟩)
    · apply Finset.mem_union_left
      rw [Finset.not_subset] at hsub
      obtain ⟨i, hi, hiA⟩ := hsub
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hz, hiA⟩⟩
  have hline : ∀ i ∈ Λs, (Vs.filter fun z => i ∉ Az z).card ≤
      P64Caps.YZ.yzSupportDegree R 1 := by
    intro i hi
    have hfull := hΛ hi
    simp only [full, Finset.mem_filter, Finset.mem_univ, true_and] at hfull
    exact card_filter_not_mem_le_of_full ω (lineOf u₀ u₁) hirr hpos i hfull Vs P Az
      hd.on_curve (fun z hz h => (hd.agree z hz i).mpr (by rw [h, eval_lineOf]))
  calc Vs.card ≤ _ := Finset.card_le_card hcover
    _ ≤ (Λs.biUnion (fun i => Vs.filter fun z => i ∉ Az z)).card +
          (Vs.filter fun z => Λs ⊆ Az z).card := Finset.card_union_le _ _
    _ ≤ _ := by
        gcongr
        calc _ ≤ ∑ i ∈ Λs, (Vs.filter fun z => i ∉ Az z).card := Finset.card_biUnion_le
          _ ≤ ∑ i ∈ Λs, P64Caps.YZ.yzSupportDegree R 1 := Finset.sum_le_sum hline
          _ = _ := by rw [Finset.sum_const, smul_eq_mul]

/-- **Lemma AF(1), (2).** -/
theorem card_le_of_afLight (ω : ι ↪ F) (hn : Fintype.card ι = 2097152) (u₀ u₁ : ι → F)
    {R : Polynomial (Polynomial (Polynomial F))} (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree)
    {Vs : Finset F} {P : F → F[X]} {Az : F → Finset ι} (hd : BadData ω u₀ u₁ R Vs P Az)
    (hlight : 208984 ≤ (full ω u₀ u₁ R).card ∨ (lam ω (lineOf u₀ u₁) R).card ≤ 208983) :
    Vs.card ≤ 208984 * P64Caps.YZ.yzSupportDegree R 1 + 117013736431 := by
  classical
  rcases hlight with hf | hl
  · obtain ⟨Λs, hΛsub, hΛcard⟩ := Finset.exists_subset_card_eq hf
    have h1 := card_le_of_full_subset ω u₀ u₁ hirr hpos hd Λs hΛsub
    have h2 := card_filter_subset_le_208984 ω hn u₀ u₁ Λs hΛcard Vs P Az hd.deg hd.card
      (fun z hz i hi => (hd.agree z hz i).mp hi) hd.bad
    rw [hΛcard] at h1
    omega
  · have := card_le_of_few_lines ω (lineOf u₀ u₁) (lineOf_natDegree_le u₀ u₁) hn R
      hirr.ne_zero Vs P Az hd.on_curve
      (fun z hz i hi => by rw [eval_lineOf]; exact (hd.agree z hz i).mp hi) hd.card hl
    omega

/-- **Theorem Q2(a)**, in the form used: a quadric with fewer than 208984 full lines has no
dangerous slope (`w ≥ 2D` and `μ_i ≤ 2`). -/
theorem not_dangerous_of_quadric (ω : ι ↪ F) (u₀ u₁ : ι → F)
    {R : Polynomial (Polynomial (Polynomial F))} (hirr : Irreducible R) (h2 : R.natDegree = 2)
    (hfew : (full ω u₀ u₁ R).card < 208984) (Az : Finset ι) :
    ¬ Dangerous ω (lineOf u₀ u₁) 1048575 1482911 R Az := by
  classical
  unfold Dangerous
  push Not
  have hw := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero 1048575
  rw [h2] at hw
  have hμ : ∀ i, lineOrd R (ω i) (lineOf u₀ u₁ i) ≤ 2 := fun i => by
    have := lineOrd_le_natDegree_of_irreducible hirr (by omega) (ω i) (lineOf u₀ u₁ i)
    omega
  have hterm : ∀ i ∈ Az, ((lineOrd R (ω i) (lineOf u₀ u₁ i) : ℤ) - 1) ≤
      if i ∈ full ω u₀ u₁ R then 1 else 0 := by
    intro i _
    have := hμ i
    split_ifs with hf
    · omega
    · simp only [full, Finset.mem_filter, Finset.mem_univ, true_and, h2] at hf
      omega
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hc : ((Az ∩ full ω u₀ u₁ R).card : ℤ) ≤ (full ω u₀ u₁ R).card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hfew' : ((full ω u₀ u₁ R).card : ℤ) < 208984 := by exact_mod_cast hfew
  have hwZ : (1048575 * 2 : ℤ) ≤ P64Caps.Weighted.weightedSupportDegree R 1048575 := by
    exact_mod_cast hw
  push_cast at *
  linarith

end P64Light
end ProximityPrize.SubmissionBinaryLower
