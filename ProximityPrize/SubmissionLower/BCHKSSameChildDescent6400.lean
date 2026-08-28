import ProximityPrize.SubmissionLower.BCHKSCrossChildRouting6400
import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization

/-!
# Same-child terminal/descent split

A positive normalized child always divides its parent.  Exposing the cofactor
gives the sound dichotomy needed by centered recursion: a degree-zero cofactor
is terminal in the root variable, while a positive-degree cofactor forces
strict descent of the child's root-variable degree.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F] [DecidableEq F]

/-- A positive normalized child either carries all of the parent's
root-variable degree, or has strictly smaller root-variable degree.  The
cofactor is retained because a nonunit coefficient-variable factor can leave
`natDegree` unchanged. -/
theorem positiveChild_terminal_or_strict_natDegree
    (B H : F[X][Y]) (hB : B ≠ 0) (hH : H ∈ positiveChildren B) :
    ∃ C : F[X][Y],
      B = H * C ∧ C ≠ 0 ∧
      ((C.natDegree = 0 ∧ H.natDegree = B.natDegree) ∨
        (0 < C.natDegree ∧ H.natDegree < B.natDegree)) := by
  have hmem : H ∈ UniqueFactorizationMonoid.normalizedFactors B :=
    (mem_positiveChildren_iff.mp hH).1
  have hH0 : H ≠ 0 :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hmem).ne_zero
  obtain ⟨C, hBC⟩ :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
  have hC0 : C ≠ 0 := by
    intro hC
    apply hB
    rw [hBC, hC, mul_zero]
  have hdeg : B.natDegree = H.natDegree + C.natDegree := by
    rw [hBC, Polynomial.natDegree_mul hH0 hC0]
  refine ⟨C, hBC, hC0, ?_⟩
  rcases Nat.eq_zero_or_pos C.natDegree with hzero | hpos
  · exact Or.inl ⟨hzero, by omega⟩
  · exact Or.inr ⟨hpos, by omega⟩

/-- For a primitive parent, the degree-zero-cofactor terminal case identifies
the child with the whole parent up to a unit.  Otherwise the recursion moves
to strictly smaller root-variable degree. -/
theorem positiveChild_associated_or_strictNatDegree
    (B H : F[X][Y]) (hB : B ≠ 0) (hprim : B.IsPrimitive)
    (hH : H ∈ positiveChildren B) :
    Associated H B ∨ H.natDegree < B.natDegree := by
  rcases positiveChild_terminal_or_strict_natDegree B H hB hH with
    ⟨_, _, _, hterminal | hdesc⟩
  · left
    have hmem : H ∈ UniqueFactorizationMonoid.normalizedFactors B :=
      (mem_positiveChildren_iff.mp hH).1
    have hirr : Irreducible H :=
      (UniqueFactorizationMonoid.prime_of_normalized_factor H hmem).irreducible
    exact associated_of_isPrimitive_irreducible_dvd_full_natDegree
      hprim hirr
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
        hterminal.2
  · exact Or.inr hdesc.2

/-- Both additive support masses are inherited by every positive child. -/
theorem positiveChild_natDegree_degreeX_le
    (B H : F[X][Y]) (hB : B ≠ 0) (hH : H ∈ positiveChildren B) :
    H.natDegree ≤ B.natDegree ∧ degreeX H ≤ degreeX B := by
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
  dsimp only at hsums
  have hYterm : H.natDegree ≤
      ∑ J ∈ positiveChildren B, J.natDegree := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hH
  have hXterm : degreeX H ≤
      ∑ J ∈ positiveChildren B, degreeX J := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hH
  constructor
  · exact hYterm.trans (by simpa [positiveChildren] using hsums.1)
  · exact hXterm.trans (by simpa [positiveChildren] using hsums.2)

/-- A positive normalized child is strictly lower in root-variable degree
whenever the parent has another distinct positive normalized child. -/
theorem positiveChild_natDegree_lt_of_distinct_sibling
    (B H J : F[X][Y]) (hB : B ≠ 0)
    (hH : H ∈ positiveChildren B)
    (hJ : J ∈ positiveChildren B)
    (hne : H ≠ J) :
    H.natDegree < B.natDegree := by
  classical
  have hsums := positiveNormalizedFactors_sum_natDegree_degreeX_le B hB
  dsimp only at hsums
  have hsum : (∑ K ∈ positiveChildren B, K.natDegree) ≤
      B.natDegree := by
    simpa [positiveChildren] using hsums.1
  have hpair : H.natDegree + J.natDegree ≤
      ∑ K ∈ positiveChildren B, K.natDegree := by
    calc
      H.natDegree + J.natDegree =
          ∑ K ∈ ({H, J} : Finset (F[X][Y])), K.natDegree := by
            simp [hne]
      _ ≤ ∑ K ∈ positiveChildren B, K.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro K hK
          simp only [Finset.mem_insert, Finset.mem_singleton] at hK
          rcases hK with rfl | rfl
          · exact hH
          · exact hJ
        · simp
  have hJpos : 0 < J.natDegree := (mem_positiveChildren_iff.mp hJ).2
  omega

/-- Cap-preserving primitive recursion package. -/
theorem positiveChild_capped_associated_or_strictNatDegree
    (B H : F[X][Y]) (hB : B ≠ 0) (hprim : B.IsPrimitive)
    (hH : H ∈ positiveChildren B) (M D : ℕ)
    (hY : B.natDegree ≤ M) (hX : degreeX B ≤ D) :
    H.natDegree ≤ M ∧ degreeX H ≤ D ∧
      (Associated H B ∨ H.natDegree < B.natDegree) := by
  have hcaps := positiveChild_natDegree_degreeX_le B H hB hH
  exact ⟨hcaps.1.trans hY, hcaps.2.trans hX,
    positiveChild_associated_or_strictNatDegree B H hB hprim hH⟩

variable [Fintype F]

/-- Complete owner routing at a common specialized root.  A distinct owner is
charged to the cross-child resultant set.  A common owner exposes a cofactor,
and hence either terminates in the root variable or recurses at strictly
smaller `natDegree`. -/
theorem crossChild_or_sameChild_terminal_or_strictNatDegree
    (B Hsection Hwitness : F[X][Y]) (z y : F) (hB : B ≠ 0)
    (hsection : Hsection ∈ positiveChildren B)
    (hwitness : Hwitness ∈ positiveChildren B)
    (hsectionRoot :
      (Hsection.map (Polynomial.evalRingHom z)).eval y = 0)
    (hwitnessRoot :
      (Hwitness.map (Polynomial.evalRingHom z)).eval y = 0) :
    z ∈ crossChildChallenges B ∨
      (Hsection = Hwitness ∧
        ∃ C : F[X][Y],
          B = Hsection * C ∧ C ≠ 0 ∧
          ((C.natDegree = 0 ∧ Hsection.natDegree = B.natDegree) ∨
            (0 < C.natDegree ∧ Hsection.natDegree < B.natDegree))) := by
  rcases same_child_or_mem_crossChildChallenges B Hsection Hwitness z y
      hsection hwitness hsectionRoot hwitnessRoot with hsame | hcross
  · exact Or.inr ⟨hsame,
      positiveChild_terminal_or_strict_natDegree B Hsection hB hsection⟩
  · exact Or.inl hcross

/-- Primitive-parent form used by the well-founded centered recursion. -/
theorem crossChild_or_sameChild_associated_or_strictNatDegree
    (B Hsection Hwitness : F[X][Y]) (z y : F)
    (hB : B ≠ 0) (hprim : B.IsPrimitive)
    (hsection : Hsection ∈ positiveChildren B)
    (hwitness : Hwitness ∈ positiveChildren B)
    (hsectionRoot :
      (Hsection.map (Polynomial.evalRingHom z)).eval y = 0)
    (hwitnessRoot :
      (Hwitness.map (Polynomial.evalRingHom z)).eval y = 0) :
    z ∈ crossChildChallenges B ∨
      (Hsection = Hwitness ∧
        (Associated Hsection B ∨ Hsection.natDegree < B.natDegree)) := by
  rcases same_child_or_mem_crossChildChallenges B Hsection Hwitness z y
      hsection hwitness hsectionRoot hwitnessRoot with hsame | hcross
  · exact Or.inr ⟨hsame,
      positiveChild_associated_or_strictNatDegree B Hsection hB hprim hsection⟩
  · exact Or.inl hcross

/-- If a selected child has a distinct positive sibling, the same-child arm
of owner routing is automatically a strict well-founded descent. -/
theorem crossChild_or_sameChild_strictNatDegree_of_distinct_sibling
    (B Hsection Hwitness J : F[X][Y]) (z y : F)
    (hB : B ≠ 0)
    (hsection : Hsection ∈ positiveChildren B)
    (hwitness : Hwitness ∈ positiveChildren B)
    (hJ : J ∈ positiveChildren B)
    (hJne : Hsection ≠ J)
    (hsectionRoot :
      (Hsection.map (Polynomial.evalRingHom z)).eval y = 0)
    (hwitnessRoot :
      (Hwitness.map (Polynomial.evalRingHom z)).eval y = 0) :
    z ∈ crossChildChallenges B ∨
      (Hsection = Hwitness ∧ Hsection.natDegree < B.natDegree) := by
  rcases same_child_or_mem_crossChildChallenges B Hsection Hwitness z y
      hsection hwitness hsectionRoot hwitnessRoot with hsame | hcross
  · exact Or.inr ⟨hsame,
      positiveChild_natDegree_lt_of_distinct_sibling B Hsection J hB
        hsection hJ hJne⟩
  · exact Or.inl hcross

end ProximityPrize.SubmissionLower
