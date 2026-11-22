import ProximityPrize.SubmissionLower.FrontIntermediateNormalize
import ProximityPrize.SubmissionLower.FrontAssembly82268
import ProximityPrize.SubmissionLower.Scalar55RefinedList

set_option Elab.async false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace FrontIntermediate
noncomputable section

open Polynomial Finset FrobeniusLocator Front82268

abbrev cheapCap : ℕ := 250071299829416283
abbrev frontFee : ℕ := anchorFee + rankFee
abbrev slopeBudget : ℕ := 272655221524771161
abbrev coreBudget : ℕ := 272512621865658327

def CoreCount (A budget : ℕ) : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, P1.FamilyAt A M Γ →
    1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) → Γ.card ≤ budget

/-- Use the 69.55 rank matrix while keeping each original agreement witness. -/
theorem split {A : ℕ} (ha : agreement ≤ A) (u : Words) (Γ : Finset K)
    (strong : StrongFamily A u Γ) :
    Γ.card ≤ cheapCap ∨
      ∃ (Δ : Finset K) (deleted : Finset I) (M : AnchorModel u deleted), Δ ⊆ Γ ∧
        Γ.card ≤ Δ.card + frontFee ∧ Nonempty (P1.FamilyAt A M Δ) := by
  classical
  have weak := weak_bad_family ha strong
  by_cases hdef : firstRank u < L
  · exact Or.inl ((deficient_count u Γ hdef weak).trans (by decide))
  have hfirst := Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef)
  by_cases hz : nullity u = 0
  · exact Or.inl ((full_column_count u Γ hfirst hz weak).trans (by decide))
  by_cases htype : TypeAtMostOne u
  · exact Or.inl ((type_one_count u htype Γ weak).trans (by decide))
  by_cases hprincipal : HomogeneousPrincipal u
  · exact Or.inl ((principal_count u Γ hprincipal weak).trans (by decide))
  by_cases hconstant : ConstantKernel u
  · exact Or.inl ((constant_count u Γ hconstant weak).trans (by decide))
  obtain ⟨T⟩ := two_active_of_positive u (Nat.pos_of_ne_zero hz) htype hprincipal
  have hu : FrontRemainder u := ⟨two_active_nullity T, hfirst, htype, hprincipal, hconstant⟩
  let R := relation_of_two_active hu T
  have hsat := Front82268_1.proof u hu T R
  let N := normalSlopes u Γ
  have hN := normal_badFamily weak
  have hnormal := @normal_on_normalSlopes u Γ
  have hNsub : N ⊆ Γ := fun _ h => (mem_normalSlopes.mp h).1
  by_cases hmoving : MovingGCD R
  · exact Or.inl ((add_rank_exceptions u hu Γ _ (moving_count u hu T R hmoving hsat N hN hnormal)).trans
      (by decide))
  have hnone (he : N = ∅) : Γ.card ≤ cheapCap :=
    (add_rank_exceptions u hu Γ 0 (by rw [show normalSlopes u Γ = ∅ from he]; simp)).trans
      (by decide)
  by_cases hinvalid : InvalidLeft R
  · apply Or.inl
    apply hnone
    apply eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨M⟩ := strong γ hγΓ
    exact (hsat γ hnγ (weakenMark ha M)).valid hinvalid
  by_cases hne : N.Nonempty
  · obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨Bγ⟩ := strong γ hγΓ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := classify_fixed hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, ⟨weakenMark ha Bγ⟩⟩
    · let h4 := Front82268_4.of_children Front82268_4_1.proof Front82268_4_2.proof
      exact Or.inl ((add_rank_exceptions u hu Γ _ (h4 u hu T R D hsat hfour N hN hnormal)).trans (by decide))
    · let h3 := Front82268_3.of_children Front82268_3_1.proof Front82268_3_2.proof
      exact Or.inl ((add_rank_exceptions u hu Γ _ (h3 u hu T R D B hsat hnp N hN hnormal)).trans (by decide))
    · by_cases hn : UnitNorm B
      · rcases coherent_anchors ha u hu T R D B hpar hn N (fun γ hγ => strong γ (hNsub hγ)) hnormal with
          hcheap | ⟨book, sub, hbook, M, F⟩
        · exact Or.inl ((add_rank_exceptions u hu Γ _ hcheap).trans (by decide))
        · refine Or.inr ⟨N \ book, fixedNodes R, M, (sdiff_subset.trans hNsub), ?_, F⟩
          have htotal := add_rank_exceptions u hu Γ _ (card_sdiff_add_card_eq_card sub).ge
          change Γ.card ≤ ((N \ book).card + book.card) + rankFee at htotal
          unfold frontFee
          omega
      · exact Or.inl ((add_rank_exceptions u hu Γ _ (Front82268_2.proof u hu T R D B hsat hpar hn N hN hnormal)).trans
          (by decide))
  · exact Or.inl (hnone (not_nonempty_iff_eq_empty.mp hne))

/-- Loosen the agreement lower bound for a previously constructed family. -/
def weakenFamily {A B : ℕ} {u : Words} {deleted : Finset I} {Γ : Finset K}
    {M : AnchorModel u deleted} (ha : B ≤ A) (F : P1.FamilyAt A M Γ) : P1.FamilyAt B M Γ where
  scalar := F.scalar
  distinct := F.distinct
  mark γ hγ := by
    let m := F.mark γ hγ
    let b : P1.BadMarkAt _ u γ := { m.bad with agreement := ha.trans m.bad.agreement }
    exact ⟨b, m.avoids_deleted, m.scalar_fixed, m.scalar_degree, m.scalar_hits, m.pole_unit, m.identity⟩

theorem CoreCount.mono {A B C D : ℕ} (ha : B ≤ A) (hcost : C ≤ D) (h : CoreCount B C) :
    CoreCount A D := by
  intro u del M Γ F hl hu
  exact (h u del M Γ (weakenFamily ha F) hl hu).trans hcost

/-- Apply an all-model count at the original agreement, with fixed front reserves. -/
theorem count_of_marks {A core budget : ℕ} (ha : agreement ≤ A)
    (count : CoreCount A core) (hcheap : cheapCap ≤ budget) (hcost : core + frontFee ≤ budget)
    (u : Words) (Γ : Finset K) (strong : StrongFamily A u Γ) : Γ.card ≤ budget := by
  rcases split ha u Γ strong with hc | ⟨Δ, deleted, M, _, hsum, ⟨F⟩⟩
  · exact hc.trans hcheap
  have hi : M.overhead ≤ (heightCap : ℤ) := by
    have h := M.height_bound
    change (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁ ≤ heightCap
    omega
  by_cases hlo : M.overhead ≤ 0
  · have hc := P1.anchored_list_count Scalar55RefinedList.scalar_list M Δ (weakenFamily ha F) hlo
    exact (hsum.trans (Nat.add_le_add_right hc _)).trans ((by decide) : _ ≤ cheapCap) |>.trans hcheap
  · exact (hsum.trans (Nat.add_le_add_right (count u deleted M Δ F (by omega) hi) _)).trans hcost

/-- Entry point for the intermediate score cells. -/
theorem count_of_bad_slopes {A : ℕ} (ha : agreement ≤ A) (count : CoreCount A coreBudget)
    (u : Words) (Γ : Finset K) (h : ∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k A γ) :
    Γ.card ≤ slopeBudget :=
  count_of_marks ha count (by decide) (by decide) u Γ (strong_family_of_bad_slopes h)

#print axioms split
#print axioms count_of_bad_slopes
end
end FrontIntermediate
