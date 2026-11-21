import ProximityPrize.SubmissionLower.Final50GeoCover

set_option Elab.async false
namespace Final50Geo
noncomputable section
open P3 (I K node)
open K1_13 (Geom embed extend Row Shape shape OnFactor atJet)
open Final50Price (Messages lowerCap Holds SmallFactor Fits)
open scoped BigOperators Polynomial
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Total allowance for the positive-top factors after paying for the lower chart. -/
def Allocation : Prop := ∀ {w Γ s}, Messages w Γ s → ∀ (top : ℕ), top ≤ 14 →
    ∀ {n} (f : Fin n → Row 4) (pieces : Fin n → Finset K),
    (∀ i, pieces i ⊆ Γ) → (∀ i, SmallFactor (f i)) →
    (∀ i j, i ≠ j → ¬ Associated (f i) (f j)) →
    Fits top (fun i => shape (f i)) → (∑ i, Final50GeoCover.activeDegree (f i)) ≤ 157 →
    (∀ i γ, γ ∈ pieces i → OnFactor (f i) (extend (s γ))) →
    ∀ E : Final50Price.FatEquations, (∀ i γ, γ ∈ pieces i → Holds E (extend (s γ))) →
    (∑ i, (pieces i).card) ≤ 272535931964746069 - lowerCap top

/-- Count the union of the lower chart, proper factors, retained factors and exceptions. -/
theorem count_of_data (allocation : Allocation) {w Γ s} (hmsg : Messages w Γ s)
    (P : Row 4) (hP : P ≠ 0) (hbox : K1_13.InBox (shape P) ⟨125, 52, 14⟩)
    (hw : Final50Price.TrueWeightLE P Final50Price.anchorCutoff) (hactive : Final50Price.ActiveFits P 157)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0)
    (lower : ∀ top ≤ 14, Final50Price.c5 top)
    (book : Finset K) (E : Final50Price.FatEquations) (booked : book.card ≤ 140000)
    (hE : ∀ γ ∈ Γ, γ ∉ book → Holds E (extend (s γ))) :
    Γ.card ≤ 272535931964886069 := by
  classical
  obtain ⟨top, n, g, f, htop, cover⟩ := Final50GeoCover.cover_of_anchor P hP hbox hw hactive hz
  let low := Γ.filter (fun γ => atJet g (extend (s γ)) = 0)
  have low_bound : low.card ≤ lowerCap top :=
    lower top htop _ _ _ (hmsg.mono (Finset.filter_subset _ _)) _ cover.lower
      (fun _ h => (Finset.mem_filter.mp h).2)
  let pieces (i : Fin n) := Γ.filter (fun γ => γ ∉ book ∧ OnFactor (f i) (extend (s γ)))
  have part_sub (i) : pieces i ⊆ Γ := Finset.filter_subset _ _
  have on_part i : ∀ γ ∈ pieces i, OnFactor (f i) (extend (s γ)) :=
    fun _ h => (Finset.mem_filter.mp h).2.2
  have total := allocation hmsg top htop f pieces part_sub cover.factors cover.different
    cover.fits cover.active_budget on_part E
    (fun i γ hγ => hE γ (part_sub i hγ) (Finset.mem_filter.mp hγ).2.1)
  have hcap : lowerCap top ≤ 272535931964746069 := by
    interval_cases top <;> decide
  have covers : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion pieces := by
    intro γ hγ
    by_cases hb : γ ∈ book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    rcases cover.covers γ hγ with hg | ⟨i, hfi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hg⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hb, hfi⟩⟩
  calc
    Γ.card ≤ _ := Finset.card_le_card covers
    _ ≤ (book.card + low.card) + ∑ i, (pieces i).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
    _ = book.card + (low.card + ∑ i, (pieces i).card) := Nat.add_assoc _ _ _
    _ ≤ 140000 + (lowerCap top + ∑ i, (pieces i).card) :=
      Nat.add_le_add booked (Nat.add_le_add_right low_bound _)
    _ ≤ 140000 + (lowerCap top + (272535931964746069 - lowerCap top)) :=
      Nat.add_le_add_left (Nat.add_le_add_left total _) _
    _ = 272535931964886069 := by
      rw [Nat.add_sub_of_le hcap]

#print axioms count_of_data
end
end Final50Geo
