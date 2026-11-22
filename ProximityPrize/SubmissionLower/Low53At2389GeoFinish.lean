import ProximityPrize.SubmissionLower.Low53At2389Geo
import ProximityPrize.SubmissionLower.Low53At2389Order
import ProximityPrize.SubmissionLower.Low53At2389Lower
import ProximityPrize.SubmissionLower.Low53At2389Fat
import ProximityPrize.SubmissionLower.ModelExactPole
import ProximityPrize.SubmissionLower.Low53At2389Anchor

set_option Elab.async false
namespace Low53At2389Geo
noncomputable section
open K1_13 (Geom extend atJet)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Count every ordinary family at 179,896 agreements through height 2,377. -/
theorem count_of_allocation (allocation : Allocation) {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179896 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2389) : Γ.card ≤ 272512621865658327 := by
  have hm := Low53At2389Order.messages_of_family M F hi
  obtain ⟨P, hP, hbox, active, weight, vanishes⟩ := Low53At2389Anchor.exists_anchor M.word
  have hw : Low53At2389Price.TrueWeightLE P Low53At2389Price.anchorCutoff := by
    apply (Low53At2389GeoCover.trueWeight_iff P).mpr
    rw [← Low53At2389GeoCover.differentialWeight_eq, ← differentialWeightedDegree]
    exact weight
  have zero (γ) (hγ : γ ∈ Γ) : atJet P (extend (F.scalar γ)) = 0 := by
    obtain ⟨T, size, hits⟩ := hm.hits γ hγ
    exact vanishes _ T (hm.degree γ hγ) size hits
  obtain ⟨pole, degree⟩ := ModelExactPole.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree ≤ 2389 := by rw [degree]; omega
  obtain ⟨book, E, hbook, hE⟩ := Low53At2389Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole small
  exact count_of_data allocation hm P hP hbox hw active zero (fun _ ht => Low53At2389Lower.lower_count ht)
    book E hbook hE

#print axioms count_of_allocation
end
end Low53At2389Geo
