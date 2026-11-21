import ProximityPrize.SubmissionLower.Low52At2390Geo
import ProximityPrize.SubmissionLower.Low52At2390Order
import ProximityPrize.SubmissionLower.Low52At2390Lower
import ProximityPrize.SubmissionLower.Low52At2390Fat
import ProximityPrize.SubmissionLower.ModelExactPole
import ProximityPrize.SubmissionLower.Low52At2390Anchor

set_option Elab.async false
namespace Low52At2390Geo
noncomputable section
open K1_13 (Geom extend atJet)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Count every ordinary family at 179,905 agreements through height 2,390. -/
theorem count_of_allocation (allocation : Allocation) {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179905 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2390) : Γ.card ≤ 272512621865658327 := by
  have hm := Low52At2390Order.messages_of_family M F hi
  obtain ⟨P, hP, hbox, active, weight, vanishes⟩ := Low52At2390Anchor.exists_anchor M.word
  have hw : Low52At2390Price.TrueWeightLE P Low52At2390Price.anchorCutoff := by
    apply (Low52At2390GeoCover.trueWeight_iff P).mpr
    rw [← Low52At2390GeoCover.differentialWeight_eq, ← differentialWeightedDegree]
    exact weight
  have zero (γ) (hγ : γ ∈ Γ) : atJet P (extend (F.scalar γ)) = 0 := by
    obtain ⟨T, size, hits⟩ := hm.hits γ hγ
    exact vanishes _ T (hm.degree γ hγ) size hits
  obtain ⟨pole, degree⟩ := ModelExactPole.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree ≤ 2390 := by rw [degree]; omega
  obtain ⟨book, E, hbook, hE⟩ := Low52At2390Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole small
  exact count_of_data allocation hm P hP hbox hw active zero (fun _ ht => Low52At2390Lower.lower_count ht)
    book E hbook hE

#print axioms count_of_allocation
end
end Low52At2390Geo
