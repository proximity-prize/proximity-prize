import ProximityPrize.SubmissionLower.Final50Geo
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.Final50Lower
import ProximityPrize.SubmissionLower.Final50Fat
import ProximityPrize.SubmissionLower.ModelExactPole
import ProximityPrize.SubmissionLower.Final50Anchor

set_option Elab.async false
namespace Final50Geo
noncomputable section
open K1_13 (Geom extend atJet)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Count every ordinary family at 179,925 agreements through height 2,404. -/
theorem count_of_allocation (allocation : Allocation) {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179925 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2404) : Γ.card ≤ 272535931964886069 := by
  have hm := Final50Order.messages_of_family M F hi
  obtain ⟨P, hP, hbox, active, weight, vanishes⟩ := Final50Anchor.exists_anchor M.word
  have hw : Final50Price.TrueWeightLE P Final50Price.anchorCutoff := by
    apply (Final50GeoCover.trueWeight_iff P).mpr
    rw [← Final50GeoCover.differentialWeight_eq, ← differentialWeightedDegree]
    exact weight
  have zero (γ) (hγ : γ ∈ Γ) : atJet P (extend (F.scalar γ)) = 0 := by
    obtain ⟨T, size, hits⟩ := hm.hits γ hγ
    exact vanishes _ T (hm.degree γ hγ) size hits
  obtain ⟨pole, degree⟩ := ModelExactPole.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree ≤ 2404 := by rw [degree]; omega
  obtain ⟨book, E, hbook, hE⟩ := Final50Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole small
  exact count_of_data allocation hm P hP hbox hw active zero (fun _ ht => Final50Lower.lower_count ht)
    book E hbook hE

#print axioms count_of_allocation
end
end Final50Geo
