import ProximityPrize.SubmissionLower.Final50Geo
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.Final50Lower
import ProximityPrize.SubmissionLower.Final50Fat
import ProximityPrize.SubmissionLower.ModelExactPole
import ProximityPrize.SubmissionLower.Final50Anchor
import ProximityPrize.SubmissionLower.Final50PriceActiveAllocation
import ProximityPrize.SubmissionLower.Final50BentCycleTilted
import ProximityPrize.SubmissionLower.Final50FatCount

set_option Elab.async false
namespace Final50Geo
noncomputable section
open K1_13 (Geom extend atJet)
open PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Count every ordinary family at 179,915 agreements through height 2,353. -/
theorem count_of_allocation (allocation : Allocation) {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179915 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2353) : Γ.card ≤ 272345433993724332 := by
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
  have small : pole.H.natDegree ≤ 2353 := by rw [degree]; omega
  obtain ⟨book, E, hbook, hE⟩ := Final50Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole small
  exact count_of_data allocation hm P hP hbox hw active zero (fun _ ht => Final50Lower.lower_count ht)
    book E hbook hE

theorem allocation : Allocation := by
  intro w Γ s hm top ht n f pieces hsub hsmall hdiff hfits hactive hon E hE
  obtain ⟨l, hlayers, hcut⟩ := Final50Order.proper_layers hm
    (fun i => (hsmall i).1) (fun i => (hsmall i).2.1)
    (fun i => (hsmall i).2.2.1.2.2.trans_lt (by decide : 13 < K1.p)) hdiff
  exact Final50PriceActiveAllocation.sum_cost top ht f l pieces hm hsub hsmall
    hfits hactive hlayers hon hcut E hE
    (Final50GeometryCut.proof Final50BentCycle.mixed_tilted) Final50FatCount.proof

/-- The ordinary slope count through height 2353 at 82,229 errors. -/
theorem count {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179915 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2353) : Γ.card ≤ 272345433993724332 :=
  count_of_allocation allocation M F lo hi

#print axioms count
#print axioms count_of_allocation
end
end Final50Geo
