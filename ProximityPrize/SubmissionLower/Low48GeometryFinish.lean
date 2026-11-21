import ProximityPrize.SubmissionLower.Low48Geometry
import ProximityPrize.SubmissionLower.Low48Rank
import ProximityPrize.SubmissionLower.Low48GeometryLower
import ProximityPrize.SubmissionLower.Low48Fat
import ProximityPrize.SubmissionLower.Low48FatCount
import ProximityPrize.SubmissionLower.Low48PriceTotal
import ProximityPrize.SubmissionLower.Low48BentCycleTilted

set_option Elab.async false
namespace Low48Geometry
noncomputable section
open K1_13 (extend atJet)
open Low48Price (Messages lowerCap)
open P3 (K)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

/-- Count an ordinary low-height family given the proper-cut price proof. -/
theorem of_cut {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179925 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2341)
    (proper : Low48Price.c6) : Γ.card ≤ 268648601901894977 := by
  have hm := Low48Order.messages_of_family M F hi
  have hmsg : Messages M.word Γ F.scalar := ⟨F.distinct, hm.degree, hm.hits⟩
  obtain ⟨P, hP, hbox, hw, hz⟩ := Low48Rank.exists_anchor M.word
  have hweight : Low48Price.TrueWeightLE P Low48Price.anchorCutoff := by
    apply (Low48GeometryCover.trueWeight_iff P).mpr
    rw [← Low48GeometryCover.differentialWeight_eq, ← differentialWeightedDegree]
    exact Nat.le_pred_of_lt hw
  have hvan (γ : K) (hγ : γ ∈ Γ) : atJet P (extend (F.scalar γ)) = 0 := by
    obtain ⟨T, hT, hhit⟩ := hm.hits γ hγ
    exact hz _ T (hm.degree γ hγ) hT hhit
  obtain ⟨pole, hpole⟩ := pole_of_anchor M F lo hi
  obtain ⟨book, E, hbook, hE⟩ := Low48Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole hpole
  refine count_of_data hmsg P hP hbox hweight hvan
    (fun _ h => Low48GeometryLower.lower_count h) proper Low48FatCount.proof ?_ book E hbook hE
  intro top htop n a l cost hfit hlayer hproper hfat
  have htotal := Low48PriceTotal.total top htop n a l cost hfit hlayer hproper hfat
  have hcap : lowerCap top ≤ Low48PriceCaps.budget := by
    interval_cases top <;> decide
  calc
    lowerCap top + ∑ i, cost i ≤ lowerCap top + Low48PriceCaps.factorCap top :=
      Nat.add_le_add_left htotal _
    _ = Low48PriceCaps.budget := Nat.add_sub_of_le hcap

theorem count {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179925 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2341) : Γ.card ≤ 268648601901894977 :=
  of_cut M F lo hi (Low48GeometryCut.proof Low48BentCycle.mixed_tilted)

#print axioms count
end
end Low48Geometry
