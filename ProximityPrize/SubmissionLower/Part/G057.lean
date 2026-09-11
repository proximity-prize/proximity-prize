import ProximityPrize.SubmissionLower.Part.G056


section Compact_SecondJetExceptionalComponents
/-! Components containing a fixed coefficient have no seeds after excluding
that coefficient's vanishing codewords. -/
namespace ProximityPrize.SubmissionLower.SecondJetExceptionalComponents
open MvPolynomial RCN264
open scoped Classical
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K] {Seed : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Seed := Classical.decEq Seed

theorem component_empty_of_nonvanishing (F A H T : MvPolynomial (Fin 3) K)
    (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (C : RegularComponent K F A H) (hT : T ∈ C.1)
    (hne : ∀ x ∈ Gamma, MvPolynomial.eval (point x) T ≠ 0) :
    (componentSeeds K F A H Gamma point C).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxG := componentSeeds_subset K F A H Gamma point C hx
  have hpoint := componentSeeds_on_prime K F A H Gamma point C x hx
  have hz := hpoint hT
  exact hne x hxG hz

def goodSeeds (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (T : MvPolynomial (Fin 3) K) : Finset Seed := by
  classical
  exact Gamma.filter (fun x => MvPolynomial.eval (point x) T ≠ 0)

def exceptionalSeeds (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (T : MvPolynomial (Fin 3) K) : Finset Seed := by
  classical
  exact Gamma.filter (fun x => MvPolynomial.eval (point x) T = 0)

theorem card_partition (Gamma : Finset Seed) (point : Seed → Fin 3 → K)
    (T : MvPolynomial (Fin 3) K) :
    Gamma.card = (goodSeeds Gamma point T).card+(exceptionalSeeds Gamma point T).card := by
  classical
  simpa only [goodSeeds,exceptionalSeeds,not_not] using
    (Finset.card_filter_add_card_filter_not
      (s := Gamma) (p := fun x => MvPolynomial.eval (point x) T ≠ 0)).symm


end
end ProximityPrize.SubmissionLower.SecondJetExceptionalComponents

end Compact_SecondJetExceptionalComponents
