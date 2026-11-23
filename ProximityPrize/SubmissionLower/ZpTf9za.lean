import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.ZbpKj1d
import ProximityPrize.SubmissionLower.ZG7dIPe
set_option Elab.async false
set_option autoImplicit true
namespace ap9
noncomputable section
open Polynomial K1 aR dN rW wH Rl
open scoped BigOperators
def c1 :Prop :=
  ∀ (f :af 4) (T:Li f) (A:kT),akB f A→XP f T A
def c3:Prop :=rW.c5
def c4 :Prop :=
  ∀ (f :af 4) (T:Li f) (A:kT),akB f A→XP f T A →
    dimension A=3 →
    MvPolynomial.affineDegree A≤MvPolynomial.affineDegree (lA A) *
      ((rH (shape f)).b:ℚ)^2
open MvPolynomial
private def aFG (f :af 4) (T:Li f) (A:kT) :Prop :=
  (dimension A=2∧lA A∈Ji f T.test) ∨
    (dimension A=3∧lA A∈aFs f)
private theorem dfX (S:Finset kT) (V:Finset n8)
    (hinj:Set.InjOn lA (S:Set kT))
    (hV : ∀ A∈S,lA A∈V) :
    ∑ A∈S,affineDegree (lA A) ≤ ∑ P∈V,affineDegree P:= by
  classical
  have hsub:S.image lA⊆V:= by
    intro P hp
    obtain ⟨A,ha,rfl⟩:=Finset.mem_image.mp hp
    exact hV A ha
  calc
    _ = ∑ P∈S.image lA,affineDegree P:=(Finset.sum_image hinj).symm
    _≤_:=Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _=>affineDegree_nonneg P)
end
end ap9
