import ProximityPrize.SubmissionLower.Final50PriceActiveAllocation
import ProximityPrize.SubmissionLower.Final50GeoFinish
import ProximityPrize.SubmissionLower.Final50FatCount
import ProximityPrize.SubmissionLower.Shared50Count
import ProximityPrize.SubmissionLower.KoalaRetainedPrimary
import ProximityPrize.SubmissionLower.KoalaRetainedCount

set_option maxHeartbeats 1800000

namespace KoalaLow6954
noncomputable section

open P3 (K)
open K1_13 (Row shape extend InBox OnFactor atJet)
open Final50Price (Messages SmallFactor ActiveFits ProperCut)
open scoped BigOperators Polynomial
open private P3_6_8.shapeSum from ProximityPrize.SubmissionLower.GoldBranch6N8

def AdaptiveCount : Prop :=
  ∀ w Γ s, Messages w Γ s → ∀ f, SmallFactor f → ActiveFits f 165 →
    (∀ γ ∈ Γ, OnFactor f (extend (s γ))) → ∀ l, 0 < l → ProperCut f Γ s l →
    ∀ u, KoalaWeightedRate.Allowed (shape f) u → ¬ Final50SharedPrice.RateFits (shape f) u →
      Γ.card ≤ Final50SharedPrice.price (shape f) l 165 u

private theorem allocation (adaptive : AdaptiveCount) : KoalaRetainedCut.Allocation 267872462194060158 165 := by
  intro w Γ s hmsg top htop E d
  let f := d.f
  let l := d.orders
  let parts := d.pieces
  have hz : d.zeros = Finset.univ.filter (fun i => l i = 0) := by
    ext i
    simp [d.zero_iff, l]
  have hr : KoalaRetainedCut.sumShape d.zeros (fun i => shape (f i)) =
      Final50PriceTotal.retainedShape (fun i => shape (f i)) l := by
    rw [hz]
    rfl
  have count : (∑ i, (parts i).card) ≤ Final50PriceCaps.factorCap top := by
    apply Final50PriceTotal.total top htop d.n (fun i => shape (f i)) l (fun i => (parts i).card)
       d.fits d.layers
    · intro i m hm hml k hk
      have hi : 0 < l i := hm.trans_le hml
      have hnot : i ∉ d.zeros := fun h => (Nat.ne_of_gt hi) ((d.zero_iff i).mp h)
      have hactive := Final50PriceActiveAllocation.factor_fits f l d.active_budget hi hk
      have hfloor : InBox (Final50PriceCaps.start k) (KoalaRetainedCut.sumShape d.zeros (fun j => shape (f j))) := by
        rw [hr]
        exact hk.1
      exact d.contracted i hnot m hm hml _ hactive _ hfloor
    · intro i m u hm hml allowed
      have hactive : ActiveFits (f i) 165 := (Final50GeoCover.activeFits_iff _ _).mpr
        ((Finset.single_le_sum (fun j _ => Nat.zero_le (Final50GeoCover.activeDegree (f j)))
          (Finset.mem_univ i)).trans d.active_budget)
      obtain ⟨Q,hproper,hbox,hw,ha,ho⟩ := d.proper i (hm.trans_le hml)
      have hcut : ProperCut (f i) (parts i) s m :=
        ⟨Q,hproper,hbox,hw,ha,fun γ hγ e he => hml.trans (ho γ (d.subset i hγ) e he)⟩
      by_cases hstock : Final50SharedPrice.RateFits (shape (f i)) u
      · exact Shared50Count.proof w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i) 165
          hactive (d.on_factor i) m hm hcut u hstock
      · exact adaptive w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i)
          hactive (d.on_factor i) m hm hcut u allowed hstock
    · intro i heligible
      exact Final50FatCount.proof w (parts i) s (hmsg.mono (d.subset i)) (f i) (d.small i)
        (d.on_factor i) heligible E (d.fat i)
  have hcap : Final50Price.lowerCap top ≤ 267872462194060158 := by interval_cases top <;> decide
  change (∑ i, (parts i).card) ≤ 267872462194060158 - Final50Price.lowerCap top at count
  change Final50Price.lowerCap top + (∑ i, (parts i).card) ≤ 267872462194060158
  omega

theorem count_with (adaptive : AdaptiveCount) {cap u del Γ}
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179886 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2413) : Γ.card ≤ 267872462194200158 := by
  have hm := Final50Order.messages_of_family M F hi
  obtain ⟨P,hP,hbox,hactive,weight,vanishes⟩ := Final50Anchor.exists_anchor M.word
  have hw : Final50Price.TrueWeightLE P Final50Price.anchorCutoff := by
    apply (Final50GeoCover.trueWeight_iff P).mpr
    rw [← Final50GeoCover.differentialWeight_eq, ← PolynomialDifferential.differentialWeightedDegree]
    exact weight
  have hz (γ) (hγ : γ ∈ Γ) : atJet P (extend (F.scalar γ)) = 0 := by
    obtain ⟨T,hT,hh⟩ := hm.hits γ hγ
    exact vanishes _ T (hm.degree γ hγ) hT hh
  obtain ⟨pole,degree⟩ := ModelExactPole.exists_pole M F lo (hi.trans (by decide))
  have small : pole.H.natDegree ≤ 2413 := by rw [degree]; omega
  obtain ⟨book,E,hbook,hE⟩ := Final50Fat.fat_equations M.word Γ F.scalar hm.degree hm.hits pole small
  exact KoalaRetainedCut.count_of_data (allocation adaptive) hm
    (KoalaRetainedCut.Bank.of_messages hm) (KoalaRetainedCut.Bank.of_messages_ranked hm)
    P hP hbox hw hactive hz (fun _ ht => Final50Lower.lower_count ht) book E hbook hE

#print axioms count_with
end
end KoalaLow6954
