import ProximityPrize.SubmissionLower.Koala6844VirtualShortAdaptiveExhaustion
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhasePayment
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhaseSeeds

namespace ProximityPrize.SubmissionLower.MultipleAdaptive
open Koala6844VirtualShort Koala6844Normalization Koala6844Receipts Koala6844Terminal
open RCN081 RCN095 RCN130 RCN140 RCN156 RCN167 RCN234 RCN266
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open Koala6831MovingAdaptive (aggregateFlag aggregateFlag_mono exhaust_finset_stage)
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K E I J : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w A errors excess p δ : ℕ} {data : CenteredVirtualData x nodes σ w A errors excess}

def partnerFlag (s : CenteredAdaptiveSource data p) : Flag := ⟨s.B, s.U, s.L+s.q+s.B⟩

/-- Exhaust all available adaptive tests. Every removed factor has a partner
from one of the original sources, and every test fails on a nonempty residue. -/
theorem exhaust [CharP K p] (sources : J → CenteredAdaptiveSource data p)
    (hw : 0 < w) (hA : 0 < A) (hδ : 0 < δ)
    (hwidth : data.d0.natDegree + affineDegree data.A0 ≤ δ)
    (hlead : ∀ i ∈ nodes, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (initial : Finset (RegularIndex H))
    (hfield : initial.card < ENat.card K)
    (hfits : ∀ j, AdaptiveSourceFits (sources j).numbers (aggregateFlag H initial))
    (htrans : ∀ F ∈ initial, ¬ F.val ∣ (centeredFlow data).flow F.val) :
    ∃ residue ⊆ initial,
      (residue = ∅ ∨ ∀ j, ¬ geometricGate (2*δ) (sources j).numbers (aggregateFlag H residue)) ∧
      ∀ F ∈ initial \ residue, ∃ (j : J) (Q : MvPolynomial (Fin 4) K),
        IsRelPrime F.val Q ∧ (physicalFlag Q).cumulativeLE (partnerFlag (sources j)) ∧
        ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0 := by
  classical
  let active (S : Finset (RegularIndex H)) :=
    ∃ j, geometricGate (2*δ) (sources j).numbers (aggregateFlag H S)
  let covered (F : RegularIndex H) :=
    ∃ (j : J) (Q : MvPolynomial (Fin 4) K), IsRelPrime F.val Q ∧
      (physicalFlag Q).cumulativeLE (partnerFlag (sources j)) ∧
      ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g Q = 0
  obtain ⟨R,hsub,hstop,hparts⟩ := exhaust_finset_stage initial active covered (by
    intro S hs hn hactive
    obtain ⟨j,hgate⟩ := hactive
    have hfieldS : S.card < ENat.card K :=
      (show (S.card : ENat) ≤ initial.card by exact_mod_cast Finset.card_le_card hs).trans_lt hfield
    obtain ⟨hr,hy,ht⟩ := aggregateFlag_mono H hs
    obtain ⟨fr,fy,ft⟩ := hfits j
    have fit : AdaptiveSourceFits (sources j).numbers (aggregateFlag H S) :=
      ⟨hr.trans fr,hy.trans fy,ht.trans ft⟩
    obtain ⟨pass⟩ := exists_centered_adaptive_pass (sources j) δ hw hA hδ hwidth hlead H S hfieldS fit
      (fun F hF => htrans F (hs hF))
    have ne : pass.residue ≠ S := by
      intro he
      rcases pass.stopped with empty | failed
      · exact hn.ne_empty (he.symm.trans empty)
      · exact failed (he.symm ▸ hgate)
    refine ⟨pass.residue,(_root_.ssubset_iff_subset_ne).mpr ⟨pass.subset_incoming,ne⟩,?_⟩
    intro F hF
    obtain ⟨Q,hbox,vanish,proper⟩ := pass.partners F hF
    have nz : Q ≠ 0 := by
      intro hz
      exact (RCN167.positiveRFactors_spec H F.val F.property).1.not_isUnit
        (proper (dvd_refl _) (hz ▸ dvd_zero _))
    exact ⟨j,Q,proper,physicalFlag_le_of_nested Q nz _ _ _ _ _ hbox,vanish⟩)
  refine ⟨R,hsub,hstop.imp_right (fun fail j test => fail ⟨j,test⟩),hparts⟩

/-- Partners supplied by different sources share one resultant charge when their
physical flags fit a common bound. -/
theorem charge (embed : K →+* E) (germ : ActiveResultantGerm data embed)
    (σpow : ∀ z ∈ data.seeds, embed (σ z) = (embed z)^prime)
    (sources : J → CenteredAdaptiveSource data p)
    (H : MvPolynomial (Fin 4) K) (paid : Finset (RegularIndex H))
    (f g : Flag) (hg : g.ordered)
    (hfit : (physicalFlag (regularProduct H paid)).cumulativeLE f)
    (hdigit : germDegreeT f g < prime)
    (hcap : ∀ j, (partnerFlag (sources j)).cumulativeLE g)
    (partners : ∀ F ∈ paid, ∃ (j : J) (Q : MvPolynomial (Fin 4) K),
      IsRelPrime F.val Q ∧ (physicalFlag Q).cumulativeLE (partnerFlag (sources j)) ∧
      ∀ z ∈ data.seeds, RCN319.specialization K (data.selected z) z Q = 0) :
    (phaseSeeds H data.selected data.seeds paid).card ≤ germPrice f g := by
  apply card_germ_paid_family data embed germ σpow H paid f g hg hfit hdigit
  intro F hF
  obtain ⟨j,Q,proper,⟨hr,hy,ht⟩,vanish⟩ := partners F hF
  obtain ⟨r,y,t⟩ := hcap j
  exact ⟨Q,proper,⟨hr.trans r,hy.trans y,ht.trans t⟩,vanish⟩

#print axioms exhaust
#print axioms charge
end
end ProximityPrize.SubmissionLower.MultipleAdaptive
