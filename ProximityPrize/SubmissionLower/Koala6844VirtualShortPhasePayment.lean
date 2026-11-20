import ProximityPrize.SubmissionLower.Koala6844VirtualShortPairGerm
import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermPrices
import ProximityPrize.SubmissionLower.Koala6844TerminalRegular


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort
open scoped Classical BigOperators
open Koala6844Normalization Koala6844Receipts Koala6844Terminal
open RCN081 RCN140 RCN156 RCN167 RCN234 RCN266 RCN319
open LocatorBatchProductRoute LocatorLowQuotient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K E I : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

private theorem physical_slope_eq (Q : MvPolynomial (Fin 4) K) :
    (physicalFlag Q).r = Q.degreeOf 2 := by
  change MvPolynomial.weightedTotalDegree residualSWeights Q = Q.degreeOf 2
  rw [MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_congr rfl
  intro d _
  rw [RCN081.weight_fin4]
  simp [residualSWeights]

theorem physicalFlag_le_of_nested (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (cut weight totalCap middleCap slopeCap : ℕ) (hbox : Q ∈ nestedCoefficientBox K cut weight totalCap middleCap slopeCap) :
    (physicalFlag Q).cumulativeLE ⟨slopeCap,middleCap,totalCap⟩ := by
  have h := nested_mem_weights hbox hQ
  exact ⟨h.2.2.1,h.2.1,h.1⟩

theorem card_germ_paid_family
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (germ : ActiveResultantGerm data embed)
    (σpow : ∀ g ∈ data.seeds, embed (σ g) = (embed g)^prime)
    (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H))
    (f g : Flag) (hg : g.ordered)
    (hfit : (physicalFlag (regularProduct H A)).cumulativeLE f)
    (hDigit : germDegreeT f g < prime)
    (partner : ∀ F ∈ A, ∃ Q : MvPolynomial (Fin 4) K,
      IsRelPrime F.1 Q ∧ (physicalFlag Q).cumulativeLE g ∧
      ∀ seed ∈ data.seeds, specialization K (data.selected seed) seed Q = 0) :
    (A.biUnion (regularSeeds H data.selected data.seeds)).card ≤ germPrice f g := by
  have hsum (weights : Fin 4 → ℕ) : wt weights (regularProduct H A) =
      ∑ F ∈ A, wt weights F.val :=
    RCN071.weightedTotalDegree_prod_eq weights A (fun F => F.val)
      (fun F _ => regularFactor_ne_zero H F)
  have hr : (∑ F ∈ A, (physicalFlag F.val).r) ≤ f.r := by
    simpa only [physicalFlag, ← hsum] using hfit.1
  have hy : (∑ F ∈ A, (physicalFlag F.val).y) ≤ f.y := by
    simpa only [physicalFlag, ← hsum] using hfit.2.1
  have ht : (∑ F ∈ A, (physicalFlag F.val).t) ≤ f.t := by
    simpa only [physicalFlag, ← hsum] using hfit.2.2
  have hfactor (F : RegularIndex H) (hF : F ∈ A) :
      (regularSeeds H data.selected data.seeds F).card ≤ germPrice (physicalFlag F.val) g := by
    let a := physicalFlag F.val
    obtain ⟨Q,hrel,hQ,hzero⟩ := partner F hF
    obtain ⟨hirr,_,hpos⟩ := positiveRFactors_spec H F.val F.property
    have hproper := (hirr.isRelPrime_iff_not_dvd).mp hrel
    have ha := physicalFlag_ordered F.val
    have har : a.r ≤ f.r := (Finset.single_le_sum (f := fun F : RegularIndex H => (physicalFlag F.val).r)
      (fun _ _ => Nat.zero_le _) hF).trans hr
    have hat : a.t ≤ f.t := (Finset.single_le_sum (f := fun F : RegularIndex H => (physicalFlag F.val).t)
      (fun _ _ => Nat.zero_le _) hF).trans ht
    have hd := (germDegreeT_mono_left a f g (hg.1.trans hg.2) har hat).trans_lt hDigit
    let S := regularSeeds H data.selected data.seeds F
    have hsub := regularSeeds_subset H data.selected data.seeds F
    exact coprime_pair_card_le_germ data embed germ prime σpow F.val Q hirr hpos hproper
      a.r a.y a.t g.r g.y g.t (physical_slope_eq F.val).symm.le ((physical_slope_eq Q).symm.trans_le hQ.1)
      le_rfl hQ.2.1 le_rfl hQ.2.2 ha.1 ha.2 hg.1 hg.2 hd S hsub
      (fun seed hseed => (Finset.mem_filter.mp hseed).2.1)
      (fun seed hseed => hzero seed (hsub hseed))
  calc
    _ ≤ ∑ F ∈ A, (regularSeeds H data.selected data.seeds F).card := Finset.card_biUnion_le
    _ ≤ ∑ F ∈ A, germPrice (physicalFlag F.val) g := Finset.sum_le_sum hfactor
    _ ≤ _ := germPrice_sum_le A (fun F => physicalFlag F.val) f g hg.1 (hg.1.trans hg.2) hr hy ht

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort

