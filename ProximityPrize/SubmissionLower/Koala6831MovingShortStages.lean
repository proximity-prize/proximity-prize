import ProximityPrize.SubmissionLower.Koala6831MovingPaidRoute
import ProximityPrize.SubmissionLower.Koala6831MovingPaidNumeric
import ProximityPrize.SubmissionLower.Koala6831MovingShortRetained

namespace ProximityPrize.SubmissionLower.Koala6831MovingPaid

open scoped Classical
open RCN081 RCN156 RCN167 RCN234 RCN266 RCN275
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingPrimaryRoute Koala6831MovingShortRetained
open Koala6831MovingLedger Koala6831MovingSources LocatorFactorAggregate LocatorLowQuotient

noncomputable section

variable {K I : Type} [Field K] [Fintype I]

theorem adaptivePrices_checked : AdaptivePrices where
  first f hpos hcap _ := adaptive1_stagePrice_le f hpos hcap
  second := adaptive2_stagePrice_le
  third := adaptive3_stagePrice_le

structure ReachedTerminal {x : I ↪ K} {original : Finset K} (R : Ready x original) where
  primary : P4 K
  primary_ne : primary ≠ 0
  primary_box : primary ∈ nestedCoefficientBox K Stage.primary.cutoff weight 41882 418 93
  regular : Finset K
  regular_subset : regular ⊆ R.seeds
  route : PaidRoute primary regular R.selected
  paid : original.card + fixedRoomCredit₁ (aggregateFlag primary route.residue) +
    fixedRoomCredit₂ (aggregateFlag primary route.residue) ≤ route.seeds.card + 39317112195672787

theorem ReachedTerminal.paid_with_certificate_credit {x : I ↪ K} {original : Finset K}
    {R : Ready x original} (T : ReachedTerminal R) (f : Koala6831Residual.Envelope)
    (hs : f.slope = (aggregateFlag T.primary T.route.residue).all)
    (hm : f.middle = middle (aggregateFlag T.primary T.route.residue)) :
    original.card + Koala6831Residual.roomCredit f ≤ T.route.seeds.card + 39317112195672787 := by
  let residual := aggregateFlag T.primary T.route.residue
  have hc : creditFlag f.flag = creditFlag residual := by
    change f.slope = residual.all at hs
    change f.middle = middle residual at hm
    simp only [creditFlag, Koala6831Residual.Envelope.flag, hs, hm, middle, Nat.add_sub_cancel]
  have hcredit : fixedRoomCredit₁ residual + fixedRoomCredit₂ residual = Koala6831Residual.roomCredit f := by
    rw [← fixedRoomCredits_eq_certificate f]
    simp only [fixedRoomCredit₁, fixedRoomCredit₂, hc]
  calc
    _ = original.card + (fixedRoomCredit₁ residual + fixedRoomCredit₂ residual) := by rw [hcredit]
    _ = original.card + fixedRoomCredit₁ residual + fixedRoomCredit₂ residual := by rw [Nat.add_assoc]
    _ ≤ _ := T.paid

theorem ReachedTerminal.factor_global_box {x : I ↪ K} {original : Finset K}
    {R : Ready x original} (T : ReachedTerminal R) (F : RegularIndex T.primary)
    {support : ResidualSupportParameters} (hData : ResidualSupportData support F.1) :
    F.1 ∈ RCN174.globalCoefficientBox K Stage.primary.cutoff weight support.total support.s := by
  have hdiv := (positiveRFactors_spec T.primary F.1 F.2).2.1
  have hcut := (nested_mem_weights T.primary_box T.primary_ne).2.2.2
  have hF := (weightedTotalDegree_le_of_dvd (contactWeights weight) F.1 T.primary hdiv
    T.primary_ne).trans_lt hcut
  intro d hd
  have hT := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans hData.total_weight
  have hS := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hData.s_weight
  have hX := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt hF
  exact ⟨by
      have htotal : d 1 + d 2 + d 3 ≤ support.total := by simpa [weight_fin4, residualTotalWeights] using hT
      change d 1 + d 3 ≤ support.total
      omega,
    by simpa [weight_fin4, residualSWeights] using hS,
    by simpa only [contact_weight] using hX⟩

theorem reaches_terminal_of_ready [CharP K 2130706433]
    (prices : AdaptivePrices) {x : I ↪ K} {original : Finset K} (R : Ready x original) :
    Nonempty (ReachedTerminal R) := by
  obtain ⟨H, hH, hbox, _, regular, hsub, hregularCount, hregular⟩ :=
    exists_primary_and_transverse_subfamily R.flow Finset.univ R.good (Finset.subset_univ _)
      (Finset.card_univ.trans R.nodes_card) x R.u₀ R.u₁ R.word R.seeds R.selected R.normalized
      R.degree R.agreement (fun g hg i _ => R.agree_good g hg i) R.pencil R.scale_ne R.affine_ne
      R.denominator_ne R.normalization R.normalized_degree R.normalized_agreement
  obtain ⟨route⟩ := exists_paid_route prices R.flow x R.u₀ R.u₁ R.word R.good R.nodes_card
    R.fixedWord R.denominator_degree R.minor_degree H hH hbox regular R.selected
    (fun g hg => R.degree g (hsub hg)) (fun g hg => R.agreement g (hsub hg))
    (fun g hg => R.agree_good g (hsub hg))
    (RCN243.noLargeSelectedPencil_mono R.selected R.seeds regular weight 81066 hsub R.pencil)
    hregular
  refine ⟨⟨H, hH, hbox, regular, hsub, route, ?_⟩⟩
  have hready := R.count
  have hpaid := route.paid
  unfold normalizationBudget at hready
  change regular.card + fixedRoomCredit₁ (aggregateFlag H route.residue) +
    fixedRoomCredit₂ (aggregateFlag H route.residue) ≤ route.seeds.card + 30713098255225143 at hpaid
  omega

open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention Koala6831Comparison
open Koala6831Separation (NormalForm)

theorem reaches_terminal_of_retainedComparison [CharP K 2130706433]
    (prices : AdaptivePrices) (x : I ↪ K) (σ : K ≃+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hpower : ∀ g : K, σ g = g ^ prime)
    (hcard : Fintype.card I = 262144) (u : Received K I) (Γ : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) (hret : RetainedComparison x σ.toRingHom u Γ selected q)
    (delta : ℕ) (hdelta : delta ≤ 9553) (N : NormalForm q 131071 delta) :
    ∃ R : Ready x Γ, Nonempty (ReachedTerminal R) := by
  obtain ⟨R⟩ := ready_of_retainedComparison x σ hfixed hpower hcard u Γ selected q hret delta hdelta N
  exact ⟨R, reaches_terminal_of_ready prices R⟩

theorem reaches_terminal_checked [CharP K 2130706433]
    (x : I ↪ K) (σ : K ≃+* K)
    (hfixed : ∀ i, σ (x i) = x i) (hpower : ∀ g : K, σ g = g ^ prime)
    (hcard : Fintype.card I = 262144) (u : Received K I) (Γ : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)) (hret : RetainedComparison x σ.toRingHom u Γ selected q)
    (delta : ℕ) (hdelta : delta ≤ 9553) (N : NormalForm q 131071 delta) :
    ∃ R : Ready x Γ, Nonempty (ReachedTerminal R) :=
  reaches_terminal_of_retainedComparison adaptivePrices_checked x σ hfixed hpower hcard u Γ selected
    q hret delta hdelta N

end

end ProximityPrize.SubmissionLower.Koala6831MovingPaid

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
