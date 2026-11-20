import ProximityPrize.SubmissionLower.Koala6844TerminalFamily


namespace ProximityPrize.SubmissionLower.Koala6844Terminal
open Koala6844Receipts
open RCN081 RCN095 RCN167 RCN319 RCN140 RCN156 RCN238 RCN266
open LocatorBatchProductRoute LocatorHybridCells
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

def intrinsicRawGuard (f : Flag) : Bool :=
  decide ((padFlag f).t ≤ 9678) &&
    match rawGeometryRates f with
    | none => false
    | some rate => decide (rate.total ≤ rate.middle ∧ rate.middle ≤ rate.slope ∧ dot f.increments rate ≤ terminalBudget)

def intrinsicRawMetadata (e : CertifiedEndpoint) : Bool :=
  match e.receipt with
  | .intrinsic _ _ => intrinsicRawGuard e.flag
  | .terminal _ _ _ => true

theorem intrinsicRawGuard_spec (f : Flag) (h : intrinsicRawGuard f = true) :
    let g := padFlag f
    f.ordered ∧ GraphGates g.t g.y g.r ∧ (rawRatesAt g).monotoneRates ∧
      dot f.increments (rawRatesAt g) ≤ terminalBudget := by
  have hh := Bool.and_eq_true_iff.mp h
  let g := padFlag f
  have ht : g.t ≤ 9678 := of_decide_eq_true hh.1
  have hs := hh.2
  have hsome : ∃ rate, rawGeometryRates f = some rate ∧
      rate.monotoneRates ∧ dot f.increments rate ≤ terminalBudget := by
    change (match rawGeometryRates f with
      | none => false
      | some rate => decide (rate.total ≤ rate.middle ∧ rate.middle ≤ rate.slope ∧ dot f.increments rate ≤ terminalBudget)) = true at hs
    cases he : rawGeometryRates f with
    | none => rw [he] at hs; contradiction
    | some rate =>
      rw [he] at hs
      obtain ⟨h1,h2,h3⟩ := of_decide_eq_true hs
      exact ⟨rate,rfl,⟨h1,h2⟩,h3⟩
  obtain ⟨rate,hrate,hmono,hbudget⟩ := hsome
  change (if rawGeometryGate f && (rawIdentity g).all (fun i cost =>
    decide ((nodes-degree)*pencilLimit*cost ≤ agreementGap*(rawRatesAt g).axis i)) then
    some (rawRatesAt g) else none) = some rate at hrate
  split at hrate
  · rename_i hg
    have he := Option.some.inj hrate
    subst rate
    have hgate := (Bool.and_eq_true_iff.mp hg).1
    have hgate' := Bool.and_eq_true_iff.mp hgate
    have horder := of_decide_eq_true hgate'.1
    have hc := of_decide_eq_true hgate'.2
    obtain ⟨hr,hy,_⟩ := pad_shape f 0
    refine ⟨⟨horder.2.1,horder.2.2⟩,?_,hmono,hbudget⟩
    have hgood : goodGraph g = true := decide_eq_true ⟨ht,hc.1,hc.2.1,hc.2.2.2,hc.2.2.1⟩
    exact graphGates_of_goodGraph g hr hy hgood
  · contradiction

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem intrinsic_regular_family [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (outer : Flag) (hguard : intrinsicRawGuard outer = true)
    (hfit : (physicalFlag (regularProduct H remaining)).cumulativeLE outer)
    (ns : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds : Finset K)
    (data : TerminalSeedData ns x u₀ u₁ selected seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H selected seeds)) :
    seeds.card ≤ terminalBudget := by
  classical
  let g := padFlag outer
  let rate := rawRatesAt g
  let family := regularFamily H remaining selected seeds
  obtain ⟨hordered,hg,hmono,hpaid⟩ := intrinsicRawGuard_spec outer hguard
  obtain ⟨hr,hy,ht⟩ := pad_shape outer 0
  have hfit' : (factorFlags family).cumulativeLE outer := by
    simpa only [family,regularFamily_flag] using hfit
  have hpay : 1 * factorCounts family ≤ dot (factorFlags family).increments rate := by
    apply factor_sum_priced family ⟨rate,1⟩
    intro a ha
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp ha
    have hcap := single_factor_le_sum family (countedRegular H selected seeds F) ha
    have hf := (positiveRFactors_spec H F.1 F.2)
    have hw := (RCN081.weightedTotalDegree_le_of_dvd (contactWeights 131071) F.1 H hf.2.1 hH).trans hcontact
    have hx : (physicalFlag F.1).cumulativeLE g :=
      ⟨hcap.1.trans (hfit'.1.trans (below_pad outer 0).1),
        hcap.2.1.trans (hfit'.2.1.trans (below_pad outer 0).2.1),
        hcap.2.2.trans (hfit'.2.2.trans (below_pad outer 0).2.2)⟩
    let Γ := regularSeeds H selected seeds F
    have hΓ := data.subset (regularSeeds_subset H selected seeds F)
    have hsol (z : K) (hz : z ∈ Γ) : specialization K (selected z) z F.1 = 0 ∧
        specialization K (selected z) z (MvPolynomial.pderiv 2 F.1) ≠ 0 := (Finset.mem_filter.mp hz).2
    have hbound := regular_raw_bound D g.t g.y g.r hD hDchar hg hr hy ht F.1 hf.1 hf.2.2
      (physical_box F.1 D (by omega) hw g hx) (physical_support F.1 g hr hy ht hx)
      selected Γ ns x u₀ u₁ hΓ.injective hΓ.nodes_card hΓ.selected_degree hΓ.agreement
      (fun z hz => (hsol z hz).1) (fun z hz => (hsol z hz).2) hΓ.noPencil
    change 1*Γ.card ≤ dot (physicalFlag F.1).increments rate
    rw [one_mul, physicalFlag_increments, rawRates_eq_bound g hr hy ht]
    exact hbound
  rw [one_mul] at hpay
  exact (regularFamily_count H remaining selected seeds hcover).trans
    (hpay.trans ((dot_cumulative_mono (factorFlags_ordered family) hordered hfit' hmono).trans hpaid))

end
end ProximityPrize.SubmissionLower.Koala6844Terminal

