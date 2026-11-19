/- Apache-2.0. Bome2017's actual 68.36 physical raw fibre bridge, based on
  the established terminal proof of Bome2017, Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Night6836RawStage
import ProximityPrize.SubmissionLower.K6833TerminalData
namespace ProximityPrize.SubmissionLower.Raw6836
open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN146 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorHybridCells LocatorFactorAggregate LocatorBatchProductRoute LocatorLowQuotient
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingPaid K6833Residual
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

/-- The other algebraic gates follow from capped shape and padding by the
physical provider. This Boolean retains just the three identity-axis conditions. -/
def rawGate (f:Envelope) : Bool :=
  (List.finRange 3).all fun j =>
    decide (131073 * 81106 * byAxis (identityRaw f) j ≤
      49968 * rawChargeWithCorrections TailCorrections.original f (unit j))

theorem identity_absorbed (f : Envelope) (left : FlagDegree)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle)
    (hgate : rawGate f = true) :
    131073 * 81106 *
        identityCurveDegree left (cellA f.total f.middle) (cellB f.middle f.slope)
          (cellS f.slope) RCN327.w ≤
      49968 * MovingFiberOrdinaryHigh6815.bound left f.total f.middle f.slope := by
  have haxis := List.all_eq_true.mp hgate
  have hZ := of_decide_eq_true (haxis (0 : Fin 3) (by simp))
  have hYZ := of_decide_eq_true (haxis (1 : Fin 3) (by simp))
  have hFull := of_decide_eq_true (haxis (2 : Fin 3) (by simp))
  let price := rawChargeWithCorrections TailCorrections.original f
  change 131073 * 81106 * (identityRaw f).zOnly ≤ 49968 * price unitZFlag at hZ
  change 131073 * 81106 * (identityRaw f).yz ≤ 49968 * price unitYZFlag at hYZ
  change 131073 * 81106 * (identityRaw f).all ≤ 49968 * price unitAllFlag at hFull
  have hlin : price left =
      left.zOnly * price unitZFlag + left.yz * price unitYZFlag +
        left.all * price unitAllFlag := by
    simp only [price, rawChargeWithCorrections, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
    ring
  rw [identityCurveDegree_eq_identityRaw f left hr hy,
    ← rawChargeWithCorrections_original_eq_incumbent f left hr hy]
  change 131073 * 81106 * _ ≤ 49968 * price left
  calc
    _ = left.zOnly * (131073*81106*(identityRaw f).zOnly) +
        left.yz * (131073*81106*(identityRaw f).yz) +
        left.all * (131073*81106*(identityRaw f).all) := by ring
    _ ≤ left.zOnly * (49968*price unitZFlag) + left.yz * (49968*price unitYZFlag) +
        left.all * (49968*price unitAllFlag) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hZ) (Nat.mul_le_mul_left _ hYZ))
        (Nat.mul_le_mul_left _ hFull)
    _ = 49968 * price left := by rw [hlin]; ring

private theorem paddedSupport_eq_cellSupport (f : Envelope) (k : ℕ) :
    f.paddedSupport k =
      cellSupport (f.pad k).total (f.pad k).middle (f.pad k).slope := by
  have hr : 3 ≤ (f.pad k).slope := by simp [Envelope.pad]
  have hy : (f.pad k).slope+2 ≤ (f.pad k).middle := by simp [Envelope.pad]
  have ht : (f.pad k).middle ≤ (f.pad k).total := by
    change max f.middle (max 3 f.slope + 2) ≤ max f.total (max f.middle (max 3 f.slope + 2) + k)
    exact (Nat.le_add_right _ _).trans (le_max_right _ _)
  have hs : (f.pad k).slope-2+2 = (f.pad k).slope := by omega
  have hm : (f.pad k).middle-(f.pad k).slope-1+((f.pad k).slope-2)+3 =
      (f.pad k).middle := by omega
  have htotal : (f.pad k).total-(f.pad k).middle+
      ((f.pad k).middle-(f.pad k).slope-1)+((f.pad k).slope-2)+3 =
      (f.pad k).total := by omega
  unfold Envelope.paddedSupport cellSupport RCN198.support cellA cellB cellS
  congr <;> omega


omit [CharP K 2130706433] in
theorem factor_global_box {H : MvPolynomial (Fin 4) K} (hH:H≠0) (F : RegularIndex H)
    {D t y r : ℕ} (hbox:H∈nestedCoefficientBox K D 131071 t y r)
    {support : ResidualSupportParameters} (hData : ResidualSupportData support F.1) :
    F.1 ∈ RCN174.globalCoefficientBox K D 131071 support.total support.s := by
  have hdiv := (positiveRFactors_spec H F.1 F.2).2.1
  have hcut := (nested_mem_weights hbox hH).2.2.2
  have hF := (weightedTotalDegree_le_of_dvd (contactWeights 131071) F.1 H hdiv
    hH).trans_lt hcut
  intro d hd
  have hT := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans hData.total_weight
  have hS := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hData.s_weight
  have hX := (MvPolynomial.le_weightedTotalDegree (contactWeights 131071) hd).trans_lt hF
  exact ⟨by
      have htotal : d 1 + d 2 + d 3 ≤ support.total := by simpa [weight_fin4, residualTotalWeights] using hT
      change d 1 + d 3 ≤ support.total
      omega,
    by simpa [weight_fin4, residualSWeights] using hS,
    by simpa only [contact_weight] using hX⟩


theorem regular_raw {x : I ↪ K} {H : MvPolynomial (Fin 4) K} (hH:H≠0)
    {D t y r:ℕ} (hD:131072≤D) (hDp:D<2130706433) (hbox:H∈nestedCoefficientBox K D 131071 t y r)
    (seeds:Finset K) (u₀ u₁:I→K) (selected:K→Polynomial K)
    (hN:Fintype.card I=262144) (deg:∀g∈seeds,(selected g).natDegree≤131071)
    (agreement:∀g∈seeds,181039≤(Finset.univ.filter fun i => (selected g).eval (x i)=u₀ i+g*u₁ i).card)
    (pencil:NoLargeSelectedPencil selected seeds 131071 81105)
    (F:RegularIndex H) (f:Envelope) (shape:f.slope≤f.middle ∧ f.middle≤f.total)
    (cap:f.slope≤18 ∧ f.middle≤76 ∧ f.total≤9352)
    (below: Below (originalCumulativeFlag F.1) f.flag) (gate:rawGate (f.pad 0)=true) :
    (regularFiber H seeds selected F).card ≤ rawChargeWithCorrections TailCorrections.original (f.pad 0)
      (originalCumulativeFlag F.1) := by
  let a := f.pad 0
  have bounds : 3≤a.slope ∧ a.slope+2≤a.middle ∧ a.middle≤a.total ∧
      a.slope≤31 ∧ a.middle≤142 ∧ a.total≤9352 := by
    simp only [a,Envelope.pad]
    omega
  obtain ⟨h3,hy,ht,hs,hm,hT⟩ := bounds
  have data := residual_support_of_endpoint F.1 f shape below
  have box := factor_global_box hH F hbox data
  change F.1 ∈ globalCoefficientBox K D 131071 a.total a.slope at box
  have supp : ResidualSupportData (cellSupport a.total a.middle a.slope) F.1 :=
    paddedSupport_eq_cellSupport f 0 ▸ data
  obtain ⟨irr,_,hR⟩ := positiveRFactors_spec H F.1 F.2
  let kept := regularFiber H seeds selected F
  have sub : kept⊆seeds := fun _ hg => (mem_regularFiber.mp hg).1
  have count := Raw6836Stage.regular_raw_seed_card_le D a.total a.middle a.slope hD hDp
    hT hm hs h3 hy ht F.1 irr hR box supp selected kept Finset.univ x u₀ u₁
    x.injective.injOn (Finset.card_univ.trans hN) (fun g hg => deg g (sub hg)) (fun g hg => agreement g (sub hg))
    (fun _ hg => (mem_regularFiber.mp hg).2.1) (fun _ hg => (mem_regularFiber.mp hg).2.2)
    (RCN243.noLargeSelectedPencil_mono selected seeds kept 131071 81105 sub pencil)
    (fun left => identity_absorbed a left h3 hy gate)
  rw [rawChargeWithCorrections_original_eq_incumbent a _ h3 hy]
  exact count
end
end ProximityPrize.SubmissionLower.Raw6836
#print axioms ProximityPrize.SubmissionLower.Raw6836.regular_raw
