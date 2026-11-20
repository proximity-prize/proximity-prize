import ProximityPrize.SubmissionLower.Koala6831MovingContact
import ProximityPrize.SubmissionLower.Koala6831MovingSupports
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open RCN081 RCN156 RCN234 ContactOrderBridge LocatorLowQuotient

noncomputable section

variable {K : Type*} [Field K] {p : ℕ} [CharP K p]

theorem FlowData.exists_contact_partner_of_room
    (B : FlowData K) {I : Type*} (node u₀ u₁ normalized : I → K)
    (h₀ : ∀ i, B.d0.eval (node i) * u₀ i + B.c0.eval (node i) =
      B.a0.eval (node i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (node i) * u₁ i + B.c1.eval (node i) =
      B.a1.eval (node i) * normalized i)
    {F S : P4 K} {j w delta m cutoff finalCutoff total middle slope : ℕ}
    (hF : Irreducible F) (hS : ¬ F ∣ S) (htrans : ¬ F ∣ B.flow F) (hj : j < p)
    (hw : 0 < w) (hdelta : 0 < delta)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ delta)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ w + delta)
    (hroom : cutoff + j * (2 * delta) ≤ finalCutoff)
    (hbox : F ^ j * S ∈ nestedCoefficientBox K cutoff w total middle slope)
    (hcontact : ∀ i, ContactAtLeast K (node i) (u₀ i) (u₁ i) m (F ^ j * S)) :
    ∃ Q : P4 K, IsRelPrime F Q ∧
      Q ∈ nestedCoefficientBox K finalCutoff w (total + j) middle slope ∧
      ∀ i, ContactAtLeast K (node i) (u₀ i) (u₁ i) m Q := by
  let P := F ^ j * S
  let Q := (B.flow : P4 K → P4 K)^[j] P
  have hneS : S ≠ 0 := by
    intro h
    exact hS (h.symm ▸ dvd_zero F)
  obtain ⟨hT, hY, hR, hD⟩ := nested_mem_weights hbox (mul_ne_zero (pow_ne_zero j hF.ne_zero) hneS)
  have htotal : wt residualTotalWeights Q ≤ total + j := by
    have h := B.flow_iterate_wt_le residualTotalWeights 1 j P B.flow_total_le
    simpa only [Nat.mul_one, Q] using h.trans (Nat.add_le_add_right hT (j * 1))
  have hmiddle : wt residualYSWeights Q ≤ middle := by
    have h := B.flow_iterate_wt_le residualYSWeights 0 j P (fun R => by
      simpa only [Nat.add_zero] using B.flow_middle_le R)
    exact (by simpa only [Q, Nat.mul_zero, Nat.add_zero] using h :
      wt residualYSWeights Q ≤ wt residualYSWeights P).trans hY
  have hslope : wt residualSWeights Q ≤ slope := by
    have h := B.flow_iterate_wt_le residualSWeights 0 j P (fun R => by
      simpa only [Nat.add_zero] using B.flow_slope_le R)
    exact (by simpa only [Q, Nat.mul_zero, Nat.add_zero] using h :
      wt residualSWeights Q ≤ wt residualSWeights P).trans hR
  have hweight : wt (contactWeights w) Q < finalCutoff := by
    have h := B.flow_iterate_wt_le (contactWeights w) (2 * delta) j P (fun R =>
      B.flow_contact_wt_le R w delta hw hdelta hden hminor)
    exact h.trans_lt ((Nat.add_lt_add_right hD _).trans_le hroom)
  refine ⟨Q, flow_partner_of_lt_characteristic B hF hS htrans hj, ?_, ?_⟩
  · intro d hd
    have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans htotal
    have hy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hmiddle
    have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hslope
    have hw' := (MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans_lt hweight
    exact ⟨by simpa [weight_fin4, residualTotalWeights] using ht,
      by simpa [weight_fin4, residualYSWeights] using hy,
      by simpa [weight_fin4, residualSWeights] using hr,
      by simpa [weight_fin4, contactWeights, Nat.mul_comm] using hw'⟩
  · intro i
    exact B.contactAtLeast_iterate_flow (node i) (u₀ i) (u₁ i) (normalized i)
      (h₀ i) (h₁ i) j (hcontact i)

end

end ProximityPrize.SubmissionLower.Koala6831Moving
