import ProximityPrize.SubmissionLower.Part.G088


section Compact_SecondJetOwnShape
/-! Connecting an actual carrier's cumulative flag to its numerical cell. -/
namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open SecondJetRegularData SecondJetRegularData.Data LocatorHybridCells LocatorHybridCellsC1
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem zOnly_le_degree (F : MvPolynomial (Fin 4) K) :
    (originalCumulativeFlag F).zOnly ≤ F.degreeOf 3 := by
  have hw : wt residualTotalWeights F ≤ wt residualYSWeights F+F.degreeOf 3 := by
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    have h1 := MvPolynomial.le_weightedTotalDegree residualYSWeights he
    have h2 := MvPolynomial.monomial_le_degreeOf (3:Fin 4) he
    simp [wt,RCN081.weight_fin4,residualYSWeights,residualTotalWeights] at h1 ⊢
    omega
  change wt residualTotalWeights F-wt residualYSWeights F ≤ F.degreeOf 3
  omega

def Own (S : Data nodes u0 u1) : Prop :=
  originalCumulativeFlag S.F = ⟨S.t-S.y,S.y-S.r,S.r⟩

theorem normal_eq (S : Data nodes u0 u1) (hown : Own S) :
    S.normal = SecondJetNumericGeometry.normal S.r (S.y-S.r) (S.t-S.y) := by
  have h1 : cellB S.y S.r = S.y-S.r-1 := rfl
  have h2 : cellS S.r = S.r-2 := rfl
  have h3 : 2*(S.y-S.r-1)+2 = 2*(S.y-S.r) := by have := S.ry; omega
  have h4 : 2*(S.r-2)+2 = 2*(S.r-1) := by have := S.rpos; omega
  unfold Data.normal
  rw [hown,SecondJetIdentity.cell_first_eq,SecondJetIdentity.cell_normal_eq]
  simp only [Lower80788.HybridIdentityC2.reducedABS,Lower80788.HybridIdentityC2.rationalABS,
    cellA,h1,h2,h3,h4,SecondJetNumericGeometry.normal]
  simp only [flagMixed]
  ring

theorem avoidance (S : Data nodes u0 u1) (hown : Own S) (L : ℕ) (hL : L < S.t-S.y) :
    L < S.F.degreeOf 3 := by
  have h := zOnly_le_degree S.F
  rw [hown] at h
  exact hL.trans_le h

theorem factorial_ne (d : ℕ) (hd : d < 2130706433) : (d.factorial : K) ≠ 0 :=
  factorial_cast_ne_zero_below_characteristic 2130706433 d hd

theorem two_ne : (2 : K) ≠ 0 := by
  have h := factorial_ne (K := K) 2 (by decide)
  simpa only [show Nat.factorial 2 = 2 by decide,Nat.cast_ofNat] using h

end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

end Compact_SecondJetOwnShape
