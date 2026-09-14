import ProximityPrize.SubmissionLower.HigherRootOwnArithmetic6810P0

namespace ProximityPrize.SubmissionLower.HigherRootOwnAssembly6810P0
open RCN095 RCN135 RCN234 RCN156
open HigherRootRegularData6810P0 HigherRootRegularData6810P0.Data
open HigherRootOwnShape6810P0 HigherRootOwnArithmetic6810P0
open HigherRootNumericGeometry6810P0 HigherRootAsymmetric6810P0
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem bound_le_polynomial (S : Data nodes u0 u1) (hown : Own S) :
    bound S ≤ ownPolynomial (S.r-3) (S.y-S.r-2) (S.t-S.y) / 1808028 := by
  obtain ⟨a,ha⟩ : ∃ a, S.r = a+3 := ⟨S.r-3,by have := S.rpos; omega⟩
  obtain ⟨b,hb⟩ : ∃ b, S.y = a+3+(b+2) := ⟨S.y-S.r-2,by have := S.ry; omega⟩
  obtain ⟨c,hc⟩ : ∃ c, S.t = a+3+(b+2)+c := ⟨S.t-S.y,by have := S.yt; omega⟩
  have hv : S.y-S.r = b+2 := by omega
  have hz : S.t-S.y = c := by omega
  have har : S.r-3 = a := by omega
  have hbr : S.y-S.r-2 = b := by omega
  have hdual : S.dual = DualCutBridge6807Arithmetic.graphNumerator
      ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c := by
    unfold Data.dual
    rw [hown,hv,hz,hc,hb,ha]
    rw [HigherRootIdentityBridge6810P0.numerator_profile_coordinates]
    rfl
  rw [har,hbr,hz]
  unfold bound
  rw [hdual]
  apply max_le
  · simpa only [Data.pair,properParameters,ha,hb,hc] using helper_cap_le a b c
  · simpa only [Data.pair,parameters,ha,hb,hc] using retained_cap_le a b c

theorem count_profile_le_polynomial (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 1800 < S.t) :
    S.seeds.card ≤ ownPolynomial (S.r-3) (S.y-S.r-2) (S.t-S.y) / 1808028 :=
  (HigherRootProfileCount6810P0.count_profile S hI (avoidance_total S hown 1800 hL)).trans
    (bound_le_polynomial S hown)

theorem count_profile_le_full_rounded (S : Data nodes u0 u1)
    (hI : Fintype.card I = 262144) (hown : Own S) (hL : 1800 < S.t) :
    S.seeds.card ≤ HigherRootArithmetic6810.P0.roundedCap
      (S.r-3) (S.y-S.r-2) (S.t-S.y) := by
  have h := count_profile_le_polynomial S hI hown hL
  have hfull : ownPolynomial (S.r-3) (S.y-S.r-2) (S.t-S.y)/1808028 ≤
      HigherRootArithmetic6810.P0.fullNumerator (S.r-3) (S.y-S.r-2) (S.t-S.y)/1808028 := by
    apply Nat.div_le_div_right
    exact Nat.le_add_right _ _
  exact (h.trans hfull).trans (HigherRootArithmetic6810.P0.full_cap_le_rounded _ _ _)

end
end ProximityPrize.SubmissionLower.HigherRootOwnAssembly6810P0
