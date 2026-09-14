import ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6808

namespace ProximityPrize.SubmissionLower.BoundaryTailOwnAssembly6808
open RCN095 RCN135 RCN234 RCN156
open BoundaryTailRegularData6808 BoundaryTailRegularData6808.Data
open BoundaryTailOwnShape6808 BoundaryTailOwnArithmetic6808
open BoundaryTailNumericGeometry6808 BoundaryTailAsymmetric6808
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

omit [CharP K 2130706433] in
theorem bound_le_polynomial (S : Data nodes u0 u1) (hown : Own S) :
    bound S ≤ ownPolynomial (S.r-3) (S.y-S.r-2) (S.t-S.y) / 1808388 := by
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
    rw [BoundaryTailIdentityBridge6808.numerator_d6_coordinates]
    rfl
  rw [har,hbr,hz]
  unfold bound
  rw [hdual]
  apply max_le
  · simpa only [Data.pair,properParameters,ha,hb,hc] using helper_cap_le a b c
  · simpa only [Data.pair,parameters,ha,hb,hc] using retained_cap_le a b c

theorem count_132_le_polynomial (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 1800 < S.t) :
    S.seeds.card ≤ ownPolynomial (S.r-3) (S.y-S.r-2) (S.t-S.y) / 1808388 :=
  (BoundaryTailProfileCount6808.count_132 S hI (avoidance_total S hown 1800 hL)).trans
    (bound_le_polynomial S hown)

end
end ProximityPrize.SubmissionLower.BoundaryTailOwnAssembly6808
