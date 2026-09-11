import ProximityPrize.SubmissionLower.PartG091


section Compact_SecondJetProfileBounds
/-! Concrete second-jet bounds, with all profile arithmetic, exceptional
counts, characteristic conditions, and interpolation hypotheses discharged. -/
namespace ProximityPrize.SubmissionLower.SecondJetProfileBounds
open RCN135 SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
open SecondJetNumericGeometry SecondJetUniformReceipts SecondJetRelaxedInterpolation
open SecondJetProperReceipts
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

def cost (S : Data nodes u0 u1) (B U L k n0 : ℕ) : ℕ :=
  S.normal+131076*((S.moving B U L k n0+k)/(k+1))+500000000000000

theorem count_of_profile (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (m B s U L k n0 : ℕ)
    (hL : L < S.t-S.y)
    (hexists : ∃ P, Interpolant m B s U L k n0 nodes u0 u1 P)
    (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L) (hks : k ≤ s) (hsm : s < m)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hBmax : B ≤ 47) (hUmax : U ≤ 157) (hLmax : L ≤ 2233) (hsmax : s ≤ 21)
    (hproper : ∀ r v z : ℕ, 3 ≤ r → 2 ≤ v → L < z →
      (properParameters r v z B U L s).regularCountCap ≤ SecondJetNumericGeometry.normal r v z) :
    S.seeds.card ≤ cost S B U L k n0 := by
  obtain ⟨P,hP⟩ := hexists
  have hg1 : S.PairGates (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1)) :=
    helper_gates S.r S.y S.t B U L s S.rbound S.ybound S.tbound hBmax hUmax hLmax hsmax
  have hg2 : S.PairGates B U L :=
    coefficient_gates S.r S.y S.t B U L S.rbound S.ybound S.tbound hBmax hUmax hLmax
  have hc := SecondJetCombinedCount.count_of_interpolant S hI P m B s U L k n0 hP
    (avoidance S hown L hL) hsB hsU hsL hks hsm hBU hUL hdn hB
    (fun d hd => factorial_ne (K := K) d (by omega))
    (two_ne (K := GenericField K)) (factorial_ne (K := GenericField K) k (by omega)) hg1 hg2
  have hsumY : S.r+(S.y-S.r) = S.y := by have := S.ry; omega
  have hsumT : S.y+(S.t-S.y) = S.t := by have := S.yt; omega
  have hp := hproper S.r (S.y-S.r) (S.t-S.y) S.rpos (by have := S.ry; omega) hL
  have hp' : (S.pair (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1))).regularCountCap ≤ S.normal := by
    rw [normal_eq S hown]
    simpa only [Data.pair,properParameters,hsumY,hsumT] using hp
  have he : (S.pair B U L).regularCountCap ≤ 500000000000000 :=
    coefficient_count S.r S.y S.t B U L S.rbound S.ybound S.tbound hBmax hUmax hLmax
  apply hc.trans
  apply max_le
  · exact hp'.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · exact Nat.add_le_add_left he _

theorem count_116 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2233 < S.t-S.y) : S.seeds.card ≤ cost S 47 157 2233 5 7 := by
  exact count_of_profile S hI hown 116 47 21 157 2233 5 7 hL
    (exists_116 hI nodes u0 u1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) proper_le_normal_116

theorem count_96 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2141 < S.t-S.y) : S.seeds.card ≤ cost S 38 130 2141 4 5 := by
  exact count_of_profile S hI hown 96 38 17 130 2141 4 5 hL
    (exists_96 hI nodes u0 u1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) proper_le_normal_96

theorem count_108 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2111 < S.t-S.y) : S.seeds.card ≤ cost S 41 146 2111 4 7 := by
  exact count_of_profile S hI hown 108 41 19 146 2111 4 7 hL
    (exists_108 hI nodes u0 u1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    proper_le_normal_108

end
end ProximityPrize.SubmissionLower.SecondJetProfileBounds

end Compact_SecondJetProfileBounds
