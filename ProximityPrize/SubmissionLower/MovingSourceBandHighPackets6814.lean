import ProximityPrize.SubmissionLower.MovingSourceBandCompleteOwners6814

/-! Unconditional packet counts for the four endpoints using the existing
L3429 interpolant. The sources and all helper/owner cases are discharged. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandHighPackets6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN234
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandCompleteOwners6814
open MovingSourceBandHelperCount6814 MovingSourceTwoProfiles6814
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def highIndex (j : Fin 4) : Fin 11 := ![0,1,5,7] j

theorem high_profile (j : Fin 4) :
    (cell (highIndex j)).B=53 ∧ (cell (highIndex j)).U=177 ∧ (cell (highIndex j)).L=3429 ∧
    (cell (highIndex j)).s=24 ∧ (cell (highIndex j)).k=6 ∧ (cell (highIndex j)).n0=8 := by
  fin_cases j <;> decide +kernel

theorem z_helper_count {t y r : ℕ} (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (Q : MvPolynomial (Fin 4) K)
    (hhelper : MovingSourceZSupplier6814.ProperHelper P.F Q r y t nodes P.u0 P.u1) :
    P.seeds.card<270000000000000000 := by
  have hw : wt residualSWeights Q≤341 ∧ wt residualYSWeights Q≤1521 ∧ wt residualTotalWeights Q≤89277 := by
    have hh := hhelper.2.1
    have hr := P.rhigh
    have hy := P.yhigh
    have ht := P.thigh
    omega
  apply packet_helper_count P Q hhelper.1 hw
  intro gamma hg
  exact hhelper.2.2 (P.selected gamma) (P.degree gamma hg) gamma
    (P.nodes.filter (fun j => (P.selected gamma).eval (nodes j)=P.u0 j+gamma*P.u1 j))
    (P.agreement gamma hg) (fun j hj => by simpa only [mul_comm] using (Finset.mem_filter.mp hj).2)
    (P.solution gamma hg)

theorem high_packet_count (j : Fin 4) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) (cell (highIndex j)).total (cell (highIndex j)).middle (cell (highIndex j)).slope)
    (hFT : 3429<wt residualTotalWeights P.F) : P.seeds.card<270000000000000000 := by
  have hr := P.rlow
  have hy := P.ylow
  have ht := P.yt
  rcases helpers_or_two_profiles nodes P.u0 P.u1 hI P.F P.irreducible hFT
    (cell (highIndex j)).slope (cell (highIndex j)).middle (cell (highIndex j)).total
    (by omega) (by omega) (by omega) ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hsmall | hZ | hsources
  · obtain ⟨Q,hQ⟩ := hsmall
    exact avoidance_helper_count nodes P Q hQ
  · obtain ⟨Q,hQ⟩ := hZ
    exact z_helper_count nodes P Q hQ
  · obtain ⟨small,SZ,hsmall,hSZ⟩ := hsources
    obtain ⟨hB,hU,hL,hs,hk,hn⟩ := high_profile j
    exact packet_from_sources_count (highIndex j) nodes hI P small SZ hsmall
      (by rw [hB,hU,hL,hs,hk,hn]; exact hSZ) (by rwa [hL])

#print axioms high_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandHighPackets6814
