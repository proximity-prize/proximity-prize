import ProximityPrize.SubmissionLower.MovingSourceBandSmallSupplier6814
import ProximityPrize.SubmissionLower.MovingSourceLowZ25Supplier6814

/-! Discharge the three lower-total interpolation sources and every
owner/helper branch at the seven low-source endpoints. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandLowPackets6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 30000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN234
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandCompleteOwners6814
open MovingSourceBandHelperCount6814 MovingSourceTwoProfiles6814 MovingSourceBandSmallSupplier6814
open MovingFiberThreeSources6811 MovingSourceBandCofactorPrices6814
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def lowIndex (j : Fin 7) : Fin 11 := ![2,3,4,6,8,9,10] j

theorem low7_helper_count {t y r : ℕ} (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (Q : MvPolynomial (Fin 4) K)
    (hhelper : MovingSourceLowZ7Supplier6814.ProperHelper P.F Q r y t nodes P.u0 P.u1) :
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

theorem low23_helper_count {t y r : ℕ} (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (Q : MvPolynomial (Fin 4) K)
    (hhelper : MovingSourceLowZ23Supplier6814.ProperHelper P.F Q r y t nodes P.u0 P.u1) :
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

theorem low25_helper_count {t y r : ℕ} (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (Q : MvPolynomial (Fin 4) K)
    (hhelper : MovingSourceLowZ25Supplier6814.ProperHelper P.F Q r y t nodes P.u0 P.u1) :
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

theorem low_packet_count (j : Fin 7) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) (cell (lowIndex j)).total (cell (lowIndex j)).middle (cell (lowIndex j)).slope)
    (hFT : (cell (lowIndex j)).L<wt residualTotalWeights P.F) : P.seeds.card<270000000000000000 := by
  have hr := P.rlow
  have hy := P.ylow
  have ht := P.yt
  have hFTsmall := (source_total_low (lowIndex j)).trans hFT
  rcases helper_or_small_source nodes P.u0 P.u1 hI P.F P.irreducible (by omega)
    (cell (lowIndex j)).slope (cell (lowIndex j)).middle (cell (lowIndex j)).total
    (by omega) (by omega) (by omega) ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelper | hsource
  · obtain ⟨Q,hQ⟩ := hhelper
    exact avoidance_helper_count nodes P Q hQ
  obtain ⟨small,hsmall⟩ := hsource
  fin_cases j
  · rcases MovingSourceLowZ7Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 2).slope (cell 2).middle (cell 2).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low7_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 2 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ23Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 3).slope (cell 3).middle (cell 3).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low23_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 3 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ25Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 4).slope (cell 4).middle (cell 4).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low25_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 4 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ25Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 6).slope (cell 6).middle (cell 6).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low25_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 6 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ7Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 8).slope (cell 8).middle (cell 8).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low7_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 8 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ23Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 9).slope (cell 9).middle (cell 9).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low23_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 9 nodes hI P small SZ hsmall hSZ hFT
  · rcases MovingSourceLowZ25Supplier6814.exists_helper_or_source nodes P.u0 P.u1 hI P.F P.irreducible hFT
      (cell 10).slope (cell 10).middle (cell 10).total (by decide) (by decide) (by decide)
      ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hhelp | hZ
    · obtain ⟨Q,hQ⟩ := hhelp
      exact low25_helper_count nodes P Q hQ
    · obtain ⟨SZ,hSZ⟩ := hZ
      exact packet_from_sources_count 10 nodes hI P small SZ hsmall hSZ hFT

#print axioms low_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandLowPackets6814
