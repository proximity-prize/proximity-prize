import ProximityPrize.SubmissionLower.MovingSourceBandCofactorCount6814
import ProximityPrize.SubmissionLower.MovingSourceBandWideLinear6814

/-! Complete all owner branches at270e15. The theorem assumes the two
actual retained interpolation sources, but no owner, count or budget
supplier: the exhaustive split and every branch are discharged here. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandCompleteOwners6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 30000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandOwnerEndpoints6814
open MovingSourceBandNativeOwnerCount6814 MovingSourceBandCofactorCount6814 MovingSourceBandCofactorPrices6814
open MovingSourceBandNonlinearAlternative6814 MovingSourceBandHelperCount6814 MovingSourceBandWideLinear6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814 MovingSourceMixedOwnerRouting6814
open MovingSourceSameSourceBudget6814 MovingSourceWideLinearFlow6814 MovingSourceCoupledClearing6814
open WholeSpaceUniqueOwnerAlternative6814 SecondJetCoefficients SecondJetCarrierDichotomy
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem avoidance_helper_count {t y r : ℕ} (nodes : I ↪ K) (P : Packet (nodes : I → K) t y r)
    (Q : MvPolynomial (Fin 4) K)
    (hhelper : WholeSpaceSourceAlternative6814.ProperHelper P.F Q r y t nodes P.u0 P.u1) :
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

theorem nonlinear_owner_count (i : Fin 11) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) (cell i).total (cell i).middle (cell i).slope) [Fact (Irreducible P.F)]
    (small SZ : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hSZ : Profile SZ (cell i).B (cell i).U (cell i).L (cell i).s (cell i).k (cell i).n0)
    (hFT : (cell i).L<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJdiv : J∣small.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J small.P)
    (hs : 2≤order J) : P.seeds.card<270000000000000000 := by
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have hFTsmall := (source_total_low i).trans hFT
  have hr := P.rlow
  have hy := P.ylow
  have ht := P.yt
  rcases unique_nonlinear_alternative i nodes P.u0 P.u1 hI P.F small hsmall hFTsmall
    P.rdegree hFchar J hJ hJdiv hroot hunique hs (cell i).slope (cell i).middle (cell i).total
    (by omega) (by omega) (by omega) ⟨P.r_weight,P.y_weight,P.total_weight⟩ with hnative | hhelper | hpair
  · exact native_owner_packet_count i P small hsmall hFTsmall J hJ hJdiv hroot hunique hnative
  · obtain ⟨Q,hQ⟩ := hhelper
    exact avoidance_helper_count nodes P Q hQ
  · exact weighted_owner_packet_count i P small SZ hsmall hSZ hFT J hJ hJdiv hroot hunique hpair.1 hpair.2

theorem packet_from_sources_count (i : Fin 11) (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) (cell i).total (cell i).middle (cell i).slope)
    (small SZ : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hSZ : Profile SZ (cell i).B (cell i).U (cell i).L (cell i).s (cell i).k (cell i).n0)
    (hFT : (cell i).L<wt residualTotalWeights P.F) : P.seeds.card<270000000000000000 := by
  letI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  have hFchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have hFTsmall := (source_total_low i).trans hFT
  have hs := canonical_source_power P.F small (by rw [hsmall.2.2.1]; omega) P.rdegree hFchar
    (by rw [hsmall.2.2.2.2.1]; decide)
  have hpow : (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^3∣rootPolynomialMap (carrierMap P.F) small.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^3∣(asS small.P).map (carrierMap P.F)
    simpa only [Source.d,hsmall.2.2.2.2.1] using hs.2
  have hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) small.P=0 :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by decide : 3≠0)).trans hpow)
  obtain ⟨J,hJ,hJdiv,hJroot,hcases⟩ := small_source_first_split
    (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) small.P (source_nonzero P.F small) hroot
  rcases hcases with huni | htwo
  · have hjpos := factor_order_pos_of_root (carrierMap P.F) _ small.P J hs.1 hJdiv hJroot
    by_cases hlinear : J.degreeOf 1=1
    · exact packet_wide_linear_count_all P J
        (wide_linear_route P.F small hsmall hFTsmall P.rdegree hFchar J hJ hJdiv hlinear hJroot huni)
    · exact nonlinear_owner_count i nodes hI P small SZ hsmall hSZ hFT J hJ hJdiv hJroot huni
        (by change 2≤J.degreeOf 1; change 0<J.degreeOf 1 at hjpos; omega)
  · obtain ⟨D,hD,hDdiv,hDroot,hcop⟩ := htwo
    exact same_owner_endpoint_count i P small SZ hsmall hSZ hFT J D hJ.ne_zero hD.ne_zero hcop hJdiv hDdiv hJroot hDroot

#print axioms nonlinear_owner_count
#print axioms packet_from_sources_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandCompleteOwners6814
