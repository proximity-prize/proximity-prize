import ProximityPrize.SubmissionLower.PortfolioBoxCover6815
import ProximityPrize.SubmissionLower.PortfolioHighOwner6815
import ProximityPrize.SubmissionLower.PortfolioLinearShape6815
namespace ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceBandGeometry6815 MovingSourceBandLeading6815 MovingSourceBandIdentity6815
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 PortfolioOwners6815
open PortfolioBoxes6815 PortfolioBoxCount6815 PortfolioBoxCover6815 PortfolioCost6815
open PortfolioLinearRoute6815 PortfolioLinearPacket6815

def rootBox (B U L s m : ℕ) : Box :=
  ⟨max m 2,s/copies3 m,2*max m 2,B/copies3 m,0,U/copies3 m,0,L/copies3 m⟩

def LinearChecks (B U L t y r cap : ℕ) : Prop :=
  Gates t y r (B-2) (U-1) (L-1) ∧
  flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433 ∧
  linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
    (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)≤cap
instance (B U L t y r cap : ℕ) : Decidable (LinearChecks B U L t y r cap) := by
  unfold LinearChecks Gates; infer_instance

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r : ℕ}

theorem packet_count (nodes : I ↪ K) (hI : Fintype.card I=262144)
    (P : Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (S SZ : Source P.F) (B U L s : ℕ) (hS : Profile S B U L s 2 3)
    (z : Degrees) (hZ : Fits SZ z) (low cap : ℕ)
    (hT : L≤995) (hFT : low≤wt residualTotalWeights P.F) (hlow : 2985<low)
    (hB : 14≤B) (hBU : B≤U) (hUL : U≤L) (hcap : 1000000000000000≤cap)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J S.P)
    (hlc : LinearChecks (B/3) (U/3) (L/3) t y r cap)
    (hhigh : Gates t y r (B-14) (U-7) (L-7) ∧
      nativeScalar (PortfolioHighOwner6815.degrees B U L) t y r/21+
        leading (PortfolioHighOwner6815.degrees B U L) t y r≤cap)
    (hc : ∀ m, 0<m → m≤6 → Covered m (Valid z m low t y r cap) (rootBox B U L s m)) :
    P.seeds.card≤max (identityPrice t y r) cap := by
  have hchar : P.F.degreeOf 2<2130706433 := P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨hm,hms,hb,hu,ht,hs,htriple,hne⟩ := unique_owner_data P.F S B U L s hS hT
    (hlow.trans_le hFT) P.rdegree hchar J hJ hJS hroot hunique
  let m := multiplicity P.F J
  have hm' : 0<m := hm
  have hq := copies3_pos m hm
  have hbd : slope J≤B/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hb)
  have hud : middle J≤U/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hu)
  have htd : total J≤L/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using ht)
  have hsd : order J≤s/copies3 m := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hs)
  have hn := source_nested J
  by_cases hlin : order J=1
  · have hme : m=1 := by omega
    have hqe : copies3 m=3 := by rw [hme]; rfl
    rw [hqe] at hbd hud htd
    have hshape : ∀ e∈J.support, 2*e 1+e 3≤B/3 ∧ e 1+e 2+e 3≤U/3 ∧ e 1+e 2+e 3+e 4≤L/3 := by
      intro e he
      have h1 := (le_weightedTotalDegree slopeWeights he).trans hbd
      have h2 := (le_weightedTotalDegree middleWeights he).trans hud
      have h3 := (le_weightedTotalDegree totalWeights he).trans htd
      refine ⟨?_,?_,?_⟩
      · simpa [weight_coords,slopeWeights,Nat.mul_comm] using h1
      · simpa [weight_coords,middleWeights] using h2
      · simpa [weight_coords,totalWeights] using h3
    exact (PortfolioLinearShape6815.packet_count_of_shape P J hJ.ne_zero hlin (B/3) (U/3) (L/3)
      (by omega) (Nat.div_le_div_right hBU) (Nat.div_le_div_right hUL) hshape
      (by have := Nat.div_le_self L 3; omega) hroot hlc.1 hlc.2.1).trans (max_le_max le_rfl hlc.2.2)
  have hs2 : 2≤order J := by omega
  have hb0 := hbd.trans (Nat.div_le_self B (copies3 m))
  have hu0 := hud.trans (Nat.div_le_self U (copies3 m))
  have ht0 := htd.trans (Nat.div_le_self L (copies3 m))
  have hs0 := hsd.trans (Nat.div_le_self s (copies3 m))
  by_cases hm7 : 7≤m
  · exact PortfolioHighOwner6815.packet_count P J m B U L s cap hm7 hms hs0 hb0 hu0 ht0
      hB hBU hUL (by omega) rfl hhigh.1 hhigh.2
  have ha : Admissible m (point J) := ⟨hms,hs2,htriple,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
  have hx : Contains (rootBox B U L s m) (point J) := by
    dsimp only [Contains,rootBox,point]
    exact ⟨max_le hms hs2,hsd,by omega,hbd,Nat.zero_le _,hud,Nat.zero_le _,htd⟩
  exact count_of_covered nodes hI P SZ z hZ _ m low cap hFT (by omega) hcap J hJ ha hx rfl hne
    (hc m hm (by omega))

end
end ProximityPrize.SubmissionLower.PortfolioUniqueCount6815
