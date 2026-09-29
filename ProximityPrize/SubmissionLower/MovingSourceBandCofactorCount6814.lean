import ProximityPrize.SubmissionLower.MovingSourceBandCofactorPrices6814
import ProximityPrize.SubmissionLower.MovingSourceBandNativeOwnerCount6814

/-! The retained cofactor now pays an actual original-packet seed count,
including all tail branches and the Z-leading exception. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandCofactorCount6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 30000
open RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceUniqueOwnerAlternative6814 WholeSpacePowerSourcePair6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814
open MovingSourceUniformPairBudget6814 MovingSourceBandNativeForms6814 MovingSourceBandNativeExit6814
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandPairCount6814
open MovingSourceBandPairArithmetic6814 MovingSourceBandLeading6814 MovingSourceBandCofactorPrices6814
open MovingSourcePairStageSupplier6814 SecondJetCarrierDichotomy
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K}

theorem weighted_owner_packet_count (i : Fin 11)
    (P : Packet x (cell i).total (cell i).middle (cell i).slope) [Fact (Irreducible P.F)]
    (small SZ : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hSZ : Profile SZ (cell i).B (cell i).U (cell i).L (cell i).s (cell i).k (cell i).n0)
    (hFT : (cell i).L<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJdiv : J∣small.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J small.P)
    (hpair : WeightedPair P.F J)
    (hfail : Failure i (multiplicity P.F J) (order J) (slope J) (middle J) (total J)) :
    P.seeds.card<270000000000000000 := by
  have hFchar : P.F.degreeOf 2<2130706433 :=
    P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  have hFTsmall := (source_total_low i).trans hFT
  obtain ⟨hm,_,hB,hU,hT,_,_⟩ := unique_owner_data P.F small hsmall hFTsmall
    P.rdegree hFchar J hJ hJdiv hroot hunique
  have hq := copies3_pos (multiplicity P.F J) hm
  have hb31 : slope J≤31 := by have := Nat.mul_le_mul_right (slope J) hq; omega
  have hu98 : middle J≤98 := by have := Nat.mul_le_mul_right (middle J) hq; omega
  have ht995 : total J≤995 := by have := Nat.mul_le_mul_right (total J) hq; omega
  obtain ⟨e,he,SJ,SQ,hSJ,hcop,hd,hJd,hQd,_,hct,hcu,hcb,hcs⟩ := source_pair_of_weighted_pair
    P.F (by omega) P.rdegree hFchar J hJ.ne_zero (by omega) hm hpair
  have hcoarse := cofactor_pair_prices J SQ.P (multiplicity P.F J) e hm he hB hU hT hcb hcu hct hcs
  have hprices := cofactor_prices i J SQ.P (multiplicity P.F J) e hm he hB hU hT hcb hcu hct hcs
    (fun hi hm3 => failure_five_order_le_ten _ _ _ _ _ hm3 hb31 hu98 ht995 (by simpa only [hi] using hfail))
  have hrec := receipts i
  have hZd : SZ.k<2130706433 := by rw [hSZ.2.2.2.2.1]; exact hrec.2.2.2.1
  have hgates : Gates (cell i).total (cell i).middle (cell i).slope
      (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0) := by
    rw [hSZ.1,hSZ.2.1,hSZ.2.2.1,hSZ.2.2.2.2.2]
    exact hrec.2.1
  have hcount := pair_packet_count P SZ SJ SQ (by rwa [hSZ.2.2.1]) hZd hgates hcop
    (min (multiplicity P.F J) (3-e*multiplicity P.F J)) hd (by omega) hJd hQd
    (by simpa only [hSJ] using hcoarse.1) (by simpa only [hSJ] using hcoarse.2.2.1)
  have hprice := pairStageCost_le_weighted SZ SJ SQ
    (min (multiplicity P.F J) (3-e*multiplicity P.F J))
    (uCap i (bucket (multiplicity P.F J) e)) (vCap i (bucket (multiplicity P.F J) e))
    (cell i).total (cell i).middle (cell i).slope
    (by rw [hSJ]; exact Nat.add_le_add (Nat.mul_le_mul_left _ hprices.1) (Nat.mul_le_mul_left _ hprices.2))
  have hn := hcount.trans (max_le_max le_rfl (Nat.add_le_add_right hprice _))
  rw [bucket_order _ _ hm he,pricedPair_of_profile SZ (cell i) hSZ,
    leadingPrice_of_profile SZ (cell i) hSZ] at hn
  exact hn.trans_lt (cofactor_receipts i (bucket (multiplicity P.F J) e))

#print axioms weighted_owner_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandCofactorCount6814
