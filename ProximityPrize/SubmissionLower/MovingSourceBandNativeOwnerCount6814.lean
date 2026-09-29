import ProximityPrize.SubmissionLower.MovingSourceBandNonlinearAlternative6814

/-! Close the native-fitting alternative for the actual selected owner.
Its source record exposes the degree fields needed to charge exceptions. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeOwnerCount6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 25000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceUniqueOwnerAlternative6814
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandNativeExit6814
open MovingSourceBandNativeArithmetic6814 MovingSourceBandNonlinearAlternative6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCarrierField6814
open MovingSourceOwnerSplit6814 MovingSourceOwnerRouting6814 MovingSourceNativeFactor6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814
open SecondJetCoefficients SecondJetClearedHelper SecondJetCarrierDichotomy
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K}

theorem exact_owner_source (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (m s b u t : ℕ) (hm : 0<m) (hms : m≤s)
    (hs : J.degreeOf 1=s) (h2s : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hshape : ∀ e∈J.support, 2*e 1+e 3≤b ∧ e 1+e 2+e 3≤u ∧ e 1+e 2+e 3+e 4≤t)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ S : Source F, S.P=J ∧ Profile S b u t s (m-1) s := by
  have hS : ∀ e∈J.support, e 1≤s := MvPolynomial.degreeOf_le_iff.mp hs.le
  have hH := carrier_H_nonzero F hpos hchar
  let source : Source F := {
    P := J, B := b, U := u, T := t, s := s, k := m-1, n0 := s
    hS := hS, hshape := hshape, hBU := hbu, hUT := hut
    hdn := by omega, hB := by omega
    hn := by rw [asS_natDegree,hs]
    hdiv := by
      intro d hd
      apply (carrierMap_zero_iff F _).mp
      rw [mapped_helper J F (carrierMap F) s d hS hH]
      have hz : ((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0 :=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot]; omega)
      rw [hz,mul_zero] }
  exact ⟨source,rfl,by repeat' constructor⟩

theorem native_owner_packet_count (i : Fin 11)
    (P : Packet x (cell i).total (cell i).middle (cell i).slope) [Fact (Irreducible P.F)]
    (small : Source P.F) (hsmall : Profile small 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights P.F)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hJdiv : J∣small.P)
    (hroot : rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap P.F) (ratio (carrierMap P.F) P.F)) J small.P)
    (hfit : ownerCost i P.F J<3*269880000000000000*multiplicity P.F J) :
    P.seeds.card<270000000000000000 := by
  have hFchar : P.F.degreeOf 2<2130706433 :=
    P.coordinate_bounds.2.1.trans_lt (by have := P.rhigh; omega)
  obtain ⟨hm,hms,hB,hU,hT,hex,hJne⟩ := unique_owner_data P.F small hsmall hFT
    P.rdegree hFchar J hJ hJdiv hroot hunique
  have hq := copies3_pos (multiplicity P.F J) hm
  have hb31 : slope J≤31 := by have := Nat.mul_le_mul_right (slope J) hq; omega
  have hu98 : middle J≤98 := by have := Nat.mul_le_mul_right (middle J) hq; omega
  have ht995 : total J≤995 := by have := Nat.mul_le_mul_right (total J) hq; omega
  have hn := source_nested J
  have hshape : ∀ e∈J.support, 2*e 1+e 3≤slope J ∧
      e 1+e 2+e 3≤max (slope J) (middle J) ∧ e 1+e 2+e 3+e 4≤max (slope J) (total J) := by
    intro e he
    constructor
    · simpa [slope,weight_coords,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
    constructor
    · have hh : e 1+e 2+e 3≤middle J := by
        simpa [middle,weight_coords,middleWeights] using MvPolynomial.le_weightedTotalDegree middleWeights he
      exact hh.trans (le_max_right _ _)
    · have hh : e 1+e 2+e 3+e 4≤total J := by
        simpa [total,weight_coords,totalWeights] using MvPolynomial.le_weightedTotalDegree totalWeights he
      exact hh.trans (le_max_right _ _)
  obtain ⟨S,hSP,hprofile⟩ := exact_owner_source P.F P.rdegree hFchar J (multiplicity P.F J) (order J)
    (slope J) (max (slope J) (middle J)) (max (slope J) (total J)) hm hms rfl hn.2.2.1
    (le_max_left _ _) (max_le_max le_rfl hn.1) hshape rfl
  have hd : S.d=multiplicity P.F J := by dsimp [Source.d]; rw [hprofile.2.2.2.2.1]; omega
  have hf : S.flag=SecondJetRelaxedFlag.budgetFlag (slope J) (max (slope J) (middle J))
      (max (slope J) (total J)) (multiplicity P.F J) (order J) := by
    unfold Source.flag
    rw [hprofile.1,hprofile.2.1,hprofile.2.2.1,hprofile.2.2.2.2.2,hd]
  apply native_small_packet_count i P S
    (by rw [hprofile.2.2.2.2.1]; have hh := hn.2.2.1; omega)
    (by rw [hprofile.2.2.1]; omega) (by rw [hprofile.1]; exact hb31)
    (by rw [hprofile.2.1]; omega) (by rw [hprofile.2.2.1]; omega)
  rw [native_numerator_eq S i _ _ _ _ _ hm hd hf,hd]
  exact hfit

#print axioms native_owner_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeOwnerCount6814
