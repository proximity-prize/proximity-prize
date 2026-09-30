import ProximityPrize.SubmissionLower.PortfolioSource6815
import ProximityPrize.SubmissionLower.PacketFourRetention6815
import ProximityPrize.SubmissionLower.CarrierSizedSource6815
namespace ProximityPrize.SubmissionLower.PortfolioAvoidanceSource6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open PortfolioSource6815 SecondJetCoefficients SecondJetCarrierDichotomy
open MovingSourceCarrierField6814 MovingSourceCoupledClearing6814 MovingFiberThreeSources6811
open RCN234 RCN156

def caps (p : Parameters) : PacketPortfolioAvoidance6815.SourceCaps :=
  ⟨p.m*181245,p.L,p.B,p.s,p.U⟩

variable {K N : Type} [Field K] [Fintype N]

theorem weighted_bounds (p : Parameters) (hp : Shape p) (P : Poly (K:=K)) (hb : Bounds p P) :
    PacketPortfolioAvoidance6815.Bounds (caps p) P := by
  have hc : weightedTotalDegree codeWeights P≤p.m*181245-1 := by
    apply Finset.sup_le
    intro e he
    have hh := (hb e he).2.2.2.2
    have hcut : p.cutoff (e 1)≤p.m*181245 := Nat.sub_le _ _
    simp [weight_coords,codeWeights]
    omega
  have hm : 0<p.m := lt_of_le_of_lt (Nat.zero_le _) hp.contact
  refine ⟨by dsimp [caps]; omega,?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    simpa [caps,weight_coords,totalWeights] using (hb e he).2.2.2.1
  · apply Finset.sup_le
    intro e he
    simpa [caps,weight_coords,slopeWeights,Nat.mul_comm] using (hb e he).1
  · exact MvPolynomial.degreeOf_le_iff.mpr (fun e he => (hb e he).2.1)
  · apply Finset.sup_le
    intro e he
    simpa [caps,weight_coords,middleWeights] using (hb e he).2.2.1

theorem exists_interpolant_not_power
    (p : Parameters) (hp : Shape p) (Kdim : ℕ) (hd : Dimension p Kdim)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : Poly (K:=K)) (hJ : J≠0) (a : PacketPortfolioAvoidance6815.OwnerBox)
    (ha : PacketPortfolioAvoidance6815.Covers a J)
    (hgood : (PacketPortfolioAvoidance6815.Impossible (caps p) a ∧ 0<Kdim) ∨
      PacketPortfolioAvoidance6815.count (caps p) a<Kdim) :
    ∃ P, Interpolant p nodes u0 u1 P ∧ ¬J^a.q∣P := by
  obtain ⟨V,hf,hv,hb,hc⟩ := exists_kernel p hp Kdim hd nodes u0 u1 hN
  letI : Module.Finite K V := hf
  obtain ⟨P,hP,hnot⟩ := PacketPortfolioAvoidance6815.exists_not_dvd_power (caps p) a Kdim
    V hv (fun P hP => weighted_bounds p hp P (hb P hP)) J hJ ha hgood
  exact ⟨P,⟨by intro hz; exact hnot (by rw [hz]; exact dvd_zero _),hb P hP,hc P hP⟩,hnot⟩

theorem helper_or_coprime_sources_retained [CharP K 2130706433]
    (p : Parameters) (hp : Shape p) (Kdim : ℕ) (hd : Dimension p Kdim)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : p.L<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (J : Poly (K:=K)) (hJ : Irreducible J)
    (Jcap : ℕ) (hTJ : total J≤Jcap) (hJFT : Jcap<wt residualTotalWeights F)
    (m : ℕ) (hm : 0<m)
    (hmul : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m)
    (hJne : (asS J).map (carrierMap F)≠0)
    (a : PacketPortfolioAvoidance6815.OwnerBox) (hq : a.q=(p.k+1+m-1)/m)
    (ha : PacketPortfolioAvoidance6815.Covers a J)
    (hgood : (PacketPortfolioAvoidance6815.Impossible (caps p) a ∧ 0<Kdim) ∨
      PacketPortfolioAvoidance6815.count (caps p) a<Kdim) :
    (∃ Q, ProperHelper p F Q r y t nodes u0 u1) ∨
      ∃ e<a.q, ∃ SJ SQ : Source F, SJ.P=J ∧ IsRelPrime SJ.P SQ.P ∧
        0<min m (p.k+1-e*m) ∧ min m (p.k+1-e*m)≤SJ.d ∧ p.k+1-e*m≤SQ.d ∧
        e*total J+total SQ.P≤p.L ∧ e*middle J+middle SQ.P≤p.U ∧
        e*slope J+slope SQ.P≤p.B ∧ e*order J+order SQ.P≤p.s := by
  obtain ⟨P,hP,hnot⟩ := exists_interpolant_not_power p hp Kdim hd nodes u0 u1 hN J hJ.ne_zero a ha hgood
  rcases helper_or_retained p hp nodes u0 u1 P hP F Fact.out hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  have hpow : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^(p.k+1)∣(asS P).map (carrierMap F) := by
    by_cases hz : (asS P).map (carrierMap F)=0
    · rw [hz]; exact dvd_zero _
    have hk : p.k<2130706433 := lt_of_lt_of_le (by have := hp.retention; omega) (hp.degree.trans hp.characteristic.le)
    exact multiplicity_of_helpers_dvd P F (carrierMap F) p.s p.k
      (fun e he => (hP.2.1 e he).2.1) (carrierMap_self F) (carrier_H_nonzero F hpos hchar) hz
      (SecondJetOwnShape.factorial_ne p.k hk) hret.2
  have hnot' : ¬J^((p.k+1+m-1)/m)∣P := by rwa [←hq]
  obtain ⟨e,he,Q,hEq,hQ,hcop,hdelta,hpowQ⟩ := PacketFourRetention6815.retained_pair_extract
    (MovingSourceOwnerSplit6814.rootPolynomialMap (carrierMap F)) (ratio (carrierMap F) F)
    J P hJ (p.k+1) m hm hnot' hJne hmul hpow
  have hb := weighted_bounds p hp P hP.2.1
  obtain ⟨_,hT,hB,hS,hU⟩ := hb
  rw [hEq,weight_mul _ _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow _ _ hJ.ne_zero] at hT hB hU
  rw [hEq,degreeOf_mul_eq (pow_ne_zero _ hJ.ne_zero) hQ,degreeOf_pow_eq _ _ _ hJ.ne_zero] at hS
  have hpowJ : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^m∣(asS J).map (carrierMap F) := by
    rw [←hmul]; exact Polynomial.pow_rootMultiplicity_dvd _ _
  obtain ⟨SJ,hSJ,hSd⟩ := CarrierSizedSource6815.source_of_power_below_carrier
    F Jcap hJFT hpos hchar J hJ.ne_zero hTJ m hm hpowJ
  obtain ⟨SQ,hSQ,hQd⟩ := CarrierSizedSource6815.source_of_power_below_carrier
    F p.L hFT hpos hchar Q hQ
    (by change weightedTotalDegree totalWeights Q≤p.L; dsimp [caps] at hT; omega)
    (p.k+1-e*m) (lt_of_lt_of_le hdelta (min_le_right _ _)) hpowQ
  refine Or.inr ⟨e,by simpa only [hq] using he,SJ,SQ,hSJ,?_,hdelta,
    (min_le_left _ _).trans hSd,hQd,?_,?_,?_,?_⟩
  · rwa [hSJ,hSQ]
  · simpa only [hSQ,caps,total] using hT
  · simpa only [hSQ,caps,middle] using hU
  · simpa only [hSQ,caps,slope] using hB
  · simpa only [hSQ,caps,order] using hS

end
end ProximityPrize.SubmissionLower.PortfolioAvoidanceSource6815
