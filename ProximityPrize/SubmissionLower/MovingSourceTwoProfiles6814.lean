import ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
namespace ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceSourceCounts6814 WholeSpaceSourceKernel6814
open MovingFiberThreeSources6811 MovingSourceCarrierField6814
open RCN234 RCN156

variable {K N : Type} [Field K] [Fintype N]

def Profile {F : MvPolynomial (Fin 4) K} (S : Source F) (B U T s k n0 : ℕ) : Prop :=
  S.B=B ∧ S.U=U ∧ S.T=T ∧ S.s=s ∧ S.k=k ∧ S.n0=n0

theorem source_nonzero (F : MvPolynomial (Fin 4) K) (S : Source F) : S.P≠0 := by
  intro hz
  have hh := S.hn
  rw [hz,map_zero,Polynomial.natDegree_zero] at hh
  have hd := S.hdn
  omega

theorem canonical_source_power [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (S : Source F)
    (hT : S.T<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hk : S.k<2130706433) :
    (asS S.P).map (carrierMap F)≠0 ∧
      (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio (carrierMap F) F))^S.d ∣
        (asS S.P).map (carrierMap F) := by
  have hn := carrier_polynomial_nonzero F S.P (source_nonzero F S) S.T
    (fun e he => (S.hshape e he).2.2) hT
  exact ⟨hn,SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd S.P F (carrierMap F)
    S.s S.k S.hS (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hn
    (SecondJetOwnShape.factorial_ne S.k hk) S.hdiv⟩

end
end ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
