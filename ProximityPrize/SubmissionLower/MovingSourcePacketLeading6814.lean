import ProximityPrize.SubmissionLower.MovingSourceOuterPrimeInjection6814
import ProximityPrize.SubmissionLower.MovingSourceUniformTail6814

/-! Count the Z-leading exception on the original arithmetic packet,
before geometric factorization. The proper-intersection theorem already
sums the geometric factors; this charge is therefore paid only once. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePacketLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceZLeadingSeeds6814
open MovingSourceCoupledClearing6814 SecondJetCoefficients
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local notation "w" => RCN326.w

def leadingPair : UnequalParameters := ⟨262144,131071,181255,57,12,3561,169,37,3421⟩

theorem leading_packet_cost : AsymmetricHelper.leftRegularCountCap leadingPair=23104862107476 := by
  decide +kernel

theorem packet_z_leading_seed_count
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hpos : 0<F.degreeOf 2)
    (hFY : F.degreeOf 1≤57) (hFR : F.degreeOf 2≤12) (hFZ : F.degreeOf 3≤3561)
    (SZ : Source F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card=262144)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤w)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      (nodes.filter (fun i => (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma∈Gamma, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma∈Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected Gamma w 80889) :
    (Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
      (SZ.leading (polynomialEmbedding K))=0)).card≤23104862107476 := by
  let Delta := Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
    (SZ.leading (polynomialEmbedding K))=0)
  have hsub : Delta⊆Gamma := Finset.filter_subset _ _
  have hw := z_leading_weights F SZ hSZ
  have hLC := SecondJetPairBounds.degree_caps_of_weights (asS SZ.P).leadingCoeff 37 169 3421 hw
  have hnot := SecondJetTotalAvoidance.leading_not_dvd SZ.P (source_nonzero F SZ) F 3429
    (fun e he => by have hh := (SZ.hshape e he).2.2; rw [hSZ.2.2.1] at hh; exact hh) hFT
  have hrel := hF.isRelPrime_iff_not_dvd.mpr hnot.2
  have hzero : ∀ gamma∈Delta, specialization K (selected gamma) gamma (asS SZ.P).leadingCoeff=0 := by
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
      (surfaceMap (polynomialEmbedding K) (asS SZ.P).leadingCoeff)=0 at hh
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  have hc := SecondJetProperCounting.regular_seed_bound_left leadingPair F (asS SZ.P).leadingCoeff
    hF hpos hrel 2130706433 hFY hFR hFZ hLC.1 hLC.2.1 hLC.2.2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    selected Delta nodes x u0 u1 hinj hnodes (by decide) (by decide) (by decide) (by decide)
    (fun gamma hg => hdegree gamma (hsub hg))
    (fun gamma hg => hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono selected Gamma Delta w 80889 hsub hno)
    (fun gamma hg => hsolution gamma (hsub hg)) (fun gamma hg => hregular gamma (hsub hg)) hzero
  have hb := SecondJetPairBounds.count_le_left_cap leadingPair F hFY hFR hFZ Delta.card (by decide) hc
  rw [leading_packet_cost] at hb
  exact hb

#print axioms packet_z_leading_seed_count
end
end ProximityPrize.SubmissionLower.MovingSourcePacketLeading6814
