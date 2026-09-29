import ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814

/-! Original-packet proper cuts and Z-leading exceptions for the audited
cell dimensions. The Z source is not fixed to the ineligible L=3429
profile at smaller carrier totals. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open MovingSourceBandGeometry6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open SecondJetCoefficients SecondJetHelperWeights
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}

def pair (t y r b u l : ℕ) : UnequalParameters := ⟨262144,131071,181255,y,r,t,u,b,l⟩

def Gates (t y r b u l : ℕ) : Prop :=
  (pair t y r b u l).mixedCost.y<2130706433 ∧
  (pair t y r b u l).mixedCost.r<2130706433 ∧
  (pair t y r b u l).mixedCost.z<2130706433

theorem proper_cut_count (P : Packet x t y r) (Q : MvPolynomial (Fin 4) K)
    (b u l : ℕ) (hrel : IsRelPrime P.F Q)
    (hweights : wt residualSWeights Q≤b ∧ wt residualYSWeights Q≤u ∧ wt residualTotalWeights Q≤l)
    (hgates : Gates t y r b u l)
    (hzero : ∀ gamma∈P.seeds, specialization K (P.selected gamma) gamma Q=0) :
    P.seeds.card≤AsymmetricHelper.leftRegularCountCap (pair t y r b u l) := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hyhi := P.yhigh
  have hthi := P.thigh
  have hQ := SecondJetPairBounds.degree_caps_of_weights Q b u l hweights
  have hc := SecondJetProperCounting.regular_seed_bound_left (pair t y r b u l) P.F Q
    P.irreducible P.rdegree hrel 2130706433 P.coordinate_bounds.1 P.coordinate_bounds.2.1 P.coordinate_bounds.2.2
    hQ.1 hQ.2.1 hQ.2.2 (by dsimp [pair]; omega) (by dsimp [pair]; omega)
    (by dsimp [pair]; omega) (by dsimp [pair]; omega) hgates.1 hgates.2.1 hgates.2.2
    P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.nodeCount
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    P.degree P.agreement
    (by simpa only [pair,UnequalParameters.errors,Nat.reduceSub,RCN326.w] using P.noPencil)
    P.solution P.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (pair t y r b u l) P.F P.coordinate_bounds.1
    P.coordinate_bounds.2.1 P.coordinate_bounds.2.2 P.seeds.card (by norm_num [pair,UnequalParameters.gap]) hc

theorem source_leading_weights (F : MvPolynomial (Fin 4) K) (S : Source F) :
    wt residualSWeights (asS S.P).leadingCoeff≤S.B-2*S.n0 ∧
    wt residualYSWeights (asS S.P).leadingCoeff≤S.U-S.n0 ∧
    wt residualTotalWeights (asS S.P).leadingCoeff≤S.T-S.n0 := by
  have hn := S.hn
  have hw := derivative_coefficient_weights S.P S.B S.U S.T 0 (asS S.P).natDegree S.hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  rw [Polynomial.leadingCoeff]
  omega

def leadingPrice {F : MvPolynomial (Fin 4) K} (S : Source F) (t y r : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (pair t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0))

theorem packet_z_leading_count (P : Packet x t y r) (S : Source P.F)
    (hFT : S.T<wt residualTotalWeights P.F)
    (hgates : Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)) :
    (P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (S.leading (polynomialEmbedding K))=0)).card≤leadingPrice S t y r := by
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (S.leading (polynomialEmbedding K))=0)
  let PB := P.restrict bad (Finset.filter_subset _ _)
  have hnot := SecondJetTotalAvoidance.leading_not_dvd S.P (source_nonzero P.F S) P.F S.T
    (fun e he => (S.hshape e he).2.2) hFT
  have hzero : ∀ gamma∈bad, specialization K (P.selected gamma) gamma (asS S.P).leadingCoeff=0 := by
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (surfaceMap (polynomialEmbedding K) (asS S.P).leadingCoeff)=0 at hh
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  exact proper_cut_count PB (asS S.P).leadingCoeff (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)
    (P.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2) (source_leading_weights P.F S) hgates hzero

#print axioms proper_cut_count
#print axioms packet_z_leading_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandLeading6814
