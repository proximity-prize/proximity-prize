import ProximityPrize.SubmissionLower.MovingSourceBandOwnerEndpoints6814

/-! The native owner retains the old additive source price, so the
submitted per-direction count sums directly over geometric Stages.
Only the agreement/error profile changes to181255/80889. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN332 RCN334 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingSourceBandGeometry6814
open MovingFiberThreeSources6811 HFreeDir6813
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}
local notation "Ω" => GenericField K

def nativeNumerator {F : MvPolynomial (Fin 4) K} (source : Source F) (t y r : ℕ) (fl : FlagDegree) : ℕ :=
  numeratorDir (fun _ => source) (3*source.d) t y r fl

theorem native_regular_packet_count
    (P : Packet x t y r) (hp : ¬P.F∣numerator K P.F (w+1)) (source : Source P.F)
    (hk : source.k<2130706433)
    (hgood : ∀ gamma∈P.seeds, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
      (source.leading (polynomialEmbedding K))≠0) :
    (3*source.d)*P.seeds.card≤nativeNumerator source t y r ⟨t-y,y-r,r⟩ := by
  have hrlo := P.rlow
  have hrhi := P.rhigh
  have hylo := P.ylow
  have hyhi := P.yhigh
  have hyt := P.yt
  have hthi := P.thigh
  have hd : 0<3*source.d := by dsimp [Source.d]; omega
  have hstage (g : GeometricFactor K P.F) :
      (3*source.d)*(geometricSeeds K P.F P.selected P.seeds g).card≤nativeNumerator source t y r (geometricCumulativeFlag K g) := by
    let S := P.stage g
    have hflag := P.stage_flag g
    have hc : (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).all<2130706433 ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all<2130706433 := by omega
    have hm := BoundaryTailGates.reduced_gate (geometricCumulativeFlag K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hproper := P.stage_proper hp g
    let B := BoundaryTailReduced.reducedBudgetFamily S hproper hc hm
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1) →
        (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) (geometricSeeds K P.F P.selected P.seeds g)
          (selectedPoint (polynomialEmbedding K) S.selected) C).card≤80890*B.yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hproper (BoundaryTailReduced.reducedBaseOrd S hproper hc hm C)
        181255 P.D t r P.nodeCount (P.stage_agreement g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hproper hc hm C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hproper hc hm C)
    have hh := retained_stage_bound_dir t y r (3*source.d) (by omega) (by omega) (by omega)
      S (fun _ => source) hd (fun _ => dvd_rfl) (hfree_stage_dir_of_gaps S (by rw [P.support_caps.2.2]; omega)) hproper hc hm
      (by omega)
      (by
        have htotal := hflag.2.2.trans hthi
        calc
          _≤2*3578*3579 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 htotal) (by omega)
          _<2130706433 := by decide)
      (by decide) (by dsimp [cellNormal,BoundaryTailAlgebra.normalFlag,RCN327.w]; omega) htangent SecondJetOwnShape.two_ne
      (fun _ => SecondJetOwnShape.factorial_ne source.k hk)
      (fun gamma hgamma _ => hgood gamma (geometricSeeds_subset K P.F P.selected P.seeds g hgamma))
    exact (Nat.mul_comm _ _).trans_le ((Nat.le_div_iff_mul_le hd).mp hh)
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hsum := sum_numeratorDir_le (fun _ => source) (3*source.d) t y r
    (geometricCumulativeFlag K) ⟨t-y,y-r,r⟩
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp; omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp; omega))
  calc
    _≤(3*source.d)*(∑ g, (geometricSeeds K P.F P.selected P.seeds g).card) := Nat.mul_le_mul_left _ P.seeds_cover
    _=∑ g, (3*source.d)*(geometricSeeds K P.F P.selected P.seeds g).card := Finset.mul_sum _ _ _
    _≤∑ g, nativeNumerator source t y r (geometricCumulativeFlag K g) := Finset.sum_le_sum (fun g _ => hstage g)
    _≤_ := hsum

open MovingSourceBandIdentity6814 MovingSourceBandLeading6814

theorem native_packet_count (P : Packet x t y r) (source : Source P.F)
    (hk : source.k<2130706433) (hFT : source.T<wt residualTotalWeights P.F)
    (hgates : Gates t y r (source.B-2*source.n0) (source.U-source.n0) (source.T-source.n0)) :
    P.seeds.card≤max (identityPrice t y r)
      (nativeNumerator source t y r ⟨t-y,y-r,r⟩/(3*source.d)+leadingPrice source t y r) := by
  by_cases hp : P.F∣numerator K P.F (w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let good := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (source.leading (polynomialEmbedding K))≠0)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (source.leading (polynomialEmbedding K))=0)
  let PG := P.restrict good (Finset.filter_subset _ _)
  have hmain := native_regular_packet_count PG hp source hk (fun gamma hg => (Finset.mem_filter.mp hg).2)
  have hdiv : good.card≤nativeNumerator source t y r ⟨t-y,y-r,r⟩/(3*source.d) := by
    apply (Nat.le_div_iff_mul_le (by dsimp [Source.d]; omega : 0<3*source.d)).mpr
    exact (Nat.mul_comm good.card (3*source.d)).trans_le hmain
  have hbad : bad.card≤leadingPrice source t y r := packet_z_leading_count P source hFT hgates
  have hpartition : P.seeds.card=good.card+bad.card := by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hdiv hbad).trans (le_max_right _ _)

#print axioms native_regular_packet_count
#print axioms native_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeCount6814
