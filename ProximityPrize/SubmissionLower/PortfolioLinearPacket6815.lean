import ProximityPrize.SubmissionLower.PortfolioLinearExceptions6815
import ProximityPrize.SubmissionLower.MovingSourceBandPairCount6815
namespace ProximityPrize.SubmissionLower.PortfolioLinearPacket6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334
open MovingSourceBandGeometry6815 MovingSourceBandIdentity6815 MovingSourceBandLeading6815
open MovingSourceLinearFlow6814 MovingSourceCarrierField6814 MovingSourceLinearSeedAssembly6814
open MovingSourcePairEnvelope6814 MovingSourceDenominatorSeeds6814
open PortfolioLinearRoute6815 PortfolioLinearProper6815 PortfolioLinearExceptions6815
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K} {t y r : ℕ}

def linearPrice (first delay : FlagDegree) (t y r b u l : ℕ) : ℕ :=
  r*AsymmetricHelper.leftRegularCountCap (pair t y r b u l)+
    flagMixed ⟨t-y,y-r,r⟩ first delay+
    80901*flagMixed ⟨t-y,y-r,r⟩ first unitYZFlag+
    flagMixed ⟨t-y,y-r,r⟩ first unitAllFlag

theorem packet_count
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (first delay : FlagDegree)
    (hroute : Route P.F J first delay) (b u l : ℕ)
    (hH : wt residualSWeights (linearH J)≤b ∧ wt residualYSWeights (linearH J)≤u ∧
      wt residualTotalWeights (linearH J)≤l)
    (hgates : Gates t y r b u l)
    (hsmall : flagMixed ⟨t-y,y-r,r⟩ first unitZFlag<2130706433) :
    P.seeds.card≤max (identityPrice t y r) (linearPrice first delay t y r b u l) := by
  by_cases hp : P.F∣numerator K P.F (RCN326.w+1)
  · exact (packet_identity_count P hp).trans (le_max_left _ _)
  let cap := AsymmetricHelper.leftRegularCountCap (pair t y r b u l)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval
    (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)
  let PB := P.restrict bad (Finset.filter_subset _ _)
  have hrel : IsRelPrime P.F (linearH J) := P.irreducible.isRelPrime_iff_not_dvd.mpr
    (fun hd => hroute.denominator ((carrierMap_zero_iff P.F _).mpr hd))
  have hbad : bad.card≤cap := by
    apply proper_cut_count PB (linearH J) b u l hrel hH hgates
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    change RCN319.specialization K (P.selected gamma) gamma (linearH J)=0
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hry : r≤y := by have := P.ylow; omega
  have hyt := P.yt
  have hsum (W : FlagDegree) : (∑ g : GeometricFactor K P.F,
      flagMixed (geometricCumulativeFlag K g) first W)≤flagMixed ⟨t-y,y-r,r⟩ first W := by
    apply sum_flagMixed_le_of_cumulative
    · exact hb.1.trans P.r_weight
    · simpa only [Nat.sub_add_cancel hry] using hb.2.1.trans P.y_weight
    · have ht := hb.2.2.trans P.total_weight
      exact ht.trans_eq (by change t=(t-y)+(y-r)+r; omega)
  have hcard : Fintype.card (GeometricFactor K P.F)≤r := by
    have hone (g : GeometricFactor K P.F) : 1≤(geometricCumulativeFlag K g).all := by
      have hd := (P.stage g).y_dependent
      have hle : (P.stage g).G.degreeOf 1≤(geometricCumulativeFlag K g).all :=
        MvPolynomial.degreeOf_le_iff.mpr (fun e he => ((P.stage g).flag_support e he).1)
      omega
    have hh := (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hone g)).trans (hb.1.trans P.r_weight)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hh
  let cost (fl : FlagDegree) := flagMixed fl first delay+
    (flagMixed fl first unitYZFlag+flagMixed fl first unitAllFlag)+80900*flagMixed fl first unitYZFlag
  have hsingle (g : GeometricFactor K P.F) :
      (geometricSeeds K P.F P.selected P.seeds g).card≤cap+cost (geometricCumulativeFlag K g) := by
    let S := P.stage g
    letI : Fact (Irreducible S.F) := ⟨P.irreducible⟩
    have hfirst := P.stage_proper hp g
    have hsmall' : flagMixed (geometricCumulativeFlag K g) first unitZFlag<2130706433 :=
      (mixed_mono_left _ ⟨t-y,y-r,r⟩ first unitZFlag (by
        have h := P.stage_flag g
        change _≤r ∧ _≤y-r+r ∧ _≤t-y+(y-r)+r
        omega)).trans_lt hsmall
    have hproper := denominator_proper S J hroute
    have hden : (denominatorSeeds S J).card≤cap := by
      apply (Finset.card_le_card (show denominatorSeeds S J⊆bad from ?_)).trans hbad
      intro gamma hg
      exact Finset.mem_filter.mpr
        ⟨geometricSeeds_subset K P.F P.selected P.seeds g (Finset.mem_filter.mp hg).1,
          (Finset.mem_filter.mp hg).2⟩
    have hd := wide_proper_seeds_sum_le S hfirst J hroute (geometricCumulativeFlag K g) S.flag_support hsmall'
    have hz := wide_constant_seed_sum_le S hfirst J hroute hproper (geometricCumulativeFlag K g) S.flag_support
    have ht := wide_persistent_seed_sum_le S hfirst J hroute hproper (geometricCumulativeFlag K g)
      S.flag_support hsmall' 181245 P.D t r P.nodeCount (P.stage_agreement g) (by decide) P.Dlow P.Dchar P.box
    have hh := (linear_seed_cover S hfirst J).trans (Nat.add_le_add hden (Nat.add_le_add hd (Nat.add_le_add hz ht)))
    exact hh.trans_eq (by dsimp only [cost]; ring)
  have hcost : (∑ g : GeometricFactor K P.F, cost (geometricCumulativeFlag K g))≤cost ⟨t-y,y-r,r⟩ := by
    unfold cost
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add (hsum delay) (Nat.add_le_add (hsum unitYZFlag) (hsum unitAllFlag)))
      (Nat.mul_le_mul_left 80900 (hsum unitYZFlag))
  have htotal : P.seeds.card≤r*cap+cost ⟨t-y,y-r,r⟩ := by
    have hh := P.seeds_cover.trans (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hsingle g))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
    exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hcard) hcost)
  apply (htotal.trans_eq ?_).trans (le_max_right _ _)
  dsimp [linearPrice,cap,cost]
  ring

end
end ProximityPrize.SubmissionLower.PortfolioLinearPacket6815
