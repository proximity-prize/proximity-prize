import ProximityPrize.SubmissionLower.MovingSourceBandHelperCount6814
import ProximityPrize.SubmissionLower.MovingSourceWideSeedAssembly6814

/-! The linear-owner count on one envelope dominating all five bands.
Its denominator zeros are counted on the original packet. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandWideLinear6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334
open LocatorHybridCells LocatorHybridCellsC1 MovingSourceBandGeometry6814 MovingSourceBandIdentity6814
open MovingSourceWideLinearFlow6814 MovingSourceWideProperSeeds6814 MovingSourceWideExceptions6814
open MovingSourceLinearSeedAssembly6814 MovingSourcePairEnvelope6814
open MovingSourceBandLeading6814 MovingSourceDenominatorSeeds6814 MovingSourceLinearFlow6814 MovingSourceCarrierField6814
local notation "w" => RCN326.w
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {x : I → K}

def denominatorCap : ℕ := AsymmetricHelper.leftRegularCountCap (pair 3578 57 13 8 31 330)

theorem packet_wide_linear_count
    (P : Packet x 3578 57 13) [Fact (Irreducible P.F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute P.F J) :
    P.seeds.card<270000000000000000 := by
  by_cases hp : P.F∣numerator K P.F (w+1)
  · exact (packet_identity_count P hp).trans_lt (by decide)
  let bad := P.seeds.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) P.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)
  let PB := P.restrict bad (Finset.filter_subset _ _)
  have hrel : IsRelPrime P.F (linearH J) := P.irreducible.isRelPrime_iff_not_dvd.mpr
    (fun hd => hroute.2.1 ((carrierMap_zero_iff P.F _).mpr hd))
  have hbad : bad.card≤denominatorCap := by
    apply proper_cut_count PB (linearH J) 8 31 330 hrel hroute.2.2.1
      (by unfold Gates; decide +kernel)
    intro gamma hg
    have hh := (Finset.mem_filter.mp hg).2
    rw [RCN170.canonical_selectedPoint_surface_evaluation] at hh
    change RCN319.specialization K (P.selected gamma) gamma (linearH J)=0
    exact polynomialEmbedding_injective K (by simpa only [map_zero] using hh)
  have hb := geometricCumulativeFlag_budgets P.F P.irreducible.ne_zero
  have hc := originalCumulativeFlag_cumulative P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hsum (W : FlagDegree) : (∑ g : GeometricFactor K P.F, flagMixed (geometricCumulativeFlag K g) wideFirstFlag W)≤
      flagMixed ⟨3521,44,13⟩ wideFirstFlag W :=
    sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K) ⟨3521,44,13⟩ wideFirstFlag W
      (hb.1.trans P.support.s_weight) (hb.2.1.trans P.support.ys_weight) (hb.2.2.trans P.support.total_weight)
  have hcard : Fintype.card (GeometricFactor K P.F)≤13 := by
    have hone (g : GeometricFactor K P.F) : 1≤(geometricCumulativeFlag K g).all := by
      have hd := (P.stage g).y_dependent
      have hle : (P.stage g).G.degreeOf 1≤(geometricCumulativeFlag K g).all :=
        MvPolynomial.degreeOf_le_iff.mpr (fun e he => ((P.stage g).flag_support e he).1)
      omega
    have hh := (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hone g)).trans (hb.1.trans P.support.s_weight)
    have hs : (cellSupport 3578 57 13).s=13 := rfl
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,hs] using hh
  let cost (fl : FlagDegree) := flagMixed fl wideFirstFlag wideDelayFlag+
    (flagMixed fl wideFirstFlag unitYZFlag+flagMixed fl wideFirstFlag unitAllFlag)+
    80890*flagMixed fl wideFirstFlag unitYZFlag
  have hsingle (g : GeometricFactor K P.F) :
      (geometricSeeds K P.F P.selected P.seeds g).card≤denominatorCap+cost (geometricCumulativeFlag K g) := by
    let S := P.stage g
    letI : Fact (Irreducible S.F) := ⟨P.irreducible⟩
    have hfirst := P.stage_proper hp g
    have hsmall : flagMixed (geometricCumulativeFlag K g) wideFirstFlag unitZFlag<2130706433 :=
      (mixed_mono_left _ ⟨3521,44,13⟩ wideFirstFlag unitZFlag (P.stage_flag g)).trans_lt (by decide : flagMixed ⟨3521,44,13⟩ wideFirstFlag unitZFlag<2130706433)
    have hH := wide_denominator_proper S J hroute
    have hS : PolynomialInFlag ⟨3521,44,13⟩ S.G := by
      intro e he
      have hh := S.flag_support e he
      have hg := P.stage_flag g
      dsimp only [InFlag] at hh ⊢
      omega
    have hden : (denominatorSeeds S J).card≤denominatorCap := by
      apply (Finset.card_le_card (show denominatorSeeds S J⊆bad from ?_)).trans hbad
      intro gamma hg
      exact Finset.mem_filter.mpr
        ⟨geometricSeeds_subset K P.F P.selected P.seeds g (Finset.mem_filter.mp hg).1,
          (Finset.mem_filter.mp hg).2⟩
    have hproper := wide_proper_seeds_sum_le S hfirst J hroute (geometricCumulativeFlag K g) S.flag_support hsmall
    have hconstant := wide_constant_seed_sum_le S hfirst J hroute hH (geometricCumulativeFlag K g) S.flag_support
    have htangent := wide_persistent_seed_sum_le S hfirst J hroute hH (geometricCumulativeFlag K g)
      S.flag_support hsmall 181255 P.D 3578 13 P.nodeCount (P.stage_agreement g) (by decide) P.Dlow P.Dchar P.box
    have hh := (linear_seed_cover S hfirst J).trans (Nat.add_le_add hden
      (Nat.add_le_add hproper (Nat.add_le_add hconstant htangent)))
    exact hh.trans_eq (by dsimp only [cost]; ring)
  have hcost : (∑ g : GeometricFactor K P.F, cost (geometricCumulativeFlag K g))≤
      cost ⟨3521,44,13⟩ := by
    unfold cost
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add (hsum wideDelayFlag)
      (Nat.add_le_add (hsum unitYZFlag) (hsum unitAllFlag))) (Nat.mul_le_mul_left 80890 (hsum unitYZFlag))
  have htotal : P.seeds.card≤13*denominatorCap+cost ⟨3521,44,13⟩ := by
    have hh := P.seeds_cover.trans (Finset.sum_le_sum (fun g (_ : g∈Finset.univ) => hsingle g))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
    exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hcard) hcost)
  apply htotal.trans_lt
  change 13*denominatorCap+ (flagMixed ⟨3521,44,13⟩ wideFirstFlag wideDelayFlag+
    (flagMixed ⟨3521,44,13⟩ wideFirstFlag unitYZFlag+flagMixed ⟨3521,44,13⟩ wideFirstFlag unitAllFlag)+
    80890*flagMixed ⟨3521,44,13⟩ wideFirstFlag unitYZFlag)<270000000000000000
  decide +kernel

theorem packet_wide_linear_count_all {t y r : ℕ}
    (P : Packet x t y r) [Fact (Irreducible P.F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute P.F J) :
    P.seeds.card<270000000000000000 := by
  let PP := P.widen 3578 57 13 P.thigh P.yhigh P.rhigh
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  letI : Fact (Irreducible PP.F) := ⟨PP.irreducible⟩
  exact packet_wide_linear_count PP J hroute

#print axioms packet_wide_linear_count
#print axioms packet_wide_linear_count_all
end
end ProximityPrize.SubmissionLower.MovingSourceBandWideLinear6814
