import ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
import ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814

/-! Actual Z-leading-zero seeds are a proper-cut exception. The full
source's leading coefficient has sharper (37,169,3421) weights because
its S degree is at least eight. -/
namespace ProximityPrize.SubmissionLower.MovingSourceZLeadingSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN001 RCN051 RCN068 RCN074 RCN086 RCN095 RCN135 RCN136 RCN156 RCN234 RCN238 RCN243 RCN244 RCN264
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceDenominatorSeeds6814 MovingSourceReducedGamma6814
open SecondJetCoefficients SecondJetHelperWeights

variable {K I : Type} [Field K]

theorem z_leading_weights (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (hSZ : Profile SZ 53 177 3429 24 6 8) :
    wt residualSWeights (asS SZ.P).leadingCoeff≤37 ∧
    wt residualYSWeights (asS SZ.P).leadingCoeff≤169 ∧
    wt residualTotalWeights (asS SZ.P).leadingCoeff≤3421 := by
  have hshape := SZ.hshape
  rw [hSZ.1,hSZ.2.1,hSZ.2.2.1] at hshape
  have hn : 8≤(asS SZ.P).natDegree := by rw [←hSZ.2.2.2.2.2]; exact SZ.hn
  have hw := derivative_coefficient_weights SZ.P 53 177 3429 0 (asS SZ.P).natDegree hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  rw [Polynomial.leadingCoeff]
  omega

variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem z_leading_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (SZ : Source S.F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights S.F) :
    ¬S.G∣SZ.leading (polynomialEmbedding K) := by
  have hnot := SecondJetTotalAvoidance.leading_not_dvd SZ.P (source_nonzero S.F SZ) S.F 3429
    (fun e he => by have hh := (SZ.hshape e he).2.2; rw [hSZ.2.2.1] at hh; exact hh) hFT
  have hF : Irreducible S.F := Fact.out
  have hrel := surfaceMap_relPrime S.F (asS SZ.P).leadingCoeff hF.ne_zero
    (hF.isRelPrime_iff_not_dvd.mpr hnot.2)
  intro hd
  exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hd)

def badSeeds (S : Stage K I Gamma x p flag errorCap stageSupport) (SZ : Source S.F) : Finset K :=
  Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
    (SZ.leading (polynomialEmbedding K))=0)

def goodSeeds (S : Stage K I Gamma x p flag errorCap stageSupport) (SZ : Source S.F) : Finset K :=
  Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
    (SZ.leading (polynomialEmbedding K))≠0)

theorem good_bad_card (S : Stage K I Gamma x p flag errorCap stageSupport) (SZ : Source S.F) :
    Gamma.card=(goodSeeds S SZ).card+(badSeeds S SZ).card := by
  classical
  unfold goodSeeds badSeeds
  rw [Nat.add_comm]
  exact (Finset.card_filter_add_card_filter_not _).symm

private theorem leading_arithmetic (n : ℕ)
    (h : n*(181255-131071)≤
      (262144-131071)*(∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![172809,796806,4137] i))+
        (80889+1)*(181255-131071)*4137) : n≤23104862107476 := by
  have hsum : (∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![172809,796806,4137] i))=
      14942095*172809+3014633*796806+933487663*4137 := by decide +kernel
  rw [hsum] at h
  norm_num at h
  omega

theorem z_leading_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hp : p=2130706433) (he : errorCap=80889)
    (SZ : Source S.F) (hSZ : Profile SZ 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights S.F)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G)
    (hFY : S.F.degreeOf 1≤57) (hFR : S.F.degreeOf 2≤12) (hFZ : S.F.degreeOf 3≤3561)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card) :
    (badSeeds S SZ).card≤23104862107476 := by
  let T := SZ.leading (polynomialEmbedding K)
  let Delta := badSeeds S SZ
  have hsub : Delta⊆Gamma := Finset.filter_subset _ _
  have hproper := z_leading_proper S SZ hSZ hFT
  have hw := z_leading_weights S.F SZ hSZ
  have hTflag : PolynomialInFlag ⟨3252,132,37⟩ T :=
    surface_flag_of_caps (polynomialEmbedding K) _ 37 169 3421 (by decide) (by decide)
      hw.1 hw.2.1 hw.2.2
  have hGc : HasCaps S.G ⟨57,12,3561⟩ := caps_of_flag S.G _ hS
  have hTc : HasCaps T ⟨169,37,3421⟩ := caps_of_flag T _ hTflag
  have hgates := actual_characteristic_gates S.G T ⟨57,12,3561⟩ ⟨169,37,3421⟩ p hGc hTc
    (by rw [hp]; intro i; fin_cases i <;> decide)
    (by rw [hp]; decide) (by rw [hp]; decide) (by rw [hp]; decide)
  let budget : Fin 3 → ℕ := ![172809,796806,4137]
  have hmix (i : Fin 3) : coordinateMixedDegree (GenericField K) S.G T i≤budget i := by
    fin_cases i
    · simpa [coordinateMixedDegree_zero,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨169,37,3421⟩ hGc hTc 1 2
    · simpa [coordinateMixedDegree_one,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨169,37,3421⟩ hGc hTc 0 2
    · simpa [coordinateMixedDegree_two,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨169,37,3421⟩ hGc hTc 0 1
  have hb (i : Fin 3) :
      (∑ C : RegularComponent (GenericField K) S.G T (regularitySurface (polynomialEmbedding K) S.F),
        RCN007.actualCoordinateDegree (GenericField K) C.1 i)≤budget i :=
    (regularComponents_degree_budget (polynomialEmbedding K) S.F S.G T p S.irreducible_G hproper
      hgates.1 hgates.2 i).trans (hmix i)
  have hc := proper_cut_seed_bound_of_projection_sum (polynomialEmbedding K) S.F S.G T
    S.irreducible_G S.G_dvd_surface hproper S.selected Delta S.nodes x S.u0 S.u1 S.x_injective
    p RCN326.w 181255 errorCap (by decide) S.characteristic_bound (by decide)
    (by rw [hnodes]; decide) hgates.1 hgates.2
    (fun gamma hg => S.degree_le gamma (hsub hg))
    (fun gamma hg => S.solution gamma (hsub hg))
    (fun gamma hg => S.regular gamma (hsub hg))
    (fun gamma hg => S.on_component gamma (hsub hg))
    (fun _ hg => (Finset.mem_filter.mp hg).2)
    (fun gamma hg => hagreement gamma (hsub hg))
    (noLargeSelectedPencil_mono S.selected Gamma Delta RCN326.w errorCap hsub S.no_large_pencil)
    (capAt (agreementCaps 57 12 3561 RCN326.w)) budget
    (fun i _ => surface_agreement_caps (polynomialEmbedding K) S.F 57 12 3561 (by decide)
      hFY hFR hFZ RCN326.w (fun j => (j.factorial : K)⁻¹) (x i) (S.u0 i) (S.u1 i)) hb
  rw [hnodes,he] at hc
  exact leading_arithmetic _ hc


#print axioms z_leading_proper
#print axioms z_leading_seed_count
end
end ProximityPrize.SubmissionLower.MovingSourceZLeadingSeeds6814
