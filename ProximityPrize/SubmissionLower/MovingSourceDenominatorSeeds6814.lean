import ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
import ProximityPrize.SubmissionLower.MovingSourceGenericField6814

/-! The new denominator is genuinely proper on EVERY geometric surface
factor, by flat coefficient extension. Its exceptional seeds are counted
by the existing small proper-cut incidence theorem. -/
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN051 RCN068 RCN074 RCN086 RCN095 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceLinearFlow6814 MovingSourceCarrierField6814 MovingSourceReducedRoutes6814
open MovingSourceFlatBaseChange6814 MovingSourceGenericField6814 MovingSourceReducedGamma6814

variable {K I : Type} [Field K]

theorem surfaceMap_relPrime (F H : MvPolynomial (Fin 4) K) (hF : F≠0) (hrel : IsRelPrime F H) :
    IsRelPrime (surfaceMap (polynomialEmbedding K) F) (surfaceMap (polynomialEmbedding K) H) := by
  have hFc : collectX K F≠0 := fun hz => hF ((collectX K).injective (hz.trans (map_zero _).symm))
  exact generic_coefficient_map_relPrime K (collectX K F) (collectX K H) hFc
    (isRelPrime_equiv (collectX K).toRingEquiv F H hrel)

variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem linear_denominator_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J) :
    ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
  have hF : Irreducible S.F := Fact.out
  have hnot : ¬S.F∣linearH J := fun hd => hroute.2.1 ((carrierMap_zero_iff S.F _).mpr hd)
  have hrel := surfaceMap_relPrime S.F (linearH J) hF.ne_zero (hF.isRelPrime_iff_not_dvd.mpr hnot)
  intro hd
  exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hd)

def denominatorSeeds (S : Stage K I Gamma x p flag errorCap stageSupport)
    (J : WholeSpaceCube6814.Poly (K:=K)) : Finset K :=
  Gamma.filter (fun gamma => MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
    (surfaceMap (polynomialEmbedding K) (linearH J))=0)

theorem caps_of_flag {Ω : Type} [Field Ω] (N : MvPolynomial (Fin 3) Ω)
    (q : FlagDegree) (hq : PolynomialInFlag q N) :
    HasCaps N ⟨q.yz+q.all,q.all,q.zOnly+q.yz+q.all⟩ := by
  intro i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hh := hq d hd
  dsimp only [InFlag] at hh
  fin_cases i
  · change d 0≤q.yz+q.all
    omega
  · exact hh.1
  · change d 2≤q.zOnly+q.yz+q.all
    omega

private theorem denominator_arithmetic (n : ℕ)
    (h : n*(181255-131071)≤
      (262144-131071)*(∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![21765,104274,573] i))+
        (80889+1)*(181255-131071)*573) : n≤3067534234414 := by
  have hsum : (∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![21765,104274,573] i))=
      14942095*21765+3014633*104274+933487663*573 := by decide +kernel
  rw [hsum] at h
  norm_num at h
  omega

theorem checked_denominator_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hp : p=2130706433) (he : errorCap=80889)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G)
    (hFY : S.F.degreeOf 1≤57) (hFR : S.F.degreeOf 2≤12) (hFZ : S.F.degreeOf 3≤3561)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card) :
    (denominatorSeeds S J).card≤3067534234414 := by
  let T := surfaceMap (polynomialEmbedding K) (linearH J)
  let Delta := denominatorSeeds S J
  have hsub : Delta⊆Gamma := Finset.filter_subset _ _
  have hproper := linear_denominator_proper S J hroute
  have hTflag : PolynomialInFlag ⟨306,19,5⟩ T :=
    surface_flag_of_caps (polynomialEmbedding K) _ 5 24 330 (by decide) (by decide)
      hroute.2.2.1.1 hroute.2.2.1.2.1 hroute.2.2.1.2.2
  have hGc : HasCaps S.G ⟨57,12,3561⟩ := caps_of_flag S.G _ hS
  have hTc : HasCaps T ⟨24,5,330⟩ := caps_of_flag T _ hTflag
  have hgates := actual_characteristic_gates S.G T ⟨57,12,3561⟩ ⟨24,5,330⟩ p hGc hTc
    (by rw [hp]; intro i; fin_cases i <;> decide)
    (by rw [hp]; decide) (by rw [hp]; decide) (by rw [hp]; decide)
  let budget : Fin 3 → ℕ := ![21765,104274,573]
  have hmix (i : Fin 3) : coordinateMixedDegree (GenericField K) S.G T i≤budget i := by
    fin_cases i
    · simpa [coordinateMixedDegree_zero,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨24,5,330⟩ hGc hTc 1 2
    · simpa [coordinateMixedDegree_one,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨24,5,330⟩ hGc hTc 0 2
    · simpa [coordinateMixedDegree_two,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨24,5,330⟩ hGc hTc 0 1
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
  exact denominator_arithmetic _ hc

#print axioms linear_denominator_proper
#print axioms checked_denominator_seed_count
end
end ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
