import ProximityPrize.SubmissionLower.MovingSourceWideProperSeeds6814

/-! The wider linear flow's exceptional strata: constant gamma, persistent
tails, and new-denominator zeros. All underlying geometric constructions
are imported from the already-proved argument. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWideExceptions6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators Classical
open RCN001 RCN002 RCN022 RCN042 RCN051 RCN068 RCN074 RCN086 RCN093 RCN095
open RCN135 RCN136 RCN159 RCN174 RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814 MovingSourceFrameZeroCount6814
open MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814 MovingSourceLinearFlow6814
open MovingSourceCarrierField6814 MovingSourceGenericField6814
open MovingSourceConstantSeeds6814 MovingSourcePersistentSeeds6814 MovingSourceDenominatorSeeds6814
open MovingSourceWideLinearFlow6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem wide_constant_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute S.F J)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G) :
    (∑ C : ConstantComponent S, (stageSeeds S C.1).card)≤
      flagMixed surfaceFlag wideFirstFlag unitYZFlag+flagMixed surfaceFlag wideFirstFlag unitAllFlag := by
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hH
  have hcard := constant_prime_family_card_le (fun a : ConstantComponent S => a.1.1)
    (fun a b h => Subtype.ext (Subtype.ext h))
    (fun a => regularComponent_ne_point (GenericField K) S.G _ _ a.1) (fun a => a.2)
    S.G (MovingSourceReducedCycle6814.reducedTailSurface (linearH J) (linearG J)) S.irreducible_G.ne_zero
    (fun hz => hproper (hz ▸ dvd_zero _)) (S.irreducible_G.isRelPrime_iff_not_dvd.mpr hproper)
    (fun a => regularComponent_G_mem (GenericField K) S.G _ _ a.1)
    (fun a => reducedTail_mem_old_component S (linearH J) (linearG J) (hroute.2.2.2.2 _).1 a.1)
    surfaceFlag wideFirstFlag hS (wide_first_flag S.F J hroute)
  calc
    _≤∑ _ : ConstantComponent S, 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact constant_parameter_seeds_le_one (polynomialEmbedding K) S.selected _ a.1.1 a.2
        (fun gamma hgamma => componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) a.1 gamma hgamma)
    _=Fintype.card (ConstantComponent S) := by simp
    _≤_ := hcard

theorem wide_constant_checked_budget :
    flagMixed ⟨3504,45,12⟩ wideFirstFlag unitYZFlag+
      flagMixed ⟨3504,45,12⟩ wideFirstFlag unitAllFlag=42352119285 := by decide +kernel


theorem wide_persistent_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute S.F J)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G)
    (hsmall : flagMixed surfaceFlag wideFirstFlag unitZFlag<p)
    (agreements bound seedCap slopeCap : ℕ)
    (hnodes : S.nodes.card=agreements+errorCap)
    (hagreement : ∀ gamma∈Gamma, agreements≤(S.agreementFiber gamma).card)
    (hwa : RCN326.w<agreements) (hshort : RCN326.w+1≤bound) (hchar : bound<p)
    (hbox : S.F∈globalCoefficientBox K bound RCN326.w seedCap slopeCap) :
    (∑ C : PersistentComponent S, (stageSeeds S C.1).card)≤
      (errorCap+1)*flagMixed surfaceFlag wideFirstFlag unitYZFlag := by
  let A := PersistentComponent S
  let component : A → FirstTailComponent S := Subtype.val
  let hz (a : A) := a.2.1
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hH
  have hT := wide_first_flag S.F J hroute
  have gate (a : A) := reduced_gamma_gate S (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hproper
    surfaceFlag wideFirstFlag hS hT hsmall a.1 (hz a)
  obtain ⟨D,hD⟩ := exists_reduced_cycle_family S hfirst (linearH J) (linearG J)
    (hroute.2.2.2.2 _).1 hH component Subtype.val_injective hz
    surfaceFlag wideFirstFlag hS hT hsmall
  let m (a : A) := localMultiplicity S (canonicalLocalDVRFamily S hfirst) a.1
  have hcount (a : A) : (stageSeeds S a.1).card≤(errorCap+1)*frameCost D hz .u a := by
    let base : SeparableLiteralCoordinate a.1.1 := ⟨2,hz a,(gate a).1,(gate a).2⟩
    have hpole := frame_unit_poles D hz gate .u a
    have hprofile := coefficientPoleProfile_of_tangent_firstTail S a.1 hfirst
      bound seedCap slopeCap (frameCost D hz .u a) (by decide : 1≤RCN326.w)
      hshort hchar hbox a.2.2 hpole
    have hpos : 1≤frameCost D hz .u a := by
      letI := (elementEmbedding (GenericField K) (CoordinateField (GenericField K) a.1.1)
        (RCN093.flagEvaluation (GenericField K) a.1.1 D.lam D.mu (D.mu*D.lam)
          (MvPolynomial.X (Axis.u.order 0))) (frame_trans D hz .u a)).toRingHom.toAlgebra
      letI := (frame_gate D hz gate .u a (frame_trans D hz .u a)).1
      exact Module.finrank_pos
    have hsub : stageSeeds S a.1⊆Gamma := componentSeeds_subset (GenericField K) S.G _ _ Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) a.1
    apply RCN145.prime_curve_card_le_of_coefficientPoleProfile
      (polynomialEmbedding K) a.1.1 S.F
      (firstTailComponent_surface_mem S a.1) (firstTailComponent_regularity_not_mem S a.1)
      base p RCN326.w agreements errorCap (frameCost D hz .u a)
      S.characteristic_bound hwa hpos hprofile
      S.selected (stageSeeds S a.1) S.nodes x S.u0 S.u1 S.x_injective hnodes
    · intro gamma hg; exact S.degree_le gamma (hsub hg)
    · intro gamma hg; exact S.solution gamma (hsub hg)
    · intro gamma hg; exact S.regular gamma (hsub hg)
    · intro gamma hg
      exact componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) a.1 gamma hg
    · intro gamma hg
      exact hagreement gamma (hsub hg)
    · exact noLargeSelectedPencil_mono S.selected Gamma (stageSeeds S a.1) RCN326.w errorCap
        hsub S.no_large_pencil
  have hsum : (∑ a : A, frameCost D hz .u a)≤flagMixed surfaceFlag wideFirstFlag unitYZFlag := by
    calc
      _≤∑ a : A, m a*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => by
        have hh := Nat.mul_le_mul_right (frameCost D hz .u a) (one_le_localMultiplicity S hfirst a.1)
        simpa only [one_mul] using hh)
      _≤_ := hD .u
  calc
    _≤∑ a : A, (errorCap+1)*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => hcount a)
    _=(errorCap+1)*(∑ a : A, frameCost D hz .u a) := (Finset.mul_sum _ _ _).symm
    _≤_ := Nat.mul_le_mul_left _ hsum

theorem wide_persistent_checked_budget :
    (80889+1)*flagMixed ⟨3504,45,12⟩ wideFirstFlag unitYZFlag=723646569172920 := by decide +kernel


private theorem wide_denominator_arithmetic (n : ℕ)
    (h : n*(181255-131071)≤
      (262144-131071)*(∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![32448,129201,828] i))+
        (80889+1)*(181255-131071)*828) : n≤4302466850810 := by
  have hsum : (∑ i : Fin 3, capAt (agreementCaps 57 12 3561 131071) i*(![32448,129201,828] i))=
      14942095*32448+3014633*129201+933487663*828 := by decide +kernel
  rw [hsum] at h
  norm_num at h
  omega

theorem wide_checked_denominator_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hp : p=2130706433) (he : errorCap=80889)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : WideLinearRoute S.F J)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G)
    (hFY : S.F.degreeOf 1≤57) (hFR : S.F.degreeOf 2≤12) (hFZ : S.F.degreeOf 3≤3561)
    (hnodes : S.nodes.card=262144)
    (hagreement : ∀ gamma∈Gamma, 181255≤(S.agreementFiber gamma).card) :
    (denominatorSeeds S J).card≤4302466850810 := by
  let T := surfaceMap (polynomialEmbedding K) (linearH J)
  let Delta := denominatorSeeds S J
  have hsub : Delta⊆Gamma := Finset.filter_subset _ _
  have hproper := wide_denominator_proper S J hroute
  have hTflag : PolynomialInFlag ⟨299,23,8⟩ T :=
    surface_flag_of_caps (polynomialEmbedding K) _ 8 31 330 (by decide) (by decide)
      hroute.2.2.1.1 hroute.2.2.1.2.1 hroute.2.2.1.2.2
  have hGc : HasCaps S.G ⟨57,12,3561⟩ := caps_of_flag S.G _ hS
  have hTc : HasCaps T ⟨31,8,330⟩ := caps_of_flag T _ hTflag
  have hgates := actual_characteristic_gates S.G T ⟨57,12,3561⟩ ⟨31,8,330⟩ p hGc hTc
    (by rw [hp]; intro i; fin_cases i <;> decide)
    (by rw [hp]; decide) (by rw [hp]; decide) (by rw [hp]; decide)
  let budget : Fin 3 → ℕ := ![32448,129201,828]
  have hmix (i : Fin 3) : coordinateMixedDegree (GenericField K) S.G T i≤budget i := by
    fin_cases i
    · simpa [coordinateMixedDegree_zero,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨31,8,330⟩ hGc hTc 1 2
    · simpa [coordinateMixedDegree_one,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨31,8,330⟩ hGc hTc 0 2
    · simpa [coordinateMixedDegree_two,budget,capAt,Nat.mul_comm,Nat.add_comm] using
        actual_pair_degree_le S.G T ⟨57,12,3561⟩ ⟨31,8,330⟩ hGc hTc 0 1
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
  exact wide_denominator_arithmetic _ hc


#print axioms wide_constant_seed_sum_le
#print axioms wide_persistent_seed_sum_le
#print axioms wide_checked_denominator_seed_count
end
end ProximityPrize.SubmissionLower.MovingSourceWideExceptions6814
