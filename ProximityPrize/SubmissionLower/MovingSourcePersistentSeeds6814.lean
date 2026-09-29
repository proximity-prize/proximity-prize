import ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814

/-! The old persistent/tangent engine works with the new frame's pole
bound. It does not require a second global budget family to be built. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN135 RCN136 RCN159 RCN174
open RCN238 RCN243 RCN244 RCN264 RCN312 RCN341
open MovingSourceProjectionFamily6814 MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev PersistentComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
      ∀ delay, globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∈C.1}

theorem persistent_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G)
    (hsmall : flagMixed surfaceFlag reducedFirstFlag unitZFlag<p)
    (agreements bound seedCap slopeCap : ℕ)
    (hnodes : S.nodes.card=agreements+errorCap)
    (hagreement : ∀ gamma∈Gamma, agreements≤(S.agreementFiber gamma).card)
    (hwa : RCN326.w<agreements) (hshort : RCN326.w+1≤bound) (hchar : bound<p)
    (hbox : S.F∈globalCoefficientBox K bound RCN326.w seedCap slopeCap) :
    (∑ C : PersistentComponent S, (stageSeeds S C.1).card)≤
      (errorCap+1)*flagMixed surfaceFlag reducedFirstFlag unitYZFlag := by
  let A := PersistentComponent S
  let component : A → FirstTailComponent S := Subtype.val
  let hz (a : A) := a.2.1
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hH
  have hT := reducedFirstFlag_of_route S.F J hroute
  have gate (a : A) := reduced_gamma_gate S (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hproper
    surfaceFlag reducedFirstFlag hS hT hsmall a.1 (hz a)
  obtain ⟨D,hD⟩ := exists_reduced_cycle_family S hfirst (linearH J) (linearG J)
    (hroute.2.2.2.2 _).1 hH component Subtype.val_injective hz
    surfaceFlag reducedFirstFlag hS hT hsmall
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
  have hsum : (∑ a : A, frameCost D hz .u a)≤flagMixed surfaceFlag reducedFirstFlag unitYZFlag := by
    calc
      _≤∑ a : A, m a*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => by
        have hh := Nat.mul_le_mul_right (frameCost D hz .u a) (one_le_localMultiplicity S hfirst a.1)
        simpa only [one_mul] using hh)
      _≤_ := hD .u
  calc
    _≤∑ a : A, (errorCap+1)*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => hcount a)
    _=(errorCap+1)*(∑ a : A, frameCost D hz .u a) := (Finset.mul_sum _ _ _).symm
    _≤_ := Nat.mul_le_mul_left _ hsum

theorem persistent_checked_budget :
    (80889+1)*flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitYZFlag=497878763753400 := by decide +kernel

#print axioms persistent_seed_sum_le
end
end ProximityPrize.SubmissionLower.MovingSourcePersistentSeeds6814
