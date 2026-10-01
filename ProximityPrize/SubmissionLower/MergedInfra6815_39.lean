import ProximityPrize.SubmissionLower.MergedInfra6815_35
import ProximityPrize.SubmissionLower.MergedInfra6815_32
import ProximityPrize.SubmissionLower.MergedInfra6815_31
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814
open MovingSourceMixedOwnerRouting6814 MovingSourceNativeFactor6814
open WholeSpacePowerCover6814
open SecondJetCoefficients SecondJetCarrierDichotomy
open RCN234 RCN156

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]

def multiplicity (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : ℕ :=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)

end
end ProximityPrize.SubmissionLower.WholeSpaceUniqueOwnerAlternative6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.PortfolioLinearRoute6815
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 900000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234 RCN244
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceDenominatorChange6814 MovingSourceReducedTailWeights6814
open MovingSourceReducedGamma6814 MovingSourceReducedCycle6814 MovingSourceCarrierField6814

variable {K : Type} [Field K]

structure Route (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (firstFlag delayFlag : FlagDegree) : Prop where
  denominator : carrierMap F (linearH J)≠0
  cross : ∀ n, F∣(linearH J)^(2*n)*RCN313.numerator K F n-
    (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n
  first : PolynomialInFlag firstFlag (reducedTailSurface (linearH J) (linearG J))
  later : ∀ mu delay : ℕ, 1≤mu → delay≤mu → PolynomialInFlag (mu • delayFlag)
    (surfaceMap (polynomialEmbedding K)
      (numerators (linearH J) (linearG J) (RCN326.w+1+delay)))

def firstFlag (r y t : ℕ) : FlagDegree :=
  ⟨(t-y)*131072,1+(y-r)*131072,r*131072⟩
def delayFlag (r y t : ℕ) : FlagDegree :=
  ⟨(t-y)*131073,1+(y-r)*131073,r*131073⟩

theorem route_of_weights [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : Poly (K:=K)) (hJ : J≠0) (hS : J.degreeOf 1=1)
    (hpos : 0<F.degreeOf 2) (hchar : F.degreeOf 2<2130706433)
    (cap : ℕ) (hT : ∀ e∈J.support, e 1+e 2+e 3+e 4≤cap)
    (hFT : cap<wt residualTotalWeights F)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).eval
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=0)
    (r y t : ℕ) (hry : r≤y) (hyt : y≤t)
    (hw : ∀ n, wt residualSWeights (numerators (linearH J) (linearG J) n)≤r*n ∧
      wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+y*n ∧
      wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+t*n) :
    Route F J (firstFlag r y t) (delayFlag r y t) := by
  refine ⟨linearH_nonzero_on_carrier J hJ hS F cap hT hFT,
    linear_denominator_change J hJ hS F hpos hchar cap hT hFT hroot,?_,?_⟩
  · have hh := hw 131072
    have he := surface_flag_of_caps (polynomialEmbedding K) _ (r*131072) (1+y*131072) (1+t*131072)
      (by omega) (by omega) hh.1 hh.2.1 hh.2.2
    convert he using 1 <;> simp only [firstFlag,RCN326.w,reducedTailSurface]
    · congr 1 <;> omega
  · intro mu d hm hd
    have hh := hw (RCN326.w+1+d)
    have hr : wt residualSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(r*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left r hd,Nat.mul_le_mul_left (r*131072) hm]
    have hy : wt residualYSWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+y*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left y hd,Nat.mul_le_mul_left (y*131072) hm]
    have ht : wt residualTotalWeights (numerators (linearH J) (linearG J) (RCN326.w+1+d))≤mu*(1+t*131073) := by
      dsimp [RCN326.w] at hh ⊢
      nlinarith [Nat.mul_le_mul_left t hd,Nat.mul_le_mul_left (t*131072) hm]
    have he := surface_flag_of_caps (polynomialEmbedding K) _ (mu*(r*131073))
      (mu*(1+y*131073)) (mu*(1+t*131073)) (by nlinarith) (by nlinarith) hr hy ht
    have eqflag : (⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩ : FlagDegree)=mu • delayFlag r y t := by
      have hz : (1+t*131073)-(1+y*131073)=(t-y)*131073 := by
        rw [Nat.sub_mul t y 131073]
        omega
      have hyz : (1+y*131073)-r*131073=1+(y-r)*131073 := by
        rw [Nat.sub_mul y r 131073]
        exact Nat.add_sub_assoc (Nat.mul_le_mul_right 131073 hry) 1
      change (⟨mu*(1+t*131073)-mu*(1+y*131073),
        mu*(1+y*131073)-mu*(r*131073),mu*(r*131073)⟩ : FlagDegree)=
        ⟨mu*((t-y)*131073),mu*(1+(y-r)*131073),mu*(r*131073)⟩
      rw [←Nat.mul_sub mu (1+t*131073) (1+y*131073),
        ←Nat.mul_sub mu (1+y*131073) (r*131073),hz,hyz]
    rw [eqflag] at he
    exact he

variable {I : Type} {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ} {stageSupport : RCN275.ResidualSupportParameters}
variable {first delay : FlagDegree}

theorem denominator_proper
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (J : Poly (K:=K)) (hroute : Route S.F J first delay) :
    ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
  have hF : Irreducible S.F := Fact.out
  have hn : ¬S.F∣linearH J := fun hd => hroute.denominator ((carrierMap_zero_iff S.F _).mpr hd)
  have hrel := MovingSourceDenominatorSeeds6814.surfaceMap_relPrime S.F (linearH J) hF.ne_zero
    (hF.isRelPrime_iff_not_dvd.mpr hn)
  intro hd
  exact S.irreducible_G.not_isUnit (hrel S.G_dvd_surface hd)

end
end ProximityPrize.SubmissionLower.PortfolioLinearRoute6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.PortfolioLinearProper6815
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN121 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814 MovingSourceProjectionFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceReducedSeedTails6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open PortfolioLinearRoute6815 MovingSourceProperSeedCount6814

private theorem sum_weighted_three {A : Type} [Fintype A]
    (m z u v : A → ℕ) (a b c : ℕ) :
    (∑ i, m i*(a*z i+b*u i+c*v i))=
      a*(∑ i, m i*z i)+b*(∑ i, m i*u i)+c*(∑ i, m i*v i) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

variable {firstFlag delayFlag : FlagDegree}

theorem wide_proper_component_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : Route S.F J firstFlag delayFlag)
    {A : Type} [Fintype A] (component : A → FirstTailComponent S)
    (hz : ∀ a, Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)) ∧
      (letI := (elementEmbedding (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)))
    (D : GammaFrame (fun a => (component a).1) S.G) (a : A)
    (hH : surfaceMap (polynomialEmbedding K) (linearH J)∉(component a).1)
    (delay : ℕ) (hdelay : delay≤localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a))
    (hproper : globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∉(component a).1) :
    (stageSeeds S (component a)).card ≤
      localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)*
        frameFlagCost D hz a delayFlag := by
  classical
  let m := localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)
  let N := surfaceMap (polynomialEmbedding K)
    (numerators (linearH J) (linearG J) (RCN326.w+1+delay))
  let seeds := stageSeeds S (component a)
  let point := selectedPoint (polynomialEmbedding K) S.selected
  let points := seeds.image point
  have hN := hroute.later m delay
    (one_le_localMultiplicity S hfirst (component a)) hdelay
  have hNproper := reduced_tail_proper_on_component S (component a) (linearH J) (linearG J)
    (RCN326.w+1+delay) (hroute.cross _) hH hproper
  have hpoints : ∀ v∈points, (component a).1≤RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G _ _ Gamma point (component a) gamma hgamma
  have hzero : ∀ v∈points, MvPolynomial.aeval v N=0 := by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
    have hGamma := componentSeeds_subset (GenericField K) S.G _ _ Gamma point (component a) hgamma
    exact reduced_selected_tail_zero S (linearH J) (linearG J) (RCN326.w+1+delay)
      (by omega) (hroute.cross _) gamma hGamma
  have hc := (frame_prime_budget D hz hgate a).zero_le (m • delayFlag) N hN hNproper
    points hpoints hzero
  have hcard : points.card=seeds.card := Finset.card_image_of_injective _
    (selectedPoint_injective (polynomialEmbedding K) S.selected)
  have hcost : frameFlagCost D hz a (m • delayFlag)=m*frameFlagCost D hz a delayFlag := by
    simp only [frameFlagCost,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
  rw [hcard,hcost] at hc
  exact hc

theorem wide_proper_seeds_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : Route S.F J firstFlag delayFlag)
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G)
    (hsmall : flagMixed surfaceFlag firstFlag unitZFlag<p) :
    (∑ C : ProperLinearComponent S hfirst (linearH J), (stageSeeds S C.1).card) ≤
      flagMixed surfaceFlag firstFlag delayFlag := by
  classical
  let A := ProperLinearComponent S hfirst (linearH J)
  let component : A → FirstTailComponent S := Subtype.val
  let hz (a : A) := a.2.1
  by_cases hA : Nonempty A
  · let a0 : A := Classical.choice hA
    have hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
      intro hd
      exact a0.2.2.1 (a0.1.1.mem_of_dvd hd (regularComponent_G_mem (GenericField K) S.G _ _ a0.1))
    have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.cross _) hH
    have hT := hroute.first
    have gate (a : A) := reduced_gamma_gate S (linearH J) (linearG J) (hroute.cross _) hproper
      surfaceFlag firstFlag hS hT hsmall a.1 (hz a)
    obtain ⟨D,hD⟩ := exists_reduced_cycle_family S hfirst (linearH J) (linearG J)
      (hroute.cross _) hH component Subtype.val_injective hz
      surfaceFlag firstFlag hS hT hsmall
    let m (a : A) := localMultiplicity S (canonicalLocalDVRFamily S hfirst) a.1
    have hcount (a : A) : (stageSeeds S a.1).card≤m a*frameFlagCost D hz a delayFlag := by
      obtain ⟨delay,-,hd,hproper⟩ := a.2.2.2
      exact wide_proper_component_seed_count S hfirst J hroute component hz gate D a a.2.2.1 delay hd hproper
    calc
      _≤∑ a : A, m a*frameFlagCost D hz a delayFlag :=
        Finset.sum_le_sum (fun a _ => hcount a)
      _=delayFlag.zOnly*(∑ a : A, m a*frameCost D hz .z a)+
          delayFlag.yz*(∑ a : A, m a*frameCost D hz .u a)+
          delayFlag.all*(∑ a : A, m a*frameCost D hz .v a) := by
        exact sum_weighted_three m (frameCost D hz .z) (frameCost D hz .u) (frameCost D hz .v)
          delayFlag.zOnly delayFlag.yz delayFlag.all
      _≤delayFlag.zOnly*flagMixed surfaceFlag firstFlag unitZFlag+
          delayFlag.yz*flagMixed surfaceFlag firstFlag unitYZFlag+
          delayFlag.all*flagMixed surfaceFlag firstFlag unitAllFlag :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (hD .z)) (Nat.mul_le_mul_left _ (hD .u)))
          (Nat.mul_le_mul_left _ (hD .v))
      _= _ := (flagMixed_projection_decomposition surfaceFlag firstFlag delayFlag).symm
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    change (∑ a : A, (stageSeeds S a.1).card)≤_
    simp

end
end ProximityPrize.SubmissionLower.PortfolioLinearProper6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PortfolioLinearExceptions6815
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
open PortfolioLinearRoute6815

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

variable {firstFlag delayFlag : FlagDegree}

theorem wide_constant_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : Route S.F J firstFlag delayFlag)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G) :
    (∑ C : ConstantComponent S, (stageSeeds S C.1).card)≤
      flagMixed surfaceFlag firstFlag unitYZFlag+flagMixed surfaceFlag firstFlag unitAllFlag := by
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.cross _) hH
  have hcard := constant_prime_family_card_le (fun a : ConstantComponent S => a.1.1)
    (fun a b h => Subtype.ext (Subtype.ext h))
    (fun a => regularComponent_ne_point (GenericField K) S.G _ _ a.1) (fun a => a.2)
    S.G (MovingSourceReducedCycle6814.reducedTailSurface (linearH J) (linearG J)) S.irreducible_G.ne_zero
    (fun hz => hproper (hz ▸ dvd_zero _)) (S.irreducible_G.isRelPrime_iff_not_dvd.mpr hproper)
    (fun a => regularComponent_G_mem (GenericField K) S.G _ _ a.1)
    (fun a => reducedTail_mem_old_component S (linearH J) (linearG J) (hroute.cross _) a.1)
    surfaceFlag firstFlag hS (hroute.first)
  calc
    _≤∑ _ : ConstantComponent S, 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact constant_parameter_seeds_le_one (polynomialEmbedding K) S.selected _ a.1.1 a.2
        (fun gamma hgamma => componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) a.1 gamma hgamma)
    _=Fintype.card (ConstantComponent S) := by simp
    _≤_ := hcard

theorem wide_persistent_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : Route S.F J firstFlag delayFlag)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G)
    (hsmall : flagMixed surfaceFlag firstFlag unitZFlag<p)
    (agreements bound seedCap slopeCap : ℕ)
    (hnodes : S.nodes.card=agreements+errorCap)
    (hagreement : ∀ gamma∈Gamma, agreements≤(S.agreementFiber gamma).card)
    (hwa : RCN326.w<agreements) (hshort : RCN326.w+1≤bound) (hchar : bound<p)
    (hbox : S.F∈globalCoefficientBox K bound RCN326.w seedCap slopeCap) :
    (∑ C : PersistentComponent S, (stageSeeds S C.1).card)≤
      (errorCap+1)*flagMixed surfaceFlag firstFlag unitYZFlag := by
  let A := PersistentComponent S
  let component : A → FirstTailComponent S := Subtype.val
  let hz (a : A) := a.2.1
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.cross _) hH
  have hT := hroute.first
  have gate (a : A) := reduced_gamma_gate S (linearH J) (linearG J) (hroute.cross _) hproper
    surfaceFlag firstFlag hS hT hsmall a.1 (hz a)
  obtain ⟨D,hD⟩ := exists_reduced_cycle_family S hfirst (linearH J) (linearG J)
    (hroute.cross _) hH component Subtype.val_injective hz
    surfaceFlag firstFlag hS hT hsmall
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
  have hsum : (∑ a : A, frameCost D hz .u a)≤flagMixed surfaceFlag firstFlag unitYZFlag := by
    calc
      _≤∑ a : A, m a*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => by
        have hh := Nat.mul_le_mul_right (frameCost D hz .u a) (one_le_localMultiplicity S hfirst a.1)
        simpa only [one_mul] using hh)
      _≤_ := hD .u
  calc
    _≤∑ a : A, (errorCap+1)*frameCost D hz .u a := Finset.sum_le_sum (fun a _ => hcount a)
    _=(errorCap+1)*(∑ a : A, frameCost D hz .u a) := (Finset.mul_sum _ _ _).symm
    _≤_ := Nat.mul_le_mul_left _ hsum

end
end ProximityPrize.SubmissionLower.PortfolioLinearExceptions6815
end MergedPart3
