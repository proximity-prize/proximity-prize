import ProximityPrize.SubmissionLower.PortfolioLinearRoute6815
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
