import ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
import ProximityPrize.SubmissionLower.MovingSourceSameSourceCount6814

/-! General pair budgets, applied to actual generic points of a Stage's
geometric carrier factor. The entire original carrier is charged once. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814 MovingSourceWholeCarrier6814
open MovingSourceGeometricBudget6814 MovingSourceMovingDegrees6814 MovingSourceCoupledClearing6814
open MovingSourceCrossSourceCount6814 MovingSourceSameSourceCount6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

abbrev FactorFamily (F : MvPolynomial (Fin 4) K) (G : MvPolynomial (Fin 3) Omega)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) :=
  RegularComponent Omega G (filteredCut n coeff (baseH F) (baseG F)) (baseH F)

def ScaledPointBudget (F : MvPolynomial (Fin 4) K) (S : Source F)
    (Q A : MvPolynomial (Fin 3) Omega) (scale z u v : ℕ) : Prop :=
  ∀ (W : FlagDegree) (cut : MvPolynomial (Fin 3) OmegaT), PolynomialInFlag W cut →
    ∀ points : Finset (Fin 3 → OmegaT),
      (∀ x∈points, MvPolynomial.eval x (wholeCarrier F)=0) →
      (∀ x∈points, MvPolynomial.eval x (regularEquation F Q A)=0) →
      (∀ x∈points, MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0) →
      (∀ x∈points, MvPolynomial.aeval x cut=0) →
      (∀ x∈points, IsolatedPoint (wholeCarrier F) (regularEquation F Q A) cut x) →
      scale*points.card≤W.zOnly*z+W.yz*u+W.all*v

theorem weighted_sources_point_budget [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ScaledPointBudget F SZ Q A (SZ.d*d) (d*flagMixed p unitZFlag SZ.flag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hh := source_pair_weighted_point_count F hF hpos hsmall S T hcop d hd hS hT hchar
    SZ hZchar p hp hunit Q A hden hQ hA hz hu W cut hcut points hG hM hregular hzero hisolated
  convert hh using 1 <;> ring

theorem sum_moving_degrees_of_pair_budget [CharP K 2130706433]
    {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (S : Source F)
    (G : MvPolynomial (Fin 3) Omega) (hGF : G∣baseCarrier F)
    (Q A : MvPolynomial (Fin 3) Omega) (scale z u v : ℕ)
    (hbound : ScaledPointBudget F S Q A scale z u v)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (W : FlagDegree) (hcut : PolynomialInFlag W (targetCut n coeff Q A))
    (old : I → FactorFamily F G n coeff) (hold : Function.Injective old)
    (hleading : ∀ i, S.leading (polynomialEmbedding K)∉(old i).1)
    (hA : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Omega (CoordinateField Omega (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Omega (CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    scale*(∑ i, SeparableCoordinate.degree Omega (CoordinateField Omega (old i).1) (projection i))≤
      W.zOnly*z+W.yz*u+W.all*v := by
  classical
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq fun a => ((projection i).embedding.commutes a).symm
  letI : ∀ i, FiniteDimensional (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (prime i)) :=
    fun i => (projection i).separable
  let points := genericFiberPoints (B:=RatFunc Omega) (L:=OmegaT) prime
  have hinj : Function.Injective prime := by
    intro i j h
    exact hold (Subtype.ext h)
  have hwhole : lift G∣wholeCarrier F := by
    have hh := map_dvd (MvPolynomial.map (coefficientEmbedding Omega)) hGF
    simpa only [baseCarrier,lift_surface,wholeCarrier] using hh
  have certificate (i : I) (f : CoordinateField Omega (prime i) →ₐ[RatFunc Omega] OmegaT) :
      let x := embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (wholeCarrier F)=0 ∧
      MvPolynomial.eval x (regularEquation F Q A)=0 ∧
      MvPolynomial.aeval x (targetCut n coeff Q A)=0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0 ∧
      IsolatedPoint (wholeCarrier F) (regularEquation F Q A) (targetCut n coeff Q A) x := by
    have hj : algebraMap (RatFunc Omega) (CoordinateField Omega (prime i)) (rationalVariable Omega)=
        movingValue (old i).1 (baseH F) (baseG F) Q A := hvalue i
    have hc := embedding_point_certificate G (baseH F) (baseG F) Q A n coeff
      (old i) hj (hA i) f
    have hc' :
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (lift G)=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (regularEquation F Q A)=0 ∧
        MvPolynomial.aeval (embeddingPoint (prime i) (f.restrictScalars Omega)) (targetCut n coeff Q A)=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (surfaceMap phi (polyH K F)*lift A)≠0 ∧
        IsolatedPoint (lift G) (regularEquation F Q A) (targetCut n coeff Q A)
          (embeddingPoint (prime i) (f.restrictScalars Omega)) := by
      simpa only [scalar_eq_lift,baseH,baseG,lift_surface,target_variable,regularEquation,targetCut] using hc
    have hzero := map_dvd (MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))) hwhole
    rw [hc'.1,zero_dvd_iff] at hzero
    have hreg : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))
        (MvPolynomial.pderiv (1 : Fin 3) (wholeCarrier F))≠0 := by
      have hr := hc'.2.2.2.1
      rw [map_mul,mul_ne_zero_iff] at hr
      simpa only [wholeCarrier,RCN267.surfaceMap_pderiv_R,polyH] using hr.1
    exact ⟨hzero,hc'.2.1,hc'.2.2.1,hc'.2.2.2.1,
      MovingSourceFactorIsolation6814.isolated_whole_of_factor
        (wholeCarrier F) (lift G) (regularEquation F Q A) (targetCut n coeff Q A)
        hwhole _ hc'.1 hreg hc'.2.2.2.2⟩
  have hc : ∀ x ∈ points,
      MvPolynomial.eval x (wholeCarrier F)=0 ∧ MvPolynomial.eval x (regularEquation F Q A)=0 ∧
      MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0 ∧
      MvPolynomial.aeval x (targetCut n coeff Q A)=0 ∧
      IsolatedPoint (wholeCarrier F) (regularEquation F Q A) (targetCut n coeff Q A) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hh := certificate i f
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.2⟩
    have hHA := hh.2.2.2.1
    rw [map_mul,mul_ne_zero_iff] at hHA
    have hL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (S.leading phi)≠0 := by
      have he : S.leading phi=lift (S.leading (polynomialEmbedding K)) := (lift_surface _).symm
      rw [he,eval_lift_embedding]
      intro hz
      exact hleading i ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
    simpa only [commonBaseEmbeddingPoint,regularDenominator,map_mul,map_ofNat] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hHA.1) (mul_ne_zero h2 hHA.2)) hL
  have hb := hbound W (targetCut n coeff Q A) hcut points
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2.1)
    (fun x hx => (hc x hx).2.2.1) (fun x hx => (hc x hx).2.2.2.1)
    (fun x hx => (hc x hx).2.2.2.2)
  have hcard := genericFiberPoints_card (B:=RatFunc Omega) (L:=OmegaT) prime hinj
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hb


#print axioms weighted_sources_point_budget
#print axioms sum_moving_degrees_of_pair_budget
end
end ProximityPrize.SubmissionLower.MovingSourcePairMovingDegrees6814
