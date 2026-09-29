import ProximityPrize.SubmissionLower.MovingSourceTargetField6814

/-! Apply the whole-carrier point budget to the ACTUAL generic embedding
points of the old moving projection. Regularity and isolation are supplied
by the existing certificate, not added as point-budget assumptions. -/
namespace ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814 MovingSourceWholeCarrier6814
open MovingSourceGeometricBudget6814 MovingSourceWholeCount6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
local instance : Algebra (RatFunc Omega) OmegaT := targetAlgebra Omega
local instance : IsScalarTower Omega (RatFunc Omega) OmegaT := target_tower Omega

def baseCarrier (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) F
def baseH (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyH K F)
def baseG (F : MvPolynomial (Fin 4) K) := surfaceMap (polynomialEmbedding K) (polyG K F)

abbrev OriginalFamily (F : MvPolynomial (Fin 4) K) (n : ℕ)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) :=
  RegularComponent Omega (baseCarrier F) (filteredCut n coeff (baseH F) (baseG F)) (baseH F)

def targetCut (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (Q A : MvPolynomial (Fin 3) Omega) : MvPolynomial (Fin 3) OmegaT :=
  eliminatedCut n (fun j => lift (coeff j)) (lift Q) (lift A) (initialCoordinate Omega)

theorem scalar_eq_lift (P : MvPolynomial (Fin 3) Omega) : scalarPolynomialMap Omega OmegaT P=lift P := by
  rw [scalarPolynomialMap,←coefficientEmbedding_eq_algebraMap Omega]

theorem lift_surface (P : MvPolynomial (Fin 4) K) :
    lift (surfaceMap (polynomialEmbedding K) P)=surfaceMap phi P := by
  simp only [surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

theorem eval_lift_embedding (C : Ideal (MvPolynomial (Fin 3) Omega)) [C.IsPrime]
    (f : CoordinateField Omega C →ₐ[Omega] OmegaT) (P : MvPolynomial (Fin 3) Omega) :
    MvPolynomial.eval (embeddingPoint C f) (lift P)=f (coordinateEvaluation Omega C P) := by
  rw [MvPolynomial.eval_map,coefficientEmbedding_eq_algebraMap]
  exact AlgHom.congr_fun (embeddingPoint_aeval C f) P

theorem sum_moving_degrees_of_whole_bound [CharP K 2130706433]
    {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (S : Source F) (p : FlagDegree)
    (Q A : MvPolynomial (Fin 3) Omega) (hbound : WholePointBound F S p Q A)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (W : FlagDegree) (hcut : PolynomialInFlag W (targetCut n coeff Q A))
    (old : I → OriginalFamily F n coeff) (hold : Function.Injective old)
    (hleading : ∀ i, S.leading (polynomialEmbedding K)∉(old i).1)
    (hA : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Omega (CoordinateField Omega (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Omega (CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (baseH F) (baseG F) Q A) :
    7*(∑ i, SeparableCoordinate.degree Omega (CoordinateField Omega (old i).1) (projection i))≤
      W.zOnly*flagMixed p unitZFlag ⟨3252,132,51⟩+7*(W.yz*25470+W.all*88560) := by
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
  have certificate (i : I) (f : CoordinateField Omega (prime i) →ₐ[RatFunc Omega] OmegaT) :
      let x := embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (wholeCarrier F)=0 ∧
      MvPolynomial.eval x (regularEquation F Q A)=0 ∧
      MvPolynomial.aeval x (targetCut n coeff Q A)=0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0 ∧
      IsolatedPoint (wholeCarrier F) (regularEquation F Q A) (targetCut n coeff Q A) x := by
    have hj : algebraMap (RatFunc Omega) (CoordinateField Omega (prime i)) (rationalVariable Omega)=
        movingValue (old i).1 (baseH F) (baseG F) Q A := hvalue i
    have hc := embedding_point_certificate (baseCarrier F) (baseH F) (baseG F) Q A n coeff
      (old i) hj (hA i) f
    simpa only [scalar_eq_lift,baseCarrier,baseH,baseG,lift_surface,target_variable,
      wholeCarrier,regularEquation,targetCut] using hc
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

/-- Reuse the existing small cut flag on the actual target polynomial. -/
theorem targetCut_small_flag
    (F : MvPolynomial (Fin 4) K) (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega) (flags : Fin (n+1) → FlagDegree)
    (hH : PolynomialInFlag ⟨a,b+1,s+1⟩ (baseH F))
    (hG : PolynomialInFlag ⟨a,b,s+3⟩ (baseG F))
    (hcoeff : ∀ j, PolynomialInFlag (flags j) (coeff j))
    (heq : ∀ j, flags j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (Q A : MvPolynomial (Fin 3) Omega)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) (targetCut n coeff Q A) := by
  have hh := (fiber_small_flags (E:=OmegaT) a b s n center (baseH F) (baseG F) Q A coeff flags
    hH hG hQ hA hcoeff heq).2
  simpa only [fiberCut,scalar_eq_lift,target_variable,targetCut] using hh

#print axioms sum_moving_degrees_of_whole_bound
#print axioms targetCut_small_flag
end
end ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
