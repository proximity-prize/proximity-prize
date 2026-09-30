import ProximityPrize.SubmissionLower.MovingSourceIndexedMovingCoordinates6814
namespace ProximityPrize.SubmissionLower.MovingSourceIndexedMovingDegrees6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN002 RCN084 RCN095 RCN134 RCN135 RCN136 RCN199 RCN202 RCN207 RCN208 RCN264 RCN313 RCN344
open MovingFiberThreeSources6811 MovingSourceTargetField6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814 MovingSourceExtendedPointCount6814
open MovingSourceExtendedMovingDegrees6814

variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [IsAlgClosed E] [CharP E 2130706433]
variable (eta : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap eta)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)
local instance : Algebra (RatFunc E) OmegaT := targetAlgebra E
local instance : IsScalarTower E (RatFunc E) OmegaT := target_tower E

theorem sum_indexed_moving_degrees
    {I : Type} [Fintype I]
    (F : MvPolynomial (Fin 4) K) (S : Source F)
    (G : I → MvPolynomial (Fin 3) Omega) (hGF : ∀ i, G i∣frozenCarrier eta F)
    (Q A : MvPolynomial (Fin 3) Omega) (scale z u v : ℕ)
    (hbound : ExtendedPointBudget eta F S Q A scale z u v)
    (n : ℕ) (coeff : Fin (n+1) → MvPolynomial (Fin 3) Omega)
    (W : FlagDegree) (hcut : PolynomialInFlag W (extendedTargetCut n coeff Q A))
    (old : ∀ i, ExtendedFactorFamily eta F (G i) n coeff)
    (hold : Function.Injective (fun i => (old i).1))
    (hleading : ∀ i, S.leading (codeMap eta)∉(old i).1)
    (hA : ∀ i, A∉(old i).1)
    (projection : ∀ i, SeparableCoordinate Omega (CoordinateField Omega (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Omega (CoordinateField Omega (old i).1) (projection i)=
      movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A) :
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
  have hinj : Function.Injective prime := hold
  have hwhole (i : I) : lift (G i)∣extendedCarrier eta F := by
    have hh := map_dvd (MvPolynomial.map (coefficientEmbedding Omega)) (hGF i)
    simpa only [frozenCarrier,lift_frozen,extendedCarrier] using hh
  have certificate (i : I) (f : CoordinateField Omega (prime i) →ₐ[RatFunc Omega] OmegaT) :
      let x := embeddingPoint (prime i) (f.restrictScalars Omega)
      MvPolynomial.eval x (extendedCarrier eta F)=0 ∧
      MvPolynomial.eval x (extendedEquation eta F Q A)=0 ∧
      MvPolynomial.aeval x (extendedTargetCut n coeff Q A)=0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*lift A)≠0 ∧
      IsolatedPoint (extendedCarrier eta F) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A) x := by
    have hj : algebraMap (RatFunc Omega) (CoordinateField Omega (prime i)) (rationalVariable Omega)=
        movingValue (old i).1 (frozenH eta F) (frozenG eta F) Q A := hvalue i
    have hc := embedding_point_certificate (G i) (frozenH eta F) (frozenG eta F) Q A n coeff
      (old i) hj (hA i) f
    have hc' :
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (lift (G i))=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (extendedEquation eta F Q A)=0 ∧
        MvPolynomial.aeval (embeddingPoint (prime i) (f.restrictScalars Omega)) (extendedTargetCut n coeff Q A)=0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (surfaceMap phi (polyH K F)*lift A)≠0 ∧
        IsolatedPoint (lift (G i)) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A)
          (embeddingPoint (prime i) (f.restrictScalars Omega)) := by
      simpa only [scalar_eq_lift,frozenH,frozenG,lift_frozen,target_variable,extendedEquation,extendedTargetCut] using hc
    have hzero := map_dvd (MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))) (hwhole i)
    rw [hc'.1,zero_dvd_iff] at hzero
    have hreg : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega))
        (MvPolynomial.pderiv (1 : Fin 3) (extendedCarrier eta F))≠0 := by
      have hr := hc'.2.2.2.1
      rw [map_mul,mul_ne_zero_iff] at hr
      simpa only [extendedCarrier,RCN267.surfaceMap_pderiv_R,polyH] using hr.1
    exact ⟨hzero,hc'.2.1,hc'.2.2.1,hc'.2.2.2.1,
      MovingSourceFactorIsolation6814.isolated_whole_of_factor
        (extendedCarrier eta F) (lift (G i)) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A)
        (hwhole i) _ hc'.1 hreg hc'.2.2.2.2⟩
  have hc : ∀ x ∈ points,
      MvPolynomial.eval x (extendedCarrier eta F)=0 ∧ MvPolynomial.eval x (extendedEquation eta F Q A)=0 ∧
      MvPolynomial.eval x (extendedDenominator eta F A*S.leading phi)≠0 ∧
      MvPolynomial.aeval x (extendedTargetCut n coeff Q A)=0 ∧
      IsolatedPoint (extendedCarrier eta F) (extendedEquation eta F Q A) (extendedTargetCut n coeff Q A) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hh := certificate i f
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.1,hh.2.2.2.2⟩
    have hHA := hh.2.2.2.1
    rw [map_mul,mul_ne_zero_iff] at hHA
    have hL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Omega)) (S.leading phi)≠0 := by
      have he : S.leading phi=lift (S.leading (codeMap eta)) := (lift_frozen eta _).symm
      rw [he,eval_lift_embedding]
      intro hz
      exact hleading i ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
    simpa only [commonBaseEmbeddingPoint,extendedDenominator,map_mul,map_ofNat] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hHA.1) (mul_ne_zero h2 hHA.2)) hL
  have hb := hbound W (extendedTargetCut n coeff Q A) hcut points
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2.1)
    (fun x hx => (hc x hx).2.2.1) (fun x hx => (hc x hx).2.2.2.1)
    (fun x hx => (hc x hx).2.2.2.2)
  have hcard := genericFiberPoints_card (B:=RatFunc Omega) (L:=OmegaT) prime hinj
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hb

end
end ProximityPrize.SubmissionLower.MovingSourceIndexedMovingDegrees6814
