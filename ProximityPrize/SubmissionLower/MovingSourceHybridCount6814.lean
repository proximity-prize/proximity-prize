import ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
namespace ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
open scoped BigOperators
open RCN002 RCN037 RCN042 RCN046 RCN072 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN341 RCN344
open SecondJetCoefficients SecondJetClearedHelper
open MovingFiberProjection6811 MovingFiberThreeSources6811 MovingFiberNativeBudget6811

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local notation "Poly3" => MvPolynomial (Fin 3) Ω

theorem old_z_bound_on_new_projections
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (S : Source F)
    (carrier : Poly3) (p : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all)<c)
    (h2 : (2 : Ω)≠0) (hfact : (S.k.factorial : Ω)≠0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (R : Poly3)
    (hH : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      surfaceMap phi (RCN313.polyH K F)∉C.1)
    (hL : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      S.leading phi∉C.1)
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      SeparableLiteralCoordinate C.1)
    (pNew qNew : FlagDegree) (unit : AdaptiveUnitProjectionFamily base pNew qNew) :
    S.d*(∑ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K F)) (surfaceMap phi (RCN313.polyG K F)) Q A target) R,
      coordinateDegree Ω (CoordinateField Ω C.1) (unit.zProjection C)) ≤
      flagMixed p unitZFlag S.flag := by
  classical
  let H := surfaceMap phi (RCN313.polyH K F)
  let M := movingEquation H (surfaceMap phi (RCN313.polyG K F)) Q A target
  let Family := RegularComponent Ω carrier M R
  let forget (C : Family) : RegularComponent Ω carrier M (H*S.leading phi) :=
    ⟨C.1,(mem_regularComponents Ω).mpr ⟨regularComponent_mem Ω carrier M R C,by
      intro hz
      exact ((inferInstance : C.1.IsPrime).mem_or_mem hz).elim (hH C) (hL C)⟩⟩
  have hinj : Function.Injective forget := by
    intro C D h
    exact Subtype.ext (congrArg (fun C0 : RegularComponent Ω carrier M (H*S.leading phi) => C0.1) h)
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext)≠0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfe : (S.k.factorial : Ext)≠0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne hfact
  exact sum_coordinate_projection_degrees (E:=Ext) phi F carrier p unitZFlag hcarrier hcarrierF hflag
    linearZ linearZ_flag c (by omega) (by simpa [unitZFlag] using hunit)
    S.P S.B S.U S.T S.s S.k S.n0 S.hS S.hshape S.hBU S.hUT S.hdn S.hB S.hn S.hdiv
    h2e hfe Q A target hQ hA forget hinj unit.zProjection unit.zValue

end
end ProximityPrize.SubmissionLower.MovingSourceHybridCount6814
