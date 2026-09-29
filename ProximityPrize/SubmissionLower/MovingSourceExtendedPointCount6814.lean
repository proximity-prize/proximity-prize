import ProximityPrize.SubmissionLower.MovingSourceExtendedThickPair6814
import ProximityPrize.SubmissionLower.MovingSourcePairPoleFamily6814

/-! One shared weighted count survives the additional field extension used
by first-cut slicing. No new degree allowance is introduced. -/
namespace ProximityPrize.SubmissionLower.MovingSourceExtendedPointCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 700000
open RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN264 RCN313 RCN338 RCN341
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814
open MovingSourceWeightedProjection6814 MovingSourceWeightedPairFamily6814 MovingSourceWeightedPairPoints6814
open MovingSourceExtendedCoefficients6814 MovingSourceExtendedThickPair6814
variable {K E : Type} [Field K] [CharP K 2130706433] [Field E] [CharP E 2130706433]
variable (f : GenericField K →+* E)
local notation "Omega" => E
local notation "OmegaT" => GenericField E
local notation "Poly3" => MvPolynomial (Fin 3) E
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding E) (codeMap f)
local notation "lift" => MvPolynomial.map (coefficientEmbedding E)

abbrev ExtendedMovingFamily (F : MvPolynomial (Fin 4) K) (Q A : Poly3) :=
  RegularComponent OmegaT (extendedCarrier f F) (extendedEquation f F Q A) (extendedDenominator f F A)

theorem extended_source_pair_family
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ∃ base : ∀ V : ExtendedMovingFamily f F Q A, SeparableLiteralCoordinate V.1,
      ∃ unit : AdaptiveUnitProjectionFamily base (ordinaryFlag S.P) (ordinaryFlag T.P),
        Nonempty (RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d)) := by
  obtain ⟨B,C,hB,hC,hBC,hBflag,hCflag,hthick⟩ := exists_extended_thick_pair f F S T hcop d hS hT hchar Q A hden hQ hA
  have ht : HasThickness (extendedCarrier f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
      (extendedEquation f F Q A) B C d := hthick
  have hG : extendedCarrier f F≠0 := by
    intro hh
    exact hF (extendedCarrier_injective f (by simpa only [extendedCarrier,map_zero] using hh))
  exact exists_weighted_pair_family (extendedCarrier f F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
    (extendedEquation f F Q A) B C hG hB hC hBC d hd ht
    (ordinaryFlag S.P) (ordinaryFlag T.P) hBflag hCflag 2130706433 hz hu
    (extendedCarrier_derivative_nonzero f F hpos hsmall)

/-- Keep the old Z-source price and pay the two new directions with their
proved common contact multiplicity. All geometric suppliers are built
from S and T; no shared-degree or intersection-count premise remains. -/
theorem extended_source_pair_point_count
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (extendedCarrier f F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433)
    (W : FlagDegree) (cut : Poly3T) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → OmegaT))
    (hG : ∀ v∈points, MvPolynomial.eval v (extendedCarrier f F)=0)
    (hM : ∀ v∈points, MvPolynomial.eval v (extendedEquation f F Q A)=0)
    (hregular : ∀ v∈points, MvPolynomial.eval v (extendedDenominator f F A*SZ.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint (extendedCarrier f F) (extendedEquation f F Q A) cut v) :
    SZ.d*d*points.card≤d*W.zOnly*flagMixed p unitZFlag SZ.flag+
      SZ.d*(W.yz*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag+
        W.all*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  obtain ⟨base,unit,⟨cert⟩⟩ := extended_source_pair_family f F hF hpos hsmall S T hcop d hd hS hT hchar
    Q A hden hQ hA hz hu
  have hGne : extendedCarrier f F≠0 := by
    intro hh
    exact hF (extendedCarrier_injective f (by simpa only [extendedCarrier,map_zero] using hh))
  have hHdiv : surfaceMap phi (polyH K F)∣extendedDenominator f F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (SZ.k.factorial : OmegaT)≠0 := SecondJetOwnShape.factorial_ne SZ.k hZchar
  exact restricted_weighted_source_point_count phi F SZ (extendedCarrier f F) p hGne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift Q) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA) (extendedDenominator f F A) hHdiv base unit d cert
    W cut hcut points hG hM hregular hzero hisolated


def ExtendedPointBudget (F : MvPolynomial (Fin 4) K) (SZ : Source F)
    (Q A : Poly3) (scale z u v : ℕ) : Prop :=
  ∀ (W : FlagDegree) (cut : Poly3T), PolynomialInFlag W cut →
    ∀ points : Finset (Fin 3 → OmegaT),
      (∀ x∈points, MvPolynomial.eval x (extendedCarrier f F)=0) →
      (∀ x∈points, MvPolynomial.eval x (extendedEquation f F Q A)=0) →
      (∀ x∈points, MvPolynomial.eval x (extendedDenominator f F A*SZ.leading phi)≠0) →
      (∀ x∈points, MvPolynomial.aeval x cut=0) →
      (∀ x∈points, IsolatedPoint (extendedCarrier f F) (extendedEquation f F Q A) cut x) →
      scale*points.card≤W.zOnly*z+W.yz*u+W.all*v

theorem extended_sources_point_budget
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (extendedCarrier f F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ExtendedPointBudget f F SZ Q A (SZ.d*d) (d*flagMixed p unitZFlag SZ.flag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag)
      (SZ.d*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hh := extended_source_pair_point_count f F hF hpos hsmall S T hcop d hd hS hT hchar
    SZ hZchar p hp hunit Q A hden hQ hA hz hu W cut hcut points hG hM hregular hzero hisolated
  convert hh using 1 <;> ring

#print axioms extended_source_pair_point_count
#print axioms extended_sources_point_budget
end
end ProximityPrize.SubmissionLower.MovingSourceExtendedPointCount6814
