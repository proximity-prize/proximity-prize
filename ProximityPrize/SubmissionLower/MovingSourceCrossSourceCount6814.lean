import ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814

/-! Actual Source records produce the multiplicity-weighted proper-pair
point count. This discharges the formerly hypothetical geometric saving;
uniform source-power avoidance and the complete ledger remain separate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCrossSourceCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN264 RCN313 RCN338 RCN341
open MovingFiberThreeSources6811 MovingSourceCoupledClearing6814 MovingSourceGeometricBudget6814
open MovingSourceWholeCarrier6814 MovingSourceThickGenericPair6814 MovingSourceWeightedProjection6814
open MovingSourceWeightedPairFamily6814 MovingSourceWeightedPairPoints6814
variable {K : Type} [Field K] [CharP K 2130706433]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
local notation "phi" => RingHom.comp (coefficientEmbedding Omega) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding Omega)

theorem source_pair_weighted_family
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433) :
    ∃ base : ∀ V : WholeMovingFamily F Q A, SeparableLiteralCoordinate V.1,
      ∃ unit : AdaptiveUnitProjectionFamily base (ordinaryFlag S.P) (ordinaryFlag T.P),
        Nonempty (RegularComponentWeightedInertiaResultantCertificate unit.toPrimeFlagBudgetFamily (fun _ => d)) := by
  obtain ⟨B,C,hB,hC,hBC,hBflag,hCflag,hthick⟩ := exists_thick_generic_pair F S T hcop d hS hT hchar Q A hden hQ hA
  have ht : HasThickness (wholeCarrier F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
      (regularEquation F Q A) B C d := hthick
  have hG : wholeCarrier F≠0 := by
    intro hh
    exact hF (wholeCarrier_injective (by simpa only [wholeCarrier,map_zero] using hh))
  exact exists_weighted_pair_family (wholeCarrier F) (surfaceMap phi (2*polyH K F)) (lift (2*A))
    (regularEquation F Q A) B C hG hB hC hBC d hd ht
    (ordinaryFlag S.P) (ordinaryFlag T.P) hBflag hCflag 2130706433 hz hu
    (wholeCarrier_derivative_nonzero F hpos hsmall)

/-- Keep the old Z-source price and pay the two new directions with their
proved common contact multiplicity. All geometric suppliers are built
from S and T; no shared-degree or intersection-count premise remains. -/
theorem source_pair_weighted_point_count
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (S T : Source F) (hcop : IsRelPrime S.P T.P)
    (d : ℕ) (hd : 0<d) (hS : d≤S.d) (hT : d≤T.d) (hchar : d≤2130706433)
    (SZ : Source F) (hZchar : SZ.k<2130706433)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (Q A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hz : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitZFlag<2130706433)
    (hu : flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag<2130706433)
    (W : FlagDegree) (cut : Poly3T) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → OmegaT))
    (hG : ∀ v∈points, MvPolynomial.eval v (wholeCarrier F)=0)
    (hM : ∀ v∈points, MvPolynomial.eval v (regularEquation F Q A)=0)
    (hregular : ∀ v∈points, MvPolynomial.eval v (regularDenominator F A*SZ.leading phi)≠0)
    (hzero : ∀ v∈points, MvPolynomial.aeval v cut=0)
    (hisolated : ∀ v∈points, IsolatedPoint (wholeCarrier F) (regularEquation F Q A) cut v) :
    SZ.d*d*points.card≤d*W.zOnly*flagMixed p unitZFlag SZ.flag+
      SZ.d*(W.yz*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitYZFlag+
        W.all*flagMixed (ordinaryFlag S.P) (ordinaryFlag T.P) unitAllFlag) := by
  obtain ⟨base,unit,⟨cert⟩⟩ := source_pair_weighted_family F hF hpos hsmall S T hcop d hd hS hT hchar
    Q A hden hQ hA hz hu
  have hGne : wholeCarrier F≠0 := by
    intro hh
    exact hF (wholeCarrier_injective (by simpa only [wholeCarrier,map_zero] using hh))
  have hHdiv : surfaceMap phi (polyH K F)∣regularDenominator F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (SZ.k.factorial : OmegaT)≠0 := SecondJetOwnShape.factorial_ne SZ.k hZchar
  exact restricted_weighted_source_point_count phi F SZ (wholeCarrier F) p hGne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift Q) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hQ) (inFlag_map _ hA) (regularDenominator F A) hHdiv base unit d cert
    W cut hcut points hG hM hregular hzero hisolated

#print axioms source_pair_weighted_family
#print axioms source_pair_weighted_point_count
end
end ProximityPrize.SubmissionLower.MovingSourceCrossSourceCount6814
