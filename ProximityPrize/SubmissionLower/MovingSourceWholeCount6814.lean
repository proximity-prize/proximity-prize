import ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814

/-! The actual retained Z-source and the whole-carrier proper pair feed
one isolated-point count. There is no per-geometric-factor budget charge. -/
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN002 RCN046 RCN084 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN341
open MovingSourceWholeCarrier6814 MovingSourceGeometricBudget6814 MovingSourceCarrierField6814
open MovingSourceRegularRestriction6814 MovingFiberThreeSources6811
open WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))

def WholePointBound (F : MvPolynomial (Fin 4) K) (S : Source F) (p : FlagDegree)
    (quadratic A : MvPolynomial (Fin 3) Omega) : Prop :=
  ∀ (W : FlagDegree) (cut : MvPolynomial (Fin 3) OmegaT), PolynomialInFlag W cut →
    ∀ points : Finset (Fin 3 → OmegaT),
      (∀ x ∈ points, MvPolynomial.eval x (wholeCarrier F)=0) →
      (∀ x ∈ points, MvPolynomial.eval x (regularEquation F quadratic A)=0) →
      (∀ x ∈ points, MvPolynomial.eval x (regularDenominator F A*S.leading phi)≠0) →
      (∀ x ∈ points, MvPolynomial.aeval x cut=0) →
      (∀ x ∈ points, IsolatedPoint (wholeCarrier F) (regularEquation F quadratic A) cut x) →
      7*points.card≤W.zOnly*flagMixed p unitZFlag ⟨3252,132,51⟩+
        7*(W.yz*25470+W.all*88560)

theorem wholePointBound_of_projection [CharP K 2130706433]
    (F : MvPolynomial (Fin 4) K) (hF : F≠0)
    (S : Source F) (hd : S.d=7) (hs : S.flag=⟨3252,132,51⟩) (hk : S.k=6)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (quadratic A : MvPolynomial (Fin 3) Omega)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1)
    (unit : AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩) :
    WholePointBound F S p quadratic A := by
  intro W cut hcut points hG hM hregular hzero hisolated
  have hne : wholeCarrier F≠0 := by
    intro hz
    exact hF (wholeCarrier_injective (by simpa only [wholeCarrier,map_zero] using hz))
  have hHdiv : surfaceMap phi (RCN313.polyH K F)∣regularDenominator F A := by
    apply dvd_mul_of_dvd_left
    rw [map_mul]
    exact dvd_mul_left _ _
  have h2 : (2 : OmegaT)≠0 := (CharP.cast_eq_zero_iff OmegaT 2130706433 2).not.mpr (by decide)
  have hfact : (S.k.factorial : OmegaT)≠0 := by
    rw [hk]
    exact SecondJetOwnShape.factorial_ne 6 (by omega)
  have hb := restricted_source_point_count phi F S (wholeCarrier F) p hne (dvd_refl _) hp
    2130706433 hunit h2 hfact (lift quadratic) (lift A) (initialCoordinate Omega)
    (inFlag_map _ hquadratic) (inFlag_map _ hA) (regularDenominator F A) hHdiv
    base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ unit W cut hcut points hG hM hregular hzero hisolated
  rw [hd,hs] at hb
  have hc := MovingSourcePrimeFamily6814.source_pair_directional_prices U T hU hUmax hUT hT
  exact hb.trans (Nat.add_le_add le_rfl (Nat.mul_le_mul_left 7
    (Nat.add_le_add (Nat.mul_le_mul_left W.yz hc.2.1) (Nat.mul_le_mul_left W.all hc.2.2))))

/-- The whole regular simple-J branch. Both source suppliers are actual
181255-agreement constructions. The two proper-helper exits remain
explicit; neither is silently treated as impossible. -/
theorem helpers_or_whole_point_bound [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (hFT : 3429<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (p : FlagDegree) (hp : PolynomialInFlag p (wholeCarrier F))
    (hunit : 2*(p.zOnly+p.yz+p.all)<2130706433) :
    (∃ Q, MovingSourceZSupplier6814.ProperHelper F Q r y t nodes u0 u1) ∨
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ S : Source F, S.d=7 ∧ S.flag=⟨3252,132,51⟩ ∧ WholePointBound F S p quadratic A := by
  rcases MovingSourceZSupplier6814.exists_helper_or_z_source nodes u0 u1 hN F Fact.out
    hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  obtain ⟨S,hd,hs,hk⟩ := hret
  rcases helper_or_whole_projection nodes u0 u1 hN J hJi hmid hB hJdegree
    U T hU hUmax hUT hT hJbounds F (by omega) r y t hr hy ht hF hpos hsmall hroot
    quadratic A hden hquadratic hA with hhelp | hfamily
  · exact Or.inr (Or.inl hhelp)
  obtain ⟨base,⟨unit⟩⟩ := hfamily
  exact Or.inr (Or.inr ⟨S,hd,hs,wholePointBound_of_projection F
    (Fact.out : Irreducible F).ne_zero S hd hs hk p hp hunit U T hU hUmax hUT hT
    quadratic A hquadratic hA base unit⟩)

#print axioms wholePointBound_of_projection
#print axioms helpers_or_whole_point_bound
end
end ProximityPrize.SubmissionLower.MovingSourceWholeCount6814
