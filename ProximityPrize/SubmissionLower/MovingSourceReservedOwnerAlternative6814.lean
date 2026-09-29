import ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814
import ProximityPrize.SubmissionLower.WholeSpacePowerSourcePair6814
import ProximityPrize.SubmissionLower.MovingSourceWideLinearFlow6814

/-! Exhaustive small-source owner routing with the native auxiliary reserve.
The original contact and factor arguments are unchanged; a main-only
native test is no longer mistaken for a complete native ledger test. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReservedOwnerAlternative6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpaceSourceKernel6814 WholeSpaceSourceAlternative6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpacePowerSupplier6814
open WholeSpaceUniqueOwnerAlternative6814 MovingSourceReservedOwnerBudget6814
open MovingSourceNativeEnvelope6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814 MovingSourceMixedOwnerRouting6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceWideLinearFlow6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156

variable {K E N : Type} [Field K] [Field E]
variable [CharP K 2130706433] [CharP E 2130706433] [Fintype N]

theorem helper_or_weighted_pair_of_box
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : Poly (K := K)) (hJi : Irreducible J) (m : ℕ) (hm : 0<m)
    (a : Box) (haq : a.q=copies3 m)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J)) (hgood : Good a)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F)
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (phi : MvPolynomial (Fin 4) K →+* E) (hphiF : phi F=0)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (hphiJ : (asS J).map phi≠0)
    (hroot : ((asS J).map phi).rootMultiplicity (ratio phi F)=m) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ e<copies3 m, ∃ Q : Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧ 0<3-e*m ∧
      (Polynomial.X-Polynomial.C (ratio phi F))^(3-e*m)∣(asS Q).map phi ∧
      e*weightedTotalDegree totalWeights J+weightedTotalDegree totalWeights Q≤1700 ∧
      e*weightedTotalDegree middleWeights J+weightedTotalDegree middleWeights Q≤98 ∧
      e*weightedTotalDegree slopeWeights J+weightedTotalDegree slopeWeights Q≤31 ∧
      e*J.degreeOf 1+Q.degreeOf 1≤14 := by
  obtain ⟨P,hP,hnot,hb,hcontact⟩ := exists_interpolant_not_dvd_power nodes u0 u1 hN J hJi.ne_zero a ha hgood
  rw [haq] at hnot
  rcases helper_or_retained nodes u0 u1 P hP hb hcontact F hFi hFT r y t hr hy ht hF with hhelp | hret
  · exact Or.inl hhelp
  have hp : (Polynomial.X-Polynomial.C (SecondJetCarrierDichotomy.ratio phi F))^3∣(asS P).map phi := by
    by_cases hz : (asS P).map phi=0
    · rw [hz]; exact dvd_zero _
    exact SecondJetCarrierDichotomy.multiplicity_of_helpers_dvd P F phi 14 2
      (fun e he => (hb e he).2.1) hphiF hH hz
      (SecondJetOwnShape.factorial_ne (K := E) 2 (by omega)) hret.2
  obtain ⟨e,he,Q,hPQ,hQ,hcop⟩ := cofactor_of_not_power J P hJi (copies3 m) hnot
  have hpower := cofactor_root_power (MovingSourceOwnerSplit6814.rootPolynomialMap phi)
    (SecondJetCarrierDichotomy.ratio phi F) J P Q e m hPQ hphiJ hroot hp
  have hw := weights_of_bounds P hb
  have hbound (w : Fin 5 → ℕ) (C : ℕ) (h : weightedTotalDegree w P≤C) :
      e*weightedTotalDegree w J+weightedTotalDegree w Q≤C := by
    rwa [hPQ,weight_mul _ _ _ (pow_ne_zero _ hJi.ne_zero) hQ,weight_pow _ _ hJi.ne_zero] at h
  have hd := hw.2.2.2.2
  rw [hPQ,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJi.ne_zero) hQ,
    MvPolynomial.degreeOf_pow_eq _ _ _ hJi.ne_zero] at hd
  exact Or.inr ⟨e,he,Q,hQ,hcop,residual_order_positive m e hm he,hpower,
    hbound _ _ hw.2.1,hbound _ _ hw.2.2.1,hbound _ _ hw.2.2.2.1,hd⟩

def fullNativeCost (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J : Poly (K := K)) : ℕ :=
  nativeCost F J+3*multiplicity F J*auxiliaryCharge (multiplicity F J) (order J) (slope J)
    (max (slope J) (middle J)) (max (slope J) (total J))

theorem unique_nonlinear_reserved_alternative
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : Poly (K := K)) (hJ : Irreducible J) (hJS : J∣S.P)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (hunique : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (hs : 2≤order J)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    fullNativeCost F J<3*272069082261391681*multiplicity F J ∨
      (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨ WeightedPair F J := by
  obtain ⟨hm,hms,hB,hU,hT,hex,hJne⟩ := unique_owner_data F S hS hFT hpos hsmall J hJ hJS hroot hunique
  have hn := source_nested J
  have hq := copies3_pos (multiplicity F J) hm
  have hb := Nat.mul_le_mul_right (slope J) hq
  have hu := Nat.mul_le_mul_right (middle J) hq
  have htt := Nat.mul_le_mul_right (total J) hq
  have hb31 : slope J≤31 := by omega
  have hu98 : max (slope J) (middle J)≤98 := by omega
  have ht995 : max (slope J) (total J)≤995 := by omega
  by_cases hfit : nativeCost F J<3*mainAllowance*multiplicity F J
  · left
    exact reserved_native_fits (multiplicity F J) (order J) (slope J)
      (max (slope J) (middle J)) (max (slope J) (total J)) hm hn.2.2.1 hb31 hu98 ht995 hfit
  by_cases hbu : slope J≤middle J
  · right
    have hbt : slope J≤total J := hbu.trans hn.1
    have hcost : nativeCost F J=native (multiplicity F J) (order J) (slope J) (middle J) (total J) := by
      simp only [nativeCost,max_eq_right hbu,max_eq_right hbt]
    obtain ⟨a,haq,ha,hgood⟩ := reserved_failure_has_box (multiplicity F J) (order J)
      (slope J) (middle J) (total J) hm hs hms hn.2.2.1 hbu hn.1 hB hU hT hex (by omega)
    exact helper_or_weighted_pair_of_box nodes u0 u1 hN J hJ (multiplicity F J) hm a haq ha hgood
      F (Fact.out : Irreducible F) (by omega) r y t hr hy ht hF
      (carrierMap F) (carrierMap_self F) (carrier_H_nonzero F hpos hsmall) hJne rfl
  · have hub : middle J≤slope J := by omega
    have hmax : copies3 (multiplicity F J)*max (slope J) (total J)≤995 := by
      rcases le_total (slope J) (total J) with h | h
      · rw [max_eq_right h]; exact hT
      · rw [max_eq_left h]; omega
    have hh := padded_reserved_native_fits (multiplicity F J) (order J) (slope J) (max (slope J) (total J))
      hm hs hms hn.2.2.1 (le_max_left _ _) hB hmax
    exact False.elim (hfit (by simpa only [nativeCost,max_eq_left hub] using hh))

/-- Every owner alternative needed by the small-source-first strategy is
now explicit. This is routing, not a claim that the mixed strata have
already been charged to the full Stage cardinality ledger. -/
theorem small_source_owner_routes
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (hFT : 2985<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    ∃ J : Poly (K:=K), Irreducible J ∧ J∣S.P ∧
      rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0 ∧
      ((∃ D, Irreducible D ∧ D∣S.P ∧ rootEvaluation (carrierMap F) (ratio (carrierMap F) F) D=0 ∧ IsRelPrime J D) ∨
        WideLinearRoute F J ∨
        fullNativeCost F J<3*272069082261391681*multiplicity F J ∨
        (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨ WeightedPair F J) := by
  have hp := canonical_source_power F S (by rw [hS.2.2.1]; omega) hpos hsmall
    (by rw [hS.2.2.2.2.1]; omega)
  have hp3 : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣rootPolynomialMap (carrierMap F) S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3∣(asS S.P).map (carrierMap F)
    simpa only [Source.d,hS.2.2.2.2.1] using hp.2
  have hz : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) S.P=0 :=
    Polynomial.dvd_iff_isRoot.mp ((dvd_pow_self _ (by decide : 3≠0)).trans hp3)
  obtain ⟨J,hJ,hJS,hroot,hcases⟩ := small_source_first_split
    (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) S.P (source_nonzero F S) hz
  refine ⟨J,hJ,hJS,hroot,?_⟩
  rcases hcases with huni | htwo
  · right
    have hdeg := MovingSourceSameSourceBudget6814.factor_order_pos_of_root
      (carrierMap F) (ratio (carrierMap F) F) S.P J hp.1 hJS hroot
    by_cases hlinear : J.degreeOf 1=1
    · exact Or.inl (wide_linear_route F S hS hFT hpos hsmall J hJ hJS hlinear hroot huni)
    · right
      exact unique_nonlinear_reserved_alternative nodes u0 u1 hN F S hS hFT hpos hsmall
        J hJ hJS hroot huni (by change 2≤J.degreeOf 1; change 0<J.degreeOf 1 at hdeg; omega)
        r y t hr hy ht hF
  · exact Or.inl htwo

#print axioms unique_nonlinear_reserved_alternative
#print axioms small_source_owner_routes
end
end ProximityPrize.SubmissionLower.MovingSourceReservedOwnerAlternative6814
