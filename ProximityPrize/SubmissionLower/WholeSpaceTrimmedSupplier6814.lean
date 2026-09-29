import ProximityPrize.SubmissionLower.WholeSpaceTrimmedReceipts6814
import ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
import ProximityPrize.SubmissionLower.MovingSourceReservedOwnerAlternative6814

/-! Actual contact interpolation for the six trimmed avoidance cases,
followed by the existing multiplicity-preserving cofactor construction. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceTrimmedSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpaceSourceKernel6814
open WholeSpaceSourceCounts6814 SecondJetGlobalSupport

variable {K N I : Type} [Field K] [Fintype N] [Fintype I]

theorem contact_not_power_generic
    (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (hb : ∀ i, 2*e i 1+e i 3≤31) (hs : ∀ i, e i 1≤14)
    (hu : ∀ i, e i 1+e i 2+e i 3≤98)
    (ht : ∀ i, e i 1+e i 2+e i 3+e i 4≤1700)
    (hc : ∀ i, e i 0+131071*e i 2+131070*e i 3+131069*e i 1<cutoff (e i 1))
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 627003341034+Fintype.card N*
      SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
        (fun h => (cutoff h+31-1)/131071)≤Fintype.card I)
    (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hgood : WholeSpaceTrimmedReceipts6814.Good a) :
    ∃ P : Poly (K := K), P≠0 ∧ ¬J^a.q∣P ∧ Bounds P ∧
      ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes i) (u0 i) (u1 i) P) := by
  obtain ⟨V,hfinite,hdim,hsupport,hcontact⟩ := exists_contact_kernel e he
    72 1700 31 14 98 131071 cutoff (by omega) hb hs hu ht hc nodes u0 u1 627003341034 hcard
  letI : Module.Finite K V := hfinite
  have hbounds : ∀ P∈V, Bounds P := by
    intro P hP d hd
    obtain ⟨i,rfl⟩ := hsupport P hP d hd
    exact ⟨hb i,hs i,hu i,ht i,hc i⟩
  obtain ⟨P,hP,hnot⟩ := WholeSpaceTrimmedPowerBox6814.exists_not_dvd_power_trimmed V hdim
    (fun P hP => (weights_of_bounds P (hbounds P hP)).1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.1)
    (fun P hP => (weights_of_bounds P (hbounds P hP)).2.2.2.1)
    J hJ a ha hgood.1 hgood.2
  exact ⟨P,by intro hz; exact hnot (by rw [hz]; exact dvd_zero _),hnot,hbounds P hP,hcontact P hP⟩

theorem exists_interpolant_not_dvd_power (nodes : N ↪ K) (u0 u1 : N → K)
    (hN : Fintype.card N=262144) (J : Poly (K := K)) (hJ : J≠0) (a : Box)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J))
    (hgood : WholeSpaceTrimmedReceipts6814.Good a) :
    ∃ P : Poly (K := K), P≠0 ∧ ¬J^a.q∣P ∧ Bounds P ∧
      ∀ i, MvPolynomial.X 0^72 ∣ SecondJetDifferentiation.substitute (K := K)
        (localize (nodes i) (u0 i) (u1 i) P) := by
  apply contact_not_power_generic
    (SecondJetRelaxedGlobalIndex.exponent (D := cutoff) (w := 131071) (L := 1700)
      (B := 31) (s := 14) (U := 98))
    (SecondJetRelaxedGlobalIndex.exponent_injective cutoff 131071 1700 31 14 98)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.2.1)
    (fun i => (SecondJetRelaxedGlobalIndex.exponent_bounds cutoff 131071 1700 31 14 98 (by omega) i).2.2.2.2)
    nodes u0 u1 ?_ J hJ a ha hgood
  simpa only [hN] using source_nullity

open WholeSpacePowerSupplier6814 MovingSourceNativeEnvelope6814 WholeSpaceSourceAlternative6814
open WholeSpaceUniqueOwnerAlternative6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingSourceOwnerSplit6814 MovingSourceMixedOwnerRouting6814
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open SecondJetCoefficients SecondJetCarrierDichotomy RCN234 RCN156
variable {E : Type} [Field E] [CharP K 2130706433] [CharP E 2130706433]

theorem helper_or_weighted_pair_of_trimmed_box
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : Poly (K := K)) (hJi : Irreducible J) (m : ℕ) (hm : 0<m)
    (a : Box) (haq : a.q=copies3 m)
    (ha : a.Covers (weightedTotalDegree slopeWeights J)
      (weightedTotalDegree middleWeights J) (weightedTotalDegree totalWeights J)) (hgood : WholeSpaceTrimmedReceipts6814.Good a)
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

#print axioms exists_interpolant_not_dvd_power
#print axioms helper_or_weighted_pair_of_trimmed_box
end
end ProximityPrize.SubmissionLower.WholeSpaceTrimmedSupplier6814
