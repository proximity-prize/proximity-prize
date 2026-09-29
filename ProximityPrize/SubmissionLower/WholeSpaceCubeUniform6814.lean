import ProximityPrize.SubmissionLower.WholeSpaceCube6814

/-! A single enlarged interpolation space excludes the remaining quadratic
fixed cubes uniformly. No enumeration of candidate polynomials is used. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped BigOperators
open MvPolynomial WholeSpaceCube6814

variable {K : Type*} [Field K]
def slopeWeights : Fin 5 → ℕ := ![0,2,0,1,0]

theorem factor_lower (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9) :
    3276766 ≤ weightedTotalDegree codeWeights J ∧
      25 ≤ weightedTotalDegree totalWeights J := by
  obtain ⟨e,he,hmax⟩ := Finset.exists_mem_eq_sup J.support (support_nonempty.mpr hJ)
    (Finsupp.weight middleWeights)
  have hmid : 25 ≤ Finsupp.weight middleWeights e := by
    change 25 ≤ J.support.sup (Finsupp.weight middleWeights) at hm
    rwa [hmax] at hm
  have hB := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans_eq hb
  have hc0 : Finsupp.weight codeWeights e ≤ weightedTotalDegree codeWeights J := Finset.le_sup he
  have ht0 : Finsupp.weight totalWeights e ≤ weightedTotalDegree totalWeights J := Finset.le_sup he
  have hc : e 0+131069*e 1+131071*e 2+131070*e 3 ≤ weightedTotalDegree codeWeights J := by
    simpa [weight_coords,codeWeights,Nat.mul_comm] using hc0
  have ht : e 1+e 2+e 3+e 4 ≤ weightedTotalDegree totalWeights J := by
    simpa [weight_coords,totalWeights] using ht0
  have hm' : 25 ≤ e 1+e 2+e 3 := by simpa [weight_coords,middleWeights] using hmid
  have hb' : 2*e 1+e 3 ≤ 9 := by simpa [weight_coords,slopeWeights,Nat.mul_comm] using hB
  constructor <;> omega

theorem quotient_bounds_uniform (J Q : Poly (K := K)) (hJ : J≠0) (hQ : Q≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9)
    (hcode : weightedTotalDegree codeWeights (J^3*Q) < 13050360)
    (htotal : weightedTotalDegree totalWeights (J^3*Q) ≤ 1700)
    (hmiddle : weightedTotalDegree middleWeights (J^3*Q) ≤ 98)
    (hslope : weightedTotalDegree slopeWeights (J^3*Q) ≤ 31) :
    weightedTotalDegree codeWeights Q < 3220062 ∧
      weightedTotalDegree totalWeights Q ≤ 1625 ∧
      weightedTotalDegree middleWeights Q ≤ 23 ∧
      weightedTotalDegree slopeWeights Q ≤ 4 := by
  have hl := factor_lower J hJ hm hb
  rw [weight_mul _ _ _ (pow_ne_zero _ hJ) hQ,weight_pow _ _ hJ] at hcode htotal hmiddle hslope
  rw [hb] at hslope
  omega

abbrev QuotientIndex :=
  Σ s : Fin 3, Σ r : Fin (5-2*s.val), Σ y : Fin 24,
    Fin (3220062-131071*y.val) × Fin 1626

def quotientExponent (i : QuotientIndex) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem coefficient_count :
    (∑ y : Fin 24, (3220062-131071*y.val)) = 41105892 := by
  norm_num [Fin.sum_univ_succ]

theorem quotient_card : Fintype.card QuotientIndex=601543623528 := by
  simp only [QuotientIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  simp only [←Finset.sum_mul,coefficient_count,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  norm_num [Fin.sum_univ_succ]

theorem quotient_support_uniform (Q : Poly (K := K))
    (hb : weightedTotalDegree codeWeights Q < 3220062 ∧
      weightedTotalDegree totalWeights Q ≤ 1625 ∧
      weightedTotalDegree middleWeights Q ≤ 23 ∧
      weightedTotalDegree slopeWeights Q ≤ 4) :
    ∀ e ∈ Q.support, e ∈ Set.range quotientExponent := by
  intro e he
  have hc := (Finset.le_sup (f := Finsupp.weight codeWeights) he).trans_lt hb.1
  have ht := (Finset.le_sup (f := Finsupp.weight totalWeights) he).trans hb.2.1
  have hm := (Finset.le_sup (f := Finsupp.weight middleWeights) he).trans hb.2.2.1
  have hs := (Finset.le_sup (f := Finsupp.weight slopeWeights) he).trans hb.2.2.2
  simp [weight_coords,codeWeights,totalWeights,middleWeights,slopeWeights] at hc ht hm hs
  refine ⟨⟨⟨e 1,by omega⟩,⟨e 3,?_⟩,⟨e 2,by omega⟩,
    ⟨e 0,?_⟩,⟨e 4,by omega⟩⟩,?_⟩
  · change e 3 < 5-2*e 1
    omega
  · change e 0 < 3220062-131071*e 2
    omega
  · ext i
    fin_cases i <;> simp [quotientExponent]

/-- Uniform whole-space avoidance. The hypotheses are source support and
nullity, not a desired counting bound or an assumed coprime source. -/
theorem exists_not_dvd_cube_uniform
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034 ≤ Module.finrank K V)
    (hcode : ∀ P ∈ V, weightedTotalDegree codeWeights P < 13050360)
    (htotal : ∀ P ∈ V, weightedTotalDegree totalWeights P ≤ 1700)
    (hmiddle : ∀ P ∈ V, weightedTotalDegree middleWeights P ≤ 98)
    (hslope : ∀ P ∈ V, weightedTotalDegree slopeWeights P ≤ 31)
    (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9) :
    ∃ P ∈ V, ¬ J^3 ∣ P := by
  classical
  by_contra hno
  have hdiv : ∀ P ∈ V, J^3 ∣ P := by simpa only [not_exists,not_and,not_not] using hno
  let hd : ∀ v : V, J^3 ∣ v.val := fun v => hdiv v.val v.property
  let f := cubeQuotientLinear V J hJ hd
  have hf : Function.Injective f := by
    intro v u he
    apply Subtype.ext
    rw [cubeQuotient_spec V J hd v,cubeQuotient_spec V J hd u]
    exact congrArg (fun Q => J^3*Q) he
  have hs : ∀ v : V, ∀ e ∈ (f v).support, e ∈ Set.range quotientExponent := by
    intro v e he
    have hq : f v ≠ 0 := by intro hz; simpa [hz] using he
    have hv : v.val=J^3*f v := cubeQuotient_spec V J hd v
    have hh := quotient_bounds_uniform J (f v) hJ hq hm hb
      (by rw [←hv]; exact hcode v.val v.property)
      (by rw [←hv]; exact htotal v.val v.property)
      (by rw [←hv]; exact hmiddle v.val v.property)
      (by rw [←hv]; exact hslope v.val v.property)
    exact quotient_support_uniform (f v) hh e he
  have hh := finrank_le_coefficients quotientExponent f hf hs
  rw [quotient_card] at hh
  omega

theorem remainder_of_not_cube (J P : Poly (K := K)) (h : ¬ J^3 ∣ P) :
    ∃ e < 3, ∃ Q, P=J^e*Q ∧ ¬ J ∣ Q := by
  by_cases h1 : J ∣ P
  · obtain ⟨Q1,h1⟩ := h1
    by_cases h2 : J ∣ Q1
    · obtain ⟨Q2,h2⟩ := h2
      refine ⟨2,by omega,Q2,?_,?_⟩
      · rw [h1,h2]; ring
      · rintro ⟨Q3,h3⟩
        apply h
        refine ⟨Q3,?_⟩
        rw [h1,h2,h3]; ring
    · exact ⟨1,by omega,Q1,by simpa using h1,h2⟩
  · exact ⟨0,by omega,P,by simp,h1⟩

/-- Whole-space avoidance followed by the exact field-root handoff.
The output cofactor remains a curvature relation and no longer contains
J. In the application J is primitive irreducible, so this is the proper
pair needed by the new count; clearing/geometry is not assumed here. -/
theorem exists_root_remainder_uniform
    {E : Type*} [Field E]
    (V : Submodule K (Poly (K := K))) [Module.Finite K V]
    (hdim : 627003341034 ≤ Module.finrank K V)
    (hcode : ∀ P ∈ V, weightedTotalDegree codeWeights P < 13050360)
    (htotal : ∀ P ∈ V, weightedTotalDegree totalWeights P ≤ 1700)
    (hmiddle : ∀ P ∈ V, weightedTotalDegree middleWeights P ≤ 98)
    (hslope : ∀ P ∈ V, weightedTotalDegree slopeWeights P ≤ 31)
    (hsdegree : ∀ P ∈ V, P.degreeOf 1 ≤ 14)
    (J : Poly (K := K)) (hJ : J≠0)
    (hm : 25 ≤ weightedTotalDegree middleWeights J)
    (hb : weightedTotalDegree slopeWeights J=9)
    (phi : Poly (K := K) →+* Polynomial E) (sigma : E)
    (hphi : phi J ≠ 0) (hroot : (phi J).rootMultiplicity sigma=1)
    (hret : ∀ P ∈ V, (Polynomial.X-Polynomial.C sigma)^3 ∣ phi P) :
    ∃ P ∈ V, P≠0 ∧ ∃ e < 3, ∃ Q : Poly (K := K),
      P=J^e*Q ∧ ¬ J ∣ Q ∧ (phi Q).eval sigma=0 ∧
      weightedTotalDegree totalWeights Q ≤ 1700 ∧
      weightedTotalDegree middleWeights Q ≤ 98 ∧
      weightedTotalDegree slopeWeights Q ≤ 31 ∧ Q.degreeOf 1 ≤ 14 := by
  obtain ⟨P,hP,hnot⟩ := exists_not_dvd_cube_uniform V hdim hcode htotal hmiddle hslope J hJ hm hb
  have hP0 : P≠0 := by
    intro hz
    exact hnot (by rw [hz]; exact dvd_zero _)
  obtain ⟨e,he,Q,hPQ,hJQ⟩ := remainder_of_not_cube J P hnot
  have hQ0 : Q≠0 := by intro hz; exact hJQ (by rw [hz]; exact dvd_zero _)
  have hrootQ : (phi Q).eval sigma=0 := by
    by_contra hval
    have hpower := hret P hP
    rw [hPQ,map_mul,map_pow] at hpower
    have hh := UniqueCurvatureOwner6814.simple_unique_owner_exponent
      (phi J) (phi Q) sigma 3 e hphi hval hroot hpower
    omega
  have hw (w : Fin 5 → ℕ) (C : ℕ) (hc : weightedTotalDegree w P ≤ C) :
      weightedTotalDegree w Q ≤ C := by
    rw [hPQ,weight_mul w _ _ (pow_ne_zero _ hJ) hQ0] at hc
    omega
  have hd := hsdegree P hP
  rw [hPQ,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hJ) hQ0] at hd
  exact ⟨P,hP,hP0,e,he,Q,hPQ,hJQ,hrootQ,
    hw _ _ (htotal P hP),hw _ _ (hmiddle P hP),hw _ _ (hslope P hP),by omega⟩

open RCN095 UniqueCurvatureOwner6814

theorem enlarged_source_pair_prices (u t : ℕ)
    (hu : 25 ≤ u) (hu30 : u ≤ 30) (hut : u ≤ t) (ht331 : t ≤ 331) :
    flagMixed ⟨t-u,u-7,9⟩ ⟨1602,81,31⟩ unitZFlag ≤ 1721 ∧
    flagMixed ⟨t-u,u-7,9⟩ ⟨1602,81,31⟩ unitYZFlag ≤ 25470 ∧
    flagMixed ⟨t-u,u-7,9⟩ ⟨1602,81,31⟩ unitAllFlag ≤ 88560 := by
  have ht := Nat.sub_add_cancel hut
  have hy : u-7+7=u := Nat.sub_add_cancel (by omega)
  norm_num [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  omega

theorem enlarged_source_main_fits :
    checkedMain (4491/7) 25470 88560 < 272069082261391681 ∧
    (272069082261391681 : ℚ)-checkedMain (4491/7) 25470 88560 = 56172124121380153/7 := by
  norm_num [checkedMain]

theorem lower_weight_quadratic_main_fits :
    checkedMain 630 25266 (223743/2) < 272069082261391681 ∧
    checkedMain 603 28815 102963 < 272069082261391681 := by
  norm_num [checkedMain]

#print axioms quotient_card
#print axioms exists_not_dvd_cube_uniform
#print axioms exists_root_remainder_uniform
#print axioms enlarged_source_pair_prices
#print axioms enlarged_source_main_fits
end
end ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
