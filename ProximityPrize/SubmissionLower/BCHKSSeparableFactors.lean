import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate
open scoped BigOperators

set_option linter.constructorNameAsVariable false

/-- . -/
local instance concreteFieldChar :
    CharP ProximityPrize.Benchmark.IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- . -/
theorem derivative_ne_zero_of_pos_natDegree_lt_char
    {K : Type} [Field K] (p : ℕ) [CharP K p] (R : K[X])
    (hpos : 0 < R.natDegree) (hlt : R.natDegree < p) : R.derivative ≠ 0 := by
  intro hzero
  have hc := congrArg (fun f : K[X] => f.coeff (R.natDegree - 1)) hzero
  rw [coeff_derivative] at hc
  have hsucc : R.natDegree - 1 + 1 = R.natDegree := by omega
  rw [hsucc] at hc
  have hcastSucc : ((R.natDegree - 1 : ℕ) : K) + 1 = (R.natDegree : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℕ => (z : K)) hsucc
  rw [hcastSucc, coeff_natDegree] at hc
  simp only [coeff_zero] at hc
  have hcast : (R.natDegree : K) ≠ 0 := by
    intro hz
    have hdvd : p ∣ R.natDegree := (CharP.cast_eq_zero_iff K p R.natDegree).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
  have hR : R ≠ 0 := by
    intro hz
    simp [hz] at hpos
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hR) hcast) hc

/-- . -/
theorem irreducible_isCoprime_derivative_of_natDegree_lt_char
    {K : Type} [Field K] (p : ℕ) [CharP K p] (R : K[X])
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hlt : R.natDegree < p) :
    IsCoprime R R.derivative := by
  have hdne := derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
  have hddeg : R.derivative.natDegree < R.natDegree :=
    natDegree_derivative_lt (ne_of_gt hpos)
  have hnotdvd : ¬ R ∣ R.derivative := by
    intro hdvd
    have hle := natDegree_le_of_dvd hdvd hdne
    omega
  by_contra hnot
  exact hnotdvd ((hirr.dvd_iff_not_isCoprime).2 hnot)

/-- . -/
theorem irreducible_resultant_derivative_ne_zero_of_natDegree_lt_char
    {K : Type} [Field K] (p : ℕ) [CharP K p] (R : K[X])
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hlt : R.natDegree < p) :
    R.resultant R.derivative ≠ 0 := by
  intro hz
  have hc := (Polynomial.resultant_eq_zero_iff.mp hz).2
  exact hc (irreducible_isCoprime_derivative_of_natDegree_lt_char p R hirr hpos hlt)

/-- . -/
theorem monic_irreducible_discr_ne_zero_of_natDegree_lt_char
    {K : Type} [Field K] (p : ℕ) [CharP K p] (R : K[X])
    (hmonic : R.Monic) (hirr : Irreducible R)
    (hpos : 0 < R.natDegree) (hlt : R.natDegree < p) : R.discr ≠ 0 := by
  have hcop := irreducible_isCoprime_derivative_of_natDegree_lt_char p R hirr hpos hlt
  have hdne := derivative_ne_zero_of_pos_natDegree_lt_char p R hpos hlt
  have hddeg : R.derivative.natDegree = R.natDegree - 1 := by
    apply le_antisymm (Polynomial.natDegree_derivative_le R)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative]
    have hs : R.natDegree - 1 + 1 = R.natDegree := by omega
    rw [hs]
    have hcastSucc : ((R.natDegree - 1 : ℕ) : K) + 1 = (R.natDegree : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℕ => (z : K)) hs
    rw [hcastSucc, Polynomial.coeff_natDegree]
    have hcast : (R.natDegree : K) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hpos hlt)
        ((CharP.cast_eq_zero_iff K p R.natDegree).mp hz)
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero) hcast
  have hres : R.resultant R.derivative R.natDegree (R.natDegree - 1) ≠ 0 := by
    simpa [hddeg] using
      irreducible_resultant_derivative_ne_zero_of_natDegree_lt_char p R hirr hpos hlt
  have hdegree : 0 < R.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hpos
  have hrel := Polynomial.resultant_deriv (f := R) hdegree
  rw [hmonic.leadingCoeff, mul_one] at hrel
  intro hz
  rw [hz, mul_zero] at hrel
  exact hres hrel

/-- .
 -/
theorem monic_discr_ne_zero_of_fraction_irreducible
    {A K : Type} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [CharP A p] (R : A[X]) (hmonic : R.Monic)
    (hirrK : Irreducible (R.map (algebraMap A K)))
    (hpos : 0 < R.natDegree) (hlt : R.natDegree < p) : R.discr ≠ 0 := by
  letI : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective A K) p
  let f : A →+* K := algebraMap A K
  let RK : K[X] := R.map f
  have hdeg : RK.natDegree = R.natDegree := hmonic.natDegree_map f
  have hposK : 0 < RK.natDegree := by simpa [hdeg]
  have hltK : RK.natDegree < p := by simpa [hdeg]
  have hcopK := irreducible_isCoprime_derivative_of_natDegree_lt_char p RK hirrK hposK hltK
  have hresK : RK.resultant RK.derivative ≠ 0 := by
    intro hz
    exact (Polynomial.resultant_eq_zero_iff.mp hz).2 hcopK
  have hddegK : RK.derivative.natDegree = RK.natDegree - 1 := by
    apply le_antisymm (Polynomial.natDegree_derivative_le RK)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative]
    have hs : RK.natDegree - 1 + 1 = RK.natDegree := by omega
    rw [hs]
    have hcastSucc : ((RK.natDegree - 1 : ℕ) : K) + 1 = (RK.natDegree : K) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun z : ℕ => (z : K)) hs
    rw [hcastSucc, Polynomial.coeff_natDegree]
    have hcast : (RK.natDegree : K) ≠ 0 := by
      intro hz
      exact (Nat.not_dvd_of_pos_of_lt hposK hltK)
        ((CharP.cast_eq_zero_iff K p RK.natDegree).mp hz)
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hirrK.ne_zero) hcast
  have hresKfixed : RK.resultant RK.derivative R.natDegree (R.natDegree - 1) ≠ 0 := by
    simpa [hdeg, hddegK] using hresK
  have hresRaw : R.resultant R.derivative R.natDegree (R.natDegree - 1) ≠ 0 := by
    intro hz
    apply hresKfixed
    dsimp [RK]
    rw [Polynomial.derivative_map]
    rw [Polynomial.resultant_map_map]
    simpa using congrArg f hz
  have hdegree : 0 < R.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hpos
  have hrel := Polynomial.resultant_deriv (f := R) hdegree
  rw [hmonic.leadingCoeff, mul_one] at hrel
  intro hzero
  rw [hzero, mul_zero] at hrel
  exact hresRaw hrel

/-- . -/
theorem degreeX_derivative_le {F : Type} [Field F] (R : F[X][Y]) :
    degreeX R.derivative ≤ degreeX R := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro j hj
  rw [Polynomial.coeff_derivative]
  calc
    (R.coeff (j + 1) * (j + 1 : F[X])).natDegree ≤
        (R.coeff (j + 1)).natDegree + ((j + 1 : F[X])).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ degreeX R := by
      have hn : ((j : F[X]) + 1).natDegree = 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add, Polynomial.natDegree_natCast]
      rw [hn, Nat.add_zero]
      exact Polynomial.Bivariate.coeff_natDegree_le_degreeX R (j + 1)

/-- .
 -/
theorem discr_natDegree_le {F : Type} [Field F] (R : F[X][Y])
    (hmonic : R.Monic) (hpos : 0 < R.natDegree) :
    R.discr.natDegree ≤ (2 * R.natDegree - 1) * degreeX R := by
  let d := R.natDegree
  let S := R.resultant R.derivative d (d - 1)
  have hSdeg : S.natDegree ≤ (d - 1) * degreeX R + d * degreeX R.derivative := by
    exact ps_nat_degree_resultant_le R.derivative R (d - 1) d
  have hSdeg' : S.natDegree ≤ (2 * d - 1) * degreeX R := by
    calc
      S.natDegree ≤ (d - 1) * degreeX R + d * degreeX R.derivative := hSdeg
      _ ≤ (d - 1) * degreeX R + d * degreeX R := by
        gcongr
        exact degreeX_derivative_le R
      _ = ((d - 1) + d) * degreeX R := by ring
      _ = (2 * d - 1) * degreeX R := by
        congr 1
        dsimp [d]
        omega
  have hdegree : 0 < R.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hpos
  have hrel := Polynomial.resultant_deriv (f := R) hdegree
  rw [hmonic.leadingCoeff, mul_one] at hrel
  by_cases hd : R.discr = 0
  · simp [hd]
  · have hu : ((-1 : F[X]) ^ (d * (d - 1) / 2)) ≠ 0 := pow_ne_zero _ (by simp)
    have heqdeg : S.natDegree = R.discr.natDegree := by
      rw [show S = (-1) ^ (d * (d - 1) / 2) * R.discr by simpa [S, d] using hrel,
        Polynomial.natDegree_mul hu hd]
      simp
    rw [← heqdeg]
    exact hSdeg'

/-- .
 -/
theorem sum_discr_natDegree_le {F ρ : Type} [Field F] [DecidableEq ρ]
    (S : Finset ρ) (R : ρ → F[X][Y])
    (hmonic : ∀ r ∈ S, (R r).Monic)
    (hpos : ∀ r ∈ S, 0 < (R r).natDegree) :
    (∑ r ∈ S, (R r).discr.natDegree) ≤
      ∑ r ∈ S, (2 * (R r).natDegree - 1) * degreeX (R r) := by
  apply Finset.sum_le_sum
  intro r hr
  exact discr_natDegree_le (R r) (hmonic r hr) (hpos r hr)

/-- .

 -/
theorem exists_good_x_of_discriminants
    {F ρ : Type} [Field F] [Fintype F] [DecidableEq ρ]
    (S : Finset ρ) (R : ρ → F[X][Y])
    (hne : ∀ r ∈ S, (R r).discr ≠ 0)
    (hdeg : (∑ r ∈ S, (R r).discr.natDegree) < Fintype.card F) :
    ∃ x₀ : F, ∀ r ∈ S, Polynomial.eval x₀ (R r).discr ≠ 0 := by
  classical
  let P : F[X] := ∏ r ∈ S, (R r).discr
  have hPne : P ≠ 0 := by
    change (∏ r ∈ S, (R r).discr) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    exact hne
  have hPdeg : P.natDegree < Fintype.card F := by
    exact (Polynomial.natDegree_prod_le S (fun r => (R r).discr)).trans_lt hdeg
  by_contra hgood
  push Not at hgood
  have hPeval : ∀ x : F, P.eval x = 0 := by
    intro x
    obtain ⟨r, hr, hz⟩ := hgood x
    change Polynomial.eval x (∏ r ∈ S, (R r).discr) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hr hz
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P Function.injective_id hPeval hPdeg
  exact hPne hzero

end ProximityPrize.SubmissionLower
