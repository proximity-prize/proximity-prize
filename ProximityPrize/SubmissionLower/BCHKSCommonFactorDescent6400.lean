import ProximityPrize.SubmissionLower.BCHKSTwoAxisResultant6400

/-!
# Integral common-factor descent from either resultant axis

This module converts the zero-resultant alternative into a genuine bivariate
factor over the original polynomial ring.  The coordinate-axis alternative
first produces a factor after swapping variables.  Primitivity of the
homogeneous factor then rules out the possibility that this factor is only a
challenge polynomial.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSCommonFactorDescent6400

open Polynomial
open Polynomial.Bivariate
open BCHKSTwoAxisResultant6400

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-- When only the right declared Sylvester degree is padded, vanishing of the
fixed resultant implies vanishing of the ordinary resultant.  Exactness of
the left degree makes its padding multiplier nonzero. -/
theorem ordinary_resultant_eq_zero_of_fixed_right_padded
    {A : Type} [CommRing A] [IsDomain A]
    (H Q : A[X]) (d n : Nat) (hH : H ≠ 0)
    (hHd : H.natDegree = d) (hQn : Q.natDegree ≤ n)
    (hfixed : Polynomial.resultant H Q d n = 0) :
    Polynomial.resultant H Q = 0 := by
  by_contra hstandard
  have hn : Q.natDegree + (n - Q.natDegree) = n :=
    Nat.add_sub_of_le hQn
  have hlc : H.coeff H.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hH
  have hnonzero :
      Polynomial.resultant H Q H.natDegree
        (Q.natDegree + (n - Q.natDegree)) ≠ 0 := by
    rw [Polynomial.resultant_add_right_deg]
    · exact mul_ne_zero (pow_ne_zero _ hlc) hstandard
    · exact le_rfl
  rw [hHd, hn] at hnonzero
  exact hnonzero hfixed

/-- If a factor is a unit multiple of the full gcd, then the residual factors
are coprime.  Keeping this Euclidean-domain algebra independent of polynomial
coefficient maps makes the integral instantiation inexpensive to elaborate. -/
theorem isCoprime_quotients_of_eq_unit_mul_gcd
    {R : Type} [EuclideanDomain R] [DecidableEq R]
    (H Q K H' Q' u : R) (hHne : H ≠ 0) (hu : IsUnit u)
    (hK : K = u * EuclideanDomain.gcd H Q)
    (hHfactor : H = K * H') (hQfactor : Q = K * Q') :
    IsCoprime H' Q' := by
  letI := EuclideanDomain.gcdMonoid R
  let G : R := EuclideanDomain.gcd H Q
  have hGne : G ≠ 0 := gcd_ne_zero_of_left hHne
  have hGdivH : G ∣ H := EuclideanDomain.gcd_dvd_left H Q
  have hGdivQ : G ∣ Q := EuclideanDomain.gcd_dvd_right H Q
  have hHquotient : H / G = u * H' := by
    apply mul_left_cancel₀ hGne
    rw [EuclideanDomain.mul_div_cancel' hGne hGdivH]
    calc
      H = K * H' := hHfactor
      _ = (u * G) * H' := by rw [hK]
      _ = G * (u * H') := by ac_rfl
  have hQquotient : Q / G = u * Q' := by
    apply mul_left_cancel₀ hGne
    rw [EuclideanDomain.mul_div_cancel' hGne hGdivQ]
    calc
      Q = K * Q' := hQfactor
      _ = (u * G) * Q' := by rw [hK]
      _ = G * (u * Q') := by ac_rfl
  have hcoprimeDiv : IsCoprime (H / G) (Q / G) :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hGne
  apply (isCoprime_mul_unit_left hu H' Q').mp
  rw [← hHquotient, ← hQquotient]
  exact hcoprimeDiv

/-- `K` is, up to a nonzero scalar, the full gcd of `H` and `Q` after
extending coefficients from `F[Z]` to its fraction field. -/
noncomputable def IsFullFractionGCDLift {F : Type} [Field F]
    (K H Q : F[X][X]) : Prop := by
  classical
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  exact ∃ c : FractionRing F[X], c ≠ 0 ∧
    K.map f = Polynomial.C c *
      EuclideanDomain.gcd (H.map f) (Q.map f)

/-- A zero ordinary resultant over `F[Z]` yields a primitive integral lift of
the full gcd over `F(Z)`.  The compact full-gcd certificate is separated from
the quotient construction so the latter elaborates with a fresh heartbeat
budget. -/
theorem exists_integralPrimitiveFullGCD_of_resultant_eq_zero
    {F : Type} [Field F]
    (H Q : F[X][X]) (hH : H ≠ 0)
    (hresultant : Polynomial.resultant H Q = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ H ∧ K ∣ Q ∧
      IsFullFractionGCDLift K H Q := by
  classical
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  let KH : Polynomial (FractionRing F[X]) := H.map f
  let KQ : Polynomial (FractionRing F[X]) := Q.map f
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hHdegree : KH.natDegree = H.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf H
  have hQdegree : KQ.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have hfixed :
      Polynomial.resultant KH KQ H.natDegree Q.natDegree = 0 := by
    rw [Polynomial.resultant_map_map]
    simpa using congrArg f hresultant
  have hresK : Polynomial.resultant KH KQ = 0 := by
    simpa only [hHdegree, hQdegree] using hfixed
  have hcriterion := Polynomial.resultant_eq_zero_iff.mp hresK
  have hnotcoprime : ¬ IsCoprime KH KQ := hcriterion.2
  have hKHne : KH ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hf).2 hH
  let G : Polynomial (FractionRing F[X]) := EuclideanDomain.gcd KH KQ
  have hGdivH : G ∣ KH := EuclideanDomain.gcd_dvd_left KH KQ
  have hGdivQ : G ∣ KQ := EuclideanDomain.gcd_dvd_right KH KQ
  have hGnotUnit : ¬ IsUnit G := by
    intro hunit
    exact hnotcoprime (EuclideanDomain.gcd_isUnit_iff.mp hunit)
  have hGne : G ≠ 0 := by
    intro hzero
    apply hKHne
    simpa [hzero] using hGdivH
  have hGdegreeNe : G.degree ≠ 0 := by
    intro hdegree
    exact hGnotUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree)
  have hGnatDegreeNe : G.natDegree ≠ 0 := by
    intro hdegree
    apply hGdegreeNe
    rw [Polynomial.degree_eq_natDegree hGne, hdegree]
    simp
  have hGpositive : 0 < G.natDegree := Nat.pos_of_ne_zero hGnatDegreeNe
  let q : F[X][X] := IsLocalization.integerNormalization
    (nonZeroDivisors F[X]) G
  let K : F[X][X] := q.primPart
  have hqne : q ≠ 0 := by
    intro hzero
    apply hGne
    exact IsFractionRing.integerNormalization_eq_zero_iff.mp hzero
  have hcontentNe : q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  obtain ⟨b, hbmem, hqmap⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors F[X]) G
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hfbne : f b ≠ 0 := fun hzero ↦
    hbne (hf (by simpa using hzero))
  have hfcne : f q.content ≠ 0 := fun hzero ↦
    hcontentNe (hf (by simpa using hzero))
  have hproduct :
      Polynomial.C (f q.content) * K.map f = Polynomial.C (f b) * G := by
    calc
      Polynomial.C (f q.content) * K.map f = q.map f := by
        dsimp only [K]
        rw [← Polynomial.map_C, ← Polynomial.map_mul]
        exact congrArg (Polynomial.map f)
          q.eq_C_content_mul_primPart.symm
      _ = b • G := hqmap
      _ = Polynomial.C (f b) * G := by
        rw [Algebra.smul_def]
        rfl
  let c : FractionRing F[X] := f b / f q.content
  have hcne : c ≠ 0 := div_ne_zero hfbne hfcne
  have hscale : K.map f = Polynomial.C c * G := by
    apply mul_left_cancel₀
      (show Polynomial.C (f q.content) ≠ 0 by simpa using hfcne)
    rw [hproduct]
    have hfc : f q.content * c = f b := by
      dsimp [c]
      exact mul_div_cancel₀ _ hfcne
    calc
      Polynomial.C (f b) * G =
          Polynomial.C (f q.content * c) * G := by rw [hfc]
      _ = Polynomial.C (f q.content) *
          (Polynomial.C c * G) := by rw [Polynomial.C_mul, mul_assoc]
  have hKprimitive : K.IsPrimitive := q.isPrimitive_primPart
  have hKdegree : K.natDegree = G.natDegree := by
    calc
      K.natDegree = (K.map f).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hf K).symm
      _ = (Polynomial.C c * G).natDegree := congrArg _ hscale
      _ = G.natDegree := Polynomial.natDegree_C_mul hcne
  have hKmapDivH : K.map f ∣ H.map f := by
    rcases hGdivH with ⟨D, hD⟩
    refine ⟨Polynomial.C c⁻¹ * D, ?_⟩
    calc
      H.map f = G * D := hD
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * D) := by ring
          _ = G * D := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = K.map f * (Polynomial.C c⁻¹ * D) := by rw [hscale]
  have hKmapDivQ : K.map f ∣ Q.map f := by
    rcases hGdivQ with ⟨D, hD⟩
    refine ⟨Polynomial.C c⁻¹ * D, ?_⟩
    calc
      Q.map f = G * D := hD
      _ = (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) := by
        symm
        calc
          (Polynomial.C c * G) * (Polynomial.C c⁻¹ * D) =
              (Polynomial.C c * Polynomial.C c⁻¹) * (G * D) := by ring
          _ = G * D := by
            rw [← Polynomial.C_mul, mul_inv_cancel₀ hcne,
              Polynomial.C_1, one_mul]
      _ = K.map f * (Polynomial.C c⁻¹ * D) := by rw [hscale]
  have hKdivH : K ∣ H :=
    hKprimitive.dvd_of_fraction_map_dvd_fraction_map hKmapDivH
  have hKdivQ : K ∣ Q :=
    hKprimitive.dvd_of_fraction_map_dvd_fraction_map hKmapDivQ
  refine ⟨K, hKprimitive, hKdegree ▸ hGpositive, hKdivH, hKdivQ, ?_⟩
  refine ⟨c, hcne, ?_⟩
  simpa only [f, KH, KQ, G] using hscale

/-- Cancelling the full primitive gcd leaves integral quotient lanes that
are coprime over the fraction field. -/
theorem exists_integralPrimitiveGCD_of_resultant_eq_zero
    {F : Type} [Field F]
    (H Q : F[X][X]) (hH : H ≠ 0)
    (hresultant : Polynomial.resultant H Q = 0) :
    ∃ K H' Q' : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧
      H = K * H' ∧ Q = K * Q' ∧
      IsCoprime
        (H'.map (algebraMap F[X] (FractionRing F[X])))
        (Q'.map (algebraMap F[X] (FractionRing F[X]))) := by
  classical
  obtain ⟨K, hKprimitive, hKpositive, hKdivH, hKdivQ, hfull⟩ :=
    exists_integralPrimitiveFullGCD_of_resultant_eq_zero H Q hH hresultant
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  change ∃ c : FractionRing F[X], c ≠ 0 ∧
    K.map f = Polynomial.C c *
      EuclideanDomain.gcd (H.map f) (Q.map f) at hfull
  obtain ⟨c, hcne, hscale⟩ := hfull
  let H' : F[X][X] := Classical.choose hKdivH
  let Q' : F[X][X] := Classical.choose hKdivQ
  have hHfactor : H = K * H' := Classical.choose_spec hKdivH
  have hQfactor : Q = K * Q' := Classical.choose_spec hKdivQ
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hHmapne : H.map f ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff hf).2 hH
  have hHmapfactor : H.map f = K.map f * H'.map f := by
    rw [hHfactor, Polynomial.map_mul]
  have hQmapfactor : Q.map f = K.map f * Q'.map f := by
    rw [hQfactor, Polynomial.map_mul]
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)
  have hcoprimeMapped : IsCoprime (H'.map f) (Q'.map f) :=
    isCoprime_quotients_of_eq_unit_mul_gcd
      (H.map f) (Q.map f) (K.map f) (H'.map f) (Q'.map f)
      (Polynomial.C c) hHmapne hCunit hscale hHmapfactor hQmapfactor
  refine ⟨K, H', Q', hKprimitive, hKpositive,
    hHfactor, hQfactor, ?_⟩
  simpa only [f] using hcoprimeMapped

/-- Compatibility wrapper retaining only the primitive common factor. -/
theorem exists_integralPrimitiveCommonFactor_of_resultant_eq_zero
    {F : Type} [Field F]
    (H Q : F[X][X]) (hH : H ≠ 0)
    (hresultant : Polynomial.resultant H Q = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ H ∧ K ∣ Q := by
  obtain ⟨K, H', Q', hKprimitive, hKpositive, hHfactor, hQfactor,
      _hcoprime⟩ :=
    exists_integralPrimitiveGCD_of_resultant_eq_zero H Q hH hresultant
  exact ⟨K, hKprimitive, hKpositive, ⟨H', hHfactor⟩,
    ⟨Q', hQfactor⟩⟩

/-- Symmetric form of integral common-factor descent.  It only requires that
the polynomial pair is nonzero, rather than privileging its first lane. -/
theorem exists_integralPrimitiveCommonFactor_of_resultant_eq_zero_of_pair_ne_zero
    {F : Type} [Field F]
    (A B : F[X][X]) (hne : A ≠ 0 ∨ B ≠ 0)
    (hresultant : Polynomial.resultant A B = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ A ∧ K ∣ B := by
  rcases hne with hA | hB
  · exact exists_integralPrimitiveCommonFactor_of_resultant_eq_zero
      A B hA hresultant
  · have hcommuted : Polynomial.resultant B A = 0 := by
      rw [Polynomial.resultant_comm, hresultant]
      simp
    obtain ⟨K, hKprimitive, hKpositive, hKdivB, hKdivA⟩ :=
      exists_integralPrimitiveCommonFactor_of_resultant_eq_zero
        B A hB hcommuted
    exact ⟨K, hKprimitive, hKpositive, hKdivA, hKdivB⟩

/-- Symmetric full-gcd descent.  Besides the primitive common factor, this
returns chosen integral quotient lanes whose fraction-field images are
coprime. -/
theorem exists_integralPrimitiveGCD_of_resultant_eq_zero_of_pair_ne_zero
    {F : Type} [Field F]
    (A B : F[X][X]) (hne : A ≠ 0 ∨ B ≠ 0)
    (hresultant : Polynomial.resultant A B = 0) :
    ∃ K A' B' : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧
      A = K * A' ∧ B = K * B' ∧
      IsCoprime
        (A'.map (algebraMap F[X] (FractionRing F[X])))
        (B'.map (algebraMap F[X] (FractionRing F[X]))) := by
  rcases hne with hA | hB
  · exact exists_integralPrimitiveGCD_of_resultant_eq_zero
      A B hA hresultant
  · have hcommuted : Polynomial.resultant B A = 0 := by
      rw [Polynomial.resultant_comm, hresultant]
      simp
    obtain ⟨K, B', A', hKprimitive, hKpositive, hBfactor, hAfactor,
        hcoprime⟩ :=
      exists_integralPrimitiveGCD_of_resultant_eq_zero
        B A hB hcommuted
    exact ⟨K, A', B', hKprimitive, hKpositive, hAfactor, hBfactor,
      hcoprime.symm⟩

/-- Fixed-degree owner-axis vanishing produces an integral common factor of
positive locator degree. -/
theorem exists_integralPrimitiveCommonFactor_of_fixed_resultant_eq_zero
    {F : Type} [Field F]
    (H Q : F[X][X]) (d n : Nat)
    (hH : H ≠ 0) (hHd : H.natDegree = d) (hQn : Q.natDegree ≤ n)
    (hfixed : Polynomial.resultant H Q d n = 0) :
    ∃ K : F[X][X],
      K.IsPrimitive ∧ 0 < K.natDegree ∧ K ∣ H ∧ K ∣ Q := by
  exact exists_integralPrimitiveCommonFactor_of_resultant_eq_zero
    H Q hH
      (ordinary_resultant_eq_zero_of_fixed_right_padded
        H Q d n hH hHd hQn hfixed)

/-- Coordinate-axis vanishing also gives a common factor of positive locator
degree.  A positive-degree swapped factor could otherwise become a
challenge-only constant after swapping back; primitivity of `H` excludes
that possibility. -/
theorem exists_positiveLocatorCommonFactor_of_swapped_fixed_resultant_eq_zero
    {F : Type} [Field F]
    (H Q : F[X][X]) (t u : Nat)
    (hHprimitive : H.IsPrimitive)
    (hHt : degreeX H = t) (hQu : degreeX Q ≤ u)
    (hfixed : Polynomial.resultant (swap H) (swap Q) t u = 0) :
    ∃ D : F[X][X],
      D.IsPrimitive ∧ 0 < D.natDegree ∧ D ∣ H ∧ D ∣ Q := by
  classical
  have hH : H ≠ 0 := hHprimitive.ne_zero
  have hswapH : swap H ≠ 0 := by
    simpa using swap.injective.ne hH
  have hswapHdegree : (swap H).natDegree = t := by
    change natDegreeY (swap H) = t
    exact (natDegreeY_swap H).trans hHt
  have hswapQdegree : (swap Q).natDegree ≤ u := by
    change natDegreeY (swap Q) ≤ u
    exact (natDegreeY_swap Q).trans_le hQu
  obtain ⟨K, hKprimitive, hKpositive, hKdivH, hKdivQ⟩ :=
    exists_integralPrimitiveCommonFactor_of_fixed_resultant_eq_zero
      (swap H) (swap Q) t u hswapH hswapHdegree hswapQdegree hfixed
  let D : F[X][X] := swap K
  have hDdivH : D ∣ H := by
    have hmap := _root_.map_dvd swap hKdivH
    simpa only [D, Polynomial.Bivariate.swap_swap_apply] using hmap
  have hDdivQ : D ∣ Q := by
    have hmap := _root_.map_dvd swap hKdivQ
    simpa only [D, Polynomial.Bivariate.swap_swap_apply] using hmap
  have hDprimitive : D.IsPrimitive :=
    Polynomial.isPrimitive_of_dvd hHprimitive hDdivH
  have hDpositive : 0 < D.natDegree := by
    by_contra hnot
    have hDdegree : D.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hDconst : D = Polynomial.C (D.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hDdegree.le
    have hCdivH : Polynomial.C (D.coeff 0) ∣ H := by
      simpa only [← hDconst] using hDdivH
    have hcoeffUnit : IsUnit (D.coeff 0) :=
      (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hHprimitive)
        (D.coeff 0) hCdivH
    have hDunit : IsUnit D := by
      rw [hDconst]
      exact Polynomial.isUnit_C.mpr hcoeffUnit
    have hKunit : IsUnit K := by
      have hmap := hDunit.map swap
      simpa only [D, Polynomial.Bivariate.swap_swap_apply] using hmap
    have hKdegree : K.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hKunit
    omega
  exact ⟨D, hDprimitive, hDpositive, hDdivH, hDdivQ⟩

/-- Production-scale two-axis fibres force a genuine common factor of the
homogeneous factor and affine component. -/
theorem production_exists_positiveLocatorCommonFactor
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (d t : Nat)
    (hHprimitive : H.IsPrimitive)
    (hHY : H.natDegree = d)
    (hHX : degreeX H = t)
    (hd : 0 < d)
    (hdcap : d ≤ homogeneousLocatorCap)
    (hCY : C.natDegree ≤ affineLocatorCap)
    (hCX : degreeX C ≤ affineChallengeCap)
    (hOwners : ownerFloor ≤ Owners.card)
    (hCoords : coordinateCount ≤ Coords.card)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i))) :
    ∃ D : F[X][X],
      D.IsPrimitive ∧ 0 < D.natDegree ∧ D ∣ H ∧ D ∣ C := by
  rcases production_resultant_zero_dichotomy
      H C Owners owner Coords coord d t
      hHprimitive.ne_zero hHY hHX hd hdcap hCY hCX hOwners hCoords
      howner hcoord with hOwnerZero | hCoordZero
  · exact exists_integralPrimitiveCommonFactor_of_fixed_resultant_eq_zero
      H C d affineLocatorCap hHprimitive.ne_zero hHY hCY hOwnerZero
  · exact exists_positiveLocatorCommonFactor_of_swapped_fixed_resultant_eq_zero
      H C t affineChallengeCap hHprimitive hHX hCX hCoordZero

end BCHKSCommonFactorDescent6400
end ProximityPrize.SubmissionLower
