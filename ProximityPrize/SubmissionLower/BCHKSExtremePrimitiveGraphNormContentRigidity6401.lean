import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphNormRigidity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveGraphNormContentRigidity6401
open Polynomial
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFaithfulGraphGauge6401
open BCHKSExtremePrimitiveGraphNormRigidity6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
section PrimitiveTwist
variable {F : Type} [Field F] [DecidableEq F]
private theorem dvd_map_finset_gcd6401
    (f : F[X] →+* F[X]) (s : Finset Nat) (a : Nat → F[X]) (r : F[X])
    (hdiv : ∀ n ∈ s, r ∣ f (a n)) :
    r ∣ f (s.gcd a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.gcd_insert]
      obtain ⟨x, y, hgcd⟩ :=
        exists_gcd_eq_mul_add_mul (a n) (s.gcd a)
      rw [hgcd, map_add, map_mul, map_mul]
      exact dvd_add
        (dvd_mul_of_dvd_left (hdiv n (Finset.mem_insert_self n s)) _)
        (dvd_mul_of_dvd_left
          (ih (fun m hm => hdiv m (Finset.mem_insert_of_mem hm))) _)
theorem isPrimitive_map_coeffEndomorphism6401
    (P : F[X][X]) (hP : P.IsPrimitive) (f : F[X] →+* F[X]) :
    (P.map f).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hrcoeff : ∀ n, r ∣ f (P.coeff n) := by
    intro n
    have := (Polynomial.C_dvd_iff_dvd_coeff r (P.map f)).mp hr n
    simpa only [Polynomial.coeff_map] using this
  have hcontent : r ∣ f P.content := by
    change r ∣ f (P.support.gcd P.coeff)
    exact dvd_map_finset_gcd6401 f P.support P.coeff r
      (fun n _ => hrcoeff n)
  have hrone : r ∣ 1 := by
    simpa only [hP.content_eq_one, map_one] using hcontent
  exact isUnit_iff_dvd_one.mpr hrone
theorem isPrimitive_graphTwist6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X])
    (hP : P.IsPrimitive) :
    (graphTwist6401 sigma q P).IsPrimitive := by
  exact isPrimitive_map_coeffEndomorphism6401 P hP _
theorem isPrimitive_graphTwistSix6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X])
    (hP : P.IsPrimitive) :
    (graphTwistSix6401 sigma q P).IsPrimitive := by
  apply isPrimitive_graphTwist6401
  apply isPrimitive_graphTwist6401
  apply isPrimitive_graphTwist6401
  apply isPrimitive_graphTwist6401
  apply isPrimitive_graphTwist6401
  exact isPrimitive_graphTwist6401 sigma q P hP
private theorem isUnit_fractionMap_of_natDegree_zero6401
    (Q : F[X][X]) (hQ : Q ≠ 0) (hdegree : Q.natDegree = 0) :
    IsUnit (Q.map (algebraMap F[X] (FractionRing F[X]))) := by
  let f : F[X] →+* FractionRing F[X] :=
    algebraMap F[X] (FractionRing F[X])
  have hf : Function.Injective f :=
    IsFractionRing.injective F[X] (FractionRing F[X])
  have hmapNe : Q.map f ≠ 0 :=
    (Polynomial.map_ne_zero_iff hf).2 hQ
  have hmapDegree : (Q.map f).natDegree = 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective hf, hdegree]
  have heq : Q.map f = Polynomial.C ((Q.map f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hmapDegree
  have hc : (Q.map f).coeff 0 ≠ 0 := by
    intro hzero
    apply hmapNe
    rw [heq, hzero, Polynomial.C_0]
  rw [heq]
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
private theorem sixthTwist_C_fractionMap_isUnit6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (c : F[X]) (hc : c ≠ 0) :
    IsUnit ((graphTwistSix6401 sigma q (Polynomial.C c)).map
      (algebraMap F[X] (FractionRing F[X]))) := by
  have hC : (Polynomial.C c : F[X][X]) ≠ 0 := by simpa using hc
  apply isUnit_fractionMap_of_natDegree_zero6401
    (graphTwistSix6401 sigma q (Polynomial.C c))
    (graphTwistSix_ne_zero6401 sigma q hq _ hC)
  rw [graphTwistSix_natDegree_eq6401 sigma q hq]
  simp
end PrimitiveTwist
section ContentRigidity
variable {F : Type} [Field F] [DecidableEq F]
theorem primitiveParts_challengeConstant_of_resultant_ne_zero_of_sixthCross6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hcross : B * graphTwistSix6401 sigma q A =
      A * graphTwistSix6401 sigma q B) :
    (∀ n, (A.primPart.coeff n).natDegree = 0) ∧
      ∀ n, (B.primPart.coeff n).natDegree = 0 := by
  let K := FractionRing F[X]
  let f : F[X] →+* K := algebraMap F[X] K
  have hf : Function.Injective f := IsFractionRing.injective F[X] K
  let AK : Polynomial K := A.map f
  let BK : Polynomial K := B.map f
  let Ap : F[X][X] := A.primPart
  let Bp : F[X][X] := B.primPart
  let ApK : Polynomial K := Ap.map f
  let BpK : Polynomial K := Bp.map f
  let T6A : F[X][X] := graphTwistSix6401 sigma q A
  let T6B : F[X][X] := graphTwistSix6401 sigma q B
  let T6Ap : F[X][X] := graphTwistSix6401 sigma q Ap
  let T6Bp : F[X][X] := graphTwistSix6401 sigma q Bp
  have hAK : AK ≠ 0 := (Polynomial.map_ne_zero_iff hf).2 hA
  have hBK : BK ≠ 0 := (Polynomial.map_ne_zero_iff hf).2 hB
  have hAdegree : AK.natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf A
  have hBdegree : BK.natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf B
  have hresFixed : Polynomial.resultant AK BK A.natDegree B.natDegree ≠ 0 := by
    rw [Polynomial.resultant_map_map]
    exact (map_ne_zero_iff f hf).2 hresultant
  have hresK : Polynomial.resultant AK BK ≠ 0 := by
    simpa only [hAdegree, hBdegree] using hresFixed
  have hcop : IsCoprime AK BK := by
    by_contra hnot
    exact hresK (Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl hAK, hnot⟩)
  have hcA : A.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hcB : B.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hfcA : f A.content ≠ 0 := fun hzero =>
    hcA (hf (by simpa using hzero))
  have hfcB : f B.content ≠ 0 := fun hzero =>
    hcB (hf (by simpa using hzero))
  have hunitA : IsUnit (Polynomial.C (f A.content) : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hfcA)
  have hunitB : IsUnit (Polynomial.C (f B.content) : Polynomial K) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hfcB)
  have hAKfactor : AK = Polynomial.C (f A.content) * ApK := by
    have h := congrArg (Polynomial.map f) A.eq_C_content_mul_primPart
    simpa only [AK, ApK, Ap, Polynomial.map_mul, Polynomial.map_C] using h
  have hBKfactor : BK = Polynomial.C (f B.content) * BpK := by
    have h := congrArg (Polynomial.map f) B.eq_C_content_mul_primPart
    simpa only [BK, BpK, Bp, Polynomial.map_mul, Polynomial.map_C] using h
  have hcopApBK : IsCoprime ApK BK := by
    rw [hAKfactor] at hcop
    exact (isCoprime_mul_unit_left_left hunitA ApK BK).mp hcop
  have hcopAKBp : IsCoprime AK BpK := by
    rw [hBKfactor] at hcop
    exact (isCoprime_mul_unit_left_right hunitB AK BpK).mp hcop
  have hcrossK : BK * T6A.map f = AK * T6B.map f := by
    simpa only [AK, BK, T6A, T6B, Polynomial.map_mul] using
      congrArg (Polynomial.map f) hcross
  have hApKdivT6A : ApK ∣ T6A.map f := by
    have hApKdivAK : ApK ∣ AK := by
      rw [hAKfactor]
      exact dvd_mul_left _ _
    have hprod : ApK ∣ BK * T6A.map f := by
      rw [hcrossK]
      exact dvd_mul_of_dvd_left hApKdivAK _
    exact hcopApBK.dvd_of_dvd_mul_left hprod
  have hBpKdivT6B : BpK ∣ T6B.map f := by
    have hBpKdivBK : BpK ∣ BK := by
      rw [hBKfactor]
      exact dvd_mul_left _ _
    have hprod : BpK ∣ AK * T6B.map f := by
      rw [← hcrossK]
      exact dvd_mul_of_dvd_left hBpKdivBK _
    exact hcopAKBp.symm.dvd_of_dvd_mul_left hprod
  have hT6Afactor : T6A =
      graphTwistSix6401 sigma q (Polynomial.C A.content) * T6Ap := by
    calc
      T6A = graphTwistSix6401 sigma q
          (Polynomial.C A.content * A.primPart) := by
            exact congrArg (graphTwistSix6401 sigma q)
              A.eq_C_content_mul_primPart
      _ = graphTwistSix6401 sigma q (Polynomial.C A.content) * T6Ap := by
        simp only [T6Ap, Ap, graphTwistSix6401, graphTwistFive6401,
          graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
          graphTwist6401, Polynomial.map_mul]
  have hT6Bfactor : T6B =
      graphTwistSix6401 sigma q (Polynomial.C B.content) * T6Bp := by
    calc
      T6B = graphTwistSix6401 sigma q
          (Polynomial.C B.content * B.primPart) := by
            exact congrArg (graphTwistSix6401 sigma q)
              B.eq_C_content_mul_primPart
      _ = graphTwistSix6401 sigma q (Polynomial.C B.content) * T6Bp := by
        simp only [T6Bp, Bp, graphTwistSix6401, graphTwistFive6401,
          graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
          graphTwist6401, Polynomial.map_mul]
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  have hscalarA := sixthTwist_C_fractionMap_isUnit6401
    sigma q hq0 A.content hcA
  have hscalarB := sixthTwist_C_fractionMap_isUnit6401
    sigma q hq0 B.content hcB
  have hscalarA' : IsUnit
      ((graphTwistSix6401 sigma q (Polynomial.C A.content)).map f) := by
    simpa only [K, f] using hscalarA
  have hscalarB' : IsUnit
      ((graphTwistSix6401 sigma q (Polynomial.C B.content)).map f) := by
    simpa only [K, f] using hscalarB
  have hApKdivT6ApK : ApK ∣ T6Ap.map f := by
    have hprod : ApK ∣
        (graphTwistSix6401 sigma q (Polynomial.C A.content)).map f *
          T6Ap.map f := by
      simpa only [hT6Afactor, Polynomial.map_mul] using hApKdivT6A
    have hcopScalar : IsCoprime ApK
        ((graphTwistSix6401 sigma q (Polynomial.C A.content)).map f) := by
      simpa only [mul_one] using
        ((isCoprime_mul_unit_left_right hscalarA' ApK 1).2
          isCoprime_one_right)
    exact hcopScalar.dvd_of_dvd_mul_left hprod
  have hBpKdivT6BpK : BpK ∣ T6Bp.map f := by
    have hprod : BpK ∣
        (graphTwistSix6401 sigma q (Polynomial.C B.content)).map f *
          T6Bp.map f := by
      simpa only [hT6Bfactor, Polynomial.map_mul] using hBpKdivT6B
    have hcopScalar : IsCoprime BpK
        ((graphTwistSix6401 sigma q (Polynomial.C B.content)).map f) := by
      simpa only [mul_one] using
        ((isCoprime_mul_unit_left_right hscalarB' BpK 1).2
          isCoprime_one_right)
    exact hcopScalar.dvd_of_dvd_mul_left hprod
  have hApdiv : Ap ∣ T6Ap :=
    A.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map
      hApKdivT6ApK
  have hBpdiv : Bp ∣ T6Bp :=
    B.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map
      hBpKdivT6BpK
  obtain ⟨UA, hUA⟩ := hApdiv
  obtain ⟨UB, hUB⟩ := hBpdiv
  have hAp : Ap ≠ 0 := A.primPart_ne_zero
  have hBp : Bp ≠ 0 := B.primPart_ne_zero
  have hT6Ap : T6Ap ≠ 0 :=
    graphTwistSix_ne_zero6401 sigma q hq0 Ap hAp
  have hT6Bp : T6Bp ≠ 0 :=
    graphTwistSix_ne_zero6401 sigma q hq0 Bp hBp
  have hUAne : UA ≠ 0 := by
    intro hzero
    apply hT6Ap
    rw [hUA, hzero, mul_zero]
  have hUBne : UB ≠ 0 := by
    intro hzero
    apply hT6Bp
    rw [hUB, hzero, mul_zero]
  have hUAdegree : UA.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hAp hUAne
    have htwist := graphTwistSix_natDegree_eq6401 sigma q hq0 Ap
    dsimp only [T6Ap] at hUA htwist
    rw [← hUA] at hmul
    omega
  have hUBdegree : UB.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hBp hUBne
    have htwist := graphTwistSix_natDegree_eq6401 sigma q hq0 Bp
    dsimp only [T6Bp] at hUB htwist
    rw [← hUB] at hmul
    omega
  let uA : F[X] := UA.coeff 0
  let uB : F[X] := UB.coeff 0
  have hUAconst : UA = Polynomial.C uA :=
    Polynomial.eq_C_of_natDegree_eq_zero hUAdegree
  have hUBconst : UB = Polynomial.C uB :=
    Polynomial.eq_C_of_natDegree_eq_zero hUBdegree
  have hT6ApPrimitive : T6Ap.IsPrimitive := by
    exact isPrimitive_graphTwistSix6401 sigma q Ap A.isPrimitive_primPart
  have hT6BpPrimitive : T6Bp.IsPrimitive := by
    exact isPrimitive_graphTwistSix6401 sigma q Bp B.isPrimitive_primPart
  have huAUnit : IsUnit uA := by
    apply (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hT6ApPrimitive)
    refine ⟨Ap, ?_⟩
    rw [hUA, hUAconst]
    ring
  have huBUnit : IsUnit uB := by
    apply (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hT6BpPrimitive)
    refine ⟨Bp, ?_⟩
    rw [hUB, hUBconst]
    ring
  have huAne : uA ≠ 0 := huAUnit.ne_zero
  have huBne : uB ≠ 0 := huBUnit.ne_zero
  have huAdegree : uA.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit huAUnit
  have huBdegree : uB.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit huBUnit
  constructor
  · intro n
    by_cases ha : Ap.coeff n = 0
    · have hzero : (Ap.coeff n).natDegree = 0 := by simp [ha]
      simpa only [Ap] using hzero
    · have hcoeff := congrArg (fun Q : F[X][X] ↦ Q.coeff n) hUA
      rw [hUAconst, Polynomial.coeff_mul_C] at hcoeff
      have hdegree := congrArg Polynomial.natDegree hcoeff
      rw [graphTwistSix_coeff_natDegree_eq6401 sigma q Ap n,
        Polynomial.natDegree_mul ha huAne, huAdegree, add_zero] at hdegree
      have hq6 : 1 < q ^ 6 := one_lt_pow₀ hq (by norm_num)
      have hzero : (Ap.coeff n).natDegree = 0 := by
        by_contra hne
        have hpos : 0 < (Ap.coeff n).natDegree := Nat.pos_of_ne_zero hne
        have hlt : (Ap.coeff n).natDegree <
            (Ap.coeff n).natDegree * q ^ 6 :=
          lt_mul_of_one_lt_right hpos hq6
        omega
      simpa only [Ap] using hzero
  · intro n
    by_cases hb : Bp.coeff n = 0
    · have hzero : (Bp.coeff n).natDegree = 0 := by simp [hb]
      simpa only [Bp] using hzero
    · have hcoeff := congrArg (fun Q : F[X][X] ↦ Q.coeff n) hUB
      rw [hUBconst, Polynomial.coeff_mul_C] at hcoeff
      have hdegree := congrArg Polynomial.natDegree hcoeff
      rw [graphTwistSix_coeff_natDegree_eq6401 sigma q Bp n,
        Polynomial.natDegree_mul hb huBne, huBdegree, add_zero] at hdegree
      have hq6 : 1 < q ^ 6 := one_lt_pow₀ hq (by norm_num)
      have hzero : (Bp.coeff n).natDegree = 0 := by
        by_contra hne
        have hpos : 0 < (Bp.coeff n).natDegree := Nat.pos_of_ne_zero hne
        have hlt : (Bp.coeff n).natDegree <
            (Bp.coeff n).natDegree * q ^ 6 :=
          lt_mul_of_one_lt_right hpos hq6
        omega
      simpa only [Bp] using hzero
theorem primitiveParts_challengeConstant_of_resultant_ne_zero_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    (∀ n, (A.primPart.coeff n).natDegree = 0) ∧
      ∀ n, (B.primPart.coeff n).natDegree = 0 := by
  apply primitiveParts_challengeConstant_of_resultant_ne_zero_of_sixthCross6401
    sigma q hq A B hA hB hresultant
  exact graphNorm_eq_imp_sixthTwist_cross6401
    sigma q (Nat.zero_lt_of_lt hq) A B hA hB hnorm
end ContentRigidity
end BCHKSExtremePrimitiveGraphNormContentRigidity6401
end ProximityPrize.SubmissionLower
