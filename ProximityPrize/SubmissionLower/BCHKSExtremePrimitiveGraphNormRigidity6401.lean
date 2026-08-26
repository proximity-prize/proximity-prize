import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFaithfulGraphGauge6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveGraphNormRigidity6401
open Polynomial
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSFrobeniusOffsetProductDegreeAudit6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveFaithfulGraphGauge6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
section GraphNormRigidity
variable {F : Type} [Field F] [DecidableEq F]
noncomputable def graphTwistSix6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) : F[X][X] :=
  graphTwist6401 sigma q (graphTwistFive6401 sigma q P)
theorem graphTwist_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) (P : F[X][X]) :
    (graphTwist6401 sigma q P).natDegree = P.natDegree := by
  exact Polynomial.natDegree_map_eq_of_injective
    (challengeFrobeniusRingHom_injective6401 sigma q hq) P
theorem graphTwistSix_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q) (P : F[X][X]) :
    (graphTwistSix6401 sigma q P).natDegree = P.natDegree := by
  simp only [graphTwistSix6401, graphTwistFive6401,
    graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401]
  rw [graphTwist_natDegree_eq6401 sigma q hq,
    graphTwist_natDegree_eq6401 sigma q hq,
    graphTwist_natDegree_eq6401 sigma q hq,
    graphTwist_natDegree_eq6401 sigma q hq,
    graphTwist_natDegree_eq6401 sigma q hq,
    graphTwist_natDegree_eq6401 sigma q hq]
theorem graphTwistSix_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (P : F[X][X]) (hP : P ≠ 0) :
    graphTwistSix6401 sigma q P ≠ 0 := by
  exact graphTwist_ne_zero6401 sigma q hq _
    (graphTwist_ne_zero6401 sigma q hq _
      (graphTwist_ne_zero6401 sigma q hq _
        (graphTwist_ne_zero6401 sigma q hq _
          (graphTwist_ne_zero6401 sigma q hq _
            (graphTwist_ne_zero6401 sigma q hq P hP)))))
theorem graphNorm_eq_imp_sixthTwist_cross6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    B * graphTwistSix6401 sigma q A =
      A * graphTwistSix6401 sigma q B := by
  let TA : F[X][X] := graphTwist6401 sigma q A
  let T2A : F[X][X] := graphTwistTwo6401 sigma q A
  let T3A : F[X][X] := graphTwistThree6401 sigma q A
  let T4A : F[X][X] := graphTwistFour6401 sigma q A
  let T5A : F[X][X] := graphTwistFive6401 sigma q A
  let T6A : F[X][X] := graphTwistSix6401 sigma q A
  let TB : F[X][X] := graphTwist6401 sigma q B
  let T2B : F[X][X] := graphTwistTwo6401 sigma q B
  let T3B : F[X][X] := graphTwistThree6401 sigma q B
  let T4B : F[X][X] := graphTwistFour6401 sigma q B
  let T5B : F[X][X] := graphTwistFive6401 sigma q B
  let T6B : F[X][X] := graphTwistSix6401 sigma q B
  let PA : F[X][X] := TA * T2A * T3A * T4A * T5A
  let PB : F[X][X] := TB * T2B * T3B * T4B * T5B
  have hnorm' : A * PA = B * PB := by
    calc
      A * PA = graphFrobeniusNormSix6401 sigma q A := by
        simp only [PA, TA, T2A, T3A, T4A, T5A,
          graphFrobeniusNormSix6401]
        ring
      _ = graphFrobeniusNormSix6401 sigma q B := hnorm
      _ = B * PB := by
        simp only [PB, TB, T2B, T3B, T4B, T5B,
          graphFrobeniusNormSix6401]
        ring
  have hshiftRaw := congrArg (graphTwist6401 sigma q) hnorm
  have hshift : PA * T6A = PB * T6B := by
    simpa [PA, PB, TA, T2A, T3A, T4A, T5A, T6A,
      TB, T2B, T3B, T4B, T5B, T6B,
      graphFrobeniusNormSix6401, graphTwistSix6401,
      graphTwistFive6401, graphTwistFour6401,
      graphTwistThree6401, graphTwistTwo6401,
      graphTwist6401, Polynomial.map_mul] using hshiftRaw
  have hTB : TB ≠ 0 := graphTwist_ne_zero6401 sigma q hq B hB
  have hT2B : T2B ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hTB
  have hT3B : T3B ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT2B
  have hT4B : T4B ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT3B
  have hT5B : T5B ≠ 0 := graphTwist_ne_zero6401 sigma q hq _ hT4B
  have hPB : PB ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hTB hT2B)
      hT3B) hT4B) hT5B
  apply mul_left_cancel₀ hPB
  calc
    PB * (B * T6A) = (B * PB) * T6A := by ring
    _ = (A * PA) * T6A := by rw [hnorm']
    _ = A * (PA * T6A) := by ring
    _ = A * (PB * T6B) := by rw [hshift]
    _ = PB * (A * T6B) := by ring
theorem graphTwistSix_coeff_natDegree_eq6401
    (sigma : F →+* F) (q : Nat) (P : F[X][X]) (n : Nat) :
    ((graphTwistSix6401 sigma q P).coeff n).natDegree =
      (P.coeff n).natDegree * q ^ 6 := by
  simp only [graphTwistSix6401, graphTwistFive6401,
    graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
    graphTwist6401, Polynomial.coeff_map,
    challengeFrobeniusRingHom_apply6401]
  rw [challengeFrobenius_natDegree, challengeFrobenius_natDegree,
    challengeFrobenius_natDegree, challengeFrobenius_natDegree,
    challengeFrobenius_natDegree, challengeFrobenius_natDegree]
  ring
theorem challengeConstant_iff_exists_map_C6401 (P : F[X][X]) :
    (∀ n, (P.coeff n).natDegree = 0) ↔
      ∃ P0 : F[X], P = P0.map Polynomial.C := by
  constructor
  · intro hconstant
    refine ⟨P.map (Polynomial.evalRingHom 0), ?_⟩
    ext n
    simp only [Polynomial.coeff_map]
    have hcoeff := Polynomial.eq_C_of_natDegree_eq_zero (hconstant n)
    rw [hcoeff]
    simp
  · rintro ⟨P0, rfl⟩ n
    simp
theorem twoStageRelPrime_graphNorm_eq_forces_challengeConstant6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hrelprime : IsRelPrime A B)
    (hrelprimeSix : IsRelPrime
      (graphTwistSix6401 sigma q A) (graphTwistSix6401 sigma q B))
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    (∀ n, (A.coeff n).natDegree = 0) ∧
      ∀ n, (B.coeff n).natDegree = 0 := by
  have hq0 : 0 < q := Nat.zero_lt_of_lt hq
  let T6A := graphTwistSix6401 sigma q A
  let T6B := graphTwistSix6401 sigma q B
  have hcross : B * T6A = A * T6B := by
    exact graphNorm_eq_imp_sixthTwist_cross6401 sigma q hq0 A B hA hB hnorm
  have hAdivProd : A ∣ B * T6A := ⟨T6B, hcross⟩
  have hAdiv : A ∣ T6A := hrelprime.dvd_of_dvd_mul_left hAdivProd
  have hBdivProd : B ∣ A * T6B := ⟨T6A, hcross.symm⟩
  have hBdiv : B ∣ T6B := hrelprime.symm.dvd_of_dvd_mul_left hBdivProd
  obtain ⟨UA, hUA⟩ := hAdiv
  obtain ⟨UB, hUB⟩ := hBdiv
  have hT6A : T6A ≠ 0 := graphTwistSix_ne_zero6401 sigma q hq0 A hA
  have hT6B : T6B ≠ 0 := graphTwistSix_ne_zero6401 sigma q hq0 B hB
  have hUAne : UA ≠ 0 := by
    intro hzero
    apply hT6A
    rw [hUA, hzero, mul_zero]
  have hUBne : UB ≠ 0 := by
    intro hzero
    apply hT6B
    rw [hUB, hzero, mul_zero]
  have hUAdegree : UA.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hA hUAne
    have htwist := graphTwistSix_natDegree_eq6401 sigma q hq0 A
    dsimp only [T6A] at hUA htwist
    rw [← hUA] at hmul
    omega
  have hUBdegree : UB.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hB hUBne
    have htwist := graphTwistSix_natDegree_eq6401 sigma q hq0 B
    dsimp only [T6B] at hUB htwist
    rw [← hUB] at hmul
    omega
  let uA : F[X] := UA.coeff 0
  let uB : F[X] := UB.coeff 0
  have hUAconst : UA = Polynomial.C uA := by
    exact Polynomial.eq_C_of_natDegree_eq_zero hUAdegree
  have hUBconst : UB = Polynomial.C uB := by
    exact Polynomial.eq_C_of_natDegree_eq_zero hUBdegree
  have huEq : uA = uB := by
    have hprod : (A * B) * Polynomial.C uA =
        (A * B) * Polynomial.C uB := by
      calc
        (A * B) * Polynomial.C uA = B * T6A := by
          rw [hUA, hUAconst]
          ring
        _ = A * T6B := hcross
        _ = (A * B) * Polynomial.C uB := by
          rw [hUB, hUBconst]
          ring
    have hAB : A * B ≠ 0 := mul_ne_zero hA hB
    have hC : Polynomial.C uA = Polynomial.C uB :=
      mul_left_cancel₀ hAB hprod
    exact Polynomial.C_injective hC
  have hUBconstA : UB = Polynomial.C uA := by
    exact hUBconst.trans (congrArg Polynomial.C huEq).symm
  have hCdivA : Polynomial.C uA ∣ T6A := by
    refine ⟨A, ?_⟩
    rw [hUA, hUAconst]
    ring
  have hCdivB : Polynomial.C uA ∣ T6B := by
    refine ⟨B, ?_⟩
    rw [hUB, hUBconstA]
    ring
  have huUnit : IsUnit uA := by
    exact Polynomial.isUnit_C.mp
      (hrelprimeSix hCdivA hCdivB)
  have huNe : uA ≠ 0 := huUnit.ne_zero
  have huDegree : uA.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit huUnit
  constructor
  · intro n
    by_cases ha : A.coeff n = 0
    · simp [ha]
    · have hcoeff := congrArg (fun P : F[X][X] ↦ P.coeff n) hUA
      rw [hUAconst, Polynomial.coeff_mul_C] at hcoeff
      have hdegree := congrArg Polynomial.natDegree hcoeff
      rw [graphTwistSix_coeff_natDegree_eq6401 sigma q A n,
        Polynomial.natDegree_mul ha huNe, huDegree, add_zero] at hdegree
      have hq6 : 1 < q ^ 6 := one_lt_pow₀ hq (by norm_num)
      by_contra hdegreeNe
      have hdegreePos : 0 < (A.coeff n).natDegree :=
        Nat.pos_of_ne_zero hdegreeNe
      have hlt : (A.coeff n).natDegree <
          (A.coeff n).natDegree * q ^ 6 := by
        simpa only [mul_one] using
          Nat.mul_lt_mul_of_pos_left hq6 hdegreePos
      exact (Nat.ne_of_lt hlt) hdegree.symm
  · intro n
    by_cases hb : B.coeff n = 0
    · simp [hb]
    · have hcoeff := congrArg (fun P : F[X][X] ↦ P.coeff n) hUB
      rw [hUBconstA, Polynomial.coeff_mul_C] at hcoeff
      have hdegree := congrArg Polynomial.natDegree hcoeff
      rw [graphTwistSix_coeff_natDegree_eq6401 sigma q B n,
        Polynomial.natDegree_mul hb huNe, huDegree, add_zero] at hdegree
      have hq6 : 1 < q ^ 6 := one_lt_pow₀ hq (by norm_num)
      by_contra hdegreeNe
      have hdegreePos : 0 < (B.coeff n).natDegree :=
        Nat.pos_of_ne_zero hdegreeNe
      have hlt : (B.coeff n).natDegree <
          (B.coeff n).natDegree * q ^ 6 := by
        simpa only [mul_one] using
          Nat.mul_lt_mul_of_pos_left hq6 hdegreePos
      exact (Nat.ne_of_lt hlt) hdegree.symm
theorem bezoutCoprime_graphNorm_eq_forces_challengeConstant6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    (∀ n, (A.coeff n).natDegree = 0) ∧
      ∀ n, (B.coeff n).natDegree = 0 := by
  have hcop1 := hcoprime.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hcop2 := hcop1.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hcop3 := hcop2.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hcop4 := hcop3.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hcop5 := hcop4.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hcop6 := hcop5.map
    (Polynomial.mapRingHom (challengeFrobeniusRingHom6401 sigma q))
  have hrelprimeSix : IsRelPrime
      (graphTwistSix6401 sigma q A) (graphTwistSix6401 sigma q B) := by
    apply IsCoprime.isRelPrime
    simpa [graphTwistSix6401, graphTwistFive6401,
      graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
      graphTwist6401] using hcop6
  exact twoStageRelPrime_graphNorm_eq_forces_challengeConstant6401
    sigma q hq A B hA hB hcoprime.isRelPrime hrelprimeSix hnorm
theorem exists_fixedLanes_of_bezoutCoprime_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcoprime : IsCoprime A B)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    ∃ A0 B0 : F[X],
      A = A0.map Polynomial.C ∧ B = B0.map Polynomial.C := by
  rcases bezoutCoprime_graphNorm_eq_forces_challengeConstant6401
      sigma q hq A B hA hB hcoprime hnorm with ⟨hAc, hBc⟩
  obtain ⟨A0, hA0⟩ :=
    (challengeConstant_iff_exists_map_C6401 A).mp hAc
  obtain ⟨B0, hB0⟩ :=
    (challengeConstant_iff_exists_map_C6401 B).mp hBc
  exact ⟨A0, B0, hA0, hB0⟩
end GraphNormRigidity
end BCHKSExtremePrimitiveGraphNormRigidity6401
end ProximityPrize.SubmissionLower
