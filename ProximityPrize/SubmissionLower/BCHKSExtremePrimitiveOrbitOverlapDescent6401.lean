import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveOrbitOverlapDescent6401
open Polynomial
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusHighSupportResidual6401
open BCHKSSubfieldFrobenius6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
noncomputable def orbitOverlapGcd6401
    {F : Type*} [Field F] (A B : F[X]) : F[X] := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  exact GCDMonoid.gcd A B
noncomputable def fifthCoefficientTwist6401
    {F : Type*} [Field F] (sigma : F →+* F) (P : F[X]) : F[X] :=
  (((((P.map sigma).map sigma).map sigma).map sigma).map sigma)
def fifthScalarTwist6401
    {F : Type*} [Field F] (sigma : F →+* F) (x : F) : F :=
  sigma (sigma (sigma (sigma (sigma x))))
theorem fifthCoefficientTwist_natDegree_eq6401
    {F : Type*} [Field F] (sigma : F →+* F) (P : F[X]) :
    (fifthCoefficientTwist6401 sigma P).natDegree = P.natDegree := by
  simp only [fifthCoefficientTwist6401,
    Polynomial.natDegree_map_eq_of_injective sigma.injective]
theorem fifthCoefficientTwist_ne_zero6401
    {F : Type*} [Field F] (sigma : F →+* F) (P : F[X])
    (hP : P ≠ 0) : fifthCoefficientTwist6401 sigma P ≠ 0 := by
  simp only [fifthCoefficientTwist6401]
  exact (Polynomial.map_ne_zero_iff sigma.injective).2
    ((Polynomial.map_ne_zero_iff sigma.injective).2
      ((Polynomial.map_ne_zero_iff sigma.injective).2
        ((Polynomial.map_ne_zero_iff sigma.injective).2
          ((Polynomial.map_ne_zero_iff sigma.injective).2 hP))))
theorem fifthCoefficientTwist_eval_fixed6401
    {F : Type*} [Field F] (sigma : F →+* F) (P : F[X]) (x : F)
    (hfixed : sigma x = x) :
    (fifthCoefficientTwist6401 sigma P).eval x =
      fifthScalarTwist6401 sigma (P.eval x) := by
  unfold fifthCoefficientTwist6401 fifthScalarTwist6401
  rw [eval_map_eq_map_eval_of_fixed sigma _ x hfixed]
  rw [eval_map_eq_map_eval_of_fixed sigma _ x hfixed]
  rw [eval_map_eq_map_eval_of_fixed sigma _ x hfixed]
  rw [eval_map_eq_map_eval_of_fixed sigma _ x hfixed]
  rw [eval_map_eq_map_eval_of_fixed sigma _ x hfixed]
theorem fifthScalarTwist_mul6401
    {F : Type*} [Field F] (sigma : F →+* F) (x y : F) :
    fifthScalarTwist6401 sigma (x * y) =
      fifthScalarTwist6401 sigma x * fifthScalarTwist6401 sigma y := by
  simp [fifthScalarTwist6401, map_mul]
theorem fifthScalarTwist_sigma_eq6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (x : F) : fifthScalarTwist6401 sigma (sigma x) = x := by
  exact horder x
theorem polynomialFrobeniusNormSix_mul6401
    {F : Type*} [Field F] (sigma : F →+* F) (P Q : F[X]) :
    polynomialFrobeniusNormSix sigma (P * Q) =
      polynomialFrobeniusNormSix sigma P *
        polynomialFrobeniusNormSix sigma Q := by
  simp only [polynomialFrobeniusNormSix, Polynomial.map_mul]
  ring
theorem polynomialFrobeniusNormSix_ne_zero6401
    {F : Type*} [Field F] (sigma : F →+* F) (P : F[X])
    (hP : P ≠ 0) : polynomialFrobeniusNormSix sigma P ≠ 0 := by
  have h1 : P.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hP
  have h2 : (P.map sigma).map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 h1
  have h3 : ((P.map sigma).map sigma).map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 h2
  have h4 : (((P.map sigma).map sigma).map sigma).map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 h3
  have h5 : ((((P.map sigma).map sigma).map sigma).map sigma).map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 h4
  dsimp [polynomialFrobeniusNormSix]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero hP h1) h2) h3) h4) h5
theorem residualNorm_eq_of_orbitOverlapFactorization6401
    {F : Type*} [Field F] (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B D A' B' : F[X]) (hD : D ≠ 0)
    (hfactorA : A = D * A')
    (hfactorB : B.map sigma = D * B')
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B) :
    polynomialFrobeniusNormSix sigma A' =
      polynomialFrobeniusNormSix sigma B' := by
  apply mul_left_cancel₀
    (polynomialFrobeniusNormSix_ne_zero6401 sigma D hD)
  calc
    polynomialFrobeniusNormSix sigma D *
          polynomialFrobeniusNormSix sigma A' =
        polynomialFrobeniusNormSix sigma (D * A') := by
      rw [polynomialFrobeniusNormSix_mul6401]
    _ = polynomialFrobeniusNormSix sigma A := by rw [← hfactorA]
    _ = polynomialFrobeniusNormSix sigma B := hnorm
    _ = polynomialFrobeniusNormSix sigma (B.map sigma) :=
      (polynomialFrobeniusNormSix_map_eq6401 sigma horder B).symm
    _ = polynomialFrobeniusNormSix sigma (D * B') := by rw [hfactorB]
    _ = polynomialFrobeniusNormSix sigma D *
          polynomialFrobeniusNormSix sigma B' :=
      polynomialFrobeniusNormSix_mul6401 sigma D B'
section GcdCross
variable {F : Type*} [Field F]
theorem orbitCross_gcd_factorization6401
    (sigma : F →+* F) (A B L R : F[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0)
    (hcross : L * B.map sigma = A * R.map sigma) :
    ∃ D A' B' T : F[X],
      D = orbitOverlapGcd6401 A (B.map sigma) ∧
      D ≠ 0 ∧ A' ≠ 0 ∧ B' ≠ 0 ∧ T ≠ 0 ∧
      A = D * A' ∧ B.map sigma = D * B' ∧
      IsCoprime A' B' ∧
      L = A' * T ∧ R.map sigma = B' * T ∧
      D.natDegree + A'.natDegree = A.natDegree ∧
      D.natDegree + B'.natDegree = B.natDegree ∧
      A'.natDegree + T.natDegree = L.natDegree ∧
      B'.natDegree + T.natDegree = R.natDegree := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  let D : F[X] := GCDMonoid.gcd A (B.map sigma)
  let A' : F[X] := A / D
  let B' : F[X] := B.map sigma / D
  have hBmap : B.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hB
  have hRmap : R.map sigma ≠ 0 :=
    (Polynomial.map_ne_zero_iff sigma.injective).2 hR
  have hD : D ≠ 0 := gcd_ne_zero_of_left hA
  have hA' : A' ≠ 0 := left_div_gcd_ne_zero hA
  have hB' : B' ≠ 0 := right_div_gcd_ne_zero hBmap
  have hfactorA : A = D * A' := by
    symm
    exact EuclideanDomain.mul_div_cancel' hD
      (GCDMonoid.gcd_dvd_left A (B.map sigma))
  have hfactorB : B.map sigma = D * B' := by
    symm
    exact EuclideanDomain.mul_div_cancel' hD
      (GCDMonoid.gcd_dvd_right A (B.map sigma))
  have hcoprime : IsCoprime A' B' :=
    isCoprime_div_gcd_div_gcd hBmap
  have hreduced : L * B' = A' * R.map sigma := by
    apply mul_left_cancel₀ hD
    calc
      D * (L * B') = L * (D * B') := by ring
      _ = L * B.map sigma := by rw [← hfactorB]
      _ = A * R.map sigma := hcross
      _ = (D * A') * R.map sigma := by rw [hfactorA]
      _ = D * (A' * R.map sigma) := by ring
  have hA'dvdL : A' ∣ L := by
    apply hcoprime.dvd_of_dvd_mul_right
    exact ⟨R.map sigma, hreduced⟩
  obtain ⟨T, hfactorL⟩ := hA'dvdL
  have hT : T ≠ 0 := by
    intro hzero
    apply hL
    rw [hfactorL, hzero, mul_zero]
  have hfactorR : R.map sigma = B' * T := by
    apply mul_left_cancel₀ hA'
    calc
      A' * R.map sigma = L * B' := hreduced.symm
      _ = (A' * T) * B' := by rw [hfactorL]
      _ = A' * (B' * T) := by ring
  have hdegreeA : D.natDegree + A'.natDegree = A.natDegree := by
    rw [hfactorA, Polynomial.natDegree_mul hD hA']
  have hdegreeB : D.natDegree + B'.natDegree = B.natDegree := by
    calc
      D.natDegree + B'.natDegree = (B.map sigma).natDegree := by
        rw [hfactorB, Polynomial.natDegree_mul hD hB']
      _ = B.natDegree :=
        Polynomial.natDegree_map_eq_of_injective sigma.injective B
  have hdegreeL : A'.natDegree + T.natDegree = L.natDegree := by
    rw [hfactorL, Polynomial.natDegree_mul hA' hT]
  have hdegreeR : B'.natDegree + T.natDegree = R.natDegree := by
    calc
      B'.natDegree + T.natDegree = (R.map sigma).natDegree := by
        rw [hfactorR, Polynomial.natDegree_mul hB' hT]
      _ = R.natDegree :=
        Polynomial.natDegree_map_eq_of_injective sigma.injective R
  refine ⟨D, A', B', T, ?_, hD, hA', hB', hT,
    hfactorA, hfactorB, hcoprime, hfactorL, hfactorR,
    hdegreeA, hdegreeB, hdegreeL, hdegreeR⟩
  rfl
theorem orbitCross_gcd_semantic_descent6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X]) (k : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0) (hLne : L ≠ 0) (hRne : R ≠ 0)
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hcross : L * B.map sigma = A * R.map sigma)
    (hspan : max L.natDegree R.natDegree ≤
      k + max A.natDegree B.natDegree) :
    ∃ D A' B' T : F[X],
      D = orbitOverlapGcd6401 A (B.map sigma) ∧
      D ≠ 0 ∧ A' ≠ 0 ∧ B' ≠ 0 ∧ T ≠ 0 ∧
      A = D * A' ∧ B.map sigma = D * B' ∧
      IsCoprime A' B' ∧
      L = A' * T ∧ R.map sigma = B' * T ∧
      T.natDegree ≤ k + D.natDegree ∧
      ∀ i, T.eval (alpha i) =
        D.eval (alpha i) * sigma (u i) := by
  obtain ⟨D, A', B', T, hDdef, hD, hA', hB', hT,
      hfactorA, hfactorB, hcoprime, hfactorL, hfactorR,
      hdegreeA, hdegreeB, hdegreeL, hdegreeR⟩ :=
    orbitCross_gcd_factorization6401 sigma A B L R
      hA hB hLne hRne hcross
  have hTdegree : T.natDegree ≤ k + D.natDegree := by
    by_cases hres : A'.natDegree ≤ B'.natDegree
    · have hAB : A.natDegree ≤ B.natDegree := by omega
      have hRmax : R.natDegree ≤ max L.natDegree R.natDegree :=
        Nat.le_max_right _ _
      rw [max_eq_right hAB] at hspan
      omega
    · have hres' : B'.natDegree ≤ A'.natDegree := by omega
      have hBA : B.natDegree ≤ A.natDegree := by omega
      have hLmax : L.natDegree ≤ max L.natDegree R.natDegree :=
        Nat.le_max_left _ _
      rw [max_eq_left hBA] at hspan
      omega
  refine ⟨D, A', B', T, hDdef, hD, hA', hB', hT,
    hfactorA, hfactorB, hcoprime, hfactorL, hfactorR, hTdegree, ?_⟩
  intro i
  have hnotBoth := Polynomial.aeval_ne_zero_of_isCoprime
    hcoprime (alpha i)
  rcases hnotBoth with hAi | hBi
  · apply mul_left_cancel₀ hAi
    calc
      A'.eval (alpha i) * T.eval (alpha i) = L.eval (alpha i) := by
        rw [hfactorL, Polynomial.eval_mul]
      _ = A.eval (alpha i) * sigma (u i) := hL i
      _ = (D.eval (alpha i) * A'.eval (alpha i)) * sigma (u i) := by
        rw [hfactorA, Polynomial.eval_mul]
      _ = A'.eval (alpha i) *
          (D.eval (alpha i) * sigma (u i)) := by ring
  · apply mul_left_cancel₀ hBi
    calc
      B'.eval (alpha i) * T.eval (alpha i) =
          (R.map sigma).eval (alpha i) := by
        rw [hfactorR, Polynomial.eval_mul]
      _ = sigma (R.eval (alpha i)) :=
        eval_map_eq_map_eval_of_fixed sigma R (alpha i) (hfixed i)
      _ = sigma (B.eval (alpha i) * u i) := by rw [hR i]
      _ = sigma (B.eval (alpha i)) * sigma (u i) := by rw [map_mul]
      _ = (B.map sigma).eval (alpha i) * sigma (u i) := by
        rw [eval_map_eq_map_eval_of_fixed sigma B (alpha i) (hfixed i)]
      _ = (D.eval (alpha i) * B'.eval (alpha i)) * sigma (u i) := by
        rw [hfactorB, Polynomial.eval_mul]
      _ = B'.eval (alpha i) *
          (D.eval (alpha i) * sigma (u i)) := by ring
theorem exists_orbitOverlap_rationalDirection6401
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : F →+* F)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (alpha : I ↪ F) (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X]) (k d : Nat)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hAdegree : A.natDegree ≤ d)
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hcross : L * B.map sigma = A * R.map sigma)
    (hspan : max L.natDegree R.natDegree ≤
      k + max A.natDegree B.natDegree) :
    ∃ Q V : F[X],
      Q ≠ 0 ∧ Q.natDegree ≤ d ∧
      V.natDegree ≤ k + Q.natDegree ∧
      ∀ i, V.eval (alpha i) = Q.eval (alpha i) * u i := by
  by_cases hLzero : L = 0
  · let Q := fifthCoefficientTwist6401 sigma A
    refine ⟨Q, 0, fifthCoefficientTwist_ne_zero6401 sigma A hA,
      ?_, by simp, ?_⟩
    · rw [fifthCoefficientTwist_natDegree_eq6401]
      exact hAdegree
    · intro i
      have hproduct : A.eval (alpha i) * sigma (u i) = 0 := by
        rw [← hL i, hLzero, Polynomial.eval_zero]
      have htwist := congrArg (fifthScalarTwist6401 sigma) hproduct
      rw [fifthScalarTwist_mul6401,
        fifthScalarTwist_sigma_eq6401 sigma horder] at htwist
      simpa only [Polynomial.eval_zero, Q,
        fifthCoefficientTwist_eval_fixed6401 sigma A (alpha i) (hfixed i),
        fifthScalarTwist6401, map_zero] using htwist.symm
  · have hRne : R ≠ 0 := by
      intro hRzero
      have hBmap : B.map sigma ≠ 0 :=
        (Polynomial.map_ne_zero_iff sigma.injective).2 hB
      have hzero : L * B.map sigma = 0 := by
        rw [hcross, hRzero, Polynomial.map_zero, mul_zero]
      exact hLzero ((mul_eq_zero.mp hzero).resolve_right hBmap)
    obtain ⟨D, A', B', T, hDdef, hD, hA', hB', hT,
        hfactorA, hfactorB, hcoprime, hfactorL, hfactorR,
        hTdegree, hTeval⟩ :=
      orbitCross_gcd_semantic_descent6401 sigma alpha hfixed u
        A B L R k hA hB hLzero hRne hL hR hcross hspan
    let Q := fifthCoefficientTwist6401 sigma D
    let V := fifthCoefficientTwist6401 sigma T
    have hDdegree : D.natDegree ≤ d := by
      have hDdvd : D ∣ A := ⟨A', hfactorA⟩
      exact (Polynomial.natDegree_le_of_dvd hDdvd hA).trans hAdegree
    have hQdegree : Q.natDegree = D.natDegree :=
      fifthCoefficientTwist_natDegree_eq6401 sigma D
    have hVdegree : V.natDegree = T.natDegree :=
      fifthCoefficientTwist_natDegree_eq6401 sigma T
    refine ⟨Q, V, fifthCoefficientTwist_ne_zero6401 sigma D hD,
      hQdegree.le.trans hDdegree, ?_, ?_⟩
    · rw [hVdegree, hQdegree]
      exact hTdegree
    · intro i
      have htwist := congrArg (fifthScalarTwist6401 sigma) (hTeval i)
      rw [fifthScalarTwist_mul6401,
        fifthScalarTwist_sigma_eq6401 sigma horder] at htwist
      simpa only [Q, V,
        fifthCoefficientTwist_eval_fixed6401 sigma T (alpha i) (hfixed i),
        fifthCoefficientTwist_eval_fixed6401 sigma D (alpha i) (hfixed i)]
        using htwist
theorem clearedRationalDirection_ownerTransform6401
    {I OwnerIndex : Type*}
    (alpha : I → F) (u0 u1 : I → F)
    (S : OwnerIndex → Prop) (challenge : OwnerIndex → F)
    (Owner : OwnerIndex → F[X]) (Agree : OwnerIndex → I → Prop)
    (Q V : F[X]) (k d : Nat)
    (hQdegree : Q.natDegree ≤ d)
    (hVdegree : V.natDegree ≤ k + d)
    (hdirection : ∀ i, V.eval (alpha i) = Q.eval (alpha i) * u1 i)
    (hOwnerDegree : ∀ z, S z → (Owner z).natDegree ≤ k)
    (howner : ∀ z, S z → ∀ i, Agree z i →
      (Owner z).eval (alpha i) = u0 i + challenge z * u1 i) :
    ∀ z, S z →
      (Q * Owner z - Polynomial.C (challenge z) * V).natDegree ≤ k + d ∧
      ∀ i, Agree z i →
        (Q * Owner z - Polynomial.C (challenge z) * V).eval (alpha i) =
          Q.eval (alpha i) * u0 i := by
  intro z hz
  constructor
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add hQdegree (hOwnerDegree z hz)) |>.trans (by omega)
    · exact Polynomial.natDegree_mul_le.trans (by
        simpa using hVdegree)
  · intro i hi
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [howner z hz i hi, hdirection i]
    ring
theorem clearedOwnerTransform_injective_of_not_dvd6401
    {OwnerIndex : Type*}
    (challenge : OwnerIndex ↪ F) (Owner : OwnerIndex → F[X])
    (Q V : F[X]) (hnot : ¬ Q ∣ V) :
    Function.Injective
      (fun z ↦ Q * Owner z - Polynomial.C (challenge z) * V) := by
  intro z w heq
  by_contra hzw
  have hchallenge : challenge z - challenge w ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ hzw (challenge.injective h))
  have hscaled : Polynomial.C (challenge z - challenge w) * V =
      Q * (Owner z - Owner w) := by
    rw [map_sub]
    linear_combination -heq
  apply hnot
  refine ⟨Polynomial.C ((challenge z - challenge w)⁻¹) *
      (Owner z - Owner w), ?_⟩
  calc
    V = Polynomial.C ((challenge z - challenge w)⁻¹) *
        (Polynomial.C (challenge z - challenge w) * V) := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      simp [hchallenge]
    _ = Polynomial.C ((challenge z - challenge w)⁻¹) *
        (Q * (Owner z - Owner w)) := by rw [hscaled]
    _ = Q * (Polynomial.C ((challenge z - challenge w)⁻¹) *
        (Owner z - Owner w)) := by ring
theorem polynomialDirection_away_of_rationalDirection_dvd6401
    {I : Type*} (alpha : I → F) (u : I → F)
    (Q V : F[X]) (k : Nat) (hQ : Q ≠ 0)
    (hVdegree : V.natDegree ≤ k + Q.natDegree)
    (hdirection : ∀ i, V.eval (alpha i) = Q.eval (alpha i) * u i)
    (hdvd : Q ∣ V) :
    ∃ W : F[X], V = Q * W ∧ W.natDegree ≤ k ∧
      ∀ i, Q.eval (alpha i) ≠ 0 → W.eval (alpha i) = u i := by
  obtain ⟨W, hfactor⟩ := hdvd
  have hWdegree : W.natDegree ≤ k := by
    by_cases hW : W = 0
    · simp [hW]
    · have hdegree : V.natDegree = Q.natDegree + W.natDegree := by
        rw [hfactor, Polynomial.natDegree_mul hQ hW]
      omega
  refine ⟨W, hfactor, hWdegree, ?_⟩
  intro i hQi
  apply mul_left_cancel₀ hQi
  calc
    Q.eval (alpha i) * W.eval (alpha i) = V.eval (alpha i) := by
      rw [hfactor, Polynomial.eval_mul]
    _ = Q.eval (alpha i) * u i := hdirection i
end GcdCross
section FiveOrbitPartition
variable {F : Type*} [Field F]
theorem exists_fiveOrbit_overlapPartition6401
    (sigma : F →+* F) (A B : F[X]) (d : Nat)
    (hA : A ≠ 0)
    (hcoprime : IsCoprime A B)
    (hnorm : polynomialFrobeniusNormSix sigma A =
      polynomialFrobeniusNormSix sigma B)
    (hAdegree : A.natDegree ≤ d) :
    ∃ C1 C2 C3 C4 C5 : F[X],
      C1 ≠ 0 ∧ C2 ≠ 0 ∧ C3 ≠ 0 ∧ C4 ≠ 0 ∧ C5 ≠ 0 ∧
      A = C1 * C2 * C3 * C4 * C5 ∧
      C1 ∣ A ∧ C2 ∣ A ∧ C3 ∣ A ∧ C4 ∣ A ∧ C5 ∣ A ∧
      C1 ∣ B.map sigma ∧
      C2 ∣ (B.map sigma).map sigma ∧
      C3 ∣ ((B.map sigma).map sigma).map sigma ∧
      C4 ∣ (((B.map sigma).map sigma).map sigma).map sigma ∧
      C5 ∣ ((((B.map sigma).map sigma).map sigma).map sigma).map sigma ∧
      C1.natDegree + C2.natDegree + C3.natDegree +
          C4.natDegree + C5.natDegree = A.natDegree ∧
      C1.natDegree + C2.natDegree + C3.natDegree +
          C4.natDegree + C5.natDegree ≤ d := by
  classical
  letI : GCDMonoid (Polynomial F) :=
    EuclideanDomain.gcdMonoid (Polynomial F)
  let B1 := B.map sigma
  let B2 := B1.map sigma
  let B3 := B2.map sigma
  let B4 := B3.map sigma
  let B5 := B4.map sigma
  have hAdivNormB : A ∣ B * B1 * B2 * B3 * B4 * B5 := by
    change A ∣ polynomialFrobeniusNormSix sigma B
    rw [← hnorm]
    refine ⟨(A.map sigma) * ((A.map sigma).map sigma) *
      (((A.map sigma).map sigma).map sigma) *
      ((((A.map sigma).map sigma).map sigma).map sigma) *
      (((((A.map sigma).map sigma).map sigma).map sigma).map sigma), ?_⟩
    dsimp [polynomialFrobeniusNormSix]
    ring
  have hAdivRest : A ∣ B1 * (B2 * (B3 * (B4 * B5))) := by
    apply hcoprime.dvd_of_dvd_mul_left
    simpa [mul_assoc] using hAdivNormB
  obtain ⟨C1, A1, hC1B, hA1rest, hAfac1⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hAdivRest
  obtain ⟨C2, A2, hC2B, hA2rest, hAfac2⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hA1rest
  obtain ⟨C3, A3, hC3B, hA3rest, hAfac3⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hA2rest
  obtain ⟨C4, C5, hC4B, hC5B, hAfac4⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hA3rest
  have hfactor : A = C1 * C2 * C3 * C4 * C5 := by
    rw [hAfac1, hAfac2, hAfac3, hAfac4]
    ring
  have hC1 : C1 ≠ 0 := by
    intro hz
    apply hA
    rw [hfactor, hz]
    simp
  have hC2 : C2 ≠ 0 := by
    intro hz
    apply hA
    rw [hfactor, hz]
    simp
  have hC3 : C3 ≠ 0 := by
    intro hz
    apply hA
    rw [hfactor, hz]
    simp
  have hC4 : C4 ≠ 0 := by
    intro hz
    apply hA
    rw [hfactor, hz]
    simp
  have hC5 : C5 ≠ 0 := by
    intro hz
    apply hA
    rw [hfactor, hz]
    simp
  have hC1A : C1 ∣ A := by
    refine ⟨C2 * C3 * C4 * C5, ?_⟩
    rw [hfactor]
    ring
  have hC2A : C2 ∣ A := by
    refine ⟨C1 * C3 * C4 * C5, ?_⟩
    rw [hfactor]
    ring
  have hC3A : C3 ∣ A := by
    refine ⟨C1 * C2 * C4 * C5, ?_⟩
    rw [hfactor]
    ring
  have hC4A : C4 ∣ A := by
    refine ⟨C1 * C2 * C3 * C5, ?_⟩
    rw [hfactor]
    ring
  have hC5A : C5 ∣ A := by
    refine ⟨C1 * C2 * C3 * C4, ?_⟩
    rw [hfactor]
    ring
  have hdegree : C1.natDegree + C2.natDegree + C3.natDegree +
      C4.natDegree + C5.natDegree = A.natDegree := by
    rw [hfactor,
      Polynomial.natDegree_mul
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hC1 hC2) hC3) hC4) hC5,
      Polynomial.natDegree_mul
        (mul_ne_zero (mul_ne_zero hC1 hC2) hC3) hC4,
      Polynomial.natDegree_mul (mul_ne_zero hC1 hC2) hC3,
      Polynomial.natDegree_mul hC1 hC2]
  refine ⟨C1, C2, C3, C4, C5, hC1, hC2, hC3, hC4, hC5,
    hfactor, hC1A, hC2A, hC3A, hC4A, hC5A,
    ?_, ?_, ?_, ?_, ?_, hdegree, hdegree.le.trans hAdegree⟩
  · simpa [B1] using hC1B
  · simpa [B1, B2] using hC2B
  · simpa [B1, B2, B3] using hC3B
  · simpa [B1, B2, B3, B4] using hC4B
  · simpa [B1, B2, B3, B4, B5] using hC5B
end FiveOrbitPartition
end BCHKSExtremePrimitiveOrbitOverlapDescent6401
end ProximityPrize.SubmissionLower
