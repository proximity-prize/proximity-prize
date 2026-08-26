import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusTailFixedPairGlobalKernel6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveOrbitCrossAlgebra6401
open Polynomial
open BCHKSFrobeniusHighSupportResidual6401
open BCHKSSubfieldFrobenius6401
open BCHKSExtremePrimitiveFixedPairSlopeDescentNoGo6401
open BCHKSFrobeniusTailFailureSpace6401
open BCHKSFrobeniusReceivedTailMatrix6401
open BCHKSFrobeniusTailKernelSufficiency6401
open BCHKSFrobeniusTailFixedPairGlobalKernel6401
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
section Algebra
variable {F : Type*} [Field F] [DecidableEq F]
variable {sigma : F →+* F}
theorem exists_primitiveQuotientCross6401
    (H U0 U1 L R : F[X]) (hH : H ≠ 0)
    (hHmap : H.map sigma = H)
    (hcross : L * (H * U1).map sigma = (H * U0) * R.map sigma)
    (hLdiv : H ∣ L) (hRdiv : H ∣ R) :
    ∃ L0 R0 : F[X], L = H * L0 ∧ R = H * R0 ∧
      L0 * U1.map sigma = U0 * R0.map sigma := by
  obtain ⟨L0, hL0⟩ := hLdiv
  obtain ⟨R0, hR0⟩ := hRdiv
  refine ⟨L0, R0, hL0, hR0, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hH hH)
  calc
    (H * H) * (L0 * U1.map sigma) =
        (H * L0) * (H * U1.map sigma) := by ac_rfl
    _ = L * (H * U1).map sigma := by
      rw [hL0, Polynomial.map_mul, hHmap]
    _ = (H * U0) * R.map sigma := hcross
    _ = (H * U0) * (H * R0.map sigma) := by
      rw [hR0, Polynomial.map_mul, hHmap]
    _ = (H * H) * (U0 * R0.map sigma) := by ac_rfl
theorem exists_primitiveSlopeFactor_of_quotientCross6401
    (U0 U1 L0 R0 : F[X]) (hU0 : U0 ≠ 0)
    (horbit : IsCoprime U0 (U1.map sigma))
    (hprimitive : L0 * U1.map sigma = U0 * R0.map sigma)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x) :
    ∃ V : F[X], L0 = U0 * V.map sigma ∧ R0 = U1 * V := by
  have hdvd : U0 ∣ L0 * U1.map sigma := ⟨R0.map sigma, hprimitive⟩
  obtain ⟨Q, hL0Q⟩ := horbit.dvd_of_dvd_mul_right hdvd
  have hR0map : R0.map sigma = U1.map sigma * Q := by
    apply mul_left_cancel₀ hU0
    calc
      U0 * R0.map sigma = L0 * U1.map sigma := hprimitive.symm
      _ = (U0 * Q) * U1.map sigma := by rw [hL0Q]
      _ = U0 * (U1.map sigma * Q) := by ac_rfl
  let V : F[X] := (((((Q.map sigma).map sigma).map sigma).map sigma).map sigma)
  have hVmap : V.map sigma = Q :=
    polynomial_map_six_eq_self6401 sigma horder Q
  refine ⟨V, ?_, ?_⟩
  · rw [hL0Q, hVmap]
  · apply Polynomial.map_injective sigma sigma.injective
    rw [Polynomial.map_mul, hVmap]
    exact hR0map
theorem adaptiveMax_add_cancel6401
    (h u0 u1 v k : Nat)
    (hleft : h + u0 + v ≤ k + max (h + u0) (h + u1))
    (hright : h + u1 + v ≤ k + max (h + u0) (h + u1)) :
    v ≤ k := by
  by_cases hle : u0 ≤ u1
  · rw [max_eq_right (Nat.add_le_add_left hle h)] at hright
    omega
  · have hle' : u1 ≤ u0 := by omega
    rw [max_eq_left (Nat.add_le_add_left hle' h)] at hleft
    omega
theorem primitiveCommonSlopeFactor_natDegree_le6401
    (H U0 U1 L R V : F[X]) (k : Nat)
    (hH : H ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hLfactor : L = H * (U0 * V.map sigma))
    (hRfactor : R = H * (U1 * V))
    (hLDeg : L.natDegree ≤ k + max (H * U0).natDegree (H * U1).natDegree)
    (hRDeg : R.natDegree ≤ k + max (H * U0).natDegree (H * U1).natDegree) :
    V.natDegree ≤ k := by
  by_cases hV : V = 0
  · simp [hV]
  · have hVmapne : V.map sigma ≠ 0 :=
      (Polynomial.map_ne_zero_iff sigma.injective).2 hV
    have hLexact : L.natDegree =
        H.natDegree + U0.natDegree + V.natDegree := by
      calc
        L.natDegree = (H * (U0 * V.map sigma)).natDegree :=
          congrArg Polynomial.natDegree hLfactor
        _ = H.natDegree + (U0 * V.map sigma).natDegree :=
          Polynomial.natDegree_mul hH (mul_ne_zero hU0 hVmapne)
        _ = H.natDegree +
            (U0.natDegree + (V.map sigma).natDegree) := by
          rw [Polynomial.natDegree_mul hU0 hVmapne]
        _ = H.natDegree + U0.natDegree + V.natDegree := by
          rw [Polynomial.natDegree_map_eq_of_injective sigma.injective]
          omega
    have hRexact : R.natDegree =
        H.natDegree + U1.natDegree + V.natDegree := by
      calc
        R.natDegree = (H * (U1 * V)).natDegree :=
          congrArg Polynomial.natDegree hRfactor
        _ = H.natDegree + (U1 * V).natDegree :=
          Polynomial.natDegree_mul hH (mul_ne_zero hU1 hV)
        _ = H.natDegree + (U1.natDegree + V.natDegree) := by
          rw [Polynomial.natDegree_mul hU1 hV]
        _ = H.natDegree + U1.natDegree + V.natDegree := by omega
    have hHU0 : (H * U0).natDegree = H.natDegree + U0.natDegree :=
      Polynomial.natDegree_mul hH hU0
    have hHU1 : (H * U1).natDegree = H.natDegree + U1.natDegree :=
      Polynomial.natDegree_mul hH hU1
    apply adaptiveMax_add_cancel6401 H.natDegree U0.natDegree U1.natDegree
      V.natDegree k
    · simpa [hLexact, hHU0, hHU1] using hLDeg
    · simpa [hRexact, hHU0, hHU1] using hRDeg
theorem coprime_eval_ne_zero_or6401
    (U0 U1 : F[X]) (x : F) (hcop : IsCoprime U0 U1) :
    U0.eval x ≠ 0 ∨ U1.eval x ≠ 0 := by
  by_cases h0 : U0.eval x = 0
  · right
    intro h1
    have hc := hcop.map (Polynomial.evalRingHom x)
    simp [h0, h1] at hc
  · exact Or.inl h0
theorem primitiveCommonSlopeFactor_eval_eq6401
    (H U0 U1 L R V : F[X]) (x u : F)
    (hfixed : sigma x = x) (hcop : IsCoprime U0 U1)
    (hHat : H.eval x ≠ 0)
    (hLeval : L.eval x = (H * U0).eval x * sigma u)
    (hReval : R.eval x = (H * U1).eval x * u)
    (hLfactor : L = H * (U0 * V.map sigma))
    (hRfactor : R = H * (U1 * V)) :
    V.eval x = u := by
  rcases coprime_eval_ne_zero_or6401 U0 U1 x hcop with hU0at | hU1at
  · have heq : (H.eval x * U0.eval x) * sigma (V.eval x) =
        (H.eval x * U0.eval x) * sigma u := by
      calc
        _ = L.eval x := by
          rw [hLfactor, Polynomial.eval_mul, Polynomial.eval_mul,
            eval_map_eq_map_eval_of_fixed sigma V x hfixed]
          ac_rfl
        _ = _ := by simpa [Polynomial.eval_mul, mul_assoc] using hLeval
    exact sigma.injective
      (mul_left_cancel₀ (mul_ne_zero hHat hU0at) heq)
  · have heq : (H.eval x * U1.eval x) * V.eval x =
        (H.eval x * U1.eval x) * u := by
      calc
        _ = R.eval x := by
          rw [hRfactor, Polynomial.eval_mul, Polynomial.eval_mul]
          ac_rfl
        _ = _ := by simpa [Polynomial.eval_mul, mul_assoc] using hReval
    exact mul_left_cancel₀ (mul_ne_zero hHat hU1at) heq
theorem exists_commonSlopeFactor_of_invariantDivisibleCross6401
    (H U0 U1 L R : F[X]) (k : Nat)
    (hH : H ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hcop : IsCoprime U0 U1)
    (hHmap : H.map sigma = H)
    (hcross : L * (H * U1).map sigma = (H * U0) * R.map sigma)
    (hLdiv : H ∣ L) (hRdiv : H ∣ R)
    (hLDeg : L.natDegree ≤ k + max (H * U0).natDegree (H * U1).natDegree)
    (hRDeg : R.natDegree ≤ k + max (H * U0).natDegree (H * U1).natDegree)
    (horbit : IsCoprime U0 (U1.map sigma))
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x) :
    ∃ V : F[X], V.natDegree ≤ k ∧
      L = H * (U0 * V.map sigma) ∧
      R = H * (U1 * V) ∧
      ∀ x u : F, sigma x = x → H.eval x ≠ 0 →
        L.eval x = (H * U0).eval x * sigma u →
        R.eval x = (H * U1).eval x * u → V.eval x = u := by
  obtain ⟨L0, R0, hL0, hR0, hprimitive⟩ :=
    exists_primitiveQuotientCross6401
      H U0 U1 L R hH hHmap hcross hLdiv hRdiv
  obtain ⟨V, hL0factor, hR0factor⟩ :=
    exists_primitiveSlopeFactor_of_quotientCross6401
      U0 U1 L0 R0 hU0 horbit hprimitive horder
  have hLfactor : L = H * (U0 * V.map sigma) := by
    rw [hL0, hL0factor]
  have hRfactor : R = H * (U1 * V) := by
    rw [hR0, hR0factor]
  have hVdegree : V.natDegree ≤ k :=
    primitiveCommonSlopeFactor_natDegree_le6401
      H U0 U1 L R V k hH hU0 hU1 hLfactor hRfactor hLDeg hRDeg
  refine ⟨V, hVdegree, hLfactor, hRfactor, ?_⟩
  intro x u hfixed hHat hLeval hReval
  exact primitiveCommonSlopeFactor_eval_eq6401
    H U0 U1 L R V x u hfixed hcop hHat hLeval hReval
      hLfactor hRfactor
end Algebra
section BoundedCross
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
theorem slopeInterpolants_cross_of_uniformDegreeCaps6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (u : I → F) (A B L R : F[X]) (k d D : Nat)
    (hL : ∀ i, L.eval (alpha i) = A.eval (alpha i) * sigma (u i))
    (hR : ∀ i, R.eval (alpha i) = B.eval (alpha i) * u i)
    (hLdegree : L.natDegree ≤ k + d) (hRdegree : R.natDegree ≤ k + d)
    (hAdegree : A.natDegree ≤ d) (hBdegree : B.natDegree ≤ d)
    (hd : d ≤ D) (htotal : k + D + D < Fintype.card I) :
    L * B.map sigma = A * R.map sigma := by
  have hBmap : (B.map sigma).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hBdegree
  have hRmap : (R.map sigma).natDegree ≤ k + d :=
    Polynomial.natDegree_map_le.trans hRdegree
  have hdegLeft : (L * B.map sigma).natDegree < Fintype.card I := by
    have hp : (L * B.map sigma).natDegree ≤ (k + d) + d :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add hLdegree hBmap)
    have hb : (k + d) + d ≤ k + D + D := by omega
    exact (hp.trans hb).trans_lt htotal
  have hdegRight : (A * R.map sigma).natDegree < Fintype.card I := by
    have hp : (A * R.map sigma).natDegree ≤ d + (k + d) :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add hAdegree hRmap)
    have hb : d + (k + d) ≤ k + D + D := by omega
    exact (hp.trans hb).trans_lt htotal
  exact slopeInterpolants_cross_identity6401 sigma alpha hfixed u A B L R
      hL hR hdegLeft hdegRight
end BoundedCross
section DecodedTailPair
variable {F I : Type*} [Field F] [DecidableEq F]
  [Fintype I] [Nonempty I] [DecidableEq I]
theorem receivedTail_threeProductDegrees_of_decodedPair6401
    (sigma : F →+* F) (alpha : I ↪ F) (u0 u1 : I → F)
    (q k d : Nat) (hq : 1 < q) (T : Finset F)
    (hsigma : ∀ z ∈ T, sigma z = z ^ q)
    (v : Fin (d + 1) ⊕ Fin (d + 1) → F)
    (A B : F[X]) (hdecode : tailPairPolynomial d v = (A, B))
    (hkernel : ∀ z ∈ T,
      (receivedTailMatrix6401 sigma alpha
        (fun i ↦ u0 i + z * u1 i) k d).mulVec v = 0)
    (hmass : q < T.card) (hwindow : k + d < Fintype.card I) :
    (receivedPairInterpolant6401 sigma alpha u0 A B).natDegree ≤ k + d ∧
      (receivedPairInterpolant6401 sigma alpha u1 A 0).natDegree ≤ k + d ∧
      (receivedPairInterpolant6401 sigma alpha u1 0 B).natDegree ≤ k + d := by
  have hproducts :=
    receivedTail_fixedPair_threeProductDegrees_of_manyOwners6401
      sigma alpha u0 u1 q k d hq T hsigma v hkernel hmass hwindow
  rw [hdecode] at hproducts
  exact hproducts
end DecodedTailPair
end BCHKSExtremePrimitiveOrbitCrossAlgebra6401
end ProximityPrize.SubmissionLower
