import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTwoRowOrbitCrossSlope6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitivePolynomialGaugeFullTail6401
open Polynomial
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSSubfieldFrobenius6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open BCHKSExtremePrimitiveTwoRowOrbitCrossSlope6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section AbstractGauge
variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
  [DecidableEq I]
theorem scalarPolynomialGauge_mul_fixed6401
    (sigma : F →+* F) (a b e k : F)
    (hnotBoth : a ≠ 0 ∨ b ≠ 0)
    (hfailure : a * sigma e = b * e)
    (hgauge : b * sigma k = a * k) :
    sigma (k * e) = k * e := by
  rcases hnotBoth with ha | hb
  · apply mul_left_cancel₀ ha
    calc
      a * sigma (k * e) = a * (sigma k * sigma e) := by rw [map_mul]
      _ = sigma k * (a * sigma e) := by ac_rfl
      _ = sigma k * (b * e) := by rw [hfailure]
      _ = (b * sigma k) * e := by ac_rfl
      _ = (a * k) * e := by rw [hgauge]
      _ = a * (k * e) := by ac_rfl
  · apply mul_left_cancel₀ hb
    calc
      b * sigma (k * e) = b * (sigma k * sigma e) := by rw [map_mul]
      _ = (b * sigma k) * sigma e := by ac_rfl
      _ = (a * k) * sigma e := by rw [hgauge]
      _ = k * (a * sigma e) := by ac_rfl
      _ = k * (b * e) := by rw [hfailure]
      _ = b * (k * e) := by ac_rfl
theorem polynomialGauge_scaledError_fixed6401
    (sigma : F →+* F) (alpha : I → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : I → F) (A B K : F[X])
    (hcop : IsCoprime A B)
    (hfailure : TwoLaneFailureRelation sigma alpha E A B)
    (hgauge : B * K.map sigma = A * K) :
    ∀ i, sigma (K.eval (alpha i) * E i) =
      K.eval (alpha i) * E i := by
  intro i
  have hnotBoth : A.eval (alpha i) ≠ 0 ∨ B.eval (alpha i) ≠ 0 := by
    simpa [Polynomial.aeval_def] using
      (Polynomial.aeval_ne_zero_of_isCoprime hcop (alpha i))
  have hgaugeAt :
      B.eval (alpha i) * sigma (K.eval (alpha i)) =
        A.eval (alpha i) * K.eval (alpha i) := by
    have h := congrArg (Polynomial.eval (alpha i)) hgauge
    simpa only [Polynomial.eval_mul,
      eval_map_eq_map_eval_of_fixed sigma K (alpha i) (hfixed i)] using h
  exact scalarPolynomialGauge_mul_fixed6401 sigma
    (A.eval (alpha i)) (B.eval (alpha i)) (E i)
    (K.eval (alpha i)) hnotBoth (hfailure i) hgaugeAt
theorem puncturedPolynomialGauge_fullScaledError_fixed6401
    (sigma : F →+* F) (alpha : I → F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (E : I → F) (L A B K : F[X])
    (hLmap : L.map sigma = L)
    (hcop : IsCoprime A B)
    (hfailure : TwoLaneFailureRelation sigma alpha E (L * A) (L * B))
    (hgauge : B * K.map sigma = A * K) :
    ∀ i, sigma ((L * K).eval (alpha i) * E i) =
      (L * K).eval (alpha i) * E i := by
  intro i
  by_cases hLi : L.eval (alpha i) = 0
  · simp [Polynomial.eval_mul, hLi]
  · have hbase : A.eval (alpha i) * sigma (E i) =
        B.eval (alpha i) * E i := by
      apply mul_left_cancel₀ hLi
      have hi := hfailure i
      simpa only [Polynomial.eval_mul, mul_assoc] using hi
    have hnotBoth : A.eval (alpha i) ≠ 0 ∨ B.eval (alpha i) ≠ 0 := by
      simpa [Polynomial.aeval_def] using
        (Polynomial.aeval_ne_zero_of_isCoprime hcop (alpha i))
    have hgaugeAt :
        B.eval (alpha i) * sigma (K.eval (alpha i)) =
          A.eval (alpha i) * K.eval (alpha i) := by
      have h := congrArg (Polynomial.eval (alpha i)) hgauge
      simpa only [Polynomial.eval_mul,
        eval_map_eq_map_eval_of_fixed sigma K (alpha i) (hfixed i)] using h
    have hKE := scalarPolynomialGauge_mul_fixed6401 sigma
      (A.eval (alpha i)) (B.eval (alpha i)) (E i)
      (K.eval (alpha i)) hnotBoth hbase hgaugeAt
    have hLfixed : sigma (L.eval (alpha i)) = L.eval (alpha i) := by
      calc
        sigma (L.eval (alpha i)) = (L.map sigma).eval (alpha i) :=
          (eval_map_eq_map_eval_of_fixed sigma L (alpha i) (hfixed i)).symm
        _ = L.eval (alpha i) := by rw [hLmap]
    simp only [Polynomial.eval_mul]
    calc
      sigma ((L.eval (alpha i) * K.eval (alpha i)) * E i) =
          sigma (L.eval (alpha i) * (K.eval (alpha i) * E i)) := by
            congr 1
            ac_rfl
      _ = sigma (L.eval (alpha i)) *
          sigma (K.eval (alpha i) * E i) := by rw [map_mul]
      _ = L.eval (alpha i) * (K.eval (alpha i) * E i) := by
        rw [hLfixed, hKE]
      _ = (L.eval (alpha i) * K.eval (alpha i)) * E i := by ac_rfl
noncomputable def fullWordInterpolant6401
    (alpha : I ↪ F) (v : I → F) : F[X] :=
  Lagrange.interpolate Finset.univ alpha v
theorem fullWordInterpolant_eval6401
    (alpha : I ↪ F) (v : I → F) (i : I) :
    (fullWordInterpolant6401 alpha v).eval (alpha i) = v i := by
  exact Lagrange.eval_interpolate_at_node v alpha.injective.injOn
    (Finset.mem_univ i)
theorem fullWordInterpolant_natDegree_lt6401
    (alpha : I ↪ F) (v : I → F)
    (hI : 0 < Fintype.card I) :
    (fullWordInterpolant6401 alpha v).natDegree < Fintype.card I := by
  let V := fullWordInterpolant6401 alpha v
  by_cases hV : V = 0
  · simpa [V, hV] using hI
  · rw [Polynomial.natDegree_lt_iff_degree_lt hV]
    change (Lagrange.interpolate Finset.univ alpha v).degree <
      ((Finset.univ : Finset I).card : WithBot Nat)
    exact Lagrange.degree_interpolate_lt v alpha.injective.injOn
theorem fullWordInterpolant_map_eq_self_of_fixed6401
    (sigma : F →+* F) (alpha : I ↪ F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (v : I → F) (hv : ∀ i, sigma (v i) = v i)
    (hI : 0 < Fintype.card I) :
    (fullWordInterpolant6401 alpha v).map sigma =
      fullWordInterpolant6401 alpha v := by
  classical
  let V := fullWordInterpolant6401 alpha v
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (V.map sigma) V ((Finset.univ : Finset I).map alpha)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    rw [eval_map_eq_map_eval_of_fixed sigma V (alpha i) (hfixed i)]
    have hVeval : V.eval (alpha i) = v i := by
      exact fullWordInterpolant_eval6401 alpha v i
    rw [hVeval, hv i]
  · rw [Finset.card_map, Finset.card_univ]
    apply max_lt
    · exact Polynomial.natDegree_map_le.trans_lt
        (fullWordInterpolant_natDegree_lt6401 alpha v hI)
    · exact fullWordInterpolant_natDegree_lt6401 alpha v hI
theorem scaledOwner_eq_receivedLine_add_errorInterpolant6401
    (alpha : I ↪ F) (T Owner : F[X]) (u0 u1 : I → F) (z : F)
    (hI : 0 < Fintype.card I)
    (hownerDegree : (T * Owner).natDegree < Fintype.card I) :
    T * Owner =
      fullWordInterpolant6401 alpha
          (fun i => T.eval (alpha i) * u0 i) +
        Polynomial.C z *
          fullWordInterpolant6401 alpha
            (fun i => T.eval (alpha i) * u1 i) +
        fullWordInterpolant6401 alpha
          (fun i => T.eval (alpha i) *
            (Owner.eval (alpha i) - (u0 i + z * u1 i))) := by
  classical
  let V0 := fullWordInterpolant6401 alpha
    (fun i => T.eval (alpha i) * u0 i)
  let V1 := fullWordInterpolant6401 alpha
    (fun i => T.eval (alpha i) * u1 i)
  let E := fullWordInterpolant6401 alpha
    (fun i => T.eval (alpha i) *
      (Owner.eval (alpha i) - (u0 i + z * u1 i)))
  have hV0 := fullWordInterpolant_natDegree_lt6401 alpha
    (fun i => T.eval (alpha i) * u0 i) hI
  have hV1 := fullWordInterpolant_natDegree_lt6401 alpha
    (fun i => T.eval (alpha i) * u1 i) hI
  have hE := fullWordInterpolant_natDegree_lt6401 alpha
    (fun i => T.eval (alpha i) *
      (Owner.eval (alpha i) - (u0 i + z * u1 i))) hI
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (T * Owner) (V0 + Polynomial.C z * V1 + E)
      ((Finset.univ : Finset I).map alpha)
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      show V0.eval (alpha i) = T.eval (alpha i) * u0 i by
        exact fullWordInterpolant_eval6401 alpha _ i,
      show V1.eval (alpha i) = T.eval (alpha i) * u1 i by
        exact fullWordInterpolant_eval6401 alpha _ i,
      show E.eval (alpha i) = T.eval (alpha i) *
          (Owner.eval (alpha i) - (u0 i + z * u1 i)) by
        exact fullWordInterpolant_eval6401 alpha _ i]
    ring
  · rw [Finset.card_map, Finset.card_univ]
    apply max_lt hownerDegree
    apply (Polynomial.natDegree_add_le _ _).trans_lt
    apply max_lt
    · apply (Polynomial.natDegree_add_le _ _).trans_lt
      apply max_lt hV0
      exact (Polynomial.natDegree_C_mul_le z V1).trans_lt hV1
    · exact hE
theorem scaledOwner_highCoefficient_relation6401
    (alpha : I ↪ F) (T Owner : F[X]) (u0 u1 : I → F) (z : F)
    (hI : 0 < Fintype.card I)
    (hownerDegree : (T * Owner).natDegree < Fintype.card I)
    (j : Nat) (hj : (T * Owner).natDegree < j) :
    (fullWordInterpolant6401 alpha
        (fun i => T.eval (alpha i) * u0 i)).coeff j +
      z * (fullWordInterpolant6401 alpha
        (fun i => T.eval (alpha i) * u1 i)).coeff j +
      (fullWordInterpolant6401 alpha
        (fun i => T.eval (alpha i) *
          (Owner.eval (alpha i) - (u0 i + z * u1 i)))).coeff j = 0 := by
  have hreconstruct := scaledOwner_eq_receivedLine_add_errorInterpolant6401
    alpha T Owner u0 u1 z hI hownerDegree
  have hcoeff := congrArg (fun P : F[X] => P.coeff j) hreconstruct
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj] at hcoeff
  simpa only [Polynomial.coeff_add, Polynomial.coeff_C_mul] using hcoeff.symm
end AbstractGauge
section PrimitiveSource
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → F[X]}
theorem twoRowPolynomialGauge_fullScaledError_fixed6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (A B K : F[X]) (z : F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hcop : IsCoprime A B)
    (hfailure : TwoLaneFailureRelation sigma alpha
      (fullOwnerError6401 W z)
      (twoRowSourcePunctureLocator6401 W * A)
      (twoRowSourcePunctureLocator6401 W * B))
    (hgauge : B * K.map sigma = A * K) :
    ∀ i,
      sigma ((twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
        fullOwnerError6401 W z i) =
      (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
        fullOwnerError6401 W z i := by
  exact puncturedPolynomialGauge_fullScaledError_fixed6401
    sigma alpha hfixed (fullOwnerError6401 W z)
    (twoRowSourcePunctureLocator6401 W) A B K
    (twoRowSourcePunctureLocator_map_eq_self6401 W hfixed)
    hcop hfailure hgauge
theorem twoRowPolynomialGauge_scaledOwner_natDegree_le_243606_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (A K : F[X]) (z : F)
    (hA : A ≠ 0)
    (haugmentedA :
      (twoRowSourcePunctureLocator6401 W * A).natDegree ≤
        homogeneousDirectionCap6401)
    (hKdegree : K.natDegree ≤ 5 * A.natDegree)
    (hOwnerDegree : (Owner z).natDegree ≤ ownerDegreeCap6401) :
    ((twoRowSourcePunctureLocator6401 W * K) * Owner z).natDegree ≤
      243606 := by
  let L := twoRowSourcePunctureLocator6401 W
  have hL : L ≠ 0 := twoRowSourcePunctureLocator_ne_zero6401 W
  have hLplusA : L.natDegree + A.natDegree ≤
      homogeneousDirectionCap6401 := by
    rw [← Polynomial.natDegree_mul hL hA]
    exact haugmentedA
  have hT := Polynomial.natDegree_mul_le (p := L) (q := K)
  have hTOwner := Polynomial.natDegree_mul_le
    (p := L * K) (q := Owner z)
  change (L * K * Owner z).natDegree ≤ 243606
  norm_num [ownerDegreeCap6401, homogeneousDirectionCap6401]
    at hLplusA hKdegree hOwnerDegree ⊢
  omega
theorem twoRowPolynomialGauge_errorInterpolant_map_eq_self6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (A B K : F[X]) (z : F)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hcop : IsCoprime A B)
    (hfailure : TwoLaneFailureRelation sigma alpha
      (fullOwnerError6401 W z)
      (twoRowSourcePunctureLocator6401 W * A)
      (twoRowSourcePunctureLocator6401 W * B))
    (hgauge : B * K.map sigma = A * K) :
    (fullWordInterpolant6401 alpha (fun i =>
      (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
        fullOwnerError6401 W z i)).map sigma =
      fullWordInterpolant6401 alpha (fun i =>
        (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
          fullOwnerError6401 W z i) := by
  apply fullWordInterpolant_map_eq_self_of_fixed6401
    sigma alpha hfixed
  · exact twoRowPolynomialGauge_fullScaledError_fixed6401
      W A B K z hfixed hcop hfailure hgauge
  · native_decide
theorem twoRowPolynomialGauge_scaledError_zero_iff_outside6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (K : F[X]) (z : F)
    (hKpoint : ∀ i, K.eval (alpha i) ≠ 0)
    (i : Fin n6401) (hi : i ∉ twoRowSourceBadCoordinates6401 W) :
    (twoRowSourcePunctureLocator6401 W * K).eval (alpha i) *
          fullOwnerError6401 W z i = 0 ↔
        fullOwnerError6401 W z i = 0 := by
  rw [Polynomial.eval_mul]
  have hmultiplier :
      (twoRowSourcePunctureLocator6401 W).eval (alpha i) *
          K.eval (alpha i) ≠ 0 :=
    mul_ne_zero (twoRowSourcePunctureLocator_eval_ne_zero6401 W i hi)
      (hKpoint i)
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left hmultiplier
  · intro hzero
    simp [hzero]
end PrimitiveSource
theorem polynomialGaugeFullTail_benchmarkLedger6401 :
    ownerDegreeCap6401 + 5 * homogeneousDirectionCap6401 = 243606 ∧
      243606 < n6401 ∧
      n6401 - (243606 + 1) = 18537 := by
  native_decide
end BCHKSExtremePrimitivePolynomialGaugeFullTail6401
end ProximityPrize.SubmissionLower
