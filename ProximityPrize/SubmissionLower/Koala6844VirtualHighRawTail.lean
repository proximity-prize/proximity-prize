import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds
import ProximityPrize.SubmissionLower.Koala6844VirtualHighTrimRecurrence



namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic MvPolynomial RCN313 RCN136

noncomputable section

variable {K : Type} [Field K]

def trimDerivation (F : Carrier K) : Derivation K (Carrier K) (Carrier K) :=
  implicitRegularity F • pderiv 0 - (pderiv 0 F : Carrier K) • pderiv 1

theorem trimDerivation_apply (F A : Carrier K) :
    trimDerivation F A = clearedImplicit F A := by
  simp only [trimDerivation, clearedImplicit, Derivation.sub_apply,
    Derivation.smul_apply, smul_eq_mul]

def rawTrimmedTail (F V W : Carrier K) (n : ℕ) : Carrier K :=
  trimmedNumerator (trimDerivation F) (implicitRegularity F) V W n

private theorem natCast_mul_cap {i : Fin 4} (n : ℕ) {A : Carrier K} {d : ℕ}
    (h : A.degreeOf i ≤ d) : ((n : Carrier K)*A).degreeOf i ≤ d := by
  simpa only [zero_add] using
    degree_mul_bound i (le_of_eq (degree_natCast_eq_zero (K := K) i n)) h

private theorem implicit_seed_bound (F A : Carrier K) (i : Fin 4) (b a : ℕ)
    (hF : F.degreeOf i ≤ b) (hA : A.degreeOf i ≤ a) :
    (trimDerivation F A).degreeOf i ≤ b+a := by
  rw [trimDerivation_apply, clearedImplicit, implicitRegularity]
  exact degree_sub_bound i
    (degree_mul_bound i (pderiv_degree_bound 1 i F b hF) (pderiv_degree_bound 0 i A a hA))
    (degree_mul_bound i (pderiv_degree_bound 0 i F b hF) (pderiv_degree_bound 1 i A a hA))

private theorem implicit_value_bound (F A : Carrier K) (y a : ℕ)
    (hy : 1 ≤ y) (ha : 1 ≤ a) (hF : F.degreeOf 1 ≤ y) (hA : A.degreeOf 1 ≤ a) :
    (trimDerivation F A).degreeOf 1 ≤ y-1+a := by
  rw [trimDerivation_apply, clearedImplicit, implicitRegularity]
  apply degree_sub_bound
  · exact degree_mul_bound 1 (pderiv_same_degree_bound 1 F y hF)
      (pderiv_degree_bound 0 1 A a hA)
  · refine (degree_mul_bound 1 (pderiv_degree_bound 0 1 F y hF)
      (pderiv_same_degree_bound 1 A a hA)).trans ?_
    omega

theorem rawTrimmedTail_seed_degree (F V W : Carrier K) (i : Fin 4) (b C n : ℕ)
    (hF : F.degreeOf i ≤ b) (hV : V.degreeOf i ≤ 0) (hW : W.degreeOf i ≤ C) :
    (rawTrimmedTail F V W n).degreeOf i ≤ (2*n+1)*b+C := by
  have hH := pderiv_degree_bound 1 i F b hF
  let H := implicitRegularity F
  change H.degreeOf i ≤ b at hH
  have hDV := implicit_seed_bound F V i b 0 hF hV
  have hDH := implicit_seed_bound F H i b b hF hH
  induction n with
  | zero =>
    unfold rawTrimmedTail
    rw [trimmedNumerator]
    apply degree_sub_bound
    · simpa using degree_mul_bound i hV (implicit_seed_bound F W i b C hF hW)
    · simpa [Nat.add_comm] using degree_mul_bound i hW hDV
  | succ n ih =>
    let N := rawTrimmedTail F V W n
    have hN : N.degreeOf i ≤ (2*n+1)*b+C := ih
    have hD := implicit_seed_bound F N i b _ hF hN
    have hA := degree_mul_bound i (degree_mul_bound i hV hH) hD
    have hL := natCast_mul_cap (n+2) hH
    have hR := natCast_mul_cap (2*n+1) hV
    have hL' : ((((n+2 : ℕ) : Carrier K)*H) * trimDerivation F V).degreeOf i ≤ b+b := by
      simpa using degree_mul_bound i hL hDV
    have hR' : ((((2*n+1 : ℕ) : Carrier K)*V) * trimDerivation F H).degreeOf i ≤ b+b := by
      simpa using degree_mul_bound i hR hDH
    have hB := degree_mul_bound i (degree_add_bound i hL' hR') hN
    change (V*H*trimDerivation F N -
      ((((n+2 : ℕ) : Carrier K)*H)*trimDerivation F V +
       (((2*n+1 : ℕ) : Carrier K)*V)*trimDerivation F H)*N).degreeOf i ≤ _
    apply degree_sub_bound
    · refine hA.trans ?_
      ring_nf
      omega
    · refine hB.trans ?_
      ring_nf
      omega

theorem rawTrimmedTail_value_degree (F V W : Carrier K) (y n : ℕ)
    (hy : 1 ≤ y) (hF : F.degreeOf 1 ≤ y) (hV : V.degreeOf 1 ≤ 0)
    (hW : W.degreeOf 1 ≤ 1) :
    (rawTrimmedTail F V W n).degreeOf 1 ≤ 1+(2*n+1)*(y-1) := by
  let s := y-1
  have hH := pderiv_same_degree_bound 1 F y hF
  let H := implicitRegularity F
  change H.degreeOf 1 ≤ s at hH
  have hDV : (trimDerivation F V).degreeOf 1 ≤ s := by
    rw [trimDerivation_apply, clearedImplicit, pderiv_eq_zero_of_degree_bound_zero 1 V hV,
      mul_zero, sub_zero]
    simpa using degree_mul_bound 1 hH (pderiv_degree_bound 0 1 V 0 hV)
  have hDH : (trimDerivation F H).degreeOf 1 ≤ s+s := by
    by_cases hs : 1 ≤ s
    · exact implicit_value_bound F H y s hy hs hF hH
    · have hs0 : s = 0 := by omega
      have hH0 : H.degreeOf 1 ≤ 0 := by simpa only [hs0] using hH
      rw [trimDerivation_apply, clearedImplicit,
        pderiv_eq_zero_of_degree_bound_zero 1 H hH0, mul_zero, sub_zero]
      simpa only [hs0, zero_add] using
        degree_mul_bound 1 hH0 (pderiv_degree_bound 0 1 H 0 hH0)
  change (rawTrimmedTail F V W n).degreeOf 1 ≤ 1+(2*n+1)*s
  induction n with
  | zero =>
    unfold rawTrimmedTail
    rw [trimmedNumerator]
    have hD := implicit_value_bound F W y 1 (by omega) (by omega) hF hW
    apply degree_sub_bound
    · simpa [s, Nat.add_comm] using degree_mul_bound 1 hV hD
    · simpa using degree_mul_bound 1 hW hDV
  | succ n ih =>
    let N := rawTrimmedTail F V W n
    have hN : N.degreeOf 1 ≤ 1+(2*n+1)*s := ih
    have hD := implicit_value_bound F N y (1+(2*n+1)*s) (by omega) (by omega) hF hN
    have hA := degree_mul_bound 1 (degree_mul_bound 1 hV hH) hD
    have hL := natCast_mul_cap (n+2) hH
    have hR := natCast_mul_cap (2*n+1) hV
    have hL' : ((((n+2 : ℕ) : Carrier K)*H) * trimDerivation F V).degreeOf 1 ≤ s+s :=
      degree_mul_bound 1 hL hDV
    have hR' : ((((2*n+1 : ℕ) : Carrier K)*V) * trimDerivation F H).degreeOf 1 ≤ s+s := by
      simpa using degree_mul_bound 1 hR hDH
    have hB := degree_mul_bound 1 (degree_add_bound 1 hL' hR') hN
    change (V*H*trimDerivation F N -
      ((((n+2 : ℕ) : Carrier K)*H)*trimDerivation F V +
       (((2*n+1 : ℕ) : Carrier K)*V)*trimDerivation F H)*N).degreeOf 1 ≤ _
    apply degree_sub_bound
    · refine hA.trans ?_
      change 0+s+(s+(1+(2*n+1)*s)) ≤ 1+(2*(n+1)+1)*s
      ring_nf
      omega
    · refine hB.trans ?_
      ring_nf
      omega

theorem surface_rawTrimmedTail_degrees {L : Type} [Field L]
    (φ : Polynomial K →+* L) (F V W : Carrier K)
    (f : Rectangle) (n : ℕ) (hy : 1 ≤ f.value)
    (hF : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hV : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0)
    (hW : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000) :
    let T := surfaceMap φ (rawTrimmedTail F V W n)
    let cap := tailRectangle (n+1) f
    T.degreeOf 0 ≤ cap.value ∧ T.degreeOf 1 ≤ cap.first ∧ T.degreeOf 2 ≤ cap.second := by
  have hen : 2*(n+1)-1 = 2*n+1 := by omega
  simp only [tailRectangle, tailValue, hen]
  exact ⟨(surfaceMap_degreeOf_le φ _ 0).trans
      (rawTrimmedTail_value_degree F V W _ n hy hF.1 hV.1 hW.1),
    (surfaceMap_degreeOf_le φ _ 1).trans
      (rawTrimmedTail_seed_degree F V W 2 _ _ n hF.2.1 hV.2.1 hW.2.1),
    (surfaceMap_degreeOf_le φ _ 2).trans
      (rawTrimmedTail_seed_degree F V W 3 _ _ n hF.2.2 hV.2.2 hW.2.2)⟩

private def polynomialDerivation : Derivation K (Polynomial K) (Polynomial K) where
  toLinearMap := Polynomial.derivative
  map_one_eq_zero' := Polynomial.derivative_one
  leibniz' a b := by
    rw [Polynomial.derivative_mul]
    simp only [smul_eq_mul]
    ring

theorem graphSpecialize_rawTrimmedTail_eq_zero (F V W : Carrier K)
    (P Q : Polynomial K) (g h s : K) (n : ℕ)
    (carrier : graphSpecialize P g h F = 0)
    (trim : graphSpecialize P g h W =
      Polynomial.C s * graphSpecialize P g h V * Q)
    (hQ : Q.natDegree ≤ n) :
    graphSpecialize P g h (rawTrimmedTail F V W n) = 0 := by
  have commute (A : Carrier K) :
      graphSpecialize P g h (trimDerivation F A) = graphSpecialize P g h (implicitRegularity F) *
        polynomialDerivation (graphSpecialize P g h A) := by
    rw [trimDerivation_apply]
    exact graphSpecialize_clearedImplicit F A P g h carrier
  have fixed : polynomialDerivation (Polynomial.C s) = 0 := Polynomial.derivative_C
  have vanish : (polynomialDerivation (K := K)^[n+1]) Q = 0 :=
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_of_le hQ)
  exact map_trimmedNumerator_eq_zero (trimDerivation F) polynomialDerivation
    (implicitRegularity F) V W (graphSpecialize P g h) commute (Polynomial.C s) Q fixed trim n vanish


end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
