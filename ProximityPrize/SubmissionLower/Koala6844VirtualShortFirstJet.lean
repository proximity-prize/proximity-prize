import ProximityPrize.SubmissionLower.Koala6844VirtualShortWeight
import ProximityPrize.SubmissionLower.Koala6844ReceiptsClearing
import ProximityPrize.SubmissionLower.Koala6844ReceiptsContactKernel


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetCoefficients SecondJetSpecialize

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3100000

variable {K : Type*} [Field K]

def toFirstJet : Poly (K := K) →ₐ[K] MvPolynomial (Fin 4) K :=
  { toRingHom := (Polynomial.constantCoeff (R := MvPolynomial (Fin 4) K)).comp (asS (K := K)).toRingHom
    commutes' := by
      intro c
      have h := (asS (K := K)).commutes c
      change asS (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) at h
      change (asS (MvPolynomial.C c)).coeff 0 = MvPolynomial.C c
      rw [h,Polynomial.coeff_C_zero] }

@[simp] theorem toFirstJet_apply (P : Poly (K := K)) : toFirstJet P = (asS P).coeff 0 := rfl

private theorem asS_natDegree_le_zero (P : Poly (K := K))
    (hP : ∀ e ∈ P.support, e 1 = 0) : (asS P).natDegree ≤ 0 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := hP _ (coefficient_support P j e he)
  rw [(lift_coordinates j e).2.1] at h
  omega

def firstJetClearedLinear (D : ℕ → ℕ) (w wQ L B U q : ℕ) (A N : Poly (K := K)) :
    (NormalizedIndex D w wQ L B 0 U q → K) →ₗ[K] MvPolynomial (Fin 4) K :=
  toFirstJet.toLinearMap.comp ((clearAuxLinear A N q).comp (reconstructNormalized D w wQ L B 0 U q))

theorem firstJetClearedLinear_mem_nestedCoefficientBox
    (D : ℕ → ℕ) (w wQ L B U q a C : ℕ) (hUL : U ≤ L) (hqU : q ≤ U) (hcut : D 0 ≤ C)
    (A₀ A₁ d C₁ : Polynomial K) (h₀ : A₀.natDegree ≤ a) (h₁ : A₁.natDegree ≤ a)
    (hd : d.natDegree+w ≤ a+wQ) (hC : C₁.natDegree ≤ a+wQ)
    (c : NormalizedIndex D w wQ L B 0 U q → K) :
    firstJetClearedLinear D w wQ L B U q (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁) c ∈
      LocatorLowQuotient.nestedCoefficientBox K (C+q*a) w (L+q) U B := by
  let P := reconstructNormalized (K := K) D w wQ L B 0 U q c
  let F := clearAux (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁) q P
  have hsupp (j e) (he : e ∈ (P.coeff j).support) :=
    reconstructed_normalized_bounds D w wQ L B 0 U q (by omega) hUL hqU c j e he
  have hweight : ∀ e ∈ F.support, sourceWeight w e < C+q*a := by
    apply clear_normalized_weight A₀ A₁ d C₁ w wQ a q C h₀ h₁ hd hC
    intro j e he
    have hs := hsupp j e he
    have hzero : e 1 = 0 := Nat.eq_zero_of_le_zero hs.2.2.1
    rw [← hzero] at hcut
    exact hs.2.2.2.2.2.1.trans_le hcut
  have hshape := clear_normalized_support A₀ A₁ d C₁ B 0 U L q P
    (fun j e he => ⟨(hsupp j e he).2.1,(hsupp j e he).2.2.1,
      (hsupp j e he).2.2.2.1,(hsupp j e he).2.2.2.2.1⟩)
  intro e he
  change e ∈ ((asS F).coeff 0).support at he
  have hm := hshape _ (coefficient_support F 0 e he)
  obtain ⟨_,h1,h2,h3,h4⟩ := lift_coordinates 0 e
  rw [h1,h2,h3,h4] at hm
  exact ⟨by omega,by omega,by omega,firstJet_coefficient_weight F w (C+q*a) hweight e he⟩

theorem firstJetClearedLinear_injective (D : ℕ → ℕ) (w wQ L B U q : ℕ)
    (hUL : U ≤ L) (hqU : q ≤ U) (A₀ A₁ d C₁ : Polynomial K) (ha : A₁ ≠ 0) (hd : d ≠ 0) :
    Function.Injective (firstJetClearedLinear D w wQ L B U q
      (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁)) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro c hc
  let P := reconstructNormalized (K := K) D w wQ L B 0 U q c
  let F := clearAux (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁) q P
  have hsupp (j e) (he : e ∈ (P.coeff j).support) :=
    reconstructed_normalized_bounds D w wQ L B 0 U q (by omega) hUL hqU c j e he
  obtain ⟨a₀,a₁,b₀,b₁,hA,hB,ha₁,hdet⟩ := normalized_affine_elimination A₀ A₁ d C₁ ha hd
  apply normalizedClearing_injective D w wQ L B 0 U q (by omega) hUL hqU _ _
    a₀ a₁ b₀ b₁ hA hB ha₁ hdet
  rw [map_zero]
  change F = 0
  have hshape := clear_normalized_support A₀ A₁ d C₁ B 0 U L q P
    (fun j e he => ⟨(hsupp j e he).2.1,(hsupp j e he).2.2.1,
      (hsupp j e he).2.2.2.1,(hsupp j e he).2.2.2.2.1⟩)
  have hdeg := asS_natDegree_le_zero F (fun e he => Nat.eq_zero_of_le_zero (hshape e he).2.1)
  have heq : (asS F).coeff 0 = 0 := LinearMap.mem_ker.mp hc
  have hdvd := Polynomial.eq_C_of_natDegree_le_zero hdeg
  rw [heq, map_zero] at hdvd
  exact (asS (K := K)).injective (by simpa only [map_zero] using hdvd)

theorem firstJetClearedLinear_clearedForm (D : ℕ → ℕ) (w wQ L B U q : ℕ) (A N : Poly (K := K))
    (c : NormalizedIndex D w wQ L B 0 U q → K) :
    Koala6844Receipts.ClearedForm (toFirstJet A) (toFirstJet N) q (firstJetClearedLinear D w wQ L B U q A N c) := by
  let P := reconstructNormalized (K := K) D w wQ L B 0 U q c
  refine ⟨fun j => toFirstJet (P.coeff j.val),?_⟩
  change toFirstJet (clearAux A N q P) = _
  unfold clearAux
  simp only [map_sum,map_mul,map_pow]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => toFirstJet A^(q-j)*toFirstJet N^j*toFirstJet (P.coeff j))]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

private theorem toFirstJet_X0 : toFirstJet (K := K) (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  change (MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 0))).coeff 0 = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_left]
  exact congrArg (fun P : Polynomial (MvPolynomial (Fin 4) K) => P.coeff 0)
    (MvPolynomial.finSuccEquiv_X_succ (j := 0)) |>.trans Polynomial.coeff_C_zero

private theorem toFirstJet_X2 : toFirstJet (K := K) (MvPolynomial.X 2) = MvPolynomial.X 1 := by
  change (MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 2))).coeff 0 = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact congrArg (fun P : Polynomial (MvPolynomial (Fin 4) K) => P.coeff 0)
    (MvPolynomial.finSuccEquiv_X_succ (j := 1)) |>.trans Polynomial.coeff_C_zero

private theorem toFirstJet_X4 : toFirstJet (K := K) (MvPolynomial.X 4) = MvPolynomial.X 3 := by
  change (MvPolynomial.finSuccEquiv K 4
    (MvPolynomial.rename (Equiv.swap (0 : Fin 5) 1) (MvPolynomial.X 4))).coeff 0 = _
  rw [MvPolynomial.rename_X,Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  exact congrArg (fun P : Polynomial (MvPolynomial (Fin 4) K) => P.coeff 0)
    (MvPolynomial.finSuccEquiv_X_succ (j := 3)) |>.trans Polynomial.coeff_C_zero

private theorem toFirstJet_embed (p : Polynomial K) :
    toFirstJet (embedDisplacement p) = Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p := by
  have h : (toFirstJet (K := K)).comp embedDisplacement =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) := by
    apply Polynomial.algHom_ext
    simpa [embedDisplacement] using toFirstJet_X0 (K := K)
  exact DFunLike.congr_fun h p

theorem toFirstJet_normalizedDenominator (A₀ A₁ : Polynomial K) :
    toFirstJet (normalizedDenominator A₀ A₁) = Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) A₀ +
      MvPolynomial.X 3 * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) A₁ := by
  simp only [normalizedDenominator,map_add,map_mul,toFirstJet_embed,toFirstJet_X4,mul_comm]

theorem toFirstJet_normalizedNumerator (d C₁ : Polynomial K) :
    toFirstJet (normalizedNumerator d C₁) = Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) d * MvPolynomial.X 1 +
      MvPolynomial.X 3 * Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) C₁ := by
  simp only [normalizedNumerator,map_add,map_mul,toFirstJet_embed,toFirstJet_X2,toFirstJet_X4]
  rw [mul_comm (Polynomial.aeval (MvPolynomial.X 0) C₁)]




end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
