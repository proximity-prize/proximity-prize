import ProximityPrize.SubmissionBinaryLower.BCHKSSingleFactor

/-!
# Inseparable factors in characteristic two

An irreducible factor `R(X,Y,Z)` with `∂R/∂Y = 0` cannot be fed to the Hensel
machinery.  There are two cases.

* `∂R/∂X ≠ 0`.  Differentiating `R(X, P_z(X), z) = 0` in `X` shows that
  `∂R/∂X` also vanishes on every selected root.  Since `R` is irreducible and
  `∂R/∂X` has smaller `X`-degree, the two are coprime, so their `Y`-resultant is
  a nonzero polynomial.  After specializing `X` at a good base point it is a
  nonzero polynomial in `Z` vanishing at every selected `z`; this bounds the
  number of selected challenges by `2 deg_Y(R) D_Z`, far below the capacity of
  the factor.
* `∂R/∂X = 0` as well, so `R ∈ F[Z][X²][Y²]`.  This case is handled by a
  Frobenius twist (below).
-/

namespace ProximityPrize.SubmissionBinaryLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

section DerivX

variable {A : Type*} [CommRing A]

/-- Differentiate every `Y`-coefficient in its own variable (the middle `X`). -/
noncomputable def dXPoly (f : Polynomial (Polynomial A)) : Polynomial (Polynomial A) :=
  ∑ j ∈ f.support, Polynomial.monomial j (Polynomial.derivative (f.coeff j))

@[simp] theorem coeff_dXPoly (f : Polynomial (Polynomial A)) (j : ℕ) :
    (dXPoly f).coeff j = Polynomial.derivative (f.coeff j) := by
  classical
  simp only [dXPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.derivative_zero]
    · intro b hb
      have : b ≠ j := fun h => hj (h ▸ hb)
      simp [this]

theorem natDegree_dXPoly_le (f : Polynomial (Polynomial A)) :
    (dXPoly f).natDegree ≤ f.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dXPoly, Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hj),
    Polynomial.derivative_zero]

theorem dXPoly_map {B : Type*} [CommRing B] (φ : A →+* B) (f : Polynomial (Polynomial A)) :
    (dXPoly f).map (Polynomial.mapRingHom φ) =
      dXPoly (f.map (Polynomial.mapRingHom φ)) := by
  ext1 j
  simp [Polynomial.coeff_map, Polynomial.derivative_map]

/-- Chain rule along an inseparable polynomial: if `∂f/∂Y = 0` then
`d/dX f(X, P(X)) = (∂f/∂X)(X, P(X))`. -/
theorem derivative_eval_of_derivative_eq_zero
    (f : Polynomial (Polynomial A)) (P : Polynomial A) (hf : f.derivative = 0) :
    Polynomial.derivative (f.eval P) = (dXPoly f).eval P := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self f.natDegree),
    Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_dXPoly_le f)
      (Nat.lt_succ_self f.natDegree)),
    Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.derivative_mul, coeff_dXPoly]
  have hzero : f.coeff j * Polynomial.derivative (P ^ j) = 0 := by
    cases j with
    | zero => simp
    | succ i =>
      have h := congrArg (fun g => g.coeff i) hf
      simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h
      rw [Polynomial.derivative_pow]
      calc f.coeff (i + 1) *
            (Polynomial.C ((↑(i + 1) : A)) * P ^ (i + 1 - 1) * Polynomial.derivative P) =
          (f.coeff (i + 1) * (↑i + 1)) * (P ^ (i + 1 - 1) * Polynomial.derivative P) := by
            rw [Polynomial.C_eq_natCast]
            push_cast
            ring
        _ = 0 := by rw [h, zero_mul]
  rw [hzero, add_zero]

end DerivX

section Dead

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Evaluating the middle variable at a constant does not raise the `Z`-degree. -/
theorem natDegree_eval_C_le_of_coeff
    (c : Polynomial (Polynomial F)) (x : F) (D : ℕ)
    (h : ∀ a, (c.coeff a).natDegree ≤ D) :
    (c.eval (Polynomial.C x)).natDegree ≤ D := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  rw [← Polynomial.C_pow]
  exact (Polynomial.natDegree_mul_le).trans (by simpa using h a)

theorem degreeX_dXPoly_lt (R : Polynomial (Polynomial (Polynomial F)))
    (hX : dXPoly R ≠ 0) :
    Polynomial.Bivariate.degreeX (dXPoly R) < Polynomial.Bivariate.degreeX R := by
  classical
  obtain ⟨j₀, hj₀⟩ := Polynomial.support_nonempty.mpr hX
  have hlt : ∀ j ∈ (dXPoly R).support,
      ((dXPoly R).coeff j).natDegree < Polynomial.Bivariate.degreeX R := by
    intro j hj
    have hne : (dXPoly R).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    rw [coeff_dXPoly] at hne ⊢
    have hc : R.coeff j ≠ 0 := by
      intro hz
      rw [hz, Polynomial.derivative_zero] at hne
      exact hne rfl
    have hdeg : (R.coeff j).natDegree ≠ 0 := by
      intro hz
      apply hne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.derivative_C]
    have h1 := Polynomial.natDegree_derivative_lt hdeg
    have h2 : (R.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX R := by
      unfold Polynomial.Bivariate.degreeX
      exact Finset.le_sup (f := fun n => (R.coeff n).natDegree)
        (Polynomial.mem_support_iff.mpr hc)
    omega
  have hpos : 0 < Polynomial.Bivariate.degreeX R := by
    have := hlt j₀ hj₀
    omega
  unfold Polynomial.Bivariate.degreeX
  exact (Finset.sup_lt_iff (by exact hpos)).mpr hlt

/-- An irreducible `R` does not divide its nonzero `X`-derivative. -/
theorem not_dvd_dXPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hX : dXPoly R ≠ 0) : ¬ R ∣ dXPoly R := by
  rintro ⟨M, hM⟩
  have hR : R ≠ 0 := by
    rintro rfl
    simp at hM
    exact hX hM
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
    exact hX hM
  have hdeg := Polynomial.Bivariate.degreeX_mul R M hR hM0
  rw [← hM] at hdeg
  have := degreeX_dXPoly_lt R hX
  omega

/-- Few challenges can have a root on a factor that is inseparable in `Y`
but not in `X`. -/
theorem dead_factor_card_le
    (R : Polynomial (Polynomial (Polynomial F)))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree)
    (hY : R.derivative = 0) (hX : dXPoly R ≠ 0)
    (DZ DX : ℕ)
    (hZcap : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ DZ)
    (hXcap : ∀ j, (R.coeff j).natDegree ≤ DX)
    (hF : 2 * R.natDegree * DX < Fintype.card F)
    (S : Finset F) (P : F → Polynomial F)
    (hvan : ∀ z ∈ S, triEval R z (P z) = 0) :
    S.card ≤ 2 * R.natDegree * DZ := by
  classical
  let D := dXPoly R
  let m := R.natDegree
  let n := D.natDegree
  have hnm : n ≤ m := natDegree_dXPoly_le R
  -- The `X`-derivative vanishes on every selected root as well.
  have hvanD : ∀ z ∈ S, triEval D z (P z) = 0 := by
    intro z hz
    have h0 := hvan z hz
    have hRz : (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).derivative = 0 := by
      rw [Polynomial.derivative_map, hY, Polynomial.map_zero]
    have hchain := derivative_eval_of_derivative_eq_zero
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) (P z) hRz
    rw [← dXPoly_map] at hchain
    unfold triEval at h0 ⊢
    rw [← hchain, h0, Polynomial.derivative_zero]
  -- The `Y`-resultant of `R` and `D` is nonzero.
  have hprim : R.IsPrimitive := hirr.isPrimitive (by omega)
  let A := Polynomial (Polynomial F)
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let RK : K[X] := R.map (algebraMap A K)
  let DK : K[X] := D.map (algebraMap A K)
  have hirrK : Irreducible RK := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hnotK : ¬ RK ∣ DK := fun h =>
    not_dvd_dXPoly R hX (hprim.dvd_of_fraction_map_dvd_fraction_map h)
  have hcop : IsCoprime RK DK := by
    by_contra hnot
    exact hnotK ((hirrK.dvd_iff_not_isCoprime).2 hnot)
  have hresK : RK.resultant DK ≠ 0 := Polynomial.resultant_ne_zero RK DK hcop
  have hRKdeg : RK.natDegree = m := Polynomial.natDegree_map_eq_of_injective hinj R
  have hDKdeg : DK.natDegree = n := Polynomial.natDegree_map_eq_of_injective hinj D
  have hRes : Polynomial.resultant R D m n ≠ 0 := by
    intro hz
    apply hresK
    have hmap := Polynomial.resultant_map_map R D m n (algebraMap A K)
    rw [hz, map_zero] at hmap
    change RK.resultant DK RK.natDegree DK.natDegree = 0
    rw [hRKdeg, hDKdeg]
    exact hmap
  -- Choose a base point `x₁` keeping the resultant nonzero.
  have hDcap : ∀ j, (D.coeff j).natDegree ≤ DX := by
    intro j
    rw [coeff_dXPoly]
    exact (Polynomial.natDegree_derivative_le _).trans (by have := hXcap j; omega)
  have hResdeg : (Polynomial.resultant R D m n).natDegree ≤ n * DX + m * DX :=
    Polynomial.natDegree_resultant_le_of_coeff_natDegree_le R D m n DX DX hXcap hDcap
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  let p : Unit → Polynomial (RatFunc F) := fun _ => (Polynomial.resultant R D m n).map g
  have hpne : ∀ r ∈ (Finset.univ : Finset Unit), p r ≠ 0 := by
    intro r _
    exact (Polynomial.map_ne_zero_iff hg).mpr hRes
  have hpdeg : (∑ r ∈ (Finset.univ : Finset Unit), (p r).natDegree) < Fintype.card F := by
    simp only [Finset.univ_unique, Finset.sum_singleton, p,
      Polynomial.natDegree_map_eq_of_injective hg]
    calc _ ≤ n * DX + m * DX := hResdeg
      _ ≤ 2 * m * DX := by nlinarith
      _ < _ := hF
  obtain ⟨x₁, hx₁⟩ := exists_base_point_avoiding_ratfunc_polynomials _ p hpne hpdeg
  let Res₁ : Polynomial F := (Polynomial.resultant R D m n).eval (Polynomial.C x₁)
  have hRes₁ : Res₁ ≠ 0 := by
    intro hz
    have hh := hx₁ () (by simp)
    apply hh
    simp only [p]
    rw [← Polynomial.eval₂_eq_eval_map]
    have heq : g (Polynomial.C x₁) = algebraMap F (RatFunc F) x₁ := by simp [g]
    rw [← heq, Polynomial.eval₂_hom]
    change g Res₁ = 0
    rw [hz, map_zero]
  have hRes₁eq : Res₁ = Polynomial.resultant (triSpecializeX R x₁) (triSpecializeX D x₁) m n := by
    simp only [Res₁, triSpecializeX]
    rw [← Polynomial.coe_evalRingHom, ← Polynomial.resultant_map_map]
  -- Its `Z`-degree is small.
  have hZR : ∀ j, ((triSpecializeX R x₁).coeff j).natDegree ≤ DZ := by
    intro j
    simp only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    exact natDegree_eval_C_le_of_coeff _ x₁ DZ (hZcap j)
  have hZD : ∀ j, ((triSpecializeX D x₁).coeff j).natDegree ≤ DZ := by
    intro j
    simp only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    apply natDegree_eval_C_le_of_coeff _ x₁ DZ
    intro a
    rw [coeff_dXPoly, Polynomial.coeff_derivative]
    calc ((R.coeff j).coeff (a + 1) * (↑a + 1)).natDegree ≤
          ((R.coeff j).coeff (a + 1)).natDegree + ((↑a + 1 : Polynomial F)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ DZ + 0 := by
        apply Nat.add_le_add (hZcap j (a + 1))
        rw [show ((↑a + 1 : Polynomial F)) = Polynomial.C ((↑a + 1 : F)) by simp]
        simp
      _ = DZ := by simp
  have hRes₁deg : Res₁.natDegree ≤ n * DZ + m * DZ := by
    rw [hRes₁eq]
    exact Polynomial.natDegree_resultant_le_of_coeff_natDegree_le _ _ m n DZ DZ hZR hZD
  -- Every selected challenge is a root of `Res₁`.
  have hroot : ∀ z ∈ S, Res₁.eval z = 0 := by
    intro z hz
    rw [hRes₁eq, ← Polynomial.coe_evalRingHom, ← Polynomial.resultant_map_map]
    let y := (P z).eval x₁
    apply fixed_resultant_eq_zero_of_common_root (y := y)
    · exact Polynomial.natDegree_map_le.trans (triSpecializeX_natDegree_le R x₁)
    · exact Polynomial.natDegree_map_le.trans (triSpecializeX_natDegree_le D x₁)
    · omega
    · have h := eval_triEval_eq_biEval_triSpecializeX R (P z) x₁ z
      rw [hvan z hz] at h
      simpa [biEval] using h.symm
    · have h := eval_triEval_eq_biEval_triSpecializeX D (P z) x₁ z
      rw [hvanD z hz] at h
      simpa [biEval] using h.symm
  calc S.card ≤ Res₁.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hRes₁]
        exact hroot z hz
    _ ≤ Res₁.roots.card := Multiset.toFinset_card_le _
    _ ≤ Res₁.natDegree := Polynomial.card_roots' _
    _ ≤ n * DZ + m * DZ := hRes₁deg
    _ ≤ 2 * R.natDegree * DZ := by nlinarith

end Dead


section Twist

/-!
## Frobenius twist

If `∂R/∂Y = 0` and `∂R/∂X = 0` then `R ∈ F[Z][X²][Y²]`.  Taking square roots of
the scalar coefficients and halving the `X`, `Y` exponents gives `T` with
`R(X, Y, t²) = T(X, Y, t)²` (`triEval_frobLift`).  A root `P` of `R` at `z = t²`
is then a root of `T` at `t`, and the line `U₀ + z^q U₁` becomes
`U₀ + t^{2q} U₁`.  `T` is irreducible with half the `Y`-degree.
-/

variable {F : Type} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The Frobenius square root on scalars. -/
noncomputable def sqrtF : F →+* F := ((frobeniusEquiv F 2).symm : F ≃+* F).toRingHom

@[simp] theorem sqrtF_sq (x : F) : sqrtF x ^ 2 = x := by
  have h := frobenius_apply_frobeniusEquiv_symm F 2 x
  rw [frobenius_def] at h
  exact h

theorem sqrtF_injective : Function.Injective (sqrtF : F → F) :=
  (frobeniusEquiv F 2).symm.injective

/-- Apply a coefficient map that preserves zero to every `Y`-coefficient. -/
noncomputable def mapYCoeffs {A : Type*} [CommRing A] (g : A → A)
    (f : Polynomial A) : Polynomial A :=
  ∑ j ∈ f.support, Polynomial.monomial j (g (f.coeff j))

theorem coeff_mapYCoeffs {A : Type*} [CommRing A] (g : A → A) (hg : g 0 = 0)
    (f : Polynomial A) (j : ℕ) : (mapYCoeffs g f).coeff j = g (f.coeff j) := by
  classical
  simp only [mapYCoeffs, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j ∈ f.support
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj, hg]
    · intro b hb
      have : b ≠ j := fun h => hj (h ▸ hb)
      simp [this]

/-- Scalar Frobenius on all coefficients, then `X ↦ X²`, then `Y ↦ Y²`. -/
noncomputable def frobLift :
    Polynomial (Polynomial (Polynomial F)) →+* Polynomial (Polynomial (Polynomial F)) :=
  (Polynomial.expand (Polynomial (Polynomial F)) 2).toRingHom.comp
    ((Polynomial.mapRingHom (Polynomial.expand (Polynomial F) 2).toRingHom).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2)))))

/-- The Frobenius twist of a polynomial in `F[Z][X²][Y²]`. -/
noncomputable def twistPoly (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (Polynomial (Polynomial F)) :=
  (mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
    (Polynomial.mapRingHom (Polynomial.mapRingHom sqrtF))

theorem frobLift_eq (A : Polynomial (Polynomial (Polynomial F))) :
    frobLift A = Polynomial.expand (Polynomial (Polynomial F)) 2
      ((A.map (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2)))).map
        (Polynomial.expand (Polynomial F) 2).toRingHom) := by
  simp only [frobLift, RingHom.comp_apply, Polynomial.coe_mapRingHom]
  rfl

theorem frobLift_twistPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hY : R.derivative = 0) (hX : dXPoly R = 0) :
    frobLift (twistPoly R) = R := by
  have hσ : (frobenius F 2).comp (sqrtF : F →+* F) = RingHom.id F := by
    ext x
    exact frobenius_apply_frobeniusEquiv_symm F 2 x
  have h2 : (Polynomial.mapRingHom (frobenius F 2)).comp
      (Polynomial.mapRingHom (sqrtF : F →+* F)) = RingHom.id _ := by
    rw [Polynomial.mapRingHom_comp, hσ, Polynomial.mapRingHom_id]
  have hcomp : (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (sqrtF : F →+* F))) =
      RingHom.id _ := by
    rw [Polynomial.mapRingHom_comp, h2, Polynomial.mapRingHom_id]
  have hR1 : (mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
      (Polynomial.expand (Polynomial F) 2).toRingHom = Polynomial.contract 2 R := by
    ext1 j
    rw [Polynomial.coeff_map, coeff_mapYCoeffs _ (by ext n; rw [Polynomial.coeff_contract (by norm_num)]; simp)]
    have hd : Polynomial.derivative ((Polynomial.contract 2 R).coeff j) = 0 := by
      rw [Polynomial.coeff_contract (by norm_num)]
      rw [← coeff_dXPoly, hX, Polynomial.coeff_zero]
    exact Polynomial.expand_contract 2 hd (by norm_num)
  have hback : ((mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R)).map
      (Polynomial.mapRingHom (Polynomial.mapRingHom (sqrtF : F →+* F)))).map
        (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))) =
      mapYCoeffs (Polynomial.contract 2) (Polynomial.contract 2 R) := by
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  rw [frobLift_eq]
  unfold twistPoly
  rw [hback, hR1]
  exact Polynomial.expand_contract 2 hY (by norm_num)

/-- Squaring a value of `B(X, Q)` is evaluating the Frobenius-twisted `B` at `Q²`. -/
theorem eval_map_frobenius_sq (B : Polynomial (Polynomial F)) (Q : Polynomial F) :
    (B.map (frobenius (Polynomial F) 2)).eval (Q ^ 2) = (B.eval Q) ^ 2 := by
  calc (B.map (frobenius (Polynomial F) 2)).eval (Q ^ 2) =
        B.eval₂ ((frobenius (Polynomial F) 2).comp (RingHom.id _))
          (frobenius (Polynomial F) 2 Q) := by
        rw [Polynomial.eval_map, frobenius_def]
        rfl
    _ = frobenius (Polynomial F) 2 (B.eval₂ (RingHom.id _) Q) :=
        (Polynomial.hom_eval₂ B (RingHom.id _) (frobenius (Polynomial F) 2) Q).symm
    _ = (B.eval Q) ^ 2 := by
        rw [frobenius_def]
        rfl

/-- The key identity `R(X, Y, t²) = T(X, Y, t)²`. -/
theorem triEval_frobLift (A : Polynomial (Polynomial (Polynomial F))) (t : F)
    (P : Polynomial F) :
    triEval (frobLift A) (t ^ 2) P = (triEval A t P) ^ 2 := by
  have hhom : ((Polynomial.mapRingHom (Polynomial.evalRingHom (t ^ 2))).comp
      (Polynomial.expand (Polynomial F) 2).toRingHom).comp
        (Polynomial.mapRingHom (Polynomial.mapRingHom (frobenius F 2))) =
      (frobenius (Polynomial F) 2).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom t)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.expand_C,
        Polynomial.coe_evalRingHom, frobenius_def, ← Polynomial.C_pow]
      congr 1
      have h := Polynomial.hom_eval₂ b (RingHom.id F) (frobenius F 2) t
      rw [Polynomial.eval_map]
      simp only [frobenius_def] at h
      rw [show (frobenius F 2).comp (RingHom.id F) = frobenius F 2 from rfl] at h
      rw [show Polynomial.eval t b = Polynomial.eval₂ (RingHom.id F) t b from rfl, h]
    · simp [frobenius_def]
  unfold triEval
  rw [frobLift_eq, Polynomial.map_expand, Polynomial.expand_eval, Polynomial.map_map,
    Polynomial.map_map, hhom, ← Polynomial.map_map]
  exact eval_map_frobenius_sq _ P

theorem natDegree_frobLift (A : Polynomial (Polynomial (Polynomial F))) :
    (frobLift A).natDegree = A.natDegree * 2 := by
  rw [frobLift_eq, Polynomial.natDegree_expand]
  congr 1
  rw [Polynomial.natDegree_map_eq_of_injective, Polynomial.natDegree_map_eq_of_injective]
  · exact Polynomial.map_injective _ (Polynomial.map_injective _ (frobenius_inj F 2))
  · exact Polynomial.expand_injective (by norm_num)

theorem coeff_coeff_frobLift (A : Polynomial (Polynomial (Polynomial F))) (j a : ℕ) :
    ((frobLift A).coeff (j * 2)).coeff (a * 2) =
      ((A.coeff j).coeff a).map (frobenius F 2) := by
  rw [frobLift_eq, Polynomial.coeff_expand_mul (by norm_num), Polynomial.coeff_map,
    Polynomial.coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Polynomial.coeff_expand_mul (by norm_num), Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  rfl

theorem isUnit_of_isUnit_frobLift (A : Polynomial (Polynomial (Polynomial F)))
    (h : IsUnit (frobLift A)) : IsUnit A := by
  have h0 : A.natDegree = 0 := by
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [natDegree_frobLift] at this
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero h0] at h ⊢
  rw [Polynomial.isUnit_C]
  set a₀ := A.coeff 0
  have h1 : IsUnit ((a₀.map (Polynomial.mapRingHom (frobenius F 2))).map
      (Polynomial.expand F 2).toRingHom |> fun x => Polynomial.expand (Polynomial F) 2
        (a₀.map (Polynomial.mapRingHom (frobenius F 2)))) := by
    simpa [frobLift_eq] using h
  have h1' : IsUnit (Polynomial.expand (Polynomial F) 2
      (a₀.map (Polynomial.mapRingHom (frobenius F 2)))) := h1
  have hdeg1 := Polynomial.natDegree_eq_zero_of_isUnit h1'
  rw [Polynomial.natDegree_expand, Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective _ (frobenius_inj F 2))] at hdeg1
  have ha0 : a₀.natDegree = 0 := by omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero ha0] at h1' ⊢
  rw [Polynomial.isUnit_C]
  set b₀ := a₀.coeff 0
  have h2 : IsUnit (b₀.map (frobenius F 2)) := by
    simpa [Polynomial.isUnit_C] using h1'
  have hdeg2 := Polynomial.natDegree_eq_zero_of_isUnit h2
  rw [Polynomial.natDegree_map_eq_of_injective (frobenius_inj F 2)] at hdeg2
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg2] at h2 ⊢
  rw [Polynomial.isUnit_C]
  rw [Polynomial.map_C, Polynomial.isUnit_C] at h2
  rw [isUnit_iff_ne_zero] at h2 ⊢
  intro hz
  apply h2
  rw [hz, map_zero]

theorem irreducible_twistPoly (R : Polynomial (Polynomial (Polynomial F)))
    (hirr : Irreducible R) (hY : R.derivative = 0) (hX : dXPoly R = 0) :
    Irreducible (twistPoly R) := by
  have hR := frobLift_twistPoly R hY hX
  refine ⟨?_, ?_⟩
  · intro hu
    apply hirr.not_isUnit
    rw [← hR]
    exact hu.map frobLift
  · intro a b hab
    have h := hirr.isUnit_or_isUnit (show R = frobLift a * frobLift b by
      rw [← hR, hab, map_mul])
    rcases h with h | h
    · exact Or.inl (isUnit_of_isUnit_frobLift a h)
    · exact Or.inr (isUnit_of_isUnit_frobLift b h)

end Twist

end ProximityPrize.SubmissionBinaryLower
