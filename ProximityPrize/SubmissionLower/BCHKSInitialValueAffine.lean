import ProximityPrize.SubmissionLower.BCHKSHenselAlignmentCore

namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

variable {F : Type} [Field F]

/-- Corrected numerator for the actual finite-Hensel initial value `T/W`.
It represents `W * (γ - (u₀ + (T/W)u₁))`, with the usual common denominator. -/
noncomputable def explicitInitialValueGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) : 𝒪 H :=
  commonWRegular *
      explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN -
    commonTRegular * commonConstRegular u₁ *
      concreteDenRegularBridge x₀ R hHyp k

/-- Exact embedding identity, including the extra clearing `W`. -/
theorem embedding_explicitInitialValueGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) :
    embeddingOf𝒪Into𝕃 H
      (explicitInitialValueGammaDifferenceRegular x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
    Wfield (H:=H) *
      (evaluatedFiniteAlpha (R:=R) (H:=H) x₀ dx N k -
        (fieldTo𝕃 (H:=H) u₀ + initialValue (H:=H) * fieldTo𝕃 (H:=H) u₁)) *
      commonDenominator (R:=R) (H:=H) x₀ hHyp k := by
  rw [explicitInitialValueGammaDifferenceRegular, map_sub, map_mul, map_mul,
    map_mul, embedding_commonWRegular,
    embedding_explicitGammaDifferenceRegular,
    embedding_commonTRegular, embedding_commonConstRegular,
    embedding_concreteDenRegularBridge]
  unfold gammaDifferenceField commonDenominator initialValue
  rw [show liftToFunctionField (H:=H) H.leadingCoeff = Wfield (H:=H) from rfl]
  simp only [map_zero, mul_zero, add_zero]
  have hW := Wfield_ne_zero (H:=H)
  field_simp [hW]
  ring

/-- Pure affine interpolation over an arbitrary extension field. -/
theorem extension_polynomial_eq_affine_of_many_evals
    {K : Type} [Field K] [DecidableEq F]
    (φ : F →+* K) (y : K) (γ : K[X]) (k : ℕ)
    (D : Finset F) (hD : k+1 ≤ D.card) (U₀ U₁ : F → F)
    (hγdeg : γ.natDegree ≤ k)
    (heval : ∀ x ∈ D, γ.eval (φ x) = φ (U₀ x) + y * φ (U₁ x)) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      γ = p₀.map φ + Polynomial.C y * p₁.map φ := by
  classical
  obtain ⟨E,hED,hcard⟩ := Finset.exists_subset_card_eq hD
  let p₀ : F[X] := Lagrange.interpolate E id U₀
  let p₁ : F[X] := Lagrange.interpolate E id U₁
  have hp₀ : p₀.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₀ k hcard
  have hp₁ : p₁.natDegree ≤ k :=
    lagrange_natDegree_le_of_card_eq_succ E U₁ k hcard
  refine ⟨p₀,p₁,hp₀,hp₁,?_⟩
  let rhs : K[X] := p₀.map φ + Polynomial.C y * p₁.map φ
  have hrhs : rhs.natDegree ≤ k := by
    apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (Polynomial.natDegree_map_le.trans hp₀)
      ((Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_map_le.trans hp₁))
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq γ rhs
    (f:=fun x:E => φ (x:F))
  · exact (RingHom.injective φ).comp Subtype.val_injective
  · intro x
    have h0 : p₀.eval (x:F)=U₀ x :=
      Lagrange.eval_interpolate_at_node U₀ (Set.injOn_id (↑E:Set F)) x.property
    have h1 : p₁.eval (x:F)=U₁ x :=
      Lagrange.eval_interpolate_at_node U₁ (Set.injOn_id (↑E:Set F)) x.property
    rw [heval x (hED x.property)]
    simp [rhs,h0,h1,Polynomial.eval_map]
  · rw [Fintype.card_coe,hcard]
    exact max_lt (hγdeg.trans_lt (Nat.lt_succ_self k))
      (hrhs.trans_lt (Nat.lt_succ_self k))

/-- The canonical centered function-field lift. -/
noncomputable def canonicalFunctionFieldGamma
    (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ) : (𝕃 H)[X] :=
  (FiniteHensel.truncSeries (finiteAlpha (R:=R) (H:=H) x₀ N) k).comp
    (Polynomial.X - Polynomial.C (fieldTo𝕃 (H:=H) x₀))

noncomputable def groundToFunctionField
    (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    F →+* 𝕃 H :=
  (liftToFunctionField (H:=H)).comp (Polynomial.C : F →+* F[X])

/-- Generic interpolation instantiated in the actual function field, with the
correct distinguished root `T/W`. -/
theorem canonicalFunctionFieldGamma_affine
    [DecidableEq F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (N k : ℕ)
    (D : Finset F) (hD : k+1 ≤ D.card) (U₀ U₁ : F → F)
    (hdeg : (canonicalFunctionFieldGamma H x₀ R N k).natDegree ≤ k)
    (heval : ∀ x ∈ D,
      (canonicalFunctionFieldGamma H x₀ R N k).eval (fieldTo𝕃 (H:=H) x) =
        fieldTo𝕃 (H:=H) (U₀ x) + initialValue (H:=H) * fieldTo𝕃 (H:=H) (U₁ x)) :
    ∃ p₀ p₁ : F[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      canonicalFunctionFieldGamma H x₀ R N k =
        p₀.map (groundToFunctionField H) +
          Polynomial.C (initialValue (H:=H)) * p₁.map (groundToFunctionField H) := by
  exact extension_polynomial_eq_affine_of_many_evals
    (groundToFunctionField H) (initialValue (H:=H))
    (canonicalFunctionFieldGamma H x₀ R N k) k D hD U₀ U₁ hdeg (by
      intro x hx
      change (canonicalFunctionFieldGamma H x₀ R N k).eval (fieldTo𝕃 (H:=H) x) =
        fieldTo𝕃 (H:=H) (U₀ x) + initialValue (H:=H) * fieldTo𝕃 (H:=H) (U₁ x)
      exact heval x hx)


/-- Exact pair-evaluation formula for the corrected numerator. -/
theorem piZ_explicitInitialValueGammaDifferenceRegular
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ z y : F) (root : rationalRoot (monicize H) z)
    (hy : root.1 = H.leadingCoeff.eval z * y)
    (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k →
      concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
        FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k → piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0) :
    piZ z root (explicitInitialValueGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) =
      H.leadingCoeff.eval z *
        (P.eval (x₀+dx) - (u₀ + y*u₁)) *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
  have hTaylor : (∑ i ∈ Finset.range (k+1),
      FiniteHensel.TaylorCoeff P x₀ i * dx^i) = P.eval (x₀+dx) := by
    calc
      _ = (FiniteHensel.truncSeries (FiniteHensel.TaylorCoeff P x₀) k).eval dx := by
        unfold FiniteHensel.truncSeries
        change (∑ i ∈ Finset.range (k+1), _) =
          (Polynomial.evalRingHom dx) (∑ i ∈ Finset.range (k+1), _)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi; simp
      _ = (P.comp (Polynomial.C x₀ + Polynomial.X)).eval dx := by
        rw [FiniteHensel.truncSeries_TaylorCoeff_eq_shift P x₀ k hPdeg]
      _ = _ := by simp [Polynomial.eval_comp]
  have hterm : ∀ i, i ≤ k →
      piZ z root
        (concreteBetaUpTo x₀ R hHyp hzeta N i * commonConstRegular dx^i *
          commonWRegular^(k-i) * xi x₀ R H hHyp ^
            (FiniteHenselWeight.denominatorExponent k -
              FiniteHenselWeight.denominatorExponent i)) =
      FiniteHensel.TaylorCoeff P x₀ i * dx^i *
        piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    intro i hik
    have hs := hspecializes i hik
    unfold concreteSpecializedAlpha at hs
    have hb := (div_eq_iff (hden i hik)).mp hs
    have hc := congrArg (piZ z root)
      (concreteDenRegularBridge_mul_to_common x₀ R hHyp hik)
    simp only [map_mul,map_pow] at hc ⊢
    rw [hb, ← hc]
    simp [commonConstRegular,piZ_mk_C]
    ring
  have hold : piZ z root (explicitGammaDifferenceRegular
      x₀ dx u₀ 0 R hHyp hzeta N k hkN) =
      (P.eval (x₀+dx)-u₀) *
        piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
    unfold explicitGammaDifferenceRegular
    rw [map_sub,map_sum,map_mul,map_add,map_mul]
    simp only [map_mul,map_pow]
    have hs : (∑ i ∈ Finset.range (k+1),
        piZ z root (concreteBetaUpTo x₀ R hHyp hzeta N i) *
          piZ z root (commonConstRegular dx)^i *
          piZ z root commonWRegular^(k-i) *
          piZ z root (xi x₀ R H hHyp)^
            (FiniteHenselWeight.denominatorExponent k-
              FiniteHenselWeight.denominatorExponent i)) =
        (∑ i ∈ Finset.range (k+1), FiniteHensel.TaylorCoeff P x₀ i*dx^i) *
          piZ z root (concreteDenRegularBridge x₀ R hHyp k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [map_mul,map_pow] using hterm i (by simpa using hi)
    rw [hs,hTaylor]
    simp [commonConstRegular,commonTRegular,piZ,piZLift]
    ring
  unfold explicitInitialValueGammaDifferenceRegular
  rw [map_sub,map_mul,map_mul,map_mul,hold]
  simp [commonWRegular,commonTRegular,commonConstRegular,piZ,piZLift,hy]
  ring

/-- Pair agreement is equivalent to vanishing of the corrected numerator at a
non-pole pair. -/
theorem piZ_explicitInitialValueGammaDifferenceRegular_eq_zero_iff
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ z y : F) (root : rationalRoot (monicize H) z)
    (hy : root.1 = H.leadingCoeff.eval z*y) (hW : H.leadingCoeff.eval z ≠ 0)
    (R : F[X][X][Y]) (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N) (P : F[X]) (hPdeg : P.natDegree ≤ k)
    (hspecializes : ∀ i, i ≤ k → concreteSpecializedAlpha x₀ R hHyp hzeta N z root i =
      FiniteHensel.TaylorCoeff P x₀ i)
    (hden : ∀ i, i ≤ k → piZ z root (concreteDenRegularBridge x₀ R hHyp i) ≠ 0) :
    piZ z root (explicitInitialValueGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) = 0 ↔
      P.eval (x₀+dx) = u₀+y*u₁ := by
  rw [piZ_explicitInitialValueGammaDifferenceRegular x₀ dx u₀ u₁ z y root hy
    R hHyp hzeta N k hkN P hPdeg hspecializes hden]
  constructor
  · intro h
    have h₁ := (mul_eq_zero.mp h).resolve_right (hden k (le_refl k))
    have h₂ := (mul_eq_zero.mp h₁).resolve_left hW
    exact sub_eq_zero.mp h₂
  · intro h
    simp [h]



/-- Sharp regular-weight bound for the corrected numerator. -/
theorem explicitInitialValueGammaDifferenceRegular_weight
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : YZCap R D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (N k : ℕ) (hkN : k ≤ N) :
    regularWeight hH (explicitInitialValueGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some ((2*k+2)*Bivariate.natDegreeY R*D) : WithBot ℕ) := by
  let B := (2*k+1)*Bivariate.natDegreeY R*D
  let M := B+D
  have hold (a b : F) : regularWeight hH
      (explicitGammaDifferenceRegular x₀ dx a b R hHyp hzeta N k hkN) D ≤
      (WithBot.some B : WithBot ℕ) := by
    exact explicitGammaDifferenceRegular_weight x₀ dx a b R hHyp hzeta hH
      hD_H hD_R hRdeg N k hkN
  have hW : regularWeight hH (commonWRegular (H:=H)) D ≤
      (WithBot.some D : WithBot ℕ) := by
    exact regularWeight_le_of_regularWeightLe (commonWRegular (H:=H))
      (by
        rw [embedding_commonWRegular]
        exact regularWeightLe_leadingCoeff hD_H hH)
  have hmul : regularWeight hH
      (commonWRegular * explicitGammaDifferenceRegular
        x₀ dx u₀ 0 R hHyp hzeta N k hkN) D ≤
      (WithBot.some M : WithBot ℕ) := by
    have ht := regularWeight_mul_le' hD_H hH (hold u₀ 0) hW
    rw [show commonWRegular * explicitGammaDifferenceRegular
      x₀ dx u₀ 0 R hHyp hzeta N k hkN =
      explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN * commonWRegular
      from mul_comm (commonWRegular : 𝒪 H) _]
    simpa [M, Nat.add_comm] using ht
  have hidentity : explicitInitialValueGammaDifferenceRegular
      x₀ dx u₀ u₁ R hHyp hzeta N k hkN =
      commonWRegular * explicitGammaDifferenceRegular
        x₀ dx u₀ 0 R hHyp hzeta N k hkN -
      explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN +
      explicitGammaDifferenceRegular x₀ dx 0 u₁ R hHyp hzeta N k hkN := by
    unfold explicitInitialValueGammaDifferenceRegular explicitGammaDifferenceRegular
    simp [commonConstRegular]
  rw [hidentity]
  have hneg : regularWeight hH
      (-explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN) D ≤
      (WithBot.some M : WithBot ℕ) := by
    rw [regularWeight_neg]
    exact (hold 0 0).trans (WithBot.coe_le_coe.mpr (by simp [M,B]))
  have hu : regularWeight hH
      (explicitGammaDifferenceRegular x₀ dx 0 u₁ R hHyp hzeta N k hkN) D ≤
      (WithBot.some M : WithBot ℕ) :=
    (hold 0 u₁).trans (WithBot.coe_le_coe.mpr (by simp [M,B]))
  have hadd := regularWeight_add_le hD_H hH
    (commonWRegular * explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN)
    (-explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN)
  have hadd' : regularWeight hH
      (commonWRegular * explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN -
       explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN) D ≤
      (WithBot.some M : WithBot ℕ) := by
    simpa [sub_eq_add_neg] using hadd.trans (max_le hmul hneg)
  have hall := (regularWeight_add_le hD_H hH
    (commonWRegular * explicitGammaDifferenceRegular x₀ dx u₀ 0 R hHyp hzeta N k hkN -
      explicitGammaDifferenceRegular x₀ dx 0 0 R hHyp hzeta N k hkN)
    (explicitGammaDifferenceRegular x₀ dx 0 u₁ R hHyp hzeta N k hkN)).trans
      (max_le hadd' hu)
  exact hall.trans (WithBot.coe_le_coe.mpr (by
    simp [M,B]
    have hd : 1 ≤ Bivariate.natDegreeY R := by omega
    nlinarith))

/-- The one-extra-`W` budget is absorbed by the global `2*DX` budget. -/
theorem initialValue_extraW_budget (k DX d D : ℕ) (hkDX : k < DX) :
    (2*k+2)*d*D ≤ 2*DX*d*D := by
  have : 2*k+2 ≤ 2*DX := by omega
  simpa [mul_assoc] using Nat.mul_le_mul_right (d*D) this

end ProximityPrize.SubmissionLower
