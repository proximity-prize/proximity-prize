import ProximityPrize.SubmissionBinaryLower.P64Charging
import ArkLib.Data.Polynomial.ResultantDegree

/-!
# Lemma R (resultant) and the pair case of Lemma 3.1 (PROOF.md 2.5, 3.1)

Lemma R: if `R` is irreducible with `deg_Y R ≥ 1` and `G ≠ 0` is not divisible by `R`, the
slopes whose bad curves lie on both are roots of one nonzero polynomial of degree at most
`deg_Y G · d_R + deg_Y R · d_G`. The proof follows `dead_factor_card_le`
(`BCHKSInseparable.lean`, 63.99 submission) with `∂_X R` replaced by `G`: the `Y`-resultant is
nonzero by Gauss's lemma, a base point `X = x₁` keeps it nonzero, and every such slope is a root of
the specialised resultant. The helpers are copied from `BCHKSFactorPigeon.lean`,
`BCHKSConcreteGoodSpecialization.lean` and `BCHKSInseparable.lean`.

The pair case: `|(P)| ≤ (Σ h)(Σ d)`, by double counting over ordered pairs of distinct factors.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Resultant

open Polynomial BCHKSSubstitutionVanish P64Charging

section Helpers

variable {F : Type} [Field F]

/-- Substitute `X = x₀` in `F[Z][X][Y]`, leaving `F[Z][Y]`. -/
noncomputable def triSpecializeX (Q : Polynomial (Polynomial (Polynomial F))) (x₀ : F) :
    Polynomial (Polynomial F) :=
  Polynomial.map (Polynomial.evalRingHom (Polynomial.C x₀)) Q

/-- Evaluate an `F[Z][Y]` polynomial at `(Y, Z) = (y, z)`. -/
noncomputable def biEval (H : Polynomial (Polynomial F)) (y z : F) : F :=
  Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom z) H)

lemma eval_map_eval_eq_eval_eval_C (A : Polynomial (Polynomial F)) (x z : F) :
    Polynomial.eval x (Polynomial.map (Polynomial.evalRingHom z) A) =
      Polynomial.eval z (Polynomial.eval (Polynomial.C x) A) := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA, hB]
  | monomial n a => simp [Polynomial.map_monomial, Polynomial.eval_monomial]

lemma eval_triEval_eq_biEval_triSpecializeX (Q : Polynomial (Polynomial (Polynomial F)))
    (P : Polynomial F) (x₀ z : F) :
    Polynomial.eval x₀ (triEval Q z P) =
      biEval (triSpecializeX Q x₀) (Polynomial.eval x₀ P) z := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      calc
        Polynomial.eval x₀ (triEval (Q + R) z P) =
            Polynomial.eval x₀ (triEval Q z P) +
              Polynomial.eval x₀ (triEval R z P) := by simp [triEval, specializeZ]
        _ = biEval (triSpecializeX Q x₀) (Polynomial.eval x₀ P) z +
              biEval (triSpecializeX R x₀) (Polynomial.eval x₀ P) z := by rw [hQ, hR]
        _ = biEval (triSpecializeX (Q + R) x₀) (Polynomial.eval x₀ P) z := by
              simp [triSpecializeX, biEval]
  | monomial n A =>
      simp [triEval, specializeZ, triSpecializeX, biEval, Polynomial.map_monomial,
        Polynomial.eval_monomial, eval_map_eval_eq_eval_eval_C]

/-- Evaluating the middle variable at a constant does not raise the `Z`-degree. -/
theorem natDegree_eval_C_le_of_coeff (c : Polynomial (Polynomial F)) (x : F) (D : ℕ)
    (h : ∀ a, (c.coeff a).natDegree ≤ D) : (c.eval (Polynomial.C x)).natDegree ≤ D := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  rw [← Polynomial.C_pow]
  exact (Polynomial.natDegree_mul_le).trans (by simpa using h a)

/-- Root counting restricted to the embedded constants. -/
theorem exists_base_point_avoiding [Fintype F] (p : Polynomial (RatFunc F)) (hne : p ≠ 0)
    (hdeg : p.natDegree < Fintype.card F) :
    ∃ x₀ : F, Polynomial.eval (algebraMap F (RatFunc F) x₀) p ≠ 0 := by
  by_contra hgood
  push Not at hgood
  exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (FaithfulSMul.algebraMap_injective F (RatFunc F)) hgood hdeg)

/-- Fixed-degree common-root vanishing of a padded resultant. -/
theorem fixed_resultant_eq_zero_of_common_root {P H : F[X]} {m n : ℕ} {y : F}
    (hPdeg : P.natDegree ≤ m) (hHdeg : H.natDegree ≤ n)
    (hsize : 0 < m + n) (hP : P.eval y = 0) (hH : H.eval y = 0) :
    Polynomial.resultant P H m n = 0 := by
  by_cases hne : P ≠ 0 ∨ H ≠ 0
  · have hstd : Polynomial.resultant P H = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      refine ⟨hne, ?_⟩
      rintro ⟨a, b, hab⟩
      have heval := congrArg (fun q : F[X] => q.eval y) hab
      simp [Polynomial.eval_add, Polynomial.eval_mul, hP, hH] at heval
    have hm : P.natDegree + (m - P.natDegree) = m := Nat.add_sub_of_le hPdeg
    have hn : H.natDegree + (n - H.natDegree) = n := Nat.add_sub_of_le hHdeg
    rw [← hm, ← hn, Polynomial.resultant_add_left_deg]
    · rw [Polynomial.resultant_add_right_deg]
      · simp [hstd]
      · exact le_rfl
    · exact le_rfl
  · push Not at hne
    rcases hne with ⟨rfl, rfl⟩
    rcases m with _ | m <;> rcases n with _ | n <;> simp_all

end Helpers

section LemmaR

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Lemma R.** -/
theorem card_common_le (R G : Polynomial (Polynomial (Polynomial F)))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hndvd : ¬ R ∣ G)
    (DZR DZG DX : ℕ)
    (hZR : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ DZR)
    (hZG : ∀ j a, ((G.coeff j).coeff a).natDegree ≤ DZG)
    (hXR : ∀ j, (R.coeff j).natDegree ≤ DX) (hXG : ∀ j, (G.coeff j).natDegree ≤ DX)
    (hF : (G.natDegree + R.natDegree) * DX < Fintype.card F)
    (S : Finset F) (P : F → Polynomial F)
    (hvan : ∀ z ∈ S, triEval R z (P z) = 0 ∧ triEval G z (P z) = 0) :
    S.card ≤ G.natDegree * DZR + R.natDegree * DZG := by
  classical
  let m := R.natDegree
  let n := G.natDegree
  have hprim : R.IsPrimitive := hirr.isPrimitive (by omega)
  let A := Polynomial (Polynomial F)
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let RK : K[X] := R.map (algebraMap A K)
  let GK : K[X] := G.map (algebraMap A K)
  have hirrK : Irreducible RK := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hnotK : ¬ RK ∣ GK := fun h => hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
  have hcop : IsCoprime RK GK := by
    by_contra hnot
    exact hnotK ((hirrK.dvd_iff_not_isCoprime).2 hnot)
  have hresK : RK.resultant GK ≠ 0 := Polynomial.resultant_ne_zero RK GK hcop
  have hRKdeg : RK.natDegree = m := Polynomial.natDegree_map_eq_of_injective hinj R
  have hGKdeg : GK.natDegree = n := Polynomial.natDegree_map_eq_of_injective hinj G
  have hRes : Polynomial.resultant R G m n ≠ 0 := by
    intro hz
    apply hresK
    have hmap := Polynomial.resultant_map_map R G m n (algebraMap A K)
    rw [hz, map_zero] at hmap
    change RK.resultant GK RK.natDegree GK.natDegree = 0
    rw [hRKdeg, hGKdeg]
    exact hmap
  have hResdeg : (Polynomial.resultant R G m n).natDegree ≤ n * DX + m * DX :=
    Polynomial.natDegree_resultant_le_of_coeff_natDegree_le R G m n DX DX hXR hXG
  let g : Polynomial F →+* RatFunc F := algebraMap _ _
  have hg : Function.Injective g := IsFractionRing.injective _ _
  have hpne : (Polynomial.resultant R G m n).map g ≠ 0 := (Polynomial.map_ne_zero_iff hg).mpr hRes
  have hpdeg : ((Polynomial.resultant R G m n).map g).natDegree < Fintype.card F := by
    rw [Polynomial.natDegree_map_eq_of_injective hg]
    calc _ ≤ n * DX + m * DX := hResdeg
      _ = (n + m) * DX := by ring
      _ < _ := hF
  obtain ⟨x₁, hx₁⟩ := exists_base_point_avoiding _ hpne hpdeg
  let Res₁ : Polynomial F := (Polynomial.resultant R G m n).eval (Polynomial.C x₁)
  have hRes₁ : Res₁ ≠ 0 := by
    intro hz
    apply hx₁
    rw [← Polynomial.eval₂_eq_eval_map]
    have heq : g (Polynomial.C x₁) = algebraMap F (RatFunc F) x₁ := by simp [g]
    rw [← heq, Polynomial.eval₂_hom]
    change g Res₁ = 0
    rw [hz, map_zero]
  have hRes₁eq : Res₁ = Polynomial.resultant (triSpecializeX R x₁) (triSpecializeX G x₁) m n := by
    simp only [Res₁, triSpecializeX]
    rw [← Polynomial.coe_evalRingHom, ← Polynomial.resultant_map_map]
  have hZR' : ∀ j, ((triSpecializeX R x₁).coeff j).natDegree ≤ DZR := by
    intro j
    simp only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    exact natDegree_eval_C_le_of_coeff _ x₁ DZR (hZR j)
  have hZG' : ∀ j, ((triSpecializeX G x₁).coeff j).natDegree ≤ DZG := by
    intro j
    simp only [triSpecializeX, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    exact natDegree_eval_C_le_of_coeff _ x₁ DZG (hZG j)
  have hRes₁deg : Res₁.natDegree ≤ n * DZR + m * DZG := by
    rw [hRes₁eq]
    exact Polynomial.natDegree_resultant_le_of_coeff_natDegree_le _ _ m n DZR DZG hZR' hZG'
  have hroot : ∀ z ∈ S, Res₁.eval z = 0 := by
    intro z hz
    rw [hRes₁eq, ← Polynomial.coe_evalRingHom, ← Polynomial.resultant_map_map]
    apply fixed_resultant_eq_zero_of_common_root (y := (P z).eval x₁)
    · exact Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
    · exact Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
    · omega
    · have h := eval_triEval_eq_biEval_triSpecializeX R (P z) x₁ z
      rw [(hvan z hz).1] at h
      simpa [biEval] using h.symm
    · have h := eval_triEval_eq_biEval_triSpecializeX G (P z) x₁ z
      rw [(hvan z hz).2] at h
      simpa [biEval] using h.symm
  calc S.card ≤ Res₁.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hRes₁]
        exact hroot z hz
    _ ≤ Res₁.roots.card := Multiset.toFinset_card_le _
    _ ≤ Res₁.natDegree := Polynomial.card_roots' _
    _ ≤ n * DZR + m * DZG := hRes₁deg

end LemmaR

section Pairs

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [NormalizationMonoid F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

omit [Fintype F] in
/-- A `Y`-free factor through a bad curve puts the slope in `(Y0)`. -/
theorem specializeZ_eq_zero_of_natDegree_eq_zero (Q R : Tri) (hR : R ∈ factors Q)
    (h0 : R.natDegree = 0) (z : F) (P : F[X]) (hRz : triEval R z P = 0) :
    specializeZ Q z = 0 := by
  have hRC : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hspec : specializeZ R z = 0 := by
    have : triEval R z P = Polynomial.map (Polynomial.evalRingHom z) (R.coeff 0) := by
      rw [hRC]
      simp [triEval, specializeZ]
    rw [this] at hRz
    rw [hRC]
    simp [specializeZ, hRz]
  obtain ⟨c, hc⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (α := Tri)
    (Multiset.mem_toFinset.mp hR)
  rw [hc, ← specializeZHom_apply, map_mul, specializeZHom_apply, hspec, zero_mul]

omit [Fintype F] in
/-- Distinct normalized factors do not divide each other. -/
theorem not_dvd_of_ne (Q R G : Tri) (hR : R ∈ factors Q) (hG : G ∈ factors Q) (hne : R ≠ G) :
    ¬ R ∣ G := by
  intro hdvd
  have hR' := Multiset.mem_toFinset.mp hR
  have hG' := Multiset.mem_toFinset.mp hG
  have hRi := (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R hR').irreducible
  have hGi := (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) G hG').irreducible
  have h := normalize_eq_normalize hdvd (hRi.dvd_symm hGi hdvd)
  rw [UniqueFactorizationMonoid.normalize_normalized_factor (α := Tri) R hR',
    UniqueFactorizationMonoid.normalize_normalized_factor (α := Tri) G hG'] at h
  exact hne h

omit [Fintype F] [DecidableEq F] [NormalizationMonoid F] in
lemma coeff_natDegree_le_yz (R : Tri) (j a : ℕ) :
    ((R.coeff j).coeff a).natDegree ≤ P64Caps.YZ.yzSupportDegree R 1 := by
  by_cases hj : R.coeff j = 0
  · simp [hj]
  · have h1 := P64Caps.YZ.coeffWeight_le_of_ne R 1 j hj
    have h2 := Polynomial.Bivariate.coeff_natDegree_le_degreeX (R.coeff j) a
    omega

omit [Fintype F] [DecidableEq F] [NormalizationMonoid F] in
lemma coeff_natDegree_le_weighted (R : Tri) (k j : ℕ) :
    (R.coeff j).natDegree ≤ P64Caps.Weighted.weightedSupportDegree R k := by
  by_cases hj : R.coeff j = 0
  · simp [hj]
  · have := P64Caps.Weighted.coeffWeight_le_of_ne R k j hj
    omega

/-- Slopes of `(P)` through the ordered pair `(R, G)`. -/
noncomputable def pairSet (Q : Tri) (S : Finset F) (P : F → F[X]) (e : Tri × Tri) : Finset F :=
  (casePair Q S P).filter fun z => triEval e.1 z (P z) = 0 ∧ triEval e.2 z (P z) = 0

/-- **Lemma 3.1, case (P).** `|(P)| ≤ (Σ h)(Σ d) ≤ deg_Y Q · d_Q`. -/
theorem card_casePair_le (Q : Tri) (hQ : Q ≠ 0) (k : ℕ)
    (hF : 2 * Q.natDegree * P64Caps.Weighted.weightedSupportDegree Q k < Fintype.card F)
    (S : Finset F) (P : F → F[X]) :
    (casePair Q S P).card ≤ Q.natDegree * P64Caps.YZ.yzSupportDegree Q 1 := by
  classical
  set s := factors Q
  set hR : Tri → ℕ := fun R => R.natDegree
  set dR : Tri → ℕ := fun R => P64Caps.YZ.yzSupportDegree R 1
  set wQ := P64Caps.Weighted.weightedSupportDegree Q k
  have hhle : ∀ R ∈ s, hR R ≤ Q.natDegree := fun R hR' =>
    (Finset.single_le_sum (f := hR) (fun _ _ => Nat.zero_le _) hR').trans (sum_natDegree_le Q hQ)
  have hwle : ∀ R ∈ s, P64Caps.Weighted.weightedSupportDegree R k ≤ wQ := fun R hR' =>
    (Finset.single_le_sum (f := fun R => P64Caps.Weighted.weightedSupportDegree R k)
      (fun _ _ => Nat.zero_le _) hR').trans (sum_weighted_le Q hQ k)
  -- each ordered pair
  have hpair : ∀ e ∈ s.offDiag, (pairSet Q S P e).card ≤ hR e.2 * dR e.1 + hR e.1 * dR e.2 := by
    rintro ⟨R, G⟩ he
    rw [Finset.mem_offDiag] at he
    obtain ⟨hRs, hGs, hne⟩ := he
    by_cases h0 : R.natDegree = 0
    · have : pairSet Q S P (R, G) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        simp only [pairSet, casePair, Finset.mem_filter] at hz
        exact hz.1.2.1 (specializeZ_eq_zero_of_natDegree_eq_zero Q R hRs h0 z (P z) hz.2.1)
      simp [this]
    have hirr := (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R
      (Multiset.mem_toFinset.mp hRs)).irreducible
    apply card_common_le R G hirr (by omega) (not_dvd_of_ne Q R G hRs hGs hne) _ _ wQ
      (coeff_natDegree_le_yz R) (coeff_natDegree_le_yz G)
      (fun j => (coeff_natDegree_le_weighted R k j).trans (hwle R hRs))
      (fun j => (coeff_natDegree_le_weighted G k j).trans (hwle G hGs))
    · have h1 := hhle R hRs
      have h2 := hhle G hGs
      calc (G.natDegree + R.natDegree) * wQ ≤ (2 * Q.natDegree) * wQ :=
            Nat.mul_le_mul_right _ (by simp only [hR] at h1 h2; omega)
        _ < _ := hF
    · intro z hz
      simp only [pairSet, Finset.mem_filter] at hz
      exact hz.2
  -- double counting
  have hdouble : 2 * (casePair Q S P).card ≤ ∑ e ∈ s.offDiag, (pairSet Q S P e).card := by
    have hcount : ∀ e ∈ s.offDiag, (pairSet Q S P e).card =
        ∑ z ∈ casePair Q S P,
          if triEval e.1 z (P z) = 0 ∧ triEval e.2 z (P z) = 0 then 1 else 0 := by
      intro e _
      rw [pairSet, Finset.card_filter]
    rw [Finset.sum_congr rfl hcount, Finset.sum_comm,
      show 2 * (casePair Q S P).card = ∑ z ∈ casePair Q S P, 2 by simp [mul_comm]]
    apply Finset.sum_le_sum
    intro z hz
    rw [← Finset.card_filter]
    have hz' := hz
    simp only [casePair, Finset.mem_filter] at hz'
    obtain ⟨_, _, R, hRs, G, hGs, hne, hR0, hG0⟩ := hz'
    have hsub : ({(R, G), (G, R)} : Finset (Tri × Tri)) ⊆
        s.offDiag.filter fun e => triEval e.1 z (P z) = 0 ∧ triEval e.2 z (P z) = 0 := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · simp only [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨hRs, hGs, hne⟩, hR0, hG0⟩
      · simp only [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨hGs, hRs, Ne.symm hne⟩, hG0, hR0⟩
    have hcard : ({(R, G), (G, R)} : Finset (Tri × Tri)).card = 2 := by
      rw [Finset.card_pair]
      intro h
      exact hne (Prod.ext_iff.mp h).1
    rw [← hcard]
    exact Finset.card_le_card hsub
  -- symmetric sum
  have hsym : ∑ e ∈ s.offDiag, (hR e.2 * dR e.1 + hR e.1 * dR e.2) =
      2 * ∑ e ∈ s.offDiag, hR e.2 * dR e.1 := by
    rw [Finset.sum_add_distrib, two_mul]
    congr 1
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro e he
      simp only [Finset.mem_offDiag, Prod.fst_swap, Prod.snd_swap] at he ⊢
      exact ⟨he.2.1, he.1, fun h => he.2.2 h.symm⟩
    · intro e he
      simp only [Finset.mem_offDiag, Prod.fst_swap, Prod.snd_swap] at he ⊢
      exact ⟨he.2.1, he.1, fun h => he.2.2 h.symm⟩
    · intro e _; rfl
    · intro e _; rfl
    · intro e _; rfl
  have hoff : ∑ e ∈ s.offDiag, hR e.2 * dR e.1 ≤ (∑ R ∈ s, hR R) * ∑ R ∈ s, dR R := by
    calc ∑ e ∈ s.offDiag, hR e.2 * dR e.1 ≤ ∑ e ∈ s ×ˢ s, hR e.2 * dR e.1 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun e he => by
            rw [Finset.mem_offDiag] at he
            exact Finset.mem_product.mpr ⟨he.1, he.2.1⟩) (by simp)
      _ = (∑ R ∈ s, hR R) * ∑ R ∈ s, dR R := by
          rw [Finset.sum_product]
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
  have hb := Finset.sum_le_sum hpair
  have hmul : (∑ R ∈ s, hR R) * ∑ R ∈ s, dR R ≤ Q.natDegree * P64Caps.YZ.yzSupportDegree Q 1 :=
    Nat.mul_le_mul (sum_natDegree_le Q hQ) (sum_yz_le Q hQ 1)
  rw [hsym] at hb
  omega

end Pairs

end P64Resultant
end ProximityPrize.SubmissionBinaryLower
