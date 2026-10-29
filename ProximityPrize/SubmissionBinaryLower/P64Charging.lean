import ProximityPrize.SubmissionBinaryLower.P64Cofactor

/-!
# Charging the bad slopes to the factors of one interpolant (PROOF.md 3.1, 3.2)

Fix a nonzero `Q` and, for every slope `z` of a finite set `S`, a witness `P z` with
`Q(X, P z (X), z) = 0` (Lemma GS). Every `z ∈ S` falls in

- `(Y0)`: `Q(X, Y, z) = 0`;
- `(P)`: not `(Y0)`, and at least two distinct normalized factors vanish along the curve;
- `(S_R)`: not `(Y0)`, and `R` is the only normalized factor that vanishes along the curve.

This file proves the cover `S ⊆ (Y0) ∪ (P) ∪ ⋃_R (S_R)` (PROOF.md 5, item 10 of formal-plan.md:
a cover, not a partition), shows that `(S_R)` is empty for `Y`-free `R` and consists of dangerous
slopes for `deg_Y R ≥ 2` (Theorem D), and proves the budgets (2.4) for the factor invariants.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Charging

open Polynomial P64LineOrder BCHKSSubstitutionVanish P64Cofactor

variable {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

/-- The distinct normalized factors of `Q`. -/
noncomputable abbrev factors (Q : Tri) : Finset Tri :=
  (UniqueFactorizationMonoid.normalizedFactors (α := Tri) Q).toFinset

/-- Case `(Y0)`: the plane `Z = z` lies on `Q = 0`. -/
noncomputable def caseY0 (Q : Tri) (S : Finset F) : Finset F :=
  S.filter fun z => specializeZ Q z = 0

/-- Case `(P)`: two distinct factors contain the curve. -/
noncomputable def casePair (Q : Tri) (S : Finset F) (P : F → F[X]) : Finset F :=
  S.filter fun z => specializeZ Q z ≠ 0 ∧
    ∃ R ∈ factors Q, ∃ R' ∈ factors Q, R ≠ R' ∧ triEval R z (P z) = 0 ∧ triEval R' z (P z) = 0

/-- Case `(S_R)`: `R` is the only factor containing the curve. -/
noncomputable def caseSingle (Q : Tri) (S : Finset F) (P : F → F[X]) (R : Tri) : Finset F :=
  S.filter fun z => specializeZ Q z ≠ 0 ∧ triEval R z (P z) = 0 ∧
    ∀ R' ∈ factors Q, triEval R' z (P z) = 0 → R' = R

/-- The cover of PROOF.md 3.1. -/
theorem subset_cover (Q : Tri) (hQ : Q ≠ 0) (S : Finset F) (P : F → F[X])
    (hbad : ∀ z ∈ S, triEval Q z (P z) = 0) :
    S ⊆ caseY0 Q S ∪ casePair Q S P ∪ (factors Q).biUnion (caseSingle Q S P) := by
  classical
  intro z hz
  by_cases hY0 : specializeZ Q z = 0
  · simp [caseY0, hz, hY0]
  obtain ⟨R, hR, hR0⟩ := exists_normalizedFactor_triEval_eq_zero Q hQ z (P z) (hbad z hz)
  by_cases hpair : ∃ R' ∈ factors Q, R' ≠ R ∧ triEval R' z (P z) = 0
  · obtain ⟨R', hR', hne, hR'0⟩ := hpair
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp only [casePair, Finset.mem_filter]
    exact ⟨hz, hY0, R, Multiset.mem_toFinset.mpr hR, R', hR', hne.symm, hR0, hR'0⟩
  · push Not at hpair
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨R, Multiset.mem_toFinset.mpr hR, ?_⟩
    simp only [caseSingle, Finset.mem_filter]
    refine ⟨hz, hY0, hR0, fun R' hR' h0 => ?_⟩
    by_contra hne
    exact hpair R' hR' hne h0

/-- The counting form of the cover. -/
theorem card_le_cover (Q : Tri) (hQ : Q ≠ 0) (S : Finset F) (P : F → F[X])
    (hbad : ∀ z ∈ S, triEval Q z (P z) = 0) :
    S.card ≤ (caseY0 Q S).card + (casePair Q S P).card +
      ∑ R ∈ factors Q, (caseSingle Q S P R).card := by
  classical
  calc S.card ≤ (caseY0 Q S ∪ casePair Q S P ∪ (factors Q).biUnion (caseSingle Q S P)).card :=
        Finset.card_le_card (subset_cover Q hQ S P hbad)
    _ ≤ (caseY0 Q S ∪ casePair Q S P).card + ((factors Q).biUnion (caseSingle Q S P)).card :=
        Finset.card_union_le _ _
    _ ≤ (caseY0 Q S).card + (casePair Q S P).card +
          ∑ R ∈ factors Q, (caseSingle Q S P R).card := by
        gcongr
        · exact Finset.card_union_le _ _
        · exact Finset.card_biUnion_le

/-- `specializeZ` as a ring homomorphism. -/
noncomputable def specializeZHom (z : F) : Tri →+* Polynomial (Polynomial F) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z))

omit [DecidableEq F] [NormalizationMonoid F] in
lemma specializeZHom_apply (z : F) (G : Tri) : specializeZHom z G = specializeZ G z := rfl

/-- A `Y`-free factor vanishing along a bad curve contains the whole plane `Z = z`, so `(S_R)` is
empty for `deg_Y R = 0` (PROOF.md 3.1). -/
theorem caseSingle_eq_empty_of_natDegree_eq_zero (Q : Tri) (S : Finset F) (P : F → F[X])
    (R : Tri) (hR : R ∈ factors Q) (h0 : R.natDegree = 0) : caseSingle Q S P R = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  simp only [caseSingle, Finset.mem_filter] at hz
  obtain ⟨_, hY0, hRz, _⟩ := hz
  apply hY0
  have hRC : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hspec : specializeZ R z = 0 := by
    have : triEval R z (P z) = Polynomial.map (Polynomial.evalRingHom z) (R.coeff 0) := by
      rw [hRC]
      simp [triEval, specializeZ]
    rw [this] at hRz
    rw [hRC]
    simp [specializeZ, hRz]
  have hdvd : R ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (α := Tri)
    (Multiset.mem_toFinset.mp hR)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, ← specializeZHom_apply, map_mul, specializeZHom_apply, hspec, zero_mul]

/-- Theorem D applied to the charging: for `deg_Y R ≥ 2`, every slope in `(S_R)` is dangerous. -/
theorem caseSingle_dangerous {ι : Type*} (ω : ι ↪ F) (y : ι → F[X]) (m k Agr : ℕ)
    (Q : Tri) (hQ : Q ≠ 0) (S : Finset F) (P : F → F[X]) (Az : F → Finset ι)
    (hAk : Agr < 2 * k) (hGS : ∀ i, OrdGE Q (ω i) (y i) m)
    (hwQ : P64Caps.Weighted.weightedSupportDegree Q k + 1 ≤ m * Agr)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ k) (hAz : ∀ z ∈ S, Agr ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (ω i) = (y i).eval z)
    (R : Tri) (hR : R ∈ factors Q) (h2 : 2 ≤ R.natDegree) :
    ∀ z ∈ caseSingle Q S P R, Dangerous ω y k Agr R (Az z) := by
  intro z hz
  simp only [caseSingle, Finset.mem_filter] at hz
  obtain ⟨hzS, _, hRz, hsingle⟩ := hz
  exact dangerous_of_single_factor ω y m k Agr Q R hQ (Multiset.mem_toFinset.mp hR) h2 hAk hGS
    hwQ z (P z) (hP z hzS) (Az z) (hAz z hzS) (hmatch z hzS)
    (fun R' hR' h0 => hsingle R' (Multiset.mem_toFinset.mpr hR') h0)

/-! ### Budgets (2.4) -/

/-- An invariant additive over products of nonzero polynomials sums over the distinct normalized
factors to at most its value on `Q`. -/
theorem sum_factors_le (φ : Tri → ℕ) (hφ : ∀ G H : Tri, G ≠ 0 → H ≠ 0 → φ (G * H) = φ G + φ H)
    (Q : Tri) (hQ : Q ≠ 0) : ∑ R ∈ factors Q, φ R ≤ φ Q := by
  classical
  have hne : ∀ R ∈ factors Q, R ≠ 0 := fun R hR =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Tri) R
      (Multiset.mem_toFinset.mp hR)).ne_zero
  have hprod : ∀ s : Finset Tri, (∀ R ∈ s, R ≠ 0) →
      s.prod id ≠ 0 ∧ φ (s.prod id) = ∑ R ∈ s, φ R + φ 1 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have ih' := ih (fun R hR => hs R (Finset.mem_insert_of_mem hR))
        have ha0 := hs a (Finset.mem_insert_self a s)
        rw [Finset.prod_insert ha, Finset.sum_insert ha, id, hφ _ _ ha0 ih'.1, ih'.2]
        exact ⟨mul_ne_zero ha0 ih'.1, by ring⟩
  have hdvd : (factors Q).prod id ∣ Q := by
    have hset := Multiset.toFinset_prod_dvd_prod
      (UniqueFactorizationMonoid.normalizedFactors (α := Tri) Q)
    exact hset.trans (UniqueFactorizationMonoid.prod_normalizedFactors (α := Tri) hQ).dvd
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hQ (by simpa using hc)
  obtain ⟨hp0, hpφ⟩ := hprod (factors Q) hne
  have hQφ : φ Q = ∑ R ∈ factors Q, φ R + φ 1 + φ c := by
    conv_lhs => rw [hc]
    rw [hφ _ _ hp0 hc0, hpφ]
  omega

theorem sum_natDegree_le (Q : Tri) (hQ : Q ≠ 0) :
    ∑ R ∈ factors Q, R.natDegree ≤ Q.natDegree :=
  sum_factors_le _ (fun _ _ hG hH => natDegree_mul hG hH) Q hQ

theorem sum_weighted_le (Q : Tri) (hQ : Q ≠ 0) (k : ℕ) :
    ∑ R ∈ factors Q, P64Caps.Weighted.weightedSupportDegree R k ≤
      P64Caps.Weighted.weightedSupportDegree Q k :=
  sum_factors_le _ (fun G H hG hH => P64Caps.Weighted.weightedSupportDegree_mul G H k hG hH) Q hQ

theorem sum_yz_le (Q : Tri) (hQ : Q ≠ 0) (k : ℕ) :
    ∑ R ∈ factors Q, P64Caps.YZ.yzSupportDegree R k ≤ P64Caps.YZ.yzSupportDegree Q k :=
  sum_factors_le _ (fun G H hG hH => P64Caps.YZ.yzSupportDegree_mul G H k hG hH) Q hQ

/-- `Σ a_R b_R ≤ (Σ a_R)(Σ b_R)` for natural-valued invariants. -/
theorem sum_mul_le_mul_sum {α : Type*} (s : Finset α) (a b : α → ℕ) :
    ∑ R ∈ s, a R * b R ≤ (∑ R ∈ s, a R) * ∑ R ∈ s, b R := by
  classical
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun R hR =>
    Nat.mul_le_mul_left _ (Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) hR)

end P64Charging
end ProximityPrize.SubmissionBinaryLower
