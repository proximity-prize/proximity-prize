import ProximityPrize.SubmissionBinaryLower.P64FactorCaps

/-!
# The cofactor lemma and single-factor slopes (PROOF.md 4.2)

Lemma C: if `Q = R^a · Q''` satisfies the interpolation conditions, `a ≤ m`, and the bad slope
`z` is not dangerous for `R`, then the bad curve `Y = P(X), Z = z` lies on `Q'' = 0`. For a
factor of `Y`-degree at least two, `a ≤ m` is automatic.

Theorem D: a bad slope whose curve lies on exactly one factor `R` of `Q`, with `deg_Y R ≥ 2`,
is dangerous for `R`.

Everything is stated over a generic field `F`, index type `ι`, evaluation points `ω` and lines
`y i = u0 i + Z·u1 i` (any `y : ι → F[Z]`), with parameters `m` (multiplicity), `k` (degree bound
`D` of the codewords) and `Agr` (agreement `A`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Cofactor

open Polynomial P64LineOrder BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F]

/-- `G ↦ G(X, P(X), z)` as a ring homomorphism. -/
noncomputable def triEvalHom (z : F) (P : F[X]) :
    Polynomial (Polynomial (Polynomial F)) →+* F[X] :=
  (Polynomial.evalRingHom P).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z)))

lemma triEvalHom_apply (z : F) (P : F[X]) (G : Polynomial (Polynomial (Polynomial F))) :
    triEvalHom z P G = triEval G z P := rfl

lemma triEval_mul (z : F) (P : F[X]) (G H : Polynomial (Polynomial (Polynomial F))) :
    triEval (G * H) z P = triEval G z P * triEval H z P := by
  simp only [← triEvalHom_apply, map_mul]

lemma triEval_pow (z : F) (P : F[X]) (G : Polynomial (Polynomial (Polynomial F))) (a : ℕ) :
    triEval (G ^ a) z P = triEval G z P ^ a := by
  simp only [← triEvalHom_apply, map_pow]

/-- Roots at distinct points use up at most the degree. -/
theorem sum_rootMultiplicity_le_natDegree [DecidableEq F] (f : F[X]) (ω : ι ↪ F)
    (A : Finset ι) : ∑ i ∈ A, f.rootMultiplicity (ω i) ≤ f.natDegree := by
  classical
  let xs : Finset F := A.map ω
  have hselected : ∑ x ∈ xs, Multiset.count x f.roots ≤ f.roots.card := by
    calc
      ∑ x ∈ xs, Multiset.count x f.roots ≤
          ∑ x ∈ xs ∪ f.roots.toFinset, Multiset.count x f.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by simp)
      _ = ∑ x ∈ f.roots.toFinset, Multiset.count x f.roots := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro x _ hx
        exact Multiset.count_eq_zero.mpr (by simpa using hx)
      _ = f.roots.card := Multiset.toFinset_sum_count_eq f.roots
  calc
    ∑ i ∈ A, f.rootMultiplicity (ω i) = ∑ x ∈ xs, f.rootMultiplicity x :=
      (Finset.sum_map A ω (fun x => f.rootMultiplicity x)).symm
    _ = ∑ x ∈ xs, Multiset.count x f.roots :=
      Finset.sum_congr rfl fun x _ => (count_roots f).symm
    _ ≤ f.roots.card := hselected
    _ ≤ f.natDegree := card_roots' f

section Weighted

open P64Caps.Weighted

lemma weightedSupportDegree_pow (R : Polynomial (Polynomial (Polynomial F))) (hR : R ≠ 0)
    (k a : ℕ) : weightedSupportDegree (R ^ a) k = a * weightedSupportDegree R k := by
  induction a with
  | zero =>
      rw [pow_zero, zero_mul, ← C_1]
      unfold weightedSupportDegree
      rw [support_C one_ne_zero]
      simp
  | succ a ih =>
      rw [pow_succ, weightedSupportDegree_mul _ _ _ (pow_ne_zero a hR) hR, ih]
      ring

/-- The `Y`-degree is paid at weight `k` per power of `Y`. -/
lemma natDegree_mul_le_weightedSupportDegree (R : Polynomial (Polynomial (Polynomial F)))
    (hR : R ≠ 0) (k : ℕ) : k * R.natDegree ≤ weightedSupportDegree R k := by
  have h := coeffWeight_le_of_ne R k R.natDegree (by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hR)
  omega

/-- The substituted polynomial has degree at most the weighted degree. -/
lemma natDegree_triEval_le (G : Polynomial (Polynomial (Polynomial F))) (z : F) (P : F[X])
    (k : ℕ) (hP : P.natDegree ≤ k) :
    (triEval G z P).natDegree ≤ weightedSupportDegree G k := by
  apply triEval_natDegree_le_of_weighted_X_cap G z P k _ hP
  intro j a ha
  have hj : G.coeff j ≠ 0 := fun h => ha (by simp [h])
  have h1 := coeffWeight_le_of_ne G k j hj
  have h2 : a ≤ (G.coeff j).natDegree := le_natDegree_of_ne_zero ha
  omega

end Weighted

open P64Caps.Weighted

/-- The bad slope `z` (witness `P`, agreement set `Az`) is **dangerous** for `R`:
`Σ_{i ∈ Az} (μ_i - 1) > w - A` (PROOF.md 2.4). -/
def Dangerous (ω : ι ↪ F) (y : ι → F[X]) (k Agr : ℕ)
    (R : Polynomial (Polynomial (Polynomial F))) (Az : Finset ι) : Prop :=
  (weightedSupportDegree R k : ℤ) - Agr < ∑ i ∈ Az, ((lineOrd R (ω i) (y i) : ℤ) - 1)

/-- **Lemma C** (cofactor). -/
theorem triEval_cofactor_eq_zero [DecidableEq F] (ω : ι ↪ F) (y : ι → F[X]) (m k Agr : ℕ)
    (R Q'' : Polynomial (Polynomial (Polynomial F))) (a : ℕ) (hR : R ≠ 0) (hQ'' : Q'' ≠ 0)
    (hGS : ∀ i, OrdGE (R ^ a * Q'') (ω i) (y i) m)
    (hwQ : weightedSupportDegree (R ^ a * Q'') k + 1 ≤ m * Agr)
    (ham : a ≤ m) (z : F) (P : F[X]) (hP : P.natDegree ≤ k) (Az : Finset ι)
    (hAz : Agr ≤ Az.card) (hmatch : ∀ i ∈ Az, P.eval (ω i) = (y i).eval z)
    (hnd : ¬ Dangerous ω y k Agr R Az) :
    triEval Q'' z P = 0 := by
  classical
  by_contra hne
  have hRa : R ^ a ≠ 0 := pow_ne_zero a hR
  set μ : ι → ℕ := fun i => lineOrd R (ω i) (y i) with hμ
  have hmult : ∀ i ∈ Az, m - a * μ i ≤ (triEval Q'' z P).rootMultiplicity (ω i) := by
    intro i hi
    have hord := ordGE_cofactor hRa hQ'' (ω i) (y i) m (hGS i)
    rw [lineOrd_pow hR] at hord
    exact le_rootMultiplicity_triEval Q'' (ω i) z (y i) P _ hord (hmatch i hi) hne
  have hsum : ∑ i ∈ Az, (m - a * μ i) ≤ weightedSupportDegree Q'' k :=
    (Finset.sum_le_sum hmult).trans ((sum_rootMultiplicity_le_natDegree _ ω Az).trans
      (natDegree_triEval_le Q'' z P k hP))
  have hwdeg := weightedSupportDegree_mul (R ^ a) Q'' k hRa hQ''
  rw [weightedSupportDegree_pow R hR] at hwdeg
  rw [hwdeg] at hwQ
  set w := weightedSupportDegree R k
  set wq := weightedSupportDegree Q'' k
  -- integer form of the counting
  have hsumZ : (∑ i ∈ Az, ((m : ℤ) - a * μ i)) ≤ wq := by
    have h1 : (∑ i ∈ Az, ((m : ℤ) - a * μ i)) ≤ ∑ i ∈ Az, ((m - a * μ i : ℕ) : ℤ) :=
      Finset.sum_le_sum fun i _ => by omega
    have h2 : (∑ i ∈ Az, ((m - a * μ i : ℕ) : ℤ)) ≤ wq := by exact_mod_cast hsum
    exact h1.trans h2
  have hnd' : (∑ i ∈ Az, ((μ i : ℤ) - 1)) ≤ (w : ℤ) - Agr := by
    unfold Dangerous at hnd
    push Not at hnd
    exact hnd
  rw [Finset.sum_sub_distrib] at hsumZ hnd'
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsumZ hnd'
  rw [← Finset.mul_sum] at hsumZ
  have hwQZ : ((a * w + wq : ℕ) : ℤ) + 1 ≤ (m : ℤ) * Agr := by exact_mod_cast hwQ
  push_cast at hwQZ
  have hAzZ : (Agr : ℤ) ≤ Az.card := by exact_mod_cast hAz
  have hamZ : (a : ℤ) ≤ m := by exact_mod_cast ham
  have hp1 : 0 ≤ ((m : ℤ) - a) * ((Az.card : ℤ) - Agr) :=
    mul_nonneg (by linarith) (by linarith)
  have hp2 : 0 ≤ (a : ℤ) * ((w : ℤ) - Agr - (∑ i ∈ Az, (μ i : ℤ) - Az.card)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- For a factor of `Y`-degree at least two, its multiplicity in `Q` is below `m`. -/
theorem lt_of_two_le_natDegree (m k Agr : ℕ) (R Q'' : Polynomial (Polynomial (Polynomial F)))
    (a : ℕ) (hR : R ≠ 0) (hQ'' : Q'' ≠ 0) (h2 : 2 ≤ R.natDegree) (hAk : Agr < 2 * k)
    (hwQ : weightedSupportDegree (R ^ a * Q'') k + 1 ≤ m * Agr) : a < m := by
  have hwdeg := weightedSupportDegree_mul (R ^ a) Q'' k (pow_ne_zero a hR) hQ''
  rw [weightedSupportDegree_pow R hR] at hwdeg
  rw [hwdeg] at hwQ
  have hw := natDegree_mul_le_weightedSupportDegree R hR k
  have h1 : a * (2 * k) ≤ a * weightedSupportDegree R k :=
    Nat.mul_le_mul_left a (by nlinarith)
  have h2 : a * (2 * k) < m * (2 * k) := by
    calc a * (2 * k) < m * Agr := by omega
      _ ≤ m * (2 * k) := Nat.mul_le_mul_left m hAk.le
  exact Nat.lt_of_mul_lt_mul_right h2

/-- Some normalized factor of a nonzero non-unit `G` with `G(X, P(X), z) = 0` also vanishes. -/
theorem exists_normalizedFactor_triEval_eq_zero [DecidableEq F] [NormalizationMonoid F]
    (G : Polynomial (Polynomial (Polynomial F))) (hG : G ≠ 0) (z : F) (P : F[X])
    (h0 : triEval G z P = 0) :
    ∃ p ∈ UniqueFactorizationMonoid.normalizedFactors G, triEval p z P = 0 := by
  classical
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors (α := Polynomial (Polynomial (Polynomial F))) hG
  obtain ⟨u, hu⟩ := hassoc
  have hprod : triEvalHom z P (UniqueFactorizationMonoid.normalizedFactors G).prod = 0 := by
    have : triEvalHom z P G = 0 := h0
    rw [← hu, map_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h ((u.isUnit.map (triEvalHom z P)).ne_zero)
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hprod
  obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.mp hprod
  exact ⟨q, hq, hq0⟩

/-- **Theorem D** (single-factor slopes are dangerous). Let `R` be a normalized factor of `Q` with
`deg_Y R ≥ 2`, and let the bad curve of `z` lie on `R` and on no other normalized factor of `Q`.
Then `z` is dangerous for `R`. -/
theorem dangerous_of_single_factor [DecidableEq F] [NormalizationMonoid F]
    (ω : ι ↪ F) (y : ι → F[X]) (m k Agr : ℕ)
    (Q R : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hR : R ∈ UniqueFactorizationMonoid.normalizedFactors Q) (h2 : 2 ≤ R.natDegree)
    (hAk : Agr < 2 * k)
    (hGS : ∀ i, OrdGE Q (ω i) (y i) m)
    (hwQ : weightedSupportDegree Q k + 1 ≤ m * Agr)
    (z : F) (P : F[X]) (hP : P.natDegree ≤ k) (Az : Finset ι)
    (hAz : Agr ≤ Az.card) (hmatch : ∀ i ∈ Az, P.eval (ω i) = (y i).eval z)
    (hsingle : ∀ R' ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triEval R' z P = 0 → R' = R) :
    Dangerous ω y k Agr R Az := by
  classical
  have hRprime := UniqueFactorizationMonoid.prime_of_normalized_factor (α := Polynomial (Polynomial (Polynomial F))) R hR
  have hRirr : Irreducible R := hRprime.irreducible
  have hR0 : R ≠ 0 := hRprime.ne_zero
  obtain ⟨a, Q'', hndvd, hQeq⟩ := WfDvdMonoid.max_power_factor (α := Polynomial (Polynomial (Polynomial F))) hQ hRirr
  have hQ'' : Q'' ≠ 0 := by
    rintro rfl
    simp at hQeq
    exact hQ hQeq
  subst hQeq
  have ham : a < m := lt_of_two_le_natDegree m k Agr R Q'' a hR0 hQ'' h2 hAk hwQ
  by_contra hnd
  have h0 := triEval_cofactor_eq_zero ω y m k Agr R Q'' a hR0 hQ'' hGS hwQ ham.le z P hP Az
    hAz hmatch hnd
  obtain ⟨p, hp, hp0⟩ := exists_normalizedFactor_triEval_eq_zero Q'' hQ'' z P h0
  have hpirr : Irreducible p :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor (α := Polynomial (Polynomial (Polynomial F))) p hp).irreducible
  have hpdvd : p ∣ Q'' := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (α := Polynomial (Polynomial (Polynomial F))) hp
  obtain ⟨q, hq, hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd (α := Polynomial (Polynomial (Polynomial F)))
    hQ hpirr (dvd_mul_of_dvd_right hpdvd (R ^ a))
  have hq0 : triEval q z P = 0 := by
    obtain ⟨u, hu⟩ := hpq
    rw [← hu, triEval_mul, hp0, zero_mul]
  have hqR := hsingle q hq hq0
  subst hqR
  exact hndvd (hpq.symm.dvd.trans hpdvd)

end P64Cofactor
end ProximityPrize.SubmissionBinaryLower
