import ProximityPrize.SubmissionLower.BCHKSHigherDerivativeRoot6400
import ProximityPrize.SubmissionLower.BCHKSResultantDegree
import ProximityPrize.SubmissionLower.BCHKSQuadraticKernel6400
import ProximityPrize.SubmissionLower.BCHKSPairSetup
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower
namespace BCHKSRadicalMultiplicityBridge6400

open Polynomial
open BCHKSHigherDerivativeRoot6400

set_option maxHeartbeats 2000000

/-!
The algebraic core of the global-radical owner bridge.

After specialization, write the interpolant as a root-free scalar times
the product of powers of its distinct global factors.  If the product of
those distinct factors is separable, every root belongs to exactly one
factor and is simple there.  Consequently its multiplicity in the full
interpolant is exactly that factor's global exponent.  Higher derivative
vanishing can then be read directly as a lower bound on the exponent.

This formulation deliberately works over an arbitrary integral coefficient
ring.  In the benchmark the coefficient ring is `F[X]`, the root is the
received polynomial `P`, and specialization is evaluation in `Z`.
-/

/-- A root is simple when the polynomial vanishes there but its derivative
does not. -/
theorem rootMultiplicity_eq_one_of_isRoot_derivative_not_isRoot
    {A : Type*} [CommRing A]
    (f : Polynomial A) (p : A) (hf : f ≠ 0)
    (hroot : f.IsRoot p) (hder : ¬ f.derivative.IsRoot p) :
    f.rootMultiplicity p = 1 := by
  have hpos : 0 < f.rootMultiplicity p :=
    (Polynomial.rootMultiplicity_pos hf).2 hroot
  have hle : f.rootMultiplicity p ≤ 1 := by
    by_contra hnot
    have hgt : 1 < f.rootMultiplicity p := Nat.lt_of_not_ge hnot
    exact hder ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hf).mp hgt).2
  omega

/-- Root multiplicity is multiplied by the exponent under a power. -/
theorem rootMultiplicity_pow
    {A : Type*} [CommRing A] [IsDomain A]
    (f : Polynomial A) (p : A) (e : ℕ) (hf : f ≠ 0) :
    (f ^ e).rootMultiplicity p = e * f.rootMultiplicity p := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero e hf) hf), ih]
      simp only [Nat.succ_mul]

/-- Additivity of root multiplicities for an explicit finite product of
powered nonzero factors. -/
theorem rootMultiplicity_finset_prod_pow
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    (S.prod (fun i ↦ f i ^ e i)).rootMultiplicity p =
      ∑ i ∈ S, e i * (f i).rootMultiplicity p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hfi : f i ≠ 0 := hf i (by simp)
      have hrest : S.prod (fun j ↦ f j ^ e j) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        exact pow_ne_zero _ (hf j (by simp [hj]))
      rw [Finset.prod_insert hi, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero _ hfi) hrest), Finset.sum_insert hi]
      rw [rootMultiplicity_pow (f := f i) (p := p) (e := e i) hfi]
      rw [ih (fun j hj ↦ hf j (by simp [hj]))]

/-- A separable polynomial and its derivative cannot vanish at the same
point.  This Bezout proof works over rings, not only fields. -/
theorem derivative_not_isRoot_of_separable_isRoot
    {A : Type*} [CommRing A] [Nontrivial A]
    (f : Polynomial A) (p : A) (hsep : f.Separable)
    (hroot : f.IsRoot p) :
    ¬ f.derivative.IsRoot p := by
  intro hder
  have hcop : IsCoprime f f.derivative := hsep
  have hne := Polynomial.aeval_ne_zero_of_isCoprime hcop p
  rcases hne with hne | hne
  · apply hne
    simpa [Polynomial.IsRoot] using hroot
  · apply hne
    simpa [Polynomial.IsRoot] using hder

/-- The root multiplicity of a separable polynomial at any root is one. -/
theorem rootMultiplicity_eq_one_of_separable_isRoot
    {A : Type*} [CommRing A] [Nontrivial A]
    (f : Polynomial A) (p : A) (hsep : f.Separable)
    (hroot : f.IsRoot p) :
    f.rootMultiplicity p = 1 := by
  exact rootMultiplicity_eq_one_of_isRoot_derivative_not_isRoot
    f p hsep.ne_zero hroot
      (derivative_not_isRoot_of_separable_isRoot f p hsep hroot)

/-- For a separable product of distinct factors, a chosen root has
multiplicity one in its factor and multiplicity zero in every other factor.
This single statement subsumes all pairwise resultants and all individual
self-resultants after specialization. -/
theorem radical_factor_root_multiplicities
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hsep : (S.prod f).Separable)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p) :
    (f q).rootMultiplicity p = 1 ∧
      ∀ r ∈ S, r ≠ q → (f r).rootMultiplicity p = 0 := by
  classical
  have hradroot : (S.prod f).IsRoot p :=
    (Polynomial.isRoot_prod S f p).2 ⟨q, hqS, hqroot⟩
  have hradeq : (S.prod f).rootMultiplicity p = 1 :=
    rootMultiplicity_eq_one_of_separable_isRoot (S.prod f) p hsep hradroot
  have hsum : (S.prod f).rootMultiplicity p =
      ∑ i ∈ S, (f i).rootMultiplicity p := by
    simpa using rootMultiplicity_finset_prod_pow S f (fun _ ↦ 1) p hf
  have hqpos : 0 < (f q).rootMultiplicity p :=
    (Polynomial.rootMultiplicity_pos (hf q hqS)).2 hqroot
  have hqle : (f q).rootMultiplicity p ≤
      (S.prod f).rootMultiplicity p := by
    rw [hsum]
    exact Finset.single_le_sum
      (f := fun i ↦ (f i).rootMultiplicity p)
      (fun _ _ ↦ Nat.zero_le _) hqS
  have hqeq : (f q).rootMultiplicity p = 1 := by omega
  refine ⟨hqeq, ?_⟩
  intro r hrS hrq
  by_contra hrzero
  have hrpos : 0 < (f r).rootMultiplicity p := Nat.pos_of_ne_zero hrzero
  have hsubset : ({q, r} : Finset ι) ⊆ S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hqS
    · exact hrS
  have htwole : (f q).rootMultiplicity p + (f r).rootMultiplicity p ≤
      ∑ i ∈ S, (f i).rootMultiplicity p := by
    calc
      (f q).rootMultiplicity p + (f r).rootMultiplicity p =
          ∑ i ∈ ({q, r} : Finset ι), (f i).rootMultiplicity p := by
            rw [Finset.sum_insert (by simpa using hrq.symm),
              Finset.sum_singleton]
      _ ≤ ∑ i ∈ S, (f i).rootMultiplicity p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
  rw [← hsum, hradeq] at htwole
  omega

/-- Pointwise form of `radical_factor_root_multiplicities`.  A global Bezout
certificate is unnecessary: it is enough that the radical's derivative does
not vanish at the particular polynomial root.  This is the form certified by
a nonzero specialized fixed resultant over `F[X]`. -/
theorem radical_factor_root_multiplicities_of_derivative_not_isRoot
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hradDerivative : ¬ (S.prod f).derivative.IsRoot p) :
    (f q).rootMultiplicity p = 1 ∧
      ∀ r ∈ S, r ≠ q → (f r).rootMultiplicity p = 0 := by
  classical
  have hradroot : (S.prod f).IsRoot p :=
    (Polynomial.isRoot_prod S f p).2 ⟨q, hqS, hqroot⟩
  have hrad0 : S.prod f ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr hf
  have hradeq : (S.prod f).rootMultiplicity p = 1 :=
    rootMultiplicity_eq_one_of_isRoot_derivative_not_isRoot
      (S.prod f) p hrad0 hradroot hradDerivative
  have hsum : (S.prod f).rootMultiplicity p =
      ∑ i ∈ S, (f i).rootMultiplicity p := by
    simpa using rootMultiplicity_finset_prod_pow S f (fun _ ↦ 1) p hf
  have hqpos : 0 < (f q).rootMultiplicity p :=
    (Polynomial.rootMultiplicity_pos (hf q hqS)).2 hqroot
  have hqle : (f q).rootMultiplicity p ≤
      (S.prod f).rootMultiplicity p := by
    rw [hsum]
    exact Finset.single_le_sum
      (f := fun i ↦ (f i).rootMultiplicity p)
      (fun _ _ ↦ Nat.zero_le _) hqS
  have hqeq : (f q).rootMultiplicity p = 1 := by omega
  refine ⟨hqeq, ?_⟩
  intro r hrS hrq
  by_contra hrzero
  have hrpos : 0 < (f r).rootMultiplicity p := Nat.pos_of_ne_zero hrzero
  have hsubset : ({q, r} : Finset ι) ⊆ S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hqS
    · exact hrS
  have htwole : (f q).rootMultiplicity p + (f r).rootMultiplicity p ≤
      ∑ i ∈ S, (f i).rootMultiplicity p := by
    calc
      (f q).rootMultiplicity p + (f r).rootMultiplicity p =
          ∑ i ∈ ({q, r} : Finset ι), (f i).rootMultiplicity p := by
            rw [Finset.sum_insert (by simpa using hrq.symm),
              Finset.sum_singleton]
      _ ≤ ∑ i ∈ S, (f i).rootMultiplicity p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
  rw [← hsum, hradeq] at htwole
  omega

/-- Under a separable radical, root multiplicity in the product with global
exponents is exactly the exponent of the unique root-owning factor. -/
theorem rootMultiplicity_powered_product_eq_exponent
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hsep : (S.prod f).Separable)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p) :
    (S.prod (fun i ↦ f i ^ e i)).rootMultiplicity p = e q := by
  classical
  obtain ⟨hqone, hother⟩ :=
    radical_factor_root_multiplicities S f p hf hsep q hqS hqroot
  rw [rootMultiplicity_finset_prod_pow S f e p hf]
  rw [Finset.sum_eq_single q]
  · simp [hqone]
  · intro r hrS hrq
    simp [hother r hrS hrq]
  · exact fun hqnot ↦ (hqnot hqS).elim

/-- Pointwise-resultant version of the powered-product multiplicity formula. -/
theorem rootMultiplicity_powered_product_eq_exponent_of_derivative_not_isRoot
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hradDerivative : ¬ (S.prod f).derivative.IsRoot p) :
    (S.prod (fun i ↦ f i ^ e i)).rootMultiplicity p = e q := by
  classical
  obtain ⟨hqone, hother⟩ :=
    radical_factor_root_multiplicities_of_derivative_not_isRoot
      S f p hf q hqS hqroot hradDerivative
  rw [rootMultiplicity_finset_prod_pow S f e p hf]
  rw [Finset.sum_eq_single q]
  · simp [hqone]
  · intro r hrS hrq
    simp [hother r hrS hrq]
  · exact fun hqnot ↦ (hqnot hqS).elim

/-- A root-free prefactor does not alter the exponent read from a separable
radical.  This is the exact form needed after mapping a global unit through
specialization. -/
theorem rootMultiplicity_unit_mul_powered_product_eq_exponent
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ)
    (u Q : Polynomial A) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hu : u ≠ 0) (hunroot : ¬ u.IsRoot p)
    (hQ : Q = u * S.prod (fun i ↦ f i ^ e i))
    (hsep : (S.prod f).Separable)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p) :
    Q.rootMultiplicity p = e q := by
  have hprod : S.prod (fun i ↦ f i ^ e i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hf i hi)
  rw [hQ, Polynomial.rootMultiplicity_mul (mul_ne_zero hu hprod),
    Polynomial.rootMultiplicity_eq_zero hunroot, zero_add]
  exact rootMultiplicity_powered_product_eq_exponent
    S f e p hf hsep q hqS hqroot

/-- Pointwise-resultant version with a root-free prefactor. -/
theorem rootMultiplicity_unit_mul_powered_product_eq_exponent_of_derivative_not_isRoot
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ)
    (u Q : Polynomial A) (p : A)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hu : u ≠ 0) (hunroot : ¬ u.IsRoot p)
    (hQ : Q = u * S.prod (fun i ↦ f i ^ e i))
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hradDerivative : ¬ (S.prod f).derivative.IsRoot p) :
    Q.rootMultiplicity p = e q := by
  have hprod : S.prod (fun i ↦ f i ^ e i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hf i hi)
  rw [hQ, Polynomial.rootMultiplicity_mul (mul_ne_zero hu hprod),
    Polynomial.rootMultiplicity_eq_zero hunroot, zero_add]
  exact
    rootMultiplicity_powered_product_eq_exponent_of_derivative_not_isRoot
      S f e p hf q hqS hqroot hradDerivative

/-- Global radical specialization bridge.  If all derivatives through `J`
vanish at the specialized received polynomial and the specialized radical is
separable, then the unique owning factor's *global* exponent exceeds `J`.

No pairwise coprimality hypotheses appear: they are all consequences of the
one separability certificate for `S.prod f`. -/
theorem lt_exponent_of_iterYDerivative_eval_zero_of_radical_separable
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ)
    (u Q : Polynomial A) (p : A) (J : ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hu : u ≠ 0) (hunroot : ¬ u.IsRoot p)
    (hQ : Q = u * S.prod (fun i ↦ f i ^ e i))
    (hsep : (S.prod f).Separable)
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hderivatives : ∀ r ≤ J,
      Polynomial.eval p (iterYDerivative r Q) = 0)
    (hfactorial : (J.factorial : A) ∈ nonZeroDivisors A) :
    J < e q := by
  have hprod : S.prod (fun i ↦ f i ^ e i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hf i hi)
  have hQzero : Q ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero hu hprod
  have hlt : J < Q.rootMultiplicity p :=
    lt_rootMultiplicity_of_iterYDerivative_eval_zero
      Q p J hQzero hderivatives hfactorial
  rw [rootMultiplicity_unit_mul_powered_product_eq_exponent
    S f e u Q p hf hu hunroot hQ hsep q hqS hqroot] at hlt
  exact hlt

/-- The pointwise form used by the resultant specialization bridge. -/
theorem lt_exponent_of_iterYDerivative_eval_zero_of_radical_derivative_not_isRoot
    {A ι : Type*} [CommRing A] [IsDomain A] [DecidableEq ι]
    (S : Finset ι) (f : ι → Polynomial A) (e : ι → ℕ)
    (u Q : Polynomial A) (p : A) (J : ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hu : u ≠ 0) (hunroot : ¬ u.IsRoot p)
    (hQ : Q = u * S.prod (fun i ↦ f i ^ e i))
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot p)
    (hradDerivative : ¬ (S.prod f).derivative.IsRoot p)
    (hderivatives : ∀ r ≤ J,
      Polynomial.eval p (iterYDerivative r Q) = 0)
    (hfactorial : (J.factorial : A) ∈ nonZeroDivisors A) :
    J < e q := by
  have hprod : S.prod (fun i ↦ f i ^ e i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hf i hi)
  have hQzero : Q ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero hu hprod
  have hlt : J < Q.rootMultiplicity p :=
    lt_rootMultiplicity_of_iterYDerivative_eval_zero
      Q p J hQzero hderivatives hfactorial
  rw [rootMultiplicity_unit_mul_powered_product_eq_exponent_of_derivative_not_isRoot
    S f e u Q p hf hu hunroot hQ q hqS hqroot hradDerivative] at hlt
  exact hlt

/-! ## One fixed resultant certifies the pointwise radical condition -/

/-- Universe-polymorphic fixed-degree common-root vanishing.  The existing
benchmark helper is universe-zero; the fraction-field bridge below needs the
same elementary statement in the coefficient ring's universe. -/
theorem fixed_resultant_eq_zero_of_common_root_universe
    {K : Type*} [Field K] {P H : Polynomial K} {m n : ℕ} {y : K}
    (hPdeg : P.natDegree ≤ m) (hHdeg : H.natDegree ≤ n)
    (hsize : 0 < m + n) (hP : P.eval y = 0) (hH : H.eval y = 0) :
    Polynomial.resultant P H m n = 0 := by
  by_cases hne : P ≠ 0 ∨ H ≠ 0
  · have hstandard : Polynomial.resultant P H = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      refine ⟨hne, ?_⟩
      rintro ⟨a, b, hab⟩
      have heval := congrArg (fun r : Polynomial K ↦ r.eval y) hab
      simp [Polynomial.eval_add, Polynomial.eval_mul, hP, hH] at heval
    have hm : P.natDegree + (m - P.natDegree) = m :=
      Nat.add_sub_of_le hPdeg
    have hn : H.natDegree + (n - H.natDegree) = n :=
      Nat.add_sub_of_le hHdeg
    rw [← hm, ← hn, Polynomial.resultant_add_left_deg]
    · rw [Polynomial.resultant_add_right_deg]
      · simp [hstandard]
      · exact le_rfl
    · exact le_rfl
  · push Not at hne
    rcases hne with ⟨rfl, rfl⟩
    rcases m with _ | m <;> rcases n with _ | n <;> simp_all

/-- A nonzero fixed resultant over an integral domain rules out a common
root in that domain.  We pass to the fraction field only for the standard
common-root resultant theorem; injectivity descends the contradiction.

This is deliberately weaker than `B.Separable`: a nonzero resultant in
`F[X]` need not be a unit and hence need not give a Bezout identity over
`F[X][Y]`.  Pointwise derivative nonvanishing is exactly what the
multiplicity bridge needs. -/
theorem derivative_not_isRoot_of_fixed_resultant_ne_zero
    {A : Type*} [CommRing A] [IsDomain A]
    (B : Polynomial A) (p : A) (n : ℕ)
    (hBdeg : B.natDegree ≤ n) (hsize : 0 < n + (n - 1))
    (hres : Polynomial.resultant B B.derivative n (n - 1) ≠ 0)
    (hroot : B.IsRoot p) :
    ¬ B.derivative.IsRoot p := by
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  have hφ : Function.Injective φ := IsFractionRing.injective A K
  intro hder
  have hBmapdeg : (B.map φ).natDegree ≤ n :=
    Polynomial.natDegree_map_le.trans hBdeg
  have hDmapdeg : (B.derivative.map φ).natDegree ≤ n - 1 :=
    Polynomial.natDegree_map_le.trans
      ((Polynomial.natDegree_derivative_le B).trans
        (Nat.sub_le_sub_right hBdeg 1))
  have hrootK : (B.map φ).eval (φ p) = 0 :=
    (Polynomial.IsRoot.map (f := φ) hroot).eq_zero
  have hderK : (B.derivative.map φ).eval (φ p) = 0 :=
    (Polynomial.IsRoot.map (f := φ) hder).eq_zero
  have hzeroK : Polynomial.resultant (B.map φ) (B.derivative.map φ)
      n (n - 1) = 0 :=
    fixed_resultant_eq_zero_of_common_root_universe
      hBmapdeg hDmapdeg hsize hrootK hderK
  have hmapped : φ (Polynomial.resultant B B.derivative n (n - 1)) = 0 := by
    rw [← Polynomial.resultant_map_map]
    exact hzeroK
  apply hres
  apply hφ
  simpa using hmapped

/-- The single global radical obstruction, padded by the radical's original
outer degree so that it remains valid under degree-dropping specialization. -/
noncomputable def globalRadicalResultant
    {A : Type*} [CommRing A] (Rad : Polynomial A) : A :=
  Polynomial.resultant Rad Rad.derivative Rad.natDegree
    (Rad.natDegree - 1)

/-- The finite set of distinct normalized factors having positive outer
degree.  Classical decidable equality is encapsulated in this definition. -/
noncomputable def positiveNormalizedFactors
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) : Finset (Polynomial A) := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun H ↦ 0 < H.natDegree)

/-- Product of the distinct positive-degree normalized factors.  Degree-zero
factors are coefficient content and belong in the root-free prefactor after
specialization. -/
noncomputable def positiveNormalizedRadical
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) : Polynomial A :=
  (positiveNormalizedFactors Q).prod id

/-- Multiplicity of a normalized irreducible factor in the canonical UFD
factor multiset. -/
noncomputable def normalizedFactorExponent
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q H : Polynomial A) : ℕ := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors Q).count H

/-- Product, with multiplicity, of the normalized factors which are constant
in the outer variable.  This is the only nonunit content part omitted from
the positive normalized radical. -/
noncomputable def zeroDegreeNormalizedPart
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) : Polynomial A := by
  classical
  exact ((UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun H ↦ ¬ 0 < H.natDegree)).prod
      (fun H ↦ H ^ normalizedFactorExponent Q H)

/-- Exact canonical factorization into a unit, the outer-degree-zero content
part, and powers of the distinct positive-degree normalized factors. -/
theorem exists_unit_mul_zeroPart_mul_positiveFactors
    {A : Type*} [CommRing A] [IsDomain A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) (hQ : Q ≠ 0) :
    ∃ v : (Polynomial A)ˣ,
      Q = ((v : Polynomial A) * zeroDegreeNormalizedPart Q) *
        (positiveNormalizedFactors Q).prod
          (fun H ↦ H ^ normalizedFactorExponent Q H) ∧
      (((v : Polynomial A) * zeroDegreeNormalizedPart Q).natDegree = 0) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  let T := M.toFinset
  let S := positiveNormalizedFactors Q
  let Zs := T.filter (fun H ↦ ¬ (0 < H.natDegree))
  let powFactor : Polynomial A → Polynomial A := fun H ↦
    H ^ normalizedFactorExponent Q H
  have hcount : M.prod = T.prod powFactor := by
    simpa [T, powFactor, normalizedFactorExponent, M] using
      (Finset.prod_multiset_count M)
  have hsplit : S.prod powFactor * Zs.prod powFactor = T.prod powFactor := by
    simpa [S, Zs, T, positiveNormalizedFactors] using
      (Finset.prod_filter_mul_prod_filter_not T
        (fun H : Polynomial A ↦ 0 < H.natDegree) powFactor)
  obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hQ
  have hZfactor : ∀ H ∈ Zs, H ≠ 0 := by
    intro H hHZ
    have hHT : H ∈ T := (Finset.mem_filter.mp hHZ).1
    have hHM : H ∈ M := Multiset.mem_toFinset.mp (by simpa [T] using hHT)
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor H hHM).ne_zero
  have hZprod : Zs.prod powFactor ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro H hHZ
    exact pow_ne_zero _ (hZfactor H hHZ)
  have hZdegree : (Zs.prod powFactor).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (Polynomial.natDegree_prod_le Zs powFactor).trans
    have hsum : ∑ H ∈ Zs, (powFactor H).natDegree = 0 := by
      apply Finset.sum_eq_zero
      intro H hHZ
      have hzero : H.natDegree = 0 := by
        have := (Finset.mem_filter.mp hHZ).2
        omega
      simp [powFactor, Polynomial.natDegree_pow, hzero]
    exact hsum.le
  have huDegree :
      (((v : Polynomial A) * Zs.prod powFactor).natDegree = 0) := by
    rw [Polynomial.natDegree_mul v.ne_zero hZprod,
      Polynomial.natDegree_eq_zero_of_isUnit v.isUnit, hZdegree, zero_add]
  refine ⟨v, ?_, ?_⟩
  · calc
      Q = M.prod * (v : Polynomial A) := hv.symm
      _ = (T.prod powFactor) * (v : Polynomial A) := by rw [hcount]
      _ = (S.prod powFactor * Zs.prod powFactor) * (v : Polynomial A) := by
        rw [hsplit]
      _ = ((v : Polynomial A) * Zs.prod powFactor) * S.prod powFactor := by
        ring
      _ = ((v : Polynomial A) * zeroDegreeNormalizedPart Q) *
          (positiveNormalizedFactors Q).prod
            (fun H ↦ H ^ normalizedFactorExponent Q H) := by
        simp only [S, Zs, T, M, powFactor, zeroDegreeNormalizedPart,
          positiveNormalizedFactors]
  · simpa [Zs, T, powFactor, zeroDegreeNormalizedPart] using huDegree

/-- Every factor in the positive normalized radical is nonzero. -/
theorem positiveNormalizedRadical_factor_ne_zero
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q H : Polynomial A)
    (hH : H ∈ positiveNormalizedFactors Q) :
    H ≠ 0 := by
  classical
  have hfilter : H ∈
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
        (fun J ↦ 0 < J.natDegree) := by
    simpa [positiveNormalizedFactors] using hH
  have hmem : H ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp hfilter).1
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor H hmem).ne_zero

/-- The positive normalized radical is nonzero. -/
theorem positiveNormalizedRadical_ne_zero
    {A : Type*} [CommRing A] [IsDomain A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) :
    positiveNormalizedRadical Q ≠ 0 := by
  classical
  unfold positiveNormalizedRadical
  apply Finset.prod_ne_zero_iff.mpr
  intro H hH
  exact positiveNormalizedRadical_factor_ne_zero Q H hH

/-- The positive normalized radical divides the original polynomial. -/
theorem positiveNormalizedRadical_dvd
    {A : Type*} [CommRing A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) (hQ : Q ≠ 0) :
    positiveNormalizedRadical Q ∣ Q := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors Q
  let T := M.toFinset
  let S := positiveNormalizedFactors Q
  have hST : S.prod id ∣ T.prod id :=
    Finset.prod_dvd_prod_of_subset S T id (Finset.filter_subset _ _)
  have hTM : T.prod id ∣ M.prod := by
    simpa [T] using Multiset.toFinset_prod_dvd_prod M
  have hMQ : M.prod ∣ Q :=
    (UniqueFactorizationMonoid.prod_normalizedFactors hQ).dvd
  simpa [positiveNormalizedRadical, positiveNormalizedFactors, M, T, S] using
    hST.trans (hTM.trans hMQ)

/-- Its outer degree is no larger than the original polynomial's. -/
theorem positiveNormalizedRadical_natDegree_le
    {A : Type*} [CommRing A] [IsDomain A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) (hQ : Q ≠ 0) :
    (positiveNormalizedRadical Q).natDegree ≤ Q.natDegree :=
  Polynomial.natDegree_le_of_dvd (positiveNormalizedRadical_dvd Q hQ) hQ

/-- The product of distinct normalized factors is genuinely squarefree.
Normalization is what turns association of two irreducibles back into
literal equality, so `toFinset` removes exactly all repetitions. -/
theorem positiveNormalizedRadical_squarefree
    {A : Type*} [CommRing A] [IsDomain A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) :
    Squarefree (positiveNormalizedRadical Q) := by
  classical
  let S := positiveNormalizedFactors Q
  change Squarefree ((positiveNormalizedFactors Q).prod id)
  change Squarefree (S.prod id)
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro H hHS J hJS hHJ
    have hHS' : H ∈
        (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun L ↦ 0 < L.natDegree) := by
      simpa [S, positiveNormalizedFactors] using hHS
    have hJS' : J ∈
        (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun L ↦ 0 < L.natDegree) := by
      simpa [S, positiveNormalizedFactors] using hJS
    have hHmem : H ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hHS').1
    have hJmem : J ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hJS').1
    have hHirr : Irreducible H :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor H hHmem
    have hJirr : Irreducible J :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor J hJmem
    apply hHirr.isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have hassoc : Associated H J := hHirr.associated_of_dvd hJirr hdiv
    have heq : H = J := hassoc.eq_of_normalized
      (UniqueFactorizationMonoid.normalize_normalized_factor H hHmem)
      (UniqueFactorizationMonoid.normalize_normalized_factor J hJmem)
    exact hHJ heq
  · intro H hHS
    have hHS' : H ∈
        (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun L ↦ 0 < L.natDegree) := by
      simpa [S, positiveNormalizedFactors] using hHS
    have hHmem : H ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hHS').1
    exact
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor H hHmem).squarefree

/-- Positive-degree irreducible factors are primitive, and primitivity is
multiplicative.  Hence the positive normalized radical has no untracked
coefficient content. -/
theorem positiveNormalizedRadical_isPrimitive
    {A : Type*} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (Q : Polynomial A) :
    (positiveNormalizedRadical Q).IsPrimitive := by
  classical
  let S := positiveNormalizedFactors Q
  change ((positiveNormalizedFactors Q).prod id).IsPrimitive
  change (S.prod id).IsPrimitive
  have heach : ∀ H ∈ S, H.IsPrimitive := by
    intro H hHS
    have hfilter : H ∈
        (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
          (fun L ↦ 0 < L.natDegree) := by
      simpa [S, positiveNormalizedFactors] using hHS
    have hfilter' := Finset.mem_filter.mp hfilter
    have hHmem : H ∈ UniqueFactorizationMonoid.normalizedFactors Q :=
      Multiset.mem_toFinset.mp hfilter'.1
    have hHirr : Irreducible H :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor H hHmem
    exact hHirr.isPrimitive (Nat.ne_of_gt hfilter'.2)
  exact Finset.prod_induction id Polynomial.IsPrimitive
    (fun _ _ hP hR ↦ hP.mul hR) Polynomial.isPrimitive_one heach

/-- Sharp `Y+Z` cap inheritance by the whole distinct-factor radical, not
merely by one factor. -/
theorem positiveNormalizedRadical_YZ_cap
    {F : Type*} [Field F]
    [NormalizationMonoid (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (D : ℕ) (hQ : Q ≠ 0)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D) :
    ∀ j a,
      (((positiveNormalizedRadical Q).coeff j).coeff a) ≠ 0 →
        (((positiveNormalizedRadical Q).coeff j).coeff a).natDegree + j < D := by
  have hraw := YZFactorCap.coefficient_cap_of_dvd Q
    (positiveNormalizedRadical Q) 1 D hQ
      (positiveNormalizedRadical_dvd Q hQ) (by
        intro j hj
        obtain ⟨a, ha, hadeg, _⟩ :=
          Polynomial.Bivariate.exists_max_index_degreeX (Q.coeff j) hj
        have hca : (Q.coeff j).coeff a ≠ 0 :=
          Polynomial.mem_support_iff.mp ha
        simpa [hadeg] using hcap j a hca)
  simpa using hraw

/-- Consequently every fixed `X` fiber of the positive radical retains the
strict total `Y+Z` cap used by the two-product resultant ledger. -/
theorem positiveNormalizedRadical_triSpecializeX_totalDegree_lt
    {F : Type*} [Field F]
    [NormalizationMonoid (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x : F) (D : ℕ) (hD : 0 < D) (hQ : Q ≠ 0)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D) :
    Polynomial.Bivariate.totalDegree
      (triSpecializeX (positiveNormalizedRadical Q) x) < D := by
  exact totalDegree_triSpecializeX_lt
    (positiveNormalizedRadical Q) x D hD
      (positiveNormalizedRadical_YZ_cap Q D hQ hcap)

/-- Nonvanishing of the global radical obstruction.  The primitive and
squarefree hypotheses are exactly what the product-of-distinct-positive-
normalized-factors construction must provide; the characteristic bound
excludes inseparable factors over the fraction field. -/
theorem globalRadicalResultant_ne_zero_of_primitive_squarefree
    {A : Type} [CommRing A] [IsDomain A] [IsGCDMonoid A]
    [UniqueFactorizationMonoid (Polynomial A)]
    (char : ℕ) [CharP A char] (Rad : Polynomial A)
    (hprim : Rad.IsPrimitive) (hsquarefree : Squarefree Rad)
    (hpos : 0 < Rad.natDegree) (hchar : Rad.natDegree < char) :
    globalRadicalResultant Rad ≠ 0 := by
  simpa [globalRadicalResultant,
    BCHKSQuadraticKernel6400.parityKernelResultant] using
      BCHKSQuadraticKernel6400.rawSepResultant_ne_zero_of_primitive_squarefree
        char Rad hprim hsquarefree hpos hchar

/-- The canonical positive normalized radical automatically supplies every
algebraic hypothesis of the nonvanishing theorem. -/
theorem positiveNormalizedRadical_globalResultant_ne_zero
    {A : Type} [CommRing A] [IsDomain A] [NormalizedGCDMonoid A]
    [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)]
    (char : ℕ) [CharP A char] (Q : Polynomial A)
    (hQ : Q ≠ 0)
    (hpos : 0 < (positiveNormalizedRadical Q).natDegree)
    (hchar : Q.natDegree < char) :
    globalRadicalResultant (positiveNormalizedRadical Q) ≠ 0 := by
  apply globalRadicalResultant_ne_zero_of_primitive_squarefree
    char (positiveNormalizedRadical Q)
  · exact positiveNormalizedRadical_isPrimitive Q
  · exact positiveNormalizedRadical_squarefree Q
  · exact hpos
  · exact (positiveNormalizedRadical_natDegree_le Q hQ).trans_lt hchar

/-- The sharp two-product degree ledger for a fixed `X` fiber.  A strict
`Y+Z<D` cap gives `degreeZ B ≤ D-1` and, crucially,
`degreeZ B_Y ≤ D-2`; the padded resultant therefore has degree strictly
below `2*n*(D-1)`. -/
theorem fixed_radical_resultant_natDegree_lt_two_mul
    {F : Type} [Field F]
    (B : Polynomial (Polynomial F)) (n D : ℕ)
    (hn : 0 < n) (hD : 1 < D)
    (htotal : Polynomial.Bivariate.totalDegree B < D) :
    (Polynomial.resultant B B.derivative n (n - 1)).natDegree <
      2 * n * (D - 1) := by
  have hBX : Polynomial.Bivariate.degreeX B ≤ D - 1 := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro j hj
    have hc := Polynomial.Bivariate.coeff_totalDegree_le B hj
    omega
  have hDX : Polynomial.Bivariate.degreeX B.derivative ≤ D - 2 := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro j hj
    have hder0 : B.derivative.coeff j ≠ 0 :=
      Polynomial.mem_support_iff.mp hj
    have hcoeff0 : B.coeff (j + 1) ≠ 0 := by
      intro hzero
      apply hder0
      rw [Polynomial.coeff_derivative, hzero]
      simp
    have hmem : j + 1 ∈ B.support :=
      Polynomial.mem_support_iff.mpr hcoeff0
    have hc := Polynomial.Bivariate.coeff_totalDegree_le B hmem
    have hmul : (B.derivative.coeff j).natDegree ≤
        (B.coeff (j + 1)).natDegree := by
      rw [Polynomial.coeff_derivative]
      simpa [mul_comm] using
        (Polynomial.natDegree_C_mul_le (j + 1 : F) (B.coeff (j + 1)))
    omega
  have hbound := bivariate_resultant_natDegree_le
    B B.derivative n (n - 1)
  calc
    (Polynomial.resultant B B.derivative n (n - 1)).natDegree ≤
        (n - 1) * Polynomial.Bivariate.degreeX B +
          n * Polynomial.Bivariate.degreeX B.derivative := hbound
    _ ≤ (n - 1) * (D - 1) + n * (D - 2) := by gcongr
    _ ≤ (n - 1) * (D - 1) + n * (D - 1) := by gcongr <;> omega
    _ = ((n - 1) + n) * (D - 1) := by ring
    _ < (n + n) * (D - 1) := by
      apply Nat.mul_lt_mul_of_pos_right
      · omega
      · omega
    _ = 2 * n * (D - 1) := by ring

/-- Trivariate wrapper for the preceding exact ledger.  `htotal` is supplied
directly by the inherited strict `Y+Z<D` cap after fixing `X=x`; no
factorwise discriminant or pairwise-resultant sums remain. -/
theorem globalRadicalResultant_evalX_natDegree_lt_two_mul
    {F : Type} [Field F]
    (Rad : Polynomial (Polynomial (Polynomial F)))
    (x : F) (D : ℕ)
    (hpos : 0 < Rad.natDegree) (hD : 1 < D)
    (htotal : Polynomial.Bivariate.totalDegree (triSpecializeX Rad x) < D) :
    (Polynomial.eval (Polynomial.C x)
      (globalRadicalResultant Rad)).natDegree <
        2 * Rad.natDegree * (D - 1) := by
  let B : Polynomial (Polynomial F) := triSpecializeX Rad x
  have hder : triSpecializeX Rad.derivative x = B.derivative := by
    simp [B, triSpecializeX, Polynomial.derivative_map]
  have hfixed : Polynomial.eval (Polynomial.C x)
      (globalRadicalResultant Rad) =
      Polynomial.resultant B B.derivative Rad.natDegree
        (Rad.natDegree - 1) := by
    calc
      Polynomial.eval (Polynomial.C x) (globalRadicalResultant Rad) =
          Polynomial.resultant
            (Rad.map (Polynomial.evalRingHom (Polynomial.C x)))
            (Rad.derivative.map
              (Polynomial.evalRingHom (Polynomial.C x)))
            Rad.natDegree (Rad.natDegree - 1) := by
              change (Polynomial.evalRingHom (Polynomial.C x))
                (Polynomial.resultant Rad Rad.derivative Rad.natDegree
                  (Rad.natDegree - 1)) = _
              exact (Polynomial.resultant_map_map Rad Rad.derivative
                Rad.natDegree (Rad.natDegree - 1)
                (Polynomial.evalRingHom (Polynomial.C x))).symm
      _ = Polynomial.resultant B B.derivative Rad.natDegree
          (Rad.natDegree - 1) := by
            change Polynomial.resultant (triSpecializeX Rad x)
              (triSpecializeX Rad.derivative x) Rad.natDegree
                (Rad.natDegree - 1) = _
            rw [hder]
  rw [hfixed]
  exact fixed_radical_resultant_natDegree_lt_two_mul
    B Rad.natDegree D hpos hD (by simpa [B] using htotal)

/-- Canonical-radical wrapper for the sharp fixed-`X` two-product ledger. -/
theorem positiveNormalizedRadical_globalResultant_evalX_natDegree_lt
    {F : Type} [Field F]
    [NormalizationMonoid (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (x : F) (D : ℕ)
    (hD : 1 < D) (hQ : Q ≠ 0)
    (hpos : 0 < (positiveNormalizedRadical Q).natDegree)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      ((Q.coeff j).coeff a).natDegree + j < D) :
    (Polynomial.eval (Polynomial.C x)
      (globalRadicalResultant (positiveNormalizedRadical Q))).natDegree <
        2 * (positiveNormalizedRadical Q).natDegree * (D - 1) := by
  apply globalRadicalResultant_evalX_natDegree_lt_two_mul
    (positiveNormalizedRadical Q) x D hpos hD
  exact positiveNormalizedRadical_triSpecializeX_totalDegree_lt
    Q x D (by omega) hQ hcap

/-- Specializing the one global radical resultant in `Z` to a nonzero
polynomial in `X` certifies that every polynomial root `P(X)` of the
specialized radical is simple.  Degree drops and identically-zero specialized
factors are automatically exceptional because they force the padded
resultant to vanish. -/
theorem specialized_radical_derivative_not_isRoot_of_resultant_ne_zero
    {F : Type*} [Field F]
    (Rad : Polynomial (Polynomial (Polynomial F)))
    (z : F) (P : Polynomial F)
    (hpos : 0 < Rad.natDegree)
    (hres : (globalRadicalResultant Rad).map
      (Polynomial.evalRingHom z) ≠ 0)
    (hroot : (BCHKSSubstitutionVanish.specializeZ Rad z).IsRoot P) :
    ¬ (BCHKSSubstitutionVanish.specializeZ Rad z).derivative.IsRoot P := by
  let B : Polynomial (Polynomial F) :=
    BCHKSSubstitutionVanish.specializeZ Rad z
  have hBdeg : B.natDegree ≤ Rad.natDegree := by
    exact Polynomial.natDegree_map_le
  have hfixed : Polynomial.resultant B B.derivative Rad.natDegree
      (Rad.natDegree - 1) =
        (globalRadicalResultant Rad).map (Polynomial.evalRingHom z) := by
    dsimp [B, BCHKSSubstitutionVanish.specializeZ,
      globalRadicalResultant]
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
    rfl
  have hresB : Polynomial.resultant B B.derivative Rad.natDegree
      (Rad.natDegree - 1) ≠ 0 := by
    rw [hfixed]
    exact hres
  apply derivative_not_isRoot_of_fixed_resultant_ne_zero
    B P Rad.natDegree hBdeg (by omega) hresB
  simpa [B] using hroot

/-- End-to-end specialization interface.  The only algebraic hypotheses
left to the factorization layer are the exact specialized product identity
and a root-free prefactor.  One nonzero global radical resultant supplies
both uniqueness of the owner and simplicity of its specialized root, after
which higher derivative vanishing forces the owner's global exponent above
`J`. -/
theorem lt_exponent_of_global_radical_resultant_specialization
    {F ι : Type*} [Field F] [DecidableEq ι]
    (Rad : Polynomial (Polynomial (Polynomial F)))
    (z : F)
    (S : Finset ι) (f : ι → Polynomial (Polynomial F))
    (e : ι → ℕ)
    (u Q : Polynomial (Polynomial F)) (P : Polynomial F) (J : ℕ)
    (hRadpos : 0 < Rad.natDegree)
    (hRad : BCHKSSubstitutionVanish.specializeZ Rad z = S.prod f)
    (hres : (globalRadicalResultant Rad).map
      (Polynomial.evalRingHom z) ≠ 0)
    (hf : ∀ i ∈ S, f i ≠ 0)
    (hu : u ≠ 0) (hunroot : ¬ u.IsRoot P)
    (hQ : Q = u * S.prod (fun i ↦ f i ^ e i))
    (q : ι) (hqS : q ∈ S) (hqroot : (f q).IsRoot P)
    (hderivatives : ∀ r ≤ J,
      Polynomial.eval P (iterYDerivative r Q) = 0)
    (hfactorial : (J.factorial : Polynomial F) ∈
      nonZeroDivisors (Polynomial F)) :
    J < e q := by
  have hradroot :
      (BCHKSSubstitutionVanish.specializeZ Rad z).IsRoot P := by
    rw [hRad]
    exact (Polynomial.isRoot_prod S f P).2 ⟨q, hqS, hqroot⟩
  have hrawDerivative :=
    specialized_radical_derivative_not_isRoot_of_resultant_ne_zero
      Rad z P hRadpos hres hradroot
  have hradDerivative : ¬ (S.prod f).derivative.IsRoot P := by
    intro hder
    apply hrawDerivative
    simpa [hRad] using hder
  exact
    lt_exponent_of_iterYDerivative_eval_zero_of_radical_derivative_not_isRoot
      S f e u Q P J hf hu hunroot hQ q hqS hqroot hradDerivative
      hderivatives hfactorial

/-- Fully normalized-factor specialization bridge.  The factor list,
exponents, radical identity, and root-free prefactor are constructed
internally.  The sole content exception is explicit: the product of the
outer-degree-zero normalized factors must not vanish after specialization.
-/
theorem lt_normalizedFactorExponent_of_globalRadicalResultant_specialization
    {F : Type*} [Field F]
    [NormalizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    [UniqueFactorizationMonoid
      (Polynomial (Polynomial (Polynomial F)))]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (z : F) (P : Polynomial F) (J : ℕ)
    (hRadpos : 0 < (positiveNormalizedRadical Q).natDegree)
    (hres : (globalRadicalResultant (positiveNormalizedRadical Q)).map
      (Polynomial.evalRingHom z) ≠ 0)
    (hcontent : BCHKSSubstitutionVanish.specializeZ
      (zeroDegreeNormalizedPart Q) z ≠ 0)
    (q : Polynomial (Polynomial (Polynomial F)))
    (hqS : q ∈ positiveNormalizedFactors Q)
    (hqroot : (BCHKSSubstitutionVanish.specializeZ q z).IsRoot P)
    (hderivatives : ∀ r ≤ J,
      Polynomial.eval P (iterYDerivative r
        (BCHKSSubstitutionVanish.specializeZ Q z)) = 0)
    (hfactorial : (J.factorial : Polynomial F) ∈
      nonZeroDivisors (Polynomial F)) :
    J < normalizedFactorExponent Q q := by
  classical
  let Rad := positiveNormalizedRadical Q
  let S := positiveNormalizedFactors Q
  let f : Polynomial (Polynomial (Polynomial F)) →
      Polynomial (Polynomial F) := fun H ↦
    BCHKSSubstitutionVanish.specializeZ H z
  let e : Polynomial (Polynomial (Polynomial F)) → ℕ := fun H ↦
    normalizedFactorExponent Q H
  let Qz := BCHKSSubstitutionVanish.specializeZ Q z
  let Φ : Polynomial (Polynomial (Polynomial F)) →+*
      Polynomial (Polynomial F) :=
    Polynomial.mapRingHom
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  obtain ⟨v, hfactor, houterZero⟩ :=
    exists_unit_mul_zeroPart_mul_positiveFactors Q hQ
  let Outer : Polynomial (Polynomial (Polynomial F)) :=
    (v : Polynomial (Polynomial (Polynomial F))) * zeroDegreeNormalizedPart Q
  let u : Polynomial (Polynomial F) :=
    BCHKSSubstitutionVanish.specializeZ Outer z
  have hRad : BCHKSSubstitutionVanish.specializeZ Rad z = S.prod f := by
    change Φ (S.prod id) = S.prod f
    rw [map_prod Φ id S]
    rfl
  have hRadZ : BCHKSSubstitutionVanish.specializeZ Rad z ≠ 0 := by
    intro hzero
    have hroot :
        (BCHKSSubstitutionVanish.specializeZ Rad z).IsRoot P := by
      simp [hzero]
    have hnot :=
      specialized_radical_derivative_not_isRoot_of_resultant_ne_zero
        Rad z P hRadpos hres hroot
    apply hnot
    simp [hzero]
  have hf : ∀ H ∈ S, f H ≠ 0 := by
    have hprod : S.prod f ≠ 0 := by simpa [hRad] using hRadZ
    exact Finset.prod_ne_zero_iff.mp hprod
  have hu : u ≠ 0 := by
    change Φ ((v : Polynomial (Polynomial (Polynomial F))) *
      zeroDegreeNormalizedPart Q) ≠ 0
    rw [map_mul]
    apply mul_ne_zero
    · exact (v.isUnit.map Φ).ne_zero
    · simpa [Φ, BCHKSSubstitutionVanish.specializeZ] using hcontent
  have huDegree : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Polynomial.natDegree_map_le.trans (by simpa [Outer] using houterZero.le)
  have hunroot : ¬ u.IsRoot P := by
    have huC : u = Polynomial.C (u.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero huDegree
    rw [huC]
    apply Polynomial.not_isRoot_C
    intro hcoeff
    apply hu
    rw [huC, hcoeff, Polynomial.C_0]
  have hQz : Qz = u * S.prod (fun H ↦ f H ^ e H) := by
    change Φ Q = Φ Outer * S.prod (fun H ↦ f H ^ e H)
    calc
      Φ Q = Φ (Outer * S.prod
          (fun H ↦ H ^ normalizedFactorExponent Q H)) := by
        exact congrArg Φ (by simpa [Outer, S] using hfactor)
      _ = Φ Outer * Φ (S.prod
          (fun H ↦ H ^ normalizedFactorExponent Q H)) := by
        rw [map_mul]
      _ = Φ Outer * S.prod
          (fun H ↦ Φ (H ^ normalizedFactorExponent Q H)) := by
        rw [map_prod Φ
          (fun H ↦ H ^ normalizedFactorExponent Q H) S]
      _ = Φ Outer * S.prod (fun H ↦ f H ^ e H) := by
        congr 1
        apply Finset.prod_congr rfl
        intro H hHS
        simp [f, e, Φ, BCHKSSubstitutionVanish.specializeZ]
  exact lt_exponent_of_global_radical_resultant_specialization
    Rad z S f e u Qz P J hRadpos hRad hres hf hu hunroot hQz
      q hqS hqroot hderivatives hfactorial

end BCHKSRadicalMultiplicityBridge6400
end ProximityPrize.SubmissionLower
