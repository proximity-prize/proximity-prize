import ProximityPrize.SubmissionLower.BCHKSLocatorContainerAlignment6400

/-!
# Low-degree determinants in spaces of polynomial pairs

This module develops the linear-algebra core of the large-nullity locator
branch.  The first result is a finite-dimensional uncertainty principle: a
large subspace of polynomials known to have degree below `D` contains a
nonzero polynomial of degree below `l` as soon as its dimension exceeds the
number `D-l` of high coefficients.

The later statements apply this to determinants of two degree-capped
polynomial pairs.  They isolate the one remaining primitive-direction lemma
from the dimension argument itself.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F : Type} [Field F]

/-- The block of `t` coefficients beginning at degree `l`. -/
def polynomialHighCoeffMap (l t : ℕ) : F[X] →ₗ[F] (Fin t → F) where
  toFun P j := P.coeff (l + j)
  map_add' P Q := by
    funext j
    simp
  map_smul' a P := by
    funext j
    simp

/-- A subspace of dimension greater than the number of coefficient positions
from `l` through `D-1` contains a nonzero element of degree below `l`.

This is the exact linear-algebra step needed after bounding the determinant
image.  It is stated for an arbitrary polynomial subspace so the locator
argument does not depend on a choice of basis or row-reduction convention.
-/
theorem exists_nonzero_low_degree_of_finrank_gt_codim
    (W : Submodule F F[X]) (D l : ℕ) (hlD : l ≤ D)
    (hbounded : W ≤ Polynomial.degreeLT F D)
    (hrank : D - l < Module.finrank F W) :
    ∃ P ∈ W, P ≠ 0 ∧ P.natDegree < l := by
  let inclusion : W →ₗ[F] Polynomial.degreeLT F D :=
    { toFun := fun P => ⟨P.1, hbounded P.2⟩
      map_add' := by intro P Q; ext; rfl
      map_smul' := by intro a P; ext; rfl }
  have hinclusion : Function.Injective inclusion := by
    intro P Q hPQ
    apply Subtype.ext
    exact congrArg (fun R : Polynomial.degreeLT F D => (R.1 : F[X])) hPQ
  letI : FiniteDimensional F W :=
    FiniteDimensional.of_injective inclusion hinclusion
  let high : W →ₗ[F] (Fin (D - l) → F) :=
    (polynomialHighCoeffMap l (D - l)).comp W.subtype
  have hker : LinearMap.ker high ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective high := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at hle
    exact (Nat.not_lt_of_ge hle) hrank
  obtain ⟨Q, hQker, hQne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hQpoly : Q.1 ≠ 0 := by
    intro hzero
    exact hQne (Subtype.ext hzero)
  have hQdegree : Q.1.degree < (D : WithBot ℕ) :=
    Polynomial.mem_degreeLT.mp (hbounded Q.2)
  have hcoeff : ∀ j : ℕ, l ≤ j → Q.1.coeff j = 0 := by
    intro j hlj
    by_cases hjD : j < D
    · let s : Fin (D - l) := ⟨j - l, by omega⟩
      have hzero : high Q = 0 := hQker
      have hs := congrFun hzero s
      change Q.1.coeff (l + (j - l)) = 0 at hs
      simpa [Nat.add_sub_of_le hlj] using hs
    · have hDj : D ≤ j := Nat.le_of_not_gt hjD
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (hQdegree.trans_le (WithBot.coe_le_coe.mpr hDj))
  refine ⟨Q.1, Q.2, hQpoly, ?_⟩
  rw [Polynomial.natDegree_lt_iff_degree_lt hQpoly,
    Polynomial.degree_lt_iff_coeff_zero]
  exact hcoeff

/-- Subtype-valued version of the high-coefficient lemma.  Keeping the
codomain finite-dimensional avoids asking rank--nullity to elaborate the
whole infinite polynomial module. -/
theorem exists_nonzero_low_degree_in_degreeLT_subspace
    (D l : ℕ) (W : Submodule F (Polynomial.degreeLT F D))
    (hlD : l ≤ D) (hrank : D - l < Module.finrank F W) :
    ∃ P : Polynomial.degreeLT F D,
      P ∈ W ∧ P.1 ≠ 0 ∧ P.1.natDegree < l := by
  let coords : W →ₗ[F] (Fin D → F) :=
    (Polynomial.degreeLTEquiv F D).toLinearMap.comp W.subtype
  have hcoords : Function.Injective coords := by
    intro P Q hPQ
    apply Subtype.ext
    apply (Polynomial.degreeLTEquiv F D).injective
    change (Polynomial.degreeLTEquiv F D) P.1 =
      (Polynomial.degreeLTEquiv F D) Q.1
    exact hPQ
  letI : FiniteDimensional F W :=
    FiniteDimensional.of_injective coords hcoords
  let high : W →ₗ[F] (Fin (D - l) → F) :=
    (polynomialHighCoeffMap l (D - l)).comp
      ((Polynomial.degreeLT F D).subtype.comp W.subtype)
  have hker : LinearMap.ker high ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective high := by
      intro P Q hPQ
      have hsub : P - Q ∈ LinearMap.ker high := by
        rw [LinearMap.mem_ker]
        calc
          high (P - Q) = high P - high Q := high.map_sub P Q
          _ = 0 := by rw [hPQ, sub_self]
      have hzero : P - Q = 0 := by
        have : P - Q ∈ (⊥ : Submodule F W) := by
          rw [← hbot]
          exact hsub
        simpa using this
      exact sub_eq_zero.mp hzero
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at hle
    exact (Nat.not_lt_of_ge hle) hrank
  obtain ⟨Q, hQker, hQne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hQpoly : Q.1.1 ≠ 0 := by
    intro hzero
    apply hQne
    apply Subtype.ext
    exact Subtype.ext hzero
  have hQdegree : Q.1.1.degree < (D : WithBot ℕ) :=
    Polynomial.mem_degreeLT.mp Q.1.2
  have hcoeff : ∀ j : ℕ, l ≤ j → Q.1.1.coeff j = 0 := by
    intro j hlj
    by_cases hjD : j < D
    · let s : Fin (D - l) := ⟨j - l, by omega⟩
      have hzero : high Q = 0 := hQker
      have hs := congrFun hzero s
      change Q.1.1.coeff (l + (j - l)) = 0 at hs
      simpa [Nat.add_sub_of_le hlj] using hs
    · have hDj : D ≤ j := Nat.le_of_not_gt hjD
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (hQdegree.trans_le (WithBot.coe_le_coe.mpr hDj))
  refine ⟨Q.1, Q.2, hQpoly, ?_⟩
  rw [Polynomial.natDegree_lt_iff_degree_lt hQpoly,
    Polynomial.degree_lt_iff_coeff_zero]
  exact hcoeff

/-- In a `q`-dimensional multiplier space whose degrees are at most `t`, one
can choose a nonzero multiplier of degree at most `t-q+1`.  This is the exact
degree rebate contributed by a large rational rank-one slice. -/
theorem exists_nonzero_multiplier_with_dimension_rebate
    (S : Submodule F F[X]) (t q : ℕ) (hq : 0 < q) (hqt : q ≤ t + 1)
    (hbounded : S ≤ Polynomial.degreeLT F (t + 1))
    (hfinrank : Module.finrank F S = q) :
    ∃ s ∈ S, s ≠ 0 ∧ s.natDegree ≤ t + 1 - q := by
  have hlD : t + 2 - q ≤ t + 1 := by omega
  have hcodim :
      (t + 1) - (t + 2 - q) < Module.finrank F S := by
    rw [hfinrank]
    omega
  obtain ⟨s, hsS, hsne, hsdegree⟩ :=
    exists_nonzero_low_degree_of_finrank_gt_codim S
      (t + 1) (t + 2 - q) hlD hbounded hcodim
  exact ⟨s, hsS, hsne, by omega⟩

/-- Multiplying a primitive polynomial direction by the rebated multiplier
reduces both component degrees by `q-1`. -/
theorem exists_reduced_primitive_multiple
    (S : Submodule F F[X]) (a b : F[X]) (c h t q : ℕ)
    (hq : 0 < q) (hqt : q ≤ t + 1)
    (haRoom : a.natDegree + t < c)
    (hbRoom : b.natDegree + t < h)
    (hbounded : S ≤ Polynomial.degreeLT F (t + 1))
    (hfinrank : Module.finrank F S = q) :
    ∃ s ∈ S, s ≠ 0 ∧
      (s * a).natDegree ≤ c - q ∧ (s * b).natDegree ≤ h - q := by
  obtain ⟨s, hsS, hsne, hsdegree⟩ :=
    exists_nonzero_multiplier_with_dimension_rebate
      S t q hq hqt hbounded hfinrank
  refine ⟨s, hsS, hsne, ?_, ?_⟩
  · calc
      (s * a).natDegree ≤ s.natDegree + a.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (t + 1 - q) + a.natDegree := Nat.add_le_add_right hsdegree _
      _ ≤ c - q := by omega
  · calc
      (s * b).natDegree ≤ s.natDegree + b.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (t + 1 - q) + b.natDegree := Nat.add_le_add_right hsdegree _
      _ ≤ h - q := by omega

/-- A zero determinant against a coprime nonzero primitive pair is exactly a
polynomial multiple of that pair.  This converts the rational rank-one slice
of the pair space into an ordinary polynomial multiplier space. -/
theorem exists_polynomial_multiplier_of_coprime_cross
    (a b A B : F[X]) (ha : a ≠ 0) (hcoprime : IsCoprime a b)
    (hcross : a * B = b * A) :
    ∃ s : F[X], A = s * a ∧ B = s * b := by
  have hadiv : a ∣ b * A := by
    refine ⟨B, ?_⟩
    simpa [mul_comm] using hcross.symm
  have haA : a ∣ A := hcoprime.dvd_of_dvd_mul_left hadiv
  let s : F[X] := A / a
  have hA : a * s = A :=
    EuclideanDomain.mul_div_cancel' ha haA
  have hB : B = s * b := by
    have hz : a * (B - s * b) = 0 := by
      calc
        a * (B - s * b) = a * B - b * (a * s) := by ring
        _ = b * A - b * A := by rw [hcross, hA]
        _ = 0 := sub_self _
    have := (mul_eq_zero.mp hz).resolve_left ha
    exact sub_eq_zero.mp this
  exact ⟨s, by simpa [mul_comm] using hA.symm, hB⟩

/-- The ambient space of a degree-`<c` first multiplier and a degree-`<h`
second multiplier. -/
abbrev PolynomialPairSpace (F : Type) [Field F] (c h : ℕ) :=
  (Polynomial.degreeLT F c) × (Polynomial.degreeLT F h)

/-- Alternating determinant of two polynomial pairs. -/
noncomputable def polynomialPairDet {c h : ℕ}
    (u v : PolynomialPairSpace F c h) : F[X] :=
  u.1.1 * v.2.1 - u.2.1 * v.1.1

/-- For fixed `u`, determinant against `u` is linear in the second pair. -/
noncomputable def polynomialPairDetLinear {c h : ℕ}
    (u : PolynomialPairSpace F c h) :
    PolynomialPairSpace F c h →ₗ[F] F[X] where
  toFun v := polynomialPairDet u v
  map_add' v w := by
    simp only [polynomialPairDet, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add]
    ring
  map_smul' a v := by
    simp only [polynomialPairDet, Prod.smul_fst, Prod.smul_snd,
      Submodule.coe_smul_of_tower, smul_eq_C_mul, RingHom.id_apply]
    ring

@[simp]
theorem polynomialPairDetLinear_apply {c h : ℕ}
    (u v : PolynomialPairSpace F c h) :
    polynomialPairDetLinear u v = polynomialPairDet u v := rfl

private theorem natDegree_lt_of_pair_component
    (n : ℕ) (hn : 0 < n) (P : Polynomial.degreeLT F n) :
    P.1.natDegree < n := by
  by_cases hP : P.1 = 0
  · simpa [hP] using hn
  · rw [Polynomial.natDegree_lt_iff_degree_lt hP]
    exact Polynomial.mem_degreeLT.mp P.2

/-- Componentwise degree bounds give the expected convolution bound on the
alternating determinant. -/
theorem polynomialPairDet_natDegree_le
    {c h a b : ℕ} (hc : 0 < c) (hh : 0 < h)
    (u v : PolynomialPairSpace F c h)
    (hu₀ : u.1.1.natDegree ≤ a) (hu₁ : u.2.1.natDegree ≤ b) :
    (polynomialPairDet u v).natDegree ≤
      max (a + (h - 1)) (b + (c - 1)) := by
  have hv₀ : v.1.1.natDegree < c :=
    natDegree_lt_of_pair_component c hc v.1
  have hv₁ : v.2.1.natDegree < h :=
    natDegree_lt_of_pair_component h hh v.2
  calc
    (polynomialPairDet u v).natDegree
        ≤ max (u.1.1 * v.2.1).natDegree
            (u.2.1 * v.1.1).natDegree := by
          exact Polynomial.natDegree_sub_le _ _
    _ ≤ max (u.1.1.natDegree + v.2.1.natDegree)
          (u.2.1.natDegree + v.1.1.natDegree) := by
          gcongr
          · exact Polynomial.natDegree_mul_le
          · exact Polynomial.natDegree_mul_le
    _ ≤ max (a + (h - 1)) (b + (c - 1)) := by
          gcongr <;> omega

/-- Once a pivot pair has degree reduced in proportion to the dimension of
its determinant kernel, rank--nullity forces a second pair with a nonzero
determinant of degree at most `c+h-L`.

The outstanding primitive-direction argument will manufacture exactly the
two component bounds on `u`.  Everything after those bounds is now checked
linear algebra.
-/
theorem exists_low_degree_pairDet_of_reduced_pivot
    (c h L q : ℕ) (hc : 0 < c) (hh : 0 < h)
    (V : Submodule F (PolynomialPairSpace F c h))
    (u : V)
    (hqL : q < L) (hLd : L ≤ c + h)
    (hqc : q ≤ c) (hqh : q ≤ h)
    (hu₀ : u.1.1.1.natDegree ≤ c - q)
    (hu₁ : u.1.2.1.natDegree ≤ h - q)
    (himageRank : Module.finrank F
      (LinearMap.range
        ((polynomialPairDetLinear u.1).comp V.subtype)) = L - q) :
    ∃ v ∈ V, polynomialPairDet u.1 v ≠ 0 ∧
      (polynomialPairDet u.1 v).natDegree ≤ c + h - L := by
  let detMap : V →ₗ[F] F[X] :=
    (polynomialPairDetLinear u.1).comp V.subtype
  let W : Submodule F F[X] := LinearMap.range detMap
  have hWrank : Module.finrank F W = L - q := by
    simpa only [W, detMap] using himageRank
  have hWbounded : W ≤ Polynomial.degreeLT F (c + h - q) := by
    intro P hP
    rcases hP with ⟨v, rfl⟩
    apply Polynomial.mem_degreeLT.mpr
    have hdet := polynomialPairDet_natDegree_le hc hh u.1 v.1 hu₀ hu₁
    have hdetStrict : (polynomialPairDet u.1 v.1).natDegree < c + h - q := by
      omega
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hdetStrict)
  have hlD : c + h - L + 1 ≤ c + h - q := by omega
  have hcodim :
      (c + h - q) - (c + h - L + 1) < Module.finrank F W := by
    rw [hWrank]
    omega
  obtain ⟨Δ, hΔW, hΔne, hΔdegree⟩ :=
    exists_nonzero_low_degree_of_finrank_gt_codim W
      (c + h - q) (c + h - L + 1) hlD hWbounded hcodim
  rcases hΔW with ⟨v, hv⟩
  have heq : polynomialPairDet u.1 v.1 = Δ := by
    simpa [detMap] using hv
  refine ⟨v.1, v.2, ?_, ?_⟩
  · rw [heq]
    exact hΔne
  · rw [heq]
    omega

/-- Determinant against a reduced pivot, valued directly in its sharp finite
degree cap. -/
noncomputable def reducedPolynomialPairDetLinear
    (c h q : ℕ) (hc : 0 < c) (hh : 0 < h)
    (hqc : q ≤ c) (hqh : q ≤ h)
    (u : PolynomialPairSpace F c h)
    (hu₀ : u.1.1.natDegree ≤ c - q)
    (hu₁ : u.2.1.natDegree ≤ h - q) :
    PolynomialPairSpace F c h →ₗ[F]
      Polynomial.degreeLT F (c + h - q) :=
  let full := polynomialPairDetLinear u
  { toFun := fun v => ⟨full v,
      Polynomial.mem_degreeLT.mpr (by
        have hdet := polynomialPairDet_natDegree_le hc hh u v hu₀ hu₁
        have hnat : (polynomialPairDet u v).natDegree < c + h - q := by
          omega
        have hnat' : (full v).natDegree < c + h - q := by
          simpa only [full, polynomialPairDetLinear_apply] using hnat
        exact Polynomial.degree_le_natDegree.trans_lt
          (by exact_mod_cast hnat'))⟩
    map_add' := by
      intro v w
      apply Subtype.ext
      exact full.map_add v w
    map_smul' := by
      intro a v
      apply Subtype.ext
      exact full.map_smul a v }

@[simp]
theorem reducedPolynomialPairDetLinear_apply
    (c h q : ℕ) (hc : 0 < c) (hh : 0 < h)
    (hqc : q ≤ c) (hqh : q ≤ h)
    (u v : PolynomialPairSpace F c h)
    (hu₀ : u.1.1.natDegree ≤ c - q)
    (hu₁ : u.2.1.natDegree ≤ h - q) :
    (reducedPolynomialPairDetLinear c h q hc hh hqc hqh u hu₀ hu₁ v).1 =
      polynomialPairDet u v := rfl

end ProximityPrize.SubmissionLower
