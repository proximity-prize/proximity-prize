import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantSpan6400

/-!
# Sharp low determinant in a rank-two polynomial-pair space

This module closes the primitive-direction step in the locator rank-two
branch.  A coprime primitive direction identifies its determinant kernel
with a polynomial multiplier space.  The dimension of that slice then
rebates both component degrees of a pivot, and rank--nullity produces a
nonzero determinant with degree at most the ambient dimension minus the
dimension of the retained pair space.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {F : Type} [Field F]

@[simp]
theorem polynomialPairDet_self {c h : ℕ}
    (u : PolynomialPairSpace F c h) : polynomialPairDet u u = 0 := by
  simp only [polynomialPairDet]
  ring

theorem polynomialPairDet_swap {c h : ℕ}
    (u v : PolynomialPairSpace F c h) :
    polynomialPairDet v u = -polynomialPairDet u v := by
  simp only [polynomialPairDet]
  ring

/-- A rank-two witness contains a pivot with both components nonzero. -/
theorem exists_bicomponent_pivot_of_pairDet_ne_zero
    {c h : ℕ} (V : Submodule F (PolynomialPairSpace F c h))
    (u v : V) (hdet : polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ w z : V, w.1.1.1 ≠ 0 ∧ w.1.2.1 ≠ 0 ∧
      polynomialPairDet w.1 z.1 ≠ 0 := by
  by_cases huA : u.1.1.1 ≠ 0
  · by_cases huB : u.1.2.1 ≠ 0
    · exact ⟨u, v, huA, huB, hdet⟩
    · have huB0 : u.1.2.1 = 0 := not_ne_iff.mp huB
      have hvB : v.1.2.1 ≠ 0 := by
        intro hvB0
        apply hdet
        simp [polynomialPairDet, huB0, hvB0]
      by_cases hvA : v.1.1.1 ≠ 0
      · refine ⟨v, u, hvA, hvB, ?_⟩
        rw [polynomialPairDet_swap]
        exact neg_ne_zero.mpr hdet
      · have hvA0 : v.1.1.1 = 0 := not_ne_iff.mp hvA
        let w : V := u + v
        refine ⟨w, v, ?_, ?_, ?_⟩
        · simpa [w, hvA0] using huA
        · simpa [w, huB0] using hvB
        · rw [show w.1 = u.1 + v.1 by rfl,
            polynomialPairDet_add_left, polynomialPairDet_self, add_zero]
          exact hdet
  · have huA0 : u.1.1.1 = 0 := not_ne_iff.mp huA
    have huB : u.1.2.1 ≠ 0 := by
      intro huB0
      apply hdet
      simp [polynomialPairDet, huA0, huB0]
    have hvA : v.1.1.1 ≠ 0 := by
      intro hvA0
      apply hdet
      simp [polynomialPairDet, huA0, hvA0]
    by_cases hvB : v.1.2.1 ≠ 0
    · refine ⟨v, u, hvA, hvB, ?_⟩
      rw [polynomialPairDet_swap]
      exact neg_ne_zero.mpr hdet
    · have hvB0 : v.1.2.1 = 0 := not_ne_iff.mp hvB
      let w : V := u + v
      refine ⟨w, u, ?_, ?_, ?_⟩
      · simpa [w, huA0] using hvA
      · simpa [w, hvB0] using huB
      · have hneg : polynomialPairDet v.1 u.1 ≠ 0 := by
          rw [polynomialPairDet_swap]
          exact neg_ne_zero.mpr hdet
        rw [show w.1 = u.1 + v.1 by rfl,
          polynomialPairDet_add_left, polynomialPairDet_self, zero_add]
        exact hneg

/-- Divide a nonzero polynomial pair by its gcd to expose a coprime
primitive direction. -/
theorem exists_coprime_primitive_factor
    (A B : F[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ d a b : F[X], d ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
      IsCoprime a b ∧ A = d * a ∧ B = d * b := by
  classical
  let d := gcd A B
  let a := A / d
  let b := B / d
  have hd : d ≠ 0 := gcd_ne_zero_of_left hA
  have ha : a ≠ 0 := left_div_gcd_ne_zero hA
  have hb : b ≠ 0 := right_div_gcd_ne_zero hB
  have hcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hd
  have hAd : d * a = A :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_left A B)
  have hBd : d * b = B :=
    EuclideanDomain.mul_div_cancel' hd (GCDMonoid.gcd_dvd_right A B)
  exact ⟨d, a, b, hd, ha, hb, hcop, hAd.symm, hBd.symm⟩

/-- The determinant kernel of a coprime primitive direction is linearly
isomorphic to a polynomial multiplier space. -/
theorem exists_injective_primitiveMultiplierMap
    {c h : ℕ} (V : Submodule F (PolynomialPairSpace F c h))
    (p : PolynomialPairSpace F c h)
    (hpA : p.1.1 ≠ 0) (hcop : IsCoprime p.1.1 p.2.1) :
    ∃ mult :
        LinearMap.ker ((polynomialPairDetLinear p).comp V.subtype) →ₗ[F] F[X],
      Function.Injective mult ∧
      ∀ x, x.1.1.1.1 = mult x * p.1.1 ∧
        x.1.1.2.1 = mult x * p.2.1 := by
  classical
  obtain ⟨r, t, hbezout⟩ := hcop
  have hcop' : IsCoprime p.1.1 p.2.1 := ⟨r, t, hbezout⟩
  let Q := LinearMap.ker ((polynomialPairDetLinear p).comp V.subtype)
  let mult : Q →ₗ[F] F[X] :=
    { toFun := fun x => r * x.1.1.1.1 + t * x.1.1.2.1
      map_add' := by
        intro x y
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := by
        intro a x
        simp only [Submodule.coe_smul_of_tower, Prod.smul_fst,
          Prod.smul_snd, smul_eq_C_mul, RingHom.id_apply]
        ring }
  have hrepresentation : ∀ x : Q,
      x.1.1.1.1 = mult x * p.1.1 ∧
        x.1.1.2.1 = mult x * p.2.1 := by
    intro x
    have hkernel : polynomialPairDet p x.1.1 = 0 := by
      have hx := x.2
      change ((polynomialPairDetLinear p).comp V.subtype) x.1 = 0 at hx
      exact hx
    have hcross : p.1.1 * x.1.1.2.1 = p.2.1 * x.1.1.1.1 := by
      exact sub_eq_zero.mp (by simpa [polynomialPairDet] using hkernel)
    obtain ⟨s, hsA, hsB⟩ :=
      exists_polynomial_multiplier_of_coprime_cross
        p.1.1 p.2.1 x.1.1.1.1 x.1.1.2.1 hpA hcop' hcross
    have hmult : mult x = s := by
      calc
        mult x = r * (s * p.1.1) + t * (s * p.2.1) := by
          change r * x.1.1.1.1 + t * x.1.1.2.1 = _
          rw [hsA, hsB]
        _ = s * (r * p.1.1 + t * p.2.1) := by ring
        _ = s := by rw [hbezout, mul_one]
    exact ⟨by rw [hsA, hmult], by rw [hsB, hmult]⟩
  have hinjective : Function.Injective mult := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rw [(hrepresentation x).1, (hrepresentation y).1, hxy]
    · apply Subtype.ext
      rw [(hrepresentation x).2, (hrepresentation y).2, hxy]
  exact ⟨mult, hinjective, hrepresentation⟩

/-- A `q`-dimensional primitive-direction slice contains a nonzero pivot
whose two component degrees are rebated by `q`. -/
theorem exists_reduced_pivot_in_primitive_kernel
    {c h q : ℕ} (V : Submodule F (PolynomialPairSpace F c h))
    (p : PolynomialPairSpace F c h)
    (hpA : p.1.1 ≠ 0) (hpB : p.2.1 ≠ 0)
    (hcop : IsCoprime p.1.1 p.2.1)
    (hqrank : Module.finrank F
      (LinearMap.ker ((polynomialPairDetLinear p).comp V.subtype)) = q)
    (hqpos : 0 < q) :
    q ≤ c ∧ q ≤ h ∧
      ∃ u : V, u ≠ 0 ∧ polynomialPairDet p u.1 = 0 ∧
        u.1.1.1.natDegree ≤ c - q ∧
        u.1.2.1.natDegree ≤ h - q := by
  classical
  let Q := LinearMap.ker ((polynomialPairDetLinear p).comp V.subtype)
  obtain ⟨mult, hmultInj, hmultRep⟩ :=
    exists_injective_primitiveMultiplierMap V p hpA hcop
  let S : Submodule F F[X] := LinearMap.range mult
  have hSrank : Module.finrank F S = q := by
    calc
      Module.finrank F S = Module.finrank F Q := by
        simpa [S] using LinearMap.finrank_range_of_inj hmultInj
      _ = q := by simpa [Q] using hqrank
  have hpAdegree : p.1.1.natDegree < c := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hpA]
    exact Polynomial.mem_degreeLT.mp p.1.2
  have hpBdegree : p.2.1.natDegree < h := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hpB]
    exact Polynomial.mem_degreeLT.mp p.2.2
  let t := min (c - 1 - p.1.1.natDegree) (h - 1 - p.2.1.natDegree)
  have htA : t ≤ c - 1 - p.1.1.natDegree := min_le_left _ _
  have htB : t ≤ h - 1 - p.2.1.natDegree := min_le_right _ _
  have haRoom : p.1.1.natDegree + t < c := by omega
  have hbRoom : p.2.1.natDegree + t < h := by omega
  have hSbounded : S ≤ Polynomial.degreeLT F (t + 1) := by
    intro s hs
    rcases hs with ⟨x, rfl⟩
    by_cases hs0 : mult x = 0
    · simp [hs0]
    · have hprodA : (mult x * p.1.1).natDegree < c := by
        rw [← (hmultRep x).1]
        rw [Polynomial.natDegree_lt_iff_degree_lt
          (by simpa [(hmultRep x).1] using mul_ne_zero hs0 hpA)]
        exact Polynomial.mem_degreeLT.mp x.1.1.1.2
      have hprodB : (mult x * p.2.1).natDegree < h := by
        rw [← (hmultRep x).2]
        rw [Polynomial.natDegree_lt_iff_degree_lt
          (by simpa [(hmultRep x).2] using mul_ne_zero hs0 hpB)]
        exact Polynomial.mem_degreeLT.mp x.1.1.2.2
      have hsA : (mult x).natDegree + p.1.1.natDegree < c := by
        rw [← Polynomial.natDegree_mul hs0 hpA]
        exact hprodA
      have hsB : (mult x).natDegree + p.2.1.natDegree < h := by
        rw [← Polynomial.natDegree_mul hs0 hpB]
        exact hprodB
      apply Polynomial.mem_degreeLT.mpr
      rw [← Polynomial.natDegree_lt_iff_degree_lt hs0]
      dsimp only [t]
      omega
  have hqt : q ≤ t + 1 := by
    rw [← hSrank]
    have hmono := Submodule.finrank_mono hSbounded
    calc
      Module.finrank F S ≤
          Module.finrank F (Polynomial.degreeLT F (t + 1)) := hmono
      _ = t + 1 := by
        rw [(Polynomial.degreeLTEquiv F (t + 1)).finrank_eq,
          Module.finrank_fin_fun]
  have hqc : q ≤ c := by omega
  have hqh : q ≤ h := by omega
  obtain ⟨s, hsS, hsne, hsAdegree, hsBdegree⟩ :=
    exists_reduced_primitive_multiple S p.1.1 p.2.1 c h t q
      hqpos hqt haRoom hbRoom hSbounded hSrank
  rcases hsS with ⟨x, hx⟩
  have hmultx : mult x = s := hx
  let u : V := x.1
  have huA : u.1.1.1 = s * p.1.1 := by
    simpa [u, hmultx] using (hmultRep x).1
  have huB : u.1.2.1 = s * p.2.1 := by
    simpa [u, hmultx] using (hmultRep x).2
  have hune : u ≠ 0 := by
    intro hu0
    have hA0 : u.1.1.1 = 0 := by rw [hu0]; rfl
    rw [huA] at hA0
    exact hsne ((mul_eq_zero.mp hA0).resolve_right hpA)
  have huker : polynomialPairDet p u.1 = 0 := by
    have hxker := x.2
    change ((polynomialPairDetLinear p).comp V.subtype) x.1 = 0 at hxker
    exact hxker
  exact ⟨hqc, hqh, u, hune, huker,
    by simpa [huA] using hsAdegree,
    by simpa [huB] using hsBdegree⟩

/-- Any finite-dimensional rank-two subspace of degree-capped polynomial
pairs contains a nonzero determinant with the sharp codimension rebate. -/
theorem exists_low_degree_pairDet_of_rank_two
    (c h L : ℕ) (hc : 0 < c) (hh : 0 < h) (hLd : L ≤ c + h)
    (V : Submodule F (PolynomialPairSpace F c h))
    (hVrank : Module.finrank F V = L)
    (hrankTwo : ∃ u v : V, polynomialPairDet u.1 v.1 ≠ 0) :
    ∃ u v : V, polynomialPairDet u.1 v.1 ≠ 0 ∧
      (polynomialPairDet u.1 v.1).natDegree ≤ c + h - L := by
  classical
  obtain ⟨u₀, v₀, hdet₀⟩ := hrankTwo
  obtain ⟨w, z, hwA, hwB, hwz⟩ :=
    exists_bicomponent_pivot_of_pairDet_ne_zero V u₀ v₀ hdet₀
  obtain ⟨d, a, b, hd, ha, hb, hcop, hwAfactor, hwBfactor⟩ :=
    exists_coprime_primitive_factor w.1.1.1 w.1.2.1 hwA hwB
  have hwAdegree : w.1.1.1.natDegree < c := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hwA]
    exact Polynomial.mem_degreeLT.mp w.1.1.2
  have hwBdegree : w.1.2.1.natDegree < h := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hwB]
    exact Polynomial.mem_degreeLT.mp w.1.2.2
  have haDvd : a ∣ w.1.1.1 := ⟨d, by simpa [mul_comm] using hwAfactor⟩
  have hbDvd : b ∣ w.1.2.1 := ⟨d, by simpa [mul_comm] using hwBfactor⟩
  have haDegree : a.natDegree < c :=
    (Polynomial.natDegree_le_of_dvd haDvd hwA).trans_lt hwAdegree
  have hbDegree : b.natDegree < h :=
    (Polynomial.natDegree_le_of_dvd hbDvd hwB).trans_lt hwBdegree
  have haMem : a ∈ Polynomial.degreeLT F c := by
    apply Polynomial.mem_degreeLT.mpr
    rw [← Polynomial.natDegree_lt_iff_degree_lt ha]
    exact haDegree
  have hbMem : b ∈ Polynomial.degreeLT F h := by
    apply Polynomial.mem_degreeLT.mpr
    rw [← Polynomial.natDegree_lt_iff_degree_lt hb]
    exact hbDegree
  let p : PolynomialPairSpace F c h := (⟨a, haMem⟩, ⟨b, hbMem⟩)
  let detP : V →ₗ[F] F[X] :=
    (polynomialPairDetLinear p).comp V.subtype
  let Q := LinearMap.ker detP
  let q := Module.finrank F Q
  have hdetFactor (x : V) :
      polynomialPairDet w.1 x.1 = d * polynomialPairDet p x.1 := by
    simp only [polynomialPairDet]
    change w.1.1.1 * x.1.2.1 - w.1.2.1 * x.1.1.1 =
      d * (a * x.1.2.1 - b * x.1.1.1)
    rw [hwAfactor, hwBfactor]
    ring
  have hpz : polynomialPairDet p z.1 ≠ 0 := by
    intro hpz0
    apply hwz
    rw [hdetFactor z, hpz0, mul_zero]
  have hwker : detP w = 0 := by
    change polynomialPairDet p w.1 = 0
    simp only [polynomialPairDet]
    change a * w.1.2.1 - b * w.1.1.1 = 0
    rw [hwAfactor, hwBfactor]
    ring
  let wQ : Q := ⟨w, hwker⟩
  have hwne : w ≠ 0 := by
    intro hw0
    apply hwA
    have := congrArg (fun x : V => x.1.1.1) hw0
    simpa using this
  have hwQne : wQ ≠ 0 := by
    intro hwQ0
    apply hwne
    exact congrArg (fun x : Q => (x.1 : V)) hwQ0
  have hqpos : 0 < q := by
    change 0 < Module.finrank F Q
    have hli : LinearIndependent F (fun _ : Fin 1 => wQ) := by
      apply Fintype.linearIndependent_iffₛ.mpr
      intro f g hfg i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [Fin.sum_univ_one] at hfg
      have hpoly := congrArg (fun y : Q => y.1.1.1.1) hfg
      have hpoly' : C (f 0) * w.1.1.1 = C (g 0) * w.1.1.1 := by
        simpa only [Submodule.coe_smul_of_tower, Prod.smul_fst,
          smul_eq_C_mul, RingHom.id_apply] using hpoly
      exact Polynomial.C_injective (mul_right_cancel₀ hwA hpoly')
    have hle := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    omega
  have himagePos : 0 < Module.finrank F (LinearMap.range detP) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let y : LinearMap.range detP := ⟨detP z, ⟨z, rfl⟩⟩
    refine ⟨y, ?_⟩
    intro hy0
    apply hpz
    have := congrArg (fun r : LinearMap.range detP => (r.1 : F[X])) hy0
    simpa [y, detP] using this
  have hqL : q < L := by
    have hrankNullity := LinearMap.finrank_range_add_finrank_ker
      (K := F) (V := V) detP
    have heq : Module.finrank F (LinearMap.range detP) + q = L := by
      simpa [Q, q, hVrank] using hrankNullity
    omega
  obtain ⟨hqc, hqh, ured, huredne, huredker, huredA, huredB⟩ :=
    exists_reduced_pivot_in_primitive_kernel V p ha hb hcop
      (by rfl) hqpos
  have hcross : p.1.1 * ured.1.2.1 = p.2.1 * ured.1.1.1 := by
    exact sub_eq_zero.mp (by simpa [polynomialPairDet] using huredker)
  obtain ⟨s, huredAfactor, huredBfactor⟩ :=
    exists_polynomial_multiplier_of_coprime_cross
      p.1.1 p.2.1 ured.1.1.1 ured.1.2.1 ha hcop hcross
  have hsne : s ≠ 0 := by
    intro hs0
    apply huredne
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · simpa [huredAfactor, hs0]
    · simpa [huredBfactor, hs0]
  let detU : V →ₗ[F] F[X] :=
    (polynomialPairDetLinear ured.1).comp V.subtype
  have hdetUFactor (x : V) : detU x = s * detP x := by
    change polynomialPairDet ured.1 x.1 = s * polynomialPairDet p x.1
    simp only [polynomialPairDet]
    rw [huredAfactor, huredBfactor]
    ring
  have hkerEq : LinearMap.ker detU = Q := by
    ext x
    change detU x = 0 ↔ detP x = 0
    rw [hdetUFactor]
    exact mul_eq_zero.trans (or_iff_right hsne)
  have himageRankU : Module.finrank F (LinearMap.range detU) = L - q := by
    have hrankNullity := LinearMap.finrank_range_add_finrank_ker
      (K := F) (V := V) detU
    rw [hkerEq] at hrankNullity
    have heq : Module.finrank F (LinearMap.range detU) + q = L := by
      simpa [q, hVrank] using hrankNullity
    omega
  obtain ⟨v, hvV, hdet, hdegree⟩ :=
    exists_low_degree_pairDet_of_reduced_pivot
      c h L q hc hh V ured hqL hLd hqc hqh
      huredA huredB himageRankU
  exact ⟨ured, ⟨v, hvV⟩, hdet, hdegree⟩

end ProximityPrize.SubmissionLower
