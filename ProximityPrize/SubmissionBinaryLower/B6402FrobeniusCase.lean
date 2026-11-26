import ProximityPrize.SubmissionBinaryLower.B6402DerivativeFactor
/-! Frobenius descent at 6402 reduces the pure-square quadratic case to one
ordinary slope-linear count at q=2 plus the slope-free exceptional labels. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402FrobeniusCase
open B6401Main
open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6401FarkasVerifier B6401HybridP64 B6401IntFarkas
open B6401IntSmallCerts B6401T4Rows B6401T4Grid
open B6401CertsT1 B6401CertsT2 B6401CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6401SmallAlg B6401ResLineOrd B6401QuotBridge B6401PointSurplus
open B6401Table4Common B6401Table4NonK B6401Table4K B6401ListAndMCA B6401FactorBound
open ReedSolomon ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index


def linearPrice (q : ℕ) : ℕ := if q=1 then 8167616324360948337+700000000000000000+100000000000000 else 16200000000000000000

def LinearFactorBound : Prop :=
  ∀ (u₀ u₁ : Idx → Fld) (q : ℕ), (q=1 ∨ q=2) → ∀ (F : ContactPoly (Polynomial Fld)),
    Irreducible F → contactDeriv F=0 → F.natDegree=1 →
    wdeg wY F≤26689499 → (q=2 → wdeg wY F≤13345478) → wYZ q F≤1811 →
    ∀ (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx),
      (∀ z∈S,(P z).natDegree≤wY) → (∀ z∈S,evalContact (evalZContact F z) (P z)=0) →
      (∀ z∈S,A≤(Az z).card) →
      (∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i) →
      (∀ z∈S,B6402HybridP64.BadOn6402 u₀ u₁ (Az z)) → (S.card:ℚ)≤linearPrice q

theorem descended_bound (linear : LinearFactorBound)
    (u₀ u₁ : Idx → Fld) {F : ContactPoly (Polynomial Fld)}
    (hD : contactDeriv F = 0) (hFdeg : F.natDegree = 2) (hf1 : F.coeff 1 = 0)
    (hWF : wdeg wY F ≤ 2 * A * 9 - 1) (hWYZ : wYZ 1 F ≤ 1811)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact F z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ S, B6402HybridP64.BadOn6402 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ ((linearPrice 2 + 1000000000000 : ℕ) : ℚ) := by
  classical
  have hev_of_deriv : ∀ g : BiPoly (Polynomial Fld), g.derivative = 0 → ∀ j, j % 2 = 1 → g.coeff j = 0 := by
    intro g hg j hj
    have h0 := congrArg (fun p : BiPoly (Polynomial Fld) => p.coeff (j - 1)) hg
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h0
    have hj1 : j - 1 + 1 = j := by omega
    have h2X : (2 : Polynomial (Polynomial Fld)) = 0 := CharTwo.two_eq_zero
    have hcast : ((j - 1 : ℕ) : Polynomial (Polynomial Fld)) + 1 = 1 := by
      have : ((j - 1 : ℕ) : Polynomial (Polynomial Fld)) = 0 := by
        rw [show j - 1 = 2 * ((j - 1) / 2) by omega]; push_cast; rw [h2X, zero_mul]
      rw [this, zero_add]
    rw [hj1, hcast, mul_one] at h0; exact h0
  have hf0_evY : ∀ j, j % 2 = 1 → (F.coeff 0).coeff j = 0 := by
    apply hev_of_deriv
    have h1 := congrArg (fun Q : ContactPoly (Polynomial Fld) => Q.coeff 1) hD
    rw [coeff_contactDeriv, Polynomial.coeff_zero] at h1
    simp only [one_ne_zero, ↓reduceIte, show (1 : ℕ) - 1 = 0 by rfl, hf1, dXBi_zero, zero_add] at h1
    exact h1
  have hd2_ev : ∀ j, j % 2 = 1 → (F.coeff 2).coeff j = 0 := by
    apply hev_of_deriv
    have h3 := congrArg (fun Q : ContactPoly (Polynomial Fld) => Q.coeff 3) hD
    rw [coeff_contactDeriv, Polynomial.coeff_zero] at h3
    have hf3 : F.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [show (3 : ℕ) ≠ 0 by omega, ↓reduceIte, show (3 : ℕ) - 1 = 2 by rfl, hf3, dXBi_zero, zero_add] at h3
    exact h3
  have hX_ev : ∀ k j i, i % 2 = 1 → (((F.coeff k).coeff j).coeff i) = 0 := by
    intro k j i hi
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · have h0 := congrArg (fun Q : ContactPoly (Polynomial Fld) => ((Q.coeff 0).coeff j).coeff (i - 1)) hD
      rw [coeff_contactDeriv, Polynomial.coeff_zero, Polynomial.coeff_zero, Polynomial.coeff_zero] at h0
      simp only [↓reduceIte, add_zero, coeff_dXBi, Polynomial.coeff_derivative] at h0
      have hi1 : i - 1 + 1 = i := by omega
      have h2P : (2 : Polynomial Fld) = 0 := CharTwo.two_eq_zero
      have hcast : ((i - 1 : ℕ) : Polynomial Fld) + 1 = 1 := by
        have : ((i - 1 : ℕ) : Polynomial Fld) = 0 := by
          rw [show i - 1 = 2 * ((i - 1) / 2) by omega]; push_cast; rw [h2P, zero_mul]
        rw [this, zero_add]
      rw [hi1, hcast, mul_one] at h0; exact h0
    · rw [hf1]; simp
    · have h2d := congrArg (fun Q : ContactPoly (Polynomial Fld) => ((Q.coeff 2).coeff j).coeff (i - 1)) hD
      rw [coeff_contactDeriv] at h2d
      simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte, show (2 : ℕ) - 1 = 1 by rfl, hf1,
        Polynomial.derivative_zero, add_zero, Polynomial.coeff_zero, coeff_dXBi,
        Polynomial.coeff_derivative] at h2d
      have hi1 : i - 1 + 1 = i := by omega
      have h2P : (2 : Polynomial Fld) = 0 := CharTwo.two_eq_zero
      have hcast : ((i - 1 : ℕ) : Polynomial Fld) + 1 = 1 := by
        have : ((i - 1 : ℕ) : Polynomial Fld) = 0 := by
          rw [show i - 1 = 2 * ((i - 1) / 2) by omega]; push_cast; rw [h2P, zero_mul]
        rw [this, zero_add]
      rw [hi1, hcast, mul_one] at h2d; exact h2d
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := F) (by omega)]; simp
  have hY_ev : ∀ k j, j % 2 = 1 → (F.coeff k).coeff j = 0 := by
    intro k j hj
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · exact hf0_evY j hj
    · rw [hf1]; simp
    · exact hd2_ev j hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := F) (by omega)]; simp
  -- Finite field char-2 Frobenius inverse `sqrtF : Fld → Fld`!
  have hfrob_surj : Function.Surjective (frobenius Fld 2) :=
    Finite.surjective_of_injective (frobenius_inj Fld 2)
  let sqrtF (a : Fld) : Fld := Classical.choose (hfrob_surj a)
  have hsqrtF : ∀ a : Fld, (sqrtF a) ^ 2 = a := fun a => Classical.choose_spec (hfrob_surj a)
  have hsqrt_inj : Function.Injective sqrtF := fun a b hab => by
    rw [← hsqrtF a, ← hsqrtF b, hab]
  let sqrtP (p : Polynomial Fld) : Polynomial Fld :=
    ∑ t ∈ Finset.range (p.natDegree + 1), Polynomial.monomial t (sqrtF (p.coeff t))
  have hsqrtP_sq : ∀ p : Polynomial Fld, (sqrtP p) ^ 2 = p.comp (X ^ 2) := by
    intro p
    dsimp only [sqrtP]; rw [sum_pow_char 2]
    apply Polynomial.ext; intro m; rw [finset_sum_coeff]
    by_cases hm : m % 2 = 0
    · rw [show m = 2 * (m / 2) by omega, comp_X_sq_coeff_even]
      by_cases hlt : m / 2 < p.natDegree + 1
      · rw [Finset.sum_eq_single (m / 2)]
        · rw [sq, Polynomial.monomial_mul_monomial, ← sq, hsqrtF, show m / 2 + m / 2 = 2 * (m / 2) by omega,
            Polynomial.coeff_monomial_same]
        · intro t _ hne; rw [sq, Polynomial.monomial_mul_monomial]
          simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show t + t ≠ 2 * (m / 2) by omega)]
        · intro h; exact absurd (Finset.mem_range.mpr hlt) h
      · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        intro t ht; rw [sq, Polynomial.monomial_mul_monomial]
        simp only [Polynomial.coeff_monomial, Finsupp.single_apply,
          if_neg (show t + t ≠ 2 * (m / 2) by have := Finset.mem_range.mp ht; omega)]
    · rw [show m = 2 * (m / 2) + 1 by omega, comp_X_sq_coeff_odd]
      apply Finset.sum_eq_zero; intro t _
      rw [sq, Polynomial.monomial_mul_monomial]
      simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show t + t ≠ 2 * (m / 2) + 1 by omega)]
  let mkBiZ (g : BiPoly (Polynomial Fld)) : BiPoly (Polynomial Fld) :=
    ∑ j ∈ Finset.range (g.natDegree / 2 + 1), Polynomial.monomial j
      (∑ i ∈ Finset.range ((g.coeff (2 * j)).natDegree / 2 + 1),
        Polynomial.monomial i (sqrtP ((g.coeff (2 * j)).coeff (2 * i))))
  have hmkBiZ_sq : ∀ g : BiPoly (Polynomial Fld),
      (∀ j, j % 2 = 1 → g.coeff j = 0) → (∀ j i, i % 2 = 1 → (g.coeff j).coeff i = 0) →
      (mkBiZ g) ^ 2 = g.map (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2))) := by
    intro g hgY hgX
    dsimp only [mkBiZ]; rw [sum_pow_char 2]
    apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    rw [finset_sum_coeff, finset_sum_coeff, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      Polynomial.coeff_map, Polynomial.coe_compRingHom]
    by_cases hj : j % 2 = 0
    · by_cases hj_le : j / 2 < g.natDegree / 2 + 1
      · rw [Finset.sum_eq_single (j / 2)]
        · rw [sq, Polynomial.monomial_mul_monomial, ← sq, sum_pow_char 2, show j / 2 + j / 2 = j by omega,
            Polynomial.coeff_monomial_same, finset_sum_coeff, show 2 * (j / 2) = j by omega]
          by_cases hi : i % 2 = 0
          · by_cases hi_le : i / 2 < (g.coeff j).natDegree / 2 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [sq, Polynomial.monomial_mul_monomial, ← sq, hsqrtP_sq, show i / 2 + i / 2 = i by omega,
                  show 2 * (i / 2) = i by omega, Polynomial.coeff_monomial_same]
              · intro i' _ hne; rw [sq, Polynomial.monomial_mul_monomial]
                simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show i' + i' ≠ i by omega)]
              · intro h; exact absurd (Finset.mem_range.mpr hi_le) h
            · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp only [Polynomial.zero_comp]
              intro i' hi'; rw [sq, Polynomial.monomial_mul_monomial]
              simp only [Polynomial.coeff_monomial, Finsupp.single_apply,
                if_neg (show i' + i' ≠ i by have := Finset.mem_range.mp hi'; omega)]
          · rw [Finset.sum_eq_zero, hgX j i (by omega)]; simp only [Polynomial.zero_comp]
            intro i' _; rw [sq, Polynomial.monomial_mul_monomial]
            simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show i' + i' ≠ i by omega)]
        · intro j' _ hne
          rw [sq, Polynomial.monomial_mul_monomial]
          simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show j' + j' ≠ j by omega), Polynomial.coeff_zero]
        · intro h; exact absurd (Finset.mem_range.mpr hj_le) h
      · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (p := g) (by omega), Polynomial.coeff_zero]; simp only [Polynomial.zero_comp]
        intro j' hj'; rw [sq, Polynomial.monomial_mul_monomial]
        simp only [Polynomial.coeff_monomial, Finsupp.single_apply,
          if_neg (show j' + j' ≠ j by have := Finset.mem_range.mp hj'; omega), Polynomial.coeff_zero]
    · rw [Finset.sum_eq_zero, hgY j (by omega), Polynomial.coeff_zero]; simp only [Polynomial.zero_comp]
      intro j' _; rw [sq, Polynomial.monomial_mul_monomial]
      simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show j' + j' ≠ j by omega), Polynomial.coeff_zero]
  let H : ContactPoly (Polynomial Fld) := Polynomial.C (mkBiZ (F.coeff 0)) + Polynomial.C (mkBiZ (F.coeff 2)) * Polynomial.X
  let F2 : ContactPoly (Polynomial Fld) :=
    F.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2))))
  have hH_sq : F2 = H ^ 2 := by
    have h2C : (2 : ContactPoly (Polynomial Fld)) = 0 := CharTwo.two_eq_zero
    have hsq : H ^ 2 = Polynomial.C ((mkBiZ (F.coeff 0)) ^ 2) + Polynomial.C ((mkBiZ (F.coeff 2)) ^ 2) * Polynomial.X ^ 2 := by
      dsimp only [H]; rw [map_pow, map_pow]
      linear_combination (Polynomial.C (mkBiZ (F.coeff 0)) * Polynomial.C (mkBiZ (F.coeff 2)) * Polynomial.X) * h2C
    rw [hsq, hmkBiZ_sq (F.coeff 0) (hY_ev 0) (hX_ev 0), hmkBiZ_sq (F.coeff 2) (hY_ev 2) (hX_ev 2)]
    apply Polynomial.ext; intro k
    rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · simp [Polynomial.coeff_C_mul_X_pow]
    · simp [hf1, Polynomial.coeff_C_mul_X_pow]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero,
        Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
        Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
  have hFne : F ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at hFdeg; omega
  have hF2_ne : F2 ≠ 0 := by
    have hinj : Function.Injective (Polynomial.compRingHom (X ^ 2 : Polynomial Fld)) :=
      fun p q h => by
        have hsub : (p - q).comp (X ^ 2) = 0 := by rw [sub_comp, sub_eq_zero]; exact h
        exact sub_eq_zero.mp ((comp_X_sq_eq_zero_iff (p - q)).mp hsub)
    exact (Polynomial.map_ne_zero_iff (Polynomial.map_injective _ (Polynomial.map_injective _ hinj))).mpr hFne
  have hH_ne : H ≠ 0 := fun h0 => hF2_ne (by rw [hH_sq, h0, zero_pow (by norm_num)])
  have hH_deg : H.natDegree = 1 := by
    have hF2_deg : F2.natDegree = 2 := by
      have hinj : Function.Injective (Polynomial.compRingHom (X ^ 2 : Polynomial Fld)) :=
        fun p q h => sub_eq_zero.mp ((comp_X_sq_eq_zero_iff (p - q)).mp (by rw [sub_comp, sub_eq_zero]; exact h))
      rw [← hFdeg]
      exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ (Polynomial.map_injective _ hinj)) F
    have h1 := Polynomial.natDegree_mul hH_ne hH_ne
    rw [← sq, ← hH_sq, hF2_deg] at h1; omega
  have hH_wdeg : wdeg wY H ≤ 13345478 := by
    have hF2_wdeg : wdeg wY F2 ≤ 2 * A * 9 - 1 := by
      rw [wdeg_le_iff]; intro k j i hnz
      have hnz' : ((F.coeff k).coeff j).coeff i ≠ 0 := fun h => hnz (by simp [F2, h])
      exact (wdeg_le_iff wY _ F).mp hWF k j i hnz'
    have hmul := wdeg_mul wY hH_ne hH_ne
    rw [← sq, ← hH_sq] at hmul
    have hN : 2 * A * 9 - 1 = 26689499 := by norm_num [A]
    omega
  have hH_wYZ : wYZ 2 H ≤ 1811 := wYZ_frobenius_descent hH_sq hWYZ
  -- Lift `S` via `sqrtF` to `SW` with `P_W w := P (w^2)` and `Az_W w := Az (w^2)`!
  let SW : Finset Fld := S.image sqrtF
  let PW : Fld → Polynomial Fld := fun w => P (w ^ 2)
  let AzW : Fld → Finset Idx := fun w => Az (w ^ 2)
  have hSW_card : SW.card = S.card := Finset.card_image_of_injective S hsqrt_inj
  have hSW_mem : ∀ w ∈ SW, w ^ 2 ∈ S := by
    intro w hw; rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩; rwa [hsqrtF]
  have hH_van : ∀ w ∈ SW, evalContact (evalZContact H w) (PW w) = 0 := by
    intro w hw
    have hw2S : w ^ 2 ∈ S := hSW_mem w hw
    have hev2 : evalZContact F2 w = evalZContact F (w ^ 2) := by
      apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
      simp only [F2, evalZContact, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
        Polynomial.coe_evalRingHom, Polynomial.coe_compRingHom, Polynomial.eval_comp,
        Polynomial.eval_pow, Polynomial.eval_X]
    have hsq0 : (evalContact (evalZContact H w) (PW w)) ^ 2 = 0 := by
      have h1 : (evalContact (evalZContact H w) (PW w)) ^ 2 = evalContact (evalZContact (H ^ 2) w) (PW w) := by
        rw [sq, ← evalContact_mul, show evalZContact H w * evalZContact H w = evalZContact (H ^ 2) w from by
          unfold evalZContact; rw [sq, Polynomial.map_mul]]
      rw [h1, ← hH_sq, hev2]
      exact hFvan (w ^ 2) hw2S
    exact sq_eq_zero_iff.mp hsq0
  -- Factor `H` in `ContactPoly (Polynomial Fld)`: `H = C G0 * H1 * uH` (`H1` irreducible of `deg_R = 1`)!
  let facs := UniqueFactorizationMonoid.normalizedFactors H
  let facs0 := facs.filter fun G => G.natDegree = 0
  let facs1 := facs.filter fun G => 1 ≤ G.natDegree
  have hfacs_split : facs = facs0 + facs1 := by
    ext G; simp only [facs0, facs1, Multiset.count_add, Multiset.count_filter]
    by_cases h0 : G.natDegree = 0
    · simp [h0]
    · simp [h0, show 1 ≤ G.natDegree by omega]
  obtain ⟨uH, huH⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := H) hH_ne
  have hH_fac : facs0.prod * facs1.prod * (uH : ContactPoly (Polynomial Fld)) = H := by
    rw [← Multiset.prod_add, ← hfacs_split]; exact huH
  have hfacs0_deg0 : facs0.prod.natDegree = 0 := by
    have hgen : ∀ m : Multiset (ContactPoly (Polynomial Fld)), (∀ G ∈ m, G.natDegree = 0) → m.prod.natDegree = 0 := by
      intro m; induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons a s ih =>
          intro h; rw [Multiset.prod_cons]
          exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_mul_le.trans
            (by rw [h a (Multiset.mem_cons_self a s), ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]))
    exact hgen facs0 fun G hG => (Multiset.mem_filter.mp hG).2
  let G0 : BiPoly (Polynomial Fld) := facs0.prod.coeff 0
  have hfacs0_eq : facs0.prod = Polynomial.C G0 := Polynomial.eq_C_of_natDegree_eq_zero hfacs0_deg0
  have hG0_ne : G0 ≠ 0 := fun h0 => hH_ne (by rw [← hH_fac, hfacs0_eq, h0, map_zero, zero_mul, zero_mul])
  have hf1p_ne : facs1.prod ≠ 0 := fun h0 => hH_ne (by rw [← hH_fac, h0, mul_zero, zero_mul])
  have hfacs1_deg : facs1.prod.natDegree = 1 := by
    have hu0 : (uH : ContactPoly (Polynomial Fld)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit uH.isUnit
    have h1 : (facs0.prod * facs1.prod * (uH : ContactPoly (Polynomial Fld))).natDegree = facs1.prod.natDegree := by
      rw [Polynomial.natDegree_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr hG0_ne |> fun h => hfacs0_eq ▸ h) hf1p_ne) uH.ne_zero,
        Polynomial.natDegree_mul (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) hf1p_ne, hfacs0_deg0, hu0, zero_add, add_zero]
    rw [hH_fac, hH_deg] at h1; exact h1.symm
  -- Since `facs1.prod.natDegree = 1`, `facs1` has EXACTLY ONE element `H1` (`Irreducible H1, H1.natDegree = 1`)!
  have hfacs1_card1 : facs1.card = 1 := by
    have hge1 : 1 ≤ facs1.card := by
      by_contra h0; have he : facs1 = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [he, Multiset.prod_zero, Polynomial.natDegree_one] at hfacs1_deg; omega
    have hle1 : facs1.card ≤ facs1.prod.natDegree := by
      have hsum : ∀ m : Multiset (ContactPoly (Polynomial Fld)), (∀ G ∈ m, Irreducible G ∧ 1 ≤ G.natDegree) →
          m.card ≤ m.prod.natDegree := by
        intro m; induction m using Multiset.induction_on with
        | empty => intro _; simp
        | cons a s ih =>
            intro h
            have ha := h a (Multiset.mem_cons_self a s)
            have hs : ∀ x ∈ s, Irreducible x ∧ 1 ≤ x.natDegree := fun x hx => h x (Multiset.mem_cons_of_mem hx)
            have hs_ne : s.prod ≠ 0 := Multiset.prod_ne_zero (s := s) fun h0 => (hs 0 h0).1.ne_zero rfl
            rw [Multiset.card_cons, Multiset.prod_cons, Polynomial.natDegree_mul ha.1.ne_zero hs_ne]
            have := ih hs; omega
      exact hsum facs1 fun G hG => ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor G
        (Multiset.mem_filter.mp hG).1, (Multiset.mem_filter.mp hG).2⟩
    omega
  obtain ⟨H1, hfacs1_eq⟩ := Multiset.card_eq_one.mp hfacs1_card1
  have hH1_mem : H1 ∈ facs1 := by rw [hfacs1_eq]; exact Multiset.mem_singleton_self H1
  have hH1_irr : Irreducible H1 := UniqueFactorizationMonoid.irreducible_of_normalized_factor H1 (Multiset.mem_filter.mp hH1_mem).1
  have hH1_deg : H1.natDegree = 1 := by simpa [hfacs1_eq] using hfacs1_deg
  have hH_eq_prod : Polynomial.C G0 * H1 * (uH : ContactPoly (Polynomial Fld)) = H := by
    simpa [hfacs0_eq, hfacs1_eq] using hH_fac
  -- Bound `G0` and `H1` separately on `SW`!
  let SW0 := SW.filter fun w => triEval G0 w (PW w) = 0
  let SW1 := SW.filter fun w => evalContact (evalZContact H1 w) (PW w) = 0
  have hSW_cover : SW ⊆ SW0 ∪ SW1 := by
    intro w hw
    have h0 := hH_van w hw
    rw [← hH_eq_prod] at h0
    have hmulZ : ∀ A B : ContactPoly (Polynomial Fld), evalZContact (A * B) w = evalZContact A w * evalZContact B w :=
      fun A B => by unfold evalZContact; exact Polynomial.map_mul _
    rw [hmulZ, hmulZ, evalContact_mul, evalContact_mul] at h0
    have hu_ne : evalContact (evalZContact (uH : ContactPoly (Polynomial Fld)) w) (PW w) ≠ 0 := by
      rcases uH.isUnit with ⟨v, hv⟩; intro h0'
      have h1 := congrArg (fun q => evalContact (evalZContact q w) (PW w)) v.mul_inv
      rw [hmulZ, evalContact_mul, hv, h0', zero_mul] at h1
      have : evalContact (evalZContact (1 : ContactPoly (Polynomial Fld)) w) (PW w) = 1 := by
        unfold evalZContact evalContact; simp
      rw [this] at h1; exact one_ne_zero h1.symm
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hu_ne) with hG | hH1v
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, by simpa [evalZContact, evalContact, triEval] using hG⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, hH1v⟩)
  -- `G0` bound: `wdegBi G0 ≤ 13345478 ⇒ deg_Y G0 ≤ 12`, `deg_Z G0 ≤ 1811`!
  have hG0_wdeg : wdeg wY (Polynomial.C G0) ≤ 13345478 := by
    have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hH1_irr.ne_zero uH.ne_zero)
    rw [← mul_assoc, hH_eq_prod] at h1; omega
  have hG0_deg : G0.natDegree ≤ 12 := by
    have h1 : wdegBiDom wY G0 ≤ 13345478 := by simpa using wdegBiDom_le_of_wdeg_coeff hG0_wdeg 0
    have h2 := wdegBiDom_ge_natDegree_mul wY G0 hG0_ne
    have hle := h2.trans h1
    have hw : wY = 1048575 := rfl
    rw [hw] at hle; omega
  have hG0_wYZ : wYZ 2 (Polynomial.C G0) ≤ 1811 := by
    have h1 := wYZ_mul 2 (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hH1_irr.ne_zero uH.ne_zero)
    rw [← mul_assoc, hH_eq_prod] at h1; omega
  have hSW0_card : (SW0.card : ℚ) ≤ (1000000000000 : ℚ) := by
    have hark := B6402HybridP64.card_le_of_biPoly_pow u₀ u₁ 2 (by omega) G0 12 1811 hG0_ne hG0_deg
      (fun j a => by simpa only [Polynomial.coeff_C_zero] using natDegree_Z_le_of_wYZ hG0_wYZ 0 j a) SW0 PW AzW
      (fun w hw => hP (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      (fun w hw => (Finset.mem_filter.mp hw).2)
      (fun w hw => hcard (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      (fun w hw i hi => (hmatch (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1) i).mp hi)
      (fun w hw => hbad (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
    refine hark.trans (max_le (by norm_num) ?_)
    unfold B6402HybridP64.arklibBoundPowQ; norm_num [N, wY, A]
  -- `H1` bound: split on `contactDeriv H1 = 0`!
  have hH1_wdeg : wdeg wY H1 ≤ 13345478 := by
    have h1 := wdeg_mul wY hH1_irr.ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hG0_ne) uH.ne_zero)
    have hEq : H1 * (Polynomial.C G0 * (uH : ContactPoly (Polynomial Fld))) = H := by rw [← hH_eq_prod]; ring
    rw [hEq] at h1; omega
  have hH1_wYZ : wYZ 2 H1 ≤ 1811 := by
    have h1 := wYZ_mul 2 hH1_irr.ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hG0_ne) uH.ne_zero)
    have hEq : H1 * (Polynomial.C G0 * (uH : ContactPoly (Polynomial Fld))) = H := by rw [← hH_eq_prod]; ring
    rw [hEq] at h1; omega
  have hSW1_card : (SW1.card : ℚ) ≤ ((linearPrice 2 : ℕ) : ℚ) := by
    by_cases hDH1 : contactDeriv H1 = 0
    · exact linear u₀ u₁ 2 (Or.inr rfl) H1 hH1_irr hDH1 hH1_deg (by omega) (fun _ => hH1_wdeg) hH1_wYZ
        SW1 PW AzW (fun w hw => hP (w^2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw => (Finset.mem_filter.mp hw).2)
        (fun w hw => hcard (w^2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw i => hmatch (w^2) (hSW_mem w (Finset.mem_filter.mp hw).1) i)
        (fun w hw => hbad (w^2) (hSW_mem w (Finset.mem_filter.mp hw).1))
    · have hcd := B6402DerivativeFactor.card_le_of_contactDeriv_ne_zero u₀ u₁ (Or.inr rfl) hH1_irr hH1_deg hH1_wdeg
        (fun k j i => (natDegree_Z_le_of_wYZ hH1_wYZ k j i).trans (by decide : 1811≤3850)) hDH1 SW1 PW AzW
        (fun w hw => hP (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw => (Finset.mem_filter.mp hw).2)
        (fun w hw => hcard (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw i hi => (hmatch (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1) i).mp hi)
        (fun w hw => hbad (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      exact hcd.trans (by decide)
  have hS_le : S.card ≤ SW0.card + SW1.card := by
    rw [← hSW_card]; exact (Finset.card_le_card hSW_cover).trans (Finset.card_union_le _ _)
  have hSQ : (S.card : ℚ) ≤ (SW0.card : ℚ) + (SW1.card : ℚ) := by exact_mod_cast hS_le
  push_cast at hSW1_card ⊢; linarith


#print axioms descended_bound
end ProximityPrize.SubmissionBinaryLower.B6402FrobeniusCase
