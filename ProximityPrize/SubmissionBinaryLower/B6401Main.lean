import ProximityPrize.SubmissionBinaryLower.B6401FactorBound
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

/-!
# Binary IRS Lower Track — 64.01 Master Theorem (`B6401Main`)

Assembles the unconditional char-2 beyond-Johnson `ker(D)` proof at score `64.01`
(`radius = 78633206 / 268435456`, `A = 1482831`, `D = wY = 1048575`, `N = 2^21`):
1. Global weighted `ker(D)` contact interpolation (`m₀ = 9, s₀ = 2, W₀ = 26690957, D_ZF = 3850`).
2. UFD factorization in `ContactPoly (Polynomial Fld)` with exact `wYZ` and `wdeg` additivity.
3. Unconditional factor dispatch:
   - `deg_R = 0` bundled `BiPoly`: `card_le_of_biPoly_pow` (`≤ 10^12`),
   - `contactDeriv F ≠ 0`: `F^2 ∣ Q` + `Res_R(F, contactDeriv F)` (`≤ 3 · 10^12`),
   - `deg_R = 1, F ∈ ker(D)`: `deg1_factor_card_le` (`q₀ = 1`, Tables 1 & 4),
   - `deg_R = 2, F ∈ ker(D), f₁ = 0`: Frobenius descent (`wYZ_frobenius_descent`) to `q₀ = 2`,
   - `deg_R = 2, F ∈ ker(D), f₁ ≠ 0`: `deg2_factor_card_le` (Tables 2, 3, 2A, 2B).
4. Combines `lineExactAgreementBound_6401` (`mcaCap = 18.4 · 10^18`) with `scalarListBound_6401`
   (`listCap = 10^7`) via `protocolClaim6401_of_lineAndList` to produce
   `ProtocolClaim 6401 78633206 268435456`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401Main

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
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

/-! ### Part 1: Irreducibility Lifting, `contactDeriv ≠ 0` Elimination, & Frobenius Descent -/

/-- Any irreducible `F ∈ ContactPoly (Polynomial Fld)` with `1 ≤ F.natDegree` remains irreducible
after lifting `Polynomial Fld → RatFunc Fld` (`liftCRat F`)! -/
lemma irreducible_liftCRat_of_irred {F : ContactPoly (Polynomial Fld)}
    (hirr : Irreducible F) (hdeg : 1 ≤ F.natDegree) :
    Irreducible (liftCRat F) := by
  classical
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg_inj : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hlift_inj : Function.Injective (liftCRat (F := Fld)) :=
    Polynomial.map_injective _ (Polynomial.map_injective _ (Polynomial.map_injective _ halg_inj))
  have hF_prime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hclear : ∀ R : ContactPoly (RatFunc Fld),
      ∃ (d : Polynomial Fld) (R' : ContactPoly (Polynomial Fld)), d ≠ 0 ∧ cC (alg d) * R = liftCRat R' := by
    intro R
    let coords : Finset (ℕ × ℕ × ℕ) :=
      R.support.biUnion fun k => (R.coeff k).support.biUnion fun j =>
        ((R.coeff k).coeff j).support.image fun i => (k, j, i)
    have hsurj : ∀ c : ℕ × ℕ × ℕ, ∃ (n d : Polynomial Fld), d ≠ 0 ∧
        alg d * (((R.coeff c.1).coeff c.2.1).coeff c.2.2) = alg n := fun c => by
      obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial Fld)) (((R.coeff c.1).coeff c.2.1).coeff c.2.2)
      exact ⟨n, d, nonZeroDivisors.ne_zero d.2, by simpa [mul_comm] using hd⟩
    choose nC dC hdC_ne hndC using hsurj
    let d : Polynomial Fld := ∏ c ∈ coords, dC c
    have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hdC_ne c
    have hnum : ∀ k j i, ∃ p : Polynomial Fld, alg d * (((R.coeff k).coeff j).coeff i) = alg p := by
      intro k j i
      by_cases hnz : ((R.coeff k).coeff j).coeff i = 0
      · exact ⟨0, by simp [hnz]⟩
      · have hmem : (k, j, i) ∈ coords := by
          simp only [coords, Finset.mem_biUnion, Finset.mem_image, Polynomial.mem_support_iff, Prod.mk.injEq]
          exact ⟨k, fun h => hnz (by simp [h]), j, fun h => hnz (by simp [h]), i, hnz, rfl, rfl, rfl⟩
        refine ⟨(∏ c ∈ coords.erase (k, j, i), dC c) * nC (k, j, i), ?_⟩
        have hd_eq : d = (∏ c ∈ coords.erase (k, j, i), dC c) * dC (k, j, i) :=
          (Finset.mul_prod_erase coords dC hmem).symm.trans (mul_comm _ _)
        rw [hd_eq, map_mul, map_mul, mul_assoc, hndC (k, j, i)]
    choose pC hpC using hnum
    let R' : ContactPoly (Polynomial Fld) :=
      ∑ k ∈ R.support, Polynomial.monomial k (∑ j ∈ (R.coeff k).support,
        Polynomial.monomial j (∑ i ∈ ((R.coeff k).coeff j).support, Polynomial.monomial i (pC k j i)))
    refine ⟨d, R', hd_ne, ?_⟩
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    have hL : (((cC (alg d) * R).coeff k).coeff j).coeff i = alg d * (((R.coeff k).coeff j).coeff i) := by
      unfold cC; simp [Polynomial.coeff_C_mul]
    rw [hL, hpC k j i]
    have hR : (((liftCRat R').coeff k).coeff j).coeff i = alg (((R'.coeff k).coeff j).coeff i) := by
      dsimp only [alg]; simp [liftCRat, liftBiRat]
    rw [hR]; congr 1
    dsimp only [R']; rw [finset_sum_coeff]
    by_cases hk : k ∈ R.support
    · rw [Finset.sum_eq_single k]
      · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
        by_cases hj : j ∈ (R.coeff k).support
        · rw [Finset.sum_eq_single j]
          · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
            by_cases hi : i ∈ ((R.coeff k).coeff j).support
            · rw [Finset.sum_eq_single i]
              · rw [Polynomial.coeff_monomial_same]
              · intro i' _ hne; simp [Polynomial.coeff_monomial, hne]
              · intro h; exact absurd hi h
            · rw [Finset.sum_eq_zero]
              · apply halg_inj; rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hi), mul_zero]
              · intro i' hi'; simp [Polynomial.coeff_monomial, show i' ≠ i from fun h => hi (h ▸ hi')]
          · intro j' _ hne; simp [Polynomial.coeff_monomial, hne]
          · intro h; exact absurd hj h
        · rw [Finset.sum_eq_zero]
          · rw [Polynomial.coeff_zero]; apply halg_inj
            rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hj), Polynomial.coeff_zero, mul_zero]
          · intro j' hj'; simp [Polynomial.coeff_monomial, show j' ≠ j from fun h => hj (h ▸ hj')]
      · intro k' _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd hk h
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.coeff_zero, Polynomial.coeff_zero]; apply halg_inj
        rw [← hpC, map_zero, not_not.mp (Polynomial.mem_support_iff.not.mp hk), Polynomial.coeff_zero, Polynomial.coeff_zero, mul_zero]
      · intro k' hk'; simp [Polynomial.coeff_monomial, show k' ≠ k from fun h => hk (h ▸ hk')]
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h1 : (liftCRat F).natDegree = F.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ (Polynomial.map_injective _ halg_inj)) F
    omega
  · intro a b hab
    obtain ⟨da, A, hda, hA⟩ := hclear a
    obtain ⟨db, B, hdb, hB⟩ := hclear b
    have hprod_rat : liftCRat (cC (da * db) * F) = liftCRat (A * B) := by
      rw [map_mul, map_mul, ← hA, ← hB, show liftCRat (cC (da * db)) = cC (alg da) * cC (alg db) by
        dsimp only [alg]; unfold liftCRat liftBiRat cC; simp [map_mul, Polynomial.map_C]]
      rw [hab]; ring
    have hprod : cC (da * db) * F = A * B := hlift_inj hprod_rat
    have hunit_of_dvd : ∀ (d1 : Polynomial Fld) (X1 Y1 : ContactPoly (Polynomial Fld)) (y1 : ContactPoly (RatFunc Fld)),
        d1 ≠ 0 → cC (alg d1) * y1 = liftCRat Y1 → cC (da * db) * F = X1 * Y1 → F ∣ X1 →
        IsUnit y1 := by
      intro d1 X1 Y1 y1 hd1 hy1 heq ⟨U, hU⟩
      rw [hU] at heq
      have hcancel : cC (da * db) = U * Y1 := mul_left_cancel₀ hirr.ne_zero (by
        calc F * cC (da * db) = cC (da * db) * F := by ring
          _ = F * U * Y1 := heq
          _ = F * (U * Y1) := by ring)
      have hlift_c := congrArg liftCRat hcancel
      rw [map_mul, ← hy1] at hlift_c
      have hc_eq : liftCRat (cC (da * db)) = cC (alg (da * db)) := by
        dsimp only [alg]; unfold liftCRat liftBiRat cC; simp [Polynomial.map_C]
      rw [hc_eq] at hlift_c
      have hu_d : IsUnit (cC (alg (da * db)) : ContactPoly (RatFunc Fld)) := by
        have hne : alg (da * db) ≠ 0 := fun h0 => mul_ne_zero hda hdb (halg_inj (h0.trans (map_zero alg).symm))
        exact Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hne)))
      rcases hu_d with ⟨u, hu⟩
      refine isUnit_iff_exists_inv.mpr ⟨liftCRat U * cC (alg d1) * (u⁻¹ : _), ?_⟩
      calc y1 * (liftCRat U * cC (alg d1) * (u⁻¹ : _))
          = (liftCRat U * (cC (alg d1) * y1)) * (u⁻¹ : _) := by ring
        _ = cC (alg (da * db)) * (u⁻¹ : _) := by rw [← hlift_c]
        _ = (u : _) * (u⁻¹ : _) := by rw [hu]
        _ = 1 := Units.mul_inv u
    have hF_dvd_AB : F ∣ A * B := ⟨cC (da * db), by rw [← hprod]; ring⟩
    rcases hF_prime.dvd_or_dvd hF_dvd_AB with hFA | hFB
    · right; exact hunit_of_dvd db A B b hdb hB hprod hFA
    · left; exact hunit_of_dvd da B A a hda hA (hprod.trans (by ring)) hFB

/-- `evalZContact` commutes with `contactDeriv`! -/
lemma evalZContact_contactDeriv (F : ContactPoly (Polynomial Fld)) (z : Fld) :
    evalZContact (contactDeriv F) z = contactDeriv (evalZContact F z) := by
  apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
  have hev : ∀ (Q : ContactPoly (Polynomial Fld)) k' j' i',
      (((evalZContact Q z).coeff k').coeff j').coeff i' = ((((Q.coeff k').coeff j').coeff i').eval z) := by
    intro Q k' j' i'
    unfold evalZContact
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
  rw [hev, coeff_contactDeriv, coeff_contactDeriv, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, coeff_dXBi, coeff_dXBi,
    Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.eval_add]
  have h1 : ((((F.coeff k).coeff j).coeff (i + 1)) * (((i : ℕ) : Polynomial Fld) + 1)).eval z =
      (((evalZContact F z).coeff k).coeff j).coeff (i + 1) * ((i : Fld) + 1) := by
    rw [Polynomial.eval_mul, hev]
    simp only [Polynomial.eval_add, Polynomial.eval_natCast, Polynomial.eval_one]
  refine congrArg₂ (· + ·) h1 ?_
  cases k with
  | zero => simp only [↓reduceIte, Polynomial.coeff_zero, Polynomial.eval_zero]
  | succ k' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Polynomial.coeff_derivative]
      have hC1 : ((j : ℕ) : Polynomial (Polynomial Fld)) + 1 = Polynomial.C (((j : ℕ) : Polynomial Fld) + 1) := by
        simp only [map_add, map_natCast, map_one]
      have hC2 : ((j : ℕ) : Polynomial Fld) + 1 = Polynomial.C ((j : Fld) + 1) := by
        simp only [map_add, map_natCast, map_one]
      rw [hC1, hC2, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, Polynomial.eval_mul, hev]
      simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_natCast, Polynomial.eval_one]

/-- `contactDeriv` never increases `Z`-degree of coefficients! -/
lemma degZ_contactDeriv_le {F : ContactPoly (Polynomial Fld)} {D : ℕ}
    (hD : ∀ k j i, (((F.coeff k).coeff j).coeff i).natDegree ≤ D) (k j i : ℕ) :
    ((((contactDeriv F).coeff k).coeff j).coeff i).natDegree ≤ D := by
  rw [coeff_contactDeriv, Polynomial.coeff_add, Polynomial.coeff_add, coeff_dXBi, Polynomial.coeff_derivative]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact Polynomial.natDegree_mul_le.trans (by
      have h1 : (((i : ℕ) : Polynomial Fld) + 1).natDegree = 0 := by
        rw [show ((i : ℕ) : Polynomial Fld) + 1 = Polynomial.C ((i : Fld) + 1) by simp]
        exact Polynomial.natDegree_C _
      rw [h1, add_zero]; exact hD k j (i + 1))
  · cases k with
    | zero => simp
    | succ k' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Polynomial.coeff_derivative]
        rw [show ((j : ℕ) : Polynomial (Polynomial Fld)) + 1 = Polynomial.C (((j : ℕ) : Polynomial Fld) + 1) by simp,
          Polynomial.coeff_mul_C]
        exact Polynomial.natDegree_mul_le.trans (by
          have h1 : (((j : ℕ) : Polynomial Fld) + 1).natDegree = 0 := by
            rw [show ((j : ℕ) : Polynomial Fld) + 1 = Polynomial.C ((j : Fld) + 1) by simp]
            exact Polynomial.natDegree_C _
          rw [h1, add_zero]; exact hD k' (j + 1) i)

/-- Bound `deg_Z` of `Polynomial.resultant F G dF dG : BiPoly (Polynomial Fld)`. -/
lemma degZ_resultant_contact_le (F G : ContactPoly (Polynomial Fld)) (dF dG D : ℕ)
    (hF : ∀ k j i, (((F.coeff k).coeff j).coeff i).natDegree ≤ D)
    (hG : ∀ k j i, (((G.coeff k).coeff j).coeff i).natDegree ≤ D) (j i : ℕ) :
    ((((Polynomial.resultant F G dF dG).coeff j).coeff i).natDegree) ≤ (dF + dG) * D := by
  have hmul : ∀ (A B : BiPoly (Polynomial Fld)) (DA DB : ℕ),
      (∀ j' i', ((A.coeff j').coeff i').natDegree ≤ DA) →
      (∀ j' i', ((B.coeff j').coeff i').natDegree ≤ DB) →
      ∀ j' i', (((A * B).coeff j').coeff i').natDegree ≤ DA + DB := by
    intro A B DA DB hA hB j' i'
    rw [Polynomial.coeff_mul, finset_sum_coeff]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun x _ => ?_)
    dsimp only [Function.comp_apply]
    exact degZ_mul_poly_le (hA x.1) (hB x.2) i'
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → BiPoly (Polynomial Fld)),
      (∀ t ∈ s, ∀ j' i', (((f t).coeff j').coeff i').natDegree ≤ D) →
      ∀ j' i', ((((∏ t ∈ s, f t).coeff j').coeff i').natDegree) ≤ s.card * D := by
    classical
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty =>
        intro j' i'
        simp only [Finset.prod_empty, Polynomial.coeff_one, Finset.card_empty, zero_mul]
        split_ifs
        · simp only [Polynomial.coeff_one]; split_ifs
          · exact Nat.le_of_eq Polynomial.natDegree_one
          · exact Nat.le_of_eq Polynomial.natDegree_zero
        · simp only [Polynomial.coeff_zero, Polynomial.natDegree_zero, le_refl]
    | insert a s ha ih =>
        intro j' i'
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_one_mul]
        have h1 := hmul (f a) (∏ t ∈ s, f t) D (s.card * D) (hf a (Finset.mem_insert_self a s))
          (ih fun t ht => hf t (Finset.mem_insert_of_mem ht)) j' i'
        omega
  unfold Polynomial.resultant
  rw [Matrix.det_apply, finset_sum_coeff, finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  dsimp only [Function.comp_apply]
  have hsmul : ∀ (u : ℤˣ) (p : BiPoly (Polynomial Fld)),
      (((u • p).coeff j).coeff i).natDegree ≤ ((p.coeff j).coeff i).natDegree := fun u p => by
    rw [Units.smul_def]
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp only [Units.val_one, one_zsmul, le_refl]
    · simp only [Units.val_neg, Units.val_one, neg_zsmul, one_zsmul, Polynomial.coeff_neg, Polynomial.natDegree_neg, le_refl]
  refine (hsmul _ _).trans ?_
  refine (hprod Finset.univ (fun t => Polynomial.sylvester F G dF dG (σ t) t) (fun t _ j' i' => ?_) j i).trans
    (by simp only [Finset.card_univ, Fintype.card_fin, le_refl])
  simp only [Polynomial.sylvester, Matrix.of_apply]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) t
  · simp only [Fin.addCases_left]; split_ifs
    · exact hG _ j' i'
    · simp only [Polynomial.coeff_zero, Polynomial.natDegree_zero, Nat.zero_le]
  · simp only [Fin.addCases_right]; split_ifs
    · exact hF _ j' i'
    · simp only [Polynomial.coeff_zero, Polynomial.natDegree_zero, Nat.zero_le]

/-- **Irreducible `contactDeriv F ≠ 0` elimination (`deg_R = 1`, `q₀ ∈ {1, 2}`):**
Whenever `F ∈ ContactPoly (Polynomial Fld)` is irreducible with `F.natDegree = 1`,
`wdeg wY F ≤ 13345478` (so `deg_Y ≤ 12`), `deg_Z F ≤ 3850`, and `contactDeriv F ≠ 0`,
`Res_R(F, contactDeriv F)` eliminates `R` and gives `(S.card : ℚ) ≤ 10000000000000` (`10^13`)! -/
lemma card_le_of_contactDeriv_ne_zero
    (u₀ u₁ : Idx → Fld) {q₀ : ℕ} (hq₀ : q₀ = 1 ∨ q₀ = 2)
    {F : ContactPoly (Polynomial Fld)} (hirr : Irreducible F) (hFdeg : F.natDegree = 1)
    (hWF : wdeg wY F ≤ 13345478) (hDZ : ∀ k j i, (((F.coeff k).coeff j).coeff i).natDegree ≤ 3850)
    (hDne : contactDeriv F ≠ 0)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact F z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ (10000000000000 : ℚ) := by
  classical
  have hwY1 : 1 ≤ wY := by norm_num [wY]
  have hndvd : ¬ F ∣ contactDeriv F := by rw [dvd_contactDeriv_iff wY hwY1 hirr.ne_zero]; exact hDne
  let dD := (contactDeriv F).natDegree
  have hdD_le : dD ≤ 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro k hk
    rw [coeff_contactDeriv]
    have hk1 : F.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hk2 : F.coeff (k - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [hk1, hk2, dXBi_zero, Polynomial.derivative_zero, ite_self, add_zero]
  let R_el : BiPoly (Polynomial Fld) := Polynomial.resultant F (contactDeriv F) 1 dD
  have hRel_ne : R_el ≠ 0 := by
    have hprim : F.IsPrimitive := hirr.isPrimitive (by omega)
    let ι : BiPoly (Polynomial Fld) →+* FractionRing (BiPoly (Polynomial Fld)) :=
      algebraMap (BiPoly (Polynomial Fld)) (FractionRing (BiPoly (Polynomial Fld)))
    have hι : Function.Injective ι :=
      IsFractionRing.injective (BiPoly (Polynomial Fld)) (FractionRing (BiPoly (Polynomial Fld)))
    have hirrK : Irreducible (F.map ι) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hndvdK : ¬ F.map ι ∣ (contactDeriv F).map ι := fun h =>
      hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
    have hcop : IsCoprime (F.map ι) ((contactDeriv F).map ι) := by
      refine EuclideanDomain.isCoprime_of_dvd (x := F.map ι) (y := (contactDeriv F).map ι) (fun h => hirrK.ne_zero h.1) ?_
      intro p hp _ hpF hpD
      rcases hpF with ⟨q, hq⟩
      rcases hirrK.isUnit_or_isUnit hq with hu | hqu
      · exact hp hu
      · rcases hqu with ⟨u, hu⟩
        have hdvd_p : F.map ι ∣ p := ⟨(u⁻¹ : _), by rw [hq, ← hu, mul_assoc, Units.mul_inv, mul_one]⟩
        exact hndvdK (hdvd_p.trans hpD)
    intro h0
    have hresK : Polynomial.resultant (F.map ι) ((contactDeriv F).map ι)
        (F.map ι).natDegree ((contactDeriv F).map ι).natDegree = 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
        Polynomial.resultant_map_map, hFdeg, show Polynomial.resultant F (contactDeriv F) 1 dD = 0 from h0, map_zero]
    exact Polynomial.resultant_ne_zero _ _ hcop hresK
  have hRel_B : R_el.natDegree ≤ 36 := by
    have hW_D : wdeg wY (contactDeriv F) ≤ 13345478 := by
      have h1 := wdeg_contactDeriv_add_one_le wY hwY1 F hDne; omega
    have hdeg_coeff : ∀ (Q : ContactPoly (Polynomial Fld)), wdeg wY Q ≤ 13345478 → ∀ k, (Q.coeff k).natDegree ≤ 12 := by
      intro Q hWQ k
      by_cases hk : Q.coeff k = 0
      · simp [hk]
      · have h1 := wdegBiDom_le_of_wdeg_coeff hWQ k
        have h2 := wdegBiDom_ge_natDegree_mul wY (Q.coeff k) hk
        have hle := h2.trans h1
        have hw : wY = 1048575 := rfl
        rw [hw] at hle; omega
    unfold R_el Polynomial.resultant
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
    dsimp only [Function.comp_apply]
    have hsmul : ∀ (u : ℤˣ) (p : BiPoly (Polynomial Fld)), (u • p).natDegree ≤ p.natDegree := fun u p => by
      rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    refine (hsmul _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
    calc ∑ i : Fin (1 + dD), (Polynomial.sylvester F (contactDeriv F) 1 dD (σ i) i).natDegree
        ≤ ∑ _i : Fin (1 + dD), 12 := by
          apply Finset.sum_le_sum; intro i _
          simp only [Polynomial.sylvester, Matrix.of_apply]
          refine Fin.addCases (fun r => ?_) (fun r => ?_) i
          · simp only [Fin.addCases_left]; split_ifs
            · exact hdeg_coeff _ hW_D _
            · simp
          · simp only [Fin.addCases_right]; split_ifs
            · exact hdeg_coeff F hWF _
            · simp
      _ = (1 + dD) * 12 := by simp
      _ ≤ 36 := by omega
  have hRel_H : ∀ j a, ((R_el.coeff j).coeff a).natDegree ≤ 11550 := fun j a =>
    (degZ_resultant_contact_le F (contactDeriv F) 1 dD 3850 hDZ (degZ_contactDeriv_le hDZ) j a).trans
      (by omega)
  have hcurve : ∀ z ∈ S, triEval R_el z (P z) = 0 := by
    intro z hz
    have hFP := hFvan z hz
    have hDP : evalContact (evalZContact (contactDeriv F) z) (P z) = 0 := by
      rw [evalZContact_contactDeriv, evalContact_contactDeriv, hFP, Polynomial.derivative_zero]
    exact triEval_resultant_eq_zero F (contactDeriv F) 1 dD (le_of_eq hFdeg) le_rfl (by omega) z (P z) hFP hDP
  have hark := card_le_of_biPoly_pow u₀ u₁ q₀ (by rcases hq₀ with rfl | rfl <;> omega)
    R_el 36 11550 hRel_ne hRel_B hRel_H S P Az hP hcurve hcard hmatch hbad
  refine hark.trans (max_le (by norm_num) ?_)
  rcases hq₀ with rfl | rfl <;> (unfold arklibBoundPowQ; norm_num [N, wY, A])

/-- **Frobenius Descent for Irreducible `deg_R = 2, F.coeff 1 = 0` (`F ∈ ker(D)`):**
Descends `F(Z, X, Y, R)` via `Z = w^2` to `H(w, X, Y, R)^2 = F(w^2, X, Y, R)` with
`deg_R H = 1`, `wdeg H = W_F / 2 < 13 * wY`, and `wYZ 2 H ≤ 3850`, then dispatches `H`'s
factors via `deg1_factor_card_le` (`q₀ = 2`) and `card_le_of_contactDeriv_ne_zero`! -/
lemma card_le_of_deg2_coeff1_zero
    (u₀ u₁ : Idx → Fld) {F : ContactPoly (Polynomial Fld)}
    (hD : contactDeriv F = 0) (hFdeg : F.natDegree = 2) (hf1 : F.coeff 1 = 0)
    (hWF : wdeg wY F ≤ 2 * A * 9 - 1) (hWYZ : wYZ 1 F ≤ 3850)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact F z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ ((T4_Q2_SUM + 80000231000 + 15000000000000 : ℕ) : ℚ) := by
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
    have hN : 2 * A * 9 - 1 = 26690957 := by norm_num [A]
    omega
  have hH_wYZ : wYZ 2 H ≤ 3850 := wYZ_frobenius_descent hH_sq hWYZ
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
  -- `G0` bound: `wdegBi G0 ≤ 13345478 ⇒ deg_Y G0 ≤ 12`, `deg_Z G0 ≤ 3850`!
  have hG0_wdeg : wdeg wY (Polynomial.C G0) ≤ 13345478 := by
    have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hH1_irr.ne_zero uH.ne_zero)
    rw [← mul_assoc, hH_eq_prod] at h1; omega
  have hG0_deg : G0.natDegree ≤ 12 := by
    have h1 : wdegBiDom wY G0 ≤ 13345478 := by simpa using wdegBiDom_le_of_wdeg_coeff hG0_wdeg 0
    have h2 := wdegBiDom_ge_natDegree_mul wY G0 hG0_ne
    have hle := h2.trans h1
    have hw : wY = 1048575 := rfl
    rw [hw] at hle; omega
  have hG0_wYZ : wYZ 2 (Polynomial.C G0) ≤ 3850 := by
    have h1 := wYZ_mul 2 (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hH1_irr.ne_zero uH.ne_zero)
    rw [← mul_assoc, hH_eq_prod] at h1; omega
  have hSW0_card : (SW0.card : ℚ) ≤ (1000000000000 : ℚ) := by
    have hark := card_le_of_biPoly_pow u₀ u₁ 2 (by omega) G0 12 3850 hG0_ne hG0_deg
      (fun j a => by simpa only [Polynomial.coeff_C_zero] using natDegree_Z_le_of_wYZ hG0_wYZ 0 j a) SW0 PW AzW
      (fun w hw => hP (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      (fun w hw => (Finset.mem_filter.mp hw).2)
      (fun w hw => hcard (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      (fun w hw i hi => (hmatch (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1) i).mp hi)
      (fun w hw => hbad (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
    refine hark.trans (max_le (by norm_num) ?_)
    unfold arklibBoundPowQ; norm_num [N, wY, A]
  -- `H1` bound: split on `contactDeriv H1 = 0`!
  have hH1_wdeg : wdeg wY H1 ≤ 13345478 := by
    have h1 := wdeg_mul wY hH1_irr.ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hG0_ne) uH.ne_zero)
    have hEq : H1 * (Polynomial.C G0 * (uH : ContactPoly (Polynomial Fld))) = H := by rw [← hH_eq_prod]; ring
    rw [hEq] at h1; omega
  have hH1_wYZ : wYZ 2 H1 ≤ 3850 := by
    have h1 := wYZ_mul 2 hH1_irr.ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hG0_ne) uH.ne_zero)
    have hEq : H1 * (Polynomial.C G0 * (uH : ContactPoly (Polynomial Fld))) = H := by rw [← hH_eq_prod]; ring
    rw [hEq] at h1; omega
  have hSW1_card : (SW1.card : ℚ) ≤ ((T4_Q2_SUM + 80000231000 + 10000000000000 : ℕ) : ℚ) := by
    by_cases hDH1 : contactDeriv H1 = 0
    · set WH1 := wdeg wY H1
      obtain ⟨h_coord, hH1_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := WH1) (s := 1) (by norm_num [wY]) H1).mp ⟨hDH1, le_of_eq hH1_deg, le_rfl⟩
      have hWH1_13 : (WH1 : ℚ) / (wY : ℚ) < 13 := by
        have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
        rw [div_lt_iff₀ hwQ]
        have h1 : (WH1 : ℚ) ≤ 13345478 := by exact_mod_cast hH1_wdeg
        norm_num [wY]; linarith
      have hbound := deg1_factor_card_le u₀ u₁ (W_F := WH1) (D_ZF := 3850) (q₀ := 2)
        (Or.inr rfl) (by linarith) (fun _ => ⟨hWH1_13, le_rfl⟩) h_coord
        (by rw [← hH1_eq]; exact irreducible_liftCRat_of_irred hH1_irr (by omega))
        (by rw [← hH1_eq]; exact hH1_deg) (by rw [← hH1_eq]) (by rw [← hH1_eq]; exact hH1_wYZ)
        SW1 PW AzW
        (fun w hw => hP (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw => by rw [← hH1_eq]; exact (Finset.mem_filter.mp hw).2)
        (fun w hw => hcard (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw i => hmatch (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1) i)
        (fun w hw => hbad (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hbound
      push_cast at hbound ⊢; linarith
    · have hcd := card_le_of_contactDeriv_ne_zero u₀ u₁ (Or.inr rfl) hH1_irr hH1_deg hH1_wdeg
        (natDegree_Z_le_of_wYZ hH1_wYZ) hDH1 SW1 PW AzW
        (fun w hw => hP (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw => (Finset.mem_filter.mp hw).2)
        (fun w hw => hcard (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
        (fun w hw i hi => (hmatch (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1) i).mp hi)
        (fun w hw => hbad (w ^ 2) (hSW_mem w (Finset.mem_filter.mp hw).1))
      push_cast; linarith
  have hS_le : S.card ≤ SW0.card + SW1.card := by
    rw [← hSW_card]; exact (Finset.card_le_card hSW_cover).trans (Finset.card_union_le _ _)
  have hSQ : (S.card : ℚ) ≤ (SW0.card : ℚ) + (SW1.card : ℚ) := by exact_mod_cast hS_le
  push_cast at hSW1_card ⊢; linarith

/-! ### Part 2: Master `LineExactAgreementBound` and `ProtocolClaim 6401` -/

/-- **Master Line Exact-Agreement Bound (`mcaCap = 18.4 · 10^18`):**
For ANY pair of received words `u₀ u₁ : Idx → Fld`, at most `18,400,000,000,000,000,000`
challenges `z ∈ Fld` admit a degree-`≤ wY` polynomial `P` agreeing with `u₀ + z · u₁` on `≥ A`
points without decomposing as an exact correlated pair `P₀ + C z * P₁`! -/
theorem lineExactAgreementBound_6401 :
    LineExactAgreementBound BinaryIRSProfile.domain (wY + 1) A (18400000000000000000 : ℝ) := by
  intro u₀ u₁
  let agr (z : Fld) (Q : Polynomial Fld) : Finset Idx :=
    polynomialAgreementSet BinaryIRSProfile.domain (fun i => u₀ i + z * u₁ i) Q
  let pred (z : Fld) : Prop :=
    ∃ P : Polynomial Fld, P.natDegree ≤ wY ∧
      A ≤ (agr z P).card ∧ BadOn6401 u₀ u₁ (agr z P)
  classical
  let S : Finset Fld := Set.toFinset {z : Fld | pred z}
  have hS_mem : ∀ z : Fld, z ∈ S ↔ pred z := fun z => by
    simp only [S, Set.mem_toFinset, Set.mem_setOf_eq]
  have hS_card : (S.card : ℚ) ≤ (18400000000000000000 : ℚ) := by
    -- Pick one bad witness `P z` for each `z ∈ S`!
    let P (z : Fld) : Polynomial Fld :=
      if hz : z ∈ S then Classical.choose ((hS_mem z).mp hz) else 0
    let Az (z : Fld) : Finset Idx := agr z (P z)
    have hPspec : ∀ z ∈ S, (P z).natDegree ≤ wY ∧ A ≤ (Az z).card ∧ BadOn6401 u₀ u₁ (Az z) := by
      intro z hz; simp only [P, Az, dif_pos hz]
      exact Classical.choose_spec ((hS_mem z).mp hz)
    have hmatch : ∀ z ∈ S, ∀ i : Idx, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i :=
      fun z _ i => by simp only [Az, agr, mem_polynomialAgreementSet]
    -- Global weighted `ker(D)` contact interpolation (`m0 = 9, s0 = 2, W0 = 26690957, D_ZF = 3850`)!
    let W0 : ℕ := 2 * A * 9 - 1
    have hsurp : Fintype.card Idx * rankKerD 9 2 * (3850 + 1) + 1 * yWeightSum wY W0 2 <
        varsKerDExact wY W0 2 * (3850 + 1) := by
      have hcardI : Fintype.card Idx = 2097152 := BinaryIRSProfile.card_index
      have hwY_eq : wY = 1048575 := rfl
      have hW0_eq : W0 = 2 * 1482831 * 9 - 1 := rfl
      rw [hcardI, hwY_eq, hW0_eq]
      exact global_surplus_6401_wtd
    obtain ⟨Q, q_coord, hQ_eq, hQ_ne, hQ_D, hQ_deg, hQ_wdeg, hQ_wYZ, _, hQ_van⟩ :=
      exists_global_contact_interpolant_wtd BinaryIRSProfile.domain (linePow u₀ u₁ 1)
        (dy := 1) (wY := wY) (W0 := W0) (s0 := 2) (m0 := 9) (D_ZF := 3850)
        (by norm_num [wY]) (fun i => linePow_natDegree_le u₀ u₁ 1 i)
        (by norm_num [W0, A, wY]) hsurp
    have hQ_eval : ∀ z ∈ S, evalContact (evalZContact Q z) (P z) = 0 := by
      intro z hz
      rw [hQ_eq]
      refine evalContact_eq_zero_of_global_coords BinaryIRSProfile.domain (linePow u₀ u₁ 1)
        (by norm_num [wY]) (by norm_num [W0, A]) q_coord hQ_van z (P z) (hPspec z hz).1
        (Az z) (hPspec z hz).2.1 ?_
      intro i hi; rw [eval_linePow, pow_one]; exact (hmatch z hz i).mp hi
    -- UFD factorization of `Q` in `ContactPoly (Polynomial Fld)`!
    let facs := UniqueFactorizationMonoid.normalizedFactors Q
    let facs0 := facs.filter fun F => F.natDegree = 0
    let facs1 := facs.filter fun F => 1 ≤ F.natDegree
    have hfacs_split : facs = facs0 + facs1 := by
      ext F; simp only [facs0, facs1, Multiset.count_add, Multiset.count_filter]
      by_cases h0 : F.natDegree = 0
      · simp [h0]
      · simp [h0, show 1 ≤ F.natDegree by omega]
    obtain ⟨uQ, huQ⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ_ne
    have hQ_fac : facs0.prod * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q := by
      rw [← Multiset.prod_add, ← hfacs_split]; exact huQ
    have hfacs0_deg0 : facs0.prod.natDegree = 0 := by
      have hgen : ∀ m : Multiset (ContactPoly (Polynomial Fld)), (∀ F ∈ m, F.natDegree = 0) → m.prod.natDegree = 0 := by
        intro m; induction m using Multiset.induction_on with
        | empty => intro _; simp
        | cons a s ih =>
            intro h; rw [Multiset.prod_cons]
            exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_mul_le.trans
              (by rw [h a (Multiset.mem_cons_self a s), ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]))
      exact hgen facs0 fun F hF => (Multiset.mem_filter.mp hF).2
    let G0 : BiPoly (Polynomial Fld) := facs0.prod.coeff 0
    have hfacs0_eq : facs0.prod = Polynomial.C G0 := Polynomial.eq_C_of_natDegree_eq_zero hfacs0_deg0
    have hG0_ne : G0 ≠ 0 := fun h0 => hQ_ne (by rw [← hQ_fac, hfacs0_eq, h0, map_zero, zero_mul, zero_mul])
    have hf1p_ne : facs1.prod ≠ 0 := fun h0 => hQ_ne (by rw [← hQ_fac, h0, mul_zero, zero_mul])
    have hG0_wdeg : wdeg wY (Polynomial.C G0) ≤ W0 := by
      have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hf1p_ne uQ.ne_zero)
      rw [← mul_assoc, show Polynomial.C G0 * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q by
        rw [← hfacs0_eq, hQ_fac]] at h1; omega
    have hG0_deg : G0.natDegree ≤ 25 := by
      have h1 : wdegBiDom wY G0 ≤ W0 := by simpa using wdegBiDom_le_of_wdeg_coeff hG0_wdeg 0
      have h2 := wdegBiDom_ge_natDegree_mul wY G0 hG0_ne
      have hle := h2.trans h1
      have hW0 : W0 = 26690957 := by norm_num [W0, A]
      have hw : wY = 1048575 := rfl
      rw [hw] at hle; omega
    have hG0_wYZ : wYZ 1 (Polynomial.C G0) ≤ 3850 := by
      have h1 := wYZ_mul 1 (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hf1p_ne uQ.ne_zero)
      rw [← mul_assoc, show Polynomial.C G0 * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q by
        rw [← hfacs0_eq, hQ_fac]] at h1; omega
    -- Bound `S0` (roots of `G0`): `≤ 10^12`!
    let S0 := S.filter fun z => triEval G0 z (P z) = 0
    have hS0_card : (S0.card : ℚ) ≤ (1000000000000 : ℚ) := by
      have hark := card_le_of_biPoly_pow u₀ u₁ 1 le_rfl G0 25 3850 hG0_ne hG0_deg
        (fun j a => by simpa only [Polynomial.coeff_C_zero] using natDegree_Z_le_of_wYZ hG0_wYZ 0 j a) S0 P Az
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
        (fun z hz i hi => by simpa only [pow_one] using (hmatch z (Finset.mem_filter.mp hz).1 i).mp hi)
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
      refine hark.trans (max_le (by norm_num) ?_)
      unfold arklibBoundPowQ; norm_num [N, wY, A]
    -- Every `z ∈ S` lies in `S0` or `SF F` for some `F ∈ facs1`!
    let SF (F : ContactPoly (Polynomial Fld)) : Finset Fld := S.filter fun z => evalContact (evalZContact F z) (P z) = 0
    have hS_cover : ∀ z ∈ S, z ∈ S0 ∨ ∃ F ∈ facs1, z ∈ SF F := by
      intro z hz
      have h0 := hQ_eval z hz
      rw [← hQ_fac] at h0
      have hmulZ : ∀ A B : ContactPoly (Polynomial Fld), evalZContact (A * B) z = evalZContact A z * evalZContact B z :=
        fun A B => by unfold evalZContact; exact Polynomial.map_mul _
      rw [hmulZ, hmulZ, evalContact_mul, evalContact_mul, hfacs0_eq] at h0
      have hu_ne : evalContact (evalZContact (uQ : ContactPoly (Polynomial Fld)) z) (P z) ≠ 0 := by
        rcases uQ.isUnit with ⟨v, hv⟩; intro h0'
        have h1 := congrArg (fun q => evalContact (evalZContact q z) (P z)) v.mul_inv
        rw [hmulZ, evalContact_mul, hv, h0', zero_mul] at h1
        have : evalContact (evalZContact (1 : ContactPoly (Polynomial Fld)) z) (P z) = 1 := by
          unfold evalZContact evalContact; simp
        rw [this] at h1; exact one_ne_zero h1.symm
      rcases mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hu_ne) with hG | hFprod
      · left; exact Finset.mem_filter.mpr ⟨hz, by simpa [evalZContact, evalContact, triEval] using hG⟩
      · right
        have hgen : ∀ m : Multiset (ContactPoly (Polynomial Fld)),
            evalContact (evalZContact m.prod z) (P z) = 0 → ∃ F ∈ m, evalContact (evalZContact F z) (P z) = 0 := by
          intro m; induction m using Multiset.induction_on with
          | empty => intro h; unfold evalZContact evalContact at h; simp at h
          | cons a s ih =>
              intro h; rw [Multiset.prod_cons, hmulZ, evalContact_mul] at h
              rcases mul_eq_zero.mp h with ha | hs
              · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
              · obtain ⟨F, hF, hv⟩ := ih hs; exact ⟨F, Multiset.mem_cons_of_mem hF, hv⟩
        obtain ⟨F, hF, hv⟩ := hgen facs1 hFprod
        exact ⟨F, hF, Finset.mem_filter.mpr ⟨hz, hv⟩⟩
    -- Helper: bound ANY `F ∈ facs1` of `natDegree = 1` with `wYZ 1 F ≤ D_ZF`!
    have hdeg1_bound : ∀ F ∈ facs1, F.natDegree = 1 →
        ((SF F).card : ℚ) ≤
          ((T4_C1_SUM + 15000060 : ℕ) : ℚ) * (wYZ 1 F : ℚ) + ((T4_C0_SUM + 2000000 + 10000000000000 : ℕ) : ℚ) := by
      intro F hF hF1
      have hF_irr : Irreducible F := UniqueFactorizationMonoid.irreducible_of_normalized_factor F (Multiset.mem_filter.mp hF).1
      have hF_dvd : F ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_filter.mp hF).1
      rcases hF_dvd with ⟨Q', hQ'⟩
      have hQ'_ne : Q' ≠ 0 := fun h0 => hQ_ne (by rw [hQ', h0, mul_zero])
      have hWF_le : wdeg wY F ≤ W0 := by
        have := wdeg_mul wY hF_irr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
      have hWYZ_le : wYZ 1 F ≤ 3850 := by
        have := wYZ_mul 1 hF_irr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
      by_cases hDF : contactDeriv F = 0
      · set W_F := wdeg wY F
        obtain ⟨f_coord, hF_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 1) (by norm_num [wY]) F).mp ⟨hDF, le_of_eq hF1, le_rfl⟩
        have hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2 := by
          have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
          rw [div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)]
          have h1 : (W_F : ℚ) ≤ 26690957 := by exact_mod_cast (show W_F ≤ 26690957 by simpa [W0, A] using hWF_le)
          norm_num [wY]; linarith
        have hbd := deg1_factor_card_le u₀ u₁ (W_F := W_F) (D_ZF := wYZ 1 F) (q₀ := 1)
          (Or.inl rfl) hWF_hi (fun h => by cases h) f_coord
          (by rw [← hF_eq]; exact irreducible_liftCRat_of_irred hF_irr (by omega))
          (by rw [← hF_eq]; exact hF1) (by rw [← hF_eq]) (by rw [← hF_eq])
          (SF F) P Az
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
          (fun z hz => by rw [← hF_eq]; exact (Finset.mem_filter.mp hz).2)
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
          (fun z hz i => by simpa only [pow_one] using hmatch z (Finset.mem_filter.mp hz).1 i)
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
        simp only [↓reduceIte] at hbd
        push_cast at hbd ⊢; linarith
      · -- `contactDeriv F ≠ 0` ⇒ `F^2 ∣ Q` ⇒ `2 * wdeg wY F ≤ W0`, so `wdeg wY F ≤ 13345478`!
        have hF_dvd_Q' : F ∣ Q' := by
          have h0 : contactDeriv F * Q' + F * contactDeriv Q' = 0 := by
            rw [← contactDeriv_mul, ← hQ', hQ_D]
          have hF_dvd_prod : F ∣ contactDeriv F * Q' := ⟨contactDeriv Q', by
            have h2 : ∀ a : ContactPoly (Polynomial Fld), a + a = 0 := CharTwo.add_self_eq_zero
            calc contactDeriv F * Q' = contactDeriv F * Q' + (F * contactDeriv Q' + F * contactDeriv Q') := by rw [h2, add_zero]
              _ = (contactDeriv F * Q' + F * contactDeriv Q') + F * contactDeriv Q' := by ring
              _ = F * contactDeriv Q' := by rw [h0, zero_add]⟩
          have hF_prime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF_irr
          have hndvd : ¬ F ∣ contactDeriv F := by
            rw [dvd_contactDeriv_iff wY (by norm_num [wY]) hF_irr.ne_zero]; exact hDF
          exact (hF_prime.dvd_or_dvd hF_dvd_prod).resolve_left hndvd
        rcases hF_dvd_Q' with ⟨Q'', hQ''⟩
        have hQ''_ne : Q'' ≠ 0 := fun h0 => hQ'_ne (by rw [hQ'', h0, mul_zero])
        have hWF_half : wdeg wY F ≤ 13345478 := by
          have h1 := wdeg_mul wY (mul_ne_zero hF_irr.ne_zero hF_irr.ne_zero) hQ''_ne
          rw [wdeg_mul wY hF_irr.ne_zero hF_irr.ne_zero, mul_assoc, ← hQ'', ← hQ'] at h1
          have hW0 : W0 = 26690957 := by norm_num [W0, A]
          omega
        have hcd := card_le_of_contactDeriv_ne_zero u₀ u₁ (Or.inl rfl) hF_irr hF1 hWF_half
          (natDegree_Z_le_of_wYZ hWYZ_le) hDF (SF F) P Az
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
          (fun z hz => (Finset.mem_filter.mp hz).2)
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
          (fun z hz i hi => by simpa only [pow_one] using (hmatch z (Finset.mem_filter.mp hz).1 i).mp hi)
          (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
        have hnn : (0 : ℚ) ≤ (wYZ 1 F : ℚ) := Nat.cast_nonneg _
        push_cast; nlinarith
    -- Now case split on `facs1.prod.natDegree ≤ 2` (`facs1.card ∈ {0, 1, 2}`)!
    have hfacs1_prod_deg : facs1.prod.natDegree ≤ 2 := by
      have hu0 : (uQ : ContactPoly (Polynomial Fld)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit uQ.isUnit
      have h1 : (facs0.prod * facs1.prod * (uQ : ContactPoly (Polynomial Fld))).natDegree = facs1.prod.natDegree := by
        rw [Polynomial.natDegree_mul (mul_ne_zero (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) hf1p_ne) uQ.ne_zero,
          Polynomial.natDegree_mul (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) hf1p_ne, hfacs0_deg0, hu0, zero_add, add_zero]
      rw [hQ_fac] at h1; omega
    have hfacs1_card_le2 : facs1.card ≤ 2 := by
      have hsum : ∀ m : Multiset (ContactPoly (Polynomial Fld)), (∀ F ∈ m, Irreducible F ∧ 1 ≤ F.natDegree) →
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
      exact (hsum facs1 fun F hF => ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor F
        (Multiset.mem_filter.mp hF).1, (Multiset.mem_filter.mp hF).2⟩).trans hfacs1_prod_deg
    rcases (show facs1.card = 0 ∨ facs1.card = 1 ∨ facs1.card = 2 by omega) with hc0 | hc1 | hc2
    · -- 0 factors of `deg_R ≥ 1`: `S ⊆ S0`!
      have he : facs1 = 0 := Multiset.card_eq_zero.mp hc0
      have hsub : S ⊆ S0 := fun z hz => (hS_cover z hz).resolve_right (by simp [he])
      have hle : (S.card : ℚ) ≤ (S0.card : ℚ) := by exact_mod_cast Finset.card_le_card hsub
      linarith
    · -- 1 factor `F` of `deg_R ∈ {1, 2}`!
      obtain ⟨F, hF_eq⟩ := Multiset.card_eq_one.mp hc1
      have hF_mem : F ∈ facs1 := by rw [hF_eq]; exact Multiset.mem_singleton_self F
      have hF_irr : Irreducible F := UniqueFactorizationMonoid.irreducible_of_normalized_factor F (Multiset.mem_filter.mp hF_mem).1
      have hF_deg1 : 1 ≤ F.natDegree := (Multiset.mem_filter.mp hF_mem).2
      have hF_deg2 : F.natDegree ≤ 2 := by simpa [hF_eq] using hfacs1_prod_deg
      have hsub : S ⊆ S0 ∪ SF F := fun z hz => by
        rcases hS_cover z hz with h0 | ⟨F', hF', hv⟩
        · exact Finset.mem_union_left _ h0
        · rw [hF_eq, Multiset.mem_singleton] at hF'; subst hF'; exact Finset.mem_union_right _ hv
      have hS_le : (S.card : ℚ) ≤ (S0.card : ℚ) + ((SF F).card : ℚ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hF_dvd : F ∣ Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_filter.mp hF_mem).1
      rcases hF_dvd with ⟨Q', hQ'⟩
      have hQ'_ne : Q' ≠ 0 := fun h0 => hQ_ne (by rw [hQ', h0, mul_zero])
      have hWF_le : wdeg wY F ≤ W0 := by have := wdeg_mul wY hF_irr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
      have hWYZ_le : wYZ 1 F ≤ 3850 := by have := wYZ_mul 1 hF_irr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
      rcases (show F.natDegree = 1 ∨ F.natDegree = 2 by omega) with hd1 | hd2
      · have h1 := hdeg1_bound F hF_mem hd1
        have hDZQ : (wYZ 1 F : ℚ) ≤ 3850 := by exact_mod_cast hWYZ_le
        norm_num [T4_C1_SUM, T4_C0_SUM] at h1; linarith
      · -- `F.natDegree = 2`: `contactDeriv F` MUST be `0` (otherwise `F^2 ∣ Q` gives `4 ≤ 2`)!
        have hDF : contactDeriv F = 0 := by
          by_contra hDne
          have h0 : contactDeriv F * Q' + F * contactDeriv Q' = 0 := by rw [← contactDeriv_mul, ← hQ', hQ_D]
          have hF_dvd_prod : F ∣ contactDeriv F * Q' := ⟨contactDeriv Q', by
            have h2 : ∀ a : ContactPoly (Polynomial Fld), a + a = 0 := CharTwo.add_self_eq_zero
            calc contactDeriv F * Q' = contactDeriv F * Q' + (F * contactDeriv Q' + F * contactDeriv Q') := by rw [h2, add_zero]
              _ = (contactDeriv F * Q' + F * contactDeriv Q') + F * contactDeriv Q' := by ring
              _ = F * contactDeriv Q' := by rw [h0, zero_add]⟩
          have hndvd : ¬ F ∣ contactDeriv F := by rw [dvd_contactDeriv_iff wY (by norm_num [wY]) hF_irr.ne_zero]; exact hDne
          have hF_prime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF_irr
          rcases (hF_prime.dvd_or_dvd hF_dvd_prod).resolve_left hndvd with ⟨Q'', hQ''⟩
          have hQ''_ne : Q'' ≠ 0 := fun h0 => hQ'_ne (by rw [hQ'', h0, mul_zero])
          have h4 := Polynomial.natDegree_mul (mul_ne_zero hF_irr.ne_zero hF_irr.ne_zero) hQ''_ne
          rw [Polynomial.natDegree_mul hF_irr.ne_zero hF_irr.ne_zero, mul_assoc, ← hQ'', ← hQ'] at h4
          omega
        by_cases hf1 : F.coeff 1 = 0
        · have hfrob := card_le_of_deg2_coeff1_zero u₀ u₁ hDF hd2 hf1 hWF_le hWYZ_le (SF F) P Az
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
            (fun z hz => (Finset.mem_filter.mp hz).2)
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
            (fun z hz i => hmatch z (Finset.mem_filter.mp hz).1 i)
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
          have hfrobQ : ((SF F).card : ℚ) ≤ 18257795175188565552 := by
            norm_num [T4_Q2_SUM] at hfrob; exact_mod_cast hfrob
          linarith
        · set W_F := wdeg wY F
          obtain ⟨f_coord, hF_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 2) (by norm_num [wY]) F).mp ⟨hDF, le_of_eq hd2, le_rfl⟩
          have hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2 := by
            have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
            rw [div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)]
            have h1 : (W_F : ℚ) ≤ 26690957 := by exact_mod_cast (show W_F ≤ 26690957 by simpa [W0, A] using hWF_le)
            norm_num [wY]; linarith
          have hd2_bd := deg2_factor_card_le u₀ u₁ hWF_hi hWYZ_le f_coord
            (by rw [← hF_eq]; exact irreducible_liftCRat_of_irred hF_irr (by omega))
            (by rw [← hF_eq]; exact hd2) (by rw [← hF_eq]; exact hf1) (by rw [← hF_eq]) (by rw [← hF_eq])
            (SF F) P Az
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
            (fun z hz => by rw [← hF_eq]; exact (Finset.mem_filter.mp hz).2)
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
            (fun z hz i => hmatch z (Finset.mem_filter.mp hz).1 i)
            (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
          have hd2Q : ((SF F).card : ℚ) ≤ 10000008000000200200 := by
            norm_num [T3_CAP_BOUND] at hd2_bd; exact_mod_cast hd2_bd
          linarith
    · -- 2 factors `F1, F2` of `deg_R = 1` with `wYZ 1 F1 + wYZ 1 F2 ≤ 3850`!
      have hne1 : facs1 ≠ 0 := fun h => by simp [h] at hc2
      obtain ⟨F1, hF1_mem0⟩ := Multiset.exists_mem_of_ne_zero hne1
      let r1 := facs1.erase F1
      have hr1 : facs1 = F1 ::ₘ r1 := (Multiset.cons_erase hF1_mem0).symm
      have hr1_card : r1.card = 1 := by rw [hr1, Multiset.card_cons] at hc2; omega
      obtain ⟨F2, hr2⟩ := Multiset.card_eq_one.mp hr1_card
      have hfacs1_pair : facs1 = {F1, F2} := by rw [hr1, hr2]; rfl
      have hF1_mem : F1 ∈ facs1 := by rw [hfacs1_pair]; simp
      have hF2_mem : F2 ∈ facs1 := by rw [hfacs1_pair]; simp
      have hF1_irr : Irreducible F1 := UniqueFactorizationMonoid.irreducible_of_normalized_factor F1 (Multiset.mem_filter.mp hF1_mem).1
      have hF2_irr : Irreducible F2 := UniqueFactorizationMonoid.irreducible_of_normalized_factor F2 (Multiset.mem_filter.mp hF2_mem).1
      have hprod_eq : facs1.prod = F1 * F2 := by rw [hfacs1_pair]; simp
      have hF1_deg : F1.natDegree = 1 := by
        have h1 : 1 ≤ F1.natDegree := (Multiset.mem_filter.mp hF1_mem).2
        have h2 : 1 ≤ F2.natDegree := (Multiset.mem_filter.mp hF2_mem).2
        have hm := Polynomial.natDegree_mul hF1_irr.ne_zero hF2_irr.ne_zero
        rw [← hprod_eq] at hm; omega
      have hF2_deg : F2.natDegree = 1 := by
        have h1 : 1 ≤ F1.natDegree := (Multiset.mem_filter.mp hF1_mem).2
        have h2 : 1 ≤ F2.natDegree := (Multiset.mem_filter.mp hF2_mem).2
        have hm := Polynomial.natDegree_mul hF1_irr.ne_zero hF2_irr.ne_zero
        rw [← hprod_eq] at hm; omega
      have hWYZ_sum : wYZ 1 F1 + wYZ 1 F2 ≤ 3850 := by
        have h1 := wYZ_mul 1 (mul_ne_zero hF1_irr.ne_zero hF2_irr.ne_zero)
          (mul_ne_zero (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) uQ.ne_zero)
        rw [wYZ_mul 1 hF1_irr.ne_zero hF2_irr.ne_zero] at h1
        have hEq : F1 * F2 * (facs0.prod * (uQ : ContactPoly (Polynomial Fld))) = Q := by
          rw [← hQ_fac, hprod_eq]; ring
        rw [hEq] at h1; omega
      have hsub : S ⊆ S0 ∪ (SF F1 ∪ SF F2) := fun z hz => by
        rcases hS_cover z hz with h0 | ⟨F', hF', hv⟩
        · exact Finset.mem_union_left _ h0
        · rw [hr1, hr2, Multiset.mem_cons, Multiset.mem_singleton] at hF'
          rcases hF' with rfl | rfl
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ hv)
      have hS_le : (S.card : ℚ) ≤ (S0.card : ℚ) + ((SF F1).card : ℚ) + ((SF F2).card : ℚ) := by
        have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_union_le _ _) _))
        exact_mod_cast (show S.card ≤ S0.card + (SF F1).card + (SF F2).card by omega)
      have hb1 := hdeg1_bound F1 hF1_mem hF1_deg
      have hb2 := hdeg1_bound F2 hF2_mem hF2_deg
      have hsumQ : (wYZ 1 F1 : ℚ) + (wYZ 1 F2 : ℚ) ≤ 3850 := by exact_mod_cast hWYZ_sum
      norm_num [T4_C1_SUM, T4_C0_SUM] at hb1 hb2
      linarith
  -- Convert `S` into `LineExactAgreementBound`!
  have hS_nat : S.card ≤ 18400000000000000000 := by exact_mod_cast hS_card
  refine ⟨S, by exact_mod_cast hS_nat, ?_⟩
  intro z hz P hPdeg hA
  have hPnat : P.natDegree ≤ wY := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg; omega
  have hnot_bad : ¬ BadOn6401 u₀ u₁ (agr z P) := by
    intro hbad
    exact hz ((hS_mem z).mpr ⟨P, hPnat, hA, hbad⟩)
  unfold BadOn6401 at hnot_bad; push Not at hnot_bad
  obtain ⟨P₀, P₁, hP₀_deg, hP₁_deg, hagree⟩ := hnot_bad
  have hP₀_lt : P₀.degree < (wY + 1 : ℕ) := by
    by_cases h0 : P₀ = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)
  have hP₁_lt : P₁.degree < (wY + 1 : ℕ) := by
    by_cases h0 : P₁ = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)
  have hP_eq : P = P₀ + Polynomial.C z * P₁ := by
    let D := P - (P₀ + Polynomial.C z * P₁)
    have hD_deg : D.natDegree ≤ wY := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le hPnat ?_)
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hP₀_deg ((Polynomial.natDegree_C_mul_le _ _).trans hP₁_deg))
    have hD_zero : D = 0 := by
      by_contra hDne
      let roots_im := (agr z P).image BinaryIRSProfile.domain
      have hsub : roots_im ⊆ D.roots.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hDne, Polynomial.IsRoot.def]
        have hPi : P.eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i :=
          (mem_polynomialAgreementSet _ _ _ _).mp hi
        have ⟨h0i, h1i⟩ := hagree i hi
        simp [D, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hPi, h0i, h1i]
      have hcard_r : A ≤ D.natDegree := by
        calc A ≤ (agr z P).card := hA
          _ = roots_im.card := (Finset.card_image_of_injective _ BinaryIRSProfile.domain.injective).symm
          _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ D.roots.card := Multiset.toFinset_card_le _
          _ ≤ D.natDegree := Polynomial.card_roots' D
      norm_num [A, wY] at hcard_r hD_deg; omega
    exact sub_eq_zero.mp hD_zero
  refine ⟨P₀, P₁, hP₀_lt, hP₁_lt, hP_eq, ?_⟩
  ext i
  rw [mem_polynomialAgreementSet, mem_commonPolynomialAgreementSet]
  constructor
  · intro hi; exact hagree i ((mem_polynomialAgreementSet _ _ _ _).mpr hi)
  · rintro ⟨h0i, h1i⟩; rw [hP_eq]; simp [h0i, h1i]

/-- **Unconditional Binary Lower Track 64.01 Certificate (`78633206 / 268435456`)!** -/
theorem protocolClaim6401 : ProtocolClaim 6401 radNum radDen :=
  protocolClaim6401_of_lineAndList
    (mcaCap := 18400000000000000000) (listCap := 10000000)
    (by norm_num) (by norm_num)
    lineExactAgreementBound_6401 scalarListBound_6401

end B6401Main
end ProximityPrize.SubmissionBinaryLower
