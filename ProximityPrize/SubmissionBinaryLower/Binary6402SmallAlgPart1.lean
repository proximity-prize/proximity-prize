import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlgPart0
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401KerD2
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402IntSmallCerts
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT1
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT2
import ProximityPrize.SubmissionBinaryLower.Binary6402CertsT3
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

/-!
# Tables 1, 2, 3, and 3-2B: Contiguous Certificate Coverage, Char-2 Resultant & UFD Algebra

Provides:
1. `decide`-verified contiguous coverage theorems (`exists_t1Cert`, `exists_t2Cert`, `exists_t3Cert`)
   over `B6402CertsT1`, `B6402CertsT2`, and `B6402CertsT3` (`O(n)` synchronized cover check for T3!).
2. Multiplicativity of `wdegBi` (`wdegBi_mul`) and exact 2D multiplicity `biMult` (`biMult_mul`,
   `biMult_even_of_in_F_X2_Y2`).
3. Resultant shift/cancellation identity (`resultant_add_mul_right_deg`) and char-2 `ker(D)`
   resultant divisibility theorems:
   - `kerD1_resY_ord` (Table 1 `v_ker` + `v_pln`),
   - `kerD2_resY_f0_g_ord` (Table 3 general `v_ker` + `v_pln` and 2B `q, g_1`),
   - `kerD2_resY_f0_g_2A_ord` (Table 3 Subcase 2A `g = q(X) * g_e(X^2, Y^2)`).
4. Char-2 `ker(D)` UFD decomposition for `deg_R = 2` (`kerD2_gcd_decomp` and `kerD2_2A_2B_dichotomy`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402SmallAlg

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6402IntFarkas B6402IntSmallCerts
open B6402CertsT1 B6402CertsT2 B6402CertsT3
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X
section BiPolyAlgebra
variable {A : Type*} [CommRing A] [IsDomain A]

/-- Exact additivity `biMult x0 y0 (f * g) = biMult x0 y0 f + biMult x0 y0 g` over any domain `A`! -/
theorem biMult_mul (x0 y0 : A) {f g : BiPoly A} (hf : f ≠ 0) (hg : g ≠ 0) :
    biMult x0 y0 (f * g) = biMult x0 y0 f + biMult x0 y0 g := by
  classical
  apply le_antisymm
  · -- Pick min-j among min-degree nonzero terms of shift f and shift g!
    let sf := shiftBi x0 y0 f
    let sg := shiftBi x0 y0 g
    have hsf : sf ≠ 0 := fun h => hf ((shiftBi_eq_zero_iff x0 y0 f).mp h)
    have hsg : sg ≠ 0 := fun h => hg ((shiftBi_eq_zero_iff x0 y0 g).mp h)
    let mf := biMult x0 y0 f
    let mg := biMult x0 y0 g
    have hmin_pair : ∀ (s : BiPoly A) (hs : s ≠ 0) (m : ℕ),
        (∀ i j, i + j < m → (s.coeff j).coeff i = 0) →
        (∃ i j, i + j = m ∧ (s.coeff j).coeff i ≠ 0) →
        ∃ j0, j0 ≤ m ∧ (s.coeff j0).coeff (m - j0) ≠ 0 ∧
          ∀ j' < j0, (s.coeff j').coeff (m - j') = 0 := by
      intro s _ m _ hex
      let Js := (Finset.range (m + 1)).filter fun j => (s.coeff j).coeff (m - j) ≠ 0
      have hJs : Js.Nonempty := by
        obtain ⟨i, j, hij, hnz⟩ := hex
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [show m - j = i by omega]⟩⟩
      let j0 := Js.min' hJs
      have hj0 := Finset.mem_filter.mp (Finset.min'_mem Js hJs)
      refine ⟨j0, by have := Finset.mem_range.mp hj0.1; omega, hj0.2, fun j' hj' => ?_⟩
      by_contra hnz
      have hmem : j' ∈ Js := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hj0.1; omega), hnz⟩
      have := Finset.min'_le Js j' hmem; omega
    have hex_f : ∃ i j, i + j = mf ∧ (sf.coeff j).coeff i ≠ 0 := by
      let degs := sf.support.biUnion fun j => (sf.coeff j).support.image fun i => i + j
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hsf
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
      have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
      have hbm : mf = degs.min' hne := by dsimp [mf]; unfold biMult; simp only [degs, sf, hne, ↓reduceDIte]
      have hmem : degs.min' hne ∈ degs := Finset.min'_mem degs hne
      rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
      rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
      exact ⟨i', j', heq.trans hbm.symm, Polynomial.mem_support_iff.mp hi'm⟩
    have hex_g : ∃ i j, i + j = mg ∧ (sg.coeff j).coeff i ≠ 0 := by
      let degs := sg.support.biUnion fun j => (sg.coeff j).support.image fun i => i + j
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hsg
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
      have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
      have hbm : mg = degs.min' hne := by dsimp [mg]; unfold biMult; simp only [degs, sg, hne, ↓reduceDIte]
      have hmem : degs.min' hne ∈ degs := Finset.min'_mem degs hne
      rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
      rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
      exact ⟨i', j', heq.trans hbm.symm, Polynomial.mem_support_iff.mp hi'm⟩
    obtain ⟨j1, hj1_le, hj1_nz, hj1_min⟩ := hmin_pair sf hsf mf (biMultGE_biMult x0 y0 f) hex_f
    obtain ⟨j2, hj2_le, hj2_nz, hj2_min⟩ := hmin_pair sg hsg mg (biMultGE_biMult x0 y0 g) hex_g
    have hnz_fg : ((shiftBi x0 y0 (f * g)).coeff (j1 + j2)).coeff ((mf - j1) + (mg - j2)) ≠ 0 := by
      rw [shiftBi_mul, Polynomial.coeff_mul, finset_sum_coeff]
      rw [Finset.sum_eq_single (j1, j2)]
      · rw [Polynomial.coeff_mul, Finset.sum_eq_single (mf - j1, mg - j2)]
        · exact mul_ne_zero hj1_nz hj2_nz
        · intro ⟨i1, i2⟩ hi hne
          have hsum : i1 + i2 = (mf - j1) + (mg - j2) := Finset.mem_antidiagonal.mp hi
          by_cases h1 : i1 + j1 < mf
          · rw [biMultGE_biMult x0 y0 f i1 j1 h1, zero_mul]
          · have h2 : i2 + j2 < mg := by by_contra hge; apply hne; ext <;> dsimp <;> omega
            rw [biMultGE_biMult x0 y0 g i2 j2 h2, mul_zero]
        · intro h; simp at h
      · intro ⟨b1, b2⟩ hb hne
        have hsum : b1 + b2 = j1 + j2 := Finset.mem_antidiagonal.mp hb
        rw [Polynomial.coeff_mul]
        apply Finset.sum_eq_zero; intro ⟨i1, i2⟩ hi
        have hisum : i1 + i2 = (mf - j1) + (mg - j2) := Finset.mem_antidiagonal.mp hi
        by_cases h1 : i1 + b1 < mf
        · rw [biMultGE_biMult x0 y0 f i1 b1 h1, zero_mul]
        · by_cases h2 : i2 + b2 < mg
          · rw [biMultGE_biMult x0 y0 g i2 b2 h2, mul_zero]
          · have heq1 : i1 = mf - b1 := by omega
            have heq2 : i2 = mg - b2 := by omega
            by_cases hb1 : b1 < j1
            · rw [heq1, hj1_min b1 hb1, zero_mul]
            · have hb2 : b2 < j2 := by by_contra hge; apply hne; ext <;> dsimp <;> omega
              rw [heq2, hj2_min b2 hb2, mul_zero]
      · intro h; simp at h
    by_contra hgt; push Not at hgt
    exact hnz_fg (biMultGE_biMult x0 y0 (f * g) ((mf - j1) + (mg - j2)) (j1 + j2) (by omega))
  · exact le_biMult_of_biMultGE x0 y0 (mul_ne_zero hf hg)
      (biMultGE_mul x0 y0 f g _ _ (biMultGE_biMult x0 y0 f) (biMultGE_biMult x0 y0 g))

lemma biMult_map_eq_of_injective {B : Type*} [CommRing B] [IsDomain B]
    (φ : A →+* B) (hφ : Function.Injective φ) (x0 y0 : A) (f : BiPoly A) :
    biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) = biMult x0 y0 f := by
  have hsh : shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) =
      (shiftBi x0 y0 f).map (Polynomial.mapRingHom φ) := by
    unfold shiftBi
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_map, Polynomial.map_map]
    have hcomm : (Polynomial.compRingHom (C (φ x0) + X)).comp (Polynomial.mapRingHom φ) =
        (Polynomial.mapRingHom φ).comp (Polynomial.compRingHom (C x0 + X)) := by
      ext <;> simp [Polynomial.compRingHom]
    rw [hcomm]
  have hcoeff : ∀ j i, ((shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))).coeff j).coeff i =
      φ (((shiftBi x0 y0 f).coeff j).coeff i) := by
    intro j i; rw [hsh, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  by_cases hf : f = 0
  · subst hf; simp [biMult, shiftBi]
  · have hfm : f.map (Polynomial.mapRingHom φ) ≠ 0 := by
      intro h0; apply hf; ext j i
      have := congrArg (fun p : BiPoly B => (p.coeff j).coeff i) h0
      simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at this
      exact hφ (by rw [this, Polynomial.coeff_zero, Polynomial.coeff_zero, map_zero])
    apply le_antisymm
    · by_contra hgt; push Not at hgt
      have hge := biMultGE_biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))
      have hgeA : biMultGE x0 y0 f (biMult (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ))) := by
        intro i j hij; exact hφ (by rw [← hcoeff j i, hge i j hij, map_zero])
      have := le_biMult_of_biMultGE x0 y0 hf hgeA; omega
    · apply le_biMult_of_biMultGE (φ x0) (φ y0) hfm
      intro i j hij; rw [hcoeff j i, biMultGE_biMult x0 y0 f i j hij, map_zero]

lemma biMultGE_map {B : Type*} [CommRing B] [IsDomain B]
    (φ : A →+* B) (x0 y0 : A) (f : BiPoly A) (m : ℕ) (h : biMultGE x0 y0 f m) :
    biMultGE (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) m := by
  intro i j hij
  have hsh : shiftBi (φ x0) (φ y0) (f.map (Polynomial.mapRingHom φ)) =
      (shiftBi x0 y0 f).map (Polynomial.mapRingHom φ) := by
    unfold shiftBi
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_map, Polynomial.map_map]
    have hcomm : (Polynomial.compRingHom (C (φ x0) + X)).comp (Polynomial.mapRingHom φ) =
        (Polynomial.mapRingHom φ).comp (Polynomial.compRingHom (C x0 + X)) := by
      ext <;> simp [Polynomial.compRingHom]
    rw [hcomm]
  rw [hsh, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h i j hij, map_zero]

/-- In characteristic 2, any polynomial `g ∈ A[X^2, Y^2]` has EVEN `biMult x0 y0 g`! -/
lemma biMult_even_of_in_X2_Y2 [CharP A 2] (x0 y0 : A) (g : BiPoly A)
    (heven : ∀ j i, (g.coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0) :
    biMult x0 y0 g % 2 = 0 := by
  classical
  have hsh_even : ∀ j i, ((shiftBi x0 y0 g).coeff j).coeff i ≠ 0 → i % 2 = 0 ∧ j % 2 = 0 := by
    -- Express g as sum of monomials C(C c) * C(X^2)^a * (X^2)^b; shift preserves even (i, j) in char 2!
    have hpow2X : ∀ u v : Polynomial A, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
      intro u v
      have h2 : (2 : Polynomial A) = 0 := CharTwo.two_eq_zero
      calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
        _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
    have hpow2Y : ∀ u v : BiPoly A, (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
      intro u v
      have h2 : (2 : BiPoly A) = 0 := CharTwo.two_eq_zero
      calc (u + v) ^ 2 = u ^ 2 + 2 * u * v + v ^ 2 := by ring
        _ = u ^ 2 + v ^ 2 := by rw [h2]; ring
    have hsh_monom : ∀ (c : A) (a b : ℕ) (j i : ℕ),
        ((shiftBi x0 y0 (Polynomial.monomial (2 * b) (Polynomial.monomial (2 * a) c))).coeff j).coeff i ≠ 0 →
        i % 2 = 0 ∧ j % 2 = 0 := by
      intro c a b j i hnz
      unfold shiftBi at hnz
      rw [Polynomial.map_monomial, Polynomial.coe_compRingHom] at hnz
      dsimp only at hnz
      rw [Polynomial.monomial_comp, Polynomial.monomial_comp] at hnz
      have hX2 : (C x0 + X : Polynomial A) ^ (2 * a) = (C (x0 ^ 2) + X ^ 2) ^ a := by
        rw [pow_mul, hpow2X, map_pow]
      have hY2 : (C (C y0) + X : BiPoly A) ^ (2 * b) = (C (C (y0 ^ 2)) + X ^ 2) ^ b := by
        rw [pow_mul, hpow2Y, map_pow, map_pow]
      rw [hX2, hY2, add_pow, add_pow, Finset.mul_sum, Finset.mul_sum,
        finset_sum_coeff, finset_sum_coeff] at hnz
      obtain ⟨l, _, hlnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      -- Directly check both j % 2 = 0 and i % 2 = 0 via coeff_mul!
      by_contra hnot
      have hcoeff_ev : ∀ (u : Polynomial A) (k m : ℕ),
          (∀ r, u.coeff r ≠ 0 → r % 2 = 0) →
          (((C u * ((C (C (y0 ^ 2)) ^ k * (X ^ 2) ^ m) * (Nat.choose b k : BiPoly A))).coeff j).coeff i = 0) := by
        intro u k m hu
        have h1 : C u * ((C (C (y0 ^ 2)) ^ k * (X ^ 2) ^ m) * (Nat.choose b k : BiPoly A)) =
            C (u * C (y0 ^ 2) ^ k * (Nat.choose b k : Polynomial A)) * X ^ (2 * m) := by
          simp only [map_mul, map_pow, map_natCast, pow_mul]; ring
        rw [h1, Polynomial.coeff_C_mul_X_pow]
        split_ifs with hjm
        · rw [mul_assoc, ← map_pow C, ← map_natCast C, ← map_mul C, Polynomial.coeff_mul_C]
          by_cases hi_ev : i % 2 = 0
          · exfalso; exact hnot ⟨hi_ev, by omega⟩
          · have : u.coeff i = 0 := by by_contra h; exact hi_ev (hu i h)
            rw [this, zero_mul]
        · simp
      have hu_ev : ∀ r, (C c * ∑ m ∈ Finset.range (a + 1), C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A)).coeff r ≠ 0 →
          r % 2 = 0 := by
        intro r hr
        rw [Polynomial.coeff_C_mul, finset_sum_coeff] at hr
        have hsum_ne : ∑ m ∈ Finset.range (a + 1), (C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A)).coeff r ≠ 0 :=
          right_ne_zero_of_mul hr
        obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        have hm' : C (x0 ^ 2) ^ m * (X ^ 2) ^ (a - m) * (Nat.choose a m : Polynomial A) =
            C ((x0 ^ 2) ^ m * (Nat.choose a m : A)) * X ^ (2 * (a - m)) := by
          simp only [map_mul, map_pow, map_natCast, pow_mul]; ring
        rw [hm', Polynomial.coeff_C_mul_X_pow] at hm
        split_ifs at hm with hrm
        · omega
        · exact absurd rfl hm
      have hzero := hcoeff_ev _ l (b - l) hu_ev
      rw [Finset.mul_sum] at hzero
      exact hlnz hzero
    -- Sum over g.support and (g.coeff j).support
    intro j i hnz
    have hg_sum : g = ∑ b ∈ g.support, ∑ a ∈ (g.coeff b).support,
        Polynomial.monomial b (Polynomial.monomial a ((g.coeff b).coeff a)) := by
      conv_lhs => rw [g.as_sum_support]
      apply Finset.sum_congr rfl; intro b _
      conv_lhs => rw [(g.coeff b).as_sum_support]
      rw [map_sum]
    have hsh_sum : shiftBi x0 y0 g = ∑ b ∈ g.support, ∑ a ∈ (g.coeff b).support,
        shiftBi x0 y0 (Polynomial.monomial b (Polynomial.monomial a ((g.coeff b).coeff a))) := by
      conv_lhs => rw [hg_sum]
      unfold shiftBi; simp only [Polynomial.map_sum, Polynomial.sum_comp]
    rw [hsh_sum, finset_sum_coeff, finset_sum_coeff] at hnz
    obtain ⟨b, hb, hbnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    rw [finset_sum_coeff, finset_sum_coeff] at hbnz
    obtain ⟨a, ha, hanz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbnz
    have hpar := heven b a (Polynomial.mem_support_iff.mp ha)
    have hb2 : b = 2 * (b / 2) := by omega
    have ha2 : a = 2 * (a / 2) := by omega
    rw [hb2, ha2] at hanz
    exact hsh_monom _ (a / 2) (b / 2) j i hanz
  by_cases hg : g = 0
  · subst hg; simp [biMult, shiftBi]
  · let s := shiftBi x0 y0 g
    have hs : s ≠ 0 := fun h => hg ((shiftBi_eq_zero_iff x0 y0 g).mp h)
    let degs := s.support.biUnion fun j => (s.coeff j).support.image fun i => i + j
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hs
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj)
    have hne : degs.Nonempty := ⟨i + j, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩⟩
    have hbm : biMult x0 y0 g = degs.min' hne := by unfold biMult; simp only [degs, s, hne, ↓reduceDIte]
    rw [hbm]
    have hmem := Finset.min'_mem degs hne
    rcases Finset.mem_biUnion.mp hmem with ⟨j', _, hi'⟩
    rcases Finset.mem_image.mp hi' with ⟨i', hi'm, heq⟩
    have hpar := hsh_even j' i' (Polynomial.mem_support_iff.mp hi'm)
    omega

end BiPolyAlgebra

/-! ### Part 3: Resultant Invariance & Char-2 `ker(D)` Resultant Divisibility (`T1`, `T3`, `T3-2A`) -/

section KerDResultants

/-- **Resultant reduction modulo `g`:**
For any polynomials `f, g, q : R[X]` over an integral domain `R` with `f.natDegree ≤ df`,
`(f + q * g).natDegree ≤ df`, and `g.natDegree = dg`:
`Polynomial.resultant (f + q * g) g df dg = Polynomial.resultant f g df dg`! -/
theorem resultant_add_mul_right_deg {R : Type*} [CommRing R] [IsDomain R]
    (f g q : R[X]) (df dg : ℕ)
    (hf : f.natDegree ≤ df) (hfq : (f + q * g).natDegree ≤ df) (hg : g.natDegree = dg) :
    Polynomial.resultant (f + q * g) g df dg = Polynomial.resultant f g df dg := by
  by_cases hg0 : g = 0
  · subst hg0; simp
  let K := FractionRing R
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let gK : K[X] := g.map (algebraMap R K)
  let L := gK.SplittingField
  have hKL : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  let φ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hφ : Function.Injective φ := hKL.comp hRK
  apply hφ
  rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map]
  have hmap_add : (f + q * g).map φ = f.map φ + q.map φ * g.map φ := by
    rw [Polynomial.map_add, Polynomial.map_mul]
  rw [hmap_add]
  have hgL_ne : g.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hg0
  have hgL_deg : (g.map φ).natDegree = dg := by rw [Polynomial.natDegree_map_eq_of_injective hφ, hg]
  have hsplits : (g.map φ).Splits := by
    have heq : g.map φ = gK.map (algebraMap K L) := by simp [φ, gK, Polynomial.map_map]
    rw [heq]; exact Polynomial.SplittingField.splits gK
  have hfac : g.map φ = C (g.map φ).leadingCoeff * ((g.map φ).roots.map fun r => X - C r).prod :=
    hsplits.eq_prod_roots
  have hroots_card : (g.map φ).roots.card = dg := by
    rw [← hgL_deg]; exact hsplits.natDegree_eq_card_roots.symm
  -- Evaluate Res(p, C a * ∏ (X - C r)) = a^df * ∏ p.eval r for BOTH p = f.map φ + q.map φ * g.map φ and p = f.map φ!
  have hres_eval : ∀ (p : L[X]), p.natDegree ≤ df →
      Polynomial.resultant p (g.map φ) df dg =
        (g.map φ).leadingCoeff ^ df * (((-1 : L) ^ df) ^ dg * ((g.map φ).roots.map fun r => p.eval r).prod) := by
    intro p hp
    have hres_prod : ∀ (S : Multiset L),
        Polynomial.resultant p (S.map fun r => X - C r).prod df S.card =
          ((-1 : L) ^ df) ^ S.card * (S.map fun r => p.eval r).prod := by
      intro S
      induction S using Multiset.induction_on with
      | empty => simp [Polynomial.resultant_one_right]
      | cons r T ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
          have hT_deg : (T.map fun a => X - C a).prod.natDegree = T.card := by
            rw [Polynomial.natDegree_multiset_prod]
            · simp
            · intro h0; rcases Multiset.mem_map.mp h0 with ⟨a, _, ha⟩; exact Polynomial.X_sub_C_ne_zero a ha
          have hr_deg : (X - C r : L[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C r
          rw [show T.card + 1 = (X - C r : L[X]).natDegree + (T.map fun a => X - C a).prod.natDegree by omega,
            Polynomial.resultant_mul_right p (X - C r) _ df hp, hr_deg, hT_deg,
            Polynomial.resultant_X_sub_C_right p df r hp, ih, pow_add, pow_one]
          ring
    conv_lhs => rw [hfac]
    have hprod_deg : ((g.map φ).roots.map fun r => X - C r).prod.natDegree = dg := by
      rw [Polynomial.natDegree_multiset_prod, ← hroots_card]
      · simp
      · intro h0; rcases Multiset.mem_map.mp h0 with ⟨a, _, ha⟩; exact Polynomial.X_sub_C_ne_zero a ha
    rw [Polynomial.resultant_C_mul_right,
      ← hroots_card, hres_prod (g.map φ).roots]
  rw [hres_eval (f.map φ + q.map φ * g.map φ) (by rw [← hmap_add]; exact Polynomial.natDegree_map_le.trans hfq),
    hres_eval (f.map φ) (Polynomial.natDegree_map_le.trans hf)]
  congr 1; congr 1; congr 1
  apply Multiset.map_congr rfl; intro r hr
  have hroot : (g.map φ).eval r = 0 := (Polynomial.mem_roots hgL_ne).mp hr
  simp [Polynomial.eval_add, Polynomial.eval_mul, hroot]

/-- Nonzero resultant over a field `F` from `IsRelPrime` in `BiPoly F = (F[X])[Y]` (or `(RatFunc F)[Y]`). -/
theorem resultant_ne_zero_of_coprime_ratFunc {F : Type*} [Field F]
    (f g : BiPoly F) (hfnz : f ≠ 0) (hgnz : g ≠ 0)
    (hcop : IsRelPrime (f.map (algebraMap (Polynomial F) (RatFunc F)))
      (g.map (algebraMap (Polynomial F) (RatFunc F)))) :
    Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := by
  classical
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  intro h0
  have h0K : Polynomial.resultant (f.map ψ) (g.map ψ) (f.map ψ).natDegree (g.map ψ).natDegree = 0 := by
    rw [Polynomial.natDegree_map_eq_of_injective hψ, Polynomial.natDegree_map_eq_of_injective hψ,
      Polynomial.resultant_map_map, h0, map_zero]
  have hcop' : IsCoprime (f.map ψ) (g.map ψ) := by
    obtain ⟨u, hu⟩ := hcop (EuclideanDomain.gcd_dvd_left (f.map ψ) (g.map ψ))
      (EuclideanDomain.gcd_dvd_right (f.map ψ) (g.map ψ))
    refine ⟨EuclideanDomain.gcdA (f.map ψ) (g.map ψ) * ↑u⁻¹,
            EuclideanDomain.gcdB (f.map ψ) (g.map ψ) * ↑u⁻¹, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab (f.map ψ) (g.map ψ)
    rw [← hu] at hbez
    calc EuclideanDomain.gcdA (f.map ψ) (g.map ψ) * ↑u⁻¹ * f.map ψ +
          EuclideanDomain.gcdB (f.map ψ) (g.map ψ) * ↑u⁻¹ * g.map ψ
        = (f.map ψ * EuclideanDomain.gcdA (f.map ψ) (g.map ψ) +
            g.map ψ * EuclideanDomain.gcdB (f.map ψ) (g.map ψ)) * ↑u⁻¹ := by ring
      _ = ↑u * ↑u⁻¹ := by rw [← hbez]
      _ = 1 := Units.mul_inv u
  exact Polynomial.resultant_ne_zero (f.map ψ) (g.map ψ) hcop' h0K

/-- Helper: if `f : BiPoly F` has `f.coeff j = 0` for all odd `j`, then `f = Polynomial.expand (Polynomial F) 2 fHalf`! -/
lemma exists_expand2_of_even_Y {R : Type*} [CommRing R] (f : R[X])
    (heven : ∀ j, j % 2 = 1 → f.coeff j = 0) :
    ∃ g : R[X], f = Polynomial.expand R 2 g ∧ 2 * g.natDegree ≤ f.natDegree ∧
      (∀ j, g.coeff j = f.coeff (2 * j)) := by
  let g : R[X] := ∑ j ∈ Finset.range (f.natDegree / 2 + 1), Polynomial.monomial j (f.coeff (2 * j))
  have hg_c : ∀ j, g.coeff j = f.coeff (2 * j) := by
    intro j
    dsimp [g]; rw [finset_sum_coeff]
    by_cases hj : j < f.natDegree / 2 + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd (Finset.mem_range.mpr hj) h
    · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      intro k hk; have := Finset.mem_range.mp hk; simp [Polynomial.coeff_monomial, show k ≠ j by omega]
  have hexp : f = Polynomial.expand R 2 g := by
    ext n
    rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
    by_cases h2 : 2 ∣ n
    · rw [if_pos h2, hg_c, show 2 * (n / 2) = n by omega]
    · rw [if_neg h2]; exact heven n (by omega)
  have hdeg : 2 * g.natDegree ≤ f.natDegree := by
    have : g.natDegree ≤ f.natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      rw [hg_c]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    omega
  exact ⟨g, hexp, hdeg, hg_c⟩

lemma shiftBi_expand2 {F : Type*} [Field F] [CharP F 2] (x0 y0 : F) (g0 : BiPoly F) :
    shiftBi x0 y0 (Polynomial.expand (Polynomial F) 2 g0) =
      Polynomial.expand (Polynomial F) 2
        ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
  unfold shiftBi
  have h2 : (C (C y0) + X : BiPoly F) ^ 2 = C (C (y0 ^ 2)) + X ^ 2 := by
    have h2bi : (2 : BiPoly F) = 0 := CharTwo.two_eq_zero
    calc (C (C y0) + X : BiPoly F) ^ 2 = C (C y0) ^ 2 + 2 * C (C y0) * X + X ^ 2 := by ring
      _ = C (C (y0 ^ 2)) + X ^ 2 := by rw [h2bi, map_pow, map_pow]; ring
  induction g0 using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, Polynomial.map_add, Polynomial.add_comp, ha, hb, Polynomial.map_add, Polynomial.add_comp, map_add]
  | monomial n c =>
      rw [Polynomial.expand_monomial, Polynomial.map_monomial, Polynomial.map_monomial,
        Polynomial.monomial_comp, Polynomial.monomial_comp,
        map_mul, map_pow, Polynomial.expand_C, map_add, Polynomial.expand_C, Polynomial.expand_X,
        mul_comm n 2, pow_mul, h2]

lemma coeff_comp_C_add_X_top {F : Type*} [Field F] (y0 : F) (p : BiPoly F) (n : ℕ)
    (hpn : p.natDegree ≤ n) : (p.comp (C (C y0) + X)).coeff n = p.coeff n := by
  conv_lhs => rw [p.as_sum_range' (n + 1) (by omega)]
  rw [Polynomial.sum_comp, finset_sum_coeff, Finset.sum_eq_single n]
  · rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, add_comm, add_pow,
      finset_sum_coeff, Finset.sum_eq_single n]
    · simp [Polynomial.coeff_X_pow]
    · intro l _ hne
      have : X ^ l * (C (C y0) : BiPoly F) ^ (n - l) * (Nat.choose n l : BiPoly F) =
          C (C (y0 ^ (n - l) * (Nat.choose n l : F))) * X ^ l := by
        simp only [map_mul, map_pow, map_natCast]; ring
      rw [this, Polynomial.coeff_C_mul_X_pow, if_neg hne.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro m hm hne
    have hlt : m < n := by have := Finset.mem_range.mp hm; omega
    rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul]
    have hdeg : ((C (C y0) + X : BiPoly F) ^ m).natDegree ≤ m :=
      Polynomial.natDegree_pow_le.trans (by
        have : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
        nlinarith only [this])
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := (C (C y0) + X : BiPoly F) ^ m) (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Table 1 Local Resultant Divisibility (`kerD1_resY_ord`):**
For `Fpoly ∈ K_{W_F}(1)` over `[Field F] [CharP F 2]` with `twOrdGE (localShift F) k`,
`d0 = (Fpoly.coeff 0).natDegree`, `d1 = (Fpoly.coeff 1).natDegree` (`2 ≤ d1`), `dp = max d0 (d1 + 1)`:
`(X - C x0) ^ resYKerD1Ord d0 d1 k ∣ (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) * Res_Y(f0, f1; d0, d1)`! -/
theorem kerD1_resY_ord {F : Type*} [Field F] [CharP F 2] {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 y0 : F) (f_coord : KerDIdx wY W_F 1 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let d0 := (Fpoly.coeff 0).natDegree
    let d1 := (Fpoly.coeff 1).natDegree
    let dp := max d0 (d1 + 1)
    2 ≤ d1 →
    (X - C x0) ^ resYKerD1Ord d0 d1 k ∣
      (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) *
        Polynomial.resultant (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 := by
  intro Fpoly d0 d1 dp hd1
  by_cases hk0 : k = 0
  · subst hk0; simp [resYKerD1Ord]
  have hk_ne : (k == 0) = false := beq_false_of_ne hk0
  have hdg_ne : (d1 / 2 == 0) = false := beq_false_of_ne (by omega)
  unfold resYKerD1Ord
  simp only [hk_ne, hdg_ne, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
  -- Helper: X^a ∣ R ∧ X^b ∣ R → X^(max a b) ∣ R
  have hdvd_max : ∀ (a b : ℕ) (R : Polynomial F),
      (X - C x0) ^ a ∣ R → (X - C x0) ^ b ∣ R → (X - C x0) ^ max a b ∣ R := by
    intro a b R ha hb; rcases le_total a b with h | h
    · rwa [Nat.max_eq_right h]
    · rwa [Nat.max_eq_left h]
  apply hdvd_max
  · -- Branch 1: vKer = resOrdWeighted dp (4*k + 2) (d1 / 2) (2*k - 1) 2 - 2 * (d1 / 2)!
    obtain ⟨_, hbm1⟩ := kerD1_local_ords hwY x0 y0 f_coord hvan
    obtain ⟨Pe, Po, hdecomp, hPe_d, hPo_d, _, _, hP_ord⟩ := kerD1_weighted_decomp hwY x0 y0 f_coord hvan
    -- Show shiftBi x0 y0 (Fpoly.coeff 1) has ONLY even Y-powers (since f_1 ∈ F[X, Y^2])!
    have hf1_ev : ∀ j, j % 2 = 1 → (shiftBi x0 y0 (Fpoly.coeff 1)).coeff j = 0 := by
      have hf1_0 : ∀ j, j % 2 = 1 → (Fpoly.coeff 1).coeff j = 0 := by
        intro j hj
        dsimp [Fpoly]; rw [finset_sum_coeff, finset_sum_coeff]
        apply Finset.sum_eq_zero; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
        have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [pow_zero, pow_zero, one_mul, one_mul,
            show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
              simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C, if_neg (by omega), Polynomial.coeff_zero]
        · rw [pow_one, pow_zero, mul_one,
            show C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) * X by
              simp only [map_mul, map_pow]; ring,
            Polynomial.coeff_C_mul_X, if_pos rfl,
            show C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
              C (C (f_coord ⟨(1, 0, b1, a1), he⟩) * (X ^ 2) ^ a1) * X ^ (2 * b1) by
              simp only [map_mul, map_pow, pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
        · rw [pow_zero, pow_one, one_mul,
            show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
              C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
              C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) * X by
              simp only [map_mul, map_pow, map_add]; ring,
            Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
            Polynomial.coeff_C_mul_X, if_pos rfl,
            show C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
              C (C (f_coord ⟨(0, 1, b1, a1), he⟩) * X * (X ^ 2) ^ a1) * X ^ (2 * b1) by
              simp only [map_mul, map_pow, pow_mul],
            Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      obtain ⟨g0, hg0_eq, _, _⟩ := exists_expand2_of_even_Y (Fpoly.coeff 1) hf1_0
      have hsh_exp : shiftBi x0 y0 (Fpoly.coeff 1) =
          Polynomial.expand (Polynomial F) 2
            ((g0.map (Polynomial.compRingHom (C x0 + X))).comp (C (C (y0 ^ 2)) + X)) := by
        rw [hg0_eq, shiftBi_expand2]
      intro j hj
      rw [hsh_exp, Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by omega)]
    have hd1_even : d1 % 2 = 0 := by
      have hf1_ne : Fpoly.coeff 1 ≠ 0 := by intro h0; simp [d1, h0] at hd1
      have hsh_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree = d1 := by
        unfold shiftBi
        have hlc : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree = d1 := by
          apply Polynomial.natDegree_map_eq_of_injective
          intro p q hpq
          have := congrArg (fun r => r.comp (X - C x0)) hpq
          simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
        have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
          intro p c
          apply le_antisymm
          · refine Polynomial.natDegree_comp_le.trans ?_
            have h1 : (C c + X : BiPoly F).natDegree ≤ 1 :=
              (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
            nlinarith only [h1]
          · have hback : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
              rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
                show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
                Polynomial.comp_X]
            rw [← hback]
            refine Polynomial.natDegree_comp_le.trans ?_
            have h1 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
              (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
            nlinarith only [h1]
        rw [hcomp, hlc]
      by_contra hodd
      have hnz : (shiftBi x0 y0 (Fpoly.coeff 1)).coeff d1 ≠ 0 := by
        rw [← hsh_deg]; exact Polynomial.leadingCoeff_ne_zero.mpr
          (fun h => hf1_ne ((shiftBi_eq_zero_iff x0 y0 _).mp h))
      exact hnz (hf1_ev d1 (by omega))
    obtain ⟨g1, hg1_eq, _, hg1_c⟩ := exists_expand2_of_even_Y (shiftBi x0 y0 (Fpoly.coeff 1)) hf1_ev
    have hsh1_deg : (shiftBi x0 y0 (Fpoly.coeff 1)).natDegree = d1 := by
      have hf1_ne : Fpoly.coeff 1 ≠ 0 := by intro h0; simp [d1, h0] at hd1
      unfold shiftBi
      have hinj : Function.Injective (Polynomial.compRingHom (C x0 + X) : Polynomial F →+* Polynomial F) := by
        intro p q hpq; have := congrArg (fun r => r.comp (X - C x0)) hpq
        simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.comp_X] using this
      have h1 : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree = d1 :=
        Polynomial.natDegree_map_eq_of_injective hinj _
      have hcomp : ∀ (p : BiPoly F) (c : Polynomial F), (p.comp (C c + X)).natDegree = p.natDegree := by
        intro p c; apply le_antisymm
        · refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C c + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
        · have hb : ((p.comp (C c + X)).comp (C (-c) + X)).natDegree = p.natDegree := by
            rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
              show C c + (C (-c) + X) = X by rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add],
              Polynomial.comp_X]
          rw [← hb]; refine Polynomial.natDegree_comp_le.trans ?_
          have h2 : (C (-c) + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [h2]
      rw [hcomp, h1]
    have hg1_deg : g1.natDegree = d1 / 2 := by
      have h2 := Polynomial.natDegree_expand (R := Polynomial F) 2 g1
      rw [← hg1_eq, hsh1_deg] at h2; omega
    have hg1_ord : weightedOrdGE 2 (2 * k - 1) g1 := by
      intro j; rw [hg1_c j]
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 (Fpoly.coeff 1) (2 * k - 1)).mp hbm1 (2 * j)
    have hPe2 : 2 * Pe.natDegree ≤ dp := by dsimp [dp, d0, d1, Fpoly] at *; omega
    have hPo2 : 2 * Po.natDegree + 1 ≤ dp := by dsimp [dp, d0, d1, Fpoly] at *; omega
    have hres_eq1 : Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X)
        (shiftBi x0 y0 (Fpoly.coeff 1)) dp d1 =
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dp (d1 / 2) := by
      conv_lhs => rw [hdecomp, hg1_eq, show d1 = 2 * (d1 / 2) by omega]
      exact resultant_expand2 Pe Po g1 dp (d1 / 2) hPe2 hPo2 hg1_deg
    have hsh0_deg : (shiftBi x0 y0 (Fpoly.coeff 0)).natDegree ≤ d0 := by
      unfold shiftBi; refine Polynomial.natDegree_comp_le.trans ?_
      have hm : ((Fpoly.coeff 0).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d0 := Polynomial.natDegree_map_le
      have hX : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
      nlinarith only [hm, hX]
    have hres_eq2 : Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X)
        (shiftBi x0 y0 (Fpoly.coeff 1)) dp d1 =
        X ^ d1 * (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff ^ (dp - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 (Fpoly.coeff 1)) d0 d1 := by
      have hdeg_lhs : (shiftBi x0 y0 (Fpoly.coeff 0) * C X).natDegree ≤ dp := by
        refine Polynomial.natDegree_mul_le.trans ?_; simp only [Polynomial.natDegree_C, add_zero]
        exact hsh0_deg.trans (le_max_left _ _)
      have hdeg_sum : (shiftBi x0 y0 (Fpoly.coeff 0) * C X + X * shiftBi x0 y0 (Fpoly.coeff 1)).natDegree ≤ dp := by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le hdeg_lhs ?_)
        refine Polynomial.natDegree_mul_le.trans ?_
        have : (X : BiPoly F).natDegree = 1 := Polynomial.natDegree_X
        rw [this, hsh1_deg]; dsimp [dp]; omega
      have hneg1 : (-1 : Polynomial F) = 1 := CharTwo.neg_eq 1
      conv_lhs =>
        rw [mul_comm (shiftBi x0 y0 (Fpoly.coeff 1)) X,
          resultant_add_mul_right_deg _ _ X dp d1 hdeg_lhs hdeg_sum hsh1_deg,
          mul_comm (shiftBi x0 y0 (Fpoly.coeff 0)) (C X),
          Polynomial.resultant_C_mul_left,
          show dp = d0 + (dp - d0) by dsimp [dp]; omega,
          Polynomial.resultant_add_left_deg _ _ d0 d1 (dp - d0) hsh0_deg,
          show (shiftBi x0 y0 (Fpoly.coeff 1)).coeff d1 = (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff by
            rw [Polynomial.leadingCoeff, hsh1_deg],
          hneg1, one_pow, one_mul]
      ring
    have hdvd_V : X ^ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 ∣
        Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) g1 dp (d1 / 2) := by
      apply pow_dvd_resultant_of_weighted_ord X (Pe ^ 2 + X * Po ^ 2) g1 dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact Polynomial.natDegree_pow_le.trans hPe2
        · refine Polynomial.natDegree_mul_le.trans ?_
          rw [Polynomial.natDegree_X]
          have := Polynomial.natDegree_pow_le (p := Po) (n := 2)
          omega
      · exact le_of_eq hg1_deg
      · exact hP_ord
      · exact hg1_ord
    rw [← hres_eq1, hres_eq2] at hdvd_V
    -- Cancel X ^ d1 = X ^ (2 * (d1 / 2))!
    have hdvd_sh : X ^ (resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 - 2 * (d1 / 2)) ∣
        (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff ^ (dp - d0) *
          Polynomial.resultant (shiftBi x0 y0 (Fpoly.coeff 0)) (shiftBi x0 y0 (Fpoly.coeff 1)) d0 d1 := by
      have hd1_eq : 2 * (d1 / 2) = d1 := by omega
      rw [hd1_eq]
      by_cases hle : d1 ≤ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2
      · have hsplit : (X : Polynomial F) ^ resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 =
            (X : Polynomial F) ^ d1 * (X : Polynomial F) ^ (resOrdWeighted dp (4 * k + 2) (d1 / 2) (2 * k - 1) 2 - d1) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        rw [hsplit, mul_assoc] at hdvd_V
        exact (mul_dvd_mul_iff_left (pow_ne_zero d1 Polynomial.X_ne_zero)).mp hdvd_V
      · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), pow_zero]; exact one_dvd _
    -- Identify (shiftBi f1).leadingCoeff = (f1.leadingCoeff).comp (C x0 + X) and shift resultant!
    have hlc_sh : (shiftBi x0 y0 (Fpoly.coeff 1)).leadingCoeff =
        (Fpoly.coeff 1).leadingCoeff.comp (C x0 + X) := by
      rw [Polynomial.leadingCoeff, hsh1_deg]
      unfold shiftBi
      have hmap_deg : ((Fpoly.coeff 1).map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ d1 :=
        Polynomial.natDegree_map_le
      rw [coeff_comp_C_add_X_top y0 _ d1 hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff]; rfl
    rw [hlc_sh, resultant_shiftBi x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 le_rfl le_rfl,
      ← Polynomial.pow_comp, ← Polynomial.mul_comp] at hdvd_sh
    exact X_sub_C_pow_dvd_of_comp_shift x0 _ _ hdvd_sh
  · -- Branch 2: vPln = resOrdExact d0 (2*k - 1) d1 (2*k - 1) + (dp - d0) * (2*k - 1 - d1)!
    obtain ⟨hbm0, hbm1⟩ := kerD1_local_ords hwY x0 y0 f_coord hvan
    have h1 := pow_dvd_leadingCoeff_of_biMultGE x0 y0 (Fpoly.coeff 1) d1 (2 * k - 1) rfl hbm1
    have h1p : (X - C x0) ^ ((dp - d0) * (2 * k - 1 - d1)) ∣ (Fpoly.coeff 1).leadingCoeff ^ (dp - d0) := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h1 (dp - d0)
    have h2s := pow_dvd_resultant_of_biMultGE x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 (2 * k - 1) d1 (2 * k - 1)
      hbm0 hbm1 le_rfl le_rfl
    rw [resultant_shiftBi x0 y0 (Fpoly.coeff 0) (Fpoly.coeff 1) d0 d1 le_rfl le_rfl] at h2s
    have h2 := X_sub_C_pow_dvd_of_comp_shift x0 _ _ h2s
    rw [add_comm, pow_add]
    exact mul_dvd_mul h1p h2

end KerDResultants
end B6402SmallAlg
end ProximityPrize.SubmissionBinaryLower
