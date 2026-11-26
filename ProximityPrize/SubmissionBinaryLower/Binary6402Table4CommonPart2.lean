import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart1
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402T4Rows
import ProximityPrize.SubmissionBinaryLower.P64Resultant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1024

/-!
# Table 4 Common `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Algebra, Resultant Bounds, `det`, and `p0_zero`

Provides the shared algebraic foundation for all 120 Table 4 branches (`B6401Table4NonK` and
`B6401Table4K`), plus complete proofs for `T4ABranch.det` and `T4ABranch.p0Zero`:
1. `SparseRow` / `baseT4Rows` satisfaction bridge matching `B6402IntFarkas.checkT4Bucket_sound`
   and `B6402T4Rows.buildT4ARows` / `buildT4BRows` definitionally.
2. Exact char-2 polynomial helpers (`sqrtPoly`, `evenPart`, `oddPart`, `sum_ord_le_natDegree`).
3. Extraction of `P_j, C_j, B_j, g_j` (`j : Fin 3`) from `f_coord : KerDIdx wY W_F 1 → Fld`
   (`W_F < 6 * wY - 1`), exact degree bounds, and shifted `(A0_j, A1_j, B^{sh}_j)` local orders.
4. Universal formal `(5, 4)` Sylvester resultant theorems:
   - `f1_eval_P_ne_zero`,
   - `natDegree_resultant_5_4_le_sylvester` (`deg_X(Res_Y) ≤ 8 W_F - 20 wY + 4 + deg_X(g_4)`),
   - `pow_dvd_resultant_5_4_U0` (`1, 11, 29 + 18(k - 3)`) and `_U1` (`4, 16, 34 + 18(k - 3)`).
5. `T4ABranch.det` (`det M ≠ 0`) and `T4ABranch.p0Zero` (`det M = 0, p = 0`) satisfaction proofs.
6. `KerD45Syzygy` (`det M = 0, p ≠ 0, U(X, P) ≠ 0`): exact coprime `(p, c, b)`, reduced minors
   `M21, M20, M10`, `Res_Y = H1 * Q2(X^2)^2`, squarefree `D2 = gcd(p, q)` & `D1 = sqrtPoly D2`,
   `D1 ∣ g_j, R, U_P`, `D1^5 ∣ H1`, all shifted local order bounds, and all degree bounds.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4Common

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401Params hiding A D
open B6402HybridP64 (A)
open B6401KerDOrders B6402IntFarkas B6402T4Rows
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

lemma coprime_triple_of_nonzero_poly {K : Type*} [Field K] [DecidableEq K]
    {p0 c0 b0 : K[X]} (hne0 : p0 ≠ 0 ∨ c0 ≠ 0 ∨ b0 ≠ 0) :
    ∃ g p c b : K[X],
      g ≠ 0 ∧ p0 = g * p ∧ c0 = g * c ∧ b0 = g * b ∧
      (p ≠ 0 ∨ c ≠ 0 ∨ b ≠ 0) ∧ (∀ d : K[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d) := by
  obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd p0 (EuclideanDomain.gcd c0 b0) := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := by
    intro hg0
    rw [hg_eq] at hg0
    have h1 := EuclideanDomain.gcd_eq_zero_iff.mp hg0
    have h2 := EuclideanDomain.gcd_eq_zero_iff.mp h1.2
    rcases hne0 with h | h | h
    · exact h h1.1
    · exact h h2.1
    · exact h h2.2
  have hg_p : g ∣ p0 := by rw [hg_eq]; exact EuclideanDomain.gcd_dvd_left p0 (EuclideanDomain.gcd c0 b0)
  have hg_c : g ∣ c0 := by rw [hg_eq]; exact (EuclideanDomain.gcd_dvd_right p0 (EuclideanDomain.gcd c0 b0)).trans (EuclideanDomain.gcd_dvd_left c0 b0)
  have hg_b : g ∣ b0 := by rw [hg_eq]; exact (EuclideanDomain.gcd_dvd_right p0 (EuclideanDomain.gcd c0 b0)).trans (EuclideanDomain.gcd_dvd_right c0 b0)
  rcases hg_p with ⟨p, hp⟩
  rcases hg_c with ⟨c, hc⟩
  rcases hg_b with ⟨b, hb⟩
  refine ⟨g, p, c, b, hg_ne, hp, hc, hb, ?_, ?_⟩
  · rcases hne0 with h | h | h
    · left; intro hp0; rw [hp0, mul_zero] at hp; exact h hp
    · right; left; intro hc0; rw [hc0, mul_zero] at hc; exact h hc
    · right; right; intro hb0; rw [hb0, mul_zero] at hb; exact h hb
  · intro d hdp hdc hdb
    have hd_all : g * d ∣ g := by
      conv_rhs => rw [hg_eq]
      apply EuclideanDomain.dvd_gcd
      · rw [hp]; exact mul_dvd_mul_left g hdp
      · apply EuclideanDomain.dvd_gcd
        · rw [hc]; exact mul_dvd_mul_left g hdc
        · rw [hb]; exact mul_dvd_mul_left g hdb
    rcases hd_all with ⟨u, hu⟩
    have hdu : d * u = 1 := mul_left_cancel₀ hg_ne (by
      calc g * (d * u) = g * d * u := by ring
        _ = g := hu.symm
        _ = g * 1 := (mul_one g).symm)
    exact isUnit_iff_exists_inv.mpr ⟨u, hdu⟩

lemma dvd_of_syzygy_coprime_poly {K : Type*} [Field K] [DecidableEq K]
    {p c b N X1 X2 : K[X]} (hp : p ≠ 0)
    (hcop : ∀ d : K[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d)
    (hpc : p * X1 = c * N) (hpb : p * X2 = b * N) : p ∣ N := by
  obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd p N := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := fun h0 => hp (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left p N) with ⟨p', hp'⟩
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right p N) with ⟨N', hN'⟩
  have hp'_cop : IsCoprime p' N' := by
    have hbez : g = p * EuclideanDomain.gcdA p N + N * EuclideanDomain.gcdB p N :=
      hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab p N)
    refine ⟨EuclideanDomain.gcdA p N, EuclideanDomain.gcdB p N, ?_⟩
    apply mul_left_cancel₀ hg_ne
    calc g * (EuclideanDomain.gcdA p N * p' + EuclideanDomain.gcdB p N * N')
        = (g * p') * EuclideanDomain.gcdA p N + (g * N') * EuclideanDomain.gcdB p N := by ring
      _ = p * EuclideanDomain.gcdA p N + N * EuclideanDomain.gcdB p N := by rw [← hp', ← hN']
      _ = g := hbez.symm
      _ = g * 1 := (mul_one g).symm
  have hp'_c : p' ∣ c := by
    have hd : p' ∣ c * N' := by
      refine ⟨X1, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (c * N') = c * (g * N') := by ring
        _ = c * N := by rw [← hN']
        _ = p * X1 := hpc.symm
        _ = g * (p' * X1) := by rw [hp']; ring
    exact hp'_cop.dvd_of_dvd_mul_right hd
  have hp'_b : p' ∣ b := by
    have hd : p' ∣ b * N' := by
      refine ⟨X2, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (b * N') = b * (g * N') := by ring
        _ = b * N := by rw [← hN']
        _ = p * X2 := hpb.symm
        _ = g * (p' * X2) := by rw [hp']; ring
    exact hp'_cop.dvd_of_dvd_mul_right hd
  have hp'_u : IsUnit p' := hcop p' ⟨g, by rw [hp', mul_comm]⟩ hp'_c hp'_b
  obtain ⟨u, hu⟩ := hp'_u
  refine ⟨(u⁻¹ : K[X]ˣ) * N', ?_⟩
  calc N = g * N' := hN'
    _ = g * (↑u * ↑u⁻¹) * N' := by rw [Units.mul_inv, mul_one]
    _ = (g * ↑u) * (↑u⁻¹ * N') := by ring
    _ = p * (↑u⁻¹ * N') := by rw [hu, ← hp']

lemma dvd_of_sq_dvd_sq_poly {K : Type*} [Field K] [DecidableEq K]
    {a b : K[X]} (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  by_cases ha : a = 0
  · subst ha; simp at h; rw [h]
  · obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd a b := ⟨_, rfl⟩
    have hg_ne : g ≠ 0 := fun h0 => ha (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left a b) with ⟨a', ha'⟩
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right a b) with ⟨b', hb'⟩
    have hcop : IsCoprime a' b' := by
      have hbez : g = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b :=
        hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab a b)
      refine ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (EuclideanDomain.gcdA a b * a' + EuclideanDomain.gcdB a b * b')
          = (g * a') * EuclideanDomain.gcdA a b + (g * b') * EuclideanDomain.gcdB a b := by ring
        _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := by rw [← ha', ← hb']
        _ = g := hbez.symm
        _ = g * 1 := (mul_one g).symm
    have hd2 : a' ^ 2 ∣ b' ^ 2 := by
      rcases h with ⟨w, hw⟩
      refine ⟨w, mul_left_cancel₀ (pow_ne_zero 2 hg_ne) ?_⟩
      calc g ^ 2 * b' ^ 2 = (g * b') ^ 2 := by ring
        _ = b ^ 2 := by rw [← hb']
        _ = a ^ 2 * w := hw
        _ = (g * a') ^ 2 * w := by rw [ha']
        _ = g ^ 2 * (a' ^ 2 * w) := by ring
    have hu : IsUnit a' := hcop.pow_right.isUnit_of_dvd' dvd_rfl ((dvd_pow_self a' (by norm_num)).trans hd2)
    obtain ⟨u, hu'⟩ := hu
    refine ⟨(u⁻¹ : K[X]ˣ) * b', ?_⟩
    calc b = g * b' := hb'
      _ = g * (↑u * ↑u⁻¹) * b' := by rw [Units.mul_inv, mul_one]
      _ = (g * ↑u) * (↑u⁻¹ * b') := by ring
      _ = a * (↑u⁻¹ * b') := by rw [hu', ← ha']

lemma syzygy_res_factor_of_inj {K : Type*} [Field K] [CharP K 2]
    (ι : Fld[X] →+* K) (hι : Function.Injective ι)
    (P0 P1 P2 C0 C1 C2 B0 B1 B2 p c b M21 M20 M10 : Fld[X])
    (hp : p ≠ 0) (hg2 : C2.comp (X ^ 2) + X * B2.comp (X ^ 2) ≠ 0)
    (hsyz0 : p * P0 + c * C0 + b * B0 = 0)
    (hsyz1 : p * P1 + c * C1 + b * B1 = 0)
    (hsyz2 : p * P2 + c * C2 + b * B2 = 0)
    (hM21 : p * M21 = C2 * B1 + C1 * B2)
    (hM20 : p * M20 = C2 * B0 + C0 * B2)
    (hM10 : p * M10 = C1 * B0 + C0 * B1) :
    let g0 := C0.comp (X ^ 2) + X * B0.comp (X ^ 2)
    let g1 := C1.comp (X ^ 2) + X * B1.comp (X ^ 2)
    let g2 := C2.comp (X ^ 2) + X * B2.comp (X ^ 2)
    let R := b.comp (X ^ 2) + X * c.comp (X ^ 2)
    let f0 : BiPoly Fld :=
      (C (P0.comp (X ^ 2)) + C (P1.comp (X ^ 2)) * X + C (P2.comp (X ^ 2)) * X ^ 2).comp (X ^ 2) +
      X * (C (B0.comp (X ^ 2)) + C (B1.comp (X ^ 2)) * X + C (B2.comp (X ^ 2)) * X ^ 2).comp (X ^ 2)
    let f1 : BiPoly Fld := (C g0 + C g1 * X + C g2 * X ^ 2).comp (X ^ 2)
    Polynomial.resultant f0 f1 5 4 =
      (p.comp (X ^ 2) ^ 4 * g0 + p.comp (X ^ 2) ^ 2 * R ^ 2 * g1 + R ^ 4 * g2) *
      ((M20 ^ 2 + M21 * M10).comp (X ^ 2)) ^ 2 := by
  intro g0 g1 g2 R f0 f1
  apply hι
  rw [← Polynomial.resultant_map_map]
  have hp_ne : ι (p.comp (X ^ 2)) ≠ 0 := fun h0 =>
    hp ((comp_X_sq_eq_zero_iff p).mp (hι (by rw [map_zero]; exact h0)))
  have hg2_ne : ι (C2.comp (X ^ 2)) + ι X * ι (B2.comp (X ^ 2)) ≠ 0 := by
    intro h0; apply hg2; apply hι
    rw [map_add, map_mul, map_zero]; exact h0
  have hsyz_lift : ∀ Pj Cj Bj : Fld[X], p * Pj + c * Cj + b * Bj = 0 →
      ι (p.comp (X ^ 2)) * ι (Pj.comp (X ^ 2)) + ι (c.comp (X ^ 2)) * ι (Cj.comp (X ^ 2)) +
      ι (b.comp (X ^ 2)) * ι (Bj.comp (X ^ 2)) = 0 := fun Pj Cj Bj h => by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, ← mul_comp, ← mul_comp, ← mul_comp,
      ← add_comp, ← add_comp, h, zero_comp, map_zero]
  have hM_lift : ∀ Ca Ba Cb Bb M : Fld[X], p * M = Ca * Bb + Cb * Ba →
      ι (p.comp (X ^ 2)) * ι (M.comp (X ^ 2)) =
      ι (Ca.comp (X ^ 2)) * ι (Bb.comp (X ^ 2)) + ι (Cb.comp (X ^ 2)) * ι (Ba.comp (X ^ 2)) := fun Ca Ba Cb Bb M hM => by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← mul_comp, ← mul_comp, ← mul_comp, ← add_comp, hM]
  have hid := char2_resultant_5_4_syzygy_factor
    (ι (P0.comp (X ^ 2))) (ι (P1.comp (X ^ 2))) (ι (P2.comp (X ^ 2)))
    (ι (C0.comp (X ^ 2))) (ι (C1.comp (X ^ 2))) (ι (C2.comp (X ^ 2)))
    (ι (B0.comp (X ^ 2))) (ι (B1.comp (X ^ 2))) (ι (B2.comp (X ^ 2)))
    (ι (p.comp (X ^ 2))) (ι (c.comp (X ^ 2))) (ι (b.comp (X ^ 2))) (ι X)
    (ι (M21.comp (X ^ 2))) (ι (M20.comp (X ^ 2))) (ι (M10.comp (X ^ 2)))
    hp_ne hg2_ne
    (hsyz_lift P0 C0 B0 hsyz0) (hsyz_lift P1 C1 B1 hsyz1) (hsyz_lift P2 C2 B2 hsyz2)
    (hM_lift C2 B2 C1 B1 M21 hM21) (hM_lift C2 B2 C0 B0 M20 hM20) (hM_lift C1 B1 C0 B0 M10 hM10)
  have hf0m : f0.map ι =
      (C (ι (P0.comp (X ^ 2))) + C (ι (P1.comp (X ^ 2))) * X + C (ι (P2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) +
      X * (C (ι (B0.comp (X ^ 2))) + C (ι (B1.comp (X ^ 2))) * X + C (ι (B2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) := by
    dsimp only [f0]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X]
  have hf1m : f1.map ι =
      (C (ι (C0.comp (X ^ 2)) + ι X * ι (B0.comp (X ^ 2))) +
       C (ι (C1.comp (X ^ 2)) + ι X * ι (B1.comp (X ^ 2))) * X +
       C (ι (C2.comp (X ^ 2)) + ι X * ι (B2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) := by
    dsimp only [f1, g0, g1, g2]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_add, map_mul]
  rw [hf0m, hf1m, hid]
  simp only [g0, g1, g2, R, add_comp, mul_comp, pow_comp, map_add, map_mul, map_pow]

lemma shifted_minor_identities_ring {R : Type*} [CommRing R] [CharP R 2]
    (p c b x y y2 y4 P0 P1 P2 C0 C1 C2 B0 B1 B2 M21 M20 M10 : R)
    (hp21 : p * M21 = C2 * B1 + C1 * B2) (hc21 : c * M21 = P2 * B1 + P1 * B2) (hb21 : b * M21 = P2 * C1 + P1 * C2)
    (hp20 : p * M20 = C2 * B0 + C0 * B2) (hc20 : c * M20 = P2 * B0 + P0 * B2) (hb20 : b * M20 = P2 * C0 + P0 * C2)
    (hp10 : p * M10 = C1 * B0 + C0 * B1) (hc10 : c * M10 = P1 * B0 + P0 * B1) (hb10 : b * M10 = P1 * C0 + P0 * C1) :
    let Bsh0 := B0 + y2 * B1 + y4 * B2
    let A0sh0 := P0 + y2 * P1 + y4 * P2 + y * Bsh0
    let A0sh1 := P1 + y * B1
    let A0sh2 := P2 + y * B2
    let A1sh0 := C0 + y2 * C1 + y4 * C2 + x * Bsh0
    let A1sh1 := C1 + x * B1
    let A1sh2 := C2 + x * B2
    let Ush := b + x * c + y * p
    let M20sh := M20 + y2 * M21
    let M10sh := M10 + y4 * M21
    (p * M21 = A1sh2 * B1 + A1sh1 * B2 ∧
     c * M21 = A0sh2 * B1 + A0sh1 * B2 ∧
     Ush * M21 = A0sh2 * A1sh1 + A0sh1 * A1sh2) ∧
    (p * M20sh = A1sh2 * Bsh0 + A1sh0 * B2 ∧
     c * M20sh = A0sh2 * Bsh0 + A0sh0 * B2 ∧
     Ush * M20sh = A0sh2 * A1sh0 + A0sh0 * A1sh2) ∧
    (p * M10sh = A1sh1 * Bsh0 + A1sh0 * B1 ∧
     c * M10sh = A0sh1 * Bsh0 + A0sh0 * B1 ∧
     Ush * M10sh = A0sh1 * A1sh0 + A0sh0 * A1sh1) := by
  intro Bsh0 A0sh0 A0sh1 A0sh2 A1sh0 A1sh1 A1sh2 Ush M20sh M10sh
  have h2z : ∀ f : R, f + f = 0 := CharTwo.add_self_eq_zero
  dsimp only [Bsh0, A0sh0, A0sh1, A0sh2, A1sh0, A1sh1, A1sh2, Ush, M20sh, M10sh]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · linear_combination hp21 - h2z (x * B2 * B1)
  · linear_combination hc21 - h2z (y * B2 * B1)
  · linear_combination hb21 + x * hc21 + y * hp21 - h2z (x * y * B2 * B1)
  · linear_combination hp20 + y2 * hp21 - h2z (y4 * C2 * B2) - h2z (x * B2 * (B0 + y2 * B1 + y4 * B2))
  · linear_combination hc20 + y2 * hc21 - h2z (y4 * P2 * B2) - h2z (y * B2 * (B0 + y2 * B1 + y4 * B2))
  · linear_combination hb20 + x * hc20 + y * hp20 + y2 * (hb21 + x * hc21 + y * hp21) -
      h2z (y4 * P2 * C2) - h2z (x * y4 * P2 * B2) - h2z (y * y4 * C2 * B2) -
      h2z (x * y * B2 * (B0 + y2 * B1 + y4 * B2))
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hp10 + y4 * hp21 -
      (y2 * C1 * B1 + x * B1 * (B0 + y2 * B1 + y4 * B2)) * h2
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hc10 + y4 * hc21 -
      (y2 * P1 * B1 + y * B1 * (B0 + y2 * B1 + y4 * B2)) * h2
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hb10 + x * hc10 + y * hp10 +
      y4 * (hb21 + x * hc21 + y * hp21) -
      (y2 * P1 * C1 + x * y2 * P1 * B1 + y * y2 * C1 * B1 +
        x * y * B1 * (B0 + y2 * B1 + y4 * B2)) * h2

/-! ### Part 4: `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Data Structure (`KerD45Data`) & Universal Bounds -/

/-- Bundled Table 4 input data for a single specialized `z`:
`F ∈ K_{W_F}(1)` with `W_F < 6 * wY - 1`, `deg_Y(f_1) = 4`, `Res_Y^{(5, 4)}(f_0, f_1) ≠ 0`,
and an agreement polynomial `P` (`deg P ≤ wY`) with `evalContact F P = 0` and `|A_z| ≥ A`. -/
structure KerD45Data where
  W_F : ℕ
  hWF_lo : 5 * wY ≤ W_F + 1
  hWF_hi : W_F + 1 < 6 * wY
  f_coord : KerDIdx wY W_F 1 → Fld
  y : Idx → Fld
  k : Idx → ℕ
  hvan : ∀ i : Idx,
    twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i)
  P : Fld[X]
  hPdeg : P.natDegree ≤ wY
  Az : Finset Idx
  hAz_card : A ≤ Az.card
  hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i
  hFvan : evalContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) P = 0
  hf1_deg : ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree = 4
  hRes_ne : Polynomial.resultant
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0)
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1) 5 4 ≠ 0

namespace KerD45Data

variable (D : KerD45Data)

noncomputable def F : ContactPoly Fld :=
  ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1

noncomputable def f0 : BiPoly Fld := D.F.coeff 0
noncomputable def f1 : BiPoly Fld := D.F.coeff 1
noncomputable def ResY : Fld[X] := Polynomial.resultant D.f0 D.f1 5 4

lemma hwY_pos (_ : KerD45Data) : 0 < wY := by norm_num [wY]

/-- Extracted `P_j(T)` (`j ∈ {0, 1, 2}`): coefficient of `Y^(2j)` in `f0(X, Y)` as a polynomial in `T = X^2`. -/
noncomputable def Pj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- Extracted `C_j(T)` (`j ∈ {0, 1, 2}`): even-`X` part of `Y^(2j)` in `f1(X, Y)`. -/
noncomputable def Cj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 1 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- Extracted `B_j(T)` (`j ∈ {0, 1, 2}`): coefficient of `Y^(2j+1)` in `f0` (and odd-`X` part of `Y^(2j)` in `f1`). -/
noncomputable def Bj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 1 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- `g_j(X) = C_j(X^2) + X B_j(X^2)` (`j = 0, 1, 2` correspond to `g_0, g_2, g_4`). -/
noncomputable def gj (j : Fin 3) : Fld[X] :=
  (D.Cj j).comp (X ^ 2) + X * (D.Bj j).comp (X ^ 2)

lemma e_b_lt_three (e : KerDIdx wY D.W_F 1) : e.1.2.2.1 < 3 := by
  have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  have hhi := D.hWF_hi
  have hw : 1 ≤ wY := by norm_num [wY]
  have : 2 * e.1.2.2.1 * wY ≤ D.W_F := by omega
  nlinarith

lemma e_kr_cases (e : KerDIdx wY D.W_F 1) :
    (e.1.1 = 0 ∧ e.1.2.1 = 0) ∨ (e.1.1 = 1 ∧ e.1.2.1 = 0) ∨ (e.1.1 = 0 ∧ e.1.2.1 = 1) := by
  have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  omega

lemma coeff_Pj (j : Fin 3) (a : ℕ) :
    (D.Pj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Pj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

lemma coeff_Cj (j : Fin 3) (a : ℕ) :
    (D.Cj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 1 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Cj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

lemma coeff_Bj (j : Fin 3) (a : ℕ) :
    (D.Bj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 1 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Bj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

attribute [irreducible] Pj Cj Bj

lemma two_mul_natDegree_Pj_le (j : Fin 3) : 2 * (D.Pj j).natDegree ≤ D.W_F - 2 * j.val * wY := by
  by_cases h0 : D.Pj j = 0
  · simp [h0]
  · have hnz : (D.Pj j).coeff (D.Pj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Pj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      simp only [zero_mul, zero_add] at hm
      omega
    · exact absurd rfl he

lemma two_mul_natDegree_Cj_le (j : Fin 3) :
    2 * (D.Cj j).natDegree ≤ D.W_F + 1 - (2 * j.val + 1) * wY := by
  by_cases h0 : D.Cj j = 0
  · simp [h0]
  · have hnz : (D.Cj j).coeff (D.Cj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Cj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      have hw : 1 ≤ wY := by norm_num [wY]
      have h1w : 1 ≤ (2 * j.val + 1) * wY := by nlinarith
      have hcost : 1 * (wY - 1) + 0 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY - 1 := by
        zify [hw, h1w]; ring
      omega
    · exact absurd rfl he

lemma two_mul_natDegree_Bj_le (j : Fin 3) :
    2 * (D.Bj j).natDegree ≤ D.W_F - (2 * j.val + 1) * wY := by
  by_cases h0 : D.Bj j = 0
  · simp [h0]
  · have hnz : (D.Bj j).coeff (D.Bj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Bj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      simp only [zero_mul, zero_add] at hm
      have : 1 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY := by ring
      omega
    · exact absurd rfl he

lemma five_wY_le_of_Bj2_ne_zero (hB2 : D.Bj 2 ≠ 0) : 5 * wY ≤ D.W_F := by
  have hnz : (D.Bj 2).coeff (D.Bj 2).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB2
  rw [coeff_Bj] at hnz
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  split_ifs at he with hc
  · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rcases hc with ⟨h1, h2, h3, h4⟩
    rw [h1, h2, h3, h4] at hm
    simp only [Fin.val_two, zero_mul, zero_add] at hm
    omega
  · exact absurd rfl he

lemma natDegree_gj_le (j : Fin 3) :
    (D.gj j).natDegree ≤ D.W_F + 1 - (2 * j.val + 1) * wY := by
  have h1 := D.two_mul_natDegree_Cj_le j
  have h2 := D.two_mul_natDegree_Bj_le j
  have h3 := natDegree_even_odd_le (D.Cj j) (D.Bj j)
  change (D.gj j).natDegree ≤ _ at h3
  have hle : (2 * j.val + 1) * wY ≤ D.W_F + 1 := by
    have := D.hWF_lo; have := j.isLt; nlinarith
  by_cases hB : D.Bj j = 0
  · simp only [hB, ↓reduceIte] at h3; omega
  · simp only [hB, ↓reduceIte] at h3
    have hleB : (2 * j.val + 1) * wY ≤ D.W_F := by
      have hnz : (D.Bj j).coeff (D.Bj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB
      rw [coeff_Bj] at hnz
      obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      split_ifs at he with hc
      · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
        rcases hc with ⟨h1, h2, h3, h4⟩
        rw [h1, h2, h3, h4] at hm
        simp only [zero_mul, zero_add] at hm
        have : 1 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY := by ring
        omega
      · exact absurd rfl he
    omega

lemma f0_eq_sum :
    D.f0 = ∑ j : Fin 3, (C ((D.Pj j).comp (X ^ 2)) * X ^ (2 * j.val) +
      C ((D.Bj j).comp (X ^ 2)) * X ^ (2 * j.val + 1)) := by
  apply Polynomial.ext; intro m
  apply Polynomial.ext; intro i
  have hL : (D.f0.coeff m).coeff i = ((D.F.coeff 0).coeff m).coeff i := rfl
  rw [hL, show D.F = ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1 from rfl,
    coeff_sum_kerDBasisPoly D.hwY_pos]
  rw [finset_sum_coeff, finset_sum_coeff]
  simp_rw [coeff_add, coeff_C_mul_X_pow]
  by_cases h00 : m % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte]
    have hRHS : (∑ j : Fin 3, ((if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i +
        (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i)) =
        if hm3 : m / 2 < 3 then (D.Pj ⟨m / 2, hm3⟩).coeff (i / 2) else 0 := by
      by_cases hm3 : m / 2 < 3
      · rw [dif_pos hm3, Finset.sum_eq_single ⟨m / 2, hm3⟩]
        · have hm2 : m = 2 * (⟨m / 2, hm3⟩ : Fin 3).val := by dsimp; omega
          have hmne : m ≠ 2 * (⟨m / 2, hm3⟩ : Fin 3).val + 1 := by dsimp; omega
          rw [if_pos hm2, if_neg hmne, coeff_zero, add_zero]
          have hi2 : i = 2 * (i / 2) := by omega
          conv_lhs => rw [hi2]
          rw [comp_X_sq_coeff_even]
        · intro j _ hne
          have h1 : m ≠ 2 * j.val := by intro h; apply hne; ext; dsimp; have := h00.1; omega
          have h2 : m ≠ 2 * j.val + 1 := by have := h00.1; omega
          rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [dif_neg hm3]; apply Finset.sum_eq_zero; intro j _
        have h1 : m ≠ 2 * j.val := by have := j.isLt; omega
        have h2 : m ≠ 2 * j.val + 1 := by have := h00.1; omega
        rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
    rw [hRHS]
    split_ifs with hmem hm3
    · rw [coeff_Pj, Finset.sum_eq_single ⟨(0, 0, m / 2, i / 2), hmem⟩]
      · simp
      · intro e _ hne
        split_ifs with hc
        · exfalso; apply hne; apply Subtype.ext
          rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · exfalso; exact hm3 (D.e_b_lt_three ⟨(0, 0, m / 2, i / 2), hmem⟩)
    · rw [coeff_Pj]; symm; apply Finset.sum_eq_zero; intro e _
      split_ifs with hc
      · exfalso; apply hmem
        rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
      · rfl
    · rfl
  · simp only [h00, ↓reduceIte]
    by_cases h10 : m % 2 = 1 ∧ i % 2 = 0
    · simp only [h10, and_self, ↓reduceIte]
      have hRHS : (∑ j : Fin 3, ((if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i +
          (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i)) =
          if hm3 : m / 2 < 3 then (D.Bj ⟨m / 2, hm3⟩).coeff (i / 2) else 0 := by
        by_cases hm3 : m / 2 < 3
        · rw [dif_pos hm3, Finset.sum_eq_single ⟨m / 2, hm3⟩]
          · have hm2 : m = 2 * (⟨m / 2, hm3⟩ : Fin 3).val + 1 := by dsimp; omega
            have hmne : m ≠ 2 * (⟨m / 2, hm3⟩ : Fin 3).val := by dsimp; omega
            rw [if_neg hmne, if_pos hm2, coeff_zero, zero_add]
            have hi2 : i = 2 * (i / 2) := by omega
            conv_lhs => rw [hi2]
            rw [comp_X_sq_coeff_even]
          · intro j _ hne
            have h1 : m ≠ 2 * j.val := by have := h10.1; omega
            have h2 : m ≠ 2 * j.val + 1 := by intro h; apply hne; ext; dsimp; have := h10.1; omega
            rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [dif_neg hm3]; apply Finset.sum_eq_zero; intro j _
          have h1 : m ≠ 2 * j.val := by have := h10.1; omega
          have h2 : m ≠ 2 * j.val + 1 := by have := j.isLt; omega
          rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
      rw [hRHS]
      split_ifs with hmem hm3
      · rw [coeff_Bj, Finset.sum_eq_single ⟨(0, 1, m / 2, i / 2), hmem⟩]
        · simp
        · intro e _ hne
          split_ifs with hc
          · exfalso; apply hne; apply Subtype.ext
            rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
          · rfl
        · intro h; exact absurd (Finset.mem_univ _) h
      · exfalso; exact hm3 (D.e_b_lt_three ⟨(0, 1, m / 2, i / 2), hmem⟩)
      · rw [coeff_Bj]; symm; apply Finset.sum_eq_zero; intro e _
        split_ifs with hc
        · exfalso; apply hmem
          rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
        · rfl
      · rfl
    · simp only [h10, ↓reduceIte]
      have hi_odd : i % 2 = 1 := by omega
      have h0_lt : ¬ (0 < (0 : ℕ)) := by omega
      simp only [h0_lt, and_false, ↓reduceIte]
      symm; apply Finset.sum_eq_zero; intro j _
      have hA : (if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i = 0 := by
        split_ifs
        · rw [show i = 2 * (i / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      have hB : (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i = 0 := by
        split_ifs
        · rw [show i = 2 * (i / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      rw [hA, hB, add_zero]

lemma f1_eq_sum : D.f1 = ∑ j : Fin 3, C (D.gj j) * X ^ (2 * j.val) := by
  apply Polynomial.ext; intro m
  apply Polynomial.ext; intro i
  have hL : (D.f1.coeff m).coeff i = ((D.F.coeff 1).coeff m).coeff i := rfl
  rw [hL, show D.F = ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1 from rfl,
    coeff_sum_kerDBasisPoly D.hwY_pos]
  rw [finset_sum_coeff, finset_sum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  have hRHS : (∑ j : Fin 3, (if m = 2 * j.val then D.gj j else 0).coeff i) =
      if hm : m % 2 = 0 ∧ m / 2 < 3 then
        (if i % 2 = 0 then (D.Cj ⟨m / 2, hm.2⟩).coeff (i / 2) else (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2))
      else 0 := by
    by_cases hm : m % 2 = 0 ∧ m / 2 < 3
    · rw [dif_pos hm, Finset.sum_eq_single ⟨m / 2, hm.2⟩]
      · have hm2 : m = 2 * (⟨m / 2, hm.2⟩ : Fin 3).val := by dsimp; omega
        rw [if_pos hm2]
        exact coeff_even_odd_pair (D.Cj ⟨m / 2, hm.2⟩) (D.Bj ⟨m / 2, hm.2⟩) i
      · intro j _ hne
        have h1 : m ≠ 2 * j.val := by intro h; apply hne; ext; dsimp; have := hm.1; omega
        rw [if_neg h1, coeff_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hm]; apply Finset.sum_eq_zero; intro j _
      have h1 : m ≠ 2 * j.val := by have := j.isLt; omega
      rw [if_neg h1, coeff_zero]
  rw [hRHS]
  by_cases h00 : m % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte]
    split_ifs with hmem hm
    · rw [coeff_Cj, Finset.sum_eq_single ⟨(1, 0, m / 2, i / 2), hmem⟩]
      · simp
      · intro e _ hne
        split_ifs with hc
        · exfalso; apply hne; apply Subtype.ext
          rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · exfalso; exact hm ⟨trivial, D.e_b_lt_three ⟨(1, 0, m / 2, i / 2), hmem⟩⟩
    · rw [coeff_Cj]; symm; apply Finset.sum_eq_zero; intro e _
      split_ifs with hc
      · exfalso; apply hmem
        rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
      · rfl
    · rfl
  · simp only [h00, ↓reduceIte]
    by_cases h10 : m % 2 = 1 ∧ i % 2 = 0
    · have hnotm : ¬ (m % 2 = 0 ∧ m / 2 < 3) := by omega
      rw [dif_neg hnotm]
      simp only [h10, and_self, ↓reduceIte]
      split_ifs with hmem
      · exfalso
        have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos 1 1 (m / 2) (i / 2)).mp hmem
        omega
      · rfl
    · simp only [h10, ↓reduceIte]
      by_cases h01 : m % 2 = 0 ∧ i % 2 = 1 ∧ 0 < (1 : ℕ)
      · have hi0 : i % 2 ≠ 0 := by omega
        have hif_rhs : (if hm : m % 2 = 0 ∧ m / 2 < 3 then
            (if i % 2 = 0 then (D.Cj ⟨m / 2, hm.2⟩).coeff (i / 2) else (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2))
            else 0) = if hm : m % 2 = 0 ∧ m / 2 < 3 then (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2) else 0 := by
          split_ifs <;> first | exact absurd ‹_› hi0 | rfl
        rw [hif_rhs]
        simp only [h01, and_self, ↓reduceIte, Nat.sub_self]
        split_ifs with hmem hm
        · rw [coeff_Bj, Finset.sum_eq_single ⟨(0, 1, m / 2, i / 2), hmem⟩]
          · simp
          · intro e _ hne
            split_ifs with hc
            · exfalso; apply hne; apply Subtype.ext
              rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
            · rfl
          · intro h; exact absurd (Finset.mem_univ _) h
        · exfalso; exact hm ⟨trivial, D.e_b_lt_three ⟨(0, 1, m / 2, i / 2), hmem⟩⟩
        · rw [coeff_Bj]; symm; apply Finset.sum_eq_zero; intro e _
          split_ifs with hc
          · exfalso; apply hmem
            rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
          · rfl
        · rfl
      · have hnotm : ¬ (m % 2 = 0 ∧ m / 2 < 3) := by omega
        rw [dif_neg hnotm]
        simp only [h01, ↓reduceIte]

lemma f0_coeff_even (j : Fin 3) : D.f0.coeff (2 * j.val) = (D.Pj j).comp (X ^ 2) := by
  rw [D.f0_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_pos rfl, if_neg (by omega), add_zero]
  · intro m _ hne
    have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
    have h2 : 2 * j.val ≠ 2 * m.val + 1 := by omega
    rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f0_coeff_odd (j : Fin 3) : D.f0.coeff (2 * j.val + 1) = (D.Bj j).comp (X ^ 2) := by
  rw [D.f0_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg (by omega), if_pos rfl, zero_add]
  · intro m _ hne
    have h1 : 2 * j.val + 1 ≠ 2 * m.val := by omega
    have h2 : 2 * j.val + 1 ≠ 2 * m.val + 1 := by intro h; apply hne; ext; omega
    rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f1_coeff_even (j : Fin 3) : D.f1.coeff (2 * j.val) = D.gj j := by
  rw [D.f1_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro m _ hne
    have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
    rw [coeff_C_mul_X_pow, if_neg h1]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f1_coeff_odd (m : ℕ) (hm : m % 2 = 1) : D.f1.coeff m = 0 := by
  rw [D.f1_eq_sum, finset_sum_coeff]
  apply Finset.sum_eq_zero; intro j _
  rw [coeff_C_mul_X_pow, if_neg (by omega)]

lemma f0_natDegree_le : D.f0.natDegree ≤ 5 := by
  rw [D.f0_eq_sum]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
  dsimp only [Function.comp_apply]
  have hj := j.isLt
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by omega))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by omega))

lemma f1_natDegree_eq : D.f1.natDegree = 4 := D.hf1_deg

lemma g2_ne_zero : D.gj 2 ≠ 0 := by
  have h4 := D.f1_coeff_even 2
  change D.f1.coeff 4 = D.gj 2 at h4
  rw [← h4, ← D.f1_natDegree_eq]
  exact leadingCoeff_ne_zero.mpr (by intro h0; have hd := D.f1_natDegree_eq; rw [h0, natDegree_zero] at hd; omega)

lemma f1_eval_P_ne_zero : D.f1.eval D.P ≠ 0 := by
  intro hf10
  have hF0 : D.f0.eval D.P + D.P.derivative * D.f1.eval D.P = 0 := by
    have hFdeg : D.F.natDegree ≤ 1 := by
      unfold F
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
      dsimp only [Function.comp_apply]
      have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      refine natDegree_mul_le.trans ?_
      have h1 : (cC (D.f_coord e)).natDegree = 0 := by unfold cC; simp
      have h2 : (kerDBasisPoly (A := Fld) e.1).natDegree ≤ e.1.1 + e.1.2.1 := by
        unfold kerDBasisPoly cR cY cX
        refine natDegree_mul_le.trans ?_
        have hb : ((C X ^ 2 : ContactPoly Fld) ^ e.1.2.2.1).natDegree = 0 := by
          rw [← map_pow, ← map_pow, natDegree_C]
        rw [hb, add_zero]
        refine natDegree_mul_le.trans ?_
        have ha : ((C (C X) ^ 2 : ContactPoly Fld) ^ e.1.2.2.2).natDegree = 0 := by
          rw [← map_pow, ← map_pow, natDegree_C]
        rw [ha, add_zero]
        refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le _) ?_)
        refine natDegree_pow_le.trans ?_
        have hlin : (C X + C (C X) * X : ContactPoly Fld).natDegree ≤ 1 :=
          (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
        nlinarith
      omega
    have hFexp : D.F = C D.f0 + C D.f1 * X := by
      apply Polynomial.ext; intro m; cases m with
      | zero => simp [f0, f1]
      | succ m' => cases m' with
        | zero => simp [f0, f1]
        | succ m'' =>
            rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hFdeg (by omega))]
            simp [coeff_C, coeff_mul_X]
    have hv := D.hFvan
    change evalContact D.F D.P = 0 at hv
    rw [hFexp] at hv
    simp only [evalContact, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      eval_add, eval_mul, eval_C, eval_X, Polynomial.coe_evalRingHom] at hv
    simpa [mul_comm] using hv
  rw [hf10, mul_zero, add_zero] at hF0
  let ι : Fld[X] →+* RatFunc Fld := algebraMap Fld[X] (RatFunc Fld)
  have hRes0' : ι D.ResY = 0 := by
    unfold ResY; rw [← Polynomial.resultant_map_map]
    exact P64Resultant.fixed_resultant_eq_zero_of_common_root
      (natDegree_map_le.trans D.f0_natDegree_le)
      (natDegree_map_le.trans (le_of_eq D.f1_natDegree_eq))
      (by omega)
      (by rw [Polynomial.eval_map_apply, hF0, map_zero])
      (by rw [Polynomial.eval_map_apply, hf10, map_zero])
  exact D.hRes_ne (IsFractionRing.injective Fld[X] (RatFunc Fld) (by change ι D.ResY = ι 0; rw [hRes0', map_zero]))

lemma ResY_ne_zero : D.ResY ≠ 0 := D.hRes_ne

lemma local_biMult_f0_f1 (i : Idx) :
    biMultGE (BinaryIRSProfile.domain i) (D.y i) D.f0 (2 * D.k i - 1) ∧
    biMultGE (BinaryIRSProfile.domain i) (D.y i) D.f1 (2 * D.k i - 1) :=
  kerD1_local_ords D.hwY_pos (BinaryIRSProfile.domain i) (D.y i) D.f_coord (D.hvan i)

attribute [irreducible] F f0 f1

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
