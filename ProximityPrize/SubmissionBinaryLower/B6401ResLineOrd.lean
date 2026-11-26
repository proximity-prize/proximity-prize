import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401HybridP64
import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
import ProximityPrize.SubmissionBinaryLower.P64Resultant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000

/-!
# Resultant Elimination & Line-Order Bridge (`B6401ResLineOrd`)

Connects `B6401QuotInterp.exists_quotient_contact_interpolant_wtd` (`F ∈ K_{W_F}(d)[Z]`,
`G ∈ K_W(s)[Z]`, `F ∤ G`) directly to `B6401HybridP64` and `B6401IntFarkas.checkCapWitness_sound`
via `Φ := Polynomial.resultant F G d s ∈ BiPoly (Polynomial F) = F[Z][X][Y]`:

1. `resultant_ne_zero_of_not_dvd`: irreducibility of `F` in `ContactPoly (RatFunc F)` with
   `F.natDegree = d ≥ 1` and `F ∤ G` over `RatFunc F` implies `Φ ≠ 0`.
2. `weightedSupportDegree_resultant_le` & `natDegree_resultant_le`:
   `wd Φ wY ≤ d * W + s * (W_F - d * (wY - 1))` and `Φ.natDegree ≤ W_Φ / wY`.
3. `degZ_resultant_le`: `∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ d * D_Z' + s * D_ZF`.
4. `triEval_resultant_eq_zero`: `evalContact (evalZContact F z) P = 0` and
   `evalContact (evalZContact G z) P = 0` imply `triEval Φ z P = 0`.
5. `lineOrd_resultant_deg1_ge` & `hΦgap_of_g_hi`: for `d = 1`, char-2 homogenization of the
   local `(t, w, u, R)` reduction yields `lineOrd Φ x0 y0 ≥ (2 * m : ℤ) + s * (2 * k - 1)`
   uniformly for ALL `k ≥ 0` (including `k = 0`), discharging `checkCapWitness_sound`'s `hΦgap`!
6. `card_roots_le_of_degZ_zero` & `card_common_roots_le_of_resultant`: when `deg_Z = 0`
   (`u₁ = 0`), gives the free `ScalarListBound` (`T.card ≤ B`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401ResLineOrd

open Polynomial B6401ContactKerD B6401QuotInterp B6401KerDOrders
open BCHKSSubstitutionVanish P64LineOrder P64Cofactor
open scoped BigOperators

/-! ### Part 1: Non-vanishing of `Polynomial.resultant F G d s` -/

/-- Lift `BiPoly (Polynomial F) →+* BiPoly (RatFunc F)` coefficientwise along `F[Z] ↪ F(Z)`. -/
noncomputable def liftBiRat {F : Type*} [Field F] :
    BiPoly (Polynomial F) →+* BiPoly (RatFunc F) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))

/-- Lift `ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F)` coefficientwise along `F[Z] ↪ F(Z)`. -/
noncomputable def liftCRat {F : Type*} [Field F] :
    ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F) :=
  Polynomial.mapRingHom liftBiRat

lemma liftBiRat_injective {F : Type*} [Field F] :
    Function.Injective (liftBiRat (F := F)) :=
  Polynomial.map_injective _ (Polynomial.map_injective _
    (IsFractionRing.injective (Polynomial F) (RatFunc F)))

lemma liftCRat_injective {F : Type*} [Field F] :
    Function.Injective (liftCRat (F := F)) :=
  Polynomial.map_injective _ liftBiRat_injective

/-- **Theorem 1:** If `Fpoly, Gpoly : ContactPoly (Polynomial F)` satisfy
`Irreducible (liftCRat Fpoly)`, `Fpoly.natDegree = d ≥ 1`, `Gpoly.natDegree ≤ s`, `Gpoly ≠ 0`,
and `Fpoly ∤ Gpoly` in `ContactPoly (RatFunc F)`, then `Polynomial.resultant Fpoly Gpoly d s ≠ 0`! -/
theorem resultant_ne_zero_of_not_dvd {F : Type*} [Field F]
    (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s : ℕ)
    (hirr : Irreducible (liftCRat Fpoly))
    (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s) (hGne : Gpoly ≠ 0)
    (hndvd : ¬ ∃ Q' : ContactPoly (RatFunc F), liftCRat Gpoly = liftCRat Fpoly * Q') :
    Polynomial.resultant Fpoly Gpoly d s ≠ 0 := by
  classical
  let A := BiPoly (RatFunc F)
  let K := FractionRing A
  have hinjAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let Frat : A[X] := liftCRat Fpoly
  let Grat : A[X] := liftCRat Gpoly
  have hFrat_deg : Frat.natDegree = d := by
    rw [show Frat = Fpoly.map liftBiRat from rfl,
      Polynomial.natDegree_map_eq_of_injective liftBiRat_injective, hFd]
  have hGrat_deg : Grat.natDegree ≤ s := by
    rw [show Grat = Gpoly.map liftBiRat from rfl,
      Polynomial.natDegree_map_eq_of_injective liftBiRat_injective]
    exact hGd
  have hprim : Frat.IsPrimitive := hirr.isPrimitive (by rw [hFrat_deg]; omega)
  let FK : K[X] := Frat.map (algebraMap A K)
  let GK : K[X] := Grat.map (algebraMap A K)
  have hirrK : Irreducible FK := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hndvd_rat : ¬ Frat ∣ Grat := fun ⟨Q', hQ'⟩ => hndvd ⟨Q', hQ'⟩
  have hndvdK : ¬ FK ∣ GK := fun h => hndvd_rat (hprim.dvd_of_fraction_map_dvd_fraction_map h)
  have hcop : IsCoprime FK GK := by
    let g := EuclideanDomain.gcd FK GK
    have hg_u : IsUnit g := by
      rcases EuclideanDomain.gcd_dvd_left FK GK with ⟨v, hv⟩
      rcases hirrK.isUnit_or_isUnit hv with hu | hu
      · exact hu
      · exfalso; apply hndvdK
        rcases EuclideanDomain.gcd_dvd_right FK GK with ⟨w, hw⟩
        obtain ⟨u, rfl⟩ := hu
        exact ⟨(u⁻¹ : K[X]ˣ) * w, by
          calc GK = g * w := hw
            _ = (g * ↑u) * (↑u⁻¹ * w) := by rw [mul_assoc, Units.mul_inv_cancel_left]
            _ = FK * (↑u⁻¹ * w) := by rw [← hv]⟩
    obtain ⟨u, hu⟩ := hg_u
    refine ⟨EuclideanDomain.gcdA FK GK * (u⁻¹ : K[X]ˣ), EuclideanDomain.gcdB FK GK * (u⁻¹ : K[X]ˣ), ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab FK GK
    change g = _ at hbez
    rw [← hu] at hbez
    calc EuclideanDomain.gcdA FK GK * ↑u⁻¹ * FK + EuclideanDomain.gcdB FK GK * ↑u⁻¹ * GK
        = (FK * EuclideanDomain.gcdA FK GK + GK * EuclideanDomain.gcdB FK GK) * ↑u⁻¹ := by ring
      _ = ↑u * ↑u⁻¹ := by rw [← hbez]
      _ = 1 := Units.mul_inv u
  have hresK_std : FK.resultant GK ≠ 0 := Polynomial.resultant_ne_zero FK GK hcop
  have hFKdeg : FK.natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective hinjAK, hFrat_deg]
  have hGKdeg_le : GK.natDegree ≤ s := by
    rw [Polynomial.natDegree_map_eq_of_injective hinjAK]; exact hGrat_deg
  have hFKne : FK ≠ 0 := hirrK.ne_zero
  have hFK_lead : FK.coeff d ≠ 0 := by
    rw [← hFKdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hFKne
  have hresK : FK.resultant GK d s ≠ 0 := by
    have hs_eq : GK.natDegree + (s - GK.natDegree) = s := Nat.add_sub_of_le hGKdeg_le
    rw [← hs_eq, Polynomial.resultant_add_right_deg]
    · refine mul_ne_zero (pow_ne_zero _ hFK_lead) ?_
      rw [← hFKdeg]
      exact hresK_std
    · exact le_rfl
  intro h0
  apply hresK
  let φ : BiPoly (Polynomial F) →+* K := (algebraMap A K).comp liftBiRat
  have hmap := Polynomial.resultant_map_map Fpoly Gpoly d s φ
  rw [h0, map_zero] at hmap
  have hFmap : Fpoly.map φ = FK := by
    dsimp only [φ, FK, Frat, liftCRat]; rw [← Polynomial.map_map]; rfl
  have hGmap : Gpoly.map φ = GK := by
    dsimp only [φ, GK, Grat, liftCRat]; rw [← Polynomial.map_map]; rfl
  rw [hFmap, hGmap] at hmap
  exact hmap

/-! ### Part 2: Weighted Support Degree & `Y`-Degree of `Polynomial.resultant F G d s` -/

section WeightedDeg

variable {A : Type*} [CommRing A] [IsDomain A]

lemma weightedSupportDegree_zero (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (0 : Polynomial (Polynomial A)) k = 0 := by
  simp [P64Caps.Weighted.weightedSupportDegree]

lemma weightedSupportDegree_one (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (1 : Polynomial (Polynomial A)) k = 0 := by
  classical
  apply Nat.le_zero.mp
  unfold P64Caps.Weighted.weightedSupportDegree
  apply Finset.sup_le; intro j hj
  have hj0 : j = 0 := by
    by_contra hne
    have : (1 : Polynomial (Polynomial A)).coeff j = 0 := by simp [coeff_one, hne]
    exact (Polynomial.mem_support_iff.mp hj) this
  subst hj0; simp

lemma weightedSupportDegree_neg (p : Polynomial (Polynomial A)) (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (-p) k =
      P64Caps.Weighted.weightedSupportDegree p k := by
  unfold P64Caps.Weighted.weightedSupportDegree
  rw [Polynomial.support_neg]
  apply Finset.sup_congr rfl; intro j _
  simp [Polynomial.coeff_neg, Polynomial.natDegree_neg]

lemma weightedSupportDegree_add_le (p q : Polynomial (Polynomial A)) (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (p + q) k ≤
      max (P64Caps.Weighted.weightedSupportDegree p k)
          (P64Caps.Weighted.weightedSupportDegree q k) := by
  classical
  conv_lhs => unfold P64Caps.Weighted.weightedSupportDegree
  apply Finset.sup_le; intro j hj
  have hnz : p.coeff j + q.coeff j ≠ 0 := by
    rw [← Polynomial.coeff_add]; exact Polynomial.mem_support_iff.mp hj
  rw [Polynomial.coeff_add]
  by_cases hp : p.coeff j = 0
  · rw [hp, zero_add]
    have hq : q.coeff j ≠ 0 := by simpa [hp] using hnz
    exact (P64Caps.Weighted.coeffWeight_le_of_ne q k j hq).trans (le_max_right _ _)
  · by_cases hq : q.coeff j = 0
    · rw [hq, add_zero]
      exact (P64Caps.Weighted.coeffWeight_le_of_ne p k j hp).trans (le_max_left _ _)
    · have hadd : (p.coeff j + q.coeff j).natDegree ≤ max (p.coeff j).natDegree (q.coeff j).natDegree :=
        Polynomial.natDegree_add_le _ _
      have hp' := P64Caps.Weighted.coeffWeight_le_of_ne p k j hp
      have hq' := P64Caps.Weighted.coeffWeight_le_of_ne q k j hq
      omega

lemma weightedSupportDegree_zsmul_le (u : ℤˣ) (p : Polynomial (Polynomial A)) (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (u • p) k ≤
      P64Caps.Weighted.weightedSupportDegree p k := by
  rw [Units.smul_def]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [weightedSupportDegree_neg]

lemma weightedSupportDegree_sum_le {α : Type*} (S : Finset α)
    (f : α → Polynomial (Polynomial A)) (k B : ℕ)
    (hf : ∀ x ∈ S, P64Caps.Weighted.weightedSupportDegree (f x) k ≤ B) :
    P64Caps.Weighted.weightedSupportDegree (∑ x ∈ S, f x) k ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [weightedSupportDegree_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (weightedSupportDegree_add_le _ _ k).trans
        (max_le (hf a (Finset.mem_insert_self a s))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)))

lemma weightedSupportDegree_mul_le_any (p q : Polynomial (Polynomial A)) (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (p * q) k ≤
      P64Caps.Weighted.weightedSupportDegree p k + P64Caps.Weighted.weightedSupportDegree q k := by
  by_cases hp : p = 0
  · simp [hp, weightedSupportDegree_zero]
  by_cases hq : q = 0
  · simp [hq, weightedSupportDegree_zero]
  exact P64Caps.Weighted.weightedSupportDegree_mul_le p q k hp hq

lemma weightedSupportDegree_prod_le {α : Type*} (S : Finset α)
    (f : α → Polynomial (Polynomial A)) (k : ℕ) :
    P64Caps.Weighted.weightedSupportDegree (∏ x ∈ S, f x) k ≤
      ∑ x ∈ S, P64Caps.Weighted.weightedSupportDegree (f x) k := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [weightedSupportDegree_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (weightedSupportDegree_mul_le_any _ _ k).trans (Nat.add_le_add_left ih _)

lemma weightedSupportDegree_coeff_add_le_of_wdeg (Q : ContactPoly A) (wY W k : ℕ)
    (hw : wdeg wY Q ≤ W) (hk : Q.coeff k ≠ 0) :
    P64Caps.Weighted.weightedSupportDegree (Q.coeff k) wY + k * (wY - 1) ≤ W := by
  classical
  have hsup : P64Caps.Weighted.weightedSupportDegree (Q.coeff k) wY ≤ W - k * (wY - 1) ∧
      k * (wY - 1) ≤ W := by
    have hkW : k * (wY - 1) ≤ W := by
      have hj0 : (Q.coeff k).coeff (Q.coeff k).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hk
      have ha0 : ((Q.coeff k).coeff (Q.coeff k).natDegree).coeff
          ((Q.coeff k).coeff (Q.coeff k).natDegree).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hj0
      have hbound := (wdeg_le_iff wY W Q).mp hw k (Q.coeff k).natDegree _ ha0
      omega
    refine ⟨?_, hkW⟩
    unfold P64Caps.Weighted.weightedSupportDegree
    apply Finset.sup_le; intro j hj
    have hjne : (Q.coeff k).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hane : ((Q.coeff k).coeff j).coeff ((Q.coeff k).coeff j).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hjne
    have hbound := (wdeg_le_iff wY W Q).mp hw k j _ hane
    have hmul : wY * j = j * wY := Nat.mul_comm wY j
    omega
  omega

/-- **Theorem 2a:** Weighted support degree of `Polynomial.resultant Fpoly Gpoly d s`:
`wd (Res_R(F, G)) wY ≤ d * W + s * (W_F - d * (wY - 1))`! -/
theorem weightedSupportDegree_resultant_le (Fpoly Gpoly : ContactPoly A)
    (wY W_F W d s : ℕ)
    (hFw : wdeg wY Fpoly ≤ W_F) (hGw : wdeg wY Gpoly ≤ W)
    (hWF_ge : d * (wY - 1) ≤ W_F) :
    P64Caps.Weighted.weightedSupportDegree (Polynomial.resultant Fpoly Gpoly d s) wY ≤
      d * W + s * (W_F - d * (wY - 1)) := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  apply weightedSupportDegree_sum_le
  intro σ _
  refine (weightedSupportDegree_zsmul_le _ _ wY).trans ?_
  by_cases hzero : ∃ j : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h0 : (∏ i : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [h0, weightedSupportDegree_zero]; exact Nat.zero_le _
  · push Not at hzero
    let jr : Fin d → ℕ := fun r' => (σ (Fin.castAdd s r')).val - r'.val
    let ir : Fin s → ℕ := fun r => (σ (Fin.natAdd d r)).val - r.val
    have hbounds :
      (∀ r' : Fin d, r'.val ≤ (σ (Fin.castAdd s r')).val ∧
        (σ (Fin.castAdd s r')).val ≤ r'.val + s ∧
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.castAdd s r')) (Fin.castAdd s r') =
          Gpoly.coeff (jr r')) ∧
      (∀ r : Fin s, r.val ≤ (σ (Fin.natAdd d r)).val ∧
        (σ (Fin.natAdd d r)).val ≤ r.val + d ∧
        Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.natAdd d r)) (Fin.natAdd d r) =
          Fpoly.coeff (ir r)) := by
      constructor
      · intro r'
        have hne := hzero (Fin.castAdd s r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r
        have hne := hzero (Fin.natAdd d r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin s, ir r) + (∑ r' : Fin d, jr r') = d * s := by
      have hperm_sum : ∑ k : Fin (d + s), (σ k).val = ∑ k : Fin (d + s), k.val :=
        Equiv.sum_comp σ (fun k : Fin (d + s) => k.val)
      have hsplit_σ : ∑ k : Fin (d + s), (σ k).val =
          (∑ r' : Fin d, (σ (Fin.castAdd s r')).val) +
          (∑ r : Fin s, (σ (Fin.natAdd d r)).val) := Fin.sum_univ_add _
      have hsplit_id : ∑ k : Fin (d + s), k.val =
          (∑ r' : Fin d, r'.val) + (∑ r : Fin s, (d + r.val)) := by
        rw [Fin.sum_univ_add]; rfl
      have hG : (∑ r' : Fin d, jr r') + (∑ r' : Fin d, r'.val) =
          ∑ r' : Fin d, (σ (Fin.castAdd s r')).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r' _
        have h1 := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin s, ir r) + (∑ r : Fin s, r.val) =
          ∑ r : Fin s, (σ (Fin.natAdd d r)).val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _
        have h1 := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd_id : ∑ r : Fin s, (d + r.val) = s * d + ∑ r : Fin s, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hcomm : s * d = d * s := mul_comm s d
      omega
    have hprod_le : P64Caps.Weighted.weightedSupportDegree
          (∏ j : Fin (d + s), Polynomial.sylvester Fpoly Gpoly d s (σ j) j) wY ≤
        (∑ r' : Fin d, P64Caps.Weighted.weightedSupportDegree (Gpoly.coeff (jr r')) wY) +
        (∑ r : Fin s, P64Caps.Weighted.weightedSupportDegree (Fpoly.coeff (ir r)) wY) := by
      rw [Fin.prod_univ_add]
      refine (weightedSupportDegree_mul_le_any _ _ wY).trans ?_
      apply Nat.add_le_add
      · refine (weightedSupportDegree_prod_le _ _ wY).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r' _; rw [(hbounds.1 r').2.2]
      · refine (weightedSupportDegree_prod_le _ _ wY).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r _; rw [(hbounds.2 r).2.2]
    have hsumG : (∑ r' : Fin d, P64Caps.Weighted.weightedSupportDegree (Gpoly.coeff (jr r')) wY) +
        (∑ r' : Fin d, jr r') * (wY - 1) ≤ d * W := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc _ ≤ ∑ _r' : Fin d, W := Finset.sum_le_sum fun r' _ => by
              have hne : Gpoly.coeff (jr r') ≠ 0 := by
                rw [← (hbounds.1 r').2.2]; exact hzero (Fin.castAdd s r')
              exact weightedSupportDegree_coeff_add_le_of_wdeg Gpoly wY W (jr r') hGw hne
        _ = d * W := by simp
    have hsumF : (∑ r : Fin s, P64Caps.Weighted.weightedSupportDegree (Fpoly.coeff (ir r)) wY) +
        (∑ r : Fin s, ir r) * (wY - 1) ≤ s * W_F := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc _ ≤ ∑ _r : Fin s, W_F := Finset.sum_le_sum fun r _ => by
              have hne : Fpoly.coeff (ir r) ≠ 0 := by
                rw [← (hbounds.2 r).2.2]; exact hzero (Fin.natAdd d r)
              exact weightedSupportDegree_coeff_add_le_of_wdeg Fpoly wY W_F (ir r) hFw hne
        _ = s * W_F := by simp
    have hmul_sub : s * (W_F - d * (wY - 1)) + d * s * (wY - 1) = s * W_F := by
      have h1 : s * (W_F - d * (wY - 1)) = s * W_F - s * (d * (wY - 1)) := Nat.mul_sub_left_distrib s _ _
      have h2 : s * (d * (wY - 1)) ≤ s * W_F := Nat.mul_le_mul_left s hWF_ge
      have h3 : d * s * (wY - 1) = s * (d * (wY - 1)) := by ring
      omega
    have htot_wt : ((∑ r : Fin s, ir r) + (∑ r' : Fin d, jr r')) * (wY - 1) = d * s * (wY - 1) := by
      rw [hsum]
    rw [Nat.add_mul] at htot_wt
    omega

/-- **Theorem 2b:** Any bivariate polynomial `Φ` satisfies `Φ.natDegree ≤ wd Φ wY / wY` for `wY > 0`. -/
theorem natDegree_le_weightedSupportDegree_div (Φ : Polynomial (Polynomial A)) (wY : ℕ)
    (hwY : 0 < wY) :
    Φ.natDegree ≤ P64Caps.Weighted.weightedSupportDegree Φ wY / wY := by
  by_cases hΦ : Φ = 0
  · simp [hΦ]
  · have hlead : Φ.coeff Φ.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hΦ
    have hw := P64Caps.Weighted.coeffWeight_le_of_ne Φ wY Φ.natDegree hlead
    rw [Nat.le_div_iff_mul_le hwY]
    have : Φ.natDegree * wY = wY * Φ.natDegree := Nat.mul_comm _ _
    omega

end WeightedDeg

/-! ### Part 3: `Z`-Degree Bound for `Polynomial.resultant F G d s` -/

section DegZ

variable {F : Type*} [Field F]

/-- Every coefficient `((Q.coeff j).coeff a)` in `F[Z]` has `natDegree ≤ D`. -/
def DegZLe (Q : BiPoly (Polynomial F)) (D : ℕ) : Prop :=
  ∀ j a, ((Q.coeff j).coeff a).natDegree ≤ D

lemma degZLe_zero (D : ℕ) : DegZLe (F := F) 0 D := by
  intro j a; simp

lemma degZLe_one : DegZLe (F := F) 1 0 := by
  intro j a
  by_cases hj : j = 0
  · subst hj; by_cases ha : a = 0
    · subst ha; simp
    · simp [Polynomial.coeff_one, ha]
  · simp [Polynomial.coeff_one, hj]

lemma degZLe_add {P Q : BiPoly (Polynomial F)} {D : ℕ}
    (hP : DegZLe P D) (hQ : DegZLe Q D) : DegZLe (P + Q) D := by
  intro j a
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP j a) (hQ j a))

lemma degZLe_neg {P : BiPoly (Polynomial F)} {D : ℕ} (hP : DegZLe P D) : DegZLe (-P) D := by
  intro j a
  rw [Polynomial.coeff_neg, Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hP j a

lemma degZLe_zsmul (u : ℤˣ) {P : BiPoly (Polynomial F)} {D : ℕ} (hP : DegZLe P D) :
    DegZLe (u • P) D := by
  rw [Units.smul_def]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hP
  · simpa using degZLe_neg hP

lemma degZLe_sum {α : Type*} (S : Finset α) (f : α → BiPoly (Polynomial F)) (D : ℕ)
    (hf : ∀ x ∈ S, DegZLe (f x) D) : DegZLe (∑ x ∈ S, f x) D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [degZLe_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact degZLe_add (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

lemma degZLe_mul {P Q : BiPoly (Polynomial F)} {D1 D2 : ℕ}
    (hP : DegZLe P D1) (hQ : DegZLe Q D2) : DegZLe (P * Q) (D1 + D2) := by
  intro j a
  rw [Polynomial.coeff_mul, finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun xy _ => ?_)
  dsimp only [Function.comp_apply]
  rw [Polynomial.coeff_mul]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun uv _ => ?_)
  dsimp only [Function.comp_apply]
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP xy.1 uv.1) (hQ xy.2 uv.2))

lemma degZLe_prod_const {α : Type*} (S : Finset α) (f : α → BiPoly (Polynomial F)) (D : ℕ)
    (hf : ∀ x ∈ S, DegZLe (f x) D) : DegZLe (∏ x ∈ S, f x) (S.card * D) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using degZLe_one (F := F)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.succ_mul, add_comm]
      exact degZLe_mul (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

/-- **Theorem 3:** Exact `Z`-degree cap for `Polynomial.resultant Fpoly Gpoly d s`:
`deg_Z(Res_R(F, G)) ≤ d * D_Z' + s * D_ZF`! -/
theorem degZ_resultant_le (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s D_ZF D_Z' : ℕ)
    (hFZ : ∀ k j a, (((Fpoly.coeff k).coeff j).coeff a).natDegree ≤ D_ZF)
    (hGZ : ∀ k j a, (((Gpoly.coeff k).coeff j).coeff a).natDegree ≤ D_Z') :
    ∀ j a, (((Polynomial.resultant Fpoly Gpoly d s).coeff j).coeff a).natDegree ≤
      d * D_Z' + s * D_ZF := by
  classical
  change DegZLe (Polynomial.resultant Fpoly Gpoly d s) (d * D_Z' + s * D_ZF)
  rw [Polynomial.resultant, Matrix.det_apply]
  apply degZLe_sum
  intro σ _
  apply degZLe_zsmul
  rw [Fin.prod_univ_add]
  apply degZLe_mul
  · have hprod := degZLe_prod_const (Finset.univ : Finset (Fin d))
      (fun r' : Fin d => Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.castAdd s r')) (Fin.castAdd s r')) D_Z'
      (fun r' _ => by
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc]
        split_ifs
        · exact hGZ _
        · exact degZLe_zero D_Z')
    simpa only [Finset.card_univ, Fintype.card_fin] using hprod
  · have hprod := degZLe_prod_const (Finset.univ : Finset (Fin s))
      (fun r : Fin s => Polynomial.sylvester Fpoly Gpoly d s (σ (Fin.natAdd d r)) (Fin.natAdd d r)) D_ZF
      (fun r _ => by
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc]
        split_ifs
        · exact hFZ _
        · exact degZLe_zero D_ZF)
    simpa only [Finset.card_univ, Fintype.card_fin] using hprod

end DegZ

/-! ### Part 4: Common Contact Root Vanishing (`triEval_resultant_eq_zero`) -/

lemma eval_map_triEvalHom_eq_evalContact {F : Type*} [Field F]
    (H : ContactPoly (Polynomial F)) (z : F) (P : Polynomial F) :
    (H.map (P64Cofactor.triEvalHom z P)).eval P.derivative =
      evalContact (evalZContact H z) P := by
  unfold evalContact evalZContact P64Cofactor.triEvalHom
  rw [Polynomial.map_map]

/-- **Theorem 4:** If `evalContact (evalZContact Fpoly z) P = 0` and
`evalContact (evalZContact Gpoly z) P = 0`, then
`triEval (Polynomial.resultant Fpoly Gpoly d s) z P = 0`! -/
theorem triEval_resultant_eq_zero {F : Type*} [Field F]
    (Fpoly Gpoly : ContactPoly (Polynomial F)) (d s : ℕ)
    (hFd : Fpoly.natDegree ≤ d) (hGd : Gpoly.natDegree ≤ s) (hpos : 0 < d + s)
    (z : F) (P : Polynomial F)
    (hFvan : evalContact (evalZContact Fpoly z) P = 0)
    (hGvan : evalContact (evalZContact Gpoly z) P = 0) :
    triEval (Polynomial.resultant Fpoly Gpoly d s) z P = 0 := by
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let φ : BiPoly (Polynomial F) →+* Polynomial F := P64Cofactor.triEvalHom z P
  let χ : BiPoly (Polynomial F) →+* RatFunc F := ψ.comp φ
  have hFmap : (Fpoly.map χ).eval (ψ P.derivative) = 0 := by
    dsimp only [χ]
    rw [← Polynomial.map_map, Polynomial.eval_map_apply, eval_map_triEvalHom_eq_evalContact, hFvan, map_zero]
  have hGmap : (Gpoly.map χ).eval (ψ P.derivative) = 0 := by
    dsimp only [χ]
    rw [← Polynomial.map_map, Polynomial.eval_map_apply, eval_map_triEvalHom_eq_evalContact, hGvan, map_zero]
  have hres0 : Polynomial.resultant (Fpoly.map χ) (Gpoly.map χ) d s = 0 := by
    have hPdeg : (Fpoly.map χ).natDegree ≤ d := Polynomial.natDegree_map_le.trans hFd
    have hHdeg : (Gpoly.map χ).natDegree ≤ s := Polynomial.natDegree_map_le.trans hGd
    by_cases hne : Fpoly.map χ ≠ 0 ∨ Gpoly.map χ ≠ 0
    · have hstd : Polynomial.resultant (Fpoly.map χ) (Gpoly.map χ) = 0 := by
        rw [Polynomial.resultant_eq_zero_iff]
        refine ⟨hne, ?_⟩
        rintro ⟨a, b, hab⟩
        have heval := congrArg (fun q : (RatFunc F)[X] => q.eval (ψ P.derivative)) hab
        simp [Polynomial.eval_add, Polynomial.eval_mul, hFmap, hGmap] at heval
      have hm : (Fpoly.map χ).natDegree + (d - (Fpoly.map χ).natDegree) = d := Nat.add_sub_of_le hPdeg
      have hn : (Gpoly.map χ).natDegree + (s - (Gpoly.map χ).natDegree) = s := Nat.add_sub_of_le hHdeg
      rw [← hm, ← hn, Polynomial.resultant_add_left_deg]
      · rw [Polynomial.resultant_add_right_deg]
        · simp [hstd]
        · exact le_rfl
      · exact le_rfl
    · push Not at hne
      rcases hne with ⟨h0F, h0G⟩
      rw [h0F, h0G]
      rcases d with _ | d' <;> rcases s with _ | s' <;> simp_all
  have hcomm := Polynomial.resultant_map_map Fpoly Gpoly d s χ
  rw [hres0] at hcomm
  have hψ : ψ (triEval (Polynomial.resultant Fpoly Gpoly d s) z P) = 0 := by
    exact hcomm.symm
  exact (IsFractionRing.injective (Polynomial F) (RatFunc F)) (by rw [map_zero]; exact hψ)

/-! ### Part 5: Exact Line-Order Lower Bound for `d = 1` (`lineOrd_resultant_deg1_ge`) -/

section Deg1LineOrd

variable {F : Type*} [Field F] [CharP F 2]

/-- `lineShift` packaged as a ring homomorphism `BiPoly (Polynomial F) →+* BiPoly (Polynomial F)`. -/
noncomputable def lineShiftHom (x0 : F) (y0 : Polynomial F) :
    BiPoly (Polynomial F) →+* BiPoly (Polynomial F) :=
  (Polynomial.mapRingHom (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x0)))).comp
    (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C y0)))

lemma lineShiftHom_apply (x0 : F) (y0 : Polynomial F) (Q : BiPoly (Polynomial F)) :
    lineShiftHom x0 y0 Q = lineShift Q x0 y0 := rfl

lemma lineShiftHom_C (x0 : F) (y0 : Polynomial F) (p : Polynomial (Polynomial F)) :
    lineShiftHom x0 y0 (Polynomial.C p) = Polynomial.C (p.comp (Polynomial.X + Polynomial.C (Polynomial.C x0))) := by
  simp [lineShiftHom]

lemma lineShiftHom_CC (x0 : F) (y0 c : Polynomial F) :
    lineShiftHom x0 y0 (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C c) := by
  simp [lineShiftHom]

lemma lineShiftHom_X (x0 : F) (y0 : Polynomial F) :
    lineShiftHom x0 y0 Polynomial.X = Polynomial.X + Polynomial.C (Polynomial.C y0) := by
  simp [lineShiftHom]

lemma lineShiftHom_CX (x0 : F) (y0 : Polynomial F) :
    lineShiftHom x0 y0 (Polynomial.C Polynomial.X) =
      Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0)) := by
  simp [lineShiftHom]

/-- Exact formula for `Polynomial.resultant Fpoly Gpoly 1 s` over any char-2 commutative ring `B`:
`Res(f_0 + f_1 R, G; 1, s) = ∑_{j=0}^s G.coeff j * f_0^j * f_1^(s - j)`! -/
theorem resultant_deg1_char2 {B : Type*} [CommRing B] [CharP B 2]
    (Fpoly Gpoly : B[X]) (s : ℕ) :
    Polynomial.resultant Fpoly Gpoly 1 s =
      ∑ j ∈ Finset.range (s + 1), Gpoly.coeff j * Fpoly.coeff 0 ^ j * Fpoly.coeff 1 ^ (s - j) := by
  classical
  have hneg1 : (-1 : B) = 1 := by
    have h2 : (2 : B) = 0 := CharTwo.two_eq_zero
    calc (-1 : B) = -1 + 2 := by rw [h2, add_zero]
      _ = 1 := by ring
  have hunit_smul : ∀ (u : ℤˣ) (x : B), u • x = x := by
    intro u x
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · rw [Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul, ← neg_one_mul, hneg1, one_mul]
  -- Define the unique valid permutation σ_j for each j ∈ {0, ..., s}:
  --   σ_j(0) = j,  σ_j(1 + r) = if r < j then r else r + 1.
  let mkPerm (j : Fin (s + 1)) : Equiv.Perm (Fin (1 + s)) :=
    { toFun := fun k =>
        if hk : k.val = 0 then ⟨j.val, by omega⟩
        else if k.val - 1 < j.val then ⟨k.val - 1, by omega⟩
        else ⟨k.val, by omega⟩
      invFun := fun i =>
        if i.val = j.val then ⟨0, by omega⟩
        else if hij : i.val < j.val then ⟨i.val + 1, by have := j.isLt; omega⟩
        else ⟨i.val, by omega⟩
      left_inv := fun k => by
        ext; dsimp only
        by_cases hk : k.val = 0
        · simp [hk]
        · by_cases hlt : k.val - 1 < j.val
          · have hne : k.val - 1 ≠ j.val := by omega
            simp only [hk, hlt, ↓reduceDIte, ↓reduceIte, hne]; omega
          · have hne : k.val ≠ j.val := by omega
            have hnotlt : ¬ k.val < j.val := by omega
            simp only [hk, hlt, ↓reduceDIte, ↓reduceIte, hne, hnotlt]
      right_inv := fun i => by
        ext; dsimp only
        by_cases heq : i.val = j.val
        · simp [heq]
        · by_cases hlt : i.val < j.val
          · have hne0 : i.val + 1 ≠ 0 := by omega
            have hlt' : i.val + 1 - 1 < j.val := by omega
            simp only [heq, hlt, ↓reduceIte, hne0, ↓reduceDIte, hlt']; omega
          · have hne0 : i.val ≠ 0 := by omega
            have hnotlt : ¬ i.val - 1 < j.val := by omega
            simp only [heq, hlt, ↓reduceIte, hne0, ↓reduceDIte, hnotlt] }
  have hmk_inj : Function.Injective mkPerm := by
    intro j1 j2 h
    have h0 := congrArg (fun p : Equiv.Perm (Fin (1 + s)) => (p ⟨0, by omega⟩).val) h
    simp [mkPerm] at h0
    exact Fin.ext h0
  have hmk_prod : ∀ j : Fin (s + 1),
      (∏ k : Fin (1 + s), Polynomial.sylvester Fpoly Gpoly 1 s (mkPerm j k) k) =
        Gpoly.coeff j.val * Fpoly.coeff 0 ^ j.val * Fpoly.coeff 1 ^ (s - j.val) := by
    intro j
    rw [Fin.prod_univ_add, Fin.prod_univ_one]
    have h0 : Polynomial.sylvester Fpoly Gpoly 1 s (mkPerm j (Fin.castAdd s 0)) (Fin.castAdd s 0) =
        Gpoly.coeff j.val := by
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc, mkPerm,
        Equiv.coe_fn_mk, Fin.val_castAdd, Fin.val_zero, ↓reduceDIte, Nat.zero_le, zero_add,
        Nat.le_of_lt_succ j.isLt, and_self, ↓reduceIte, Nat.sub_zero]
    rw [h0]
    have hright : (∏ r : Fin s,
        Polynomial.sylvester Fpoly Gpoly 1 s (mkPerm j (Fin.natAdd 1 r)) (Fin.natAdd 1 r)) =
        Fpoly.coeff 0 ^ j.val * Fpoly.coeff 1 ^ (s - j.val) := by
      have hpt : ∀ r : Fin s,
          Polynomial.sylvester Fpoly Gpoly 1 s (mkPerm j (Fin.natAdd 1 r)) (Fin.natAdd 1 r) =
            if r.val < j.val then Fpoly.coeff 0 else Fpoly.coeff 1 := by
        intro r
        have hne0 : (Fin.natAdd 1 r).val ≠ 0 := by simp
        have hsub1 : (Fin.natAdd 1 r).val - 1 = r.val := by simp
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc,
          mkPerm, Equiv.coe_fn_mk, hne0, ↓reduceDIte, hsub1]
        by_cases hlt : r.val < j.val
        · have hb : r.val ≤ r.val ∧ r.val ≤ r.val + 1 := by omega
          simp only [hlt, ↓reduceIte, hb, and_self, Nat.sub_self]
        · have hb : r.val ≤ (Fin.natAdd 1 r).val ∧ (Fin.natAdd 1 r).val ≤ r.val + 1 := by simp; omega
          have hsub : (Fin.natAdd 1 r).val - r.val = 1 := by simp
          simp only [hlt, ↓reduceIte, hb, and_self, hsub]
      simp_rw [hpt]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have hc1 : (Finset.univ.filter fun r : Fin s => r.val < j.val).card = j.val := by
        have hbij : (Finset.univ.filter fun r : Fin s => r.val < j.val) =
            (Finset.range j.val).attach.image fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩ := by
          ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, Subtype.exists, Finset.mem_range]
          constructor
          · intro hlt; exact ⟨r.val, hlt, Fin.ext rfl⟩
          · rintro ⟨a, ha, hEq⟩; rw [← congrArg Fin.val hEq]; exact ha
        rw [hbij, Finset.card_image_of_injective]
        · simp
        · intro a b h; exact Subtype.ext (congrArg Fin.val h)
      have hc2 : (Finset.univ.filter fun r : Fin s => ¬ r.val < j.val).card = s - j.val := by
        have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s)))
          (p := fun r : Fin s => r.val < j.val)
        simp only [Finset.card_univ, Fintype.card_fin, hc1] at hsum
        omega
      rw [hc1, hc2]
    rw [hright, mul_assoc]
  -- Show any permutation NOT of the form `mkPerm j` has a zero Sylvester entry!
  have hzero_other : ∀ σ : Equiv.Perm (Fin (1 + s)), (∀ j : Fin (s + 1), σ ≠ mkPerm j) →
      (∏ k : Fin (1 + s), Polynomial.sylvester Fpoly Gpoly 1 s (σ k) k) = 0 := by
    intro σ hne
    by_contra hprod_ne
    have hnz : ∀ k : Fin (1 + s), Polynomial.sylvester Fpoly Gpoly 1 s (σ k) k ≠ 0 :=
      fun k hk => hprod_ne (Finset.prod_eq_zero (Finset.mem_univ k) hk)
    have hband : ∀ r : Fin s, r.val ≤ (σ (Fin.natAdd 1 r)).val ∧ (σ (Fin.natAdd 1 r)).val ≤ r.val + 1 := by
      intro r
      have h := hnz (Fin.natAdd 1 r)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at h
      split_ifs at h with hc
      · exact hc
      · exact absurd rfl h
    let j0 : Fin (s + 1) := ⟨(σ ⟨0, by omega⟩).val, by have := (σ ⟨0, by omega⟩).isLt; omega⟩
    have hlow : ∀ r : ℕ, (hr : r < s) → r < j0.val → (σ (Fin.natAdd 1 ⟨r, hr⟩)).val = r := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
          intro hr hlt
          let tgt : Fin (1 + s) := ⟨r, by omega⟩
          let k := σ.symm tgt
          have hk0 : k.val ≠ 0 := by
            intro h0
            have hk_eq : k = ⟨0, by omega⟩ := Fin.ext h0
            have h1 := congrArg (fun x : Fin (1 + s) => x.val) (σ.apply_symm_apply tgt)
            rw [show σ (σ.symm tgt) = σ k from rfl, hk_eq] at h1
            dsimp [tgt, j0] at h1 hlt
            omega
          let r' : Fin s := ⟨k.val - 1, by have := k.isLt; omega⟩
          have hk_nat : k = Fin.natAdd 1 r' := Fin.ext (by simp [r']; omega)
          have hσr' : (σ (Fin.natAdd 1 r')).val = r := by
            rw [← hk_nat]; exact congrArg Fin.val (σ.apply_symm_apply tgt)
          have hb := hband r'
          rw [hσr'] at hb
          by_cases heq : r'.val = r
          · have hr'_eq : r' = ⟨r, hr⟩ := Fin.ext heq
            rwa [hr'_eq] at hσr'
          · have hlt' : r'.val < r := by omega
            have hprev := ih r'.val hlt' r'.isLt (by omega)
            rw [show (⟨r'.val, r'.isLt⟩ : Fin s) = r' from rfl, hσr'] at hprev
            omega
    have hhigh : ∀ d' : ℕ, (hd' : d' < s) → j0.val ≤ s - 1 - d' →
        (σ (Fin.natAdd 1 ⟨s - 1 - d', by omega⟩)).val = (s - 1 - d') + 1 := by
      intro d'
      induction d' using Nat.strong_induction_on with
      | _ d' ih =>
          intro hd' hge
          let r := s - 1 - d'
          let tgt : Fin (1 + s) := ⟨r + 1, by omega⟩
          let k := σ.symm tgt
          have hk0 : k.val ≠ 0 := by
            intro h0
            have hk_eq : k = ⟨0, by omega⟩ := Fin.ext h0
            have h1 := congrArg (fun x : Fin (1 + s) => x.val) (σ.apply_symm_apply tgt)
            rw [show σ (σ.symm tgt) = σ k from rfl, hk_eq] at h1
            dsimp [tgt, j0, r] at h1 hge
            omega
          let r' : Fin s := ⟨k.val - 1, by have := k.isLt; omega⟩
          have hk_nat : k = Fin.natAdd 1 r' := Fin.ext (by simp [r']; omega)
          have hσr' : (σ (Fin.natAdd 1 r')).val = r + 1 := by
            rw [← hk_nat]; exact congrArg Fin.val (σ.apply_symm_apply tgt)
          have hb := hband r'
          rw [hσr'] at hb
          by_cases heq : r'.val = r
          · have hr'_eq : r' = ⟨r, by omega⟩ := Fin.ext heq
            rwa [hr'_eq] at hσr'
          · have hgt' : r < r'.val := by omega
            let d'' := s - 1 - r'.val
            have hd''_lt : d'' < d' := by dsimp [d'', r]; omega
            have hprev := ih d'' hd''_lt (by dsimp [d'']; omega) (by dsimp [d'', r] at hgt' ⊢; omega)
            have hr''_eq : (⟨s - 1 - d'', by omega⟩ : Fin s) = r' := Fin.ext (by dsimp [d'']; omega)
            rw [hr''_eq, hσr'] at hprev
            dsimp [d'', r] at hprev hgt'; omega
    apply hne j0
    ext k
    by_cases hk : k.val = 0
    · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [hk0]; simp [mkPerm, j0]
    · let r : Fin s := ⟨k.val - 1, by have := k.isLt; omega⟩
      have hk_nat : k = Fin.natAdd 1 r := Fin.ext (by simp [r]; omega)
      rw [hk_nat]
      have hne0 : (Fin.natAdd 1 r).val ≠ 0 := by simp
      have hsub1 : (Fin.natAdd 1 r).val - 1 = r.val := by simp
      simp only [mkPerm, Equiv.coe_fn_mk, hne0, ↓reduceDIte, hsub1]
      by_cases hlt : r.val < j0.val
      · simp only [hlt, ↓reduceIte]
        exact hlow r.val r.isLt hlt
      · simp only [hlt, ↓reduceIte]
        have hrlt := r.isLt
        have h1 := hhigh (s - 1 - r.val) (by omega) (by omega)
        have hreq : (⟨s - 1 - (s - 1 - r.val), by omega⟩ : Fin s) = r := Fin.ext (by dsimp only; omega)
        rw [hreq] at h1
        have hval : (Fin.natAdd 1 r).val = r.val + 1 := by simp; omega
        omega
  rw [Polynomial.resultant, Matrix.det_apply]
  simp_rw [hunit_smul]
  have hS : (Finset.univ.image mkPerm : Finset (Equiv.Perm (Fin (1 + s)))) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hS]
  · rw [Finset.sum_image (fun a _ b _ h => hmk_inj h)]
    simp_rw [hmk_prod]
    rw [Fin.sum_univ_eq_sum_range (fun j => Gpoly.coeff j * Fpoly.coeff 0 ^ j * Fpoly.coeff 1 ^ (s - j)) (s + 1)]
  · intro σ _ hnot
    apply hzero_other σ
    intro j hj
    exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩)

/-- Total `(s, v)`-order predicate on `BiPoly A` (matching `P64LineOrder.OrdGE` on `lineShift`). -/
def BiOrdGE {A : Type*} [CommRing A] (S : BiPoly A) (r : ℕ) : Prop :=
  ∀ a b, a + b < r → (S.coeff b).coeff a = 0

lemma biOrdGE_zero {A : Type*} [CommRing A] (S : BiPoly A) : BiOrdGE S 0 := by
  intro a b hab; omega

lemma biOrdGE_of_zero {A : Type*} [CommRing A] (r : ℕ) : BiOrdGE (0 : BiPoly A) r := by
  intro a b _; simp

lemma biOrdGE_mono {A : Type*} [CommRing A] {S : BiPoly A} {r1 r2 : ℕ}
    (h : r1 ≤ r2) (hS : BiOrdGE S r2) : BiOrdGE S r1 :=
  fun a b hab => hS a b (lt_of_lt_of_le hab h)

lemma biOrdGE_add {A : Type*} [CommRing A] {S1 S2 : BiPoly A} {r : ℕ}
    (h1 : BiOrdGE S1 r) (h2 : BiOrdGE S2 r) : BiOrdGE (S1 + S2) r := by
  intro a b hab
  rw [Polynomial.coeff_add, Polynomial.coeff_add, h1 a b hab, h2 a b hab, add_zero]

lemma biOrdGE_sub {A : Type*} [CommRing A] {S1 S2 : BiPoly A} {r : ℕ}
    (h1 : BiOrdGE S1 r) (h2 : BiOrdGE S2 r) : BiOrdGE (S1 - S2) r := by
  intro a b hab
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, h1 a b hab, h2 a b hab, sub_zero]

lemma biOrdGE_sum {A α : Type*} [CommRing A] (T : Finset α) (f : α → BiPoly A) (r : ℕ)
    (hf : ∀ x ∈ T, BiOrdGE (f x) r) : BiOrdGE (∑ x ∈ T, f x) r := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [biOrdGE_of_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact biOrdGE_add (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

lemma biOrdGE_mul {A : Type*} [CommRing A] {S1 S2 : BiPoly A} {r1 r2 : ℕ}
    (h1 : BiOrdGE S1 r1) (h2 : BiOrdGE S2 r2) : BiOrdGE (S1 * S2) (r1 + r2) := by
  intro a b hab
  rw [Polynomial.coeff_mul, finset_sum_coeff]
  apply Finset.sum_eq_zero; intro xy hxy
  have hxy' : xy.1 + xy.2 = b := Finset.mem_antidiagonal.mp hxy
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero; intro uv huv
  have huv' : uv.1 + uv.2 = a := Finset.mem_antidiagonal.mp huv
  by_cases hlt1 : uv.1 + xy.1 < r1
  · rw [h1 uv.1 xy.1 hlt1, zero_mul]
  · rw [h2 uv.2 xy.2 (by omega), mul_zero]

lemma biOrdGE_pow {A : Type*} [CommRing A] {S : BiPoly A} {r : ℕ}
    (hS : BiOrdGE S r) (n : ℕ) : BiOrdGE (S ^ n) (n * r) := by
  induction n with
  | zero => simp [biOrdGE_zero]
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact biOrdGE_mul ih hS

lemma biOrdGE_CC_mul {A : Type*} [CommRing A] (c : A) {S : BiPoly A} {r : ℕ}
    (hS : BiOrdGE S r) : BiOrdGE (Polynomial.C (Polynomial.C c) * S) r := by
  simpa using biOrdGE_mul (biOrdGE_zero (Polynomial.C (Polynomial.C c))) hS

lemma biOrdGE_CX_sq {A : Type*} [CommRing A] : BiOrdGE (Polynomial.C (Polynomial.X ^ 2) : BiPoly A) 2 := by
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [Polynomial.coeff_C, if_pos rfl, Polynomial.coeff_X_pow]
    simp [show a ≠ 2 by omega]
  · rw [Polynomial.coeff_C, if_neg hb, Polynomial.coeff_zero]

lemma biOrdGE_X_sq {A : Type*} [CommRing A] : BiOrdGE (Polynomial.X ^ 2 : BiPoly A) 2 := by
  intro a b hab
  rw [Polynomial.coeff_X_pow]
  split_ifs with hb
  · omega
  · simp

lemma biOrdGE_X_mul_add_CX_mul {A : Type*} [CommRing A] (S1 S2 : BiPoly A) :
    BiOrdGE (Polynomial.X * S1 + Polynomial.C Polynomial.X * S2) 1 := by
  intro a b hab
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  subst ha0; subst hb0
  rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, zero_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul_zero]

/-- Invariant `j ≤ 2 * p + d` on monomials `t^p w^q R^j` of `LocalPoly A`. -/
def RLeTwoPAdd {A : Type*} [CommRing A] (H : LocalPoly A) (d : ℕ) : Prop :=
  ∀ p q j, (((H.coeff p).coeff q).coeff j) ≠ 0 → j ≤ 2 * p + d

lemma rLeTwoPAdd_locC {A : Type*} [CommRing A] (c : A) : RLeTwoPAdd (locC c) 0 := by
  intro p q j hnz
  unfold locC at hnz
  by_cases hp : p = 0 <;> by_cases hq : q = 0 <;> by_cases hj : j = 0 <;>
    simp_all [Polynomial.coeff_C]

lemma rLeTwoPAdd_locT {A : Type*} [CommRing A] : RLeTwoPAdd (locT (A := A)) 0 := by
  intro p q j hnz
  unfold locT at hnz
  rw [Polynomial.coeff_X] at hnz
  split_ifs at hnz with hp
  · subst hp
    by_cases hq : q = 0 <;> by_cases hj : j = 0 <;> simp_all [Polynomial.coeff_one]
  · simp at hnz

lemma rLeTwoPAdd_locW {A : Type*} [CommRing A] : RLeTwoPAdd (locW (A := A)) 0 := by
  intro p q j hnz
  unfold locW at hnz
  by_cases hp : p = 0
  · subst hp
    rw [Polynomial.coeff_C, if_pos rfl, Polynomial.coeff_X] at hnz
    split_ifs at hnz with hq
    · by_cases hj : j = 0 <;> simp_all [Polynomial.coeff_one]
    · simp at hnz
  · rw [Polynomial.coeff_C, if_neg hp] at hnz; simp at hnz

lemma rLeTwoPAdd_locR {A : Type*} [CommRing A] : RLeTwoPAdd (locR (A := A)) 1 := by
  intro p q j hnz
  unfold locR at hnz
  by_cases hp : p = 0
  · subst hp; rw [Polynomial.coeff_C, if_pos rfl] at hnz
    by_cases hq : q = 0
    · subst hq; rw [Polynomial.coeff_C, if_pos rfl, Polynomial.coeff_X] at hnz
      split_ifs at hnz with hj <;> [omega; simp at hnz]
    · rw [Polynomial.coeff_C, if_neg hq] at hnz; simp at hnz
  · rw [Polynomial.coeff_C, if_neg hp] at hnz; simp at hnz

lemma rLeTwoPAdd_mono {A : Type*} [CommRing A] {H : LocalPoly A} {d1 d2 : ℕ}
    (hd : d1 ≤ d2) (hH : RLeTwoPAdd H d1) : RLeTwoPAdd H d2 :=
  fun p q j hnz => (hH p q j hnz).trans (by omega)

lemma rLeTwoPAdd_add {A : Type*} [CommRing A] {H1 H2 : LocalPoly A} {d : ℕ}
    (h1 : RLeTwoPAdd H1 d) (h2 : RLeTwoPAdd H2 d) : RLeTwoPAdd (H1 + H2) d := by
  intro p q j hnz
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add] at hnz
  by_cases c1 : ((H1.coeff p).coeff q).coeff j = 0
  · apply h2 p q j; simpa [c1] using hnz
  · exact h1 p q j c1

lemma rLeTwoPAdd_mul {A : Type*} [CommRing A] {H1 H2 : LocalPoly A} {d1 d2 : ℕ}
    (h1 : RLeTwoPAdd H1 d1) (h2 : RLeTwoPAdd H2 d2) : RLeTwoPAdd (H1 * H2) (d1 + d2) := by
  intro p q j hnz
  rw [Polynomial.coeff_mul, finset_sum_coeff, finset_sum_coeff] at hnz
  obtain ⟨pp, hpp, hne1⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  have hpp' : pp.1 + pp.2 = p := Finset.mem_antidiagonal.mp hpp
  rw [Polynomial.coeff_mul, finset_sum_coeff] at hne1
  obtain ⟨qq, _, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
  rw [Polynomial.coeff_mul] at hne2
  obtain ⟨jj, hjj, hne3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne2
  have hjj' : jj.1 + jj.2 = j := Finset.mem_antidiagonal.mp hjj
  have hne_a : ((H1.coeff pp.1).coeff qq.1).coeff jj.1 ≠ 0 := left_ne_zero_of_mul hne3
  have hne_b : ((H2.coeff pp.2).coeff qq.2).coeff jj.2 ≠ 0 := right_ne_zero_of_mul hne3
  have hb1 := h1 pp.1 qq.1 jj.1 hne_a
  have hb2 := h2 pp.2 qq.2 jj.2 hne_b
  omega

lemma rLeTwoPAdd_pow {A : Type*} [CommRing A] {H : LocalPoly A} {d : ℕ}
    (hH : RLeTwoPAdd H d) (n : ℕ) : RLeTwoPAdd (H ^ n) (n * d) := by
  induction n with
  | zero =>
      rw [pow_zero, Nat.zero_mul]
      simpa [locC] using rLeTwoPAdd_locC (1 : A)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact rLeTwoPAdd_mul ih hH

lemma rLeTwoPAdd_localU {A : Type*} [CommRing A] : RLeTwoPAdd (localU (A := A)) 0 := by
  unfold localU
  apply rLeTwoPAdd_add
  · simpa using rLeTwoPAdd_pow (rLeTwoPAdd_locW (A := A)) 2
  · intro p q j hnz
    have hmul := rLeTwoPAdd_mul (rLeTwoPAdd_locT (A := A)) (rLeTwoPAdd_pow (rLeTwoPAdd_locR (A := A)) 2)
    -- Wait: locT has p = 1, so t * R^2 actually has j = 2 = 2 * 1 + 0! Check directly:
    have hcoeff : (((locT (A := A) * locR ^ 2).coeff p).coeff q).coeff j =
        if p = 1 ∧ q = 0 ∧ j = 2 then 1 else 0 := by
      unfold locT locR
      rw [← map_pow, ← map_pow]
      cases p with
      | zero => simp [Polynomial.coeff_X_mul_zero]
      | succ p' =>
          rw [Polynomial.coeff_X_mul]
          by_cases hp : p' = 0
          · subst hp
            simp only [Nat.reduceEqDiff, ↓reduceIte, true_and, Polynomial.coeff_C_zero,
              Polynomial.coeff_C, Polynomial.coeff_X_pow]
            by_cases hq : q = 0
            · subst hq; simp only [↓reduceIte, true_and]; by_cases hj : j = 2 <;> simp [hj, eq_comm]
            · simp [hq]
          · have hp1 : p' + 1 ≠ 1 := by omega
            simp only [hp, hp1, ↓reduceIte, false_and, Polynomial.coeff_C, Polynomial.coeff_zero]
    rw [hcoeff] at hnz
    split_ifs at hnz with h
    · omega
    · exact absurd rfl hnz

lemma rLeTwoPAdd_sum {A α : Type*} [CommRing A] (T : Finset α) (f : α → LocalPoly A) (d : ℕ)
    (hf : ∀ x ∈ T, RLeTwoPAdd (f x) d) : RLeTwoPAdd (∑ x ∈ T, f x) d := by
  classical
  induction T using Finset.induction_on with
  | empty => intro p q j hnz; simp at hnz
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact rLeTwoPAdd_add (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

lemma rLeTwoPAdd_kerDLocalPoly {A : Type*} [CommRing A] (x0 y0 : A) (e : ℕ × ℕ × ℕ × ℕ) :
    RLeTwoPAdd (kerDLocalPoly x0 y0 e) (e.1 + e.2.1) := by
  unfold kerDLocalPoly
  have h1 : RLeTwoPAdd (locR (A := A) ^ e.1) e.1 := by simpa using rLeTwoPAdd_pow rLeTwoPAdd_locR e.1
  have h2 : RLeTwoPAdd ((locC y0 + locC x0 * locR + locW) ^ e.2.1) e.2.1 := by
    have hbase : RLeTwoPAdd (locC y0 + locC x0 * locR + locW) 1 := by
      apply rLeTwoPAdd_add
      · apply rLeTwoPAdd_add (rLeTwoPAdd_mono (by omega) (rLeTwoPAdd_locC y0))
        simpa using rLeTwoPAdd_mul (rLeTwoPAdd_locC x0) rLeTwoPAdd_locR
      · exact rLeTwoPAdd_mono (by omega) rLeTwoPAdd_locW
    simpa using rLeTwoPAdd_pow hbase e.2.1
  have h3 : RLeTwoPAdd ((locC (x0 ^ 2) + locT) ^ e.2.2.2) 0 := by
    simpa using rLeTwoPAdd_pow (rLeTwoPAdd_add (rLeTwoPAdd_locC _) rLeTwoPAdd_locT) e.2.2.2
  have h4 : RLeTwoPAdd ((locC (y0 ^ 2) + localU) ^ e.2.2.1) 0 := by
    simpa using rLeTwoPAdd_pow (rLeTwoPAdd_add (rLeTwoPAdd_locC _) rLeTwoPAdd_localU) e.2.2.1
  simpa using rLeTwoPAdd_mul (rLeTwoPAdd_mul (rLeTwoPAdd_mul h1 h2) h3) h4

private lemma field_pow_step {K : Type*} [Field K] (c v s : K) (hs : s ≠ 0) (p j : ℕ)
    (hj : j ≤ 2 * p + 1) :
    c * s ^ (2 * p + 1 - j) * v ^ j = s * (c * (v ^ j / s ^ j) * (s ^ 2) ^ p) := by
  have hpow : s ^ (2 * p + 1 - j) * s ^ j = s * (s ^ 2) ^ p := by
    rw [← pow_mul, ← pow_succ', ← pow_add]; congr 1; omega
  have hsj : s ^ j ≠ 0 := pow_ne_zero j hs
  apply mul_right_cancel₀ hsj
  calc c * s ^ (2 * p + 1 - j) * v ^ j * s ^ j
      = c * v ^ j * (s ^ (2 * p + 1 - j) * s ^ j) := by ring
    _ = c * v ^ j * (s * (s ^ 2) ^ p) := by rw [hpow]
    _ = s * (c * (v ^ j / s ^ j * s ^ j) * (s ^ 2) ^ p) := by rw [div_mul_cancel₀ _ hsj]; ring
    _ = s * (c * (v ^ j / s ^ j) * (s ^ 2) ^ p) * s ^ j := by ring

private lemma field_lin_step {K : Type*} [Field K] (s v f0 f1 : K) (hs : s ≠ 0) :
    s * (f0 + f1 * (v / s)) = v * f1 + s * f0 := by
  calc s * (f0 + f1 * (v / s))
      = f1 * (v / s * s) + s * f0 := by ring
    _ = v * f1 + s * f0 := by rw [div_mul_cancel₀ _ hs]; ring

private lemma ring_sq_add_char2 {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (u v : R) :
    (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
  linear_combination u * v * h2

private lemma ring_yxr_char2 {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (y0 x0 v rvs : R) :
    y0 + x0 * rvs = (v + y0) + (v + x0 * rvs) := by
  linear_combination -v * h2

private noncomputable def psiVS {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K) :
    LocalPoly (Polynomial F) →+* K :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (ι.comp (Polynomial.C.comp Polynomial.C))
        (ι Polynomial.X / ι (Polynomial.C Polynomial.X)))
      (0 : K))
    (ι (Polynomial.C (Polynomial.X ^ 2)))

private noncomputable def chiVS {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K)
    (x0 : F) (y0 : Polynomial F) : ContactPoly (Polynomial F) →+* K :=
  Polynomial.eval₂RingHom (ι.comp (lineShiftHom x0 y0))
    (ι Polynomial.X / ι (Polynomial.C Polynomial.X))

private noncomputable def biOrdSliceS (Floc : LocalPoly (Polynomial F)) : BiPoly (Polynomial F) :=
  ∑ p ∈ Floc.support, ∑ j ∈ ((Floc.coeff p).coeff 0).support,
    Polynomial.C (Polynomial.C (((Floc.coeff p).coeff 0).coeff j)) *
      Polynomial.C (Polynomial.X ^ (2 * p + 1 - j)) * Polynomial.X ^ j

private lemma psiVS_locC {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K)
    (c : Polynomial F) : psiVS ι (locC c) = ι (Polynomial.C (Polynomial.C c)) := by
  simp only [psiVS, locC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply]

private lemma psiVS_locR {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K) :
    psiVS ι locR = ι Polynomial.X / ι (Polynomial.C Polynomial.X) := by
  simp only [psiVS, locR, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private lemma psiVS_locW {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K) :
    psiVS ι locW = 0 := by
  simp only [psiVS, locW, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

private lemma psiVS_locT {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K) :
    psiVS ι locT = ι (Polynomial.C (Polynomial.X ^ 2)) := by
  simp only [psiVS, locT, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

private lemma psiVS_localU {K : Type*} [Field K] (ι : BiPoly (Polynomial F) →+* K)
    (hιCX_ne : ι (Polynomial.C Polynomial.X) ≠ 0) :
    psiVS ι localU = ι (Polynomial.X ^ 2) := by
  unfold localU
  rw [map_add, map_pow, map_mul, map_pow, psiVS_locW, psiVS_locT, psiVS_locR]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add, div_pow, map_pow]
  exact mul_div_cancel₀ _ (pow_ne_zero 2 hιCX_ne)

private lemma psiVS_kerDLocalPoly_eq_chiVS {K : Type*} [Field K] [CharP K 2]
    (ι : BiPoly (Polynomial F) →+* K) (hιCX_ne : ι (Polynomial.C Polynomial.X) ≠ 0)
    (x0 : F) (y0 : Polynomial F) (e : ℕ × ℕ × ℕ × ℕ) :
    psiVS ι (kerDLocalPoly (C x0) y0 e) = chiVS ι x0 y0 (kerDBasisPoly e) := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases e with ⟨k1, r1, b1, a1⟩
  unfold kerDLocalPoly kerDBasisPoly
  simp only [map_mul, map_pow, map_add, psiVS_locR, psiVS_locC, psiVS_locW, psiVS_locT,
    psiVS_localU ι hιCX_ne, add_zero]
  have hχ_cR : chiVS ι x0 y0 cR = ι Polynomial.X / ι (Polynomial.C Polynomial.X) := by
    simp only [chiVS, cR, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hχ_cX : chiVS ι x0 y0 cX = ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) := by
    unfold chiVS cX
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_CX]
  have hχ_cY : chiVS ι x0 y0 cY = ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) := by
    unfold chiVS cY
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_X]
  rw [hχ_cR, hχ_cX, hχ_cY]
  have hsqK : ∀ u v : K, (u + v) ^ 2 = u ^ 2 + v ^ 2 := ring_sq_add_char2 h2K
  have hX2 : ι (Polynomial.C (Polynomial.C (C x0))) ^ 2 + ι (Polynomial.C Polynomial.X) ^ 2 =
      ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) ^ 2 := by
    rw [Polynomial.C_add, map_add, hsqK, add_comm]
  have hY2 : ι (Polynomial.C (Polynomial.C y0)) ^ 2 + ι Polynomial.X ^ 2 =
      ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) ^ 2 := by
    rw [map_add, hsqK, add_comm]
  have hYXR : ι (Polynomial.C (Polynomial.C y0)) +
      ι (Polynomial.C (Polynomial.C (C x0))) * (ι Polynomial.X / ι (Polynomial.C Polynomial.X)) =
      ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) +
        ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) *
          (ι Polynomial.X / ι (Polynomial.C Polynomial.X)) := by
    rw [Polynomial.C_add, map_add, map_add, add_mul]
    rw [mul_div_cancel₀ _ hιCX_ne]
    exact ring_yxr_char2 h2K _ _ (ι Polynomial.X) (ι Polynomial.X / ι (Polynomial.C Polynomial.X))
  rw [hX2, hY2, hYXR]

private lemma chiVS_Fpoly_eq {K : Type*} [Field K]
    (ι : BiPoly (Polynomial F) →+* K) (hιCX_ne : ι (Polynomial.C Polynomial.X) ≠ 0)
    (x0 : F) (y0 : Polynomial F) (Fpoly : ContactPoly (Polynomial F)) (hFdeg_le : Fpoly.natDegree ≤ 1) :
    ι (Polynomial.C Polynomial.X) * chiVS ι x0 y0 Fpoly =
      ι (Polynomial.X * lineShift (Fpoly.coeff 1) x0 y0 +
        Polynomial.C Polynomial.X * lineShift (Fpoly.coeff 0) x0 y0) := by
  have hFexp : Fpoly = Polynomial.C (Fpoly.coeff 0) + Polynomial.C (Fpoly.coeff 1) * Polynomial.X := by
    ext m
    cases m with
    | zero => simp
    | succ m' =>
        cases m' with
        | zero => simp
        | succ m'' =>
            have hlt : Fpoly.natDegree < m''.succ.succ := lt_of_le_of_lt hFdeg_le (by omega)
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
            simp [Polynomial.coeff_mul_X]
  conv_lhs => rw [hFexp]
  simp only [chiVS, map_add, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X, RingHom.comp_apply, lineShiftHom_apply]
  exact field_lin_step (ι (Polynomial.C Polynomial.X)) (ι Polynomial.X)
    (ι (lineShift (Fpoly.coeff 0) x0 y0)) (ι (lineShift (Fpoly.coeff 1) x0 y0)) hιCX_ne

private lemma map_biOrdSliceS_eq {K : Type*} [Field K]
    (ι : BiPoly (Polynomial F) →+* K) (hιCX_ne : ι (Polynomial.C Polynomial.X) ≠ 0)
    (Floc : LocalPoly (Polynomial F)) (hFloc_R : RLeTwoPAdd Floc 1) :
    ι (biOrdSliceS Floc) = ι (Polynomial.C Polynomial.X) * psiVS ι Floc := by
  have hψ_eval : psiVS ι Floc =
      ∑ p ∈ Floc.support, ∑ j ∈ ((Floc.coeff p).coeff 0).support,
        ι (Polynomial.C (Polynomial.C (((Floc.coeff p).coeff 0).coeff j))) *
          (ι Polynomial.X / ι (Polynomial.C Polynomial.X)) ^ j *
          ι (Polynomial.C (Polynomial.X ^ 2)) ^ p := by
    unfold psiVS
    change Polynomial.eval₂ _ _ Floc = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl; intro p _
    change Polynomial.eval₂ _ (0 : K) (Floc.coeff p) * _ = _
    rw [Polynomial.eval₂_at_zero]
    change Polynomial.eval₂ _ (ι Polynomial.X / ι (Polynomial.C Polynomial.X)) ((Floc.coeff p).coeff 0) * _ = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rfl
  rw [hψ_eval, Finset.mul_sum]
  unfold biOrdSliceS; rw [map_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  have hjne : ((Floc.coeff p).coeff 0).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hjle : j ≤ 2 * p + 1 := hFloc_R p 0 j hjne
  have hC2 : ι (Polynomial.C (Polynomial.X ^ 2)) = ι (Polynomial.C Polynomial.X) ^ 2 := by
    rw [← map_pow, Polynomial.C_pow]
  have hCj : ι (Polynomial.C (Polynomial.X ^ (2 * p + 1 - j))) =
      ι (Polynomial.C Polynomial.X) ^ (2 * p + 1 - j) := by
    rw [← map_pow, Polynomial.C_pow]
  rw [map_mul, map_mul, hCj, map_pow, hC2, div_pow]
  exact field_pow_step (ι (Polynomial.C (Polynomial.C (((Floc.coeff p).coeff 0).coeff j))))
    (ι Polynomial.X) (ι (Polynomial.C Polynomial.X)) hιCX_ne p j hjle

private lemma biOrdGE_biOrdSliceS {k : ℕ} (Floc : LocalPoly (Polynomial F))
    (hFloc_R : RLeTwoPAdd Floc 1) (hvan : twOrdGE Floc k) :
    BiOrdGE (biOrdSliceS Floc) (2 * k + 1) := by
  unfold biOrdSliceS
  apply biOrdGE_sum; intro p _
  apply biOrdGE_sum; intro j hj
  have hjne : ((Floc.coeff p).coeff 0).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hjle : j ≤ 2 * p + 1 := hFloc_R p 0 j hjne
  have hpk : k ≤ p := by
    by_contra hlt
    have h0 := hvan p 0 (by omega)
    exact hjne (by rw [show (Floc.coeff p).coeff 0 = 0 from h0, Polynomial.coeff_zero])
  rw [mul_assoc]
  apply biOrdGE_CC_mul
  have hterm : BiOrdGE (Polynomial.C (Polynomial.X ^ (2 * p + 1 - j)) * Polynomial.X ^ j : BiPoly (Polynomial F))
      ((2 * p + 1 - j) + j) := by
    apply biOrdGE_mul
    · intro a b hab
      by_cases hb : b = 0
      · subst hb; rw [Polynomial.coeff_C, if_pos rfl, Polynomial.coeff_X_pow]
        simp [show a ≠ 2 * p + 1 - j by omega]
      · rw [Polynomial.coeff_C, if_neg hb, Polynomial.coeff_zero]
    · intro a b hab
      rw [Polynomial.coeff_X_pow]
      split_ifs with hb
      · omega
      · simp
  exact biOrdGE_mono (by omega) hterm

private lemma natDegree_kerDBasisPoly_le (e : ℕ × ℕ × ℕ × ℕ) :
    (kerDBasisPoly (A := Polynomial F) e).natDegree ≤ e.1 + e.2.1 := by
  unfold kerDBasisPoly cR cY cX
  refine Polynomial.natDegree_mul_le.trans ?_
  have hb : ((Polynomial.C Polynomial.X ^ 2 : ContactPoly (Polynomial F)) ^ e.2.2.1).natDegree = 0 := by
    rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
  rw [hb, add_zero]
  refine Polynomial.natDegree_mul_le.trans ?_
  have ha : ((Polynomial.C (Polynomial.C Polynomial.X) ^ 2 : ContactPoly (Polynomial F)) ^ e.2.2.2).natDegree = 0 := by
    rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
  rw [ha, add_zero]
  have hmul := Polynomial.natDegree_mul_le (p := (Polynomial.X : ContactPoly (Polynomial F)) ^ e.1)
    (q := (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X) ^ e.2.1)
  have hx : ((Polynomial.X : ContactPoly (Polynomial F)) ^ e.1).natDegree ≤ e.1 :=
    Polynomial.natDegree_X_pow_le _
  have hlin : (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
      ContactPoly (Polynomial F)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hp : ((Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
      ContactPoly (Polynomial F)) ^ e.2.1).natDegree ≤ e.2.1 :=
    Polynomial.natDegree_pow_le.trans (by nlinarith)
  omega

/-- Polymorphic field helper for `biOrdGE_v_sf1_add_s_sf0` (avoids `FractionRing` `whnf` timeouts). -/
private lemma biOrdGE_v_sf1_add_s_sf0_field {K : Type*} [Field K] [CharP K 2]
    (ι : BiPoly (Polynomial F) →+* K) (hι_inj : Function.Injective ι)
    {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let sf0 := lineShift (Fpoly.coeff 0) x0 y0
    let sf1 := lineShift (Fpoly.coeff 1) x0 y0
    BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1) := by
  classical
  intro Fpoly sf0 sf1
  have hCX_ne : (Polynomial.C Polynomial.X : BiPoly (Polynomial F)) ≠ 0 := by
    intro h0; exact Polynomial.X_ne_zero (Polynomial.C_eq_zero.mp h0)
  have hιCX_ne : ι (Polynomial.C Polynomial.X) ≠ 0 := by
    intro h0; exact hCX_ne (hι_inj (by rw [map_zero]; exact h0))
  set Floc : LocalPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1
  have hFloc_eq : psiVS ι Floc = chiVS ι x0 y0 Fpoly := by
    dsimp only [Floc, Fpoly]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl; intro e _
    rw [map_mul, map_mul, psiVS_locC, psiVS_kerDLocalPoly_eq_chiVS ι hιCX_ne x0 y0 e.1]
    have hχ_cC : chiVS ι x0 y0 (cC (f_coord e)) = ι (Polynomial.C (Polynomial.C (f_coord e))) := by
      unfold chiVS cC
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_CC]
    rw [hχ_cC]
  have hFdeg_le : Fpoly.natDegree ≤ 1 := by
    dsimp only [Fpoly]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
    dsimp only [Function.comp_apply]
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    refine Polynomial.natDegree_mul_le.trans ?_
    have h1 : (cC (f_coord e)).natDegree = 0 := by unfold cC; simp
    have h2 := natDegree_kerDBasisPoly_le (F := F) e.1
    omega
  have hFloc_R : RLeTwoPAdd Floc 1 := by
    apply rLeTwoPAdd_sum; intro e _
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    have h1 := rLeTwoPAdd_mul (rLeTwoPAdd_locC (f_coord e)) (rLeTwoPAdd_kerDLocalPoly (C x0) y0 e.1)
    rw [zero_add] at h1
    exact rLeTwoPAdd_mono hmem.2.1 h1
  have hχF := chiVS_Fpoly_eq ι hιCX_ne x0 y0 Fpoly hFdeg_le
  have hS_eq := map_biOrdSliceS_eq ι hιCX_ne Floc hFloc_R
  have heqB : Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0 = biOrdSliceS Floc :=
    hι_inj (by rw [← hχF, ← hFloc_eq, hS_eq])
  rw [heqB]
  exact biOrdGE_biOrdSliceS Floc hFloc_R hvan

/-- **15-line char-2 magic:** For `F ∈ K_{W_F}(1)[Z]` with `twOrdGE Floc k`,
`X * sf1 + C X * sf0` (`v * sf1 + s * sf0`) has total `(s, v)`-order `≥ 2 * k + 1`! -/
theorem biOrdGE_v_sf1_add_s_sf0 {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let sf0 := lineShift (Fpoly.coeff 0) x0 y0
    let sf1 := lineShift (Fpoly.coeff 1) x0 y0
    BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1) := by
  let K := FractionRing (BiPoly (Polynomial F))
  let ι : BiPoly (Polynomial F) →+* K := algebraMap (BiPoly (Polynomial F)) K
  have hι_inj : Function.Injective ι := IsFractionRing.injective (BiPoly (Polynomial F)) K
  haveI : CharP K 2 := charP_of_injective_ringHom hι_inj 2
  exact biOrdGE_v_sf1_add_s_sf0_field ι hι_inj hwY x0 y0 f_coord hvan

/-- Lift `B6401KerDOrders.kerD1_local_ords` from `RatFunc F` back to `BiPoly (Polynomial F)`:
`BiOrdGE sf0 (2 * k - 1) ∧ BiOrdGE sf1 (2 * k - 1)`! -/
theorem biOrdGE_sf0_sf1_of_twOrdGE {wY W_F k : ℕ} (hwY : 0 < wY)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    BiOrdGE (lineShift (Fpoly.coeff 0) x0 y0) (2 * k - 1) ∧
    BiOrdGE (lineShift (Fpoly.coeff 1) x0 y0) (2 * k - 1) := by
  intro Fpoly
  let alg : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have halg_inj : Function.Injective alg := IsFractionRing.injective (Polynomial F) (RatFunc F)
  haveI : CharP (RatFunc F) 2 := charP_of_injective_ringHom halg_inj 2
  let mapL : LocalPoly (Polynomial F) →+* LocalPoly (RatFunc F) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom alg))
  have hvan_rat : twOrdGE (∑ e : KerDIdx wY W_F 1,
      locC (alg (f_coord e)) * kerDLocalPoly (alg (C x0)) (alg y0) e.1) k := by
    have hmap_sum : mapL (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) =
        ∑ e : KerDIdx wY W_F 1, locC (alg (f_coord e)) * kerDLocalPoly (alg (C x0)) (alg y0) e.1 := by
      rw [map_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [map_mul]; congr 1
      · unfold locC; simp [mapL]
      · unfold kerDLocalPoly localU locR locW locT locC
        simp [mapL, map_mul, map_pow, map_add]
    intro p q hpq
    rw [← hmap_sum]
    unfold twCoeff mapL
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    rw [show ((∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1).coeff p).coeff q = 0
      from hvan p q hpq, Polynomial.map_zero]
  have hords := B6401KerDOrders.kerD1_local_ords (F := RatFunc F) hwY (alg (C x0)) (alg y0)
    (fun e => alg (f_coord e)) hvan_rat
  have hmap_shift : ∀ r : ℕ,
      liftBiRat (lineShift (Fpoly.coeff r) x0 y0) =
        shiftBi (alg (C x0)) (alg y0)
          ((∑ e : KerDIdx wY W_F 1, cC (alg (f_coord e)) * kerDBasisPoly e.1).coeff r) := by
    intro r
    have hF_rat : liftCRat Fpoly = ∑ e : KerDIdx wY W_F 1, cC (alg (f_coord e)) * kerDBasisPoly e.1 := by
      dsimp only [Fpoly]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro e _
      rw [map_mul]; congr 1
      · unfold cC liftCRat liftBiRat
        simp only [Polynomial.coe_mapRingHom, Polynomial.map_C]
        rfl
      · unfold kerDBasisPoly cR cY cX liftCRat liftBiRat
        simp only [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    have hcoeff_r : liftBiRat (Fpoly.coeff r) =
        (∑ e : KerDIdx wY W_F 1, cC (alg (f_coord e)) * kerDBasisPoly e.1).coeff r := by
      rw [← hF_rat]; simp [liftCRat]
    rw [← hcoeff_r]
    generalize Fpoly.coeff r = Q
    have hinner : (Polynomial.mapRingHom alg).comp (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x0))) =
        (Polynomial.compRingHom (Polynomial.C (alg (Polynomial.C x0)) + Polynomial.X)).comp (Polynomial.mapRingHom alg) := by
      apply RingHom.ext; intro p
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_compRingHom,
        Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, add_comm]
    unfold lineShift Polynomial.Bivariate.shift shiftBi liftBiRat
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_map]
    rw [hinner, add_comm (Polynomial.C (Polynomial.C (alg y0))) Polynomial.X]
    simp only [Polynomial.coe_compRingHom, Polynomial.C_comp, Polynomial.map_C]
    rfl
  constructor
  · intro a b hab
    have h0 := hords.1 a b hab
    rw [← hmap_shift 0] at h0
    simp only [liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h0
    exact halg_inj (h0.trans (map_zero alg).symm)
  · intro a b hab
    have h0 := hords.2 a b hab
    rw [← hmap_shift 1] at h0
    simp only [liftBiRat, Polynomial.coe_mapRingHom, Polynomial.coeff_map] at h0
    exact halg_inj (h0.trans (map_zero alg).symm)

/-- Denominator-free homogenization of `localBasisElem (q, j, a, b)` at `R = sf0 / sf1`,
multiplied by `sf1^s` (valid whenever `q + j ≤ s`):
`(v * sf1 + s * sf0)^q * sf0^j * sf1^(s - q - j) * (s^2)^a * (v^2)^b`. -/
noncomputable def evalBasisHomog (sf0 sf1 : BiPoly (Polynomial F)) (s : ℕ)
    (e : ℕ × ℕ × ℕ × ℕ) : BiPoly (Polynomial F) :=
  let (q, j, a, b) := e
  (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) ^ q *
    sf0 ^ j * sf1 ^ (s - q - j) * (Polynomial.C (Polynomial.X ^ 2)) ^ a * (Polynomial.X ^ 2) ^ b

lemma biOrdGE_evalBasisHomog (sf0 sf1 : BiPoly (Polynomial F)) (k m s q j a b : ℕ)
    (hqs : q + j ≤ s) (hge : m ≤ q + a + b)
    (hW : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1))
    (h0 : BiOrdGE sf0 (2 * k - 1)) (h1 : BiOrdGE sf1 (2 * k - 1)) :
    BiOrdGE (evalBasisHomog sf0 sf1 s (q, j, a, b))
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  unfold evalBasisHomog
  have hp1 := biOrdGE_pow hW q
  have hp2 := biOrdGE_pow h0 j
  have hp3 := biOrdGE_pow h1 (s - q - j)
  have hp4 := biOrdGE_pow (biOrdGE_CX_sq (A := Polynomial F)) a
  have hp5 := biOrdGE_pow (biOrdGE_X_sq (A := Polynomial F)) b
  have hprod := biOrdGE_mul (biOrdGE_mul (biOrdGE_mul (biOrdGE_mul hp1 hp2) hp3) hp4) hp5
  apply biOrdGE_mono _ hprod
  split_ifs with hk0
  · subst hk0; simp only [Nat.mul_zero, Nat.zero_add, mul_one, Nat.zero_sub, mul_zero, add_zero]
    omega
  · have h2k : 2 * k + 1 = (2 * k - 1) + 2 := by omega
    have htot : q * (2 * k + 1) + j * (2 * k - 1) + (s - q - j) * (2 * k - 1) + a * 2 + b * 2 =
        2 * (q + a + b) + s * (2 * k - 1) := by
      have hs_eq : q + j + (s - q - j) = s := by omega
      rw [h2k]
      calc q * ((2 * k - 1) + 2) + j * (2 * k - 1) + (s - q - j) * (2 * k - 1) + a * 2 + b * 2
          = 2 * (q + a + b) + (q + j + (s - q - j)) * (2 * k - 1) := by ring
        _ = 2 * (q + a + b) + s * (2 * k - 1) := by rw [hs_eq]
    rw [htot]
    omega

private lemma ring_char2_sq_id {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (v s s0 s1 : R) :
    s ^ 2 * s0 ^ 2 = v ^ 2 * s1 ^ 2 + (v * s1 + s * s0) ^ 2 := by
  linear_combination -(v * s1 * s * s0 + v ^ 2 * s1 ^ 2) * h2

private lemma ring_evalBasisHomog_step {R : Type*} [CommRing R] (W s0 s1 x2 y2 : R)
    (q j2 a b t : ℕ) (hid : x2 * s0 ^ 2 = y2 * s1 ^ 2 + W ^ 2) :
    W ^ q * s0 ^ (j2 + 2) * s1 ^ t * x2 ^ (a + 1) * y2 ^ b =
      W ^ q * s0 ^ j2 * s1 ^ (t + 2) * x2 ^ a * y2 ^ (b + 1) +
      W ^ (q + 2) * s0 ^ j2 * s1 ^ t * x2 ^ a * y2 ^ b := by
  rw [pow_add s0 j2 2, pow_succ x2 a, pow_add s1 t 2, pow_succ y2 b, pow_add W q 2]
  linear_combination (W ^ q * s0 ^ j2 * s1 ^ t * x2 ^ a * y2 ^ b) * hid

/-- Exact char-2 reduction step for `evalBasisHomog`:
`evalBasisHomog (q, j, a + 1, b) = evalBasisHomog (q, j - 2, a, b + 1) + evalBasisHomog (q + 2, j - 2, a, b)`! -/
lemma evalBasisHomog_step (sf0 sf1 : BiPoly (Polynomial F)) (s q j a b : ℕ)
    (hqs : q + j ≤ s) (hj : 2 ≤ j) :
    evalBasisHomog sf0 sf1 s (q, j, a + 1, b) =
      evalBasisHomog sf0 sf1 s (q, j - 2, a, b + 1) +
      evalBasisHomog sf0 sf1 s (q + 2, j - 2, a, b) := by
  unfold evalBasisHomog
  dsimp only
  have h2B : (2 : BiPoly (Polynomial F)) = 0 := by
    have : (2 : Polynomial F) = 0 := by simp [CharTwo.two_eq_zero]
    rw [show (2 : BiPoly (Polynomial F)) = Polynomial.C (Polynomial.C (2 : Polynomial F)) by
      rw [show (2 : BiPoly (Polynomial F)) = 1 + 1 by norm_num,
        show (2 : Polynomial F) = 1 + 1 by norm_num, map_add, map_one, map_add, map_one],
      this, map_zero, map_zero]
  have hid : Polynomial.C (Polynomial.X ^ 2) * sf0 ^ 2 =
      Polynomial.X ^ 2 * sf1 ^ 2 + (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) ^ 2 := by
    rw [Polynomial.C_pow]
    exact ring_char2_sq_id h2B Polynomial.X (Polynomial.C Polynomial.X) sf0 sf1
  have hj_pow : sf0 ^ j = sf0 ^ (j - 2 + 2) := congrArg (sf0 ^ ·) (by omega)
  have hsf1_eq : s - q - (j - 2) = (s - q - j) + 2 := by omega
  have hsf1_eq2 : s - (q + 2) - (j - 2) = s - q - j := by omega
  rw [hj_pow, hsf1_eq, hsf1_eq2]
  exact ring_evalBasisHomog_step (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0)
    sf0 sf1 (Polynomial.C (Polynomial.X ^ 2)) (Polynomial.X ^ 2) q (j - 2) a b (s - q - j) hid

/-- Homogenized analog of `twOrdGE_sub_reduceMonomialCoords` in `BiPoly (Polynomial F)`! -/
lemma biOrdGE_evalBasisHomog_sub_reduce (sf0 sf1 : BiPoly (Polynomial F))
    (k m s q j a b : ℕ) (hqs : q + j ≤ s)
    (hW : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1))
    (h0 : BiOrdGE sf0 (2 * k - 1)) (h1 : BiOrdGE sf1 (2 * k - 1)) :
    BiOrdGE (evalBasisHomog sf0 sf1 s (q, j, a, b) -
      ∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j a b idx : ℕ) : Polynomial F)) *
          evalBasisHomog sf0 sf1 s idx.1)
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  induction a generalizing q j b with
  | zero =>
      by_cases hlt : q + 0 + b < m
      · have hmem : (q, j, 0, b) ∈ localBasisFinset m s :=
          (mem_localBasisFinset_iff m s q j 0 b).mpr ⟨hqs, hlt, Or.inr rfl⟩
        have hsum : (∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j 0 b idx : ℕ) : Polynomial F)) *
              evalBasisHomog sf0 sf1 s idx.1) = evalBasisHomog sf0 sf1 s (q, j, 0, b) := by
          rw [Finset.sum_eq_single ⟨(q, j, 0, b), hmem⟩]
          · simp [reduceMonomialCoords]
          · intro idx _ hne
            have hne' : idx.1 ≠ (q, j, 0, b) := fun h => hne (Subtype.ext h)
            simp [reduceMonomialCoords, hne']
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum, sub_self]; exact biOrdGE_of_zero _
      · have hsum : (∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j 0 b idx : ℕ) : Polynomial F)) *
              evalBasisHomog sf0 sf1 s idx.1) = 0 := by
          apply Finset.sum_eq_zero; intro idx _
          rcases idx with ⟨⟨q', j', a', b'⟩, hidx⟩
          have hne' : (q', j', a', b') ≠ (q, j, 0, b) := by
            intro h; simp only [Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl⟩
            have := ((mem_localBasisFinset_iff m s q' j' 0 b').mp hidx).2.1; omega
          simp [reduceMonomialCoords, hne']
        rw [hsum, sub_zero]
        exact biOrdGE_evalBasisHomog sf0 sf1 k m s q j 0 b hqs (by omega) hW h0 h1
  | succ a ih =>
      by_cases hge : m ≤ q + (a + 1) + b
      · have hsum : (∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j (a + 1) b idx : ℕ) : Polynomial F)) *
              evalBasisHomog sf0 sf1 s idx.1) = 0 := by
          apply Finset.sum_eq_zero; intro idx _
          simp [reduceMonomialCoords, hge]
        rw [hsum, sub_zero]
        exact biOrdGE_evalBasisHomog sf0 sf1 k m s q j (a + 1) b hqs hge hW h0 h1
      · by_cases hj2 : j < 2
        · have hmem : (q, j, a + 1, b) ∈ localBasisFinset m s :=
            (mem_localBasisFinset_iff m s q j (a + 1) b).mpr ⟨hqs, by omega, Or.inl hj2⟩
          have hsum : (∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j (a + 1) b idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1) = evalBasisHomog sf0 sf1 s (q, j, a + 1, b) := by
            rw [Finset.sum_eq_single ⟨(q, j, a + 1, b), hmem⟩]
            · simp [reduceMonomialCoords, hge, hj2]
            · intro idx _ hne
              have hne' : idx.1 ≠ (q, j, a + 1, b) := fun h => hne (Subtype.ext h)
              simp [reduceMonomialCoords, hge, hj2, hne']
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hsum, sub_self]; exact biOrdGE_of_zero _
        · have hstep := evalBasisHomog_step sf0 sf1 s q j a b hqs (by omega)
          have hsum_add : (∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q j (a + 1) b idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1) =
              (∑ idx : LocalBasisIdx m s,
                Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q (j - 2) a (b + 1) idx : ℕ) : Polynomial F)) *
                  evalBasisHomog sf0 sf1 s idx.1) +
              (∑ idx : LocalBasisIdx m s,
                Polynomial.C (Polynomial.C ((reduceMonomialCoords m s (q + 2) (j - 2) a b idx : ℕ) : Polynomial F)) *
                  evalBasisHomog sf0 sf1 s idx.1) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro idx _
            simp only [reduceMonomialCoords, hge, hj2, ↓reduceIte, Nat.cast_add, map_add, add_mul]
          rw [hstep, hsum_add, show ∀ x1 x2 y1 y2 : BiPoly (Polynomial F),
            (x1 + x2) - (y1 + y2) = (x1 - y1) + (x2 - y2) by intros; ring]
          exact biOrdGE_add (ih q (j - 2) (b + 1) (by omega)) (ih (q + 2) (j - 2) b (by omega))

/-- Unified homogenized binomial expansion of `kerDLocalPoly (C x0) y0 e1 * localBasisElem e2`
at `R = sf0 / sf1`, multiplied by `sf1^s`! -/
noncomputable def evalKerDProdHomog (sf0 sf1 : BiPoly (Polynomial F)) (s : ℕ)
    (x0 : F) (y0 : Polynomial F) (e1 e2 : ℕ × ℕ × ℕ × ℕ) : BiPoly (Polynomial F) :=
  let (k1, r1, b1, a1) := e1
  let (q2, j2, a2, b2) := e2
  ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
    Polynomial.C (Polynomial.C ((Nat.choose a1 a' : Polynomial F) * ((Polynomial.C x0) ^ 2) ^ (a1 - a') *
      ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')))) *
    (if r1 = 0 then
      evalBasisHomog sf0 sf1 s (q2, k1 + j2, a' + a2, b' + b2)
     else
      Polynomial.C (Polynomial.C y0) * evalBasisHomog sf0 sf1 s (q2, k1 + j2, a' + a2, b' + b2) +
      Polynomial.C (Polynomial.C (Polynomial.C x0)) * evalBasisHomog sf0 sf1 s (q2, k1 + 1 + j2, a' + a2, b' + b2) +
      evalBasisHomog sf0 sf1 s (q2 + 1, k1 + j2, a' + a2, b' + b2))

private lemma evalBasisHomog_field_id {K : Type*} [Field K]
    (x y f0 f1 : K) (hf1 : f1 ≠ 0) (s q j a b : ℕ) (hqs : q + j ≤ s) :
    (y * f1 + x * f0) ^ q * f0 ^ j * f1 ^ (s - q - j) * (x ^ 2) ^ a * (y ^ 2) ^ b =
      f1 ^ s * ((y + x * (f0 / f1)) ^ q * (f0 / f1) ^ j * (x ^ 2) ^ a * (y ^ 2) ^ b) := by
  have h1 : y * f1 + x * f0 = f1 * (y + x * (f0 / f1)) := by field_simp [hf1]
  have h2 : f1 ^ q * f1 ^ (s - q - j) * f1 ^ j = f1 ^ s := by
    rw [← pow_add, ← pow_add, show q + (s - q - j) + j = s by omega]
  rw [h1, mul_pow, div_pow, ← h2]
  field_simp [hf1]

private lemma resultant_term_field_id {K : Type*} [Field K]
    (c f0 f1 : K) (hf1 : f1 ≠ 0) (s j : ℕ) (hj : j ≤ s) :
    c * f0 ^ j * f1 ^ (s - j) = f1 ^ s * (c * (f0 ^ j / f1 ^ j)) := by
  have hpow : f1 ^ (s - j) * f1 ^ j = f1 ^ s := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [← hpow]
  field_simp [hf1]

/-- Polymorphic field helper for Step 3 of `ordGE_resultant_deg1_ge` (avoids `FractionRing` `whnf` timeouts). -/
private lemma lineShift_resultant_eq_SG_sub_SFV_field {K : Type*} [Field K] [CharP K 2]
    (ι : BiPoly (Polynomial F) →+* K) (hι_inj : Function.Injective ι)
    {wY W_F W m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hf1 : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let Gpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1
    let sf0 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 0) x0 y0
    let sf1 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 1) x0 y0
    let S_G : BiPoly (Polynomial F) := ∑ e : KerDIdx wY W s,
      Polynomial.C (Polynomial.C (g_coord e)) * evalKerDProdHomog sf0 sf1 s x0 y0 e.1 (0, 0, 0, 0)
    let S_FV : BiPoly (Polynomial F) := ∑ b : LocalBasisIdx (m - k) (s - 1),
      Polynomial.C (Polynomial.C (v_coord b)) *
        (∑ e1 : KerDIdx wY W_F 1,
          Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1)
    lineShift (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 = S_G - S_FV := by
  classical
  intro Fpoly Gpoly sf0 sf1 S_G S_FV
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsf1_ne : sf1 ≠ 0 := (lineShift_eq_zero_iff (Fpoly.coeff 1) x0 y0).not.mpr hf1
  have hιsf1_ne : ι sf1 ≠ 0 := fun h0 => hsf1_ne (hι_inj (by rw [map_zero]; exact h0))
  let rK : K := ι sf0 / ι sf1
  let evalLoc : LocalPoly (Polynomial F) →+* K :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (ι.comp (Polynomial.C.comp Polynomial.C)) rK)
        (ι Polynomial.X + ι (Polynomial.C Polynomial.X) * rK))
      (ι (Polynomial.C (Polynomial.X ^ 2)))
  have heL_C : ∀ c : Polynomial F, evalLoc (locC c) = ι (Polynomial.C (Polynomial.C c)) := fun c => by
    simp [evalLoc, locC]
  have heL_R : evalLoc locR = rK := by simp [evalLoc, locR]
  have heL_W : evalLoc locW = ι Polynomial.X + ι (Polynomial.C Polynomial.X) * rK := by simp [evalLoc, locW]
  have heL_T : evalLoc locT = ι (Polynomial.C (Polynomial.X ^ 2)) := by simp [evalLoc, locT]
  have heL_U : evalLoc localU = ι (Polynomial.X ^ 2) := by
    unfold localU
    rw [map_add, map_pow, map_mul, map_pow, heL_W, heL_T, heL_R]
    have hsq : (ι Polynomial.X + ι (Polynomial.C Polynomial.X) * rK) ^ 2 =
        ι (Polynomial.X ^ 2) + ι (Polynomial.C (Polynomial.X ^ 2)) * rK ^ 2 := by
      have : ι (Polynomial.C Polynomial.X) ^ 2 = ι (Polynomial.C (Polynomial.X ^ 2)) := by
        simp only [← map_pow]
      calc (ι Polynomial.X + ι (Polynomial.C Polynomial.X) * rK) ^ 2
          = ι Polynomial.X ^ 2 + 2 * (ι Polynomial.X * (ι (Polynomial.C Polynomial.X) * rK)) +
              ι (Polynomial.C Polynomial.X) ^ 2 * rK ^ 2 := by ring
        _ = ι (Polynomial.X ^ 2) + ι (Polynomial.C (Polynomial.X ^ 2)) * rK ^ 2 := by
              rw [h2K, this, ← map_pow]; ring
    rw [hsq]
    have hadd : ι (Polynomial.C (Polynomial.X ^ 2)) * rK ^ 2 +
        ι (Polynomial.C (Polynomial.X ^ 2)) * rK ^ 2 = 0 := by
      calc _ = (2 : K) * (ι (Polynomial.C (Polynomial.X ^ 2)) * rK ^ 2) := by ring
        _ = 0 := by rw [h2K, zero_mul]
    rw [add_assoc, hadd, add_zero]
  have heL_basis : ∀ e : ℕ × ℕ × ℕ × ℕ, e.1 + e.2.1 ≤ s →
      ι (evalBasisHomog sf0 sf1 s e) = (ι sf1) ^ s * evalLoc (localBasisElem e) := by
    rintro ⟨q, j, a, b⟩ hqs
    dsimp only at hqs
    unfold evalBasisHomog localBasisElem
    simp only [map_mul, map_pow, map_add, heL_W, heL_R, heL_T, heL_U]
    exact evalBasisHomog_field_id (ι (Polynomial.C Polynomial.X)) (ι Polynomial.X)
      (ι sf0) (ι sf1) hιsf1_ne s q j a b hqs
  have heL_kerDProd : ∀ (e1 e2 : ℕ × ℕ × ℕ × ℕ), e1.2.1 < 2 → e1.1 + e1.2.1 + e2.1 + e2.2.1 ≤ s →
      ι (evalKerDProdHomog sf0 sf1 s x0 y0 e1 e2) =
        (ι sf1) ^ s * evalLoc (kerDLocalPoly (C x0) y0 e1 * localBasisElem e2) := by
    rintro ⟨k1, r1, b1, a1⟩ ⟨q2, j2, a2, b2⟩ hr1 hqs
    dsimp only at hr1 hqs ⊢
    unfold evalKerDProdHomog kerDLocalPoly
    have hpow_a : (locC ((C x0) ^ 2) + locT) ^ a1 =
        ∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a')) * locT ^ a' := by
      rw [add_comm, add_pow (R := LocalPoly (Polynomial F))]
      apply Finset.sum_congr rfl; intro a' _
      have hc : locC ((C x0) ^ 2) ^ (a1 - a') * (Nat.choose a1 a' : LocalPoly (Polynomial F)) =
          locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a')) := by
        unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
      rw [mul_assoc, hc]; ring
    have hpow_b : (locC (y0 ^ 2) + localU) ^ b1 =
        ∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b' := by
      rw [add_comm, add_pow (R := LocalPoly (Polynomial F))]
      apply Finset.sum_congr rfl; intro b' _
      have hc : locC (y0 ^ 2) ^ (b1 - b') * (Nat.choose b1 b' : LocalPoly (Polynomial F)) =
          locC ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) := by
        unfold locC; simp only [map_mul, map_pow, map_natCast]; ring
      rw [mul_assoc, hc]; ring
    rw [hpow_a, hpow_b]
    rcases (show r1 = 0 ∨ r1 = 1 by omega) with rfl | rfl
    · simp only [↓reduceIte, pow_zero, mul_one]
      have hprod_eq : locR ^ k1 *
          (∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a')) * locT ^ a') *
          (∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b') *
          localBasisElem (q2, j2, a2, b2) =
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b'))) *
              localBasisElem (q2, k1 + j2, a' + a2, b' + b2) := by
        conv_lhs => arg 1; arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem locC; simp only [map_mul, pow_add]; ring
      rw [hprod_eq, map_sum, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a' _
      rw [map_sum, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b' _
      simp only [map_mul, heL_C]
      rw [heL_basis (q2, k1 + j2, a' + a2, b' + b2) (by dsimp; omega)]
      ring
    · simp only [one_ne_zero, ↓reduceIte, pow_one]
      have hprod_eq : locR ^ k1 * (locC y0 + locC (C x0) * locR + locW) *
          (∑ a' ∈ Finset.range (a1 + 1), locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a')) * locT ^ a') *
          (∑ b' ∈ Finset.range (b1 + 1), locC ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) * localU ^ b') *
          localBasisElem (q2, j2, a2, b2) =
          ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
            locC ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b'))) *
            (locC y0 * localBasisElem (q2, k1 + j2, a' + a2, b' + b2) +
             locC (C x0) * localBasisElem (q2, k1 + 1 + j2, a' + a2, b' + b2) +
             localBasisElem (q2 + 1, k1 + j2, a' + a2, b' + b2)) := by
        conv_lhs => arg 1; arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a' _
        conv_lhs => arg 1; rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b' _
        unfold localBasisElem locC; simp only [map_mul, pow_add, pow_succ]; ring
      rw [hprod_eq, map_sum, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a' _
      rw [map_sum, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b' _
      simp only [map_mul, map_add, heL_C]
      rw [heL_basis (q2, k1 + j2, a' + a2, b' + b2) (by dsimp; omega),
          heL_basis (q2, k1 + 1 + j2, a' + a2, b' + b2) (by dsimp; omega),
          heL_basis (q2 + 1, k1 + j2, a' + a2, b' + b2) (by dsimp; omega)]
      ring
  let χK : ContactPoly (Polynomial F) →+* K :=
    Polynomial.eval₂RingHom (ι.comp (lineShiftHom x0 y0)) rK
  have heL_eq_χK : ∀ e : ℕ × ℕ × ℕ × ℕ, evalLoc (kerDLocalPoly (C x0) y0 e) = χK (kerDBasisPoly e) := by
    intro ⟨k1, r1, b1, a1⟩
    unfold kerDLocalPoly kerDBasisPoly
    simp only [map_mul, map_pow, map_add, heL_R, heL_C, heL_W, heL_T, heL_U]
    have hχ_cR : χK cR = rK := by simp [χK, cR]
    have hχ_cX : χK cX = ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) := by
      simp [χK, cX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_CX]
    have hχ_cY : χK cY = ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) := by
      simp [χK, cY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_X]
    rw [hχ_cR, hχ_cX, hχ_cY]
    have hsqK : ∀ u v : K, (u + v) ^ 2 = u ^ 2 + v ^ 2 := ring_sq_add_char2 h2K
    have hX2 : ι (Polynomial.C (Polynomial.C (C x0))) ^ 2 + ι (Polynomial.C Polynomial.X) ^ 2 =
        ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) ^ 2 := by
      rw [Polynomial.C_add, map_add, hsqK, add_comm]
    have hY2 : ι (Polynomial.C (Polynomial.C y0)) ^ 2 + ι Polynomial.X ^ 2 =
        ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) ^ 2 := by
      rw [map_add, hsqK, add_comm]
    have hYXR : ι (Polynomial.C (Polynomial.C y0)) + ι (Polynomial.C (Polynomial.C (C x0))) * rK +
          (ι Polynomial.X + ι (Polynomial.C Polynomial.X) * rK) =
        ι (Polynomial.X + Polynomial.C (Polynomial.C y0)) +
          ι (Polynomial.C (Polynomial.X + Polynomial.C (Polynomial.C x0))) * rK := by
      rw [Polynomial.C_add, map_add, map_add]; ring
    rw [hX2, hY2, hYXR]
  have hFdeg_le : Fpoly.natDegree ≤ 1 := by
    dsimp [Fpoly]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
    dsimp only [Function.comp_apply]
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    refine Polynomial.natDegree_mul_le.trans ?_
    have h1 : (cC (f_coord e)).natDegree = 0 := by unfold cC; simp
    have h2 : (kerDBasisPoly (A := Polynomial F) e.1).natDegree ≤ e.1.1 + e.1.2.1 := by
      unfold kerDBasisPoly cR cY cX
      refine Polynomial.natDegree_mul_le.trans ?_
      have hb : ((Polynomial.C Polynomial.X ^ 2 : ContactPoly (Polynomial F)) ^ e.1.2.2.1).natDegree = 0 := by
        rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
      rw [hb, add_zero]
      refine Polynomial.natDegree_mul_le.trans ?_
      have ha : ((Polynomial.C (Polynomial.C Polynomial.X) ^ 2 : ContactPoly (Polynomial F)) ^ e.1.2.2.2).natDegree = 0 := by
        rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
      rw [ha, add_zero]
      have hmul := Polynomial.natDegree_mul_le (p := (Polynomial.X : ContactPoly (Polynomial F)) ^ e.1.1)
        (q := (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X) ^ e.1.2.1)
      have hx : ((Polynomial.X : ContactPoly (Polynomial F)) ^ e.1.1).natDegree ≤ e.1.1 :=
        Polynomial.natDegree_X_pow_le _
      have hlin : (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
          ContactPoly (Polynomial F)).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact Polynomial.natDegree_mul_le.trans (by simp)
      have hp : ((Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
          ContactPoly (Polynomial F)) ^ e.1.2.1).natDegree ≤ e.1.2.1 :=
        Polynomial.natDegree_pow_le.trans (by nlinarith)
      omega
    omega
  have hχK_F : χK Fpoly = 0 := by
    have hFexp : Fpoly = Polynomial.C (Fpoly.coeff 0) + Polynomial.C (Fpoly.coeff 1) * Polynomial.X := by
      ext m
      cases m with
      | zero => simp
      | succ m' =>
          cases m' with
          | zero => simp
          | succ m'' =>
              have hlt : Fpoly.natDegree < m''.succ.succ := lt_of_le_of_lt hFdeg_le (by omega)
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
              simp [Polynomial.coeff_mul_X]
    rw [hFexp]
    simp only [χK, map_add, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      RingHom.comp_apply, lineShiftHom_apply, rK]
    change ι sf0 + ι sf1 * (ι sf0 / ι sf1) = 0
    rw [mul_div_cancel₀ _ hιsf1_ne]
    calc ι sf0 + ι sf0 = (2 : K) * ι sf0 := by ring
      _ = 0 := by rw [h2K, zero_mul]
  have hι_SFV : ι S_FV = 0 := by
    dsimp only [S_FV]; rw [map_sum]
    apply Finset.sum_eq_zero; intro b _
    rw [map_mul, map_sum]
    have hinner : (∑ e1 : KerDIdx wY W_F 1,
        ι (Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1)) = 0 := by
      have h1 : ∀ e1 : KerDIdx wY W_F 1,
          ι (Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1) =
          (ι sf1) ^ s * evalLoc (localBasisElem b.1) *
            (χK (cC (f_coord e1) * kerDBasisPoly e1.1)) := by
        intro e1
        have hmem1 := (mem_kerDIdxFinset_iff wY W_F 1 hwY e1.1.1 e1.1.2.1 e1.1.2.2.1 e1.1.2.2.2).mp e1.2
        have hmem2 := ((mem_localBasisFinset_iff (m - k) (s - 1) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2).mp b.2).1
        rw [map_mul, heL_kerDProd e1.1 b.1 hmem1.1 (by omega), map_mul, heL_eq_χK, map_mul]
        have hχc : χK (cC (f_coord e1)) = ι (Polynomial.C (Polynomial.C (f_coord e1))) := by
          simp [χK, cC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_CC]
        rw [hχc]; ring
      simp_rw [h1, ← Finset.mul_sum, ← map_sum]
      change (ι sf1) ^ s * evalLoc (localBasisElem b.1) * χK Fpoly = 0
      rw [hχK_F, mul_zero]
    rw [hinner, mul_zero]
  have hι_SG : ι S_G = (ι sf1) ^ s * χK Gpoly := by
    dsimp only [S_G, Gpoly]; rw [map_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro e _
    have hmem := (mem_kerDIdxFinset_iff wY W s hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rw [map_mul, heL_kerDProd e.1 (0, 0, 0, 0) hmem.1 (by dsimp; omega),
      show localBasisElem (A := Polynomial F) (0, 0, 0, 0) = 1 by simp [localBasisElem],
      mul_one, heL_eq_χK, map_mul]
    have hχc : χK (cC (g_coord e)) = ι (Polynomial.C (Polynomial.C (g_coord e))) := by
      simp [χK, cC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, lineShiftHom_CC]
    rw [hχc]; ring
  have hGdeg_le : Gpoly.natDegree ≤ s := by
    dsimp [Gpoly]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
    dsimp only [Function.comp_apply]
    have hmem := (mem_kerDIdxFinset_iff wY W s hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    refine Polynomial.natDegree_mul_le.trans ?_
    have h1 : (cC (g_coord e)).natDegree = 0 := by unfold cC; simp
    have h2 : (kerDBasisPoly (A := Polynomial F) e.1).natDegree ≤ e.1.1 + e.1.2.1 := by
      unfold kerDBasisPoly cR cY cX
      refine Polynomial.natDegree_mul_le.trans ?_
      have hb : ((Polynomial.C Polynomial.X ^ 2 : ContactPoly (Polynomial F)) ^ e.1.2.2.1).natDegree = 0 := by
        rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
      rw [hb, add_zero]
      refine Polynomial.natDegree_mul_le.trans ?_
      have ha : ((Polynomial.C (Polynomial.C Polynomial.X) ^ 2 : ContactPoly (Polynomial F)) ^ e.1.2.2.2).natDegree = 0 := by
        rw [← map_pow, ← map_pow, Polynomial.natDegree_C]
      rw [ha, add_zero]
      have hmul := Polynomial.natDegree_mul_le (p := (Polynomial.X : ContactPoly (Polynomial F)) ^ e.1.1)
        (q := (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X) ^ e.1.2.1)
      have hx : ((Polynomial.X : ContactPoly (Polynomial F)) ^ e.1.1).natDegree ≤ e.1.1 :=
        Polynomial.natDegree_X_pow_le _
      have hlin : (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
          ContactPoly (Polynomial F)).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact Polynomial.natDegree_mul_le.trans (by simp)
      have hp : ((Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C Polynomial.X) * Polynomial.X :
          ContactPoly (Polynomial F)) ^ e.1.2.1).natDegree ≤ e.1.2.1 :=
        Polynomial.natDegree_pow_le.trans (by nlinarith)
      omega
    omega
  have hι_res : ι (lineShift (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0) = (ι sf1) ^ s * χK Gpoly := by
    rw [resultant_deg1_char2 Fpoly Gpoly s, ← lineShiftHom_apply, map_sum, map_sum]
    have hχG : χK Gpoly = ∑ j ∈ Finset.range (s + 1), ι (lineShift (Gpoly.coeff j) x0 y0) * rK ^ j := by
      unfold χK
      change Polynomial.eval₂ _ rK Gpoly = _
      rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hGdeg_le)]
      apply Finset.sum_congr rfl; intro j _; rfl
    rw [hχG, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    have hjle : j ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [map_mul, map_pow, lineShiftHom_apply, rK, div_pow]
    change ι (lineShift (Gpoly.coeff j) x0 y0) * ι sf0 ^ j * ι sf1 ^ (s - j) =
      ι sf1 ^ s * (ι (lineShift (Gpoly.coeff j) x0 y0) * (ι sf0 ^ j / ι sf1 ^ j))
    exact resultant_term_field_id (ι (lineShift (Gpoly.coeff j) x0 y0)) (ι sf0) (ι sf1) hιsf1_ne s j hjle
  exact hι_inj (by rw [map_sub, hι_SG, hι_SFV, sub_zero, hι_res])

private lemma sub3_ring {R : Type*} [CommRing R] (c a1 a2 x1 x2 x3 y1 y2 y3 : R) :
    c * (a1 * x1 + a2 * x2 + x3) - (c * a1 * y1 + c * a2 * y2 + c * y3) =
    c * (a1 * (x1 - y1) + a2 * (x2 - y2) + (x3 - y3)) := by ring

private lemma mul3_ring {R : Type*} [CommRing R] (c a1 a2 r1 r2 r3 e : R) :
    c * (a1 * r1 + a2 * r2 + r3) * e =
    c * a1 * (r1 * e) + c * a2 * (r2 * e) + c * (r3 * e) := by ring

private lemma sub_sub_ring {R : Type*} [CommRing R] (a b c d : R) :
    (a - b) - ((a - c) - (b - d)) = c - d := by ring

private lemma sum_sub_ring {ι R : Type*} [CommRing R] (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, (f i - g i)) = (∑ i ∈ s, f i) - (∑ i ∈ s, g i) :=
  Finset.sum_sub_distrib f g

private lemma mul_sub_ring {R : Type*} [CommRing R] (a b c : R) :
    a * (b - c) = a * b - a * c := mul_sub a b c

private lemma sub_mul_ring {R : Type*} [CommRing R] (a b c : R) :
    (a - b) * c = a * c - b * c := sub_mul a b c

private lemma sub_sub_cancel_ring {R : Type*} [CommRing R] (a b c : R) :
    (a - c) - (b - c) = a - b := sub_sub_sub_cancel_right a b c

private noncomputable def prodNFEntry (m s : ℕ) (x0 : F) (y0 : Polynomial F)
    (e1 e2 : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) : Polynomial F :=
  let (k1, r1, b1, a1) := e1
  let (q2, j2, a2, b2) := e2
  ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
    (Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
    ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) *
    (if r1 = 0 then
      ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)
     else
      y0 * ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F) +
      C x0 * ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F) +
      ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F))

private lemma prodLocalNF_eq_sum_prodNFEntry {wY W_F m s : ℕ} (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F) (e2 : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) :
    prodLocalNF (C x0) y0 f_coord e2 idx =
      ∑ e1 : KerDIdx wY W_F 1, f_coord e1 * prodNFEntry m s x0 y0 e1.1 e2 idx := by
  rcases e2 with ⟨q2, j2, a2, b2⟩
  unfold prodLocalNF
  apply Finset.sum_congr rfl; intro e1 _
  rcases e1 with ⟨⟨k1, r1, b1, a1⟩, _⟩
  rfl

private lemma deg1_nf_eq {wY W_F W m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hvan : twOrdGE
      ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C x0) y0 e.1) -
       (∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) *
       (∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) * localBasisElem b.1)) m) :
    ∀ idx : LocalBasisIdx m s,
      (∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) =
      (∑ b : LocalBasisIdx (m - k) (s - 1), v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) := by
  classical
  have hdiff_zero : ∀ idx : LocalBasisIdx m s,
      (∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) -
      (∑ b : LocalBasisIdx (m - k) (s - 1), v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) = 0 := by
    apply localBasis_linearIndependent_mod m s
    have hG_nf : twOrdGE ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C x0) y0 e.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
          g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) * localBasisElem idx.1) m := by
      have hrew : (∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C x0) y0 e.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
            g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) * localBasisElem idx.1 =
          ∑ e : KerDIdx wY W s, locC (g_coord e) *
            (kerDLocalPoly (C x0) y0 e.1 -
              ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s (C x0) y0 e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← sum_sub_ring (R := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro e _
        rw [mul_sub_ring (R := LocalPoly (Polynomial F))]; congr 1
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W s hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF m s (C x0) y0 e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have hFV_nf : twOrdGE ((∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) *
        (∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) * localBasisElem b.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - 1),
          v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1) m := by
      have hrew : (∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) *
          (∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) * localBasisElem b.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - 1),
            v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1 =
          ∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) *
            ((∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) * localBasisElem b.1 -
              ∑ idx : LocalBasisIdx m s, locC (prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1) := by
        rw [Finset.mul_sum]
        have h2b : (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - 1),
              v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1) =
            ∑ b : LocalBasisIdx (m - k) (s - 1), ∑ idx : LocalBasisIdx m s,
              locC (v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1 := by
          trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k) (s - 1),
              locC (v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1
          · apply Finset.sum_congr rfl; intro idx _; unfold locC; simp only [map_sum, Finset.sum_mul]
          · exact Finset.sum_comm
        rw [h2b, ← sum_sub_ring (R := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro b _
        rw [mul_sub_ring (R := LocalPoly (Polynomial F))]
        refine congrArg₂ (· - ·) (by rw [← mul_assoc, mul_comm _ (locC (v_coord b)), mul_assoc]) ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        unfold locC; simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro b _
      have hb := ((mem_localBasisFinset_iff (m - k) (s - 1) _ _ _ _).mp b.2).1
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_prodLocal_sub_NF hwY hs (C x0) y0 f_coord b.1 hb)
    have hcomb := twOrdGE_sub hvan (twOrdGE_sub hG_nf hFV_nf)
    rw [sub_sub_ring (R := LocalPoly (Polynomial F))] at hcomb
    have hsub_sum : (∑ idx : LocalBasisIdx m s,
        locC ((∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) -
          (∑ b : LocalBasisIdx (m - k) (s - 1), v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) *
          localBasisElem idx.1) =
        (∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
          g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx) * localBasisElem idx.1) -
        (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k) (s - 1),
          v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx) * localBasisElem idx.1) := by
      rw [← sum_sub_ring (R := LocalPoly (Polynomial F))]
      apply Finset.sum_congr rfl; intro idx _
      unfold locC; simp only [map_sub]; exact sub_mul_ring (R := LocalPoly (Polynomial F)) _ _ _
    rw [hsub_sum]; exact hcomb
  intro idx; exact sub_eq_zero.mp (hdiff_zero idx)

private lemma biOrdGE_evalKerDProdHomog_sub_nf
    (sf0 sf1 : BiPoly (Polynomial F)) (m s : ℕ) {k : ℕ} (x0 : F) (y0 : Polynomial F)
    (hW_ord : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1))
    (hsf0_ord : BiOrdGE sf0 (2 * k - 1))
    (hsf1_ord : BiOrdGE sf1 (2 * k - 1))
    (e1 e2 : ℕ × ℕ × ℕ × ℕ) (hr1 : e1.2.1 < 2) (hqs : e1.1 + e1.2.1 + e2.1 + e2.2.1 ≤ s) :
    BiOrdGE (evalKerDProdHomog sf0 sf1 s x0 y0 e1 e2 -
      ∑ idx : LocalBasisIdx m s, Polynomial.C (Polynomial.C (prodNFEntry m s x0 y0 e1 e2 idx)) *
        evalBasisHomog sf0 sf1 s idx.1)
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  classical
  rcases e1 with ⟨k1, r1, b1, a1⟩
  rcases e2 with ⟨q2, j2, a2, b2⟩
  dsimp only at hr1 hqs ⊢
  have hcomm : ∀ (f : ℕ → ℕ → LocalBasisIdx m s → BiPoly (Polynomial F)),
      (∑ idx : LocalBasisIdx m s, ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1), f a' b' idx) =
      ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1), ∑ idx : LocalBasisIdx m s, f a' b' idx := by
    intro f; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a' _; rw [Finset.sum_comm]
  have hrew : evalKerDProdHomog sf0 sf1 s x0 y0 (k1, r1, b1, a1) (q2, j2, a2, b2) -
      ∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C (prodNFEntry m s x0 y0 (k1, r1, b1, a1) (q2, j2, a2, b2) idx)) *
        evalBasisHomog sf0 sf1 s idx.1 =
      ∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
        Polynomial.C (Polynomial.C ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
          ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')))) *
        (if r1 = 0 then
          (evalBasisHomog sf0 sf1 s (q2, k1 + j2, a' + a2, b' + b2) -
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1)
         else
          Polynomial.C (Polynomial.C y0) * (evalBasisHomog sf0 sf1 s (q2, k1 + j2, a' + a2, b' + b2) -
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1) +
          Polynomial.C (Polynomial.C (C x0)) * (evalBasisHomog sf0 sf1 s (q2, k1 + 1 + j2, a' + a2, b' + b2) -
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1) +
          (evalBasisHomog sf0 sf1 s (q2 + 1, k1 + j2, a' + a2, b' + b2) -
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
                evalBasisHomog sf0 sf1 s idx.1)) := by
    unfold evalKerDProdHomog prodNFEntry
    simp_rw [map_sum, Finset.sum_mul]
    rw [hcomm, ← sum_sub_ring (R := BiPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro a' _
    rw [← sum_sub_ring (R := BiPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro b' _
    rcases (show r1 = 0 ∨ r1 = 1 by omega) with rfl | rfl
    · simp only [↓reduceIte]
      have hsum0 : (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (
            (Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) *
            ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F))) *
          evalBasisHomog sf0 sf1 s idx.1) =
          Polynomial.C (Polynomial.C ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
            ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')))) *
          ∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
              evalBasisHomog sf0 sf1 s idx.1 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro idx _
        simp only [map_mul, mul_assoc]
      rw [hsum0]; exact (mul_sub_ring (R := BiPoly (Polynomial F)) _ _ _).symm
    · simp only [one_ne_zero, ↓reduceIte]
      have h3 : ∀ (f1 f2 f3 : LocalBasisIdx m s → BiPoly (Polynomial F)),
          (∑ idx, f1 idx) + (∑ idx, f2 idx) + (∑ idx, f3 idx) = ∑ idx, (f1 idx + f2 idx + f3 idx) := by
        intro f1 f2 f3; rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      set cc : BiPoly (Polynomial F) :=
        Polynomial.C (Polynomial.C ((Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
          ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b'))))
      set s1 : BiPoly (Polynomial F) := ∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
          evalBasisHomog sf0 sf1 s idx.1
      set s2 : BiPoly (Polynomial F) := ∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
          evalBasisHomog sf0 sf1 s idx.1
      set s3 : BiPoly (Polynomial F) := ∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)) *
          evalBasisHomog sf0 sf1 s idx.1
      have hsum_eq :
          (∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C (
              (Nat.choose a1 a' : Polynomial F) * ((C x0) ^ 2) ^ (a1 - a') *
              ((Nat.choose b1 b' : Polynomial F) * (y0 ^ 2) ^ (b1 - b')) *
              (y0 * ((reduceMonomialCoords m s q2 (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F) +
               C x0 * ((reduceMonomialCoords m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F) +
               ((reduceMonomialCoords m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2) idx : ℕ) : Polynomial F)))) *
              evalBasisHomog sf0 sf1 s idx.1) =
          cc * Polynomial.C (Polynomial.C y0) * s1 +
            cc * Polynomial.C (Polynomial.C (C x0)) * s2 + cc * s3 := by
        dsimp only [cc, s1, s2, s3]
        simp_rw [Finset.mul_sum]; rw [h3]
        apply Finset.sum_congr rfl; intro idx _
        simp only [map_mul, map_add]
        exact mul3_ring (R := BiPoly (Polynomial F)) _ _ _ _ _ _ _
      rw [hsum_eq]
      exact sub3_ring cc (Polynomial.C (Polynomial.C y0)) (Polynomial.C (Polynomial.C (C x0))) _ _ _ s1 s2 s3
  rw [hrew]
  apply biOrdGE_sum; intro a' _; apply biOrdGE_sum; intro b' _; apply biOrdGE_CC_mul
  rcases (show r1 = 0 ∨ r1 = 1 by omega) with rfl | rfl
  · simp only [↓reduceIte]
    exact biOrdGE_evalBasisHomog_sub_reduce sf0 sf1 k m s q2 (k1 + j2) (a' + a2) (b' + b2)
      (by omega) hW_ord hsf0_ord hsf1_ord
  · simp only [one_ne_zero, ↓reduceIte]
    apply biOrdGE_add
    · apply biOrdGE_add
      · exact biOrdGE_CC_mul _ (biOrdGE_evalBasisHomog_sub_reduce sf0 sf1 k m s q2 (k1 + j2) (a' + a2) (b' + b2)
          (by omega) hW_ord hsf0_ord hsf1_ord)
      · exact biOrdGE_CC_mul _ (biOrdGE_evalBasisHomog_sub_reduce sf0 sf1 k m s q2 (k1 + 1 + j2) (a' + a2) (b' + b2)
          (by omega) hW_ord hsf0_ord hsf1_ord)
    · exact biOrdGE_evalBasisHomog_sub_reduce sf0 sf1 k m s (q2 + 1) (k1 + j2) (a' + a2) (b' + b2)
        (by omega) hW_ord hsf0_ord hsf1_ord

private lemma lineShift_resultant_eq_SG_sub_SFV {wY W_F W m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hf1 : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let Gpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1
    let sf0 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 0) x0 y0
    let sf1 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 1) x0 y0
    lineShift (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 =
      (∑ e : KerDIdx wY W s,
        Polynomial.C (Polynomial.C (g_coord e)) * evalKerDProdHomog sf0 sf1 s x0 y0 e.1 (0, 0, 0, 0)) -
      (∑ b : LocalBasisIdx (m - k) (s - 1),
        Polynomial.C (Polynomial.C (v_coord b)) *
          (∑ e1 : KerDIdx wY W_F 1,
            Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1)) := by
  let K := FractionRing (BiPoly (Polynomial F))
  let ι : BiPoly (Polynomial F) →+* K := algebraMap (BiPoly (Polynomial F)) K
  have hι_inj : Function.Injective ι := IsFractionRing.injective (BiPoly (Polynomial F)) K
  have : CharP K 2 := charP_of_injective_ringHom hι_inj 2
  exact lineShift_resultant_eq_SG_sub_SFV_field ι hι_inj hwY hs x0 y0 f_coord g_coord v_coord hf1

private lemma deg1_SG_ord {wY W m s k : ℕ} (hwY : 0 < wY)
    (sf0 sf1 : BiPoly (Polynomial F)) (x0 : F) (y0 : Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (hW_ord : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1))
    (hsf0_ord : BiOrdGE sf0 (2 * k - 1))
    (hsf1_ord : BiOrdGE sf1 (2 * k - 1)) :
    BiOrdGE
      ((∑ e : KerDIdx wY W s,
          Polynomial.C (Polynomial.C (g_coord e)) * evalKerDProdHomog sf0 sf1 s x0 y0 e.1 (0, 0, 0, 0)) -
       (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1))
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  classical
  have hrew :
      (∑ e : KerDIdx wY W s,
          Polynomial.C (Polynomial.C (g_coord e)) * evalKerDProdHomog sf0 sf1 s x0 y0 e.1 (0, 0, 0, 0)) -
      (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) =
      ∑ e : KerDIdx wY W s, Polynomial.C (Polynomial.C (g_coord e)) *
        (evalKerDProdHomog sf0 sf1 s x0 y0 e.1 (0, 0, 0, 0) -
          ∑ idx : LocalBasisIdx m s, Polynomial.C (Polynomial.C (kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) := by
    simp_rw [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm, ← sum_sub_ring (R := BiPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro e _
    have hsum_e : (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) =
        Polynomial.C (Polynomial.C (g_coord e)) *
          ∑ idx : LocalBasisIdx m s, Polynomial.C (Polynomial.C (kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro idx _
      simp only [map_mul, mul_assoc]
    rw [hsum_e]
    exact (mul_sub_ring (R := BiPoly (Polynomial F)) _ _ _).symm
  rw [hrew]; apply biOrdGE_sum; intro e _; apply biOrdGE_CC_mul
  have hmem := (mem_kerDIdxFinset_iff wY W s hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  have h := biOrdGE_evalKerDProdHomog_sub_nf sf0 sf1 m s x0 y0 hW_ord hsf0_ord hsf1_ord
    e.1 (0, 0, 0, 0) hmem.1 (by dsimp; omega)
  have hnf0 : ∀ idx : LocalBasisIdx m s,
      prodNFEntry m s x0 y0 e.1 (0, 0, 0, 0) idx = kerDLocalNF m s (C x0) y0 e.1 idx := by
    intro idx; rcases e.1 with ⟨k1, r1, b1, a1⟩
    simp only [prodNFEntry, kerDLocalNF, add_zero, zero_add]
  simp_rw [hnf0] at h
  exact h

private lemma deg1_SFV_ord {wY W_F m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (sf0 sf1 : BiPoly (Polynomial F)) (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hW_ord : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1))
    (hsf0_ord : BiOrdGE sf0 (2 * k - 1))
    (hsf1_ord : BiOrdGE sf1 (2 * k - 1)) :
    BiOrdGE
      ((∑ b : LocalBasisIdx (m - k) (s - 1),
          Polynomial.C (Polynomial.C (v_coord b)) *
            (∑ e1 : KerDIdx wY W_F 1,
              Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1)) -
       (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ b : LocalBasisIdx (m - k) (s - 1),
            v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1))
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  classical
  have hrew :
      (∑ b : LocalBasisIdx (m - k) (s - 1),
          Polynomial.C (Polynomial.C (v_coord b)) *
            (∑ e1 : KerDIdx wY W_F 1,
              Polynomial.C (Polynomial.C (f_coord e1)) * evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1)) -
      (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ b : LocalBasisIdx (m - k) (s - 1),
            v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) =
      ∑ b : LocalBasisIdx (m - k) (s - 1), Polynomial.C (Polynomial.C (v_coord b)) *
        (∑ e1 : KerDIdx wY W_F 1, Polynomial.C (Polynomial.C (f_coord e1)) *
          (evalKerDProdHomog sf0 sf1 s x0 y0 e1.1 b.1 -
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C (prodNFEntry m s x0 y0 e1.1 b.1 idx)) *
              evalBasisHomog sf0 sf1 s idx.1)) := by
    have hNF_pull : (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ b : LocalBasisIdx (m - k) (s - 1),
            v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) * evalBasisHomog sf0 sf1 s idx.1) =
        ∑ b : LocalBasisIdx (m - k) (s - 1),
          ∑ idx : LocalBasisIdx m s,
            Polynomial.C (Polynomial.C (v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) * evalBasisHomog sf0 sf1 s idx.1 := by
      trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k) (s - 1),
          Polynomial.C (Polynomial.C (v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) * evalBasisHomog sf0 sf1 s idx.1
      · apply Finset.sum_congr rfl; intro idx _
        simp only [map_sum, Finset.sum_mul]
      · exact Finset.sum_comm
    rw [hNF_pull, ← sum_sub_ring (R := BiPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro b _
    simp_rw [prodLocalNF_eq_sum_prodNFEntry]
    rw [Finset.mul_sum, Finset.mul_sum]
    have hmap_v : (∑ idx : LocalBasisIdx m s,
        Polynomial.C (Polynomial.C (v_coord b *
          ∑ e1 : KerDIdx wY W_F 1, f_coord e1 * prodNFEntry m s x0 y0 e1.1 b.1 idx)) *
        evalBasisHomog sf0 sf1 s idx.1) =
        ∑ e1 : KerDIdx wY W_F 1, Polynomial.C (Polynomial.C (v_coord b)) *
          (Polynomial.C (Polynomial.C (f_coord e1)) *
            ∑ idx : LocalBasisIdx m s,
              Polynomial.C (Polynomial.C (prodNFEntry m s x0 y0 e1.1 b.1 idx)) *
                evalBasisHomog sf0 sf1 s idx.1) := by
      trans ∑ idx : LocalBasisIdx m s, ∑ e1 : KerDIdx wY W_F 1,
          Polynomial.C (Polynomial.C (v_coord b)) *
            (Polynomial.C (Polynomial.C (f_coord e1)) *
              (Polynomial.C (Polynomial.C (prodNFEntry m s x0 y0 e1.1 b.1 idx)) *
                evalBasisHomog sf0 sf1 s idx.1))
      · apply Finset.sum_congr rfl; intro idx _
        simp only [map_mul, map_sum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro e1 _
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hmap_v, ← sum_sub_ring (R := BiPoly (Polynomial F))]
    apply Finset.sum_congr rfl; intro e1 _
    rw [← mul_sub_ring (R := BiPoly (Polynomial F)), ← mul_sub_ring (R := BiPoly (Polynomial F))]
  rw [hrew]; apply biOrdGE_sum; intro b _; apply biOrdGE_CC_mul
  apply biOrdGE_sum; intro e1 _; apply biOrdGE_CC_mul
  have hmem1 := (mem_kerDIdxFinset_iff wY W_F 1 hwY e1.1.1 e1.1.2.1 e1.1.2.2.1 e1.1.2.2.2).mp e1.2
  have hmem2 := ((mem_localBasisFinset_iff (m - k) (s - 1) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2).mp b.2).1
  exact biOrdGE_evalKerDProdHomog_sub_nf sf0 sf1 m s x0 y0 hW_ord hsf0_ord hsf1_ord
    e1.1 b.1 hmem1.1 (by omega)

private lemma biOrdGE_sub_cancel {A : Type*} [CommRing A] {S1 S2 C : BiPoly A} {r : ℕ}
    (h1 : BiOrdGE (S1 - C) r) (h2 : BiOrdGE (S2 - C) r) : BiOrdGE (S1 - S2) r := by
  intro a b hab
  have h1' := h1 a b hab
  have h2' := h2 a b hab
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, sub_eq_zero] at h1' h2'
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, h1', h2', sub_self]

set_option maxHeartbeats 2400000 in
/-- **Theorem 5a (Unified `d = 1` resultant line-order lower bound for ALL `k ≥ 0`):**
Given `F ∈ K_{W_F}(1)[Z]` with `F.coeff 1 ≠ 0` and `twOrdGE Floc k`, and `G ∈ K_W(s)[Z]`
with local quotient witness `v` satisfying `twOrdGE (Gloc - Floc * Vloc) m`,
the resultant `Φ := Polynomial.resultant F G 1 s` satisfies:
`OrdGE Φ x0 y0 (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1))`,
and hence (whenever `Φ ≠ 0`):
`(2 * m : ℤ) + (s : ℤ) * (2 * (k : ℤ) - 1) ≤ (lineOrd Φ x0 y0 : ℤ)`! -/
theorem ordGE_resultant_deg1_ge {wY W_F W m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hf1 : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hk : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k)
    (hvan : twOrdGE
      ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C x0) y0 e.1) -
       (∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) *
       (∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) * localBasisElem b.1)) m) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let Gpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1
    OrdGE (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0
      (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) := by
  classical
  intro Fpoly Gpoly
  let sf0 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 0) x0 y0
  let sf1 : BiPoly (Polynomial F) := lineShift (Fpoly.coeff 1) x0 y0
  have hW_ord : BiOrdGE (Polynomial.X * sf1 + Polynomial.C Polynomial.X * sf0) (2 * k + 1) :=
    biOrdGE_v_sf1_add_s_sf0 hwY x0 y0 f_coord hk
  have h01_ord := biOrdGE_sf0_sf1_of_twOrdGE hwY x0 y0 f_coord hk
  have hNF_eq := deg1_nf_eq (m := m) (k := k) hwY hs x0 y0 f_coord g_coord v_coord hvan
  have hSG_ord := deg1_SG_ord (m := m) (k := k) hwY sf0 sf1 x0 y0 g_coord hW_ord h01_ord.1 h01_ord.2
  have hSFV_ord := deg1_SFV_ord (m := m) (k := k) hwY hs sf0 sf1 x0 y0 f_coord v_coord hW_ord h01_ord.1 h01_ord.2
  have hSNF_eq :
      (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ e : KerDIdx wY W s, g_coord e * kerDLocalNF m s (C x0) y0 e.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) =
      (∑ idx : LocalBasisIdx m s,
          Polynomial.C (Polynomial.C (∑ b : LocalBasisIdx (m - k) (s - 1),
            v_coord b * prodLocalNF (C x0) y0 f_coord b.1 idx)) *
            evalBasisHomog sf0 sf1 s idx.1) := by
    apply Finset.sum_congr rfl; intro idx _; rw [hNF_eq idx]
  rw [← hSNF_eq] at hSFV_ord
  have hSdiff_ord := biOrdGE_sub_cancel hSG_ord hSFV_ord
  have hsΦ_eq := lineShift_resultant_eq_SG_sub_SFV (m := m) (k := k) hwY hs x0 y0 f_coord g_coord v_coord hf1
  intro a b hab
  rw [hsΦ_eq]
  exact hSdiff_ord a b hab

/-- **Theorem 5b (`ℤ` form for ALL `k ≥ 0`, including `k = 0`!):** -/
theorem lineOrd_resultant_deg1_ge {wY W_F W m s k : ℕ} (hwY : 0 < wY) (hs : 1 ≤ s)
    (x0 : F) (y0 : Polynomial F)
    (f_coord : KerDIdx wY W_F 1 → Polynomial F)
    (g_coord : KerDIdx wY W s → Polynomial F)
    (v_coord : LocalBasisIdx (m - k) (s - 1) → Polynomial F)
    (hf1 : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hk : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (C x0) y0 e.1) k)
    (hvan : twOrdGE
      ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C x0) y0 e.1) -
       (∑ e1 : KerDIdx wY W_F 1, locC (f_coord e1) * kerDLocalPoly (C x0) y0 e1.1) *
       (∑ b : LocalBasisIdx (m - k) (s - 1), locC (v_coord b) * localBasisElem b.1)) m)
    (hΦ : Polynomial.resultant
      (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1)
      (∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1) 1 s ≠ 0) :
    let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    let Gpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1
    (2 * (m : ℤ)) + (s : ℤ) * (2 * (k : ℤ) - 1) ≤
      (lineOrd (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 : ℤ) := by
  intro Fpoly Gpoly
  have hord := ordGE_resultant_deg1_ge hwY hs x0 y0 f_coord g_coord v_coord hf1 hk hvan
  have hle : (if k = 0 then 2 * m - s else 2 * m + s * (2 * k - 1)) ≤
      lineOrd (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 :=
    (ordGE_iff hΦ x0 y0 _).mp hord
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte] at hle
    have hleZ : ((2 * m - s : ℕ) : ℤ) ≤ (lineOrd (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 : ℤ) := by
      exact_mod_cast hle
    omega
  · simp only [hk0, ↓reduceIte] at hle
    have hleZ : ((2 * m + s * (2 * k - 1) : ℕ) : ℤ) ≤
        (lineOrd (Polynomial.resultant Fpoly Gpoly 1 s) x0 y0 : ℤ) := by
      exact_mod_cast hle
    have h2k : 1 ≤ 2 * k := by omega
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2k] at hleZ
    push_cast at hleZ
    linarith

end Deg1LineOrd

/-! ### Part 6: Free `ScalarListBound` (`deg_Z = 0`) & Concrete `hΦgap_of_g_hi` for 64.01! -/

/-- **Theorem 6a:** If `Φ : BiPoly (Polynomial F)` is nonzero, `Φ.natDegree ≤ B`, and
`Φ` has `deg_Z = 0` (`∀ j a, ((Φ.coeff j).coeff a).natDegree = 0`), then at most `B` distinct
polynomials `P : Polynomial F` satisfy `triEval Φ 0 P = 0`! -/
theorem card_roots_le_of_degZ_zero {F : Type*} [Field F]
    (Φ : BiPoly (Polynomial F)) (B : ℕ)
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B)
    (hZ0 : ∀ j a, ((Φ.coeff j).coeff a).natDegree = 0)
    (T : Finset (Polynomial F))
    (hvan : ∀ P ∈ T, triEval Φ 0 P = 0) :
    T.card ≤ B := by
  classical
  let Φ0 : Polynomial (Polynomial F) := specializeZ Φ 0
  have hΦ0_ne : Φ0 ≠ 0 := by
    intro h0; apply hΦ
    refine Polynomial.ext fun j => Polynomial.ext fun a => ?_
    have hj : (Φ0.coeff j).coeff a = 0 := by rw [h0]; simp
    have heval0 : ((Φ.coeff j).coeff a).eval 0 = 0 := by
      simpa [Φ0, specializeZ] using hj
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (hZ0 j a)
    have hcoeff0 : ((Φ.coeff j).coeff a).coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using heval0
    rw [hC, hcoeff0, map_zero, Polynomial.coeff_zero, Polynomial.coeff_zero]
  have hΦ0_deg : Φ0.natDegree ≤ B := Polynomial.natDegree_map_le.trans hB
  let ψ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  have hψ_inj : Function.Injective ψ := IsFractionRing.injective (Polynomial F) (RatFunc F)
  let ΦK : Polynomial (RatFunc F) := Φ0.map ψ
  have hΦK_ne : ΦK ≠ 0 := (Polynomial.map_ne_zero_iff hψ_inj).mpr hΦ0_ne
  have hΦK_deg : ΦK.natDegree ≤ B := Polynomial.natDegree_map_le.trans hΦ0_deg
  have hsub : T.image ψ ⊆ ΦK.roots.toFinset := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨P, hP, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦK_ne, Polynomial.IsRoot.def,
      Polynomial.eval_map_apply, show Φ0.eval P = triEval Φ 0 P from rfl, hvan P hP, map_zero]
  calc T.card = (T.image ψ).card := (Finset.card_image_of_injective T hψ_inj).symm
    _ ≤ ΦK.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ ΦK.roots.card := Multiset.toFinset_card_le ΦK.roots
    _ ≤ ΦK.natDegree := Polynomial.card_roots' ΦK
    _ ≤ B := hΦK_deg

/-- **Theorem 6b:** Combined scalar root-count corollary from `Fpoly, Gpoly : ContactPoly (Polynomial F)`
with `deg_Z = 0` (`D_ZF = D_Z' = 0`): at most `W_Phi / wY` distinct `P : Polynomial F` satisfy
`evalContact (evalZContact Fpoly 0) P = 0 ∧ evalContact (evalZContact Gpoly 0) P = 0`! -/
theorem card_common_roots_le_of_resultant {F : Type*} [Field F]
    (Fpoly Gpoly : ContactPoly (Polynomial F)) (wY W_F W d s : ℕ)
    (hwY : 1 ≤ wY)
    (hirr : Irreducible (liftCRat Fpoly))
    (hFd : Fpoly.natDegree = d) (hd : 1 ≤ d)
    (hGd : Gpoly.natDegree ≤ s) (hGne : Gpoly ≠ 0)
    (hFw : wdeg wY Fpoly ≤ W_F) (hGw : wdeg wY Gpoly ≤ W)
    (hWF_ge : d * (wY - 1) ≤ W_F)
    (hFZ0 : ∀ k j a, (((Fpoly.coeff k).coeff j).coeff a).natDegree ≤ 0)
    (hGZ0 : ∀ k j a, (((Gpoly.coeff k).coeff j).coeff a).natDegree ≤ 0)
    (hndvd : ¬ ∃ Q' : ContactPoly (RatFunc F), liftCRat Gpoly = liftCRat Fpoly * Q')
    (T : Finset (Polynomial F))
    (hvan : ∀ P ∈ T,
      evalContact (evalZContact Fpoly 0) P = 0 ∧ evalContact (evalZContact Gpoly 0) P = 0) :
    T.card ≤ (d * W + s * (W_F - d * (wY - 1))) / wY := by
  let Φ := Polynomial.resultant Fpoly Gpoly d s
  have hΦ : Φ ≠ 0 := resultant_ne_zero_of_not_dvd Fpoly Gpoly d s hirr hFd hd hGd hGne hndvd
  have hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤ d * W + s * (W_F - d * (wY - 1)) :=
    weightedSupportDegree_resultant_le Fpoly Gpoly wY W_F W d s hFw hGw hWF_ge
  have hB : Φ.natDegree ≤ (d * W + s * (W_F - d * (wY - 1))) / wY :=
    (natDegree_le_weightedSupportDegree_div Φ wY (by omega)).trans (Nat.div_le_div_right hWΦ)
  have hZ0 : ∀ j a, ((Φ.coeff j).coeff a).natDegree = 0 := fun j a =>
    Nat.eq_zero_of_le_zero (by simpa using degZ_resultant_le Fpoly Gpoly d s 0 0 hFZ0 hGZ0 j a)
  exact card_roots_le_of_degZ_zero Φ _ hΦ hB hZ0 T fun P hP =>
    triEval_resultant_eq_zero Fpoly Gpoly d s (le_of_eq hFd) hGd (by omega) 0 P
      (hvan P hP).1 (hvan P hP).2

section Concrete6401

open B6401Params B6401HybridP64 B6401IntFarkas
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-- **Corollary 5c (`hΦgap` bridge into `B6401IntFarkas.checkCapWitness_sound`):**
For `d = 1`, `W = 2 * A * m - 1`, if `Φ = Res_R(F, G; 1, s)` satisfies
`wd Φ wY ≤ (2 * A * m - 1) + s * (W_F - (wY - 1))` and `lineOrd Φ (domain i) (linePow u₀ u₁ q₀ i) ≥ 2 * m + s * (2 * k i - 1)`,
and on `Az z` the `G_F`-bucket upper bound `(hiGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) - ∑ i ∈ Az z, (2 * (k i : ℤ) - 1)) ≤ (hiGNum * N : ℤ)` holds,
then `Φ` satisfies the EXACT `hΦgap` hypothesis of `B6401IntFarkas.checkCapWitness_sound`! -/
theorem hΦgap_of_g_hi (u₀ u₁ : Idx → Fld) (q₀ W_F m s hiGNum hiGDen : ℕ)
    (hhiGDen : 0 < hiGDen)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤
      (2 * A * m - 1) + s * (W_F - (wY - 1)))
    (hWF_ge : wY - 1 ≤ W_F)
    (k : Idx → ℕ)
    (hord : ∀ i : Idx, (2 * (m : ℤ)) + (s : ℤ) * (2 * (k i : ℤ) - 1) ≤
      (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ))
    (Az : Finset Idx)
    (hG_hi : (hiGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ∑ i ∈ Az, (2 * (k i : ℤ) - 1)) ≤ (hiGNum * N : ℤ)) :
    (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
      (∑ i ∈ Az, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
      (2 * (m : ℤ)) * ((Az.card : ℤ) - (A : ℤ)) ≤
      ((s * hiGNum * N) / hiGDen : ℕ) := by
  have hWΦZ : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) ≤
      2 * (A : ℤ) * (m : ℤ) + (s : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ)) := by
    have h1 : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) ≤
        ((2 * A * m - 1 : ℕ) : ℤ) + (s : ℤ) * ((W_F - (wY - 1) : ℕ) : ℤ) := by
      exact_mod_cast hWΦ
    have h2 : ((2 * A * m - 1 : ℕ) : ℤ) ≤ 2 * (A : ℤ) * (m : ℤ) := by
      have : 2 * A * m - 1 ≤ 2 * A * m := Nat.sub_le _ _
      exact_mod_cast this
    rw [Nat.cast_sub hWF_ge] at h1
    nlinarith
  have hsum_ord : (2 * (m : ℤ)) * (Az.card : ℤ) + (s : ℤ) * (∑ i ∈ Az, (2 * (k i : ℤ) - 1)) ≤
      ∑ i ∈ Az, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Az) => hord i
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h
    linarith
  set Gz : ℤ := (W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) - ∑ i ∈ Az, (2 * (k i : ℤ) - 1)
  have hlhs_le : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
      (∑ i ∈ Az, (lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
      (2 * (m : ℤ)) * ((Az.card : ℤ) - (A : ℤ)) ≤ (s : ℤ) * Gz := by
    dsimp [Gz]; linarith
  refine hlhs_le.trans ?_
  by_cases hGz : Gz ≤ 0
  · have h1 : (s : ℤ) * Gz ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg s) hGz
    exact h1.trans (Nat.cast_nonneg _)
  · push Not at hGz
    lift Gz to ℕ using le_of_lt hGz with g hg
    have hmulZ : (hiGDen : ℤ) * ((s * g : ℕ) : ℤ) ≤ ((s * hiGNum * N : ℕ) : ℤ) := by
      push_cast
      have := mul_le_mul_of_nonneg_left hG_hi (Nat.cast_nonneg s)
      nlinarith
    have hmulN : hiGDen * (s * g) ≤ s * hiGNum * N := by exact_mod_cast hmulZ
    have hdiv : s * g ≤ (s * hiGNum * N) / hiGDen :=
      (Nat.le_div_iff_mul_le hhiGDen).mpr (by rw [mul_comm]; exact hmulN)
    exact_mod_cast hdiv

end Concrete6401

end B6401ResLineOrd
end ProximityPrize.SubmissionBinaryLower
