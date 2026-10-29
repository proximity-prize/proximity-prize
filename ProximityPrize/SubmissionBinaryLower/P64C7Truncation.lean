import ProximityPrize.SubmissionBinaryLower.P64C7HS
import ProximityPrize.SubmissionBinaryLower.P64FoundSupp
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Truncated multiples for the bounded-pole count

Projection to a finite exponent set is linear. If the set covers all terms
below normal degree `s` in `U`, the discarded part is divisible by `U^s`.
Primality of `U` then makes truncation of `S*G` injective on bounded cofactors.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Truncation

open Polynomial P64Found

variable {F : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

noncomputable def U : Tri := Polynomial.C (Polynomial.X : Polynomial (Polynomial F))

noncomputable def cut (T : Finset (ℕ × ℕ × ℕ)) : Tri →ₗ[F] Tri :=
  (comb3 T).comp (extr3 T)

lemma c3_cut (T : Finset (ℕ × ℕ × ℕ)) (R : Tri) (a b l : ℕ) :
    c3 (cut T R) a b l = if (a, b, l) ∈ T then c3 R a b l else 0 := by
  classical
  rw [cut, LinearMap.comp_apply, c3_comb3]
  split_ifs <;> rfl

lemma cut_mem (T : Finset (ℕ × ℕ × ℕ)) (R : Tri) : cut T R ∈ supp T :=
  comb3_mem_supp T (extr3 T R)

lemma U_pow_dvd_iff (s : ℕ) (R : Tri) :
    U ^ s ∣ R ↔ ∀ a b, a < s → (R.coeff b).coeff a = 0 := by
  rw [U, ← Polynomial.C_pow, Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h a b ha
    exact Polynomial.X_pow_dvd_iff.mp (h b) a ha
  · intro h b
    exact Polynomial.X_pow_dvd_iff.mpr (fun a ha => h a b ha)

lemma eq_zero_of_U_pow_dvd (s : ℕ) (T : Finset (ℕ × ℕ × ℕ)) (R : Tri)
    (hT : ∀ p ∈ T, p.1 < s) (hR : R ∈ supp T) (hd : U ^ s ∣ R) : R = 0 := by
  ext b a l
  by_cases ha : a < s
  · have hz := (U_pow_dvd_iff s R).mp hd a b ha
    simp [hz]
  · exact hR a b l (fun hp => ha (hT _ hp))

lemma U_pow_dvd_sub_cut (s : ℕ) (T : Finset (ℕ × ℕ × ℕ)) (R : Tri)
    (hcover : ∀ a b l, a < s → c3 R a b l ≠ 0 → (a, b, l) ∈ T) :
    U ^ s ∣ R - cut T R := by
  classical
  apply (U_pow_dvd_iff s _).mpr
  intro a b ha
  ext l
  change c3 (R - cut T R) a b l = 0
  have hc : c3 (R - cut T R) a b l = c3 R a b l - c3 (cut T R) a b l := by
    simp [c3]
  rw [hc, c3_cut]
  by_cases hp : (a, b, l) ∈ T
  · simp [hp]
  · have hz : c3 R a b l = 0 := by
      by_contra hn
      exact hp (hcover a b l ha hn)
    simp [hp, hz]

lemma prime_U : Prime (U : Tri) :=
  Polynomial.prime_C_iff.mpr Polynomial.prime_X

lemma not_U_dvd (S : Tri)
    (hS : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0) : ¬ U ∣ S := by
  intro hd
  apply hS
  ext b : 1
  have hb := (Polynomial.C_dvd_iff_dvd_coeff _ S).mp hd b
  have hz := Polynomial.X_dvd_iff.mp hb
  simpa using hz

noncomputable def multipleMap (S : Tri) (BT MT : Finset (ℕ × ℕ × ℕ)) :
    supp (F := F) MT →ₗ[F] supp (F := F) BT :=
  LinearMap.codRestrict (supp BT)
    ((cut BT).comp ((LinearMap.mulLeft F S).comp (supp MT).subtype))
    (fun G => cut_mem BT (S * G.1))

lemma multipleMap_val (S : Tri) (BT MT : Finset (ℕ × ℕ × ℕ)) (G : supp (F := F) MT) :
    (multipleMap S BT MT G).1 = cut BT (S * G.1) := rfl

theorem multipleMap_injective (S : Tri) (s : ℕ) (BT MT : Finset (ℕ × ℕ × ℕ))
    (hS : S.map (Polynomial.constantCoeff (R := Polynomial F)) ≠ 0)
    (hMT : ∀ p ∈ MT, p.1 < s)
    (hcover : ∀ G ∈ supp (F := F) MT, ∀ a b l,
      a < s → c3 (S * G) a b l ≠ 0 → (a, b, l) ∈ BT) :
    Function.Injective (multipleMap S BT MT) := by
  apply (injective_iff_map_eq_zero (multipleMap S BT MT)).mpr
  intro G hG
  apply Subtype.ext
  have hc : cut BT (S * G.1) = 0 := congrArg Subtype.val hG
  have hd := U_pow_dvd_sub_cut s BT (S * G.1) (hcover G.1 G.2)
  rw [hc, sub_zero] at hd
  have hdiv : U ^ s ∣ G.1 := prime_U.pow_dvd_of_dvd_mul_left s (not_U_dvd S hS) hd
  exact eq_zero_of_U_pow_dvd s MT G.1 hMT G.2 hdiv

noncomputable def residualIdeal (s : ℕ) (S : Tri) : Ideal Tri :=
  Ideal.span {U ^ s, S}

lemma residual_U_mem (s : ℕ) (S : Tri) : U ^ s ∈ residualIdeal s S :=
  Ideal.subset_span (by simp)

lemma residual_S_mem (s : ℕ) (S : Tri) : S ∈ residualIdeal s S :=
  Ideal.subset_span (by simp)

theorem multipleMap_mem (S : Tri) (s : ℕ) (BT MT : Finset (ℕ × ℕ × ℕ))
    (hcover : ∀ G ∈ supp (F := F) MT, ∀ a b l,
      a < s → c3 (S * G) a b l ≠ 0 → (a, b, l) ∈ BT) (G : supp (F := F) MT) :
    (multipleMap S BT MT G).1 ∈ residualIdeal s S := by
  have hs : S * G.1 ∈ residualIdeal s S := Ideal.mul_mem_right _ _ (residual_S_mem s S)
  obtain ⟨Q, hQ⟩ := U_pow_dvd_sub_cut s BT (S * G.1) (hcover G.1 G.2)
  have hd : S * G.1 - cut BT (S * G.1) ∈ residualIdeal s S := by
    rw [hQ]
    exact Ideal.mul_mem_right _ _ (residual_U_mem s S)
  have h := sub_mem hs hd
  simpa only [multipleMap_val, sub_sub_cancel] using h

end P64C7Truncation
end ProximityPrize.SubmissionBinaryLower
