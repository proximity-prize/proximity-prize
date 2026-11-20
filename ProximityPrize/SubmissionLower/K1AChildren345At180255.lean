import ProximityPrize.SubmissionLower.Pack_K1DefsAt180255
import ProximityPrize.SubmissionLower.Fast068
set_option Elab.async false

/-! First K1A children at the 6916 radius (A = 180255), UNBUILT. Each is the official proof
re-run on the ported definitions with the generic official lemma it already used:
* c3: `K1_3.deficient_hankel_count` (k + l + t = n with 131072 + 49183 + 81889), bound n + 49182;
* c4: `Principal.generic_principal_bad_count_coarse` (copy of `Native.native_generic_principal_MCA_count`
  with a + q = 81889), bound p*(262144 + 81890);
* c5: the A-free private lemmas of `K1_5` copied verbatim (`constantRankCount`), bound p*81890.
Official 69.15 values for comparison: 311336, p*(262144+81880) = 733014149906392, p*81880 = 174462242734040. -/

section PackSource_NativeGenericPrincipalAt180255
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace FrobeniusLocator.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open FrobeniusLocator.Principal

def GenericPrincipalCertificateAt (u v : I → K) : Prop :=
  ∃ a q : ℕ, a+q=81889 ∧ Nonempty (PrincipalAt
    (fun b j => genericSlopeEmbedding (parameterSyndromes p IRSProfile.domain u v b j))
    131072 a q)

theorem generic_principal_MCA_count_at (U : Fin 2 → I → K)
    (hprincipal : GenericPrincipalCertificateAt (U 0) (U 1))
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U K1A.radiusAt) :
    Γ.card ≤ p*(262144+81890) := by
  obtain ⟨a,q,hsum,⟨P⟩⟩ := hprincipal
  have hbad : ∀ γ ∈ Γ,
      BadSlope IRSProfile.domain (U 0) (U 1) 131072 (131072+(131072-(a+q))) γ := by
    intro γ hγ
    rw [hsum]
    exact K1A.badSlope_at U γ (hΓ γ hγ)
  have hh := generic_principal_bad_count_coarse genericSlopeEmbedding
    (IsFractionRing.injective K[X] GenericSlopeField) p (by norm_num [p])
    IRSProfile.domain IRSProfile.domain.injective native_domain_fixed (U 0) (U 1)
    131072 131072 a q (by norm_num only [IRSProfile.card_index]) (by omega) P Γ hbad
  rw [IRSProfile.card_index] at hh
  exact hh.trans (Nat.mul_le_mul_left p (by omega))

end
end FrobeniusLocator.Native
end PackSource_NativeGenericPrincipalAt180255

section PackSource_K1A_3At180255
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace K1A_3
noncomputable section
open Polynomial FrobeniusLocator

/-- Copy of `K1_3.proof` (Fast068.lean:674) on the ported definitions. -/
theorem proof_at (u : K1A.Words) (Γ : Finset K1A.K) (hrank : K1A.firstRank u < 49183)
    (hΓ : K1A.BadFamily u Γ) : Γ.card ≤ 311326 := by
  have h := K1_3.deficient_hankel_count K1A.node (u 0) (u 1) K1A.node.injective
    131072 49183 81889 (K1A.firstRank u)
    (by rw [ProximityPrize.Benchmark.IRSProfile.card_index]) hrank rfl Γ
    (fun γ hγ => K1A.badSlope_at u γ (hΓ γ hγ))
  rw [ProximityPrize.Benchmark.IRSProfile.card_index] at h
  omega

theorem c3_of (Bg : K1A.Budget) (h : 311326 ≤ Bg.c3) : K1A.c3 Bg :=
  fun u Γ hr hΓ => (proof_at u Γ hr hΓ).trans h

end
end K1A_3
end PackSource_K1A_3At180255

section PackSource_K1A_4At180255
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace K1A_4
noncomputable section
open Polynomial FrobeniusLocator

/-- Copy of `K1_4.proof` (Fast069.lean:8616) on the ported definitions. -/
theorem proof_at (u : K1A.Words) (Γ : Finset K1A.K) (hprincipal : K1A.HomogeneousPrincipal u)
    (hΓ : K1A.BadFamily u Γ) : Γ.card ≤ 733035456970722 := by
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (81889 - a) = 81889 := by omega
  have hcertificate : Native.GenericPrincipalCertificateAt (u 0) (u 1) := by
    refine ⟨a, 81889 - a, hsum, ⟨{
      generator := g
      nonzero := hg
      degree_bound := hga
      kernel_eq := ?_
    }⟩⟩
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ 81889 ∧
      ((K1A.twoBlock u).map (algebraMap K1A.K[X] K1A.Frac)).mulVec
        (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : K1A.Frac[X], Q.natDegree ≤ 81889 - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ 81889 :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  exact (Native.generic_principal_MCA_count_at u hcertificate Γ hΓ).trans (by norm_num [Native.p])

theorem c4_of (Bg : K1A.Budget) (h : 733035456970722 ≤ Bg.c4) : K1A.c4 Bg :=
  fun u Γ hp hΓ => (proof_at u Γ hp hΓ).trans h

end
end K1A_4
end PackSource_K1A_4At180255

section PackSource_K1A_5At180255
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000

namespace K1A_5
noncomputable section

open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

/-- The ordinary and Frobenius coefficients, in the order used by `K1.coefficientStack`. -/
private def coefficientStack (p : ℕ) (x : ι → F) (u v : ι → F) (L t : ℕ) :
    Matrix (Fin 4 × Fin L) (Fin (t + 1)) F := fun i j =>
  if i.1 = 0 then syndrome x u (i.2.val + j.val) else
  if i.1 = 1 then syndrome x v (i.2.val + j.val) else
  if i.1 = 2 then syndrome x u (i.2.val + j.val) ^ p else
    syndrome x v (i.2.val + j.val) ^ p

/-- A common coefficient-kernel vector annihilates the whole polynomial pencil. -/
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t + 1) → F) (hc : (coefficientStack p x u v L t).mulVec c = 0) :
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0 := by
  funext i
  have h0 := congrFun hc (0, i.2)
  have h1 := congrFun hc (1, i.2)
  have h2 := congrFun hc (2, i.2)
  have h3 := congrFun hc (3, i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientStack, Fin.reduceEq,
    ite_true, ite_false, Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi : i.1 = 0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R := F) * C (∑ j, syndrome x v (i.2.val + j.val) * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h0, h1, map_zero, mul_zero, add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R := F) ^ p * C (∑ j, syndrome x v (i.2.val + j.val) ^ p * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h2, h3, map_zero, mul_zero, add_zero]

/-- Equal ranks give a fixed kernel of the correct dimension for the normal-fiber count. -/
private theorem constantRankCount {E : Type} [Field E]
    (φ : F[X] →+* E) (hφ : Function.Injective φ) (p : ℕ) [ExpChar F p] (hp : 1 ≤ p)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A) (hL : k + L = A)
    (ht : A + t = Fintype.card ι)
    (r : ℕ) (hgeneric : ((stacked p x u v L t).map φ).rank = r)
    (hconstant : (coefficientStack p x u v L t).rank = r)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k A γ) : Γ.card ≤ p * r := by
  let M := stacked p x u v L t
  let C₀ := coefficientStack p x u v L t
  let W := LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h := LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientStack p x u v L t).rank + Module.finrank F W = _ at h
    rw [hconstant, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j)) = 0 :=
    coefficientKernel_annihilates p x u v L t c hc
  have hminor : (NormalFiber.pivot B).det.natDegree ≤ p * r := by
    have h := NormalFiber.minor_degree_le φ M r B (fun _ => p) (by
      intro i j
      exact (stacked_entry_natDegree p x u v L t i j).trans (by split_ifs <;> omega))
    simpa [Nat.mul_comm] using h
  exact Principal.constant_kernel_count p x hx hfixed u v k A L t (p * r) hkA hL ht
    _ B.minor_ne hminor (Principal.constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW)
    Γ hΓ


/-- Copy of `K1_5.proof` (Fast068.lean:771) on the ported definitions. -/
theorem proof_at (u : K1A.Words) (Γ : Finset K1A.K) (hu : K1A.ConstantKernel u)
    (hΓ : K1A.BadFamily u Γ) : Γ.card ≤ 174483549798370 := by
  let φ := algebraMap K1A.K[X] K1A.Frac
  have hrank : ((K1A.twoBlock u).map φ).rank = K1A.stackRank u := rfl
  have hconstant : (coefficientStack K1A.p K1A.node (u 0) (u 1) 49183 81889).rank =
      K1A.stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective K1A.K[X] K1A.Frac)
    K1A.p (by norm_num [Native.p]) K1A.node IRSProfile.domain.injective Native.native_domain_fixed
    (u 0) (u 1) 131072 180255 49183 81889 (by norm_num) (by norm_num)
    (by norm_num only [IRSProfile.card_index]) (K1A.stackRank u) hrank hconstant
    Γ (fun γ hγ => K1A.badSlope_at u γ (hΓ γ hγ))
  have hr : K1A.stackRank u ≤ 81890 := by
    have h := Matrix.rank_le_card_width ((K1A.twoBlock u).map φ)
    simpa only [hrank, Fintype.card_fin] using h
  calc
    Γ.card ≤ K1A.p * K1A.stackRank u := hcount
    _ ≤ K1A.p * 81890 := Nat.mul_le_mul_left K1A.p hr
    _ = 174483549798370 := by norm_num [Native.p]

theorem c5_of (Bg : K1A.Budget) (h : 174483549798370 ≤ Bg.c5) : K1A.c5 Bg :=
  fun u Γ hk hΓ => (proof_at u Γ hk hΓ).trans h

end
end K1A_5
end PackSource_K1A_5At180255
