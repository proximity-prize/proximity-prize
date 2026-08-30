import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.BI
namespace ProximityPrize.SubmissionLower.RCN181
open scoped BigOperators
open Set UniqueFactorizationMonoid
open RCN100
open RCN180
open RCN137
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K : Type*} [Field K]
abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K
local instance : StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def submoduleReconstructLinear {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K)) :
   V →ₗ[K] Poly4 K :=
 (reconstructLinear (K := K) D w L s).comp V.subtype
theorem submoduleReconstructLinear_injective {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K)) :
   Function.Injective (submoduleReconstructLinear V) := by
 intro x y h
 apply Subtype.ext
 exact reconstructLinear_injective (K := K) D w L s h
def commonDivisorProof {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) :
   ∀ v : V,commonGCD V b ∣ submoduleReconstructLinear V v := by
 intro v
 exact commonGCD_dvd V b v
def commonQuotientLinear {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V)
   (hH : commonGCD V b ≠ 0) : V →ₗ[K] Poly4 K :=
 quotientLinear (submoduleReconstructLinear V) (commonGCD V b) hH
   (commonDivisorProof V b)
def quotientDvdSubmodule {V : Type*} [AddCommGroup V] [Module K V]
   (q : V →ₗ[K] Poly4 K) (F : Poly4 K) : Submodule K V where
 carrier := {v | F ∣ q v}
 zero_mem' := by simp
 add_mem' := by
   intro x y hx hy
   change F ∣ q x at hx
   change F ∣ q y at hy
   change F ∣ q (x + y)
   rw [map_add]
   exact dvd_add hx hy
 smul_mem' := by
   intro a x hx
   change F ∣ q x at hx
   change F ∣ q (a • x)
   rw [map_smul,MvPolynomial.smul_eq_C_mul]
   exact dvd_mul_of_dvd_right hx _
theorem quotientDvdSubmodule_ne_top {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V)
   (hH : commonGCD V b ≠ 0) (F : Poly4 K) (hF : Irreducible F) :
   quotientDvdSubmodule (commonQuotientLinear V b hH) F ≠ ⊤ := by
 intro htop
 have hall : ∀ v : V,F ∣ commonQuotientLinear V b hH v := by
   intro v
   have hv : v ∈ quotientDvdSubmodule (commonQuotientLinear V b hH) F := by
     rw [htop]
     trivial
   exact hv
 have hmul : commonGCD V b * F ∣ commonGCD V b := by
   apply (dvd_commonGCD_iff V b (commonGCD V b * F)).2
   intro v
   have hq := hall v
   have heq := recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear V) (commonGCD V b)
     (commonDivisorProof V b) v
   change commonGCD V b * F ∣ submoduleReconstructLinear V v
   rw [heq]
   exact mul_dvd_mul_left (commonGCD V b) hq
 have hFone : F ∣ (1 : Poly4 K) := by
   apply (mul_dvd_mul_iff_left hH).mp
   simpa using hmul
 exact hF.not_isUnit (isUnit_iff_dvd_one.mpr hFone)
theorem exists_common_quotient_isRelPrime {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] [Nonempty ι] (b : Module.Basis ι K V)
   (hH : commonGCD V b ≠ 0) (P : Poly4 K) (hP : P ≠ 0)
   (hcard : (normalizedFactorSet P).card < ENat.card K) :
   ∃ v : V,v ≠ 0 ∧ IsRelPrime (commonQuotientLinear V b hH v) P := by
 classical
 letI : DecidableEq (Fin 4) := Classical.decEq _
 by_cases hunit : IsUnit P
 · let i : ι := Classical.choice inferInstance
   refine ⟨b i,b.ne_zero i,hunit.isRelPrime_right⟩
 · let S := normalizedFactorSet P
   have hSne : S.Nonempty := by
     obtain ⟨F,hF⟩ := exists_mem_normalizedFactors hP hunit
     exact ⟨F,Multiset.mem_toFinset.mpr hF⟩
   let bad : S → Submodule K V := fun F ↦
     quotientDvdSubmodule (commonQuotientLinear V b hH) F.1
   have hproper : ∀ F : S,bad F ≠ ⊤ := by
     intro F
     exact quotientDvdSubmodule_ne_top V b hH F.1
       (normalizedFactorSet_spec P F.1 F.2).1
   have hsmall : (Finset.univ : Finset S).card < ENat.card K := by
     simpa [S] using hcard
   have hss := RCN133.finite_iUnion_ssubset
     (Finset.univ : Finset S) bad hproper hsmall
   obtain ⟨v,hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hss
   have havoid : ∀ F : S,v ∉ bad F := by
     intro F hmem
     apply hv
     simp only [Set.mem_iUnion,Finset.mem_univ,true_and]
     exact ⟨F,trivial,hmem⟩
   have hv0 : v ≠ 0 := by
     intro hz
     obtain ⟨F,hF⟩ := hSne
     have hnot := havoid ⟨F,hF⟩
     apply hnot
     subst v
     change F ∣ commonQuotientLinear V b hH 0
     simp
   refine ⟨v,hv0,?_⟩
   apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
   · intro hzero
     exact hP hzero.2
   · intro z hz hzq hzPdiv
     obtain ⟨F,hFnorm,hassoc⟩ :=
       exists_mem_normalizedFactors_of_dvd hP hz hzPdiv
     have hnot := havoid
       (⟨F,Multiset.mem_toFinset.mpr hFnorm⟩ : S)
     apply hnot
     change F ∣ commonQuotientLinear V b hH v
     exact hassoc.dvd_iff_dvd_left.mp hzq
theorem gcd_mul_right_of_isRelPrime_associated
   (P H q : Poly4 K) (hc : IsRelPrime q P) :
   Associated (gcd P (H * q)) (gcd P H) := by
 apply associated_of_dvd_dvd
 · have hleft : gcd P (H * q) ∣ P := gcd_dvd_left P (H * q)
   have hright : gcd P (H * q) ∣ H * q := gcd_dvd_right P (H * q)
   have hcop : IsRelPrime (gcd P (H * q)) q :=
     hc.symm.of_dvd_left hleft
   exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
 · exact dvd_gcd (gcd_dvd_left P H)
     ((gcd_dvd_right P H).trans (dvd_mul_right H q))
theorem irreducible_positive_degree_sum_fin4
   (F : Poly4 K) (hF : Irreducible F) :
   0 < F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 := by
 by_contra hn
 have hsum : F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 = 0 :=
   Nat.eq_zero_of_not_pos hn
 have h0 : F.degreeOf (0 : Fin 4) = 0 := by omega
 have h1 : F.degreeOf (1 : Fin 4) = 0 := by omega
 have h2 : F.degreeOf (2 : Fin 4) = 0 := by omega
 have h3 : F.degreeOf (3 : Fin 4) = 0 := by omega
 have hdeg (i : Fin 4) : F.degreeOf i = 0 := by
   fin_cases i
   · simpa using h0
   · simpa using h1
   · simpa using h2
   · simpa using h3
 have heq : F = MvPolynomial.C (F.coeff 0) := by
   apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
   apply Nat.eq_zero_of_le_zero
   rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
   intro d hd
   have hd0 : d = 0 := by
     ext i
     have hi := MvPolynomial.monomial_le_degreeOf i hd
     rw [hdeg i] at hi
     exact Nat.eq_zero_of_le_zero hi
   simp [hd0]
 have hc : F.coeff 0 ≠ 0 := by
   intro hz
   apply hF.ne_zero
   rw [heq,hz,map_zero]
 apply hF.not_isUnit
 rw [heq]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem normalizedFactorSet_card_le_degree_sum_fin4
   (P : Poly4 K) (hP : P ≠ 0) :
   (normalizedFactorSet P).card ≤
     P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3 := by
 classical
 calc
   (normalizedFactorSet P).card =
       ∑ _F ∈ normalizedFactorSet P,(1 : ℕ) := by simp
   _ ≤ ∑ F ∈ normalizedFactorSet P,
       (F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3) := by
     apply Finset.sum_le_sum
     intro F hF
     exact irreducible_positive_degree_sum_fin4 F
       (normalizedFactorSet_spec P F hF).1
   _ = (∑ F ∈ normalizedFactorSet P,F.degreeOf 0) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 1) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 2) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 3) := by
     simp only [Finset.sum_add_distrib]
   _ ≤ P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3 := by
     gcongr <;> exact normalizedFactorSet_degree_budget P hP _
theorem degreeOf_X_le_of_mem_flagBox (P : Poly4 K)
   (D w L s : ℕ) (hbox : P ∈ globalCoefficientBox K D w L s) :
   P.degreeOf (0 : Fin 4) ≤ D - 1 := by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hc := (hbox hd).2.2
 omega
theorem normalizedFactorSet_card_le_of_mem_flagBox
   (P : Poly4 K) (D w L s : ℕ) (hw : 0 < w) (hP : P ≠ 0)
   (hbox : P ∈ globalCoefficientBox K D w L s) :
   (normalizedFactorSet P).card ≤
     (D - 1) + (D - 1) / w + s + L := by
 have hsum := normalizedFactorSet_card_le_degree_sum_fin4 P hP
 have hX := degreeOf_X_le_of_mem_flagBox P D w L s hbox
 have hY : P.degreeOf (1 : Fin 4) ≤ (D - 1) / w := by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   apply (Nat.le_div_iff_mul_le hw).mpr
   have hc := (hbox hd).2.2
   have hm : d 1 * w = w * d 1 := Nat.mul_comm _ _
   omega
 have hR : P.degreeOf (2 : Fin 4) ≤ s := by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hZ : P.degreeOf (3 : Fin 4) ≤ L := by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hL := (hbox hd).1
   omega
 omega
end
end ProximityPrize.SubmissionLower.RCN181
