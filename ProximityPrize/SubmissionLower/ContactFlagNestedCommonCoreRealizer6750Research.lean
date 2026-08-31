import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactNestedFamilyCommonCoreRealization6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactFlagNestedCommonCoreRealizer6750Research

open scoped Classical
open UniqueFactorizationMonoid
open ContactFlagInterpolation6641Research
open ContactFlagKernelZeroExtension6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactNestedFamilyCommonCoreRealization6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactFullKernelCoprimePair6660Research
open ContactFullKernelHeightTwoRouting6660Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

universe u v w x

variable {K : Type u} [Field K]
variable {I : Type v} [Fintype I]
variable {ι : Type w}

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

local instance : StrongNormalizationMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

local instance : NormalizedGCDMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)

 

def reconstructedSelectedFamily
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1))) :
    Submodule K (Poly4 K) :=
  LinearMap.range
    ((flagReconstructLinear (K := K) D w0 Lmax s).comp
      (embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
        cap hcap Selected).subtype)

 

theorem reconstruct_mem_nestedFiveCap_of_mem_selectedFamilySum
    (D w0 Lmax s m T YS S : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (hsource : ∀ i (theta : Selected i),
      reconstruct K D w0 (cap i) s theta.1.1 ∈
        nestedFiveCapCoefficientBox K D w0 T YS S)
    (a : embeddedSelectedKernelFamilySum D w0 Lmax s m
      nodes u0 u1 cap hcap Selected) :
    reconstruct K D w0 Lmax s a.1 ∈
      nestedFiveCapCoefficientBox K D w0 T YS S := by
  let Box := nestedFiveCapCoefficientBox K D w0 T YS S
  let Pre : Submodule K (CoefficientIndex D w0 Lmax s → K) :=
    Box.comap (flagReconstructLinear (K := K) D w0 Lmax s)
  have hsum : embeddedSelectedKernelFamilySum D w0 Lmax s m
      nodes u0 u1 cap hcap Selected ≤ Pre := by
    apply iSup_le
    intro i
    rintro _ ⟨theta, rfl⟩
    change reconstruct K D w0 Lmax s
      (zeroExtendConstraintKernelToArray (K := K) (D := D)
        (w := w0) (s := s) (m := m) (hcap i)
        nodes u0 u1 theta.1) ∈ Box
    rw [zeroExtendConstraintKernelToArray_apply, reconstruct_zeroExtendTotal]
    exact hsource i theta
  exact hsum a.2

 



theorem exists_coprime_commonGCDAtMax_residual
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (g : CoefficientIndex D w0 Lmax s → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K
      (adjoinFixedArray g
        (embeddedSelectedKernelFamilySum D w0 Lmax s m
          nodes u0 u1 cap hcap Selected)))
    (hg : reconstruct K D w0 Lmax s g ≠ 0)
    (hcard : ∀ Q : Poly4 K,
      reconstruct K D w0 Lmax s g =
        commonGCDAtMax
          (adjoinFixedArray g
            (embeddedSelectedKernelFamilySum D w0 Lmax s m
              nodes u0 u1 cap hcap Selected)) b * Q →
      Q ≠ 0 → (allFactors Q).card < ENat.card K) :
    ∃ Q : Poly4 K,
      Q ≠ 0 ∧
      reconstruct K D w0 Lmax s g =
        commonGCDAtMax
          (adjoinFixedArray g
            (embeddedSelectedKernelFamilySum D w0 Lmax s m
              nodes u0 u1 cap hcap Selected)) b * Q ∧
      ∃ vT : adjoinFixedArray g
          (embeddedSelectedKernelFamilySum D w0 Lmax s m
            nodes u0 u1 cap hcap Selected),
        vT.1 ∈ embeddedSelectedKernelFamilySum D w0 Lmax s m
            nodes u0 u1 cap hcap Selected ∧
        ∃ T : Poly4 K,
          reconstruct K D w0 Lmax s vT.1 =
            commonGCDAtMax
              (adjoinFixedArray g
                (embeddedSelectedKernelFamilySum D w0 Lmax s m
                  nodes u0 u1 cap hcap Selected)) b * T ∧
          NoCommonNonunitDivisor Q T := by
  let Warray := embeddedSelectedKernelFamilySum D w0 Lmax s m
    nodes u0 u1 cap hcap Selected
  let V := adjoinFixedArray g Warray
  let H := commonGCDAtMax V b
  let G := reconstruct K D w0 Lmax s g
  let reconW : Warray →ₗ[K] Poly4 K :=
    (flagReconstructLinear (K := K) D w0 Lmax s).comp Warray.subtype
  let Wpoly : Submodule K (Poly4 K) := LinearMap.range reconW
  have hgV : g ∈ V := fixed_mem_adjoinFixedArray g Warray
  have hHdvdG : H ∣ G := commonGCDAtMax_dvd V b ⟨g, hgV⟩
  have hH : H ≠ 0 := by
    intro hzero
    obtain ⟨Q, hQ⟩ := hHdvdG
    apply hg
    change G = 0
    rw [hQ, hzero, zero_mul]
  obtain ⟨Q, hGQ⟩ := hHdvdG
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hg
    change G = 0
    rw [hGQ, hzero, mul_zero]
  have hiff : ∀ F : Poly4 K,
      F ∣ H ↔ ∀ q : adjoinFixed G Wpoly, F ∣ (q : Poly4 K) := by
    intro F
    constructor
    · intro hFH
      apply (dvd_all_adjoinFixed_iff F G Wpoly).mpr
      constructor
      · exact hFH.trans (commonGCDAtMax_dvd V b ⟨g, hgV⟩)
      · intro q
        obtain ⟨a, ha⟩ := q.2
        let va : V := ⟨a.1, mem_adjoinFixedArray_of_mem g Warray a.2⟩
        have hdiv := hFH.trans (commonGCDAtMax_dvd V b va)
        change F ∣ reconW a at hdiv
        rw [ha] at hdiv
        exact hdiv
    · intro hall
      have hsides := (dvd_all_adjoinFixed_iff F G Wpoly).mp hall
      apply (dvd_commonGCDAtMax_adjoinedSelectedFamily_iff
        D w0 Lmax s m nodes u0 u1 cap hcap Selected g b F).mpr
      constructor
      · exact hsides.1
      · intro i theta
        let a : Warray :=
          ⟨zeroExtendConstraintKernelToArray (K := K) (D := D)
              (w := w0) (s := s) (m := m) (hcap i)
              nodes u0 u1 theta.1,
            selected_zeroExtend_mem_familySum D w0 Lmax s m
              nodes u0 u1 cap hcap Selected i theta⟩
        let q : Wpoly := ⟨reconW a, ⟨a, rfl⟩⟩
        have hdiv := hsides.2 q
        change F ∣ reconW a at hdiv
        change F ∣ reconstruct K D w0 Lmax s
          (zeroExtendConstraintKernelToArray (K := K) (D := D)
            (w := w0) (s := s) (m := m) (hcap i)
            nodes u0 u1 theta.1) at hdiv
        rw [zeroExtendConstraintKernelToArray_apply,
          reconstruct_zeroExtendTotal] at hdiv
        exact hdiv
  have hcore : IsExactAdjoinedCommonCore H G Wpoly :=
    isExactAdjoinedCommonCore_of_dvd_iff H G Wpoly hH hiff
  have hfield : (allFactors Q).card < ENat.card K := by
    apply hcard Q
    · simpa only [G, H, V, Warray] using hGQ
    · exact hQ
  obtain ⟨q, hqfactor, hcoprime⟩ :=
    exists_member_realizing_exact_common_core Wpoly H G Q hcore
      hGQ hQ hfield
  obtain ⟨a, ha⟩ := q.2
  let vT : V := ⟨a.1, mem_adjoinFixedArray_of_mem g Warray a.2⟩
  let T : Poly4 K :=
    fixedFactorQuotientLinearMap H hH Wpoly hcore.2.2.1 q
  refine ⟨Q, hQ, ?_, vT, a.2, T, ?_, ?_⟩
  · simpa only [G, H, V, Warray] using hGQ
  · calc
      reconstruct K D w0 Lmax s vT.1 = reconW a := rfl
      _ = (q : Poly4 K) := ha
      _ = H * T := by simpa only [T] using hqfactor.symm
      _ = commonGCDAtMax
          (adjoinFixedArray g
            (embeddedSelectedKernelFamilySum D w0 Lmax s m
              nodes u0 u1 cap hcap Selected)) b * T := by
        rfl
  · simpa only [T] using hcoprime

end

end ContactFlagNestedCommonCoreRealizer6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedCommonCoreRealizer6750Research.exists_coprime_commonGCDAtMax_residual
