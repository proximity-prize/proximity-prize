import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research

 










namespace ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research

open scoped Classical BigOperators
open ContactFlagInterpolation6641Research
open ContactFlagKernelZeroExtension6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v w x

variable {K : Type u} [Field K]
variable {I : Type v} [Fintype I]
variable {ι : Type w}

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 

def embeddedKernelFamilySum
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax) :
    Submodule K (CoefficientIndex D w0 Lmax s → K) :=
  ⨆ i, LinearMap.range
    (zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
      (s := s) (m := m) (hcap i) nodes u0 u1)

theorem zeroExtend_mem_embeddedKernelFamilySum
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (i : ι)
    (theta : LinearMap.ker
      (constraintMap K D w0 (cap i) s m nodes u0 u1)) :
    zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
        (s := s) (m := m) (hcap i) nodes u0 u1 theta ∈
      embeddedKernelFamilySum D w0 Lmax s m nodes u0 u1 cap hcap := by
  exact (le_iSup (fun j ↦ LinearMap.range
    (zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
      (s := s) (m := m) (hcap j) nodes u0 u1)) i) ⟨theta, rfl⟩

 

def adjoinFixedArray
    {D w0 Lmax s : Nat}
    (g : CoefficientIndex D w0 Lmax s → K)
    (W : Submodule K (CoefficientIndex D w0 Lmax s → K)) :
    Submodule K (CoefficientIndex D w0 Lmax s → K) :=
  K ∙ g ⊔ W

theorem fixed_mem_adjoinFixedArray
    {D w0 Lmax s : Nat}
    (g : CoefficientIndex D w0 Lmax s → K)
    (W : Submodule K (CoefficientIndex D w0 Lmax s → K)) :
    g ∈ adjoinFixedArray g W := by
  exact (le_sup_left : K ∙ g ≤ adjoinFixedArray g W)
    (Submodule.subset_span (Set.mem_singleton g))

theorem mem_adjoinFixedArray_of_mem
    {D w0 Lmax s : Nat}
    (g : CoefficientIndex D w0 Lmax s → K)
    (W : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {q : CoefficientIndex D w0 Lmax s → K} (hq : q ∈ W) :
    q ∈ adjoinFixedArray g W :=
  (le_sup_right : W ≤ adjoinFixedArray g W) hq

local instance : StrongNormalizationMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

local instance : NormalizedGCDMonoid (Poly4 K) :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)

 

def commonGCDAtMax
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] (b : Module.Basis β K V) : Poly4 K :=
  Finset.univ.gcd (fun i ↦ reconstruct K D w0 Lmax s (b i).1)

theorem commonGCDAtMax_dvd_basis
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] (b : Module.Basis β K V) (i : β) :
    commonGCDAtMax V b ∣ reconstruct K D w0 Lmax s (b i).1 := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem commonGCDAtMax_ne_zero
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] [Nonempty β] (b : Module.Basis β K V) :
    commonGCDAtMax V b ≠ 0 := by
  rw [commonGCDAtMax, Finset.gcd_ne_zero_iff]
  let i : β := Classical.choice inferInstance
  refine ⟨i, Finset.mem_univ i, ?_⟩
  apply reconstruct_ne_zero K D w0 Lmax s
  intro hi
  apply b.ne_zero i
  exact Subtype.ext hi

theorem commonGCDAtMax_dvd
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] (b : Module.Basis β K V) (v : V) :
    commonGCDAtMax V b ∣ reconstruct K D w0 Lmax s v.1 := by
  rw [← b.sum_repr v]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change commonGCDAtMax V b ∣
    flagReconstructLinear (K := K) D w0 Lmax s
      (∑ i, (b.repr v) i • (b i).1)
  rw [map_sum]
  apply Finset.dvd_sum
  intro i hi
  rw [map_smul, MvPolynomial.smul_eq_C_mul]
  exact dvd_mul_of_dvd_right (commonGCDAtMax_dvd_basis V b i) _

theorem dvd_commonGCDAtMax_iff
    {D w0 Lmax s : Nat}
    (V : Submodule K (CoefficientIndex D w0 Lmax s → K))
    {β : Type x} [Fintype β] (b : Module.Basis β K V)
    (F : Poly4 K) :
    F ∣ commonGCDAtMax V b ↔
      ∀ v : V, F ∣ reconstruct K D w0 Lmax s v.1 := by
  constructor
  · intro hF v
    exact hF.trans (commonGCDAtMax_dvd V b v)
  · intro hF
    apply Finset.dvd_gcd_iff.mpr
    intro i hi
    exact hF (b i)

 

def reconstructedMultipleSubmodule
    {D w0 Lmax s : Nat} (F : Poly4 K) :
    Submodule K (CoefficientIndex D w0 Lmax s → K) :=
  ((Ideal.span ({F} : Set (Poly4 K))).restrictScalars K).comap
    (flagReconstructLinear (K := K) D w0 Lmax s)

theorem mem_reconstructedMultipleSubmodule_iff
    {D w0 Lmax s : Nat} (F : Poly4 K)
    (theta : CoefficientIndex D w0 Lmax s → K) :
    theta ∈ reconstructedMultipleSubmodule (K := K)
      (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F ↔
      F ∣ reconstruct K D w0 Lmax s theta := by
  simp [reconstructedMultipleSubmodule, Ideal.mem_span_singleton,
    flagReconstructLinear]

 
theorem dvd_commonGCDAtMax_adjoinedFamily_iff
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (g : CoefficientIndex D w0 Lmax s → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K
      (adjoinFixedArray g
        (embeddedKernelFamilySum D w0 Lmax s m nodes u0 u1 cap hcap)))
    (F : Poly4 K) :
    F ∣ commonGCDAtMax
        (adjoinFixedArray g
          (embeddedKernelFamilySum D w0 Lmax s m nodes u0 u1 cap hcap)) b ↔
      F ∣ reconstruct K D w0 Lmax s g ∧
        ∀ (i : ι)
          (theta : LinearMap.ker
            (constraintMap K D w0 (cap i) s m nodes u0 u1)),
          F ∣ reconstruct K D w0 (cap i) s theta.1 := by
  let W := embeddedKernelFamilySum D w0 Lmax s m nodes u0 u1 cap hcap
  rw [dvd_commonGCDAtMax_iff]
  constructor
  · intro hall
    constructor
    · exact hall ⟨g, fixed_mem_adjoinFixedArray g W⟩
    · intro i theta
      have hext :
          zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
              (s := s) (m := m) (hcap i) nodes u0 u1 theta ∈ W :=
        zeroExtend_mem_embeddedKernelFamilySum D w0 Lmax s m nodes u0 u1
          cap hcap i theta
      have hdiv := hall ⟨_, mem_adjoinFixedArray_of_mem g W hext⟩
      simpa only [zeroExtendConstraintKernelToArray_apply,
        reconstruct_zeroExtendTotal] using hdiv
  · rintro ⟨hfixed, hfamily⟩ v
    let Div := reconstructedMultipleSubmodule (K := K)
      (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F
    have hfixedSpan : K ∙ g ≤ Div := by
      apply Submodule.span_le.mpr
      intro q hq
      have hqg : q = g := Set.mem_singleton_iff.mp hq
      subst q
      exact (mem_reconstructedMultipleSubmodule_iff
        (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F g).mpr hfixed
    have hfamilySum : W ≤ Div := by
      apply iSup_le
      intro i
      rintro q ⟨theta, rfl⟩
      apply (mem_reconstructedMultipleSubmodule_iff
        (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F _).mpr
      rw [zeroExtendConstraintKernelToArray_apply,
        reconstruct_zeroExtendTotal]
      exact hfamily i theta
    have hvDiv : (v : CoefficientIndex D w0 Lmax s → K) ∈ Div :=
      (sup_le hfixedSpan hfamilySum) v.2
    exact (mem_reconstructedMultipleSubmodule_iff
      (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F v).mp hvDiv

section SelectedSubspaces

 


def embeddedSelectedKernelFamilySum
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1))) :
    Submodule K (CoefficientIndex D w0 Lmax s → K) :=
  ⨆ i, LinearMap.range
    ((zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
      (s := s) (m := m) (hcap i) nodes u0 u1).comp (Selected i).subtype)

theorem selected_zeroExtend_mem_familySum
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (i : ι) (theta : Selected i) :
    zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
        (s := s) (m := m) (hcap i) nodes u0 u1 theta.1 ∈
      embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
        cap hcap Selected := by
  exact (le_iSup (fun j ↦ LinearMap.range
    ((zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
      (s := s) (m := m) (hcap j) nodes u0 u1).comp
        (Selected j).subtype)) i) ⟨theta, rfl⟩

 


theorem dvd_commonGCDAtMax_adjoinedSelectedFamily_iff
    (D w0 Lmax s m : Nat) (nodes u0 u1 : I → K)
    (cap : ι → Nat) (hcap : ∀ i, cap i ≤ Lmax)
    (Selected : ∀ i, Submodule K
      (LinearMap.ker (constraintMap K D w0 (cap i) s m nodes u0 u1)))
    (g : CoefficientIndex D w0 Lmax s → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K
      (adjoinFixedArray g
        (embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
          cap hcap Selected)))
    (F : Poly4 K) :
    F ∣ commonGCDAtMax
        (adjoinFixedArray g
          (embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
            cap hcap Selected)) b ↔
      F ∣ reconstruct K D w0 Lmax s g ∧
        ∀ (i : ι) (theta : Selected i),
          F ∣ reconstruct K D w0 (cap i) s theta.1.1 := by
  let W := embeddedSelectedKernelFamilySum D w0 Lmax s m nodes u0 u1
    cap hcap Selected
  rw [dvd_commonGCDAtMax_iff]
  constructor
  · intro hall
    constructor
    · exact hall ⟨g, fixed_mem_adjoinFixedArray g W⟩
    · intro i theta
      have hext :
          zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
              (s := s) (m := m) (hcap i) nodes u0 u1 theta.1 ∈ W :=
        selected_zeroExtend_mem_familySum D w0 Lmax s m nodes u0 u1
          cap hcap Selected i theta
      have hdiv := hall ⟨_, mem_adjoinFixedArray_of_mem g W hext⟩
      simpa only [zeroExtendConstraintKernelToArray_apply,
        reconstruct_zeroExtendTotal] using hdiv
  · rintro ⟨hfixed, hfamily⟩ v
    let Div := reconstructedMultipleSubmodule (K := K)
      (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F
    have hfixedSpan : K ∙ g ≤ Div := by
      apply Submodule.span_le.mpr
      intro q hq
      have hqg : q = g := Set.mem_singleton_iff.mp hq
      subst q
      exact (mem_reconstructedMultipleSubmodule_iff
        (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F g).mpr hfixed
    have hfamilySum : W ≤ Div := by
      apply iSup_le
      intro i
      rintro q ⟨theta, rfl⟩
      apply (mem_reconstructedMultipleSubmodule_iff
        (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F _).mpr
      change F ∣ reconstruct K D w0 Lmax s
        (zeroExtendConstraintKernelToArray (K := K) (D := D) (w := w0)
          (s := s) (m := m) (hcap i) nodes u0 u1 theta.1)
      rw [zeroExtendConstraintKernelToArray_apply,
        reconstruct_zeroExtendTotal]
      exact hfamily i theta
    have hvDiv : (v : CoefficientIndex D w0 Lmax s → K) ∈ Div :=
      (sup_le hfixedSpan hfamilySum) v.2
    exact (mem_reconstructedMultipleSubmodule_iff
      (K := K) (D := D) (w0 := w0) (Lmax := Lmax) (s := s) F v).mp hvDiv

end SelectedSubspaces

end

end ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research.commonGCDAtMax_ne_zero
#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research.dvd_commonGCDAtMax_adjoinedFamily_iff
#print axioms ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research.dvd_commonGCDAtMax_adjoinedSelectedFamily_iff
