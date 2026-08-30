import ProximityPrize.SubmissionLower.L1

/-!
A multi-R-layer coefficient collar for a whole interpolation kernel.

Research source only: this file is outside the 67.36 submission tree and has
not been compiled. All maps below use the original C1 coefficient index.
The algebraic assertion excluding a low weighted prefix is an explicit input;
no irreducibility or derivative assertion is proved or presumed here.

Only L1 is imported. It supplies the reconstruction equivalence, the linear
quotient and the generic quotient-box theorem without importing the later
fixed numerical collar or two-kernel selection modules.
-/
namespace ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient

open scoped BigOperators
open RCN081 RCN100 RCN156 RCN180 RCN234

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq _

abbrev Index (D w L q : ℕ) := CoefficientIndex D w L q

theorem index_ext {D w L q : ℕ} {a b : Index D w L q}
    (hy : a.1.val = b.1.val)
    (hr : a.2.1.val = b.2.1.val)
    (hz : a.2.2.1.val = b.2.2.1.val)
    (hx : a.2.2.2.val = b.2.2.2.val) : a = b := by
  rcases a with ⟨⟨ay, hay⟩, ⟨⟨ar, har⟩, ⟨⟨az, haz⟩, ⟨ax, hax⟩⟩⟩⟩
  rcases b with ⟨⟨byVal, hby⟩, ⟨⟨br, hbr⟩, ⟨⟨bz, hbz⟩, ⟨bx, hbx⟩⟩⟩⟩
  change ay = byVal at hy
  change ar = br at hr
  change az = bz at hz
  change ax = bx at hx
  subst byVal
  subst br
  subst bz
  subst bx
  rfl

/-- The discarded X prefix in the joint Y/R layer (j,r). -/
def collarCut (D w c j r : ℕ) : ℕ :=
  D - c - w * j - (w - 1) * r

theorem collar_width (D w c j r : ℕ) :
    D - w * j - (w - 1) * r - collarCut D w c j r =
      min c (D - w * j - (w - 1) * r) := by
  unfold collarCut
  omega

/-- All four C1 coordinates are retained. Only the last width is shortened,
and its X value is stored as an offset from the lower endpoint. -/
abbrev RetainedIndex (D w L q c : ℕ) :=
  (j : Fin (L + 1)) × (r : Fin (q + 1)) ×
    (Fin (L + 1 - j.val - r.val) ×
      Fin (D - w * j.val - (w - 1) * r.val -
        collarCut D w c j.val r.val))

theorem retainedIndex_ext {D w L q c : ℕ}
    {a b : RetainedIndex D w L q c}
    (hy : a.1.val = b.1.val)
    (hr : a.2.1.val = b.2.1.val)
    (hz : a.2.2.1.val = b.2.2.1.val)
    (hx : a.2.2.2.val = b.2.2.2.val) : a = b := by
  rcases a with ⟨⟨ay, hay⟩, ⟨⟨ar, har⟩, ⟨⟨az, haz⟩, ⟨ax, hax⟩⟩⟩⟩
  rcases b with ⟨⟨byVal, hby⟩, ⟨⟨br, hbr⟩, ⟨⟨bz, hbz⟩, ⟨bx, hbx⟩⟩⟩⟩
  change ay = byVal at hy
  change ar = br at hr
  change az = bz at hz
  change ax = bx at hx
  subst byVal
  subst br
  subst bz
  subst bx
  rfl

def retainedColumn {D w L q : ℕ} (c : ℕ)
    (a : RetainedIndex D w L q c) : Index D w L q :=
  ⟨a.1, ⟨a.2.1, ⟨a.2.2.1,
    ⟨collarCut D w c a.1.val a.2.1.val + a.2.2.2.val, by
      have h := a.2.2.2.isLt
      change collarCut D w c a.1.val a.2.1.val + a.2.2.2.val <
        D - w * a.1.val - (w - 1) * a.2.1.val
      omega⟩⟩⟩⟩

theorem retainedColumn_injective {D w L q : ℕ} (c : ℕ) :
    Function.Injective (retainedColumn (D := D) (w := w) (L := L) (q := q) c) := by
  intro a b hab
  have hy : a.1.val = b.1.val :=
    congrArg (fun e : Index D w L q => e.1.val) hab
  have hr : a.2.1.val = b.2.1.val :=
    congrArg (fun e : Index D w L q => e.2.1.val) hab
  have hz : a.2.2.1.val = b.2.2.1.val :=
    congrArg (fun e : Index D w L q => e.2.2.1.val) hab
  apply retainedIndex_ext hy hr hz
  have hx := congrArg (fun e : Index D w L q => e.2.2.2.val) hab
  change collarCut D w c a.1.val a.2.1.val + a.2.2.2.val =
    collarCut D w c b.1.val b.2.1.val + b.2.2.2.val at hx
  have hcut : collarCut D w c a.1.val a.2.1.val =
      collarCut D w c b.1.val b.2.1.val :=
    (congrArg (fun j : ℕ => collarCut D w c j a.2.1.val) hy).trans
      (congrArg (collarCut D w c b.1.val) hr)
  have hsum : collarCut D w c b.1.val b.2.1.val + a.2.2.2.val =
      collarCut D w c b.1.val b.2.1.val + b.2.2.2.val :=
    (congrArg (fun cut : ℕ => cut + a.2.2.2.val) hcut).symm.trans hx
  exact Nat.add_left_cancel hsum

theorem retainedColumn_preimage {D w L q : ℕ} (c : ℕ)
    (a : Index D w L q)
    (ha : collarCut D w c a.1.val a.2.1.val ≤ a.2.2.2.val) :
    ∃ b : RetainedIndex D w L q c, retainedColumn c b = a := by
  let b : RetainedIndex D w L q c :=
    ⟨a.1, ⟨a.2.1, ⟨a.2.2.1,
      ⟨a.2.2.2.val - collarCut D w c a.1.val a.2.1.val, by
        have h := a.2.2.2.isLt
        omega⟩⟩⟩⟩
  refine ⟨b, ?_⟩
  apply index_ext
  · rfl
  · rfl
  · rfl
  · change collarCut D w c a.1.val a.2.1.val +
      (a.2.2.2.val - collarCut D w c a.1.val a.2.1.val) = a.2.2.2.val
    omega

def coefficientProjection {D w L q : ℕ}
    (V : Submodule K (Index D w L q → K)) (c : ℕ) :
    V →ₗ[K] (RetainedIndex D w L q c → K) where
  toFun a b := a.1 (retainedColumn c b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero retained coordinates force the original reconstruction into the
weighted prefix D-c, with unchanged total and R bounds. This includes all
truncated or empty width cases. -/
theorem reconstruct_mem_prefix_of_retained_zero
    {D w L q c : ℕ} (a : Index D w L q → K)
    (hkept : ∀ b : Index D w L q,
      collarCut D w c b.1.val b.2.1.val ≤ b.2.2.2.val → a b = 0) :
    reconstruct K D w L q a ∈ globalCoefficientBox K (D - c) w L q := by
  classical
  unfold reconstruct
  apply Submodule.sum_mem
  intro b _
  apply (MvPolynomial.monomial_mem_restrictSupport (R := K)).mpr
  by_cases hb : a b = 0
  · exact Or.inr hb
  · left
    have hr := b.2.1.isLt
    have hz := b.2.2.1.isLt
    have hx : b.2.2.2.val < collarCut D w c b.1.val b.2.1.val := by
      by_contra hnot
      exact hb (hkept b (Nat.le_of_not_gt hnot))
    unfold collarCut at hx
    simp only [globalExponents, Set.mem_setOf_eq, columnExponent_x,
      columnExponent_y, columnExponent_r, columnExponent_z]
    omega

theorem collarProjection_injective {D w L q : ℕ}
    (V : Submodule K (Index D w L q → K)) (c : ℕ)
    (hprefix : ∀ a : V,
      reconstruct K D w L q a.1 ∈ globalCoefficientBox K (D - c) w L q → a = 0) :
    Function.Injective (coefficientProjection V c) := by
  intro a b hab
  have hd : coefficientProjection V c (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  apply sub_eq_zero.mp
  apply hprefix (a - b)
  apply reconstruct_mem_prefix_of_retained_zero
  intro e he
  obtain ⟨f, hfe⟩ := retainedColumn_preimage c e he
  have hh := congrFun hd f
  change (a - b).1 (retainedColumn c f) = 0 at hh
  simpa only [hfe] using hh

theorem finrank_le_collar_card {D w L q : ℕ}
    (V : Submodule K (Index D w L q → K)) (c : ℕ)
    (hprefix : ∀ a : V,
      reconstruct K D w L q a.1 ∈ globalCoefficientBox K (D - c) w L q → a = 0) :
    Module.finrank K V ≤ Fintype.card (RetainedIndex D w L q c) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (collarProjection_injective V c hprefix)
  simpa only [Module.finrank_fintype_fun_eq_card] using h

theorem retainedIndex_card (D w L q c : ℕ) :
    Fintype.card (RetainedIndex D w L q c) =
      ∑ j ∈ Finset.range (L + 1), ∑ r ∈ Finset.range (q + 1),
        (L + 1 - j - r) *
          (D - w * j - (w - 1) * r - collarCut D w c j r) := by
  simp [RetainedIndex, Fintype.card_sigma, Finset.sum_range]

theorem retainedIndex_card_min (D w L q c : ℕ) :
    Fintype.card (RetainedIndex D w L q c) =
      ∑ j ∈ Finset.range (L + 1), ∑ r ∈ Finset.range (q + 1),
        (L + 1 - j - r) * min c (D - w * j - (w - 1) * r) := by
  rw [retainedIndex_card]
  simp only [collar_width]

/-- Exact quotient caps, including the zero quotient, from L1's generic
product-degree lemma. No fixed numerical two-kernel module is needed. -/
theorem quotient_mem_actual_box
    (Q F P : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hF : F ≠ 0) (hbox : Q ∈ globalCoefficientBox K D w L s)
    (heq : Q = F * P) :
    P ∈ globalCoefficientBox K (D - wt (contactWeights w) F) w
      (L - wt residualTotalWeights F) (s - wt residualSWeights F) := by
  classical
  by_cases hP : P = 0
  · subst P
    exact (globalCoefficientBox K _ _ _ _).zero_mem
  · have hQ : Q ≠ 0 := by
      rw [heq]
      exact mul_ne_zero hF hP
    exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      Q F P D w L s (wt (contactWeights w) F)
      (wt residualTotalWeights F) (wt residualSWeights F)
      hQ hF hP hbox heq (le_refl _) (le_refl _) (le_refl _)

section WholeKernel

variable {I : Type*} [Fintype I]

/-- The full kernel rank bound at the actual three quotient caps.
The low-prefix exclusion is supplied by a separate algebraic theorem. -/
theorem whole_kernel_finrank_le_collar
    (D w L s m c : ℕ) (nodes u0 u1 : I → K)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hzero : ∀ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
      (P : MvPolynomial (Fin 4) K),
      reconstruct K D w L s v.1 = F * P →
      P ∈ globalCoefficientBox K (D - wt (contactWeights w) F - c) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P = 0) :
    Module.finrank K (ConstraintKernel (K := K) D w L s m nodes u0 u1) ≤
      Fintype.card (RetainedIndex (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) c) := by
  classical
  let Dq := D - wt (contactWeights w) F
  let Lq := L - wt residualTotalWeights F
  let qcap := s - wt residualSWeights F
  let U := ConstraintKernel (K := K) D w L s m nodes u0 u1
  have hdivK : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ kernelReconstructLinear (K := K) D w L s m nodes u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  let recon : U →ₗ[K] MvPolynomial (Fin 4) K :=
    kernelReconstructLinear (K := K) D w L s m nodes u0 u1
  let quot : U →ₗ[K] MvPolynomial (Fin 4) K := quotientLinear recon F hF hdivK
  have hprod : ∀ v : U, reconstruct K D w L s v.1 = F * quot v := by
    intro v
    have h := recon_eq_mul_quotientPolynomial
      (kernelReconstructLinear (K := K) D w L s m nodes u0 u1) F hdivK v
    simpa only [kernelReconstructLinear_apply, quot, recon, quotientLinear,
      LinearMap.coe_mk, AddHom.coe_mk] using h
  have hqbox : ∀ v : U, quot v ∈ globalCoefficientBox K Dq w Lq qcap := by
    intro v
    exact quotient_mem_actual_box (reconstruct K D w L s v.1) F (quot v)
      D w L s hF (reconstruct_mem_globalCoefficientBox K D w L s v.1) (hprod v)
  have hqinjective : Function.Injective quot :=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K := K) D w L s m nodes u0 u1)
      F hF hdivK
  let qb : U →ₗ[K] globalCoefficientBox K Dq w Lq qcap :=
    LinearMap.codRestrict (globalCoefficientBox K Dq w Lq qcap) quot hqbox
  let e := reconstructBoxEquiv (K := K) Dq w Lq qcap
  let enc : U →ₗ[K] (Index Dq w Lq qcap → K) := e.symm.toLinearMap.comp qb
  let V : Submodule K (Index Dq w Lq qcap → K) := enc.range
  have henc : Function.Injective enc := by
    intro a b hab
    have hqb : qb a = qb b := e.symm.injective hab
    apply hqinjective
    simpa only [qb, LinearMap.codRestrict_apply] using congrArg Subtype.val hqb
  have hencode : ∀ v : U, reconstruct K Dq w Lq qcap (enc v) = quot v := by
    intro v
    exact congrArg Subtype.val (e.apply_symm_apply (qb v))
  have hprefix : ∀ a : V,
      reconstruct K Dq w Lq qcap a.1 ∈ globalCoefficientBox K (Dq - c) w Lq qcap →
        a = 0 := by
    intro a ha
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp a.2
    have hlow : quot v ∈ globalCoefficientBox K (Dq - c) w Lq qcap := by
      simpa only [← hv, hencode v] using ha
    have hz : quot v = 0 := hzero v (quot v) (hprod v) hlow
    apply Subtype.ext
    apply reconstruct_injective K Dq w Lq qcap
    simpa only [← hv, hencode v, ZeroMemClass.coe_zero, reconstruct_zero] using hz
  have hupper := finrank_le_collar_card V c hprefix
  have hrank : Module.finrank K V = Module.finrank K U :=
    enc.finrank_range_of_inj henc
  rw [hrank] at hupper
  exact hupper

end WholeKernel

/-- A small explicit target index. Its number of Y layers is J rather than
the potentially huge actual total-degree bound L+1. -/
abbrev CandidateIndex (Dcap w Lcap qcap c J : ℕ) :=
  (j : Fin J) × (r : Fin (qcap + 1)) ×
    (Fin (Lcap + 1 - j.val - r.val) ×
      Fin (min c (Dcap - w * j.val - (w - 1) * r.val)))

theorem retained_width_le_candidate {D Dcap w c : ℕ}
    (hD : D ≤ Dcap) (j r : ℕ) :
    D - w * j - (w - 1) * r - collarCut D w c j r ≤
      min c (Dcap - w * j - (w - 1) * r) := by
  rw [collar_width]
  omega

/-- A positive retained X width forces j<J. No extra w>0 hypothesis is
needed: when w=0 the assumed cap makes the source index empty. -/
theorem retainedIndex_y_lt {D Dcap w L q c J : ℕ}
    (hD : D ≤ Dcap) (hJ : Dcap ≤ w * J)
    (a : RetainedIndex D w L q c) : a.1.val < J := by
  by_contra hnot
  have hj : J ≤ a.1.val := Nat.le_of_not_gt hnot
  have hmul : w * J ≤ w * a.1.val := Nat.mul_le_mul_left w hj
  have hx := a.2.2.2.isLt
  omega

def candidateIndexMap {D Dcap w L Lcap q qcap c J : ℕ}
    (hD : D ≤ Dcap) (hL : L ≤ Lcap) (hq : q ≤ qcap)
    (hJ : Dcap ≤ w * J) (a : RetainedIndex D w L q c) :
    CandidateIndex Dcap w Lcap qcap c J :=
  ⟨⟨a.1.val, retainedIndex_y_lt hD hJ a⟩,
    ⟨⟨a.2.1.val, a.2.1.isLt.trans_le (Nat.add_le_add_right hq 1)⟩,
      ⟨⟨a.2.2.1.val, by
        have hLength : L + 1 ≤ Lcap + 1 := Nat.add_le_add_right hL 1
        exact a.2.2.1.isLt.trans_le
          (Nat.sub_le_sub_right (Nat.sub_le_sub_right hLength a.1.val) a.2.1.val)⟩,
        ⟨a.2.2.2.val, a.2.2.2.isLt.trans_le
          (retained_width_le_candidate hD a.1.val a.2.1.val)⟩⟩⟩⟩

theorem candidateIndexMap_injective {D Dcap w L Lcap q qcap c J : ℕ}
    (hD : D ≤ Dcap) (hL : L ≤ Lcap) (hq : q ≤ qcap)
    (hJ : Dcap ≤ w * J) :
    Function.Injective (candidateIndexMap (c := c) hD hL hq hJ) := by
  intro a b hab
  apply retainedIndex_ext
  · exact congrArg (fun e : CandidateIndex Dcap w Lcap qcap c J => e.1.val) hab
  · exact congrArg (fun e : CandidateIndex Dcap w Lcap qcap c J => e.2.1.val) hab
  · exact congrArg (fun e : CandidateIndex Dcap w Lcap qcap c J => e.2.2.1.val) hab
  · exact congrArg (fun e : CandidateIndex Dcap w Lcap qcap c J => e.2.2.2.val) hab

theorem candidateIndex_card (Dcap w Lcap qcap c J : ℕ) :
    Fintype.card (CandidateIndex Dcap w Lcap qcap c J) =
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
        (Lcap + 1 - j - r) * min c (Dcap - w * j - (w - 1) * r) := by
  simp [CandidateIndex, Fintype.card_sigma, Finset.sum_range]

theorem collar_card_le_candidate_card {D Dcap w L Lcap q qcap c J : ℕ}
    (hD : D ≤ Dcap) (hL : L ≤ Lcap) (hq : q ≤ qcap)
    (hJ : Dcap ≤ w * J) :
    Fintype.card (RetainedIndex D w L q c) ≤
      Fintype.card (CandidateIndex Dcap w Lcap qcap c J) :=
  Fintype.card_le_of_injective (candidateIndexMap (c := c) hD hL hq hJ)
    (candidateIndexMap_injective hD hL hq hJ)

theorem collar_card_le_small_sum {D Dcap w L Lcap q qcap c J : ℕ}
    (hD : D ≤ Dcap) (hL : L ≤ Lcap) (hq : q ≤ qcap)
    (hJ : Dcap ≤ w * J) :
    Fintype.card (RetainedIndex D w L q c) ≤
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
        (Lcap + 1 - j - r) * min c (Dcap - w * j - (w - 1) * r) := by
  rw [← candidateIndex_card]
  exact collar_card_le_candidate_card hD hL hq hJ

section WholeKernel

variable {I : Type*} [Fintype I]

/-- The complete symbolic handoff to a numerical certificate. Only the small
J-by-(qcap+1) sum needs later evaluation; actual Dq,Lq,q are not replaced
until the injective coordinate embedding. -/
theorem whole_kernel_finrank_le_small_sum
    (D w L s m c : ℕ) (nodes u0 u1 : I → K)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hzero : ∀ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
      (P : MvPolynomial (Fin 4) K),
      reconstruct K D w L s v.1 = F * P →
      P ∈ globalCoefficientBox K (D - wt (contactWeights w) F - c) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) →
      P = 0)
    (Dcap Lcap qcap J : ℕ)
    (hD : D - wt (contactWeights w) F ≤ Dcap)
    (hL : L - wt residualTotalWeights F ≤ Lcap)
    (hq : s - wt residualSWeights F ≤ qcap)
    (hJ : Dcap ≤ w * J) :
    Module.finrank K (ConstraintKernel (K := K) D w L s m nodes u0 u1) ≤
      ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range (qcap + 1),
        (Lcap + 1 - j - r) * min c (Dcap - w * j - (w - 1) * r) := by
  exact (whole_kernel_finrank_le_collar D w L s m c nodes u0 u1 F hF hdiv hzero).trans
    (collar_card_le_small_sum hD hL hq hJ)

end WholeKernel

end
end ProximityPrize.SubmissionLower.LocatorMultiSlopeQuotient
