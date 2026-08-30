import ProximityPrize.SubmissionLower.TwoKernelCaps
import ProximityPrize.SubmissionLower.RegularColonTopSlice
import ProximityPrize.SubmissionLower.RegularColonMass
/-!
Regular-colon exclusion from the whole A-kernel, contact-order residual
mass, and the slope-free quotient projection. The actual quotient degree
differences are retained until the final coordinate bound.

The final theorem assumes an actual full A-kernel divisor, full slope
degree, a regular polynomial solution, its degree bound, and A agreements.
No quotient dimension, local-root, or residual-mass bound is assumed.
-/
namespace ProximityPrize.SubmissionLower.RegularColonExclusion
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN100 RCN119
open RCN180 RCN081
open RCN234 RCN156
open RCN130 RCN286
open TwoKernelSelection ContactOrderBridge RegularColonTopSlice RegularColonMass
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

section Extension
variable {E J : Type*} [Zero E]

/-- Extend received data from distinct node indices to all field elements. -/
def extendEmbedding (x : J ↪ E) (u : J → E) (t : E) : E := by
  classical
  letI : Decidable (∃ i, x i = t) := Classical.propDecidable _
  exact if h : ∃ i, x i = t then u (Classical.choose h) else 0

theorem extendEmbedding_apply (x : J ↪ E) (u : J → E) (i : J) :
    extendEmbedding x u (x i) = u i := by
  classical
  letI : Decidable (∃ j, x j = x i) := Classical.propDecidable _
  have h : ∃ j, x j = x i := ⟨i, rfl⟩
  simp only [extendEmbedding, dif_pos h]
  exact congrArg u (x.injective (Classical.choose_spec h))

end Extension

theorem residualS_eq_degreeR (F : P4) :
    wt residualSWeights F = F.degreeOf (2 : Fin 4) := by
  change F.support.sup (Finsupp.weight residualSWeights) = F.degreeOf (2 : Fin 4)
  rw [MvPolynomial.degreeOf_eq_sup]
  apply congrArg (fun f : (Fin 4 →₀ ℕ) → ℕ => F.support.sup f)
  funext d
  rw [weight_fin4]
  simp [residualSWeights]

theorem full_A_divisor_mem_box (u0 u1 : I → K) (F : P4)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 7645344 131071 240000 12 v.1) :
    F ∈ globalCoefficientBox K 7645344 131071 240000 12 := by
  classical
  have hExists := RCN100.exists_nonzero_kernel_array (I := I)
    K 7645344 131071 240000 12 42 IRSProfile.domain u0 u1 TwoKernelSelection.gateA
  obtain ⟨a, ha, hk⟩ := hExists
  let v : AKernel u0 u1 := ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct K 7645344 131071 240000 12 a ≠ 0 :=
    reconstruct_ne_zero K 7645344 131071 240000 12 a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F
    (reconstruct K 7645344 131071 240000 12 a)
    7645344 131071 240000 12 hQ (hdiv v)
    (reconstruct_mem_globalCoefficientBox K 7645344 131071 240000 12 a)

/-- The 67.35 regular-colon exclusion for a divisor of the whole A-kernel. -/
theorem full_slope_regular_factor_ys_le
    (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 7645344 131071 240000 12 v.1)
    (hR : F.degreeOf (2 : Fin 4) = 12)
    (P : Polynomial K) (gamma : K) (selected : Finset I)
    (hP : P.natDegree ≤ 131071) (hA : 182032 ≤ selected.card)
    (hvalues : ∀ i ∈ selected,
      P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
    (hregular : RegularSolution F P gamma) :
    wt residualYSWeights F ≤ 53 := by
  classical
  by_contra hnot
  have hYS : 54 ≤ wt residualYSWeights F := by omega
  have hRwt : wt residualSWeights F = 12 := (residualS_eq_degreeR F).trans hR
  have hbox := full_A_divisor_mem_box u0 u1 F hdiv
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    7645344 131071 240000 12 (by decide)).mp hbox
  have hcw := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 7077822 ≤ wt (contactWeights 131071) F := by omega
  have ht : 54 ≤ wt residualTotalWeights F :=
    hYS.trans (residual_weight_nested F).2

  /- Keep both actual degree differences. Using their upper bounds before
     the mass inequality would silently strengthen that inequality. -/
  let Dq : ℕ := 7645344 - wt (contactWeights 131071) F
  let Lq : ℕ := 240000 - wt residualTotalWeights F
  have hDq : Dq ≤ 567522 := by dsimp [Dq]; omega
  have hLq : Lq ≤ 239946 := by dsimp [Lq]; omega

  let u0e : K → K := extendEmbedding IRSProfile.domain u0
  let u1e : K → K := extendEmbedding IRSProfile.domain u1
  let points : Finset K := (Finset.univ : Finset I).image IRSProfile.domain
  let agreements : Finset K := selected.image IRSProfile.domain
  let mu : K → ℕ := fun x =>
    42 - contactOrder K x (u0e x) (u1e x) F
  have hpoints : points.card = 262144 := by
    change ((Finset.univ : Finset I).image IRSProfile.domain).card = _
    rw [Finset.card_image_of_injective _ IRSProfile.domain.injective, Finset.card_univ]
    norm_num [I, IRSProfile.Index]
  have hsub : agreements ⊆ points :=
    Finset.image_subset_image (Finset.subset_univ selected)
  have hAc : 182032 ≤ agreements.card := by
    change 182032 ≤ (selected.image IRSProfile.domain).card
    rw [Finset.card_image_of_injective _ IRSProfile.domain.injective]
    exact hA
  have hv : ∀ x ∈ agreements, P.eval x = u0e x + gamma * u1e x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simpa only [u0e, u1e, extendEmbedding_apply] using hvalues i hi
  have hreg : RCN122.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 := by
    change RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0
    exact hregular.2
  have hmass : Dq ≤
      RegularColonQuotientProjection.residualMass points mu 0 + 50962 := by
    have h := irs_mass_on_points points agreements u0e u1e F P gamma
      hsub hAc hP hv hreg
    simpa only [Dq, mu, RegularColonQuotientProjection.residualMass,
      Nat.sub_zero, wt] using h

  let U := AKernel u0 u1
  have hdivK : ∀ v : AKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        7645344 131071 240000 12 42 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  let recon : U →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) 7645344 131071 240000 12 42 IRSProfile.domain u0 u1
  let q : U →ₗ[K] P4 := quotientLinear recon F hF hdivK
  have hqbox : ∀ v : U, q v ∈ globalCoefficientBox K Dq 131071 Lq 0 := by
    have h := TwoKernelCaps.quotient_box_of_full_divisor
      7645344 131071 240000 12 42
      (wt (contactWeights 131071) F) (wt residualTotalWeights F) 12
      IRSProfile.domain u0 u1 F hF hdivK (le_refl _) (le_refl _) (by omega)
    intro v
    simpa only [q, recon, Dq, Lq, quotientLinear,
      LinearMap.coe_mk, AddHom.coe_mk, Nat.sub_self] using h v
  have hqinjective : Function.Injective q :=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K := K)
        7645344 131071 240000 12 42 IRSProfile.domain u0 u1) F hF hdivK
  have hqcontact : ∀ v : U, ∀ i : I,
      ContactAtLeast K (IRSProfile.domain i) (u0 i) (u1 i)
        (42 - contactOrder K (IRSProfile.domain i) (u0 i) (u1 i) F) (q v) := by
    intro v i
    have hk := contactAtLeast_of_mem_kernel K
      7645344 131071 240000 12 42 IRSProfile.domain u0 u1 v.1 v.2 i
    have heq : reconstruct K 7645344 131071 240000 12 v.1 = F * q v := by
      have h := recon_eq_mul_quotientPolynomial
        (kernelReconstructLinear (K := K)
          7645344 131071 240000 12 42 IRSProfile.domain u0 u1) F hdivK v
      simpa only [kernelReconstructLinear_apply, q, recon, quotientLinear,
        LinearMap.coe_mk, AddHom.coe_mk] using h
    exact (contact_colon_iff K (IRSProfile.domain i) (u0 i) (u1 i)
      42 F (q v) hF).mp (by simpa only [heq] using hk)

  /- Transfer the entire quotient image, not just one chosen interpolant,
     to C1 coefficient arrays by the existing box equivalence. -/
  let qb : U →ₗ[K] globalCoefficientBox K Dq 131071 Lq 0 :=
    LinearMap.codRestrict (globalCoefficientBox K Dq 131071 Lq 0) q hqbox
  let e := reconstructBoxEquiv (K := K) Dq 131071 Lq 0
  let enc : U →ₗ[K] (CoefficientIndex Dq 131071 Lq 0 → K) :=
    e.symm.toLinearMap.comp qb
  let W : Submodule K (CoefficientIndex Dq 131071 Lq 0 → K) := enc.range
  have henc : Function.Injective enc := by
    intro a b hab
    have hqb : qb a = qb b := e.symm.injective hab
    apply hqinjective
    simpa only [qb, LinearMap.codRestrict_apply] using congrArg Subtype.val hqb
  have hencode : ∀ v : U, reconstruct K Dq 131071 Lq 0 (enc v) = q v := by
    intro v
    exact congrArg Subtype.val (e.apply_symm_apply (qb v))
  have hWcontact : ∀ a : W, ∀ x ∈ points,
      ContactAtLeast K x (u0e x) (u1e x) (mu x)
        (reconstruct K Dq 131071 Lq 0 a.1) := by
    intro a x hx
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp a.2
    rw [← hv, hencode v]
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [mu, u0e, u1e, extendEmbedding_apply] using hqcontact v i
  have hroots := lowTopRootDivisibility_of_contact W points mu u0e u1e hWcontact
  have hupper := RegularColonQuotientProjection.finrank_le_candidate
    W points mu hroots hpoints hmass hDq hLq
  have hrank : Module.finrank K W = Module.finrank K U := enc.finrank_range_of_inj henc
  rw [hrank] at hupper
  have hlower := constraintKernel_finrank_lower_bound (K := K)
    7645344 131071 240000 12 42 IRSProfile.domain u0 u1
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    RegularColonArithmetic.kernelA_nullity] at hlower
  change 181392944031 ≤ Module.finrank K U at hlower
  omega

end
end ProximityPrize.SubmissionLower.RegularColonExclusion
