import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.I
namespace ProximityPrize.SubmissionLower.ContactRegularZeroBudget6676Research
open scoped Classical
open ContactResidualSparseComponentAdapterResearch
open ContactFlagAffineResidualAutomorphismResearch
open ContactIdentityResidualPrimeTransportResearch
open ContactIdentityResidualZeroBudgetTransportResearch
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Ring3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
private theorem eval_eq_of_sub_mem (P:Ideal (Ring3 K))
   {A B:Ring3 K} (h:A-B∈P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom):
   MvPolynomial.aeval v A=MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A-B)=0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
def FiniteRegularZeroSetBound (P:Ideal (Ring3 K)) (H A:Ring3 K)
   (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → K),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v H≠0) →
   (∀ v∈points,MvPolynomial.aeval v A=0) → points.card ≤ cost
theorem FiniteRegularZeroSetBound.of_all_points
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteZeroSetBound P A cost):FiniteRegularZeroSetBound P H A cost:=by
 intro points hP _ hA
 exact h points hP hA
theorem FiniteRegularZeroSetBound.mono
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost cost':ℕ}
   (h:FiniteRegularZeroSetBound P H A cost) (hle:cost ≤ cost'):
   FiniteRegularZeroSetBound P H A cost':=by
 intro points hP hH hA
 exact (h points hP hH hA).trans hle
theorem FiniteRegularZeroSetBound.of_sub_mem
   {P:Ideal (Ring3 K)} {H A B:Ring3 K} {cost:ℕ}
   (hAB:A-B∈P) (h:FiniteRegularZeroSetBound P H B cost):
   FiniteRegularZeroSetBound P H A cost:=by
 intro points hP hH hA
 apply h points hP hH
 intro v hv
 rw [←eval_eq_of_sub_mem P hAB v (hP v hv)]
 exact hA v hv
theorem FiniteRegularZeroSetBound.regularity_congr
   {P:Ideal (Ring3 K)} {H H' A:Ring3 K} {cost:ℕ}
   (hHH':H-H'∈P) (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound P H' A cost:=by
 intro points hP hH' hA
 apply h points hP _ hA
 intro v hv
 rw [eval_eq_of_sub_mem P hHH' v (hP v hv)]
 exact hH' v hv
theorem FiniteRegularZeroSetBound.regularity_dvd
   {P:Ideal (Ring3 K)} {H H' A:Ring3 K} {cost:ℕ}
   (hdiv:H∣H') (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound P H' A cost:=by
 obtain ⟨B,rfl⟩:=hdiv
 intro points hP hHB hA
 apply h points hP _ hA
 intro v hv hzero
 apply hHB v hv
 simp only [map_mul,hzero,zero_mul]
theorem FiniteRegularZeroSetBound.map_residual
   (aY v bY aS bS cS:K) (hv:v≠0)
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     (residualAlgHom aY v bY aS bS cS H)
     (residualAlgHom aY v bY aS bS cS A) cost:=by
 classical
 intro points hP hH hA
 let forward:=forwardResidualPoint aY v bY aS bS cS
 let oldPoints:=points.image forward
 have hcard:oldPoints.card=points.card:=
   Finset.card_image_of_injective points
     (forwardResidualPoint_injective aY v bY aS bS cS hv)
 rw [←hcard]
 apply h oldPoints
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   exact (map_le_pointKernel_iff aY v bY aS bS cS hv P q).mp (hP q hq)
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hn:=hH q hq
   change MvPolynomial.eval q (residualEquiv aY v bY aS bS cS hv H)≠0 at hn
   change MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) H≠0
   rwa [eval_residualEquiv] at hn
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hz:=hA q hq
   change MvPolynomial.eval q (residualEquiv aY v bY aS bS cS hv A)=0 at hz
   change MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) A=0
   rwa [eval_residualEquiv] at hz
theorem FiniteRegularZeroSetBound.map_residual_of_inverse
   (aY v bY aS bS cS:K) (hv:v≠0)
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteRegularZeroSetBound P
     (originalAlgHom aY v bY aS bS cS H)
     (originalAlgHom aY v bY aS bS cS A) cost):
   FiniteRegularZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     H A cost:=by
 have ht:=h.map_residual aY v bY aS bS cS hv
 simpa only [residual_original_apply aY v bY aS bS cS hv] using ht
section Selected
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem agreement_fiber_card_le_of_regular_zero_bound
   (φ:Polynomial K →+*Ω) (P:Ideal (Ring3 Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteRegularZeroSetBound P (regularitySurface φ F)
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hcount:points.card ≤ cost:=by
   apply hzero points
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     exact hpoint γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     change MvPolynomial.eval (selectedPoint φ selected γ)
       (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
     rw [selectedPoint_evaluation]
     exact hregular γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
     exact (selected_agreement_zero_iff φ F selected p w hchar γ
       (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
end Selected
end
end ProximityPrize.SubmissionLower.ContactRegularZeroBudget6676Research
