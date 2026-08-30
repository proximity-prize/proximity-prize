import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C2
import ProximityPrize.SubmissionLower.BG
import ProximityPrize.SubmissionLower.AJ
namespace ProximityPrize.SubmissionLower.ContactKernelCommonGCDResearch
open scoped BigOperators
open ContactFlagInterpolation6641Research
open ContactFactorCaps
open ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalFlagResearch
noncomputable section
variable {K : Type*} [Field K]
abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K
def reconstructLinear (D w L s : ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K] Poly4 K where
 toFun := reconstruct K D w L s
 map_add' θ η := by
   classical
   simp [reconstruct,Finset.sum_add_distrib]
 map_smul' a θ := by
   classical
   rw [show reconstruct K D w L s (a • θ) =
       ∑ c : CoefficientIndex D w L s,
         MvPolynomial.monomial (columnExponent c) (a * θ c) by
     simp [reconstruct]]
   change (∑ c : CoefficientIndex D w L s,
     MvPolynomial.monomial (columnExponent c) (a * θ c)) =
     a • (∑ c : CoefficientIndex D w L s,
       MvPolynomial.monomial (columnExponent c) (θ c))
   rw [Finset.smul_sum]
   apply Finset.sum_congr rfl
   intro c hc
   rw [MvPolynomial.smul_monomial]
   simp [smul_eq_mul]
theorem reconstructLinear_injective (D w L s : ℕ) :
   Function.Injective (reconstructLinear (K := K) D w L s) :=
 reconstruct_injective K D w L s
def reconstructIntoBox (D w L s : ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearMap.codRestrict (globalCoefficientBox K D w L s)
   (reconstructLinear (K := K) D w L s)
   (reconstruct_mem_globalCoefficientBox K D w L s)
theorem reconstructIntoBox_injective (D w L s : ℕ) :
   Function.Injective (reconstructIntoBox (K := K) D w L s) := by
 intro θ η h
 apply reconstructLinear_injective (K := K) D w L s
 exact congrArg Subtype.val h
def columnIndexOfExponent {D w L s : ℕ} (d : Fin 4 →₀ ℕ)
   (hd : d ∈ globalExponents D w L s) : CoefficientIndex D w L s := by
 rcases hd with ⟨hL,hs,hD⟩
 have hi : d 1 < L + 1 := by omega
 have hj : d 2 < s + 1 := by omega
 have hz : d 3 < L + 1 - d 1 - d 2 := by omega
 have hx : d 0 < D - w * d 1 - (w - 1) * d 2 := by omega
 exact ⟨⟨d 1,hi⟩,⟨⟨d 2,hj⟩,⟨⟨d 3,hz⟩,⟨d 0,hx⟩⟩⟩⟩
theorem columnExponent_columnIndexOfExponent {D w L s : ℕ}
   (d : Fin 4 →₀ ℕ) (hd : d ∈ globalExponents D w L s) :
   columnExponent (columnIndexOfExponent d hd) = d := by
 rcases hd with ⟨hL,hs,hD⟩
 ext i
 fin_cases i <;> simp [columnIndexOfExponent]
def encodeBox {D w L s : ℕ} (Q : globalCoefficientBox K D w L s) :
   CoefficientIndex D w L s → K :=
 fun c ↦ MvPolynomial.coeff (columnExponent c) Q.1
theorem reconstruct_encodeBox {D w L s : ℕ}
   (Q : globalCoefficientBox K D w L s) :
   reconstruct K D w L s (encodeBox Q) = Q.1 := by
 classical
 ext d
 by_cases hd : d ∈ globalExponents D w L s
 · let c := columnIndexOfExponent d hd
   have hc : columnExponent c = d :=
     columnExponent_columnIndexOfExponent d hd
   rw [← hc,reconstruct_coeff]
   rfl
 · have hQ : MvPolynomial.coeff d Q.1 = 0 := by
     by_contra hn
     exact hd (Q.2 (MvPolynomial.mem_support_iff.mpr hn))
   have hRmem := reconstruct_mem_globalCoefficientBox K D w L s (encodeBox Q)
   have hR : MvPolynomial.coeff d
       (reconstruct K D w L s (encodeBox Q)) = 0 := by
     by_contra hn
     exact hd (hRmem (MvPolynomial.mem_support_iff.mpr hn))
   rw [hQ,hR]
theorem reconstructIntoBox_surjective (D w L s : ℕ) :
   Function.Surjective (reconstructIntoBox (K := K) D w L s) := by
 intro Q
 refine ⟨encodeBox Q,?_⟩
 apply Subtype.ext
 exact reconstruct_encodeBox Q
def reconstructBoxEquiv (D w L s : ℕ) :
   (CoefficientIndex D w L s → K) ≃ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearEquiv.ofBijective (reconstructIntoBox (K := K) D w L s)
   ⟨reconstructIntoBox_injective (K := K) D w L s,
     reconstructIntoBox_surjective (K := K) D w L s⟩
instance globalCoefficientBoxFinite (D w L s : ℕ) :
   Module.Finite K (globalCoefficientBox K D w L s) :=
 Module.Finite.of_surjective (reconstructIntoBox (K := K) D w L s)
   (reconstructIntoBox_surjective (K := K) D w L s)
theorem globalCoefficientBox_finrank (D w L s : ℕ) :
   Module.finrank K (globalCoefficientBox K D w L s) =
     coefficientCount D w L s := by
 rw [← coefficient_index_card D w L s,
   ← Module.finrank_fintype_fun_eq_card K]
 exact LinearEquiv.finrank_eq (reconstructBoxEquiv (K := K) D w L s).symm
theorem mem_flagGlobalCoefficientBox_iff (Q : Poly4 K)
   (D w L s : ℕ) (hD : 0 < D) :
   Q ∈ globalCoefficientBox K D w L s ↔
     wt residualTotalWeights Q ≤ L ∧
     wt residualSWeights Q ≤ s ∧
     wt (contactWeights w) Q ≤ D - 1 := by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff residualTotalWeights Q L).mpr
     intro d hd
     have hq := h hd
     rw [weight_fin4]
     simp [residualTotalWeights]
     exact hq.1
   · apply (weightedTotalDegree_le_iff residualSWeights Q s).mpr
     intro d hd
     have hq := h hd
     rw [weight_fin4]
     simp [residualSWeights]
     exact hq.2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) Q (D - 1)).mpr
     intro d hd
     rw [contact_weight]
     have hq := (h hd).2.2
     omega
 · rintro ⟨ht,hs,hc⟩ d hd
   have hdt := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
   have hds := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
   have hdc := (MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
   rw [weight_fin4] at hdt hds
   rw [contact_weight] at hdc
   simp [residualTotalWeights] at hdt
   simp [residualSWeights] at hds
   exact ⟨hdt,hds,by omega⟩
theorem residualYS_mul_le_contact_add_slope (Q : Poly4 K)
   (w : ℕ) (hw : 1 ≤ w) :
   w * wt residualYSWeights Q ≤
     wt (contactWeights w) Q + wt residualSWeights Q := by
 by_cases hQ : Q = 0
 · subst Q
   simp [wt,MvPolynomial.weightedTotalDegree]
 obtain ⟨d,hd,heq⟩ := Finset.exists_mem_eq_sup Q.support
   (MvPolynomial.support_nonempty.mpr hQ)
   (Finsupp.weight residualYSWeights)
 have hc := MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
 have hs := MvPolynomial.le_weightedTotalDegree residualSWeights hd
 change wt residualYSWeights Q = Finsupp.weight residualYSWeights d at heq
 rw [weight_fin4] at heq hs
 rw [contact_weight] at hc
 simp [residualYSWeights] at heq
 simp [residualSWeights] at hs
 simp only [residualYSWeights,residualSWeights]
 rw [heq]
 have hwsub : w - 1 + 1 = w := by omega
 have hwmul : w * d 2 = (w - 1) * d 2 + d 2 := by
   calc
     w * d 2 = ((w - 1) + 1) * d 2 := by rw [hwsub]
     _ = (w - 1) * d 2 + d 2 := by ring
 calc
   w * (d 1 + d 2) ≤
       (d 0 + w * d 1 + (w - 1) * d 2) + d 2 := by
     rw [Nat.mul_add,hwmul]
     omega
   _ ≤ wt (contactWeights w) Q + wt residualSWeights Q :=
     Nat.add_le_add hc hs
theorem quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   (Q H R : Poly4 K) (D w L s contactLower totalLower slopeLower : ℕ)
   (hQ : Q ≠ 0) (hH : H ≠ 0) (hR : R ≠ 0)
   (hbox : Q ∈ globalCoefficientBox K D w L s)
   (heq : Q = H * R)
   (hcontact : contactLower ≤ wt (contactWeights w) H)
   (htotal : totalLower ≤ wt residualTotalWeights H)
   (hslope : slopeLower ≤ wt residualSWeights H) :
   R ∈ globalCoefficientBox K (D - contactLower) w
     (L - totalLower) (s - slopeLower) := by
 have hD : 0 < D := by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have := (hbox hd).2.2
   omega
 have hc := (mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 simp only [wt] at hc hcontact htotal hslope
 have hmulT := weightedTotalDegree_mul residualTotalWeights H R hH hR
 have hmulS := weightedTotalDegree_mul residualSWeights H R hH hR
 have hmulC := weightedTotalDegree_mul (contactWeights w) H R hH hR
 rw [← heq] at hmulT hmulS hmulC
 have hDq : 0 < D - contactLower := by omega
 apply (mem_flagGlobalCoefficientBox_iff R (D - contactLower) w
   (L - totalLower) (s - slopeLower) hDq).mpr
 simp only [wt]
 omega
theorem mem_flagGlobalCoefficientBox_of_dvd
   (F Q : Poly4 K) (D w L s : ℕ)
   (hQ : Q ≠ 0) (hdiv : F ∣ Q)
   (hbox : Q ∈ globalCoefficientBox K D w L s) :
   F ∈ globalCoefficientBox K D w L s := by
 have hD : 0 < D := by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have := (hbox hd).2.2
   omega
 have hc := (mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_flagGlobalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans hc.1,
   (weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans hc.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hc.2.2⟩
section CommonGCD
local instance : StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def commonGCD {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) : Poly4 K :=
 Finset.univ.gcd (fun i ↦ reconstruct K D w L s (b i).1)
theorem commonGCD_dvd_basis {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) (i : ι) :
   commonGCD V b ∣ reconstruct K D w L s (b i).1 := by
 exact Finset.gcd_dvd (Finset.mem_univ i)
theorem commonGCD_ne_zero {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] [Nonempty ι] (b : Module.Basis ι K V) :
   commonGCD V b ≠ 0 := by
 rw [commonGCD,Finset.gcd_ne_zero_iff]
 let i : ι := Classical.choice inferInstance
 refine ⟨i,Finset.mem_univ i,?_⟩
 apply reconstruct_ne_zero K D w L s
 intro hi
 apply b.ne_zero i
 exact Subtype.ext hi
theorem commonGCD_dvd {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) (v : V) :
   commonGCD V b ∣ reconstruct K D w L s v.1 := by
 rw [← b.sum_repr v]
 simp only [Submodule.coe_sum,Submodule.coe_smul]
 change commonGCD V b ∣
   reconstructLinear (K := K) D w L s
     (∑ i,(b.repr v) i • (b i).1)
 rw [map_sum]
 apply Finset.dvd_sum
 intro i hi
 rw [map_smul,MvPolynomial.smul_eq_C_mul]
 exact dvd_mul_of_dvd_right (commonGCD_dvd_basis V b i) _
theorem dvd_commonGCD_iff {D w L s : ℕ}
   (V : Submodule K (CoefficientIndex D w L s → K))
   {ι : Type*} [Fintype ι] (b : Module.Basis ι K V) (F : Poly4 K) :
   F ∣ commonGCD V b ↔
     ∀ v : V,F ∣ reconstruct K D w L s v.1 := by
 constructor
 · intro hF v
   exact hF.trans (commonGCD_dvd V b v)
 · intro hF
   apply Finset.dvd_gcd_iff.mpr
   intro i hi
   exact hF (b i)
end CommonGCD
section LinearQuotient
variable {V : Type*} [AddCommGroup V] [Module K V]
def quotientPolynomial (recon : V →ₗ[K] Poly4 K) (H : Poly4 K)
   (hdiv : ∀ v,H ∣ recon v) (v : V) : Poly4 K :=
 Classical.choose (hdiv v)
theorem recon_eq_mul_quotientPolynomial
   (recon : V →ₗ[K] Poly4 K) (H : Poly4 K)
   (hdiv : ∀ v,H ∣ recon v) (v : V) :
   recon v = H * quotientPolynomial recon H hdiv v :=
 Classical.choose_spec (hdiv v)
def quotientLinear (recon : V →ₗ[K] Poly4 K) (H : Poly4 K)
   (hH : H ≠ 0) (hdiv : ∀ v,H ∣ recon v) : V →ₗ[K] Poly4 K where
 toFun := quotientPolynomial recon H hdiv
 map_add' v z := by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (v + z),map_add,
     recon_eq_mul_quotientPolynomial recon H hdiv v,
     recon_eq_mul_quotientPolynomial recon H hdiv z,mul_add]
 map_smul' a v := by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (a • v),map_smul,
     recon_eq_mul_quotientPolynomial recon H hdiv v]
   simp only [MvPolynomial.smul_eq_C_mul]
   ac_rfl
theorem quotientLinear_injective
   (recon : V →ₗ[K] Poly4 K) (hrecon : Function.Injective recon)
   (H : Poly4 K) (hH : H ≠ 0) (hdiv : ∀ v,H ∣ recon v) :
   Function.Injective (quotientLinear recon H hH hdiv) := by
 intro v z hvz
 apply hrecon
 rw [recon_eq_mul_quotientPolynomial recon H hdiv v,
   recon_eq_mul_quotientPolynomial recon H hdiv z]
 exact congrArg (fun Q : Poly4 K ↦ H * Q) hvz
theorem finrank_le_quotient_box
   (recon : V →ₗ[K] Poly4 K) (hrecon : Function.Injective recon)
   (H : Poly4 K) (hH : H ≠ 0) (hdiv : ∀ v,H ∣ recon v)
   (W : Submodule K (Poly4 K)) [Module.Finite K W]
   (hmem : ∀ v,quotientPolynomial recon H hdiv v ∈ W) :
   Module.finrank K V ≤ Module.finrank K W := by
 let q : V →ₗ[K] W := LinearMap.codRestrict W
   (quotientLinear recon H hH hdiv) hmem
 apply LinearMap.finrank_le_finrank_of_injective (f := q)
 intro v z hvz
 apply quotientLinear_injective recon hrecon H hH hdiv
 exact congrArg Subtype.val hvz
end LinearQuotient
section ConstraintKernel
open ContactFlagRankKernel6641Research
variable {I : Type*} [Fintype I]
abbrev ConstraintKernel (D w L s m : ℕ)
   (nodes u₀ u₁ : I → K) :=
 LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)
def kernelReconstructLinear (D w L s m : ℕ)
   (nodes u₀ u₁ : I → K) :
   ConstraintKernel (K := K) D w L s m nodes u₀ u₁ →ₗ[K] Poly4 K :=
 (reconstructLinear (K := K) D w L s).comp
   (ConstraintKernel (K := K) D w L s m nodes u₀ u₁).subtype
@[simp] theorem kernelReconstructLinear_apply (D w L s m : ℕ)
   (nodes u₀ u₁ : I → K)
   (v : ConstraintKernel (K := K) D w L s m nodes u₀ u₁) :
   kernelReconstructLinear (K := K) D w L s m nodes u₀ u₁ v =
     reconstruct K D w L s v.1 := rfl
theorem kernelReconstructLinear_injective (D w L s m : ℕ)
   (nodes u₀ u₁ : I → K) :
   Function.Injective
     (kernelReconstructLinear (K := K) D w L s m nodes u₀ u₁) := by
 intro v z hvz
 apply Subtype.ext
 apply reconstructLinear_injective (K := K) D w L s
 exact hvz
private theorem nat_sub_le_of_add_eq_of_le {R K C B : ℕ}
   (hsum : R + K = C) (hr : R ≤ B) : C - B ≤ K := by
 apply Nat.sub_le_of_le_add
 rw [← hsum]
 simpa [Nat.add_comm] using Nat.add_le_add_right hr K
theorem constraintKernel_finrank_lower_bound (D w L s m : ℕ)
   (nodes u₀ u₁ : I → K) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     Module.finrank K
       (ConstraintKernel (K := K) D w L s m nodes u₀ u₁) := by
 let f := constraintMap K D w L s m nodes u₀ u₁
 have hsum := f.finrank_range_add_finrank_ker
 have hrange : Module.finrank K f.range ≤
     Fintype.card I * localRankBound m L s :=
   f.range.finrank_le.trans (globalTarget_finrank_le K m L s)
 have hdom : Module.finrank K (CoefficientIndex D w L s → K) =
     coefficientCount D w L s := by
   rw [Module.finrank_fintype_fun_eq_card K,coefficient_index_card]
 dsimp [f] at hsum hrange
 rw [hdom] at hsum
 dsimp [ConstraintKernel] at hsum ⊢
 exact nat_sub_le_of_add_eq_of_le hsum hrange
theorem common_divisor_dimension_obstruction
   (D w L s m Dq Lq sq : ℕ) (nodes u₀ u₁ : I → K)
   (H : Poly4 K) (hH : H ≠ 0)
   (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u₀ u₁,
     H ∣ kernelReconstructLinear (K := K) D w L s m nodes u₀ u₁ v)
   (hqbox : ∀ v : ConstraintKernel (K := K) D w L s m nodes u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K := K) D w L s m nodes u₀ u₁)
       H hdiv v ∈ globalCoefficientBox K Dq w Lq sq) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     coefficientCount Dq w Lq sq := by
 have hlo := constraintKernel_finrank_lower_bound
   (K := K) D w L s m nodes u₀ u₁
 have hhi := finrank_le_quotient_box
   (kernelReconstructLinear (K := K) D w L s m nodes u₀ u₁)
   (kernelReconstructLinear_injective (K := K) D w L s m nodes u₀ u₁)
   H hH hdiv (globalCoefficientBox K Dq w Lq sq) hqbox
 rw [globalCoefficientBox_finrank] at hhi
 exact hlo.trans hhi
end ConstraintKernel
namespace Numeric6734
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactStackedParameters6670Research
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem profileA_localRank_exact :
   localRankBound 42 84439 12 = 769336295 := by
 decide
theorem profileB_localRank_exact :
   localRankBound 81 1284 25 = 81865225 := by
 decide
theorem profileA_full_nullity_exact :
   coefficientCount 7645344 131071 84439 12 -
       262144 * localRankBound 42 84439 12 = 56672067842 := by
 rw [profileA_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   7645344 131071 84439 12 59 (by decide) (by decide)]
 decide
theorem profileA_corner_quotient_exact :
   coefficientCount 305380 131071 84383 0 = 44126411183 := by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   305380 131071 84383 0 3 (by decide) (by decide)]
 decide
theorem profileA_uniform_ys_quotient_exact :
   coefficientCount 174309 131071 84382 12 = 22005818561 := by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   174309 131071 84382 12 2 (by decide) (by decide)]
 decide
theorem profileB_full_nullity_exact :
   coefficientCount 14744592 131071 1284 25 -
       262144 * localRankBound 81 1284 25 = 169054054 := by
 rw [profileB_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   14744592 131071 1284 25 113 (by decide) (by decide)]
 decide
theorem profileB_total_quotient_exact :
   coefficientCount 14744592 131071 2 25 = 146135215 := by
 decide
theorem profileB_uniform_ys_quotient_exact :
   coefficientCount 8584280 131071 3 25 = 167753485 := by
 decide
theorem profileA_uniform_ys_dimension :
   coefficientCount 7645344 131071 84439 12 -
       262144 * localRankBound 42 84439 12 >
     coefficientCount 174309 131071 84382 12 := by
 rw [profileA_full_nullity_exact]
 rw [profileA_uniform_ys_quotient_exact]
 decide
theorem profileA_corner_dimension :
   coefficientCount 7645344 131071 84439 12 -
       262144 * localRankBound 42 84439 12 >
     coefficientCount 305380 131071 84383 0 := by
 rw [profileA_full_nullity_exact]
 rw [profileA_corner_quotient_exact]
 decide
theorem profileB_total_dimension :
   coefficientCount 14744592 131071 1284 25 -
       262144 * localRankBound 81 1284 25 >
     coefficientCount 14744592 131071 2 25 := by
 rw [profileB_full_nullity_exact]
 rw [profileB_total_quotient_exact]
 decide
theorem profileB_uniform_ys_dimension :
   coefficientCount 14744592 131071 1284 25 -
       262144 * localRankBound 81 1284 25 >
     coefficientCount 8584280 131071 3 25 := by
 rw [profileB_full_nullity_exact]
 rw [profileB_uniform_ys_quotient_exact]
 decide
end Numeric6734
namespace Caps6734
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactGCDCumulativeFlagsResearch
open Numeric6734
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev AKernel (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K := IRSProfile.Field)
   7645344 131071 84439 12 42 IRSProfile.domain u₀ u₁
abbrev BKernel (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K := IRSProfile.Field)
   14744592 131071 1284 25 81 IRSProfile.domain u₀ u₁
private theorem commonGCD_data
   (D L s m : ℕ) (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field
     (ConstraintKernel (K := IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁)) :
   let V := ConstraintKernel (K := IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁
   let H := commonGCD (D := D) (w := 131071) (L := L) (s := s) V b
   H ≠ 0 ∧
     (∀ v : V,H ∣ kernelReconstructLinear (K := IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁ v) ∧
     H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s := by
 dsimp only
 let V := ConstraintKernel (K := IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let H := commonGCD (D := D) (w := 131071) (L := L) (s := s) V b
 have hH : H ≠ 0 := commonGCD_ne_zero V b
 have hdiv : ∀ v : V,H ∣ kernelReconstructLinear (K := IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁ v := by
   intro v
   rw [kernelReconstructLinear_apply]
   exact commonGCD_dvd V b v
 let i : ι := Classical.choice inferInstance
 let Qi := reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQi : Qi ≠ 0 := by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hbzero
   apply b.ne_zero i
   exact Subtype.ext hbzero
 have hQibox : Qi ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
   reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1
 have hHbox : H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
   mem_flagGlobalCoefficientBox_of_dvd H Qi D 131071 L s hQi
     (commonGCD_dvd_basis V b i) hQibox
 exact ⟨hH,hdiv,hHbox⟩
private theorem quotient_box_of_commonGCD
   (D L s m contactLower totalLower slopeLower : ℕ)
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field
     (ConstraintKernel (K := IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁))
   (hcontact : contactLower ≤ wt (contactWeights 131071)
     (commonGCD (D := D) (w := 131071) (L := L) (s := s)
       (ConstraintKernel (K := IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b))
   (htotal : totalLower ≤ wt residualTotalWeights
     (commonGCD (D := D) (w := 131071) (L := L) (s := s)
       (ConstraintKernel (K := IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b))
   (hslope : slopeLower ≤ wt residualSWeights
     (commonGCD (D := D) (w := 131071) (L := L) (s := s)
       (ConstraintKernel (K := IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b)) :
   let V := ConstraintKernel (K := IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁
   let H := commonGCD (D := D) (w := 131071) (L := L) (s := s) V b
   ∀ v : V,quotientPolynomial
     (kernelReconstructLinear (K := IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁) H
     (fun v ↦ commonGCD_dvd V b v) v ∈
       globalCoefficientBox IRSProfile.Field (D - contactLower) 131071
         (L - totalLower) (s - slopeLower) := by
 dsimp only
 intro v
 let V := ConstraintKernel (K := IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let H := commonGCD (D := D) (w := 131071) (L := L) (s := s) V b
 let recon := kernelReconstructLinear (K := IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let hdiv : ∀ z : V,H ∣ recon z := by
   intro z
   rw [kernelReconstructLinear_apply]
   exact commonGCD_dvd V b z
 have hH : H ≠ 0 := commonGCD_ne_zero V b
 by_cases hv : v = 0
 · subst v
   have hqzero : quotientPolynomial recon H hdiv 0 = 0 := by
     apply mul_left_cancel₀ hH
     rw [← recon_eq_mul_quotientPolynomial recon H hdiv 0]
     simp
   rw [hqzero]
   exact (globalCoefficientBox IRSProfile.Field _ _ _ _).zero_mem
 · let R := quotientPolynomial recon H hdiv v
   have hQv : recon v ≠ 0 := by
     intro hz
     apply hv
     apply kernelReconstructLinear_injective (K := IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁
     simpa only [map_zero] using hz
   have hR : R ≠ 0 := by
     intro hz
     apply hQv
     rw [recon_eq_mul_quotientPolynomial recon H hdiv v]
     change H * R = 0
     rw [hz,mul_zero]
   have hReconBox : recon v ∈ globalCoefficientBox IRSProfile.Field
       D 131071 L s := by
     rw [kernelReconstructLinear_apply]
     exact reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s v.1
   exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
     (recon v) H R D 131071 L s contactLower totalLower slopeLower
     hQv hH hR hReconBox (recon_eq_mul_quotientPolynomial recon H hdiv v)
     hcontact htotal hslope
private theorem globalCoefficientBox_mono
   {D D' w L L' s s' : ℕ} (hD : D ≤ D') (hL : L ≤ L') (hs : s ≤ s') :
   globalCoefficientBox IRSProfile.Field D w L s ≤
     globalCoefficientBox IRSProfile.Field D' w L' s' := by
 intro Q hQ d hd
 exact ⟨(hQ hd).1.trans hL,(hQ hd).2.1.trans hs,
   lt_of_lt_of_le (hQ hd).2.2 hD⟩
theorem profileA_commonGCD_ys_le
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   wt residualYSWeights
     (commonGCD (D := 7645344) (w := 131071) (L := 84439) (s := 12)
       (AKernel u₀ u₁) b) ≤ 56 := by
 let H := commonGCD (D := 7645344) (w := 131071) (L := 84439) (s := 12)
   (AKernel u₀ u₁) b
 obtain ⟨hH,hdiv,hHbox⟩ := commonGCD_data 7645344 84439 12 42 u₀ u₁ b
 have hHcaps := (mem_flagGlobalCoefficientBox_iff H
   7645344 131071 84439 12 (by decide)).mp hHbox
 by_contra hnot
 change ¬ wt residualYSWeights H ≤ 56 at hnot
 have hys : 57 ≤ wt residualYSWeights H := by omega
 let r := wt residualSWeights H
 have hr : r ≤ 12 := hHcaps.2.1
 have htotal : 57 ≤ wt residualTotalWeights H :=
   hys.trans (residual_weight_nested H).2
 have hrel := residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact : 57 * 131071 - r ≤ wt (contactWeights 131071) H := by
   dsimp [r]
   omega
 have hqbox0 := quotient_box_of_commonGCD 7645344 84439 12 42
   (57 * 131071 - r) 57 r u₀ u₁ b hcontact htotal (le_refl r)
 have hqbox : ∀ v : AKernel u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K := IRSProfile.Field)
         7645344 131071 84439 12 42 IRSProfile.domain u₀ u₁)
       H hdiv v ∈ globalCoefficientBox IRSProfile.Field
         174309 131071 84382 12 := by
   intro v
   apply globalCoefficientBox_mono
     (D := 7645344 - (57 * 131071 - r)) (L := 84439 - 57) (s := 12 - r)
     (by omega) (by omega) (by omega)
   exact hqbox0 v
 have hobs := common_divisor_dimension_obstruction
   (K := IRSProfile.Field) 7645344 131071 84439 12 42
   174309 84382 12
   IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileA_uniform_ys_dimension) hobs
theorem profileA_commonGCD_corner
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   wt residualYSWeights
       (commonGCD (D := 7645344) (w := 131071) (L := 84439) (s := 12)
         (AKernel u₀ u₁) b) ≤ 55 ∨
     wt residualSWeights
       (commonGCD (D := 7645344) (w := 131071) (L := 84439) (s := 12)
         (AKernel u₀ u₁) b) ≤ 11 := by
 let H := commonGCD (D := 7645344) (w := 131071) (L := 84439) (s := 12)
   (AKernel u₀ u₁) b
 obtain ⟨hH,hdiv,hHbox⟩ := commonGCD_data 7645344 84439 12 42 u₀ u₁ b
 have hHcaps := (mem_flagGlobalCoefficientBox_iff H
   7645344 131071 84439 12 (by decide)).mp hHbox
 by_contra hnot
 change ¬ (wt residualYSWeights H ≤ 55 ∨
   wt residualSWeights H ≤ 11) at hnot
 push_neg at hnot
 have hys : 56 ≤ wt residualYSWeights H := by omega
 have hslope : 12 ≤ wt residualSWeights H := by omega
 have htotal : 56 ≤ wt residualTotalWeights H :=
   hys.trans (residual_weight_nested H).2
 have hrel := residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact : 56 * 131071 - 12 ≤ wt (contactWeights 131071) H := by
   omega
 have hqbox := quotient_box_of_commonGCD 7645344 84439 12 42
   (56 * 131071 - 12) 56 12 u₀ u₁ b hcontact htotal hslope
 have hobs := common_divisor_dimension_obstruction
   (K := IRSProfile.Field) 7645344 131071 84439 12 42
   305380 84383 0
   IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileA_corner_dimension) hobs
theorem profileB_commonGCD_total_le
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   wt residualTotalWeights
     (commonGCD (D := 14744592) (w := 131071) (L := 1284) (s := 25)
       (BKernel u₀ u₁) b) ≤ 1281 := by
 let H := commonGCD (D := 14744592) (w := 131071) (L := 1284) (s := 25)
   (BKernel u₀ u₁) b
 obtain ⟨hH,hdiv,_hHbox⟩ := commonGCD_data 14744592 1284 25 81 u₀ u₁ b
 by_contra hnot
 change ¬ wt residualTotalWeights H ≤ 1281 at hnot
 have htotal : 1282 ≤ wt residualTotalWeights H := by omega
 have hqbox := quotient_box_of_commonGCD 14744592 1284 25 81
   0 1282 0 u₀ u₁ b (Nat.zero_le _) htotal (Nat.zero_le _)
 have hobs := common_divisor_dimension_obstruction
   (K := IRSProfile.Field) 14744592 131071 1284 25 81
   14744592 2 25 IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileB_total_dimension) hobs
theorem profileB_commonGCD_corner
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field)
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   wt residualTotalWeights
       (commonGCD (D := 14744592) (w := 131071) (L := 1284) (s := 25)
         (BKernel u₀ u₁) b) ≤ 1280 ∨
     wt residualYSWeights
       (commonGCD (D := 14744592) (w := 131071) (L := 1284) (s := 25)
         (BKernel u₀ u₁) b) ≤ 46 := by
 let H := commonGCD (D := 14744592) (w := 131071) (L := 1284) (s := 25)
   (BKernel u₀ u₁) b
 obtain ⟨hH,hdiv,hHbox⟩ := commonGCD_data 14744592 1284 25 81 u₀ u₁ b
 have hHcaps := (mem_flagGlobalCoefficientBox_iff H
   14744592 131071 1284 25 (by decide)).mp hHbox
 by_contra hnot
 change ¬ (wt residualTotalWeights H ≤ 1280 ∨
   wt residualYSWeights H ≤ 46) at hnot
 push_neg at hnot
 have htotal : 1281 ≤ wt residualTotalWeights H := by omega
 have hys : 47 ≤ wt residualYSWeights H := by omega
 let r := wt residualSWeights H
 have hr : r ≤ 25 := hHcaps.2.1
 have hrel := residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact : 47 * 131071 - r ≤ wt (contactWeights 131071) H := by
   dsimp [r]
   omega
 have hqbox0 := quotient_box_of_commonGCD 14744592 1284 25 81
   (47 * 131071 - r) 1281 r u₀ u₁ b hcontact htotal (le_refl r)
 have hqbox : ∀ v : BKernel u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K := IRSProfile.Field)
         14744592 131071 1284 25 81 IRSProfile.domain u₀ u₁)
       H hdiv v ∈ globalCoefficientBox IRSProfile.Field
         8584280 131071 3 25 := by
   intro v
   apply globalCoefficientBox_mono
     (D := 14744592 - (47 * 131071 - r)) (L := 1284 - 1281) (s := 25 - r)
     (by omega) (by omega) (by omega)
   exact hqbox0 v
 have hobs := common_divisor_dimension_obstruction
   (K := IRSProfile.Field) 14744592 131071 1284 25 81
   8584280 3 25 IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileB_uniform_ys_dimension) hobs
end Caps6734
end
end ProximityPrize.SubmissionLower.ContactKernelCommonGCDResearch
