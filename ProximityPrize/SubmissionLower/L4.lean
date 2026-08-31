import ProximityPrize.SubmissionLower.L2
namespace ProximityPrize.SubmissionLower.RCN183
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN100 RCN119
open RCN101
open RCN180 RCN181
open RCN137 RCN130
open RCN234
open RCN156
open RCN081
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:StrongNormalizationMonoid GlobalPoly:=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
def agreements6733:ℕ:=182042
abbrev AKernel (u₀ u₁:IRSProfile.Index→ IRSProfile.Field):=
 ConstraintKernel (K:=IRSProfile.Field)
   7645764 131071 84439 12 42 IRSProfile.domain u₀ u₁
abbrev BKernel (u₀ u₁:IRSProfile.Index→ IRSProfile.Field):=
 ConstraintKernel (K:=IRSProfile.Field)
   14745402 131071 1262 25 81 IRSProfile.domain u₀ u₁
abbrev CKernel (u₀ u₁:IRSProfile.Index→ IRSProfile.Field):=
 ConstraintKernel (K:=IRSProfile.Field)
   7463722 131071 41787 12 41 IRSProfile.domain u₀ u₁
theorem gateA:
   Fintype.card IRSProfile.Index * localRankBound 42 84439 12<
     coefficientCount 7645764 131071 84439 12:=by
 rw [show Fintype.card IRSProfile.Index=262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7645764 131071 84439 12 59 (by decide) (by decide)]
 decide
theorem gateB:
   Fintype.card IRSProfile.Index * localRankBound 81 1262 25<
     coefficientCount 14745402 131071 1262 25:=by
 rw [show Fintype.card IRSProfile.Index=262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   14745402 131071 1262 25 113 (by decide) (by decide)]
 decide
theorem gateC:
   Fintype.card IRSProfile.Index * localRankBound 41 41787 12<
     coefficientCount 7463722 131071 41787 12:=by
 rw [show Fintype.card IRSProfile.Index=262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7463722 131071 41787 12 57 (by decide) (by decide)]
 decide
theorem field_cardinality:
   Fintype.card IRSProfile.Field=(2130706433:ℕ)^6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem normalizedFactorSet_card_lt_field_of_mem_flagBox
   (P:GlobalPoly) (D L s:ℕ) (hP:P≠ 0)
   (hbox:P∈ globalCoefficientBox IRSProfile.Field D 131071 L s)
   (hsmall:(D-1)+(D-1)/131071+s+L<
     (2130706433:ℕ)^6):
   (normalizedFactorSet P).card< ENat.card IRSProfile.Field:=by
 have hle:=normalizedFactorSet_card_le_of_mem_flagBox
   P D 131071 L s (by decide) hP hbox
 rw [ENat.card_eq_coe_fintype_card,field_cardinality]
 exact_mod_cast hle.trans_lt hsmall
theorem commonGCD_mem_flagBox
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field (CoefficientIndex D 131071 L s→ IRSProfile.Field))
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field V):
   commonGCD V b∈ globalCoefficientBox IRSProfile.Field D 131071 L s:=by
 let i:ι:=Classical.choice inferInstance
 let Q:=reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQ:Q≠ 0:=by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hb
   apply b.ne_zero i
   exact Subtype.ext hb
 exact mem_flagGlobalCoefficientBox_of_dvd (commonGCD V b) Q
   D 131071 L s hQ (commonGCD_dvd_basis V b i)
   (reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1)
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
private theorem gcd_mul_right_plain_associated
   (P H q:GlobalPoly) (hc:IsRelPrime q P):
   Associated (gcd P (H * q)) (gcd P H):=by
 apply associated_of_dvd_dvd
 · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
   have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
   have hcop:IsRelPrime (gcd P (H * q)) q:=
     hc.symm.of_dvd_left hleft
   exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
 · exact dvd_gcd (gcd_dvd_left P H)
     ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
   (H q P:GlobalPoly) (hc:IsRelPrime q P):
   Associated (gcd (H * q) P) (gcd H P):=by
 apply associated_of_dvd_dvd
 · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
   have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
   have hcop:IsRelPrime (gcd (H * q) P) q:=
     hc.symm.of_dvd_left hright
   exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
 · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
     (gcd_dvd_right H P)
@[simp] theorem submoduleReconstructLinear_apply
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field
     (CoefficientIndex D 131071 L s→ IRSProfile.Field)) (v:V):
   submoduleReconstructLinear V v=
     reconstruct IRSProfile.Field D 131071 L s v.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN183
