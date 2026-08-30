import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.F0
import ProximityPrize.SubmissionLower.O7
namespace ProximityPrize.SubmissionLower.RCN284
open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
def radius:ℝ≥0:=RCN278.radius6630
def errors:ℕ:=RCN278.errors6630
def mcaBudget:ℕ:=274980727511395087
theorem field_cardinality:
   Fintype.card IRSProfile.Field=(2130706433:ℕ)^6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem irs_code_eq_base_interleaved:
   IRSProfile.code=
     (IRSProfile.baseCode^⋈ (Fin IRSProfile.interleaving):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin IRSProfile.interleaving → IRSProfile.Field)):=by
 ext v
 change v∈IRSProfile.code ↔
   ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode
 exact RCN018.irs_code_mem_iff_rows v
theorem nat_div_le_inv_pow {m q t:ℕ} (hm:0 < m)
   (hq:m*2^t ≤ q):
   (m:ENNReal)/(q:ENNReal) ≤ 1/2^t:=by
 have hm0:(m:ENNReal)≠0:=by exact_mod_cast hm.ne'
 have hmtop:(m:ENNReal)≠⊤:=ENNReal.natCast_ne_top m
 have hqE:((m*2^t:ℕ):ENNReal) ≤ (q:ENNReal):=by
   exact_mod_cast hq
 have hcast:((m*2^t:ℕ):ENNReal)=(m:ENNReal)*2^t:=by
   push_cast
   ring
 calc
   (m:ENNReal)/(q:ENNReal) ≤
       (m:ENNReal)/((m*2^t:ℕ):ENNReal):=
     ENNReal.div_le_div_left hqE _
   _=(m:ENNReal)/((m:ENNReal)*2^t):=by rw [hcast]
   _=(m:ENNReal)*1/((m:ENNReal)*2^t):=by rw [mul_one]
   _=1/2^t:=ENNReal.mul_div_mul_left 1 (2^t) hm0 hmtop
theorem affineLineAlignmentBound_mono_budget
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   {C:LinearCode ι F} {e a b:ℕ}
   (hab:a ≤ b) (h:AffineLineAlignmentBound C e a):
   AffineLineAlignmentBound C e b:=by
 intro U S A hS hcard hprojected
 exact h U S A (hab.trans_lt hS) hcard hprojected
theorem field_capacity_split:
   2^(128:ℕ)*
       (mcaBudget+RCN281.listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [field_cardinality]
 norm_num [mcaBudget,RCN281.listBudget]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors by
     simpa only [radius,errors] using
       RCN278.radius6630_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,RCN278.errors6630] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=
     base_mca_le_of_alignment halign
   _=(mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
         IRSProfile.Field))
     (radius:ℝ) ≤
       (RCN281.listBudget:ℕ∞):=by
 apply RCN280.irs_squared_lambda_seedless
 norm_num [radius,RCN278.radius6630,claimedRadius,
   RCN279.errors,IRSProfile.Index]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0)/2^(128:ℕ):=by
 rw [←ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code^⋈ (Fin 2):
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal)+
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
     add_le_add (mca_le_of_alignment halign) hList
   _=((mcaBudget+RCN281.listBudget:ℕ):ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [←ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal)/2^(128:ℕ):=by
     apply nat_div_le_inv_pow
     · norm_num [mcaBudget,RCN281.listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6710_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   ProtocolClaim 6710 319467 1048576 where
 admissible:=RCN278.radius6630_admissible
 reduction:=by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   exact (certifiedGammaError_le_of_alignment halign).trans
     (by norm_num [reductionTarget,ProximityGap.prizeThreshold,div_le_iff₀])
 score:=RCN278.radius6630_score
theorem protocolClaim6696_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   ProtocolClaim 6710 319467 1048576:=
 protocolClaim6710_of_alignment halign
end
end ProximityPrize.SubmissionLower.RCN284
