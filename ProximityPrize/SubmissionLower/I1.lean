import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.I0
namespace ProximityPrize.SubmissionLower.RCN061
open scoped BigOperators
open RCN060
noncomputable section
variable {k F L:Type*} [Field k] [Field F] [Field L] [Algebra k F]
theorem coefficient_pole_le_generic_evaluation_of_trdeg_le_one
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F ≤ 1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 classical
 letI:Decidable (Algebra.trdeg k F=0):=Classical.propDecidable _
 by_cases hz:Algebra.trdeg k F=0
 · letI:Algebra.IsAlgebraic k F:=trdeg_eq_zero_iff.mp hz
   letI:Algebra.IsIntegral k F:=
     Algebra.isAlgebraic_iff_isIntegral.mp (inferInstance:Algebra.IsAlgebraic k F)
   obtain ⟨c,hc⟩:=
     (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=k)).2 (a i)
   have hφ:φ (a i)=algebraMap Ω L (algebraMap k Ω c):=by
     rw [←hc,hcompat]
   have hpole:RCN187.poleOrder v (φ (a i))=0:=by
     rw [hφ]
     change max 0 (v (algebraMap Ω L (algebraMap k Ω c))).log=0
     rw [←RCN187.log_max_one,
       max_eq_left (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _),
       WithZero.log_one]
   rw [hpole]
   exact le_max_left _ _
 · have hone:(1:Cardinal) ≤ Algebra.trdeg k F:=
     Cardinal.one_le_iff_ne_zero.mpr hz
   have heq:Algebra.trdeg k F=1:=le_antisymm htrdeg hone
   exact coefficient_pole_le_generic_evaluation v φ hcompat heq x htrans a i
end
end ProximityPrize.SubmissionLower.RCN061
