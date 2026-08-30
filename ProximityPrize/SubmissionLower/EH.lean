import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.G
namespace ProximityPrize.SubmissionLower.RCN129
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
 [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
theorem trdeg_le_one_of_functionField:Algebra.trdeg K L ≤ 1:=by
 classical
 unfold Algebra.trdeg
 refine ciSup_le' fun s↦Cardinal.mk_le_one_iff_set_subsingleton.mpr ?_
 intro x hx y hy
 by_contra hxy
 let i:s.1:=⟨x,hx⟩
 let j:s.1:=⟨y,hy⟩
 have ht:Transcendental K x:=s.2.transcendental i
 letI:FiniteDimensional (IntermediateField.adjoin K ({x}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental ht
 have hyalg:IsAlgebraic (Algebra.adjoin K ({x}:Set L)) y:=
   IntermediateField.isAlgebraic_adjoin_iff.mp
     (Algebra.IsAlgebraic.isAlgebraic y)
 have hji:j∉({i}:Set s.1):=by
   simpa only [Set.mem_singleton_iff] using
     (show j≠i from fun h↦hxy (congrArg Subtype.val h).symm)
 have hytr:=s.2.transcendental_adjoin hji
 have himage:(fun z:s.1↦(z:L)) '' ({i}:Set s.1)={x}:=by
   simp [i]
 change Transcendental (Algebra.adjoin K
   ((fun z:s.1↦(z:L)) '' ({i}:Set s.1))) y at hytr
 rw [himage] at hytr
 exact hytr hyalg
end
end ProximityPrize.SubmissionLower.RCN129
