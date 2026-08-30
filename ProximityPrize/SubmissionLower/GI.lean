import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.GE
import ProximityPrize.SubmissionLower.CC
namespace ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
open ProximityPrize.Benchmark
open ContactTranslation ContactRecursiveGCDResearch
open ContactStackedGCDCover6670Research
noncomputable section
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq (Polynomial IRSProfile.Field):=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def gcd12Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 ContactStackedSeedPartition6656Research.gcd12Vanishes
   selected QA QB gamma
def gcd123Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB QC:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 ContactStackedSeedPartition6656Research.gcd123Vanishes
   selected QA QB QC gamma
def firstResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB:GlobalPoly):
   Finset IRSProfile.Field:=
 ContactStackedSeedPartition6656Research.firstResidualSeeds
   selected Gamma QA QB
def secondResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=
 ContactStackedSeedPartition6656Research.secondResidualSeeds
   selected Gamma QA QB QC
def fixedSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=
 ContactStackedSeedPartition6656Research.fixedSeeds
   selected Gamma QA QB QC
theorem partition_card
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   (firstResidualSeeds selected Gamma QA QB).card+
     (secondResidualSeeds selected Gamma QA QB QC).card+
     (fixedSeeds selected Gamma QA QB QC).card=Gamma.card:=by
 simpa only [firstResidualSeeds,secondResidualSeeds,fixedSeeds] using
   ContactStackedSeedPartition6656Research.partition_card
     selected Gamma QA QB QC
theorem firstResidualSeeds_subset
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB:GlobalPoly):
   firstResidualSeeds selected Gamma QA QB ⊆ Gamma:=by
 classical
 intro gamma hgamma
 rw [firstResidualSeeds,
   ContactStackedSeedPartition6656Research.firstResidualSeeds] at hgamma
 exact (Finset.mem_filter.mp hgamma).1
theorem secondResidualSeeds_subset
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   secondResidualSeeds selected Gamma QA QB QC ⊆ Gamma:=by
 classical
 intro gamma hgamma
 rw [secondResidualSeeds,
   ContactStackedSeedPartition6656Research.secondResidualSeeds] at hgamma
 exact (Finset.mem_filter.mp (Finset.mem_filter.mp hgamma).1).1
theorem fixedSeeds_subset
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   fixedSeeds selected Gamma QA QB QC ⊆ Gamma:=by
 classical
 intro gamma hgamma
 rw [fixedSeeds,
   ContactStackedSeedPartition6656Research.fixedSeeds] at hgamma
 exact (Finset.mem_filter.mp (Finset.mem_filter.mp hgamma).1).1
private theorem old_cover_of_new_cover
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC):
   ∀ gamma∈Gamma,
     ContactStackedGCDCover6656Research.RecursiveSpecializationBranch
       (selected gamma) gamma QA QB QC:=by
 intro gamma hgamma
 simpa only [RecursiveSpecializationBranch,
   ContactStackedGCDCover6656Research.RecursiveSpecializationBranch] using
     hcover gamma hgamma
theorem firstResidualSeeds_quotient_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC):
   ∀ gamma∈firstResidualSeeds selected Gamma QA QB,
     specialization IRSProfile.Field (selected gamma) gamma
         (quotientA QA QB)=0∧
       specialization IRSProfile.Field (selected gamma) gamma
         (quotientB QA QB)=0:=by
 simpa only [firstResidualSeeds] using
   ContactStackedSeedPartition6656Research.firstResidualSeeds_quotient_vanish
     selected Gamma QA QB QC
     (old_cover_of_new_cover selected Gamma QA QB QC hcover)
theorem secondResidualSeeds_quotient_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC):
   ∀ gamma∈secondResidualSeeds selected Gamma QA QB QC,
     specialization IRSProfile.Field (selected gamma) gamma
         (middleQuotient QA QB QC)=0∧
       specialization IRSProfile.Field (selected gamma) gamma
         (quotientC QA QB QC)=0:=by
 simpa only [secondResidualSeeds] using
   ContactStackedSeedPartition6656Research.secondResidualSeeds_quotient_vanish
     selected Gamma QA QB QC
     (old_cover_of_new_cover selected Gamma QA QB QC hcover)
theorem fixedSeeds_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   ∀ gamma∈fixedSeeds selected Gamma QA QB QC,
     specialization IRSProfile.Field (selected gamma) gamma
       (gcd123 QA QB QC)=0:=by
 simpa only [fixedSeeds] using
   ContactStackedSeedPartition6656Research.fixedSeeds_vanish
     selected Gamma QA QB QC
end
end ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
