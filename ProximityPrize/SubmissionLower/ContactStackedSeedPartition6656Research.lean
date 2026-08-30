import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6656Research
namespace ProximityPrize.SubmissionLower.ContactStackedSeedPartition6656Research
open ProximityPrize.Benchmark
open ContactTranslation ContactRecursiveGCDResearch
open ContactStackedGCDCover6656Research
noncomputable section
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq (Polynomial IRSProfile.Field):=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def gcd12Vanishes
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (QA QB:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
  specialization IRSProfile.Field (selected gamma) gamma (gcd12 QA QB)=0
def gcd123Vanishes
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (QA QB QC:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
  specialization IRSProfile.Field (selected gamma) gamma (gcd123 QA QB QC)=0
def firstResidualSeeds
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB:GlobalPoly):
    Finset IRSProfile.Field:=by
  classical
  exact Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)
def secondResidualSeeds
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
    Finset IRSProfile.Field:=by
  classical
  exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
    (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)
def fixedSeeds
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
    Finset IRSProfile.Field:=by
  classical
  exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
    (gcd123Vanishes selected QA QB QC)
theorem partition_card
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
    (firstResidualSeeds selected Gamma QA QB).card+
      (secondResidualSeeds selected Gamma QA QB QC).card+
      (fixedSeeds selected Gamma QA QB QC).card=Gamma.card:=by
  classical
  have houter:=Finset.card_filter_add_card_filter_not
    (s:=Gamma) (gcd12Vanishes selected QA QB)
  have hinner:=Finset.card_filter_add_card_filter_not
    (s:=Gamma.filter (gcd12Vanishes selected QA QB))
    (gcd123Vanishes selected QA QB QC)
  simp only [firstResidualSeeds,secondResidualSeeds,fixedSeeds]
  change
    (Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)).card+
      ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
        (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)).card+
      ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
        (gcd123Vanishes selected QA QB QC)).card=Gamma.card
  omega
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
  classical
  intro gamma hgamma
  rw [firstResidualSeeds] at hgamma
  have hm:=Finset.mem_filter.mp hgamma
  have hbranch:=hcover gamma hm.1
  rcases hbranch with hfirst | hsecond | hfixed
  · exact hfirst.2
  · exact False.elim (hm.2 hsecond.1)
  · exact False.elim (hm.2 hfixed.2)
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
  classical
  intro gamma hgamma
  rw [secondResidualSeeds] at hgamma
  have hmOuter:=Finset.mem_filter.mp hgamma
  have hmInner:=Finset.mem_filter.mp hmOuter.1
  have hbranch:=hcover gamma hmInner.1
  rcases hbranch with hfirst | hsecond | hfixed
  · exact False.elim (hfirst.1 hmInner.2)
  · exact hsecond.2.2
  · exact False.elim (hmOuter.2 hfixed.1)
theorem fixedSeeds_vanish
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
    ∀ gamma∈fixedSeeds selected Gamma QA QB QC,
      specialization IRSProfile.Field (selected gamma) gamma
        (gcd123 QA QB QC)=0:=by
  classical
  intro gamma hgamma
  rw [fixedSeeds] at hgamma
  exact (Finset.mem_filter.mp hgamma).2
end
end ProximityPrize.SubmissionLower.ContactStackedSeedPartition6656Research
