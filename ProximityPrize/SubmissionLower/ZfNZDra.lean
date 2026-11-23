import ProximityPrize.SubmissionLower.ZQBQYdc
import ProximityPrize.SubmissionLower.ZhyMlza
set_option Elab.async false
section
namespace q85rTDe
noncomputable section
open P5 (p)
open q2TwyLa (PhysicalField i5 ek diffPoly)
open scoped Polynomial WithZero
abbrev physicalVal:Valuation PhysicalField ℤᵐ⁰:=Valued.v
structure SeedData where
 constants :Subfield PhysicalField
 z :PhysicalField
 D:Derivation ℤ PhysicalField PhysicalField
 seed_deriv :D z=1
 kill : ∀ c:constants,D (c:PhysicalField)=0
 coeff_deriv : ∀ g:i5[X],D (ek g)=ek (diffPoly g)
 powers : ∀ a :PhysicalField,a^p∈constants
 expand : ∀ a :PhysicalField,∃ c:Fin p→ constants,
   a = ∑ i,(c i:PhysicalField)*z^(i:ℕ)
 unit :physicalVal z=1
 residue_guard : ∀ c:constants,¬ physicalVal ((c:PhysicalField) - z)<1
abbrev constantsAlgebra (B:SeedData) (E :Type) [Field E] [Algebra PhysicalField E] :
   Algebra B.constants E :=
 ((algebraMap PhysicalField E).comp B.constants.subtype).toAlgebra
section FixedField
variable (B:SeedData) {E :Type} [Field E] [Algebra PhysicalField E]
local instance :Algebra B.constants E :=constantsAlgebra B E
end FixedField
end
end q85rTDe
end
section
namespace qnyP9Da
noncomputable section
open Polynomial
open P5 (p)
open cu (L)
open qziIa4d (SeedSeries)
def LX:SeedSeries :=HahnSeries.single 1 1
def frobBase {M:Type} [Field M] (ι:SeedSeries[X] →+* M) :Subfield M :=
  Subfield.closure (Set.range (fun a :SeedSeries=>ι (C (a^p))) ∪ {ι Polynomial.X})
def frobRoot {M:Type} [Field M] (ι:SeedSeries[X] →+* M) (r :M) :
    IntermediateField (frobBase ι) M :=
  IntermediateField.adjoin (frobBase ι) {r^p}
def seedField {M:Type} [Field M] (F:Subfield M) (s :M) :IntermediateField F M :=
  IntermediateField.adjoin F {s}
def a8p {M:Type} [Field M] (F:Subfield M) (s :M) :seedField F s :=
  ⟨s,IntermediateField.mem_adjoin_simple_self F s⟩
def PowerExpansion {A:Type} [Field A] (k :ℕ) (π:A) (d:A→A) :Prop :=
  ∀ a :A,∃ b:Fin k→A,
    a = ∑ i,b i^k*π^(i:ℕ) ∧
    d a = ∑ i,b i^k*(i:ℕ)*π^((i:ℕ) - 1)
def SeedExpansion :Prop :=
  (∀ a :SeedSeries,a^p≠LX) ∧
  PowerExpansion p LX (LaurentSeries.derivative L)
def FrobeniusRootData :Prop :=
  SeedExpansion →
  ∀ {M:Type} [Field M] (ι:SeedSeries[X] →+* M),Function.Injective ι →
    ∀ (G:SeedSeries[X][X]) (r :M),G≠0→G.natDegree<p→G.eval₂ ι r=0 →
    let F:=frobRoot ι r
    FiniteDimensional (frobBase ι) F∧Module.finrank (frobBase ι) F≤G.natDegree ∧
    ∃ b:Fin p→F,r = ∑ i,(b i:M)*(ι (C LX))^(i:ℕ)
def FrobeniusOrthogonal:Prop :=
  ∀ {M Γ:Type} [Field M] [LinearOrderedCommGroupWithZero Γ]
    (v :Valuation M Γ) (ι:SeedSeries[X] →+* M),Function.Injective ι →
    (∀ a :SeedSeries,a≠0→v (ι (C a))=1)→v (ι Polynomial.X)<1 →
    (∀ a :SeedSeries,a^p≠LX) →
    ∀ (F:IntermediateField (frobBase ι) M),FiniteDimensional (frobBase ι) F →
      Module.finrank (frobBase ι) F<p →
      ι (C LX)∉F ∧ ∀ (b:Fin p→F) (i:Fin p),
        v (b i:M)≤v (∑ j,(b j:M)*(ι (C LX))^(j:ℕ))
end
end qnyP9Da
end
section
namespace qU1uHGd
noncomputable section
open Polynomial
def an1 {R:Type*} [CommRing R] (F H :R[X]) :R[X][X] :=
  F.derivative.map C+C (Polynomial.X:R[X])*H.map C
def qW {R:Type*} [CommRing R] (F H :R[X]) (d:ℕ) :R[X] :=
  (F.map C).resultant (an1 F H) d d
end
end qU1uHGd
end
