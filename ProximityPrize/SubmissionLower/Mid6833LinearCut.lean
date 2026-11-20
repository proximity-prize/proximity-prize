/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833RationalSlope
namespace ProximityPrize.SubmissionLower.Genuine6969
open ProximityPrize.Benchmark K6969Global Koala6831Comparison
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet)
open Koala6831BenchmarkField (prime)
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-- On a genuinely hard linear row the rational slope has a pole, its reduced
denominator has degree at least 473, and there is no overflow at infinity. -/
def HardLinear (U : Received F IRSProfile.Index) (E : Finset F) (P : SelectionMap F) (δ : ℕ) : Prop :=
  ∃ a b B L R : F[X], a≠0 ∧ b≠0 ∧ a.natDegree≤δ ∧ b.natDegree≤δ ∧
    L.natDegree≤131071+a.natDegree ∧ ¬a∣L ∧
    (∀G D J : F[X],G≠0 → a=G*D → L=G*J → 473≤D.natDegree) ∧
    a.map σ*R=b*L.map σ ∧ (∀g∈E,a*P g+b*(P g).map σ=B+C g*L+C (σ g)*R) ∧
    ∀g∈E,∀i∈agreementSet Dmn U P g, (a.eval (Dmn i)≠0 ∨ b.eval (Dmn i)≠0) ∧
      a.eval (Dmn i)*U 1 i=L.eval (Dmn i) ∧ b.eval (Dmn i)*σ (U 1 i)=R.eval (Dmn i)

theorem linear_or_small (U : Received F IRSProfile.Index) (E : Finset F)
    (P : SelectionMap F) (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U E P q)
    (bad : Bad Dmn U E P) (linear : combinedDegree q≤1) :
    HardLinear U E P (primitiveExcess 131071 q) ∨ E.card≤214887237245589756 := by
  classical
  obtain ⟨a,b,B,L,R,na,nb,da,db,_,compat,row,point⟩ := GenuineLinearData.actual_coefficients Dmn σ
    Koala6831BenchmarkField.domain_fixed IRSProfile.card_index U E P q h linear
  by_cases nzE : E.Nonempty
  swap
  · right
    simp [Finset.not_nonempty_iff_eq_empty.mp nzE]
  obtain ⟨g,hg⟩ := nzE
  by_cases high : 131071+a.natDegree<L.natDegree
  · right
    exact (overflow_count σ prime 131071 (by decide) Koala6831BenchmarkField.frobenius_apply a b B L R na nb compat
      high E P h.selection.degree_le row).trans (by decide)
  have no : ¬∃V : F[X],V.natDegree≤131071 ∧ a*V=L := by
    rintro ⟨V,dv,eq⟩
    exact bad g hg (Frontier.LinearKernel.polynomial_slope_joint σ Dmn (U 0) (U 1)
      (agreementSet Dmn U P g) 131071 g (P g) V a b L R na (h.selection.degree_le g hg) dv compat eq
      (fun i hi => eval_eq_of_mem_agreementSet hi) (fun i _ => Koala6831BenchmarkField.domain_fixed i)
      (fun i hi => (point g hg i hi).1) (fun i hi => (point g hg i hi).2))
  have nd : ¬ a∣L := by
    rintro ⟨V,eq⟩
    apply no
    refine ⟨V,?_,eq.symm⟩
    by_cases z : V=0
    · simp [z]
    rw [eq,natDegree_mul na z] at high
    omega
  by_cases hard : ∀G D J : F[X],G≠0 → a=G*D → L=G*J → 473≤D.natDegree
  · left
    exact ⟨a,b,B,L,R,na,nb,da,db,by omega,nd,hard,compat,row,point⟩
  right
  push Not at hard
  obtain ⟨G,D,J,nG,aa,ll,small⟩ := hard
  have nD : D≠0 := fun z => na (by simp [aa,z])
  have nJ : J≠0 := fun z => nd (by simp [ll,z])
  rw [aa,ll,natDegree_mul nG nD,natDegree_mul nG nJ] at high
  apply small_denominator_count U E P h.selection D J (by omega) (by omega)
  · intro k hk i hi
    obtain ⟨act,left,right⟩ := point k hk i hi
    exact cancel_slope_at_node σ (Dmn i) (U 1 i) (Koala6831BenchmarkField.domain_fixed i)
      a b L R G D J nG aa ll compat act left right
  rintro ⟨V,dv,eq⟩
  exact nd ⟨V,by rw [ll,aa,←eq,mul_assoc]⟩

#print axioms linear_or_small
end
end ProximityPrize.SubmissionLower.Genuine6969
