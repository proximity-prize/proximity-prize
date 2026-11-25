import ProximityPrize.SubmissionLower.R6966ProofNonlinearMarkDegrees
import ProximityPrize.SubmissionLower.R6966ProofWordSurfacePrice
import Mathlib.Algebra.MvPolynomial.Equiv

set_option Elab.async false

namespace Research6966.OdeSurfaceBridge
open Polynomial Finset
open WordSurfaceJets (Pol)
open NonlinearMarkRows (Eqn evaluate)
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 700000

variable {F:Type*} [Field F]
def coordinates (P:Eqn (Fin 2) F) : Pol (Fin 3) F:=(MvPolynomial.finSuccEquiv F 2).symm P

theorem read (P:Eqn (Fin 2) F) (p:Fin 2→F) (y:F) :
    MvPolynomial.eval (Fin.cons y p) (coordinates P)=evaluate p y P := by
  rw [MvPolynomial.eval_eq_eval_mv_eval']
  simp only [coordinates,AlgEquiv.apply_symm_apply,eval_map]
  rfl

theorem degrees (P:Eqn (Fin 2) F) (b:ℕ) (u:Fin 2→ℕ) (bound:P.natDegree≤b)
    (seed:∀ z,NonlinearMarkDegrees.cap (Pi.single z 1) (u z) P) :
    ∀ i,(coordinates P).degreeOf i≤Fin.cons (α:=fun _:Fin 3=>ℕ) b u i := by
  classical
  have coef (e:Fin 3→₀ℕ): (coordinates P).coeff e=(P.coeff (e 0)).coeff e.tail := by
    rw [←Finsupp.cons_tail e,←MvPolynomial.finSuccEquiv_coeff_coeff]
    simp [coordinates]
  intro i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have active: (P.coeff (e 0)).coeff e.tail ≠0:=coef e ▸ MvPolynomial.mem_support_iff.mp he
  refine Fin.cases ?_ (fun z=>?_) i
  · have live:P.coeff (e 0)≠0:=fun eq=>active (by rw [eq,MvPolynomial.coeff_zero];rfl)
    exact (le_natDegree_of_ne_zero live).trans bound
  · have v:=MvPolynomial.mem_restrictWeightAtMost.mp (seed z (e 0)) e.tail (MvPolynomial.mem_support_iff.mpr active)
    rwa [Finsupp.weight_single_one_apply] at v

theorem axis_cap (P:Eqn (Fin 2) F) (z:Fin 2) (u:ℕ) :
    NonlinearMarkDegrees.cap (Pi.single z 1) u P ↔ ∀ j,(P.coeff j).degreeOf z≤u := by
  simp only [NonlinearMarkDegrees.cap,MvPolynomial.mem_restrictWeightAtMost,Finsupp.weight_single_one_apply,
    MvPolynomial.degreeOf_le_iff]

variable {K ι I:Type*} [Field K] [Fintype ι] [Fintype I] [DecidableEq I]
private abbrev E:=GenericPhysicalCentre.Frac K
private abbrev scalar:=algebraMap K (E (K:=K))
private abbrev physical:=algebraMap K[X] (E (K:=K))

/-- The surface tariff on genuine polynomial solutions of a slope-linear
ODE. Its node equations are constructed from the derivatives at the generic
physical centre. The nodal tests, their individual degrees and the common
surface are all proved for this concrete construction. -/
theorem regular (params:ι→Fin 2→E (K:=K)) (fixed:∀ z i,Differential.deriv (params z i)=0)
    (A B H:Eqn (Fin 2) E) (Hnz:H≠0) (r d sy agreement:ℕ) (u v:Fin 2→ℕ)
    (rp:1≤r) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1) (hy:H.natDegree≤sy)
    (az:∀ z j,(A.coeff j).degreeOf z≤u z) (bz:∀ z j,(B.coeff j).degreeOf z≤u z)
    (hz:∀ z j,(H.coeff j).degreeOf z≤v z)
    (words:ι→K[X]) (unique:Function.Injective words) (degree:∀ z,(words z).natDegree≤d)
    (law:∀ z,evaluate (params z) (physical (words z)) A*physical (words z).derivative=
      evaluate (params z) (physical (words z)) B)
    (den:∀ z,evaluate (params z) (physical (words z)) A≠0)
    (surface:∀ z,evaluate (params z) (physical (words z)) H=0)
    (nodes:I→K) (distinct:Function.Injective nodes) (received:I→K)
    (fac:∀ j≤d,(j.factorial:E (K:=K))≠0) (gap:d<agreement)
    (hitCount:∀ z,∃ T:Finset I,agreement≤T.card ∧ ∀ i∈T,(words z).eval (nodes i)=received i) :
    let m:=2*d-1
    let h₀:=max 1 (m*u 0)
    let h₁:=max 1 (m*u 1)
    let hY:=m*r+1
    let side:=WordSurfacePrice.side (Fintype.card I) agreement d
    Fintype.card ι*(agreement-d)^2 ≤ 2*(sy*side h₀*side h₁+v 0*side hY*side h₁+v 1*side hY*side h₀) := by
  classical
  let m:=2*d-1
  let h:Fin 2→ℕ:=fun z=>max 1 (m*u z)
  let heights:=Fin.cons (α:=fun _:Fin 3=>ℕ) (m*r+1) h
  let xi:E (K:=K):=physical (Polynomial.X:K[X])
  let eqn (i:I):=NonlinearMarkRows.node A B d xi (scalar (nodes i)) (scalar (received i))
  let row (i:I):=coordinates (eqn i)
  let point (z:ι):=Fin.cons (α:=fun _:Fin 3=>E (K:=K)) (physical (words z)) (params z)
  let word (z:ι):=(words z).map scalar
  have inject:Function.Injective (scalar (K:=K)) := (algebraMap K (E (K:=K))).injective
  have hs:∀ z i,MvPolynomial.eval (point z) (row i)=0 ↔ (word z).eval (scalar (nodes i))=scalar (received i) := by
    intro z i
    rw [show MvPolynomial.eval (point z) (row i)=evaluate (params z) (physical (words z)) (eqn i) from read ..]
    exact NonlinearMarkRows.detects _ (fixed z) _ _ (words z) d (degree z) fac _ _ (law z) (den z)
  have caps (i:I) (j:Fin 3):(row i).degreeOf j≤heights j := by
    apply degrees (eqn i) _ h (NonlinearMarkDegrees.node_ordinate rp ay byDeg ..)
    intro z l
    exact MvPolynomial.restrictWeightAtMost_mono _ (le_max_right 1 (m*u z))
      (NonlinearMarkDegrees.node_seeds ((axis_cap ..).mpr (az z)) ((axis_cap ..).mpr (bz z)) d xi
        (scalar (nodes i)) (scalar (received i)) l)
  have count:=WordSurfacePrice.count_words point row (coordinates H)
    ((map_ne_zero_iff _ (MvPolynomial.finSuccEquiv (E (K:=K)) 2).symm.injective).mpr Hnz)
    (fun z=>(read ..).trans (surface z)) (Fin.cons (α:=fun _:Fin 3=>ℕ) sy v) heights
    (degrees H sy v hy (fun z=>(axis_cap ..).mpr (hz z)))
    caps (fun i=>scalar (nodes i)) (inject.comp distinct) (fun i=>scalar (received i))
    word ((map_injective _ inject).comp unique) agreement d gap
    (fun z=>natDegree_map_le.trans (degree z)) hs (by
      intro z
      obtain ⟨T,enough,hit⟩:=hitCount z
      apply enough.trans (card_le_card _)
      intro i mem
      apply WordSurfaceMarks.hit.mpr ((hs z i).mpr _)
      exact (Polynomial.eval_map_apply scalar _).trans (congrArg scalar (hit i mem)))
  exact count

#print axioms degrees
#print axioms regular
end
end Research6966.OdeSurfaceBridge
