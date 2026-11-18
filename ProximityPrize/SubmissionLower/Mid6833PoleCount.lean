/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833FixedPoles
import ProximityPrize.SubmissionLower.Mid6833LineProjection

namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open Koala6831Moving (affineDenominator)
open K6969Global (RetainedComparison)
open Koala6831BenchmarkField (prime)
open Koala6831BenchmarkPrimitive (Received SelectionMap)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1500000
variable {K I : Type} [Field K] [Fintype I]

/-- If the specialized denominator vanishes while its determinant is nonzero,
the value of the normalized polynomial at that pole identifies its seed. -/
private theorem pole_injection (α : K) (d : K[X]) (A C' : Fin 2 → K[X]) (S : Finset K)
    (P T : K → K[X]) (pole : d.eval α=0)
    (neq : (A 0*C' 1-A 1*C' 0).eval α ≠ 0)
    (row : ∀ g∈S, d*P g+affineDenominator (C' 0) (C' 1) g=affineDenominator (A 0) (A 1) g*T g) :
    Function.Injective (fun g : S => (T g).eval α) := by
  intro g h same
  apply Subtype.ext
  have gval := congrArg (Polynomial.eval α) (row g g.property)
  have hval := congrArg (Polynomial.eval α) (row h h.property)
  simp only [affineDenominator,eval_add,eval_mul,eval_C,pole,zero_mul,zero_add] at gval hval
  change (T g).eval α=(T h).eval α at same
  rw [←same] at hval
  apply sub_eq_zero.mp
  suffices z : ((g:K)-(h:K))*(A 0*C' 1-A 1*C' 0).eval α = 0 by exact (mul_eq_zero.mp z).resolve_right neq
  simp only [eval_sub,eval_mul]
  linear_combination ((A 0).eval α+(h:K)*(A 1).eval α)*gval -
    ((A 0).eval α+(g:K)*(A 1).eval α)*hval

/-- Agreement and a fixed-field linear pole with incompatible residues give at
most p seeds after the usual normalization cleanup. -/
theorem fixed_pole_count (x : I ↪ K) (σ : K →+* K) (fixed : ∀ i, σ (x i)=x i)
    (hσ : ∀ a, σ a = a^prime)
    (U : Received K I) (E : Finset K) (P : SelectionMap K) (q : SymbolicRow (Seeds K))
    (h : RetainedComparison x σ U E P q)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) (short : primitiveExcess 131071 q ≤ 12136)
    (α : K) (hx : σ α=α) (pole : N.d₀.eval α=0)
    (neq : (N.A 0*N.C 1-N.A 1*N.C 0).eval α ≠ 0) :
    E.card ≤ prime+(Fintype.card I+1+(prime+1)*primitiveExcess 131071 q) := by
  classical
  obtain ⟨S,sub,card,T,v,fit⟩ := retained_solutions x σ fixed U E P q h N short
  suffices S.card≤prime by omega
  have inj := pole_injection α N.d₀ N.A N.C S P T pole neq (fun g hg => (fit g hg).2.1)
  by_cases nonempty : S.Nonempty
  · obtain ⟨r,hr⟩ := nonempty
    let s : ↥S := ⟨r,hr⟩
    by_cases varies : ∃ g : S, T g ≠ T s
    · have na : N.A 0≠0 ∨ N.A 1≠0 := by
        by_contra! z
        simp [z] at neq
      obtain ⟨j,jn⟩ : ∃ j, N.A j ≠ 0 := na.elim (fun h=>⟨0,h⟩) (fun h=>⟨1,h⟩)
      let L := N.d₁*(N.A j).map σ
      let R := N.d₀.map σ*N.B j
      have ln : L≠0 := mul_ne_zero N.d₁_ne (Polynomial.map_ne_zero jn)
      obtain ⟨H,Q,w,hn,hs,units,factor,_⟩ := KoalaFrontier.normalized_affine_family σ
        L R (fun g : S => T g) s (fun _ : Unit => α) (fun _ => (0:K)) (fun _=>hx) ln
        (offset σ N j) (fun g => by linear_combination (fit g g.property).2.2.2 j) varies
      let f : S → K := fun g => (Q g).eval α
      have finj : Function.Injective f := by
        intro a b same
        apply inj
        have av := congrArg (Polynomial.eval α) (factor a).2
        have bv := congrArg (Polynomial.eval α) (factor b).2
        simp only [eval_sub,eval_mul] at av bv
        change (Q a).eval α = (Q b).eval α at same
        rw [same] at av
        linear_combination av-bv
      let values := univ.image f
      have fixv : ∀ t∈values, σ t=t := by
        intro t ht
        obtain ⟨g,_,rfl⟩ := mem_image.mp ht
        have ev := eval_map_apply (p:=Q g) σ α
        simpa only [hx,(factor g).1,f] using ev.symm
      have n := Frontier6969.Projection.prime_line σ prime (by decide) hσ values 1 1
        one_ne_zero one_ne_zero (by intro t ht;simpa only [mul_one,map_one,fixv t ht])
      simpa only [values,card_image_of_injective _ finj,card_univ,Fintype.card_coe] using n
    · have small : S.card≤1 := card_le_one.mpr (by
        intro a ha b hb
        have eq (g : S) : T g = T s := by_contra (fun ne => varies ⟨g,ne⟩)
        have cc : (⟨a,ha⟩ : S) = ⟨b,hb⟩ := inj (congrArg (Polynomial.eval α) ((eq ⟨a,ha⟩).trans (eq ⟨b,hb⟩).symm))
        exact congrArg Subtype.val cc)
      exact small.trans (by decide)
  · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

#print axioms fixed_pole_count
end
end Frontier6969.GenuineMoving
