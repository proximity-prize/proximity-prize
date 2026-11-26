import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960CollisionTameBranchFrame
set_option Elab.async false


set_option Elab.async false

namespace Research6966.FixedNodeTariff
open Polynomial Finset Module WordSurfaceMarks
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
variable {K I ι:Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype ι]

/-- Count all marked words from their regular agreement nodes. The
per-word polynomial controls which nodes are regular. Each individual
node is priced in the two-seed plane, with the sharp total-degree constant. -/
theorem count (p:ι→Fin 2→K) (words:ι→K[X]) (distinct:Function.Injective words)
    (nodes:I→K) (inj:Function.Injective nodes) (received:I→K)
    (A B:FixedNodeRows.Row (Fin 2) K) (d u a singular:ℕ)
    (ha:∀ i,(A.coeff i).totalDegree≤u) (hb:∀ i,(B.coeff i).totalDegree≤u)
    (fac:∀ j≤d,(j.factorial:K)≠0) (gap:d<a) (deg:∀ z,(words z).natDegree≤d)
    (law:∀ z,FixedNodeRows.evaluate (p z) (words z) A*(words z).derivative=FixedNodeRows.evaluate (p z) (words z) B)
    (enough:∀ z,∃ T:Finset I,a≤T.card ∧ ∀i∈T,(words z).eval (nodes i)=received i)
    (witness:∀ z,∃ S:K[X],S≠0 ∧ S.natDegree≤singular ∧ ∀i,S.eval (nodes i)≠0 →
      (FixedNodeRows.evaluate (p z) (words z) A).eval (nodes i)≠0) :
    Fintype.card ι*(a-singular) ≤ Fintype.card I*
      ((((Fintype.card I-a)*((2*d-1)*u)+(a-d))^2)/(a-d)^2) := by
  classical
  let reg (z:ι) (i:I):Prop := (words z).eval (nodes i)=received i ∧
    (FixedNodeRows.evaluate (p z) (words z) A).eval (nodes i)≠0
  let good (i:I):=univ.filter (fun z=>reg z i)
  let price:=(((Fintype.card I-a)*((2*d-1)*u)+(a-d))^2)/(a-d)^2
  have column (i:I):(good i).card≤price := by
    let cut (j:I):=FixedNodeRows.test A B d (nodes i) (received i) (nodes j) (received j)
    let pp (z:↥(good i)):=p z.val
    have hitTest (z:↥(good i)) (j:I):MvPolynomial.eval (pp z) (cut j)=0 ↔
        (words z.val).eval (nodes j)=received j := by
      have t:reg z.val i:=(mem_filter.mp z.property).2
      exact FixedNodeRows.test_detects _ _ _ _ _ _ t.1 _ _ (law z) t.2 _ (deg z) fac
    have height (j:I):cut j∈MvPolynomial.restrictWeightAtMost (fun _:Fin 2=>1) ((2*d-1)*u) := by
      apply MvPolynomial.mem_restrictWeightAtMost.mpr
      intro e he
      have b:=MvPolynomial.le_totalDegree he
      have eq:e.weight (fun _:Fin 2=>1)=e.degree := by rw [Finsupp.degree_eq_weight_one]
      rw [eq]
      exact b.trans (FixedNodeRows.test_degree A B d u _ _ _ _ ha hb)
    have bound:=WordUnconstrainedPrice.plane pp cut ((2*d-1)*u) a d gap height (by
      intro z
      obtain ⟨T,size,hits⟩:=enough z.val
      exact size.trans (card_le_card (fun j mem=>hit.mpr ((hitTest z j).mpr (hits j mem)))))
      (WordSurfacePrice.word_overlap pp cut nodes inj received (fun z=>words z.val)
        (distinct.comp Subtype.val_injective) d (fun z=>deg z.val) hitTest)
    apply (Nat.le_div_iff_mul_le (pow_pos (by omega : 0<a-d) 2)).mpr
    simpa only [Fintype.card_coe] using bound
  have row (z:ι):a-singular≤(univ.filter (reg z)).card := by
    obtain ⟨T,size,agree⟩:=enough z
    obtain ⟨S,sn,sd,regular⟩:=witness z
    have hits:=QuadraticWeight.regular_hits nodes inj T S sn
    have sub:T.filter (fun i=>S.eval (nodes i)≠0)⊆univ.filter (reg z) := by
      intro i hi
      obtain ⟨mem,unit⟩:=mem_filter.mp hi
      exact mem_filter.mpr ⟨mem_univ _,agree i mem,regular i unit⟩
    have cnt:=card_le_card sub
    omega
  have balance:(∑ z:ι,(univ.filter (reg z)).card)=(∑ i:I,(good i).card) := by
    simp only [good,card_filter];rw [sum_comm]
  have left:=sum_le_sum (s:=univ) (fun z _=>row z)
  have right:=sum_le_sum (s:=univ) (fun i _=>column i)
  rw [balance] at left
  simpa only [sum_const,card_univ,smul_eq_mul] using left.trans right

#print axioms count
end
end Research6966.FixedNodeTariff
