import ProximityPrize.SubmissionLower.R6960RetainedLinearConjugacy

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private def linearAt (B A : E[X]) : Plane E := C B*Polynomial.X-C A

private theorem map_linearAt (B A : E[X]) (r : Fn E) (ha : incl E A=incl E B*r) :
    (linearAt B A).map (incl E)=C (incl E B)*(Polynomial.X-C r) := by
  simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    ha,C_mul,mul_sub]

private theorem mapped_all (B : E[X]) (A : Fn E→E[X]) (s : Multiset (Fn E))
    (h : ∀ r∈s,incl E (A r)=incl E B*r) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (incl E)=C ((incl E B)^s.card) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have rest := ih (fun a ha=>(h a (Multiset.mem_cons_of_mem ha)))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,map_linearAt B _ r hr,
      rest,Multiset.card_cons,pow_succ,C_mul]
    ring

private theorem specialized_all (B : E[X]) (A : Fn E→E[X]) (s : Multiset (Fn E)) (x t : E)
    (h : ∀ r∈s,(A r).eval x=B.eval x*t) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (evalRingHom x)=
      C ((B.eval x)^s.card)*(Polynomial.X-C t)^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have first : (linearAt B (A r)).map (evalRingHom x)=C (B.eval x)*(Polynomial.X-C t) := by
      simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
        Polynomial.map_X,coe_evalRingHom,hr,C_mul,mul_sub]
    have rest := ih (fun a ha=>h a (Multiset.mem_cons_of_mem ha))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,first,rest,
      Multiset.card_cons,pow_succ,C_mul]
    ring

/-- An irreducible plane polynomial which splits into rational abscissa
branches over algebraic constants has a pure received fibre at every
arithmetic node at which the received ordinate is a root. -/
theorem pure_specialization [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree) (splits : (geometric (E:=E) P).Splits)
    (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    P.map (evalRingHom x)=C (P.map (evalRingHom x)).leadingCoeff*(Polynomial.X-C t)^P.natDegree := by
  classical
  let G := geometric (E:=E) P
  let roots := G.roots
  let Q := P.map (constants (F:=F) (E:=E))
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let atX := evalRingHom x'
  let degree := P.natDegree
  have lifts : Q.map (incl E)=G := by
    simp [Q,G,geometric,base,Polynomial.map_map]
  have d : roots.card=degree := splits.natDegree_eq_card_roots.symm.trans (geometric_deg P)
  obtain ⟨b,hb,numerators⟩ := common_numerators (E:=E) ir pos splits x t hit
  let B := constants (E:=E) b
  let A (r : Fn E) : E[X] := if h : r∈roots then (numerators r h).choose else 0
  have den : B.eval x'≠0 := by rw [eval_constants]; exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hb
  have both (r : Fn E) (h : r∈roots) :
      incl E (A r)=incl E B*r ∧ (A r).eval x'=B.eval x'*t' := by
    simpa only [A,dite_eq_left h,eval_constants,x',t',B,base,RingHom.comp_apply] using
      (numerators r h).choose_spec
  let H := (roots.map (fun r=>linearAt B (A r))).prod
  have shape : H.map (incl E)=C ((incl E B)^degree)*(roots.map (fun r=>Polynomial.X-C r)).prod := by
    rw [mapped_all B A roots (fun r hr=>(both r hr).1),d]
  have fibre : H.map atX=C ((B.eval x')^degree)*(Polynomial.X-C t')^degree := by
    rw [specialized_all B A roots x' t' (fun r hr=>(both r hr).2),d]
  have lead : incl E Q.leadingCoeff=G.leadingCoeff := by
    rw [← lifts, leadingCoeff_map_of_injective (incl_injective E)]
  have packed : C (B^degree)*Q=C Q.leadingCoeff*H := by
    apply Polynomial.map_injective _ (incl_injective E)
    rw [Polynomial.map_mul,Polynomial.map_C,map_pow,lifts,Polynomial.map_mul,Polynomial.map_C,lead,shape]
    calc
      C ((incl E B)^degree)*G =
          C ((incl E B)^degree)*(C G.leadingCoeff*(roots.map (fun r=>Polynomial.X-C r)).prod) :=
        congrArg _ splits.eq_prod_roots
      _ = _ := by ring
  have mapped := congrArg (Polynomial.map atX) packed
  simp only [Polynomial.map_mul,Polynomial.map_C,atX,coe_evalRingHom,eval_pow] at mapped
  change C ((B.eval x')^degree)*(Q.map atX)=C (Q.leadingCoeff.eval x')*(H.map atX) at mapped
  rw [fibre] at mapped
  have qeq : Q.map atX=C (Q.leadingCoeff.eval x')*(Polynomial.X-C t')^degree := by
    apply mul_left_cancel₀ (a:=C ((B.eval x')^degree)) (C_ne_zero.mpr (pow_ne_zero _ den))
    calc
      _ = C (Q.leadingCoeff.eval x')*(C ((B.eval x')^degree)*(Polynomial.X-C t')^degree) := mapped
      _ = _ := by ring
  have lead_eq : (Q.map atX).leadingCoeff=Q.leadingCoeff.eval x' := by
    have monic : ((Polynomial.X-C t')^degree).Monic := (monic_X_sub_C t').pow _
    rw [qeq,leadingCoeff_mul,leadingCoeff_C,monic.leadingCoeff,mul_one]
  rw [← lead_eq] at qeq
  have recover : Q.map atX=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Q,atX,coeff_map,coe_evalRingHom,eval_constants,x']
  apply Polynomial.map_injective _ (algebraMap F E).injective
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,← leadingCoeff_map_of_injective (algebraMap F E).injective,← recover]
  exact qeq

#print axioms pure_specialization
end
end Lower6960.RetainedLinear
