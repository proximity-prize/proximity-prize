import ProximityPrize.SubmissionLower.R6966ProofPadeNativeQuotient
import ProximityPrize.SubmissionLower.PortHighFinish
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

set_option Elab.async false

namespace Research6966.NativeGraphMarks
open Polynomial Finset
open K1_14 (Jet Equation Seeds FX graphEval atX)
open K1_14_3 (SeedField SeedClosure Parent Surface OnSeedFibre)
open PadeNativeQuotient (Native)
open scoped Polynomial
open scoped Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

private abbrev f:=algebraMap SeedField SeedClosure

private def evalPair (y v:SeedClosure) : SeedClosure[X][X]→+*SeedClosure :=
  eval₂RingHom (evalRingHom y) v

private theorem eval_fibre (y v:SeedClosure) :
    (evalPair y v).comp (K1_14_1_4.doubleMap K1_14_3.seedGeneric)=K1_14_3.seedFibreEval y v := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c;simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]
    · simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]
  · simp [evalPair,K1_14_1_4.doubleMap,K1_14_3.seedFibreEval]

theorem owner_iff {G:Pade.Row SeedField} (N:Native G) {q:Surface} {y v:SeedClosure} (onq:OnSeedFibre q y v) :
    N.poly∈q.asIdeal ↔ (G.map f).a.eval y*v=(G.map f).b.eval y := by
  rw [←onq,RingHom.mem_ker,←eval_fibre]
  change evalPair y v (K1_14_3.fibreRow N.poly)=0 ↔ _
  rw [N.eq,map_mul]
  have c:evalPair y v (K1_14_1.jetConstant N.scalar)=N.scalar:=by
    simp [evalPair,K1_14_1.jetConstant]
  rw [c,mul_eq_zero,or_iff_right N.nonzero,Pade.Row.polynomial]
  simpa only [evalPair,coe_eval₂RingHom,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X,coe_evalRingHom]
    using (sub_eq_zero : (G.map f).a.eval y*v-(G.map f).b.eval y=0 ↔ _)

/-- The partition in the leaf ledger uses actual ideal membership. Its
rejected parents collectively own at most c-a distinct ordinates. -/
theorem off_owner {G:Pade.Row SeedField} (N:Native G) {parents:Finset Surface}
    (geo:∀ q∈parents,Parent q) {c:ℕ}
    (controls:Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets parents) c)
    (nonempty:(parents.filter (fun q=>N.poly∉q.asIdeal)).Nonempty) :
    ∃ P:Equation,K1_14_3.ProjectedProduct (parents.filter (fun q=>N.poly∉q.asIdeal)) P ∧
      P.natDegree+G.graphDegree≤c := by
  classical
  let S:=parents.filter (fun q=>N.poly∉q.asIdeal)
  have sub:S⊆parents:=filter_subset _ _
  apply Pade.Native.off_graph_product sub nonempty (fun q hq=>geo q (sub hq)) G c controls
  intro y v sheet equality
  obtain ⟨q,mem,onq⟩:=(Pade.Native.sheets_iff ..).mp sheet
  let emb:=(separableClosure SeedField SeedClosure).val
  have lift (P:SeedField[X]):(P.map f).eval (y:SeedClosure)=emb ((P.map (algebraMap SeedField Pade.Native.Sep)).eval y) := by
    calc
      _ = aeval (emb y) P := by rw [eval_map];rfl
      _ = emb (aeval y P) := Polynomial.aeval_algHom_apply emb y P
      _ = _ := by rw [eval_map];rfl
  have eq' := congrArg emb equality
  have hit:(G.map f).a.eval (y:SeedClosure)*(v:SeedClosure)=(G.map f).b.eval (y:SeedClosure) := by
    change (G.a.map f).eval _*_=(G.b.map f).eval _
    rw [lift,lift]
    exact (map_mul emb _ _).symm.trans eq'
  exact (mem_filter.mp mem).2 ((owner_iff N onq).mpr hit)

theorem slope_degree {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) : N.poly.natDegree=1 := by
  have mapInj:=map_injective K1_14_3.seedGeneric (f.injective.comp (IsFractionRing.injective Seeds SeedField))
  have top:(K1_14_3.fibreRow N.poly).natDegree=N.poly.natDegree :=
    natDegree_map_eq_of_injective (f:=mapRingHom K1_14_3.seedGeneric) mapInj N.poly
  rw [←top,N.eq]
  change (K1_14_1.jetConstant N.scalar*(G.map f).polynomial).natDegree=1
  rw [natDegree_mul (show (K1_14_1.jetConstant N.scalar:SeedClosure[X][X])≠0 from
    C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne ((G.primitive_map f).mpr gp)),
    (G.map f).slope_degree ((G.primitive_map f).mpr gp)]
  simp [K1_14_1.jetConstant]

theorem mark_law {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) {q:Surface} {label:K1.K}
    {word:Polynomial K1.K} (owns:N.poly∈q.asIdeal) (mark:∀ P∈q.asIdeal,K1_14.jetAt P label word=0) :
    (N.poly.coeff 1).eval₂ (graphEval label) (atX word)*atX word.derivative =
      (-N.poly.coeff 0).eval₂ (graphEval label) (atX word) := by
  have law:=mark N.poly owns
  let z:=graphEval label
  let y:=atX word
  let v:=atX word.derivative
  change eval₂RingHom (eval₂RingHom z y) v N.poly=0 at law
  have eq:=Polynomial.eq_X_add_C_of_natDegree_le_one (slope_degree N gp).le
  have evaluated:=congrArg (eval₂RingHom (eval₂RingHom z y) v) eq
  change _ = _ at evaluated
  simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X] at evaluated
  change (N.poly.coeff 1).eval₂ z y*v=(-N.poly.coeff 0).eval₂ z y
  rw [eval₂_neg]
  apply eq_neg_of_add_eq_zero_left
  exact evaluated.symm.trans law

#print axioms owner_iff
#print axioms off_owner
#print axioms mark_law

theorem equation_degrees {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    (N.poly.coeff 1).natDegree≤G.graphDegree-1 ∧ (-N.poly.coeff 0).natDegree≤G.graphDegree := by
  let deg:=G.graphDegree
  have gn:=(G.primitive_map f).mpr gp
  have total:Pade.totalJet (K1_14_3.fibreRow N.poly)=deg := by
    rw [N.eq]
    change Pade.totalJet (K1_14_1.jetConstant N.scalar*(G.map f).polynomial)=deg
    rw [Pade.totalJet_mul (show (K1_14_1.jetConstant N.scalar:SeedClosure[X][X])≠0 from
      C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne gn),
      (G.map f).total_polynomial gn,Pade.Row.degree_map]
    have zero:Pade.totalJet (K1_14_1.jetConstant N.scalar)=0 := Nat.eq_zero_of_le_zero
      ((Pade.totalJet_le _ 0).mpr (by
        intro j i ne
        by_cases j0:j=0
        · subst j;by_cases i0:i=0
          · omega
          · exact False.elim (ne (by simp [K1_14_1.jetConstant,coeff_C,i0]))
        · exact False.elim (ne (by simp [K1_14_1.jetConstant,coeff_C,j0]))))
    rw [zero,zero_add]
  have support (j i:ℕ) (ne:(N.poly.coeff j).coeff i≠0):i+j≤deg := by
    apply (Pade.totalJet_le _ deg).mp total.le
    simp only [K1_14_3.fibreRow,coeff_map,coe_mapRingHom]
    exact (map_ne_zero_iff K1_14_3.seedGeneric (f.injective.comp (IsFractionRing.injective Seeds SeedField))).mpr ne
  have cap (j:ℕ): (N.poly.coeff j).natDegree≤deg-j := by
    by_cases zero:N.poly.coeff j=0
    · simp [zero]
    have spent:=support j _ (show (N.poly.coeff j).coeff (N.poly.coeff j).natDegree≠0 from by
      rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr zero)
    omega
  exact ⟨cap 1,by simpa using cap 0⟩

#print axioms equation_degrees
end
end Research6966.NativeGraphMarks
