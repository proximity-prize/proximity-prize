import ProximityPrize.SubmissionLower.R6966ProofNearLedgerApply
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineRows
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineLedger
import ProximityPrize.SubmissionLower.R6966ProofWordAxisPrice

set_option Elab.async false

namespace Research6966.NearLedgerWordMethods
open Polynomial Finset NearLedger
open K1 (K I p)
open K1_14 (L FX Equation atX liftPoly graphEval seedEmbedding)
open K1_14_3 (SeedField Surface)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NativeAffineRows (Owned seedPoint)
open scoped Polynomial Differential
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

private theorem constant_power {R : Type*} [Field R] [Differential R] (x : R)
    (fixed : Differential.deriv x=0) (n : ℕ) : Differential.deriv (x^n)=0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Derivation.leibniz,fixed,ih,smul_zero,smul_zero,add_zero]

private theorem constant_pair {R : Type*} [Field R] [Differential R] (x : R) (n : ℕ)
    (fixed : Differential.deriv x=0) (i : Fin 2) :
    Differential.deriv ((![x,x^n] : Fin 2→R) i)=0 := by
  fin_cases i
  · exact fixed
  · exact constant_power x fixed n

private theorem fixed_seed (z : K) (i : Fin 2) : Differential.deriv (seedPoint z i)=0 := by
  apply constant_pair (seedEmbedding z) p _ i
  change Differential.deriv (algebraMap L[X] FX (C (algebraMap K L z)))=0
  rw [GenericPhysicalCentre.physical_poly,derivative_C,map_zero]

private abbrev m : ℕ := 2*wordDegree-1
private abbrev gap : ℕ := agreement-wordDegree
private def fee (a : ℕ) (u : Fin 2→ℕ) := (2*a-1)*(u 0+p*u 1)

private structure Rows (T : Finset K) (a : ℕ) (u : Fin 2→ℕ) where
  good : Finset K
  exceptional : T.card≤good.card+fee a u
  test : I→MvPolynomial (Fin 3) FX
  point : ↥good→Fin 3→FX
  caps : ∀ i z, (test i).degreeOf z≤Fin.cons (α:=fun _ : Fin 3 => ℕ) (yHeight a) (fun z=>m*u z) z
  enough : ∀ z, agreement≤(WordSurfaceMarks.hits (point z) test).card
  shared : ∀ x y, x≠y →
    ((WordSurfaceMarks.hits (point x) test)∩(WordSurfaceMarks.hits (point y) test)).card≤wordDegree

private theorem prepare {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (width : Fin 2→ℕ) (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small : (2*G.graphDegree-1)*width 0<p)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    Nonempty (Rows T G.graphDegree width) := by
  classical
  let val (z : K) (P : Equation) := P.eval₂ (graphEval (M.label z)) (atX (F.scalar z))
  have law z (hz : z∈T) : val z (den N)*atX (F.scalar z).derivative=val z (rhs N) := by
    obtain ⟨q,_,own,mark⟩:=owners z hz
    exact NativeGraphMarks.mark_law N gp own mark
  let bad := T.filter (fun z=>val z (den N)=0)
  let good := T\bad
  have gsub : good⊆T := sdiff_subset
  have nz (z : ↥good) : val z (den N)≠0 := fun zero =>
    (mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨gsub z.property,zero⟩)
  have bad_le := NativeGraphExceptional.singular_count N gp width axes small bad M.label
    (NativeAffineRows.label_inj M).injOn (fun z=>atX (F.scalar z))
    (fun z mem=>(mem_filter.mp mem).2) (by
      intro z mem
      obtain ⟨ht,zero⟩:=mem_filter.mp mem
      have vz:=law z ht
      rw [zero,zero_mul] at vz
      exact vz.symm)
  have size : good.card+bad.card=T.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  let words (z : ↥good) := liftPoly (F.scalar z.val)
  have mark (z : ↥good) := F.mark z.val (sub (gsub z.property))
  have deg (z : ↥good) : (words z).natDegree≤wordDegree := by
    change ((F.scalar z.val).map (algebraMap K L)).natDegree≤wordDegree
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (mark z).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar z.val).natDegree:ℤ)≤131071+M.overhead at bound
      omega
  have distinct : Function.Injective words := fun x z eq => Subtype.ext
    (F.distinct (sub (gsub x.property)) (sub (gsub z.property))
      ((map_injective _ (algebraMap K L).injective) eq))
  let ξ : FX := algebraMap L[X] FX Polynomial.X
  let scalar := algebraMap L FX
  let node (i : I) := scalar (algebraMap K L (K1.node i))
  let recv (i : I) := scalar (algebraMap K L (M.word i))
  let eqn (i : I) : Equation := NonlinearMarkRows.node (den N) (rhs N) wordDegree ξ (node i) (recv i)
  let row (i : I) := OdeSurfaceBridge.coordinates (eqn i)
  let point (z : ↥good) : Fin 3→FX := Fin.cons (atX (F.scalar z.val)) (seedPoint (M.label z.val))
  have detect (z : ↥good) (i : I) :
      MvPolynomial.eval (point z) (row i)=0 ↔ ((words z).map scalar).eval (node i)=recv i := by
    rw [show MvPolynomial.eval (point z) (row i)=
       NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (atX (F.scalar z.val)) (eqn i)
       from OdeSurfaceBridge.read ..]
    have ode : val z.val (den N)*algebraMap L[X] FX (words z).derivative=val z.val (rhs N) := by
      simpa only [words,liftPoly,derivative_map,atX] using law z.val (gsub z.property)
    exact NonlinearMarkRows.detects _ (fixed_seed (M.label z.val)) _ _ (words z) wordDegree (deg z)
      (fun j hj=>K1_14_2_4_2.factorial_ne_zero (hj.trans_lt (by decide : wordDegree<p))) _ _ ode (nz z)
  have caps (i : I) :
      ∀ j, (row i).degreeOf j≤Fin.cons (α:=fun _ : Fin 3=>ℕ) (yHeight G.graphDegree) (fun z=>m*width z) j := by
    obtain ⟨da,db⟩:=NativeGraphMarks.equation_degrees N gp
    have D₁ : (rhs N).natDegree≤G.graphDegree-1+1 := by
      rw [Nat.sub_add_cancel (by omega : 1≤G.graphDegree)]
      exact db
    apply OdeSurfaceBridge.degrees (eqn i) _ _ (NonlinearMarkDegrees.node_ordinate (by omega) da D₁ ..)
    intro z l
    have A := (OdeSurfaceBridge.axis_cap (den N) z (width z)).mpr (fun j=>axes 1 j z)
    have B := (OdeSurfaceBridge.axis_cap (rhs N) z (width z)).mpr
      (fun j=>by simpa [rhs,coeff_neg] using axes 0 j z)
    exact NonlinearMarkDegrees.node_seeds A B wordDegree ξ (node i) (recv i) l
  refine ⟨⟨good,?_,row,point,caps,?_,?_⟩⟩
  · rw [←size]
    exact Nat.add_le_add_left bad_le _
  · intro z
    let b:=mark z
    apply b.bad.agreement.trans (card_le_card _)
    intro i hi
    apply WordSurfaceMarks.hit.mpr ((detect z i).mpr _)
    exact (Polynomial.eval_map_apply scalar _).trans (congrArg scalar
      ((Polynomial.eval_map_apply (algebraMap K L) _).trans (congrArg _ (b.scalar_hits i hi))))
  · exact WordSurfacePrice.word_overlap point row node
      (scalar.injective.comp ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective))
      recv (fun z=>(words z).map scalar) ((map_injective _ scalar.injective).comp distinct)
      wordDegree (fun z=>natDegree_map_le.trans (deg z)) detect

private def keepTwo (seed : Fin 2) : Fin 2↪Fin 3 where
  toFun := Fin.cons 0 (fun _=>seed.succ)
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j
    · rfl
    · exact (Fin.succ_ne_zero seed eq.symm).elim
    · exact (Fin.succ_ne_zero seed eq).elim
    · rfl

private def keepOne : Fin 1↪Fin 3 :=
  ⟨fun _=>0,fun i j _=>Subsingleton.elim i j⟩

private theorem side_large (h : ℕ) :
    WordSurfacePrice.side (Fintype.card I) agreement wordDegree h≤max 1 h*(nodes-wordDegree) := by
  rw [ProximityPrize.Benchmark.IRSProfile.card_index]
  exact NativeAffineLedger.side_ratio (by decide) (by decide)

/-- The actual nonlinear slope graph with one active seed uses two
coordinates in the nodal interpolation, including the initial value. -/
theorem single {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (width : Fin 2→ℕ) (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small : (2*G.graphDegree-1)*width 0<p)
    (active : Fin 2) (inactive : ∀ z, z≠active → width z=0)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    T.card≤(2*G.graphDegree-1)*(width 0+p*width 1)+
      2*yHeight G.graphDegree*max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*
        (nodes-wordDegree)^2/gap^2 := by
  obtain ⟨q⟩:=prepare F sub N gp nonlinear width axes small physical owners
  let y:=yHeight G.graphDegree
  let h : Fin 2→ℕ := Fin.cons y (fun _=>m*width active)
  have selected (i:I) (j:Fin 2) : (q.test i).degreeOf (keepTwo active j)≤h j := by
    fin_cases j
    · exact q.caps i 0
    · exact q.caps i active.succ
  have discarded (i:I) (j:Fin 3) (out:j∉Set.range (keepTwo active)) : (q.test i).degreeOf j=0 := by
    revert out
    refine Fin.cases ?_ (fun z=>?_) j
    · intro out; exact (out ⟨0,rfl⟩).elim
    · intro out
      have ne : z≠active := fun eq=>out ⟨1,by subst z;rfl⟩
      exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ,inactive z ne,Nat.mul_zero] using q.caps i z.succ)
  have count:=WordAxisPrice.two q.point q.test (keepTwo active) h agreement wordDegree
    (by decide) selected discarded q.enough q.shared
  rw [Fintype.card_coe] at count
  have hy : 1≤y:=Nat.le_add_left _ _
  have bycap := side_large y
  rw [max_eq_right hy] at bycap
  have hx : max 1 (m*width active)≤max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1)) := by
    have one : G.graphDegree≠1:=by omega
    fin_cases active
    · change max 1 ((2*wordDegree-1)*width 0)≤_
      simpa only [seedHeight,ite_eq_right one] using
        le_max_left (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))
    · change max 1 ((2*wordDegree-1)*width 1)≤_
      simpa only [seedHeight,ite_eq_right one] using
        le_max_right (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))
  have scaled : q.good.card*gap^2≤
      2*y*max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*(nodes-wordDegree)^2 := by
    refine count.trans ?_
    change 2*WordSurfacePrice.side (Fintype.card I) agreement wordDegree y*
      WordSurfacePrice.side (Fintype.card I) agreement wordDegree (m*width active) ≤ _
    calc
      _ ≤ 2*(y*(nodes-wordDegree))*
          (max (seedHeight G.graphDegree (width 0)) (seedHeight G.graphDegree (width 1))*(nodes-wordDegree)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ bycap)
          ((side_large _).trans (Nat.mul_le_mul_right _ hx))
      _ = _ := by ring
  have good := (Nat.le_div_iff_mul_le (by decide : 0<gap^2)).mpr scaled
  exact q.exceptional.trans ((Nat.add_le_add_right good _).trans_eq (Nat.add_comm _ _))

/-- Seed-independent nonlinear graphs use only the initial-value
coordinate. Their actual differential denominator has no exceptional labels. -/
theorem fixed {u deleted maxHeight} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt agreement M Γ) (sub : T⊆Γ) {parents : Finset Surface}
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) (nonlinear : 2≤G.graphDegree)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z≤0)
    (physical : (131071:ℤ)+M.overhead≤wordDegree) (owners : Owned F T parents N) :
    T.card≤yHeight G.graphDegree*(nodes-wordDegree)/gap := by
  obtain ⟨q⟩:=prepare F sub N gp nonlinear (fun _=>0) axes
    (by simpa only [Nat.mul_zero] using (show (0:ℕ)<p by decide)) physical owners
  let y:=yHeight G.graphDegree
  have discarded (i:I) (j:Fin 3) (out:j∉Set.range keepOne) : (q.test i).degreeOf j=0 := by
    revert out
    refine Fin.cases ?_ (fun z _=>?_) j
    · intro out; exact (out ⟨0,rfl⟩).elim
    · exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ,Nat.mul_zero] using q.caps i z.succ)
  have count:=WordAxisPrice.one q.point q.test keepOne y agreement wordDegree
    (by decide) (fun i=>q.caps i 0) discarded q.enough q.shared
  rw [Fintype.card_coe] at count
  have bycap := side_large y
  have hy : 1≤y := Nat.le_add_left _ _
  rw [max_eq_right hy] at bycap
  have good := (Nat.le_div_iff_mul_le (by decide : 0<gap)).mpr (count.trans bycap)
  have size := q.exceptional
  simp only [fee,Nat.mul_zero,Nat.add_zero] at size
  exact size.trans good

#print axioms single
#print axioms fixed
end
end Research6966.NearLedgerWordMethods
