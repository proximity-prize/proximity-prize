import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_WeightedSimplex
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_WeightAtMost
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_MvPolynomial_WeightedOrder
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_NoZeroDivisors
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Polynomial
import ProximityPrize.SubmissionLower.LibraryMathlib_FieldTheory_Galois_Infinite
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Finite_Quotient
import ProximityPrize.SubmissionLower.R6966ProofGenericPhysicalCentre

section Merged6967_R6960LineEulerPolynomial
set_option Elab.async false





set_option Elab.async false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open Polynomial Module Submodule
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- For a square polynomial matrix of nonzero determinant, its cokernel
has finite dimension over the coefficient field, equal to the degree of
the determinant. -/
theorem polynomial_cokernel (A : Matrix ι ι (Polynomial k)) (nonzero : A.det≠0) :
    FiniteDimensional k ((ι→(Polynomial k)) ⧸ LinearMap.range (Matrix.toLin' A)) ∧
    Module.finrank k ((ι→(Polynomial k)) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natDegree := by
  let f := Matrix.toLin' A
  let N := LinearMap.range f
  have inj : Function.Injective f :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr nonzero)
  let e : (ι→(Polynomial k)) ≃ₗ[(Polynomial k)] N := LinearEquiv.ofInjective f inj
  have rank : Module.finrank (Polynomial k) N = Module.finrank (Polynomial k) (ι→(Polynomial k)) := e.finrank_eq.symm
  let b := Pi.basisFun (Polynomial k) ι
  let top := smithNormalFormTopBasis b rank
  let bot := smithNormalFormBotBasis b rank
  let a := smithNormalFormCoeffs b rank
  have anz (i : ι) : a i≠0 := smithNormalFormCoeffs_ne_zero b rank i
  let e' : (ι→(Polynomial k)) ≃ₗ[(Polynomial k)] N := top.equiv bot (Equiv.refl ι)
  let g : (ι→(Polynomial k)) →ₗ[(Polynomial k)] (ι→(Polynomial k)) := N.subtype ∘ₗ e'.toLinearMap
  have comp : N.subtype ∘ₗ e.toLinearMap = f := by ext x; rfl
  have asso := LinearMap.associated_det_comp_equiv N.subtype e e'
  rw [comp] at asso
  change Associated (LinearMap.det f) (LinearMap.det g) at asso
  have mat : LinearMap.toMatrix top top g = Matrix.diagonal a := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply]
    change top.repr (↑(e' (top j)) : ι→(Polynomial k)) i = _
    have ej : (↑(e' (top j)) : ι→(Polynomial k))=a j • top j := calc
      _ = ↑(bot j) := congrArg Subtype.val (Basis.equiv_apply (b:=top) (b':=bot) (e:=Equiv.refl ι) (i:=j))
      _ = _ := smithNormalFormBotBasis_def b rank j
    rw [ej,top.repr.map_smul,Finsupp.smul_apply,Basis.repr_self,Matrix.diagonal_apply]
    by_cases same : j=i
    · subst i
      simp only [Finsupp.single_eq_same,smul_eq_mul,mul_one,ite_true]
    · rw [Finsupp.single_eq_of_ne (Ne.symm same),smul_zero]
      simp only [Ne.symm same,ite_false]
  rw [LinearMap.det_toLin',←LinearMap.det_toMatrix top,mat,Matrix.det_diagonal] at asso
  let : ∀ i, FiniteDimensional k ((Polynomial k) ⧸ Ideal.span ({a i} : Set (Polynomial k))) :=
    fun i=>(AdjoinRoot.powerBasis (anz i)).finite
  let dec := N.quotientEquivPiSpan b rank
  have finite : FiniteDimensional k ((ι→(Polynomial k)) ⧸ N) :=
    FiniteDimensional.of_injective (dec.restrictScalars k).toLinearMap dec.injective
  refine ⟨finite,?_⟩
  calc
    Module.finrank k ((ι→(Polynomial k)) ⧸ N) = ∑ i, Module.finrank k ((Polynomial k) ⧸ Ideal.span ({a i} : Set (Polynomial k))) :=
      Submodule.finrank_quotient_eq_sum k b rank
    _ = ∑ i, (a i).natDegree := Finset.sum_congr rfl fun i _=>(AdjoinRoot.powerBasis (anz i)).finrank
    _ = (∏ i,a i).natDegree := (natDegree_prod _ _ (fun i _=>anz i)).symm
    _ = A.det.natDegree := (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated asso)).symm

#print axioms polynomial_cokernel
end
end Lower6960.LineEuler

end Merged6967_R6960LineEulerPolynomial

section Merged6967_R6966ProofNonlinearMarkRows
set_option Elab.async false





set_option Elab.async false

namespace Research6966.NonlinearMarkRows
open Polynomial Finset
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 600000
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds

private abbrev S (σ F:Type*) [Field F] := MvPolynomial σ F
abbrev Eqn (σ F:Type*) [Field F] := (S σ F)[X]

def coeffRow (A B:Eqn σ F) (d:ℕ) : ℕ→Eqn σ F
  | 0=>Polynomial.X*A^(2*d-1)
  | j+1=>QuadraticWeight.numerator A B j*A^(2*d-1-(2*j+1))

def node (A B:Eqn σ F) (d:ℕ) (centre x received:F) : Eqn σ F :=
  (∑ j∈range (d+1),C (MvPolynomial.C ((x-centre)^j/(j.factorial:F)))*coeffRow A B d j)-
    C (MvPolynomial.C received)*A^(2*d-1)

def evaluate (p:σ→F) (y:F) : Eqn σ F→+*F:=eval₂RingHom (MvPolynomial.eval p) y

private theorem coeffRow_at (p:σ→F) (fixed:∀i,Differential.deriv (p i)=0) (y:F)
    (A B:Eqn σ F) (law:evaluate p y A*Differential.deriv y=evaluate p y B) (d j:ℕ) (le:j≤d) :
    evaluate p y (coeffRow A B d j)=(evaluate p y A)^(2*d-1)*Differential.deriv^[j] y := by
  cases j with
  | zero=>
    rw [coeffRow,map_mul,map_pow]
    change evaluate p y Polynomial.X*_=_*y
    rw [show evaluate p y Polynomial.X=y by simp [evaluate],mul_comm]
  | succ j=>
    letI : Algebra (S σ F) F := (MvPolynomial.eval p).toAlgebra
    letI : DifferentialAlgebra (S σ F) F := ⟨fun c=>GenericPhysicalCentre.deriv_eval p fixed c⟩
    have step:=QuadraticWeight.cleared A B y law j
    change (evaluate p y A)^(2*j+1)*Differential.deriv^[j+1] y=evaluate p y (QuadraticWeight.numerator A B j) at step
    rw [coeffRow,map_mul,map_pow,←step]
    have add:2*j+1+(2*d-1-(2*j+1))=2*d-1:=by omega
    rw [mul_right_comm,←pow_add,add]

variable {K:Type*} [Field K]
private abbrev Q:=GenericPhysicalCentre.Frac K
attribute [local instance] GenericPhysicalCentre.physical
private abbrev xi : Q (K:=K):=algebraMap K[X] (GenericPhysicalCentre.Frac K) Polynomial.X

private theorem generic_eval (P:K[X]) :
    (P.map (algebraMap K (GenericPhysicalCentre.Frac K))).eval xi=algebraMap K[X] (GenericPhysicalCentre.Frac K) P := by
  let E:=GenericPhysicalCentre.Frac K
  have eq:(evalRingHom (xi (K:=K))).comp (mapRingHom (algebraMap K E))=algebraMap K[X] E := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C,coe_evalRingHom,eval_C]
      exact IsScalarTower.algebraMap_apply K K[X] E c
    · simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_X,coe_evalRingHom,eval_X];rfl
  exact RingHom.congr_fun eq P

theorem taylor_at_generic (P:K[X]) (x:GenericPhysicalCentre.Frac K) (d:ℕ) (degree:P.natDegree≤d)
    (fac:∀ j≤d,(j.factorial:GenericPhysicalCentre.Frac K)≠0) :
    (P.map (algebraMap K _)).eval x=∑i∈range (d+1),((x-xi)^i/(i.factorial:GenericPhysicalCentre.Frac K))*
      Differential.deriv^[i] (algebraMap K[X] (GenericPhysicalCentre.Frac K) P) := by
  let E:=GenericPhysicalCentre.Frac K
  let y:=algebraMap K[X] E P
  have tay:=AffineODE.evaluation_from_derivatives (P.map (algebraMap K E)) xi x d
    (natDegree_map_le.trans degree) fac
  have jets (j:ℕ) : (Polynomial.derivative^[j] (P.map (algebraMap K E))).eval xi=Differential.deriv^[j] y := by
    have comm (l:ℕ) : (Polynomial.derivative^[l] (P.map (algebraMap K E)))=
        (Polynomial.derivative^[l] P).map (algebraMap K E) := by
      induction l with
      | zero=>rfl
      | succ l ih=>rw [Function.iterate_succ_apply',Function.iterate_succ_apply' (f:=Polynomial.derivative) (x:=P),ih,derivative_map]
    rw [comm,generic_eval,GenericPhysicalCentre.physical_iterate]
  simp_rw [jets] at tay
  exact tay

theorem detects (p:σ→GenericPhysicalCentre.Frac K) (fixed:∀i,Differential.deriv (p i)=0)
    (A B:Eqn σ (GenericPhysicalCentre.Frac K)) (P:K[X]) (d:ℕ) (degree:P.natDegree≤d)
    (fac:∀ j≤d,(j.factorial:GenericPhysicalCentre.Frac K)≠0) (x received:GenericPhysicalCentre.Frac K)
    (law:evaluate p (algebraMap K[X] _ P) A * algebraMap K[X] _ P.derivative =
      evaluate p (algebraMap K[X] _ P) B) (regular:evaluate p (algebraMap K[X] _ P) A≠0) :
    evaluate p (algebraMap K[X] _ P) (node A B d xi x received)=0 ↔
    (P.map (algebraMap K _)).eval x=received := by
  let E:=GenericPhysicalCentre.Frac K
  let y:=algebraMap K[X] E P
  let ev:=evaluate p y
  have ode: ev A*Differential.deriv y=ev B := by
    rw [show Differential.deriv y=algebraMap K[X] E P.derivative from GenericPhysicalCentre.physical_poly P]
    exact law
  have wt (c:E) : ev (C (MvPolynomial.C c))=c := by simp [ev,evaluate]
  have tay:=taylor_at_generic P x d degree fac
  change ev (node A B d xi x received)=0 ↔ _
  rw [node,map_sub,map_sum,map_mul,wt,map_pow]
  have sum:(∑j∈range (d+1),ev (C (MvPolynomial.C ((x-xi)^j/(j.factorial:E)))*coeffRow A B d j))=
      (ev A)^(2*d-1)*(P.map (algebraMap K E)).eval x := by
    rw [tay,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [map_mul,wt,show ev (coeffRow A B d j)=(ev A)^(2*d-1)*Differential.deriv^[j] y from
      coeffRow_at p fixed y A B ode d j (by simpa using hj)]
    ring
  rw [sum,mul_comm received,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ regular),sub_eq_zero]

#print axioms detects
end
end Research6966.NonlinearMarkRows

end Merged6967_R6966ProofNonlinearMarkRows

section Merged6967_R6966ProofPadeDescent
set_option Elab.async false





set_option Elab.async false

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K E : Type*} [Field K] [Field E]

def Row.map (f:K→+*E) (G:Row K) : Row E := ⟨G.a.map f,G.b.map f⟩

theorem Row.degree_map (f:K→+*E) (G:Row K) :
    (G.map f).graphDegree=G.graphDegree := by
  simp [Row.map,Row.graphDegree,natDegree_map_eq_of_injective f.injective]

theorem Row.primitive_map (f:K→+*E) {G:Row K} :
    (G.map f).primitive ↔ G.primitive := by
  simp only [Row.primitive,Row.map,Polynomial.isCoprime_map]
  rw [show G.a.map f≠0 ↔ G.a≠0 from map_ne_zero_iff (mapRingHom f) (map_injective f f.injective)]

private theorem err_at_map (f:K→+*E) (G:Row K) (x z:K) :
    (G.map f).a.eval (f x)*f z-(G.map f).b.eval (f x) =
      f (G.a.eval x*z-G.b.eval x) := by
  simp only [Row.map,eval_map_apply,map_sub,map_mul]

variable [Algebra K E]

theorem Controls.conjugate {sheet:E→E→Prop} {c:ℕ} {G:Row E} (h:Controls G sheet c)
    (stable : ∀ (σ:E≃ₐ[K]E) x y,sheet x y → sheet (σ x) (σ y))
    (σ:E≃ₐ[K]E) : Controls (G.map σ.toRingHom) sheet c := by
  classical
  intro s v hv
  let t:=s.image σ.symm
  let w (x:E):=σ.symm (v (σ x))
  have cnt := h t w (by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hx
    have hy':=hv y hy
    refine ⟨by simpa [w] using stable σ.symm _ _ hy'.1,?_⟩
    intro zero
    apply hy'.2
    have eq:=err_at_map σ.toRingHom G (σ.symm y) (w (σ.symm y))
    change G.a.eval (σ.symm y)*w (σ.symm y)-G.b.eval (σ.symm y)=0 at zero
    rw [zero,map_zero] at eq
    simpa [Row.err,w] using eq)
  have eq:t.card=s.card:=card_image_of_injective _ σ.symm.injective
  rwa [eq,←Row.degree_map σ.toRingHom G] at cnt

private theorem polynomial_descent [IsGalois K E] (p:E[X])
    (fixed : ∀ σ:E≃ₐ[K]E,p.map σ.toRingHom=p) :
    ∃ q:K[X],q.map (algebraMap K E)=p := by
  apply (mem_lifts p).mp
  apply (lifts_iff_coeff_lifts p).mpr
  intro j
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K) _).mpr
  intro σ
  change σ.toRingHom (p.coeff j)=p.coeff j
  rw [←coeff_map]
  exact congrArg (fun v:E[X]=>v.coeff j) (fixed σ)

/-- Descent uses the actual unique normalized graph over a Galois field.
In positive characteristic this is applied to separable sheet coordinates. -/
theorem descend_control [IsGalois K E] (sheet:E→E→Prop) (e c:ℕ) (gap:2*c<e)
    (initial : ∃ (s:Finset E) (v:E→E),s.card=e ∧ ∀x∈s,sheet x (v x))
    (stable : ∀ (σ:E≃ₐ[K]E) x y,sheet x y → sheet (σ x) (σ y))
    {F:Row E} (fp:F.primitive) (control:Controls F sheet c) :
    ∃ G:Row K,G.primitive ∧ G.graphDegree=F.graphDegree ∧
      Controls (G.map (algebraMap K E)) sheet c := by
  let t:=F.a.leadingCoeff⁻¹
  have tn:t≠0 := inv_ne_zero (leadingCoeff_ne_zero.mpr fp.1)
  let G:=F.scale t
  have monic:G.a.Monic := by simpa [G,Row.scale,t,mul_comm] using monic_mul_leadingCoeff_inv fp.1
  have gp:G.primitive := Row.primitive_scale fp tn
  have gc:Controls G sheet c := control.scale tn
  have invariant (σ:E≃ₐ[K]E) : G.map σ.toRingHom=G :=
    unique_monic_control sheet e c gap initial gp ((Row.primitive_map σ.toRingHom).mpr gp)
      monic (monic.map σ.toRingHom) gc (gc.conjugate stable σ)
  obtain ⟨a,ha⟩:=polynomial_descent (K:=K) G.a (fun σ=>congrArg Row.a (invariant σ))
  obtain ⟨b,hb⟩:=polynomial_descent (K:=K) G.b (fun σ=>congrArg Row.b (invariant σ))
  let H:Row K:=⟨a,b⟩
  have actual:H.map (algebraMap K E)=G := by
    change Row.mk (a.map _) (b.map _) = G
    rw [ha,hb]
  refine ⟨H,(Row.primitive_map _).mp (actual ▸ gp),?_,actual ▸ gc⟩
  rw [←Row.degree_map (algebraMap K E) H,actual]
  exact Row.degree_scale F tn

#print axioms descend_control
end
end Research6966.Pade

end Merged6967_R6966ProofPadeDescent

section Merged6967_R6966ProofPadePowers
set_option Elab.async false





set_option Elab.async false

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def jetVars : K[X][X] ≃ₐ[K] MvPolynomial (Fin 2) K :=
  (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm).trans
    (MvPolynomial.finSuccEquiv K 1).symm

private theorem coeff_vars (P:K[X][X]) (d:Fin 2 →₀ ℕ) :
    (jetVars P).coeff d=(P.coeff (d 0)).coeff (d 1) := by
  let Q:=P.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingHom
  change ((MvPolynomial.finSuccEquiv K 1).symm Q).coeff d=_
  rw [←Finsupp.cons_tail d,←MvPolynomial.finSuccEquiv_coeff_coeff,AlgEquiv.apply_symm_apply]
  simp only [Q,Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm (P.coeff (d 0))).coeff d.tail=_
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm];rfl

def totalJet (P:K[X][X]) := (jetVars P).totalDegree

theorem totalJet_mul {P Q:K[X][X]} (p:P≠0) (q:Q≠0) : totalJet (P*Q)=totalJet P+totalJet Q := by
  unfold totalJet
  rw [map_mul,MvPolynomial.totalDegree_mul_of_isDomain ((map_ne_zero_iff _ jetVars.injective).mpr p)
    ((map_ne_zero_iff _ jetVars.injective).mpr q)]

theorem totalJet_le (P:K[X][X]) (b:ℕ) :
    totalJet P≤b ↔ ∀ j i,(P.coeff j).coeff i≠0 → i+j≤b := by
  classical
  have add (d:Fin 2→₀ℕ) : d.sum (fun _ n=>n)=d 1+d 0 := by
    rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two,Nat.add_comm]
  constructor
  · intro bound j i nz
    let d:Fin 2→₀ℕ := Finsupp.equivFunOnFinite.symm ![j,i]
    have mem : d∈(jetVars P).support := MvPolynomial.mem_support_iff.mpr (by rw [coeff_vars];exact nz)
    have h: d.sum (fun _ n=>n)≤b := (MvPolynomial.le_totalDegree mem).trans bound
    rw [add] at h;exact h
  · intro bound
    apply Finset.sup_le
    intro d hd
    apply (add d).le.trans
    exact bound _ _ (coeff_vars P d ▸ MvPolynomial.mem_support_iff.mp hd)

def Row.polynomial (G:Row K) : K[X][X] := C G.a*«X»-C G.b

theorem Row.slope_degree {G:Row K} (p:G.primitive) : G.polynomial.natDegree=1 := by
  unfold Row.polynomial
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply (natDegree_sub_le ..).trans;apply max_le
    · rw [natDegree_mul (C_ne_zero.mpr p.1) X_ne_zero,natDegree_C,natDegree_X]
    · simp
  · simpa [coeff_sub,coeff_C_mul] using p.1

theorem Row.polynomial_ne {G:Row K} (p:G.primitive) : G.polynomial ≠ 0 := by
  intro z
  have h:=G.slope_degree p
  simp [z] at h

theorem Row.polynomial_primitive {G:Row K} (p:G.primitive) : G.polynomial.IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have div := (C_dvd_iff_dvd_coeff d _).mp hd
  have da : d∣G.a := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using div 1
  have db : d∣G.b := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using div 0
  obtain ⟨u,v,eq⟩:=p.2
  apply isUnit_iff_dvd_one.mpr
  rw [←eq]
  exact dvd_add (dvd_mul_of_dvd_right da _) (dvd_mul_of_dvd_right db _)

theorem Row.total_polynomial {G:Row K} (p:G.primitive) : totalJet G.polynomial=G.graphDegree := by
  apply le_antisymm
  · apply (totalJet_le ..).mpr
    intro j i nz
    rcases j with _|j
    · have non : G.b.coeff i≠0 := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using nz
      exact (le_natDegree_of_ne_zero non).trans (le_max_right ..)
    rcases j with _|j
    · have non : G.a.coeff i≠0 := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using nz
      exact (Nat.add_le_add_right (le_natDegree_of_ne_zero non) 1).trans (le_max_left ..)
    · have := coeff_eq_zero_of_natDegree_lt (show G.polynomial.natDegree<j+2 by rw [G.slope_degree p];omega)
      simp [this] at nz
  · apply max_le
    · have h := (totalJet_le G.polynomial _).mp le_rfl 1 G.a.natDegree
      apply h
      simp [Row.polynomial,leadingCoeff_ne_zero.mpr p.1]
    · by_cases zero:G.b=0
      · simp [zero]
      have h := (totalJet_le G.polynomial _).mp le_rfl 0 G.b.natDegree
      apply (by simpa using h : ((G.polynomial.coeff 0).coeff G.b.natDegree≠0) → G.b.natDegree≤_)
      simp [Row.polynomial,leadingCoeff_ne_zero.mpr zero]

private theorem roots_degree (ys:Finset K) : (∏ y∈ys,(«X»-C y : K[X])).natDegree=ys.card := by
  rw [natDegree_prod ys (fun y=>«X»-C y) (fun y _=>X_sub_C_ne_zero y)]
  simp

/-- A nonmultiplicative row has enough room for every vanishing order on
the graph in a single univariate restriction. -/
theorem bezout_sheet_order {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (Q:K[X][X]) (b j k:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (order:∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k)
    (avoids:¬G.polynomial∣Q) : ys.card*k≤b+(G.graphDegree-1)*min b j := by
  have non : Q≠0 := fun z=>avoids (z ▸ dvd_zero _)
  have degree:Q.natDegree≤b := by
    have q:Q.coeff Q.natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr non
    have h := (totalJet_le Q b).mp bt Q.natDegree (Q.coeff Q.natDegree).natDegree
      (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr q)
    omega
  have cap := le_min degree sj
  have regular (y) (hy:y∈ys) : G.a.eval y≠0 := by
    intro zero
    have bzero:G.b.eval y=0 := by simpa [Row.err,zero] using graph y hy
    obtain ⟨u,w,bz⟩:=gp.2
    have H:=congrArg (eval y) bz
    simp [zero,bzero] at H
  have dv := TerminalProjection.all_sheets G.a G.b Q ys v (min b j) k cap (fun y hy=>
    ⟨regular y hy,sub_eq_zero.mp (graph y hy),order y hy⟩)
  have nz:=TerminalProjection.nonzero_of_avoids G.a G.b Q _ cap gp.1 (G.polynomial_primitive gp) avoids
  have lower:=natDegree_le_of_dvd dv nz
  rw [natDegree_pow,roots_degree,Nat.mul_comm] at lower
  apply lower.trans
  refine TerminalProjection.ordinate_width G.a G.b Q _ G.graphDegree b cap
    (by unfold Row.graphDegree;omega) (by unfold Row.graphDegree;omega) (le_max_right ..) ?_
  intro i hi
  have le:Q.coeff i≠0:=mem_support_iff.mp hi
  exact (totalJet_le Q b).mp bt i _ (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr le)

/-- Successive forcing for exactly the row, degree and order budget
used by the physical terminal cut. -/
theorem forced_power {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀y∈ys,G.err v y=0) (Q:K[X][X]) (b j k t:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (ord:∀y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) (tk:t≤k)
    (forces:∀ i<t,i*G.graphDegree≤b → i≤j →
        b-i*G.graphDegree+(G.graphDegree-1)*min (b-i*G.graphDegree) (j-i)
        < ys.card*(k-i)) : G.polynomial^t ∣ Q := by
  classical
  by_cases z:Q=0
  · simp [z]
  have gn:=G.polynomial_ne gp
  have powers (i:ℕ) : i≤t → ∃ R:K[X][X],Q=G.polynomial^i*R ∧
      ∀y∈ys,R∈(TerminalProjection.fibrePoint y (v y))^(k-i) := by
    induction i with
    | zero => intro _;exact ⟨Q,by simp,by simpa using ord⟩
    | succ i ih =>
      intro next
      obtain ⟨R,eq,contact⟩:=ih (by omega)
      have rn:R≠0:= right_ne_zero_of_mul (eq ▸ z)
      have powdeg (n:ℕ) : totalJet (G.polynomial^n)=n*G.graphDegree := by
        induction n with
        | zero => simp [totalJet,jetVars]
        | succ n h =>
          rw [pow_succ,totalJet_mul (pow_ne_zero _ gn) gn,h,G.total_polynomial gp,Nat.succ_mul]
      have total:=bt
      have slope:=sj
      rw [eq,totalJet_mul (pow_ne_zero _ gn) rn,powdeg] at total
      rw [eq,natDegree_mul (pow_ne_zero _ gn) rn,natDegree_pow,G.slope_degree gp,mul_one] at slope
      have bd:totalJet R≤b-i*G.graphDegree := by omega
      have jd:R.natDegree≤j-i := by omega
      have div : G.polynomial∣ R := by
        by_contra no
        exact (Nat.not_le_of_lt (forces i (by omega) (by omega) (by omega)))
          (bezout_sheet_order gp ys v graph R _ _ _ bd jd contact no)
      obtain ⟨T,hT⟩:=div
      refine ⟨T,by rw [eq,hT,pow_succ,mul_assoc],?_⟩
      intro y hy
      have hit:=sub_eq_zero.mp (graph y hy)
      have reg : G.a.eval y≠0 := by
        intro hz
        change G.a.eval y*v y=G.b.eval y at hit
        obtain ⟨l,w,one⟩:=gp.2
        have test:=congrArg (eval y) one
        simp [←hit,hz] at test
      apply PadeJetOrder.strip G.a G.b T y (v y) (k-(i+1)) reg hit
      rw [show k-(i+1)+1=k-i by omega]
      exact hT ▸ contact y hy
  obtain ⟨R,eq,_⟩:=powers t le_rfl
  exact ⟨R,eq⟩

#print axioms bezout_sheet_order
#print axioms forced_power

/-- Number charged by the physical quotient receipt, using a rounded-up
division only when a positive number of graph factors is forced. -/
def layers (a n b j k:ℕ) : ℕ :=
  let width:=b+(a-1)*min b j
  if width<n*k then min k (1+(n*k-width-1)/(n-(2*a-1))) else 0

theorem layers_force {a n b j k i:ℕ} (ap:0<a) (many:2*a-1<n)
    (active:i<layers a n b j k) (ib:i*a≤b) (ij:i≤j) :
    b-i*a+(a-1)*min (b-i*a) (j-i)<n*(k-i) := by
  let width:=b+(a-1)*min b j
  by_cases excess:width<n*k
  · change i<(if width<n*k then min k (1+(n*k-width-1)/(n-(2*a-1))) else 0) at active
    rw [ite_eq_left excess,lt_min_iff] at active
    have ik:=active.1.le
    have div:i≤(n*k-width-1)/(n-(2*a-1)):=by omega
    have spend: i*(n-(2*a-1))≤n*k-width-1 :=
      (Nat.le_div_iff_mul_le (by omega)).mp div
    have split:i*(n-(2*a-1))+i*(2*a-1)=i*n:=by
      rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
    have full:n*(k-i)+i*n=n*k:=by
      rw [Nat.mul_comm i n,←Nat.mul_add,Nat.sub_add_cancel ik]
    have ia : i ≤ i*a := by simpa only [mul_one] using Nat.mul_le_mul_left i (show 1≤a from ap)
    have drop:min (b-i*a) (j-i)+i≤min b j := by
      have l:=min_le_left (b-i*a) (j-i)
      have r:=min_le_right (b-i*a) (j-i)
      omega
    have cols:=Nat.mul_le_mul_left (a-1) drop
    rw [Nat.mul_add] at cols
    have reduced:b-i*a+(a-1)*min (b-i*a) (j-i)+i*(2*a-1)≤width := by
      dsimp only [width]
      rw [show 2*a-1=a+(a-1) by omega,Nat.mul_add,Nat.mul_comm i (a-1)]
      omega
    omega
  · simp [layers,show ¬b+(a-1)*min b j<n*k from excess] at active

theorem forced_layers {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀y∈ys,G.err v y=0) (Q:K[X][X]) (b j k:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (ord:∀y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k)
    (many:2*G.graphDegree-1<ys.card) :
    G.polynomial^(layers G.graphDegree ys.card b j k) ∣ Q := by
  apply forced_power gp ys v graph Q b j k _ bt sj ord
  · dsimp only [layers]
    split
    · exact min_le_left ..
    · exact Nat.zero_le _
  · intro i hi ib ij
    exact layers_force (by unfold Row.graphDegree;omega) many hi ib ij

#print axioms forced_layers
end
end Research6966.Pade

end Merged6967_R6966ProofPadePowers

section Merged6967_R6966ProofWordSurfaceMarks
set_option Elab.async false







set_option Elab.async false

-- merged module R6966ProofWordSurfaceJets
section Merged_R6966ProofWordSurfaceJets

namespace Research6966.WordSurfaceJets
open Finset Module MvPolynomial
variable {σ K:Type*} [Fintype σ] [DecidableEq σ] [Field K]
noncomputable section
set_option maxHeartbeats 500000

abbrev Pol (σ K:Type*) [CommSemiring K] := MvPolynomial σ K

def high (σ K:Type*) [Field K] (k:ℕ) : Ideal (Pol σ K) :=
  restrictSupportIdeal K {e : σ →₀ ℕ | k≤e.degree} (by
    intro a b h hp
    exact (show k≤a.degree from hp).trans (Finsupp.degree_mono h))

def low (σ K:Type*) [Field K] (k:ℕ) : Submodule K (Pol σ K) :=
  restrictSupport K {e | e.degree<k}

abbrev Local (σ K:Type*) [Field K] (k:ℕ) := Pol σ K ⧸ high σ K k

theorem mem_high {P:Pol σ K} {k:ℕ} : P∈high σ K k ↔ ∀ e∈P.support,k≤e.degree := Iff.rfl

theorem high_eq (k:ℕ) :
    (high σ K k).restrictScalars K=restrictWeightedOrder (R:=K) (fun _:σ=>1) k := by
  ext P
  change (∀ e∈P.support,k≤e.degree) ↔ ∀ e∈P.support,k≤e.weight (fun _:σ=>1)
  simp only [Finsupp.degree_eq_weight_one,Pi.one_def]

theorem high_mul {a b:ℕ} {P Q:Pol σ K} (hp:P∈high σ K a) (hq:Q∈high σ K b) :
    P*Q∈high σ K (a+b) := by
  change P∈(high σ K a).restrictScalars K at hp
  change Q∈(high σ K b).restrictScalars K at hq
  change P*Q∈(high σ K (a+b)).restrictScalars K
  rw [high_eq] at hp hq ⊢
  exact mul_mem_restrictWeightedOrder hp hq

theorem high_pow {a:ℕ} {P:Pol σ K} (hp:P∈high σ K a) (n:ℕ) : P^n∈high σ K (n*a) := by
  induction n with
  | zero=>simp [mem_high]
  | succ n ih=>rw [pow_succ,Nat.succ_mul];exact high_mul ih hp

theorem high_one {P:Pol σ K} : P∈high σ K 1 ↔ constantCoeff P=0 := by
  constructor
  · intro h
    by_contra ne
    exact (by simpa using mem_high.mp h 0 (mem_support_iff.mpr ne) : False)
  · intro hz
    apply mem_high.mpr
    intro e he
    by_contra! small
    have zero:e=0:=by
      ext i
      have cap:=Finsupp.le_degree (s:=i) (f:=e)
      simp only [Finsupp.zero_apply];omega
    exact (mem_support_iff.mp he) (zero ▸ hz)

def trunc (k:ℕ) : Pol σ K →ₗ[K] low σ K k :=
  (weightedTruncation (fun _:σ=>1) k).codRestrict _ (fun P=>by
    change ∀ e∈((weightedTruncation (fun _:σ=>1) k) P).support,e.degree<k
    intro e he
    have alive : ((weightedTruncation (fun _:σ=>1) k) P).coeff e≠0 := mem_support_iff.mp he
    by_contra h
    apply alive
    rw [coeff_weightedTruncation,ite_eq_right]
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using h)

theorem trunc_class (k:ℕ) (P:Pol σ K) :
    Ideal.Quotient.mk (high σ K k) ((trunc k P).val) = Ideal.Quotient.mk _ P := by
  apply Ideal.Quotient.eq.mpr
  apply mem_high.mpr
  intro e he
  by_contra! small
  apply mem_support_iff.mp he
  change (weightedTruncation _ k P-P).coeff e=0
  rw [coeff_sub,coeff_weightedTruncation,ite_eq_left,sub_self]
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using small

def read (k:ℕ) : low σ K k →ₗ[K] Local σ K k :=
  ((Ideal.Quotient.mkₐ K (high σ K k)).toLinearMap).comp (low σ K k).subtype

theorem read_bijective (k:ℕ) : Function.Bijective (read (σ:=σ) (K:=K) k) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro P h
    have hp:P.val∈high σ K k:=Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp h)
    apply Subtype.ext
    by_contra ne
    obtain ⟨e,he⟩:=Finset.nonempty_iff_ne_empty.mpr (show P.val.support≠∅ from by simpa using ne)
    exact (Nat.not_lt_of_ge (mem_high.mp hp e he)) (P.property he)
  · intro z
    obtain ⟨P,rfl⟩:=Ideal.Quotient.mk_surjective z
    exact ⟨trunc k P,trunc_class k P⟩

theorem local_dimension (k:ℕ) :
    finrank K (Local σ K (k+1))=(k+Fintype.card σ).choose (Fintype.card σ) := by
  rw [←(LinearEquiv.ofBijective _ (read_bijective (σ:=σ) (K:=K) (k+1))).finrank_eq]
  unfold low
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  let equiv : {e:σ→₀ℕ // e.degree<k+1} ≃ {e:σ→₀ℕ // e.weight (fun _:σ=>1)≤k} :=
    Equiv.subtypeEquivRight (fun _=>by simp [Finsupp.degree_eq_weight_one,Pi.one_def])
  change Nat.card {e:σ→₀ℕ // e.degree<k+1}=_
  rw [Nat.card_congr equiv,Finset.card_finsupp_weight_le_eq_card_natWeightedSimplex _ (by simp),
    Finset.card_natWeightedSimplex_one]

instance (k:ℕ) : FiniteDimensional K (low σ K k) := by
  apply restrictSupport_finite
  exact (Finsupp.finite_of_degree_le k).subset (fun _ h=>Nat.le_of_lt h)

instance (k:ℕ) : FiniteDimensional K (Local σ K k) :=
  Module.Finite.of_surjective (read k) (read_bijective k).2

/-- Truncating a multiplier one degree earlier preserves its product by
any relation vanishing at this point. This holds also at singular points. -/
theorem relation_image (k:ℕ) (F Q:Pol σ K) (hz:constantCoeff F=0) :
    Ideal.Quotient.mk (high σ K (k+1)) (F*Q)=
      Ideal.Quotient.mk _ (F*(trunc k Q).val) := by
  apply Ideal.Quotient.eq.mpr
  rw [←mul_sub]
  have diff:=Ideal.Quotient.eq.mp (trunc_class k Q).symm
  simpa only [Nat.add_comm 1 k] using high_mul (high_one.mpr hz) diff

/-- A separator nonzero at its own point is a unit in every truncated
local ring there. -/
theorem local_unit (k:ℕ) {P:Pol σ K} (atOrigin:constantCoeff P≠0) :
    IsUnit (Ideal.Quotient.mk (high σ K k) P) := by
  let π:=Ideal.Quotient.mk (high σ K k)
  let c:=constantCoeff P
  have hz:constantCoeff (P-C c)=0:=by simp [c]
  have nil:IsNilpotent (π (P-C c)):=by
    refine ⟨k,?_⟩
    rw [←map_pow,Ideal.Quotient.eq_zero_iff_mem]
    simpa using high_pow (high_one.mpr hz) k
  have unit:IsUnit (π (C c)) := (atOrigin.isUnit.map (C:K→+*Pol σ K)).map π
  have sum:=nil.isUnit_add_right_of_commute unit (Commute.all _ _)
  simpa [map_sub] using sum

#print axioms local_dimension
#print axioms relation_image
#print axioms local_unit
end
end Research6966.WordSurfaceJets

end Merged_R6966ProofWordSurfaceJets

-- merged module R6966ProofWordSurfaceInterpolation
section Merged_R6966ProofWordSurfaceInterpolation

namespace Research6966.WordSurfaceInterpolation
open Finset Module MvPolynomial WordSurfaceJets
variable {σ K ι:Type*} [Fintype σ] [DecidableEq σ] [Field K]
noncomputable section

def shift (p:σ→K) : Pol σ K →ₐ[K] Pol σ K := bind₁ (fun i=>«X» i+C (p i))

theorem shift_inverse (p:σ→K) (Q:Pol σ K) : shift p (shift (-p) Q)=Q := by
  have id:(shift p).comp (shift (-p))=AlgHom.id K (Pol σ K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [shift]
  exact AlgHom.congr_fun id Q

theorem shift_origin (p:σ→K) (Q:Pol σ K) : constantCoeff (shift p Q)=eval p Q := by
  have id:(constantCoeff (σ:=σ) (R:=K)).comp (shift p).toRingHom=eval p := by
    apply MvPolynomial.ringHom_ext
    · intro c;simp [shift,RingHom.comp_apply]
    · intro i;simp [shift,RingHom.comp_apply]
  exact RingHom.congr_fun id Q

def rect (σ K:Type*) [Field K] (cap:σ→ℕ) : Submodule K (Pol σ K) :=
  restrictSupport K {e | ∀ i,e i≤cap i}

theorem in_rect {Q:Pol σ K} {cap:σ→ℕ} : Q∈rect σ K cap ↔ ∀ i,Q.degreeOf i≤cap i := by
  change (∀ e∈Q.support,∀ i,e i≤cap i) ↔ _
  simp only [MvPolynomial.degreeOf_le_iff]
  exact ⟨fun h i e he=>h e he i,fun h e he i=>h i e he⟩

private def boxEquiv (cap:σ→ℕ) : {e:σ→₀ℕ // ∀ i,e i≤cap i} ≃ (∀ i,Fin (cap i+1)) where
  toFun e i:=⟨e.val i,Nat.lt_succ_of_le (e.property i)⟩
  invFun x:=⟨Finsupp.equivFunOnFinite.symm (fun i=>(x i).val),fun i=>Nat.le_of_lt_succ (x i).isLt⟩
  left_inv _:=Subtype.ext (by ext;rfl)
  right_inv _:=by funext i;exact Fin.ext rfl

instance (cap:σ→ℕ) : FiniteDimensional K (rect σ K cap) := by
  letI : Finite {e:σ→₀ℕ // ∀ i,e i≤cap i}:=Finite.of_equiv _ (boxEquiv cap).symm
  exact Module.Finite.of_basis (basisRestrictSupport K {e:σ→₀ℕ | ∀ i,e i≤cap i})

theorem rectangle_dimension (cap:σ→ℕ) : finrank K (rect σ K cap)=∏i, (cap i+1) := by
  unfold rect
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  change Nat.card {e:σ→₀ℕ // ∀ i,e i≤cap i}=_
  rw [Nat.card_congr (boxEquiv cap),Nat.card_eq_fintype_card,Fintype.card_pi]
  simp

private theorem low_shift_axis (p:σ→K) (k:ℕ) (pos:0<k) (Q:low σ K k) (i:σ) :
    (shift p Q.val).degreeOf i≤k-1 := by
  let w:σ→ℕ:=fun _=>1
  have lowBound:Q.val∈restrictWeightAtMost w (k-1) := by
    intro e he
    have h:e.degree<k:=Q.property he
    change e.weight w≤k-1
    have eq:e.weight w=e.degree:=by rw [Finsupp.degree_eq_weight_one]
    omega
  have shifted:shift p Q.val ∈ restrictWeightAtMost w (k-1) :=
    bind₁_mem_restrictWeightAtMost (w:=w) (fun z=>(restrictWeightAtMost w (w z)).add_mem
      (X_mem_restrictWeightAtMost _ _ le_rfl) (C_mem_restrictWeightAtMost _ (Nat.zero_le _) _)) lowBound
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  exact (Finsupp.le_degree (s:=i) (f:=e)).trans (by
    rw [Finsupp.degree_eq_weight_one];exact mem_restrictWeightAtMost.mp shifted e he)

def atPoint (p:σ→K) (k:ℕ) : Pol σ K →ₐ[K] Local σ K k := (Ideal.Quotient.mkₐ K (high σ K k)).comp (shift p)
def atPoints (p:ι→σ→K) (k:ℕ) : Pol σ K →ₗ[K] (ι→Local σ K k) :=
  LinearMap.pi (fun i=>(atPoint (p i) k).toLinearMap)

/-- Multijet interpolation with an explicit box of global coordinate
degrees. The local inverse of each separator has a Taylor representative
of total degree at most k-1 in all characteristics. -/
theorem interpolate_on [Fintype ι] (p:ι→σ→K) (k:ℕ) (V:Submodule K (Pol σ K))
    (sep:ι→Pol σ K) (fits:∀ i (Q:low σ K k),sep i*shift (-(p i)) Q.val∈V)
    (own:∀ i,eval (p i) (sep i)≠0) (other:∀ i j,i≠j → shift (p i) (sep j) ∈ high σ K k) :
    Function.Surjective ((atPoints p k).domRestrict V) := by
  classical
  intro target
  have patch (i:ι) : ∃ R:low σ K k,(atPoint (p i) k (sep i))*read k R=target i := by
    have unit:IsUnit (atPoint (p i) k (sep i)) :=
      local_unit k ((shift_origin (p i) (sep i)) ▸ own i)
    obtain ⟨x,eq⟩:=(unit.dvd : atPoint (p i) k (sep i) ∣ target i)
    obtain ⟨R,rx⟩:=(read_bijective k).2 x
    exact ⟨R,rx ▸ eq.symm⟩
  choose jet correct using patch
  let term (i:ι):=sep i*shift (-(p i)) (jet i).val
  refine ⟨⟨∑i,term i,Submodule.sum_mem _ (fun i _=>fits i (jet i))⟩,?_⟩
  funext i
  change atPoint (p i) k (∑j,term j)=target i
  rw [map_sum,Finset.sum_eq_single i]
  · dsimp only [term]
    rw [map_mul]
    change _*Ideal.Quotient.mk _ (shift (p i) (shift (-p i) (jet i).val))=_
    rw [shift_inverse];exact correct i
  · intro j _ ne
    change atPoint (p i) k (sep j*_) = 0
    rw [map_mul]
    have zero:atPoint (p i) k (sep j)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (other i j ne.symm)
    rw [zero,zero_mul]
  · simp

theorem interpolate [Fintype ι] (p:ι→σ→K) (k:ℕ) (pos:0<k) (D:σ→ℕ)
    (sep:ι→Pol σ K) (cap:∀ i j,(sep i).degreeOf j≤D j)
    (own:∀ i,eval (p i) (sep i)≠0) (other:∀ i j,i≠j → shift (p i) (sep j) ∈ high σ K k) :
    Function.Surjective ((atPoints p k).domRestrict (rect σ K (fun i=>D i+(k-1)))) := by
  apply interpolate_on p k _ sep _ own other
  intro i Q
  exact in_rect.mpr (fun z=>(degreeOf_mul_le z ..).trans
    (Nat.add_le_add (cap i z) (low_shift_axis _ k pos Q z)))

#print axioms rectangle_dimension
#print axioms interpolate
end
end Research6966.WordSurfaceInterpolation

end Merged_R6966ProofWordSurfaceInterpolation

-- merged module R6966ProofWordSurfaceCount
section Merged_R6966ProofWordSurfaceCount

namespace Research6966.WordSurfaceCount
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation
variable {σ K ι:Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype ι]
noncomputable section
set_option maxHeartbeats 700000

/-- The global multiples of H have at most one fewer Taylor degree of
local image at each marked lift. This subtracts the common surface from
the count even at singular lifts. -/
theorem jet_budget (p:ι→σ→K) (k:ℕ) (cap small:σ→ℕ) (H:Pol σ K) (hn:H≠0)
    (fits:∀ j,H.degreeOf j+small j≤cap j) (vanish:∀ i,eval (p i) H=0)
    (onto:Function.Surjective ((atPoints p (k+1)).domRestrict (rect σ K cap))) :
    Fintype.card ι*finrank K (Local σ K (k+1)) + (∏j,(small j+1)) ≤
      (∏j,(cap j+1)) + Fintype.card ι*finrank K (low σ K k) := by
  classical
  let V:=rect σ K cap
  let V₀:=rect σ K small
  let A:↥V→ₗ[K](ι→Local σ K (k+1)):=(atPoints p (k+1)).domRestrict V
  let mul:↥V₀→ₗ[K]V := ((Algebra.lmul K (Pol σ K) H).comp V₀.subtype).codRestrict V (fun Q=>
    in_rect.mpr (fun j=>(degreeOf_mul_le j H Q.val).trans
      ((Nat.add_le_add_left (in_rect.mp Q.property j) _).trans (fits j))))
  let test:=A.comp mul
  let localMul (i:ι) : low σ K k →ₗ[K] Local σ K (k+1) :=
    (Ideal.Quotient.mkₐ K (high σ K (k+1))).toLinearMap.comp
      ((Algebra.lmul K (Pol σ K) (shift (p i) H)).comp (low σ K k).subtype)
  let lifting:(ι→low σ K k)→ₗ[K](ι→Local σ K (k+1)) :=
    LinearMap.pi (fun i=>(localMul i).comp (LinearMap.proj i))
  have image:test.range≤lifting.range := by
    rintro _ ⟨Q,rfl⟩
    refine ⟨fun i=>trunc k (shift (p i) Q.val),?_⟩
    funext i
    change Ideal.Quotient.mk _ (shift (p i) H*(trunc k (shift (p i) Q.val)).val)=
      Ideal.Quotient.mk _ (shift (p i) (H*Q.val))
    rw [map_mul (shift (p i))]
    exact (relation_image k _ _ ((shift_origin _ _).trans (vanish i))).symm
  have irank:finrank K test.range≤finrank K (ι→low σ K k):=
    (Submodule.finrank_mono image).trans (LinearMap.finrank_range_le lifting)
  let embed:test.ker→ₗ[K]A.ker:=(mul.comp test.ker.subtype).codRestrict _ (fun Q=>Q.property)
  have inject:Function.Injective embed := fun a b eq=>Subtype.ext (Subtype.ext
    (mul_left_cancel₀ hn (congrArg (fun x:↥A.ker=>(x.val:Pol σ K)) eq)))
  have krank:=LinearMap.finrank_le_finrank_of_injective inject
  have dimA:=LinearMap.finrank_range_add_finrank_ker A
  have dimT:=LinearMap.finrank_range_add_finrank_ker test
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,Module.finrank_pi_fintype] at dimA
  rw [Module.finrank_pi_fintype] at irank
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at dimA irank
  have big:finrank K V=∏j,(cap j+1):=rectangle_dimension (K:=K) cap
  have little:finrank K V₀=∏j,(small j+1):=rectangle_dimension (K:=K) small
  omega

/-- A three-variable surface needs two independent Taylor directions
per marked lift. -/
theorem trivariate_budget (p:ι→Fin 3→K) (k:ℕ) (cap small:Fin 3→ℕ)
    (H:Pol (Fin 3) K) (hn:H≠0) (fits:∀ j,H.degreeOf j+small j≤cap j)
    (vanish:∀ i,eval (p i) H=0)
    (onto:Function.Surjective ((atPoints p (k+2)).domRestrict (rect (Fin 3) K cap))) :
    Fintype.card ι*((k+3).choose 2)+(∏j,(small j+1))≤∏j,(cap j+1) := by
  have count:=jet_budget p (k+1) cap small H hn fits vanish onto
  rw [(LinearEquiv.ofBijective _ (read_bijective (σ:=Fin 3) (K:=K) (k+1))).finrank_eq,
    local_dimension,local_dimension] at count
  simp only [Fintype.card_fin] at count
  have step:(k+1+3).choose 3=(k+3).choose 2+(k+3).choose 3 := by
    rw [show k+1+3=(k+3)+1 by omega,Nat.choose_succ_succ]
  rw [step,Nat.mul_add] at count
  omega

#print axioms jet_budget
#print axioms trivariate_budget
end
end Research6966.WordSurfaceCount

end Merged_R6966ProofWordSurfaceCount

-- merged module R6966ProofWordSurfaceMarks
section Merged_R6966ProofWordSurfaceMarks

namespace Research6966.WordSurfaceMarks
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceCount
variable {σ K ι I :Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype I] [DecidableEq I]
noncomputable section
set_option maxHeartbeats 500000

def hits (x:σ→K) (rows:I→Pol σ K) : Finset I := by
  classical
  exact univ.filter (fun i=>eval x (rows i)=0)

theorem hit {x:σ→K} {rows:I→Pol σ K} {i:I} : i∈hits x rows ↔ eval x (rows i)=0 := by
  classical
  simp [hits]

def separator (p:ι→σ→K) (rows:I→Pol σ K) (t:ℕ) (x:ι) : Pol σ K :=
  (∏i∈(univ\hits (p x) rows),rows i)^t

/-- A mark's missed rows provide its own separator. Other marks hit
at least A-d of these rows, so the separator has the claimed local order. -/
theorem separator_spec (p:ι→σ→K) (rows:I→Pol σ K) (D:σ→ℕ) (cap:∀ i j,(rows i).degreeOf j≤D j)
    (A d t:ℕ) (enough:∀ z,A≤(hits (p z) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    let sep:=separator p rows t
    (∀ x j,(sep x).degreeOf j≤t*(Fintype.card I-A)*D j) ∧
      (∀ x,eval (p x) (sep x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (sep y)∈high σ K (t*(A-d))) := by
  classical
  let misses (x:ι):=univ\hits (p x) rows
  let product (x:ι):=∏i∈misses x,rows i
  change (∀ x j,((product x)^t).degreeOf j≤_) ∧ (∀ x,eval (p x) ((product x)^t)≠0) ∧ _
  refine ⟨?_,?_,?_⟩
  · intro x j
    have pair:=card_sdiff_add_card_eq_card (subset_univ (hits (p x) rows))
    have n:(misses x).card≤Fintype.card I-A := by dsimp only [misses];rw [card_univ] at pair;have:=enough x;omega
    have deg:(product x).degreeOf j≤(misses x).card*D j :=
      (degreeOf_prod_le j _ _).trans ((sum_le_sum (s:=misses x) (fun i _=>cap i j)).trans_eq (by simp))
    exact (degreeOf_pow_le j _ t).trans (by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left t (deg.trans (Nat.mul_le_mul_right (D j) n)))
  · intro x
    rw [map_pow]
    apply pow_ne_zero
    rw [show eval (p x) (product x)=∏i∈misses x,eval (p x) (rows i) from map_prod ..]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi;exact fun eq=>(mem_sdiff.mp hi).2 (hit.mpr eq)
  · intro x y ne
    have close:(hits (p x) rows\hits (p y) rows).card≥A-d := by
      have := card_sdiff_add_card_inter (hits (p x) rows) (hits (p y) rows)
      have n:=enough x
      have join:=shared x y ne
      omega
    let order:I→ℕ:=fun i=>if i∈hits (p x) rows then 1 else 0
    have covered: (∑i∈misses y,order i) = (hits (p x) rows\hits (p y) rows).card := by
      dsimp [order]
      rw [Finset.sum_boole]
      have eq:((misses y).filter (fun i=>i∈hits (p x) rows)) = hits (p x) rows\hits (p y) rows := by
        ext i;simp [misses];tauto
      rw [eq];rfl
    have rowOrder (i:I) : shift (p x) (rows i) ∈
        restrictWeightedOrder (fun _:σ=>1) (order i) := by
      by_cases inside:i∈hits (p x) rows
      · rw [show order i=1 by simp [order,inside],←high_eq]
        exact high_one.mpr ((shift_origin _ _).trans (hit.mp inside))
      · simp [order,inside]
    have all:=prod_mem_restrictWeightedOrder (R:=K) (w:=fun _:σ=>1) (misses y)
      (a:=order) (p:=fun i=>shift (p x) (rows i)) (fun i _=>rowOrder i)
    have base:shift (p x) (product y)∈high σ K (A-d) := by
      change _∈(high σ K (A-d)).restrictScalars K
      rw [high_eq]
      dsimp only [product];rw [map_prod]
      exact restrictWeightedOrder_anti _ (covered ▸ close) all
    change shift (p x) ((product y)^t) ∈ _
    rw [map_pow]
    exact high_pow base t

theorem separators (p:ι→σ→K) (rows:I→Pol σ K) (D:σ→ℕ) (cap:∀ i j,(rows i).degreeOf j≤D j)
    (A d t:ℕ) (enough:∀ z,A≤(hits (p z) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    ∃ sep:ι→Pol σ K,
      (∀ x j,(sep x).degreeOf j≤t*(Fintype.card I-A)*D j) ∧
      (∀ x,eval (p x) (sep x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (sep y)∈high σ K (t*(A-d))) := by
  exact ⟨separator p rows t,separator_spec p rows D cap A d t enough shared⟩

#print axioms separators
end
end Research6966.WordSurfaceMarks

end Merged_R6966ProofWordSurfaceMarks

end Merged6967_R6966ProofWordSurfaceMarks
