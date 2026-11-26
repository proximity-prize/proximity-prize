import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960CollisionMarkedDiscTransport
import ProximityPrize.SubmissionLower.R6960CollisionTameLineDegree
import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapFreeTrace
import ProximityPrize.SubmissionLower.R6966ProofGenericPhysicalCentre

section Merged6967_R6960CollisionTameBranchFrame
set_option Elab.async false




set_option Elab.async false

-- merged module R6960CollisionTameDiscriminantLocalization
section Merged_R6960CollisionTameDiscriminantLocalization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Module Matrix
open scoped Matrix BigOperators

variable {A R F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field F] [Field E] [Algebra A R] [Algebra A F] [Algebra A E] [Algebra R F] [Algebra R E] [Algebra F E]
  [IsScalarTower A R F] [IsScalarTower A R E] [IsScalarTower A F E] [IsScalarTower R F E]
  [IsFractionRing A F] [IsFractionRing R F] [FiniteDimensional F E] [Algebra.IsSeparable F E]

def integralsIncl : integralClosure A E→+*integralClosure R E :=
  Subring.inclusion (show (integralClosure A E).toSubring≤(integralClosure R E).toSubring
    from fun _ h=>(show IsIntegral A _ from h).tower_top)

theorem gram_map {ι : Type*} (u : ι→integralClosure A E) :
    (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A R) =
      tupleGram (integralTraceForm (A:=R) (E:=E) F) (fun i=>integralsIncl (R:=R) (u i)) := by
  apply Matrix.ext
  intro i j
  apply IsFractionRing.injective R F
  change algebraMap R F (algebraMap A R (integralTraceForm (A:=A) (E:=E) F (u i) (u j)))=
    algebraMap R F (integralTraceForm (A:=R) (E:=E) F (integralsIncl (u i)) (integralsIncl (u j)))
  rw [←IsScalarTower.algebraMap_apply,integralTraceForm_map,integralTraceForm_map]
  rfl

/-- The normalized discriminant ideal commutes with localization of the
base chart. Every full-size local tuple has one common denominator. -/
theorem normalizationDiscriminant_map (S : Submonoid A) [IsLocalization S R] :
    (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)=
      normalizationDiscriminant (A:=R) (E:=E) F := by
  let e := finrank F E
  let trA := integralTraceForm (A:=A) (E:=E) F
  let trR := integralTraceForm (A:=R) (E:=E) F
  let iR := (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)
  let j := algebraMap A R
  apply le_antisymm
  · apply (Ideal.map_le_iff_le_comap).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨u,rfl⟩
    change j (tupleGram trA u).det∈gramIdeal (ι:=Fin e) trR
    have det : j (tupleGram trA u).det=(tupleGram trR (fun i=>integralsIncl (u i))).det :=
      (RingHom.map_det j _).trans (congrArg Matrix.det (gram_map u))
    rw [det]
    exact gramIdeal_mem trR _
  · change gramIdeal (ι:=Fin e) trR ≤ iR
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    classical
    choose a ha using fun i : Fin e=>IsIntegral.exists_multiple_integral_of_isLocalization S (v i:E) (v i).property
    let s : S := ∏ i,a i
    have clear (i : Fin e) : IsIntegral A ((s:A) • (v i:E)) := by
      obtain ⟨t,ht⟩ : a i∣s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have es : (s:A)=(t:A)*(a i:A) := by rw [ht]; exact mul_comm _ _
      rw [es,mul_smul]
      exact (ha i).smul (t:A)
    let u (i : Fin e) : integralClosure A E := ⟨_,clear i⟩
    have scale (i : Fin e) : integralsIncl (u i)=j (s:A) • v i := by
      apply Subtype.ext
      change (s:A) • (v i:E)=_
      rw [Subalgebra.coe_smul,←IsScalarTower.algebraMap_smul R]
    have mapped : (tupleGram trA u).map j=(j (s:A))^2 • tupleGram trR v := by
      rw [gram_map,show (fun i=>integralsIncl (u i))=(fun i=>j (s:A) • v i) from funext scale,
        tupleGram_smul]
    have det : j (tupleGram trA u).det=(j (s:A))^(2*e)*(tupleGram trR v).det := by
      rw [show j (tupleGram trA u).det=((tupleGram trA u).map j).det from RingHom.map_det j _,
        mapped,det_smul,←pow_mul,Fintype.card_fin]
    have mem : j (tupleGram trA u).det∈iR := Ideal.mem_map_of_mem j (gramIdeal_mem trA u)
    rw [det] at mem
    exact (Ideal.unit_mul_mem_iff_mem iR ((IsLocalization.map_units R s).pow (2*e))).mp mem

#print axioms normalizationDiscriminant_map
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameDiscriminantLocalization

-- merged module R6960CollisionTameBranchFrame
section Merged_R6960CollisionTameBranchFrame
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Ideal IsLocalRing Module Polynomial Matrix NormalizedFiber
open scoped Polynomial Matrix BigOperators
open Lower6960.CollisionTame (gram_map integralsIncl)
open Lower6960.CollisionTame (integralClosure_torsionFree)
variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]
theorem branch_frame_trace_order {n : ℕ}
    (P : Ideal (Plane k)) [P.IsPrime] (q : Plane k) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin n→Order k E) (f : (Fin n→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (outside : g∉P) (clear : ∀ x : Order k E,∃ t,f t=g • x) :
    let T := tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u
    emultiplicity q T.det=((n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) := by
  classical
  let A := Plane k
  let F := FractionRing A
  let D := Localization.AtPrime P
  let : IsDiscreteValuationRing D := principal_prime_dvr P q pir.ne_zero span
  let : Algebra D F := (branchFractionHom (F:=F) P).toAlgebra
  let : IsFractionRing D F := branchFraction_isFractionRing (F:=F) P
  let : IsScalarTower A D F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=F) fun r=>
    (branchFractionHom_apply (F:=F) P r).symm
  let : Algebra D E := ((algebraMap F E).comp (branchFractionHom (F:=F) P)).toAlgebra
  let : IsScalarTower D F E := IsScalarTower.of_algebraMap_eq (R:=D) (S:=F) (A:=E) fun _=>rfl
  let : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=E) fun r=>by
    change algebraMap A E r=algebraMap F E (branchFractionHom P (algebraMap A D r))
    rw [branchFractionHom_apply,IsScalarTower.algebraMap_apply A F E]
  let C := integralClosure D E
  let : CommRing C := @Subalgebra.toCommRing D E _ _ (inferInstance : Algebra D E) C
  let B := Order k E
  let incl : B→+*C := Lower6960.CollisionTame.integralsIncl
  let : Algebra B C := incl.toAlgebra
  let : Algebra A C := C.algebra'
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=C) fun r=>by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply A D E r
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=B) (A:=C) fun a=>by
    apply Subtype.ext
    change algebraMap A E a=(incl (algebraMap A B a):E)
    rfl
  let : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq (R:=B) (S:=C) (A:=E) fun _=>rfl
  let M := P.primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid E M) E := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨a,ha,rfl⟩
    have nz : a≠0 := fun eq=>(Ideal.mem_primeCompl_iff.mp ha) (eq.symm ▸ P.zero_mem)
    have ainj : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ ainj).mpr nz)
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) C :=
    IsLocalization.integralClosure (S:=E) (Rf:=D) (Sf:=E) M
  let j := (IsScalarTower.toAlgHom A B C).toLinearMap
  let : IsLocalizedModule M j := inferInstanceAs (IsLocalizedModule M (IsScalarTower.toAlgHom A B C).toLinearMap)
  have jinj : Function.Injective j := fun x y eq=>Subtype.ext (congrArg (fun t : C=>(t:E)) eq)
  obtain ⟨b,basis⟩ := localized_fibre_frame (A:=A) (R:=D) (M:=B) (P:=C) M j jinj f inj
    ⟨g,Ideal.mem_primeCompl_iff.mpr outside⟩ clear
  have repr (i : Fin n) : b i=incl (u i) := by
    rw [basis]
    have l : f (Pi.single i 1)=u i := by
      rw [sum,Finset.sum_eq_single i]
      · simp
      · intro j _ ji
        simp [Ne.symm ji]
        exact zero_smul A (u j)
      · simp
    rw [l]
    rfl
  let : Module.Free D C := Module.Free.of_basis b
  let : Module.Finite D C := Module.Finite.of_basis b
  let : Module.IsTorsionFree D C := Lower6960.CollisionTame.integralClosure_torsionFree (A:=D) (E:=E) F
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  have localMatrix : T.map (algebraMap A D)=Algebra.traceMatrix D b := by
    calc
      _ = tupleGram (integralTraceForm (A:=D) (E:=E) F) (fun i=>incl (u i)) :=
        Lower6960.CollisionTame.gram_map (A:=A) (R:=D) (F:=F) (E:=E) u
      _ = _ := by
        rw [show (fun i=>incl (u i))=(b:Fin n→C) from funext fun i=>(repr i).symm]
        apply Matrix.ext
        intro i j
        change Algebra.intTrace D C (b i*b j)=Algebra.trace D C (b i*b j)
        rw [Algebra.intTrace_eq_trace]
  let charMap : k→+*ResidueField D := (residue D).comp ((algebraMap A D).comp (Polynomial.C.comp Polynomial.C))
  let : CharP (ResidueField D) p := charP_of_injective_ringHom charMap.injective p
  have h := trace_order_from_local_matrix P q pir span p small b T localMatrix
  simpa only [Fintype.card_fin] using h
#print axioms branch_frame_trace_order
end
end Lower6960.CollisionTame

end Merged_R6960CollisionTameBranchFrame

end Merged6967_R6960CollisionTameBranchFrame

section Merged6967_R6966ProofAffineMarkRows
set_option Elab.async false



set_option Elab.async false

namespace Research6966.AffineMarkRows
open Polynomial Finset
open NonlinearMarkRows (Eqn evaluate)
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds GenericPhysicalCentre.physical

abbrev S (σ F:Type*) [CommSemiring F] := MvPolynomial σ F
private abbrev within (w:σ→ℕ) (u:ℕ) := MvPolynomial.restrictWeightAtMost (R:=F) w u

private theorem dx {w:σ→ℕ} {u:ℕ} {P:S σ F} (cap:P∈within w u) : Differential.deriv P∈within w u := by
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro e he
  apply MvPolynomial.mem_restrictWeightAtMost.mp cap e (MvPolynomial.mem_support_iff.mpr ?_)
  intro z
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,z,map_zero])

theorem pair_cap (w:σ→ℕ) (A B C₀:S σ F) (u n:ℕ) (hA:A∈within w u) (hB:B∈within w u) (hC:C₀∈within w u) :
    (AffineODE.pair Differential.deriv A B C₀ n).1∈within w (n*u) ∧
      (AffineODE.pair Differential.deriv A B C₀ n).2∈within w (n*u) := by
  induction n with
  | zero=>
    simp only [AffineODE.pair,zero_mul]
    exact ⟨MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl (1:F),Submodule.zero_mem _⟩
  | succ n ih=>
    have step {l m g:S σ F} (hl:l∈within w (n*u)) (hm:m∈within w (n*u)) (hg:g∈within w u) :
        A*Differential.deriv m-(n:S σ F)*Differential.deriv A*m+g*l∈within w ((n+1)*u) := by
      rw [Nat.succ_mul,Nat.add_comm (n*u) u]
      apply Submodule.add_mem _ _ (MvPolynomial.mul_mem_restrictWeightAtMost hg hl)
      apply Submodule.sub_mem _ (MvPolynomial.mul_mem_restrictWeightAtMost hA (dx hm))
      rw [mul_assoc,←nsmul_eq_mul]
      exact nsmul_mem (MvPolynomial.mul_mem_restrictWeightAtMost (dx hA) hm) n
    exact ⟨step ih.1 ih.1 hB,step ih.1 ih.2 hC⟩

private theorem response_cap (w:σ→ℕ) (A:S σ F) (u d:ℕ) (weights:ℕ→F) (P:ℕ→S σ F)
    (hA:A∈within w u) (hP:∀i,P i∈within w (i*u)) :
    AffineODE.response d (fun i=>MvPolynomial.C (weights i)) A P∈within w (d*u) := by
  unfold AffineODE.response
  apply Submodule.sum_mem
  intro j hj
  rw [mul_assoc,←MvPolynomial.smul_eq_C_mul]
  apply Submodule.smul_mem
  have cap:=MvPolynomial.mul_mem_restrictWeightAtMost (MvPolynomial.pow_mem_restrictWeightAtMost hA (d-j)) (hP j)
  have cast : (d-j) • u + j*u=d*u := by
    change (d-j)*u+j*u=d*u
    rw [←Nat.add_mul,Nat.sub_add_cancel (Nat.le_of_lt_succ (mem_range.mp hj))]
  rwa [cast] at cap

def row (A B C₀:S σ F) (d:ℕ) (origin x received:F) : Eqn σ F :=
  let wt:=fun i=>MvPolynomial.C ((x-origin)^i/(i.factorial:F))
  let lr:=AffineODE.response d wt A (fun i=>(AffineODE.pair Differential.deriv A B C₀ i).1)
  let cr:=AffineODE.response d wt A (fun i=>(AffineODE.pair Differential.deriv A B C₀ i).2)
  C lr*Polynomial.X+C (cr-MvPolynomial.C received*A^d)

private theorem linear_degree (a b:S σ F) : (C a*Polynomial.X+C b).natDegree≤1 :=
  (natDegree_add_le (C a*Polynomial.X) (C b)).trans
    (max_le ((show (C a*Polynomial.X).natDegree≤(C a).natDegree+(Polynomial.X:Eqn σ F).natDegree from natDegree_mul_le).trans (by simp))
      (by rw [natDegree_C];decide))

private theorem linear_cap {w:σ→ℕ} {u:ℕ} {a b:S σ F} (ha:a∈within w u) (hb:b∈within w u) :
    NonlinearMarkDegrees.cap w u (C a*Polynomial.X+C b) := by
  intro i
  rw [C_mul_X_eq_monomial,coeff_add,coeff_monomial,coeff_C,Finsupp.single_apply]
  split <;> split
  all_goals first
    | exact Submodule.add_mem _ ha hb
    | simpa only [zero_add,add_zero] using ha
    | simpa only [zero_add,add_zero] using hb
    | simpa only [zero_add] using (Submodule.zero_mem (within (F:=F) w u))

theorem row_degree (A B C₀:S σ F) (d:ℕ) (origin x received:F) :
    (row A B C₀ d origin x received).natDegree≤1 := by
  exact linear_degree _ _

theorem row_cap (w:σ→ℕ) (A B C₀:S σ F) (u d:ℕ) (hA:A∈within w u) (hB:B∈within w u) (hC:C₀∈within w u)
    (origin x received:F) : NonlinearMarkDegrees.cap w (d*u) (row A B C₀ d origin x received) := by
  let wt:=fun i:ℕ=>(x-origin)^i/(i.factorial:F)
  have lin:=response_cap w A u d wt _ hA (fun i=>(pair_cap w A B C₀ u i hA hB hC).1)
  have const:=response_cap w A u d wt _ hA (fun i=>(pair_cap w A B C₀ u i hA hB hC).2)
  have den:MvPolynomial.C received*A^d∈within w (d*u) := by
    rw [←MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (MvPolynomial.pow_mem_restrictWeightAtMost hA d)
  exact linear_cap lin (Submodule.sub_mem _ const den)

private theorem entries (p:σ→F) (fixed:∀ i,Differential.deriv (p i)=0) (A B C₀:S σ F) (y:F)
    (original:MvPolynomial.eval p A*Differential.deriv y=MvPolynomial.eval p B*y+MvPolynomial.eval p C₀) (i:ℕ) :
    MvPolynomial.eval p A^i*Differential.deriv^[i] y=
      MvPolynomial.eval p (AffineODE.pair Differential.deriv A B C₀ i).1*y+
      MvPolynomial.eval p (AffineODE.pair Differential.deriv A B C₀ i).2 := by
  exact AffineODE.cleared_derivatives Differential.deriv Differential.deriv.toAddMonoidHom (MvPolynomial.eval p)
    (by change Differential.deriv (1:F)=0;simp) (by
      intro a b
      change Differential.deriv (a*b)=Differential.deriv a*b+a*Differential.deriv b
      rw [Derivation.leibniz];simp [smul_eq_mul,mul_comm,add_comm])
    (GenericPhysicalCentre.deriv_eval p fixed) A B C₀ y original i

variable {K:Type*} [Field K]
private abbrev E:=GenericPhysicalCentre.Frac K
private abbrev incl:=algebraMap K[X] (E (K:=K))

theorem detects (p:σ→E (K:=K)) (fixed:∀i,Differential.deriv (p i)=0) (A B C₀:S σ E)
    (P:K[X]) (d:ℕ) (degree:P.natDegree≤d) (fac:∀ j≤d,(j.factorial:E (K:=K))≠0)
    (x received:E (K:=K)) (law:MvPolynomial.eval p A*incl P.derivative=MvPolynomial.eval p B*incl P+MvPolynomial.eval p C₀)
    (den:MvPolynomial.eval p A≠0) :
    evaluate p (incl P) (row A B C₀ d (incl Polynomial.X) x received)=0 ↔
      (P.map (algebraMap K _)).eval x=received := by
  let y:=incl P
  let D: E (K:=K)→+E (K:=K):=Differential.deriv.toAddMonoidHom
  let ev:=MvPolynomial.eval p
  let wt (i:ℕ):S σ (E (K:=K)):=MvPolynomial.C ((x-incl Polynomial.X)^i/(i.factorial:E (K:=K)))
  let data :=AffineODE.pair Differential.deriv A B C₀
  have original:ev A*D y=ev B*y+ev C₀:=by
    change ev A*Differential.deriv (incl P)=_
    rw [GenericPhysicalCentre.physical_poly];exact law
  have jet (i:ℕ):ev A^i*D^[i] y=ev (data i).1*y+ev (data i).2 :=
    entries p fixed A B C₀ y original i
  have full:=AffineODE.common_denominator A ev y (fun i=>(data i).1) (fun i=>(data i).2) (fun i=>D^[i] y) d wt (fun i _=>jet i)
  have tay:=NonlinearMarkRows.taylor_at_generic P x d degree fac
  have scalar (i):ev (wt i)=(x-incl Polynomial.X)^i/(i.factorial:E (K:=K)):=MvPolynomial.eval_C _
  simp_rw [scalar] at full
  change ev A^d*(∑i∈range (d+1),((x-incl Polynomial.X)^i/(i.factorial:E (K:=K)))*Differential.deriv^[i] (incl P))=_ at full
  rw [←tay] at full
  let l:=AffineODE.response d wt A (fun i=>(data i).1)
  let m:=AffineODE.response d wt A (fun i=>(data i).2)
  change (eval₂RingHom ev y) (C l*Polynomial.X+C (m-MvPolynomial.C received*A^d))=0 ↔ _
  simp only [coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,eval₂_X]
  rw [map_sub ev,map_mul ev,map_pow ev,show ev (MvPolynomial.C received)=received from MvPolynomial.eval_C _]
  change ev (AffineODE.response d wt A _)*y+(ev (AffineODE.response d wt A _)-received*ev A^d)=0 ↔ _
  rw [←add_sub_assoc,←full,mul_comm received,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ den),sub_eq_zero]

#print axioms row_cap
#print axioms detects
end
end Research6966.AffineMarkRows

end Merged6967_R6966ProofAffineMarkRows

section Merged6967_R6966ProofFixedNodeRows
set_option Elab.async false




set_option Elab.async false

namespace Research6966.FixedNodeRows
open Polynomial Finset Module
open WordSurfaceJets (Pol)
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false

variable {K σ:Type*} [Field K]
abbrev Coeff (σ K:Type*) [Field K] := MvPolynomial σ K[X]
abbrev Row (σ K:Type*) [Field K] := (Coeff σ K)[X]

private def makeDifferential {R:Type*} [CommRing R] (D:R→+R) (mul:∀a b,D (a*b)=a*D b+b*D a) : Differential R where
  deriv:=Derivation.mk' D.toIntLinearMap (fun a b=>mul a b)

@[instance_reducible] def ordinary (K:Type*) [Field K] : Differential K[X] :=
  makeDifferential Polynomial.derivative.toAddMonoidHom (fun a b=>by
    change (a*b).derivative=a*b.derivative+b*a.derivative
    rw [Polynomial.derivative_mul];ring)
attribute [local instance] ordinary GenericPhysicalCentre.seeds

def evaluate (z:σ→K) (y:K[X]) : Row σ K→+*K[X] :=
  eval₂RingHom (MvPolynomial.eval (fun i=>C (z i))) y

def centre (x y:K) : Row σ K→+*MvPolynomial σ K :=
  eval₂RingHom (MvPolynomial.map (evalRingHom x)) (MvPolynomial.C y)

theorem specialize (z:σ→K) (S:K[X]) (x:K) :
    (MvPolynomial.eval z).comp (centre x (S.eval x))=(evalRingHom x).comp (evaluate z S) := by
  apply Polynomial.ringHom_ext
  · intro p
    have base:(MvPolynomial.eval z).comp (MvPolynomial.map (evalRingHom x))=
        (evalRingHom x).comp (MvPolynomial.eval (fun i=>C (z i))) := by
      apply MvPolynomial.ringHom_ext
      · intro c;simp
      · intro i;simp
    simpa only [centre,evaluate,RingHom.comp_apply,coe_eval₂RingHom,eval₂_C] using RingHom.congr_fun base p
  · simp [centre,evaluate]

private theorem center_degree (x y:K) {P:Row σ K} {u:ℕ}
    (bound:∀ i,(P.coeff i).totalDegree≤u) : (centre x y P).totalDegree≤u := by
  change (P.eval₂ (MvPolynomial.map (evalRingHom x)) (MvPolynomial.C y)).totalDegree≤_
  rw [eval₂_eq_sum,Polynomial.sum_def]
  apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le _)
  intro i _
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [←map_pow,MvPolynomial.totalDegree_C,add_zero]
  exact (Finset.sup_mono (MvPolynomial.support_map_subset (evalRingHom x) (P.coeff i))).trans (bound i)

private theorem deriv_total (P:Coeff σ K) : (Differential.deriv P).totalDegree≤P.totalDegree := by
  apply Finset.sup_le
  intro e he
  apply MvPolynomial.le_totalDegree
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,zero,map_zero])

def coeffAt (A B:Row σ K) (d:ℕ) (x₀ y₀:K) : ℕ→MvPolynomial σ K
  | 0=>MvPolynomial.C y₀*(centre x₀ y₀ A)^(2*d-1)
  | j+1=>centre x₀ y₀ (QuadraticWeight.numerator A B j)*(centre x₀ y₀ A)^(2*d-1-(2*j+1))

def test (A B:Row σ K) (d:ℕ) (x₀ y₀ x answer:K) : MvPolynomial σ K :=
  (∑ j∈range (d+1),MvPolynomial.C ((x-x₀)^j/(j.factorial:K))*coeffAt A B d x₀ y₀ j)-
    MvPolynomial.C answer*(centre x₀ y₀ A)^(2*d-1)

theorem test_degree (A B:Row σ K) (d u:ℕ) (x₀ y₀ x answer:K) (ha:∀ i,(A.coeff i).totalDegree≤u)
    (hb:∀ i,(B.coeff i).totalDegree≤u) : (test A B d x₀ y₀ x answer).totalDegree≤(2*d-1)*u := by
  let k:=2*d-1
  have den:(centre x₀ y₀ A).totalDegree≤u:=center_degree x₀ y₀ ha
  have power (n:ℕ):((centre x₀ y₀ A)^n).totalDegree≤n*u :=
    (MvPolynomial.totalDegree_pow ..).trans (Nat.mul_le_mul_left n den)
  have cap (j:ℕ) (le:j≤d):(coeffAt A B d x₀ y₀ j).totalDegree≤k*u := by
    cases j with
    | zero=>exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact power k)
    | succ j=>
      have num:=center_degree x₀ y₀ (QuadraticWeight.coefficient_degree A B u deriv_total ha hb j)
      exact (MvPolynomial.totalDegree_mul ..).trans
        ((Nat.add_le_add num (power (k-(2*j+1)))).trans_eq (by rw [←Nat.add_mul];congr 1;dsimp [k];omega))
  unfold test
  apply (MvPolynomial.totalDegree_sub ..).trans (max_le _ _)
  · apply (MvPolynomial.totalDegree_finsetSum ..).trans (Finset.sup_le _)
    intro j hj
    exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact cap j (Nat.le_of_lt_succ (mem_range.mp hj)))
  · exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact power k)

theorem test_detects (z:σ→K) (S:K[X]) (x₀ y₀ x answer:K) (hit:S.eval x₀=y₀) (A B:Row σ K)
    (law:evaluate z S A*S.derivative=evaluate z S B) (regular:(evaluate z S A).eval x₀≠0)
    (d:ℕ) (deg:S.natDegree≤d) (fac:∀ j≤d,(j.factorial:K)≠0) :
    MvPolynomial.eval z (test A B d x₀ y₀ x answer)=0 ↔ S.eval x=answer := by
  subst y₀
  let e:=MvPolynomial.eval z
  let v:=evaluate z S
  let a:=(v A).eval x₀
  have comm (P:Row σ K):e (centre x₀ (S.eval x₀) P)=(v P).eval x₀ :=
    RingHom.congr_fun (specialize z S x₀) P
  have entry (j:ℕ) (le:j≤d):e (coeffAt A B d x₀ (S.eval x₀) j)=a^(2*d-1)*(Polynomial.derivative^[j] S).eval x₀ := by
    cases j with
    | zero=>rw [coeffAt,map_mul,map_pow,comm];simp [e,a,mul_comm]
    | succ j=>
      letI : Algebra (Coeff σ K) K[X] := (MvPolynomial.eval (fun i=>C (z i))).toAlgebra
      letI : DifferentialAlgebra (Coeff σ K) K[X] := ⟨fun P=>GenericPhysicalCentre.deriv_eval
        (fun i=>C (z i)) (fun i=>Polynomial.derivative_C) P⟩
      have raw:=QuadraticWeight.cleared A B S law j
      have dj (n:ℕ):Differential.deriv^[n] S=Polynomial.derivative^[n] S:=rfl
      change v A^(2*j+1)*Differential.deriv^[j+1] S=v (QuadraticWeight.numerator A B j) at raw
      have evaluated:=congrArg (evalRingHom x₀) raw
      simp only [map_mul,map_pow,coe_evalRingHom,dj] at evaluated
      rw [coeffAt,map_mul,map_pow,comm,comm,←evaluated,mul_right_comm,←pow_add]
      rw [show 2*j+1+(2*d-1-(2*j+1))=2*d-1 by omega]
  change e (test A B d x₀ (S.eval x₀) x answer)=0 ↔ _
  rw [test,map_sub,map_sum,map_mul,map_pow,comm]
  have value:e (MvPolynomial.C answer)=answer:=MvPolynomial.eval_C _
  have sum:(∑j∈range (d+1),e (MvPolynomial.C ((x-x₀)^j/(j.factorial:K))*coeffAt A B d x₀ (S.eval x₀) j))=
      a^(2*d-1)*S.eval x := by
    rw [AffineODE.evaluation_from_derivatives S x₀ x d deg fac,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [map_mul,entry j (Nat.le_of_lt_succ (mem_range.mp hj)),show e (MvPolynomial.C ((x-x₀)^j/(j.factorial:K)))=_ from MvPolynomial.eval_C _]
    ring
  rw [sum,value,mul_comm answer,←mul_sub,mul_eq_zero,or_iff_right (pow_ne_zero _ regular),sub_eq_zero]

#print axioms test_degree
#print axioms test_detects
end
end Research6966.FixedNodeRows

end Merged6967_R6966ProofFixedNodeRows

section Merged6967_R6966ProofWordAxisPrice
set_option Elab.async false


set_option Elab.async false

namespace Research6966.WordAxisPrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceMarks
variable {σ τ K ι I : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 600000

/-- Only the variables used by the nodal rows are needed for their separator
interpolation. Restricting to these variables preserves every hit set. -/
theorem restrict_axes (p : ι → σ → K) (rows : I → Pol σ K) (f : τ ↪ σ)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0) :
    ∃ projected : I → Pol τ K,
      (∀ i j, (projected i).degreeOf j = (rows i).degreeOf (f j)) ∧
      ∀ x, hits (p x ∘ f) projected = hits (p x) rows := by
  classical
  have supported (i : I) : (↑(rows i).vars : Set σ) ⊆ Set.range f := by
    intro j hj
    by_contra hn
    exact (mem_vars_iff_degreeOf_ne_zero.mp hj) (keep i j hn)
  choose projected hr using fun i => exists_rename_eq_of_vars_subset_range (rows i) f f.injective (supported i)
  refine ⟨projected, ?_, ?_⟩
  · intro i j
    rw [← hr i, degreeOf_rename_of_injective f.injective]
  · intro x
    ext i
    rw [hit, hit, ← hr i, eval_rename]

private theorem footprint (p : ι → σ → K) (rows : I → Pol σ K) (h : σ → ℕ) (A d : ℕ)
    (gap : d < A) (height : ∀ i j, (rows i).degreeOf j ≤ h j)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι * finrank K (Local σ K (A-d)) ≤
      ∏ j, WordSurfacePrice.side (Fintype.card I) A d (h j) := by
  classical
  let k := A-d
  have pos : 0 < k := by dsimp [k]; omega
  obtain ⟨sep, cap, own, other⟩ := separators p rows h height A d 1 enough shared
  simp only [one_mul] at cap other
  have onto := interpolate p k pos _ sep cap own other
  have rank := LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype, sum_const, card_univ, smul_eq_mul, rectangle_dimension] at rank
  have scale (j : σ) :
      (Fintype.card I-A)*h j+(k-1)+1 = WordSurfacePrice.side (Fintype.card I) A d (h j) := by
    rw [Nat.add_assoc, Nat.sub_add_cancel pos]
    rfl
  simpa only [scale] using rank

theorem two (p : ι → σ → K) (rows : I → Pol σ K) (f : Fin 2 ↪ σ) (h : Fin 2 → ℕ)
    (A d : ℕ) (gap : d < A) (height : ∀ i j, (rows i).degreeOf (f j) ≤ h j)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι*(A-d)^2 ≤ 2*WordSurfacePrice.side (Fintype.card I) A d (h 0)*
      WordSurfacePrice.side (Fintype.card I) A d (h 1) := by
  obtain ⟨projected, caps, test⟩ := restrict_axes p rows f keep
  have rank := footprint (fun x => p x ∘ f) projected h A d gap
    (fun i j => (caps i j).le.trans (height i j)) (fun x => (test x) ▸ enough x)
    (fun x y ne => by rw [test x, test y]; exact shared x y ne)
  let k := A-d
  have kp : 0 < k := by dsimp [k]; omega
  have dim : finrank K (Local (Fin 2) K k) = (k+1).choose 2 := by
    have v := local_dimension (σ := Fin 2) (K := K) (k-1)
    rw [Nat.sub_add_cancel kp, Fintype.card_fin] at v
    rwa [show k-1+2=k+1 by omega] at v
  rw [dim, Fin.prod_univ_two] at rank
  have eq := Nat.choose_succ_right_eq (k+1) 1
  rw [Nat.choose_one_right, Nat.add_sub_cancel] at eq
  have lower : k^2 ≤ 2*(k+1).choose 2 := by nlinarith
  refine (Nat.mul_le_mul_left _ lower).trans ?_
  nlinarith only [Nat.mul_le_mul_right 2 rank]

theorem one (p : ι → σ → K) (rows : I → Pol σ K) (f : Fin 1 ↪ σ) (h A d : ℕ)
    (gap : d < A) (height : ∀ i, (rows i).degreeOf (f 0) ≤ h)
    (keep : ∀ i j, j ∉ Set.range f → (rows i).degreeOf j = 0)
    (enough : ∀ x, A ≤ (hits (p x) rows).card)
    (shared : ∀ x y, x ≠ y → ((hits (p x) rows) ∩ (hits (p y) rows)).card ≤ d) :
    Fintype.card ι*(A-d) ≤ WordSurfacePrice.side (Fintype.card I) A d h := by
  obtain ⟨projected, caps, test⟩ := restrict_axes p rows f keep
  have rank := footprint (fun x => p x ∘ f) projected (fun _ => h) A d gap
    (fun i j => by rw [caps, Subsingleton.elim j (0:Fin 1)]; exact height i)
    (fun x => (test x) ▸ enough x)
    (fun x y ne => by rw [test x, test y]; exact shared x y ne)
  let k := A-d
  have kp : 0 < k := by dsimp [k]; omega
  have dim : finrank K (Local (Fin 1) K k) = k := by
    have v := local_dimension (σ := Fin 1) (K := K) (k-1)
    rw [Nat.sub_add_cancel kp, Fintype.card_fin, Nat.choose_one_right] at v
    rwa [Nat.sub_add_cancel kp] at v
  change Fintype.card ι * finrank K (Local (Fin 1) K k) ≤ _ at rank
  simpa only [dim, Fin.prod_univ_one] using rank

#print axioms two
#print axioms one
end
end Research6966.WordAxisPrice

end Merged6967_R6966ProofWordAxisPrice
