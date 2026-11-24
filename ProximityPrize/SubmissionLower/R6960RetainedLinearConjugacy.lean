import ProximityPrize.SubmissionLower.R6960RetainedLinearFactor
import Mathlib.RingTheory.AdjoinRoot

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2700000

namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private theorem base_injective : Function.Injective (base (F:=F) (E:=E)) :=
  (incl_injective E).comp (constants_injective (F:=F) (E:=E))

private theorem adjoint_conjugates {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (b : (Polynomial F)) (x t : F) {r s : Fn E} (hr : r∈(geometric (E:=E) P).roots)
    (hs : s∈(geometric (E:=E) P).roots) :
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(r-base (C t))/(base (Polynomial.X-C x))) →
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(s-base (C t))/(base (Polynomial.X-C x))) := by
  let Q := arithmetic P
  letI : Fact (Irreducible Q) := ⟨arithmetic_irred ir pos⟩
  let j := (AdjoinRoot.of Q).comp (incl F)
  let u : AdjoinRoot Q := j b*(AdjoinRoot.root Q-j (C t))/j (Polynomial.X-C x)
  have raw (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      Q.eval₂ (rationalConstants (F:=F) (E:=E)) a=0 := by
    have injective : Function.Injective (Polynomial.mapRingHom (base (F:=F) (E:=E))) :=
      Polynomial.map_injective _ base_injective
    have nonzero : geometric (E:=E) P≠0 := (map_ne_zero_iff _ injective).mpr ir.ne_zero
    have ez := (mem_roots nonzero).mp ha
    change (geometric (E:=E) P).eval a=0 at ez
    rw [geometric_map,eval_map] at ez
    exact ez
  let lift (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :=
    AdjoinRoot.lift (rationalConstants (F:=F) (E:=E)) a (raw a ha)
  have extends_base (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      (lift a ha).comp j=base (F:=F) (E:=E) := by
    apply RingHom.ext
    intro a'
    dsimp [lift,j]
    rw [AdjoinRoot.lift_of,rationalConstants_incl]
    rfl
  have eq (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      lift a ha u=base b*(a-base (C t))/base (Polynomial.X-C x) := by
    simp only [u,map_div₀,map_mul,map_sub]
    have root : lift a ha (AdjoinRoot.root Q)=a := AdjoinRoot.lift_root (raw a ha)
    have one (v : (Polynomial F)) : lift a ha (j v)=base v := DFunLike.congr_fun (extends_base a ha) v
    simp only [root,one]
  intro original
  have at_r : ((lift r hr).comp j).IsIntegralElem (lift r hr u) := by
    rwa [extends_base r hr,eq r hr]
  have integral : j.IsIntegralElem u :=
    at_r.of_map (lift r hr).injective
  have at_s := integral.map (lift s hs)
  rwa [extends_base s hs,eq s hs] at at_s

/-- Lift the received ordinate along one primitive branch. Every conjugate
has a common arithmetic denominator and the same physical residue. -/
theorem common_numerators [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧
      ∀ r∈(geometric (E:=E) P).roots, ∃ a : (Polynomial E),
        incl E a=base b*r ∧
        a.eval (algebraMap F E x)=algebraMap F E (b.eval x)*algebraMap F E t := by
  obtain ⟨r,hr,rden,rt⟩ := exists_regular_root (E:=E) ir pos splits x t hit
  obtain ⟨b,hb,m,hm⟩ := base_multiple x (denominator r) rden
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let pX : (Polynomial E) := Polynomial.X-C x'
  have pX_image : base (Polynomial.X-C x) = incl E pX := by
    simp [base,constants,pX,x']
  have x_nonzero : base (E:=E) (Polynomial.X-C x)≠0 :=
    (map_ne_zero_iff _ base_injective).mpr (X_sub_C_ne_zero _)
  have t_image : base (C t)=incl E (C t') := by simp [base,constants,t']
  have exact_root : pX ∣ numerator r-C t'*denominator r := by
    apply dvd_iff_isRoot.mpr
    change (numerator r-C t'*denominator r).eval x'=0
    rw [eval_sub,eval_mul,eval_C,rt]
    ring
  obtain ⟨c,hc⟩ := exact_root
  have b_image : base b=incl E (denominator r*m) := by
    change incl E (constants b)=_
    rw [hm]
  have b_slope : base b*(r-base (C t))/base (Polynomial.X-C x)=incl E (c*m) := by
    apply (div_eq_iff x_nonzero).mpr
    calc
      _ = incl E ((numerator r-C t'*denominator r)*m) := by
        rw [b_image,t_image]
        simp only [map_mul,map_sub]
        rw [← numerator_eq r]
        ring
      _ = _ := by rw [hc,pX_image]; simp only [map_mul]; ring
  have regular : (base (F:=F) (E:=E)).IsIntegralElem
      (base b*(r-base (C t))/base (Polynomial.X-C x)) := by
    rw [b_slope]
    exact polynomial_integral (c*m)
  refine ⟨b,hb,?_⟩
  intro s hs
  have h := adjoint_conjugates ir pos b x t hr hs regular
  obtain ⟨n,hn⟩ := integral_is_polynomial h
  let a := constants (E:=E) b*C t'+pX*n
  have eq : base b*(s-base (C t))=incl E n*base (Polynomial.X-C x) :=
    (div_eq_iff x_nonzero).mp hn.symm
  refine ⟨a,?_ ,?_⟩
  · unfold a
    simp only [map_add,map_mul]
    have b_incl : incl E (constants (E:=E) b)=base b := rfl
    rw [b_incl,← t_image,← pX_image]
    linear_combination -eq
  · simp [a,pX,x',t',eval_constants]

#print axioms common_numerators
end
end Lower6960.RetainedLinear
