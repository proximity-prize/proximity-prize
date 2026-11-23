import ProximityPrize.SubmissionLower.R6960LineEuler

set_option Elab.async false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Module
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Evaluation at the chosen finite point `t=0` is the constant Laurent
coefficient of a global section in the finite frame. -/
def crossingEval (G : Matrix ι ι (Laurent k)) : H0 G →ₗ[k] (ι→k) :=
  LinearMap.pi fun i=>(Finsupp.lapply (0:ℤ)).comp ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp
    ((LinearMap.proj i).comp (finiteLattice k ι⊓transitionLattice G).subtype))

@[simp] theorem crossingEval_apply (G : Matrix ι ι (Laurent k)) (v : H0 G) (i : ι) :
    crossingEval G v i=(v.1 i).coeff 0 := rfl

/-- Requiring a zero at `t=0` factors out one `t` in the finite frame,
which subtracts one from the exponent of the transition at infinity. -/
def negativeTwist (G : Matrix ι ι (Laurent k)) : Matrix ι ι (Laurent k) :=
  (T (R:=k) (-1)) • G

private def shiftLaurent (m : ℤ) : (ι→Laurent k) →ₗ[k] ι→Laurent k :=
  LinearMap.pi fun i=>(LinearMap.mul k (Laurent k) (T m)).comp (LinearMap.proj i)

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftLaurent_apply (m : ℤ) (w : ι→Laurent k) (i : ι) :
    shiftLaurent m w i=T m*w i := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem shift_inverse (m : ℤ) (w : ι→Laurent k) :
    shiftLaurent (-m) (shiftLaurent m w)=w := by
  funext i
  rw [shiftLaurent_apply,shiftLaurent_apply,←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul]

private theorem shift_transition (m : ℤ) (G : Matrix ι ι (Laurent k)) :
    transitionLattice ((T (R:=k) m) • G)=(transitionLattice G).map (shiftLaurent m) := by
  have eval (x : ι→Laurent k) : Matrix.toLin' ((T (R:=k) m) • G) x = shiftLaurent m (Matrix.toLin' G x) := by
    funext i
    rw [Matrix.toLin'_apply,shiftLaurent_apply,Matrix.toLin'_apply]
    change (∑ j,((T (R:=k) m) • G) i j * x j) = T m * ∑ j,G i j*x j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _=>by simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc]
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Matrix.toLin' G x,⟨x,hx,rfl⟩,(eval x).symm⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,eval x⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem shift_one_finite {w : ι→Laurent k} (hw : w∈finiteLattice k ι) :
    shiftLaurent 1 w∈finiteLattice k ι := by
  intro i hi
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro n hn
  rw [shiftLaurent_apply,coeff_shift]
  apply (AddMonoidAlgebra.mem_supported'.mp (hw i hi))
  change ¬0≤n at hn
  change ¬0≤n-1
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem shift_minus_one_finite {w : ι→Laurent k} (hw : w∈finiteLattice k ι)
    (zero : ∀ i,(w i).coeff 0=0) : shiftLaurent (-1) w∈finiteLattice k ι := by
  intro i hi
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro n hn
  rw [shiftLaurent_apply,coeff_shift]
  change ¬0≤n at hn
  by_cases eq : n=-1
  · simpa only [eq,sub_self] using zero i
  · exact (AddMonoidAlgebra.mem_supported'.mp (hw i hi)) _ (by change ¬0≤n-(-1); omega)

/-- The kernel of simple crossing evaluation is exactly the section
space of the negative twist. -/
def crossingKernel (G : Matrix ι ι (Laurent k)) : H0 (negativeTwist G) ≃ₗ[k] (crossingEval G).ker := by
  have shift : transitionLattice (negativeTwist G)=(transitionLattice G).map (shiftLaurent (-1)) :=
    shift_transition (-1) G
  let mapIn : H0 (negativeTwist G) →ₗ[k] (ι→Laurent k) :=
    (shiftLaurent 1).comp (finiteLattice k ι⊓transitionLattice (negativeTwist G)).subtype
  have inH0 (w : H0 (negativeTwist G)) : mapIn w∈finiteLattice k ι⊓transitionLattice G := by
    refine ⟨shift_one_finite w.property.1,?_⟩
    have hw : (w:ι→Laurent k)∈(transitionLattice G).map (shiftLaurent (-1)) := shift ▸ w.property.2
    obtain ⟨v,hv,h⟩ := hw
    have inverse := shift_inverse (-1) v
    change shiftLaurent 1 (shiftLaurent (-1) v)=v at inverse
    change shiftLaurent 1 (w:ι→Laurent k)∈transitionLattice G
    rw [←h,inverse]
    exact hv
  let toH0 := mapIn.codRestrict (finiteLattice k ι⊓transitionLattice G) inH0
  have toKer (w : H0 (negativeTwist G)) : toH0 w∈(crossingEval G).ker := by
    apply LinearMap.mem_ker.mpr
    funext i
    change (shiftLaurent 1 (w:ι→Laurent k) i).coeff 0=0
    rw [shiftLaurent_apply,coeff_shift]
    exact (AddMonoidAlgebra.mem_supported'.mp (w.property.1 i (Set.mem_univ _))) _ (by decide)
  let toKernel := toH0.codRestrict (crossingEval G).ker toKer
  refine LinearEquiv.ofBijective toKernel ⟨?_,?_⟩
  · intro x y eq
    have same : shiftLaurent 1 (x:ι→Laurent k)=shiftLaurent 1 (y:ι→Laurent k) :=
      congrArg (fun w : (crossingEval G).ker=>(w.1:ι→Laurent k)) eq
    exact Subtype.ext (by simpa only [shift_inverse] using congrArg (shiftLaurent (-1)) same)
  · intro x
    let w : ι→Laurent k := shiftLaurent (-1) (x.1:ι→Laurent k)
    have zero (i : ι) : ((x.1:ι→Laurent k) i).coeff 0=0 :=
      congrFun (LinearMap.mem_ker.mp x.property) i
    have h : w∈finiteLattice k ι⊓transitionLattice (negativeTwist G) := by
      refine ⟨shift_minus_one_finite x.1.property.1 zero,?_⟩
      rw [shift]
      exact ⟨_,x.1.property.2,rfl⟩
    refine ⟨⟨w,h⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact shift_inverse (-1) (x.1:ι→Laurent k)

private theorem negative_degree (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    IsUnit (negativeTwist G) ∧ ∃ d : ℤ,G.det.degree=(d:WithBot ℤ) ∧
      (negativeTwist G).det.degree=((d-Fintype.card ι:ℤ):WithBot ℤ) := by
  have ud := (Matrix.isUnit_iff_isUnit_det G).mp unit
  have ut : IsUnit (T (R:=k) (-1)) := isUnit_of_invertible _
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr ?_,?_⟩
  · rw [negativeTwist,Matrix.det_smul]
    exact (ut.pow _).mul ud
  · obtain ⟨c,d,nonzero,eq⟩ := unit_monomial G.det ud
    have twist : (negativeTwist G).det=LaurentPolynomial.C c*T (d-Fintype.card ι) := by
      rw [negativeTwist,Matrix.det_smul,eq,T_pow,mul_left_comm,←T_add]
      congr 2
      omega
    exact ⟨d,by rw [eq,degree_C_mul_T _ _ nonzero],by rw [twist,degree_C_mul_T _ _ nonzero]⟩

/-- The increase in the dimension of first cohomology obeys the exact
one-point rank formula for the finite-frame evaluation map. -/
theorem crossing_rank (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    (finrank k (H1 (negativeTwist G)):ℤ)-(finrank k (H1 G):ℤ)=
      (Fintype.card ι:ℤ)-(finrank k (crossingEval G).range:ℤ) := by
  obtain ⟨twist_unit,d,deg,ddeg⟩ := negative_degree G unit
  obtain ⟨finite,_,m,hm,chi⟩ := euler_index G unit
  obtain ⟨_,_,n,hn,chi'⟩ := euler_index (negativeTwist G) twist_unit
  have meq : m=d := WithBot.coe_inj.mp (hm.symm.trans deg)
  have neq : n=d-Fintype.card ι := WithBot.coe_inj.mp (hn.symm.trans ddeg)
  have rank := LinearMap.finrank_range_add_finrank_ker (crossingEval G)
  rw [←(crossingKernel G).finrank_eq] at rank
  omega

#print axioms crossingKernel
#print axioms crossing_rank
end
end Lower6960.LineEuler
