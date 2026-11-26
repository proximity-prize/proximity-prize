import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.R6960LineEulerFree

section Merged6967_R6960CollisionTameLineDegree
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Matrix LaurentPolynomial LineEuler Module
open scoped Polynomial Matrix BigOperators
variable {k E ι : Type*} [Field k] [Field E] [Algebra (Laurent k) E]
  [Fintype ι] [DecidableEq ι]
theorem trace_matrix_on_torus (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    (Algebra.traceMatrix (Polynomial k) b).map (chartEmbedding s (k:=k))=
      Algebra.traceMatrix (Laurent k) (localBasis s b) := by
  have tr (x : chartOrder (k:=k) (E:=E) s) : chartEmbedding s (Algebra.trace (Polynomial k) _ x)=
      Algebra.trace (Laurent k) _ (chartOrderMap s x) := by
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace (localBasis s b)]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change chartEmbedding s ((Algebra.leftMulMatrix b x) i i)=
      ((Algebra.leftMulMatrix (localBasis s b) (chartOrderMap s x)) i i)
    rw [Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
      localBasis_apply,←map_mul,localBasis_repr]
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,Algebra.traceMatrix_apply,Algebra.traceForm_apply,localBasis_apply,←map_mul]
  exact tr (b i*b j)
private theorem transition_expansion
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) (i : ι) :
    (∑ j,normalizedTransition bf bi j i • localBasis false bf j)=localBasis true bi i := by
  let fin := localBasis false bf
  let inf := localBasis true bi
  have coord : normalizedTransition bf bi *ᵥ Pi.single i (1:Laurent k) = fin.equivFun (inf i) := by
    rw [normalizedTransition_mulVec]
    have s : inf.equivFun (inf i)=Pi.single i 1 := by
      funext j
      rw [Basis.equivFun_apply,Basis.repr_self]
      simp only [Finsupp.single_eq_pi_single]
    rw [←s,LinearEquiv.symm_apply_apply]
  have repr : ∀ j,normalizedTransition bf bi j i=fin.equivFun (inf i) j := by
    rw [Matrix.mulVec_single_one] at coord
    exact fun j=>congrFun coord j
  rw [show (∑ j,normalizedTransition bf bi j i • fin j)=(∑ j,fin.equivFun (inf i) j • fin j)
    from Finset.sum_congr rfl (fun j _=>congrArg (· • fin j) (repr j))]
  exact (fin.equivFun_symm_apply (fin.equivFun (inf i))).symm.trans (fin.equivFun.symm_apply_apply (inf i))
theorem normalized_trace_transition
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    invert ((Algebra.traceMatrix (Polynomial k) bi).det.toLaurent)=
      (normalizedTransition bf bi).det^2*(Algebra.traceMatrix (Polynomial k) bf).det.toLaurent := by
  let G := normalizedTransition bf bi
  let «X» := Algebra.traceMatrix (Polynomial k) bf
  let «Z» := Algebra.traceMatrix (Polynomial k) bi
  let M := (Algebra.traceMatrix (Laurent k) (localBasis false bf))
  let N := (Algebra.traceMatrix (Laurent k) (localBasis true bi))
  have change : N=G.transpose*M*G := by
    let tr := Algebra.traceForm (Laurent k) (torusOrder (k:=k) (E:=E))
    change tupleGram tr (localBasis true bi)=G.transpose*tupleGram tr (localBasis false bf)*G
    rw [←tupleGram_change]
    exact congrArg (tupleGram tr) (funext fun i=>(transition_expansion bf bi i).symm)
  have finDet : M.det=«X».det.toLaurent := by
    have h := congrArg Matrix.det (trace_matrix_on_torus false bf)
    have det : («X».map (chartEmbedding false (k:=k))).det=chartEmbedding false «X».det :=
      ((chartEmbedding false (k:=k)).toRingHom.map_det «X»).symm
    exact h.symm.trans det
  have infDet : N.det=infinityEmbedding «Z».det := by
    have h := congrArg Matrix.det (trace_matrix_on_torus true bi)
    have det : («Z».map (chartEmbedding true (k:=k))).det=chartEmbedding true «Z».det :=
      ((chartEmbedding true (k:=k)).toRingHom.map_det «Z»).symm
    exact h.symm.trans det
  change infinityEmbedding «Z».det=G.det^2*«X».det.toLaurent
  rw [←infDet,change,det_mul,det_mul,det_transpose,finDet]
  ring
theorem normalized_line_discriminant_degree
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true))
    (nonzero : (Algebra.traceMatrix (Polynomial k) bf).det≠0) :
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      ((Algebra.traceMatrix (Polynomial k) bf).det.natDegree:ℤ)≤-2*d := by
  let G := normalizedTransition bf bi
  let «X» := Algebra.traceMatrix (Polynomial k) bf
  let «Z» := Algebra.traceMatrix (Polynomial k) bi
  obtain ⟨c,d,cn,dc⟩ := unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp (normalizedTransition_unit bf bi))
  have h := normalized_trace_transition bf bi
  change infinityEmbedding «Z».det=G.det^2*«X».det.toLaurent at h
  rw [dc] at h
  have product : infinityEmbedding «Z».det=LaurentPolynomial.C (c^2)*(T (d+d)*«X».det.toLaurent) := by
    rw [T_add,map_pow,h,pow_two]
    ring
  refine ⟨d,by rw [dc,degree_C_mul_T _ _ cn],?_⟩
  let n : ℤ := «X».det.natDegree
  have alive : («X».det.toLaurent).coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nonzero,rfl⟩)
  have supported : infinityEmbedding «Z».det∈AddMonoidAlgebra.supported k k (Set.Iic ((0:ℕ):ℤ)) := by
    rw [←range_shiftPolynomial 0]
    exact ⟨«Z».det,by rw [shiftPolynomial_apply,Nat.cast_zero,T_zero,one_mul]⟩
  by_contra bad
  have neg : ¬ n+(d+d)∈Set.Iic ((0:ℕ):ℤ) := by
    change ¬n+(d+d)≤0
    change ¬n≤-2*d at bad
    omega
  have z := AddMonoidAlgebra.mem_supported'.mp supported _ neg
  rw [product,←single_eq_C,AddMonoidAlgebra.coeff_single_zero_mul,coeff_shift,add_sub_cancel_right] at z
  exact mul_ne_zero (pow_ne_zero 2 cn) alive z
#print axioms trace_matrix_on_torus
#print axioms normalized_trace_transition
#print axioms normalized_line_discriminant_degree
end
end Lower6960.CollisionTame

end Merged6967_R6960CollisionTameLineDegree

section Merged6967_R6966ProofNativeAffineLedger
set_option Elab.async false


set_option Elab.async false

namespace Research6966.NativeAffineLedger
open WordSurfacePrice (side)
set_option maxHeartbeats 300000

/-- Turn a scaled word count into its integer fee and rounded-down regular price. -/
theorem floor {marks fee scale bill : ℕ} (pos : 0 < scale)
    (count : marks*scale ≤ fee*scale+bill) : marks ≤ fee+bill/scale := by
  have h : (marks-fee)*scale ≤ bill := by rw [Nat.sub_mul]; omega
  have q := (Nat.le_div_iff_mul_le pos).mpr h
  omega

theorem side_mono {n a d h H : ℕ} (hh : h ≤ H) : side n a d h ≤ side n a d H :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _

theorem side_one {n a d : ℕ} (gap : d < a) (an : a ≤ n) : side n a d 1 = n-d := by
  unfold side
  rw [Nat.mul_one]
  omega

theorem side_ratio {n a d h : ℕ} (gap : d < a) (an : a ≤ n) :
    side n a d h ≤ max 1 h*(n-d) := by
  have hm : 1 ≤ max 1 h := le_max_left _ _
  have h1 : a-d ≤ (a-d)*max 1 h := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a-d) hm
  calc
    side n a d h ≤ side n a d (max 1 h) := side_mono (le_max_right _ _)
    _ ≤ (n-a)*max 1 h+(a-d)*max 1 h := Nat.add_le_add_left h1 _
    _ = max 1 h*(n-d) := by rw [← Nat.add_mul, show n-a+(a-d)=n-d by omega, Nat.mul_comm]

/-- The three-coordinate affine ledger accepts both the degree-six box
price and the degree-three common-total-degree price. -/
theorem three_floor {n a d marks fee c h₀ h₁ : ℕ} (gap : d < a) (an : a ≤ n)
    (count : marks*(a-d)^3 ≤ fee*(a-d)^3+c*side n a d 1*side n a d h₀*side n a d h₁) :
    marks ≤ fee+(c*max 1 h₀*max 1 h₁*(n-d)^3)/(a-d)^3 := by
  apply floor (pow_pos (by omega) 3)
  refine count.trans (Nat.add_le_add_left ?_ _)
  rw [side_one gap an]
  calc
    c*(n-d)*side n a d h₀*side n a d h₁ ≤
        c*(n-d)*(max 1 h₀*(n-d))*(max 1 h₁*(n-d)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (side_ratio gap an)) (side_ratio gap an)
    _ = _ := by ring

theorem two_floor {n a d marks fee h : ℕ} (gap : d < a) (an : a ≤ n)
    (count : marks*(a-d)^2 ≤ fee*(a-d)^2+2*side n a d 1*side n a d h) :
    marks ≤ fee+(2*max 1 h*(n-d)^2)/(a-d)^2 := by
  apply floor (pow_pos (by omega) 2)
  refine count.trans (Nat.add_le_add_left ?_ _)
  rw [side_one gap an]
  calc
    2*(n-d)*side n a d h ≤ 2*(n-d)*(max 1 h*(n-d)) := Nat.mul_le_mul_left _ (side_ratio gap an)
    _ = _ := by ring

theorem fixed_floor {n a d marks : ℕ} (gap : d < a) (an : a ≤ n)
    (count : marks*(a-d) ≤ side n a d 1) : marks ≤ (n-d)/(a-d) := by
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (count.trans_eq (side_one gap an))

/-- The projected ledger keeps the individual side lengths. This variant
permits the width-zero padding used by the numerical ledger. -/
theorem projected_floor {n a d marks fee g v₀ v₁ h₀ h₁ : ℕ} (gap : d < a)
    (count : marks*(a-d)^2 ≤ fee*(a-d)^2+2*
      (g*side n a d h₀*side n a d h₁+v₀*side n a d 1*side n a d h₁+v₁*side n a d 1*side n a d h₀)) :
    marks ≤ fee+2*
      (g*side n a d (max 1 h₀)*side n a d (max 1 h₁)+
        v₀*side n a d 1*side n a d (max 1 h₁)+v₁*side n a d 1*side n a d (max 1 h₀))/(a-d)^2 := by
  apply floor (pow_pos (by omega) 2)
  have z : side n a d h₀ ≤ side n a d (max 1 h₀) := side_mono (le_max_right _ _)
  have o : side n a d h₁ ≤ side n a d (max 1 h₁) := side_mono (le_max_right _ _)
  exact count.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ z) o) (Nat.mul_le_mul_left _ o))
    (Nat.mul_le_mul_left _ z))) _)

#print axioms three_floor
#print axioms two_floor
#print axioms fixed_floor
#print axioms projected_floor
end Research6966.NativeAffineLedger

end Merged6967_R6966ProofNativeAffineLedger

section Merged6967_R6966ProofOdeSurfaceBridge
set_option Elab.async false




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

end Merged6967_R6966ProofOdeSurfaceBridge
