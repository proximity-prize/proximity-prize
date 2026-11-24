import ProximityPrize.SubmissionLower.R6960RetainedCompressionBox

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000

namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators Polynomial Matrix

private def vectorPoly {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) : Curve A :=
  ∑ m : Slots a b, MvPolynomial.monomial (exponent m) (v m)

private theorem coeff_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (v : Slots a b→A) (j : Slots a b) : (vectorPoly v).coeff (exponent j)=v j := by
  classical
  rw [vectorPoly,MvPolynomial.coeff_sum,Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ neq
    rw [MvPolynomial.coeff_monomial, if_neg (exponent_injective.ne neq)]

private theorem vector_box {A : Type*} [CommSemiring A] {a b : ℕ} (v : Slots a b→A) :
    vectorPoly v∈Box A a b := by
  classical
  change ∀ m∈(vectorPoly v).support,m∈Exponents a b
  intro m mem
  by_contra fit
  apply MvPolynomial.mem_support_iff.mp mem
  rw [vectorPoly,MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_monomial]
  apply if_neg
  intro eq
  apply fit
  rw [← eq]
  exact ⟨by simpa only [exponent_y] using Nat.le_of_lt_succ j.1.isLt,
    by simpa only [exponent_z] using Nat.le_of_lt_succ j.2.isLt⟩

private theorem vector_recover {A : Type*} [CommSemiring A] {a b : ℕ} (Q : Curve A)
    (fit : Q∈Box A a b) : vectorPoly (fun j : Slots a b => Q.coeff (exponent j))=Q := by
  classical
  ext m
  by_cases has : ∃ j : Slots a b, exponent j=m
  · obtain ⟨j,rfl⟩ := has
    exact coeff_vector _ j
  have zero (W : Curve A) (hW : W∈Box A a b) : W.coeff m=0 := by
    by_contra hn
    exact has (exponent_exhaustive (hW (MvPolynomial.mem_support_iff.mpr hn)))
  rw [zero _ (vector_box _), zero _ fit]

def evaluate {F : Type*} [Field F] (z : F) (S : (Polynomial F)) : Curve (Polynomial F) →+* (Polynomial F) :=
  MvPolynomial.eval (fun j : Index => j.elim S (fun _ => C z))

def markMatrix {F α : Type*} [Field F] (z : α→F) (S : α→(Polynomial F)) (a b : ℕ) :
    Matrix α (Slots a b) (Polynomial F) :=
  Matrix.of fun i j => S i ^ j.1.val * C (z i ^ j.2.val)

private theorem mark_degree {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) (d a b : ℕ) (deg : ∀ i,(S i).natDegree≤d) :
    ∀ i j,(markMatrix z S a b i j).natDegree≤columnWeight d j := by
  intro i j
  have h := Polynomial.natDegree_mul_le
    (p:=S i ^ j.1.val) (q:=C (z i ^ j.2.val))
  rw [natDegree_C,add_zero] at h
  exact h.trans ((Polynomial.natDegree_pow_le_of_le _ (deg i)).trans_eq (Nat.mul_comm _ _))

private theorem eval_vector {A : Type*} [CommSemiring A] {a b : ℕ}
    (s z : A) (V : Slots a b→A) :
    MvPolynomial.eval (fun j : Index => j.elim s (fun _ => z)) (vectorPoly V) =
      ∑ j : Slots a b, (s^j.1.val*z^j.2.val)*V j := by
  classical
  rw [vectorPoly,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_option]
  simp only [Option.elim_none,Option.elim_some,exponent_y,Fintype.prod_unique,exponent_z]
  ac_rfl

private theorem eval_map_incl {F : Type*} [Field F] (z : F) (S : (Polynomial F)) (Q : Curve (Polynomial F)) :
    MvPolynomial.eval (fun j : Index => j.elim
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)) S)
        (fun _ => algebraMap (Polynomial F) (FractionRing (Polynomial F)) (C z)))
      (MvPolynomial.map (algebraMap (Polynomial F) (FractionRing (Polynomial F))) Q) =
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) (evaluate z S Q) := by
  let incl := algebraMap (Polynomial F) (FractionRing (Polynomial F))
  have ring : (MvPolynomial.eval (fun j : Index => j.elim (incl S) (fun _ => incl (C z)))).comp
      (MvPolynomial.map incl) = incl.comp (evaluate z S) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [evaluate]
    · intro i; cases i <;> simp [evaluate]
  exact DFunLike.congr_fun ring Q

/-- Multiplication by the nonzero marked factor supplies the full quotient
rectangle as independent rational kernel directions. -/
theorem rational_kernel {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (f : Curve (Polynomial F)) (fn : f≠0) (e v : ℕ)
    (box : f∈Box (Polynomial F) e v) (marks : ∀ i,evaluate (z i) (S i) f=0) :
    Fintype.card (QuotRect e v)≤Module.finrank (FractionRing (Polynomial F))
      (LinearMap.ker ((markMatrix z S (boxOrdinate e) (paddedSeed v)).map
        (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).mulVecLin) := by
  classical
  let E := FractionRing (Polynomial F)
  let j := algebraMap (Polynomial F) E
  let g := MvPolynomial.map j f
  let W := markMatrix z S (boxOrdinate e) (paddedSeed v)
  have gn : g≠0 := (map_ne_zero_iff _ (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial F) E))).mpr fn
  have gbox : g∈Box E e v := by
    change ∀ m∈g.support,m∈Exponents e v
    have supp : g.support=f.support :=
      MvPolynomial.support_map_of_injective f (IsFractionRing.injective (Polynomial F) E)
    rw [supp]
    exact box
  let mulVec : (QuotRect e v→E) →ₗ[E] (Rect e v→E) := {
    toFun := fun u m => (g*vectorPoly u).coeff (exponent m)
    map_add' := fun u w => by
      funext m
      have add : vectorPoly (u+w)=vectorPoly u+vectorPoly w := by
        simp only [vectorPoly, Pi.add_apply, map_add, Finset.sum_add_distrib]
      change (g*vectorPoly (u+w)).coeff (exponent m)=_
      rw [add,mul_add,MvPolynomial.coeff_add]
      rfl
    map_smul' := fun a u => by
      funext m
      have smul : vectorPoly (a • u)=a • vectorPoly u := by
        simp only [vectorPoly,Pi.smul_apply,Finset.smul_sum,MvPolynomial.smul_monomial]
      change (g*vectorPoly (a • u)).coeff (exponent m)=_
      rw [smul,mul_smul_comm,MvPolynomial.coeff_smul]
      rfl }
  have recovered (u : QuotRect e v→E) : vectorPoly (mulVec u)=g*vectorPoly u := by
    apply vector_recover
    have h := (box_iff _ _ _).mp gbox
    have hs := (box_iff _ _ _).mp (vector_box u)
    apply (box_iff _ _ _).mpr
    refine ⟨(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_,(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_⟩
    · exact (Nat.add_le_add h.1 hs.1).trans (by unfold boxOrdinate; omega)
    · exact (Nat.add_le_add h.2 hs.2).trans (by unfold paddedSeed quotientSeed; omega)
  have kernel (u : QuotRect e v→E) : mulVec u∈LinearMap.ker (W.map j).mulVecLin := by
    rw [LinearMap.mem_ker]
    funext i
    have h := eval_vector (j (S i)) (j (C (z i))) (mulVec u)
    have eq : (W.map j).mulVecLin (mulVec u) i =
        MvPolynomial.eval (fun v : Index => v.elim (j (S i)) (fun _ => j (C (z i))))
          (vectorPoly (mulVec u)) := by
      rw [h]
      change (∑ m : Rect e v, j (W i m) * mulVec u m)=_
      simp only [W,markMatrix,Matrix.of_apply,map_mul,map_pow,C_pow]
    rw [eq,recovered,map_mul]
    change MvPolynomial.eval _ (MvPolynomial.map j f) * _ = 0
    rw [eval_map_incl,marks i,map_zero,zero_mul]
  have inject : Function.Injective (mulVec.codRestrict _ kernel) := by
    intro u w eq
    have eu : mulVec u=mulVec w := congrArg Subtype.val eq
    have ew := congrArg vectorPoly eu
    rw [recovered,recovered] at ew
    have V := mul_left_cancel₀ gn ew
    funext j
    exact (coeff_vector _ j).symm.trans ((congrArg (fun P : Curve E => P.coeff (exponent j)) V).trans (coeff_vector _ j))
  have dim := LinearMap.finrank_le_finrank_of_injective inject
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,card_univ,
    nsmul_eq_mul,mul_one,Nat.cast_id,W,j,E] using dim

private theorem eval_packed {F α : Type*} [Field F]
    (z : α→F) (S : α→(Polynomial F)) {a b d W : ℕ}
    (u : HeightCompression.Coeffs F (fun j : Slots a b => columnWeight d j) W) (i : α) :
    evaluate (z i) (S i) (packLinear F a b d W u) =
      HeightCompression.evaluation (markMatrix z S a b) (columnWeight d) W u i := by
  change evaluate (z i) (S i) (vectorPoly (fun j => (u j : (Polynomial F))))=_
  unfold evaluate
  rw [eval_vector]
  simp [HeightCompression.evaluation,markMatrix,C_pow]

/-- At excessive weight, the full kernel cannot consist entirely of multiples
of the marked factor. The resulting relation is an actual escaping cutter. -/
theorem escape {F α : Type*} [Field F] [Finite α]
    (z : α→F) (S : α→(Polynomial F)) (d : ℕ) (hd : 0<d) (degree : ∀ i,(S i).natDegree≤d)
    (f : Curve (Polynomial F)) (fn : f≠0) {e v : ℕ} (he : 2≤e)
    (ed : f.degreeOf ordinate=e) (vd : f.degreeOf parameter=v)
    (marks : ∀ i,evaluate (z i) (S i) f=0) (hlarge : heightCap e d<height d f) :
    ∃ G : Curve (Polynomial F), G≠0 ∧ ¬ f∣G ∧ G∈Box (Polynomial F) (boxOrdinate e) (paddedSeed v) ∧
      height d G<width e d ∧ ∀ i,evaluate (z i) (S i) G=0 := by
  classical
  let A := markMatrix z S (boxOrdinate e) (paddedSeed v)
  let ker := LinearMap.ker (HeightCompression.evaluation A (columnWeight d) (width e d))
  let pack := packLinear F (boxOrdinate e) (paddedSeed v) d (width e d)
  let mult := (LinearMap.mulLeft F f).comp (packLinear F e (quotientSeed v) d (quotientWidth e d))
  have ker_size : Module.finrank F (HeightCompression.Coeffs F
      (fun j : QuotRect e v => columnWeight d j) (quotientWidth e d)) < Module.finrank F ker :=
    relation_space_gt he hd A (mark_degree z S d _ _ degree)
      (rational_kernel z S f fn e v ((box_iff _ _ _).mpr ⟨ed.le,vd.le⟩) marks)
  by_contra! h
  have all (u : ker) : f ∣ pack u.val := by
    by_cases zero : pack u.val=0
    · rw [zero]; exact dvd_zero f
    by_contra! bad
    obtain ⟨i,wrong⟩ := h (pack u.val) zero bad (pack_box u.val)
      (pack_height (by unfold width; omega) u.val)
    apply wrong
    change evaluate (z i) (S i) (packLinear F (boxOrdinate e) (paddedSeed v) d (width e d) u.val)=0
    rw [eval_packed]
    exact congrFun (LinearMap.mem_ker.mp u.property) i
  have fits (u : ker) : pack u.val∈LinearMap.range mult := by
    by_cases zero : pack u.val=0
    · exact zero ▸ Submodule.zero_mem _
    obtain ⟨Q,eq⟩ := all u
    have qn : Q≠0 := fun no => zero (by rw [eq,no,mul_zero])
    have dQ : Q∈Box (Polynomial F) e (quotientSeed v) := by
      have fit := (box_iff _ _ _).mp (pack_box u.val)
      change (pack u.val).degreeOf ordinate≤_ ∧ (pack u.val).degreeOf parameter≤_ at fit
      rw [eq,MvPolynomial.degreeOf_mul_eq fn qn,MvPolynomial.degreeOf_mul_eq fn qn,ed,vd] at fit
      apply (box_iff _ _ _).mpr
      unfold boxOrdinate paddedSeed quotientSeed at *
      omega
    have wQ : height d Q<quotientWidth e d := by
      have top := pack_height (by unfold width; omega) u.val
      change height d (pack u.val)<width e d at top
      rw [eq,height_mul d fn qn] at top
      unfold heightCap width quotientWidth at *
      have eq : (3*e-1)*d=(2*e-1)*d+e*d := by
        rw [show 3*e-1=(2*e-1)+e by omega, Nat.add_mul]
      omega
    obtain ⟨w,hw⟩ := represented Q dQ wQ
    refine ⟨w,?_⟩
    change f*(packLinear F e (quotientSeed v) d (quotientWidth e d) w)=_
    rw [hw,eq]
  let emb := (pack.comp ker.subtype).codRestrict _ fits
  have hn : Function.Injective emb := by
    intro u v eq
    apply Subtype.ext
    exact pack_injective _ _ _ _ (congrArg Subtype.val eq)
  have short := LinearMap.finrank_le_finrank_of_injective hn
  exact (not_lt_of_ge (short.trans mult.finrank_range_le)) ker_size

#print axioms rational_kernel
#print axioms escape
end
end Lower6960.RetainedCompression
