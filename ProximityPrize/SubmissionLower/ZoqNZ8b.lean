import ProximityPrize.SubmissionLower.ZycQTHe
import ProximityPrize.SubmissionLower.ZJEYUQc
import ProximityPrize.SubmissionLower.ZQDgS7b
set_option Elab.async false
open _root_ renaming Fin.ext → zmq, Finset.sum_subset → zVG, MvPolynomial.X → z9v, MvPolynomial.monomial → ztt, Nat.le_of_lt_succ → zeh
section
set_option autoImplicit true
namespace qnRjM0a
noncomputable section
open Finset Polynomial
open scoped Polynomial BigOperators Pointwise
open cu (L)
open jA (kS)
open NR (O8 Lq)

open P5_7_2 (TopRow)
open qje58fc (ModelIndex modelExponent modelImage modelMatrix)
set_option backward.isDefEq.respectTransparency false
abbrev Model:=MvPolynomial (Fin 5) L
private abbrev ringSemiring :Semiring Lq:=(inferInstance :Ring Lq).toSemiring
def poleIdeal (α:L) (n:ℕ) : @Ideal Lq ringSemiring :=
 @Ideal.span Lq ringSemiring { (MvPolynomial.C (O8 α) :Lq)^n }
abbrev PoleQuot (α:L) (n:ℕ) :=Lq ⧸ poleIdeal α n
def poleMk (α:L) (n:ℕ) :Lq →ₐ[L] PoleQuot α n :=
 Ideal.Quotient.mkₐ L (poleIdeal α n)
def seedConst:kS →+* Lq:=MvPolynomial.C.comp C
def rawVar (α:L) (z :kS) :Fin 5→Lq :=
  ![MvPolynomial.C (O8 α),seedConst z,
    z9v 0,z9v 1,z9v 2]
def readModel (α:L) (z :kS) (n:ℕ) :Model →ₐ[L] PoleQuot α n :=
 (poleMk α n).comp (MvPolynomial.aeval (rawVar α z))
private def bounded (w:Fin 5→ℕ) (n:ℕ) (F:Model) :Prop :=
 ∀ m∈F.support,m.weight w≤n
private theorem bX (w:Fin 5→ℕ) (i:Fin 5) :bounded w (w i) (z9v i) := by
 intro m hm
 rw [MvPolynomial.support_X,mem_singleton] at hm
 simp [hm,Finsupp.weight_single]
private theorem badd {w u v F G} (hF:bounded w u F) (hG:bounded w v G) :
   bounded w (max u v) (F+G) := by
 classical
 intro m hm
 rcases mem_union.mp (MvPolynomial.support_add hm) with h | h
 · exact (hF _ h).trans (le_max_left _ _)
 · exact (hG _ h).trans (le_max_right _ _)
private theorem bmul {w u v F G} (hF:bounded w u F) (hG:bounded w v G) :
  bounded w (u+v) (F*G) := by
 classical
 intro m hm
 obtain ⟨i,hi,j,hj,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul F G hm)
 rw [map_add]
 exact Nat.add_le_add (hF i hi) (hG j hj)
private theorem bpow {w u F} (h:bounded w u F) (k :ℕ) :
   bounded w (u*k) (F^k) := by
 induction k with
 | zero =>
   intro m hm
   have he :m=0:= by simpa using hm
   simp [he]
 | succ k ih =>
   rw [pow_succ,Nat.mul_succ]
   exact bmul ih h
private theorem image_bound {t U} (i:ModelIndex t U) (w:Fin 5→ℕ) :
  bounded w (w 0*i.2.2.1.val+w 1*i.2.2.2.val +
    max (w 1) (w 0+w 2)*(i.1.val-i.2.1.1.val-i.2.1.2.val) +
    max (w 2) (w 0+w 3)*i.2.1.2.val +
    max (w 3) (w 0+w 4)*i.2.1.1.val) (modelImage i) :=
 bmul (bmul (bmul (bmul (bpow (bX w 0) _) (bpow (bX w 1) _))
  (bpow (badd (bX w 1) (bmul (bX w 0) (bX w 2))) _))
  (bpow (badd (bX w 2) (bmul (bX w 0) (bX w 3))) _))
  (bpow (badd (bX w 3) (bmul (bX w 0) (bX w 4))) _)
private theorem output_bounds {t U} (i:ModelIndex t U) {m} (hm:m∈(modelImage i).support) :
   m 2+m 3+m 4≤t.shape.B∧m 3+2*m 4≤t.shape.J ∧
     m 4≤t.YM∧m 1≤U+t.shape.B:= by
 have hq:=i.1.isLt
 have hz :=i.2.2.2.isLt
 have hc:=zeh i.2.1.1.isLt
 have hb:=zeh i.2.1.2.isLt
 change i.2.1.1.val≤ min i.1.val (min t.YM (t.shape.J/2)) at hc
 change i.2.1.2.val≤ min (i.1.val-i.2.1.1.val) (t.shape.J-2*i.2.1.1.val) at hb
 rw [le_min_iff,le_min_iff] at hc
 rw [le_min_iff] at hb
 have h₀:=image_bound i ![0,0,1,1,1] m hm
 have h₁:=image_bound i ![0,0,0,1,2] m hm
 have h₂:=image_bound i ![0,0,0,0,1] m hm
 have h₃:=image_bound i ![0,1,0,0,0] m hm
 simp [Finsupp.weight_eq_sum,Fin.sum_univ_five,smul_eq_mul] at h₀ h₁ h₂ h₃
 omega
private theorem exponent_injective (t:TopRow) (U:ℕ) :
  Function.Injective (@modelExponent t U) := by
 intro i j h
 have hh (k :Fin 5) :=congrArg (fun m:Fin 5 →₀ ℕ=>m k) h
 have h₀:=hh 0
 have h₁:=hh 1
 have h₂:=hh 2
 have h₃:=hh 3
 have h₄:=hh 4
 simp [modelExponent] at h₀ h₁ h₂ h₃ h₄
 have hci:=(zeh i.2.1.1.isLt).trans (min_le_left _ _)
 have hcj:=(zeh j.2.1.1.isLt).trans (min_le_left _ _)
 have hbi:=(zeh i.2.1.2.isLt).trans (min_le_left _ _)
 have hbj:=(zeh j.2.1.2.isLt).trans (min_le_left _ _)
 have hq:i.1.val=j.1.val := by omega
 obtain ⟨iq,⟨ic,ib⟩,ix,iz⟩:=i
 obtain ⟨jq,⟨jc,jb⟩,jx,jz⟩:=j
 obtain rfl :iq=jq:=zmq hq
 obtain rfl :ic=jc:=zmq h₄
 obtain rfl :ib=jb:=zmq h₃
 obtain rfl :ix=jx :=zmq h₀
 obtain rfl :iz=jz :=zmq h₁
 rfl
private theorem exponent_exists {t U} (m:Fin 5 →₀ ℕ)
  (hq:m 2+m 3+m 4≤t.shape.B) (hj:m 3+2*m 4≤t.shape.J)
  (hc:m 4≤t.YM) (hx :m 0<t.shape.B+t.shape.J) (hz :m 1≤U) :
  ∃ i:ModelIndex t U,modelExponent i=m:= by
 let q:Fin (t.shape.B+1) :=⟨m 2+m 3+m 4,by omega⟩
 let c:Fin (min q.val (min t.YM (t.shape.J/2))+1) :=
  ⟨m 4,by simp only [q,Nat.lt_succ_iff,le_min_iff]; omega⟩
 let b:Fin (min (q.val-c.val) (t.shape.J-2*c.val)+1) :=
  ⟨m 3,by simp only [q,c,Nat.lt_succ_iff,le_min_iff]; omega⟩
 refine ⟨⟨q,⟨c,b⟩,⟨m 0,hx⟩,⟨m 1,by omega⟩⟩,?_⟩
 ext i
 fin_cases i <;> simp [modelExponent,q,c,b]
theorem read_power_high {α z n j} (hj:n≤j) :
   readModel α z n (z9v 0^j)=0:= by
 have hp:poleMk α n ((rawVar α z 0)^n)=0:= by
   rw [poleMk,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem,
     poleIdeal,Ideal.mem_span_singleton]
   exact dvd_rfl
 rw [map_pow] at hp
 simp only [readModel,AlgHom.comp_apply,map_pow,MvPolynomial.aeval_X]
 rw [← Nat.add_sub_of_le hj,pow_add,hp,zero_mul]
private theorem read_mono_high {α z n} {m:Fin 5 →₀ ℕ} (hm:n≤ m 0) (v :L) :
  readModel α z n (ztt m v)=0:= by
 rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),
  Fin.prod_univ_five]
 simp only [map_mul,read_power_high hm,zero_mul,mul_zero]
private def decode {t:TopRow} (α:L) (z :kS) :
   (ModelIndex t (t.shape.U+t.shape.B)→L) →ₗ[L] PoleQuot α (t.shape.B+t.shape.J) :=
 ∑ i,(LinearMap.proj i).smulRight
   (readModel α z _ (ztt (modelExponent i) 1))
private theorem decode_column {t:TopRow} (α:L) (z :kS)
    (j:ModelIndex t t.shape.U) :
    decode (t:=t) α z ((modelMatrix t).mulVecLin (Pi.single j 1)) =
      readModel α z _ (modelImage j) := by
  classical
  let P:=modelImage j
  let s :=(univ :Finset (ModelIndex t (t.shape.U+t.shape.B))).image modelExponent
  let f : (Fin 5 →₀ ℕ)→PoleQuot α (t.shape.B+t.shape.J) :=
    fun m=>readModel α z _ (ztt m (P.coeff m))
  simp only [decode,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply,
    Matrix.mulVecLin_apply,Matrix.mulVec_single_one,Matrix.col_apply,modelMatrix]
  have hs (m:Fin 5 →₀ ℕ) :
      P.coeff m•readModel α z _ (ztt m 1)=f m:= by
    rw [← map_smul]
    simp [f,MvPolynomial.smul_monomial]
  change (∑ i:ModelIndex t (t.shape.U+t.shape.B),
    P.coeff (modelExponent i)•readModel α z _ (ztt (modelExponent i) 1)) =
    readModel α z _ P
  simp_rw [hs]
  rw [← Finset.sum_image (f :=f) (fun _ _ _ _ h=>exponent_injective _ _ h)]
  change ∑ m∈s,f m=readModel α z _ P
  conv_rhs=>rw [P.as_sum,map_sum]
  change ∑ m∈s,f m = ∑ m∈P.support,f m
  calc
    _ = ∑ m∈s∪P.support,f m:= by
      apply zVG subset_union_left
      intro m _ hm
      by_cases h:m∈P.support
      · have hb:=output_bounds j h
        have hx :t.shape.B+t.shape.J≤ m 0:= by
          by_contra! hh
          obtain ⟨i,hi⟩:=exponent_exists m hb.1 hb.2.1 hb.2.2.1 hh hb.2.2.2
          exact hm (Finset.mem_image.mpr ⟨i,mem_univ _,hi⟩)
        exact read_mono_high hx _
      · simp [f,MvPolynomial.notMem_support_iff.mp h]
    _ = _:= by
      symm
      apply zVG subset_union_right
      intro m _ hm
      simp [f,MvPolynomial.notMem_support_iff.mp hm]
def modelRange (t:TopRow) (α:L) (z :kS) :
    Submodule L (PoleQuot α (t.shape.B+t.shape.J)) :=
  (LinearMap.range (modelMatrix t).mulVecLin).map (decode (t:=t) α z)
theorem read_column_mem {t:TopRow} (α:L) (z :kS)
  (j:ModelIndex t t.shape.U) :readModel α z _ (modelImage j)∈modelRange t α z := by
 classical
 exact ⟨_,⟨Pi.single j 1,rfl⟩,decode_column α z j⟩
theorem modelRange_le (t:TopRow) (α:L) (z :kS) :
  Module.finrank L (modelRange t α z)≤(modelMatrix t).rank :=
 Submodule.finrank_map_le _ _
end
end qnRjM0a
end
