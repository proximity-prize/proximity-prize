import ProximityPrize.SubmissionLower.Z4EMMWa
import ProximityPrize.SubmissionLower.ZK8GpQb
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qrGSFbd
noncomputable section
open Polynomial Finset WithZero
open scoped Classical WithZero nonZeroDivisors
open qZu9hjc (valueZeros valueCoeffs)
open qFD8jve (aFA)
open E7 (poleOrder KB Tq)
open private b4s bHf adG cTA aMX b4t cNC from ProximityPrize.SubmissionLower.Y
variable {E :Type} [Field E]
abbrev pencilVal (w:Valuation E ℤᵐ⁰) :=b4s w
theorem pencilVal_poly (w:Valuation E ℤᵐ⁰) (f :E[X]) :
  pencilVal w (algebraMap E[X] (RatFunc E) f)=adG w f :=
 bHf w f
theorem pencilVal_const (w:Valuation E ℤᵐ⁰) (c:E) :
 pencilVal w (RatFunc.C c)=w c:=(pencilVal_poly w _).trans (cTA w c)
private theorem valueZeros_eq (w:Valuation E ℤᵐ⁰) {N :E[X]} (hm:N.Monic) :
    valueZeros w N=(log (adG w N)-log (w (N.coeff 0))).toNat := by
  let m:=adG w N
  have hm₀:m≠0:=b4t w hm.ne_zero
  have hm₁:1≤ m:= by
    simpa only [coeff_natDegree,hm.leadingCoeff,map_one] using aMX w N N.natDegree
  have hlog:0≤log m:=(le_log_iff_exp_le (a :=(0:ℤ)) hm₀).mpr (by simpa only [exp_zero] using hm₁)
  have cle (i:ℕ) :log (w (N.coeff i))≤log m:= by
    by_cases hi:N.coeff i=0
    · simpa only [hi,map_zero,log_zero] using hlog
    · exact (log_le_log (w.ne_zero_iff.mpr hi) hm₀).mpr (aMX w N i)
  obtain ⟨i,hi,_⟩:=cNC w N hm.ne_zero
  have hmem:i∈N.support :=mem_support_iff.mpr (fun hz=>hm₀ (hi.symm.trans (hz ▸ map_zero w)))
  have hs :Tq w (valueCoeffs N)=(log m).toNat := by
    apply le_antisymm
    · exact Finset.sup_le fun j _=>Int.toNat_le_toNat (cle j)
    · have :=Finset.le_sup (f := fun j=>poleOrder w (valueCoeffs N j))
        (mem_univ (⟨i,Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hmem)⟩:Fin (N.natDegree+1)))
      simpa only [Tq,poleOrder,valueCoeffs,hi,m] using this
  unfold valueZeros poleOrder KB
  rw [hs]
  change (log m).toNat - (log (w (N.coeff 0))).toNat+(-log (w (N.coeff 0))).toNat =
    (log m-log (w (N.coeff 0))).toNat
  have :=cle 0
  omega
theorem primitive (w:Valuation E ℤᵐ⁰) (hw:Function.Surjective w)
   (N : (RatFunc E)[X]) (hm:N.Monic) (hn:N.coeff 0≠0) :
   ∃ P:E[X][X],P.coeff 0≠0∧aFA w P 0 ∧
     N∣P.map (algebraMap E[X] (RatFunc E)) ∧
     (-log (P5_7_1_7_4_3_4.adG w (P.coeff 0))).toNat=valueZeros (pencilVal w) N := by
 let j:E[X] →+* RatFunc E :=algebraMap _ _
 let v :=pencilVal w
 let m:=adG v N
 have hm₀:m≠0:=b4t v hm.ne_zero
 let P₀:=IsLocalization.integerNormalization E[X]⁰ N
 obtain ⟨D,hD,hP₀⟩:=IsLocalization.integerNormalization_spec E[X]⁰ N
 change P₀.map j=D•N at hP₀
 have hDv :v (j D)≠0:=v.ne_zero_iff.mpr ((map_ne_zero_iff j (IsFractionRing.injective E[X] (RatFunc E))).mpr (nonZeroDivisors.ne_zero hD))
 obtain ⟨c,hc⟩:=hw ((v (j D)*m)⁻¹)
 let P:=C (C c)*P₀
 have hP:P.map j=C (RatFunc.C c*j D)*N := by
   rw [Polynomial.map_mul,map_C,hP₀,Algebra.smul_def]
   change C (RatFunc.C c)*(C (j D)*N)= _
   rw [← mul_assoc,← C_mul]
 have hl:v (RatFunc.C c*j D)=m⁻¹:= by
   rw [map_mul,pencilVal_const,hc,mul_inv_rev,mul_assoc,inv_mul_cancel₀ hDv,mul_one]
 have hcoeff (i:ℕ) :v (j (P.coeff i))=v (N.coeff i)/m:= by
   have he :=congrArg (fun f : (RatFunc E)[X]=>f.coeff i) hP
   simp only [coeff_map,coeff_C_mul] at he
   rw [he,map_mul,hl,div_eq_mul_inv,mul_comm]
 have hk :v (N.coeff 0)≠0:=v.ne_zero_iff.mpr hn
 have hp0:P.coeff 0≠0:= by
   intro hz
   have h:=hcoeff 0
   rw [hz,map_zero,map_zero] at h
   exact (div_ne_zero hk hm₀) h.symm
 refine ⟨P,hp0,fun i k => ?_,⟨C (RatFunc.C c*j D),hP.trans (mul_comm _ _)⟩,?_⟩
 · rw [Nat.cast_zero,exp_zero]
   refine (aMX w (P.coeff i) k).trans ?_
   rw [← pencilVal_poly,hcoeff]
   exact (div_le_one₀ (zero_lt_iff.mpr hm₀)).mpr (aMX v N i)
 · change (-log (adG w (P.coeff 0))).toNat= _
   rw [← pencilVal_poly,hcoeff,log_div hk hm₀,neg_sub,valueZeros_eq v hm]
end
end qrGSFbd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrGSFbd
noncomputable section
open Finset WithZero
open cu (L)
open E7 (KB)
open qNu3xvc (Equation GraphVal seed constant)
open P5_7_1_7_4_3_4 (Pencil gauge relativePolar)
open scoped Classical WithZero
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
private theorem gauge_id (x y :L) :
  constant A (y-x)=constant A y*gauge A x - constant A x*gauge A y := by
 simp only [P5_7_1_7_4_3_4.gauge,constant,map_sub]
 ring
theorem nonzero_tilt (C:Pencil A) {ι:Type} [Fintype ι] (r :ι→Bool)
   (v : ∀ i,GraphVal A (r i)) :
   ∃ C' : Pencil A,C'.tilt≠0∧C'.base=C.base ∧
     ∀ i,KB (v i).val (relativePolar C)≤KB (v i).val (relativePolar C') := by
 by_cases ht:C.tilt≠0
 · exact ⟨C,ht,rfl,fun _=>le_rfl⟩
 let bad (i:ι) :Set L := {x | (v i).val (gauge A x)<1}
 have hb (i:ι) : (bad i).Finite :=Set.Subsingleton.finite (by
   intro x hx y hy
   by_contra hxy
   have hx' : (v i).val (constant A x)≤1 := by
     obtain rfl | h:=eq_or_ne x 0
     · simp [constant]
     · exact ((v i).constants _ h).le
   have hy' : (v i).val (constant A y)≤1 := by
     obtain rfl | h:=eq_or_ne y 0
     · simp [constant]
     · exact ((v i).constants _ h).le
   have h:=(v i).val.map_sub (constant A y*gauge A x) (constant A x*gauge A y)
   rw [← gauge_id,(v i).constants _ (sub_ne_zero.mpr (Ne.symm hxy)),map_mul,map_mul] at h
   exact (not_le_of_gt (max_lt
     ((mul_le_of_le_one_left' hy').trans_lt hx)
     ((mul_le_of_le_one_left' hx').trans_lt hy))) h)
 let zbad:Set L := {x | gauge A x=0}
 have hz :zbad.Finite :=Set.Subsingleton.finite (by
   intro x hx y hy
   by_contra hxy
   change gauge A x=0 at hx
   change gauge A y=0 at hy
   have hconst:constant A (y-x)≠0:= by
     change seed A (algebraMap L E (y-x))≠0
     exact (_root_.map_ne_zero _).mpr ((_root_.map_ne_zero _).mpr (sub_ne_zero.mpr (Ne.symm hxy)))
   exact hconst (by rw [gauge_id,hx,hy,mul_zero,mul_zero,sub_zero]))
 obtain ⟨x,hx⟩:=Infinite.exists_notMem_finset
   (insert 0 (hz.toFinset∪univ.biUnion fun i=>(hb i).toFinset))
 have hx0:x≠0:= fun h=>hx (h ▸ mem_insert_self _ _)
 have hg:gauge A x≠0:= fun h=>hx (mem_insert_of_mem (mem_union_left _ (hz.mem_toFinset.mpr h)))
 let C' : Pencil A := { C with tilt:=x,gauge_ne :=hg }
 refine ⟨C',hx0,rfl,fun i => ?_⟩
 have hs :1≤(v i).val (gauge A x) :=le_of_not_gt fun h =>
   hx (mem_insert_of_mem (mem_union_right _ (mem_biUnion.mpr
     ⟨i,mem_univ _,(hb i).mem_toFinset.mpr h⟩)))
 have h0:gauge A C.tilt=1 := by
   rw [not_ne_iff.mp ht]
   simp [P5_7_1_7_4_3_4.gauge,constant]
 have hn:relativePolar C≠0:=div_ne_zero C.polar_ne (pow_ne_zero _ C.gauge_ne)
 have hn' : relativePolar C' ≠ 0:=div_ne_zero C'.polar_ne (pow_ne_zero _ C'.gauge_ne)
 apply Int.toNat_le_toNat
 apply neg_le_neg
 apply (log_le_log ((v i).val.ne_zero_iff.mpr hn') ((v i).val.ne_zero_iff.mpr hn)).mpr
 unfold relativePolar
 rw [h0,one_pow,div_one,map_div₀,map_pow,div_eq_mul_inv]
 exact mul_le_of_le_one_right' ((inv_le_one₀
   (pow_pos (zero_lt_one.trans_le hs) _)).mpr (one_le_pow₀ hs))
end
end qrGSFbd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrGSFbd
noncomputable section
open Polynomial Finset
open cu (L)
open E7 (CurvePlace poleOrder KB Tq)
open XX (aoG)
open qZu9hjc (valueZeros valueCoeffs)
open private adG b4t aMX cNC from ProximityPrize.SubmissionLower.Y
open scoped Classical WithZero
variable {E :Type} [Field E] [Algebra L E]
def specializeCoeff (z :L) (x :RatFunc E) :E :=
 RatFunc.eval (RingHom.id E) (algebraMap L E z) x
private theorem avoid_poly (w:CurvePlace L E) (f :E[X]) :
   ∃ bad:Finset L,∀ z∉bad,w.value (f.eval (algebraMap L E z))=adG w.value f := by
 obtain rfl | hf :=eq_or_ne f 0
 · exact ⟨∅,by simp [adG]⟩
 let v :=w.value
 let m:=adG v f
 obtain ⟨i,hi,_⟩:=cNC v f hf
 have hm:m≠0:=b4t v hf
 let c:=f.coeff i
 have hc:v c=m:=hi
 let g:=C c⁻¹*f
 let O:=v.valuationSubring
 let j:=O.subtype
 have hg (k :ℕ) :v (g.coeff k)≤1 := by
   rw [show g.coeff k=c⁻¹*f.coeff k from coeff_C_mul f,map_mul,map_inv₀,hc]
   exact (inv_mul_le_one₀ (zero_lt_iff.mpr hm)).mpr (aMX v f k)
 have hgi:v (g.coeff i)=1 := by
   rw [show g.coeff i=c⁻¹*c from coeff_C_mul f,map_mul,map_inv₀,hc,inv_mul_cancel₀ hm]
 obtain ⟨G,hG⟩:=(mem_lifts g).mp ((lifts_iff_coeff_lifts g).mpr fun k=>⟨⟨_,hg k⟩,rfl⟩ :
   g∈lifts j)
 let ρ:=IsLocalRing.residue O
 let H :=G.map ρ
 have hH :H≠0:= by
   intro hz
   have hz' : ρ (G.coeff i)=0:= by simpa only [H,coeff_map,coeff_zero] using congrArg (fun p=>p.coeff i) hz
   have hv :=v.mem_maximalIdeal_iff.mp ((IsLocalRing.residue_eq_zero_iff _).mp hz')
   rw [show (G.coeff i:E)=g.coeff i by
     change j (G.coeff i)=g.coeff i
     simpa only [coeff_map] using congrArg (fun p=>p.coeff i) hG,hgi] at hv
   exact (lt_irrefl _) hv
 let jL:=aoG w
 let k :=ρ.comp jL
 refine ⟨H.roots.toFinset.preimage k k.injective.injOn,fun z hz => ?_⟩
 have hHz :H.eval (k z)≠0:= fun he =>
   hz (Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots hH).mpr he)))
 let t:O:=G.eval (jL z)
 have hres :ρ t≠0:= by
   change (G.map ρ).eval (ρ (jL z))≠0 at hHz
   rwa [Polynomial.eval_map,eval₂_hom] at hHz
 have hv :v (t:E)=1 :=
   le_antisymm t.property (le_of_not_gt fun h =>
     hres ((IsLocalRing.residue_eq_zero_iff _).mpr (v.mem_maximalIdeal_iff.mpr h)))
 have hEval : (t:E)=g.eval (algebraMap L E z) := by
   change j (G.eval (jL z))= _
   rw [← eval₂_hom j,eval₂_eq_eval_map,hG]
   rfl
 rw [hEval,show g.eval (algebraMap L E z)=c⁻¹*f.eval (algebraMap L E z)
   from eval_C_mul] at hv
 rw [map_mul,map_inv₀,hc,inv_mul_eq_div,div_eq_one_iff_eq (hm)] at hv
 exact hv
private theorem avoid_rat (w:CurvePlace L E) (x :RatFunc E) :
  ∃ bad:Finset L,∀ z∉bad,w.value (specializeCoeff z x)=pencilVal w.value x := by
 obtain ⟨B,hB⟩:=avoid_poly w x.num
 obtain ⟨D,hD⟩:=avoid_poly w x.denom
 refine ⟨B∪D,fun z hz => ?_⟩
 rw [specializeCoeff,RatFunc.eval,eval₂_id,eval₂_id,map_div₀,
  hB z (fun h=>hz (mem_union_left _ h)),hD z (fun h=>hz (mem_union_right _ h))]
 have he :=congrArg (pencilVal w.value) (RatFunc.num_div_denom x)
 simpa only [map_div₀,pencilVal_poly] using he
theorem avoid_coeffs {ι:Type} (M:Finset ι) (w:ι→CurvePlace L E)
   (N : (RatFunc E)[X]) (B:Finset L) :
   ∃ z :L,z∉B ∧ ∀ i∈M,∀ j,(w i).value (specializeCoeff z (N.coeff j)) =
     pencilVal (w i).value (N.coeff j) := by
 classical
 choose bad hb using fun (i:ι) (j:ℕ)=>avoid_rat (w i) (N.coeff j)
 obtain ⟨z,hz⟩:=Infinite.exists_notMem_finset
   (B∪M.biUnion fun i=>(range (N.natDegree+1)).biUnion (bad i))
 refine ⟨z,fun h=>hz (mem_union_left _ h),fun i hi j => ?_⟩
 by_cases hj:N.natDegree<j
 · simp [coeff_eq_zero_of_natDegree_lt hj,specializeCoeff,RatFunc.eval]
 · exact hb i j z (fun h=>hz (mem_union_right _ (mem_biUnion.mpr
     ⟨i,hi,mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),h⟩⟩)))
omit [Algebra L E] in
theorem specialize_zeros (w:Valuation E ℤᵐ⁰) (N : (RatFunc E)[X]) (T:E[X])
   (h : ∀ i,w (T.coeff i)=pencilVal w (N.coeff i)) :
   valueZeros w T=valueZeros (pencilVal w) N := by
 have hd:T.natDegree=N.natDegree := by
   apply le_antisymm <;> apply natDegree_le_iff_coeff_eq_zero.mpr <;> intro i hi
   · apply w.zero_iff.mp
     rw [h,coeff_eq_zero_of_natDegree_lt hi,map_zero]
   · apply (pencilVal w).zero_iff.mp
     rw [← h,coeff_eq_zero_of_natDegree_lt hi,map_zero]
 have hs :=congrArg (fun n:ℕ=>(univ :Finset (Fin (n+1))).sup
   (fun i=>(WithZero.log (pencilVal w (N.coeff (i:ℕ)))).toNat)) hd
 simp only [valueZeros,Tq,valueCoeffs,poleOrder,KB,h]
 rw [hs]
end
end qrGSFbd
end
section
namespace qdpQ3Rb
noncomputable section
open Polynomial qNu3xvc
open cu (L)
open E7 (CurvePlace)
open qFD8jve (sheetPole)
open qZu9hjc (HE)
open P5_7_1_7_4_3_4 (bix)
variable {E :Type} [Field E] [Algebra L E]
def numerator (A:Equation E) (a b c:L) :E[X][X] :=
  C (C (algebraMap L E a))*(C (Polynomial.X:E[X])*A.f.derivative) +
    C (C (algebraMap L E b))*(Polynomial.X*A.f.derivative) +
    C (C (algebraMap L E (-c)))*physicalDerivative A.f
structure AffinePencil (A:Equation E) where
 a :L
 b:L
 c:L
 polar_ne :polar A false≠0
 base :RatFunc E →+* EC A
 base_seed : ∀ t,base (RatFunc.C t)=seed A t
 base_X:base RatFunc.X=KM A false (numerator A a b c)/polar A false
 finite :letI:=base.toAlgebra; Module.Finite (RatFunc E) (EC A)
 separable :letI:=base.toAlgebra; Algebra.IsSeparable (RatFunc E) (EC A)
variable {A:Equation E}
def AffinePencil.cut (C₀:AffinePencil A) (z :L) :E[X][X] :=
 numerator A C₀.a C₀.b C₀.c+C (C (algebraMap L E (-z)))*A.f.derivative
def CutBound (D:AffinePencil A) (z :L) :Prop :=
  (D.cut z).natDegree≤A.d∧HE (D.cut z) A.s (A.b+A.d*A.s) ∧
    ∀ w:CurvePlace L E,sheetPole w.value (D.cut z)≤ sheetPole w.value A.f
def AffinePencil.polynomial (C₀:AffinePencil A) : (RatFunc E)[X] :=
 bix C₀.base (polar A false) C₀.finite
end
end qdpQ3Rb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qdpQ3Rb
noncomputable section
open Polynomial Finset qNu3xvc
open cu (L)
open E7 (CurvePlace Tq poleOrder)
open qFD8jve (aFA sheetPole)
open qrezXJe (sheet_bound)
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E] {A:Equation E}
private def Good (A:Equation E) (g:E[X][X]) :Prop :=
 (∀ i j,(g.coeff i).coeff j≠0→i≤A.d∧j+i*A.s≤A.b+A.d*A.s) ∧
 ∀ w:CurvePlace L E,aFA w.value g (sheetPole w.value A.f)
private theorem ic {g:E[X][X]}
    (h : ∀ i j,(g.coeff i).coeff j=0 ∨
      ∃ (i' j' : ℕ) (a :L),i≤ i' ∧ j+i*A.s≤j'+i'*A.s ∧
        (g.coeff i).coeff j=algebraMap L E a*(A.f.coeff i').coeff j') :Good A g:= by
  constructor
  · intro i j hn
    obtain ⟨i',j',a,hi,hj,he⟩:=(h i j).resolve_left hn
    have hc: (A.f.coeff i').coeff j' ≠ 0:= fun hz=>hn (by rw [he,hz,mul_zero])
    have hf :A.f.coeff i' ≠ 0:= fun hz=>hc (by rw [hz,coeff_zero])
    exact ⟨hi.trans (le_natDegree_of_ne_zero hf),hj.trans
      ((Nat.add_le_add_right (le_natDegree_of_ne_zero hc) _).trans ((A.weight i').resolve_right hf))⟩
  · intro w i j
    rcases h i j with he | ⟨i',j',a,_,_,he⟩
    · rw [he,map_zero]; exact zero_le
    · rw [he,map_mul]
      by_cases ha :a=0
      · simp [ha]
      · rw [w.on_constants a ha,one_mul]
        exact sheet_bound w.value A.f i' j'
private theorem good_combine {g h:E[X][X]} (hg:Good A g) (hh:Good A h) (a :L) :
   Good A (g+C (C (algebraMap L E a))*h) := by
 constructor
 · intro i j hn
   by_cases he : (g.coeff i).coeff j=0
   · apply hh.1 i j
     intro hz
     exact hn (by simp [coeff_add,coeff_C_mul,he,hz])
   · exact hg.1 i j he
 · intro w i j
   rw [coeff_add,coeff_C_mul,coeff_add,coeff_C_mul]
   apply (w.value.map_add _ _).trans (max_le (hg.2 w i j) ?_)
   rw [map_mul]
   by_cases ha :a=0
   · simp [ha]
   · rw [w.on_constants a ha,one_mul]
     exact hh.2 w i j
omit [Algebra L E] in
private theorem partial_coeff (f :E[X][X]) (i:ℕ) :
   (physicalDerivative f).coeff i=(f.coeff i).derivative := by
 classical
 by_cases hi:i∈f.support
 · simp [physicalDerivative,sum_def,coeff_monomial,hi]
 · simp [physicalDerivative,sum_def,coeff_monomial,hi,notMem_support_iff.mp hi]
private theorem polar_coeff (f :E[X][X]) (i j:ℕ) :
   (f.derivative.coeff i).coeff j =
     algebraMap L E (i+1 :ℕ)*(f.coeff (i+1)).coeff j:= by
 have hcast: (↑i+1 :E[X])=C (↑(i+1) :E) := by
   rw [Polynomial.C_eq_natCast,Nat.cast_succ]
 rw [coeff_derivative,hcast,mul_comm,coeff_C_mul,map_natCast]
theorem dSE (D:AffinePencil A) (z :L) (hs :0<A.s) :CutBound D z := by
  have hx :Good A (C (Polynomial.X:E[X])*A.f.derivative) :=ic fun i j=> by
    rw [coeff_C_mul]
    cases j with
    | zero=>exact Or.inl (coeff_X_mul_zero _)
    | succ j =>
      refine Or.inr ⟨i+1,j,(i+1 :ℕ),by omega,?_,?_⟩
      · rw [Nat.add_mul]; omega
      · rw [coeff_X_mul,polar_coeff]
  have hy :Good A (Polynomial.X*A.f.derivative) :=ic fun i j=> by
    cases i with
    | zero=>exact Or.inl (by rw [coeff_X_mul_zero,coeff_zero])
    | succ i=>exact Or.inr ⟨i+1,j,(i+1 :ℕ),le_rfl,le_rfl,by rw [coeff_X_mul,polar_coeff]⟩
  have hD:Good A (physicalDerivative A.f) :=ic fun i j =>
    Or.inr ⟨i,j+1,(j+1 :ℕ),le_rfl,by omega,by
      rw [partial_coeff,coeff_derivative,map_natCast,mul_comm,Nat.cast_succ]⟩
  have hp:Good A A.f.derivative :=ic fun i j =>
    Or.inr ⟨i+1,j,(i+1 :ℕ),by omega,by rw [Nat.add_mul]; omega,polar_coeff A.f i j⟩
  have hzero :Good A 0:=ic fun _ _=>Or.inl (by simp)
  have h:=good_combine (good_combine (good_combine (good_combine hzero hx D.a) hy D.b) hD (-D.c)) hp (-z)
  have hg:Good A (D.cut z) := by
    simpa only [AffinePencil.cut,numerator,zero_add] using h
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr (fun i hi => ?_),?_,?_⟩
  · ext j
    rw [coeff_zero]
    by_contra hn
    exact (not_le_of_gt hi) (hg.1 i j hn).1
  · intro i hi
    exact (hg.1 i _ (by rwa [coeff_natDegree,leadingCoeff_ne_zero])).2
  · intro w
    unfold sheetPole Tq
    apply Finset.sup_le
    intro ij _
    unfold poleOrder
    by_cases hz : ((D.cut z).coeff ij.1).coeff ij.2=0
    · simp [hz]
    · change _≤ sheetPole w.value A.f
      exact Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr hz)).mpr
        (hg.2 w _ _))
end
end qdpQ3Rb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qdpQ3Rb
noncomputable section
open Polynomial Finset qNu3xvc
open P5 (p)
open cu (L)
open E7 (CurveField CurvePlace)
open qZV9OWb (ValueSlice)
open qZu9hjc (valueZeros)
open P5_7_1_7_4_3_4 (adG)
open qrGSFbd (specializeCoeff avoid_coeffs specialize_zeros primitive)
open private same_center from ProximityPrize.SubmissionLower.ZT8CHOb
open scoped Classical WithZero
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),
    CurveField L E→2≤A.d→A.d<p →
    ∀ (ι:Type) [Fintype ι] (w:ι→CurvePlace L E) (x :ι→L)
      (v :ι→GraphVal A false),(∀ i,Over (v i) (w i) (x i)) →
      ∃ C₀:AffinePencil A,∀ i,∃ n:ℕ,0<n ∧ ∀ f :E[X],
        (v i).val (C₀.base (algebraMap E[X] (RatFunc E) f))=adG (w i).value f^n
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (C₀:AffinePencil A),
    ∃ bad:Finset L,∀ z∉bad,CutBound C₀ z → ∃ B:ValueSlice A,B.g=C₀.cut z ∧
      ∀ j,B.N.coeff j=specializeCoeff z (C₀.polynomial.coeff j)
def c3:Prop :=P5_7_1_7_4_3_4.c3
theorem of_children (qW:c1) (cut:c2) (norm:c3) :qZV9OWb.c4 := by
  intro E _ _ A hc hs hd hp ι _ w x v hinj _ hover
  obtain ⟨C₀,hgauss⟩:=qW A hc hd hp ι w x v hover
  obtain ⟨bad,hcut⟩:=cut A C₀
  let N :=C₀.polynomial
  obtain ⟨z,hz,hval⟩:=avoid_coeffs univ w N bad
  obtain ⟨B,_,hB⟩:=hcut z hz (dSE C₀ z hs)
  have hm:N.Monic:= by
    let _:=C₀.base.toAlgebra
    let _:=C₀.finite
    exact LinearMap.charpoly_monic _
  have hn:N.coeff 0≠0:= by
    intro h
    apply B.constant_ne
    rw [hB,show C₀.polynomial.coeff 0=0 from h]
    simp [specializeCoeff,RatFunc.eval]
  refine ⟨B,?_⟩
  have hlocal (t:CurvePlace L E) (ht:t∈univ.image w) :
      (∑ i∈univ.filter (fun i=>w i=t),poleCharge (v i))≤valueZeros t.value B.N := by
    obtain ⟨P,hP,hInt,hDiv,hZero⟩:=primitive t.value t.normalized N hm hn
    have hNorm:=norm t C₀.base (polar A false) C₀.finite C₀.separable C₀.polar_ne P hP hInt hDiv
      (univ.filter (fun i=>w i=t)) (fun i=>(v i).val)
      (by
        intro i hi j hj h
        have hw:=(mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
        exact hinj (Prod.ext hw (same_center (hover i) (hw.symm ▸ hover j) h)))
      (fun i _=>(v i).normalized) (fun i hi=>(mem_filter.mp hi).2 ▸ hgauss i)
    obtain ⟨i,_,rfl⟩:=mem_image.mp ht
    have hSpecial:=specialize_zeros (w i).value N B.N
      (fun j=>(congrArg (w i).value (hB j)).trans (hval i (mem_univ i) j))
    exact hNorm.trans (hZero.trans hSpecial.symm).le
  calc
    (∑ i,poleCharge (v i)) =
        ∑ t∈univ.image w,∑ i∈univ.filter (fun i=>w i=t),poleCharge (v i) :=
      (sum_fiberwise_of_maps_to (fun _ hi=>mem_image_of_mem _ hi) _).symm
    _≤_:=sum_le_sum hlocal
end
end qdpQ3Rb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qrGSFbd
noncomputable section
open Polynomial Finset
open P5 (p)
open cu (L)

open qZu9hjc (Slice)
open qNu3xvc (Equation)
open P5_7_1_7_4_3_4 (Pencil relativePolar bix)
open scoped Classical
def c1 :Prop :=qNu3xvc.c2
def c2 :Prop :=qNu3xvc.c3
def c4 :Prop :=P5_7_1_7_4_3_4.c3
def c5:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (C:Pencil A) (a :ℕ),
    2≤A.d→A.d<p→A.b+A.d*A.s≤a→C.tilt≠0 →
    ∃ bad:Finset L,∀ z∉bad,
      ∃ T:Slice A.f A.s a,∀ j,T.N.coeff j =
        RatFunc.eval (RingHom.id E) (algebraMap L E z)
          ((bix C.base (relativePolar C) C.finite).coeff j)
end
end qrGSFbd
end
