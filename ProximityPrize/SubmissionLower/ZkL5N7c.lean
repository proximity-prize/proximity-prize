import ProximityPrize.SubmissionLower.ZPaaHRd
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.Z97nQia
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, Algebra.algebraMap_self → zCp, CommRing → za6, Function.Injective → zq4, Function.comp_apply → z3s, Ideal.Quotient.mk_surjective → zld, IsFractionRing.div_surjective → zJC, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.ringHom_ext → z86, PowerSeries.coeff → z2o, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.id_apply → z6n
section
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace qyEseja
noncomputable section
open MvPolynomial
open cu (L)
open qe6nVeb (SeedPlane)
open q7YMR4d (SmoothAt simpleQuadratic quadraticAt)
open qYzLClc (lift_plane)
open private AT section_eval section_deriv from ProximityPrize.SubmissionLower.ZXn7V0b
open private translate d3d degree_ge_two blowup blowup_red from ProximityPrize.SubmissionLower.ZSYEDJb
local notation "PS" => PowerSeries L
local notation "T" => (PowerSeries.X:PS)
local notation "PC" => (PowerSeries.C:L →+* PS)
local notation "ct" => (PowerSeries.constantCoeff :PS →+* L)
abbrev subAt {x :PS} (hx :ct x=0) :PS →ₐ[L] PS :=
 PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hx)
local notation "S[" h "]" => subAt h
theorem subst_C {x :PS} (hx :ct x=0) (c:L) :S[hx] (PC c)=PC c:= by
 simpa only [PowerSeries.algebraMap_apply,zCp,z6n] using
   (S[hx]).commutes c
theorem subst_ct {x :PS} (hx :ct x=0) (f :PS) :ct (S[hx] f)=ct f := by
 rw [subAt,PowerSeries.coe_substAlgHom,PowerSeries.constantCoeff_eq]
 simpa only [zCp,z6n] using
   PowerSeries.constantCoeff_subst_of_constantCoeff_zero hx f
private theorem other {i j k :Fin 2} (hij:i≠j) (hki:k≠i) :k=j:= by
 by_contra h
 exact hki (Fin.eq_of_val_eq (by omega))
private theorem eval_image {R:Type*} [CommSemiring R] (F:PS →+* R) (b:Fin 2→PS)
   (q:z3y (Fin 2) PS) :
   eval (F ∘ b) (map F q)=F (eval b q) := by
 rw [← eval₂_eq_eval_map,← eval₂_id (g:=b),eval₂_comp_left,RingHom.comp_id]
private theorem unique_branch (i:Fin 2) (b t:Fin 2→PS)
   (q:z3y (Fin 2) PS) (hb:eval b q=0) (ht:eval t q=0)
   (hc:ct (t i)=ct (b i)) (he : ∀ j,j≠i→t j=b j)
   (hd:eval (ct ∘ b) (pderiv i (map ct q))≠0) :t=b:= by
 let g:=AT i b q
 let d:=t i - b i
 have hpt: (fun j=>b j+if j=i then d else 0)=t:= by
   funext j
   by_cases hj:j=i
   · subst j
     simp [d]
   · simp [hj,he j hj]
 have hg0:g.eval 0=0:= by
   simpa [g,section_eval] using hb
 have hgd:g.eval d=0:= by
   change (AT i b q).eval d=0
   rw [section_eval,hpt,ht]
 have hgc:ct (g.derivative.eval 0)≠0:= by
   change ct ((AT i b q).derivative.eval 0)≠0
   rw [section_deriv,section_eval,show (fun j=>b j+if j=i then (0:PS) else 0)=b
     from funext fun j=> by simp,← eval_image ct,← pderiv_map]
   exact hd
 obtain ⟨k,hk⟩:=g.exists_mul_sq_add_linear_part_eq_eval_add 0 d
 rw [hg0,zero_add,hgd,add_zero,pow_two,← mul_assoc,← add_mul] at hk
 have hunit :ct (k*d+g.derivative.eval 0)≠0:= by
   simpa only [map_add,map_mul,d,map_sub,hc,sub_self,mul_zero,zero_add] using hgc
 have hz :=(mul_eq_zero.mp hk).resolve_left (fun hz=>hunit (by rw [hz,map_zero]))
 funext j
 by_cases hj:j=i
 · subst j
   exact sub_eq_zero.mp hz
 · exact he j hj
private theorem descend {x :PS} (hx :ct x=0) (i:Fin 2)
   (q:z3y (Fin 2) PS) (b d:Fin 2→PS)
   (hb:eval b (map (S[hx]).toRingHom q)=0)
   (hd:eval (ct ∘ b) (pderiv i (map ct q))≠0)
   (hc : ∀ j,ct (d j)=ct (b j)) (he : ∀ j,j≠i→S[hx] (d j)=b j) :
   ∃ t:Fin 2→PS,∀ j,S[hx] (t j)=b j:= by
 let F:=(S[hx]).toRingHom
 have hm:map ct (map F q)=map ct q:= by
   rw [map_map,show (ct).comp F=ct from zz4 (subst_ct hx)]
 have hr :eval (ct ∘ b) (map ct q)=0:= by rw [← hm,eval_image,hb,map_zero]
 have hc' : ct ∘ d=ct ∘ b:=funext hc
 obtain ⟨t,ht,hfix,hq⟩:=lift_plane i d q (by rwa [hc']) (by rwa [hc'])
 have ht' : F ∘ t=b:= by
   apply unique_branch i b _ _ hb
   · rw [eval_image,hq,map_zero]
   · exact (subst_ct hx _).trans ((ht i).trans (hc i))
   · intro j hj
     exact (congrArg F (hfix j hj)).trans (he j hj)
   · rwa [hm]
 exact ⟨t,congrFun ht'⟩
private theorem smooth_descend (q:SeedPlane) (u:Fin 2→L) (b:Fin 2→PS)
   (hc : ∀ j,ct (b j)=u j) (hb:eval₂ PC b q=0) (hs :SmoothAt q u) :
   ∃ (j:Fin 2) (h:ct (b j-PC (u j))=0) (f :Fin 2→PS),∀ i,S[h] (f i)=b i:= by
 obtain ⟨_,i,hi⟩:=hs
 let j:=i.succAbove (0:Fin 1)
 have hji:j≠i:=Fin.succAbove_ne i _
 let x :=b j-PC (u j)
 have hx :ct x=0:= by simp [x,hc]
 let d:Fin 2→PS:= fun k=>PC (u k)+if k=i then 0 else T
 have hm:map ct (map PC q)=q:= by
   rw [map_map,PowerSeries.constantCoeff_comp_C,map_id]
 have hmb:map (S[hx]).toRingHom (map PC q)=map PC q:= by
   rw [map_map,show (S[hx]).toRingHom.comp PC=PC from zz4 (subst_C hx)]
 refine ⟨j,hx,descend hx i (map PC q) b d ?_ ?_ ?_ ?_⟩
 · rwa [hmb,← eval₂_eq_eval_map]
 · rwa [hm,show ct ∘ b=u from funext hc]
 · intro k
   by_cases hk :k=i <;> simp [d,hk,hc]
 · intro k hk
   have hkj:k=j:=other hji.symm hk
   subst k
   change S[hx] (PC (u j)+if j=i then 0 else T)=b j
   rw [ite_eq_right hji,map_add,subst_C,PowerSeries.substAlgHom_X]
   dsimp [x]
   ring
private theorem quadratic_form (q:SeedPlane) (h:q.IsHomogeneous 2)
   {i j:Fin 2} (hij:i≠j) :
   ∃ A B D:L,q=C A*z9v i^2 +
     C B*(z9v i*z9v j)+C D *z9v j^2 := by
 obtain ⟨a,b,c,hq⟩:=qGzrWfb.binary_form q h
 have two (k :Fin 2) :k=0∨k=1 := by fin_cases k <;> decide
 rcases two i with rfl|rfl <;> rcases two j with rfl|rfl
 · exact (hij rfl).elim
 · exact ⟨a,b,c,by rw [hq];ring⟩
 · exact ⟨c,b,a,by rw [hq];ring⟩
 · exact (hij rfl).elim
private theorem chart_simple (q:SeedPlane) (hh:q.IsHomogeneous 2)
   (hs : ∃ v,SmoothAt q v) {i j:Fin 2} (hij:i≠j) (w:Fin 2→L)
   (hw:w j=1) (hroot :eval w q=0) :eval w (pderiv i q)≠0:= by
 obtain ⟨A,B,D,hq⟩:=quadratic_form q hh hij
 intro hd
 rw [hq] at hroot hd
 simp only [map_add,map_mul,map_pow,eval_X,eval_C,hw,mul_one,one_pow] at hroot
 simp [pderiv_X_of_ne (Ne.symm hij),
   hw,pow_one,mul_assoc,mul_comm,mul_left_comm] at hd
 have hB:B = -(2*A*w i) := by linear_combination hd
 have hD:D =A*(w i)^2 := by rw [hB] at hroot; linear_combination hroot
 let l:SeedPlane :=z9v i - C (w i)*z9v j
 have hq' : q=C A*l^2 := by
   rw [hq,hB,hD]
   simp only [l,map_neg,map_mul,map_pow,map_ofNat]
   ring
 obtain ⟨v,hv,k,hk⟩:=hs
 by_cases ha :A=0
 · simp [hq',ha] at hk
 rw [hq'] at hv hk
 have hl:eval v l=0:= by
   rw [map_mul,eval_C,map_pow] at hv
   by_contra hn
   exact pow_ne_zero _ hn ((mul_eq_zero.mp hv).resolve_left ha)
 simp [hl] at hk
private theorem blowup_at (q:SeedPlane) (h : ∀ m∈q.support,2≤ m.degree)
   {x :PS} (hx :ct x=0) (v :Fin 2→PS) :
   eval₂ PC (fun i=>x*v i) q=x^2*eval v (map (S[hx]).toRingHom (blowup q)) := by
 rw [eval₂_eq,blowup,map_sum,map_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro m hm
 rw [map_monomial,← eval₂_id,eval₂_monomial,z6n]
 simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,map_mul,map_pow,
   subst_C,PowerSeries.substAlgHom_X,mul_pow,Finset.prod_mul_distrib,
   Finset.prod_pow_eq_pow_sum,← Finsupp.degree_apply,Finsupp.prod]
 have hd:m.degree=2+(m.degree - 2) := by have :=h m hm; omega
 conv_lhs=>rw [hd,pow_add]
 ring
private theorem node_descend (q:SeedPlane) (u:Fin 2→L) (b:Fin 2→PS)
   (hc : ∀ j,ct (b j)=u j) (hb:eval₂ PC b q=0)
   (h₀:eval u q=0) (hd : ∀ j,eval u (pderiv j q)=0)
   (hs :simpleQuadratic q u) :
   ∃ (j:Fin 2) (h:ct (b j-PC (u j))=0) (f :Fin 2→PS),∀ i,S[h] (f i)=b i:= by
 classical
 let c:Fin 2→PS:= fun j=>b j-PC (u j)
 have hc0 (j) :ct (c j)=0:= by simp [c,hc]
 have hb' (j) :c j+PC (u j)=b j:=sub_add_cancel _ _
 by_cases hconst : ∀ j,c j=0
 · refine ⟨0,hc0 0,PC ∘ u,fun j => ?_⟩
   rw [z3s,subst_C]
   simpa only [hconst j,zero_add] using hb' j
 have hn : ∃ n:ℕ,∃ j,z2o n (c j)≠0:= by
   by_contra! hn
   exact hconst fun j=>PowerSeries.ext fun n=> by simp [hn n j]
 let n:=Nat.find hn
 obtain ⟨j,hj⟩:=Nat.find_spec hn
 have hf (k) :T^n∣c k :=PowerSeries.X_pow_dvd_iff.mpr fun m hm =>
   not_not.mp (fun hn' => Nat.find_min hn hm ⟨k,hn'⟩)
 choose w hw using hf
 have hunit :ct (w j)≠0:= by
   have hcoeff :z2o n (T^n*w j)=ct (w j) := by
     simpa only [zero_add,zW1] using
       PowerSeries.coeff_X_pow_mul (w j) n 0
   change z2o n (c j)≠0 at hj
   rwa [hw j,hcoeff] at hj
 let x :=c j
 have hx :ct x=0:=hc0 j
 have hxn:x≠0:= fun he=>hj (by change z2o n x=0; simp [he])
 let v :Fin 2→PS:= fun k=>(w j)⁻¹*w k
 have hv (k) :x*v k=c k := by
   change x*((w j)⁻¹*w k)=c k
   rw [hw k,show x=T^n*w j from hw j,mul_assoc,← mul_assoc (w j),
     PowerSeries.mul_inv_cancel _ hunit,one_mul]
 have hvj:v j=1 :=PowerSeries.inv_mul_cancel _ hunit
 let i:=j.succAbove (0:Fin 1)
 have hij:i≠j:=Fin.succAbove_ne j _
 let r :=translate u q
 let g:=blowup r
 have hdeg (m) (hm:m∈r.support) :2≤ m.degree :=degree_ge_two h₀ hd hm
 have hred:map ct g=quadraticAt q u:=blowup_red r hdeg
 have hvroot :eval v (map (S[hx]).toRingHom g)=0:= by
   have heq :eval₂ PC (fun k=>x*v k) r=0:= by
     change eval₂ PC (fun k=>x*v k) (translate u q)=0
     rw [d3d]
     simpa only [hv,hb'] using hb
   rw [blowup_at r hdeg hx] at heq
   exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hxn)
 have hr :eval (ct ∘ v) (quadraticAt q u)=0:= by
   rw [← hred,← show map ct (map (S[hx]).toRingHom g)=map ct g from
     (map_map _ _ _).trans (congrArg (fun f=>map f g) (zz4 (subst_ct hx))),
     eval_image,hvroot,map_zero]
 have hd' : eval (ct ∘ v) (pderiv i (map ct g))≠0:= by
   rw [hred]
   exact chart_simple _ (homogeneousComponent_isHomogeneous ..)
     (by obtain ⟨z,_,hz⟩:=hs; exact ⟨z,hz⟩)
     hij _ (by simp [hvj]) hr
 obtain ⟨t,ht⟩:=descend hx i g v (PC ∘ ct ∘ v) hvroot hd'
   (by intro k; simp only [z3s,PowerSeries.constantCoeff_C])
   (by
     intro k hk
     have hkj:k=j:=other hij hk
     subst k
     simp only [z3s,hvj,map_one])
 refine ⟨j,hx,fun k=>T*t k+PC (u k),fun k => ?_⟩
 rw [map_add,map_mul,PowerSeries.substAlgHom_X,ht,subst_C,hv,hb']
theorem parameter (q:SeedPlane) (u:Fin 2→L) (b:Fin 2→PS)
   (hc : ∀ j,ct (b j)=u j) (hb:eval₂ PC b q=0) (h₀:eval u q=0)
   (h:SmoothAt q u∨simpleQuadratic q u) :
   ∃ (j:Fin 2) (hx :ct (b j-PC (u j))=0) (f :Fin 2→PS),∀ i,S[hx] (f i)=b i:= by
 by_cases hs :SmoothAt q u
 · exact smooth_descend q u b hc hb hs
 · exact node_descend q u b hc hb h₀
     (fun i=> by by_contra hi; exact hs ⟨h₀,i,hi⟩) (h.resolve_left hs)
end
end qyEseja
end
set_option backward.isDefEq.respectTransparency false
namespace qyEseja
noncomputable section
open MvPolynomial
open cu (L)
open Cu
open qZfVj1b (gRK)
open scoped WithZero
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
open private series_value from ProximityPrize.SubmissionLower.Z66Jm5b
attribute [local instance] gRK
local notation "PS" => PowerSeries L
local notation "LS" => LaurentSeries L
local notation "ct" => (PowerSeries.constantCoeff :PS →+* L)
local notation "PC" => (PowerSeries.C:L →+* PS)
local notation "ν" => (Valued.v :Valuation LS ℤᵐ⁰)
local notation "S[" h "]" => subAt h
private def incl:PS →ₐ[L] LS :=
 ⟨HahnSeries.ofPowerSeries ℤ L,fun c=> by
   rw [PowerSeries.algebraMap_apply,zCp,LaurentSeries.algebraMap_apply]
   exact PowerSeries.coe_C _⟩
private theorem value_exp (f :PS) (hf :f≠0) :
   ν (f :LS)=WithZero.exp (-(f.order.toNat :ℤ)) :=
 series_value f _ (PowerSeries.coeff_of_lt_order_toNat) (PowerSeries.coeff_order hf)
private theorem value_subst {x :PS} (hx :ct x=0) (f :PS) (hf :S[hx] f≠0) :
   ν (S[hx] f :LS)=ν (x :LS)^f.order.toNat := by
 have hf' : f≠0:= fun he=>hf (by rw [he,map_zero])
 have hu:ν (S[hx] (PowerSeries.divXPowOrder f) :LS)=1 := by
   rw [← WithZero.exp_zero]
   apply series_value _ 0 (fun _ hm=>(Nat.not_lt_zero _ hm).elim)
   rw [zW1,subst_ct]
   exact PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf'
 have hh:=congrArg S[hx] (PowerSeries.X_pow_order_mul_divXPowOrder (f :=f))
 rw [map_mul,map_pow,PowerSeries.substAlgHom_X] at hh
 rw [← hh,PowerSeries.coe_mul,PowerSeries.coe_pow,map_mul,map_pow,hu,mul_one]
theorem proof :qZfVj1b.c4 := by
 intro Q _ u _ h₀ hr v a hv b ha hc
 have he (g:sQ) :
     a (algebraMap (abz Q) (oO Q)
       (Ideal.Quotient.mk (auG Q) g))=(↑(eval₂ PC b g:PS) :LS) := by
   let e :sQ →ₐ[L] PS:=aeval b
   have hh:a.comp (aeval (Wt Q))=incl.comp e := by
     apply MvPolynomial.algHom_ext
     intro i
     simpa [e,incl] using ha i
   rw [← dc8]
   exact DFunLike.congr_fun hh g
 have hb:eval₂ PC b Q=0:= by
   apply HahnSeries.ofPowerSeries_injective (Γ:=ℤ)
   change (↑(eval₂ PC b Q:PS) :LS)=(0:PS)
   rw [← he,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton Q)),
     map_zero,map_zero,PowerSeries.coe_zero]
 obtain ⟨j,hx,f,hf⟩:=parameter Q u b hc hb h₀ hr
 let x :=b j-PC (u j)
 let G (g:sQ) :PS:=eval₂ PC f g
 have hG (g:sQ) :S[hx] (G g)=eval₂ PC b g:= by
   change (S[hx]).toRingHom (eval₂ PC f g)= _
   rw [eval₂_comp_left,show (S[hx]).toRingHom.comp PC=PC from zz4 (subst_C hx),
     show (S[hx]).toRingHom ∘ f=b from funext hf]
 obtain ⟨c,hval⟩:=v.normalized (WithZero.exp (-1 :ℤ))
 rw [hv] at hval
 obtain ⟨r,s,_,rfl⟩:=zJC (abz Q) c
 obtain ⟨r,rfl⟩:=zld r
 obtain ⟨s,rfl⟩:=zld s
 rw [map_div₀,he,he,← hG,← hG,map_div₀] at hval
 have hnz :=div_ne_zero_iff.mp (hval.trans_ne WithZero.exp_ne_zero)
 have hn (g:sQ) (hg:ν (S[hx] (G g) :LS)≠0) :S[hx] (G g)≠0 :=
   fun h=>hg (by simp [h,PowerSeries.coe_zero])
 have hvr :=value_subst hx _ (hn r hnz.1)
 have hvs :=value_subst hx _ (hn s hnz.2)
 rw [hvr,hvs] at hval
 have hxn:x≠0:= by
   intro hz
   have hpow (n:ℕ) (hn:ν (x :LS)^n≠0) :n=0:= by
     contrapose! hn
     simp [hz,PowerSeries.coe_zero,zero_pow hn]
   simp only [hpow _ (hvr ▸ hnz.1),hpow _ (hvs ▸ hnz.2),pow_zero,div_one] at hval
   exact (by decide : (0:ℤ) ≠ -1) (WithZero.exp_inj.mp (WithZero.exp_zero.trans hval))
 rw [show b j-PC (u j)=x from rfl,value_exp x hxn,← WithZero.exp_nsmul,
   ← WithZero.exp_nsmul,← WithZero.exp_sub] at hval
 have hint :=WithZero.exp_inj.mp hval
 simp only [nsmul_eq_mul] at hint
 have hone : (x.order.toNat :ℤ)*((G r).order.toNat - ((G s).order.toNat :ℤ))=1 := by
   linear_combination -hint
 have hn1 :x.order.toNat=1 := by
   have hh:=congrArg Int.natAbs hone
   rw [Int.natAbs_mul,Int.natAbs_natCast] at hh
   exact Nat.dvd_one.mp ⟨_,hh.symm⟩
 refine ⟨j,?_⟩
 have hn' := PowerSeries.coeff_order hxn
 rw [hn1] at hn'
 simpa [x,PowerSeries.coeff_C] using hn'
end
end qyEseja
end
section
section
set_option backward.isDefEq.respectTransparency false
namespace qThdpma
noncomputable section
open Polynomial
open scoped nonZeroDivisors
open cu (L)
open qNu3xvc (Equation EC a7W seed amm jU chartEq KM polar)
open qdpQ3Rb (AffinePencil numerator)
open qZu9hjc (physicalDeriv jacobian)
open qLXroAb (tu evalXY)
open qJm9rWb (pencil_derivation directional)
theorem pair_map {R S T:Type} [za6 R] [za6 S] [za6 T]
    (j:R →+* S) (k :S →+* T) (x y :S) (f :R[X][X]) :
    k (pairHom j x y f)=pairHom (k.comp j) (k x) (k y) f := by
  have h:k.comp (pairHom j x y)=pairHom (k.comp j) (k x) (k y) := by
    apply z86
    · suffices hc:k.comp (eval₂RingHom j x)=eval₂RingHom (k.comp j) (k x) by
        intro r
        simpa [pairHom] using zLs hc r
      apply z86
      · simp
      · simp
    · simp [pairHom]
  exact zLs h f
theorem jac_map {R E S:Type} [Field E] [za6 R] [za6 S]
  (j:E →+* R) (k :R →+* S) (x y u:R) (f g:E[X][X]) :
  k (cutJac j x y u f g)=cutJac (k.comp j) (k x) (k y) (k u) f g:= by
 simp only [cutJac,map_mul,map_sub,pair_map]
variable {E :Type} [Field E] [zZE L E] {A:Equation E}
theorem ab6 (D:AffinePencil A) (z :L) :
  D.cut z=numerator A D.a D.b D.c - C (C (algebraMap L E z))*A.f.derivative := by
 let j:=((z1z:E[X] →+* E[X][X]).comp (z1z:E →+* E[X])).comp
  (algebraMap L E)
 have hj:C (C (algebraMap L E (-z))) = -(C (C (algebraMap L E z)) :E[X][X]) :=j.map_neg z
 rw [AffinePencil.cut,hj]
 exact (congrArg (fun t:E[X][X]=>numerator A D.a D.b D.c+t)
  (neg_mul (C (C (algebraMap L E z))) A.f.derivative)).trans (sub_eq_add_neg _ _).symm
theorem jac_cut (D:AffinePencil A) (z :L) {S:Type} [Field S]
   (j:E →+* S) (x y :S) :
   jacobian j x y A.f (D.cut z) =
     cutJac j x y (j (algebraMap L E z)) A.f (numerator A D.a D.b D.c) := by
 let a :=algebraMap L E z
 have hd (b c:E[X][X]) :physicalDeriv (b - C (C a)*c) =
     physicalDeriv b - C (C a)*physicalDeriv c:= by
   ext i:1
   change (qLXroAb.dx (b - C (C a)*c)).coeff i =
     (qLXroAb.dx b - C (C a)*qLXroAb.dx c).coeff i
   simp only [qJm9rWb.bXI,coeff_sub,coeff_C_mul,derivative_sub,
     derivative_C_mul]
 change pairHom j x y (physicalDeriv A.f)*pairHom j x y (D.cut z).derivative -
   pairHom j x y A.f.derivative*pairHom j x y (physicalDeriv (D.cut z))= _
 rw [ab6,hd,derivative_sub,derivative_C_mul]
 simp [cutJac,pairHom,a]
theorem generic_jac (D:AffinePencil A) :
    cutJac (seed A) (amm A) (jU A false) (D.base RatFunc.X)
      A.f (numerator A D.a D.b D.c)≠0:= by
  let F:=EC A
  have hseed (a :E) :algebraMap E F a=seed A a := by
    rw [zG3 E (AdjoinRoot A.f) F,AdjoinRoot.algebraMap_eq']
    rfl
  let e :RatFunc E ≃+* tu E :=RatFunc.toFractionRingRingEquiv E
  have he (q:E[X]) :e.symm (algebraMap E[X] (tu E) q)=algebraMap E[X] (RatFunc E) q:= by
    change (RatFunc.toFractionRingRingEquiv E).symm _ = _
    rw [RatFunc.toFractionRingRingEquiv_symm_eq]
    exact (IsLocalization.algEquiv (E[X]⁰) (tu E) (RatFunc E)).commutes q
  let j:tu E →+* F:=D.base.comp e.symm.toRingHom
  let:zZE (tu E) F:=j.toAlgebra
  let:IsScalarTower E (tu E) F :=
    zsL (R:=E) (S:=tu E) (A:=F) fun a=> by
    change algebraMap E F a=D.base (e.symm (algebraMap E (tu E) a))
    rw [hseed,zG3 E E[X] (tu E),he]
    change seed A a=D.base (algebraMap E[X] (RatFunc E) (C a))
    rw [RatFunc.algebraMap_C]
    exact (D.base_seed a).symm
  let:zZE ℤ F:=Ring.toIntAlgebra F
  let:zw7 (tu E) F:= by
    let:zZE (RatFunc E) F:=D.base.toAlgebra
    let:zw7 (RatFunc E) F:=D.separable
    let:zZE (RatFunc E) (tu E) :=e.toRingHom.toAlgebra
    let:IsScalarTower (RatFunc E) (tu E) F :=
      zsL (R:=RatFunc E) (S:=tu E) (A:=F) fun t=> by
      change D.base t=D.base (e.symm (e t))
      rw [e.symm_apply_apply]
    exact Algebra.isSeparable_tower_top_of_isSeparable (RatFunc E) (tu E) F
  obtain ⟨δ,hδ,hu⟩:=pencil_derivation (E :=E) (M:=F)
  have hu' : δ (D.base RatFunc.X)=1 := by
    change δ (D.base (e.symm (algebraMap E[X] (tu E) z7y)))=1 at hu
    rw [he,RatFunc.algebraMap_X] at hu
    exact hu
  let x :=amm A
  let y :=jU A false
  let u:=D.base RatFunc.X
  let g:=numerator A D.a D.b D.c
  let ev :=pairHom (seed A) x y
  have hroot :ev=a7W A:= by
    apply z86
    · suffices he :eval₂RingHom (seed A) x=(a7W A).comp z1z by
        intro r
        simpa [ev,pairHom] using zLs he r
      apply z86
      · intro a
        simp [seed]
      · simp [x,amm]
    · simp [ev,pairHom,y,jU]
  have hchart:KM A false=ev := by
    simp only [KM,← hroot]
    change eval₂RingHom (ev.comp C) y=ev
    apply z86 <;> simp [ev,pairHom]
  have hq:ev A.f.derivative≠0:= by
    simpa only [polar,chartEq,Bool.false_eq_true,ite_false,hchart] using D.polar_ne
  have hf :ev A.f=0:= by simp [hroot,a7W]
  have hg:ev g=u*ev A.f.derivative := by
    have h:=D.base_X
    change u=KM A false g/polar A false at h
    simp only [polar,chartEq,Bool.false_eq_true,ite_false,hchart] at h
    exact ((eq_div_iff hq).mp h).symm
  have hc (r :E[X][X]) :δ (ev r) =
      ev (physicalDeriv r)*δ x+ev r.derivative*δ y := by
    have hh:algebraMap E F=seed A:=zz4 hseed
    simpa only [ev,pairHom,evalXY,coe_eval₂RingHom,hh,qLXroAb.dx,physicalDeriv] using
      directional δ hδ x y r
  have hdf :=hc A.f
  rw [hf,map_zero] at hdf
  have hdg:=congrArg δ hg
  have hleib:=δ.leibniz u (ev A.f.derivative)
  change δ (u*ev A.f.derivative)=u*δ (ev A.f.derivative)+ev A.f.derivative*δ u at hleib
  rw [show δ u=1 from hu',mul_one] at hleib
  rw [hc g,hleib,hc A.f.derivative] at hdg
  intro hz
  change ev (physicalDeriv A.f)*(ev g.derivative - u*ev A.f.derivative.derivative) -
    ev A.f.derivative*(ev (physicalDeriv g) - u*ev (physicalDeriv A.f.derivative))=0 at hz
  apply hq
  apply (mul_eq_zero.mp (_:ev A.f.derivative*ev A.f.derivative=0)).resolve_left hq
  linear_combination -(ev A.f.derivative)*hdg -
    (ev g.derivative - u*ev A.f.derivative.derivative)*hdf-δ x*hz
end
end qThdpma
end
section
namespace qThdpma
noncomputable section
open Polynomial
theorem companion_product {E :Type} [Field E] (P Q:E[X]) (hP:P.Monic) (hs :P.Separable) :
    ∃ r :Fin P.natDegree→AlgebraicClosure E,zq4 r ∧
      (∀ i,P.eval₂ (algebraMap E (AlgebraicClosure E)) (r i)=0) ∧
      (multMatrix P.natDegree P Q).charpoly.map (algebraMap E (AlgebraicClosure E)) =
        ∏ i,((z7y: (AlgebraicClosure E)[X]) -
          C (Q.eval₂ (algebraMap E (AlgebraicClosure E)) (r i))) := by
  classical
  let Ω:=AlgebraicClosure E
  let k :=algebraMap E Ω
  let e :Fin P.natDegree ≃ P.rootSet Ω:=(Fintype.equivFinOfCardEq (card_rootSet_eq_natDegree hs (IsAlgClosed.splits _))).symm
  let r (i:Fin P.natDegree) :Ω:=(e i).val
  have hinj:zq4 r :=Subtype.val_injective.comp e.injective
  have hr (i:Fin P.natDegree) :P.eval₂ k (r i)=0:= by
    exact (aeval_eq_zero_of_mem_rootSet (e i).property :aeval (r i) P=0)
  refine ⟨r,hinj,hr,?_⟩
  let M:=(multMatrix P.natDegree P Q).map k
  let V:=Matrix.vandermonde r
  let J:=Matrix.diagonal (fun i=>Q.eval₂ k (r i))
  have hV:V*M=J*V:= by
    ext i j
    let p:= Q*(z7y:E[X])^(j:ℕ)
    have hrem:=sum_modByMonic_coeff (p:=p) hP (degree_le_natDegree :P.degree≤P.natDegree)
    have hEval :=congrArg (eval₂RingHom k (r i)) hrem
    rw [map_sum] at hEval
    simp only [coe_eval₂RingHom,eval₂_monomial] at hEval
    rw [eval₂_modByMonic_eq_self_of_root (hr i),eval₂_mul,eval₂_pow,eval₂_X] at hEval
    rw [Matrix.mul_apply,Matrix.diagonal_mul]
    simpa only [V,M,J,Matrix.vandermonde_apply,Matrix.map_apply,multMatrix,
      p,mul_comm] using hEval
  have hv :IsUnit V.det:=(Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  rw [← Matrix.charpoly_map]
  change M.charpoly= _
  calc
    M.charpoly=(V⁻¹*(V*M)).charpoly := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hv]
    _=(J*(V*V⁻¹)).charpoly := by rw [hV,Matrix.charpoly_mul_comm V⁻¹,mul_assoc]
    _=J.charpoly := by rw [Matrix.mul_nonsing_inv _ hv,mul_one]
    _ = _:=Matrix.charpoly_diagonal _
end
end qThdpma
end
section
set_option backward.isDefEq.respectTransparency false
namespace qxblDlc
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open gT (kM)
open Cu
open E7 (CurveField CurvePlace poleOrder Gb)
open agN (O7 d4p emC
 gDD b27)
open qK3TPae (regular)
open qZfVj1b (gRK pivot)
open q1kuFjb (AtSite)
open quN7Z4a (Sheet physicalWeight)
open qBajpRb (cls)
open qRoCwuc (dSG)
open qkgz7gb (rV)
open scoped Classical
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
open private projection seed_transcendental from ProximityPrize.SubmissionLower.Z66Jm5b
open private curve b5S pivot_ne normal_degree normal_monic normal_irreducible at_normal from ProximityPrize.SubmissionLower.ZPaaHRd
attribute [local instance] gRK
def c1 :Prop :=qZfVj1b.c2
def c2 :Prop :=qZfVj1b.c3
def c3:Prop :=qZfVj1b.c4
private theorem linear_single {k E :Type} [Field k] [Field E] [zZE k E]
  (s :Fin 2→E) (i:Fin 2) :O7 (Pi.single i (1 :k)) s=s i:= by
 simp [O7]
theorem curve_field :qZfVj1b.c1 := by
  intro Q hQ _
  let E :=oO Q
  let s :=Wt Q
  let e :sQ →ₐ[L] E :=zIe s
  have hk :RingHom.ker e.toRingHom=auG Q:= by
    ext q
    rw [RingHom.mem_ker]
    change zIe (Wt Q) q=0↔q∈auG Q
    rw [dc8,map_eq_zero_iff _ (IsFractionRing.injective (abz Q) E),
      Ideal.Quotient.eq_zero_iff_mem]
  have hq:e Q=0:=RingHom.mem_ker.mp (hk.symm ▸ Ideal.mem_span_singleton_self Q)
  have hg:IntermediateField.adjoin L (Set.range s) = ⊤ := by
    have hm (a :abz Q) :
        algebraMap (abz Q) E a∈IntermediateField.adjoin L (Set.range s) := by
      obtain ⟨q,rfl⟩:=zld a
      apply IntermediateField.algebra_adjoin_le_adjoin L (Set.range s)
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨q,dc8 Q q⟩
    apply top_unique
    intro x _
    obtain ⟨a,b,_,rfl⟩:=zJC (abz Q) x
    exact div_mem (hm a) (hm b)
  obtain ⟨i,hi⟩:=seed_transcendental Q hQ.out s hk
  have hC:CurveField L E := by
    let a :Fin 2→L:=Pi.single i 1
    have ha :O7 a s=s i:=linear_single s i
    exact ⟨s i,hi,ha ▸ (projection Q hQ.out.ne_zero s hq hg a (ha.symm ▸ hi)).1⟩
  have hdiv :=aFU.of_children
    bRt.proof bRu.proof L E hC
  obtain ⟨a,ha,_⟩:=d4p hdiv s
  have ht:0<Gb L E s :=(emC hC hdiv s).1 ⟨i,hi⟩
  have hh: (∑ᶠ v :CurvePlace L E,poleOrder v.value (O7 a s)) =
      Gb L E s :=finsum_congr ha
  have hz :=gDD (hh.symm ▸ ht)
  have hdeg:Gb L E s≤Q.totalDegree := by
    rw [← hh,(hdiv _).2.2.2 hz]
    exact (projection Q hQ.out.ne_zero s hq hg a hz).2
  have hv :Nonempty (CurvePlace L E) := by
    by_contra hn
    let:=not_nonempty_iff.mp hn
    simp only [Gb,finsum_of_isEmpty,Nat.lt_irrefl] at ht
  exact ⟨Classical.choice hv,hC,fun j =>
    (finsum_le_finsum (hdiv (s j)).1 (b27 hdiv s) (fun v =>
      Finset.le_sup (f := fun i=>poleOrder v.value (s i)) (Finset.mem_univ j))).trans hdeg⟩
private theorem normal_weight {Q:sQ} [Fact (Irreducible Q)]
   {J:Ideal kM} {g H D W:ℕ} {T:Finset K} {z :K→K} {s :K→K[X]}
   (S:Sheet Q J g H T z s) (hw:physicalWeight D S.root.equation≤W) :
   ∀ i,(qZfVj1b.normalize S.root.equation).coeff i≠0 →
     ((qZfVj1b.normalize S.root.equation).coeff i).natDegree+i*D ≤W:= by
 intro i hi
 simp only [qZfVj1b.normalize,coeff_C_mul] at hi ⊢
 rw [natDegree_C_mul (inv_ne_zero (b5S S))]
 exact (Finset.le_sup (f := fun i=>(S.root.equation.coeff i).natDegree+i*D)
   (mem_support_iff.mpr (right_ne_zero_of_mul hi))).trans hw
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :qYdH9sc.c2 := by
  intro Q _ J T z s D g H W S hz hg hpg hw
  have hp:Q.totalDegree<p:=(Nat.le_mul_of_pos_right _ hg).trans_lt hpg
  obtain ⟨v,hc,hh⟩:=curve_field Q hp
  let Cq:=curve hc hh
  let U:=regular Q z T
  have hU:U⊆T:=filter_subset _ _
  let G:=U.filter fun γ=>MvPolynomial.eval (S.parameter γ) (pivot S)≠0
  have hG:G⊆U:=filter_subset _ _
  have hcut: (U \ G).card≤H := by
    have hb:=dSG S hz (pivot S) (pivot_ne S) (U \ G)
      (fun _ hg=>hU (mem_sdiff.mp hg).1) (fun γ hg=> by
        by_contra hn
        exact (mem_sdiff.mp hg).2 (mem_filter.mpr ⟨(mem_sdiff.mp hg).1,hn⟩))
    simpa only [one_mul] using hb.trans (Nat.mul_le_mul_right H (S.bY.degree.2 _ _))
  let lift (γ:K) (hγ:γ∈G) :=
    Classical.choice (h2 S.bY hp hc (z γ) (S.parameter γ) (S.onBase γ (hU (hG hγ))))
  let A (γ:K) (hγ:γ∈G) :AtSite Cq (rV z γ) := by
    let B:=lift γ hγ
    refine ⟨B.map,B.place,B.value,?_⟩
    let b (i:Fin 2) :=B.series (cls S.bY (z9v (Sum.inl i)))
    have hb (i:Fin 2) :B.map (Cq.seed i)=(b i:LaurentSeries L) := by
      rw [B.lift_eq,qBajpRb.incl_cls]
      simp [qBajpRb.ek,Cq,curve]
    have hres (i:Fin 2) :PowerSeries.constantCoeff (b i)=rV z γ i:= by
      rw [B.reduce,qBajpRb.atMark_cls,MvPolynomial.eval_X]
      rfl
    exact ⟨b,hb,hres,h3 _ hp (S.onSeed γ (hU (hG hγ))) (mem_filter.mp (hG hγ)).2
      B.place B.map B.value b hb hres⟩
  let place (γ:K) :CurvePlace L Cq.E :=if hγ:γ∈G then (A γ hγ).place else v
  have hplace (γ:K) (hγ:γ∈G) :place γ=(A γ hγ).place :=dite_eq_left hγ
  have hd:=normal_degree S
  let F:P5_7_3_5_2.Sheet Cq z s := {
    f :=qZfVj1b.normalize S.root.equation
    irreducible :=normal_irreducible S
    positive :=hd.symm ▸ hg
    normalized:=normal_monic S
    marks :=G
    atPlace := fun γ hγ=>(A γ hγ).map
    place :=place
    distinct := by
      intro γ hγ δ hδ hh
      rw [hplace γ hγ,hplace δ hδ] at hh
      exact hz (hU (hG hγ)) (hU (hG hδ))
        ((algebraMap K L).injective (congrFun ((A γ hγ).site_eq_of_place (A δ hδ) hh) 0))
    value := fun γ hγ c=>(congrArg (fun w:CurvePlace L Cq.E=>w.value c) (hplace γ hγ)).trans
      ((A γ hγ).value c)
    arc := fun γ hγ=>(A γ hγ).arc
    integral:= fun γ hγ i j=> by
      exact (congrArg (fun w:CurvePlace L Cq.E =>
        w.value (((qZfVj1b.normalize S.root.equation).coeff i).coeff j)) (hplace γ hγ)).trans_le
          ((at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).1 i j)
    root := fun γ hγ=>(at_normal S (hγ:=hU (hG hγ)) (lift γ hγ) (mem_filter.mp hγ).2).2 }
  exact ⟨Cq,F,hd,h1 S.bY hc S.height,normal_weight S hw,hG,hcut⟩
end
end qxblDlc
end
section
namespace q1XeJwa
noncomputable section
open Polynomial
open P5 (K I)
open cu (L)
open Cu (sQ oO Wt)
open E7 (CurveField CurvePlace poleOrder)
open q82zwcd (WordChart)
open qb0hmCe (CurveModel)
open qZfVj1b (gRK)
open private curve from ProximityPrize.SubmissionLower.ZPaaHRd
attribute [local instance] gRK
open scoped WithZero
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
def changed (J:WordChart D w U s) {E :Type} [Field E] [zZE L E]
    (f :E[X][X]) :E[X][X] :=
  let m:=Polynomial.mapRingHom (algebraMap L E)
  qwGrtCa.transform (m J.b₀) (-m J.b₁) (-m J.a₀) (m J.a₁) f.natDegree f
abbrev seedCurve {q:sQ} [Fact (Irreducible q)]
  (hc:CurveField L (oO q))
  (hh : ∀ i,(∑ᶠ v :CurvePlace L (oO q),
    poleOrder v.value (Wt q i))≤q.totalDegree) :CurveModel q :=
 curve hc hh
end
end q1XeJwa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
namespace qVuPRtb
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (p)


open q82zwcd (WordChart DualSheet CompressionOK highFee)
open qK3TPae (AmplifiedCut)




def c1 :Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} (F:DualSheet J q z) (k c j W B:ℕ),
    (∀ γ∈U,(J.Q γ).natDegree≤J.u₀∧(J.P γ).natDegree≤J.u₁) →
    3≤F.d→F.d<p→ CompressionOK D F.d k c j W B → ¬ F.Jm W →
    ∃ C:AmplifiedCut U,C.ng.sum (fun _ n=>n)<p^C.order*(highFee F.d k c*F.h+1)
end
end qVuPRtb
end
end
