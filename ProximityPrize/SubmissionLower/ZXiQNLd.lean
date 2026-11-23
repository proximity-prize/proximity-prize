import ProximityPrize.SubmissionLower.ZFKrBre
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Equiv.swap → zFe, Function.Injective → zq4, Ideal.Quotient.mk → zVv, Ideal.isPrime_span_singleton_of_prime → zN9, Ideal.span → zyf, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.degreeOf_eq_sup → zXi, MvPolynomial.finSuccEquiv → z8s, MvPolynomial.finSuccEquiv_X_succ → z07, MvPolynomial.finSuccEquiv_apply → zye, MvPolynomial.map → zDK, MvPolynomial.map_map → z6Y, MvPolynomial.optionEquivLeft_coeff_coeff → z9x, MvPolynomial.rename → zHw, MvPolynomial.renameEquiv → zGY, MvPolynomial.rename_X → z6l, MvPolynomial.support_map_of_injective → zra, MvPolynomial.totalDegree_C → ziW, MvPolynomial.totalDegree_add → zdH, MvPolynomial.totalDegree_mul → zhM, MvPolynomial.totalDegree_pow → zVs, MvPolynomial.uniqueFactorizationMonoid → zhK, Nat.add_le_add_right → zlr, Nat.add_zero → zXY, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.zero_add → zbc, Polynomial → zM1, Polynomial.X → z7y, Polynomial.algebraMap_apply → zpj, Polynomial.derivative → zst, Polynomial.mapEquiv → zNc, Polynomial.uniqueFactorizationMonoid → zV6, RingHom.comp_apply → zQb, RingHom.ker → zdq
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qT3dOZa
noncomputable section
open Polynomial Finset
open cu (FX aZ Equation Jet)
open pI (oU)
open atc (aW4 jetDegree gY)
open vq (Dx aG6)
open Qv (S4 lX)
open P5_7_1 (TopRow topLift topConjugate wD)
open qaySLPd (pad orient SupportCaps)
open private aOh aki from ProximityPrize.SubmissionLower.T
theorem phys_zero :lX 0=0:= by
 simp [lX]
theorem coeffLift {d:Equation→Equation} (h0:d 0=0) (f :Jet) (v :ℕ) :
   (S4 d f).coeff v=d (f.coeff v) := by
 rw [S4,Polynomial.sum_def,Polynomial.finsetSum_coeff,Finset.sum_eq_single v]
 · exact coeff_monomial_same _ _
 · exact fun j _ hj=>coeff_monomial_of_ne _ hj.symm
 · intro hv
   rw [notMem_support_iff.mp hv,h0,monomial_zero_right,coeff_zero]
theorem lift_support {i:Fin 2} {T:TopRow} {e :Fin 4 →₀ ℕ}
   (he :e∈(topLift (orient i T)).support) :e∈T.support := by
 have ho:=MvPolynomial.support_map_subset _ _ he
 by_cases hi:i=0
 · simpa only [orient,hi,ite_true] using ho
 · exact MvPolynomial.support_map_subset _ _ (by simpa only [orient,hi,ite_false,
     topConjugate] using ho)
private abbrev dM (P:Jet) (b j u:ℕ) :Prop :=oU P ⟨0,b,j,u⟩
private theorem weaken {P:Jet} {b j u b' j' u' : ℕ}
  (h:dM P b j u) (hb:b≤b') (hj:j≤j') (hu:u≤u') :dM P b' j' u' :=
 fun v y hP=>⟨(h v y hP).1.trans hb,(h v y hP).2.1.trans hj,(h v y hP).2.2.trans hu⟩
private theorem addFits {P Q:Jet} {b j u:ℕ}
  (hP:dM P b j u) (hQ:dM Q b j u) :dM (P+Q) b j u:= by
 simp only [dM,aW4,jetDegree,gY,map_add] at hP hQ ⊢
 exact ⟨(zdH _ _).trans (max_le hP.1 hQ.1),
  natDegree_add_le_of_degree_le hP.2.1 hQ.2.1,
  (zdH _ _).trans (max_le hP.2.2 hQ.2.2)⟩
private theorem mulFits {P Q:Jet} {b j u b' j' u' : ℕ}
  (hP:dM P b j u) (hQ:dM Q b' j' u') :dM (P*Q) (b+b') (j+j') (u+u') := by
 simp only [dM,aW4,jetDegree,gY,map_mul] at hP hQ ⊢
 exact ⟨(zhM _ _).trans (Nat.add_le_add hP.1 hQ.1),
  natDegree_mul_le_of_le hP.2.1 hQ.2.1,
  (zhM _ _).trans (Nat.add_le_add hP.2.2 hQ.2.2)⟩
private theorem negFits {P:Jet} {b j u:ℕ} (h:dM P b j u) :dM (-P) b j u:= by
 simp only [dM,aW4,jetDegree,gY,map_neg,MvPolynomial.totalDegree_neg] at h ⊢
 exact ⟨h.1,natDegree_neg_le_of_le h.2.1,h.2.2⟩
private theorem powFits {P:Jet} {b j u:ℕ} (h:dM P b j u) (n:ℕ) :
  dM (P^n) (n*b) (n*j) (n*u) := by
 obtain ⟨hb,hj,hu⟩:=(aW4 _ _).mp h
 exact (aW4 _ _).mpr ⟨by
  simpa only [jetDegree,map_pow,z5A] using
   (zVs (aOh P) n).trans (zBI n hb),
  by simpa only [z5A] using natDegree_pow_le_of_le n hj,by
  simpa only [gY,map_pow,z5A] using
   (zVs (aki P) n).trans (zBI n hu)⟩
private theorem sumFits {α:Type*} (A:Finset α) (F:α→Jet) {b j u:ℕ}
   (h : ∀ a∈A,dM (F a) b j u) :dM (∑ a∈A,F a) b j u:= by
 classical
 induction A using Finset.induction_on with
 | empty=>simp [dM,oU]
 | insert a A ha ih =>
   rw [Finset.sum_insert ha]
   exact addFits (h a (Finset.mem_insert_self _ _))
     (ih fun x hx=>h x (Finset.mem_insert_of_mem hx))
private theorem monoFits (a :aZ) (y v u:ℕ) (ha :a.totalDegree≤u) :
   dM (monomial v (monomial y a)) (y+v) v u:= by
 intro j i h
 by_cases hv :j=v
 · subst j
   by_cases hy :i=y
   · subst i
     exact ⟨le_rfl,le_rfl,by simpa only [coeff_monomial_same] using ha⟩
   · exact (h (by rw [coeff_monomial_same,coeff_monomial_of_ne _ hy])).elim
 · exact (h (by rw [coeff_monomial_of_ne _ hv,coeff_zero])).elim
private theorem scalarFits (a :FX) :dM (algebraMap FX Jet a) 0 0 0:= by
 change dM (C (C (znf a))) 0 0 0
 simpa only [monomial_zero_left,zbc] using
  monoFits (znf a) 0 0 0 (ziW _).le
private theorem velocityFits :dM (z7y:Jet) 1 1 0:= by
 simpa only [monomial_zero_left,C_1,monomial_one_one_eq_X,zbc] using
  monoFits 1 0 1 0 MvPolynomial.totalDegree_one.le
private theorem ordinateFits :dM (C (z7y:Equation)) 1 0 0:= by
 simpa only [monomial_zero_left,monomial_one_one_eq_X,zXY] using
  monoFits 1 1 0 0 MvPolynomial.totalDegree_one.le
private theorem seedFits (i:Fin 2) :dM (C (C (z9v i))) 0 0 1 := by
 simpa only [monomial_zero_left,zbc] using
  monoFits (z9v i) 0 0 1 (MvPolynomial.totalDegree_X _).le
private theorem own (f :Jet) :dM f (wD f 0) (wD f 1) (wD f 2) :=
 (aW4 _ _).mpr ⟨le_rfl,le_rfl,le_rfl⟩
private theorem physFits (f :Jet) :
   dM (S4 lX f) (wD f 0) (wD f 1) (wD f 2) := by
 intro v y hv
 rw [coeffLift phys_zero] at hv ⊢
 have hd (e :Fin 2 →₀ ℕ) :
     ((lX (f.coeff v)).coeff y).coeff e=Dx (((f.coeff v).coeff y).coeff e) := by
   rw [lX,z9x,aG6,
     ← z9x FX,AlgEquiv.apply_symm_apply]
 have hs : ((lX (f.coeff v)).coeff y).support ⊆
     ((f.coeff v).coeff y).support := by
   intro a ha
   rw [MvPolynomial.mem_support_iff,hd] at ha
   exact MvPolynomial.mem_support_iff.mpr (fun h=>ha (by rw [h,map_zero]))
 have hf : (f.coeff v).coeff y≠0:= by
   intro h
   apply hv
   apply MvPolynomial.ext
   intro a
   rw [hd,h]
   simp
 obtain ⟨hb,hj,hu⟩:=own f v y hf
 exact ⟨hb,hj,(Finset.sup_mono hs).trans hu⟩
private theorem ordinateDiffFits (f :Jet) :
   dM (S4 zst f) (wD f 0-1) (wD f 1) (wD f 2) := by
 intro v y h
 rw [coeffLift derivative_zero,coeff_derivative,← Nat.cast_succ] at h ⊢
 have hf : (f.coeff v).coeff (y+1)≠0:= fun hz=>h (by rw [hz,zero_mul])
 obtain ⟨hb,hj,hu⟩:=own f v (y+1) hf
 change y+1+v≤wD f 0 at hb
 refine ⟨?_,hj,(zhM _ _).trans ?_⟩
 · change y+v≤wD f 0-1
   omega
 · rwa [← map_natCast (znf:FX →+* aZ),ziW,zXY]
private theorem separantFits (f :Jet) :
  dM ((2 :Jet)*f.derivative) (wD f 0-1) (wD f 1-1) (wD f 2) := by
 have hd:dM f.derivative (wD f 0-1) (wD f 1-1) (wD f 2) := by
  intro v y h
  rw [coeff_derivative,← Nat.cast_succ,coeff_mul_natCast] at h ⊢
  have hf : (f.coeff (v+1)).coeff y≠0:= fun hz=>h (by rw [hz,zero_mul])
  obtain ⟨hb,hj,hu⟩:=own f (v+1) y hf
  change y+(v+1)≤wD f 0 at hb
  change v+1≤wD f 1 at hj
  refine ⟨?_,?_,(zhM _ _).trans ?_⟩
  · change y+v≤wD f 0-1
    omega
  · change v≤wD f 1-1
    omega
  · rwa [← map_natCast (znf:FX →+* aZ),ziW,zXY]
 have ht:dM (2 :Jet) 0 0 0:= by
  simpa only [map_ofNat] using scalarFits 2
 simpa only [zbc] using mulFits ht hd
theorem padCaps (f :Jet) (i:Fin 2) (T:TopRow) (B J C U:ℕ)
    (h:SupportCaps B J C U T) :
    dM (pad f i C T) (B+C*(wD f 0-1)) (J+C*(wD f 1-1)) (U+C*wD f 2) := by
  let b:=wD f 0-1
  let j:=wD f 1-1
  let u:=wD f 2
  have hn:dM (-(S4 lX f +
        (z7y:Jet)*S4 zst f)) (b+1) (j+2) u:= by
    apply negFits
    apply addFits
    · exact weaken (physFits f) (by dsimp [b]; omega) (by dsimp [j]; omega) le_rfl
    · exact weaken (mulFits velocityFits (ordinateDiffFits f))
        (by dsimp [b]; omega) (by dsimp [j]; omega) (zbc _).le
  unfold pad
  refine sumFits _ _ ?_
  intro e he
  obtain ⟨hb,hj,hc,hu⟩:=h e (lift_support he)
  have hterm :=mulFits (mulFits (mulFits (mulFits (mulFits
    (scalarFits ((topLift (orient i T)).coeff e)) (powFits (seedFits i) (e 0)))
    (powFits ordinateFits (e 1))) (powFits velocityFits (e 2))) (powFits hn (e 3)))
    (powFits (separantFits f) (C-e 3))
  simp only [Nat.mul_zero,Nat.mul_one,zbc,zXY] at hterm
  have hmul (a :ℕ) :e 3*a+(C-e 3)*a=C*a := by rw [← Nat.add_mul,Nat.add_sub_of_le hc]
  have hB:e 1+e 2+e 3*(b+1)+(C-e 3)*b≤B+C*b:= calc
    _=e 1+e 2+e 3+C*b:= by
      rw [Nat.mul_add,Nat.mul_one,← hmul b]
      ac_rfl
    _≤_:=zlr hb _
  have hJ:e 2+e 3*(j+2)+(C-e 3)*j≤J+C*j:= calc
    _=e 2+2*e 3+C*j:= by
      rw [Nat.mul_add,z5A (e 3) 2,← hmul j]
      ac_rfl
    _≤_:=zlr hj _
  have hU:e 0+e 3*u+(C-e 3)*u≤U+C*u:= by
    rw [Nat.add_assoc,hmul u]
    exact zlr hu _
  exact weaken hterm hB hJ hU
end
end qT3dOZa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qNOhJGb
noncomputable section
open Polynomial MvPolynomial Finset UniqueFactorizationMonoid

open P5_7_1
open qaySLPd
open cu (L FX)
open scoped BigOperators
private abbrev Lifted:=z3y (Fin 4) FX
private theorem lift_injective :zq4 topLift :=
 MvPolynomial.map_injective _ (zxb L[X] FX)
private theorem degree_lift (i:Fin 4) (F:TopRow) :
  (topLift F).degreeOf i=F.degreeOf i:= by
 rw [degreeOf_eq_sup,degreeOf_eq_sup]
 change (zDK (algebraMap L[X] FX) F).support.sup (fun e=>e i)= _
 rw [zra _ (zxb L[X] FX)]
private theorem degree_dvd {R:Type*} [CommRing R] [IsDomain R] (i:Fin 4)
  {F G:z3y (Fin 4) R} (h:F∣G) (hG:G≠0) :
  F.degreeOf i≤G.degreeOf i:= by
 rw [← weightedTotalDegree_piSingle,← weightedTotalDegree_piSingle]
 exact weightedTotalDegree_le_of_dvd _ h hG
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev am5:Submonoid TopRow :=
 (nonZeroDivisors (L[X])).map znf
private theorem lift_factor {F:TopRow} (hF:Irreducible F) (hTop:0<F.degreeOf 3) :
   Irreducible (topLift F) ∧ ∀ G:TopRow,topLift F∣topLift G→F∣G:= by
 let I:Ideal TopRow :=zyf {F}
 have hp:I.IsPrime :=zN9 hF.prime
 have hd:Disjoint (am5:Set TopRow) I:= by
   rw [Set.disjoint_left]
   intro a ha hI
   obtain ⟨b,hb,rfl⟩:=ha
   have hdiv :F∣znf b:=Ideal.mem_span_singleton.mp hI
   have hb' : (znf b:TopRow)≠0 :=
     MvPolynomial.C_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb)
   have hdeg:=degree_dvd 3 hdiv hb'
   rw [degreeOf_C] at hdeg
   omega
 have hmap :I.map (algebraMap TopRow Lifted)=zyf {topLift F} := by
   rw [show I=zyf {F} from rfl,Ideal.map_span,Set.image_singleton]
   rfl
 have hne :topLift F≠0:=(map_ne_zero_iff topLift lift_injective).mpr hF.ne_zero
 have hprime :=IsLocalization.isPrime_of_isPrime_disjoint am5 Lifted I hp hd
 rw [hmap,Ideal.span_singleton_prime hne] at hprime
 refine ⟨hprime.irreducible,fun G hG=>Ideal.mem_span_singleton.mp ?_⟩
 have hback :=IsLocalization.under_map_of_isPrime_disjoint am5 Lifted hp hd
 change G∈I
 rw [← hback,hmap]
 exact Ideal.mem_span_singleton.mpr hG
private def weights (a b c:ℕ) :Fin 4→ℕ := ![0,a,b,c]
private theorem weight_exp (a b c:ℕ) (e :Fin 4 →₀ ℕ) :
  e.weight (weights a b c)=a*e 1+b*e 2+c*e 3:= by
 simp [Finsupp.weight_eq_sum,Fin.sum_univ_four,weights,smul_eq_mul,z5A]
private theorem support_dvd {F G:TopRow} {U:ℕ} (hF:F≠0) (h:G∣F)
  (hcap:SupportCaps 87 27 12 U F) (hseed :G.degreeOf 0=0) :
  SupportCaps 87 27 12 0 G:= by
 have hb:F.weightedTotalDegree (weights 1 1 1)≤87:= by
  apply Finset.sup_le
  intro e he
  simpa only [weight_exp,one_mul] using (hcap e he).1
 have hj:F.weightedTotalDegree (weights 0 1 2)≤27:= by
  apply Finset.sup_le
  intro e he
  simpa only [weight_exp,zero_mul,zero_add,one_mul] using (hcap e he).2.1
 have hc:F.degreeOf (3:Fin 4)≤12 :=
  degreeOf_le_iff.mpr fun e he=>(hcap e he).2.2.1
 intro e he
 have hb' := (le_weightedTotalDegree (weights 1 1 1) he).trans
  ((weightedTotalDegree_le_of_dvd _ h hF).trans hb)
 have hj' := (le_weightedTotalDegree (weights 0 1 2) he).trans
  ((weightedTotalDegree_le_of_dvd _ h hF).trans hj)
 exact ⟨by simpa only [weight_exp,one_mul] using hb',
  by simpa only [weight_exp,zero_mul,zero_add,one_mul] using hj',
  (monomial_le_degreeOf _ he).trans ((degree_dvd _ h hF).trans hc),
  (monomial_le_degreeOf _ he).trans hseed.le⟩
private abbrev flatten:=(MvPolynomial.optionEquivRight L (Fin 4)).symm
private theorem cSJ (F:TopRow) (e :Fin 4 →₀ ℕ) (a :ℕ) :
  (flatten F).coeff (e.optionElim a)=(F.coeff e).coeff a := by
 rw [← MvPolynomial.optionEquivRight_coeff_coeff,AlgEquiv.apply_symm_apply]
end
end qNOhJGb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace qxI9jja
noncomputable section
open Polynomial
open P5 (K p)
open cu (L FX Jet Equation aZ jz)
open bjF (Fixed view)
open P5_7_1 (TopRow topLift topConjugate)
open qaySLPd
open Qv (S4 lX)
open private co3 bNH from ProximityPrize.SubmissionLower.A3
private abbrev Generic:=z3y (Fin 4) FX
private abbrev TopBound (c:ℕ) (T:TopRow) := ∀ e∈T.support,e 3≤ c
private theorem kernel_factor {R E :Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field E] (ψ:R[X] →+* E)
    (hinj:zq4 (ψ.comp Polynomial.C)) {P:R[X]}
    (hP:P≠0) (hz :ψ P=0) :
    ∃ G:R[X],Irreducible G∧0<G.natDegree ∧ ∀ Q,ψ Q=0↔G∣Q:= by
  have hbot:zdq ψ ≠ ⊥ := fun h =>
    hP (Ideal.mem_bot.mp (h ▸ (show P∈zdq ψ from hz)))
  obtain ⟨G,hG,hp⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot (RingHom.ker_isPrime ψ) hbot
  have hGd:G.natDegree≠0:= by
    intro hd
    have h:=eq_C_of_natDegree_eq_zero hd
    have hzero :ψ (C (G.coeff 0))=0:=h ▸ hG
    have hc:G.coeff 0=0:=hinj (hzero.trans (map_zero (ψ.comp C)).symm)
    exact hp.ne_zero (by rw [h,hc,map_zero])
  let F:=FractionRing R
  let φ:R →+* F:=algebraMap R F
  let m:=Polynomial.mapRingHom φ
  let e :=eval₂RingHom (IsFractionRing.lift hinj:F →+* E) (ψ z7y)
  have he :e.comp m=ψ:= by
    apply Polynomial.ringHom_ext
    · intro a
      change e ((C a).map φ)=ψ (C a)
      rw [map_C]
      simpa only [e,coe_eval₂RingHom,eval₂_C,zQb] using
        IsFractionRing.lift_algebraMap (K:=F) hinj a
    · change e ((z7y:R[X]).map φ)=ψ z7y
      simp [e]
  have hcomp (Q:R[X]) :e (m Q)=ψ Q:=zmU he Q
  have hprim:=hp.irreducible.isPrimitive hGd
  have hirr :Irreducible (m G) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K:=F)).mp hp.irreducible
  have hspan:zyf {m G} = zdq e :=
    (PrincipalIdealRing.isMaximal_of_irreducible hirr).eq_of_le (RingHom.ker_ne_top e)
      ((Ideal.span_singleton_le_iff_mem _).mpr (show e (m G)=0 by rwa [hcomp]))
  refine ⟨G,hp.irreducible,Nat.pos_of_ne_zero hGd,fun Q=>⟨?_,?_⟩⟩
  · intro h
    apply hprim.dvd_of_fraction_map_dvd_fraction_map (K:=F)
    apply Ideal.mem_span_singleton.mp
    change m Q∈zyf {m G}
    rw [hspan]
    exact (hcomp Q).trans h
  · rintro ⟨A,rfl⟩
    rw [map_mul,show ψ G=0 from hG,zero_mul]
private abbrev E8:=z3y (Fin 1) FX
private def baseView:z3y (Fin 3) FX ≃+* Fixed :=
 ((zGY FX (zFe (0:Fin 3) 1)).trans
   (z8s FX 2)).toRingEquiv.trans
   (zNc (z8s FX 1).toRingEquiv)
private def YN :Generic ≃+* zM1 Fixed :=
 ((zGY FX (zFe (0:Fin 4) 3)).trans
   (z8s FX 3)).toRingEquiv.trans (zNc baseView)
private theorem topView_C (a :FX) :
  YN (znf a)=C (C (C (znf a))) := by
 simp [YN,baseView,zye]
private theorem topView_X_succ {k :Fin 4} {j:Fin 3}
  (h:zFe (0:Fin 4) 3 k=j.succ) :
  YN (z9v k)=C (baseView (z9v j)) := by
 change ((z8s FX 3 (zHw _ _)).map _)= _
 rw [z6l,h,z07,map_C]
 rfl
private theorem baseView_X_succ {k :Fin 3} {j:Fin 2}
  (h:zFe (0:Fin 3) 1 k=j.succ) :
  baseView (z9v k)=C (z8s FX 1 (z9v j)) := by
 change ((z8s FX 2 (zHw _ _)).map _)= _
 rw [z6l,h,z07,map_C]
 rfl
private theorem topView_X0 :
  YN (z9v 0)=C (C (C (z9v (0:Fin 1) :E8))) := by
 rw [topView_X_succ (k :=0) (j:=2) (by decide),
  baseView_X_succ (k :=2) (j:=1) (by decide),
  show (1 :Fin 2)=(0:Fin 1).succ by decide,MvPolynomial.finSuccEquiv_X_succ]
private theorem topView_X1 :
  YN (z9v 1)=C (C (z7y:zM1 E8)) := by
 rw [topView_X_succ (k :=1) (j:=0) (by decide),
  baseView_X_succ (k :=0) (j:=0) (by decide),
  MvPolynomial.finSuccEquiv_X_zero]
private theorem topView_X2 :
  YN (z9v 2)=C (z7y:Fixed) := by
 rw [topView_X_succ (k :=2) (j:=1) (by decide)]
 simp [baseView,zye]
private theorem topView_X3:YN (z9v 3)=Polynomial.X:= by
 simp [YN,zye]
private theorem top_degree (Q:Generic) : (YN Q).natDegree= Q.degreeOf 3:= by
 change ((z8s FX 3 (zHw
  (zFe (0:Fin 4) 3) Q)).map baseView.toRingHom).natDegree= _
 rw [natDegree_map_eq_of_injective baseView.injective,MvPolynomial.natDegree_finSuccEquiv,
  ← Equiv.swap_apply_right (0:Fin 4) 3]
 exact MvPolynomial.degreeOf_rename_of_injective (zFe (0:Fin 4) 3).injective 3
private abbrev jetSeed (i:Fin 2) :Jet:=C (C (z9v i))
private abbrev jetOrd:Jet:=C (z7y:Equation)
private abbrev jetVel:Jet:=z7y
private def sep (f :Jet) :Jet:=(2 :Jet)*f.derivative
private def num (f :Jet) :Jet :=
 -(S4 lX f+jetVel*S4 derivative f)
private theorem view_C (i:Fin 2) (a :FX) :
  view (omitted i) (algebraMap FX Jet a)=C (C (C (znf a))) := by
 simp [view,zpj,zKm,co3,
  Bivariate.swap_C_C]
private theorem view_seed (i:Fin 2) :
  view (omitted i) (jetSeed i)=C (C (C (z9v (0:Fin 1) :E8))) := by
 fin_cases i <;> simp [view,omitted,bNH,Bivariate.swap_C_C]
private theorem view_ord (i:Fin 2) :
  view (omitted i) jetOrd=C (C (z7y:zM1 E8)) := by
 simp [view,Bivariate.swap_Y,Bivariate.swap_C_C]
private theorem view_vel (i:Fin 2) :
  view (omitted i) jetVel=C (z7y:Fixed) := by
 simp [view,Bivariate.swap_Y]
private def baseEval {E :Type*} [Field E] (π:Jet →+* E) (i:Fin 2) :Fixed →+* E :=
 π.comp ((view (omitted i)).symm.toRingHom.comp Polynomial.C)
private def evalTop {E :Type*} [Field E] (π:Jet →+* E) (f :Jet) (i:Fin 2) :
  Generic →+* E :=
 MvPolynomial.eval₂Hom (π.comp (algebraMap FX Jet))
  ![π (jetSeed i),π jetOrd,π jetVel,π (num f)/π (sep f)]
private theorem evalTop_view {E :Type*} [Field E] (π:Jet →+* E) (f :Jet) (i:Fin 2) :
   (eval₂RingHom (baseEval π i) (π (num f)/π (sep f))).comp YN.toRingHom =
     evalTop π f i:= by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp [topView_C,evalTop,baseEval]
   rw [← view_C i a,RingEquiv.symm_apply_apply]
   simp only [zpj,zKm]
 · intro j
   fin_cases j
   · simp [topView_X0,evalTop,baseEval]
     rw [← view_seed i,RingEquiv.symm_apply_apply]
   · simp [topView_X1,evalTop,baseEval]
     rw [← view_ord i,RingEquiv.symm_apply_apply]
   · simp [topView_X2,evalTop,baseEval]
     rw [← view_vel i,RingEquiv.symm_apply_apply]
   · simp [topView_X3,evalTop]
private theorem oriented_support (T:TopRow) (i:Fin 2) :
   (topLift (orient i T)).support=T.support := by
 have h:=zra (orient i T)
   (zxb L[X] FX)
 change (topLift (orient i T)).support=(orient i T).support at h
 rw [h]
 fin_cases i
 · rfl
 · exact zra T
     (Polynomial.map_injective _ (frobenius L p).injective)
private theorem pad_eval {E :Type*} [Field E] (π:Jet →+* E) (f :Jet) (i:Fin 2)
  (hs :π (sep f)≠0) {T:TopRow} {c:ℕ} (hT:TopBound c T) :
  π (pad f i c T)=π (sep f)^c*evalTop π f i (topLift (orient i T)) := by
 classical
 let Q:=topLift (orient i T)
 change π (∑ e∈Q.support,algebraMap FX Jet (Q.coeff e) *
  jetSeed i^(e 0)*jetOrd^(e 1)*jetVel^(e 2)*num f^(e 3) *
  sep f^(c-e 3))= _
 rw [show topLift (orient i T)= Q from rfl]
 simp only [map_sum,map_mul,map_pow,evalTop,MvPolynomial.coe_eval₂Hom,
  MvPolynomial.eval₂_eq',Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro e he
 have hle :=hT e ((oriented_support T i) ▸ he)
 simp only [Fin.prod_univ_four,zQb]
 let a :=π (algebraMap FX Jet (Q.coeff e))
 let z :=π (jetSeed i)^e 0
 let y :=π jetOrd^e 1
 let v :=π jetVel^e 2
 let n:=π (num f)
 let s :=π (sep f)
 change a*z*y*v*n^e 3*s^(c-e 3) =
  s^c*(a*(z*y*v*(n/s)^e 3))
 have hpow:s^(c-e 3)*s^(e 3)=s^c :=
  by rw [← pow_add,Nat.sub_add_cancel hle]
 have hc:s^(e 3)≠0:=pow_ne_zero _ hs
 rw [div_pow,← hpow]
 field_simp [hc]
private theorem relation_in_field {E :Type*} [Field E] (π:Jet →+* E) {f :Jet} {i:Fin 2}
    (hπ : ∀ A:Jet,π A=0↔f∣A) (htwo: (2 :E)≠0)
    (hsep : ¬ f∣f.derivative) (hdep:0<(view (omitted i) f).natDegree)
    {T:TopRow} (hT:T≠0) {c:ℕ} (hc:TopBound c T) (hp:f∣pad f i c T) :
    ∃ Q:Generic,Irreducible Q∧0<Q.degreeOf 3 ∧
      ∀ {S:TopRow} {c' : ℕ},TopBound c' S →
        (f∣pad f i c' S↔Q∣topLift (orient i S)) := by
  have hs :π (sep f)≠0:= by
    simpa only [sep,map_mul,map_ofNat] using mul_ne_zero htwo (fun h=>hsep ((hπ _).mp h))
  have hpad {S:TopRow} {c' : ℕ} (hS:TopBound c' S) :
      f∣pad f i c' S↔evalTop π f i (topLift (orient i S))=0:= by
    rw [← hπ,pad_eval π f i hs hS,mul_eq_zero]
    exact or_iff_right (pow_ne_zero _ hs)
  have hb:zq4 (baseEval π i) := by
    apply (injective_iff_map_eq_zero (baseEval π i)).mpr
    intro a ha
    let J:=view (omitted i)
    have hh:=(hπ (J.symm (C a))).mp ha
    have hd:=map_dvd J.toRingHom hh
    change J f∣J (J.symm (C a)) at hd
    rw [J.apply_symm_apply] at hd
    by_contra hn
    exact (not_le_of_gt hdep) (by simpa using natDegree_le_of_dvd hd (C_ne_zero.mpr hn))
  let ψ:=eval₂RingHom (baseEval π i) (π (num f)/π (sep f))
  have he (Q:Generic) :ψ (YN Q)=evalTop π f i Q :=
    zmU (evalTop_view π f i) Q
  let P:=YN (topLift (orient i T))
  have hP:P≠0:= by
    intro h0
    have hz : (topLift (orient i T)).support = ∅ :=
      MvPolynomial.support_eq_empty.mpr (YN.injective (h0.trans YN.map_zero.symm))
    exact hT (MvPolynomial.support_eq_empty.mp ((oriented_support T i).symm.trans hz))
  let:UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid Fixed :=
    baseView.toMulEquiv.uniqueFactorizationMonoid (zhK (Fin 3))
  obtain ⟨G,hg,hd,hG⟩:=kernel_factor ψ (by simpa [ψ,eval₂RingHom_comp_C] using hb)
    hP ((he _).trans ((hpad hc).mp hp))
  let Q:=YN.symm G
  refine ⟨Q,hg.map YN.symm,?_,?_⟩
  · rwa [← top_degree,show YN Q=G from YN.apply_symm_apply G]
  · intro S cs hS
    rw [hpad hS,← he,hG,← YN.apply_symm_apply G]
    exact map_dvd_iff YN
private theorem top_relation {f :Jet} {i:Fin 2} (hf :Irreducible f)
    (hsep : ¬ f∣f.derivative) (hdep:0<(view (omitted i) f).natDegree)
    {T:TopRow} (hT:T≠0) {c:ℕ} (hc:TopBound c T) (hp:f∣pad f i c T) :
    ∃ Q:Generic,Irreducible Q∧0<Q.degreeOf 3 ∧
      ∀ {S:TopRow} {c' : ℕ},TopBound c' S →
        (f∣pad f i c' S↔Q∣topLift (orient i S)) := by
  let:UniqueFactorizationMonoid FX:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid aZ:=zhK (Fin 2)
  let:UniqueFactorizationMonoid Equation :=zV6 (D:=aZ)
  let:UniqueFactorizationMonoid Jet:=zV6 (D:=Equation)
  let I:Ideal Jet:=zyf {f}
  let:I.IsPrime :=zN9
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  let E :=FractionRing (Jet ⧸ I)
  let π:Jet →+* E :=(algebraMap (Jet ⧸ I) E).comp (zVv I)
  have hπ (A:Jet) :π A=0↔f∣A:= by
    change algebraMap (Jet ⧸ I) E (zVv I A)=0↔_
    rw [(zxb (Jet ⧸ I) E).eq_iff' (map_zero _),
      Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let:CharP E p:=charP_of_injective_ringHom (π.comp (algebraMap FX Jet)).injective p
  have htwo: (2 :E)≠0:= fun h =>
    (by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff E p 2).mp h)
  exact relation_in_field π hπ htwo hsep hdep hT hc hp
private def σP:L[X] ≃+* L[X] :=zNc (frobeniusEquiv L p)
private def σF:FX ≃+* FX:=IsFractionRing.ringEquivOfRingEquiv σP
private def conjugate :Generic ≃+* Generic:=MvPolynomial.mapEquiv (Fin 4) σF
private theorem lift_conjugate (T:TopRow) :
  topLift (topConjugate T)=conjugate (topLift T) := by
 let incl:=algebraMap L[X] FX
 change zDK incl (zDK σP.toRingHom T) =
  zDK σF.toRingHom (zDK incl T)
 have he :incl.comp σP.toRingHom=σF.toRingHom.comp incl :=
  RingHom.ext fun a=>(IsFractionRing.ringEquivOfRingEquiv_algebraMap σP a).symm
 rw [z6Y,z6Y,he]
private theorem conjugate_degree (Q:Generic) (j:Fin 4) :
  (conjugate.symm Q).degreeOf j= Q.degreeOf j:= by
 rw [zXi,zXi]
 exact congrArg (fun s=>s.sup fun e=>e j)
  (zra Q σF.symm.injective)
end
end qxI9jja
end
section
set_option backward.isDefEq.respectTransparency false
namespace qh06gse
noncomputable section
open Polynomial
open cu (aZ)
open qaySLPd (pe)
open private alV b2f d3R baseChange from ProximityPrize.SubmissionLower.G
def lift:pe[X] →+* aZ:=baseChange.comp alV.toRingHom
theorem bIr (q:pe) :lift (C q)=uk.wZ q:= by
 change baseChange (alV (C q))= _
 rw [b2f]
 exact z6Y _ _ _
theorem cXC:lift (z7y:pe[X])=znf uk.center := by
 change baseChange (alV z7y)= _
 rw [d3R]
 exact MvPolynomial.map_C _ _
end
end qh06gse
end
