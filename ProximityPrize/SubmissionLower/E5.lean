import ProximityPrize.SubmissionLower.CF
set_option Elab.async false
open _root_ renaming Finsupp.weight_apply → zDM, Function.iterate_succ_apply → zWS, Function.iterate_succ_apply' → zLk, MvPolynomial.C → znf, MvPolynomial.map → zDK, MvPolynomial.mem_support_iff → zuk, MvPolynomial.weightedTotalDegree → zXg, Nat.mul_le_mul_left → zBI
set_option autoImplicit true
section
namespace aKM
noncomputable section
open aR jA MvPolynomial UniqueFactorizationMonoid
private abbrev Exponent:=Fin 3 →₀ ℕ
private abbrev avc (i:Fin 3) (a :ℕ) (P:Lower) :Lower :=
 (pderiv (R:=iP) i)^[a] P
private theorem natCast_ne_zero {n:ℕ} (hpos :0<n) (hn:n<K1.p) :
  (n:iP)≠0:= by
 let _:CharP iP K1.p :=
  charP_of_injective_ringHom (DI.comp embed).injective K1.p
 intro hz
 exact (not_le_of_gt hn) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff _ _ _).mp hz))
private theorem apx (i:Fin 3) (a :ℕ) (P:Lower)
   {m:Exponent} (hm:m∈(avc i a P).support) :
   m+Finsupp.single i a∈P.support := by
 induction a generalizing m with
 | zero=>simpa [avc] using hm
 | succ a ih =>
   have hs :m+Finsupp.single i 1∈(avc i a P).support := by
     rw [zuk] at hm ⊢
     intro hz
     apply hm
     change ((pderiv (R:=iP) i)^[a + 1] P).coeff m=0
     rw [zLk,coeff_pderiv,hz,zero_mul]
   simpa only [add_assoc,← Finsupp.single_add,Nat.add_comm 1 a] using ih hs
private theorem gDL (i:Fin 3) (P:Lower) (y :Fin 3→iP) :
   translate y (pderiv i P)=pderiv i (translate y P) := by
 classical
 induction P using MvPolynomial.induction_on with
 | C c=>simp [jA.translate]
 | add P Q hP hQ=>simp [map_add,hP,hQ]
 | mul_X P j hP =>
   rw [pderiv_mul,map_add,map_mul,map_mul,hP,map_mul,pderiv_mul]
   by_cases hj:j=i
   · subst j
     simp [jA.translate,map_add]
   · simp [jA.translate,map_add,pderiv_X_of_ne hj]
private theorem dhV (i:Fin 3) (P:Lower) (y :Fin 3→iP) (a :ℕ) :
   translate y (avc i a P)=avc i a (translate y P) := by
 induction a with
 | zero=>rfl
 | succ a ih =>
   simp only [avc,zLk] at ih ⊢
   rw [gDL,ih]
private theorem cNr (i:Fin 3) {f :Lower} (hf :Prime f)
   (hsep : ¬ f∣pderiv i f) (a :ℕ) (ha :a<K1.p) {U:Lower} (hU : ¬ f∣U) :
   ¬ f∣avc i a (f^a*U) := by
 induction a generalizing U with
 | zero=>simpa [avc] using hU
 | succ a ih =>
   let V:=((a+1 :ℕ) :Lower)*(pderiv i f*U)+f*pderiv i U
   have hstep:pderiv i (f^(a+1)*U)=f^a*V:= by
     rw [pderiv_mul,pderiv_pow,Nat.add_sub_cancel,pow_succ f a]
     dsimp only [V]
     ring
   have hu:IsUnit ((a+1 :ℕ) :Lower) := by
     rw [← map_natCast (C:iP →+* Lower)]
     exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero (Nat.succ_pos a) ha)).map C
   have hV : ¬ f∣V:= by
     intro hd
     have h:=(dvd_add_left (dvd_mul_right f (pderiv i U))).mp hd
     exact (hf.dvd_or_dvd (hu.dvd_mul_left.mp h)).elim hsep hU
   change ¬ f∣(pderiv (R:=iP) i)^[a + 1] (f^(a+1)*U)
   rw [zWS,hstep]
   exact ih (Nat.lt_of_succ_lt ha) hV
private theorem bFB {f :Lower} (hf :Prime f) (hb:f.totalDegree<K1.p) :
   ∃ i:Fin 3,¬ f∣pderiv i f := by
 have hv :f.vars.Nonempty := by
   by_contra! he
   have heq :=vars_eq_empty_iff_eq_C.mp he
   have hn:f.coeff 0≠0:= by
     intro hz
     exact hf.ne_zero (by rw [heq,hz,map_zero])
   exact hf.not_isUnit (heq ▸ (isUnit_iff_ne_zero.mpr hn).map C)
 obtain ⟨i,hi⟩:=hv
 have hpos :=Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
 have hc:=natCast_ne_zero hpos ((degreeOf_le_totalDegree f i).trans_lt hb)
 have hn:=pderiv_ne_zero_of_natCast_ne_zero i f hc
 have hdeg:=degreeOf_pderiv_le_sub_one i f
 refine ⟨i,?_⟩
 rintro ⟨g,hg⟩
 have hg0:g≠0:= by
   intro h
   exact hn (by rw [hg,h,mul_zero])
 rw [hg,degreeOf_mul_eq hf.ne_zero hg0] at hdeg
 omega
private theorem b6f (m:Exponent) :
  Finsupp.weight (R:=ℕ) (Fin.val :Fin 3→ℕ) m=m.sum (fun i e=>i.val*e) := by
 simp only [zDM,smul_eq_mul,Nat.mul_comm]
end
end aKM
end
section
namespace aKM
noncomputable section
open aR wH axh Polynomial
open jA (qV H9)
private theorem bCl {Q:af 3} {R:jA.Lower} {b j:ℕ}
  (hs :Q.support=R.support) (hb:R.totalDegree≤b) (hj:H9 R≤j) :
  Gh Q b j:= by
 simpa only [Gh,MvPolynomial.totalDegree,qE,H9,hs] using And.intro hb hj
private theorem bJE {Q:af 3} {R:jA.Lower}
  (hs :Q.support=R.support) (hR:R≠0) :Q≠0 :=
 MvPolynomial.support_nonempty.mp (hs ▸ MvPolynomial.support_nonempty.mpr hR)
private theorem arA (P:af 3) :
  qE P=zXg Fin.val P:= by
 unfold qE zXg
 simp only [zDM,smul_eq_mul,Nat.mul_comm]
private theorem bCk {P Q:af 3} {b₁ j₁ b₂ j₂:ℕ} (hP:P≠0) (hQ:Q≠0)
  (hp:Gh P b₁ j₁) (hq:Gh Q b₂ j₂) :
  Gh (P*Q) (b₁+b₂) (j₁+j₂) := by
 refine ⟨(MvPolynomial.totalDegree_mul P Q).trans (Nat.add_le_add hp.1 hq.1),?_⟩
 rw [arA,MvPolynomial.weightedTotalDegree_mul _ _ _ hP hQ,
  ← arA,← arA]
 exact Nat.add_le_add hp.2 hq.2
private theorem c5L {P Q:jA.Lower} {P' Q' : af 3} {dP dQ:ao[X]}
   (hP:P≠0) (hQ:Q≠0) (hrel :IsRelPrime P Q)
   (hdP:dP≠0) (hdQ:dQ≠0)
   (hmP:zDK qV P' = znf (qV dP)*P)
   (hmQ:zDK qV Q' = znf (qV dQ)*Q) :
   IsRelPrime (fW P') (fW Q') := by
 let i:=algebraMap iP cH
 have hu (x :ao[X]) (hx :x≠0) :IsUnit (znf (σ:=Fin 3) (i (qV x))) :=
   (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff i i.injective).mpr
     ((map_ne_zero_iff qV al5).mpr hx))).map znf
 have hg (A:af 3) (B:jA.Lower) (d:ao[X])
     (h:zDK qV A=znf (qV d)*B) :
     fW A=znf (i (qV d))*zDK i B:= by
   unfold fW
   change zDK (i.comp qV) A= _
   rw [← MvPolynomial.map_map,h,map_mul,MvPolynomial.map_C]
 rw [hg P' P dP hmP,hg Q' Q dQ hmQ,
   isRelPrime_mul_unit_left_left (hu dP hdP),isRelPrime_mul_unit_left_right (hu dQ hdQ)]
 exact fVP P Q hP hQ hrel
end
end aKM
end
section
namespace dn3
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH lB
private def bD7 (p:Shape) :Shape :=⟨p.b - 1,p.j-3,p.t - 1⟩
private theorem cKw (f :af 4) {j:ℕ} (hj:0<j) :
  aO (shape ((separant^[j]) f)) (bD7 (shape f).iU) := by
 obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
 rw [zWS]
 have h:=a3t (separant f) k
 have hb: (shape (separant f)).b≤(shape f).b - 1 := by
  have hd:=weightedTotalDegree_pderiv_le_sub (1 :Fin 4→ℕ) 3 f
  simpa only [shape,weightedTotalDegree_one,Pi.one_apply,separant] using hd
 have hi: (shape (separant f)).j≤(shape f).j-3:= by
  have hd:=weightedTotalDegree_pderiv_le_sub (fun i:Fin 4=>i.val) 3 f
  have hthree : (3:Fin 4).val=3:=rfl
  simpa only [shape,C6,separant,hthree] using hd
 have ht: (shape (separant f)).t≤(shape f).t - 1 := by
  simpa only [Function.iterate_one] using bD9 f 1
 exact ⟨h.1.trans (hb.trans (Nat.sub_le_sub_right (le_max_left _ _) 1)),
  h.2.1.trans hi,h.2.2.trans ht⟩
end
end dn3
end
section
namespace aKM
noncomputable section
open Polynomial aR wH K1_13_7_4
open scoped BigOperators
private theorem bsc:K1_13_7_4.c2 :=
 aqa.of_children bzL.proof aRV.proof
private theorem bOE {A:Type*} [CommSemiring A]
  (F:MvPolynomial (Fin 3) A) (a :A) :
  (znf a*F).support⊆F.support := by
 intro m hm
 simp only [zuk,MvPolynomial.coeff_C_mul] at hm ⊢
 exact right_ne_zero_of_mul hm
private theorem b5O (a :Fin 3 →₀ ℕ) {F:af 3} {b j:ℕ}
   (hF:Gh F b j) :Gh (BV a F) b j:= by
 classical
 have hs {m:Fin 3 →₀ ℕ} (hm:m∈(BV a F).support) :
     ∃ v∈F.support,m=v-a := by
   by_contra! h
   apply (MvPolynomial.mem_support_iff.mp hm)
   unfold BV
   rw [MvPolynomial.coeff_sum]
   apply Finset.sum_eq_zero
   intro v hv
   simp [MvPolynomial.coeff_monomial,Ne.symm (h v hv)]
 have hweight (w:Fin 3→ℕ) {m:Fin 3 →₀ ℕ}
     (hm:m∈(BV a F).support) :
     ∃ v∈F.support,m.sum (fun i k=>w i*k)≤v.sum (fun i k=>w i*k) := by
   obtain ⟨v,hv,rfl⟩:=hs hm
   refine ⟨v,hv,?_⟩
   simp only [Finsupp.sum_fintype _ _ (fun _=>Nat.mul_zero _)]
   exact Finset.sum_le_sum fun i _=>zBI _ (Nat.sub_le _ _)
 constructor
 · apply Finset.sup_le
   intro m hm
   obtain ⟨v,hv,h⟩:=hweight (fun _=>1) hm
   exact (by simpa only [one_mul,EY] using h:EY m≤EY v).trans
     ((Finset.le_sup (f :=EY) hv).trans hF.1)
 · apply Finset.sup_le
   intro m hm
   obtain ⟨v,hv,h⟩:=hweight Fin.val hm
   exact h.trans ((Finset.le_sup (f := fun m=>m.sum (fun i k=>i.val*k)) hv).trans hF.2)
end
end aKM
end
section
namespace aKM
noncomputable section
open aR wH K1_13_7_6 MvPolynomial
private theorem cVG:K1_13_7_6.c2 :=
 aKv.of_children bzQ.proof aRX.proof
private theorem cDl (n b j w:ℕ) (hj:j≤b) (hw:0<w)
  (h: (n:ℚ)*(w:ℚ)≤6*(j:ℚ)^2*((b:ℚ)-(j:ℚ))) :
  n≤ ceilDiv (3*(2*j)^2*(2*b - 2*j)) (4*w) := by
 have hNat :n*w≤6*j^2*(b - j) := by
  exact_mod_cast (by simpa only [Nat.cast_sub hj] using h :
    (n:ℚ)*(w:ℚ)≤6*(j:ℚ)^2*(↑(b - j) :ℚ))
 have hsub:2*b - 2*j=2*(b - j) := by omega
 have hmul :n*(4*w)≤3*(2*j)^2*(2*b - 2*j) := by
  rw [hsub]
  calc
    n*(4*w)=4*(n*w) := by ring
    _≤4*(6*j^2*(b - j)) :=zBI _ hNat
    _ = _:= by ring
 unfold ceilDiv
 have hleft:=(Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) hw)).mpr hmul
 have hpad:3*(2*j)^2*(2*b - 2*j)≤3*(2*j)^2*(2*b - 2*j)+4*w - 1 := by
  omega
 exact hleft.trans (Nat.div_le_div_right hpad)
end
end aKM
end
section
namespace bAq
noncomputable section
open aR dN wH lB agP
open Rl (acp He)
open Ex (C6)
open MvPolynomial
open private bKl from ProximityPrize.SubmissionLower.J
private theorem a4g {q:af 3} {b j:ℕ} (hq:Gh q b j) (hb:1≤b)
    (hj:2≤j) :
    aO (shape (acp q)) ⟨b,j+1,1⟩:= by
  have azs (w:Fin 4→ℕ) :
      (He q).weightedTotalDegree w=q.weightedTotalDegree (w ∘ Fin.castSucc) :=
    weightedTotalDegree_rename_of_injective (Fin.castSucc_injective 3)
  refine ⟨?_,?_,?_⟩
  · have h:=bKl 1 b 0 (by simp) (fun _=>hb) (He q) (by
      simpa only [azs,show (1 :Fin 4→ℕ) ∘ Fin.castSucc=1 from rfl,
        weightedTotalDegree_one] using hq.1)
    simpa only [shape,acp,weightedTotalDegree_one,Nat.add_zero] using h
  · have h:=bKl Fin.val j 1 (fun i=> by simp [Fin.val_succ])
      (fun i=>(Nat.le_of_lt_succ i.isLt:i.val≤2).trans hj) (He q) (by
        simpa only [azs,show (Fin.val :Fin 4→ℕ) ∘ Fin.castSucc=Fin.val from rfl,
          ← C6] using hq.2)
    simpa only [shape,acp,← C6] using h
  · let w:Fin 4→ℕ:=Pi.single 3 1
    have h:=bKl w 0 1 (fun i=> by fin_cases i <;> decide)
      (fun i=> by fin_cases i <;> decide) (He q) (by
        simp [w,weightedTotalDegree_piSingle,bZ5])
    simpa [shape,acp,w,weightedTotalDegree_piSingle] using h
end
end bAq
end
