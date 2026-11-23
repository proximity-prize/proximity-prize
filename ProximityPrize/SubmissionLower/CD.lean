import ProximityPrize.SubmissionLower.E
import ProximityPrize.SubmissionLower.CT
set_option Elab.async false
open _root_ renaming Fin.castSucc → z1o, Finset.sum_insert → z5O, Finsupp.weight_eq_sum → z1K, MvPolynomial.map → zDK, MvPolynomial.mem_support_iff → zuk, Nat.add_zero → zXY, Nat.cast_add → z6H, Nat.cast_mul → z2R, Nat.cast_ofNat → zWE, Nat.cast_sub → zjK, Nat.eq_zero_of_le_zero → za7, Nat.mul_le_mul_left → zBI, Nat.pos_of_ne_zero → zOl, Nat.sub_add_cancel → zxt, Nat.sub_le_sub_right → zIu
set_option autoImplicit true
section
namespace bSd
noncomputable section
open aR jA MvPolynomial
open scoped Polynomial BigOperators
open anj (afo)
open private al5 lX ajn afx
 ZW b1V aUp bZ4 a3y
 bwf a6u from ProximityPrize.SubmissionLower.CS
private theorem bwK (n:ℕ) (hpos :0<n) (hsmall:n≤19) :
  (n:iP)≠0:= by
 let:CharP iP K1.p:=charP_of_injective_ringHom (DI.comp embed).injective K1.p
 intro hz
 have hlarge :19<K1.p:= by decide
 exact (not_le_of_gt (hsmall.trans_lt hlarge))
  (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff iP K1.p n).mp hz))
private theorem btv {f g:ko} (i k :mA) (a :iP)
  (hi:0<f.degreeOf i) (hsmall:f.degreeOf i≤19) (hk :f.degreeOf k=0)
  (ha :a≠0) (hg:pderiv k g=C a*pderiv i f) : ¬ f∣g:= by
 have hpartial:pderiv i f≠0 :=
  pderiv_ne_zero_of_natCast_ne_zero i f (bwK _ hi hsmall)
 have hnonzero :C a*pderiv i f≠0:=mul_ne_zero (C_ne_zero.mpr ha) hpartial
 have hdegree : (C a*pderiv i f).degreeOf i≤f.degreeOf i - 1 :=
  (degreeOf_C_mul_le _ _ _).trans (degreeOf_pderiv_le_sub_one i f)
 rintro ⟨q,hq⟩
 rw [hq,pderiv_mul,pderiv_eq_zero_of_degreeOf_eq_zero hk,zero_mul,zero_add] at hg
 have hq' : pderiv k q≠0:= by
  intro hz
  exact hnonzero (by rw [← hg,hz,mul_zero])
 rw [← hg,degreeOf_mul_eq (ne_zero_of_degreeOf_ne_zero hi.ne') hq'] at hdegree
 omega
private theorem b1a {f r :ko} (hf :Irreducible f)
    (hb:0<vC f) (ht:vC f≤19) (htop:f.degreeOf (some 2)=0)
    (hr :r.support⊆f.support) (a :iP) (ha :a≠0) :
    IsRelPrime f (afx r (C a*f)) := by
  have hd (i:mA) : (C a*f).degreeOf i=f.degreeOf i:= by
    rw [degreeOf_mul_eq (C_ne_zero.mpr ha) hf.ne_zero,degreeOf_C,zero_add]
  have hsmall (i:Fin 3) :f.degreeOf (some i)≤19 :=
    (degreeOf_le_weightedTotalDegree (fun j:mA=>j.elim 0 (fun _=>1))
      (some i) (show 0<(1 :ℕ) by decide) f).trans ht
  have hzero (i:mA) (hi:f.degreeOf i=0) :pderiv i r=0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero (za7
      ((bZ4 hr i).trans_eq hi))
  have htop' : (C a*f).degreeOf (some 2)=0:=(hd _).trans htop
  apply hf.isRelPrime_iff_not_dvd.mpr
  by_cases h₁:f.degreeOf (some 1)=0
  · have h₀:0<f.degreeOf (some 0) := by
      by_contra! h₀
      have hz :vC f≤0:= by
        apply Finset.sup_le
        intro m hm
        have hm₀:=(le_degreeOf_of_mem_support (some 0) hm).trans h₀
        have hm₁:=(le_degreeOf_of_mem_support (some 1) hm).trans_eq h₁
        have hm₂:=(le_degreeOf_of_mem_support (some 2) hm).trans_eq htop
        rw [z1K,Fintype.sum_option,Fin.sum_univ_three]
        simp [za7 hm₀,za7 hm₁,za7 hm₂]
      omega
    have h₁' : (C a*f).degreeOf (some 1)=0:=(hd _).trans h₁
    refine btv (some 0) (some 1) a h₀ (hsmall 0) h₁ ha ?_
    unfold afx
    rw [pderiv_eq_zero_of_degreeOf_eq_zero h₁']
    simp only [mul_zero,add_zero,map_add,hzero _ h₁,zero_add,a6u h₁',
      pderiv_X_self,one_mul]
    rw [pderiv_C_mul]
  · refine btv (some 1) (some 2) ((2 :iP)*a) (zOl h₁)
      (hsmall 1) htop (mul_ne_zero (bwK 2 (by decide) (by decide)) ha) ?_
    unfold afx
    rw [map_add,map_add,hzero _ htop,a6u (i:=some 0) (j:=some 1) htop',
      pderiv_X_of_ne (by decide : (some 1 :mA)≠some 2),zero_mul,add_zero,
      pderiv_C_mul,a6u htop',pderiv_X_self,one_mul,pderiv_C_mul]
    simp only [zero_add,map_mul,mul_assoc]
theorem b9v (f :ko) (hf :Irreducible f)
    (hb:0<vC f) (ht:vC f≤19) (htop:f.degreeOf (some 2)=0) :
    ∃ g:ko,IsRelPrime f g∧gY g≤gY f ∧
      vC g≤vC f∧lP g≤lP f+1 ∧
      ∀ (z :ao) (S:ao[X]),
        eval (ED (DI z) (jW S)) f=0 →
        eval (ED (DI z) (jW S)) g=0:= by
  obtain ⟨d,P,hd,hs,hP⟩:=afo f
  let r :=zDK qV (lX P)
  let A:=zDK qV P
  have hA:A.support=f.support :=(support_map_of_injective P al5).trans hs
  have hr :r.support⊆f.support := by
    intro m hm
    rw [← hs,zuk]
    rw [zuk,coeff_map,ajn] at hm
    intro hz
    exact hm (by rw [hz,map_zero,map_zero])
  have htopP:P.degreeOf (some 2)=0:= by rwa [degreeOf_eq_sup,hs,← degreeOf_eq_sup]
  have ha :qV d≠0:=(map_ne_zero_iff qV al5).mpr hd
  refine ⟨afx r A,?_,?_,?_,?_,?_⟩
  · rw [show A=C (qV d)*f from hP]
    exact b1a hf hb ht htop hr _ ha
  · rw [← bwf,← bwf]
    simpa [weightedTotalDegree,hA] using
      a3y (Pi.single none 1) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [vC,weightedTotalDegree,hA] using
      a3y (fun i=>i.elim 0 (fun _=>1)) r A 0 (hA.symm ▸ hr) (by decide) (by decide)
  · simpa [lP,weightedTotalDegree,hA] using
      a3y (fun i=>i.elim 0 Fin.val) r A 1 (hA.symm ▸ hr) (by decide) (by decide)
  · intro z S hz
    have hzP:eval (ZW z S) P=0:= by
      apply al5
      rw [map_zero,← aUp,hP,map_mul,hz,mul_zero]
    have hmap :afx r A=zDK qV (afx (lX P) P) := by
      simp only [afx,A,r,map_add,map_mul,map_X,pderiv_map,map_ofNat]
    rw [hmap,aUp,b1V P z S htopP,hzP,map_zero,map_zero]
end
end bSd
end
section
namespace bAl
noncomputable section
open K1 aR jA
open scoped Polynomial BigOperators
theorem bxL (F:jK) :gY (bC F)=gY F:= by
 have hs : (bC F).support=F.support :=
  MvPolynomial.support_map_of_injective F (IsFractionRing.injective ao[X] iP)
 simp only [gY,MvPolynomial.degreeOf_eq_sup,hs]
end
end bAl
end
section
namespace aSj
noncomputable section


open aR (Shape)

open scoped BigOperators Polynomial
def tC (p:Shape) :Shape :=
 ⟨p.b,p.j+1,min (p.t+1) ((p.j+1)/2)⟩
end
end aSj
end
section
namespace aSj
noncomputable section
open aeA
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open private beA from ProximityPrize.SubmissionLower.A3
private theorem bAW {ι:Type*} (T:Finset ι) (b c d:ι→ℕ) (B a bound:ℕ)
    (hb : ∑ i∈T,b i≤B) (hc : ∑ i∈T,c i≤bound) (hB:a*bound≤B)
    (hbase : ∀ i∈T,a*c i≤b i)
    (hzero : ∀ i∈T,c i=0→d i≤b i)
    (hpos : ∀ i∈T,0<c i→d i+a*(c i)^2≤(2*c i - 1)*b i) :
    ∑ i∈T,d i≤ max B ((2*bound - 1)*B-a*bound^2) := by
  let C := ∑ i∈T,c i
  have hci (i:ι) (hi:i∈T) :c i≤C:=Finset.single_le_sum (fun j _=>Nat.zero_le (c j)) hi
  by_cases hC:C=0
  · have h:=(Finset.sum_le_sum fun i hi=>hzero i hi (by have :=hci i hi; omega)).trans hb
    exact h.trans (le_max_left _ _)
  have hCpos :=zOl hC
  have hterm (i:ι) (hi:i∈T) :d i+a*(C*c i)≤(2*C - 1)*b i:= by
    by_cases hi₀:c i=0
    · rw [hi₀,Nat.mul_zero,Nat.mul_zero,zXY]
      exact (hzero i hi hi₀).trans (by
        simpa using Nat.mul_le_mul_right (b i) (show 1≤2*C - 1 by omega))
    · have h:=beA (zOl hi₀) (hci i hi)
        ((hbase i hi).trans (by omega :b i≤2*b i)) (hpos i hi (zOl hi₀))
      have he :C=c i+(C - c i) := by have :=hci i hi; omega
      have hweight:a*(C*c i)=a*(c i)^2+a*((C - c i)*c i) := by
        calc
          _=a*((c i+(C - c i))*c i) :=congrArg (fun n=>a*(n*c i)) he
          _ = _:= by ring
      rw [hweight,← Nat.add_assoc]
      exact h
  have hs : (∑ i∈T,(d i+a*(C*c i)))≤(2*C - 1)*B :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact zBI _ hb)
  have hjoint: (∑ i∈T,d i)+a*C ^2≤(2*C - 1)*B:= by
    simp only [Finset.sum_add_distrib,← Nat.mul_assoc,← Finset.mul_sum] at hs
    change (∑ i∈T,d i)+(a*C)*C≤_ at hs
    rwa [Nat.mul_assoc,← pow_two] at hs
  have ha :a*(bound+C)≤2*B:= by
    calc
      _≤a*(bound+bound) :=zBI _ (Nat.add_le_add_left hc bound)
      _=2*(a*bound) := by ring
      _≤_:=zBI 2 hB
  have hfinal:=beA hCpos hc ha hjoint
  have he :bound=C+(bound - C) := by omega
  have hsq:a*C ^2+a*((bound - C)*(bound+C))=a*bound^2 := by
    calc
      _=a*C ^2+a*((bound - C)*((C+(bound - C))+C)) := by
        exact congrArg (fun n=>a*C ^2+a*((bound - C)*(n+C))) he
      _=a*(C+(bound - C))^2 := by ring
      _ = _:= by rw [← he]
  exact (Nat.le_sub_of_add_le (by simpa only [Nat.add_assoc,hsq] using hfinal)).trans
    (le_max_right _ _)
end
end aSj
end
section
namespace aSj
noncomputable section
open aR (ao af cK embed jet)
open oR (qg)
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open private Mt Ka aUW bqd aYc
 aDh aUV QI from ProximityPrize.SubmissionLower.AH
set_option maxHeartbeats 600000 in
private theorem bpk {H :ℕ} (hH :2≤H) (hchar :H<K1.p)
    (f :af 2) (hf :Irreducible f) (hb:f.totalDegree≤H) :
    QI f≠0∧(QI f).natDegree≤f.totalDegree*(H - 1) ∧
      ∀ S:ao[X],cK f S=0→(QI f).eval S=0 ∨
        (0<f.degreeOf 1∧qg 1 f S) := by
  let A:=Mt f
  let c:=A.natDegree
  let b:=f.totalDegree
  have hcb:c≤b:= by
    change (Mt f).natDegree≤f.totalDegree
    exact (aUW f).le.trans (f.degreeOf_le_totalDegree 1)
  have hAb:A≠0:=(map_ne_zero_iff _ Mt.injective).mpr hf.ne_zero
  by_cases hc:0<c
  · let R:=A.resultant A.derivative c (c - 1)
    have hform :QI f=Ka R:=ite_eq_left hc
    have hcast: (c:af 1)≠0:= by
      have :CharP ao K1.p:=charP_of_injective_ringHom embed.injective K1.p
      have :CharP ao[X] K1.p :=
        charP_of_injective_ringHom (Polynomial.C_injective (R:=ao)) K1.p
      have :CharP (af 1) K1.p :=
        charP_of_injective_ringHom (MvPolynomial.C_injective (σ:=Fin 1) (R:=ao[X])) K1.p
      intro h
      have hp:K1.p∣c:=(CharP.cast_eq_zero_iff (af 1) K1.p c).mp h
      exact (not_le_of_gt (hcb.trans_lt (hb.trans_lt hchar)))
        (Nat.le_of_dvd hc hp)
    have hder :A.derivative≠0:= by
      intro h
      have hz :=congrArg (fun P: (af 1)[X]=>P.coeff (c - 1)) h
      rw [Polynomial.coeff_derivative,zxt hc,Polynomial.coeff_zero] at hz
      have hnat : (((c - 1 :ℕ) :af 1)+1)=(c:af 1) := calc
        _=((c - 1+1 :ℕ) :af 1) := by rw [z6H,Nat.cast_one]
        _ = _:=congrArg (fun k :ℕ=>(k :af 1)) (zxt hc)
      rw [hnat] at hz
      change A.leadingCoeff*(c:af 1)=0 at hz
      exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hAb) hcast) hz
    have hR:R≠0 :=
      Polynomial.resultant_derivative_ne_zero_of_irreducible A (hf.map Mt) hder
    have hdeg: (Ka R).natDegree+c^2≤(2*c - 1)*b:= by
      let B:=A.map Ka.toRingHom
      have h:=Polynomial.natDegree_resultant_derivative_padded_add_sq_le B c b (by
        intro k hk
        rw [Polynomial.coeff_map]
        exact aUV f k (hk.trans hcb))
      dsimp only [B] at h
      rw [Polynomial.derivative_map,Polynomial.resultant_map_map] at h
      exact h
    have hbudget: (Ka R).natDegree≤b*(b - 1) := by
      have hbpos :1≤b:=hc.trans_le hcb
      have hcpos :1≤2*c:= by omega
      zify [hbpos,hcpos] at hdeg ⊢
      nlinarith [sq_nonneg ((b:ℤ)-(c:ℤ))]
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ Ka.injective).mpr hR,?_,?_⟩
    · rw [hform]
      exact hbudget.trans (zBI b (zIu hb 1))
    · intro S hS
      by_cases hS' : cK (pderiv 1 f) S=0
      · left
        rw [hform,aYc]
        exact Polynomial.map_resultant_eq_zero_of_common_root (MvPolynomial.eval (jet S))
          A A.derivative le_rfl (Polynomial.natDegree_derivative_le A) (Or.inl hc.ne')
          (jet S (1 :Fin 2)) ((aDh f S).trans hS) (by
            rw [show A.derivative=Mt (pderiv 1 f) from (bqd f).symm]
            exact (aDh _ S).trans hS')
      · exact Or.inr ⟨(aUW f) ▸ hc,hS,hS'⟩
  · have hform :QI f=Ka (A.coeff 0) :=ite_eq_right hc
    have hAc:A=Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (Nat.eq_zero_of_not_pos hc).le
    have hA0:A.coeff 0≠0:= fun h=>hAb (by simpa [h] using hAc)
    refine ⟨by rw [hform]; exact (map_ne_zero_iff _ Ka.injective).mpr hA0,?_,?_⟩
    · rw [hform]
      have h:=aUV f 0 (Nat.zero_le _)
      exact (by simpa using h: (Ka (A.coeff 0)).natDegree≤b).trans
        (by simpa using Nat.mul_le_mul_left b (by omega :1≤H - 1))
    · intro S hS
      left
      have h:=(aDh f S).trans hS
      change (A.map _).eval _=0 at h
      conv at h=>lhs; rw [hAc]
      rw [hform,aYc]
      simpa only [Polynomial.map_C,Polynomial.eval_C] using h
end
end aSj
end
section
namespace dnR
noncomputable section
open Ds (LN)
open aSj (tC)
open aR (ao af Shape cK qE)
open oR (separant)
open we (eT DO graph fW)
open aA1 (KX KY Xj apE YL bf4 su centre btu bHp)
open lB (Po abx)
open MvPolynomial
open Polynomial (hasseDeriv)
open scoped BigOperators Polynomial
open private bfH bzt.aa5 cXB cXW bHm
 bh4 indexWeight topWeight bet azs fits
 from ProximityPrize.SubmissionLower.L
open private cBr from ProximityPrize.SubmissionLower.BG
local notation "W" => weightedTotalDegree
private def VT (m:ℕ) (f :af 3) (i:Fin m) :eT 4 :=
 ∑ j:Fin m,MvPolynomial.C (((Polynomial.X-Polynomial.C centre)^j.val).coeff i.val) *
   fW (bf4 f (m-4) j.val)
private def cut (m:ℕ) (f :af 3) :eT 4 :=fW (YL f (m-3))
private def next (m:ℕ) (f :af 3) :eT 4 :=fW (YL f (m - 2))
private theorem ca9 (w:Fin 4→ℕ) {initial step m:ℕ} {f :af 3}
    (hinit : ∀ i,w i≤ initial) (hs :W w (KY f)≤ step)
    (hthird : ∀ k,W w (YL f k)≤w 3+k*step) (j:Fin m) :
    W w (bf4 f (m-4) j.val)≤ initial+(m-4)*step:= by
  unfold bf4 su
  have hpow:=(weightedTotalDegree_pow_le w (KY f) (m-4-(j.val-3))).trans
    (zBI _ hs)
  split_ifs with hj
  · have hz :j.val-3=0:= by omega
    rw [hz,Nat.sub_zero] at hpow ⊢
    exact (bfH hpow ((abx w _).trans (hinit _))).trans_eq (Nat.add_comm _ _)
  · have hsum: (m-4-(j.val-3))+(j.val-3)=m-4 := by
      have hj' := j.isLt
      omega
    calc
      _≤(m-4-(j.val-3))*step+(w 3+(j.val-3)*step) :=
        bfH hpow ((Po w _ _).trans (hthird _))
      _=w 3+((m-4-(j.val-3))+(j.val-3))*step:= by ring
      _≤_:= by rw [hsum]; exact Nat.add_le_add_right (hinit 3) _
private theorem a9A (w:Fin 4→ℕ) (base delta step initial m:ℕ) {f :af 3}
    (hf :W w (KX f)≤base)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+delta)
    (hsep:base - w 2+delta≤ step) (hvelocity :base+2*delta≤w 3+step)
    (hinit : ∀ i,w i≤ initial) :
    W w (graph f)≤base+delta ∧
    (∀ k,W w (fW (YL f k))≤w 3+k*step) ∧
    (∀ i,W w (VT m f i)≤ initial+(m-4)*step) := by
  have hg:W w (Xj f)≤base+delta := by
    rw [← btu]
    exact bzt.aa5 w hshift hf
  have hs :W w (KY f)≤base - w 2 := by
    rw [cXB]
    exact (weightedTotalDegree_pderiv_le_sub w 2 _).trans (zIu hf _)
  have hu:W w (apE f)≤w 3+step:= by
    unfold apE
    exact ((Po w _ _).trans (bzt.aa5 w hshift hg)).trans (by omega)
  have hthird (k :ℕ) :W w (YL f k)≤w 3+k*step:= by
    induction k with
    | zero =>
      simpa only [YL,Nat.zero_mul,zXY] using abx (R:=ao[X]) w 3
    | succ k ih =>
      rw [YL,Nat.succ_mul,← Nat.add_assoc]
      exact cXW w hshift ih hs hsep hu k
  refine ⟨?_,fun k=>(bHm w _).trans (hthird k),?_⟩
  · rw [← bHp]
    exact (bHm w _).trans hg
  · intro i
    unfold VT
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sum_mem
    intro j _
    exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((Po w _ _).trans ((bHm w _).trans
        (ca9 w hinit (hs.trans ((Nat.le_add_right _ _).trans hsep)) hthird j)))
private theorem support (m:ℕ) (hm:4≤ m) (f :af 3) (p:Shape)
   (hb:f.totalDegree≤p.b) (hj:qE f≤p.j) (ht:f.degreeOf 2≤p.t) :
   DO (graph f) (tC p) 1 ∧
   DO (cut m f) (LN (m+1) p) (m - 1) ∧
   DO (next m f) (LN (m+2) p) m ∧
   ∀ i,DO (VT m f i) (LN m p) (m - 2) := by
 have htotal:W bh4 (KX f)≤p.b:= by
   rw [azs,show bh4 ∘ z1o=(1 :Fin 3→ℕ) from by
     funext i; fin_cases i <;> decide,weightedTotalDegree_one]
   exact hb
 have hindex :W indexWeight (KX f)≤p.j:= by
   rw [azs,show indexWeight ∘ z1o=(Fin.val :Fin 3→ℕ) from by
     funext i; fin_cases i <;> decide,← Ex.C6]
   exact hj
 have htop:W topWeight (KX f)≤p.t:= by
   rw [azs,show topWeight ∘ z1o=Pi.single (2 :Fin 3) 1 from by
     funext i; fin_cases i <;> decide,weightedTotalDegree_piSingle]
   exact ht
 have hheight:W bet (KX f)≤0:= by
   rw [azs,show bet ∘ z1o=(0:Fin 3→ℕ) from by
     funext i; fin_cases i <;> decide,weightedTotalDegree,Finset.sup_le_iff]
   intro a _
   simp [z1K]
 obtain ⟨bg,bn,bc⟩:=a9A bh4 p.b 0 p.b 1 m htotal
   (by intro i; fin_cases i <;> decide) (by change p.b - 1+0≤p.b; omega)
   (by change p.b+2*0≤0+p.b; omega) (by intro i; fin_cases i <;> decide)
 obtain ⟨jg,jn,jc⟩:=a9A indexWeight p.j 1 (p.j+2) 2 m hindex
   (by intro i; fin_cases i <;> decide) (by change p.j - 2+1≤p.j+2; omega)
   (by change p.j+2*1≤0+(p.j+2); omega) (by intro i; fin_cases i <;> decide)
 obtain ⟨tg,tn,tc⟩:=a9A topWeight p.t 1 (p.t+2) 1 m htop
   (by intro i; fin_cases i <;> decide) (by change p.t - 1+1≤p.t+2; omega)
   (by change p.t+2*1≤0+(p.t+2); omega) (by intro i; fin_cases i <;> decide)
 obtain ⟨hg,hn,hc⟩:=a9A bet 0 1 1 1 m hheight
   (by intro i; fin_cases i <;> decide) (by decide) (by decide)
   (by intro i; fin_cases i <;> decide)
 have hjet (k :ℕ) :
     DO (fW (YL f k)) (LN (k+4) p) (k+2) := by
   have hk :k+4-4=k := by omega
   unfold LN
   rw [hk]
   apply fits
   · exact (bn k).trans (by change 0+_≤_; omega)
   · exact (jn k).trans (by change 0+_≤_; omega)
   · exact (tn k).trans (by change 0+_≤_; omega)
   · exact (hn k).trans (by change 1+_≤_; omega)
 refine ⟨?_,?_,?_,fun i=>fits (bc i) (jc i) (tc i) ((hc i).trans (by omega))⟩
 · exact fits (by simpa only [zXY] using bg) jg tg (by simpa only [Nat.zero_add] using hg)
 · unfold cut
   simpa only [show m-3+4=m+1 by omega,show m-3+2=m - 1 by omega] using hjet (m-3)
 · unfold next
   simpa only [show m - 2+4=m+2 by omega,show m - 2+2=m by omega] using hjet (m - 2)
private theorem cBs (f :af 3) (S:ao[X]) (hf :cK f S=0)
  {m:ℕ} (hm:m<K1.p) (j:Fin m) :
  cK (bf4 f (m-4) j.val) S =
    cK (separant f) S^(m-4)*hasseDeriv j.val S:= by
 have hj:=j.isLt
 exact cBr f S hf (m-4) j.val (by omega) (hj.trans hm)
end
end dnR
end
section
namespace bSe
noncomputable section
open yz (iz)
open MeasureTheory Filter MvPolynomial
open scoped BigOperators Pointwise Topology




variable (v :ℕ)
private theorem bhH (L:iz→ℝ)
   (hL : ∀ (a :ℝ) x,L (a•x)=a•L x) (P:Set iz) (a :ℝ) (ha :0≤a) :
   sSup (L '' (a•P))=a*sSup (L '' P) := by
 have heq :L '' (a•P)=a•(L '' P) := by
   ext z
   simp only [Set.mem_image,Set.mem_smul_set]
   constructor
   · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
     exact ⟨L x,⟨x,hx,rfl⟩,(hL a x).symm⟩
   · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
     exact ⟨a•x,⟨x,hx,rfl⟩,hL a x⟩
 rw [heq,Real.sSup_smul_of_nonneg ha,smul_eq_mul]
end
end bSe
end
section
namespace bSe
noncomputable section
open aR (Shape)
open oR (amU Wc)
open Qp (bF)
open aeB (ajg rest)
open scoped BigOperators
open private Qp.xl from ProximityPrize.SubmissionLower.BG
private def coefficients (q r :Shape) :ℕ×ℕ×ℕ :=
 (q.t*(r.j - r.t)+r.t*(q.j - q.t),
   q.t*(r.b - r.j)+r.t*(q.b - q.j)+q.t*r.t,
   (q.j - 2*q.t)*(r.b - r.t)+(r.j - 2*r.t)*(q.b - q.j+q.t))
private def linear (q r :Shape) (B J T:ℝ) :ℝ :=
 ((coefficients q r).1 :ℝ)*B+((coefficients q r).2.1 :ℝ)*J +
   ((coefficients q r).2.2 :ℝ)*T
private theorem bIz (q r :Shape) (hq:bF q) (hr :bF r) (B J T:ℝ) :
    linear q r B J T =
      ((q.t:ℝ)*(r.j-(r.t:ℝ))+(r.t:ℝ)*(q.j-(q.t:ℝ)))*B +
      ((q.t:ℝ)*(r.b-(r.j:ℝ))+(r.t:ℝ)*(q.b-(q.j:ℝ))+(q.t:ℝ)*r.t)*J +
      (((q.j:ℝ) - 2*q.t)*(r.b-(r.t:ℝ)) +
        ((r.j:ℝ) - 2*r.t)*(q.b-(q.j:ℝ)+q.t))*T:= by
  have hqt:q.t≤q.j:= by have :=hq.2; omega
  have hrt:r.t≤ r.j:= by have :=hr.2; omega
  simp only [linear,coefficients,z6H,z2R,zWE,
    zjK hqt,zjK hrt,zjK (hrt.trans hr.1),
    zjK hq.1,zjK hr.1,zjK hq.2,zjK hr.2]
private theorem biD (p q r :Shape) (hq:bF q) (hr :bF r) :
  (amU p q r :ℝ)=p.t*((q.j:ℝ) - q.t)*(2*(r.b:ℝ) - r.j) := by
 have hqt:q.t≤q.j:= by have :=hq.2; omega
 have hrb:r.j≤2*r.b:= by have :=hr.1; omega
 simp only [amU,z2R,zWE,zjK hqt,zjK hrb]
private theorem c0p (p q r :Shape) (hp:bF p) (hq:bF q) (hr :bF r) :
   (Wc p q r :ℝ)=linear q r p.b p.j p.t:= by
 let k :=(coefficients q r).1*p.b+(coefficients q r).2.1*p.j+(coefficients q r).2.2*p.t
 have hk : (k :ℝ)=linear q r p.b p.j p.t:= by
   simp only [k,linear,z6H,z2R]
 have h:amU p q r+amU p r q+amU q p r +
     amU q r p+amU r p q+amU r q p=2*k := by
   apply (Nat.cast_inj (R:=ℝ)).mp
   simp only [z6H,z2R,zWE,hk,bIz q r hq hr]
   rw [biD p q r hq hr,biD p r q hr hq,biD q p r hp hr,
     biD q r p hr hp,biD r p q hp hq,biD r q p hq hp]
   ring
 rw [Wc,h,Nat.mul_div_cancel_left _ (by decide :0<2),hk]
open private cBc from ProximityPrize.SubmissionLower.CT
private theorem BE (a :Fin 4→Shape) (h:Fin 4→ℕ)
   (hg:bF (a 1)) (hx :bF (a 2)) (hy :bF (a 3)) (B J T:ℝ) :
   (∑ S∈rest.powerset,(-1 :ℝ)^(3 - S.card) *
     ajg (Qp.xl S a) (∑ i∈S,h i) B J T) =
     (h 1 :ℝ)*linear (a 2) (a 3) B J T +
     (h 2 :ℝ)*linear (a 1) (a 3) B J T +
     (h 3:ℝ)*linear (a 1) (a 2) B J T:= by
 rw [cBc,bIz _ _ hx hy,bIz _ _ hg hy,bIz _ _ hg hx]
 simp only [Qp.xl,Finset.sum_empty,
   z5O (a :=(1 :Fin 4)) (s := ∅) (by decide),
   z5O (a :=(2 :Fin 4)) (s := ∅) (by decide),
   z5O (a :=(3:Fin 4)) (s := ∅) (by decide),
   z5O (a :=(1 :Fin 4)) (s :=insert 2 (insert 3 ∅)) (by decide),
   z5O (a :=(1 :Fin 4)) (s :=insert 2 ∅) (by decide),
   z5O (a :=(1 :Fin 4)) (s :=insert 3 ∅) (by decide),
   z5O (a :=(2 :Fin 4)) (s :=insert 3 ∅) (by decide),
   ajg,z6H,Nat.cast_zero,add_zero]
 ring
end
end bSe
end
