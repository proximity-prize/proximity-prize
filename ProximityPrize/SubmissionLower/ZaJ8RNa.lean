import ProximityPrize.SubmissionLower.ZK3v1Id
import ProximityPrize.SubmissionLower.ZlyD2pd
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, Ideal.Quotient.mk → zVv, IsFractionRing.injective → zxb, IsLocalization.Away → zSo, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.map → zDK, MvPolynomial.map_X → z7N, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.coeff_map → z0b, Polynomial.coeff_zero → zO6, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_map → zem, Polynomial.eval₂_monomial → zFK, Polynomial.hom_eval₂ → zly, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
section
set_option maxRecDepth 1500
namespace K1_13_7_2_5_1
noncomputable section
open Polynomial aR dN rW Rl
open scoped BigOperators
private def Oe :Rl.jo[X] →+* mK :=
 zqf (zDK ni) (znf rI)
private theorem bpK (i:ℕ) :
  Oe (hasseDeriv i Sp)=J1 rI i:= by
 classical
 simp only [Sp,C_mul_X_pow_eq_monomial,map_sum,J1]
 refine Finset.sum_congr rfl fun j _ => ?_
 rw [hasseDeriv_monomial]
 simp only [Oe,z4Q,zFK,
  map_mul,map_natCast,z7N,map_pow]
 ac_rfl
private theorem cTM :
   zqf ni rI=j8:= by
 apply Polynomial.ringHom_ext
 · intro b
   exact Polynomial.eval₂_C _ _
 · exact Polynomial.eval₂_X _ _
private theorem a3L (R:af 4) :
    Oe (aip R)=mS (bC R) := by
  change (Oe.comp
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom znf)
        (fun i:Fin 4=>hasseDeriv i.val Sp))) R =
    (mS.comp (zDK j8)) R
  apply zLs
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [zQb,zTv,MvPolynomial.map_C,mS]
    change Polynomial.eval₂ (zDK ni) (znf rI)
        (a.map znf)=znf (j8 a)
    have hm: (zDK ni).comp (znf:ao →+* Rl.jo) =
        (znf:GeoField →+* mK).comp ni:= by
      apply RingHom.ext
      simp
    rw [zem,hm,← zly]
    change znf ((zqf ni rI) a)= _
    rw [cTM]
  · intro i
    simpa only [zQb,MvPolynomial.eval₂Hom_X',z7N,
      mS] using bpK i.val
private theorem b18 {A:kT} (hA:A.IsPrime)
    (p:Rl.jo[X]) :
    Oe p∈gN A ↔ ∀ n,p.coeff n∈A:= by
  constructor
  · intro hp n
    rw [← hA.radical,← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K:=ao)]
    intro x hx
    let ev :=zY9 (ni ∘ x)
    have hev :ev.comp (zDK ni) =
        ni.comp (zY9 x) := by
      apply RingHom.ext
      intro q
      exact (MvPolynomial.eval_map _ _ _).trans (MvPolynomial.eval₂_comp _ _ _).symm
    have hker :gN A≤RingHom.ker ev := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro q hq
      change (ev.comp (zDK ni)) q=0
      rw [hev,zQb,(show zY9 x q=0 from hx q hq),map_zero]
    have he :ev (Oe p)=j8 (p.map (zY9 x)) := by
      change ev (p.eval₂ (zDK ni) (znf rI))= _
      rw [zly,hev]
      have hC:ev (znf rI)=rI:=MvPolynomial.eval_C _
      rw [hC,← zem]
      exact zLs cTM _
    have hzero :j8 (p.map (zY9 x))=0 :=
      he.symm.trans (RingHom.mem_ker.mp (hker hp))
    have hinj:zq4 j8 :=
      (algebraMap lN GeoField).injective.comp (zxb ao[X] lN)
    have hz :p.map (zY9 x)=0:=hinj (hzero.trans (map_zero _).symm)
    simpa only [MvPolynomial.aeval_eq_eval,z0b,zO6] using
      congrArg (fun g:ao[X]=>g.coeff n) hz
  · intro hp
    rw [congrArg Oe p.as_sum_range,map_sum]
    apply Ideal.sum_mem
    intro n _
    rw [Oe,z4Q,zFK]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hp n))
private abbrev aFB (A:kT) :=FractionRing (Rl.jo ⧸ A)
private def W9 (A:kT) :
   Rl.jo →+* aFB A :=
 (algebraMap (Rl.jo ⧸ A) (aFB A)).comp (zVv A)
private theorem cGy (A:kT) [A.IsPrime]
  (a :Rl.jo) :
  W9 A a=0↔a∈A:= by
 change algebraMap (Rl.jo ⧸ A) (aFB A) (zVv A a)=0↔_
 rw [map_eq_zero_iff _ (zxb (Rl.jo ⧸ A) (aFB A)),
  Ideal.Quotient.eq_zero_iff_mem]
private def btY {m:ℕ} (a :Fin m→Rl.jo) :
   Rl.jo[X] :=
 ∑ j:Fin m,C (a j)*Polynomial.X ^j.val
private theorem coeff_sum {m:ℕ} (a :Fin m→Rl.jo) (n:ℕ) :
   (btY a).coeff n=if hn:n< m then a ⟨n,hn⟩ else 0:= by
 classical
 simp only [btY,C_mul_X_pow_eq_monomial,Polynomial.finsetSum_coeff]
 split_ifs with hn
 · rw [Finset.sum_eq_single (⟨n,hn⟩:Fin m)]
   · exact coeff_monomial_same _ _
   · intro j _ hj
     exact coeff_monomial_of_ne _ (fun he=>hj (Fin.ext he.symm))
   · simp
 · exact Finset.sum_eq_zero fun j _=>coeff_monomial_of_ne _ (fun he=>hn (he.symm ▸ j.isLt))
private theorem dMB {m:ℕ} (a :Fin m→Rl.jo) (i:Fin m) :
  (btY a).coeff i.val=a i:= by
 rw [coeff_sum,dite_eq_left i.isLt]
private theorem dMA {m:ℕ} (a :Fin m→Rl.jo) (n:ℕ)
  (hn : ¬ n< m) : (btY a).coeff n=0:= by
 rw [coeff_sum,dite_eq_right hn]
private theorem diH :
  Sp=btY (m:=bf) MvPolynomial.X :=
 rfl
private theorem gG6 (i:Fin bf) :
  Sp.coeff i.val=z9v i:= by
 rw [diH]
 exact dMB (m:=bf) z9v i
private theorem gG7 :
  Sp.natDegree≤133671 := by
 apply natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 rw [diH]
 have hlen : ¬ n<bf :=not_lt_of_ge (Nat.succ_le_of_lt hn)
 exact dMA (m:=bf) z9v n hlen
private theorem aVN (A:kT) [A.IsPrime]
   [Algebra ao (aFB A)]
   (hk :algebraMap ao (aFB A)=(W9 A).comp znf)
   (R:af 4) :
   (aip R).map (W9 A) =
     Ve R (Sp.map (W9 A)) := by
 change (mapRingHom (W9 A)) (MvPolynomial.eval₂ (mapRingHom znf)
   (fun i:Fin 4=>hasseDeriv i.val Sp) R)= _
 rw [MvPolynomial.hom_eval₂,Polynomial.mapRingHom_comp,← hk]
 simp only [zKC,← hasseDeriv_map,Ve]
theorem eea {f :af 4} (T:Li f) {A:kT}
    (h:akB f A) :
    bC f∈lA A ∧
      bC (separant f)∉lA A ∧
      bC T.test∈lA A ∧
      bC T.denom∉lA A ∧
      ∀ i,z9v i*mS (bC T.denom) -
        mS (bC (T.Fr i))∈gN A:= by
  let:A.IsPrime :=h.prime
  let k :ao →+* aFB A:=(W9 A).comp znf
  let:Algebra ao (aFB A) :=k.toAlgebra
  let U:=Sp.map (W9 A)
  have hmap (R:af 4) : (aip R).map (W9 A)=Ve R U :=
    aVN A rfl R
  have heval (p:Rl.jo[X]) :
      p.map (W9 A)=0↔Oe p∈gN A:= by
    rw [b18 h.prime]
    exact ⟨fun hz n=>(cGy A _).mp (by
      simpa only [z0b,zO6] using
        congrArg (fun g: (aFB A)[X]=>g.coeff n) hz),
      fun hn=>Polynomial.ext fun n=> by
        rw [z0b,zO6,cGy]
        exact hn n⟩
  have hfresh (R:af 4) :Ve R U=0↔bC R∈lA A:= by
    change Ve R U=0↔mS (bC R)∈gN A
    rw [← hmap,← a3L,heval]
  have hf :bC f∈lA A:= by
    change mS (bC f)∈gN A
    rw [← a3L,b18 h.prime]
    exact h.solves
  have hs :bC (separant f)∉lA A:= by
    change mS (bC (separant f))∉gN A
    rw [← a3L,b18 h.prime]
    obtain ⟨n,hn⟩:=h.regular
    exact fun hall=>hn (hall n)
  have hd:U.natDegree≤133671 :=natDegree_map_le.trans gG7
  obtain ⟨hden,ht,hr⟩:=T.ar5 (aFB A) U hd ((hfresh f).mpr hf)
    (fun hz=>hs ((hfresh (separant f)).mp hz))
  refine ⟨hf,hs,(hfresh T.test).mp ht,fun hm=>hden ((hfresh T.denom).mpr hm),?_⟩
  intro i
  let p:=C (z9v i:Rl.jo)*aip T.denom -
    aip (T.Fr i)
  have hp:p.map (W9 A)=0:= by
    change mapRingHom (W9 A) p=0
    simp only [p,map_sub,map_mul,zKC,Polynomial.map_C,hmap]
    rw [hr i,show U.coeff i.val=W9 A (z9v i) by
      rw [z0b,gG6],mul_comm,sub_self]
  have hm:=(heval p).mp hp
  simpa only [p,map_sub,map_mul,a3L,
    show ∀ a :Rl.jo,Oe (C a)=zDK ni a
      from fun _=>eval₂_C _ _,z7N] using hm
end
end K1_13_7_2_5_1
end
section
namespace K1_13_7_2_5_1
noncomputable section
open aR dN rW Rl ap9
open MvPolynomial
private def al7:GeoJets →ₐ[GeoField] mK :=
 aeval (fun i:Fin 4=>J1 rI i.val)
private theorem dXd {A:kT} (hA: (gN A).IsPrime)
    (D:GeoJets) (N :Fin bf→GeoJets)
    (hD:D∉lA A)
    (hN : ∀ i,z9v i*mS D - mS (N i)∈gN A) :
    dimension (lA A)=dimension (gN A) := by
  let I:=gN A
  let J:=lA A
  let q:=zVv I
  let F:=Ideal.quotientMapₐ I al7 (show J≤I.comap al7.toRingHom from le_rfl)
  have hF (p:GeoJets) :F (zVv J p)=q (mS p) :=rfl
  have hinj:zq4 F :=
    Ideal.quotientMap_injective' (H :=show J≤I.comap al7.toRingHom from le_rfl) le_rfl
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
  let d:=q (mS D)
  have hX (i:Fin bf) :q (mS (N i))=d*q (z9v i) := by
    have hz :=Ideal.Quotient.eq_zero_iff_mem.mpr (hN i)
    change q (z9v i*mS D - mS (N i))=0 at hz
    rw [map_sub,sub_eq_zero,map_mul,mul_comm] at hz
    exact hz.symm
  have hclear (p:mK) : ∃ (u:GeoJets) (n:ℕ),
      q (mS u)=d^n*q p:= by
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨znf a,0,?_⟩
      simp only [pow_zero,one_mul,mS,zTv]
    | add p r hp hr =>
      obtain ⟨u,n,hu⟩:=hp
      obtain ⟨v,m,hv⟩:=hr
      refine ⟨u*D^m+v*D^n,n+m,?_⟩
      simp only [map_add,map_mul,map_pow,hu,hv,pow_add]
      change d^n*q p*d^m+d^m*q r*d^n =
        d^n*d^m*(q p+q r)
      ring
    | mul_X p i hp =>
      obtain ⟨u,n,hu⟩:=hp
      refine ⟨u*N i,n+1,?_⟩
      simp only [map_mul,hu,hX,pow_succ]
      ring
  let t:=zVv J D
  let L:=Localization.Away d
  let:zSo (F t) L:= by
    change zSo d L
    infer_instance
  let G:=IsLocalization.Away.mapₐ (R:=GeoField) (Localization.Away t) L F t
  have hsurj:Function.Surjective G:= by
    apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom t).mpr
    intro a
    obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective a
    obtain ⟨u,n,hu⟩:=hclear p
    refine ⟨zVv J u,n,?_⟩
    change F (zVv J u)=F (zVv J D)^n*q p
    rw [hF,hF]
    exact hu
  let:I.IsPrime :=hA
  have hreg:IsLeftRegular d:=IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
theorem proof :ap9.c1 := by
 intro f T A hA
 obtain ⟨hp,hd,_⟩:=bRp.proof A hA.prime
 obtain ⟨hf,hs,ht,hD,hN⟩:=eea T hA
 exact ⟨hp,(dXd hp _ _ hD hN).trans hd,hf,hs,ht,hD,hN⟩
end
end K1_13_7_2_5_1
end
