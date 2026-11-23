import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.ZB2eCyc
import ProximityPrize.SubmissionLower.ZTNySHa
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Finset.sum_mul → zkq, Function.Injective → zq4, IsFractionRing.injective → zxb, IsLocalization.lift_comp → zrr, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.eval → zY9, MvPolynomial.eval_X → zV6, MvPolynomial.eval₂ → zSZ, MvPolynomial.eval₂Hom → zOD, MvPolynomial.homogeneousComponent → zyc, MvPolynomial.killCompl → ziz, MvPolynomial.rename_X → z6l, MvPolynomial.ringHom_ext → zXT, Nat.sub_le_sub_right → zIu, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qzFnQja
noncomputable section
open K1 (K)
open cu (L Shape j9)
open DP bax Polynomial
open scoped Polynomial
open private a06 specialize bq3 enZ bsb ey4 gtY Qa edC cMJ from ProximityPrize.SubmissionLower.Z
theorem perturbed_poles {h:ℕ} {D:jF h} (Crt:zG D)
    {z :K} {S:K[X]} (hm:aKF D z S) {s :Shape} {P:Source}
    (hP:P∈btN Crt s) (V:L[X]) :
    Iy D^(s.B+s.J) ∣
      ab3 (Z7 z) (j9 S+Iy D *V) P:= by
  let t:=Z7 z
  let A:=a06 t
  let f :=algebraMap qC A
  let e :=specialize t
  let g:=bq3 t
  let j:L →+* A:=f.comp znf
  have hef :e.comp f=zY9 t:=zrr _
  have hgf :g.comp f=algebraMap qC aQ:=zrr _
  have hej:e.comp j=RingHom.id L:= by
    change (e.comp f).comp znf= _
    rw [hef]
    ext a
    simp
  have hgj:g.comp j=algebraMap L aQ:= by
    change (g.comp f).comp znf= _
    rw [hgf]
    ext a
    simp [IsScalarTower.algebraMap_apply L qC aQ,MvPolynomial.algebraMap_eq]
  have hd (i:Fin 2) : (Crt.denominator i).eval (t i)≠0:=Crt.regular i _ (hm i).1
  obtain ⟨R,hR⟩:=cZS Crt hm
  let T:=R+V
  have hS:Iy D*T+azz Crt t=j9 S+Iy D*V:= by
    rw [show T=R+V from rfl,mul_add,← hR]
    abel
  let H :=(Iy D).map j
  let U:=T.map j
  let lift:=bsb Crt t hd
  let jetY:=H*U + lift
  let Q:=adA (C.comp f) z7y jetY jetY.derivative P
  let F:=H^(s.B+s.J)
  have hFm:F.Monic:=((D.monic 0).mul (D.monic 1) |>.map j).pow _
  have egH :H.map g=IE D:= by rw [map_map,hgj]; rfl
  have eeH :H.map e=Iy D:= by rw [map_map,hej,map_id]
  have eeU:U.map e=T:= by rw [map_map,hej,map_id]
  have egY:jetY.map g=IE D *U.map g+OY Crt:= by
    rw [zS4,zNl,egH,ey4]
  have eeY:jetY.map e=j9 S+Iy D*V:= by
    rw [zS4,zNl,eeH,eeU,gtY,hS]
  have hgQ :
      Q.map g= Qa (U.map g) (forward Crt P) := by
    change ((mapRingHom g).comp (adA (C.comp f) z7y jetY jetY.derivative)) P =
      ((Qa (U.map g)).comp (forward Crt).toRingHom) P
    rw [cMJ,hgf,← derivative_map,egY,edC,derivative_add,derivative_mul]
    congr 2
    abel
  have hgF:F.map g=IE D^(s.B+s.J) := by rw [z5m,egH]
  have hdiv :F.map g∣Q.map g:= by
    rw [hgF,hgQ]
    have h:=map_dvd (Qa (U.map g)) hP
    simpa [Qa,pW,eval₂_pow] using h
  have hlocal:F∣Q:= by
    apply (modByMonic_eq_zero_iff_dvd hFm).mp
    apply map_injective g (enZ t)
    rw [map_modByMonic g hFm,Polynomial.map_zero]
    exact (modByMonic_eq_zero_iff_dvd (hFm.map g)).mpr hdiv
  have heQ:Q.map e=ab3 t (j9 S+Iy D*V) P:= by
    change ((mapRingHom e).comp (adA (C.comp f) z7y jetY jetY.derivative)) P= _
    rw [cMJ,hef,← derivative_map,eeY]
    rfl
  have heF:F.map e=Iy D^(s.B+s.J) := by rw [z5m,eeH]
  have hmapped:=map_dvd (mapRingHom e) hlocal
  change F.map e∣Q.map e at hmapped
  rwa [heF,heQ] at hmapped
end
end qzFnQja
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxSynthPendingDepth 16
namespace qzFnQja
noncomputable section
open Polynomial
open P6 (dw)
open cu (L j9 Shape)
open DP
open bax (cMK ab3 cHy)
open qQCjxhb (inc mL)
open scoped Polynomial BigOperators
open private gNp from ProximityPrize.SubmissionLower.B4
private def Bounded (e b:ℕ) (F:Param) :Prop :=
  ∀ n,(F.coeff n).natDegree≤b+e*n
private theorem afg {e a b:ℕ} {F G:Param}
    (hF:Bounded e a F) (hG:Bounded e b G) :Bounded e (a+b) (F*G) := by
  intro n
  rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hs :=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hs,Nat.mul_add]
  omega
private theorem aCs {e a :ℕ} {S:L[X]} (hS:S.natDegree≤a) :
    Bounded e a (C S) := by
  intro n
  by_cases h:n=0
  · simpa [h] using hS
  · simp [coeff_C,h]
private theorem aMs {e b:ℕ} {F:Param} (hf :Bounded e b F) (n:ℕ) :
    Bounded e (b*n) (F^n) := by
  induction n with
  | zero=>simpa using aCs (e :=e) (S:=(1 :L[X])) (a :=0) (by simp)
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact afg ih hf
private theorem bounded_jetLine {e b:ℕ} {S V:L[X]}
    (hS:S.natDegree≤b) (hV:V.natDegree≤b+e) :Bounded e b (aIh S V) := by
  intro n
  rw [aIh,coeff_add,coeff_C,coeff_C_mul_X]
  by_cases h0:n=0
  · simpa [h0] using hS
  · by_cases h1 :n = 1
    · simpa [h1] using hV
    · simp [h0,h1]
private theorem sourceLine_degree {h W e :ℕ} {s :Shape} {Q:Source}
    (hQ:Q∈Aw h s W) (t:Fin 2→L) (S V:L[X])
    (hS:S.natDegree≤131071+h) (hV:V.natDegree≤131071+h+e) (n:ℕ) :
    ((sourceLine t S V Q).coeff n).natDegree≤W+(s.B+s.J)*(2*h)+e*n:= by
  let d:=131071+h
  change S.natDegree≤d at hS
  change V.natDegree≤d+e at hV
  have hy :Bounded e d (aIh S V) :=bounded_jetLine hS hV
  have hd:1≤d:= by dsimp [d]; omega
  have hv :Bounded e (d-1) (aIh S.derivative V.derivative) := by
    apply bounded_jetLine ((natDegree_derivative_le S).trans (zIu hS _))
    exact (natDegree_derivative_le V).trans ((zIu hV _).trans (by omega))
  have hx :Bounded e 1 (C (z7y:L[X])) :=aCs (by simp)
  rw [sourceLine,cMK,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [zkq,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro i _
  rw [zkq,zkq,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hw:a+(i+j)*d≤W+(s.B+s.J)*(2*h)+j:= by
    by_contra hn
    apply mem_support_iff.mp ha
    ext k
    exact hQ j i a k (fun hk=>hn hk.2.2.2)
  have hc (c:L) :Bounded e 0 (C (C c) :Param) :=aCs (by simp)
  have ht:=afg (afg
    (afg (hc (zY9 t (((Q.coeff j).coeff i).coeff a))) (aMs hx a))
    (aMs hy i)) (aMs hv j) n
  refine ht.trans ?_
  have hj: (d-1)*j+j=d*j:= by rw [← Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel hd]
  rw [Nat.add_mul] at hw
  simp only [zero_add,one_mul]
  rw [Nat.mul_comm i d,Nat.mul_comm j d] at hw
  omega
private theorem coeff_dvd_of_eval {F:Param} {G:L[X]} (hG:G.Monic)
    (he : ∀ c:L,G∣F.eval (C c)) (n:ℕ) :G∣F.coeff n:= by
  classical
  apply (modByMonic_eq_zero_iff_dvd hG).mp
  let f :=modByMonicHom G
  change f (F.coeff n)=0
  ext i
  let q:L[X] := ∑ j∈F.support,monomial j ((f (F.coeff j)).coeff i)
  have hq (c:L) :q.eval c=0:= by
    have hh:f (F.eval (C c))=0:=(modByMonic_eq_zero_iff_dvd hG).mpr (he c)
    have hsum:F.eval (C c) = ∑ j∈F.support,(c^j)•F.coeff j:= by
      rw [eval_eq_sum]
      simp only [Polynomial.sum,smul_eq_C_mul,← map_pow]
      exact Finset.sum_congr rfl fun _ _=>mul_comm _ _
    have hcoe :=congrArg (fun p:L[X]=>p.coeff i) hh
    rw [hsum] at hcoe
    simp only [map_sum,map_smul,finsetSum_coeff,coeff_smul,coeff_zero] at hcoe
    simpa [q,eval_finsetSum,eval_monomial,mul_comm] using hcoe
  have hq0:q=0:= by
    apply eq_zero_of_infinite_isRoot
    simpa [IsRoot,hq] using (Set.infinite_univ : (Set.univ :Set L).Infinite)
  have hn:q.coeff n=(f (F.coeff n)).coeff i:= by
    change (∑ j∈F.support,monomial j ((f (F.coeff j)).coeff i)).coeff n= _
    rw [finsetSum_coeff]
    by_cases hmem:n∈F.support
    · rw [Finset.sum_eq_single_of_mem n hmem]
      · simp
      · intro j _ hne
        simp [coeff_monomial,hne]
    · rw [Finset.sum_eq_zero]
      · simp [notMem_support_iff.mp hmem]
      · intro j hj
        have hne :j≠n:= fun h=>hmem (h ▸ hj)
        simp [coeff_monomial,hne]
  rw [← hn,hq0]
  simp only [coeff_zero]
theorem proof :qQCjxhb.c1 := by
  intro h D Crt word s W Q hQ hnode z S hm hd T hT hhit U hU n _ _ hn
  obtain ⟨⟨ha,hc⟩,hp⟩:=hQ
  let V:=mL D T*U
  let F:=sourceLine (Z7 z) (j9 S) V Q
  let e :=dw-131071+1+h
  have hmD: (Iy D).Monic:=(D.monic 0).mul (D.monic 1)
  have hD: (Iy D).natDegree=2*h:= by
    rw [Iy,natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero,D.degree,D.degree]
    omega
  have hL: (mL D T).natDegree≤2*h+dw:= by
    unfold mL
    exact natDegree_mul_le.trans (by rw [hD,gR.ZQ,hT])
  have hV:V.natDegree≤131071+h+e := by
    refine (natDegree_mul_le_of_le hL hU).trans ?_
    have hA:131071≤dw:= by decide
    dsimp [e]
    omega
  have heval (c:L) :F.eval (C c)=ab3 (Z7 z) (j9 S+C c*V) Q :=
    sourceLine_eval _ _ _ _ _
  have hpole :Iy D^(s.B+s.J)∣F.coeff n:= by
    apply coeff_dvd_of_eval (hmD.pow _)
    intro c
    rw [heval,show C c*V=Iy D*(C c*(gR.mL ad0 T*U)) by
      dsimp [V,mL]; ac_rfl]
    exact perturbed_poles Crt hm hp _
  have hcontact (k) (hk :k∈T) : (z7y-C (ad0 k))^s.m∣F.coeff n:= by
    apply coeff_dvd_of_eval ((monic_X_sub_C _).pow _)
    intro c
    rw [heval]
    apply cHy hc _ _ k
    have hl:=gR.arK ad0 T k hk
    simp [V,mL,hl,hhit k hk]
  have hdeg:=sourceLine_degree ha (Z7 z) (j9 S) V hd hV n
  have hzero :F.coeff n=0:=gNp (W:=W+e*n) hnode
    (hdeg.trans_eq (Nat.add_right_comm _ _ _)) hpole T hT.ge hcontact hn
  rw [← sourceLine_map,coeff_map]
  change inc (F.coeff n)=0
  rw [hzero,map_zero]
end
end qzFnQja
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qRgrd5a
noncomputable section
open Polynomial
open P6 (K)
open cu (L FX)
open gT (Ambient)
open qQCjxhb (inc line point)
open scoped Polynomial BigOperators
private theorem bXP (P:Ambient) (v :Fin 4→FX) (n:ℕ) :
    (zSZ C (fun i=>C (v i)*z7y) P).coeff n =
      zY9 v (zyc n P) := by
  classical
  rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff,MvPolynomial.homogeneousComponent_apply]
  change _=zOD (RingHom.id _) v _
  rw [map_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← map_pow z1z,
    ← map_prod z1z,← map_mul z1z,← mul_assoc,Finset.prod_pow_eq_pow_sum,
    Polynomial.coeff_C_mul_X_pow,RingHom.id_apply,Finsupp.degree_apply]
  split_ifs <;> simp_all
private def lP:Fin 2→Fin 4 := ![2,3]
private theorem jetIndex_injective :zq4 lP:= by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [lP]
private def withSeedsZero (v :Fin 2→FX) :Fin 4→FX := ![0,0,v 0,v 1]
private theorem eval_pure (P:Ambient) (v :Fin 2→FX) :
    zY9 v (P.killCompl jetIndex_injective) =
      zY9 (withSeedsZero v) P:= by
  have h: (zY9 v).comp (ziz jetIndex_injective).toRingHom =
      zY9 (withSeedsZero v) := by
    apply zXT
    · intro c
      simp
    · intro i
      change zY9 v (ziz jetIndex_injective
        (z9v i))=zY9 (withSeedsZero v) (z9v i)
      rw [zV6]
      fin_cases i
      · simp [ziz,lP,withSeedsZero]
      · simp [ziz,lP,withSeedsZero]
      · change zY9 v (ziz jetIndex_injective
          (z9v (lP 0)))=v 0
        rw [← z6l lP 0,MvPolynomial.killCompl_rename_app,
          zV6]
      · change zY9 v (ziz jetIndex_injective
          (z9v (lP 1)))=v 1
        rw [← z6l lP 1,MvPolynomial.killCompl_rename_app,
          zV6]
  exact zmU h P
private theorem line_translate (F:Ambient) (z :K) (S:K[X]) (y v :FX) :
    line F z S y v =
      zSZ C (fun i=>C (withSeedsZero ![y,v] i)*z7y)
        (jA.translate (point z S) F) := by
  unfold line
  let ev :Ambient →+* Polynomial FX :=
    zOD C (fun i=>C (withSeedsZero ![y,v] i)*z7y)
  have h:ev.comp (jA.translate (point z S)) =
      zOD C
        ![C (point z S 0),C (point z S 1),
          C (point z S 2)+C y*z7y,C (point z S 3)+C v*z7y] := by
    apply zXT
    · intro c
      simp [ev,jA.translate]
    · intro i
      fin_cases i <;> simp [ev,jA.translate,withSeedsZero,add_comm]
  exact (zmU h F).symm
private def direction {R:Type*} [CommRing R] (x d e :R) (v :Fin 2→R) :Fin 2→R :=
  let u:=v 0 + x*v 1
  ![d*u,e*u+d*v 1]
private theorem direction_surjective (x d e :FX) (hd:d≠0) :
    Function.Surjective (direction x d e) := by
  intro w
  let u:=w 0/d
  let b:=(w 1-e*u)/d
  have h0:d*u=w 0:= by
    change d*(w 0/d)=w 0
    rw [mul_comm,div_mul_cancel₀ _ hd]
  have h1 :d*b=w 1-e*u:= by
    change d*((w 1-e*u)/d)=w 1-e*u
    rw [mul_comm,div_mul_cancel₀ _ hd]
  refine ⟨![u-x*b,b],?_⟩
  funext i
  fin_cases i
  · change d*((u-x*b)+x*b)=w 0
    rw [sub_add_cancel,h0]
  · change e*((u-x*b)+x*b)+d*b=w 1
    rw [sub_add_cancel,h1,add_comm,sub_add_cancel]
private abbrev constant:L →+* FX:=inc.comp C
private theorem direction_ext (Q:MvPolynomial (Fin 2) FX) (x d e :FX) (hd:d≠0)
    (h : ∀ c b:L,zY9 (direction x d e ![constant c,constant b]) Q=0) :
    Q=0:= by
  have hc:zq4 constant :=
    (zxb L[X] FX).comp Polynomial.C_injective
  let:Infinite FX:=Infinite.of_injective constant hc
  let H :=zIe
    (direction (znf x) (znf d) (znf e) z9v) Q
  have he (v :Fin 2→FX) :
      zY9 v H=zY9 (direction x d e v) Q:= by
    change zIe v (zIe _ Q)= _
    rw [MvPolynomial.comp_aeval_apply]
    change zY9 _ Q=zY9 _ Q
    refine congrArg (fun f :Fin 2→FX=>zY9 f Q) ?_
    funext i
    fin_cases i <;> simp [direction]
  have hH :H=0:= by
    apply MvPolynomial.funext_set (fun _=>Set.range constant)
      (fun _=>Set.infinite_range_of_injective hc)
    intro v hv
    obtain ⟨c,hc⟩:=hv 0 (Set.mem_univ _)
    obtain ⟨b,hb⟩:=hv 1 (Set.mem_univ _)
    have hv' : ![constant c,constant b]=v := by
      funext i
      fin_cases i
      · exact hc
      · exact hb
    rw [he,map_zero,← hv']
    exact h c b
  apply MvPolynomial.funext
  intro w
  obtain ⟨v,rfl⟩:=direction_surjective x d e hd w
  simp only [← he,hH,map_zero]
private theorem direction_affine (D:L[X]) (c b:L) :
    let U:L[X] :=C c+C b*z7y
    direction (inc z7y) (inc D) (inc D.derivative) ![constant c,constant b] =
      ![inc (D*U),inc (D*U).derivative] := by
  intro U
  have hu:constant c+inc z7y*constant b=inc U:= by
    change inc (C c)+inc z7y*inc (C b)=inc (C c+C b*z7y)
    rw [map_add,map_mul,mul_comm (inc z7y)]
  have hd:inc U.derivative=constant b:= by
    change inc ((C c+C b*z7y).derivative)=inc (C b)
    rw [derivative_add,derivative_C,derivative_C_mul_X,zero_add]
  funext i
  fin_cases i
  · change inc D *(constant c+inc z7y*constant b)=inc (D*U)
    rw [hu,map_mul]
  · change inc D.derivative*(constant c+inc z7y*constant b) +
      inc D *constant b=inc (D*U).derivative
    rw [hu,← hd]
    simp only [derivative_mul,map_add,map_mul]
theorem proof :qQCjxhb.c2 := by
  intro F z S D hD a h0 h1 _ _ h
  let T:=jA.translate (point z S) F
  let P:=zyc (a 2+a 3) T
  let Q:=P.killCompl jetIndex_injective
  have hz :Q=0:= by
    have hd:inc D ≠0:= by
      simpa only [map_zero] using (zxb L[X] FX).ne hD
    apply direction_ext Q (inc z7y) (inc D) (inc D.derivative) hd
    intro c b
    let U:L[X] :=C c+C b*z7y
    have hU:U.natDegree≤1 :=natDegree_add_le_of_degree_le (by simp)
      (by simpa using natDegree_C_mul_X_pow_le b 1)
    rw [direction_affine]
    dsimp only [Q,P]
    rw [eval_pure,← bXP,← line_translate]
    exact h U hU
  have hs : ↑a.support⊆Set.range lP:= by
    intro i hi
    fin_cases i
    · exact (Finsupp.mem_support_iff.mp hi h0).elim
    · exact (Finsupp.mem_support_iff.mp hi h1).elim
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  have hn:a.degree=a 2+a 3:= by
    rw [Finsupp.degree_eq_sum,Fin.sum_univ_four,h0,h1]
    omega
  have hc:=congrArg (fun q:MvPolynomial (Fin 2) FX =>
    q.coeff (a.comapDomain lP jetIndex_injective.injOn)) hz
  change (P.killCompl jetIndex_injective).coeff _ = _ at hc
  dsimp only [P] at hc
  rw [MvPolynomial.coeff_killCompl,
    Finsupp.mapDomain_comapDomain _ jetIndex_injective _ hs,
    MvPolynomial.coeff_homogeneousComponent] at hc
  simpa only [hn,eq_self,ite_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hc
end
end qRgrd5a
end
