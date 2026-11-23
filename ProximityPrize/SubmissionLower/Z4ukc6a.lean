import ProximityPrize.SubmissionLower.ZycQTHe
import ProximityPrize.SubmissionLower.ZlfuKwd
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Finsupp.single → zhf, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.map → zDK, MvPolynomial.mem_support_iff → zuk, Polynomial.hasseDeriv → z75, Polynomial.mapRingHom → zhd
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qOhg0Kc
noncomputable section
open Polynomial MvPolynomial
open cu (L)
open jA (kS mA jH)
open q7IA62d (Lq forward a6h oneNumerator_small)

private def raw (i:Fin 3) :ℕ:=131071 - i.val
private def amm (h:ℕ) (i:mA) :ℕ :=
 i.elim 0 (fun j=>131071+h - j.val)
private theorem weight_sum {σ:Type*} (a :σ →₀ ℕ) (w:σ→ℕ) :
  a.weight w=a.sum (fun i e=>w i*e) := by
 rw [Finsupp.weight_apply]
 congr 1
 funext i e
 exact Nat.mul_comm _ _
theorem proof :qAzyIze.c1 := by
  intro h hh D Crt T P hP
  let H :=jH (D.block 0)
  have hH :H.natDegree=h:=(natDegree_map _).trans (D.degree 0)
  have hR: (a6h Crt).natDegree≤h :=
    (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (oneNumerator_small Crt hh).le)
  let g:mA→Lq:= fun i=>i.elim
    (znf (Polynomial.C (algebraMap L[X] kS Polynomial.X)))
    (fun j=>znf (hasseDeriv j.val (a6h Crt)) +
      ∑ k :Fin 3,if k.val≤j.val then
        znf (hasseDeriv (j.val - k.val) H)*z9v k else 0)
  have hg (i:mA) :g i∈restrictJointDegree raw (amm h i) := by
    cases i with
    | none=>exact C_mem_restrictJointDegree raw (by simp [amm])
    | some j =>
      change _+_∈restrictJointDegree raw (131071+h - j.val)
      apply Submodule.add_mem
      · apply C_mem_restrictJointDegree
        have hj:=j.isLt
        have hd:=natDegree_hasseDeriv_le (a6h Crt) j.val
        omega
      · apply Submodule.sum_mem
        intro k _
        by_cases hk :k.val≤j.val
        · rw [ite_eq_left hk]
          by_cases hd:j.val - k.val≤h
          · refine restrictJointDegree_mono raw ?_ (mul_mem_restrictJointDegree
                (C_mem_restrictJointDegree raw (natDegree_hasseDeriv_le H (j.val - k.val)))
                (X_mem_restrictJointDegree raw k le_rfl))
            have hj:=j.isLt
            have hk' := k.isLt
            unfold raw
            omega
          · rw [hasseDeriv_eq_zero_of_lt_natDegree H _ (by omega),map_zero,zero_mul]
            exact Submodule.zero_mem _
        · rw [ite_eq_right hk]
          exact Submodule.zero_mem _
  let f :=zhd (algebraMap L kS)
  have hp:zDK f P∈restrictJointDegree (amm h) T:= by
    apply mem_restrictJointDegree.mpr
    intro a ha
    rw [MvPolynomial.coeff_map] at ha ⊢
    have hne :P.coeff a≠0:= fun hz=>ha (by rw [hz,map_zero])
    change ((P.coeff a).map (algebraMap L kS)).natDegree+_≤_
    rw [natDegree_map,weight_sum]
    have hw:a.sum (fun i e=>amm h i*e) =
        a.sum (fun i e=>i.elim 0 (fun j=>(131071+h - j.val)*e)) := by
      congr 1
      funext i e
      cases i <;> simp [amm]
    rw [hw]
    exact hP a (MvPolynomial.mem_support_iff.mpr hne)
  have he :bind₁ g (zDK f P)=forward Crt P:= by
    change eval₂Hom znf g (zDK f P)= _
    rw [eval₂Hom_map_hom]
    rfl
  have hb:=bind₁_mem_restrictJointDegree hg hp
  rw [he] at hb
  intro a ha
  have hd:=mem_restrictJointDegree.mp hb a (MvPolynomial.mem_support_iff.mp ha)
  rwa [weight_sum] at hd
end
end qOhg0Kc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qal8fRb
noncomputable section
open MvPolynomial
open scoped Polynomial MonomialOrder
open cu (L)
open DP (jF zG)
open jA (jK ko iP kS jH bC)
open q7IA62d (forward Lq)
open qAzyIze (Exp RawExp jetExp)
private abbrev dualLex :MonomialOrder ((Fin 3)ᵒᵈ) :=MonomialOrder.lex
private def m:MonomialOrder (Fin 3) where
 syn:=dualLex.syn
 toSyn:=(Finsupp.domCongr OrderDual.toDual).trans dualLex.toSyn
 toSyn_monotone := by
  intro a b hab
  apply dualLex.toSyn_monotone
  intro j
  exact hab (OrderDual.ofDual j)
private abbrev swapCoeffs :L[X][X] →+* kS[X] :=
 (zhd (algebraMap L[X] kS)).comp
   (Polynomial.Bivariate.swap (R:=L)).toRingHom
private def nL:jK →+* Lq :=
 (zDK swapCoeffs).comp (optionEquivRight L[X] (Fin 3)).toRingHom
private theorem option_monomial (a :Exp) (r :L[X]) :
   optionEquivRight L[X] (Fin 3) (monomial a r) =
     monomial a.some (Polynomial.monomial (a none) r) := by
 rw [← Polynomial.C_mul_X_pow_eq_monomial]
 simp only [monomial_eq,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fintype.prod_option,
   map_mul,map_prod,map_pow,optionEquivRight_C,optionEquivRight_X_none,
   optionEquivRight_X_some,Finsupp.some_apply,mul_assoc]
private theorem option_coeff (P:jK) (b:RawExp) (n:ℕ) :
    ((optionEquivRight L[X] (Fin 3) P).coeff b).coeff n=P.coeff (b.optionElim n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial a r =>
    rw [option_monomial,coeff_monomial,coeff_monomial]
    by_cases ha :a.some=b
    · subst b
      by_cases hn:a none=n
      · simp [← hn]
      · have he :a≠a.some.optionElim n:= fun e =>
          hn (by simpa using zmU e none)
        simp [hn,he,Polynomial.coeff_monomial]
    · have he :a≠b.optionElim n:= fun e =>
        ha (by simpa using congrArg Finsupp.some e)
      simp [ha,he]
private theorem grouped_support (P:jK) (b:RawExp) :
   b∈(nL P).support ↔ ∃ a∈P.support,jetExp a=b:= by
 have hi:Function.Injective swapCoeffs :=
   (Polynomial.map_injective _ (zxb L[X] kS)).comp
     Polynomial.Bivariate.swap.injective
 have hj (a :Exp) :jetExp a=a.some := by
   ext j
   rfl
 change b∈(zDK swapCoeffs (optionEquivRight L[X] (Fin 3) P)).support↔_
 rw [support_map_of_injective _ hi,zuk]
 constructor
 · intro hn
   obtain ⟨n,hn⟩:=Polynomial.support_nonempty.mpr hn
   rw [Polynomial.mem_support_iff,option_coeff] at hn
   exact ⟨b.optionElim n,MvPolynomial.mem_support_iff.mpr hn,by simp [hj]⟩
 · rintro ⟨a,ha,rfl⟩ hn
   rw [hj] at hn
   apply MvPolynomial.mem_support_iff.mp ha
   rw [← Finsupp.optionElim_some a,← option_coeff,hn,Polynomial.coeff_zero]
private def jet {h} {D:jF h} (crt:zG D) (i:Fin 3) :Lq :=
 forward crt (z9v (some i))
private theorem forward_eq {h} {D:jF h} (crt:zG D) (P:jK) :
    forward crt P=eval₂Hom C (jet crt) (nL P) := by
  have he : (forward crt).toRingHom=(eval₂Hom C (jet crt)).comp nL:= by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [forward,nL,swapCoeffs,aevalTower_C,
        Polynomial.Bivariate.swap_C,Polynomial.map_map]
      rfl
    · rintro (_ | i)
      · simp [forward,nL,swapCoeffs,aevalTower_X,
          Polynomial.Bivariate.swap_Y]
      · simp [nL,jet]
  exact zmU he P
private theorem jet_degree {h} {D:jF h} (crt:zG D) (i:Fin 3) :
    m.degree (jet crt i)=zhf i 1 := by
  classical
  let H :=jH (D.block 0)
  let c:=z75 i.val (q7IA62d.a6h crt)
  let t (j:Fin 3) :Lq:=if j.val≤ i.val then
    C (z75 (i.val - j.val) H)*z9v j else 0
  have hH :H≠0:=((D.monic 0).map _).ne_zero
  have hi:t i=monomial (zhf i 1) H := by
    simp [t,C_mul_X_eq_monomial]
  have hs :0 ≺[m] zhf i 1 :=
    by
      rw [map_zero]
      exact m.toSyn_lt_iff_ne_zero.mpr (by simp)
  have ht (j:Fin 3) (hj:j∈Finset.univ.erase i) :
      m.degree (t j) ≺[m] zhf i 1 := by
    unfold t
    split
    next hle =>
      rw [C_mul_X_eq_monomial]
      refine lt_of_le_of_lt (m.degree_monomial_le _) ?_
      have hj' : j< i:=lt_of_le_of_ne hle (Finset.mem_erase.mp hj).1
      change toLex (Finsupp.equivMapDomain OrderDual.toDual (zhf j 1)) <
        toLex (Finsupp.equivMapDomain OrderDual.toDual (zhf i 1))
      apply Finsupp.Lex.lt_iff.mpr
      refine ⟨OrderDual.toDual i,?_,?_⟩
      · intro k hk
        have hik :i<OrderDual.ofDual k :=hk
        have hi' : OrderDual.toDual i≠k := fun he =>
          (ne_of_lt hik) (congrArg OrderDual.ofDual he)
        have hj'' : OrderDual.toDual j≠k := fun he =>
          (ne_of_lt (hj'.trans hik)) (congrArg OrderDual.ofDual he)
        simp [hi',hj'']
      · simp [ne_of_lt hj']
    next=>simpa using hs
  have hr :m.degree (C c + ∑ j∈Finset.univ.erase i,t j) ≺[m] zhf i 1 := by
    apply lt_of_le_of_lt m.degree_add_le
    apply sup_lt_iff.mpr
    refine ⟨by simpa using hs,lt_of_le_of_lt m.degree_sum_le ?_⟩
    exact (Finset.sup_lt_iff (by simpa using hs)).mpr ht
  have he :jet crt i=t i+(C c + ∑ j∈Finset.univ.erase i,t j) := by
    change forward crt (z9v (some i))= _
    simp only [forward,aevalTower_X,Option.elim_some]
    change C c + ∑ j,t j= _
    rw [← Finset.add_sum_erase _ t (Finset.mem_univ i),add_left_comm]
  have hm:m.degree (t i)=zhf i 1 := by
    rw [hi,m.degree_monomial,ite_eq_right hH]
  have hlt:m.degree (C c + ∑ j∈Finset.univ.erase i,t j) ≺[m] m.degree (t i) := by
    rwa [hm]
  rw [he,m.degree_add_of_lt hlt,hm]
private theorem leading_survives (g:Fin 3→Lq)
   (hg : ∀ i,m.degree (g i)=zhf i 1)
   {P:Lq} (hP:P≠0) :
   m.degree P∈(eval₂Hom C g P).support := by
 classical
 have hg0 (i:Fin 3) :g i≠0 :=
   m.ne_zero_of_degree_ne_zero (by simp [hg])
 let a :=m.degree P
 let term (b:RawExp) :Lq:=C (P.coeff b) * ∏ i∈b.support,g i^b i
 have hterm (b:RawExp) (hb:b∈P.support) :
     term b≠0∧m.degree (term b)=b:= by
   have hc:C (P.coeff b)≠(0:Lq) := by simpa using MvPolynomial.mem_support_iff.mp hb
   have hp: (∏ i∈b.support,g i^b i)≠0 :=
     Finset.prod_ne_zero_iff.mpr fun i _=>pow_ne_zero _ (hg0 i)
   refine ⟨mul_ne_zero hc hp,?_⟩
   change m.degree (C (P.coeff b)*_)=b
   rw [m.degree_mul hc hp,m.degree_C,zero_add,
     m.degree_prod (fun i _=>pow_ne_zero _ (hg0 i))]
   simp only [m.degree_pow,hg,Finsupp.smul_single_one]
   exact Finsupp.sum_single b
 have he :eval₂Hom C g P = ∑ b∈P.support,term b:= by
   conv_lhs=>rw [P.as_sum]
   simp only [map_sum,eval₂Hom_monomial,term,Finsupp.prod]
 rw [zuk,he,coeff_sum,Finset.sum_eq_single_of_mem a (m.degree_mem_support hP)]
 · obtain ⟨hn,hd⟩:=hterm a (m.degree_mem_support hP)
   change (term a).coeff a≠0
   have hc:=m.coeff_degree_ne_zero_iff.mpr hn
   rwa [hd] at hc
 · intro b hb hba
   apply m.coeff_eq_zero_of_lt
   rw [(hterm b hb).2]
   exact lt_of_le_of_ne (m.le_degree hb) (fun h=>hba (m.toSyn.injective h))
private theorem cW6 {h} {D:jF h} (crt:zG D)
   {P:jK} (hP:P≠0) :
   ∃ a∈P.support,a (some 2)=P.degreeOf (some 2)∧jetExp a∈(forward crt P).support := by
 obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr hP
 have hn:nL P≠0 :=
   MvPolynomial.support_nonempty.mp ⟨jetExp e,(grouped_support P _).mpr ⟨e,he,rfl⟩⟩
 obtain ⟨a,ha,hjet⟩ :=
   (grouped_support P _).mp (m.degree_mem_support hn)
 refine ⟨a,ha,le_antisymm (monomial_le_degreeOf _ ha) ?_,?_⟩
 · apply degreeOf_le_iff.mpr
   intro b hb
   have hle :=m.le_degree ((grouped_support P _).mpr ⟨b,hb,rfl⟩)
   rw [← hjet] at hle
   by_contra! hlt
   apply (not_lt_of_ge hle)
   change toLex (Finsupp.equivMapDomain OrderDual.toDual (jetExp a)) <
     toLex (Finsupp.equivMapDomain OrderDual.toDual (jetExp b))
   apply Finsupp.Lex.lt_iff.mpr
   refine ⟨OrderDual.toDual (2 :Fin 3),?_,hlt⟩
   intro j hj
   have hj' : (2 :Fin 3)<OrderDual.ofDual j:=hj
   exact (not_lt_of_ge (Fin.le_last (OrderDual.ofDual j)) hj').elim
 · rw [hjet,forward_eq]
   exact leading_survives _ (jet_degree crt) hn
private def aoe :jK →ₗ[L[X]] ko :=
 (MvPolynomial.mapAlgHom (Algebra.ofId L[X] iP)).toLinearMap
private theorem forward_span {h} {D:jF h} (crt:zG D)
    (s :Set jK) (A:RawExp→Prop)
    (hs : ∀ P∈s,∀ a∈(forward crt P).support,A a)
    {P:jK} (hP:P∈Submodule.span L[X] s) :
    ∀ a∈(forward crt P).support,A a := by
  intro a ha
  by_contra hn
  have hz : (forward crt P).coeff a=0:= by
    have hgen (R:jK) (hR:R∈s) : (forward crt R).coeff a=0 :=
      notMem_support_iff.mp fun hm=>hn (hs R hR a hm)
    clear ha
    induction hP using Submodule.span_induction with
    | mem R hR=>exact hgen R hR
    | zero=>simp
    | add R S _ _ hr hs=>simp [hr,hs]
    | smul d R _ hr =>
      have hd:forward crt (C d)=C (jH d) := by
        simp [forward,aevalTower_C,jH]
      rw [smul_eq_C_mul,map_mul,hd,coeff_C_mul,hr,mul_zero]
  exact MvPolynomial.mem_support_iff.mp ha hz
theorem proof :qAzyIze.c2 := by
 intro h D crt s A hs Q hQ hn
 obtain ⟨d,hd⟩:=multiple_mem_span_of_mem_localization_span
   (nonZeroDivisors L[X]) (R' := iP) _ Q hQ
 change (d:L[X])•Q∈Submodule.span L[X] (aoe '' s) at hd
 rw [← Submodule.map_span] at hd
 obtain ⟨P,hP,he⟩:=hd
 change bC P=(d:L[X])•Q at he
 have hd0:algebraMap L[X] iP d≠0:= by
   simpa only [map_zero] using
     (zxb L[X] iP).ne (nonZeroDivisors.ne_zero d.property)
 have hsup:P.support= Q.support := by
   rw [← support_map_of_injective P (zxb L[X] iP)]
   change (bC P).support= Q.support
   rw [he]
   ext a
   simp only [zuk,coeff_smul]
   rw [Algebra.smul_def]
   exact ⟨right_ne_zero_of_mul,mul_ne_zero hd0⟩
 have hp0:P≠0:=MvPolynomial.support_nonempty.mp (hsup.symm ▸ MvPolynomial.support_nonempty.mpr hn)
 obtain ⟨a,ha,ht,hf⟩:=cW6 crt hp0
 rw [degreeOf_eq_sup,hsup,← degreeOf_eq_sup] at ht
 exact ⟨a,hsup ▸ ha,ht,forward_span crt s A hs hP _ hf⟩
end
end qal8fRb
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa0:gZ! 12 11:=⟨rHi! 259816 12 451 76 78 24 5 2 8 0x900041b7001d5f2c01fd27c110d5ac088ebe2044bcd092b97d1c,trivial⟩
theorem yQa1:gZ! 13 12:=⟨rHi! 259816 13 441 74 78 26 5 2 8 0xf0000f5cb001cf9c2007f487c110d59a4223af9e844bcda74ae70374,trivial⟩
theorem yQa2:gZ! 14 13:=⟨rHi! 259816 14 431 74 78 26 5 3 8 0xf8000e2df001c9257087f45b8110d5604223af66844bcdb04ae82364,trivial⟩
theorem grades2775E:GradeSigns (terminal .daL) 2775 12 ((((P5_7_3.fO.daL).schedule.gw).drop 11).take 3) :=⟨yQa0.1,yQa1.1,yQa2.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa3:gZ! 15 14:=⟨rHi! 259816 15 421 77 78 23 5 4 8 0x8000673a0070a3e10fe82e110d4f8111d76a112f34295d2a70,trivial⟩
theorem yQa4:gZ! 16 15:=⟨rHi! 259816 16 409 76 78 24 5 4 8 0x10002ec1001bc9f021fcfbe110d4d0088ebb5844bcdad2ba9870,trivial⟩
theorem yQa5:gZ! 17 16:=⟨rHi! 259816 17 396 73 78 27 5 5 8 0x53a80006db7e810fe77ce110d49b8111d7636112f391a95d6d822,trivial⟩
theorem grades2775F:GradeSigns (terminal .daL) 2775 15 ((((P5_7_3.fO.daL).schedule.gw).drop 14).take 3) :=⟨yQa3.1,yQa4.1,yQa5.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa6:gZ! 18 17:=⟨rHi! 259816 18 383 77 78 23 5 5 8 0x4980006c3bc10fe6cc110d416111d70a112f36695d9134,trivial⟩
theorem yQa7:gZ! 19 18:=⟨rHi! 259816 19 367 74 78 26 5 4 8 0x809a001abd62087f3328110d3dec223ae0c844bce644aed7974,trivial⟩
theorem yQa8:gZ! 20 19:=⟨rHi! 259816 20 351 77 78 23 5 2 8 0x37260069a0410fe5b0110d354111d6a8112f36c95dcf7e,trivial⟩
theorem grades2775G:GradeSigns (terminal .daL) 2775 18 ((((P5_7_3.fO.daL).schedule.gw).drop 17).take 3) :=⟨yQa6.1,yQa7.1,yQa8.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa9:gZ! 21 20:=⟨rHi! 259816 21 332 74 78 26 5 1 8 0x5dd7001a1e66087f29de110d30cc223ad23844bce284aef566c,trivial⟩
theorem yQa10:gZ! 22 21:=⟨rHi! 259816 22 313 77 78 23 5 12 7 0x2706006742010fe482110d27a111d628112f34e95e0826,trivial⟩
theorem yQa11:gZ! 23 22:=⟨rHi! 259816 23 291 75 78 25 5 11 7 0x801c0066329843f901c110d22684475806112f3582578840c,trivial⟩
theorem grades2775H:GradeSigns (terminal .daL) 2775 21 ((((P5_7_3.fO.daL).schedule.gw).drop 20).take 3) :=⟨yQa9.1,yQa10.1,yQa11.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa12:gZ! 24 23:=⟨rHi! 259816 24 268 75 78 25 5 10 7 0x669c006522c043f8dd4110d1b9844756f2112f33fa578e6f0,trivial⟩
theorem yQa13:gZ! 25 24:=⟨rHi! 259816 25 244 76 78 24 5 9 7 0x9fc8019049021fc5a4110d138088eab0044bcc2d2bca45e,trivial⟩
theorem yQa14:gZ! 26 25:=⟨rHi! 259816 26 217 71 78 29 5 8 7 0x3c80000632113843f89946110d0edc844754f2e112f314125799b7fe,trivial⟩
theorem grades2775I:GradeSigns (terminal .daL) 2775 24 ((((P5_7_3.fO.daL).schedule.gw).drop 23).take 3) :=⟨yQa12.1,yQa13.1,yQa14.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa15:gZ! 27 26:=⟨rHi! 259816 27 190 76 78 24 5 8 7 0x5798018873421fc390110d06e088ea6e844bcb652bcfa1e,trivial⟩
theorem yQa16:gZ! 28 27:=⟨rHi! 259816 28 161 76 78 24 5 7 7 0x3c58018495021fc27e110d002088ea49044bcac92bd22b4,trivial⟩
theorem yQa17:gZ! 29 28:=⟨rHi! 259816 29 130 75 78 25 5 6 7 0x1370006038e043f8322110cfa884475162112f29ca57a8fa4,trivial⟩
theorem grades2775J:GradeSigns (terminal .daL) 2775 27 ((((P5_7_3.fO.daL).schedule.gw).drop 26).take 3) :=⟨yQa15.1,yQa16.1,yQa17.1,trivial⟩
end q5HD6ae
end
section
set_option autoImplicit true
namespace q5HD6ae
open qqf9uAa (GradeSigns)
open P5_7_3 (terminal)
open scoped q5HD6ae
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .daL) 2775 e ((((P5_7_3.fO.daL).schedule.gw).drop a).take 1)
theorem yQa18:gZ! 30 29:=⟨rHi! 259816 30 98 75 78 25 5 6 7 0xb60005f490843f8122110cf420447503e112f274a57ad90e,trivial⟩
theorem yQa19:gZ! 31 30:=⟨rHi! 259816 31 64 72 78 28 5 5 7 0xb95801798eb821fbfb4e110ceee3088e9ec4844bc97a92bd8e0fa,trivial⟩
theorem yQa20:gZ! 32 31:=⟨rHi! 259816 32 29 72 78 28 5 5 7 0x4ad80175f0e421fbec88110ce8fc088e9ca6044bc8e452bdaf33c,trivial⟩
theorem grades2775K:GradeSigns (terminal .daL) 2775 30 (((P5_7_3.fO.daL).schedule.gw).drop 29) :=⟨yQa18.1,yQa19.1,yQa20.1,trivial⟩
end q5HD6ae
end
