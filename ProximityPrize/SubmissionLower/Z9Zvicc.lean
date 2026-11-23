import ProximityPrize.SubmissionLower.Zqby9gc
import ProximityPrize.SubmissionLower.ZJ6ikSc
import ProximityPrize.SubmissionLower.ZdY8S8d
import ProximityPrize.SubmissionLower.Z1LucWb
import ProximityPrize.SubmissionLower.ZeFzsob
import ProximityPrize.SubmissionLower.Z67mtTa
import ProximityPrize.SubmissionLower.ZIe8dlc
set_option Elab.async false
section
set_option autoImplicit true
namespace q4bstwa
open P6_7_3 (afa stages introductions)
open qxWWUna (Bank)
abbrev AuxIndex :=Fin introductions.length
def free (i:afa) :Bank :=
  ⟨(stages.get i).free,(stages.get i).dI,
    (![0x1342ad480,0x1ae596429,0x52439b5a0,0x573ae3b5d,
     0x3de2463a9b,0x74a93d5f73,0xc60647effb,0x1d500dd37ee] :Fin 8→ℕ) i⟩
def moving (i:afa) :Bank :=
  ⟨(stages.get i).moving,(stages.get i).dI,
    (![0x68363e1ac7148,0x9e2810eb7bc00,0x10ace9333bae0b,0x233074911d1e46,
     0x44ca13ab9f6674,0xbec699394785ea,0x34add7c48a29170,0x5ddf1a3808d2418] :Fin 8→ℕ) i⟩
def aux (i:AuxIndex) :Bank :=
  ⟨(introductions.get i).2,(introductions.get i).1,
    (![0x7ac78e5c6,0x10ce0e5be0,0x22234bc026,0x160fb58dfd,
     0x4f19d62d6c,0x428435ea19,0x71d350ce44,0xe954067900,
     0x11c140853d3,0x1ae596429,0x573ae3b5d,0x1b96ae90768,
     0x1c7c7f86adb] :Fin 13→ℕ) i⟩
end q4bstwa
end
section
set_option autoImplicit true
namespace q4bstwa
open Finset
open P6 (dw p)
open P6_7_3 (afa lo hi)
open qxWWUna (Bank Tests count O3 j3)
open qZyoMPc (aP4 bound)
open cu (triangle ku)
open DP (bga)
open czX (a8x dei)
open private row aJm level cck from ProximityPrize.SubmissionLower.E7
open private total asB from ProximityPrize.SubmissionLower.Z07A6ec
open private bid from ProximityPrize.SubmissionLower.CN
open private cA5 origin worst gq1 from ProximityPrize.SubmissionLower.ZdY8S8d
private def signedTotal (b:Bank) (mode :ℕ) (h:ℤ) :ℤ :=
  total b.shape (2*origin b h) (-2*(131071-h)) (1-2*mode*h)
private theorem total_le (b:Bank) (mode h:ℕ) (hh:h≤131071) (hJ:b.shape.J≤b.shape.B+1) :
    (triangle b.shape.U:ℤ)*signedTotal b mode h≤12*(O3 h b mode :ℤ) := by
  unfold signedTotal O3 ku
  push_cast
  rw [asB _ _ _ _ hJ]
  have hsum: (∑ q∈range (b.shape.B+1),
      row (2*origin b h) (-2*(131071-(h:ℤ))) (1-2*mode*(h:ℤ)) q (min q b.shape.J+1)) ≤
    2 * ∑ q∈range (b.shape.B+1),∑ j∈range (min q b.shape.J+1),
      ((count h b+j-q*(131071-h)-mode*(2*h*j) :ℕ) :ℤ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro q _
    rw [show row (2*origin b h) (-2*(131071-(h:ℤ))) (1-2*mode*(h:ℤ)) q (min q b.shape.J+1) =
        2 * ∑ j∈range (min q b.shape.J+1),
          (origin b h-(131071-(h:ℤ))*q+(1-2*mode*(h:ℤ))*j) by
      rw [bid]
      unfold row
      ring]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _=>gq1 b h mode q j hh) (by decide)
  have hb:=mul_le_mul_of_nonneg_left hsum
    (show 0≤6*(triangle b.shape.U:ℤ) from mul_nonneg (by decide) (Int.natCast_nonneg _))
  convert hb using 1 <;> ring
private def score (b:Bank) (mode :ℕ) (h:ℤ) :ℤ :=
  (triangle b.shape.U:ℤ) *
      (signedTotal b mode h - 2*(262144*a8x (b.shape.m-2*b.shape.J) b.shape.J:ℕ)) -
    24*h*b.DG
private theorem test (b:Bank) (mode h:ℕ) (hl:lo≤h) (hu:h≤hi)
    (hj:b.shape.J≤b.shape.B) (hu' : b.shape.B≤b.shape.U) (hp:b.shape.B<K1.p)
    (hd:aP4 b.shape.B b.shape.J b.shape.U≤2880*(b.DG:ℤ))
    (hm:2*b.shape.J≤b.shape.m) (hB:b.shape.m+b.shape.J≤b.shape.B+1)
    (hw₀:0<worst b lo) (hw₁:0<worst b hi)
    (hs₀:0<score b mode lo) (hs₁:0<score b mode hi) :
    Tests h b mode := by
  have hli: (lo:ℤ)≤h:=Int.ofNat_le.mpr hl
  have hui: (h:ℤ)≤hi:=Int.ofNat_le.mpr hu
  have hh:=hu.trans (show hi≤131071 by decide)
  have wa (t:ℤ) :worst b t=worst b lo+(t-(lo:ℤ))*((b.shape.B:ℤ)-2*b.dI) := by
    unfold worst origin
    ring
  have sa (t:ℤ) :score b mode t=score b mode lo+(t-(lo:ℤ))*(score b mode (lo+1)-score b mode lo) := by
    unfold score signedTotal total aJm level origin
    ring
  rw [wa] at hw₁
  rw [sa (hi:ℤ)] at hs₁
  have hw:=(wa h).symm ▸ cck hli hui hw₀ hw₁
  have hs :=(sa h).symm ▸ cck hli hui hs₀ hs₁
  unfold worst origin at hw
  have hn:0≤(131071-(h:ℤ))*(b.shape.B:ℤ) :=
    mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
  have hbuf :2*h*b.dI≤b.shape.m*dw:= by
    apply Int.ofNat_le.mp
    push_cast
    rw [cA5] at hw
    linarith only [hw,hn]
  have hwidth :b.shape.B*(131071-h)<count h b:= by
    apply Int.ofNat_lt.mp
    unfold count
    push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
    rw [cA5] at hw
    linarith only [hw]
  have hnode :=congrArg (fun n:ℕ=>(n:ℤ)) (dei b.shape hm hB)
  have hphys :bga b.shape=triangle b.shape.U*agU.ad1 b.shape := by
    unfold bga agU.ad1
    rw [Nat.mul_assoc]
  have hJ:b.shape.J≤b.shape.B+1 :=(Nat.le_add_left _ _).trans hB
  have ht:=total_le b mode h hh hJ
  refine ⟨hj,hu',hp,bound _ _ hj hu' hd,hwidth,Int.ofNat_lt.mp ?_⟩
  unfold score at hs
  rw [← hnode] at hs
  unfold j3
  rw [hphys]
  push_cast at hs ⊢
  linarith only [hs,ht]
local notation "test!" => test _ _ _ ‹lo≤_› ‹_≤hi›
  (by decide) (by decide) (by decide) (of_decide_eq_true rfl)
  (by decide) (by decide) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
  (of_decide_eq_true rfl) (of_decide_eq_true rfl)
theorem free_test {h:ℕ} (hl:lo≤h) (hu:h≤hi) (i:afa) :
    Tests h (free i) 0:= by
  fin_cases i <;> exact test!
theorem moving_test {h:ℕ} (hl:lo≤h) (hu:h≤hi) (i:afa) :
    Tests h (moving i) 1 := by
  fin_cases i <;> exact test!
theorem aux_test {h:ℕ} (hl:lo≤h) (hu:h≤hi) (i:AuxIndex) :
    Tests h (aux i) 0:= by
  fin_cases i <;> exact test!
theorem ddk (i:afa) : (free i).shape.U<p:= by
  fin_cases i <;> decide
end q4bstwa
end
section
set_option autoImplicit true
set_option Elab.async false
set_option maxSynthPendingDepth 8
namespace q3sDcEa
noncomputable section
open P6_7_3 (Input Poles akE afa stages introductions buffer cutoff emz lo hi)
open qxWWUna (Bank count)
open q4bstwa
open cu (Jet)
open qdY8S8d (ofTests)
private theorem height (x :Input) :0<x.h∧x.h≤131070 :=
  ⟨(show 0<lo by decide).trans_le (emz x).1,
   (emz x).2.trans (show hi≤131070 by decide)⟩
private theorem buffer_eq (h:ℕ) (b:Bank) :
    buffer h b.dI b.shape=count h b - 1 := by
  unfold count buffer cutoff
  omega
private theorem pick_pair {x :Input} (P:Poles x) (i:afa) :
    Nonempty (akE x.h P.rows (stages.get i)) := by
  obtain ⟨Q,R,hQ,hR,hn,hn',ha⟩:=qdY8S8d.pick_pair P.crt x.word (height x).1 (height x).2
    (ofTests (free_test (emz x).1 (emz x).2 i))
    (ofTests (moving_test (emz x).1 (emz x).2 i)) (ddk i)
  rw [← buffer_eq] at hQ hR
  exact ⟨⟨Q,R,hn,hn',hQ,hR,ha⟩⟩
theorem proof :P6_7_3.c2 := by
  classical
  intro x P
  let main (i:afa) :=Classical.choice (pick_pair P i)
  have hex (i:AuxIndex) : ∃ Q∈P.rows (aux i).shape (buffer x.h (aux i).dI (aux i).shape),
      Q≠0:= by
    rw [buffer_eq]
    exact qdY8S8d.bVl P.crt x.word (height x).1 (height x).2
      (ofTests (aux_test (emz x).1 (emz x).2 i))
  let introRow (i:AuxIndex) :Jet :=
    if i=⟨9,by decide⟩ then (main ⟨1,by decide⟩).free
    else if i=⟨10,by decide⟩ then (main ⟨3,by decide⟩).free
    else Classical.choose (hex i)
  have ha (i:AuxIndex) :
      introRow i∈P.rows (aux i).shape (buffer x.h (aux i).dI (aux i).shape)∧introRow i≠0:= by
    unfold introRow
    split_ifs with h9 Kr
    · subst i
      exact ⟨(main ⟨1,by decide⟩).free_mem,(main ⟨1,by decide⟩).free_ne⟩
    · subst i
      exact ⟨(main ⟨3,by decide⟩).free_mem,(main ⟨3,by decide⟩).free_ne⟩
    · exact Classical.choose_spec (hex i)
  refine ⟨⟨main,introRow,fun i=>(ha i).2,?_,?_⟩⟩
  · intro i
    have hm:=(ha i).1
    cases e :introductions.get i with
    | mk r s=>simpa only [aux,e] using hm
  · constructor <;> simp [introRow]
end
end q3sDcEa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qFOgTpd
noncomputable section
open Finset
open P6 (p)
open P6_7_3
open cu (Jet Shape)
open pI (oU)
open TD (auN arC aIe)
open akZ (ajz aHP weightedDegree cs5 bCj)
open scoped Classical
abbrev RY:Shape :=⟨0,373,69,5507⟩
def box (i:IntroIndex) :Shape :=
  if h:i.val<last then shape ⟨i.val,h⟩ else RY
theorem box_J (i:IntroIndex) : (box i).J≤(box i).B:= by
  fin_cases i <;> decide
theorem introCap_succ (i:Intro) (j:Fin 3) :
    introCap (i.val+1) j=min (introCap i.val j) (auN (shape i) j/(dI i+1)) := by
  unfold introCap
  rw [List.take_succ_eq_append_getElem i.isLt,List.foldl_append]
  rfl
theorem enclose_last {f c:Jet} (h : ∀ j,wD f j≤ introCap last j) (l:Bool)
    (hc:oU c (if l then akZ.btm f else aOm f)) :
    oU c RY:= by
  have hb:wD f 0≤12 :=(h 0).trans_eq (by decide)
  have hj:wD f 1≤2 :=(h 1).trans_eq (by decide)
  have hu:wD f 2≤130:=(h 2).trans_eq (by decide)
  apply (bCj _ _).mpr
  intro i
  refine ((bCj _ _).mp hc i).trans ?_
  cases l <;> fin_cases i
  · change 164+19*(wD f 0-1)≤373
    omega
  · change 50+19*(wD f 1-1)≤69
    omega
  · change 3037+19*wD f 2≤5507
    omega
  · exact hb.trans (by decide)
  · exact hj.trans (by decide)
  · exact hu.trans (by decide)
private def account (k :Fin 4) :List (ℕ×Shape)→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [],cap,old=>aIe cap old RY k
  | (r,s) :: next,cap,old =>
    aIe cap old s k+account k next
      (fun j=>min (cap j) (auN s j/(r+1)))
      (fun j=>max (old j) (arC s k j))
abbrev massCap:Fin 4→ℕ := ![8395,111824,528999,3163477]
private theorem account_cap (k :Fin 4) :
    account k introductions (introCap 0) (fun _=>0)≤ massCap k := by
  fin_cases k <;> decide
theorem mass_small (k :Fin 4) :massCap k<p:= by
  fin_cases k <;> decide
theorem charge (D:Finset Jet) (origin :Jet→ IntroIndex)
    (nest : ∀ i≤last,∀ j,ajz (D.filter (fun f=>i≤(origin f).val)) j≤ introCap i j)
    (k :Fin 4) :
    (∑ f∈D,aHP (box (origin f)) k f)≤ massCap k := by
  let tail (n:ℕ) :=D.filter fun f=>n≤(origin f).val
  have bound : ∀ ls n,introductions.drop n=ls→n≤last → ∀ old,
      (∑ f∈tail n,aHP (box (origin f)) k f) ≤
        account k ls (introCap n) old+weightedDegree old (tail n) := by
    intro ls
    induction ls with
    | nil =>
      intro n he hn old
      have eq :n=last := by
        have hh:=congrArg List.length he
        simp only [List.length_drop,List.length_nil] at hh
        change last-n=0 at hh
        omega
      subst n
      have hbox (f :Jet) (hf :f∈tail last) :box (origin f)=RY :=
        dite_eq_right (Nat.not_lt_of_ge (mem_filter.mp hf).2)
      have ht:=cs5 (D:=tail last) (T := ∅) (empty_subset _) _ old RY k (nest _ le_rfl)
      simp only [sdiff_empty,weightedDegree,ajz,sum_empty,mul_zero,
        sum_const_zero,add_zero] at ht
      rw [sum_congr rfl (fun f hf=>congrArg (fun s=>aHP s k f) (hbox f hf))]
      simpa only [account,weightedDegree,ajz,add_comm] using ht
    | cons a ls ih =>
      intro n he hn old
      have hlt:n<last := by
        have hh:=congrArg List.length he
        simp only [List.length_drop,List.length_cons] at hh
        change last-n=ls.length+1 at hh
        omega
      let i:Intro:=⟨n,hlt⟩
      rw [List.drop_eq_getElem_cons hlt] at he
      obtain ⟨rfl,hrest⟩:=List.cons.inj he
      have hsub:tail (n+1)⊆tail n:= fun f hf =>
        let hf' := mem_filter.mp hf
        mem_filter.mpr ⟨hf'.1,(Nat.le_succ n).trans hf'.2⟩
      have hbox (f :Jet) (hf :f∈tail n \ tail (n+1)) :
          box (origin f)=shape i:= by
        obtain ⟨h₁,h₂⟩:=mem_sdiff.mp hf
        obtain ⟨hD,h₁⟩:=mem_filter.mp h₁
        have heq : (origin f).val=n:= by
          have h₃ : ¬ n+1≤(origin f).val := fun h=>h₂ (mem_filter.mpr ⟨hD,h⟩)
          omega
        unfold box
        rw [dite_eq_left (heq.symm ▸ hlt)]
        exact congrArg shape (Fin.ext heq)
      let w:= fun j=>max (old j) (arC (shape i) k j)
      have step:=cs5 hsub (introCap n) old (shape i) k (nest n hn)
      have rest:=ih (n+1) hrest (Nat.succ_le_of_lt hlt) w
      have hcap:introCap (n+1)=fun j =>
          min (introCap n j) (auN (shape i) j/(dI i+1)) :=
        funext (introCap_succ i)
      rw [hcap] at rest
      calc
        _=(∑ f∈tail n \ tail (n+1),aHP (shape i) k f) +
            ∑ f∈tail (n+1),aHP (box (origin f)) k f := by
          rw [← sum_sdiff hsub]
          congr 1
          exact sum_congr rfl fun f hf=>congrArg (fun s=>aHP s k f) (hbox f hf)
        _≤_:= by
          let a := ∑ f∈tail n \ tail (n+1),aHP (shape i) k f
          let c:=account k ls (fun j=>min (introCap n j) (auN (shape i) j/(dI i+1))) w
          let d:=aIe (introCap n) old (shape i) k
          change a+_≤d+c+weightedDegree old (tail n)
          calc
            _≤a+(c+weightedDegree w (tail (n+1))) :=Nat.add_le_add_left rest _
            _=c+(a+weightedDegree w (tail (n+1))) := by ac_rfl
            _≤ c+(weightedDegree old (tail n)+d) :=Nat.add_le_add_left step _
            _ = _:= by ac_rfl
  have h:=bound introductions 0 rfl (Nat.zero_le _) (fun _=>0)
  have htail:tail 0=D:=Finset.filter_true_of_mem fun f _=>Nat.zero_le _
  rw [htail] at h
  exact (by simpa [weightedDegree] using h:_≤account k introductions (introCap 0) _)
    |>.trans (account_cap k)
end
end qFOgTpd
end
section
set_option autoImplicit true
namespace qUrGXob
noncomputable section
open Finset Polynomial
open P6 (K blockLength)
open P5_7 (farAgreement)
open P6_7_3 (Input Poles Picks degree emz movingOrder)
open TD (aBh)
open baX (mix)
open gT (tK FW)
open pI (abM aaS d2l)
open aF0 (BJ YM)
open private cSy from ProximityPrize.SubmissionLower.Z6ykYva
open scoped BigOperators
private def marks (x :Input) (G:tK) :Finset K:= by
  classical
  exact x.Γ.filter fun γ=>FW G (x.F.scalar γ)=0
private def uq (B J:ℕ) :ℕ :=
  2*((B-J)*YM degree B J+J*BJ degree B)+B^2
private theorem gH (x :Input) {B J:ℕ} (g:aBh B J)
    (G:tK) (hG:abM G B J) : (marks x G).card≤uq B J:= by
  classical
  let T:=marks x G
  have hsub:T⊆x.Γ:=filter_subset _ _
  have hdeg (γ) (hγ:γ∈T) : (x.F.scalar γ).natDegree≤degree := by
    exact (P6_7.aic x.F (hsub hγ)).trans
      (Nat.add_le_add_left (emz x).2 _)
  let a :=BJ degree B
  let v :=YM degree B J
  let β:ℚ:=((blockLength - farAgreement:ℕ) :ℚ)/(farAgreement - degree :ℕ)
  have hva :v≤a :=min_le_left _ _
  have hq: (0:ℚ)<((farAgreement - degree :ℕ) :ℚ) := by
    exact_mod_cast (show 0<farAgreement - degree by decide)
  have hβ:β≤2 :=(div_le_iff₀ hq).mpr (by
    exact_mod_cast (show blockLength - farAgreement≤2*(farAgreement - degree) by decide))
  have hscale (b j:ℕ) :mix b j (2*a) (2*v)=2*mix b j a v := by
    unfold mix
    ring
  have h:=cSy (x.F.distinct.mono hsub) g G hG
    (fun γ hγ=>(mem_filter.mp hγ).2) (2*a) (2*v) (by positivity)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hva) (by decide : (0:ℚ)≤2))
    (fun U hU f hf hp hB hJ hreg=> by
      have hc:=qUJtx6c.ePE (x.F.distinct.mono (hU.trans hsub))
        (fun γ hγ=>hdeg γ (hU hγ)) (fun γ hγ =>
          let mark :=x.F.mark γ (hsub (hU hγ))
          ⟨mark.bad.support,(show farAgreement≤P6.dw by decide).trans
            mark.bad.dw,mark.scalar_hits⟩)
        (by decide :2≤degree) (by decide :degree<farAgreement) g.jpos f hf hp hB hJ hreg
      have hnonneg:0≤ mix f.totalDegree (f.degreeOf 1) a v := by
        unfold mix
        positivity
      rw [hscale]
      exact hc.trans (add_le_add (mul_le_mul_of_nonneg_right hβ hnonneg) le_rfl))
  rw [hscale] at h
  have hcast: (T.card:ℚ)≤(uq B J:ℚ) := by
    simpa only [uq,mix,a,v,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  exact_mod_cast hcast
private theorem pair_price (i:Fin movingOrder.length) :
    let s :=stage (movingStage i)
    aBh s.free.B s.free.J∧aBh s.moving.B s.moving.J ∧
      uq s.free.B s.free.J+uq s.moving.B s.moving.J≤0x1a821748fa0:= by
  fin_cases i <;> exact ⟨⟨by decide,by decide,by decide,by decide⟩,
    ⟨by decide,by decide,by decide,by decide⟩,by decide⟩
theorem fixed_book (x :Input) (P:Poles x) (pick :Picks x.h P.rows)
    (R:bQX pick) :
    ∃ F:Finset K,F.card≤au1 ∧
      ∀ γ∈x.Γ,∀ I,onMark x I γ → ¬ clean R I→γ∈F:= by
  classical
  let left:= fun i=>(R.free (movingStage i)).equation
  let right:= fun i=>(R.moving (movingStage i)).equation
  let pair := fun i=>marks x (left i)∪marks x (right i)
  refine ⟨univ.biUnion pair,?_,?_⟩
  · calc
      _ ≤ ∑ i,(pair i).card:=card_biUnion_le
      _ ≤ ∑ _i:Fin movingOrder.length,(0x1a821748fa0:ℕ) := by
        apply sum_le_sum
        intro i _
        obtain ⟨hf,hm,hprice⟩:=pair_price i
        apply (card_union_le _ _).trans
        exact (Nat.add_le_add (gH x hf _ (R.free (movingStage i)).equation_caps)
          (gH x hm _ (R.moving (movingStage i)).equation_caps)).trans hprice
      _=4*0x1a821748fa0:= by
        have hlength:movingOrder.length=4 :=rfl
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hlength,Nat.cast_ofNat]
      _≤au1 := by decide
  · intro γ hγ I hmark hbad
    have hz (G:tK) (hG:aaS G I) :FW G (x.F.scalar γ)=0:= by
      simpa only [d2l] using RingHom.mem_ker.mp (hmark hG)
    unfold clean at hbad
    push Not at hbad
    obtain ⟨i,hi⟩:=hbad
    refine mem_biUnion.mpr ⟨i,mem_univ _,?_⟩
    by_cases h:aaS (left i) I
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hz _ h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,hz _ (hi h)⟩)
end
end qUrGXob
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace qUrGXob
noncomputable section
open Finset
open P6 (K)
open P6_7_3 (Input Poles Picks OriginCover IntroIndex prefixFee terminal)
open cu (Jet)
open gT (Ambient)
open pI (xN acW dual mass pN)
open TD (GM J2 FP)
open ac6.Bridge (aQF cbq)
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (x :Input) (P:Poles x) (pick :Picks x.h P.rows)
    (R:bQX pick) (O:OriginCover x (pick.main ⟨0,by decide⟩).free),
    Geometry R O
def c2 :Prop :=
  ∀ (x :Input) (o:IntroIndex) (S:Finset (Ideal Ambient)),
    (∀ I∈S,xN I ∧ ¬ dual I ∧
      ∀ k,(pN I k :ℚ)≤ min (originBox o k) (initialBound k)) →
    ((rankMarks x S).card:ℚ)≤FP (rankPrice o) (J2 S)
def c3:Prop :=
  ∀ (x :Input) (_P:Poles x) (C:acW) (d a b:ℚ),
    aSz d a b→(C.cost 0:ℚ)≤d →
    ((onCurves x C).card:ℚ)≤(a+1)*C.cost 0+b*C.cost 1
def c4 :Prop :=Nonempty cL
private theorem dot_mass (v :GM) (S:Finset (Ideal Ambient)) :
    FP v (J2 S) = ∑ I∈S,FP v (fun k=>pN I k) := by
  simp only [FP,J2,mass,Nat.cast_sum,mul_sum]
  exact sum_comm
private theorem weight_nonneg (j:Fin 3) (t:Trial) (k :Fin 4) :
    0≤SS j t k :=Nat.cast_nonneg _
private theorem charge_nonneg (j:Fin 3) (t:Trial) (S:Finset (Ideal Ambient)) :
    0≤FP (SS j t) (J2 S) :=
  TD.dYm (weight_nonneg j t) (TD.cZV S)
private theorem card_union_q (A B:Finset K) : ((A∪B).card:ℚ)≤A.card+B.card:= by
  exact_mod_cast card_union_le A B
private theorem card_biUnion_q {α:Type*} (A:Finset α) (B:α→Finset K) :
    ((A.biUnion B).card:ℚ) ≤ ∑ a∈A,((B a).card:ℚ) := by
  exact_mod_cast (card_biUnion_le : (A.biUnion B).card≤_)
private theorem dSG (h:c3) (x :Input) (P:Poles x) (C:acW) (d a b:ℚ)
    (hr :aSz d a b) (hd: (C.cost 0:ℚ)≤d)
    (q:Fin 3→ℚ) (hq : ∀ j,(C.cost j:ℚ)≤q j) :
    ((C.direct∪onCurves x C).card:ℚ)≤a*q 0+b*q 1+q 0+q 2 := by
  have ha :0≤a :=hr.1.trans ((le_max_left _ _).trans hr.2.2.1)
  have hA:=mul_le_mul_of_nonneg_left (hq 0) ha
  have hB:=mul_le_mul_of_nonneg_left (hq 1) hr.2.2.2.1
  have hC:=h x P C d a b hr hd
  have hD: (C.direct.card:ℚ)≤q 2 :=hq 2
  have hu:=card_union_q C.direct (onCurves x C)
  nlinarith only [hA,hB,hC,hD,hu,hq 0]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_7_3.c5:= by
  classical
  intro x P pick O
  let R:=chooseFixed P pick
  obtain ⟨F,hF,hclean⟩:=fixed_book x P pick R
  let G:=h1 x P pick R O
  let B:=Az R O G
  obtain ⟨D⟩:=h4
  obtain ⟨hdegree,hpoint,hdual⟩:=D.bills B
  let stoppedAt (f :Jet) (t:Trial) :=stopped R O f t.succ
  let C (t:Trial) (I:Ideal Ambient) :acW :=
    if h:xN I ∧ ¬ passes pick t I then Classical.choose (cut_at_failure P pick t h.1 h.2)
    else pI.b1w
  have origin_mem {f :Jet} {s :bAL} {I:Ideal Ambient} (hI:I∈stopped R O f s) :
      I∈O.parents f :=(mem_filter.mp (stopped_sub R O s hI)).1
  have cut_spec (f :Jet) (hf :f∈O.factors) (t:Trial) (I:Ideal Ambient)
      (hI:I∈stoppedAt f t) :
      (∀ j,((C t I).cost j:ℚ)≤FP (SS j t) (fun k=>pN I k)) ∧
      ∀ γ∈x.Γ,onMark x I γ→γ∈(C t I).direct∨γ∈onCurves x (C t I) := by
    have ha :=(O.geometric f hf I (origin_mem hI)).1
    have hn : ¬ passes pick t I:= by
      change I∈stopped R O f t.succ at hI
      rw [stopped_succ] at hI
      exact (mem_filter.mp hI).2
    simpa only [C,dite_eq_left (And.intro ha hn)] using
      Classical.choose_spec (cut_at_failure P pick t ha hn)
  let W (f :Jet) (t:Trial) (j:Fin 3) :=FP (SS j t) (J2 (stoppedAt f t))
  have htotal (f :Jet) (hf :f∈O.factors) (t:Trial) :W f t 0≤projectionBound:= by
    have h₁:=single_le_sum (f := fun s=>W f s 0)
      (fun s _=>charge_nonneg 0 s (stoppedAt f s)) (mem_univ t)
    have h₂:=single_le_sum (f := fun a => ∑ s :Trial,W a s 0)
      (fun a _=>sum_nonneg fun s _=>charge_nonneg 0 s (stoppedAt a s)) hf
    exact h₁.trans (h₂.trans hdegree)
  let Hj (f :Jet) (t:Trial) :=
    (stoppedAt f t).biUnion fun I=>(C t I).direct∪onCurves x (C t I)
  have hlost (f :Jet) (hf :f∈O.factors) (t:Trial) :
      ((Hj f t).card:ℚ) ≤
        D.a (O.origin f) t*W f t 0+D.b (O.origin f) t*W f t 1 +
        W f t 0+W f t 2 := by
    classical
    let o:=O.origin f
    let a :=D.a o t
    let b:=D.b o t
    have hd (I:Ideal Ambient) (hI:I∈stoppedAt f t) :
        ((C t I).cost 0:ℚ)≤D.d o t:= by
      have his :=(cut_spec f hf t I hI).1 0
      have hs :FP (SS 0 t) (fun k=>pN I k)≤W f t 0:= by
        unfold W
        rw [dot_mass]
        exact single_le_sum (fun J _=>TD.dYm (weight_nonneg 0 t)
          (fun k=>Nat.cast_nonneg (pN J k))) hI
      have ha :=(O.geometric f hf I (origin_mem hI)).1
      exact (le_min (his.trans (hs.trans (htotal f hf t))) his).trans
        (D.directional o t _ ha.seed_size.1 (G.member f hf t I (stopped_sub R O t.succ hI)))
    calc
      _ ≤ ∑ I∈stoppedAt f t,(((C t I).direct∪onCurves x (C t I)).card:ℚ) :=
        card_biUnion_q _ _
      _ ≤ ∑ I∈stoppedAt f t,
          (a*FP (SS 0 t) (fun k=>pN I k) +
            b*FP (SS 1 t) (fun k=>pN I k) +
            FP (SS 0 t) (fun k=>pN I k) +
            FP (SS 2 t) (fun k=>pN I k)) :=
        sum_le_sum fun I hI=>dSG h3 x P (C t I) (D.d o t) a b (D.bgt o t)
          (hd I hI) (fun j=>FP (SS j t) (fun k=>pN I k))
          (cut_spec f hf t I hI).1
      _ = _:= by simp only [W,o,a,b,sum_add_distrib,← mul_sum,← dot_mass]
  let rank f :=rankMarks x (stopped R O f 0)
  let booked f :=(O.lineMarks f∪rank f)∪univ.biUnion (Hj f)
  have hbooked (f :Jet) (hf :f∈O.factors) :
      ((booked f).card:ℚ) ≤
        lineCharge f (O.line f) +
        (∑ s :bAL,FP (stopPrice D.a D.b (O.origin f) s) (B.stops f s)) +
        (∑ t:Trial,W f t 0) + ∑ t:Trial,W f t 2 := by
    have hline :=(Nat.cast_le (α:=ℚ)).mpr (O.line_bound f hf)
    have hrank :=h2 x (O.origin f) (stopped R O f 0) (fun I hI=> by
      refine ⟨(O.geometric f hf I (origin_mem hI)).1,?_,G.rank f hf I hI⟩
      rw [stopped_zero] at hI
      exact (mem_filter.mp hI).2)
    have hL:=(card_biUnion_q univ (Hj f)).trans
      (sum_le_sum fun t _=>hlost f hf t)
    have hu:=card_union_q (O.lineMarks f∪rank f) (univ.biUnion (Hj f))
    have hu' := card_union_q (O.lineMarks f) (rank f)
    rw [Fin.sum_univ_succ]
    simp only [stopPrice,Fin.cases_zero,Fin.cases_succ,B,Az] at ⊢
    change _≤_+(_ + ∑ t:Trial,FP (fun k =>
        D.a (O.origin f) t*SS 0 t k+D.b (O.origin f) t*SS 1 t k)
        (J2 (stoppedAt f t)))+_+_
    simp only [← TD.cK6]
    change (_:ℚ)≤lineCharge f (O.line f) +
      (FP (rankPrice (O.origin f)) (J2 (stopped R O f 0)) +
        ∑ t:Trial,(D.a (O.origin f) t*W f t 0+D.b (O.origin f) t*W f t 1)) +
      (∑ t,W f t 0) + ∑ t,W f t 2
    simp only [sum_add_distrib] at hL ⊢
    change (_:ℚ)≤lineCharge f (O.line f) at hline
    change ((rank f).card:ℚ)≤_ at hrank
    change ((booked f).card:ℚ)≤_ at hu
    linarith only [hline,hrank,hL,hu,hu']
  let charged:=O.factors.biUnion booked
  have hcharged:charged.card≤dualFee+projectionFee+pointFee := by
    have hs :=(card_biUnion_q _ _).trans (sum_le_sum fun f hf=>hbooked f hf)
    simp only [sum_add_distrib] at hs
    have hpay :=hdegree.trans D.projection
    change ((charged.card:ℚ)≤_) at hs
    change (∑ f∈O.factors,∑ t,W f t 0)≤(projectionFee :ℚ) at hpay
    change (∑ f∈O.factors,∑ t,W f t 2)≤(pointFee :ℚ) at hpoint
    change (∑ f∈O.factors,(lineCharge f (O.line f) +
      ∑ s :bAL,FP (stopPrice D.a D.b (O.origin f) s) (B.stops f s)))≤(dualFee :ℚ) at hdual
    simp only [sum_add_distrib] at hdual
    have ht: (charged.card:ℚ)≤(dualFee :ℚ)+projectionFee+pointFee := by
      linarith only [hs,hpay,hpoint,hdual]
    exact_mod_cast ht
  let book :=(O.gH∪F)∪charged
  have hb:book.card≤prefixFee :=
    ((card_union_le _ _).trans (Nat.add_le_add
      ((card_union_le _ _).trans (Nat.add_le_add O.paid_bound hF)) hcharged)).trans (by decide)
  let V:=O.factors.biUnion (final R O)
  have final_mem {I:Ideal Ambient} (hI:I∈V) :
      xN I∧I.height=2∧dual I∧inBank P.rows terminal I:= by
    obtain ⟨f,hf,hfin⟩:=mem_biUnion.mp hI
    obtain ⟨hp,_,hd,ht⟩:=mem_filter.mp hfin
    obtain ⟨ha,hh,_,_⟩:=O.geometric f hf I hp
    exact ⟨ha,hh,hd,ht (11 :Trial)⟩
  let aI (I:V) :=aQF I.val (final_mem I.property).1.prime
  refine ⟨⟨book,hb,V.attach.image aI,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨I,_,rfl⟩:=mem_image.mp hq
    obtain ⟨ha,hh,hd,_⟩:=final_mem I.property
    exact cbq ha hh hd
  · intro q hq
    obtain ⟨I,_,rfl⟩:=mem_image.mp hq
    exact (final_mem I.property).2.2.2
  · intro γ hγ
    by_cases h:γ∈book
    · exact Or.inl h
    have hno (f :Jet) (hf :f∈O.factors) (hm:γ∈booked f) :False :=
      h (mem_union_right _ (mem_biUnion.mpr ⟨f,hf,hm⟩))
    rcases O.Eh γ hγ with hp | ⟨f,hf,hl | ⟨I,hi,hm⟩⟩
    · exact (h (mem_union_left _ (mem_union_left _ hp))).elim
    · exact (hno f hf (mem_union_left _ (mem_union_left _ hl))).elim
    have hc:clean R I:= by
      by_contra hn
      exact h (mem_union_left _ (mem_union_right _ (hclean γ hγ I hm hn)))
    rcases placed R O hi hc with ⟨s,hs⟩ | hv
    · exfalso
      apply hno f hf
      induction s using Fin.cases with
      | zero =>
        exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hγ,I,hs,hm⟩))
      | succ t =>
        have hc:=(cut_spec f hf t I hs).2 γ hγ hm
        have hm' : γ∈(C t I).direct∪onCurves x (C t I) :=mem_union.mpr hc
        exact mem_union_right _ (mem_biUnion.mpr ⟨t,mem_univ _,mem_biUnion.mpr ⟨I,hs,hm'⟩⟩)
    · let J:V:=⟨I,mem_biUnion.mpr ⟨f,hf,hv⟩⟩
      exact Or.inr ⟨aI J,mem_image_of_mem _ (mem_attach _ _),
        P6_7_7.eGu (F:=P6_7.weakenFamily x.F (by decide)) (final_mem J.property).1.prime hm⟩
end
end qUrGXob
end
