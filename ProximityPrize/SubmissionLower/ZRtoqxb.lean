import ProximityPrize.SubmissionLower.ZwYh3la
import ProximityPrize.SubmissionLower.ZnXcxbb
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qBPZs8a
noncomputable section
open Finset
open P6 (p)
open P6_7_1
open cu (Jet Shape)
open pI (oU)
open TD (auN arC aIe)
open akZ (ajz aHP weightedDegree cs5 bCj)
open scoped Classical
abbrev RY:Shape :=⟨0,373,69,3188⟩
def box (i:Origin) :Shape :=
  if h:i.val<last then shape ⟨i.val,h⟩ else RY
theorem box_J (i:Origin) : (box i).J≤(box i).B:= by
  fin_cases i <;> decide
theorem enclose_last {f c:Jet} (h : ∀ j,wD f j≤ introCap last j) (l:Bool)
    (hc:oU c (if l then akZ.btm f else aOm f)) :
    oU c RY:= by
  have hb:wD f 0≤12 :=(h 0).trans_eq (by decide)
  have hj:wD f 1≤2 :=(h 1).trans_eq (by decide)
  have hu:wD f 2≤142 :=(h 2).trans_eq (by decide)
  apply (bCj _ _).mpr
  intro i
  refine ((bCj _ _).mp hc i).trans ?_
  cases l <;> fin_cases i
  · change 164+19*(wD f 0-1)≤373
    omega
  · change 50+19*(wD f 1-1)≤69
    omega
  · change 490+19*wD f 2≤3188
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
abbrev massCap:Fin 4→ℕ := ![8456,129214,0x94bc9,0x3ee599]
private theorem account_cap (k :Fin 4) :
    account k introductions (introCap 0) (fun _=>0)≤ massCap k := by
  fin_cases k <;> decide
theorem mass_small (k :Fin 4) :massCap k<p:= by
  fin_cases k <;> decide
theorem charge (D:Finset Jet) (origin :Jet→Origin)
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
end qBPZs8a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1200000
namespace qBPZs8a
noncomputable section
open Finset
open P6 (K p)
open P6_7_1 (Input Origin introCap)
open cu (Jet)
open gT (Ambient IZ gk iJ)
open pI (xN oU dM pN mass a5I F7)
open YX (bQz bjf eHX evL)

open qQ (VN a4N bH5 bH6 bH4
  aJr bNe)
open akZ (ajz btm bKa caQ cfi)
open scoped Classical
open private a8m bYs ddo from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
structure Parents (x :Input) (D:Finset Jet) (cut:Jet→Jet) where
  parents :Jet→Finset (Ideal Ambient)
  gH :Finset K
  paid_bound:gH.card≤projectionFee
  geometric : ∀ f∈D,∀ q∈parents f,
    xN q∧q.height=2∧iJ f∈q∧iJ (cut f)∈q
  disjoint : ∀ f∈D,∀ g∈D,f≠g→Disjoint (parents f) (parents g)
  Eh : ∀ f∈D,∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
    γ∈gH ∨ ∃ g∈D,∃ q∈parents g,IZ q (x.M.label γ) (x.F.scalar γ)
theorem geometric_cover (x :Input) (D:Finset Jet) (origin :Jet→Origin)
    (cut:Jet→Jet) (hirr : ∀ f∈D,Irreducible f) (hcut : ∀ f∈D,¬ f∣cut f)
    (hcaps : ∀ f∈D,oU (cut f) (box (origin f)))
    (nest : ∀ i≤last,∀ j,ajz (D.filter (fun f=>i≤(origin f).val)) j≤ introCap i j) :
    Nonempty (Parents x D cut) := by
  have each (f :Jet) (hf :f∈D) :
      ∃ S:Finset (Ideal Ambient),bQz f (cut f) S ∧
        (∀ q∈S,q.height=2∧bjf q) ∧
        dM S (fun k=>akZ.aHP (box (origin f)) k f) ∧
        ∀ γ∈x.Γ,Mark x f γ→Mark x (cut f) γ →
          ∃ q∈S,IZ q (x.M.label γ) (x.F.scalar γ) := by
    have hp:=b6z (hirr f hf) (hcut f hf)
    obtain ⟨S,hs,hcover⟩:=aRY.proof _ _ hp
    obtain ⟨hfinite,hfit⟩:=a8m _ _ hp (btm f) (box (origin f))
      (caQ (hirr f hf).ne_zero) (box_J _) (bKa f) (hcaps f hf) S hs
    refine ⟨S,hs,?_,fun k=>(hfit k).trans_eq (cfi _ _ (box_J _) k),
      fun γ _=>hcover (x.M.label γ) (x.F.scalar γ)⟩
    intro q hq
    obtain ⟨hprime,hd,hrow,hg⟩:=hs q hq
    exact ⟨bYs hp hprime hd hrow hg,hfinite q hq⟩
  let S (f :Jet) :=if h:f∈D then Classical.choose (each f h) else ∅
  have hs (f :Jet) (hf :f∈D) :=Classical.choose_spec (each f hf)
  have hS (f :Jet) (hf :f∈D) :
      S f=Classical.choose (each f hf) :=dite_eq_left hf
  let all:=D.biUnion S
  have hmass :dM all massCap:= fun k=> calc
    _ ≤ ∑ f∈D,mass (S f) k :=pI.bhF _ _ _
    _ ≤ ∑ f∈D,akZ.aHP (box (origin f)) k f :=
      sum_le_sum fun f hf=> by rw [hS f hf]; exact (hs f hf).2.2.1 k
    _≤_:=charge D origin nest k
  have geom (q:Ideal Ambient) (hq:q∈all) :
      q.IsPrime∧ringKrullDim (gk q)=2∧q.height=2∧bjf q:= by
    obtain ⟨f,hf,hq⟩:=mem_biUnion.mp hq
    rw [hS f hf] at hq
    exact ⟨((hs f hf).1 q hq).1,((hs f hf).1 q hq).2.1,(hs f hf).2.1 q hq⟩
  let Kw:=all.filter fun q=>pN q 0=0
  have seedExists (q:Ideal Ambient) (hq:q∈Kw) :
      ∃ C:VN,C.curve.totalDegree≤pN q 2 ∧
        C.points.card≤pN q 3 ∧ ∀ z R,IZ q z R→C.ow z := by
    obtain ⟨hq,hz⟩:=mem_filter.mp hq
    obtain ⟨hprime,hd,_,hf⟩:=geom q hq
    exact ddo q hprime hd hf hz
  let images (q:Ideal Ambient) :VN :=
    if h:q∈Kw then Classical.choose (seedExists q h) else ⟨1,one_ne_zero,∅⟩
  have hi (q:Ideal Ambient) (hq:q∈Kw) :
      (images q).curve.totalDegree≤pN q 2 ∧
      (images q).points.card≤pN q 3 ∧ ∀ z R,IZ q z R→(images q).ow z := by
    simpa only [images,dite_eq_left hq] using Classical.choose_spec (seedExists q hq)
  let cover :=a4N Kw images
  have hc:=(bH5 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).1).trans
      ((a5I (filter_subset _ _) 2).trans (hmass 2)))
  have hp:=(bH6 Kw images).trans
    ((sum_le_sum fun q hq=>(hi q hq).2.1).trans
      ((a5I (filter_subset _ _) 3).trans (hmass 3)))
  let seedPaid :=x.Γ.filter fun γ=>cover.ow (x.M.label γ)
  have hseed :seedPaid.card≤(p+1)*massCap 2+massCap 3 :=
    (aJr (T:=seedPaid) (fun _ _ _ _ h=>sub_left_inj.mp h) cover
      (hc.trans_lt (mass_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hc) hp)
  let dominant (q:Ideal Ambient) :=Function.Injective ((Ideal.Quotient.mk q).comp F7)
  let ord:=all.filter fun q=>0<pN q 0 ∧ ¬ dominant q
  let marks (q:Ideal Ambient) :=x.Γ.filter fun γ=>IZ q (x.M.label γ) (x.F.scalar γ)
  let ordPaid :=ord.biUnion marks
  have hord:ordPaid.card≤ massCap 0:= by
    refine (card_biUnion_le.trans (sum_le_sum ?_)).trans
      ((a5I (filter_subset _ _) 0).trans (hmass 0))
    intro q hq
    obtain ⟨hq,hpos,hno⟩:=mem_filter.mp hq
    refine (card_le_one.mpr fun y hy z hz => ?_).trans hpos
    obtain ⟨hy,hm⟩:=mem_filter.mp hy
    obtain ⟨hz,hn⟩:=mem_filter.mp hz
    exact x.F.distinct hy hz (bNe (eHX (geom q hq).1 hno hm hn))
  let owner (q:Ideal Ambient) :=if h:q∈all then Classical.choose (mem_biUnion.mp h) else 0
  have owns (q:Ideal Ambient) (h:q∈all) :owner q∈D ∧q∈S (owner q) := by
    simpa only [owner,dite_eq_left h] using Classical.choose_spec (mem_biUnion.mp h)
  let Bp (f :Jet) :=(S f).filter fun q =>
    owner q=f∧0<pN q 0∧dominant q
  refine ⟨⟨Bp,seedPaid∪ordPaid,(card_union_le _ _).trans
    ((Nat.add_le_add hseed hord).trans (by decide)),?_,?_,?_⟩⟩
  · intro f hf q hq
    obtain ⟨hq,_,hpos,hdom⟩:=mem_filter.mp hq
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,hq⟩
    obtain ⟨hprime,hd,hh,hfinite⟩:=geom q hall
    have hlim (k :Fin 4) :pN q k<p :=
      ((evL hall k).trans (hmass k)).trans_lt (mass_small k)
    have hmem:=(hs f hf).1 q (hS f hf ▸ hq)
    exact ⟨⟨hprime,hd,hfinite.Kw,hfinite.jU,hfinite.kK,hfinite.Bo,
      ⟨hpos,hlim 0⟩,hlim 2,hlim 3,hdom⟩,hh,hmem.2.2⟩
  · intro f _ g _ hne
    exact disjoint_left.mpr fun q hf hg=>hne ((mem_filter.mp hf).2.1.symm.trans (mem_filter.mp hg).2.1)
  · intro f hf γ hγ hz hw
    obtain ⟨q,hq,hmark⟩:=(hs f hf).2.2.2 γ hγ hz hw
    have hall:q∈all:=mem_biUnion.mpr ⟨f,hf,(hS f hf).symm ▸ hq⟩
    by_cases hzero :pN q 0=0
    · have hmem:q∈Kw:=mem_filter.mpr ⟨hall,hzero⟩
      exact Or.inl (mem_union_left _ (mem_filter.mpr
        ⟨hγ,bH4 hmem ((hi q hmem).2.2 _ _ hmark)⟩))
    · have hpos :=Nat.pos_of_ne_zero hzero
      by_cases hdom:dominant q
      · obtain ⟨hg,hq⟩:=owns q hall
        exact Or.inr ⟨owner q,hg,q,mem_filter.mpr ⟨hq,rfl,hpos,hdom⟩,hmark⟩
      · exact Or.inl (mem_union_right _ (mem_biUnion.mpr
          ⟨q,mem_filter.mpr ⟨hall,hpos,hdom⟩,mem_filter.mpr ⟨hγ,hmark⟩⟩))
end
end qBPZs8a
end
section
set_option autoImplicit true
namespace qiFSOoc
noncomputable section
open Finset Polynomial
open P6_7_1
open cu (FX)
open DP (d3r)
private theorem booked {volume j3 rows capacity O3:ℕ}
    (hf :volume≤j3+rows) (hr :rows≤ capacity)
    (ht:capacity+O3=volume) :O3≤j3:= by omega
theorem proof :P6_7_1.c6:= by
  intro x P t f hn hE hv src trace
  let s :=Lc t
  let a :=direction t
  let N :=terminal.m*P6.dw
  obtain ⟨hl,hu⟩:=heights x
  change 2350≤x.h at hl
  change x.h≤2369 at hu
  have hh:0<x.h:= by omega
  have hk :0<131071-x.h:= by omega
  have he :0<threshold t:= by rcases t with _ | ⟨i,a⟩ <;> exact Nat.succ_pos _
  have hm:s.m=terminal.m:=(ctc t).1
  have hmax : (∑ W∈range N,Module.finrank FX (rectBank P s W)) ≤
      ∑ W∈range N,aT2 N x.h s a (threshold t) (apo t) W:= by
    apply sum_le_sum
    intro W hW
    refine boi N x.h s a _ _ W _ hn hE hv hk he ?_ ?_ ?_ ?_
    · intro g hg hne
      have hc: ((g.coeff g.natDegree).coeff g.leadingCoeff.natDegree)≠0:= by
        rw [coeff_natDegree,coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hne)
      have h:=d3r P.crt x.word (rectBank_le P s W hg) _ _ hc
      exact ⟨h.1,h.2.1⟩
    · intro g hg hne
      exact atp.eu5 hh (by omega) P.crt x.word s.box W g (rectBank_le P s W hg) hne
    · intro g hg j
      exact bank_seed hg j
    · exact trace W (mem_range.mp hW)
  have htot:=bDM x.h s a (threshold t) (apo t) (by omega) hk
  rw [hm] at htot
  have hfloor :=src.floor t
  change rectVolume x.h s≤ rectDebit x.h s + ∑ W∈range N,Module.finrank FX (rectBank P s W) at hfloor
  exact booked hfloor hmax htot
end
end qiFSOoc
end
