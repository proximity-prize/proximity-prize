import ProximityPrize.SubmissionLower.ZDyoNob
set_option Elab.async false
set_option maxHeartbeats 1500000
open _root_ renaming Finset→lJ,Finset.filter_subset→nq,Ideal→lI,Nat.eq_zero_of_le_zero→ oK,Nat.le_of_lt_succ→ oj,Nat.succ_le_of_lt→ oY,P1.bje→cy,P5_7.FarBand→mD,P5_7.Pairs→aU,P5_7.farAgreement→c9,dite_eq_left→n5,dite_eq_right→ ox,gT.Ambient→lz,ite_eq_left→lV
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace P5_7_5
noncomputable section

open P5_7 (terminal)



open pI (xN dM dual aaS)
open scoped Classical
def nextIndex {b:mD} (i:ℕ) (hi:i<Fo b) :afa b :=
 ⟨i+1,by unfold Fo at hi; omega⟩
structure Process {b h rows} (pairs :aU b h rows) where
 sched:aqE b
 parents :lJ (lI lz)
 fixed : ∀ i:afa b,bQX pairs i
 DN : ∀ I∈parents,xN I∧I.height=2
 init_mass :dM parents (BC b)
def Process.Clean {b h rows} {pairs :aU b h rows} (R:Process pairs)
    (I:lI lz) :Prop :=
  ∀ i,¬ aaS (R.fixed i).free.equation I ∧ ¬ aaS (R.fixed i).moving.equation I
def dqh {b h rows} (pairs :aU b h rows) (i:ℕ) (I:lI lz) :Prop :=
 ∀ j:afa b,0<j.val→j.val≤ i→axS (arS pairs j) I
def Process.Lc {b h rows} {pairs :aU b h rows} (R:Process pairs) (i:ℕ) :
    lJ (lI lz) :=
  R.parents.filter fun I=>R.Clean I∧dqh pairs i I
def Process.Bp {b h rows} {pairs :aU b h rows} (R:Process pairs) (i:ℕ) :
    lJ (lI lz) :=
  (R.Lc i).filter fun I=>Wx b≤ i→dual I
def Process.aWI {b h rows} {pairs :aU b h rows} (R:Process pairs) :
    lJ (lI lz) :=
  (R.Lc (Wx b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs :aU b h rows} (R:Process pairs) :
    lJ (lI lz) :=
  (R.Bp (Fo b)).filter (agA rows (terminal b).shape)
def Process.QV {b h rows} {pairs :aU b h rows} (R:Process pairs) (i:ℕ) :
    lJ (lI lz) :=
  if i≤Fo b then R.Bp i else R.final
def Process.Hj {b h rows} {pairs :aU b h rows} (R:Process pairs) (i:ℕ) :
    lJ (lI lz) :=
  if hi:i<Fo b then
    (R.Bp i).filter fun I => ¬ axS (arS pairs (nextIndex i hi)) I
  else
    (R.Bp i).filter fun I => ¬ agA rows (terminal b).shape I
theorem Process.bxI {b h rows} {pairs :aU b h rows} (R:Process pairs)
  (i:ℕ) :R.Lc i⊆R.parents :=
 nq _ _
theorem Process.a4R {b h rows} {pairs :aU b h rows} (R:Process pairs)
  (i:ℕ) :R.Bp i⊆R.Lc i :=
 nq _ _
theorem Process.bGA {b h rows} {pairs :aU b h rows} (R:Process pairs) :
  R.final⊆R.Bp (Fo b) :=
 nq _ _
theorem Process.cYQ {b h rows} {pairs :aU b h rows} (R:Process pairs)
  (i:ℕ) :R.Hj i⊆R.Bp i:= by
 unfold Process.Hj
 split <;> exact nq _ _
private theorem Process.dha {b h rows} {pairs :aU b h rows} (R:Process pairs)
  {i j:ℕ} (hij:i≤j) :R.Lc j⊆R.Lc i:= by
 intro I hI
 obtain ⟨hm,hc,hp⟩:=Finset.mem_filter.mp hI
 exact Finset.mem_filter.mpr ⟨hm,hc,fun k hpos hk=>hp k hpos (hk.trans hij)⟩
private theorem Process.cWA {b h rows} {pairs :aU b h rows} (R:Process pairs)
  {i j:ℕ} (hij:i≤j) :R.Bp j⊆R.Bp i:= by
 intro I hI
 obtain ⟨hm,hp⟩:=Finset.mem_filter.mp hI
 exact Finset.mem_filter.mpr ⟨R.dha hij hm,fun h=>hp (h.trans hij)⟩
theorem Process.eEO {b h rows} {pairs :aU b h rows} (R:Process pairs)
   {i:ℕ} (hi:i≤Fo b) :R.QV (i+1)⊆R.QV i:= by
 rcases hi.lt_or_eq with ht | he
 · simp only [Process.QV,lV hi,lV (oY ht)]
   exact R.cWA (Nat.le_succ _)
 · subst i
   simpa [Process.QV] using R.bGA
theorem Process.eyg {b h rows} {pairs :aU b h rows} (R:Process pairs)
    {i:ℕ} (hi:i≤Fo b) :R.Hj i⊆R.QV i \ R.QV (i+1) := by
  intro I hm
  refine Finset.mem_sdiff.mpr ⟨by simpa only [Process.QV,lV hi] using R.cYQ i hm,?_⟩
  intro hn
  rcases hi.lt_or_eq with ht | he
  · have hf :=(Finset.mem_filter.mp
        (show I∈(R.Bp i).filter _ from by simpa only [Process.Hj,n5 ht] using hm)).2
    have hk :I∈R.Bp (i+1) := by
      simpa only [Process.QV,lV (oY ht)] using hn
    have hpasses :=(Finset.mem_filter.mp (R.a4R _ hk)).2.2
    exact hf (hpasses (nextIndex i ht) (by change 0< i+1; omega) le_rfl)
  · subst i
    have hf :=(Finset.mem_filter.mp
        (show I∈(R.Bp (Fo b)).filter _ from by
          simpa only [Process.Hj,ox (Nat.lt_irrefl _)] using hm)).2
    have hf' : I∈R.final:= by simpa [Process.QV] using hn
    exact hf (Finset.mem_filter.mp hf').2
theorem Process.fTa {b h rows} {pairs :aU b h rows} (R:Process pairs)
   {I:lI lz} (hI:I∈R.aWI) :xN I ∧ ¬ dual I :=
 let hm:=Finset.mem_filter.mp hI
 ⟨(R.DN I (R.bxI _ hm.1)).1,hm.2⟩
theorem Process.fXs {b h rows} {pairs :aU b h rows} (R:Process pairs)
    {I:lI lz} (hI:I∈R.parents) (hc:R.Clean I)
    (hrank :I∉R.aWI) (hlost : ∀ i≤Fo b,I∉R.Hj i) :
    I∈R.final:= by
  have keep : ∀ i≤Fo b,I∈R.Bp i:= by
    intro i hi
    induction i with
    | zero =>
      have ht:I∈R.Lc 0 :=
        Finset.mem_filter.mpr ⟨hI,hc,fun j hp hj=>(Nat.not_lt_of_ge hj hp).elim⟩
      refine Finset.mem_filter.mpr ⟨ht,?_⟩
      intro hs
      by_contra hd
      exact hrank (Finset.mem_filter.mpr ⟨by simpa [oK hs] using ht,hd⟩)
    | succ i ih =>
      have ht:i<Fo b:=hi
      have hprev :=ih (Nat.le_of_lt ht)
      have hp:axS (arS pairs (nextIndex i ht)) I:= by
        by_contra hfail
        apply hlost i ht.le
        simpa only [Process.Hj,n5 ht] using Finset.mem_filter.mpr ⟨hprev,hfail⟩
      have htest :I∈R.Lc (i+1) := by
        refine Finset.mem_filter.mpr ⟨hI,hc,?_⟩
        intro j hj hji
        rcases hji.lt_or_eq with hj' | he
        · exact (Finset.mem_filter.mp (R.a4R i hprev)).2.2 j hj (oj hj')
        · rw [show j=nextIndex i ht from Fin.ext he]
          exact hp
      refine Finset.mem_filter.mpr ⟨htest,?_⟩
      intro hs
      by_cases hh:Wx b≤ i
      · exact (Finset.mem_filter.mp hprev).2 hh
      · have he :Wx b=i+1 := by omega
        by_contra hd
        exact hrank (Finset.mem_filter.mpr ⟨by simpa [he] using htest,hd⟩)
  have hk :=keep (Fo b) le_rfl
  refine Finset.mem_filter.mpr ⟨hk,?_⟩
  by_contra hf
  apply hlost (Fo b) le_rfl
  simpa only [Process.Hj,ox (Nat.lt_irrefl _)] using Finset.mem_filter.mpr ⟨hk,hf⟩
end
end P5_7_5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace P5_7_5
noncomputable section




open pI (mass)

open scoped Classical BigOperators
theorem kG (b:mD) (bw:Fin 3) (i:ℕ) (S:lJ (lI lz)) :
  ((pI.dot (pI.weight (aHp b i) bw) (mass S) :ℕ) :ℚ) =
    FP (SS b bw i) (J2 S) := by
 simp only [FP,pI.dot,SS,J2,Nat.cast_sum,Nat.cast_mul]
theorem enb (b:mD) (i:ℕ) (k :Fin 4) :
   V8 b i k≤BC b k := by
 induction i with
 | zero=>exact le_rfl
 | succ i ih=>exact (min_le_left _ _).trans ih
theorem le_ceil_toNat (x :ℚ) :x≤(x.ceil.toNat :ℚ) :=
 Rat.le_ceil.trans (by exact_mod_cast Int.self_le_toNat x.ceil)
end
end P5_7_5
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace P5_7_5
noncomputable section
open Polynomial
open P5 (K jG)
open P5_7 (InFar)

open gT (tK FW)
open pI (abM)


open scoped BigOperators Classical
theorem cbe :aSt:=aZC.proof
def c2 :Prop :=
  ∀ (b:mD) u del (M:jG u del) Γ (F:cy c9 M Γ),
    InFar b M.iF →
    ∀ B J:ℕ,aBh B J →
    ∀ G:tK,abM G B J → ∀ T⊆Γ,
    (∀ γ∈T,FW G (F.scalar γ)=0)→T.card≤au1 b.row.hi B J
def c3:Prop := ∀ b:mD,aqE b
private def bdZ {u del} {M:jG u del} {Γ} (F:cy c9 M Γ)
 (G:tK) :lJ K:=Γ.filter fun γ=>FW G (F.scalar γ)=0
private theorem b3r (hcount:c2) {b u del} {M:jG u del} {Γ}
  (F:cy c9 M Γ) (hw:InFar b M.iF) {B J:ℕ}
  (guard :aBh B J) {G:tK} (cap:abM G B J) :
  (bdZ F G).card≤au1 b.row.hi B J :=
 hcount b u del M Γ F hw B J guard G cap _ (nq _ _)
  (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
end
end P5_7_5
end
