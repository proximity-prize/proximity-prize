import ProximityPrize.SubmissionLower.Z0Ff26b
set_option Elab.async false
set_option autoImplicit true
namespace P6_7_2
noncomputable section
open Polynomial
open P6 (I K p dw)
open P6_7 (RectTail)
open cu (FX Equation qD yq jz Vg)
open qQ (zI N5 aLQ)
open P5_7 (OneSeedEquation NativeSeedBound atNative)
def c1 :Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x),Nonempty (Picks (b:=b) x.h P.rows)
def c2 :Prop :=
  ∀ (b:RectTail) (x :Input b),Nonempty (TopPair x)
def c3:Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x),
    Picks (b:=b) x.h P.rows→TopPair x→Nonempty (Prefix P)
def c4 :Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x) (r :sk),Subrect b r →
    rectVolume b x.h r≤ rectDebit b x.h r+rankSum P r
def c5:Prop :=
  ∀ (b:RectTail) (x :Input b) (P:Poles x) (r :sk),Subrect b r →
    ∀ (Q:Finset zI) (f :Equation),
      (∀ q∈Q,N5 q∧TerminalPass P q)→aLQ Q f →
      ∀ (kd:Fin 2) E v,0<E→E≤f.natDegree →
        (v=0 ∨ ∃ l,v≤(f.coeff l).degreeOf kd) →
        rankSum P r+ZN b x.h r kd E v≤ rectVolume b x.h r
def c6:Prop :=
  ∀ (b:RectTail) h,b.kA.lo≤h→h≤(Bs b).hi →
    Subrect b (full b) ∧
    rectDebit b h (full b)<ZN b h (full b) 0 ((Bs b).ordinateCap+1) 0 ∧
    ∀ (i:jJ b) (kd:Fin 2),
      Subrect b (Lc i kd) ∧
      rectDebit b h (Lc i kd)<ZN b h (Lc i kd) kd (i.val+1) (seedCap i+1)
def c7:Prop :=
  ∀ (b:RectTail) (i:jJ b) (word:I→K) (T:Finset K) (z :K→K) (S:K→K[X]),
    Set.InjOn z (T:Set K)→Set.InjOn S (T:Set K) →
    (∀ γ∈T,(S γ).natDegree≤131071+(Bs b).hi) →
    (∀ γ∈T,∃ lg:Finset I,dw≤lg.card ∧
      ∀ j∈lg,(S γ).eval (P6.node j)=word j) →
    ∀ g:OneSeedEquation,g≠0→ g.natDegree≤ i.val+1 →
      NativeSeedBound g (seedCap i+p*seedCap i) →
      (∀ γ∈T,atNative g (z γ) (S γ)=0)→T.card≤ retainedFee b
private theorem emz {b:RectTail} (x :Input b) :
    b.kA.lo≤x.h∧x.h≤(Bs b).hi:= by
  obtain ⟨hl,hu⟩:=x.kA
  have hhi:b.kA.hi≤(Bs b).hi:= by cases b <;> decide
  change (b.kA.lo:ℤ)≤x.M.iF at hl
  change x.M.iF≤(b.kA.hi:ℤ) at hu
  change b.kA.lo≤x.M.iF.toNat∧x.M.iF.toNat≤(Bs b).hi
  omega
theorem paid_guard (b:RectTail) (w:ℕ) (hw:b.kA.lo≤w) :
    (Bs b).paidOrder*(dw-131071+1+w)≤2*w*(Bs b).dI:= by
  cases b
  · change 2*(48757+w)≤2*w*22
    change 2360≤w at hw
    omega
  all_goals simp [Bs]
private theorem poles {b:RectTail} (x :Input b) :Nonempty (Poles x) := by
  obtain ⟨D,h0,h1,hn,hm⟩:=P6_7.bW4 x.M x.F x.H x.bY
  obtain ⟨Crt⟩:=atp.dRH D
  exact ⟨⟨D,Crt,h0,h1,hn,hm⟩⟩
private theorem eiO {b:RectTail} {f :Equation} (hp:0<f.natDegree)
    (hord:f.natDegree<(Bs b).ordinateCap+1)
    (reject : ∀ (i:jJ b) (a :Fin 2) (l:ℕ),i.val+1≤f.natDegree →
      seedCap i+1≤(f.coeff l).degreeOf a→False) :
    ∃ i:jJ b,f.natDegree=i.val+1∧AxisBound f 0 (seedCap i)∧AxisBound f 1 (seedCap i) := by
  let i:jJ b:=⟨f.natDegree-1,by omega⟩
  have he :f.natDegree=i.val+1 := by dsimp [i]; omega
  have ha (a :Fin 2) :AxisBound f a (seedCap i) := by
    intro l
    by_contra! h
    exact reject i a l he.ge h
  exact ⟨i,he,ha 0,ha 1⟩
private theorem graph_specialize (z :K) :
    (evalRingHom (jz z)).comp (Vg (F:=FX) p).toRingHom =
      qD z := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [Vg,qD]
  · intro i
    fin_cases i <;> simp [Vg,qD]
theorem native_restriction {f :Equation} (hn:f≠0) {a b:ℕ}
    (ha :a<p) (hz :AxisBound f 0 a) (ht:AxisBound f 1 b) :
    ∃ g:OneSeedEquation,g≠0∧g.natDegree≤f.natDegree∧NativeSeedBound g (a+p*b) ∧
      ∀ z S,atNative g z S=yq f z S:= by
  let g:OneSeedEquation :=f.map (Vg p).toRingHom
  refine ⟨g,?_,natDegree_map_le,?_,?_⟩
  · have hl:=cu.bG0 p (by decide) (f.coeff f.natDegree)
      (by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hn) ((hz _).trans_lt ha)
    intro h
    apply hl
    have hc:=congrArg (fun g:OneSeedEquation=>g.coeff f.natDegree) h
    rw [show g=f.map (Vg p).toRingHom from rfl,coeff_map,coeff_zero] at hc
    exact hc
  · intro l
    change (g.coeff l).natDegree≤_
    rw [show g=f.map (Vg p).toRingHom from rfl,coeff_map]
    exact cu.b33 p a b (f.coeff l) (hz l) (ht l)
  · intro z S
    rw [atNative,show g=f.map (Vg p).toRingHom from rfl,
      eval₂_map,graph_specialize,yq]
private theorem kept_count (h4 :c4) (h5:c5) (h6:c6) (h7:c7)
    {b:RectTail} {x :Input b} {P:Poles x} (Q:Prefix P) :
    (x.Γ \ Q.book).card≤ retainedFee b:= by
  classical
  let T:=x.Γ \ Q.book
  have hT:T⊆x.Γ:=Finset.sdiff_subset
  change T.card≤ retainedFee b
  by_cases hTn:T.Nonempty
  · have cover : ∀ γ∈T,∃ q∈Q.parents,P6_7.axy x.M x.F q γ:= fun γ hγ =>
      (Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
    obtain ⟨γ,hγ⟩:=hTn
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
    obtain ⟨hl,hu⟩:=emz x
    obtain ⟨hfull,hord,hgrade⟩:=h6 b x.h hl hu
    have geom (q) (hq:q∈Q.parents) :=And.intro (Q.geometric q hq) (Q.terminal_pass q hq)
    have bound (r :sk) (hr :Subrect b r) (kd:Fin 2) (E v :ℕ) (hE :0<E)
        (he :E≤f.natDegree) (hv :v=0 ∨ ∃ l,v≤(f.coeff l).degreeOf kd) :
        ZN b x.h r kd E v≤ rectDebit b x.h r := by
      have hflo:=h4 b x P r hr
      have hloss :=h5 b x P r hr Q.parents f geom hf kd E v hE he hv
      omega
    have he :f.natDegree<(Bs b).ordinateCap+1 := by
      by_contra! hh
      exact hord.not_ge (bound (full b) hfull 0 _ 0 (Nat.succ_pos _) hh (Or.inl rfl))
    obtain ⟨i,hi,hz,ht⟩:=eiO hf.positive he fun i a l he hv =>
      (hgrade i a).2.not_ge (bound (Lc i a) (hgrade i a).1 a _ _ (Nat.succ_pos _) he
        (Or.inr ⟨l,hv⟩))
    have hs :seedCap i<p:=(Nat.mod_lt _ (by decide :0<4096)).trans (by decide)
    have hfn :f≠0:= by
      intro h
      have hp:=hf.positive
      simp [h] at hp
    obtain ⟨g,hg,hd,hb,hgraph⟩:=native_restriction hfn hs hz ht
    refine h7 b i x.M.word T x.M.label x.F.scalar (fun _ _ _ _ h=>sub_left_inj.mp h)
      (x.F.distinct.mono hT) ?_ ?_ g hg (hd.trans hi.le) hb ?_
    · intro η hη
      exact (P6_7.aic x.F (hT hη)).trans (Nat.add_le_add_left hu _)
    · intro η hη
      let m:=x.F.mark η (hT hη)
      exact ⟨m.bad.support,m.bad.dw,m.scalar_hits⟩
    · intro η hη
      rw [hgraph]
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hh:=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,yq] using hh
  · simp [Finset.not_nonempty_iff_eq_empty.mp hTn]
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) (h7:c7) :
    P6_7.c2 := by
  classical
  intro b u del M Γ F hw hshift H hH
  let x :Input b:=⟨u,del,M,Γ,F,hw,hshift,H,hH⟩
  obtain ⟨P⟩:=poles x
  obtain ⟨pick⟩:=h1 b x P
  obtain ⟨top⟩:=h2 b x
  obtain ⟨Q⟩:=h3 b x P pick top
  have hret:=kept_count h4 h5 h6 h7 Q
  have hpart:=Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left:x.Γ∩Q.book⊆x.Γ)
  have hdiff :x.Γ \ (x.Γ∩Q.book)=x.Γ \ Q.book := by
    ext γ
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hdiff] at hpart
  have hbook :=(Finset.card_le_card
    (Finset.inter_subset_right:x.Γ∩Q.book⊆Q.book)).trans Q.book_bound
  change x.Γ.card≤b.kA.regular
  rw [← hpart]
  exact (Nat.add_le_add hret hbook).trans (by cases b <;> decide)
end
end P6_7_2
