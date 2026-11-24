import ProximityPrize.SubmissionLower.ZUURnQa
set_option Elab.async false
open _root_ renaming IsCoprime→lJ,Module.finrank→mD,Nat.eq_zero_of_le_zero→nI,Nat.le_of_lt_succ→nX,Nat.mul_le_mul_left→lV,P5_7_2.terminal→aU,P5_7_2.threshold→cy,Polynomial.C→c9,Polynomial.coeff_natDegree→lI,Polynomial.map_mul→nq,cu.Equation→lz
section
set_option autoImplicit true
namespace P5_7_2
noncomputable section
open Finset Polynomial MvPolynomial
open P5 (K p jG)
open P5_7 (YQ)
open cu (Shape ku FX L Jet slots triangle vm j9)
open DP (jF zG aKF VY)
open qQ (oU zI N5 aLQ wU)
open Qt (aH3 gY bg4 Qc)
open baY (Bp)
open private bKE from ProximityPrize.SubmissionLower.D8
open private cer cTX from ProximityPrize.SubmissionLower.D8
open private ddI from ProximityPrize.SubmissionLower.A1
open private bGH Wb from ProximityPrize.SubmissionLower.A0
def ahs (h:ℕ) (s :Shape) (W:ℕ) :=1+(O2 s-W)/(2*h)
set_option backward.isDefEq.respectTransparency false in
theorem bW4 {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ)
    (H :L[X]) (hH :YQ M F H) :
    ∃ D:jF M.iF.toNat,
      D.block 0=H∧D.block 1=H.map (frobenius L p) ∧
      NodeUnits D ∧ ∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ) := by
  let σ:=frobenius L p
  rcases hH with ⟨hm,hd,_,hm',hd',_,hcop,hnode,hdet,hdet',hmarks⟩
  let A:=j9 (M.factor*M.A₀)
  let B:=j9 (M.factor*M.A₁)
  let Q:=j9 M.Q
  have hdet0:lJ (Q*A) H := by
    simpa [Q,A,j9,mul_assoc] using hdet
  have hdet1 :lJ (Q.map σ*A.map σ) (H.map σ) := by
    simpa [Q,A,j9,mul_assoc,σ,nq] using hdet'
  let D:jF M.iF.toNat :=
    ⟨![H,H.map σ],![Q,Q.map σ],![A,A.map σ],![B,B.map σ],
      fun i=> by fin_cases i <;> first | exact hm | exact hm',
      fun i=> by fin_cases i <;> first | exact hd | exact hd',
      hcop,fun i=> by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D,rfl,rfl,?_,?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z :=algebraMap K L (M.label γ)
    have hz :j9 (M.factor*M.wK γ)=A+(@c9 L _) z*B:= by
      simp [A,B,z,P1.FJ.wK,j9,mul_add,mul_left_comm]
    obtain ⟨h₀,h₁,hr₀,hr₁⟩:=hmarks γ hγ
    fin_cases i
    · change lJ (A+(@c9 L _) z*B) H ∧
        H∣(A+(@c9 L _) z*B)*j9 (F.scalar γ)+(@c9 L _) z*Q
      rw [← hz]
      exact ⟨h₀,hr₀⟩
    · have hσ: (j9 (M.factor*M.wK γ)).map σ =
          A.map σ+(@c9 L _) (z^p)*B.map σ:= by
        rw [hz,Polynomial.map_add,nq,Polynomial.map_C]
        rfl
      change lJ (A.map σ+(@c9 L _) (z^p)*B.map σ) (H.map σ) ∧
        H.map σ∣(A.map σ+(@c9 L _) (z^p)*B.map σ)*j9 (F.scalar γ) +
          (@c9 L _) (z^p)*Q.map σ
      rw [← hσ]
      exact ⟨h₁,hr₁⟩
private def aT2 (h:ℕ) (s :Shape) (E v W:ℕ) :ℕ :=
 ku s fun q j =>
   if q*(131071-h)≤W+j then
     Bp s.U v ((q-j)/E) (ahs h s W - j)
   else 0
private def b4O (h:ℕ) (s :Shape) (E v W j:ℕ) :ℕ :=
 let r :=ahs h s W - j
 (aH3 (131071-h) s.B W j - r*E)*slots s.U (r*v)
private theorem cJb (h:ℕ) (s :Shape) (E v W:ℕ)
  (hk :0<131071-h) (he :0<E) :
  (∑ j∈range (s.J+1),b4O h s E v W j)=aT2 h s E v W:= by
 rw [aT2,← ddI]
 apply sum_congr rfl
 intro j _
 exact cTX _ _ _ _ _ _ _ _ hk he
set_option backward.isDefEq.respectTransparency false in
private theorem boi (h:ℕ) (s :Shape) (E v W:ℕ) (V:Submodule FX Jet)
    {f :lz} (hf :f≠0) (hE :E≤f.natDegree) (hv :v≤gY f)
    (hk :0<131071-h) (he :0<E)
    (hcaps : ∀ P∈V,oU P s)
    (hlead : ∀ P∈V,P≠0 →
      (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree)
    (hdvd : ∀ P∈V,P≠0→f^(ahs h s W-P.natDegree)∣P.leadingCoeff) :
    mD FX V≤aT2 h s E v W:= by
  have hrow {P:Jet} (hP:P∈V) (hn:P≠0) :
      P.leadingCoeff.natDegree+P.natDegree≤ s.B∧P.natDegree≤ s.J ∧
      vm P.leadingCoeff s.U:= by
    have ha : (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree≠0:= by
      rw [lI,lI]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    obtain ⟨hB,hJ,_⟩:=hcaps P hP _ _ ha
    refine ⟨hB,hJ,fun i => ?_⟩
    by_cases hi:P.leadingCoeff.coeff i=0
    · simp [hi]
    · rw [← lI] at hi ⊢
      exact (hcaps P hP _ _ hi).2.2
  rw [← cJb h s E v W hk he]
  refine bGH (F:=FX) (A:=lz) V (b4O h s E v W)
    (s.J+1) ?_ ?_
  · intro j
    let r :=ahs h s W - j
    apply cer _ (g:=f^r) (pow_ne_zero r hf)
    · rw [Polynomial.natDegree_pow]
      exact lV _ hE
    · rw [bg4 hf]
      exact lV _ hv
    · rintro c ⟨⟨P,hP⟩,rfl⟩ hc
      change P.coeff j≠0 at hc
      obtain ⟨hpV,hd⟩:=Wb.mp hP
      have hn:P≠0:= by
        intro hz
        exact hc (by simp [hz])
      have hj:P.natDegree=j :=
        le_antisymm (nX ((natDegree_lt_iff_degree_lt hn).2 hd))
          (le_natDegree_of_ne_zero hc)
      obtain ⟨hB,_,hseed⟩:=hrow hpV hn
      have hwidth :=hlead P hpV hn
      have hdiv :=hdvd P hpV hn
      rw [hj] at hB hwidth hdiv
      change (P.coeff j).natDegree<_∧vm (P.coeff j) _∧_∣P.coeff j
      rw [← hj,lI,hj]
      refine ⟨?_,hseed,hdiv⟩
      have hd:=(Nat.le_div_iff_mul_le hk).2 hwidth
      unfold aH3
      omega
  · intro P hp
    by_cases hn:P=0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hrow hp hn).2.1)
private theorem bDM (h:ℕ) (s :Shape) (E v :ℕ) (hh:0<2*h) (hk :1≤131071-h) :
    (∑ W∈range (s.m*A),aT2 h s E v W)+ZN h s E v =
      triangle s.U*ku s (fun q j=>s.m*A+j-q*(131071-h)) := by
  have hswap (F:ℕ→ℕ→ℕ→ℕ) :
      (∑ W∈range (s.m*A),ku s (F W)) =
        ku s (fun q j => ∑ W∈range (s.m*A),F W q j) := by
    unfold ku
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
  simp only [aT2,ZN]
  rw [hswap]
  simp only [ku,← sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro j hj
  have hjq:j≤q:=(nX (mem_range.mp hj)).trans (min_le_left _ _)
  have hq:q≤q*(131071-h) := by simpa using lV q hk
  exact bKE (s.m*A) (2*h) (q*(131071-h)) j s.U v ((q-j)/E)
    (hjq.trans hq) hh
private theorem tested_shape (b:fO) (x :Test b) :
   (Lc b x).shape.m=(aU b).shape.m ∧
   (Lc b x).shape.B=(aU b).shape.B ∧
   (Lc b x).shape.J=(aU b).shape.J ∧
   (Lc b x).shape.U≤(aU b).shape.U:= by
 cases x
 · exact ⟨rfl,rfl,rfl,le_rfl⟩
 · exact ⟨rfl,rfl,rfl,Nat.sub_le _ _⟩
private theorem eHv {b h} {D:jF h} (Crt:zG D) (word:P5.I→L)
   (hh:0<h) (hchar : (aU b).shape.m*A<p)
   (x :Test b) {q:zI} (hq:N5 q)
   (hv : ∀ P∈VY Crt word (aU b).shape (O2 (aU b).shape),
     P∈q.asIdeal)
   {W P} (hW:W<(Lc b x).shape.m*A) (hP:P∈VY Crt word (Lc b x).shape W) :
   wU q P (ahs h (Lc b x).shape W) := by
 let s :=(Lc b x).shape
 obtain ⟨hm,hb,hj,hu⟩:=tested_shape b x
 have hp:s.m*A<p:=hm ▸ hchar
 have htop:O2 s=O2 (aU b).shape :=congrArg (fun m=>m*A-1) hm
 apply baD.proof _ _ _ hq
 · have hd:=Nat.div_le_self (O2 s-W) (2*h)
   change 1+(O2 s-W)/(2*h)<p
   change W<s.m*A at hW
   unfold O2 at *
   omega
 intro a c hac
 change a+c<1+(O2 s-W)/(2*h) at hac
 have hc:=(Nat.le_div_iff_mul_le (by omega :0<2*h)).mp
   (show a+c≤(O2 s-W)/(2*h) by omega)
 rw [Nat.mul_comm (a+c),Nat.mul_add] at hc
 have hwc:W≤O2 s := by
   change W<s.m*A at hW
   unfold O2
   omega
 have hw' : W+2*h*a+2*h*c≤O2 (aU b).shape := by omega
 have ha :=atp.d3s Crt word hP 0 a
 have hc' := atp.d3s Crt word ha 1 c
 exact hv _ (DP.d3q Crt word hm hb hj hu hw' hc')
theorem eqx {b h} {D:jF h} (Crt:zG D) (word:P5.I→L)
    (hh:0<h) (hk :h<131071) (hchar : (aU b).shape.m*A<p)
    {qs :Finset zI} (hq : ∀ q∈qs,N5 q)
    (hp : ∀ q∈qs,∀ P∈VY Crt word (aU b).shape (O2 (aU b).shape),
      P∈q.asIdeal)
    {f :lz} (hf :aLQ qs f)
    (x :Test b) (ht:TerminalFloor h (Lc b x) (VY Crt word))
    (hE :cy x≤f.natDegree) (hv :apo x≤gY f) :
    ZN h (Lc b x).shape (cy x) (apo x)≤j3 h (Lc b x) := by
  have he :0<cy x := by cases x <;> exact Nat.succ_pos _
  have hne :f≠0:= by
    intro hz
    simpa only [hz,natDegree_zero,lt_self_iff_false] using hf.positive
  let t:=Lc b x
  let top:=t.shape.m*A
  have hm :
      (∑ W∈range top,mD FX (VY Crt word t.shape W)) ≤
      ∑ W∈range top,aT2 h t.shape (cy x) (apo x) W:= by
    apply sum_le_sum
    intro W hW
    exact boi h t.shape _ _ W _ hne hE hv (by omega) he
      (fun _ hP j i hn=>DP.d3r Crt word hP j i hn)
      (fun _ hP hn=>atp.eu5 hh (by omega) Crt word t.shape W _ hP hn)
      (fun P hP hn=>hf.divides_leading P _ hn (fun q hq' =>
        eHv Crt word hh hchar x (hq q hq') (hp q hq') (mem_range.mp hW) hP))
  have heq :=bDM h t.shape (cy x) (apo x) (by omega) (by omega)
  unfold TerminalFloor at ht
  change triangle t.shape.U*ku t.shape (fun q j=>top+j-q*(131071-h)) ≤
    j3 h t + ∑ W∈range top,mD FX (VY Crt word t.shape W) at ht
  change (∑ W∈range top,aT2 h t.shape (cy x) (apo x) W) +
    ZN h t.shape (cy x) (apo x) =
    triangle t.shape.U*ku t.shape (fun q j=>top+j-q*(131071-h)) at heq
  change ZN h t.shape (cy x) (apo x)≤j3 h t
  omega
theorem eiO {b:fO} {f :lz} (hp:0<f.natDegree)
  (reject : ∀ x :Test b,cy x≤f.natDegree→apo x≤gY f→False) :
  ∃ i:aKj b,f.natDegree=i.val+1∧vm f (seedCap b i) := by
 have he :f.natDegree≤(row b).bDZ:= by
  by_contra! hlo
  exact reject none hlo (Nat.zero_le _)
 let i:aKj b:=⟨f.natDegree-1,by omega⟩
 have hidx :f.natDegree=i.val+1 := by dsimp [i]; omega
 refine ⟨i,hidx,(Qc _ _).mp ?_⟩
 by_contra! hlow
 exact reject (some i) hidx.ge hlow
end
end P5_7_2
end
section
set_option autoImplicit true
namespace P5_7_2
noncomputable section
open Polynomial
open P5 (I K p jG)
open P5_7 (YQ)
open cu (L vm yq)
open DP (jF zG aKF VY)
open Qt (gY Qc)
def c1 :Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L) (x :Test b),
      TerminalFloor h (Lc b x) (VY Crt word)
def c2 :Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi →
    ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L),
      Nonempty (Donors b Crt word)
def c3:Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Window b M.iF→M.shift∉Γ → ∀ H,YQ M F H →
    ∀ (D:jF M.iF.toNat),D.block 0=H→D.block 1=H.map (frobenius L p) →
    NodeUnits D→(∀ γ∈Γ,aKF D (M.label γ) (F.scalar γ)) →
    ∀ (Crt:zG D),Donors b Crt (wordLift M) →
      Nonempty (bkU b M F (VY Crt (wordLift M)))
def c4 :Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi → ∀ x :Test b,
    j3 h (Lc b x)<ZN h (Lc b x).shape (cy x) (apo x)
def c5:Prop :=W0 (· ≤ 2)
def c6:Prop :=W0 (3 ≤ ·)
private theorem budget (b:fO) :
  (row b).prefixFee+(row b).Z1≤(jX b).cap:= by
 fin_cases b <;> decide
private theorem guards (b:fO) :
  0<(jX b).lo∧(jX b).hi<131071 ∧
  (aU b).shape.m*A<p∧(row b).bDZ≤(row b).Z1 := by
 fin_cases b <;> decide
open cu (FX qD kr)
private theorem ecU {u del} (M:jG u del) {Γ} (F:P1.bje A M Γ)
   (T:Finset K) (hT:T⊆Γ) {f :lz} (hf :0<f.natDegree) (hs :vm f 0)
   (hr : ∀ γ∈T,yq f (M.label γ) (F.scalar γ)=0) :T.card≤f.natDegree := by
 classical
 let g:=f.map (qD 0)
 have hc (z :K) (i:ℕ) :qD z (f.coeff i)=(f.coeff i).coeff 0:= by
   have h:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (nI (hs i))
   conv_lhs=>rw [h]
   simp [qD]
 have he (z :K) :f.map (qD z)=g:= by
   ext i
   simp only [g,coeff_map,hc]
 have hn:g≠0:= by
   intro hz
   have hlead:=congrArg (fun G:FX[X]=>G.coeff f.natDegree) hz
   simp only [g,coeff_map,hc,coeff_zero] at hlead
   have h:=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
     (nI (hs f.natDegree))
   have hfn :f≠0:= fun h0=> by simp [h0] at hf
   exact (leadingCoeff_ne_zero.mpr hfn) (h.trans (by rw [hlead,map_zero]))
 let val := fun γ=>kr (F.scalar γ)
 have hi:Set.InjOn val (T:Set K) :=
   fun _ ha _ hb h=>F.distinct (hT ha) (hT hb) (qQ.bNe h)
 calc
   T.card=(T.image val).card:=(Finset.card_image_of_injOn hi).symm
   _≤g.natDegree :=Polynomial.card_le_degree_of_subset_roots (by
     intro x hx
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
     apply (Polynomial.mem_roots hn).mpr
     change g.eval (val γ)=0
     rw [← he (M.label γ),Polynomial.eval_map]
     exact hr γ hγ)
   _≤f.natDegree :=Polynomial.natDegree_map_le
private theorem count (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6)
    (b:fO) :P5_7.RegularBound A (jX b) := by
  classical
  intro u del M Γ F hw hshift H bY
  have hwin:Window b M.iF:=hw
  have hlo:=hwin.1
  have hhi:=hwin.2
  have hl: (jX b).lo≤M.iF.toNat := by omega
  have hu:M.iF.toNat≤(jX b).hi:= by omega
  obtain ⟨glo,ghi,gchar,gdegree⟩:=guards b
  obtain ⟨D,hfirst,hadjacent,hnode,hres⟩:=bW4 M F H bY
  obtain ⟨Crt⟩:=atp.dRH D
  obtain ⟨donors⟩:=h2 b _ hl hu D hnode Crt (wordLift M)
  obtain ⟨Q⟩:=h3 b u del M Γ F hwin hshift H bY D hfirst hadjacent hnode hres Crt donors
  let T:=Γ \ Q.gH
  have hT:T⊆Γ:=Finset.sdiff_subset
  have hp: (Γ \ T).card≤(row b).prefixFee := by
    apply (Finset.card_le_card ?_).trans Q.paid_bound
    intro γ hγ
    obtain ⟨hmem,hnot⟩:=Finset.mem_sdiff.mp hγ
    by_contra hn
    exact hnot (Finset.mem_sdiff.mpr ⟨hmem,hn⟩)
  suffices hkept:T.card≤(row b).Z1 by
    exact (Finset.card_sdiff_add_card_eq_card hT ▸ Nat.add_le_add hp hkept).trans (budget b)
  have cover : ∀ γ∈T,∃ q∈Q.parents,P5_7.axy M F q γ:= fun γ hγ =>
    (Q.Eh γ (hT hγ)).resolve_left (Finset.mem_sdiff.mp hγ).2
  by_cases hm:T.Nonempty
  · obtain ⟨γ,hγ⟩:=hm
    obtain ⟨q,hq,_⟩:=cover γ hγ
    obtain ⟨f,hf⟩:=czI.proof Q.parents ⟨q,hq⟩ Q.geometric
    obtain ⟨i,he,hs⟩:=eiO (b:=b) hf.positive (fun x hE hv =>
      (h4 b _ hl hu x).not_ge (eqx Crt (wordLift M) (glo.trans_le hl)
        (hu.trans_lt ghi) gchar Q.geometric Q.terminal_pass hf x (h1 b _ hl hu D hnode Crt _ x) hE hv))
    have roots : ∀ η∈T,yq f (M.label η) (F.scalar η)=0:= by
      intro η hη
      obtain ⟨q',hq',hon⟩:=cover η hη
      have hz :=RingHom.mem_ker.mp (hon (hf.aiq q' hq'))
      simpa only [coe_eval₂RingHom,eval₂_C,yq] using hz
    by_cases hzero :gY f=0
    · exact (ecU M F T hT hf.positive ((Qc f 0).mp hzero.le) roots).trans
        ((he.trans_le (Nat.succ_le_of_lt i.isLt)).trans gdegree)
    have hseed :=Nat.pos_of_ne_zero hzero
    have hred:Dt.Reduced f :=⟨hf.positive,hf.primitive,hf.separable⟩
    by_cases hsmall:f.natDegree≤2
    · exact h5 b u del M Γ F hwin hshift H bY i f hred he hsmall hseed hs T hT roots
    · exact h6 b u del M Γ F hwin hshift H bY i f hred he (by omega) hseed hs T hT roots
  · simp [Finset.not_nonempty_iff_eq_empty.mp hm]
end
end P5_7_2
end
