import ProximityPrize.SubmissionLower.ZTqYzLd
import ProximityPrize.SubmissionLower.ZhDU57c
import ProximityPrize.SubmissionLower.ZTOdMMe
set_option Elab.async false
open _root_ renaming Module.finrank → zsE, Polynomial → zM1, Polynomial.uniqueFactorizationMonoid → zV6, Submodule → zpI, Submodule.mem_bot → zLn
section
set_option autoImplicit true
namespace qMNIwTb
noncomputable section
open P5 (I p)
open P5_7_2 (Aux anM O2)
open cu (L FX Shape aZ Equation Jet triangle)
open DP Polynomial Finset
open private bKE from ProximityPrize.SubmissionLower.D6
open private ddi from ProximityPrize.SubmissionLower.C
open private c4y from ProximityPrize.SubmissionLower.ZdZNCPb
theorem Yf (h:ℕ) (a :Aux) :
  anM h a.dI a.shape=Mq h a - 1 := by
 unfold anM O2 Mq
 omega
theorem width_room {h:ℕ} {a :Aux} (hw:aL4 h a) :
  0<Mq h a :=
 lt_of_le_of_lt (Nat.zero_le _) hw
theorem physical_to_rank {h:ℕ} (hhi:h≤131070) {D:jF h}
   (Crt:zG D) (word:I→L) (a :Aux) (hw:aL4 h a) {P:ℕ}
   (hp:zsE L (aq7 h word a.shape (anM h a.dI a.shape)) ≤
     P+Module.finrank L (complete Crt word a.shape (anM h a.dI a.shape))) :
   azS h a.shape+O3 h a (fullCap a.shape) false ≤
     bga a.shape+P+rankSum (Mq h a) (VY Crt word a.shape) := by
 let s :=a.shape
 let W:=anM h a.dI s
 have hW:W+1=Mq h a := by
   have hn:=width_room hw
   dsimp only [W,s]
   rw [Yf]
   omega
 have hcond:c69 h s W:= by
   intro q hq j _
   rw [hW]
   exact ((Nat.mul_le_mul_right _ hq).trans hw.le).trans (Nat.le_add_right _ _)
 have hv :=atp.bT9 (hhi.trans (by decide)) s W hcond
 have hc:=atp.Yw h word s W
 have hs :=agU.telescope hhi Crt word s W
 rw [hW] at hs
 have hg:ceG h s W=O3 h a (fullCap s) false := by
   unfold ceG O3 cu.ku capSum
   rw [hW]
   simp only [fullCap,Bool.false_eq_true,ite_false,Nat.sub_zero]
   rfl
 rw [hg] at hv
 change zsE L (aq7 h word s W)≤P +
   zsE L (complete Crt word s W) at hp
 change azS h s+O3 h a (fullCap s) false ≤
   bga s+P + ∑ t∈range (Mq h a),zsE FX (VY Crt word s t)
 omega
theorem historical_poles {h:ℕ} (hh:0<h) (hhi:h≤131070) {D:jF h}
    (Crt:zG D) (word:I→L) (s :Shape) (hb:s.B<p) (W:ℕ) :
    zsE L (aq7 h word s W) ≤
      (azS h s+2*h*((s.U+1)*agU.ajD s.B s.J)) +
        zsE L (complete Crt word s W) := by
  have hlocal:=aeL.of_children czW.proof aSk.proof
  simpa only [Nat.mul_assoc] using c4y hlocal hh (hhi.trans_lt (by decide)) Crt word s hb W
theorem ceiling_add_gain (h:ℕ) (a :Aux) (d:ℕ→ℕ) (hk :1≤131071-h)
   (hd : ∀ q,d q≤fullCap a.shape q) :
   aMH h a d+O3 h a d true=O3 h a d false := by
 let N :=Mq h a
 let s :=a.shape
 have hswap :
     (∑ W∈range N,Xq h a d W) =
     capSum s d (fun q j => ∑ W∈range N,if eligible h N W q j then 1 else 0) := by
   simp only [ Xq,capSum]
   rw [sum_comm]
   apply sum_congr rfl
   intro q _
   rw [sum_comm]
 unfold aMH O3
 rw [hswap,← Nat.mul_add]
 congr 1
 simp only [capSum,s,ite_true,Bool.false_eq_true,ite_false,Nat.sub_zero]
 rw [← sum_add_distrib]
 apply sum_congr rfl
 intro q _
 rw [← sum_add_distrib]
 apply sum_congr rfl
 intro j hj
 have hjq:=(mem_range_succ_iff.mp hj).trans ((hd q).trans (min_le_left _ _))
 have hq:q≤q*(131071-h) := by simpa using Nat.mul_le_mul_left q hk
 exact bKE h N q j (hjq.trans hq)
theorem cutoff_rank {h:ℕ} {D:jF h} {Crt:zG D} {word:I→L}
    (hh:0<h) (hhi:h≤131070) {a :Aux} {d:ℕ→ℕ} {V:ℕ→zpI FX Jet}
    (src :LayeredBank Crt word a d V) {W:ℕ}
    (horder : ∀ P∈V W,P≠0→Mq h a≤W+2*h*P.natDegree) :
    zsE FX (V W)≤triangle a.shape.U*Xq h a d W:= by
  classical
  let S:=((range (a.shape.B+1)).sigma (fun q=>range (d q+1))).filter
    (fun qj=>eligible h (Mq h a) W qj.1 qj.2)
  let T:=MvPolynomial.restrictTotalDegree (Fin 2) FX a.shape.U
  let coord (x :S) :V W →ₗ[FX] aZ :=
    (((lcoeff aZ (x.1.1-x.1.2)).restrictScalars FX).comp
      ((lcoeff Equation x.1.2).restrictScalars FX)).comp (V W).subtype
  let proj:V W →ₗ[FX] (S→T) :=LinearMap.pi fun x=>(coord x).codRestrict T (by
    intro P
    change (P.1.coeff x.1.2).coeff (x.1.1-x.1.2)∈T
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).2
    by_cases hz : (P.1.coeff x.1.2).coeff (x.1.1-x.1.2)=0
    · simp [hz]
    · exact (d3r Crt word (src.incl W P.2) _ _ hz).2.2)
  have hker :LinearMap.ker proj = ⊥ := by
    apply bot_unique
    intro P hP
    apply (zLn FX).mpr
    apply Subtype.ext
    by_contra hn
    let j:=P.val.natDegree
    let i:=P.val.leadingCoeff.natDegree
    have hn' : P.val≠0:=hn
    have hc: (P.val.coeff j).coeff i≠0:= by
      change (P.val.coeff P.val.natDegree).coeff P.val.leadingCoeff.natDegree≠0
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')
    have hB:=(d3r Crt word (src.incl W P.2) _ _ hc).1
    have hd:=src.support W _ P.2 j i hc
    have hp:eligible h (Mq h a) W (i+j) j :=
      ⟨atp.eu5 hh hhi Crt word a.shape W _ (src.incl W P.2) hn',
        horder _ P.2 hn'⟩
    let x :S:=⟨⟨i+j,j⟩,by simp [S,hB,hd,hp]⟩
    have hz :=congrArg (fun f :S→T=>(f x :aZ)) (LinearMap.mem_ker.mp hP)
    change (P.val.coeff j).coeff (i+j-j)=0 at hz
    rw [Nat.add_sub_cancel] at hz
    exact hc hz
  have hinj:Function.Injective proj:= by
    intro x y hxy
    let z :V W:=x+(-1 :FX)•y
    have hz :proj z=0:= calc
      _=proj x+(-1 :FX)•proj y := by dsimp only [z]; rw [map_add,map_smul]
      _=((1 :FX) + -1)•proj y := by rw [add_smul,one_smul,hxy]
      _=0:= by rw [add_neg_cancel,zero_smul]
    have hz' : z∈proj.ker :=LinearMap.mem_ker.mpr hz
    rw [hker] at hz'
    have h:=congrArg Subtype.val ((zLn FX).mp hz')
    change x.val+(-1 :FX)•y.val=(0:Jet) at h
    have hneg:y.val+(-1 :FX)•y.val=0:= calc
      _=((1 :FX) + -1)•y.val := by rw [add_smul,one_smul]
      _=0:= by rw [add_neg_cancel,zero_smul]
    have he :=congrArg (fun r :Jet=>r+y.val) h
    rw [add_assoc,add_comm ((-1 :FX)•y.val),hneg,add_zero,zero_add] at he
    exact Subtype.ext he
  have hcard:S.card=Xq h a d W:= by
    unfold S Xq capSum
    rw [card_filter,sum_sigma]
  calc
    _≤zsE FX (S→T) :=LinearMap.finrank_le_finrank_of_injective hinj
    _ = _:= by
      let:Module.Free FX T:=Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
      rw [Module.finrank_pi_fintype FX (M:= fun _:S=>T)]
      simp [T,ddi,hcard,Nat.mul_comm]
end
end qMNIwTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qMNIwTb
noncomputable section
open P5 (I p)
open P5_7_2 (Aux ChosenRow anM)
open cu (L FX aZ Equation Jet)
open DP
open gT (alm)
open Polynomial Finset UniqueFactorizationMonoid
open private cSB from ProximityPrize.SubmissionLower.T
open private eHt from ProximityPrize.SubmissionLower.ZhDU57c
private def divisor (G:Jet) :zpI FX Jet :=
 (Ideal.span ({G} : Set Jet)).restrictScalars FX
private theorem mem_divisor {G Q:Jet} : Q∈divisor G↔G∣Q:= by
 change Q∈Ideal.span ({G} : Set Jet)↔G∣Q
 exact Ideal.mem_span_singleton
private theorem common_le {h:ℕ} {D:jF h} {Crt:zG D} {word:I→L}
  {a :Aux} {G:Jet}
  (hc : ∀ Q∈complete Crt word a.shape (anM h a.dI a.shape),G∣U4 Q)
  {W:ℕ} (hW:W≤Mq h a - 1) :
  ∀ P∈VY Crt word a.shape W,G∣P:= by
 have hsub:VY Crt word a.shape (anM h a.dI a.shape)≤divisor G :=
  Submodule.span_le.mpr (by rintro _ ⟨Q,hQ,rfl⟩; exact mem_divisor.mpr (hc Q hQ))
 intro P hP
 rw [← Yf] at hW
 exact mem_divisor.mp (hsub (d3q Crt word rfl rfl rfl le_rfl hW hP))
theorem nonzero_raw {h:ℕ} {D:jF h} {Crt:zG D} {word:I→L}
    {a :Aux} {V:ℕ→zpI FX Jet} (hr :0<Mq h a)
    (hV : ∀ W,V W≤VY Crt word a.shape W)
    (hpos :0< rankSum (Mq h a) V) :
    Nonempty (ChosenRow Crt word a.dI a.shape) := by
  by_contra hn
  have hc (Q) (hQ:Q∈complete Crt word a.shape (anM h a.dI a.shape)) :
      (0:Jet)∣U4 Q:= by
    apply zero_dvd_iff.mpr
    by_contra hq
    exact hn ⟨⟨Q,hQ,hq,Nat.sub_pos_iff_lt.mp hr⟩⟩
  have hz :rankSum (Mq h a) V=0:= by
    unfold rankSum
    apply sum_eq_zero
    intro W hW
    have hbot:V W = ⊥ := bot_unique (by
      intro P hP
      exact (zLn FX).mpr (zero_dvd_iff.mp
        (common_le hc (by have :=mem_range.mp hW; omega) _ (hV W hP))))
    rw [hbot,finrank_bot]
  omega
private theorem cCz {h:ℕ} {D:jF h} {Crt:zG D} {word:I→L}
    (hh:0<h) (hhi:h≤131070) {a a₀:Aux} {d:ℕ→ℕ} {V:ℕ→zpI FX Jet}
    (src :LayeredBank Crt word a d V) (P:ChosenRow Crt word a₀.dI a₀.shape)
    (hp:a₀.shape.U<p)
    {G:Jet} (hi:Irreducible G) (hdiv :G∣P.jet) (hv :0<G.natDegree) (hm:alm G) :
    ∃ Q∈complete Crt word a.shape (anM h a.dI a.shape),¬ G∣U4 Q:= by
  by_contra! hc
  have hseed (j i:ℕ) : ((P.jet.coeff j).coeff i).totalDegree≤a₀.shape.U:= by
    by_cases hz : (P.jet.coeff j).coeff i=0
    · simp [hz]
    · have hP:P.jet∈VY Crt word a₀.shape (anM h a₀.dI a₀.shape) :=
        Submodule.subset_span ⟨P.raw,P.mem,rfl⟩
      exact (d3r Crt word hP j i hz).2.2
  have upper :rankSum (Mq h a) V≤aMH h a d:= by
    unfold rankSum aMH
    rw [mul_sum]
    apply sum_le_sum
    intro W hW
    apply cutoff_rank hh hhi src
    intro R hR hnR
    apply eHt _ _ _ hh (mem_range.mp hW) hi hv hm P.nonzero hdiv hp hseed hnR
    intro i k hk
    exact common_le hc hk _ (atp.d3s Crt word (src.incl W hR) i k)
  exact (not_lt_of_ge upper) src.DG
theorem choose_layered {h:ℕ} {D:jF h} {Crt:zG D} {word:I→L}
   (hh:0<h) (hhi:h≤131070) {a a₀:Aux} {d:ℕ→ℕ} {V:ℕ→zpI FX Jet}
   (src :LayeredBank Crt word a d V) (P:ChosenRow Crt word a₀.dI a₀.shape)
   (hp:a₀.shape.U<p) :
   ∃ Q:ChosenRow Crt word a.dI a.shape,qQ.aeH P.jet Q.jet:= by
 classical
 let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 let:UniqueFactorizationMonoid Equation :=zV6 (D:=aZ)
 let:UniqueFactorizationMonoid Jet:=zV6 (D:=Equation)
 let C:=complete Crt word a.shape (anM h a.dI a.shape)
 let F := {H :Jet // H∈factors P.jet}
 let:Finite F:=Set.finite_coe_iff.mpr (factors P.jet).finite_toSet
 let T := {H :F // ∃ G:Jet,Irreducible G∧G∣P.jet∧0<G.natDegree ∧
   alm G∧Associated G H.val}
 let test :Option T→Jet:= fun k=>k.elim 0 (fun x=>x.val.val)
 let E :C →ₗ[L] Jet:=U4.toLinearMap.comp C.subtype
 let sub (k :Option T) :zpI L C:=((divisor (test k)).restrictScalars L).comap E
 have proper (k :Option T) :sub k ≠ ⊤ := by
   suffices ∃ Q:C,¬ test k∣U4 Q.val by
     obtain ⟨Q,hQ⟩:=this
     intro hsub
     exact hQ (mem_divisor.mp (show Q∈sub k from hsub ▸ Submodule.mem_top))
   cases k with
   | none =>
     obtain ⟨Q⟩:=nonzero_raw src.cfw src.incl ((Nat.zero_le _).trans_lt src.DG)
     exact ⟨⟨Q.raw,Q.mem⟩,by simpa [test] using Q.nonzero⟩
   | some H =>
     obtain ⟨G,hi,hd,hv,hm,ha⟩:=H.property
     obtain ⟨Q,hQ,hn⟩:=cCz hh hhi src P hp hi hd hv hm
     exact ⟨⟨Q,hQ⟩,fun h=>hn (ha.dvd.trans h)⟩
 obtain ⟨Q,hQ⟩:=Submodule.exists_forall_notMem_of_forall_ne_top (K:=L) (M:=C) sub proper
 have hn:U4 Q.val≠0:= by
   intro hz
   apply hQ none
   apply mem_divisor.mpr
   change (0:Jet)∣U4 Q.val
   rw [hz]
 refine ⟨⟨Q.val,Q.property,hn,Nat.sub_pos_iff_lt.mp src.cfw⟩,?_⟩
 intro G hi hd hd' hv
 apply cSB G
 intro hm
 obtain ⟨H,hH,ha⟩:=exists_mem_factors_of_dvd P.nonzero hi hd
 let k :T:=⟨⟨H,hH⟩,⟨G,hi,hd,hv,hm,ha⟩⟩
 exact hQ (some k) (mem_divisor.mpr (ha.symm.dvd.trans hd'))
end
end qMNIwTb
end
section
set_option autoImplicit true
namespace qcT6PRb
open P5 (I)
open P5_7_2 (Aux)
open qMNIwTb (trimCap)
open cu (L FX Jet)
open DP Polynomial Finset
noncomputable section
def Admits {R:Type*} [CommSemiring R] (d:ℕ→ℕ) (P:zM1 (zM1 R)) :Prop :=
 ∀ j i,d (i+j)<j→(P.coeff j).coeff i=0
def profiled {F R:Type*} [Field F] [CommSemiring R] [Algebra F R] (d:ℕ→ℕ) :
    zpI F (zM1 (zM1 R)) where
  carrier := {P | Admits d P}
  zero_mem' := by simp [Admits]
  add_mem' := by
    intro P Q hP hQ j i hj
    simp only [coeff_add,(show Admits d P from hP) j i hj,
     (show Admits d Q from hQ) j i hj,add_zero]
  smul_mem' := by
    intro b P hP j i hj
    simp only [coeff_smul,(show Admits d P from hP) j i hj,smul_zero]
def completeAt {h:ℕ} {D:jF h} (Crt:zG D)
    (word:I→L) (a :Aux) (W:ℕ) :zpI L Source :=
  complete Crt word a.shape W ⊓ profiled (trimCap a)
def ack {h:ℕ} {D:jF h} (Crt:zG D)
    (word:I→L) (a :Aux) (W:ℕ) :zpI FX Jet :=
  Submodule.span FX (U4 '' (completeAt Crt word a W:Set Source))

end
end qcT6PRb
end
