import ProximityPrize.SubmissionLower.DR
import ProximityPrize.SubmissionLower.Z3wMysc
import ProximityPrize.SubmissionLower.ZS1sWBc
import ProximityPrize.SubmissionLower.ZGAUtmc
import ProximityPrize.SubmissionLower.ZGSvmVd
import ProximityPrize.SubmissionLower.ZPNEdXb
set_option Elab.async false
open _root_ renaming Finset.range → z4x, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_ite_eq' → zhO, Fintype.card → zhP, Fintype.card_le_of_injective → zWJ, Fintype.sum_sigma → zla
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
section
set_option autoImplicit true
namespace qeXVAea
open qoWrama
open qHde8fc (Ground aD yv)
open fP (cF xH oG)
open scoped BigOperators
open private R0 from ProximityPrize.SubmissionLower.DR
noncomputable section
theorem nG (e :aY) :
    cP (aD e.val)=52+(3*e.val 0+e.val 2+2*e.val 3) := by
  rw [Sj,oG]
private theorem aNn {e v :aY}
    (h:cP (aD v.val)<cP (aD e.val)) :
    dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  unfold dZ
  omega
private theorem i7 {cut:ℕ} (m:gU cut) :
    cut≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
      m.val 1+2*m.val 2 + 3*m.val 3≤56:= by
  obtain ⟨_,hl,hu,_⟩:=m.property
  rw [xH] at hl hu
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
private theorem a2O {cut:ℕ} {m n:gU cut}
    (hb:m.val 1=n.val 1) (hc:m.val 2=n.val 2) (hf :m.val 3=n.val 3) :
    m=n:= by
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · change m.val 0=n.val 0
    omega
  · exact hb
  · exact hc
  · exact hf
private theorem iN {cut b c f :ℕ} (m:gU cut)
    (h:c< m.val 2∨f< m.val 3) :cE cut (b,c,f) m=0:= by
  rcases h with h | h <;> simp [cE,yv,Nat.choose_eq_zero_of_lt h]
private def kg (a c f :ℕ) (h:a+c+f≤52) :aY :=
  ⟨Finsupp.equivFunOnFinite.symm ![a,52 - c - f-a,c,f],by
    rw [cF]
    change a+(52 - c - f-a)+c+f=52
    omega⟩
private def upper (c f :ℕ) :ℕ:=min (52 - c - f) (56-(2*c+3*f))
private theorem bqe {cut:ℕ} (m:gU cut) :
    cut - (2*m.val 2 + 3*m.val 3)≤ m.val 1∧m.val 1≤upper (m.val 2) (m.val 3) := by
  obtain ⟨hl,hu⟩:=i7 m
  have hd:=cF m.val
  rw [m.property.1] at hd
  unfold upper
  omega
theorem c5k (e :aY) (cut:ℕ) (hcut:cap (e.val 2+2*e.val 3)+1≤ cut+e.val 0) :
    cE cut (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val)) := by
  classical
  let S:=Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
  change cE cut (aD e.val)∈S
  have hsingle (n:ℕ) : ∀ m:gU cut,m.val 2+m.val 3=n →
      m.val 2≤e.val 2→m.val 3≤e.val 3→Pi.single m (1 :Ground)∈S:= by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm hc hf
      let c:=m.val 2
      let f :=m.val 3
      let L:=cut - (2*c+3*f)
      let U:=upper c f
      let w:=U + 1 - L
      have hU₀:U≤52 - c - f :=min_le_left _ _
      have hU₁:U≤56-(2*c+3*f) :=min_le_right _ _
      obtain ⟨hL,hU⟩:L≤ m.val 1∧m.val 1≤U:=bqe m
      have hd:=cF m.val
      rw [m.property.1] at hd
      obtain ⟨_,hmax⟩:=i7 m
      have hcap:U + 2*c+3*f≤ cap (e.val 2+2*e.val 3) := by
        unfold cap
        dsimp only [c,f] at *
        omega
      have hw:w≤e.val 0:= by
        dsimp only [w,L] at *
        omega
      let v (i:Fin w) :aY:=kg i.val c f (by omega)
      have hv (i:Fin w) :aD (v i).val=(52 - c - f - i.val,c,f) :=rfl
      have hbefore (i:Fin w) :dZ (v i)<dZ e := by
        apply aNn
        rw [nG,nG]
        change 52+(3*i.val+c+2*f)<_
        omega
      let y (i:Fin w) :Ground :=if U - i.val=m.val 1 then 1 else 0
      obtain ⟨coef,hcoef⟩:=qKVdmob.SX (52 - c - f) U w
        (by omega) hU₀ (by dsimp only [w]; omega) y
      let g:gU cut→Ground :=
        ∑ i:Fin w,coef i•cE cut (aD (v i).val)
      have hg:g∈S:= by
        apply Submodule.sum_mem
        intro i _
        exact S.smul_mem _ (Submodule.subset_span ⟨⟨v i,hbefore i⟩,rfl⟩)
      have hbox (z :gU cut) (hz :c<z.val 2∨f<z.val 3) :g z=0:= by
        simp only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv]
        apply Finset.sum_eq_zero
        intro i _
        rw [iN z hz,mul_zero]
      let δ:gU cut→Ground :=Pi.single m (1 :Ground)
      have hfit (z :gU cut) (h₂:z.val 2=c) (h₃:z.val 3=f) :g z=δ z := by
        obtain ⟨hl,hu⟩:=bqe z
        rw [h₂,h₃] at hl hu
        change L≤z.val 1 at hl
        change z.val 1≤U at hu
        let j:Fin w:=⟨U - z.val 1,by dsimp only [w]; omega⟩
        have hj:U - j.val=z.val 1 := by dsimp only [j]; omega
        have heq :g z=y j:= by
          simpa only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv,cE,
            yv,Prod.fst,Prod.snd,h₂,h₃,hj,Nat.choose_self,Nat.cast_one,mul_one] using hcoef j
        rw [heq]
        change (if U - j.val=m.val 1 then 1 else 0)=δ z
        rw [hj]
        by_cases hzm:z=m
        · subst z
          simp [δ]
        · have hne :z.val 1≠m.val 1 := fun h=>hzm (a2O h h₂ h₃)
          simp [δ,hne,Pi.single_eq_of_ne hzm]
      have hrest:δ - g∈S:= by
        apply R0
        intro z hz
        have hsmall:z.val 2≤ c∧z.val 3≤f := by
          by_contra ho
          have hor :c<z.val 2∨f<z.val 3:= by omega
          have hne :z≠m:= by
            rintro rfl
            exact ho ⟨le_rfl,le_rfl⟩
          apply hz
          rw [Pi.sub_apply,hbox z hor,sub_zero]
          simp [δ,hne]
        have hlt:z.val 2+z.val 3<n:= by
          by_contra! hle
          have hmatch :z.val 2=c∧z.val 3=f := by dsimp only [c,f] at hsmall ⊢; omega
          exact hz (by rw [Pi.sub_apply,hfit z hmatch.1 hmatch.2,sub_self])
        exact ih _ hlt z rfl (hsmall.1.trans hc) (hsmall.2.trans hf)
      simpa only [sub_add_cancel] using S.add_mem hrest hg
  apply R0 S
  intro m hm
  have hle :m.val 2≤e.val 2∧m.val 3≤e.val 3:= by
    by_contra hn
    exact hm (iN m (by omega))
  exact hsingle _ m rfl hle.1 hle.2
end
end qeXVAea
end
section
set_option autoImplicit true
namespace qeXVAea
open qoWrama

open fP (cF)
theorem proof :qoWrama.c1 := by
  intro e _ hhi
  let a :=e.val 0
  let b:=e.val 1
  let c:=e.val 2
  let f :=e.val 3
  have hd:a+b+c+f=52 := by simpa only [cF] using e.property
  have hcost:=nG e
  have hweight:3*a+c+2*f≤27:= by omega
  obtain ⟨j,hj,hc,hi⟩:=eLq a b c f hd hweight
  let i:=oldIndex a (c+2*f)
  refine ⟨i+1,Or.inr ⟨j,hj,hc.trans hcost.symm,?_⟩,c5k e (i+1) ?_⟩
  · rw [hi]
    change ((i+1 :ℕ) :ℤ)≤(i:ℤ)+1
    simp
  · change cap (c+2*f)+1≤ i+1+a
    dsimp only [i,oldIndex]
    omega
end qeXVAea
end
section
set_option autoImplicit true
namespace q1US8Va
open qK9H6va (offset)
open qxuyiwe (h55 profileCutoff)
open fP (qI Qg aAs)
open scoped BigOperators
noncomputable section
private theorem hist_len:h55.length=99:=rfl
private theorem hist_count (k :ℕ) (hk :k<99) :
    qI 57 (groupCount k)=h55[k]! := by
  have h:(List.range 99).all (fun k=>decide (qI 57 (groupCount k)=h55[k]!))=true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h k (List.mem_range.mpr hk))
private def gapEquiv (k :Fin 99) :
    (Σ i:Fin 57,Fin (groupCount k.val i.val)) ≃
      Fin (h55[(k.cast hist_len.symm).val]) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin,← Qg]
    simpa only [← getElem!_pos,Fin.val_cast] using hist_count k.val k.isLt)
private def pack (p:Pivot) :qxuyiwe.Pivot h55 :=
  ⟨p.1.cast hist_len.symm,gapEquiv p.1 p.2⟩
private theorem pack_injective :Function.Injective pack := by
  rintro ⟨k,s⟩ ⟨k',s'⟩ hp
  have hk :k=k' := Fin.ext (congrArg (fun p:qxuyiwe.Pivot h55=>p.1.val) hp)
  subst k'
  have h:gapEquiv k s=gapEquiv k s' := eq_of_heq (Sigma.mk.inj hp).2
  exact congrArg (Sigma.mk k) ((gapEquiv k).injective h)
def ix (p:qxuyiwe.Pivot h55) :Fin 57 :=
  ((gapEquiv (p.1.cast hist_len)).symm p.2).1
private theorem ix_pack (p:Pivot) :ix (pack p)=p.2.1 := by
  change ((gapEquiv p.1).symm (gapEquiv p.1 p.2)).1=p.2.1
  rw [Equiv.symm_apply_apply]
theorem selected_le_eligible (r :ℕ) :
    zhP (Selected (56 - r) (155 - r)) ≤
      zhP (qxuyiwe.FF ix (offset r) (profileCutoff 55 55 (offset r))) := by
  let f (p:Selected (56 - r) (155 - r)) :
      qxuyiwe.FF ix (offset r) (profileCutoff 55 55 (offset r)) :=
    ⟨pack p.val,by
      have hp:=p.property
      rw [ix_pack]
      change (p.val.1.val :ℤ)+p.val.2.1.val<99 - 55 - offset r+55 ∧
        -offset r≤p.val.2.1.val
      unfold offset
      omega⟩
  exact zWJ f fun _ _ h =>
    Subtype.ext (pack_injective (congrArg Subtype.val h))
theorem selected_mono (lo:ℕ) {w w' : ℕ} (h:w≤w') :
    zhP (Selected lo w)≤zhP (Selected lo w') :=
  zWJ
    (fun p:Selected lo w=>(⟨p.val,p.property.1,p.property.2.trans_le h⟩:Selected lo w'))
    (fun _ _ hp=>Subtype.ext (congrArg (fun p:Selected lo w' => p.val) hp))
def byIndex (w i:ℕ) :ℕ :=
  qI 99 fun k=>if k+i<w then groupCount k i else 0
def byWeight (lo w:ℕ) :ℕ :=
  qI 57 fun i=>if lo≤ i∧i≤w∧w - i<99 then groupCount (w - i) i else 0
theorem selected_card (lo w:ℕ) :
    zhP (Selected lo w) =
      qI 57 fun i=>if lo≤ i then byIndex w i else 0:= by
  classical
  calc
    _ = ∑ p:Pivot,if lo≤p.2.1.val∧p.1.val+p.2.1.val<w then 1 else 0:= by
      simp only [Selected,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]
    _ = ∑ k :Fin 99,∑ i:Fin 57,
          if lo≤ i.val∧k.val+i.val<w then groupCount k.val i.val else 0:= by
      rw [zla]
      refine zUo rfl fun k _ => ?_
      rw [zla]
      refine zUo rfl fun i _ => ?_
      by_cases h:lo≤ i.val∧k.val+i.val<w <;> simp [h]
    _ = _:= by
      rw [Finset.sum_comm,Qg]
      refine zUo rfl fun i _ => ?_
      by_cases hi:lo≤ i.val <;> simp [hi,byIndex,Qg]
private theorem index_succ (w i:ℕ) :
    byIndex (w+1) i=byIndex w i +
      (if i≤w∧w - i<99 then groupCount (w - i) i else 0) := by
  simp only [byIndex,aAs]
  have step (k :ℕ) :
      (if k+i<w+1 then groupCount k i else 0) =
        (if k+i<w then groupCount k i else 0) +
        (if k=w - i∧i≤w then groupCount k i else 0) := by
    by_cases h:k+i<w
    · simp [h,show k+i<w+1 by omega,show ¬ (k=w - i∧i≤w) by omega]
    · have he :k+i<w+1↔k=w - i∧i≤w:= by omega
      simp only [he,ite_eq_right h,Nat.zero_add]
  have extra :
      (∑ k∈z4x 99,if k=w - i∧i≤w then groupCount k i else 0) =
        (if i≤w∧w - i<99 then groupCount (w - i) i else 0) := by
    by_cases hi:i≤w
    · simp only [hi,and_true,true_and,zhO,Finset.mem_range]
    · simp [hi]
  calc
    _ = ∑ k∈z4x 99,((if k+i<w then groupCount k i else 0) +
        (if k=w - i∧i≤w then groupCount k i else 0)) :=
      zUo rfl fun k _=>step k
    _ = _:= by rw [zfW,extra]
theorem selected_succ (lo w:ℕ) :
    zhP (Selected lo (w+1))=zhP (Selected lo w)+byWeight lo w:= by
  simp only [selected_card,byWeight,aAs,← zfW]
  refine zUo rfl fun i _ => ?_
  by_cases hi:lo≤ i
  · simp only [hi,true_and,ite_true,index_succ]
  · simp [hi]
end
end q1US8Va
end
section
set_option autoImplicit true
namespace q1US8Va
open fP (aAs)
open xE (denominator U1)
open P6_6_2 (oppositeBound)
open scoped BigOperators
private def colMass (lo:ℕ) :ℕ :=
  if lo=10 then 5744 else if lo=11 then 5743 else if lo=12 then 5738 else
    (U1 55 56 16-U1 55 ((lo:ℤ) - 1) 16).toNat
private theorem col_step (i:ℕ) (hlo:10≤ i) (hhi:i≤56) :
    colMass i=colMass (i+1)+byIndex 112 i:= by
  have h:(List.range' 10 47).all (fun i=>decide (colMass i=colMass (i+1)+byIndex 112 i))=true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨hlo,by omega⟩))
private theorem select_step (i:ℕ) (hi:i<57) :
    zhP (Selected i 112)=zhP (Selected (i+1) 112)+byIndex 112 i:= by
  have step (j:ℕ) :
      (if i≤j then byIndex 112 j else 0) =
        (if i+1≤j then byIndex 112 j else 0) +
        (if j=i then byIndex 112 j else 0) := by
    by_cases he :j=i
    · subst j
      simp
    · by_cases h:i≤j
      · simp [he,h,show i+1≤j by omega]
      · simp [he,h,show ¬ i+1≤j by omega]
  simp only [selected_card,aAs]
  calc
    _ = ∑ j∈z4x 57,((if i+1≤j then byIndex 112 j else 0) +
        (if j=i then byIndex 112 j else 0)) :=zUo rfl fun j _=>step j
    _ = _:= by rw [zfW,zhO,ite_eq_left (Finset.mem_range.mpr hi)]
private theorem card112 (i:ℕ) (hlo:10≤ i) (hhi:i≤57) :
    zhP (Selected i 112)=colMass i:= by
  refine Nat.decreasingInduction' (P:= fun j=>zhP (Selected j 112)=colMass j)
    (fun j hj hjlo ih => ?_) hhi ?_
  · rw [select_step j hj,col_step j (hlo.trans hjlo) (by omega),ih]
  · rw [show colMass 57=0 by rfl,selected_card,aAs]
    exact Finset.sum_eq_zero fun j hj =>
      ite_eq_right (by have :=Finset.mem_range.mp hj; omega)
theorem zo (r :ℕ) (hr :r≤43) :
    oppositeBound (flag r)≤zhP (Selected (56 - r) (155 - r)) := by
  have h:oppositeBound (flag r)≤ colMass (56 - r) := by
    have h:(List.range 44).all (fun r=>decide (oppositeBound (flag r)≤ colMass (56 - r)))=true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp h r (List.mem_range.mpr (by omega)))
  exact (h.trans_eq (card112 _ (by omega) (by omega)).symm).trans
    (selected_mono _ (by omega))
theorem middle44 :5503≤zhP (Selected 12 111) := by
  have hb:zhP (Selected 12 112)=5738:=card112 12 (by decide) (by decide)
  rw [selected_succ 12 111,show byWeight 12 111=235 by rfl] at hb
  omega
theorem middle45:5257≤zhP (Selected 11 110) := by
  have hb:zhP (Selected 11 112)=5743:=card112 11 (by decide) (by decide)
  rw [selected_succ 11 111,selected_succ 11 110,
    show byWeight 11 111=235 by rfl,show byWeight 11 110=251 by rfl] at hb
  omega
theorem middle46:4999≤zhP (Selected 10 109) := by
  have hb:zhP (Selected 10 112)=5744 :=card112 10 (by decide) (by decide)
  rw [selected_succ 10 111,selected_succ 10 110,selected_succ 10 109,
    show byWeight 10 111=235 by rfl,show byWeight 10 110=251 by rfl,
    show byWeight 10 109=259 by rfl] at hb
  omega
private def rowMass (n:ℕ) :ℕ :=
  (denominator ((n:ℤ) - 1) - denominator ((n:ℤ) - 52)).toNat
private theorem row_step (n:ℕ) (hn:n<53) :
    rowMass (n+1)=rowMass n+byWeight 9 (55+n) := by
  have h:(List.range 53).all (fun n=>decide (rowMass (n+1)=rowMass n+byWeight 9 (55+n)))=true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h n (List.mem_range.mpr hn))
private theorem cfP (n:ℕ) (hn:n≤53) :
    rowMass n≤zhP (Selected 9 (55+n)) := by
  induction n with
  | zero=>exact Nat.zero_le _
  | succ n ih =>
    rw [row_step n (by omega),show 55+(n+1)=(55+n)+1 by omega,selected_succ]
    exact Nat.add_le_add_right (ih (by omega)) _
theorem be1 (r :ℕ) (hr :47≤ r) :
    oppositeBound (flag r)≤zhP (Selected (56 - r) (155 - r)) := by
  by_cases hz :100≤ r
  · have ho: (flag r).order≤0:= by
      change (100:ℤ)-(r :ℤ)≤0
      omega
    rw [oppositeBound,ite_eq_left ho]
    exact Nat.zero_le _
  have h:oppositeBound (flag r)≤ rowMass (100 - r) := by
    have h:(List.range' 47 53).all (fun r=>decide (oppositeBound (flag r)≤ rowMass (100 - r)))=true := by
      decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp h r (List.mem_range'_1.mpr ⟨hr,by omega⟩))
  have hc:=cfP (100 - r) (by omega)
  rw [show 55+(100 - r)=155 - r by omega] at hc
  let f (p:Selected 9 (155 - r)) :Selected (56 - r) (155 - r) :=
    ⟨p.val,by have :=p.property.1; omega,p.property.2⟩
  exact h.trans (hc.trans (zWJ f fun _ _ hp =>
    Subtype.ext (congrArg (fun p:Selected (56 - r) (155 - r)=>p.val) hp)))
end q1US8Va
end
section
set_option autoImplicit true
namespace q1US8Va
open qK9H6va (iO)
private theorem ay9 {q:ℕ} (h:iO q=55) :q=55:= by
  unfold iO P6_6_1.asu at h
  split at h
  · by_cases hq:q≤56
    · simpa only [min_eq_left hq] using h
    · rw [min_eq_right (by omega)] at h
      omega
  · split at h
    · have hb:=min_le_right q (54 - 2*((q - 112)/2))
      omega
    · have hb:=min_le_right q (35 - 2*((q - 130)/2))
      omega
theorem proof :qxuyiwe.c5:= by
  refine ⟨ix,?_⟩
  intro q hd r
  have hq:=ay9 hd
  subst q
  refine Nat.le_trans ?_ (selected_le_eligible r.val)
  refine (rank_le_opposite r.val).trans ?_
  by_cases he :r.val≤43
  · exact zo r.val he
  by_cases hl:47≤ r.val
  · exact be1 r.val hl
  have h44 :r.val = 44∨r.val = 45∨r.val = 46:= by omega
  rcases h44 with h | h | h
  · rw [h]
    exact (show P6_6_2.oppositeBound (flag 44)≤5503 by decide).trans middle44
  · rw [h]
    exact (show P6_6_2.oppositeBound (flag 45)≤5257 by decide).trans middle45
  · rw [h]
    exact (show P6_6_2.oppositeBound (flag 46)≤4999 by decide).trans middle46
end q1US8Va
end
