import ProximityPrize.SubmissionLower.ZB2eCyc
set_option Elab.async false
open _root_ renaming Nat.cast_add → z6H, Nat.cast_le → z9h, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_ofNat → zWE, Nat.cast_one → z4o, Nat.cast_sub → zjK
section
set_option autoImplicit true
namespace qpVOZ2b
open P6 (p)
open P6_7 (RectTail)
open P6_7_2_3 (degree oldAgreement persistentRate BlendOK NativeOK nativeRate)
abbrev gap (D:ℕ) :=oldAgreement-D
abbrev GF (a h g n k v w:ℕ) :Prop :=
  n*(p-a*g)*w≤h*k*(p*w-v*g)
abbrev persistNum (D g:ℕ) :ℕ :=
  (2*g-1)*(oldAgreement+2*262144*D)*gap D+(262144-D)*oldAgreement
abbrev heightNum (D e extra c W:ℕ) :ℕ :=
  max ((e*(c+1)+e+extra)*gap D)
    ((7+6*e)*gap D+((2*e+1)*262144+(6*e-2)*W-3*e*e*D))
abbrev thresholdDen (g:ℕ) :ℕ:=3*g*1275
abbrev thresholdNum (d g:ℕ) :ℕ:=d+(4*g+8)*thresholdDen g
theorem threshold {v w z a :ℕ} (hw:0<w) (h:v≤ min z a*w) :
    (v :ℚ)/w≤ min (z :ℚ) (a :ℚ) := by
  apply (div_le_iff₀ (show (0:ℚ)<w by exact_mod_cast hw)).2
  exact_mod_cast h
private theorem blend_le {a h g n k v w:ℕ}
    (hg:0<g) (hk :0<k) (hw:0<w)
    (ha : (a :ℚ)<(p:ℚ)/g) (hv : (v :ℚ)/w≤a)
    (hc:GF a h g n k v w) :
    (n:ℚ)/k*((p:ℚ)/g-a)/((p:ℚ)/g-(v :ℚ)/w)≤h:= by
  have hgq: (0:ℚ)<g:= by exact_mod_cast hg
  have hkq: (0:ℚ)<k := by exact_mod_cast hk
  have hwq: (0:ℚ)<w:= by exact_mod_cast hw
  have hs :a*g≤p:= by exact_mod_cast (le_div_iff₀ hgq).mp ha.le
  have hL: ((p:ℚ)/g-a)*g=(p:ℚ)-a*g:= by
    rw [sub_mul,div_mul_cancel₀ _ hgq.ne']
  have hR: ((p:ℚ)/g-(v :ℚ)/w)*g*w=(p:ℚ)*w-v*g:= by
    rw [sub_mul,div_mul_cancel₀ _ hgq.ne',sub_mul]
    rw [mul_right_comm,div_mul_cancel₀ _ hwq.ne']
  have hpos :=sub_pos.mpr (hv.trans_lt ha)
  have htq: (v :ℚ)*g≤(p:ℚ)*w:= by
    apply sub_nonneg.mp
    rw [← hR]
    exact mul_nonneg (mul_nonneg hpos.le hgq.le) hwq.le
  have ht:v*g≤p*w:= by exact_mod_cast htq
  have hcq:=(z9h (α:=ℚ)).2 hc
  push_cast [zjK hs,zjK ht] at hcq
  change (n:ℚ)*((p:ℚ)-a*g)*w≤(h:ℚ)*k*((p:ℚ)*w-v*g) at hcq
  rw [← hL,← hR] at hcq
  apply (div_le_iff₀ hpos).2
  rw [div_mul_eq_mul_div₀]
  apply (div_le_iff₀ hkq).2
  apply (mul_le_mul_iff_right₀ (mul_pos hgq hwq)).1
  convert hcq using 1 <;> ring
private theorem base_le {a h g n k :ℕ}
    (hg:0<g) (hk :0<k) (ha : (a :ℚ)<(p:ℚ)/g)
    (hc:GF a h g n k 0 1) :
    (1-(a :ℚ)/((p:ℚ)/g))*((n:ℚ)/k)≤h:= by
  have hq: (0:ℚ)<(p:ℚ)/g:=(zqJ a).trans_lt ha
  have hs :=blend_le hg hk (by decide :0<(1 :ℕ)) ha
    (show ((0:ℕ) :ℚ)/((1 :ℕ) :ℚ)≤a by simp) hc
  simp only [Nat.cast_zero,zero_div,sub_zero] at hs
  rw [← div_self hq.ne',← sub_div,mul_comm,← mul_div_assoc]
  exact hs
private theorem affine_eq (u v k :ℕ) (hk : (0:ℚ)<k) :
    (u:ℚ)+(v :ℚ)/k=((u*k+v :ℕ) :ℚ)/k := by
  push_cast
  rw [add_div,mul_div_cancel_right₀ _ hk.ne']
private theorem persistent_eq (b:RectTail) (g:ℕ) (hg:0<g)
    (hk :0<gap (degree b)) :
    persistentRate b g=(persistNum (degree b) g:ℚ)/(oldAgreement*gap (degree b) :ℕ) := by
  have hA: (0:ℚ)<oldAgreement:= by decide
  have hK: (0:ℚ)<gap (degree b) := by exact_mod_cast hk
  unfold persistentRate
  dsimp only [persistNum]
  push_cast [zjK (show 1≤2*g by omega)]
  field_simp [hA.ne',hK.ne']; ring
theorem persistent {b:RectTail} {g a h:ℕ} {d z :ℚ}
    (hg:0<g) (hk :0<gap (degree b)) (ha : (a :ℚ)<(p:ℚ)/g)
    (hc:GF a h g (persistNum (degree b) g) (oldAgreement*gap (degree b)) 0 1) :
    BlendOK b g ((p:ℚ)/g) d z a h:= by
  left
  rw [persistent_eq b g hg hk]
  exact base_le hg (Nat.mul_pos (by decide) hk) ha hc
theorem linear {b:RectTail} {a h:ℕ} {d z :ℚ}
    (hk :0<gap (degree b)) (ha : (a :ℚ)<(p:ℚ)/(1 :ℕ))
    (hc:GF a h 1 (gap (degree b)+3*262144) (gap (degree b)) 0 1) :
    BlendOK b 1 ((p:ℚ)/(1 :ℕ)) d z a h:= by
  right
  left
  refine ⟨rfl,?_⟩
  have hK: (0:ℚ)<gap (degree b) := by exact_mod_cast hk
  rw [show (1 :ℚ)+3*262144/(gap (degree b) :ℚ) =
      ((gap (degree b)+3*262144 :ℕ) :ℚ)/(gap (degree b) :ℚ) by
    simpa only [z6H,z2R,zWE,z4o,Nat.one_mul]
      using affine_eq 1 (3*262144) _ hK]
  exact base_le (by decide) hk ha hc
theorem quadratic {b:RectTail} {a h z :ℕ} {d:ℚ}
    (hk :0<gap (degree b)) (ha : (a :ℚ)<(p:ℚ)/(2 :ℕ))
    (hz :16≤ min z a)
    (hc:GF a h 2 (13*gap (degree b)+8*262144) (gap (degree b)) 16 1) :
    BlendOK b 2 ((p:ℚ)/(2 :ℕ)) d z a h:= by
  right
  right
  left
  have hzq: (16:ℚ)≤ min (z :ℚ) (a :ℚ) := by exact_mod_cast hz
  refine ⟨rfl,hzq,?_⟩
  have hK: (0:ℚ)<gap (degree b) := by exact_mod_cast hk
  rw [show (13:ℚ)+8*262144/(gap (degree b) :ℚ) =
      ((13*gap (degree b)+8*262144 :ℕ) :ℚ)/(gap (degree b) :ℚ) by
    simpa only [z6H,z2R,zWE]
      using affine_eq 13 (8*262144) _ hK]
  simpa only [zWE,z4o,div_one] using
    blend_le (by decide :0<(2 :ℕ)) hk (by decide :0<(1 :ℕ)) ha
      (show ((16:ℕ) :ℚ)/((1 :ℕ) :ℚ)≤a by simpa using hzq.trans (min_le_right _ _)) hc
private theorem native_eq (D e extra c W:ℕ) (hk :0<gap D) :
    nativeRate D e extra c W=(heightNum D e extra c W:ℚ)/gap D:= by
  have hK: (0:ℚ)<gap D:= by exact_mod_cast hk
  rw [nativeRate,Nat.cast_max,← max_div_div_right hK.le,z2R,
    mul_div_cancel_right₀ _ hK.ne',← affine_eq _ _ _ hK]
theorem native {b:RectTail} {g a h z d extra c W M:ℕ}
    (hg:3≤g) (hk :0<gap (degree b)) (ha : (a :ℚ)<(p:ℚ)/g)
    (hW:NativeOK (degree b) g extra c W M)
    (hz :thresholdNum d g≤ min z a*thresholdDen g)
    (hc:GF a h g (heightNum (degree b) g extra c W) (gap (degree b))
      (thresholdNum d g) (thresholdDen g)) :
    BlendOK b g ((p:ℚ)/g) ((d:ℚ)/1275) z a h:= by
  right
  right
  right
  have hg0:0<g:= by omega
  have hw:0<thresholdDen g:= by positivity
  have hgq: (0:ℚ)<g:= by exact_mod_cast hg0
  have ht: ((d:ℚ)/1275)/(3*(g:ℚ))+4*g+8 =
      (thresholdNum d g:ℚ)/thresholdDen g:= by
    push_cast
    field_simp [hgq.ne']; ring
  refine ⟨hg,extra,c,W,M,hW,?_⟩
  dsimp only
  rw [ht,native_eq _ _ _ _ _ hk]
  have hzq:=threshold hw hz
  exact ⟨hzq,blend_le hg0 hk hw ha (hzq.trans (min_le_right _ _)) hc⟩
end qpVOZ2b
end
section
set_option autoImplicit true
namespace qgfN14a
noncomputable section
open P6_7 (RectTail)
open P6_7_2 (Bs free)
open P6_7_2_3 qVWQWJa
open TD (arC)
open scoped BigOperators
private def originN (b:RectTail) (o:Origin) (k :Fin 4) :ℕ :=
  ∑ j,introCap b o j*arC (originShape b o) k j
private def capN (b:RectTail) (o:Origin) (k :Fin 4) :ℕ :=
  min (originN b o k) (BC b k).num.toNat
private theorem cap_cast (b:RectTail) (o:Origin) (k :Fin 4) :
    memberCap b o 0 k=(capN b o k :ℚ) := by
  have h:BC b k=((BC b k).num.toNat :ℕ) := by
    cases b <;> fin_cases k <;> rfl
  change min (originBox b o k) (BC b k)= _
  rw [capN,Nat.cast_min,← h]
  simp only [originBox,kK,originN,Nat.cast_sum,z2R]
private abbrev aEt (b:RectTail) (o:Origin) :=capN b o 2
private abbrev aEv (b:RectTail) (o:Origin) :=min (capN b o 1) (aEt b o)
private theorem rank_y (D B R:ℕ) (hg:0<oldAgreement-D)
    (h:4*262144*D*B*(oldAgreement-D)+(262144-D)*10*oldAgreement ≤
      R*10*oldAgreement*(oldAgreement-D)) :
    4*((262144 :ℚ)/oldAgreement)*D*B/10+(↑(262144-D) :ℚ)/↑(oldAgreement-D) ≤
      (R:ℚ) := by
  have hgq: (0:ℚ)<(oldAgreement-D:ℕ) :=Nat.cast_pos.mpr hg
  have hq:4*262144*(D:ℚ)*B*↑(oldAgreement-D)+↑(262144-D)*10*oldAgreement ≤
      (R:ℚ)*10*oldAgreement*↑(oldAgreement-D) := by exact_mod_cast h
  apply le_of_mul_le_mul_right _ (show (0:ℚ)<10*oldAgreement*↑(oldAgreement-D) by
    unfold oldAgreement
    positivity)
  convert hq using 1
  unfold oldAgreement
  field_simp [hgq.ne']
  ring
private theorem rank_z (D B J R:ℕ) (hb:0<B)
    (h:9*262144*D*4*J*B+(B+1)*10*oldAgreement*B ≤
      R*10*oldAgreement*B+9*262144*D*2*J*J) :
    ((262144 :ℚ)/oldAgreement)*D*(4*J-2*(J:ℚ)*J/B)*9/10+B+1≤(R:ℚ) := by
  have hbq: (0:ℚ)<B:=Nat.cast_pos.mpr hb
  have hq:9*262144*(D:ℚ)*4*J*B+((B:ℚ)+1)*10*oldAgreement*B ≤
      (R:ℚ)*10*oldAgreement*B+9*262144*(D:ℚ)*2*J*J:= by exact_mod_cast h
  apply le_of_mul_le_mul_right _ (show (0:ℚ)<10*oldAgreement*(B:ℚ) by
    unfold oldAgreement
    positivity)
  have he :
      (((262144 :ℚ)/oldAgreement)*D*(4*J-2*(J:ℚ)*J/B)*9/10+B+1) *
        (10*oldAgreement*(B:ℚ)) =
      9*262144*(D:ℚ)*4*J*B+((B:ℚ)+1)*10*oldAgreement*B-9*262144*(D:ℚ)*2*J*J:= by
    unfold oldAgreement
    field_simp [hbq.ne']
    ring
  rw [he]
  linarith only [hq]
private theorem rank_check (b:RectTail) (o:Origin) :
    let D:=degree b
    let B:=aEt b o
    let J:=aEv b o
    let A:=oldAgreement
    0<B ∧
    4*262144*D*B*(A-D)+(262144-D)*10*A≤ residueN b o 1*10*A*(A-D) ∧
    9*262144*D*4*J*B+(B+1)*10*A*B≤ residueN b o 2*10*A*B+9*262144*D*2*J*J:= by
  cases b <;> fin_cases o <;> decide
private theorem rank_le (b:RectTail) (o:Origin) (k :Fin 4) :
    rankPrice b o k≤ residue b o k := by
  obtain ⟨hb,hy,hz⟩:=rank_check b o
  have hg:0<oldAgreement-degree b:= by cases b <;> decide
  have hbq: (aEt b o:ℚ)≠0:=(Nat.cast_pos.mpr hb: (0:ℚ)<aEt b o).ne'
  simp only [rankPrice,cap_cast,← Nat.cast_min,ite_eq_right hbq]
  fin_cases k
  · exact zqJ _
  · exact rank_y (degree b) (aEt b o) (residueN b o 1) hg hy
  · exact rank_z (degree b) (aEt b o) (aEv b o) (residueN b o 2) hb hz
  · exact zqJ _
private def freeN (B J U a h:ℕ) :Fin 4→ℕ :=
  ![(a+1)*U,(a+1)*(B-J)+h*U,(a+1)*J+U,h*J+B]
private theorem free_order (b:RectTail) (i:FreeTest) :
    (free b (freeStage i)).J≤(free b (freeStage i)).B:= by
  cases b <;> fin_cases i <;> decide
private theorem free_cast (b:RectTail) (o:Origin) (i:FreeTest) (k :Fin 4) :
    freePrice b i ((bgt b).freeSeed o i) ((bgt b).freeHeight o i) k+freeAllowance b i k =
      (freeN (free b (freeStage i)).B (free b (freeStage i)).J (free b (freeStage i)).U
        (freeSeedN b o i) (freeHeightN b o i) k :ℚ) := by
  simp only [freePrice,freeAllowance,Tl,pointWeight,bgt]
  have hs :=free_order b i
  generalize free b (freeStage i)=s at hs ⊢
  generalize freeSeedN b o i=a
  generalize freeHeightN b o i=h
  fin_cases k <;> simp [freeN,z6H,z2R,zjK hs] <;> ring
private theorem free_check (b:RectTail) (o:Origin) (i:FreeTest) :
    let s :=free b (freeStage i)
    ∀ k,freeN s.B s.J s.U (freeSeedN b o i) (freeHeightN b o i) k≤ residueN b o k := by
  cases b <;> fin_cases o <;> fin_cases i <;> decide
private def coeff (r w a :ℕ) :ℕ:=if r=0 then a else max ((r+1)*w) a
private theorem coeff_eq (r w a :ℕ) :
    (if r=0 then (a :ℚ)/(r+1 :ℕ) else max (w:ℚ) ((a :ℚ)/(r+1 :ℕ))) =
      (coeff r w a :ℚ)/(r+1 :ℕ) := by
  have hd: (0:ℚ)<(r+1 :ℕ) :=Nat.cast_pos.mpr (Nat.succ_pos r)
  have ha (x :ℚ) : ((r+1 :ℕ) :ℚ)*(x/(r+1 :ℕ))=x := by field_simp
  by_cases hr :r=0
  · simp only [coeff,hr,ite_true]
  · apply mul_left_cancel₀ hd.ne'
    simp only [coeff,ite_eq_right hr,mul_max_of_nonneg _ _ hd.le,ha,Nat.cast_max,
      z2R]
private def terminalN (r B J U z a h:ℕ) :Fin 4→ℕ :=
  let d:=coeff r U z+coeff r U (a+1)
  let y :=B-J
  let c:=coeff r y h
  let j:=if r=0 then 0 else (r+1)*J
  ![d*U,d*y+2*U*c,d*J+2*U*j+(r+1)*(2*U),J*c+(y+J)*j+(r+1)*B]
private theorem terminal_cast (b:RectTail) (o:Origin) (k :Fin 4) :
    let s :=(Bs b).terminal
    let r :=(Bs b).paidOrder
    ((r+1 :ℕ) :ℚ) *
      (terminalPrice b ((bgt b).terminalZ o) ((bgt b).terminalT o)
        ((bgt b).terminalHeight o) k+terminalAllowance b k) =
      (terminalN r s.B s.J s.U (terminalZNT b o) (terminalSeedN b o) (terminalHeightN b o) k :ℚ) := by
  simp only [terminalPrice,terminalAllowance,pointWeight,bgt]
  generalize (Bs b).terminal=s
  generalize (Bs b).paidOrder=r
  generalize terminalZNT b o=z
  generalize terminalSeedN b o=a
  generalize terminalHeightN b o=h
  rw [← z4o (R:=ℚ),← z6H]
  simp only [coeff_eq]
  have hd: ((r :ℚ)+1)≠0:= by positivity
  have hj: (if r=0 then (0:ℚ) else (s.J:ℚ)) =
      ((if r=0 then 0 else (r+1)*s.J:ℕ) :ℚ)/(r+1 :ℕ) := by
    by_cases hr :r=0 <;> simp only [hr,ite_true,ite_false,Nat.cast_zero,zero_div,
      z2R,z6H,z4o]
    field_simp [hd]
  rw [hj]
  simp only [terminalN]
  generalize (if r=0 then 0 else (r+1)*s.J:ℕ)=j
  fin_cases k <;> simp [z6H,z2R] <;> field_simp [hd]
private theorem terminal_check (b:RectTail) (o:Origin) :
    let s :=(Bs b).terminal
    let r :=(Bs b).paidOrder
    ∀ k,terminalN r s.B s.J s.U (terminalZNT b o) (terminalSeedN b o) (terminalHeightN b o) k ≤
      (r+1)*(residueN b o k+terminalDualN b o k) := by
  cases b <;> fin_cases o <;> decide
private theorem terminal_le (b:RectTail) (o:Origin) (k :Fin 4) :
    terminalPrice b ((bgt b).terminalZ o) ((bgt b).terminalT o)
      ((bgt b).terminalHeight o) k+terminalAllowance b k ≤
      residue b o k+terminalDual b o k := by
  apply le_of_mul_le_mul_left _ (show (0:ℚ)<((Bs b).paidOrder+1 :ℕ) by positivity)
  rw [terminal_cast]
  simpa only [residue,terminalDual,z2R,z6H] using
    (z9h (α:=ℚ)).mpr (terminal_check b o k)
private theorem free_stop (b:RectTail) (o:Origin) (i:FreeTest) (k :Fin 4) :
    (priceAt (bgt b) o (freeStop i)+bAY b (freeStop i)) k ≤
      a3D b o (freeStop i) k := by
  have hi: (freeStop i).val<6:= by
    have :=i.isLt
    change i.val+1<6
    omega
  have h0:freeStop i≠0:= by
    intro h
    have hv :i.val+1=0:=congrArg Fin.val h
    omega
  have h6:freeStop i≠terminalStop:= by
    intro h
    rw [h] at hi
    exact (by decide : ¬ (terminalStop:bAL).val<6) hi
  have inv : (⟨(freeStop i).val-1,by
      have :=i.isLt
      change i.val+1-1<5
      omega⟩:FreeTest)=i:=Fin.ext (Nat.add_sub_cancel _ _)
  simp only [Pi.add_apply,priceAt,bAY,ite_eq_right h0,dite_eq_left hi,inv,a3D,
    ite_eq_right h6,add_zero,free_cast,residue]
  exact (z9h (α:=ℚ)).mpr (free_check b o i k)
theorem proof :qVWQWJa.c3:= by
  intro b o s k
  have h0: (priceAt (bgt b) o 0+bAY b 0) k≤a3D b o 0 k := by
    simpa only [priceAt,bAY,ite_true,Pi.add_apply,Pi.zero_apply,add_zero,
      a3D,ite_eq_right (by decide : (0:bAL)≠terminalStop)] using rank_le b o k
  have h6: (priceAt (bgt b) o terminalStop+bAY b terminalStop) k ≤
      a3D b o terminalStop k := by
    simpa only [priceAt,bAY,ite_eq_right (by decide : (terminalStop:bAL)≠0),
      dite_eq_right (by decide : ¬ (terminalStop:bAL).val<6),Pi.add_apply,
      a3D,ite_true] using terminal_le b o k
  fin_cases s
  · exact h0
  · exact free_stop b o 0 k
  · exact free_stop b o 1 k
  · exact free_stop b o 2 k
  · exact free_stop b o 3 k
  · exact free_stop b o 4 k
  · exact h6
end
end qgfN14a
end
