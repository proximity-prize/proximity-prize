import ProximityPrize.SubmissionLower.ZGSvmVd
set_option Elab.async false
section
set_option autoImplicit true
namespace qKSECDd
open xE (denominator)
open aRR (DW)
open aAZ (Jc)
open private b0m from ProximityPrize.SubmissionLower.BH
open private bPo aAD from ProximityPrize.SubmissionLower.BH
open Finset
local notation "D" => denominator
local notation "P" => DW
private def poly (q r n:ℤ) :ℤ :=
  12*n*aAD q r+6*n*(n-1)*(72*q^2+4*(21+6*r)*q+2*(11+7*r+r^2)) +
    2*n*(n-1)*(2*n-1)*(144*q+4*(21+6*r))+288*n^2*(n-1)^2
private def stride12 (u:ℤ) :ℤ :=
  if u<0 then 0 else poly (u%12/6) (u%6) (u/12)
private theorem stride12_step (u:ℤ) :stride12 (u+12) - stride12 u=24*D u:= by
  by_cases hu:u<0
  · rw [Jc _ hu]
    by_cases h:u+12<0
    · simp [stride12,hu,h]
    · simp [stride12,hu,h,show (u+12)/12=0 by omega,poly]
  have ha : (u+12)/12=u/12+1 := by omega
  have hb: (u+12)%12=u%12 := by omega
  have hc: (u+12)%6=u%6:= by omega
  have hd:u/6=u%12/6+2*(u/12) := by omega
  simp only [stride12,not_lt.mpr (le_of_not_gt hu),show ¬ u+12<0 by omega,ite_false,ha,hb,hc]
  rw [show 24*D u=12*(2*D u) by ring,bPo _ (by omega),hd]
  unfold poly aAD
  ring
private def stride4 (u:ℤ) :ℤ:=stride12 u+stride12 (u+4)+stride12 (u+8)
private theorem stride4_step (u:ℤ) :stride4 (u+4) - stride4 u=24*D u:= by
  unfold stride4
  rw [show u+4+4=u+8 by ring,show u+4+8=u+12 by ring]
  linear_combination stride12_step u
def oldPrim (j:ℤ) :ℤ:=24*j*D 1710-P j
def oppPrim (m j:ℤ) :ℤ:=P (m+j) - stride4 (4*j+3*m-5130)
def prodPrim (m t j:ℤ) :ℤ :=
  let a :=jO m
  oldPrim j-(24*j*D (1710-3*t)-P (m+j-3*t)+P (m+j-3*a)-P (j-2*t) +
    P (j+a-1711)+P (j+a-1712)+P (j+a-1713))
theorem old_step (j:ℤ) :oldPrim (j+1) - oldPrim j=24*(D 1710 - D j) := by
  unfold oldPrim
  linear_combination -b0m j
private theorem step_add (a j:ℤ) :P (a+(j+1))-P (a+j)=24*D (a+j) := by
  rw [← add_assoc]
  exact b0m _
theorem opp_step (m j:ℤ) :
    oppPrim m (j+1) - oppPrim m j=24*(D (m+j) - D (4*j+3*m-5130)) := by
  unfold oppPrim
  rw [show 4*(j+1)+3*m-5130=(4*j+3*m-5130)+4 by ring]
  linear_combination step_add m j - stride4_step (4*j+3*m-5130)
theorem prod_step (m t j:ℤ) :
    prodPrim m t (j+1) - prodPrim m t j=24*(D 1710 - D j - kernelValue m t j) := by
  have s (c:ℤ) :P (c+1)-P c=24*D c:=b0m c
  simp only [prodPrim,kernelValue]
  linear_combination (norm:=ring_nf) old_step j+s (m+j-3*t) -
    s (m+j-3*jO m)+s (j-2*t) -
    s (j+jO m-1711) - s (j+jO m-1712) - s (j+jO m-1713)
theorem sum_step (g f :ℤ→ℤ) (step : ∀ j,g (j+1) - g j=24*f j)
    {lo hi:ℕ} (h:lo≤hi) :
    24*(∑ j∈Ico lo hi,f j)=g hi-g lo:= by
  rw [sum_Ico_eq_sum_range]
  have hs (n:ℕ) :24*(∑ i∈range n,f (↑(lo+i:ℕ)))=g (↑(lo+n:ℕ))-g lo:= by
    induction n with
    | zero=>simp
    | succ n ih =>
      rw [sum_range_succ,mul_add,ih,Nat.add_succ,Nat.cast_succ,← step]
      ring
  simpa only [Nat.add_sub_of_le h] using hs (hi-lo)
end qKSECDd
end
section
set_option autoImplicit true
namespace qKSECDd
open P6_6_2 (Offset xR al2)
open xE (denominator)
open aRR (DW afw)
open private b0m from ProximityPrize.SubmissionLower.BH
open Finset
local notation "D" => denominator
local notation "P" => DW
private def reflect (i:Offset) :Offset :=
  if h:i.val<1710 then ⟨1709-i.val,by change 1709-i.val<4710; omega⟩ else i
private theorem reflect_inv (i:Offset) :reflect (reflect i)=i:= by
  by_cases hi:i.val<1710
  · have he :reflect i=⟨1709-i.val,by change 1709-i.val<4710; omega⟩:=dite_eq_left hi
    rw [he,reflect,dite_eq_left (by dsimp; omega)]
    apply Fin.ext
    dsimp
    omega
  · simp [reflect,hi]
private def perm:Offset ≃ Offset :=⟨reflect,reflect,reflect_inv,reflect_inv⟩
private theorem perm_eq (i:Offset) : perm i=reflect i:=rfl
private def entry (h:ℕ) (p:ℕ→Fin 11→ℕ) (j:ℕ) :ℤ :=
  if hj:j<4710 then xR (2150+h) (perm ⟨j,hj⟩) (p j) else 0
private def Slice (h lo hi:ℕ) (b:ℤ) :Prop :=
  ∃ p,24 * ∑ j∈Ico lo hi,entry h p j≤b
private theorem append {h lo mid hi:ℕ} {a b:ℤ} (hl:lo≤ mid) (hr :mid≤hi)
    (ha :Slice h lo mid a) (hb:Slice h mid hi b) :Slice h lo hi (a+b) := by
  obtain ⟨p,hp⟩:=ha
  obtain ⟨q,hq⟩:=hb
  let s := fun j=>if j< mid then p j else q j
  refine ⟨s,?_⟩
  rw [← sum_Ico_consecutive (entry h s) hl hr,mul_add]
  have l: (∑ j∈Ico lo mid,entry h s j) = ∑ j∈Ico lo mid,entry h p j :=
    sum_congr rfl fun j hj=> by simp only [entry,s,ite_eq_left (mem_Ico.mp hj).2]
  have r : (∑ j∈Ico mid hi,entry h s j) = ∑ j∈Ico mid hi,entry h q j :=
    sum_congr rfl fun j hj=> by simp only [entry,s,ite_eq_right (not_lt.mpr (mem_Ico.mp hj).1)]
  rw [l,r]
  exact add_le_add hp hq
private theorem slice {h lo hi:ℕ} (p:Fin 11→ℕ) (g f :ℤ→ℤ)
    (hl:lo≤hi) (step : ∀ j,g (j+1)-g j=24*f j)
    (he : ∀ j∈Ico lo hi,entry h (fun _=>p) j≤f j) :
    Slice h lo hi (g hi-g lo) :=
  ⟨fun _=>p,(mul_le_mul_of_nonneg_left (sum_le_sum he) (by decide)).trans_eq (sum_step g f step hl)⟩
private theorem entry_neg (h j:ℕ) (hj:j<1710) (p:ℕ→Fin 11→ℕ) :
    entry h p j=(xR (2150+h) ⟨1709-j,by change 1709-j<4710; omega⟩ (p j) :ℤ) := by
  simp only [entry,dite_eq_left (show j<4710 by omega),perm_eq,reflect,dite_eq_left hj]
private def finish (h:ℕ) :ℕ :=
  min (860+h) (min 1190 (min (879+91*h/100) (min (929+73*h/100) (993+49*h/100))))
private def start (h:ℕ) :ℕ:=if h<120 then finish h else min (finish h) (915+49*h/100)
private def next (h b v :ℕ) :ℕ:=min (finish h) (max b v)
private def b1 (h:ℕ) :ℕ:=next h (start h) (864+69*h/100)
private def b2 (h:ℕ) :ℕ:=next h (b1 h) (880+70*h/100)
private def b3 (h:ℕ) :ℕ:=next h (b2 h) (899+70*h/100)
private def b4 (h:ℕ) :ℕ:=next h (b3 h) (min (890+82*h/100) (934+65*h/100))
private theorem finish_le (h:ℕ) :finish h≤860+h∧finish h≤1190 :=
  ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _)⟩
private theorem Ph (h:ℕ) :start h≤finish h:= by
  unfold start
  split
  · rfl
  · exact min_le_left _ _
private theorem next_bounds (h b v :ℕ) (hb:b≤finish h) :
    b≤next h b v∧next h b v≤finish h:=⟨le_min hb (le_max_left _ _),min_le_left _ _⟩
def row (h:ℕ) :ℤ :=
  let m:ℤ:=850-h
  (oppPrim m (start h) - oppPrim m 0) +
  (prodPrim m 288 (b1 h) - prodPrim m 288 (start h)) +
  (prodPrim m 352 (b2 h) - prodPrim m 352 (b1 h)) +
  (prodPrim m 416 (b3 h) - prodPrim m 416 (b2 h)) +
  (prodPrim m 480 (b4 h) - prodPrim m 480 (b3 h)) +
  (prodPrim m 512 (finish h) - prodPrim m 512 (b4 h)) +
  (oldPrim 1710 - oldPrim (finish h))+P m
theorem grade_cap (h:ℕ) (hh:h<400) :
    ∃ p,24*(al2 (2150+h) p:ℤ)≤ row h:= by
  let m:ℤ:=850-h
  have hf :=finish_le h
  have hstart:=Ph h
  have hs :start h≤1141 := by
    unfold start
    split
    · omega
    · exact (min_le_right _ _).trans (by omega)
  have h1 :start h≤b1 h∧b1 h≤finish h:=next_bounds h _ _ hstart
  have h2 :b1 h≤b2 h∧b2 h≤finish h:=next_bounds h _ _ h1.2
  have h3:b2 h≤b3 h∧b3 h≤finish h:=next_bounds h _ _ h2.2
  have h4 :b3 h≤b4 h∧b4 h≤finish h:=next_bounds h _ _ h3.2
  have ho:Slice h 0 (start h) (oppPrim m (start h)-oppPrim m 0) := by
    apply slice (fun _=>0) _ _ (Nat.zero_le _) (opp_step m)
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    rw [entry_neg _ _ (by omega)]
    exact opp_le _ _ hh (by omega) (by omega) _ (by dsimp; omega) _
  have hp (t lo hi:ℕ) (ht:t≤512) (hl:lo≤hi) (hr :hi≤finish h) :
      Slice h lo hi (prodPrim m t hi-prodPrim m t lo) := by
    apply slice (Ej t) _ _ hl (prod_step m t)
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    rw [entry_neg _ _ (by omega)]
    exact prod_le _ _ _ hh (by omega) (by omega) ht _ (by dsimp; omega)
  have hL:Slice h (finish h) 1710 (oldPrim 1710-oldPrim (finish h)) := by
    apply slice (fun _=>0) _ _ (by omega) old_step
    intro j hj
    have hj' := (mem_Ico.mp hj).2
    rw [entry_neg _ _ hj']
    exact old_le _ _ hh _ (by dsimp; omega) _
  have hR:Slice h 1710 4710 (P m) := by
    let g:ℤ→ℤ:= fun j => -P (2560-(h:ℤ)-j)
    have hg (j:ℤ) :g (j+1)-g j=24*D (2559-(h:ℤ)-j) := by
      dsimp [g]
      rw [show 2560-(h:ℤ)-(j+1)=2559-h-j by ring,show 2560-(h:ℤ)-j=(2559-h-j)+1 by ring]
      linear_combination b0m (2559-h-j)
    have he :=slice (h:=h) (lo:=1710) (hi:=4710) (fun _=>0) g
      (fun j=>D (2559-(h:ℤ)-j)) (by decide) hg
    have hval :g 4710 - g 1710=P m:= by
      dsimp [g,m]
      rw [afw (2560-(h:ℤ)-4710) (by omega)]
      congr 1 <;> ring
    rw [← hval]
    apply he
    intro j hj
    obtain ⟨hj₀,hj₁⟩:=mem_Ico.mp hj
    simp only [entry,dite_eq_left hj₁,perm_eq,reflect,dite_eq_right (not_lt.mpr hj₀)]
    have hb:=pos_le h (j-1710) hh ⟨j,hj₁⟩ (by dsimp; omega) (fun _=>0)
    convert hb using 2
    omega
  have e1 :=append (Nat.zero_le _) h1.1 ho (hp 288 _ _ (by decide) h1.1 h1.2)
  have e2 :=append (Nat.zero_le _) h2.1 e1 (hp 352 _ _ (by decide) h2.1 h2.2)
  have e3:=append (Nat.zero_le _) h3.1 e2 (hp 416 _ _ (by decide) h3.1 h3.2)
  have e4 :=append (Nat.zero_le _) h4.1 e3 (hp 480 _ _ (by decide) h4.1 h4.2)
  have e5:=append (Nat.zero_le _) h4.2 e4 (hp 512 _ _ (by decide) h4.2 le_rfl)
  have e6:=append (Nat.zero_le _) (by omega) e5 hL
  obtain ⟨p,hp⟩:=append (Nat.zero_le _) (by decide) e6 hR
  refine ⟨fun r=>p (perm.symm r).val,?_⟩
  rw [Nat.Ico_zero_eq_range] at hp
  rw [al2,Nat.cast_sum]
  change 24*(∑ r :Offset,(xR (2150+h) r (p (perm.symm r).val) :ℤ))≤ row h
  have he : (∑ r :Offset,(xR (2150+h) r (p (perm.symm r).val) :ℤ)) =
      ∑ j∈range 4710,entry h p j:= by
    rw [← Fin.sum_univ_eq_sum_range,← perm.sum_comp (fun r =>
      (xR (2150+h) r (p (perm.symm r).val) :ℤ))]
    refine sum_congr rfl fun j _ => ?_
    have hj:j.val<4710 :=j.isLt
    simp only [Equiv.symm_apply_apply,entry,dite_eq_left hj]
  rw [he]
  exact hp
end qKSECDd
end
section
set_option autoImplicit true
namespace qKSECDd
open Finset
private def chunk (lo:ℕ) :ℤ :=
  row lo+row (lo+1)+row (lo+2)+row (lo+3)+row (lo+4)
private def gxo:ℕ→ℤ
  | 0=>0
  | n+1=>gxo n+chunk (5*n)
private theorem sums_eq (n:ℕ) :gxo n = ∑ j∈range (5*n),row j:= by
  induction n with
  | zero=>simp [gxo]
  | succ n ih =>
    rw [gxo,ih,Nat.mul_succ,sum_range_add]
    simp [chunk,sum_range_succ,add_assoc]
private theorem checked {n:ℕ} {a b:ℤ} (h:gxo n=a) (e :chunk (5*n)=b-a) :
    gxo (n+1)=b:= by rw [gxo,h,e]; ring
local notation "asr" h=>checked h rfl
private theorem r0:gxo 0=0:=rfl
private theorem r1 :gxo 1=0xd40b644a0e0:=asr r0
private theorem r2 :gxo 2=0x1a6fcdf7a4f0:=asr r1
private theorem r3:gxo 3=0x278d4f9109b8:=asr r2
private theorem r4 :gxo 4=0x349943a1d100:=asr r3
private theorem r5:gxo 5=0x4193b2d410f0:=asr r4
private theorem r6:gxo 6=0x4e7ca5eb2d58:=asr r5
private theorem r7:gxo 7=0x5b5425c3e788:=asr r6
private theorem r8:gxo 8=0x681a3b5497c8:=asr r7
private theorem r9:gxo 9=0x74ceefad3d00:=asr r8
private theorem dz :gxo 10=0x81724bf7b678:=asr r9
private theorem dD:gxo 11=0x8e045977d338:=asr dz
private theorem dK:gxo 12=0x9a85218b8bf8:=asr dD
private theorem e8:gxo 13=0xa6f4adab1250:=asr dK
private theorem gD:gxo 14=0xb35307690af0:=asr e8
private theorem gx :gxo 15=0xbfa038729c88:=asr gD
private theorem iu:gxo 16=0xcbdc4a8faa30:=asr gx
private theorem kD:gxo 17=0xd80747a2e220:=asr iu
private theorem lH :gxo 18=0xe42139a9f860:=asr kD
private theorem kR:gxo 19=0xf02a2abdb538:=asr lH
private theorem jV:gxo 20=0xfc2225123010 :=asr kR
private theorem lp:gxo 21=0x1080932f6ddb0:=asr jV
private theorem kZ:gxo 22=0x113df5ed6cb68:=asr lp
private theorem lQ:gxo 23=0x11fa4b338ad08:=asr kZ
private theorem nJ:gxo 24=0x12b593abf1838:=asr lQ
private theorem nP:gxo 25=0x136fd02d3e968:=asr nJ
private theorem qA:gxo 26=0x1429013dbbc08:=asr nP
private theorem tj:gxo 27=0x14e1277aa4d08:=asr qA
private theorem qH :gxo 28=0x1598438602440:=asr tj
private theorem oQ:gxo 29=0x164e560c532f8:=asr qH
private theorem xM:gxo 30=0x17035fb674580:=asr oQ
private theorem xd:gxo 31=0x17b76131a13f0:=asr xM
private theorem r32 :gxo 32=0x186a5b2894fb0:=asr xd
private theorem A4 :gxo 33=0x191c4e4945b58:=asr r32
private theorem BY:gxo 34=0x19cd3b40bc530:=asr A4
private theorem Cp:gxo 35=0x1a7d22bf08150:=asr BY
private theorem EZ:gxo 36=0x1b2c056da2010 :=asr Cp
private theorem Iz :gxo 37=0x1bd9e3f8d8c58:=asr EZ
private theorem IB:gxo 38=0x1c86bf0b76988:=asr Iz
private theorem Ku:gxo 39=0x1d32975362b40:=asr IB
private theorem Hz :gxo 40=0x1ddd6d7cd8948:=asr Ku
private theorem ID :gxo 41=0x1e874234b1518:=asr Hz
private theorem LU:gxo 42=0x1f30162afe8f0:=asr ID
private theorem Vr :gxo 43=0x1fd7ea0efb3f8:=asr LU
private theorem Xv :gxo 44=0x207ebe9360c78:=asr Vr
private theorem Xw:gxo 45=0x21249467231a0:=asr Xv
private theorem Cw:gxo 46=0x21c96c3f1a8b0:=asr Xw
private theorem Cx :gxo 47=0x226d46cb548c8:=asr Cw
private theorem zB:gxo 48=0x231024c284b38:=asr Cx
private theorem CR:gxo 49=0x23b206d631760:=asr zB
private theorem Db:gxo 50=0x2452edbe821f8:=asr CR
private theorem LB:gxo 51=0x24f2da2ce79d8:=asr Db
private theorem De :gxo 52=0x2591ccdbad9e0:=asr LB
private theorem LD:gxo 53=0x262fc67de7cd8:=asr De
private theorem OD:gxo 54=0x26ccc7c8b99b0:=asr LD
private theorem OK :gxo 55=0x2768d17087718:=asr OD
private theorem LH :gxo 56=0x2803e42966450:=asr OK
private theorem Vb:gxo 57=0x289e00aac6580:=asr LH
private theorem Vc:gxo 58=0x293727ab9bc40:=asr Vb
private theorem WV:gxo 59=0x29cf59e5bd730:=asr Vc
private theorem OL:gxo 60=0x2a6698118de60:=asr WV
private theorem OM:gxo 61=0x2afce2e304698:=asr OL
private theorem OP:gxo 62=0x2b923b1a931d0:=asr OM
private theorem Vd:gxo 63=0x2c26a171ffc70:=asr OP
private theorem r64 :gxo 64=0x2cba16a947768:=asr Vd
private theorem WZ:gxo 65=0x2d4c9b79452c0:=asr r64
private theorem r66:gxo 66=0x2dde30a3ae758:=asr WZ
private theorem r67:gxo 67=0x2e6ed6e1be478:=asr r66
private theorem r68:gxo 68=0x2efe8ef730640:=asr r67
private theorem r69:gxo 69=0x2f8d599ea1a00:=asr r68
private theorem r70:gxo 70=0x301b379c065d8:=asr r69
private theorem W7:gxo 71=0x30a829a8f6e38:=asr r70
private theorem Vo:gxo 72=0x3134308cda4f8:=asr W7
private theorem r73:gxo 73=0x31bf4d09124f0:=asr Vo
private theorem r74 :gxo 74=0x32497fe0f6708:=asr r73
private theorem r75:gxo 75=0x32d2c9d6ec088:=asr r74
private theorem r76:gxo 76=0x335b2baf11868:=asr r75
private theorem r77:gxo 77=0x33e2a62d6cd60:=asr r76
private theorem r78:gxo 78=0x34693a17ef4c8:=asr r77
private theorem r79:gxo 79=0x34eee8333f330:=asr r78
private theorem Xe :gxo 80=0x3573b14699d58:=asr r79
theorem amJ: (∑ j∈range 400,row j)=0x3573b14699d58:=(sums_eq 80).symm.trans Xe
end qKSECDd
end
section
set_option autoImplicit true
namespace qKSECDd
open P6_6_2 (kJ rankBand)
open Finset
theorem proof :qwbsesc.c3:= by
  classical
  change ∃ p:kJ,rankBand p 2150 2550≤0x23a2868838a6
  let p:kJ:= fun q=>if hg:q-2150<400 then (grade_cap (q-2150) hg).choose
    else fun _ _=>0
  refine ⟨p,?_⟩
  have hs :24*(rankBand p 2150 2550:ℤ) ≤ ∑ h∈range 400,row h:= by
    rw [rankBand,sum_Ico_eq_sum_range,Nat.cast_sum,mul_sum]
    apply sum_le_sum
    intro h hh
    have hg:h<400:=mem_range.mp hh
    have he :p (2150+h)=(grade_cap h hg).choose := by
      simp only [p,Nat.add_sub_cancel_left,dif_pos hg]
    rw [he]
    exact (grade_cap h hg).choose_spec
  rw [amJ] at hs
  omega
end qKSECDd
end
