import ProximityPrize.SubmissionLower.ZA2HeGc
import ProximityPrize.SubmissionLower.ZRtoqxb
import ProximityPrize.SubmissionLower.ZEGTqPa
set_option Elab.async false
open _root_ renaming Fin.sum_univ_succ → zCS, Fin.sum_univ_zero → zDT, Finset → zJe, Finset.sum_le_sum → zQk, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.cast_le → z9h, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_sum → zCt, Nat.cast_zero → zQq, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.sub_le_sub_right → zIu, Polynomial.uniqueFactorizationMonoid → zV6
section
set_option autoImplicit true
namespace qVWQWJa
noncomputable section
open Finset P6_7_2_3
open P6_7 (RectTail)
open P6_7_2 (prefixFee)
open TD (FP)
open scoped Classical BigOperators
private def costs :RectTail→Origin→ℕ
  | .pruned => ![0x974eda505aabc6,0x138c661830d51c7,0x1c454f11d3fe6,0,0x137673dd69931f,0,0x1e31db0f02d1a,0x1f28cb0379c553,0x9924a04e3ec06,0,0,0x28f4a9692285ab,0,0]
  | .tailOne => ![0x94f677709f9a6b,0x15a6fb41f2d4701,0x56fcde30d8b1c,0,0x16a2e44fd8fe36,0,0x295709a04cc74,0x40127638d660df,0xc4058cf9c60d0,0,0,0x31d7521554d631,0,0]
  | .tailTwo => ![0x881064dbdfdade,0x111f7eed00ba8ba,0x6d55d7b3c6030,0,0x1540b96a94daec,0,0x280083944cc2b,0x480303dba824a5,0xb2a326c378041,0,0,0x2b94736aa1fd98,0,0]
  | .tailThree => ![0x77b1e22e21e144,0x9649daf707b203,0x61cebf36be7d4,0,0x13a4a45a9d6cb6,0x9661b7c2a7f5a,0x734d79070d6be,0x36a9da10c8d77a,0xa15b2b6aec6a4,0,0,0x1e3131b3158916,0,0]
private def factorTotal :RectTail→ℕ
  | .pruned=>0x238e2e0c45f34b0
  | .tailOne=>0x28c386f7a7fcf12
  | .tailTwo=>0x237601c7d832d5d
  | .tailThree=>0x19748fefa5b651d
private def terminalNum:RectTail→ℕ
  | .pruned=>0x3e7fb20ba4da5b56
  | .tailOne=>0x555dc7b28a89478b
  | .tailTwo=>0x49cf0607ab37035c
  | .tailThree=>0x30afbed898f3e0ff
private def terminalExtra :RectTail→ℕ
  | .pruned=>0x3abe88284fa
  | .tailOne=>0
  | .tailTwo=>0
  | .tailThree=>0
private theorem factor_eq (b:RectTail) :factorBook b=factorTotal b:= by
  have row (o:Origin) : (∑ j:Fin 3,a4Q b o j*introCap b o j)=costs b o:= by
    simp only [zCS,zDT,add_zero]
    cases b <;> fin_cases o <;> with_unfolding_all rfl
  simp only [factorBook,row,zCS,zDT,add_zero]
  cases b <;> rfl
private theorem end_eq (b:RectTail) :
    terminalBook b=(terminalNum b:ℚ)/425+terminalExtra b:= by
  have h (o:Origin) (_:o∈(univ :zJe Origin)) (ho:o∉({0,8} : zJe Origin)) :
      FP (terminalDual b o) (endCap b o)=0:= by
    have h0:o≠0:= fun h=>ho (by simp [h])
    have h8:o≠8:= fun h=>ho (by simp [h])
    simp only [FP,terminalDual,terminalDualN,h0,h8,ite_false,zQq,zero_mul,sum_const_zero]
  have h0:FP (terminalDual b 0) (endCap b 0)=(terminalNum b:ℚ)/425:= by
    simp only [FP,zCS,zDT,add_zero]
    cases b <;> with_unfolding_all rfl
  have h8:FP (terminalDual b 8) (endCap b 8)=(terminalExtra b:ℚ) := by
    simp only [FP,zCS,zDT,add_zero]
    cases b <;> with_unfolding_all rfl
  rw [terminalBook,← sum_subset (subset_univ ({0,8} : zJe Origin)) h,
    sum_pair (show (0:Origin)≠8 by decide),h0,h8]
private theorem budget (f g a e cap:ℕ) (h: (f+g+e)*425+a≤ cap*425) :
    (f :ℚ)+g+((a :ℚ)/425+e)≤ cap:= by
  have hq: ((f :ℚ)+g+e)*425+a≤(cap:ℚ)*425:= by exact_mod_cast h
  linarith only [hq]
theorem booksCovered (b:RectTail) :
    (ee3 b:ℚ)+((factorBook b:ℕ) :ℚ)+terminalBook b≤(prefixFee b:ℚ) := by
  rw [factor_eq,end_eq]
  apply budget
  cases b
  · with_unfolding_all exact (show 0x40571160ca47693b6≤0x4057122e610e89fe3 by decide)
  · with_unfolding_all exact (show 0x4a2102e84c891178e≤0x4a21043b488dc77c9 by decide)
  · with_unfolding_all exact (show 0x40858f1be9ff020a2≤0x408590576b36e089f by decide)
  · with_unfolding_all exact (show 0x2e46505db43320e34≤0x2e46516cd34a75f3f by decide)
end
end qVWQWJa
end
section
set_option autoImplicit true
namespace qVWQWJa
noncomputable section
open P6_7 (RectTail)
open P6_7_2_3
open cu (Shape)
open TD (FP a3x arC)
open scoped BigOperators
private abbrev bw:ℕ:=0xe2aa061ae33fa
private theorem line_cap (b:RectTail) {B J U:ℕ} (hb:B≤12) (hj:J≤2) (hu:U≤139) :
    lineFee b B J U≤bw:= by
  let t:=2*degree b-3
  let a :=1+t*(B-1)
  let v :=min a (t*(J-1)+degree b)
  let w:=t*U
  let m:=U*(2*a*v-v*v)+2*w*(B*v+J*(a-v))
  let n:=U*(2*a+v)+w*(2*B+J)+B*v+J*a+U+B+J
  let gap:=oldAgreement-degree b
  have ht:t≤266951 := by cases b <;> decide
  have hd:degree b≤133477:= by cases b <;> decide
  have hg:46263≤gap:= by cases b <;> decide
  have hg' : gap≤46288:= by cases b <;> decide
  have ha :a≤2936462 :=z3b
    (zcp ht (zIu hb 1)) 1
  have hv :v≤400428:=(min_le_right _ _).trans
    (z9f (zcp ht (zIu hj 1)) hd)
  have hw:w≤37106189:=zcp ht hu
  have hm:m≤0x3fa05e73c9b68:=z9f
    (zcp hu ((Nat.sub_le _ _).trans (zcp (zBI 2 ha) hv)))
    (zcp (zBI 2 hw)
      (z9f (zcp hb hv) (zcp hj ((Nat.sub_le _ _).trans ha))))
  have hn₁:=zcp hu (z9f (zBI 2 ha) hv)
  have hn₂:=zcp hw (z9f (zBI 2 hb) hj)
  have hn₃:=z9f (z9f hn₁ hn₂) (zcp hb hv)
  have hn:n≤0x6e1d9f2f :=z9f
    (z9f (z9f (z9f hn₃ (zcp hj ha)) hu) hb) hj
  have hdiv : (164808*(m+n)+gap-1)/gap≤bw-152 := by
    apply zeh
    apply (Nat.div_lt_iff_lt_mul (show 0<gap by omega)).2
    have hnum :=zIu
      (z9f (zBI 164808 (z9f hm hn)) hg') 1
    exact hnum.trans_lt ((show 164808*(0x3fa05e73c9b68+0x6e1d9f2f)+46288-1 <
      (bw-152+1)*46263 by decide).trans_le (zBI _ hg))
  change (164808*(m+n)+gap-1)/gap+B+U+1≤bw
  exact Nat.add_le_add_right (z9f (z9f hdiv hb) hu) 1
private def upper :Shape :=⟨0,14,2,139⟩
private theorem cols_le {v :Fin 3→ℕ} (hb:v 0≤12) (hj:v 1≤2) (hu:v 2≤139)
    (k :Fin 4) (j:Fin 3) :arC ⟨0,v 0,v 1,v 2⟩ k j≤arC upper k j:= by
  fin_cases k <;> fin_cases j <;> first
    | exact Nat.zero_le _
    | exact hb.trans (by decide :12≤14)
    | exact hj
    | exact hu
    | exact (Nat.sub_le _ _).trans hb
private theorem credit_nat (b:RectTail) (j:Fin 3) :
    (∑ k :Fin 4,residueN b last k * arC upper k j) +
      (if j=1 then bw else 0)≤unitN b last j:= by
  unfold unitN
  simp only [zCS,zDT,add_zero]
  cases b <;> fin_cases j
  · with_unfolding_all exact (show 0x2b28ba1630cb≤0x537edaa24e893 by decide)
  · with_unfolding_all exact (show 0xf96762f29779+bw≤0x17f540a358746f by decide)
  · with_unfolding_all exact (show 0x253f7f25304≤0x456c95efd1b0 by decide)
  · with_unfolding_all exact (show 0x355db3ec14fd≤0x65c93df9313e9 by decide)
  · with_unfolding_all exact (show 0x12b3e57b43f1e+bw≤0x1c9cf551f983a4 by decide)
  · with_unfolding_all exact (show 0x302702a4bd0≤0x5950a89a41d3 by decide)
  · with_unfolding_all exact (show 0x2f0bacad955d≤0x58b712f54021e by decide)
  · with_unfolding_all exact (show 0x1075b553691fc+bw≤0x190a7961bd75d8 by decide)
  · with_unfolding_all exact (show 0x2d9b3169978≤0x54905ac1205b by decide)
  · with_unfolding_all exact (show 0x2351e474908a≤0x43a63d1a0ff30 by decide)
  · with_unfolding_all exact (show 0xcf5ec415156e+bw≤0x13b26cc10df92e by decide)
  · with_unfolding_all exact (show 0x200937f0ef2≤0x3bcef6ef592e by decide)
theorem lineAbsorbs (b:RectTail) (v :Fin 3→ℕ) (hv : ∀ j,v j≤ introCap b last j)
    (hj:0<v 1) :
    (lineFee b (v 0) (v 1) (v 2) :ℚ)+FP (residue b last) (kK v ⟨0,v 0,v 1,v 2⟩) ≤
      ∑ j,(unitN b last j:ℚ)*(v j:ℚ) := by
  have hb:v 0≤12 :=(hv 0).trans (by cases b <;> decide)
  have hj' : v 1≤2 :=(hv 1).trans (by cases b <;> decide)
  have hu:v 2≤139:=(hv 2).trans (by cases b <;> decide)
  have hf :=(z9h (α:=ℚ)).mpr (line_cap b hb hj' hu)
  have hv1 : (1 :ℚ)≤(v 1 :ℚ) :=Nat.cast_le.mpr (show 1≤v 1 from hj)
  have hm:FP (residue b last) (kK v ⟨0,v 0,v 1,v 2⟩) ≤
      FP (residue b last) (kK v upper) :=
    a3x (fun k=>zqJ _) fun k =>
      zQk fun j _=>mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (cols_le hb hj' hu k j)) (zqJ (v j))
  let cost (j:Fin 3) :ℕ :=
    (∑ k :Fin 4,residueN b last k * arC upper k j)+if j=1 then bw else 0
  calc
    _≤(bw:ℚ)*(v 1 :ℚ)+FP (residue b last) (kK v upper) :=
      add_le_add (hf.trans (le_mul_of_one_le_right (zqJ bw) hv1)) hm
    _ = ∑ j,(cost j:ℚ)*(v j:ℚ) := by
      rw [add_comm ((bw:ℚ)*(v 1 :ℚ))]
      unfold cost
      simp only [FP,kK,residue,Nat.cast_add,zCt,z2R,Finset.mul_sum,Finset.sum_mul,
        Nat.cast_ite,zQq,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _ => ?_
      ring
    _≤_:=zQk fun j _=>mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (credit_nat b j)) (zqJ (v j))
end
end qVWQWJa
end
section
set_option autoImplicit true
namespace qr1Ougb
open P6 (p)
open P6_7 (RectTail)
open P6_7_2_3
open qVWQWJa
abbrev q:ℕ:=p+1
abbrev gap (b:RectTail) :ℕ:=oldAgreement-degree b
private def projectionCode :RectTail→ℕ
  | .pruned=>0x10ada3ddc416c98d8e1cbb25c2434c4c64005baefdf72f896a1cc92639eea84ec3d21b09b93d7f80f9ef8b8a66e18caa950fca9878ac4d7d8814de6c8022238218404aa3af6211a1e299d07fe972240ed676644197d07e1877492d121bc3039d80cbe83f0c17c44f548289dea4f2861be774a6fd8dcd04652521507e96c02a0e0b5f67262747a2e94403dd598a7073f12144dbd8062129ec48890a2d8f323c894fe80fddbe73e1d3559144329e357995152b6a443d432b502409e56c846d7fde30726583a42489769b4985366ad041e0bca08781470030d25432a648a6cb450fadacb5e07deb10860f2be321c1904d28f8d21adf3326e6d041e16afb0c8c2dcda95b047da37a62c69c63466427b75c64bf25d244a351d8320ef405f70291442b30ac8ab70447f7be549931ca2161b978436aa
  | .tailOne=>0x105a6fe5438a38f1481c008360033c9f0120592b82f82dc54dfec7fb75c6c04ba143cf095afbbfe0efabb7ac634e8c01d25313dea8a5c631621421b4b5620dfd6e8448995f3e8f416a94b07bd0eec40e6ec87a418a03b8b873c49c2b18055a0880c501dc5c170fc5938272bdcd0279703bd890262cdc44480b50587c3b14340da69d0ea5f0616f0d1a16715d0a0b9069f1396b5ffa1fdd91f088d5ab6e09ef6e831d0f6bba0ac1c90137fc31191421943284d283b03243d622766d39c43d5dd0906d408ac723d15496283b885fd4402ec4cc075d1d6e10cc7aa216468350658da75129d079c419a80eba17df41827c9768c8190e35a200f78561599c7c8c2ba1a191044579bc825defbd2f54bc3b5364232d87248d4e9f840d08b653e27ba3d1fa9573f32947b752e609277be4f6b774387ba
  | .tailTwo=>0x101e838dc330d7fff41b74539c8331c327e057438ada2c6637b58739d4c228492d76130912594b40e79e9eda6083fedc508e2c74c0a0a34e6d138f9e1ea1fd03bd40470056e18dbb0a3cf07893a3500e1eb959c17f10076870ff8e01159dc98300bf8803b41683539282605508426e0edca48176ee58c42ebc38d87a1b7fea0d4f6280c5c309b794fecc328189b86d50813003e4e61ecb9eb6c8a772a539bdb9f4920f099c6ae1bfee4c042fcb42c2137b996e035412c9cc2130426c0416b242f06916c7b8232a6e63e767547cc03eb38607873c5af170c764478c44d83a288c598ebb50767e86840e622ba3c177914da8c0638a0d9ecd85fd914c20682a29f6e47a8419c6fb2219d41a7d4ae5a3cb63be09b87c7f285afd0bc97a20926a007eba86892042c7831909a91f1d1b27b5cb7e9fe
  | .tailThree=>0xfe3af5d02eb180dec1aee53238326fd9840557960d02b1f04b106a090a02846e6a03208ceaa3e40e032ce1e5de5d5a64f289f21089bd8eb9f13068ef761ed501ca44579ecd38c88e9a0e07585b84c0dd21ac54174dcdcd06e6645e513bb0be540ba6e6e6815ff7aef824f5eafa26492b254761af07e0419082ab078601d0a0d05232aa59b0b1d64e967e04d896eab8c5127bef6221dd9f354c88003db99972975c80eb443f901b84554ac2eab131312db06ad430ba73c0e2010296643f4d0c670656dbb712286185ee6c13556ac3d471edc871bd8f410c294e5c24352c5248b53f7c8e073826d9c0e120b94416db0eff0b97167479c42ce02d13ff1daf228763ea283f279cfc1e1d8acd3433fc17b436e414d007411502a0acda6f0925967cc827acd0af98751c628b91751d342b4428127e
private def witnessCode :ℕ:=0x8234f7ff347db187b6fd792e376aea746d4722be6fea56da8a6b66f6925566e3b64a22622295fe155d9fa5b5e0591c756daf545b35219e4fd844d96c4b55548d584694144529421133f9143d4fd3b0e7388e4364d0340bb318b72f4a42cc9b2a88c2847925c74238622105c1ec4b1c44419c3c1782e1502712820100180dc0f0b40a
def projectionN (b:RectTail) (o:Origin) (i:FreeTest) :ℕ :=
  (projectionCode b >>> (35*(5*o.val+i.val))) % 2^35
private def entry (i:ℕ) :ℕ:=(witnessCode >>> (20*i)) % 2^20
private def extra36:RectTail→ℕ
  | .pruned=>455
  | .tailOne=>459
  | .tailTwo=>461
  | .tailThree=>464
def extra (b:RectTail) (i:ℕ) :ℕ:=if i=33 then extra36 b else entry i % 1024
def param (i:ℕ) :ℕ:=entry i >>> 10
def width (b:RectTail) (i:ℕ) :ℕ :=
  let e :=i+3
  let D:=degree b
  let c:=param i
  let g:=extra b i
  let E :=e+g
  let L:=(g+1)*c
  let j:=L/(c+1)
  let j3:=(c+1)*(D*E*(E+1)/2+D*j*(j+1)/2)
  max (e*D) (max (j3/L-j*D) ((E-j)*D))
abbrev rateNum (D k e g c W:ℕ) :ℕ :=
  max ((e*(c+1)+e+g)*k)
    ((7+6*e)*k+((2*e+1)*262144+(6*e-2)*W-3*e*e*D))
private abbrev num (b:RectTail) (i:ℕ) :ℕ :=
  rateNum (degree b) (gap b) (i+3) (extra b i) (param i) (width b i)
abbrev Cross (k d a h e n:ℕ) :Prop :=
  1530*n*q+h*k*(d+1530*e*(4*e+8))≤h*k*(1530*q)+1530*n*a*e
def checks (b:RectTail) (d a h:ℕ) :ℕ→Bool
  | 0=>true
  | i+1=>checks b d a h i &&
      (decide (q≤a*(i+3)) || decide (Cross (gap b) d a h (i+3) (num b i)))
theorem cross_of_checks {b:RectTail} {d a h m i:ℕ} (hi:i< m)
    (hc:checks b d a h m=true) (he :a*(i+3)<q) :
    Cross (gap b) d a h (i+3) (num b i) := by
  induction m with
  | zero=>omega
  | succ m ih =>
    simp only [checks,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hc
    rcases eq_or_lt_of_le (zeh hi) with rfl | hh
    · exact hc.2.resolve_left (not_le_of_gt he)
    · exact ih hh hc.1
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem projection_eq (b:RectTail) (o:Origin) (i:FreeTest) :
    freeProjection b o i=(projectionN b o i:ℚ)/510 := by
  simp only [freeProjection,projectionBound,TD.FP,memberCap,liveCap,
    originBox,kK,zCS,zDT,add_zero]
  cases b <;> fin_cases o <;> fin_cases i <;> with_unfolding_all rfl
set_option maxHeartbeats 4000000 in
theorem witness (b:RectTail) (i:Fin 52) :
    NativeOK (degree b) (i.val+3) (extra b i.val) (param i.val) (width b i.val)
      (width b i.val+1+((extra b i.val+1)*param i.val/(param i.val+1))*degree b) := by
  unfold NativeOK
  cases b <;> fin_cases i <;> decide
set_option maxHeartbeats 8000000 in
theorem checked (b:RectTail) (o:Origin) (i:FreeTest) :
    projectionN b o i≤510*freeSeedN b o i∧100≤freeHeightN b o i ∧
    checks b (projectionN b o i) (freeSeedN b o i) (freeHeightN b o i) 52=true := by
  cases b <;> fin_cases o <;> fin_cases i <;> exact ⟨by decide,by decide,by decide⟩
end qr1Ougb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qLhhyke
noncomputable section
open Finset
open P6_7_1
open q3rjQGe
open cu (Jet Shape)
open pI (oU)
open TD (J2)
open akZ (btm bKa caQ aHP cfi)
open private a8m from ProximityPrize.SubmissionLower.CR
open private b6z from ProximityPrize.SubmissionLower.D7
open private cast_fold from ProximityPrize.SubmissionLower.Zc1KtHb
open scoped Classical
variable {x P R} (O:OriginCover x P R)
theorem spend_cap {f :Jet} (hf :f∈O.factors) (j:Fin 3) :
    wD f j≤ introCap (O.origin f).val j :=
  (single_le_sum (fun _ _=>Nat.zero_le _) (f := fun g=>wD g j)
    (show f∈O.factors.filter (fun g=>(O.origin f).val≤(O.origin g).val) from
      mem_filter.mpr ⟨hf,le_rfl⟩)).trans
    (O.nested _ (zeh (O.origin f).isLt) j)
theorem origin_eq_box (o:Origin) :originShape o=qBPZs8a.box o:= by
  unfold originShape qBPZs8a.box
  split
  · rfl
  · rename_i h
    have he :o.val=introductions.length :=
      le_antisymm (zeh o.isLt) (Nat.le_of_not_gt h)
    rw [he]
    rfl
theorem origin_J (o:Origin) : (originShape o).J≤(originShape o).B:= by
  rw [origin_eq_box]
  exact qBPZs8a.box_J o
private theorem early_caps {f :Jet} (hf :f∈O.factors)
    (h: (O.origin f).val< introductions.length) :
    oU (O.cut f) (originShape (O.origin f)) := by
  rw [originShape,dite_eq_left h]
  exact DP.d3r P.crt x.word (O.early_cut f hf ⟨_,h⟩ rfl).1
theorem origin_cut_caps {f :Jet} (hf :f∈O.factors) :
    oU (O.cut f) (originShape (O.origin f)) := by
  by_cases h: (O.origin f).val< introductions.length
  · exact early_caps O hf h
  · have he :O.origin f=lastOrigin :=
      Fin.ext (le_antisymm (zeh (O.origin f).isLt) (Nat.le_of_not_gt h))
    rw [he,origin_eq_box]
    refine qBPZs8a.enclose_last (f :=f) ?_ (O.line f) (O.last_cut f hf he).2
    intro j
    have hcap:=spend_cap O hf j
    rwa [he] at hcap
private theorem assigned_caps {f :Jet} (hf :f∈O.factors) :
    oU (O.cut f) (afF (O.origin f) f (O.line f)) := by
  by_cases h:O.line f=true
  · have hc:=(O.last_cut f hf (O.line_pos f hf h).1).2
    simpa only [afF,ite_eq_left h,asShape] using hc
  · simpa only [afF,ite_eq_right h] using origin_cut_caps O hf
theorem tD {a b:Fin 3→ℕ} (h : ∀ j,a j≤b j) (s :Shape) (k :Fin 4) :
    kK a s k≤kK b s k :=
  sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (h j)) (zqJ _)
theorem b9i (a :Fin 3→ℕ) (s :Shape) (k :Fin 4) :0≤kK a s k :=
  sum_nonneg fun _ _=>mul_nonneg (zqJ _) (zqJ _)
private theorem mass_cut {f :Jet} (hf :f∈O.factors) (k :Fin 4)
    {s :Shape} (hs :s.J≤ s.B) (hc:oU (O.cut f) s) :
    pI.mass (O.parents f) k≤aHP s k f := by
  have hp:=O.proper f hf
  obtain ⟨_,hm⟩:=a8m f (O.cut f) (b6z hp.1 hp.2.2.2)
    (btm f) s (caQ hp.1.ne_zero) hs (bKa f) hc (O.parents f) (fun I hI=> by
      obtain ⟨ha,_,hp,hq⟩:=O.geometric f hf I hI
      exact ⟨ha.prime,ha.dimension,hp,hq⟩)
  exact (hm k).trans_eq (cfi f s hs k)
private theorem tariff_cast (s :Shape) (k :Fin 4) (f :Jet) :
    (aHP s k f :ℚ)=kK (wD f) s k := by
  simp only [kK,aHP,TD.arC,mixedCols,P5_7_1.wD,akZ.yE,
    zCt,z2R,mul_comm]
theorem mass_assigned {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤kK (wD f) (afF (O.origin f) f (O.line f)) k := by
  have hj: (afF (O.origin f) f (O.line f)).J≤(afF (O.origin f) f (O.line f)).B:= by
    unfold afF
    split
    · exact caQ (O.proper f hf).1.ne_zero
    · exact origin_J _
  exact ((z9h (α:=ℚ)).mpr (mass_cut O hf k hj (assigned_caps O hf))).trans_eq
    (tariff_cast _ _ _)
theorem mass_origin_spend {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤kK (wD f) (originShape (O.origin f)) k :=
  ((z9h (α:=ℚ)).mpr (mass_cut O hf k (origin_J _) (origin_cut_caps O hf))).trans_eq
    (tariff_cast _ _ _)
theorem mass_origin {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤originBox (O.origin f) k :=
  (mass_origin_spend O hf k).trans (tD (spend_cap O hf) _ _)
private def oldN (v :Origin→ℕ) (i:ℕ) :ℕ :=
  ((List.ofFn v).take i).foldl max 0
private def billN (k :Fin 4) (j:Fin 3) :ℕ :=
  ∑ i:Origin,
    let v := fun o=>mixedCols (originShape o) k j
    (max (v i) (oldN v i.val) - oldN v i.val)*introCap i.val j
private theorem old_cast (v :Origin→Fin 3→ℕ) (i:ℕ) (j:Fin 3) :
    (((List.ofFn (fun o l=>(v o l:ℚ))).take i).foldl (fun n w=>max n (w j)) 0) =
    (oldN (fun o=>v o j) i:ℚ) := by
  rw [List.ofFn_comp' v (fun w l=>(w l:ℚ)),← List.map_take,← zQq,← cast_fold]
  unfold oldN
  rw [List.ofFn_comp' v (fun w=>w j),← List.map_take,List.foldl_map]
private theorem bill_cast (k :Fin 4) :
    resourceBill (fun o j=>mixedCols (originShape o) k j) = ∑ j,(billN k j:ℚ) := by
  unfold resourceBill billN
  simp only [old_cast,zCt,z2R,Nat.cast_sub (le_max_right _ _),Nat.cast_max]
  exact sum_comm
private def billCols :Fin 4→Fin 3→ℕ :=
  ![![4785,3659,0],![0,77284,51788],![369996,0,235821],![0,0,4101845]]
private theorem bill_value (k :Fin 4) (j:Fin 3) :billN k j=billCols k j:= by
  fin_cases k <;> fin_cases j <;> decide
private def iy (k :Fin 4) :ℕ :=
  let v :=introCap lastOrigin.val
  (![v 0,v 2,2*v 0*v 2,v 2*v 2] :Fin 4→ℕ) k
private theorem au9 (k :Fin 4) : (qBPZs8a.massCap k :ℚ)=initialBound k := by
  have hv (k :Fin 4) :qBPZs8a.massCap k=(∑ j,billCols k j)+iy k := by
    fin_cases k <;> decide
  unfold initialBound
  rw [bill_cast,hv,Nat.cast_add,zCt]
  simp only [bill_value,iy]
theorem mass_initial (k :Fin 4) : (∑ f∈O.factors,J2 (O.parents f) k)≤ initialBound k := by
  have h (f :Jet) (hf :f∈O.factors) :
      pI.mass (O.parents f) k≤aHP (qBPZs8a.box (O.origin f)) k f := by
    rw [← origin_eq_box]
    exact mass_cut O hf k (origin_J _) (origin_cut_caps O hf)
  have ht:=(sum_le_sum h).trans (qBPZs8a.charge O.factors O.origin O.nested k)
  rw [← au9]
  simpa only [J2,zCt] using (z9h (α:=ℚ)).mpr ht
end
end qLhhyke
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace qLhhyke
noncomputable section
open Finset
open P6 (p)
open P6_7_1
open q3rjQGe
open cu (Jet aZ Equation)
open DP (d3q d3r)
open gT (Ambient aQ iJ)
open pI (xN dual O9 oU pN)
open ac2 (bp3 dLt aVL Ih)
open XY (ag6)
open TD (J2 bfw cZV)
open akZ (bCj cN4 caQ)
open q54LkTb (le_folds)
open private positive_spend from ProximityPrize.SubmissionLower.Zc1KtHb
open private dfc ddV from ProximityPrize.SubmissionLower.U
open private b6z from ProximityPrize.SubmissionLower.D7
open scoped Classical
private theorem free_guard (i:Free) :
    (stage i).free.J≤(stage i).free.B∧(stage i).dI<p ∧
      2*packetHi*(stage i).dI≤ cutoff (stage i).free := by
  fin_cases i <;> decide
private theorem ref_J (o:Origin) : (refShape o).J≤(refShape o).B:= by
  have h:introCap o.val 1≤ introCap o.val 0:= by fin_cases o <;> decide
  exact max_le_max h (origin_J o)
private theorem spend_ref {o:Origin} {F:Jet} (h : ∀ j,wD F j≤ introCap o.val j) :
    oU F (refShape o) :=
  (bCj _ _).mpr fun j=>(h j).trans (by fin_cases j <;> exact le_max_left _ _)
private theorem cut_ref {o:Origin} {G:Jet} (h:oU G (originShape o)) :
    oU G (refShape o) :=
  (bCj _ _).mpr fun j =>
    ((bCj _ _).mp h j).trans (by fin_cases j <;> exact le_max_right _ _)
private theorem free_order {x P} (R:EarlyPicks x P) (i:Free)
    {I:Ideal Ambient} (ha :xN I) (hd:dual I) (hv :passes P i.castSucc I) :
    O9 I (R.free i.succ).row ((stage i).dI+1) := by
  let s :=(stage i).free
  let r :=(stage i).dI
  have hroom:2*x.h*r≤ cutoff s :=
    (Nat.mul_le_mul_right r (zBI 2 (heights x).2)).trans (free_guard i).2.2
  have hcut:buffer x.h r s+2*x.h*r≤ cutoff s :=(Nat.sub_add_cancel hroom).le
  have hs :qQ.bk4 x.h P.rows s :=
    fun _ _ h a t=>atp.d3s P.crt x.word h a t
  let a :=algebraMap aZ aQ
  let Q:=(R.free i.succ).row
  have hc:bp3 (I.map (Ih a)) (Ih a (iJ Q)) r := by
    intro t ht
    rw [← dfc]
    apply Ideal.mem_map_of_mem
    apply hv
    rw [free_bank]
    exact d3q P.crt x.word rfl rfl rfl le_rfl
      ((z3b (zBI _ ht) _).trans hcut)
      (ddV hs (R.free i.succ).mem t)
  change bp3 (I.map (Ih (algebraMap aZ aQ)))
    (Ih (algebraMap aZ aQ) (iJ Q)) r at hc
  rw [← aVL] at hc
  exact dLt hd (cy0.proof I ha.prime ha.jet_finite hd ha.jet_lt _
    r (free_guard i).2.1 hc)
private theorem free_mass {x P} (R:EarlyPicks x P) (i:Free) (o:Origin)
    {F G:Jet} (hproper :ag6 F G) (hF:oU F (refShape o)) (hG:oU G (refShape o))
    (S:zJe (Ideal Ambient))
    (hS : ∀ I∈S,xN I∧dual I∧iJ F∈I∧iJ G∈I∧passes P i.castSucc I)
    (k :Fin 4) :J2 S k≤freeBound o i k := by
  let Q:=R.free i.succ
  have hc:=d3r P.crt x.word Q.mem
  have h:=q41fOQb.proof _ _ _ _ _ S _ (Nat.succ_pos _) Q.ne_zero hproper
    (free_guard i).1 (ref_J o) hc hF hG (fun I hI=> by
      obtain ⟨ha,hd,hf,hg,hb⟩:=hS I hI
      exact ⟨ha,hd,hf,hg,free_order R i ha hd hb⟩) k
  simpa only [freeBound,Nat.cast_succ,qehP9ee.kK,qehP9ee.mixedCols,kK,mixedCols] using h
private theorem survive_le {o:Origin} {s :bAL} {k :Fin 4} {v :ℚ}
    (h:v≤originBox o k) (hf : ∀ i:Free,i.val+1<s.val→v≤freeBound o i k) :
    v≤ survivedBound o s k := by
  unfold survivedBound
  apply le_folds _ _ id _ h
  intro a ha
  obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp ha
  have hi:=hn
  simp only [List.length_take,List.length_ofFn,lt_min_iff] at hi
  let i:Free :=⟨n,hi.2⟩
  have hval :freeBound o i k=a := by
    simpa only [List.getElem_take,List.getElem_ofFn] using he
  rw [← hval]
  exact hf i (by change n+1<s.val; omega)
variable {x P R} (O:OriginCover x P R)
private theorem live_cap {f :Jet} (hf :f∈O.factors) (s :bAL) (k :Fin 4) :
    J2 (QV O f s) k≤ survivedBound (O.origin f) s k := by
  apply survive_le ((bfw (filter_subset _ _) k).trans (mass_origin O hf k))
  intro i hi
  apply free_mass R i _ (b6z (O.proper f hf).1 (O.proper f hf).2.2.2)
    (spend_ref (spend_cap O hf)) (cut_ref (origin_cut_caps O hf)) (QV O f s) _ k
  intro I hI
  obtain ⟨hI,hd,hp⟩:=mem_filter.mp hI
  obtain ⟨ha,_,hF,hG⟩:=O.geometric f hf I hI
  exact ⟨ha,hd (by omega),hF,hG,hp i.castSucc hi⟩
private def bin (o:Origin) :zJe Jet:=O.factors.filter fun f=>O.origin f=o
private theorem bin_spend (o:Origin) (j:Fin 3) :
    (∑ f∈bin O o,wD f j)≤ introCap o.val j:= by
  refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>Nat.zero_le _)).trans
    (O.nested _ (zeh o.isLt) j)
  intro f hf
  obtain ⟨hf,he⟩:=mem_filter.mp hf
  exact mem_filter.mpr ⟨hf,he.ge⟩
private theorem bin_origin (o:Origin) (k :Fin 4) :
    (∑ f∈bin O o,J2 (QV O f termStop) k)≤originBox o k := by
  calc
    _ ≤ ∑ f∈bin O o,kK (wD f) (originShape o) k := by
      apply sum_le_sum
      intro f hf
      obtain ⟨hf,he⟩:=mem_filter.mp hf
      rw [← he]
      exact (bfw (filter_subset _ _) k).trans (mass_origin_spend O hf k)
    _=kK (fun j => ∑ f∈bin O o,wD f j) (originShape o) k := by
      simp only [kK,zCt,sum_mul]
      exact sum_comm
    _≤_:=tD (bin_spend O o) _ _
private theorem free_nonneg (o:Origin) (i:Free) (k :Fin 4) :0≤freeBound o i k :=
  div_nonneg (b9i _ _ _) (add_nonneg (zqJ _) zero_le_one)
private theorem early_free (o:Origin) (ho:o.val< introductions.length)
    (i:Free) (k :Fin 4) :
    (∑ f∈bin O o,J2 (QV O f termStop) k)≤freeBound o i k := by
  let D:=bin O o
  by_cases he :D.Nonempty
  · obtain ⟨f,hf⟩:=he
    let F:Jet := ∏ g∈D,g
    let S:=D.biUnion fun g=>QV O g termStop
    have hcuts (g:Jet) (hg:g∈D) :O.cut g=O.cut f := by
      obtain ⟨hg,hgo⟩:=mem_filter.mp hg
      obtain ⟨hf,hfo⟩:=mem_filter.mp hf
      exact O.shared_cut g hg f hf (hgo.symm ▸ ho) (hgo.trans hfo.symm)
    have hn (g:Jet) (hg:g∈D) :g≠0:=(O.proper g (mem_filter.mp hg).1).1.ne_zero
    have hproper :ag6 F (O.cut f) := by
      refine ⟨(Finset.prod_ne_zero_iff (s :=D) (f := fun g:Jet=>g)).mpr hn,
        (b6z (O.proper f (mem_filter.mp hf).1).1
          (O.proper f (mem_filter.mp hf).1).2.2.2).right_ne,?_⟩
      intro H hH hd hc
      let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
      let:UniqueFactorizationMonoid Equation :=zV6 (D:=aZ)
      let:UniqueFactorizationMonoid Jet:=zV6 (D:=Equation)
      change H ∣ ∏ g∈D,g at hd
      obtain ⟨g,hg,hgd⟩:=(hH.prime.dvd_finsetProd_iff (S:=D) (fun g:Jet=>g)).mp hd
      have hp:=O.proper g (mem_filter.mp hg).1
      exact hp.2.2.2 ((hH.associated_of_dvd hp.1 hgd).dvd'.trans ((hcuts g hg).symm ▸ hc))
    have hF:oU F (refShape o) :=spend_ref (fun j=> by
      change akZ.yE (∏ g∈D,g) j≤ introCap o.val j
      rw [cN4 (S:=D) (f := fun g:Jet=>g) hn]
      exact bin_spend O o j)
    have hG:oU (O.cut f) (refShape o) :=
      cut_ref ((mem_filter.mp hf).2 ▸ origin_cut_caps O (mem_filter.mp hf).1)
    have hd: (D:Set Jet).PairwiseDisjoint (fun g=>QV O g termStop) := by
      intro g hg g' hg' hn
      exact (O.disjoint g (mem_filter.mp hg).1 g' (mem_filter.mp hg').1 hn).mono
        (filter_subset _ _) (filter_subset _ _)
    have hg:=free_mass R i o hproper hF hG S (fun I hI=> by
      obtain ⟨g,hg,hI⟩:=mem_biUnion.mp hI
      obtain ⟨hI,hd,hp⟩:=mem_filter.mp hI
      obtain ⟨ha,_,haF,haG⟩:=O.geometric g (mem_filter.mp hg).1 I hI
      exact ⟨ha,hd (by decide),
        I.mem_of_dvd (map_dvd iJ (dvd_prod_of_mem (fun a=>a) hg)) haF,
        hcuts g hg ▸ haG,hp i.castSucc (by have :=i.isLt; change i.val+1<5; omega)⟩) k
    simpa only [S,D,J2,pI.mass,sum_biUnion hd,zCt] using hg
  · rw [show bin O o = ∅ from not_nonempty_iff_eq_empty.mp he,sum_empty]
    exact free_nonneg o i k
private theorem all_free (o:Origin) (k :Fin 4) :
    (∑ f∈bin O o,J2 (QV O f termStop) k)≤allFreeCap o k := by
  unfold allFreeCap
  by_cases ho:o=lastOrigin
  · rw [ite_eq_left ho]
    have hcard: (bin O o).card ≤ ∑ j,introCap o.val j:= by
      calc
        _ = ∑ f∈bin O o,(1 :ℕ) := by simp
        _ ≤ ∑ f∈bin O o,∑ j,wD f j :=
          sum_le_sum fun f hf=>positive_spend (O.proper f (mem_filter.mp hf).1).1
        _ = ∑ j,∑ f∈bin O o,wD f j:=sum_comm
        _≤_:=sum_le_sum fun j _=>bin_spend O o j
    have hn:0≤ survivedBound o termStop k :=
      survive_le (b9i _ _ _) (fun i _=>free_nonneg o i k)
    calc
      _ ≤ ∑ f∈bin O o,survivedBound o termStop k :=
        sum_le_sum fun f hf=> by
          obtain ⟨hf,he⟩:=mem_filter.mp hf
          rw [← he]
          exact live_cap O hf _ _
      _=survivedBound o termStop k*((bin O o).card:ℚ) :=
        by rw [sum_const,nsmul_eq_mul,mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) hn
  · rw [ite_eq_right ho,Nat.cast_one,mul_one]
    have hlt:o.val< introductions.length:= by
      by_contra! h
      exact ho (Fin.ext (le_antisymm (zeh o.isLt) h))
    exact survive_le (bin_origin O o k) (fun i _=>early_free O o hlt i k)
theorem proof :q3rjQGe.c1 := by
  intro x P R O
  refine ⟨fun f hf=>caQ (O.proper f hf).1.ne_zero,
    fun _ hf=>mass_assigned O hf,mass_initial O,all_free O,?_⟩
  intro f hf s I hI k
  have hle {S:zJe (Ideal Ambient)} (h:I∈S) :
      (pN I k :ℚ)≤J2 S k :=
    Nat.cast_le.mpr (YX.evL h k)
  refine le_min ((hle hI).trans (live_cap O hf s k)) ?_
  exact (hle (mem_filter.mp hI).1).trans
    ((single_le_sum (fun g _=>cZV (O.parents g) k) hf).trans (mass_initial O k))
end
end qLhhyke
end
