import ProximityPrize.SubmissionLower.DdZqZuDUb
import ProximityPrize.SubmissionLower.DdZtKKe0d
import ProximityPrize.SubmissionLower.DdZRlaVZc
import ProximityPrize.SubmissionLower.DdZ1iXjHc
import ProximityPrize.SubmissionLower.DdZENrqsd
import ProximityPrize.SubmissionLower.DdZW31ykd
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Fin.last → zym, Finset → zJe, Finset.sum_add_distrib → zfW, Finset.sum_mul → zkq, Fintype.card → zhP, Fintype.equivFinOfCardEq → zFl, MvPolynomial.eval → zY9, Nat.add_le_add → z9f, Nat.add_le_add_left → z3b, Nat.cast_nonneg → zqJ, Nat.le_add_right → z8K, Nat.mul_add → zws, Nat.mul_le_mul_left → zBI
section
set_option autoImplicit true
set_option maxRecDepth 100000
namespace P6_8
open i4 Finset
open P5_8 (Jn Gq small smallCaps donorCaps chartCaps tariffShape tW properDegree componentCap)
open scoped BigOperators
open P5_8_6 (dNb cofactor_zero cofactor_index emptySum extendSum capRow)
local notation:65 s:65 " +[" len "," val "]" => extendSum (n:=len) (y :=val) s rfl
private theorem excluded {b j n v :ℕ}
    (h:Gq ⟨b,j,0⟩ = ∑ i∈range n,capRow b j i)
    (hs : (∑ i∈range n,capRow b j i)=v)
    (hv :48700*v<0x5e3ebe4653e55c) :
    (i4.gap A+2)*Gq ⟨b,j,0⟩<donorMargin:= by
  rw [h,hs]
  exact hv
private theorem r0: (gap A+2)*Gq ⟨25,0,0⟩<donorMargin:= by
  refine excluded (n:=250) (v :=0x7c9424b32c) (cofactor_zero 25) ?_ (by decide)
  exact emptySum (capRow 25 0)
    +[32,0x22cfb7ce00] +[32,0x1d14c4be00] +[32,0x1759d1ae00]
    +[32,0x119ede9e00] +[32,0xbe3eb8e00] +[32,0x63040ed77]
    +[32,0x19216a38d] +[26,0x10b4bc28]
private theorem r1: (gap A+2)*Gq ⟨24,1,0⟩<donorMargin:= by
  refine excluded (n:=260) (v :=0x7a7717d471) (cofactor_index 24 1 (by decide)) ?_ (by decide)
  exact emptySum (capRow 24 1)
    +[32,0x226aeb5208] +[32,0x1c2bc6d908] +[32,0x1648737008]
    +[32,0x10bebd1708] +[32,0xb8c6fce08] +[32,0x6af60c3e9]
    +[32,0x2637b9980] +[32,0x39e6b100] +[4,0x245e0]
private theorem r2: (gap A+2)*Gq ⟨22,2,0⟩<donorMargin:= by
  refine excluded (n:=284) (v :=0x7c27efbcf4) (cofactor_index 22 2 (by decide)) ?_ (by decide)
  exact emptySum (capRow 22 2)
    +[32,0x2222acc900] +[32,0x1b8ef2f300] +[32,0x15a4bf1d00]
    +[32,0x105c314700] +[32,0xbad697100] +[32,0x790879b00]
    +[32,0x3fddc6052] +[32,0x129f3792a] +[28,0xf9eb778]
private theorem r3: (gap A+2)*Gq ⟨20,3,0⟩<donorMargin:= by
  refine excluded (n:=312) (v :=0x7c21880666) (cofactor_index 20 3 (by decide)) ?_ (by decide)
  exact emptySum (capRow 20 3)
    +[32,0x21d8cbdbb0] +[32,0x1ae6429fb0] +[32,0x14def9d3b0]
    +[32,0xfb35577b0] +[32,0xb53b98bb0] +[32,0x7b08a0fb0]
    +[32,0x4ba2b03b0] +[32,0x2610133e7] +[32,0xa9f9d67f]
    +[24,0x6c09630]
private theorem r4: (gap A+2)*Gq ⟨17,4,0⟩<donorMargin:= by
  refine excluded (n:=367) (v :=0x7d76de8363) (cofactor_index 17 4 (by decide)) ?_ (by decide)
  exact emptySum (capRow 17 4)
    +[32,0x21a8fd29f0] +[32,0x1a7a469df0] +[32,0x1461a611f0]
    +[32,0xf489b85f0] +[32,0xb18a6f9f0] +[32,0x7bb486df0]
    +[32,0x519ffe1f0] +[32,0x31e4d55f0] +[32,0x1b1b0c9f0]
    +[32,0xbdaa3df0] +[32,0x2d15a21b] +[15,0xabd9e8]
private theorem r5: (gap A+2)*Gq ⟨12,5,0⟩<donorMargin:= by
  refine excluded (n:=391) (v :=0x7e715a5a8a) (cofactor_index 12 5 (by decide)) ?_ (by decide)
  exact emptySum (capRow 12 5)
    +[32,0x21ac716b48] +[32,0x1a8381c648] +[32,0x146f79f148]
    +[32,0xf5a15ec48] +[32,0xb2d11b748] +[32,0x7d2295248]
    +[32,0x53318bd48] +[32,0x3399bf848] +[32,0x1cf6f0348]
    +[32,0xde4dde48] +[32,0x4ff48948] +[32,0xe1f0448]
    +[7,0x171d2a]
private theorem r6: (gap A+2)*Gq ⟨4,6,0⟩<donorMargin:= by
  refine excluded (n:=326) (v :=0x7dfe37533e) (cofactor_index 4 6 (by decide)) ?_ (by decide)
  exact emptySum (capRow 4 6)
    +[32,0x21f9e5cdd0] +[32,0x1b2b9973d0] +[32,0x15288719d0]
    +[32,0xfed4ebfd0] +[32,0xb769065d0] +[32,0x7c0ec0bd0]
    +[32,0x4c901b1d0] +[32,0x28b7157d0] +[32,0x104dafdd0]
    +[32,0x31dea3d0] +[6,0x391b1e]
private theorem r7: (gap A+2)*Gq ⟨1,7,0⟩<donorMargin:= by
  refine excluded (n:=279) (v :=0x71470d1c82) (cofactor_index 1 7 (by decide)) ?_ (by decide)
  exact emptySum (capRow 1 7)
    +[32,0x21bdbaa278] +[32,0x1a72bdbf78] +[32,0x13f26e2c78]
    +[32,0xe4847e978] +[32,0x97fc6f678] +[32,0x5a4675378]
    +[32,0x2c1a50078] +[32,0xe2fbfd78] +[23,0x130f5cc2]
private def cutoff :ℕ→ℕ
  | 0=>25
  | 1=>24
  | 2=>22
  | 3=>20
  | 4=>17
  | 5=>12
  | 6=>4
  | _=>1
private theorem reject {a :Jn} (ha :Allocation a) {b j:ℕ}
    (hp:0<b) (hB:b≤a.B) (hJ:j≤a.J)
    (hr : (i4.gap A+2)*Gq ⟨b,j,0⟩<donorMargin) :False :=
  (not_le_of_gt hr) ((ha.capacity (hp.trans_le hB)).trans
    (zBI _ (dNb hp hB hJ (Nat.zero_le a.C))))
private theorem limits {b j c:ℕ} (ha :Allocation ⟨b,j,c⟩) :j≤6∧b<cutoff j:= by
  have hj:j≤6:= by
    by_contra! hh
    have ht:c≤b:=ha.top_total
    have hi:j≤b+c:=ha.index_total
    exact reject ha (by decide :0<1) (show 1≤b by omega) (show 7≤j by omega) r7
  have hc: (i4.gap A+2)*Gq ⟨cutoff j,j,0⟩<donorMargin:= by
    interval_cases j
    all_goals simp only [cutoff]
    · exact r0
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
  have hp:0<cutoff j:= by interval_cases j <;> decide
  exact ⟨hj,Nat.lt_of_not_ge fun hb=>reject ha hp hb le_rfl hc⟩
private theorem ee8:gap A=48698:=rfl
private theorem d1C:errors A=82375:=rfl
private theorem chart_eq :chartCaps=⟨21495235,6160222,2752440⟩:= by
  have ha :a₀ small = 21495235:=rfl
  have hd:D small=6160222 :=rfl
  have he :e small = 2752440:= by
    have hx :t*(small.C-1)+k-2=2752440:=rfl
    have hy :D small/2=3080111 := by rw [hd]
    rw [e,hx,hy]
    exact min_eq_left (by decide)
  unfold chartCaps
  rw [ha,hd,he]
private theorem low_eq :lowFee small=0x403676b8ec7789:= by
  have hH :H small=1622 :=rfl
  have hI:I₁ small = 283:=rfl
  have ha :a₁ small=0x1953e058:=rfl
  have hd:d₁ small=0x469fa7d:=rfl
  have hr :R₁ small=0x33160a2d17:= by rw [R₁,hH,hd,hI,ha]
  rw [lowFee,d1C,ee8,hr,hH]
  rfl
private def HE (r n:ℕ) :=82375*r+48698*n
private def jX (a :Jn) :ℕ :=
  let s :=tariffShape a
  HE (R₁ s) (H s^2)+(if a.C=0 then 0 else HE (2*R₂ s) s.B) +
    HE (tW (smallCaps.wD a).repair (donorCaps.wD a).repair
      ⟨21495235,6160222,2752440⟩) (componentCap a)+0x403676b8ec7789
private theorem eNY (a :Jn) :commonFee a+c5H a+lowFee small=jX a := by
  rw [low_eq]
  simp only [jX,commonFee,c5H,properDegree,chart_eq,lowFee,regularFee,
    d1C,ee8,HE]
private def fO (b stop j c:ℕ) :Prop :=
  ∀ i,b≤ i→i<stop→jX ⟨i,j,c⟩≤0x1f80ba7d6c82de08
private theorem done {b j c:ℕ} : fO b b j c:= by
  intro i hl hu
  omega
private theorem bandCons {b stop j c v :ℕ}
    (he :jX ⟨b,j,c⟩=v) (hv :v≤0x1f80ba7d6c82de08)
    (ht:fO (b+1) stop j c) :fO b stop j c:= by
  intro i hl hu
  by_cases h:i=b
  · rwa [h,he]
  · exact ht i (by omega) hu
local notation:65 val:66 " |+| " tail:65=>bandCons (v :=val) rfl (by decide) tail
private theorem cost_0_0 :fO 0 25 0 0 :=
  0x1b5f06a8ac96b9f |+| 0x1b426af4b120511 |+| 0x1b25cf40b5c1af7 |+| 0x1b0934a64794803 |+|
  0x1aec9a0bd996df7 |+| 0x1acfff716bc8cd3 |+| 0x1ab364d6fe2a497 |+| 0x1a96ca3c90bb543 |+|
  0x1a7a2fa2237bed7 |+| 0x1a5d9507b66c153 |+| 0x1a40fa6d498bcb7 |+| 0x1a245fd2dcdb103 |+|
  0x1a07c5387059e37 |+| 0x19eb2a9e0408453 |+| 0x19ce900397e6357 |+| 0x19b1f5692bf3b43 |+|
  0x19955acec030c17 |+| 0x1978c034549d5d3 |+| 0x195c2599e939877 |+| 0x193f8aff7e05403 |+|
  0x1922f0651300877 |+| 0x190655caa82b5d3 |+| 0x18e9bb303d85c17 |+| 0x18cd2095d30fb43 |+|
  0x18b085fb68c9357 |+|
  done
private theorem cost_1_0 :fO 1 24 1 0 :=
  0x1ab6850c8d44d9f |+| 0x1a99eff1db56395 |+| 0x1a7d5bf0b6990b1 |+| 0x1a60c7ef920b6b5 |+|
  0x1a4433ee6dad5a1 |+| 0x1a279fed497ed75 |+| 0x1a0b0bec257fe31 |+| 0x19ee77eb01b07d5 |+|
  0x19d1e3e9de10a61 |+| 0x19b54fe8baa05d5 |+| 0x1998bbe7975fa31 |+| 0x197c27e6744e775 |+|
  0x195f93e5516cda1 |+| 0x1942ffe42ebacb5 |+| 0x19266be30c384b1 |+| 0x1909d7e1e9e5595 |+|
  0x18ed43e0c7c1f61 |+| 0x18d0afdfa5ce215 |+| 0x18b41bde8409db1 |+| 0x189787dd6275235 |+|
  0x187af3dc410ffa1 |+| 0x185e5fdb1fda5f5 |+| 0x1841cbd9fed4531 |+|
  done
private theorem cost_2_0 :fO 2 22 2 0 :=
  0x1a0dbd5dd56860c |+| 0x19f130bf151133a |+| 0x19d4a42054e9950 |+| 0x19b8178194f184e |+|
  0x199b8ae2d529034 |+| 0x197efe441590102 |+| 0x196271a55626ab8 |+| 0x1945e50696ecd56 |+|
  0x19295867d7e28dc |+| 0x190ccbc91907d4a |+| 0x18f03f2a5a5caa0 |+| 0x18d3b28b9be10de |+|
  0x18b725ecdd95004 |+| 0x189a994e1f78812 |+| 0x187e0caf618b908 |+| 0x18618010a3ce2e6 |+|
  0x1844f371e6405ac |+| 0x182866d328e215a |+| 0x180bda346bb35f0 |+| 0x17ef4d95aeb436e |+|
  done
private theorem cost_2_1 :fO 1 22 2 1 :=
  0x1c4d1f6dbda24d7 |+| 0x1c30927e8b0fae1 |+| 0x1ee8007076ad80f |+| 0x219f6e62627ae25 |+|
  0x2456dc544e77d23 |+| 0x270e4a463aa4509 |+| 0x29c5b83827005d7 |+| 0x2c7d262a138bf8d |+|
  0x2f34941c004722b |+| 0x31ec020ded31db1 |+| 0x34a36fffda4c21f |+| 0x375addf1c795f75 |+|
  0x3a124be3b50f5b3 |+| 0x3cc9b9d5a2b84d9 |+| 0x3f8127c79090ce7 |+| 0x423895b97e98ddd |+|
  0x44f003ab6cd07bb |+| 0x47a7719d5b37a81 |+| 0x4a5edf8f49ce62f |+| 0x4d164d813894ac5 |+|
  0x4fcdbb73278a843 |+|
  done
private theorem cost_3_0 :fO 3 20 3 0 :=
  0x196560adaca7bfe |+| 0x1948db4918a705e |+| 0x192c55e484d5da6 |+| 0x190fd07ff1343d6 |+|
  0x18f34b1b5dc22ee |+| 0x18d6c5b6ca7faee |+| 0x18ba4052376cbd6 |+| 0x189dbaeda4895a6 |+|
  0x1881358911d585e |+| 0x1864b0247f513fe |+| 0x18482abfecfc886 |+| 0x182ba55b5ad75f6 |+|
  0x180f1ff6c8e1c4e |+| 0x17f29a92371bb8e |+| 0x17d6152da5853b6 |+| 0x17b98fc9141e4c6 |+|
  0x179d0a6482e6ebe |+|
  done
private theorem cost_3_1 :fO 2 20 3 1 :=
  0x29c8a64f299fac2 |+| 0x29ac1ff94094d50 |+| 0x36213cea565a6e4 |+| 0x429659db6c4f960 |+|
  0x4f0b76cc82744c4 |+| 0x5b8093bd98c8910 |+| 0x67f5b0aeaf4c644 |+| 0x746acd9fc5ffc60 |+|
  0x80dfea90dce2b64 |+| 0x8d550781f3f5350 |+| 0x99ca24730b37424 |+| 0xa63f416422a8de0 |+|
  0xb2b45e553a4a084 |+| 0xbf297b46521ac10 |+| 0xcb9e98376a1b084 |+| 0xd813b528824ade0 |+|
  0xe488d2199aaa424 |+| 0xf0fdef0ab339350 |+|
  done
private theorem cost_4_0 :fO 4 17 4 0 :=
  0x18aca9db82bef6e |+| 0x18902d435100b04 |+| 0x1873b0ab1f71f82 |+| 0x18573412ee12ce8 |+|
  0x183ab77abce3336 |+| 0x181e3ae28be326c |+| 0x1801be4a5b12a8a |+| 0x17e541b22a71b90 |+|
  0x17c8c519fa0057e |+| 0x17ac4881c9be854 |+| 0x178fcbe999ac412 |+| 0x17734f5169c98b8 |+|
  0x1756d2b93a16646 |+|
  done
private theorem cost_4_1 :fO 3 17 4 1 :=
  0x41a27121347436c |+| 0x4185f22dafe7280 |+| 0x58092fb5b62b6b4 |+| 0x6e8c6d3dbc9f3d0 |+|
  0x850faac5c3429d4 |+| 0x9b92e84dca158c0 |+| 0xb21625d5d118094 |+| 0xc899635dd84a150 |+|
  0xdf1ca0e5dfabaf4 |+| 0xf59fde6de73cd80 |+| 0x10c231bf5eefd8f4 |+| 0x122a6597df6edd50 |+|
  0x139299705ff0da94 |+| 0x14facd48e075d0c0 |+|
  done
private theorem cost_4_2 :fO 2 17 4 2 :=
  0x54891acfa83291b |+| 0x546c9ca53e83bbd |+| 0x54501e7ad4ecad3 |+| 0x7531e5ddde592a5 |+|
  0x9613ad40e8b36ff |+| 0xb6f574a3f3fb7e1 |+| 0xd7d73c07003154b |+| 0xf8b9036a0d54f3d |+|
  0x1199acacd1b665b7 |+| 0x13a7c92302a658b9 |+| 0x15b5e59933a52843 |+| 0x17c4020f64b2d455 |+|
  0x19d21e8595cf5cef |+| 0x1be03afbc6fac211 |+| 0x1dee5771f83503bb |+|
  done
private theorem cost_5_0 :fO 5 12 5 0 :=
  0x1804888eee33ede |+| 0x17e81330e8cc1a6 |+| 0x17cb9dd2e393d56 |+| 0x17af2874de8b1ee |+|
  0x1792b316d9b1f6e |+| 0x17763db8d5085d6 |+| 0x1759c85ad08e526 |+|
  done
private theorem cost_5_1 :fO 4 12 5 1 :=
  0x638abee494a8258 |+| 0x636e468a59a2df0 |+| 0x83ffa3e0356fcc2 |+| 0xa4910136116c47c |+|
  0xc5225e8bed9851e |+| 0xe5b3bbe1c9f3ea8 |+| 0x106451937a67f11a |+| 0x126d6768d8339c74 |+|
  done
private theorem cost_5_2 :fO 3 12 5 2 :=
  0x9e08f7400d13ee8 |+| 0x9dec7faeecece0e |+| 0x9dd0081dccdd9a8 |+| 0xd784a2bc9f18864 |+|
  0x111393d5b72413a8 |+| 0x14aedd7fa4657b74 |+| 0x184a272991b5bfc8 |+| 0x1be570d37f14e0a4 |+|
  0x1f80ba7d6c82de08 |+|
  done
private theorem cost_6_3 :fO 3 4 6 3 :=
  0x11e91f9a9bdf3dd1 |+|
  done
private theorem eNX {b j c:ℕ} (hj:j≤6) (hb:b<cutoff j)
    (hc:2*c≤j) (ht:c≤b) (hi:j≤b+c) : jX ⟨b,j,c⟩≤0x1f80ba7d6c82de08:= by
  have hc' : c≤j/2 := by omega
  interval_cases j
  all_goals interval_cases c
  · exact cost_0_0 b (by omega) hb
  · exact cost_1_0 b (by omega) hb
  · exact cost_2_0 b (by omega) hb
  · exact cost_2_1 b (by omega) hb
  · exact cost_3_0 b (by omega) hb
  · exact cost_3_1 b (by omega) hb
  · exact cost_4_0 b (by omega) hb
  · exact cost_4_1 b (by omega) hb
  · exact cost_4_2 b (by omega) hb
  · exact cost_5_0 b (by omega) hb
  · exact cost_5_1 b (by omega) hb
  · exact cost_5_2 b (by omega) hb
  · have stop : b<4 := hb
    omega
  · have stop : b<4 := hb
    omega
  · have stop : b<4 := hb
    omega
  · exact cost_6_3 b (by omega) hb
private theorem dEV:gap A*P6.LM=0x1f80ba7d6c838a84:=rfl
theorem uq : ∀ a :Jn,Allocation a →
    commonFee a+c5H a+lowFee small≤gap A*P6.LM:= by
  rintro ⟨b,j,c⟩ ha
  obtain ⟨hj,hb⟩:=limits ha
  rw [eNY,dEV]
  exact (eNX hj hb ha.top_index ha.top_total ha.index_total).trans (by decide)
end P6_8
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 MvPolynomial Finset Filter
open P5_8 (Jn Equation ProperCharts caps smallCaps donorCaps chartCaps properDegree componentCap)
open P5_8_5
open scoped BigOperators Polynomial
open P5_8_5 (cp0)
open P5_8_5 (within mix_mono mix_symm jetCaps_ok repair_ok bct floor_mix)
open qTS2oyd (addCaps jetCaps_mul)
open i4 (aTZ)
private theorem image_slope {L R:BL 2} (hL:L≠0) (hR:R≠0)
    (hrel :IsRelPrime L R) (F:ProperCharts L R)
    (hd : ∀ i,(affineHilbertPolynomial (F.ideal i)).natDegree=1) :
    (∑ i,affineDegree (F.ideal i))≤ mix (jetCaps L) (jetCaps R) chartCaps := by
  obtain ⟨shift,hshift⟩:=qIWmIFe.proof F
  obtain ⟨hu₁,hu₂,hu₃⟩:=A9
  have hu:=(tendsto_add_atTop_nat shift).eventually
    (qTS2oyd.proof L R hL hR hrel chartCaps hu₁ hu₂ hu₃)
  have he : ∀ᶠ m:ℕ in atTop,∀ i:Fin F.count,
      (affineHilbertPolynomial (F.ideal i)).eval (m:ℚ) =
        (affineHilbertFunction (F.ideal i) m:ℚ) :=
    eventually_all.mpr fun i=>eventually_eval_affineHilbertPolynomial (F.ideal i)
  let s := ∑ i,affineDegree (F.ideal i)
  let t := ∑ i,(affineHilbertPolynomial (F.ideal i)).coeff 0
  let M:=mix (jetCaps L) (jetCaps R) chartCaps
  let B:=boxDifference chartCaps (jetCaps L) (jetCaps R) 0
  have hle : ∀ᶠ m:ℕ in atTop,s*(m:ℚ)+t≤M*(m:ℚ)+(M*shift+B) := by
    filter_upwards [he,hu] with m hm hq
    have hs :s*(m:ℚ)+t=(∑ i,affineHilbertFunction (F.ideal i) m:ℕ) := by
      rw [Nat.cast_sum,zkq,← zfW]
      exact Finset.sum_congr rfl fun i _=>(linear_eval _ (hd i) _).symm.trans (hm i)
    rw [hs]
    refine ((Nat.cast_le (α:=ℚ)).mpr (hshift m)).trans ?_
    rw [boxDifference_linear,Nat.cast_add,mul_add,add_assoc] at hq
    exact hq
  exact cp0 hle
private def sumCaps {ι:Type*} (s :zJe ι) (a :ι→Jn) :Jn :=
  ⟨∑ i∈s,(a i).B,∑ i∈s,(a i).J,∑ i∈s,(a i).C⟩
private theorem eOT {ι:Type*} (s :zJe ι) (p:ι→BL 2)
    (h: (∏ i∈s,p i)≠0) :jetCaps (∏ i∈s,p i)=sumCaps s (jetCaps ∘ p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [jetCaps,sumCaps]
    rw [← MvPolynomial.C_1,weightedTotalDegree_C]
  | insert i s hi ih =>
    rw [prod_insert hi] at h ⊢
    rw [jetCaps_mul (left_ne_zero_of_mul h) (right_ne_zero_of_mul h),ih (right_ne_zero_of_mul h)]
    simp [sumCaps,addCaps,hi]
private theorem sum_mix {ι:Type*} (s :zJe ι) (a :ι→Jn) (b u:Jn) :
    (∑ i∈s,mix (a i) b u)=mix (sumCaps s a) b u:= by
  simp only [mix,sumCaps,Nat.cast_sum,zkq,zfW]
private theorem caps_mono {L R:BL 2} (h:L∣R) (hR:R≠0) :
    within (jetCaps L) (jetCaps R) := by
  obtain ⟨V,rfl⟩:=h
  rw [jetCaps_mul (left_ne_zero_of_mul hR) (right_ne_zero_of_mul hR)]
  exact ⟨z8K ..,z8K ..,z8K ..⟩
private theorem left_ne {Q:Equation} {w:Node→K} (hQ:Q≠0) (d:Companion Q w) :
    d.left≠0:= by
  apply apQ.b6j
  rw [d.azo] at hQ
  exact right_ne_zero_of_mul hQ
theorem ePy {Q:Equation} {w:Node→K} (hQ:Q≠0) (d:Companion Q w)
    {F:FactorCharts d.left d.right} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w)
    (hcover : ∀ f∈T,∃ i j,Gp f∈(F.charts i).image j) :
    gap A*T.card≤ c5H (caps d.common) := by
  classical
  let p (i:Fin F.count) :=apQ.initial (F.factor i)
  have hL:=left_ne hQ d
  have hdvd (i:Fin F.count) :p i∣d.left :=
    (dvd_prod_of_mem p (mem_univ i)).trans F.bKQ
  have hn (i:Fin F.count) :p i≠0:=ne_zero_of_dvd_ne_zero hL (hdvd i)
  have hrel (i:Fin F.count) :IsRelPrime (p i) d.right:=d.coprime.of_dvd_left (hdvd i)
  let I:=Σ i:Fin F.count,Fin (F.charts i).count
  let C (i:I) :=(F.charts i.1).ideal i.2
  have dim (i:I) : (affineHilbertPolynomial (C i)).natDegree=1 :=
    (enK (F.charts i.1) i.2).2.trans
      (dOy (hn i.1) (hrel i.1) ((F.charts i.1).minimal i.2))
  let a :=(smallCaps.wD (caps d.common)).repair
  let b:=(donorCaps.wD (caps d.common)).repair
  have hs :jetCaps (∏ i,p i)=sumCaps univ (jetCaps ∘ p) :=
    eOT _ _ (ne_zero_of_dvd_ne_zero hL F.bKQ)
  have ha :within (sumCaps univ (jetCaps ∘ p)) a := by
    rw [← hs]
    exact ⟨(caps_mono F.bKQ hL).1.trans (aFz.aIz.mp d.left_band).1,
      (caps_mono F.bKQ hL).2.1.trans (aFz.aIz.mp d.left_band).2.1,
      (caps_mono F.bKQ hL).2.2.trans (aFz.aIz.mp d.left_band).2.2⟩
  have hb:within (jetCaps d.right) b:=aFz.aIz.mp d.right_band
  have hcount:zhP I≤ componentCap (caps d.common) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ i,(p i).totalDegree*d.right.totalDegree :=
        sum_le_sum fun i _=>component_count (hn i) (hrel i) (F.charts i)
      _=(sumCaps univ (jetCaps ∘ p)).B*(jetCaps d.right).B :=
        (zkq ..).symm
      _≤_:=Nat.mul_le_mul (ha.1.trans (by rfl)) (hb.1.trans (by rfl))
  have hdeg: (∑ i,affineDegree (C i))≤(properDegree (caps d.common) :ℚ) := by
    have hsum: (∑ i,affineDegree (C i))≤ mix a b chartCaps := by
      obtain ⟨_,hc,hj⟩:=A9
      have h₁:=mix_mono ha (jetCaps_ok d.right) hc.le hj.le
      have h₂:mix (jetCaps d.right) a chartCaps≤ mix b a chartCaps :=
        mix_mono hb (repair_ok (smallCaps.wD (caps d.common))) hc.le hj.le
      rw [mix_symm (jetCaps d.right) a,mix_symm b a] at h₂
      calc
        _ = ∑ i,∑ j,affineDegree (C ⟨i,j⟩) :=Fintype.sum_sigma _
        _ ≤ ∑ i,mix (jetCaps (p i)) (jetCaps d.right) chartCaps :=
          sum_le_sum fun i _=>image_slope (hn i) d.right_ne (hrel i) (F.charts i) (fun j=>dim ⟨i,j⟩)
        _=mix (sumCaps univ (jetCaps ∘ p)) (jetCaps d.right) chartCaps :=
          sum_mix _ (jetCaps ∘ p) _ _
        _≤_:=h₁.trans h₂
    choose z hz using fun i:I=>linear_degree_integral (C i) (dim i)
    have hint : (∑ i,affineDegree (C i))=((∑ i,z i:ℤ) :ℚ) := by simp [hz,Int.cast_sum]
    have hfloor :=(Int.floor_mono hsum).trans_eq (floor_mix a b chartCaps (repair_ok _) (repair_ok _) bct)
    rw [hint,Int.floor_intCast] at hfloor
    rw [hint]
    exact_mod_cast hfloor
  let part (i:I) :=T.filter fun f=>Gp f∈(F.charts i.1).image i.2
  have hc:T.card ≤ ∑ i,(part i).card:= by
    apply (card_le_card (t:=univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i,j,hij⟩:=hcover f hf
    exact mem_biUnion.mpr ⟨⟨i,j⟩,mem_univ _,mem_filter.mpr ⟨hf,hij⟩⟩
  have hp (i:I) : (gap A:ℚ)*(part i).card≤(errors A:ℚ)*affineDegree (C i)+gap A :=
    (aTZ (T:=part i) (fun _ hf=>ht (mem_filter.mp hf).1) agreement_ok
      (enK (F.charts i.1) i.2).1 (dim i)
      (fun _ hf=>zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2)).1
  have hq: (T.card:ℚ) ≤ ∑ i,((part i).card:ℚ) := by exact_mod_cast hc
  have hbill: (gap A:ℚ)*T.card≤(errors A:ℚ)*properDegree (caps d.common) +
      gap A*componentCap (caps d.common) := calc
    _≤(gap A:ℚ) * ∑ i,((part i).card:ℚ) :=mul_le_mul_of_nonneg_left hq (zqJ _)
    _ = ∑ i,(gap A:ℚ)*(part i).card:=mul_sum ..
    _≤_:=sum_le_sum fun i _=>hp i
    _=(errors A:ℚ)*(∑ i,affineDegree (C i))+gap A*zhP I:= by
      rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ,mul_comm (zhP I:ℚ)]
    _≤_:=add_le_add (mul_le_mul_of_nonneg_left hdeg (zqJ _))
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) (zqJ _))
  unfold c5H
  exact_mod_cast hbill
end
end P6_8
end
section
set_option autoImplicit true
set_option maxRecDepth 4000
namespace P6_8
noncomputable section
open i4 apQ MvPolynomial PolynomialDifferential UniqueFactorizationMonoid
open P5_8 (small small_shape ProperCharts chartOpen ke)
open scoped Polynomial BigOperators
open cxa (cVd cfE)
local instance :StrongNormalizationMonoid Equation :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private theorem charts (G:Equation) (R:BL 2) (hG:ato small G) :
    ∃ F:ProperCharts (initial G) R,∀ f :(Polynomial K),f.degree<k →
      differentialSpecialization G f=0 →
      differentialSpecialization (separant G (zym 2)) f≠0 →
      zY9 (ahT f) R=0 → ∃ j,Gp f∈F.image j:= by
  classical
  let S:=(ke (initial G) R).minimalPrimesFinset.filter fun J=>T4 G∉J
  let e :Fin S.card ≃ ↥S:=(zFl (Fintype.card_coe S)).symm
  have he (i:Fin S.card) :=Finset.mem_filter.mp (e i).property
  have hm (i:Fin S.card) : (e i).val∈(ke (initial G) R).minimalPrimes :=
    Ideal.mem_minimalPrimesFinset.mp (he i).1
  let F:ProperCharts (initial G) R := {
    count:=S.card
    component:= fun i=>(e i).val
    distinct :=Subtype.val_injective.comp e.injective
    minimal:=hm
    bY:= fun _=>bY G (initial G)
    den_reg:= fun i h=>(he i).2 ((hm i).isPrime.mem_of_pow_mem t h)
    bands := fun _=> by
      simp only [bY]
      exact ⟨b0p hG,fun j =>
        eFC (G:=G) small_shape hG (cxb.proof small small_shape G hG) j⟩
    recover := fun _ x hx j=>a2o G (initial G) x (fun hz=>hx.2 (by
      change zY9 x (T4 G^t)=0
      rw [map_pow,hz,zero_pow (by decide :t≠0)])) j }
  refine ⟨F,?_⟩
  intro f hf hroot hsep hR
  let ev :=zY9 (ahT f)
  have hL:ev (initial G)=0:= by rw [bHS,hroot,map_zero]
  have hS:ev (T4 G)≠0:= by
    rw [eom]
    exact (map_ne_zero_iff RG bch).mpr hsep
  have hcut:ke (initial G) R≤RingHom.ker ev := by
    simp only [ke,Ideal.span_insert,sup_le_iff,Ideal.span_singleton_le_iff_mem]
    exact ⟨hL,hR⟩
  let: (RingHom.ker ev).IsPrime :=RingHom.ker_isPrime ev
  obtain ⟨J,hJ,hpoint⟩:=Ideal.exists_minimalPrimes_le hcut
  let v : ↥S:=⟨J,Finset.mem_filter.mpr
    ⟨Ideal.mem_minimalPrimesFinset.mpr hJ,fun h=>hS (hpoint h)⟩⟩
  let i:=e.symm v
  refine ⟨i,ahT f,?_,dIj G (initial G) f hf hroot hS⟩
  change ahT f∈chartOpen (e i).val (bY G (initial G))
  rw [e.apply_symm_apply v]
  exact ⟨fun _ h=>hpoint h,by
    change ev (T4 G^t)≠0
    rw [map_pow]
    exact pow_ne_zero _ hS⟩
theorem factor_charts {w:Node→K} {Q:Equation} (hQ:ato small Q)
    (d:Companion Q w) :
    ∃ F:FactorCharts d.left d.right,
      ∀ f∈close A w,ae8 Q f→differentialSpecialization d.common f≠0 →
        ∃ i j,Gp f∈(F.charts i).image j:= by
  classical
  have hLn:d.leftNative≠0:= fun h =>
    hQ.1 (d.azo.trans (by rw [h,mul_zero]))
  have hLQ:d.leftNative∣Q:=⟨d.jO,d.azo.trans (mul_comm _ _)⟩
  let S:=(normalizedFactors d.leftNative).toFinset
  let e :Fin S.card ≃ ↥S:=(zFl (Fintype.card_coe S)).symm
  let G (i:Fin S.card) :=(e i).val
  have hG (i:Fin S.card) :ato small (G i) :=
    eHq hQ ((dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (e i).property)).trans hLQ)
  choose C hC using fun i=>charts (G i) d.right (hG i)
  have hprod: (∏ i,initial (G i))∣d.left:= by
    have hs : (∏ g∈S,g)∣d.leftNative :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hLn).dvd
    have hm:=map_dvd cVd hs
    rw [map_prod] at hm
    change (∏ g∈S,initial g)∣d.left at hm
    have he : (∏ i,initial (G i)) = ∏ g∈S,initial g :=
      (e.prod_comp (fun g : ↥S=>initial g.val)).trans (Finset.prod_coe_sort S initial)
    rwa [he]
  refine ⟨⟨S.card,G,hprod,C⟩,?_⟩
  intro f hf hr ho
  obtain ⟨g,hgi,hgd,hgr,hgs⟩:=hr
  have hgL:g∣d.leftNative := by
    rw [d.azo] at hgd
    rcases hgi.prime.dvd_mul.mp hgd with h | h
    · obtain ⟨l,hl⟩:=d.removed_support
      have hz :=map_dvd (zY9 (ahT f)) ((map_dvd cVd h).trans hl)
      change zY9 (ahT f) (initial g) ∣
        zY9 (ahT f) (initial d.common^l) at hz
      rw [bHS,hgr,map_zero,zero_dvd_iff,map_pow,bHS] at hz
      exact (pow_ne_zero l ((map_ne_zero_iff RG bch).mpr ho) hz).elim
    · exact h
  obtain ⟨g',hmem,hassoc⟩:=exists_mem_normalizedFactors_of_dvd hLn hgi hgL
  obtain ⟨hroot,hsep⟩:=cfE hassoc hgr hgs
  let v : ↥S:=⟨g',Multiset.mem_toFinset.mpr hmem⟩
  let i:=e.symm v
  have hi:G i=g' := congrArg Subtype.val (e.apply_symm_apply v)
  obtain ⟨j,hj⟩:=hC i f hf.1 (by rwa [hi]) (by rwa [hi]) (d.roots f hf ho).2
  exact ⟨i,j,hj⟩
end
end P6_8
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 Finset PolynomialDifferential MvPolynomial
open P5_8 (Jn Equation caps tariffShape)
open scoped Polynomial BigOperators
private theorem add_tail (h:ℕ) :h+h*(h-1)=h^2 := by
  cases h with
  | zero=>rfl
  | succ h=>rw [Nat.succ_sub_one]; ring
private theorem first_order {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:DifferentialPolynomial K 1}
    (hq:bRZ s Q) (hroot : ∀ f∈T,differentialSpecialization Q f=0) :
    gap A*T.card≤lowFee s := by
  classical
  let U:=T.filter (ae8 Q)
  let V:=T.filter fun f => ¬ ae8 Q f
  obtain ⟨F,hF,hcov⟩:=byX.proof s hs Q hq
  have hcap:=cOg (T:=U) (fun _ hf=>ht (mem_filter.mp hf).1) ha (Or.inl rfl)
    F (cxe.proof s hs F hF) (fun f hf =>
      hcov f (ht (mem_filter.mp hf).1).1 (mem_filter.mp hf).2)
  have hU:gap A*U.card≤errors A*R₁ s+gap A*F.count:= by
    have hcast:gap A*U.card≤errors A*(1*R₁ s)+gap A*F.count:= by
      exact_mod_cast hcap
    simpa only [one_mul] using hcast
  obtain ⟨G,hG,hd,htail⟩:=cxf.proof s hs Q hq
  have hV:V.card≤H s*(H s-1) := by
    apply (Polynomial.card_le_degree_of_subset_roots (p:=G) ?_).trans hd
    intro f hf
    obtain ⟨hfT,hsing⟩:=mem_filter.mp (show f∈V from hf)
    exact (Polynomial.mem_roots hG).mpr (htail f (ht hfT).1 (hroot f hfT) hsing)
  have hsizes :U.card+V.card=T.card:=card_filter_add_card_filter_not ..
  calc
    gap A*T.card=gap A*U.card+gap A*V.card:= by rw [← zws,hsizes]
    _≤(errors A*R₁ s+gap A*H s)+gap A*(H s*(H s-1)) :=
      z9f (hU.trans (z3b (zBI _ hF.count) _))
        (zBI _ hV)
    _=lowFee s := by rw [lowFee,add_assoc,← zws,add_tail]
theorem nonregular_count {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:Equation}
    (hq:ato s Q)
    (hroot : ∀ f∈T,differentialSpecialization Q f=0 ∧ ¬ ae8 Q f) :
    gap A*T.card≤lowFee s := by
  obtain ⟨Q₁,hQ₁,hᵣ⟩:=a9N.proof s hs Q hq
  exact first_order hs ht ha hQ₁ (fun f hf=>hᵣ f (ht hf).1 (hroot f hf).1 (hroot f hf).2)
private theorem ceY {s :Source} (hs :Rz s) {w:Node→K} {T:zJe (Polynomial K)}
    (ht: (T:Set (Polynomial K))⊆close A w) (ha :aRk A) {Q:Equation}
    (hq:ato s Q) (hreg : ∀ f∈T,ae8 Q f) :
    gap A*T.card≤ regularFee s := by
  obtain ⟨F,hF,hcov⟩:=apQ.of_children cxa.proof cxb.proof s hs Q hq
  have hcap:=cOg ht ha (Or.inr rfl) F
    (aFz.of_children cxc.proof cxd.proof s hs F hF)
    (fun f hf=>hcov f (ht hf).1 (hreg f hf))
  have hcast:gap A*T.card≤errors A*(2*R₂ s)+gap A*F.count:= by
    exact_mod_cast hcap
  exact hcast.trans (z3b (zBI _ hF.count) _)
private theorem tariff_shape {a :Jn} (ha :Allocation a) :Rz (tariffShape a) := by
  obtain ⟨hB,hJ,_,_,hc,_,_⟩:=ha
  have hbound:max 2 (max a.B a.J)≤83:= by omega
  have hchar :max N (83*(83-1))<p:= by decide
  refine ⟨Nat.zero_lt_one,?_,?_,?_,?_,?_,?_⟩
  · change 0< max 1 a.C
    omega
  · change 2*max 1 a.C≤ max 2 a.J
    omega
  · change max 2 a.J≤ max 2 (max a.B a.J)
    omega
  · exact (max_le_max le_rfl (Nat.mul_le_mul hbound (Nat.sub_le_sub_right hbound 1))).trans_lt hchar
  · intro j hj
    simp [tariffShape] at hj
  · intro j hj _
    simp [tariffShape] at hj
private theorem no_regular_of_zero_top {Q:Equation} (hQ:Q≠0) (hz : (caps Q).C=0)
    (f :(Polynomial K)) : ¬ ae8 Q f := by
  rintro ⟨G,_,hd,_,hs⟩
  have htop:=weightedTotalDegree_le_of_dvd (Pi.single (some (zym 2)) 1) hd hQ
  rw [weightedTotalDegree_piSingle,weightedTotalDegree_piSingle] at htop
  change Q.degreeOf (some (zym 2))=0 at hz
  rw [hz] at htop
  change differentialSpecialization (pderiv (some (zym 2)) G) f≠0 at hs
  rw [pderiv_eq_zero_of_degreeOf_eq_zero (Nat.eq_zero_of_le_zero htop)] at hs
  exact hs (map_zero (differentialSpecializationHom f))
theorem common_count {w:Node→K} {T:zJe (Polynomial K)} (ht: (T:Set (Polynomial K))⊆close A w)
    (ha :aRk A) {Q:Equation} (hq:Q≠0) (halloc:Allocation (caps Q))
    (hroot : ∀ f∈T,differentialSpecialization Q f=0) :
    gap A*T.card≤ commonFee (caps Q) := by
  classical
  let a :=caps Q
  let s :=tariffShape a
  have hshape :Rz s :=tariff_shape halloc
  have horder :ato s Q:= by
    refine ⟨hq,?_,?_,?_⟩
    · change a.B≤ max 2 (max a.B a.J)
      omega
    · exact le_max_right 2 a.J
    · exact le_max_right 1 a.C
  by_cases hz :a.C=0
  · rw [commonFee,ite_eq_left hz,add_zero]
    exact nonregular_count hshape ht ha horder
      (fun f hf=>⟨hroot f hf,no_regular_of_zero_top hq hz f⟩)
  · let U:=T.filter (ae8 Q)
    let V:=T.filter fun f => ¬ ae8 Q f
    have hU:=ceY (T:=U) hshape (fun _ hf=>ht (mem_filter.mp hf).1) ha horder
      (fun _ hf=>(mem_filter.mp hf).2)
    have hV:=nonregular_count (T:=V) hshape (fun _ hf=>ht (mem_filter.mp hf).1) ha horder
      (fun f hf=>⟨hroot f (mem_filter.mp hf).1,(mem_filter.mp hf).2⟩)
    have hsizes :U.card+V.card=T.card:=card_filter_add_card_filter_not ..
    rw [← hsizes,zws,commonFee,ite_eq_right hz,add_comm (lowFee s)]
    exact z9f hU hV
end
end P6_8
end
section
set_option autoImplicit true
namespace P6_8
noncomputable section
open i4 PolynomialDifferential Finset
open P5_8 (Equation small small_shape)
open scoped Polynomial
def c1 :Prop :=P5_8_2.c4
def c2 :Prop :=
  ∀ (w:Node→K) (Q:Equation),ato small Q →
    (∀ f∈close A w,differentialSpecialization Q f=0) →
    DonorSurplus w→Nonempty (Companion Q w)
theorem of_children (h1 :c1) (h2 :c2) :i4.axW P6.dw P6.LM:= by
  classical
  intro w
  have hfin: (close A w).Finite :=
    ReedSolomon.closePolynomialSet_finite node w (show k≤A from agreement_ok.gt_degree)
  obtain ⟨Q,hQ,hroot⟩:=small_equation w
  obtain ⟨hr,hm⟩:=P5_8_2.of_children qHvCGFa.proof qNtJgmd.proof qZtSHva.proof h1
  obtain ⟨d⟩:=h2 w Q hQ hroot (donor_surplus hr hm w)
  obtain ⟨F,hF⟩:=factor_charts hQ d
  let T:=hfin.toFinset
  let commonMarks :=T.filter fun f=>differentialSpecialization d.common f=0
  let offCommon :=T.filter fun f=>differentialSpecialization d.common f≠0
  let U:=offCommon.filter (ae8 Q)
  let V:=offCommon.filter fun f => ¬ ae8 Q f
  have ht (f :(Polynomial K)) (hf :f∈T) :f∈close A w:=hfin.mem_toFinset.mp hf
  have hs (f :(Polynomial K)) (hf :f∈offCommon) :f∈close A w:=ht f (mem_filter.mp hf).1
  have hz :=common_count (T:=commonMarks) (fun f hf=>ht f (mem_filter.mp hf).1) agreement_ok
    d.common_ne d.allocation (fun _ hf=>(mem_filter.mp hf).2)
  have hu:=ePy hQ.1 d (F:=F) (T:=U) (fun f hf=>hs f (mem_filter.mp hf).1)
    (fun f hf=>hF f (hs f (mem_filter.mp hf).1) (mem_filter.mp hf).2
      (mem_filter.mp (mem_filter.mp hf).1).2)
  have hv :=nonregular_count (T:=V) small_shape (fun f hf=>hs f (mem_filter.mp hf).1)
    agreement_ok hQ (fun f hf=>⟨hroot f (hs f (mem_filter.mp hf).1),(mem_filter.mp hf).2⟩)
  have hzs :commonMarks.card+offCommon.card=T.card:=card_filter_add_card_filter_not ..
  have huv :U.card+V.card=offCommon.card:=card_filter_add_card_filter_not ..
  have hcard:gap A*T.card≤gap A*P6.LM:= by
    rw [← hzs,← huv,← add_assoc,zws,zws]
    exact (z9f (z9f hz hu) hv).trans (uq _ d.allocation)
  exact ⟨hfin,by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.le_of_mul_le_mul_left hcard (Nat.sub_pos_of_lt agreement_ok.gt_degree)⟩
end
end P6_8
end
