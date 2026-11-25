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
    (hv :48729*v<0x60a5bb93bf610c) :
    (i4.gap A+2)*Gq ⟨b,j,0⟩<donorMargin:= by
  rw [h,hs]
  exact hv
private theorem r0: (gap A+2)*Gq ⟨24,0,0⟩<donorMargin:= by
  refine excluded (n:=260) (v :=0x81cb446b5c) (cofactor_zero 24) ?_ (by decide)
  exact emptySum (capRow 24 0)
    +[32,0x22edf94c40] +[32,0x1d6db3cc40] +[32,0x17ed6e4c40]
    +[32,0x126d28cc40] +[32,0xcece34c40] +[32,0x76dcf9620]
    +[32,0x28064611c] +[32,0x39e6b100] +[4,0x245e0]
private theorem r1: (gap A+2)*Gq ⟨23,1,0⟩<donorMargin:= by
  refine excluded (n:=271) (v :=0x7f7b569af0) (cofactor_index 23 1 (by decide)) ?_ (by decide)
  exact emptySum (capRow 23 1)
    +[32,0x228882b8b0] +[32,0x1c80365eb0] +[32,0x16d00af4b0]
    +[32,0x1175e47ab0] +[32,0xc6fa6f0b0] +[32,0x7bb3656b0]
    +[32,0x36a3bd5b4] +[32,0x95e63a84] +[15,0x1aebc98]
private theorem r2: (gap A+2)*Gq ⟨21,2,0⟩<donorMargin:= by
  refine excluded (n:=297) (v :=0x8138a6a33e) (cofactor_index 21 2 (by decide)) ?_ (by decide)
  exact emptySum (capRow 21 2)
    +[32,0x223f9c3810] +[32,0x1bdf01d010] +[32,0x1620d5e810]
    +[32,0x10fd988010] +[32,0xc6dc99810] +[32,0x869e93010]
    +[32,0x4ea774810] +[32,0x1f6e3e418] +[32,0x42612bf4]
    +[9,0x2b12c2]
private theorem r3: (gap A+2)*Gq ⟨19,3,0⟩<donorMargin:= by
  refine excluded (n:=329) (v :=0x80f327d84b) (cofactor_index 19 3 (by decide)) ?_ (by decide)
  exact emptySum (capRow 19 3)
    +[32,0x21f5157428] +[32,0x1b320fb728] +[32,0x1550144a28]
    +[32,0x10405f2d28] +[32,0xbf42c6028] +[32,0x85cb7e328]
    +[32,0x56b3db628] +[32,0x310f9d928] +[32,0x140dda630]
    +[32,0x2d7dfcf8] +[9,0x17bfe3]
private theorem r4: (gap A+2)*Gq ⟨16,4,0⟩<donorMargin:= by
  refine excluded (n:=390) (v :=0x81b178e76c) (cofactor_index 16 4 (by decide)) ?_ (by decide)
  exact emptySum (capRow 16 4)
    +[32,0x21c4a30bd0] +[32,0x1ac1f0cfd0] +[32,0x14c84893d0]
    +[32,0xfc2aa57d0] +[32,0xb9c161bd0] +[32,0x83f8bdfd0]
    +[32,0x5980ba3d0] +[32,0x3909567d0] +[32,0x214292bd0]
    +[32,0x10dc6efd0] +[32,0x686eb3d0] +[32,0x114c3464]
    +[6,0x41518]
private theorem r5: (gap A+2)*Gq ⟨11,5,0⟩<donorMargin:= by
  refine excluded (n:=391) (v :=0x814fe087f4) (cofactor_index 11 5 (by decide)) ?_ (by decide)
  exact emptySum (capRow 11 5)
    +[32,0x21c775b790] +[32,0x1ac727f590] +[32,0x14cc28e390]
    +[32,0xfc28c8190] +[32,0xb9666cf90] +[32,0x833cbcd90]
    +[32,0x586cf7b90] +[32,0x37b85d990] +[32,0x1fe02e790]
    +[32,0xfa5aa590] +[32,0x5ca11390] +[32,0x10ea3190]
    +[7,0x1cb134]
private theorem r6: (gap A+2)*Gq ⟨2,6,0⟩<donorMargin:= by
  refine excluded (n:=326) (v :=0x81fa628376) (cofactor_index 2 6 (by decide)) ?_ (by decide)
  exact emptySum (capRow 2 6)
    +[32,0x222eaf7b30] +[32,0x1bab1b8d30] +[32,0x15cf069f30]
    +[32,0x109dd0b130] +[32,0xc1ad9c330] +[32,0x84981d530]
    +[32,0x52d28e730] +[32,0x2c92ef930] +[32,0x120f40b30]
    +[32,0x37d81d30] +[6,0x408996]
private theorem r7: (gap A+2)*Gq ⟨1,7,0⟩<donorMargin:= by
  refine excluded (n:=279) (v :=0x71470d1c82) (cofactor_index 1 7 (by decide)) ?_ (by decide)
  exact emptySum (capRow 1 7)
    +[32,0x21bdbaa278] +[32,0x1a72bdbf78] +[32,0x13f26e2c78]
    +[32,0xe4847e978] +[32,0x97fc6f678] +[32,0x5a4675378]
    +[32,0x2c1a50078] +[32,0xe2fbfd78] +[23,0x130f5cc2]
private def cutoff :ℕ→ℕ
  | 0=>24
  | 1=>23
  | 2=>21
  | 3=>19
  | 4=>16
  | 5=>11
  | 6=>2
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
private theorem ee8:gap A=48727:=rfl
private theorem d1C:errors A=82346:=rfl
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
private theorem low_eq :lowFee small=0x4030ad3e5189c2:= by
  have hH :H small=1622 :=rfl
  have hI:I₁ small = 283:=rfl
  have ha :a₁ small=0x1953e058:=rfl
  have hd:d₁ small=0x469fa7d:=rfl
  have hr :R₁ small=0x33160a2d17:= by rw [R₁,hH,hd,hI,ha]
  rw [lowFee,d1C,ee8,hr,hH]
  rfl
private def HE (r n:ℕ) :=82346*r+48727*n
private def jX (a :Jn) :ℕ :=
  let s :=tariffShape a
  HE (R₁ s) (H s^2)+(if a.C=0 then 0 else HE (2*R₂ s) s.B) +
    HE (tW (smallCaps.wD a).repair (donorCaps.wD a).repair
      ⟨21495235,6160222,2752440⟩) (componentCap a)+0x4030ad3e5189c2
private theorem eNY (a :Jn) :commonFee a+c5H a+lowFee small=jX a := by
  rw [low_eq]
  simp only [jX,commonFee,c5H,properDegree,chart_eq,lowFee,regularFee,
    d1C,ee8,HE]
private def fO (b stop j c:ℕ) :Prop :=
  ∀ i,b≤ i→i<stop→jX ⟨i,j,c⟩≤0x1be2ed353fdc34b1
private theorem done {b j c:ℕ} : fO b b j c:= by
  intro i hl hu
  omega
private theorem bandCons {b stop j c v :ℕ}
    (he :jX ⟨b,j,c⟩=v) (hv :v≤0x1be2ed353fdc34b1)
    (ht:fO (b+1) stop j c) :fO b stop j c:= by
  intro i hl hu
  by_cases h:i=b
  · rwa [h,he]
  · exact ht i (by omega) hu
local notation:65 val:66 " |+| " tail:65=>bandCons (v :=val) rfl (by decide) tail
private theorem r00 :fO 0 24 0 0 :=
  0x1b5c8f2821d9dbd |+| 0x1b3ff608318511a |+| 0x1b235ce84148125 |+|
  0x1b06c4e1c4dcaf1 |+| 0x1aea2cdb48a0e19 |+| 0x1acd94d4cc94a9d |+|
  0x1ab0fcce50b807d |+| 0x1a9464c7d50afb9 |+| 0x1a77ccc1598d851 |+|
  0x1a5b34bade3fa45 |+| 0x1a3e9cb46321595 |+| 0x1a2204ade832a41 |+|
  0x1a056ca76d73849 |+| 0x19e8d4a0f2e3fad |+| 0x19cc3c9a788406d |+|
  0x19afa493fe53a89 |+| 0x19930c8d8452e01 |+| 0x197674870a81ad5 |+|
  0x1959dc8090e0105 |+| 0x193d447a176e091 |+| 0x1920ac739e2b979 |+|
  0x1904146d2518bbd |+| 0x18e77c66ac3575d |+| 0x18cae4603381c59 |+|
  done
private theorem dz :fO 1 23 1 0 :=
  0x1ab41cbbc2e726e |+| 0x1a978a3483db2d9 |+| 0x1a7af8c6b8a0d05 |+|
  0x1a5e6758ed9608d |+| 0x1a41d5eb22bad71 |+| 0x1a25447d580f3b1 |+|
  0x1a08b30f8d9334d |+| 0x19ec21a1c346c45 |+| 0x19cf9033f929e99 |+|
  0x19b2fec62f3ca49 |+| 0x19966d58657ef55 |+| 0x1979dbea9bf0dbd |+|
  0x195d4a7cd292581 |+| 0x1940b90f09636a1 |+| 0x192427a1406411d |+|
  0x1907963377944f5 |+| 0x18eb04c5aef4229 |+| 0x18ce7357e6838b9 |+|
  0x18b1e1ea1e428a5 |+| 0x1895507c56311ed |+| 0x1878bf0e8e4f491 |+|
  0x185c2da0c69d091 |+| done
private theorem jV :fO 2 21 2 0 :=
  0x1a0b64431c1e8a3 |+| 0x19eeda370aeb53b |+| 0x19d2502af9e7b2f |+|
  0x19b5c61ee913a7f |+| 0x19993c12d86f32b |+| 0x197cb206c7fa533 |+|
  0x196027fab7b5097 |+| 0x19439deea79f557 |+| 0x192713e297b9373 |+|
  0x190a89d68802aeb |+| 0x18edffca787bbbf |+| 0x18d175be69245ef |+|
  0x18b4ebb259fc97b |+| 0x189861a64b04663 |+| 0x187bd79a3c3bca7 |+|
  0x185f4d8e2da2c47 |+| 0x1842c3821f39543 |+| 0x1826397610ff79b |+|
  0x1809af6a02f534f |+| done
private theorem lp :fO 1 21 2 1 :=
  0x1c4a9277dd313b4 |+| 0x1c2e081b6102897 |+| 0x1ee53760736442a |+|
  0x219c66a585f5919 |+| 0x245395ea98b6764 |+| 0x270ac52faba6f0b |+|
  0x29c1f474bec700e |+| 0x2c7923b9d216a6d |+| 0x2f3052fee595e28 |+|
  0x31e78243f944b3f |+| 0x349eb1890d231b2 |+| 0x3755e0ce2131181 |+|
  0x3a0d1013356eaac |+| 0x3cc43f5849dbd33 |+| 0x3f7b6e9d5e78916 |+|
  0x42329de27344e55 |+| 0x44e9cd278840cf0 |+| 0x47a0fc6c9d6c4e7 |+|
  0x4a582bb1b2c763a |+| 0x4d0f5af6c8520e9 |+| done
private theorem xM :fO 3 19 3 0 :=
  0x196316bf5fe2dd3 |+| 0x194693ecd447383 |+| 0x192a111a48db28f |+|
  0x190d8e47bd9eaf7 |+| 0x18f10b753291cbb |+| 0x18d488a2a7b47db |+|
  0x18b805d01d06c57 |+| 0x189b82fd9288a2f |+| 0x187f002b083a163 |+|
  0x18627d587e1b1f3 |+| 0x1845fa85f42bbdf |+| 0x182977b36a6bf27 |+|
  0x180cf4e0e0dbbcb |+| 0x17f0720e577b1cb |+| 0x17d3ef3bce4a127 |+|
  0x17b76c6945489df |+| done
private theorem xd :fO 2 19 3 1 :=
  0x29c4e24828d32bf |+| 0x29a85e845ded4b0 |+| 0x361c5c0ab2f5c93 |+|
  0x42905991082ddd2 |+| 0x4f0457175d9586d |+| 0x5b78549db32cc64 |+|
  0x67ec522408f39b7 |+| 0x74604faa5eea066 |+| 0x80d44d30b510071 |+|
  0x8d484ab70b659d8 |+| 0x99bc483d61eac9b |+| 0xa63045c3b89f8ba |+|
  0xb2a4434a0f83e35 |+| 0xbf1840d06697d0c |+| 0xcb8c3e56bddb53f |+|
  0xd8003bdd154e6ce |+| 0xe47439636cf11b9 |+| done
private theorem Hz :fO 4 16 4 0 :=
  0x18aa7092e857de3 |+| 0x188df68bf4000c3 |+| 0x18717c84ffd7cff |+|
  0x1855027e0bdf297 |+| 0x18388877181618b |+| 0x181c0e70247c9db |+|
  0x17ff94693112b87 |+| 0x17e31a623dd868f |+| 0x17c6a05b4acdaf3 |+|
  0x17aa265457f28b3 |+| 0x178dac4d6546fcf |+| 0x1771324672cb047 |+|
  done
private theorem ID :fO 3 16 4 1 :=
  0x419c86d2403ed30 |+| 0x41800a702f77e3b |+| 0x5801408f911e1ca |+|
  0x6e8276aef2f3eb5 |+| 0x8503acce54f94fc |+| 0x9b84e2edb72e49f |+|
  0xb206190d1992d9e |+| 0xc8874f2c7c26ff9 |+| 0xdf08854bdeeabb0 |+|
  0xf589bb6b41de0c3 |+| 0x10c0af18aa500f32 |+| 0x1228c27aa08536fd |+|
  0x1390d5dc96bd5824 |+| done
private theorem LU :fO 2 16 4 2 :=
  0x54817c6bc7cf8bd |+| 0x546500d2bfc6f26 |+| 0x54488539b7d623d |+|
  0x752755f6fc82890 |+| 0x960626b4421cdaf |+| 0xb6e4f77188a519a |+|
  0xd7c3c82ed01b451 |+| 0xf8a298ec187f5d4 |+| 0x1198169a961d1623 |+|
  0x13a603a66ac1153e |+| 0x15b3f0b23f73f325 |+| 0x17c1ddbe1435afd8 |+|
  0x19cfcac9e9064b57 |+| 0x1bddb7d5bde5c5a2 |+| done
private theorem Db :fO 5 11 5 0 :=
  0x18025e6d661b1df |+| 0x17e5eb9ff75add7 |+| 0x17c978d288ca32b |+|
  0x17ad06051a691db |+| 0x17909337ac379e7 |+| 0x1774206a3e35b4f |+|
  done
private theorem LB :fO 4 11 5 1 :=
  0x6381c646ebf8b19 |+| 0x6365507d8c7a932 |+| 0x83f3be6cf1e8661 |+|
  0xa4822c5c5785cec |+| 0xc5109a4bbd52cd3 |+| 0xe59f083b234f616 |+|
  0x1062d762a897b8b5 |+| done
private theorem De :fO 3 11 5 2 :=
  0x9dfab9175e10206 |+| 0x9dde4417075057d |+| 0x9dc1cf16b0a85a2 |+|
  0xd7713656249eb0d |+| 0x111209d959982f44 |+| 0x14ad004d50f55247 |+|
  0x1847f6c148615416 |+| 0x1be2ed353fdc34b1 |+| done
private theorem eNX {b j c:ℕ} (hj:j≤6) (hb:b<cutoff j)
    (hc:2*c≤j) (ht:c≤b) (hi:j≤b+c) :
    jX ⟨b,j,c⟩≤0x1be2ed353fdc34b1:= by
  have hc' : c≤j/2 := by omega
  interval_cases j
  all_goals interval_cases c
  · exact r00 b (by omega) hb
  · exact dz b (by omega) hb
  · exact jV b (by omega) hb
  · exact lp b (by omega) hb
  · exact xM b (by omega) hb
  · exact xd b (by omega) hb
  · exact Hz b (by omega) hb
  · exact ID b (by omega) hb
  · exact LU b (by omega) hb
  · exact Db b (by omega) hb
  · exact LB b (by omega) hb
  · exact De b (by omega) hb
  · have h2 : b<2 := hb
    omega
  · have h2 : b<2 := hb
    omega
  · have h2 : b<2 := hb
    omega
  · have h2 : b<2 := hb
    omega
private theorem dEV:gap A*P6.LM=0x1be2ed353fdc89da:=rfl
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
