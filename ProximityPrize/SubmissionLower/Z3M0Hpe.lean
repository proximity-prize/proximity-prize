import ProximityPrize.SubmissionLower.Z8Nymda
import ProximityPrize.SubmissionLower.Zsr715c
import ProximityPrize.SubmissionLower.CG
import ProximityPrize.SubmissionLower.Zx0Npsd
import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.A2
import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.ZwiFoca
import ProximityPrize.SubmissionLower.ZG1muKa
import ProximityPrize.SubmissionLower.ZIBb1mb
import ProximityPrize.SubmissionLower.ZOrwy2c
set_option Elab.async false
open _root_ renaming Finset.range_mono → znF, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_le_sum → zQk, Fintype.card → zhP, Fintype.card_le_of_injective → zWJ, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_right → zs0, LinearMap.ker → z83, LinearMap.range_domRestrict → zyK, Module.Finite → zAa, Module.Finite.of_basis → zwB, Module.finrank → zsE, Nat.eq_zero_of_le_zero → za7, Nat.zero_add → zbc
section
set_option autoImplicit true
namespace qpkGSFe
open aR (Shape aO)
open P6_6
open P6_6_8 (sharedOrder dNb Q5)
open P6_6_8_3 (caps retainedBox layerMass)
open q33KzTa (tu AffineFits)
open private block_affine from ProximityPrize.SubmissionLower.Z8Nymda
open wV (HY)
open private bSj.aTY from ProximityPrize.SubmissionLower.E6
open private eiI from ProximityPrize.SubmissionLower.E6
open private WC bP5 aEH byM bvX from ProximityPrize.SubmissionLower.E6
open private width total mass_anti from ProximityPrize.SubmissionLower.Zsr715c
open scoped BigOperators
private abbrev ahX (v :Shape) :Shape :=⟨(caps (retainedBox v)).b+1,0,0⟩
abbrev ot (b j t:ℕ) :Prop :=
  let v :Shape :=⟨b,j,t⟩
  CompanionTest v (ahX v) (sharedOrder v)
private def sample (v r :Shape) (ell i:ℕ) :ℕ :=
  AJ.ahC Wk ((v.scale (i+1)).plus (r.scale (i+2 - ell)))
private theorem homogeneous (x :Shape) :Gq x≤AJ.ahC Wk x := by
  unfold Gq AJ.ahC
  by_cases h:x.b≤Wk.b∧x.j≤Wk.j∧x.t≤Wk.t
  · simp only [ite_eq_left h]
    rw [← show HY (Wk.b - x.b+1) (Wk.j - x.j)
      (Wk.t - x.t)=AJ.bmI
      ⟨Wk.b - x.b,Wk.j - x.j,Wk.t - x.t⟩ from rfl,bSj.aTY]
    exact zQk fun _ _=>eiI (min_le_left _ _) le_rfl le_rfl
  · simp only [ite_eq_right h,le_rfl]
private theorem sample_ge (v r :Shape) (ell i:ℕ) :layerMass v r ell i≤ sample v r ell i:= by
  rw [layerMass,P6_6_8.aUJ]
  exact homogeneous _
def bi9 (v r :Shape) (ell start:ℕ) :List (List ℕ×ℕ)→Prop
  | []=>True
  | (ws,m) :: rest=>aEH (sample v r ell) start ws=m ∧
      bi9 v r ell (start+ws.sum) rest
private theorem bxv (v r :Shape) (ell n:ℕ) (cs :List (List ℕ×ℕ))
    (h:bi9 v r ell n cs) :WC (layerMass v r ell) n (width cs)≤total cs := by
  induction cs generalizing n with
  | nil=>simp [width,total,WC]
  | cons c cs ih =>
    obtain ⟨ws,m⟩:=c
    rw [width,total,bP5]
    have hw:=byM (mass_anti v r ell) ws n
    have hm:=bvX (sample_ge v r ell) ws n
    exact Nat.add_le_add (hw.trans (hm.trans_eq h.1)) (ih _ h.2)
private def xF:ℕ→ℕ→List ℕ
  | 0,_=>[]
  | fuel+1,w =>
    if w=0 then []
    else if w % 8=0 then w/8 % 256 :: xF fuel (w/2048)
    else w % 8 :: xF fuel (w/8)
def unpack (w:ℕ) :List ℕ×ℕ:=(xF 8 (w >>> 45),w % 0x200000000000)
private theorem azU {b j n a s :ℕ} (h:tu j n a s)
    (hj:0<j) (hf :AffineFits b j n) (r :Shape) {ell:ℕ}
    (hn:n≤ell - 1) :
    WC (layerMass ⟨b,j,1⟩ r ell) 0 n=a - b*s := by
  have he :=block_affine hj hf
  rw [h.1,h.2] at he
  have hblock :q33KzTa.block ⟨b,j,1⟩ 0 n=a - b*s := by omega
  rw [← hblock]
  simp only [q33KzTa.block,AJ.bOw,WC,zbc,
    q33KzTa.stock_eq,layerMass,P6_6_8.aUJ]
  refine zUo rfl fun i hi => ?_
  have hd:i+2 - ell=0:= by have :=Finset.mem_range.mp hi; omega
  simp only [hd,Shape.plus,Shape.scale,Nat.zero_mul,Nat.add_zero]
theorem row {b j n a s len mass :ℕ} {cs :List (List ℕ×ℕ)}
    (hbase :tu j n a s) (hj:0<j) (hf :AffineFits b j n)
    (hn:n≤ sharedOrder ⟨b,j,1⟩ - 1)
    (hs :bi9 ⟨b,j,1⟩ (ahX ⟨b,j,1⟩) (sharedOrder ⟨b,j,1⟩) n cs)
    (hlen:n+width cs=len) (hm:total cs=mass)
    (hz :layerMass ⟨b,j,1⟩ (ahX ⟨b,j,1⟩) (sharedOrder ⟨b,j,1⟩) len=0)
    (hlt:a - b*s+mass<gG) :ot b j 1 := by
  let v :Shape :=⟨b,j,1⟩
  let r :=ahX v
  let ell:=sharedOrder v
  change CompanionTest v r ell
  have htail:=bxv v r ell n cs hs
  rw [hm] at htail
  have hfull:WC (layerMass v r ell) 0 len<gG:= by
    rw [← hlen,bP5,zbc,azU hbase hj hf r hn]
    exact (Nat.add_le_add_left htail _).trans_lt hlt
  unfold CompanionTest
  simp only [← P6_6_8.aUJ]
  change (∑ i∈Finset.range ack,layerMass v r ell i)<gG
  rw [FI.aQD _ len (fun i hi =>
    za7 (((mass_anti v r ell) hi).trans_eq hz))]
  exact (Finset.sum_le_sum_of_subset (znF (min_le_right _ _))).trans_lt
    (by simpa only [WC,zbc] using hfull)
private theorem axis_mono {b j t b' j' t' : ℕ}
    (hv :aO (⟨b,j,t⟩:Shape) ⟨b',j',t'⟩)
    (hr : (caps (retainedBox ⟨b,j,t⟩)).b≤(caps (retainedBox ⟨b',j',t'⟩)).b)
    (ho:sharedOrder ⟨b',j',t'⟩≤ sharedOrder ⟨b,j,t⟩)
    (h:ot b j t) :ot b' j' t' := by
  unfold ot CompanionTest at *
  dsimp only [ahX] at *
  refine (zQk fun i _=>dNb ?_).trans_lt h
  apply nZ.zK (Q5 hv (i+1))
  exact ⟨Nat.mul_le_mul (Nat.sub_le_sub_left ho _) (Nat.succ_le_succ hr),
    by simp [Shape.scale],by simp [Shape.scale]⟩
theorem next_axis {b j:ℕ}
    (hr : (caps (retainedBox ⟨b,j,1⟩)).b≤(caps (retainedBox ⟨b+1,j,1⟩)).b)
    (ho:sharedOrder ⟨b+1,j,1⟩≤ sharedOrder ⟨b,j,1⟩)
    (h:ot b j 1) :ot (b+1) j 1 :=
  axis_mono (b:=b) (j:=j) (t:=1) (b' := b+1) (j' := j) (t' := 1)
    ⟨Nat.le_succ b,le_rfl,le_rfl⟩ hr ho h
theorem top_two {b j:ℕ} (h:ot b j 1) :ot b j 2 :=
  axis_mono (b:=b) (j:=j) (t:=1) (b' := b) (j' := j) (t' := 2)
    ⟨le_rfl,le_rfl,Nat.le_succ 1⟩ le_rfl le_rfl h
end qpkGSFe
end
section
set_option autoImplicit true
namespace qCfmNSd
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false in
local notation "q!" x "," y=>row (b:=x) (j:=y) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lane3_1 (b:ℕ) (h0:1≤b) (h1 :b≤24) :dM ⟨b,3,1⟩:= by
  interval_cases b
  · exact q! 0x2b386f098fcf9,0xfe8598862e74e
  · exact q! 0x2a3fb008fde7f,0xf602f7d820112
  · exact q! 0x2a3f7be96b327,0xf30acee5b2e82
  · exact q! 0x2950e001aa460,0xeade308d934fe
  · exact q! 0x286bca5f4acdb,0xe2f92e506ff8e
  · exact q! 0x286bc99d81bc5,0xe01483d5a6975
  · exact q! 0x278faada15c2f,0xd87b84d79752d
  · exact q! 0x26bbfe906fb60,0xd121aa83f6433
  · exact q! 0x26bbced25d6c8,0xce4cf886bb5cd
  · exact q! 0x252befd131327,0xc31c66c207276
  · exact q! 0x246ee0f5d7758,0xbc6b84ca70f9d
  · exact q! 0x23b88e2c5f0c1,0xb5eced2982168
  · exact q! 0x2308723f7a864,0xaf9d2794616de
  · exact q! 0x225e8e7d76cac,0xa97b60671b92f
  · exact q! 0x211bb86b58b96,0xa051ad7ecc878
  · exact q! 0x20820fe98032e,0x9aa36e05383f0
  · exact q! 0x1f5da2980ad5e,0x923fbc27db451
  · exact q! 0x1ed21b29c21fa,0x8cf5efe519e2c
  · exact q! 0x1dc7f997bc766,0x853d1847439ad
  · exact q! 0x1c55786f43db0,0x7b923a22cd494
  · exact q! 0x1b01da8c7542c,0x729bc4aaecb36
  · exact q! 0x1966731221c83,0x685fcec94aefe
  · exact q! 0x17f3e46b52ae0,0x5f09358235c9d
  · exact q! 0x1573907d5c031,0x50b915a95fb96
end qCfmNSd
end
section
set_option autoImplicit true
namespace qCfmNSd
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false in
local notation "q!" x "," y=>row (b:=x) (j:=y) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lane4_1 (b:ℕ) (h0:2≤b) (h1 :b≤22) :dM ⟨b,4,1⟩:= by
  interval_cases b
  · exact q! 0x23f2d4d454f52,0xd915b326c2ad6
  · exact q! 0x23f2a85b4f331,0xd66197502d5f6
  · exact q! 0x232ef43c6c9cc,0xcf55cb59c32a8
  · exact q! 0x227279ecc09ef,0xc8826ad774311
  · exact q! 0x21bc9228ce016,0xc1db13c570e3f
  · exact q! 0x210d653f3ac2c,0xbb6fbef876609
  · exact q! 0x210d3c62db84b,0xb8d961139f55d
  · exact q! 0x1fc0b5365e37e,0xaf1c96dda2f9c
  · exact q! 0x1f22fcc214726,0xa93999aa7f2be
  · exact q! 0x1e8a5c130817a,0xa37eaea0d0d5e
  · exact q! 0x1df6a03d5bb09,0x9de37133adbc0
  · exact q! 0x1cdda0c50c232,0x959509b32d0ce
  · exact q! 0x1c5754528e7e8,0x905e1ff0ced2f
  · exact q! 0x1add3348a3879,0x86331f9ad5e70
  · exact q! 0x1a667b3df691d,0x8172a749d8461
  · exact q! 0x1916754f7e92c,0x7853329f71738
  · exact q! 0x17e16e7cce654,0x6fd90dbe535fd
  · exact q! 0x16c45bb8e7feb,0x67f163dc98757
  · exact q! 0x151757025e237,0x5d44fd4bc0384
  · exact q! 0x135478979c5c8,0x524d7663c93be
  · exact q! 0x10a71a8974db1,0x42e7da625a22c
end qCfmNSd
end
section
set_option autoImplicit true
namespace qCfmNSd
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false in
local notation "q!" x "," y=>row (b:=x) (j:=y) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lane5_1 (b:ℕ) (h0:2≤b) (h1 :b≤19) :dM ⟨b,5,1⟩:= by
  interval_cases b
  · exact q! 0x1e837603b6bc7,0xbfbe5668a6b89
  · exact q! 0x1de12258baff9,0xb9966891eb4b5
  · exact q! 0x1d4435b427000,0xb39461805e67a
  · exact q! 0x1c1a2781f3787,0xaa74bbf4783bd
  · exact q! 0x1c1a04a18d4fd,0xa81710bf0e956
  · exact q! 0x1b02f352818a0,0x9f81d9794535d
  · exact q! 0x19fd65b95c0f6,0x976c67818cc53
  · exact q! 0x19806d7717e84,0x92669ff753e9c
  · exact q! 0x1892020f72d79,0x8af6e67c4e0a5
  · exact q! 0x181fd7238ac10,0x8645e20196a09
  · exact q! 0x17459aa3dbbf8,0x7f667874b7cf4
  · exact q! 0x167750cf4edce,0x78d9b6f51bb5f
  · exact q! 0x14fb30c7bf034,0x6eae7473ae13e
  · exact q! 0x13f7224398386,0x6727e17a594c5
  · exact q! 0x1305fa62bba9d,0x601aed2009dbf
  · exact q! 0x1198d860be842,0x5693306bf3377
  · exact q! 0x10160471cbf0b,0x4cb58190d9c9f
  · exact q! 0xdc3e02e36dee,0x3ebcf72049ceb
end qCfmNSd
end
section
set_option autoImplicit true
namespace qCfmNSd
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false in
local notation "q!" x "," y=>row (b:=x) (j:=y) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lane6_1 (b:ℕ) (h0:2≤b) (h1 :b≤16) :dM ⟨b,6,1⟩:= by
  interval_cases b
  · exact q! 0x17c2f1f3578eb,0x9d18fbc4f1552
  · exact q! 0x17c2d44f999b9,0x9aef70fe6e456
  · exact q! 0x16d6e4c9d645c,0x934f2c8093c55
  · exact q! 0x15f8c14cf9bab,0x8c13dce038a29
  · exact q! 0x158e61a3dcbbb,0x8790012d658b6
  · exact q! 0x14612da26c623,0x7ea9d701e7fd2
  · exact q! 0x13a5c2b3e2a91,0x786c9fb2ba108
  · exact q! 0x12f42400337c9,0x72770dce0db02
  · exact q! 0x11fa95e645282,0x6af793cf1af40
  · exact q! 0x10c99f1d13b3d,0x6254528983b6a
  · exact q! 0xfb47c268c425,0x5a661ee76e923
  · exact q! 0xe7bb27967c02,0x51c8c3762a2a8
  · exact q! 0xcfa633f8d068,0x47b553b86488b
  · exact q! 0xb290868f10f4,0x3c0baaafc0c1b
  · exact q! 0x80400e7e4f45,0x2953fb95e98f5
theorem lane6_2 (b:ℕ) (h0:2≤b) (h1 :b≤16) :dM ⟨b,6,2⟩:= by
  interval_cases b
  · exact q! 0x17b95739436a8,0x9bf296c04b0cc
  · exact q! 0x17b91ca86a1fa,0x99cd7fd21b6e4
  · exact q! 0x16cd56c1f6ace,0x923a4bc87214c
  · exact q! 0x15ef5b6debce1,0x8b0b9bcc71a31
  · exact q! 0x1584f51dd99fa,0x868fe154b4145
  · exact q! 0x1457fb6650d4a,0x7db915885008b
  · exact q! 0x139c9df2b98a9,0x7786ddb0f8323
  · exact q! 0x12eb0d56f5607,0x719c0a1338563
  · exact q! 0x11f1b630fdd17,0x6a2a5b60a3243
  · exact q! 0x10c0f0ef848b3,0x619668fb66053
  · exact q! 0xfabfeccb7cd8,0x59b6b3605e257
  · exact q! 0xe7375b392049,0x51294083f05d5
  · exact q! 0xcf27503234c2,0x472833a47b1ac
  · exact q! 0xb2187bc7d540,0x3b9403bad66e0
  · exact q! 0x7fd84951ed07,0x28ff2bc5c53c7
end qCfmNSd
end
section
set_option autoImplicit true
namespace qCfmNSd
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false in
local notation "q!" x "," y=>row (b:=x) (j:=y) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem lane7_1 (b:ℕ) (h0:3≤b) (h1 :b≤10) :dM ⟨b,7,1⟩:= by
  interval_cases b
  · exact q! 0x10b9467b345ce,0x7510a80729654
  · exact q! 0xfcfe657bff2c,0x6db6938123192
  · exact q! 0xeb292e0afc71,0x653930c34b7b5
  · exact q! 0xdaedeb5c7d80,0x5d6a0e2efb2c4
  · exact q! 0xcc19a377d072,0x5638aed0c708a
  · exact q! 0xb81aaa931e34,0x4d34339d38095
  · exact q! 0x9e485f84dd3c,0x422a601fcf144
  · exact q! 0x7ba4910083d0,0x3410b8e179fbc
theorem lane7_2 (b:ℕ) (h0:3≤b) (h1 :b≤10) :dM ⟨b,7,2⟩:= by
  interval_cases b
  · exact q! 0x10b11d181ed04,0x743c798a469da
  · exact q! 0xfc7e2280f012,0x6ced608977a92
  · exact q! 0xeaae2e72fcc3,0x647e2d36e2320
  · exact q! 0xda74f57b1d02,0x5cb90fbef6d69
  · exact q! 0xcba4a11bea94,0x55941c4850b8c
  · exact q! 0xb7aa20ef2516,0x4c9d80c5ec70c
  · exact q! 0x9ddf571270f2,0x41a4edef5110d
  · exact q! 0x7b474d7040c7,0x33a165ff56e84
end qCfmNSd
end
section
set_option autoImplicit true
namespace qeru0sa
open qK9H6va
open fP (Ew cF xH oG
  qI Qg aAs)
open private order ao5 from ProximityPrize.SubmissionLower.CG
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def DV (q r :ℕ) :ℕ:=155-(q+r)
private theorem aq6 (q r :ℕ) :
    (Vm q (offset r)).toNat=DV q r := by
  unfold Vm offset DV
  omega
private def Ig (q r z c:ℕ) :Prop :=
  (if q<130 then (132 - q)/2 else 0)≤ r ∨
  ((r≠0∨125<q)∧152≤q+4*r+z∧252≤2*q+4*r+c)
private instance (q r z c:ℕ) :Decidable (Ig q r z c) := by
  unfold Ig
  infer_instance
private theorem selected_mono {q r z c z' c' : ℕ} (hz :z≤z') (hc:c≤ c')
    (h:Ig q r z c) :Ig q r z' c' := by
  unfold Ig at *
  exact h.elim Or.inl fun ⟨h₁,h₂,h₃⟩=>Or.inr ⟨h₁,by omega,by omega⟩
private def ajZ (q r :ℕ) (e :ait q (offset r)) :Prop :=
  56+e.val 0+3*(e.val 3 - 16)≤ iO q+order e.val+r ∧
    Ig q r (order e.val) (e.val 3)
private def ajY (q r :ℕ) (m:XN q (offset r)) :Prop :=
  order m.val<DV q r ∧ ¬ Ig q r (order m.val) (m.val 3)
private theorem aEb (q r :ℕ) (e :ait q (offset r)) (m:XN q (offset r))
    (hn:Gy q (offset r) e m≠0) :ajZ q r e∨ajY q r m:= by
  have hle (i:Fin 4) (hi:i=1∨i=2∨i=3) :m.val i≤e.val i:= by
    by_contra! hg
    have hz :=Nat.choose_eq_zero_of_lt hg
    rcases hi with rfl | rfl | rfl <;> exact hn (by simp [Gy,prefixMatrix,hz])
  have h₁:=hle 1 (by simp)
  have h₂:=hle 2 (by simp)
  have h₃:=hle 3 (by simp)
  have hmc:=m.property
  simp only [Ew,xH,cF] at hmc
  obtain ⟨_,hlo,_,hcap⟩:=hmc
  unfold offset at hlo
  obtain ⟨hd,hw⟩:=e.property
  rw [cF] at hd
  rw [oG] at hw
  have hw' := hw.trans_le (aq6 q r).le
  by_cases ha :Ig q r (order m.val) (m.val 3)
  · exact Or.inl ⟨by unfold order; omega,selected_mono (by unfold order; omega) h₃ ha⟩
  · exact Or.inr ⟨by unfold order; omega,ha⟩
private def aEG (d h r z c:ℕ) :ℕ :=
  min (d+c+1 - z) (min ((h+2 - z)/3) (d+z+r+1-(56+3*(c - 16))))
private def a2K (d z :ℕ) :ℕ:=d+z - 56
private def aHb (d r z c:ℕ) :ℕ :=
  if c≤16 then min (d+c+1 - z) (d+z+r+1 - 56)-a2K d z else 0
private def a3V (q d h r :ℕ) (z c:ℕ) (row:Bool) :ℕ :=
  if row then (if Ig q r z c then aEG d h r z c else 0)
  else (if Ig q r z c then 0 else aHb d r z c)
private abbrev ax0 (q d h r :ℕ) (row:Bool) :=
  Σ z :Fin h,Σ c:Fin (z.val/2+1),Fin (a3V q d h r z c row)
private theorem cIc (d:ℕ) {e m:Fin 4 →₀ ℕ}
    (he :e.degree=d) (hm:m.degree=d)
    (h₀:e 0=m 0) (hc:e 3=m 3) (hz :order e=order m) :e=m:= by
  rw [cF] at he hm
  unfold order at hz
  ext i
  have h₂:e 2=m 2 := by omega
  have h₁:e 1=m 1 := by omega
  fin_cases i <;> assumption
private theorem c9a (q r :ℕ)
    [DecidablePred (ajZ q r)] :
    zhP {e // ajZ q r e} ≤
      zhP (ax0 q (iO q) (DV q r) r true) := by
  let encode (e : {e // ajZ q r e}) :
      ax0 q (iO q) (DV q r) r true :=
    ⟨⟨order e.val.val,by
        have hw:=e.val.property.2
        rw [oG] at hw
        have hw' := hw.trans_le (aq6 q r).le
        unfold order
        omega⟩,
      ⟨e.val.val 3,by
        change e.val.val 3<order e.val.val/2+1
        unfold order
        omega⟩,
      ⟨e.val.val 0,by
        obtain ⟨hd,hw⟩:=e.val.property
        rw [cF] at hd
        rw [oG] at hw
        have hw' := hw.trans_le (aq6 q r).le
        obtain ⟨hreach,habove⟩:=e.property
        change e.val.val 0<a3V _ _ _ _ (order e.val.val) (e.val.val 3) true
        simp only [a3V,ite_true,ite_eq_left habove,aEG,lt_min_iff]
        unfold order at *
        omega⟩⟩
  refine zWJ encode (fun e m h => ?_)
  have hz :=congrArg (fun p:ax0 _ _ _ _ true=>p.1.val) h
  have hc:=congrArg (fun p:ax0 _ _ _ _ true=>p.2.1.val) h
  have ha :=congrArg (fun p:ax0 _ _ _ _ true=>p.2.2.val) h
  exact Subtype.ext (Subtype.ext (cIc _ e.val.property.1 m.val.property.1 ha hc hz))
private theorem cGO (q r :ℕ)
    [DecidablePred (ajY q r)] :
    zhP {m // ajY q r m} ≤
      zhP (ax0 q (iO q) (DV q r) r false) := by
  have low (m:XN q (offset r)) :
      a2K (iO q) (order m.val)≤ m.val 0:= by
    obtain ⟨hd,_,hi,_⟩:=m.property
    rw [cF] at hd
    rw [xH] at hi
    unfold a2K order
    omega
  let encode (m : {m // ajY q r m}) :
      ax0 q (iO q) (DV q r) r false :=
    ⟨⟨order m.val.val,m.property.1⟩,
      ⟨m.val.val 3,by
        change m.val.val 3<order m.val.val/2+1
        unfold order
        omega⟩,
      ⟨m.val.val 0-a2K (iO q) (order m.val.val),by
        obtain ⟨hd,hlo,_,hcap⟩:=m.val.property
        rw [cF] at hd
        rw [xH] at hlo
        unfold offset at hlo
        have habove :=m.property.2
        have hlow:=low m.val
        change _<a3V _ _ _ _ (order m.val.val) (m.val.val 3) false
        simp only [a3V,Bool.false_eq_true,ite_false,ite_eq_right habove,aHb,
          ite_eq_left hcap]
        unfold a2K order at *
        omega⟩⟩
  refine zWJ encode (fun e m h => ?_)
  have hz :order e.val.val=order m.val.val :=
    congrArg (fun p:ax0 _ _ _ _ false=>p.1.val) h
  have hc:=congrArg (fun p:ax0 _ _ _ _ false=>p.2.1.val) h
  have ha :e.val.val 0-a2K (iO q) (order e.val.val) =
      m.val.val 0-a2K (iO q) (order m.val.val) :=
    congrArg (fun p:ax0 _ _ _ _ false=>p.2.2.val) h
  rw [hz] at ha
  have he :=low e.val
  have hm:=low m.val
  rw [hz] at he
  exact Subtype.ext (Subtype.ext
    (cIc _ e.val.property.1 m.val.property.1 (by omega) hc hz))
private def aht (q r :ℕ) :ℕ :=
  let d:=iO q
  let h:=DV q r
  qI h fun z=>qI (z/2+1) fun c =>
    if Ig q r z c then aEG d h r z c else aHb d r z c
private theorem aHj (q r :ℕ)
    [DecidablePred (ajZ q r)] [DecidablePred (ajY q r)] :
    zhP {e // ajZ q r e} +
      zhP {m // ajY q r m} ≤
        aht q r := by
  refine (Nat.add_le_add (c9a q r) (cGO q r)).trans_eq ?_
  simp only [ax0,Fintype.card_sigma,Fintype.card_fin,aht,Qg]
  rw [← zfW]
  refine zUo rfl fun z _ => ?_
  rw [← zfW]
  exact zUo rfl fun c _=> by
    by_cases h:Ig q r z c <;> simp [a3V,h]
private theorem ces (q r :ℕ) :
    (Gy q (offset r)).rank≤aht q r := by
  classical
  exact (ao5 _ _ _ (aEb q r)).trans (aHj q r)
private theorem rank_zero (q r :ℕ) (hr :155≤q+r) :
    (Gy q (offset r)).rank=0:= by
  have hz :Gy q (offset r)=0:= by
    ext e
    have h:=e.property.2.trans_le (aq6 q r).le
    unfold DV at h
    omega
  rw [hz,Matrix.rank_zero]
private def chunk (q start len:ℕ) :ℕ :=
  qI len fun i=>aht q (start+i)
private theorem chunk_add (q k n m:ℕ) :
    chunk q k (n+m)=chunk q k n+chunk q (k+n) m:= by
  simp only [chunk,aAs,Finset.sum_range_add,Nat.add_assoc]
private theorem rank_le_total {q:ℕ} (hq:120≤q) :
    Oi q≤ chunk q 0 35:= by
  let f (r :ℕ) :=(Gy q (offset r)).rank
  calc
    Oi q = ∑ r∈Finset.range 35,f r := by
      unfold Oi
      rw [Fin.sum_univ_eq_sum_range (fun r=>f r)]
      symm
      refine Finset.sum_subset (znF (by decide)) ?_
      intro r _ hr
      have hn : ¬ r<35:= fun h=>hr (Finset.mem_range.mpr h)
      exact rank_zero q r (by omega)
    _≤_:= by
      simp only [chunk,aAs,zbc]
      exact zQk fun r _=>ces q r
private theorem checked (q a b c d e f g:ℕ) (hq:120≤q)
    (h₀:chunk q 0 5=a) (h₁:chunk q 5 5=b) (h₂:chunk q 10 5=c)
    (h₃:chunk q 15 5=d) (h₄:chunk q 20 5=e) (h₅:chunk q 25 5=f)
    (h₆:chunk q 30 5=g) (hb:Ni q=a+b+c+d+e+f+g) :
    Oi q≤Ni q:= by
  refine (rank_le_total hq).trans_eq ?_
  calc
    _=chunk q 0 5+chunk q 5 5+chunk q 10 5+chunk q 15 5 +
        chunk q 20 5+chunk q 25 5+chunk q 30 5:= by
      change chunk q 0 (5+5+5+5+5+5+5)= _
      simp only [chunk_add]
    _ = _:= by rw [h₀,h₁,h₂,h₃,h₄,h₅,h₆,hb]
local notation "g!" q "," a "," b "," c "," d "," e "," f "," g =>
  checked q a b c d e f g (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3500000 in
theorem proof :qK9H6va.c2 := by
  intro q h47 h131 hdlo hdhi
  have c6t:120≤q:= by
    by_contra! h
    unfold iO P6_6_1.asu at hdhi
    split at hdhi <;> (try split at hdhi) <;> omega
  clear h47 hdlo hdhi
  interval_cases q
  · exact g! 120,2856,3345,2218,1202,522,164, 25
  · exact g! 121, 2676,3010,1964,1035,428,122,14
  · exact g! 122,2332,2485,1660,881,346,88,7
  · exact g! 123,2145,2200,1450,746,275,61,3
  · exact g! 124,1771,1731,1169,617,215,40,1
  · exact g! 125,1588,1500,1000,511,164, 25,0
  · exact g! 126,1215,1100,750,401,122,14,0
  · exact g! 127,1050,920,620,321,88,7,0
  · exact g! 128,712,601,414, 226,61,3,0
  · exact g! 129,576,470,320,170,40,1,0
  · exact g! 130,220,170,120,70,21,0,0
  · exact g! 131,161,124,86,49,12,0,0
end qeru0sa
end
section
set_option autoImplicit true
namespace qmQUdWa
noncomputable section
open aR dN vS Dr Kd
open ap8 (aES aQe)
open bjA (dAn dAl gur dS7)
open MvPolynomial Filter
open scoped Pointwise
open private c7s from ProximityPrize.SubmissionLower.BI
private abbrev OV (p:Shape) :=restrictSupport GeoField (capExponents p)
private theorem bWn {p s :Shape} {D f :GeoJets} (hD:D∈OV s)
    (hf :f∈OV p) :D *f∈OV (p.plus s) := by
  apply restrictSupport_mono GeoField (s :=capExponents s+capExponents p)
  · rintro _ ⟨u,hu,v,hv,rfl⟩
    simp only [aiK.OW,Shape.plus,Finsupp.add_apply] at *
    omega
  · rw [restrictSupport_add]
    exact Submodule.mul_mem_mul hD hf
private theorem cev {J K L:Ideal GeoJets} {D:GeoJets} {p s :Shape}
    (hle :K≤L) (hcolon : ∀ f,D *f∈K↔f∈J) (hzero :D∈L)
    (hD:D∈OV s) :
    Sn L (capExponents (p.plus s))+Sn J (capExponents p) ≤
      Sn K (capExponents (p.plus s)) := by
  let S:=OV p
  let T:=OV (p.plus s)
  let V:=T.map (zvR GeoField K).toLinearMap
  let src :=(zvR GeoField J).toLinearMap.domRestrict S
  let mult:=(zvR GeoField K).toLinearMap.comp (LinearMap.mulLeft GeoField D)
  let μ:=(mult.domRestrict S).codRestrict V
    (fun f=>Submodule.mem_map.mpr ⟨D *f,bWn hD f.2,rfl⟩)
  let π:=(Ideal.Quotient.factorₐ GeoField hle).toLinearMap.domRestrict V
  have hker :z83 μ=z83 src := by
    ext f
    simp only [LinearMap.mem_ker]
    change (⟨zVv K (D *(f :GeoJets)),_⟩:V)=0 ↔
      zVv J (f :GeoJets)=0
    rw [← Subtype.val_inj,Submodule.coe_zero,z1Q,
      z1Q,hcolon]
  have hle' : LinearMap.range μ≤z83 π:= by
    rintro _ ⟨f,rfl⟩
    exact LinearMap.mem_ker.mpr
      (Ideal.Quotient.eq_zero_iff_mem.mpr (L.mul_mem_right _ hzero))
  have hπ:LinearMap.range π=T.map (zvR GeoField L).toLinearMap:= by
    rw [zyK,← Submodule.map_comp]
    rfl
  let _:zAa GeoField S:=zwB (basisRestrictSupport GeoField _)
  let _:zAa GeoField T:=zwB (basisRestrictSupport GeoField _)
  let _:zAa GeoField V:=Module.Finite.map _ _
  have hμ:=μ.finrank_range_add_finrank_ker
  have hsrc :=src.finrank_range_add_finrank_ker
  have hπ' := π.finrank_range_add_finrank_ker
  have hm:=Submodule.finrank_mono hle'
  rw [hker] at hμ
  rw [zyK] at hsrc
  rw [hπ] at hπ'
  change zsE GeoField (T.map (zvR GeoField L).toLinearMap) +
    zsE GeoField (S.map (zvR GeoField J).toLinearMap)≤zsE GeoField V
  omega
private abbrev base :Shape :=⟨3, 3,1⟩
private theorem cap_limit (sh:Bool→Shape) (hs : ∀ i,ChamberBox (sh i))
    (J:Ideal GeoJets) (i:Bool) (used :List Bool) (hi:i∉used) (hu:used.Nodup)
    (hd:dimension J≤used.length) :
    ∀ᶠ a in atTop,
      uU used (fun a=>(Sn J (capExponents (ku sh a)) :ℚ)) a =
        BE (capCoeff J used.length) (used.map sh) (sh i) := by
  have h:=c7s aKr.proof bzz.proof aKs.proof
    bzA.proof ap8.proof sh J i used hs hi hu hd
  have he :lO (Fd sh) (HW sh J) =
      fun a=>(Sn J (capExponents (ku sh a)) :ℚ) := by
    funext a
    rw [(aKs.proof sh J).2,bzz.proof sh hs a]
  rwa [he] at h
theorem gr7 {T:Ideal GeoJets} (hd:dimension T=1) {s :Shape}
    (hb:s.j≤ s.b) (ht:3*s.t≤ s.j) {D:GeoJets}
    (hD:VE s D) (hreg:IsLeftRegular (zVv T D)) :
    tW (cut T D) []≤tW T [s] := by
  classical
  let sh:Bool→Shape := fun | false=>base | true=>base.plus s
  have hs : ∀ i,ChamberBox (sh i) := by
    intro i
    cases i
    · change ChamberBox base
      exact ⟨by decide,by decide,by decide⟩
    · change ChamberBox (base.plus s)
      exact ⟨Nat.add_le_add_left hb _,by change 3*(1+s.t)≤3+s.j; omega,by
        change 0<1+s.t; omega⟩
  let J:=cut T D
  let J₂:=cut T (D^2)
  have hJ:dimension J≤0:= by
    simpa [J,hd] using aCR hreg
  have hle :J₂≤J:=sup_le le_sup_left (Ideal.span_le.mpr
    (Set.singleton_subset_iff.mpr (zs0
      (Ideal.mem_span_singleton.mpr ⟨D,pow_two D⟩))))
  have h₀:=cap_limit sh hs T true [false] (by simp) (by simp) (by simp [hd])
  have h₁:=cap_limit sh hs T false [true] (by simp) (by simp) (by simp [hd])
  have hJ₀:=cap_limit sh hs J false [] (by simp) (by simp) hJ
  have hshift (i:Bool) :Tendsto (fun a :Bool→ℕ=>a+step i) atTop atTop :=
    tendsto_atTop_mono (fun _ _=>Nat.le_add_right _ _) tendsto_id
  suffices h : ∀ᶠ _a in (atTop:Filter (Bool→ℕ)),tW J []≤tW T [s] from
    h.exists.choose_spec
  filter_upwards [h₀,h₁,(hshift false).eventually hJ₀,(hshift true).eventually hJ₀] with a f g j₀ j₁
  let p:=ku sh (a+step false)
  have hshape :ku sh (a+step true)=p.plus s := by
    simp only [p,aES,aQe]
    cases ku sh a
    cases s
    simp [sh,base,Shape.plus,Nat.add_assoc]
  have hA:=cev (p:=p) (s :=s) (show T≤J₂ from le_sup_left)
    (gur T D hreg) (zs0 (z5J _))
    (show D^2∈OV s from dAl hD)
  have hB:=cev (p:=p) (s :=s) hle (dS7 T D hreg)
    (zs0 (z5J _)) (show D∈OV s from dAn hD)
  have hA' : (Sn J₂ (capExponents (p.plus s)) :ℚ)+Sn T (capExponents p)
      ≤ Sn T (capExponents (p.plus s)) := by exact_mod_cast hA
  have hB' : (Sn J (capExponents (p.plus s)) :ℚ)+Sn J (capExponents p)
      ≤ Sn J₂ (capExponents (p.plus s)) := by exact_mod_cast hB
  simp only [uU,List.length_cons,List.length_nil,zbc,List.map_cons,
    List.map_nil,BE,hshape] at f g j₀ j₁
  have hcomm: (base.plus s).plus base=base.plus (base.plus s) := by
    cases s
    simp [Shape.plus,Nat.add_left_comm,Nat.add_comm]
  change _=capCoeff T 1 ((base.plus s).plus base) - capCoeff T 1 (base.plus s) at f
  change _=capCoeff T 1 (base.plus (base.plus s)) - capCoeff T 1 base at g
  rw [hcomm] at f
  change _=capCoeff J 0 base at j₀ j₁
  change capCoeff J 0 base/(2 :ℚ)^0 ≤
    (capCoeff T 1 (base.plus s) - capCoeff T 1 base)/(2 :ℚ)^1
  norm_num only [pow_zero,pow_one,div_one]
  linarith
end
end qmQUdWa
end
section
set_option autoImplicit true
namespace qmQUdWa
noncomputable section
open P6_6 P6_6_7 q8NBBre
open aR (shape aO extend embed)
open dN (bC j8 AX Ch)
open BO (Ue bfW)
open agL (BV a4B a4A bft)
open vS (JV bTT)
open Dr (tW dimension bHn aPQ aCR
  AN oF btI eMn bge)
open lB (bF Tn)
open private active_spec curve_geometry from ProximityPrize.SubmissionLower.ZwiFoca
open private b0H from ProximityPrize.SubmissionLower.BE
open private literal_fits from ProximityPrize.SubmissionLower.ZIBb1mb
open private physical_chamber join_chamber from ProximityPrize.SubmissionLower.ZOrwy2c
open private eMr from ProximityPrize.SubmissionLower.E4
private theorem components :Dr.c3 :=
  bzB.of_children bar.proof
    (aRS.of_children cyo.proof cyp.proof)
theorem proof :q8NBBre.c3:= by
  classical
  intro C R G ell cs hp assigned A B hB a _ hproper horder
  let D:=BV a (A.polynomial B)
  let s :=commonBody C R ell cs
  have hR:aO (shape R) s := by
    have hfirst:aO (shape R) (firstBody C R cs) := by
      cases cs with
      | union l=>exact literal_fits hp.guard.2.2
      | own i=>exact ⟨le_max_left _ _,le_rfl,le_rfl⟩
    exact P6_6_7_3.cDD hfirst ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _⟩
  have hs :bF s := by
    apply join_chamber _ (physical_chamber _ _)
    cases cs with
    | union l=>exact physical_chamber _ _
    | own i=>exact Tn R
  have hD:=bHn (a4B a (a4B (A.first B.1) hR))
  obtain ⟨hT,hdim,_,_,_⟩:=curve_geometry hp A hB
  let _:=hT
  have hd:dimension B.2=1 := by
    have h:=(b0H B.2).symm.trans hdim
    exact_mod_cast h
  let J:=AX B.2 D
  have hreg:=aPQ hT hproper
  have hJ:dimension J=0:=za7 (by simpa [J,AX,hd] using aCR hreg)
  let M:=(A.marks B).filter (fun γ=>0<A.a4Q B γ)
  let x (γ:P6.K) :=JV (extend (C.s γ))
  let P (γ:P6.K) :=oF (x γ)
  have hmark {γ:P6.K} (hγ:γ∈A.marks B) :B.2≤P γ∧γ∈C.Δ:= by
    obtain ⟨ha,hb⟩:=Finset.mem_filter.mp hγ
    refine ⟨?_,(active_spec ha).1⟩
    change B.2≤Ch (extend (C.s γ))
    rw [← hb]
    exact (A.valid γ ha).2.2.2
  have hmin (γ) (hγ:γ∈M) :J.IsMinimalPrime (P γ) := by
    obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hγ
    exact eMr hJ (x γ) (sup_le (hmark hm).1
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ue.mpr (bfW hj (horder γ hm)))))
  have hinj:Set.InjOn P (M:Set P6.K) := by
    intro γ hγ δ hδ h
    exact C.messages.distinct (hmark (Finset.mem_filter.mp hγ).1).2 (hmark (Finset.mem_filter.mp hδ).1).2
      (Polynomial.map_injective embed embed.injective (bTT (btI h)))
  calc
    _ = ∑ γ∈M,(A.a4Q B γ:ℚ) := by
      simp only [M,Finset.sum_filter]
      apply zUo rfl
      intro γ _
      split_ifs with hj
      · rfl
      · have hz :A.a4Q B γ=0:= by omega
        simp [hz]
    _ ≤ ∑ γ∈M,(AN J (P γ) :ℚ)*tW (P γ) [] := by
      apply zQk
      intro γ hγ
      have hm:=(Finset.mem_filter.mp hγ).1
      have hlt:B.2<P γ:=lt_of_le_of_ne (hmark hm).1 fun h=> by
        rw [h,eMn] at hd
        exact Nat.zero_ne_one hd
      rw [bge,mul_one]
      let _:=(hmin γ hγ).isPrime
      exact_mod_cast evJ hT hlt (hmin γ hγ)
        (bRn.gK5 (bC D) (P γ) (A.a4Q B γ) (fun b hb=> by
          change BV b (MvPolynomial.map j8 D)∈Ch (extend (C.s γ))
          rw [← bft]
          exact Ue.mpr (a4A hb (horder γ hm))))
    _ = ∑ U∈M.image P,(AN J U:ℚ)*tW U [] :=
      (Finset.sum_image (f := fun U=>(AN J U:ℚ)*tW U [])
        (fun _ hγ _ hδ h=>hinj hγ hδ h)).symm
    _≤tW J [] :=components J [] (by simp) (by simp [hJ]) _ (by
      intro U hU
      obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hU
      exact hmin γ hγ)
    _≤_:=gr7 hd hs.1 hs.2 hD hreg
end
end qmQUdWa
end
