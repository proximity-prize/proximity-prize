import ProximityPrize.SubmissionLower.HighBanks82190

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighTerminal82190

open Finset
open P3 (HighBand)
open P3_7 (Bank Test tested debit grades terminal threshold seedThreshold)
open P3_7_4 (BlockChecks)
open K1_14 (Shape shapeSum triangle slots)
open HighBanks82190 (adjusted count start)
open private slots_anti from ProximityPrize.SubmissionLower.UpperBranch6

private def weighted (c f : ℕ → ℕ) (g : ℕ) : ℕ :=
  (∑ a ∈ range g, (c a - c (a+1)) * f a) + c g * f g

private theorem total_weight (c : ℕ → ℕ) (hc : Antitone c) (g : ℕ) :
    (∑ a ∈ range g, (c a - c (a+1))) + c g = c 0 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [sum_range_succ]
    have hs : c (g+1) ≤ c g := hc (Nat.le_succ g)
    change _ + c (g+1) = c 0
    omega

private theorem perturb (c f f' : ℕ → ℕ) (g d : ℕ) (hc : Antitone c)
    (he : ∀ a, f a ≤ f' a + d) :
    weighted c f g ≤ weighted c f' g + c 0 * d := by
  calc
    weighted c f g ≤ weighted c (fun a => f' a + d) g :=
      Nat.add_le_add (sum_le_sum fun a _ => Nat.mul_le_mul_left _ (he a))
        (Nat.mul_le_mul_left _ (he g))
    _ = weighted c f' g + c 0 * d := by
      simp only [weighted, Nat.mul_add, sum_add_distrib, ← sum_mul]
      rw [← total_weight c hc g, Nat.add_mul]
      omega

private def width (A h : ℕ) (s : Shape) (q j a : ℕ) :=
  s.m*A + j - q*(131071-h) - 2*h*(j+a)

private def entry (A h : ℕ) (s : Shape) (E v q j : ℕ) :=
  weighted (fun a => slots s.U (a*v)) (width A h s q j) ((q-j)/E)

def gain (h : ℕ) (s : Shape) (E v : ℕ) :=
  shapeSum s (entry 179954 h s E v)

private theorem joint_upper (h : ℕ) (s : Shape) (E v : ℕ) :
    P3_7.jointGain h s E v ≤ gain h s E v + triangle s.U * (count s*(29*s.m)) := by
  have bound (q j : ℕ) :
      entry 179983 h s E v q j ≤ entry 179954 h s E v q j + triangle s.U*(29*s.m) := by
    let c := fun a => slots s.U (a*v)
    have hc : Antitone c := fun _ _ hab => slots_anti s.U (Nat.mul_le_mul_right v hab)
    have hzero : c 0 = triangle s.U := by simp [c, slots]
    rw [← hzero]
    apply perturb _ _ _ _ _ hc
    intro a
    unfold width
    have hcut : s.m*179983 = s.m*179954 + 29*s.m := by ring
    omega
  have le : shapeSum s (entry 179983 h s E v) ≤
      shapeSum s (fun q j => entry 179954 h s E v q j + triangle s.U*(29*s.m)) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => bound q j
  rw [HighBanks82190.sum_shift] at le
  change shapeSum s (entry 179983 h s E v) ≤ shapeSum s (entry 179954 h s E v) + _
  simpa only [Nat.mul_left_comm] using le

private theorem from_blocks {t : Bank} {lo h E v : ℕ}
    (hl : lo ≤ h) (hh : h < 131071) (hj : t.shape.J ≤ 131071-(lo+1))
    (he : 0 < E) (c : BlockChecks t.shape (adjusted t).nodeRows t.poleMoment lo E v) :
    debit h t < gain h t.shape E v := by
  let a := adjusted t
  change BlockChecks a.shape a.nodeRows a.poleMoment lo E v at c
  unfold BlockChecks at c
  have hj' : a.shape.J ≤ 131071-(lo+1) := hj
  rw [P3_7_4.blockSurplus_eq a lo E v (by omega) (by omega) he,
    P3_7_4.blockSurplus_eq a (lo+1) E v (by omega) hj' he] at c
  obtain ⟨hp, hr⟩ := c
  have positive := P3_7_4.strict_of_first_difference (b := a) (E := E) (v := v)
    hl hh (by omega) (by omega)
  have eq : debit h a = debit h t + triangle t.shape.U*(count t.shape*(29*t.shape.m)) := by
    unfold a P3_7.debit P1_7.debit adjusted
    dsimp only
    ring
  rw [eq] at positive
  change _ < P3_7.jointGain h t.shape E v at positive
  have upper := joint_upper h t.shape E v
  omega


open private checks_at_grade from ProximityPrize.SubmissionLower.GoldBranch7N4

private def Checks (b : HighBand) (x : Test b) : Prop :=
  let t := tested b x
  BlockChecks t.shape (adjusted t).nodeRows t.poleMoment (start b) (threshold b x) (seedThreshold b x)

private theorem grade_checks (b : HighBand) (hz : Checks b none)
    (hs : P3_7_4.GradeChecks (adjusted (terminal b)) (start b) 1 (grades b)) (x : Test b) :
    Checks b x := by
  cases x with
  | none => exact hz
  | some i => exact checks_at_grade _ _ _ _ hs i

set_option quotPrecheck false
local notation "last!" l "," r => P3_7_4.Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => P3_7_4.Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => P3_7_4.certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)

namespace H2274
local notation "S" u => (⟨6600,9172,1952,u⟩ : Shape)
local notation "N" => 8507928580194120
local notation "P" => 191486597252812
private theorem r0 : BlockChecks (S 211000) N P 2349 23 0 :=
  block! 2351,15,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34d521c8a9f8fa3da39db4fe0,0x34dae14876b413af447a1e740, (last! 0x24d29d05eb1965459b2bcd40,0x2477d774bec2968e58b35ba0))
private theorem r1 : BlockChecks (S 162873) N P 2349 1 359 :=
  block! 2406,1,0x20dc23658482fa3085e37b900,0x20dc2495d8a962cbba20eaf00,(more! 0x1ef2572279006d9e3b588a2c0,0x1ef5c5eb779fd133db50c27a0, (more! 0x1e9d4b8ab58f4bd0342d25e0,0x1e6722cc1964c75f504ccd40, (last! 0x2bfca8e35b60801aff40,0x22b3d2542d7fdaa30320)))
private theorem r2 : BlockChecks (S 164297) N P 2349 2 354 :=
  block! 2417,1,0x216fc74ccb6627b0b4fb9f100,0x216fc87fc8b24debac7e6d700,(more! 0x1f823c8a0a1d93306dc8cfe20,0x1f85ba832406165b4dab90160, (more! 0x1ed8a692c8e5c2bcacddb840,0x1ea19edda09056084aa98ec0, (last! 0xd66c01066258a9da3280,0xbc361aaf4d6fca00a0c0)))
private theorem r3 : BlockChecks (S 166033) N P 2349 3 349 :=
  block! 2428,2,0x22258113650376e7a25d6ed00,0x22258249a0b2d6489aa0acb00,(more! 0x20324efc523a5632b84dc1760,0x2035dfbf9578cfa8e6526ea00, (more! 0x1f31d8b566395f40d8cc1a40,0x1ef9bfd6ded9c0c64aebd640, (last! 0x254a8c268a9e4d7c5b620,0x222d204f3008c84b4e2e0)))
private theorem r4 : BlockChecks (S 167408) N P 2349 4 343 :=
  block! 2441,2,0x22b6cb7b0bf010ac4eabbb800,0x22b6ccb3d954f55a6b372bf00,(more! 0x20c0b7bdb27f86ddc2fb77640,0x20c45777f821ffd8921649b20, (more! 0x1f5d6af565d08b67fe7ef7c0,0x1f247f9129b93fc012e63720, (last! 0x4b41ba2c7d412ff0409a0,0x4686354b1e9be8848b3c0)))
private theorem r5 : BlockChecks (S 169216) N P 2349 5 337 :=
  block! 2455,3,0x2377a94e6a5f59673a1386000,0x2377aa8a98981d95658f7d700,(more! 0x217bfb3115f55f0db93969080,0x217faeead57a296bced1f8920, (more! 0x1fb384b65668972d7f470020,0x1f7979f321d10de6ff468880, (last! 0x83c9b105750b30e2ed7a0,0x7d4566d873b3b4bb1b3c0)))
private theorem r6 : BlockChecks (S 171591) N P 2349 6 331 :=
  block! 2471,3,0x247828800bcd3630b48ce2c00,0x247829c0aa10f7e41eb41a400,(more! 0x2273410055276f02a2e115560,0x22770f74bd0edd2922e7fe8e0, (more! 0x204269c91a54dc0a4370d540,0x2006d6e51f5e3154a37d0da0, (last! 0xd1947e2d5ed5b84d4bfe0,0xc92e0358ce18ee7775620)))
private theorem r7 : BlockChecks (S 173880) N P 2349 7 324 :=
  block! 2489,4,0x2572bf85e298eafb30c21cc00,0x2572c0cac7c4aa9d9df794b00,(more! 0x23657bf7de900b0f2a2312660,0x236964926c07228b0699da2c0, (more! 0x20c25e54924e29e759d60de0,0x208548dfe8d370d8e3f36120, (last! 0x12ba24b8f891da40b22ec0,0x121927c290301ff9406340)))
private theorem r8 : BlockChecks (S 177154) N P 2349 8 317 :=
  block! 2511,5,0x26def08cb5262a8505e417f00,0x26def1d7b86292fbcd962e400,(more! 0x24c2c2671856b5c963ec28a60,0x24c6d12f4053d0ff6f9b50900, (more! 0x21aa6236c18a8e2ee5bdf1c0,0x216b0bc3f4ab8afbf7b895a0, (last! 0x197d203bede2f4c3710400,0x18c1ec71bb35a069ea01e0)))
private theorem r9 : BlockChecks (S 180959) N P 2349 9 309 :=
  block! 2538,6,0x288eba8189278f003799dd000,0x288ebbd3a8736b23826b3f000,(more! 0x266008e9ca62cb0ac1def9620,0x26644518e6a16ba3534f0c2c0, (more! 0x22cbb5550877385d8e43a8e0,0x2289a6e83093a64acd4e9720, (last! 0x204560b70516613a6d5a40,0x1f74be50e42921debd4240)))
private theorem r10 : BlockChecks (S 187112) N P 2349 10 301 :=
  block! 2574,7,0x2b5c5f01ebc6baaaab1568400,0x2b5c605f8a42c99df25f4d300,(more! 0x290a575fe5c8f8cda8e6c7d00,0x290edf45d48007aeb732f2700, (more! 0x24fa5428dbd7696ca35064a0,0x24b3b0dcbbc1881c400a3d00, (last! 0x277e7a676f2852f974c8c0,0x2696579a2712dbcf6e68e0)))
private theorem r11 : BlockChecks (S 195637) N P 2349 11 291 :=
  block! 2625,9,0x2f664b71624fa2a1c9999c300,0x2f664cdeee9785a68b6fedd00,(more! 0x2cddeaf8f17474fe18cdb2540,0x2ce2e0590df48c87476b9c240, (more! 0x285adac177e1fcd10c9864a0,0x280d8c0535a5a131a48a6920, (last! 0x2c91b6bdc3791d72699520,0x2b92f50afa6e6e0dafc380)))
private theorem r12 : BlockChecks (S 211000) N P 2349 12 278 :=
  block! 2711,12,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34284fa2a22f3672441473f20,0x342e17576e0c34c69eea93f60, (more! 0x2f68dd0690bcc2a796fc49e0,0x2f0eb824566a289b1bea1f00, (last! 0x2f7539bbe51adb0aa300a0,0x2e507a2b4dceda1ddc6c60)))
private theorem r13 : BlockChecks (S 211000) N P 2349 13 263 :=
  block! 2658,10,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x343e0758ab1b181ab04829d60,0x3443cdf3d476941417eb049e0, (more! 0x2e23c393dcf57251905c9e80,0x2dc95377539e212b04393920, (last! 0x195bb8d8313b4757a7aa60,0x1893d3042fbce2d0a05dc0)))
private theorem r14 : BlockChecks (S 211000) N P 2349 14 245 :=
  block! 2608,8,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x345164585e8264e052c5d4500,0x34572a0a35855b956dcfdfe00, (more! 0x2cfce545376dd73fb5b75e60,0x2ca22e03082aaf5b37f79e40, (last! 0xa1ef6212758d4f0fd8b00,0x9acc062776b18436629e0)))
private theorem r15 : BlockChecks (S 211000) N P 2349 15 226 :=
  block! 2564,7,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x3464994e49a68c4f60c3e77a0,0x346a5df5818b40796647e63a0, (more! 0x2bd238ed3a6b022091b780e0,0x2b774ae22d9a886a441788a0, (last! 0x221aab3382e8ef0b46ce0,0x1f6f7e1258a0e3d522840)))
private theorem r16 : BlockChecks (S 211000) N P 2349 16 203 :=
  block! 2526,5,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x3474d469be978d67e79746080,0x347a985e61ee1fcd77bf93ca0, (more! 0x2ad02c267ddcd3a43a8a5ca0,0x2a75213d1d40b14b6c03f1a0, (last! 0x8ec002b9108112789c0,0x6323177134c73b599c0)))
private theorem r17 : BlockChecks (S 211000) N P 2349 17 178 :=
  block! 2492,4,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x348424d088100a92855c1d000,0x3489e81d3d4e677b2e25a6880, (more! 0x29db00ed48e397c6c547c1e0,0x297ffdc2599fc466ebd7cfc0, (last! 0,0)))
private theorem r18 : BlockChecks (S 211000) N P 2349 18 151 :=
  block! 2462,3,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34928d406de1a2b6a4d879bc0,0x34984ff40cd45b29fa2f90ec0, (more! 0x28f482a498d175ffcceda620,0x2899890aa5d448eaee5615c0, (last! 0,0)))
private theorem r19 : BlockChecks (S 211000) N P 2349 19 122 :=
  block! 2435,2,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34a0148d9fb45ca96a31b3b20,0x34a5d6ba3e1607f913f4193c0, (more! 0x281c3e93dd17ede1472f5b80,0x27c14d6e22d2a585f4aa7d00, (last! 0,0)))
private theorem r20 : BlockChecks (S 211000) N P 2349 20 90 :=
  block! 2411,1,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34ac2699daa00cb1d5c298f40,0x34b1e871c93772f4706ae5000, (more! 0x275aed5074b469243e176c40,0x2700016f5966a7f968b97ec0, (last! 0,0)))
private theorem r21 : BlockChecks (S 211000) N P 2349 21 56 :=
  block! 2389,16,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34b7827e23be9cf3e3942eea0,0x34bd44152045c1f56012e3c80, (last! 0x26a51e7f3f0ed23b79101560,0x264a36aa8f06744dadaeeec0))
private theorem r22 : BlockChecks (S 211000) N P 2349 22 20 :=
  block! 2369,16,0x3721c368b2bd475cf717c4c00,0x3721c4f2f3a9d1b14c43acb00,(more! 0x34c2304a76f311700bc143ce0,0x34c7f1b5dfa473c7a28978700, (last! 0x25fa47306a2390405eff0600,0x259f6214cdad9c757fe0c520))
theorem checks : ∀ x : Test .h2274, Checks .h2274 x :=
  grade_checks .h2274 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, trivial⟩
end H2274

namespace H2294
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 12669451138057196
local notation "P" => 327528160189452
private theorem r0 : BlockChecks (S 234728) N P 2369 22 0 :=
  block! 2696,16,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x51e829f1a9391c2553ab75c60,0x51f2a6f03879a4f7d3ea3c440, (more! 0x108dcca74cc60059ccd0c2300,0x108abdee12143a5b882c8df60, (last! 0x3264180601a4b37e14981d40,0x31ef67990043558d195f13e0)))
private theorem r1 : BlockChecks (S 179424) N P 2369 1 331 :=
  block! 2761,3,0x3b63140d448b25fafd2e2ce80,0x3b63164ab3f76de8f3b287580,(more! 0x2ee59d014241a16c640e1dc20,0x2eebb67ae927129f0da775d60, (more! 0x9a783c4f7740d221767ae980,0x9a60b6a5e8db9424bbba5460, (more! 0x2d4a6fd9f5f1f611acd20fc0,0x2d02b21fd9b476468abf9d80, (last! 0x15a9ab6b10c2ebf1ef3860,0x14a6a8a42b236b2c3c0c60))))
private theorem r2 : BlockChecks (S 180915) N P 2369 2 326 :=
  block! 2773,3,0x3c60a0101a55649a77971bb00,0x3c60a2524da456bfc5fdaa700,(more! 0x2fb6fc0d459bd15298e51a900,0x2fbd2ffe3ed46241d9e0e86c0, (more! 0x9d0c44b2998cc1da22bad940,0x9cf3de48bb3a528077ba7820, (more! 0x2d6ee2af44df1d84bb1f5860,0x2d26a1dcb5436c89083cf280, (last! 0x20057d737de852a900c120,0x1ec4310679cc5def623ec0))))
private theorem r3 : BlockChecks (S 182775) N P 2369 3 321 :=
  block! 2788,4,0x3d9fdc4ffee88dbf42eb2fa00,0x3d9fde9824016433e8cdcc200,(more! 0x30bc353d4f7f75f79d7852560,0x30c28a7b98693fbdc1787ada0, (more! 0xa04d909da42739afeea7a8e0,0xa0342eca6a1056f7df01f100, (more! 0x2dc0e4a7b2cab7f50c89f4c0,0x2d77d19ce1e5dae08aee7520, (last! 0x2d2aceba06a01bbf95d640,0x2ba9081861bd5f99823400))))
private theorem r4 : BlockChecks (S 185099) N P 2369 4 316 :=
  block! 2804,4,0x3f33519b42cfebc11d0b24d00,0x3f3353ead553ac4650b81a100,(more! 0x3203ee2b8f65555e41e971200,0x320a6d7c0687840c5c2e0a900, (more! 0xa46d10a05188eb7f6199ffc0,0xa45290776a65750521087e00, (more! 0x2e4d76eb2b78a88a230049c0,0x2e032b711c51be3647a55740, (last! 0x3d69586da42f9fc0cd4600,0x3ba5b7d1a5a7f02359a940))))
private theorem r5 : BlockChecks (S 187083) N P 2369 5 310 :=
  block! 2822,5,0x408fc83144356605fbbd21d00,0x408fca872df6e6dfd0ff7b100,(more! 0x33217820d099740b9243f4400,0x33281be26fda4dc03be6c43a0, (more! 0xa7fdc5e26860f9d3ed36e520,0xa7e23a28d0ce26002fa93080, (more! 0x2e9a31307d1cd5fa6f919340,0x2e4ee82256c7d27a538c12c0, (last! 0x4e8990009a8e7d1c380f60,0x4c8f4787e6824a88a1c200))))
private theorem r6 : BlockChecks (S 189769) N P 2369 6 304 :=
  block! 2843,6,0x426d752d74b86f5d432df4a80,0x426d778bf411ed1d48df75080,(more! 0x34a4dfaec14b1ed1c7c27fa00,0x34abb5589bcd4c5dd4281d8a0, (more! 0xace3be4cffcb67b33ff3d4c0,0xacc6f1f2a5cc24df57e86540, (more! 0x2f44dc7b0d66b7051ef35920,0x2ef7f5afe5a2a3f6f2bdb820, (last! 0x6264bd13a2cc6db747e060,0x60345275e1dd95a3a44b60))))
private theorem r7 : BlockChecks (S 192397) N P 2369 7 297 :=
  block! 2866,7,0x4447679baf602e3ff35e05d80,0x44476a0294dd882e02b4e3f80,(more! 0x3626297f6fa51f74231025720,0x362d30cb46b131b64d6892960, (more! 0xb1c2d860a6b5cadb37111ba0,0xb1a4cb6d24b280adfb919f20, (more! 0x2fdc66228d86769ae79d7140,0x2f8dd9141c491477d7feba00, (last! 0x75c1157fb6a1991fb0bd00,0x736741b84e2d50eef46a20))))
private theorem r8 : BlockChecks (S 196316) N P 2369 8 290 :=
  block! 2895,8,0x47164700a7f0140428d201180,0x4716497413d1dbcaf0a059c80,(more! 0x3868471c4c6d887920af5c8c0,0x386f99983b3ec28db8cc46ea0, (more! 0xb9299c64375b37534ad6f1a0,0xb909e9b013f854ad9b3d19c0, (more! 0x312c45a9b1cf29906ee55e20,0x30dae60f909c1a47e097cbe0, (last! 0x8b4e0c7d63c455e8d14060,0x88c88b04c990b979c57100))))
private theorem r9 : BlockChecks (S 201102) N P 2369 9 282 :=
  block! 2932,9,0x4a97d5760287081f215264d00,0x4a97d7f8ba26ce9108b8db600,(more! 0x3b3754439657508b7edf96fa0,0x3b3f04bbffed896533ca0cfc0, (more! 0xc26d0f5d3bcc0acefb3af880,0xc24b6d119e4841a934362da0, (more! 0x32fcc0aad14c86c6460726e0,0x32a7a935252586a40df61540, (last! 0x9f22d325859069bea4a760,0x9c77af5f2c832633c9f640))))
private theorem r10 : BlockChecks (S 209391) N P 2369 10 274 :=
  block! 2983,11,0x50dd7257d9b7171652f845400,0x50dd74f50f1de3c8c7429e400,(more! 0x4032a6326a18a355352abca40,0x403afeacec31aded81d2830c0, (more! 0xd3048ddbdab3829bcb0157c0,0xd2dfd5e33cf31a7f563e92c0, (more! 0x36f3d88049f95d64f9eee080,0x3697b5bc0251874079ec8540, (last! 0xb6497a37c985eeeaa1d580,0xb360c2bb831be1eed89760))))
private theorem r11 : BlockChecks (S 221352) N P 2369 11 263 :=
  block! 3060,14,0x5a5c90f5f77228bc86f9ea080,0x5a5c93b966ee24d04bfdabf80,(more! 0x47b33535ae2448ff0e4d63480,0x47bc8cb166c26d7b4542b0dc0, (more! 0xec3b322307b881167bacbca0,0xec121bcc92e0cad4f5d62be0, (more! 0x3d91dcd49a1b6f12a6624680,0x3d2ab1b3acefe15bd5749ba0, (last! 0xc9c6279ec10a5fcbbf2780,0xc686886eb58781e1a25fa0))))
private theorem r12 : BlockChecks (S 234728) N P 2369 12 250 :=
  block! 3094,15,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x509def810715348e1282afc80,0x50a874af4cda87ab4a61d9120, (more! 0x10a0d402a2fe9cfbe7d5c2180,0x109defe1016f239afc27b6680, (more! 0x450d88e190b39e1b6e114d00,0x44990337defcc3d6e54fc300, (last! 0xba4e23eed141f6583ad860,0xb6f56f9eab4e878c9e3c20))))
private theorem r13 : BlockChecks (S 234728) N P 2369 13 234 :=
  block! 3027,13,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x50c92f838c0291cd7533e57a0,0x50d3b424a9262c98da675ac20, (more! 0x109ec5713a2ea8291f84230a0,0x109bd75135b0743dc3de58f20, (more! 0x42c4d6db7a1eccf2668507a0,0x42501e96647beecca6e9ed80, (last! 0x70325b862a03fbd2d32040,0x6db4fac6fee403f7b74360))))
private theorem r14 : BlockChecks (S 234728) N P 2369 14 215 :=
  block! 2969,10,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x50efa4fff86d9bbb7e1bf6cc0,0x50fa292eb401a917e6d9553a0, (more! 0x109d173972a067036c6551160,0x109a21270cce0cfaa4a8772a0, (more! 0x40af382d9a6e5f88baff7e80,0x403a3422bfcc583fb879cae0, (last! 0x38aebd46a64161511d2e20,0x37035387c0e4e5da4d4600))))
private theorem r15 : BlockChecks (S 234728) N P 2369 15 194 :=
  block! 2919,9,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x51142831809f4c17c38d8dde0,0x511eabc93a742afbbae35eee0, (more! 0x109b4dfa3303149bb126687c0,0x1098514896ff3c4b31ca18d60, (more! 0x3ea750ca93357d4ddbb564c0,0x3e31fed7625956ac7b4b1ba0, (last! 0x14ede39d9882974efc2220,0x1403bdb76668a285a7ae80))))
private theorem r16 : BlockChecks (S 234728) N P 2369 16 171 :=
  block! 2875,7,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x5136a5f3ce3e8b786f23abda0,0x514128da3ec6c61d4f32fcc60, (more! 0x10997b9c91a256fa5fd91d620,0x109679965d0d878b94eebbe60, (more! 0x3cae223b88a6bf124250a740,0x3c3897950881c17b570e0c80, (last! 0x3e4347b89a5800b42d400,0x39327a4b50685be917c80))))
private theorem r17 : BlockChecks (S 234728) N P 2369 17 145 :=
  block! 2837,6,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x515542ff7854fed0bf9d3b1e0,0x515fc5543041059d98cff50e0, (more! 0x109812715544f3e73802cd380,0x10950d04ee447e2c194194d60, (more! 0x3ade7855b25bdb9854d39740,0x3a68dece6a80dffb0e32a9e0, (last! 0x6ae8c2ba6a468c97d20,0x3f3a536152051a2ce80))))
private theorem r18 : BlockChecks (S 234728) N P 2369 18 117 :=
  block! 2802,4,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x51722c04669115262940895e0,0x517cadb714b3993f140f06c60, (more! 0x1096afde553ef474f80b22200,0x1093a842d84cbb5550114f8a0, (more! 0x39263ba13ca718c3c9e65a80,0x38b0cc701fe6885d47720340, (last! 0,0))))
private theorem r19 : BlockChecks (S 234728) N P 2369 19 86 :=
  block! 2771,3,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x518bd43dbdd7ef35634178a20,0x5196556ee5424e75181292d80, (more! 0x1095b65e84e213f177b8b46c0,0x1092ae6df79efff42dabe1280, (more! 0x379ab912d9e0194cc49e0480,0x372557364b83ea16499c5100, (last! 0,0))))
private theorem r20 : BlockChecks (S 234728) N P 2369 20 53 :=
  block! 2744,2,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x51a412fedb37b42c602ce4660,0x51ae93a4c506d3493d7b36680, (more! 0x1094cd1e785d19c9809ed15c0,0x1091c5fe33f73cc724ab1c240, (more! 0x36251e1d08f348ff54774460,0x35afb7e49c08eca91f9de1e0, (last! 0,0))))
private theorem r21 : BlockChecks (S 234728) N P 2369 21 18 :=
  block! 2719,1,0x659b1e28c9f80741a06923080,0x659b2116f93da066af11c0f80,(more! 0x51baef1d0b0e469e62cfdd7e0,0x51c56f32d93d37a8eb2668a80, (more! 0x1093fb94483e6b5f88f358f00,0x1090f6623032c4c90b724f660, (more! 0x34c46d54677b63ea52bbdda0,0x344ef136b3ea1fdbb33e4b60, (last! 0,0))))
theorem checks : ∀ x : Test .h2294, Checks .h2294 x :=
  grade_checks .h2294 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, trivial⟩
end H2294

namespace H7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 52897912936
local notation "P" => 22832869
private theorem r0 : BlockChecks (S 946) N P 7773 7 0 :=
  block! 57,1,0x1e13b701fb539cfc0,0x1e13ba8c2e04e6c80,(last! 0x1e170bd72aee0e480,0x1e1713d446d33f5c0)
private theorem r1 : BlockChecks (S 886) N P 7773 1 26 :=
  block! 67,2,0x1a69ccde3a487c2c0,0x1a69d02f02c4e9080,(last! 0x1a6c14eaf40e08420,0x1a6c1c1d901a4af00)
private theorem r2 : BlockChecks (S 913) N P 7773 2 24 :=
  block! 71,2,0x1c0853a544a1c2580,0x1c08570fe34f92a00,(last! 0x1c09805f614986ba0,0x1c0987deabfc71960)
private theorem r3 : BlockChecks (S 946) N P 7773 3 22 :=
  block! 76,3,0x1e13b701fb539cfc0,0x1e13ba8c2e04e6c80,(last! 0x1e15edfeeac865a80,0x1e15f5f27d5a52500)
private theorem r4 : BlockChecks (S 946) N P 7773 4 19 :=
  block! 76,3,0x1e13b701fb539cfc0,0x1e13ba8c2e04e6c80,(last! 0x1e164d1f9c2cf9420,0x1e1655163799283a0)
private theorem r5 : BlockChecks (S 946) N P 7773 5 14 :=
  block! 67,2,0x1e13b701fb539cfc0,0x1e13ba8c2e04e6c80,(last! 0x1e15565b8c4b42100,0x1e155e4a3faae98c0)
private theorem r6 : BlockChecks (S 946) N P 7773 6 8 :=
  block! 61,1,0x1e13b701fb539cfc0,0x1e13ba8c2e04e6c80,(last! 0x1e16bd15d1e123400,0x1e16c51055c53dac0)
theorem checks : ∀ x : Test .h7773, Checks .h7773 x :=
  grade_checks .h7773 r0 ⟨r1, r2, r3, r4, r5, r6, trivial⟩
end H7773


theorem terminal_surpluses (b : HighBand) (x : Test b) {h : ℕ} (hl : start b ≤ h) (hu : h < 131071) :
    debit h (tested b x) < gain h (tested b x).shape (threshold b x) (seedThreshold b x) := by
  have hj : (terminal b).shape.J ≤ 131071-(start b+1) := by cases b <;> decide
  have hj' : (tested b x).shape.J = (terminal b).shape.J := by cases x <;> rfl
  have he : 0 < threshold b x := by cases x <;> exact Nat.succ_pos _
  apply from_blocks hl hu (hj' ▸ hj) he
  cases b with
  | h2274 => exact H2274.checks x
  | h2294 => exact H2294.checks x
  | h7773 => exact H7773.checks x

#print axioms terminal_surpluses
end HighTerminal82190
