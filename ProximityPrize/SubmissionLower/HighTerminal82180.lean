import ProximityPrize.SubmissionLower.HighBanks82180

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighTerminal82180

open Finset
open P3 (HighBand)
open P3_7 (Bank Test tested debit grades terminal threshold seedThreshold)
open P3_7_4 (BlockChecks)
open K1_14 (Shape shapeSum triangle slots)
open HighBanks82180 (adjusted count start)
open private slots_anti from ProximityPrize.SubmissionLower.UpperBranch6

private def weighted (c f : ℕ → ℕ) (g : ℕ) : ℕ :=
  (∑ a ∈ range g, (c a - c (a+1)) * f a) + c g * f g

theorem total_weight (c : ℕ → ℕ) (hc : Antitone c) (g : ℕ) :
    (∑ a ∈ range g, (c a - c (a+1))) + c g = c 0 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [sum_range_succ]
    have hs : c (g+1) ≤ c g := hc (Nat.le_succ g)
    change _ + c (g+1) = c 0
    omega

theorem perturb (c f f' : ℕ → ℕ) (g d : ℕ) (hc : Antitone c)
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
  shapeSum s (entry 179964 h s E v)

theorem joint_upper (h : ℕ) (s : Shape) (E v : ℕ) :
    P3_7.jointGain h s E v ≤ gain h s E v + triangle s.U * (count s*(19*s.m)) := by
  have bound (q j : ℕ) :
      entry 179983 h s E v q j ≤ entry 179964 h s E v q j + triangle s.U*(19*s.m) := by
    let c := fun a => slots s.U (a*v)
    have hc : Antitone c := fun _ _ hab => slots_anti s.U (Nat.mul_le_mul_right v hab)
    have hzero : c 0 = triangle s.U := by simp [c, slots]
    rw [← hzero]
    apply perturb _ _ _ _ _ hc
    intro a
    unfold width
    have hcut : s.m*179983 = s.m*179964 + 19*s.m := by ring
    omega
  have le : shapeSum s (entry 179983 h s E v) ≤
      shapeSum s (fun q j => entry 179964 h s E v q j + triangle s.U*(19*s.m)) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => bound q j
  rw [HighBanks82180.sum_shift] at le
  change shapeSum s (entry 179983 h s E v) ≤ shapeSum s (entry 179964 h s E v) + _
  simpa only [Nat.mul_left_comm] using le

theorem from_blocks {t : Bank} {lo h E v : ℕ}
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
  have eq : debit h a = debit h t + triangle t.shape.U*(count t.shape*(19*t.shape.m)) := by
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

theorem grade_checks (b : HighBand) (hz : Checks b none)
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
local notation "N" => 8506872003288120
local notation "P" => 191486597252812
private theorem r0 : BlockChecks (S 211000) N P 2323 23 0 :=
  block! 2351,16,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x342526bc2351a8ac4e0e79600,0x342b0dc2241650617b60c89a0, (last! 0x2fb32f4b738a1ca6c3012de0,0x2f55f14efdec075a087c1960))
private theorem r1 : BlockChecks (S 162873) N P 2323 1 359 :=
  block! 2406,2,0x20daf965897f2549db3381700,0x20dafa95dda58de50f70f0d00,(more! 0x1e89c0ca320faa508abcced40,0x1e8d42af37ac479228e2eeaa0, (more! 0x251008ed2ca1313cf0240fc0,0x24d8f37fc93a1e00f7bfb8c0, (last! 0x3e275061a0234a318fb00,0x39416be42704789bdb1a0)))
private theorem r2 : BlockChecks (S 164297) N P 2323 2 354 :=
  block! 2417,2,0x216e9856ce32864d05bf15f00,0x216e9989cb7eac87fd41e4500,(more! 0x1f17ca0f905e4f98965c64ee0,0x1f1b5bef4dec239006f2f4080, (more! 0x25666c7e6b74fe46accbf280,0x252e7af9330a9aa8717f5580, (last! 0x6f570fd396f6da5a0e940,0x6869d0e95028635eadb80)))
private theorem r3 : BlockChecks (S 166033) N P 2323 3 349 :=
  block! 2428,3,0x22244c02ff4df9a5439b42300,0x22244d393afd59063bde80100,(more! 0x1fc5928ab123a2c1d10d3ed40,0x1fc93813fa4549cdf996b52e0, (more! 0x25e10081dd59e4fb63a476e0,0x25a7fbcedb74e0b735b70560, (last! 0xb4d470f2c8d136954be80,0xabae0760717e19cecb7c0)))
private theorem r4 : BlockChecks (S 167408) N P 2323 4 343 :=
  block! 2441,3,0x22b5918a1e0aec37f583e3800,0x22b592c2eb6fd0e6120f53f00,(more! 0x2052258a1e0617b81c0d3e460,0x2055dad763488467c3039c640, (more! 0x2626cff400375b3c269dc140,0x25ecf2ee2aba54efa0e69ac0, (last! 0x107cc153c579b540059de0,0xfc97696e5354874189e40)))
private theorem r5 : BlockChecks (S 169216) N P 2323 5 337 :=
  block! 2455,4,0x237668e4f27b480b7e15e1000,0x23766a2120b40c39a991d8700,(more! 0x210af9d55442a17e5e7a438c0,0x210ec40b617dddd132b4108a0, (more! 0x26a0804d5711f8eb2bbf0240,0x26657a3086a916c214f9d3c0, (last! 0x16f7ec7667087ee4228fa0,0x1623386925c5e7d1b582c0)))
private theorem r6 : BlockChecks (S 171591) N P 2323 6 331 :=
  block! 2471,4,0x2476df7cee7de988eca269400,0x2476e0bd8cc1ab3c56c9a0c00,(more! 0x21ff0338e6e989bb8822dfa80,0x2202e939c34e7f92d707e23c0, (more! 0x275f9b24de1bcf388704b300,0x2722ff53142f283071555560, (last! 0x1ed922d881a36d22fdca80,0x1de2dd62149374c4afe6c0)))
private theorem r7 : BlockChecks (S 173880) N P 2323 7 324 :=
  block! 2489,5,0x25716e1d54974f360702e6400,0x25716f6239c30ed874385e300,(more! 0x22ee1350601022dddd14d9d60,0x22f2148557eb569d1a71ead00, (more! 0x280f2753f5edb9b667624e00,0x27d0f8fac454920dac2273a0, (last! 0x27083d2be0031edb9e2080,0x25f679a12194ec6611b940)))
private theorem r8 : BlockChecks (S 177154) N P 2323 8 317 :=
  block! 2511,6,0x26dd92f2d2dfbc96e8681e100,0x26dd943dd61c250db01a34600,(more! 0x2446c00ae5d0a1d513a4d3200,0x244ae8c0e91f8ddf5e9eb4740, (more! 0x293d7822c98b86153a78da80,0x28fcf4d9b9c8af1a35113580, (last! 0x3052e01b489406a6510a60,0x2f25a032e498ab8e6d9500)))
private theorem r9 : BlockChecks (S 180959) N P 2323 9 309 :=
  block! 2538,7,0x288d4e76a87e350cf58673000,0x288d4fc8c7ca11304057d5000,(more! 0x25de9097315414adc1b774260,0x25e2e830cfb582c0a5db92d40, (more! 0x2ab32fdf0d7f66c3262fac00,0x2a6fddd78b057a5020669020, (last! 0x392b406fc4d7352f0473a0,0x37e78ba53f059377fb92e0)))
private theorem r10 : BlockChecks (S 187112) N P 2323 10 301 :=
  block! 2574,8,0x2b5adafec5d6641cd34bb2c00,0x2b5adc5c645273101a9597b00,(more! 0x287fcc9f554e72e1b9b76fd60,0x2884721c4a5b76ff1cc43d120, (more! 0x2d6eff65fec353dc11939040,0x2d26fa9b5072dfd5631ea6c0, (last! 0x42d32dc829d6a726e28860,0x417313cd6c32579ec38be0)))
private theorem r11 : BlockChecks (S 195637) N P 2323 11 291 :=
  block! 2625,10,0x2f64a4f5e54201e2e3d27ad00,0x2f64a6637189e4e7a5a8cc700,(more! 0x2c4648ed2adcb399c3f5b2960,0x2c4b5eccbc24f9fe31da38300, (more! 0x319c380df7803fe99f289d40,0x314d62f98fed220a31356b40, (last! 0x4a78129e003a2c5268f3e0,0x48f7abd2bdd4a2b71f58a0)))
private theorem r12 : BlockChecks (S 211000) N P 2323 12 278 :=
  block! 2711,13,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x337795538efbe138847a9f380,0x337d829ee4a9c8132bc812900, (more! 0x3a32c98aad2e7396a65ca880,0x39d6e71a7df38fb67c935300, (last! 0x5222a96019704c54a29060,0x5062080714e8562770da00)))
private theorem r13 : BlockChecks (S 211000) N P 2323 13 263 :=
  block! 2658,11,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x338d5d2cbf8470c2fee726040,0x339349f47c33a6bc59b3fa940, (more! 0x38f668a03a73100d6509d720,0x389a1c6f61d9d8b641b92160, (last! 0x324de61c098ee85c9588a0,0x30ff4427d7584b2382d360)))
private theorem r14 : BlockChecks (S 211000) N P 2323 14 245 :=
  block! 2608,9,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33a0c813c37143f8461be4200,0x33a6b469e2c649a561ec81720, (more! 0x37d7d87e140b82dbed27d360,0x377b266f2cc9c21451f83160, (last! 0x19e599c739ebb94a246880,0x1903e4e4f2657ed94b9d80)))
private theorem r15 : BlockChecks (S 211000) N P 2323 15 226 :=
  block! 2564,8,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33b410149480fb082bb8322e0,0x33b9fbccfb5d63b78e68cd7a0, (more! 0x36b428b6b9d8de58f2389380,0x36571aff34daf51a4426b1e0, (last! 0x9b96dab364ca256d2c9c0,0x93d4cf29fca9837b2e160)))
private theorem r16 : BlockChecks (S 211000) N P 2323 16 203 :=
  block! 2526,6,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33c4587181df884189af75820,0x33ca43bbff3f7b518a8c83020, (more! 0x35b7008df7f4c89bf2a1a860,0x3559aa019c733db706d135e0, (last! 0x1e976979cf995c5a69920,0x1bcfa9768f63a16eb8660)))
private theorem r17 : BlockChecks (S 211000) N P 2323 17 178 :=
  block! 2492,5,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33d3b72d6c89c9056282588a0,0x33d9a200187cbf3e2bae302c0, (more! 0x34c2cc65ad5f3161443ce4e0,0x346552c61bc9681dd3dd43c0, (last! 0x4d53f76a9b73ba4cc80,0x2e2d202420901550c20)))
private theorem r18 : BlockChecks (S 211000) N P 2323 18 151 :=
  block! 2462,4,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33e22e85bd9681fb4cfa75980,0x33e818dafa6f234bebe0fa320, (more! 0x33db6477725fae3fdac16760,0x337df0bbe33e8313e7592c40, (last! 0,0)))
private theorem r19 : BlockChecks (S 211000) N P 2323 19 122 :=
  block! 2435,3,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33efc4ea0874c2e9983c00980,0x33f5aebf8934332e111e08120, (more! 0x33022e8960ea4b5d09850900,0x32a4c2cdae171c3b7ff1b4a0, (last! 0,0)))
private theorem r20 : BlockChecks (S 211000) N P 2323 20 90 :=
  block! 2411,2,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x33fbe38fa6164a3b0fbb8fde0,0x3401ccf98ec552739274fb500, (more! 0x3240145669b41271befae140,0x31e2af4dc56a8b52686608a0, (last! 0,0)))
private theorem r21 : BlockChecks (S 211000) N P 2323 21 56 :=
  block! 2389,1,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x34074c075e8aa6f5967673f20,0x340d350528ff73d2873fc2500, (more! 0x31897c95a74202243291bcc0,0x312c1e4c1cf0f171822d3f60, (last! 0,0)))
private theorem r22 : BlockChecks (S 211000) N P 2323 22 20 :=
  block! 2369,16,0x371fdb1cdaf80e54b599be400,0x371fdca71be498a90ac5a6300,(more! 0x3412062e00e5d7036f785cf80,0x3417eec0dd2f30ec2617dd560, (last! 0x30dddfa74bf340803aaf65c0,0x3080880c673ad7b9b4a60fe0))
theorem checks : ∀ x : Test .h2274, Checks .h2274 x :=
  grade_checks .h2274 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, trivial⟩
end H2274

namespace H2294
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 12667876648826196
local notation "P" => 327528160189452
private theorem r0 : BlockChecks (S 234728) N P 2343 22 0 :=
  block! 2696,1,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x505928787bf95b5210a09c540,0x506e3482716942c7486ea6a20, (more! 0x110ed7a2be5994ff3f67e1220,0x1102c22803264af5a63073e40, (more! 0x430a3b85ad87580f0bb92160,0x427d0662cc3e96721fd07540, (last! 0,0))))
private theorem r1 : BlockChecks (S 179424) N P 2343 1 331 :=
  block! 2761,4,0x3b60f6cc0b88c82e96cbb9180,0x3b60f9097af5101c8d5013880,(more! 0x2dfda8a6c1ad81a610f14d260,0x2e09e414ee60e15790dcf71e0, (more! 0x9ebddd59cab7580a31b21c00,0x9e4f14e4ec82950426b0af20, (more! 0x373645f04fd2cd1772321820,0x36e4c9fbfd8518bf565b3960, (last! 0x413986254a1fe488bc3520,0x3f1834f0d7947e9b6900c0))))
private theorem r2 : BlockChecks (S 180915) N P 2343 2 326 :=
  block! 2773,4,0x3c5e7a436351792fd995f3500,0x3c5e7c8596a06b5527fc82100,(more! 0x2ecb1870de296ff311e64dcc0,0x2ed78903b7a8fa0a77bcc7660, (more! 0xa16f0ff82c9a2609dd100a80,0xa0fe3ea59666533532f55ba0, (more! 0x3774c710363c2b0a7bf44600,0x37224a6b68640a265eadcae0, (last! 0x52c68cbc0b790279d58560,0x5061d170194a5e128577e0))))
private theorem r3 : BlockChecks (S 182775) N P 2343 3 321 :=
  block! 2788,5,0x3d9dabc27a4070c4aac172600,0x3d9dae0a9f59473950a40ee00,(more! 0x2fcb5e4e18548075e3b50e8a0,0x2fd811bd709d6ebc67b7e6260, (more! 0xa4d2586f8d13f3f135b77280,0xa45f01c8abd6df6d074b51a0, (more! 0x37ec09f3c452e826192066a0,0x37982ee58a6664e0caebaca0, (last! 0x6734c91b8ecc946a40ef40,0x648cbc7b4bfd57c091d9a0))))
private theorem r4 : BlockChecks (S 185099) N P 2343 4 316 :=
  block! 2804,5,0x3f311378df0d3fd0006ea4300,0x3f3115c871910055341b99700,(more! 0x310cd64bcf89505217861d080,0x3119de30b57273071710e2cc0, (more! 0xa91a14157734879d3533d900,0xa8a398373b9f6e2c258260c0, (more! 0x38ac3b182e588f78e341a280,0x385689ba825d6955f0fdf180, (last! 0x7eca741fd9e94e639c14c0,0x7bdf1915596b363057eb80))))
private theorem r5 : BlockChecks (S 187083) N P 2343 5 310 :=
  block! 2822,6,0x408d7e55d7627e7248d5b7300,0x408d80abc123ff4c1e1810700,(more! 0x3224f54b9692131496f17c220,0x3232465df911a070f02cdffc0, (more! 0xaccf5356e27e8d2714d2a000,0xac561776e23444713cec5920, (more! 0x392488137a817874e38c0620,0x38cd3e7144377bfc983a0920, (last! 0x95c039c365a1931b2fd600,0x92a192cb097a16438f8080))))
private theorem r6 : BlockChecks (S 189769) N P 2343 6 304 :=
  block! 2843,7,0x426b1b42f55ac0dd27dafdd80,0x426b1da174b43e9d2d8c7e380,(more! 0x33a0f1996b05afd519b0d8620,0x33aea6df3cc847216aa82e160, (more! 0xb1e360c9449f3a4763aaf900,0xb1666f8d9db42c173ac1b6c0, (more! 0x3a10fdd06099b77567993160,0x39b76403434b5943aedef3a0, (last! 0xaf6b918fb937a1059eb460,0xac193d8eaf5fe84f2f2aa0))))
private theorem r7 : BlockChecks (S 192397) N P 2343 7 297 :=
  block! 2866,8,0x4444fdc53f9d31d58f64aba80,0x4445002c251a8bc39ebb89c80,(more! 0x351ada6a973732b5123e722e0,0x3528f35afc736a363c5d2c6e0, (more! 0xb6f0761c045c65320b3ac7c0,0xb66fd3e08a61dfbaa61f1c80, (more! 0x3aeb4fd48b376120f19eda60,0x3a8f5b217f468a9532231320, (last! 0xc714239065bf6a098467a0,0xc39ce5d79bbb9810fbaea0))))
private theorem r8 : BlockChecks (S 196316) N P 2343 8 290 :=
  block! 2895,9,0x4713c5096f4046e7faecafe80,0x4713c77cdb220eaec2bb08980,(more! 0x3751cabb59b7776c59d43b740,0x37607aa07b2ec188b9b49d980, (more! 0xbe975c48d8a6954bdf73d800,0xbe113733c80c6b87ab7f5820, (more! 0x3ca794e3e81cbb945bec45c0,0x3c47ee49f23bad46c5b4d7c0, (last! 0xe167710012e062bdb09b40,0xddc4aed8866a012725c220))))
private theorem r9 : BlockChecks (S 201102) N P 2343 9 282 :=
  block! 2932,10,0x4a9535677e813629508ec1b00,0x4a9537ea3620fc9b37f538400,(more! 0x3a12df229d9e5cea3ec9144e0,0x3a224bbc0fe38a340cb4ef0c0, (more! 0xc828415ff9fb31243d33b980,0xc79b42865323c6e824119600, (more! 0x3f03fdd4a93cd852a643e1e0,0x3e9fa0f127f7fc14bf70bba0, (last! 0xf982181c614d277711d7a0,0xf5b6d0929fc35de14b2b40))))
private theorem r10 : BlockChecks (S 209391) N P 2343 10 274 :=
  block! 2983,12,0x50da9c8b8641d350a1659ec00,0x50da9f28bba8a00315aff7c00,(more! 0x3ef537d57d9961194b0321cc0,0x3f05f5b7115bc08da690fa120, (more! 0xd941e2ec888be7402ff03c40,0xd8a8c4358d7b73326acf06e0, (more! 0x43fd6b68b0322a7a96b09220,0x43908ab2c48235d8ba2d2fa0, (last! 0x1185aeb9d15fd8fb6797740,0x1144062815638c5889ea8c0))))
private theorem r11 : BlockChecks (S 221352) N P 2343 11 263 :=
  block! 3060,15,0x5a5969fadc633e7f9ecdedf80,0x5a596cbe4bdf3a9363d1afe80,(more! 0x464fde90aa2b63f0f9ae25e40,0x46629c6cb65cc8b431cbf5e80, (more! 0xf33735b4dc163a74ae6666a0,0xf28bc7b86d7ff5a0f0a62b60, (more! 0x4c2a9cb8014660194f35dd20,0x4bb0ba5244ae024f102eb000, (last! 0x137613c5735db05a4e73b40,0x132ca6ff99fdd09ddd1da00))))
private theorem r12 : BlockChecks (S 234728) N P 2343 12 250 :=
  block! 3094,16,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4f0dbf3de37cf21fc17c3e120,0x4f22dade5c7f78f2565b1c740, (more! 0x111eaf5683b1f11da53029000,0x11129dbe74887c342d5625480, (more! 0x558736b1efe398301fc8aca0,0x54fda0a863a9e434aa7136a0, (last! 0x12cd16891ee725df2d86ee0,0x127f94248f01af432074160))))
private theorem r13 : BlockChecks (S 234728) N P 2343 13 234 :=
  block! 3027,14,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4f39129861a54998f406c2800,0x4f4e2d447e4c84f1f36936760, (more! 0x111d79c4bcfbb067790bf2d20,0x1111655dadbe641d65dce0be0, (more! 0x5349cb4392845ee8418a3720,0x52bf71fd8e57bf0da7577200, (last! 0xc8a9a03df21de878962000,0xc4d0eb68d63a436f7684c0))))
private theorem r14 : BlockChecks (S 234728) N P 2343 14 215 :=
  block! 2969,11,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4f5f976b915d6634495e4ab40,0x4f74b1598a991da4146119f80, (more! 0x111c77608beda7ae4ad713c80,0x111060b916bf6b0a47d13ada0, (more! 0x5141b49d40f83bb4a1c798e0,0x50b691fba102e5d84b419640, (last! 0x77ee154e6770d918981960,0x750e8972fdc28805d840a0))))
private theorem r15 : BlockChecks (S 234728) N P 2343 15 194 :=
  block! 2919,10,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4f842fa5334b5b98f2a442380,0x4f994885f81ed4efa6e2016a0, (more! 0x111b3a76dd7742def21369c40,0x110f22335ac7c427f5f7e7100, (more! 0x4f47bc4baee9de1429ac7f80,0x4ebbd1390aa3ac8f22492480, (last! 0x3c292304d312dc3ce25c80,0x3a3c940968c2875223b7c0))))
private theorem r16 : BlockChecks (S 234728) N P 2343 16 171 :=
  block! 2875,8,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4fa6c6916c01c58356ffe5460,0x4fbbde2b1df3ec002c437d780, (more! 0x1119d5aa00a04bd7a68d4d6a0,0x110dbc630560b07b76693c6e0, (more! 0x4d5acf788233e8b77454a500,0x4cce2c4c5badc4efa595af00, (last! 0x16714945eb299402de44c0,0x156183ebe5918a80b5f1e0))))
private theorem r17 : BlockChecks (S 234728) N P 2343 17 145 :=
  block! 2837,7,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4fc57813d9e9e1ea9f173cae0,0x4fda8ea5d52b24953c8b52720, (more! 0x1118ae83a8d10ec8e44b65cc0,0x110c94c3049c2ae91c3a40300, (more! 0x4b93dfcb372c1c9324a0ebc0,0x4b06a7102a5c937d46a95c40, (last! 0x4733371f51a15c0b1b6e0,0x4110532edd3ab44c26840))))
private theorem r18 : BlockChecks (S 234728) N P 2343 18 117 :=
  block! 2802,5,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4fe2782b31e85fe0ca6413060,0x4ff78d90896fe23d45e5e94e0, (more! 0x111770a508f843ecfb70fccc0,0x110b56f55130a0c4a811e93a0, (more! 0x49dc44beff5cfe1e47cca6c0,0x494ec0c22b02216d6d9c3940, (last! 0xe8aa8c40a0fea869a20,0x9588417ce16f337fd40))))
private theorem r19 : BlockChecks (S 234728) N P 2343 19 86 :=
  block! 2771,4,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x4ffc329a93c92501f43f8d560,0x50114714fd73b31548c11b3e0, (more! 0x11167194fe372a983dea68760,0x110a587c04ef76a9ee515a700, (more! 0x4850088010e7744687eda340,0x47c2847ef1f6410ddec2e480, (last! 0,0))))
private theorem r20 : BlockChecks (S 234728) N P 2343 20 53 :=
  block! 2744,3,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x50148526f92c18132071b6560,0x5029989fb3394e823610edf20, (more! 0x111566c057fbe97fbc31bf2a0,0x11094ebe22ef007190de90a00, (more! 0x46db4b4457a88824246bc420,0x464dc5e6a688f8d7e582c780, (last! 0,0))))
private theorem r21 : BlockChecks (S 234728) N P 2343 21 18 :=
  block! 2719,2,0x6597974e915d031826dc44f80,0x65979a3cc0a29c3d3584e2e80,(more! 0x502b75e80e3e8dc5db1a85ec0,0x50408852a20e141ff641cb160, (more! 0x111458390b6504bb92cc7e680,0x110841c69b1e8de3684c946a0, (more! 0x457d208fe68ac30c7e8131c0,0x44ef9313ce70dcad4578e620, (last! 0,0))))
theorem checks : ∀ x : Test .h2294, Checks .h2294 x :=
  grade_checks .h2294 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, trivial⟩
end H2294

namespace H7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 52891447576
local notation "P" => 22832869
private theorem r0 : BlockChecks (S 946) N P 7773 7 0 :=
  block! 57,1,0x1e12c973f758333c0,0x1e12ccfe2a097d080,(last! 0x1e170bd72aee0e480,0x1e1713d446d33f5c0)
private theorem r1 : BlockChecks (S 886) N P 7773 1 26 :=
  block! 67,2,0x1a68fc72639a27ac0,0x1a68ffc32c1694880,(last! 0x1a6c14eaf40e08420,0x1a6c1c1d901a4af00)
private theorem r2 : BlockChecks (S 913) N P 7773 2 24 :=
  block! 71,2,0x1c0776599b31cef80,0x1c0779c439df9f400,(last! 0x1c09805f614986ba0,0x1c0987deabfc71960)
private theorem r3 : BlockChecks (S 946) N P 7773 3 22 :=
  block! 76,3,0x1e12c973f758333c0,0x1e12ccfe2a097d080,(last! 0x1e15edfeeac865a80,0x1e15f5f27d5a52500)
private theorem r4 : BlockChecks (S 946) N P 7773 4 19 :=
  block! 76,3,0x1e12c973f758333c0,0x1e12ccfe2a097d080,(last! 0x1e164d1f9c2cf9420,0x1e1655163799283a0)
private theorem r5 : BlockChecks (S 946) N P 7773 5 14 :=
  block! 67,2,0x1e12c973f758333c0,0x1e12ccfe2a097d080,(last! 0x1e15565b8c4b42100,0x1e155e4a3faae98c0)
private theorem r6 : BlockChecks (S 946) N P 7773 6 8 :=
  block! 61,1,0x1e12c973f758333c0,0x1e12ccfe2a097d080,(last! 0x1e16bd15d1e123400,0x1e16c51055c53dac0)
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
end HighTerminal82180
