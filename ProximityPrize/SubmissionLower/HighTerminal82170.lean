import ProximityPrize.SubmissionLower.HighBanks82170

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighTerminal82170

open Finset
open P3 (HighBand)
open P3_7 (Bank Test tested debit grades terminal threshold seedThreshold)
open P3_7_4 (BlockChecks)
open K1_14 (Shape shapeSum triangle slots)
open HighBanks82170 (adjusted count start)
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
  shapeSum s (entry 179974 h s E v)

private theorem joint_upper (h : ℕ) (s : Shape) (E v : ℕ) :
    P3_7.jointGain h s E v ≤ gain h s E v + triangle s.U * (count s*(9*s.m)) := by
  have bound (q j : ℕ) :
      entry 179983 h s E v q j ≤ entry 179974 h s E v q j + triangle s.U*(9*s.m) := by
    let c := fun a => slots s.U (a*v)
    have hc : Antitone c := fun _ _ hab => slots_anti s.U (Nat.mul_le_mul_right v hab)
    have hzero : c 0 = triangle s.U := by simp [c, slots]
    rw [← hzero]
    apply perturb _ _ _ _ _ hc
    intro a
    unfold width
    have hcut : s.m*179983 = s.m*179974 + 9*s.m := by ring
    omega
  have le : shapeSum s (entry 179983 h s E v) ≤
      shapeSum s (fun q j => entry 179974 h s E v q j + triangle s.U*(9*s.m)) :=
    sum_le_sum fun q _ => sum_le_sum fun j _ => bound q j
  rw [HighBanks82170.sum_shift] at le
  change shapeSum s (entry 179983 h s E v) ≤ shapeSum s (entry 179974 h s E v) + _
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
  have eq : debit h a = debit h t + triangle t.shape.U*(count t.shape*(9*t.shape.m)) := by
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
local notation "N" => 8505815426382120
local notation "P" => 191486597252812
private theorem r0 : BlockChecks (S 211000) N P 2297 23 0 :=
  block! 2351,1,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x337397fe570e1ad22c893fa80,0x33798b91a948dec01b32e7060,(more! 0x3aacfd7cbf9cb2f1e2d77ea0,0x3a4ef6a2b0d8a5825a7f53e0,(last! 0x0,0x0)))
private theorem r1 : BlockChecks (S 162873) N P 2297 1 359 :=
  block! 2406,3,0x20d9cf658e7b5063308387500,0x20d9d095e2a1b8fe64c0f6b00,(more! 0x1e20433ec530bdb297e5587c0,0x1e23cc73695ba18ee44e02360,(more! 0x2b8684fc1ef1b410e2636f60,0x2b4f8bf93315a82adb462a20,(last! 0x124dd956ed7521c3240400,0x116e129f66c95ca08aeae0)))
private theorem r2 : BlockChecks (S 164297) N P 2297 2 354 :=
  block! 2417,3,0x216d6960d0fee4e956828cd00,0x216d6a93ce4b0b244e055b300,(more! 0x1eac6bc36fc49e8fb97583780,0x1eb005148a6eed87801d764a0,(more! 0x2bf6fdc4e9b26aecd13da860,0x2bbf2ec3b0258d3602a7b020,(last! 0x19069dd73a5e8b160f9dc0,0x17fe2bf21849cd46475a00)))
private theorem r3 : BlockChecks (S 166033) N P 2297 3 349 :=
  block! 2428,3,0x222316f299987c62e4d915900,0x22231828d547dbc3dd1c53700,(more! 0x1f57e4b3e584ee99217e3f4c0,0x1f5b91d804f284ba11aad86e0,(more! 0x2c9253613d094f14819cda80,0x2c597488c3937fa8b2679bc0,(last! 0x2131901eebce0b167d8ac0,0x1fff9d5744a8e33e0645a0)))
private theorem r4 : BlockChecks (S 167408) N P 2297 4 343 :=
  block! 2441,4,0x22b457993025c7c39c5c0b800,0x22b458d1fd8aac71b8e77bf00,(more! 0x1fe29d590243a61126f110000,0x1fe65a6290e6a54953f65ec40,(more! 0x2cf221f9e7540e5f0503f500,0x2cb86a7079ce612fd645c300,(last! 0x29b8a580a1fd964d6f2a80,0x2864156d0759eef6555140)))
private theorem r5 : BlockChecks (S 169216) N P 2297 5 337 :=
  block! 2455,4,0x2375287b7a9736afc2183c000,0x237529b7a8cffadded9433700,(more! 0x2098fc8de9c2b2843970a37c0,0x209cceac8136b648931e127a0,(more! 0x2d8f65041af74a20ad9b1d60,0x2d54826078ad75a9368fd1a0,(last! 0x338948f8f3b5574d379dc0,0x32128ea304aff592d49420)))
private theorem r6 : BlockChecks (S 171591) N P 2297 6 331 :=
  block! 2471,5,0x24759679d12e9ce124b7efc00,0x247597ba6f725e948edf27400,(more! 0x2189c1cd33f44ff6a2a131000,0x218daff1522957d9293881b60,(more! 0x2e7ee2a13797265f7338d3a0,0x2e426711b53d7d4c7e9ca260,(last! 0x3ebd95bfe6fa88143de6c0,0x3d24d54656ccce43465d40)))
private theorem r7 : BlockChecks (S 173880) N P 2297 7 324 :=
  block! 2489,6,0x25701cb4c695b370dd43afc00,0x25701df9abc173134a7927b00,(more! 0x22759f6cbb9992f4033cdf600,0x2279a8fe9f2022866e52fcd20,(more! 0x2f5e6d2c4ba2cd2020b21ce0,0x2f205a07f8ef805a63f168a0,(last! 0x498db73e9700b1e9005dc0,0x47daeb53a2fac8d8bf2340)))
private theorem r8 : BlockChecks (S 177154) N P 2297 8 317 :=
  block! 2511,6,0x26dc3558f0994ea8caec24300,0x26dc36a3f3d5b71f929e3a800,(more! 0x23c9a7a65bae965bf7c539e00,0x23cdd90cd5b1fab592763cf60,(more! 0x30d38cc12bd7baa0dd009c20,0x30931f8fc70a04775b84c360,(last! 0x558af0eb5970bdb978f3e0,0x53bc8ced4bc5d687d9e5a0)))
private theorem r9 : BlockChecks (S 180959) N P 2297 9 309 :=
  block! 2538,7,0x288be26bc7d4db19b37309000,0x288be3bde720b73cfe446b000,(more! 0x255bf57d91664bab0429a2980,0x2560562af43ac49fe4ee3eae0,(more! 0x329e4a410666afa2942e5860,0x325b08d39b6240bf7ff452e0,(last! 0x609e3d39e7d2f8bf9f2de0,0x5eb8acccd9c9c672507860)))
private theorem r10 : BlockChecks (S 187112) N P 2297 10 301 :=
  block! 2574,9,0x2b5956fb9fe60d8efb81fd400,0x2b5958593e621c8242cbe2300,(more! 0x27f40a41ded99a593bf0365c0,0x27f8b97739bb396e4f6481be0,(more! 0x35e7ef54bf7f5aa679adcee0,0x359ff76b6b3df669323106a0,(last! 0x6d5d8d898faf4beaff2880,0x6b5506241095554e0c3800)))
private theorem r11 : BlockChecks (S 195637) N P 2297 11 291 :=
  block! 2625,11,0x2f62fe7a68346123fe0b59700,0x2f62ffe7f47c4428bfe1ab100,(more! 0x2bad5163e56d8d3dace89f100,0x2bb271e9cbb9f8b4384b69100,(more! 0x3ae2793fd25c813478c481e0,0x3a93afd94480c15e6ae62700,(last! 0x78d300e0880c11656a6660,0x769c80943d42f1ac7b7820)))
private theorem r12 : BlockChecks (S 211000) N P 2297 12 278 :=
  block! 2711,14,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x32c54cabbda2f05fc51f39500,0x32cb46662506823ff02718ce0,(more! 0x4501e14f3a7b759734a29040,0x44a612bdd65c415875552240,(last! 0x888b23e8a7b6b5d73fff00,0x85efab1281f72d1b842480)))
private theorem r13 : BlockChecks (S 211000) N P 2297 13 263 :=
  block! 2658,12,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x32db23929fc36d1076192c360,0x32e11ccdc958476a236b8b140,(more! 0x43d0d47632961763756d8720,0x437485673847d82540bb6ea0,(last! 0x5c70ef1ce58902b8386be0,0x5a5deccae880ab1bf522c0)))
private theorem r14 : BlockChecks (S 211000) N P 2297 14 245 :=
  block! 2608,10,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x32ee9b688ec2549ae2235cb00,0x32f49436853299b1b74434f80,(more! 0x42bd4d1685ec54ef2d9294a0,0x42608060819d643da2b6d460,(last! 0x38320c6ed4f060f45ef380,0x36a3796a5b3577cd7c7340)))
private theorem r15 : BlockChecks (S 211000) N P 2297 15 226 :=
  block! 2564,8,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x3301f59d953994f1762bdcdc0,0x3307edd175167eaf40efd5dc0,(more! 0x41a3e6b7b282c88c82da4540,0x4146a0b401c5538f64e46fc0,(last! 0x1c979571c3333a05864c00,0x1b8c016d9fc8bd5572f740)))
private theorem r16 : BlockChecks (S 211000) N P 2297 16 203 :=
  block! 2526,7,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x33124a87ca9612741a4bcc380,0x3318425199a2fbcb74d54c0e0,(more! 0x40afa5a842e618aee4884240,0x4051f1db9b39e2f06352f240,(last! 0xb19307ef33e645d320160,0xa81f7acb99e215b8104c0)))
private theorem r17 : BlockChecks (S 211000) N P 2297 17 178 :=
  block! 2492,6,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x3321b706bbd5678e10f67ca60,0x3327ae5c1e1e7ac76e6686fc0,(more! 0x3fc16caf8c5496c7adf82820,0x3f63620dabd83d286c824980,(last! 0x25ddf70e97d71b5582580,0x224bbcf83b9e06b039d60)))
private theorem r18 : BlockChecks (S 211000) N P 2297 18 151 :=
  block! 2462,5,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x33303cd5db03ed50ae566d280,0x333633b0c7af1c3cf2bc171c0,(more! 0x3edb69d54496c3157c9ce260,0x3e7d31f120e1db5dde0e58a0,(last! 0xc97b0396876f657c480,0x85d122ef6d5d4784780)))
private theorem r19 : BlockChecks (S 211000) N P 2297 19 122 :=
  block! 2435,4,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x333de1fe79aef524830c0fdc0,0x3343d85c4fae4d87c11337480,(more! 0x3e0153d02039fba98fd8ddc0,0x3da31f86cbfa38855df20e00,(last! 0x0,0x0)))
private theorem r20 : BlockChecks (S 211000) N P 2297 20 90 :=
  block! 2411,3,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x334a0d0a57dd33a0ffcbb5c20,0x335002ff2bd575d1c7b27a100,(more! 0x3d3e73e1ecb666265a4c5080,0x3ce0462232d39ef3d83bdde0,(last! 0x0,0x0)))
private theorem r21 : BlockChecks (S 211000) N P 2297 21 56 :=
  block! 2389,2,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x335581fee9a1e29d17bc46b20,0x335b7789eeda13c75f9d327e0,(more! 0x3c87149d151caeba2412c620,0x3c28ed7768cfd31ffcf843e0,(last! 0x0,0x0)))
private theorem r22 : BlockChecks (S 211000) N P 2297 22 20 :=
  block! 2369,1,0x371df2d10332d54c741bb7c00,0x371df45b441f5fa0c9479fb00,(more! 0x33604884461a0dbe29e24a4a0,0x33663da6753196bb9e42f40e0,(more! 0x3bdab1ca6c7a657dfecede60,0x3b7c9131cf8133983e937620,(last! 0x0,0x0)))
theorem checks : ∀ x : Test .h2274, Checks .h2274 x :=
  grade_checks .h2274 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, trivial⟩
end H2274

namespace H2294
local notation "S" u => (⟨7550,10506,2218,u⟩ : Shape)
local notation "N" => 12666302159595196
local notation "P" => 327528160189452
private theorem r0 : BlockChecks (S 234728) N P 2318 22 0 :=
  block! 2696,2,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4ed15130869d0e12048ecfe40,0x4edbfc853193223adb684a1c0,(more! 0x115f154b94237204657c3a300,0x11677eba8542d3b4aaf83a020,(more! 0x564cc746b6c4c7fa1f42b2c0,0x551daec60131982609668fa0,(last! 0x0,0x0))))
private theorem r1 : BlockChecks (S 179424) N P 2318 1 331 :=
  block! 2761,5,0x3b5edbc841f2b25026ed9fb80,0x3b5ede05b15efa3e1d71fa280,(more! 0x2d19e8f2f6a7bae021af38400,0x2d201cd5c38530fb41e70d7e0,(more! 0xa199fa79e8ffffc6327c04c0,0xa1e887208c67b89e0d8214c0,(more! 0x4227d5def319533895daa920,0x417af9599aaba14ac62e56a0,(last! 0x8e9b59b1fcbd7e8ec83280,0x8afe283cd14abe54e596c0))))
private theorem r2 : BlockChecks (S 180915) N P 2318 2 326 :=
  block! 2773,5,0x3c5c56b8df9c7fea89fb59b00,0x3c5c58fb12eb720fd861e8700,(more! 0x2de37b9f38a5b4b47d1b36cc0,0x2de9ca6d6dfa16ad281371320,(more! 0xa4588617584a1bc9ea669920,0xa4a86774706be17baeaa4f40,(more! 0x428f4e53db75012b9d814460,0x41dfb3a9b947e213fc516360,(last! 0xa724de28a8c9f98c91ba60,0xa347b6c857e2425c372740))))
private theorem r3 : BlockChecks (S 182775) N P 2318 3 321 :=
  block! 2788,6,0x3d9b7d7d1ab12a3eb87a51a00,0x3d9b7fc53fca00b35e5cee200,(more! 0x2edee5011fe0af19623c2d2c0,0x2ee555ae809924a975aa527e0,(more! 0xa7cc5f7d58ce42fe8d454ba0,0xa81ded9a9612935f97710580,(more! 0x433c30b6b7472cb128999e20,0x4289116b9f47860bcf0d9680,(last! 0xc2825777c1aa2e85819140,0xbe65d6ca3ff775f6e2c020))))
private theorem r4 : BlockChecks (S 185099) N P 2318 4 316 :=
  block! 2804,6,0x3f2ed7a60dce5464177f18d00,0x3f2ed9f5a05214e94b2c0e100,(more! 0x301a38ed4ca1e36ac8c363540,0x3020d464eba2ee7a5cc451840,(more! 0xac28ce6814dda7e67a419900,0xac7c7a33d88d1a14c5132500,(more! 0x44422b6f83593f1bef33d680,0x438a89f07975514077228680,(last! 0xe1076b94110ec56853cc40,0xdcab4fb5a82698d33bf380))))
private theorem r5 : BlockChecks (S 187083) N P 2318 5 310 :=
  block! 2822,7,0x408b36d0545117b86b30a5d00,0x408b39263e1298924072ff100,(more! 0x312d05ed30c141bc2679e9800,0x3133c67613f2e345cba3ada80,(more! 0xaff0275d65df86f8227419c0,0xb045a822051068f9ae6dcae0,(more! 0x44f7c0a7b2b464b4603beb80,0x443c2c2aceded319c6908020,(last! 0xfd0578010403228410ea80,0xf87d9218f70893f1e819c0))))
private theorem r6 : BlockChecks (S 189769) N P 2318 6 304 :=
  block! 2843,8,0x4268c3b6f556901d123987680,0x4268c61574b00ddd17eb07c80,(more! 0x32a1b9319f633ab1827153920,0x32a8ac7d9194cbe8d1a7cc160,(more! 0xb51ca7433fc849bf3ded9940,0xb574aa63200b8970fd95c4e0,(more! 0x463a296f62d840b8273b71c0,0x45791ef7a793ce47613f0a20,(last! 0x11be1994a96fec43d6ff080,0x1172b24f8b3214cedb42ca0))))
private theorem r7 : BlockChecks (S 192397) N P 2318 7 297 :=
  block! 2866,9,0x44429655b5578f593ac22f980,0x444298bc9ad4e9474a190db80,(more! 0x341462fdaa8cd880f630f0180,0x341b88c5e105561f62a1c73a0,(more! 0xba42182546db7f38e3a32080,0xba9c99d50906d7819e02bac0,(more! 0x476b897df4c719f541e39a60,0x46a5012fc0a097a323608160,(last! 0x1371aa5c08649282e740340,0x132458d0f5ed1a0e17c5200))))
private theorem r8 : BlockChecks (S 196316) N P 2318 8 290 :=
  block! 2895,10,0x47114585a272419294d5b7680,0x471147f90e5409595ca410180,(more! 0x3640598ab619fa94bac5f3680,0x3647cbccdbbea4a6ac05f7960,(more! 0xc20d67db0219ba2bbc6a5740,0xc26bb11d8a7b5718ab0ec9a0,(more! 0x49acf73bd9b0b40639f8cbc0,0x48de19f63f0b066b89402c80,(last! 0x1560054d8a72c8b2db32840,0x151000802db6e95020099a0))))
private theorem r9 : BlockChecks (S 201102) N P 2318 9 282 :=
  block! 2932,11,0x4a9297dbb21b2aa5673195200,0x4a929a5e69baf1174e980bb00,(more! 0x38f3b59503e9d239e33b21d60,0x38fb87705cf915d17d4693300,(more! 0xcbcb9e36236460743814c660,0xcc2ea0ba4a73dea0175d44e0,(more! 0x4cb145a10595112fc1ef2e60,0x4bd7f4cee92ad9d966bb0020,(last! 0x17296c71d8d1ab7f3832b00,0x16d69e2ab71d280bd607280))))
private theorem r10 : BlockChecks (S 209391) N P 2318 10 274 :=
  block! 2983,13,0x50d7c95c68335c3d641d51400,0x50d7cbf99d9a28efd867aa400,(more! 0x3dbd883e8678ec48b54713360,0x3dc604fc5aaa0396da4cfff80,(more! 0xdd35853f90b20f82bba2b800,0xdda0f9d28fbf8c422b0fae80,(more! 0x52d601afe1bc422467e0ccc0,0x51ea178e9e4288ee1d7b3840,(last! 0x19af527f3421fd94f26e580,0x19562eb7368c771666c8b20))))
private theorem r11 : BlockChecks (S 221352) N P 2318 11 263 :=
  block! 3060,16,0x5a5645c330d050567ba5b3d80,0x5a564886a04c4c6a40a975c80,(more! 0x44f2f55d670283dd6316d6960,0x44fc757c94f12365721561980,(more! 0xf7a44238eaa62ffdafc32780,0xf81c8733901dee0fa78e6660,(more! 0x5cc8ee9641015a7dc2fc7380,0x5bc0da8987d5bf8aea692720,(last! 0x1c982bb0effa7dfc06b8b40,0x1c34659888b26afddec7580))))
private theorem r12 : BlockChecks (S 234728) N P 2318 12 250 :=
  block! 3094,1,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4d84ca63e3c281cd3e2e5bd80,0x4d8f7d6c562e796ba3e915b40,(more! 0x116e80f84a55b8a3197fd7d60,0x1176f774b8cd3acaef32c5020,(more! 0x6846bd8de7d18dbd729b21e0,0x671d098462f274aff19e14c0,(more! 0x1c894ae8e1b045143900d40,0x1c1e2ab189bf5908dd99d60,(last! 0x0,0x0)))))
private theorem r13 : BlockChecks (S 234728) N P 2318 13 234 :=
  block! 3027,14,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4db02f291f0ef42787ed95460,0x4dbae1b754326bfc6bbedb000,(more! 0x116d67c6789061bfe41fc3ac0,0x1175dcf8c8f2f8330e7271ba0,(more! 0x66233f36da1514a6497d54e0,0x64f8868e03bed1d8b0501880,(last! 0x147a33abeb1e62a2d427960,0x142121b478281372c5b3820))))
private theorem r14 : BlockChecks (S 234728) N P 2318 14 215 :=
  block! 2969,12,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4dd6c17e6335e29cad8bb8dc0,0x4de173ad411e6b52c63fec360,(more! 0x116c7e5ee6ae8e3065aea81c0,0x1174f263d5dbdb8e805df4620,(more! 0x6434f46aa2bf36aee677b2a0,0x630938f41cbe7deb5edcf140,(last! 0xdab696840ecd20b65f1b80,0xd640f4c78a754329b58980))))
private theorem r15 : BlockChecks (S 234728) N P 2318 15 194 :=
  block! 2919,10,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4dfb6ce9a3d31f60270ba4740,0x4e061e92a8ab8d275ae03c020,(more! 0x116b55cc7e31c07a75c4c0e40,0x1173c8919f0bca20cb90500c0,(more! 0x62547be6e4761e5954e393c0,0x6127c0179cd650c6bca1a340,(last! 0x82fa19e7c3bb1d7de71060,0x7fa122de5e0781a1894d60))))
private theorem r16 : BlockChecks (S 234728) N P 2318 16 171 :=
  block! 2875,9,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4e1e1b3269781f9dda0a40460,0x4e28cc3964b8b0c58c6f27ea0,(more! 0x116a00e6c6cd4120ff264e600,0x1172726429027f127eb231a40,(more! 0x607f7c776a79cd16cdca5e40,0x5f51cb95c89b754f07ea6360,(last! 0x42dfeb189aabe983435ec0,0x409aaa1949789a5d689ea0))))
private theorem r17 : BlockChecks (S 234728) N P 2318 17 145 :=
  block! 2837,8,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4e3cdf876493033ac03a556a0,0x4e47900b633166c3d38a56c40,(more! 0x1168e60c4395b8fa84b6b2fa0,0x11715668454f75b1e256dda00,(more! 0x5ecd2b8867eb270e3235ed60,0x5d9e9c3cce1f3333f95404c0,(last! 0x1a528c5be869ea75482540,0x1905ed2518843f85e9cc20))))
private theorem r18 : BlockChecks (S 234728) N P 2318 18 117 :=
  block! 2802,6,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4e59f51b8d687063ece9cd060,0x4e64a50a915d53cb7e1d4f0e0,(more! 0x1167b073abd3efd7dbc873f40,0x11701fadcebaba32f60efd920,(more! 0x5d23a1c12ce4181176e66f60,0x5bf464f728f76c86cb833fc0,(last! 0x600902b57d4b8acd3e700,0x57cdb9b64b69bdb4066a0))))
private theorem r19 : BlockChecks (S 234728) N P 2318 19 86 :=
  block! 2771,5,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4e73c051f30567ddce12fb200,0x4e7e6fcc36075c1861e9f1da0,(more! 0x1166b642fccb2efeb486dd800,0x116f248070511c743db97de60,(more! 0x5b9bcaf1a53805f47babe8a0,0x5a6c2f5d91e507698632cd20,(last! 0x34426438dda4f4248580,0x2659926cc5bb30098280))))
private theorem r20 : BlockChecks (S 234728) N P 2318 20 53 :=
  block! 2744,4,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4e8c2549daed4963d78d38580,0x4e96d444486709faaabffbba0,(more! 0x1165acadaced039582056adc0,0x116e19f178dba123b4ae3faa0,(more! 0x5a260869a46acfea7dad9c40,0x58f6767902e2612b9df76860,(last! 0x0,0x0))))
private theorem r21 : BlockChecks (S 234728) N P 2318 21 18 :=
  block! 2719,3,0x6594136288079813bbf804d80,0x65941650b74d3138caa0a2c80,(more! 0x4ea3295e5738dd3797b9c7500,0x4eadd7d2e9945dae5ab81b280,(more! 0x11649c050e826bca41b90e640,0x116d08550a83777a1ad1ba3a0,(more! 0x58c6cb04c7a857edde16c960,0x579750aa3e10d0b5b75bf2e0,(last! 0x0,0x0))))
theorem checks : ∀ x : Test .h2294, Checks .h2294 x :=
  grade_checks .h2294 r0 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, trivial⟩
end H2294

namespace H7773
local notation "S" u => (⟨124,173,32,u⟩ : Shape)
local notation "N" => 52884982216
local notation "P" => 22832869
private theorem r0 : BlockChecks (S 946) N P 7773 7 0 :=
  block! 57,1,0x1e11dbe5f35cc97c0,0x1e11df70260e13480,(last! 0x1e170bd72aee0e480,0x1e1713d446d33f5c0)
private theorem r1 : BlockChecks (S 886) N P 7773 1 26 :=
  block! 67,2,0x1a682c068cebd32c0,0x1a682f57556840080,(last! 0x1a6c14eaf40e08420,0x1a6c1c1d901a4af00)
private theorem r2 : BlockChecks (S 913) N P 7773 2 24 :=
  block! 71,2,0x1c06990df1c1db980,0x1c069c78906fabe00,(last! 0x1c09805f614986ba0,0x1c0987deabfc71960)
private theorem r3 : BlockChecks (S 946) N P 7773 3 22 :=
  block! 76,3,0x1e11dbe5f35cc97c0,0x1e11df70260e13480,(last! 0x1e15edfeeac865a80,0x1e15f5f27d5a52500)
private theorem r4 : BlockChecks (S 946) N P 7773 4 19 :=
  block! 76,3,0x1e11dbe5f35cc97c0,0x1e11df70260e13480,(last! 0x1e164d1f9c2cf9420,0x1e1655163799283a0)
private theorem r5 : BlockChecks (S 946) N P 7773 5 14 :=
  block! 67,2,0x1e11dbe5f35cc97c0,0x1e11df70260e13480,(last! 0x1e15565b8c4b42100,0x1e155e4a3faae98c0)
private theorem r6 : BlockChecks (S 946) N P 7773 6 8 :=
  block! 61,1,0x1e11dbe5f35cc97c0,0x1e11df70260e13480,(last! 0x1e16bd15d1e123400,0x1e16c51055c53dac0)
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
end HighTerminal82170
