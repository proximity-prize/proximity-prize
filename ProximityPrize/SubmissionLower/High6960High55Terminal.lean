import ProximityPrize.SubmissionLower.High6960High55Arithmetic
import ProximityPrize.SubmissionLower.High6960High55Data

set_option Elab.async false
set_option maxRecDepth 18000

namespace High6960High55Terminal
open High6960High55
open K1_14 (Shape)
open HighCore82268TerminalArithmetic (Parts)

private def GradeChecks (t : Bank) (h : ℕ) : ℕ → List Grade → Prop
  | _,[] => True
  | e, g :: gs =>
    debit h ({t with shape := {t.shape with U := g.slots}}) <
      jointGain h ({t.shape with U:=g.slots}) e (g.seedCap+1) ∧
      GradeChecks t h (e+1) gs

private theorem grade_at (t : Bank) (h : ℕ) (gs : List Grade) (e : ℕ)
    (hc:GradeChecks t h e gs) (i:Fin gs.length) :
    debit h ({t with shape := {t.shape with U := (gs.get i).slots}}) <
      jointGain h {t.shape with U:=(gs.get i).slots} (i.val+e) ((gs.get i).seedCap+1):=by
  induction gs generalizing e with
  | nil => exact Fin.elim0 i
  | cons g gs ih =>
    rcases i with ⟨_ | j,hj⟩
    · simpa [GradeChecks] using hc.1
    · have h' := ih (e+1) hc.2 ⟨j, by simpa using hj⟩
      simpa only [List.get_cons_succ,Nat.succ_add,Nat.add_succ] using h'


set_option quotPrecheck false
local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "values!" nn "," k "," l "," r "," p =>
  High6960High55Arithmetic.receipt_values (n:=nn) (last:=k) (cost:=l) (costNext:=r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)

namespace h2570
local notation "S" => (⟨7550,10506,2218,234728⟩:Shape)
local notation "N" => 0x2cfea55aa80000
local notation "P" => 0x129e297a45c0c
private theorem r0 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 22 0 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2696,15,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x564a7cba5112fbbf1b5375ac0,0x5654b3eb62dc6dbb8d5501000,(more! 0xdd6b64ae7e401295107998c0,0xdd0fbe4f7d87f1ea0118bc20,(last! 0x174300014af2bd88362e5c60,0x16fd67753fb1c73557b71200)))) (by decide +kernel) (by decide +kernel)

private theorem r1 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 1 349 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2891,7,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x52f672af94786120834eb8e40,0x5300b6e047f16eef0ceeb96e0,(more! 0xe5f4eaaf322cbc5f2943df00,0xe5b54c01c6da7f5f46e8c100,(more! 0x4299d306116d47dfcbfa3080,0x423deeaa9284709788db8880,(last! 0x14c2012936b91748af2f3a0,0x145928e46f351aa5d430d00))))) (by decide +kernel) (by decide +kernel)

private theorem r2 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 2 342 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2905,7,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x53213e5f306f533b8b7fd14c0,0x532b8278eb9dd6c425b0f8740,(more! 0xe568d527ca717bba31c83720,0xe527419e496e278f02c10fe0,(more! 0x40615da9263f74ec683f2c80,0x400766e54880b909386d4280,(last! 0x16316bb22e67cdbd4f30540,0x15c91d2a4e86d76e2ae4280))))) (by decide +kernel) (by decide +kernel)

private theorem r3 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 3 335 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2919,8,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x534e7c988ec6a87d9bedf29c0,0x5358c07f5078a4d5eff1f95e0,(more! 0xe4d9ceb8ad3d4657f9b935c0,0xe4964581f716f0747e6774e0,(more! 0x3e0d88d8a595016cd9c0d300,0x3db564291c8f9ae2998c4e00,(last! 0x171cfcef32df2531514b800,0x16b71a60c01198f389557a0))))) (by decide +kernel) (by decide +kernel)

private theorem r4 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 4 328 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2934,8,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x537e2bb0da6619a6d1a71d9c0,0x53886f452a62d6d2e172ba0c0,(more! 0xe4477ed349a4e5ca19d69080,0xe401ff4f88106889d7866180,(more! 0x3ba085cb7aef884479167500,0x3b4a18bdbad52af2a3726800,(last! 0x176a1ef79bbf8e131584e00,0x17087a163bbc2a967b26e60))))) (by decide +kernel) (by decide +kernel)

private theorem r5 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 5 321 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2950,9,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x53b0414f472a18f0e621327a0,0x53ba846dc4ee3bf3f40c4d380,(more! 0xe3b1807df71e97803fee2fe0,0xe36a0a3f21cb38dda9310e40,(more! 0x391cd02d5caa8c82055cff80,0x38c802365a7c84b6ff4eb880,(last! 0x17033547a70124bdeb99c20,0x16a7823f73203b52d07f1e0))))) (by decide +kernel) (by decide +kernel)

private theorem r6 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 6 313 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2968,10,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x53dfccaef277e83dcac843260,0x53ea0f86d7206903f90eb9ba0,(more! 0xe326f343ab41f392d6a60a00,0xe2dd9f921b4ee5a663452e40,(more! 0x36b8cbc4f16f7b97ec214180,0x36657bf86ec075c0e7fd4280,(last! 0x16606c01f42c0fb0d1a15e0,0x160af3d1356399d76f1c2a0))))) (by decide +kernel) (by decide +kernel)

private theorem r7 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 7 304 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2991,11,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x540da56cdce4584eac5abaf80,0x5417e823fd69b31b21c9ecb60,(more! 0xe2a68506699ea16df1362b80,0xe25b6b32e8b69f680fb9ef00,(more! 0x346bfab50f720666fe4fbe00,0x341a05cafb5b4cd0a1833900,(last! 0x154a49e1c04c962d1a1b420,0x14fba46f98e3b39c91db740))))) (by decide +kernel) (by decide +kernel)

private theorem r8 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 8 295 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3014,12,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x543edcda1d566dc135683a0e0,0x54491f3524dc614a39c7d83c0,(more! 0xe21f769caa896fc0cbfdf260,0xe1d293f3a0adda9e6c303b60,(more! 0x320233daa8735ba9300da280,0x31b1843047253eded75af700,(last! 0x1323bb123138f0d03352d20,0x12ddab28a1499999d06b3c0))))) (by decide +kernel) (by decide +kernel)

private theorem r9 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 9 285 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3042,13,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x546f58d2c7d910c764f676980,0x54799addb6c4168f4f41fcec0,(more! 0xe19f5ccd00d1d428fb6aa420,0xe150c63d7cf379e101332400,(more! 0x2fa7ab384675c8886cb36a80,0x2f582039b7d04289e672ff80,(last! 0x104dc158138e770aaa77700,0x1010f471563dde88fb13ba0))))) (by decide +kernel) (by decide +kernel)

private theorem r10 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 10 274 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3075,14,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x549fc237adb35989bf7527800,0x54aa03e7dfb84099b2126f060,(more! 0xe1237a4518cc58f2d016fd80,0xe0d342e60023e42c45277f20,(more! 0x2d554a378bc3a720923d61e0,0x2d06c54d028bca0c63b2fa80,(last! 0xcc4ca5f1efa46620c8b060,0xc92032644e97388e9b2620))))) (by decide +kernel) (by decide +kernel)

private theorem r11 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 11 262 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3114,16,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x54d07bc60effa5a13ff830080,0x54dabcefeccc06089b6d82940,(more! 0xe0a7faf9d07934cfabbf6a40,0xe056341ef7d98d84c2793080,(more! 0x2b046725f826a5d598d007c0,0x2ab6ce5ea9b70b08ddb9aae0,(last! 0x8d97617287586b6e14d860,0x8b16b10491a7e5a2cbc780))))) (by decide +kernel) (by decide +kernel)

private theorem r12 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 12 248 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3094,15,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x54fe7e5be5cab8d6fbed3db60,0x5508bef475ce088885127a620,(more! 0xe0364139b4e4fa0eef9a9b00,0xdfe310c031d5adc16a9aa5e0,(more! 0x28cf64dd889a124c28a75ba0,0x288291b043fa398d39e83e80,(last! 0x545b38c0e537c46de7fd40,0x52879e84905a21882f8640))))) (by decide +kernel) (by decide +kernel)

private theorem r13 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 13 232 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 3027,12,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x552a03f5246c8f1376a8f1e80,0x553443dae1243357d55c11de0,(more! 0xdfcc0f5a765c5adf07e41e00,0xdf7798b33d44f0f719a1c940,(more! 0x26ae0e81162156dd284deac0,0x2661e3c42381f305f1aa8ba0,(last! 0x28111adbad6066066a9c40,0x26e6711582c0de2f543b40))))) (by decide +kernel) (by decide +kernel)

private theorem r14 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 14 213 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2969,10,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x5550b74574e061fd0cd23e7c0,0x555af693cc894300d6b60aee0,(more! 0xdf751cc1acf359d359aef240,0xdf1f94ea339cd9894bdff500,(more! 0x24b485c1b0c33ae7b2453a80,0x2468df6f64c72c58fc6ee180,(last! 0xcd03c24723ff547a14880,0xc3bb9a7fa926a8c74d420))))) (by decide +kernel) (by decide +kernel)

private theorem r15 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 15 192 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2919,8,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x557559dd5d0a2ccb856c1cea0,0x557f98733c4c80b06f7cac360,(more! 0xdf24d3c4598a86dcc9a0cf00,0xdece576c95bdfbe10dda6240,(more! 0x22c62971f011ee92ef056580,0x227b139e647694ea41be2360,(last! 0x175be13ae7828f8a383c0,0x150c2ac02d2189047d220))))) (by decide +kernel) (by decide +kernel)

private theorem r16 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 16 168 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2875,6,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x5595f0863acc796f5c0c81b40,0x55a02e7f9fa89969af92a7cc0,(more! 0xdee6993837202a61fdc170a0,0xde8f559f655052ef8e110320,(more! 0x20fbc96373fc0e9fa019c5a0,0x20b15f870fb00f6e697dfc80,(last! 0,0))))) (by decide +kernel) (by decide +kernel)

private theorem r17 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 17 142 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2837,4,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x55b4bfc3ae5b206f566b55580,0x55befd0b6d070ee2a72621700,(more! 0xdeaf1da3a3a52ee2fa93cca0,0xde5728f0e5c45c1164c5e240,(more! 0x1f4643e07babeaa18043a220,0x1efc96325e464e5fa3e25980,(last! 0,0))))) (by decide +kernel) (by decide +kernel)

private theorem r18 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 18 114 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2802,3,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x55d1c5d573762ba43c342b060,0x55dc025ec2b982e50bee4ef40,(more! 0xde7ec01fae18acc197451be0,0xde262dd276964a2f3c827360,(more! 0x1da6a42cbe02d7025fc419c0,0x1d5da006167b5276aad156c0,(last! 0,0))))) (by decide +kernel) (by decide +kernel)

private theorem r19 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 19 83 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2771,2,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x55eb8ba025b9456069c3764c0,0x55f5c78d21b30f9ea334698c0,(more! 0xde5f490654e8b1bc75db9a80,0xde063c20399ec8d586e357e0,(more! 0x1c2951b07be382ac926481c0,0x1be0d1d95054d73cb5f39380,(last! 0,0))))) (by decide +kernel) (by decide +kernel)

private theorem r20 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 20 50 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2744,1,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x5603d9bf6db386bf3f3784140,0x560e150934e648f518ac2e400,(more! 0xde467f696f865d318eb3c2e0,0xdded057cb7bb4e7c9083f9c0,(more! 0x1abd231fc28c1426be6dbe80,0x1a751a7d1ba474d7fd6bae00,(last! 0,0))))) (by decide +kernel) (by decide +kernel)

private theorem r21 {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 21 15 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=2570) (first:=start .h2570) (by decide) (by decide) hl hh
    (values! 2719,16,0x65940dda2fc1d46593918b600,0x659410c85f076d8aa23a29500,(more! 0x561aba7f0a48d46b113e33b80,0x5624f52329a7e1340ae767fe0,(more! 0xde3467c17d84a379853a06c0,0xddda8befde311b6744b207e0,(last! 0x196154c3a7b7fff26fea1ec0,0x1919b86175bae4aa9e3741a0)))) (by decide +kernel) (by decide +kernel)

theorem none {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    debit h (terminal .h2570) < jointGain h (terminal .h2570).shape
      (threshold .h2570 Option.none) 0:=r0 hl hh

theorem all {h : ℕ} (hl : start .h2570 ≤ h) (hh : h < 131071) :
    GradeChecks (terminal .h2570) h 1 (grades .h2570) :=
  ⟨r1 hl hh,r2 hl hh,r3 hl hh,r4 hl hh,r5 hl hh,r6 hl hh,r7 hl hh,r8 hl hh,r9 hl hh,r10 hl hh,r11 hl hh,r12 hl hh,r13 hl hh,r14 hl hh,r15 hl hh,r16 hl hh,r17 hl hh,r18 hl hh,r19 hl hh,r20 hl hh,r21 hl hh,trivial⟩
end h2570

namespace h8100
local notation "S" => (⟨124,173,32,804⟩:Shape)
local notation "N" => 0xc4fd80000
local notation "P" => 0x15c66e5
private theorem r0 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 9 0 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 52,1,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15d56c956a66b78a0,0x15d5730dd88dbc440)) (by decide +kernel) (by decide +kernel)

private theorem r1 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 1 26 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 63,1,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cc8dab9462fd4a0,0x15cc93dc3ce311f40)) (by decide +kernel) (by decide +kernel)

private theorem r2 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 2 25 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 65,2,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15ce17390c5ce6040,0x15ce1d76250a4e380)) (by decide +kernel) (by decide +kernel)

private theorem r3 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 3 23 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 67,2,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cd50ed489bfd0c0,0x15cd57241bfa974e0)) (by decide +kernel) (by decide +kernel)

private theorem r4 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 4 21 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 71,2,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cdc414572f491a0,0x15cdca4ec97c383a0)) (by decide +kernel) (by decide +kernel)

private theorem r5 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 5 18 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 67,2,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cdc834b1104f5a0,0x15cdce6f4a6dc5e80)) (by decide +kernel) (by decide +kernel)

private theorem r6 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 6 14 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 61,1,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15ce48f36e7600fa0,0x15ce4f32197c27b00)) (by decide +kernel) (by decide +kernel)

private theorem r7 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 7 8 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 57,1,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cd748e55297e4a0,0x15cd7ac649ba49340)) (by decide +kernel) (by decide +kernel)

private theorem r8 {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h ⟨S,N,P⟩ < jointGain h S 8 1 :=
  High6960High55Arithmetic.terminal_transfer_of_values
    (b:=⟨S,N,P⟩) (lo:=8100) (first:=start .h8100) (by decide) (by decide) hl hh
    (values! 54,1,0x15cc5ac0210a8ed00,0x15cc5dc271fa78640,(last! 0x15cd3291d48e370a0,0x15cd38c7b33c10a40)) (by decide +kernel) (by decide +kernel)

theorem none {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    debit h (terminal .h8100) < jointGain h (terminal .h8100).shape
      (threshold .h8100 Option.none) 0:=r0 hl hh

theorem all {h : ℕ} (hl : start .h8100 ≤ h) (hh : h < 131071) :
    GradeChecks (terminal .h8100) h 1 (grades .h8100) :=
  ⟨r1 hl hh,r2 hl hh,r3 hl hh,r4 hl hh,r5 hl hh,r6 hl hh,r7 hl hh,r8 hl hh,trivial⟩
end h8100

theorem terminal_bounds (b : Band) {h : ℕ} (hl : start b ≤ h)
    (hu:h≤finish b) (x:Test b) :
    debit h (tested b x) <
      jointGain h (tested b x).shape (threshold b x) (seedThreshold b x):=by
  have hh:h < 131071:=hu.trans_lt (by cases b <;> decide)
  cases x with
  | none =>
    cases b
    · exact h2570.none hl hh
    · exact h8100.none hl hh
  | some i =>
    have hc : GradeChecks (terminal b) h 1 (grades b) := by
      cases b
      · exact h2570.all hl hh
      · exact h8100.all hl hh
    exact grade_at _ _ _ _ hc i

#print axioms terminal_bounds
end High6960High55Terminal
