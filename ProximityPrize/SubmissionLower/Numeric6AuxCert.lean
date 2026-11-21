import ProximityPrize.SubmissionLower.Numeric6Defs
import ProximityPrize.SubmissionLower.Fast055
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_1
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
private def l1v0 : List Lane := [⟨9,10,1,1,1⟩,⟨8,8,4,31,0x7effffebfbfffb5bf7ff817feff6de9⟩,⟨7,7,6,31,0x3f7ffff4fefffd92fdffc0bdfbfbb727f7c89defedcbb9b⟩,⟨6,6,8,31,0x7effffb9fbfff0d5fbfe7087efe4f32fdea4f15fb250db7f0f639d7bfba293⟩,⟨5,5,10,31,0x3f7fffe87efffabffdff7243fbf639bff780ee67eaf0511fb5f2a13e9c423d78ca81165d1e5393⟩,⟨4,4,12,31,0x7effff87fbffe4c3f7fd0b57efca7997ed388f1fa319023e8b5f4bf83ec789566a705f2a37cb104b38a5817e80d12⟩,⟨3,3,14,31,0x3f7fffdbfefff788fdff0d8dfbee5a5ff70f22cfe5f81eaf8911091d4af50a7060ab29aeccf5088a11373e1e20e3d716d2fd16862b68a⟩,⟨2,2,16,31,0x7effff55fbffd71dfbfb487fefa571e7eb08199f898dfd5ddb64a2f0f0102426219e401795b02cef97773a3dd7ff2d2e2a52fc80ad4fc999b9cff517d1b6⟩,⟨1,1,18,31,0x3f7fffcf7efff3edfdfe9043fbe392c7f664bc4fdde1051f3a12403acc530c5f501bcec97100828499b3c908e9e1e31d51bf3824860e8fc4536cb9b7f1c85dae5a2c5d2dc736⟩,⟨0,0,20,31,0x7effff23fbffc7ebf7f91eafef73aa1fd7d40bbf610fc27c00e554e37fe1c145f69ddfccad573edd68f572465daecf9543eb984895d04f95e3f3bd8356d8becafe23c02dbf874289b75d9e7eace⟩]
private def l1v1 : List Lane := [⟨9,9,1,1,1⟩,⟨8,8,4,30,0xfe000004000000d000002bc0000640⟩,⟨7,7,6,17,0x2001a00a902db4934575c0⟩,⟨6,6,8,30,0xfe0000080000028fe00083c00011d30001c9080023fdc0024f48c01f9e06⟩,⟨5,5,10,25,0x40000370001730006660014cb8034fcb06df920be86611809ed610f43⟩,⟨4,4,12,31,0x7f0000060000011c00001ed000022e47f01cfe40012d86c009f7608046695080a6ba260887190c263447409557ff4⟩,⟨3,3,14,30,0xc0000058000013b00002de10004e4e400685fe00711288066407704ea15ec3418be41e048120f23fdb16b730866a094c62⟩,⟨2,2,16,31,0x7f000008000001a9fc0030f00003abb7f03394200235631fd3a92c00920d45829adae213a4e41a593f2ec1845e3ebd82947bf21df01c147f7b5086d3378c⟩,⟨1,1,18,31,0x20000007d00000ee0000126800010a68000bbe08006b8be00335be0014dd5300750759c23c7006099cf258248798e87b31fa5873bbcb5fe11c7afd48610e33c03c4dc⟩,⟨0,0,20,31,0x7f00000a00000244000047280005ac000054958003d70a002436f0011ce3600772b2dc2b087b30d9013223c2faa80ec7b49a93e6db0de20e52574401239d687a434fd7b0174baf602e933a0f4bc⟩]
private def z1 : CJ1.Block where
  bank := .leftHigh
  cap := 108
  free := [(9,0),(9,1)]
  vectors := [l1v0,l1v1].map (vectorData true 36 16)
private def b1 := bands [(34,36,1),(33,34,3),(32,32,5),(31,31,6),(30,30,7),(29,29,8),(28,28,9),(27,27,10),(26,26,10),(25,25,10),(24,24,9),(23,23,8),(22,22,7),(21,21,6),(20,20,5),(19,19,4),(18,18,3),(17,17,2),(16,16,1)]
private theorem k1v0 : good true 36 l1v0 b1 := rfl
private theorem v1j0 : CJ6.VectorDots 36 16 z1 0 := v! true, 36, b1, l1v0, k1v0
private theorem k1v1 : good true 36 l1v1 b1 := rfl
private theorem v1j1 : CJ6.VectorDots 36 16 z1 1 := v! true, 36, b1, l1v1, k1v1
theorem r1 : (CJ0.blockMatrix CJ6.source 36 ((16 : ℤ)-20)).rank ≤ 108 :=
  (CJ6.block_rank_le 36 16).trans (CJ6.rank_of_dots (z := z1) (by decide) (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v1j0) v1j1))
private def l2v0 : List Lane := [⟨9,0,0,0,0⟩,⟨8,9,3,31,0x1262e0dfd6a1780f80000001⟩,⟨7,7,6,31,0x63449b03542108463bd9e1c312948e4fdffe92d6082ffc⟩,⟨6,6,8,31,0x8d2e5f4a03c81960be06fbe40b89c6c354200a20830d77aa809d7448b467ed⟩,⟨5,5,10,31,0x3c8bac26f74776c6664303eda78b143576614e7c5a4cdc7b857942ed4ef0c1fad9a3f73711ca4a⟩,⟨4,4,12,31,0x49d21aae10dc1bd2c32a8bc549d34217e21e8440d116c8333437aa6e91ba4b83d542d02543cc46146de65184f427b⟩,⟨3,3,14,31,0x240627628db55c0e5bb466a000a13c75e7828c7c87a2604c60655c9370f21e443b0a12369a0f5ffa6cee50edf50734809c5e58a183294⟩,⟨2,2,16,31,0xc702392df2dc6cf54dbab904f5ff4c6e0b09c214c2071e52e98dbc20d9b24dbdb185e7784d3d1466e5cc5c88605a9e23f0246d4336d28862a2902a855bf0⟩,⟨1,1,18,31,0x3ba3bb653c30e9a82a3a6db703abe42a71375891d4c1c3bafbfbf3e9b8aa931819349afd14abc1f400a1a7cdc5ca87394171dbf684f737f6bb12132fd091d8cafac4ebed320f⟩,⟨0,0,20,31,0x8bebac0cc5db1e850acb639b6aa0e5a8e86a0f86b5249ce9df66dcddb995c2ecd0b63b511e257b6aa766ebc1dbd1acf9ad34f0f387960a57d94678707e7a7203c5cc776845dfd7923831ac5aa9⟩]
private def l2v1 : List Lane := [⟨9,0,0,0,0⟩,⟨8,8,4,31,0xe53bc1b5cdd51f24000000000000001⟩,⟨7,7,6,31,0x1e60757ee3a2303be5e45e08a3def7f2fa0002fecf96706⟩,⟨6,6,8,31,0xb8d23cd74858d4daad658962abd89fc87318e5291d8724a7059fbff1470066⟩,⟨5,5,10,31,0x294b3d91c160d29989377b55cf0613d247a20bfade2502c83eae98f5195f1e4d3784e878e1e09f⟩,⟨4,4,12,31,0x3e92024ad046110f12541b69d0629ef08ff4c116f9b9de96886d93f2b6f9b19aafc3666cc16fe9178aab443dcf51d⟩,⟨3,3,14,31,0x20c058392cb7c613aec65243054fabf8c230146c9b4615b31a37169688cdec30eb592278ef98766602ae8cffd6a219b578f6d694c0366⟩,⟨2,2,16,31,0x747b1212b78c4fa28576698e26cce18c16e592f3325d1e0359063fca8117933f97b5c87f89f4eab08f90c17023526032b518d1cfc60e5675f4d7f06fe3e3⟩,⟨1,1,18,31,0x4bfc5753a22e9a1022b0b8b0d00281557e0eb67987c99f30776d381918d1e1d584809003833a033f14d6ed07a4868e0f3829d32bcd6cc0771937b06aa0a4b33250369d621be⟩,⟨0,0,20,31,0x5c8d6c2d501b0c74f4f3062c51da346e83172d71e0cd419935750487755a8b2b9bdd9be9dde96e690d3ebe7cb10c0d46d5cf6b7523513d1fa105b7d817dd956bc0c0246209ffed9d3d73f9c25c0⟩]
private def l2v2 : List Lane := [⟨9,10,1,1,1⟩,⟨8,10,2,31,0x1eb9ce745a210847⟩,⟨7,7,6,31,0x31294a585e39cf77395af19d68861068001bc567afbd586⟩,⟨6,6,8,31,0xdd39ceb3063198d3d73b17d800170c1dd4d6602e6429ffaf98ae2987e5cf69⟩,⟨5,5,10,31,0x31294a71b95add22937c8bad99b985ae2dcc4652d7e3b3555c5808d962212449fb95e85dae00ba⟩,⟨4,4,12,31,0x7ae73a9deb9d139506364fc189a109a18de2dfce8845186698e03f3e38d42465b33b9f325ccbe9370cc0c98d1ada7⟩,⟨3,3,14,31,0x4d3d73ae1f08337280d52b92cfb85ab69f401edc21c0e3c7aaab6312ff050dbce9fd282f236025da7f1e3b9cbc156b80d3f7313⟩,⟨2,2,16,31,0x51ef7d90d508a5d7129ff6a800d7cc100be0f78084051f04b54877a44ac2e3f0ce322d7a6f5390048fd7f6d59827a04499b61891df25d4b20ef10058bbdc⟩,⟨1,1,18,31,0x1cad6beb9894c78a312d4e458998f520046f654032629801d52a380e61d0682185868dbecc50fca5b1a3eba5a63918a5944a0d136fc9b318b9eb07744a69af05e3502c66a40e⟩,⟨0,0,20,31,0x6252978e72b6640b5436fef7b02dd0ac63eb8c0129ee7a0b157ec058d5d5806756cb446e4be8944684cb6e1549454edfb3197e32bf52054ba14a739342764bf82e1315154048958593db44106d2⟩]
private def l2v3 : List Lane := [⟨9,9,1,1,1⟩,⟨8,10,2,31,0x283318c6a24f7bdf⟩,⟨7,7,6,31,0x3ebb5ad7106318bca1d2939947bddc56f9fef05c18b9b81⟩,⟨6,6,8,31,0x106318c578e7395b89630c4af9ff2118f625c708b4249cf7ccf47b9d8fb145⟩,⟨5,5,10,31,0x36cb5ad622d29468f3c20a143128d6fae1654e528f3af3955e4134c4079b07107586f630b0ca13⟩,⟨4,4,12,31,0x614c6313c4b18ac578e70cdb3357a4a9272f8b24bad335ed00531465f12759937248bb06ef6ca7d09db152f3a85bb⟩,⟨3,3,14,31,0x27affffde04630ecf9e72809917a94459db4629c59906c636e180bed1ccb95b8cce2642ba64322d7ef71f45434899735ed135c473e197⟩,⟨2,2,16,31,0x95884202147bdb5bebb5441ef1f82697ef91638fdb332b07c435a74e0ecb2536c558464c85df747bc66f4a66e54d2d6fcc221d43538a7115e8166381e4ea⟩,⟨1,1,18,31,0x11694a4df2b5ac2ee56b35a53757fdb7f7d6deffee2cc3dfcf02a6ff3abf9e7bfdcd0aea60df5d933142ae10bcff440e7ebe82bf23a40f430aa0a0e274d440dd6f35cd9c160f⟩,⟨0,0,20,31,0xad16b595042522ba4deeb12418b63c89b9ea21dfb53dd83f1989e6fbcaffdd68f0b04479c9dd4d3de21e8b15445729de8696f46a3bf90eb1c7e7c5eac475922dcec916f7039981d37aa0aa0a718⟩]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 106
  free := [(8,2),(8,3),(9,0),(9,1)]
  vectors := [l2v0,l2v1,l2v2,l2v3].map (vectorData true 37 15)
private def b2 := bands [(34,36,2),(33,34,4),(32,32,6),(31,31,7),(30,30,8),(29,29,9),(28,28,10),(27,27,10),(26,26,10),(25,25,9),(24,24,8),(23,23,7),(22,22,6),(21,21,5),(20,20,4),(19,19,3),(18,18,2),(17,17,1)]
private theorem k2v0 : good true 37 l2v0 b2 := rfl
private theorem v2j0 : CJ6.VectorDots 37 15 z2 0 := v! true, 37, b2, l2v0, k2v0
private theorem k2v1 : good true 37 l2v1 b2 := rfl
private theorem v2j1 : CJ6.VectorDots 37 15 z2 1 := v! true, 37, b2, l2v1, k2v1
private theorem k2v2 : good true 37 l2v2 b2 := rfl
private theorem v2j2 : CJ6.VectorDots 37 15 z2 2 := v! true, 37, b2, l2v2, k2v2
private theorem k2v3 : good true 37 l2v3 b2 := rfl
private theorem v2j3 : CJ6.VectorDots 37 15 z2 3 := v! true, 37, b2, l2v3, k2v3
theorem r2 : (CJ0.blockMatrix CJ6.source 37 ((15 : ℤ)-20)).rank ≤ 106 :=
  (CJ6.block_rank_le 37 15).trans (CJ6.rank_of_dots (z := z2) (by decide) (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc (CJ6.belowSucc CJ6.belowZero v2j0) v2j1) v2j2) v2j3))
private def l3v0 : List Lane := [⟨9,9,1,1,1⟩,⟨8,8,3,9,276319⟩,⟨7,7,5,15,0x1003805e86664ffb⟩,⟨6,6,7,19,0x4000e8019601c8c1731ce7f1f3f8c⟩,⟨5,5,9,23,0x100003c0006cc007ee006b0d045954243dbcf882c594efd⟩,⟨4,4,11,26,0x1000007c0001d1000463c007ae900a5edc0b3c190a07f1c785f554ce792ea4c2a5⟩,⟨3,3,13,28,0x1000002000001f000013600008c7800312a000dd3d00335be00a07f1c1abfda03d860f07b0c1e0d755348⟩,⟨2,2,15,30,0x1000000840000210000055400009fd8000e7c60010e6700104bec00d3dafc0931f2f05845e902e248b41526152888a74da30ce0970⟩,⟨1,1,17,31,0x100000044000008c40000bb00000b52800087de0005216200290b1001150aac0640af701f436d30886c0b020af37f86e9fd1214bdf736374fe890045dc855⟩,⟨0,0,19,31,0x400000118000025300003322000332200027a0c0018c47800cd3750059c833021ab1320af1330431bcb958c6f2e562bff90440b47c567852f5befcbf665d483ae4d01075c9a0⟩]
private def z3 : CJ1.Block where
  bank := .leftHigh
  cap := 99
  free := [(9,0)]
  vectors := [l3v0].map (vectorData true 38 15)
private def b3 := bands [(35,37,2),(34,35,4),(33,33,6),(32,32,7),(31,31,8),(30,30,9),(29,29,10),(28,28,10),(27,27,10),(26,26,9),(25,25,8),(24,24,7),(23,23,6),(22,22,5),(21,21,4),(20,20,3),(19,19,2),(18,18,1)]
private theorem k3v0 : good true 38 l3v0 b3 := rfl
private theorem v3j0 : CJ6.VectorDots 38 15 z3 0 := v! true, 38, b3, l3v0, k3v0
theorem r3 : (CJ0.blockMatrix CJ6.source 38 ((15 : ℤ)-20)).rank ≤ 99 :=
  (CJ6.block_rank_le 38 15).trans (CJ6.rank_of_dots (z := z3) (by decide) (CJ6.belowSucc CJ6.belowZero v3j0))
end CJ6_1
end
section
namespace CJ6_1
theorem proof : CJ6.c1 := ⟨r1, r2, r3, trivial⟩
end CJ6_1
end
section
namespace K1_13_2_3_6
open K1_13_2 K1_13_2_3
open scoped BigOperators
private def decode (code : ℕ) : Powers :=
  ⟨code % 2048, code / 2048 % 1024, code / 2097152 % 1024⟩
private def runLength (code : ℕ) : ℕ := code / 2147483648 + 1
private def rowLength : List ℕ → ℕ
  | [] => 0
  | code :: tail => runLength code + rowLength tail
private def rowPower (k : ℕ) : List ℕ → Powers
  | [] => ⟨0, 0, 0⟩
  | code :: tail =>
    if k < runLength code then decode code else rowPower (k - runLength code) tail
private def sumFrom (f : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFrom f j n + f (j + n)
private theorem sumFrom_eq (f : ℕ → ℕ) (j n : ℕ) :
    sumFrom f j n = ∑ k ∈ Finset.range n, f (j + k) := by
  induction n with
  | zero => simp [sumFrom]
  | succ n ih => rw [sumFrom, Finset.sum_range_succ, ih]
private def runValue (s j code : ℕ) : ℕ :=
  if code % 2147483648 = 0 then 0
  else sumFrom (fun u => blockSaving s u (decode code)) j (runLength code)
private theorem runValue_eq (s j code : ℕ) :
    runValue s j code = ∑ k ∈ Finset.range (runLength code),
      blockSaving s (j + k) (decode code) := by
  unfold runValue
  split
  · rename_i h
    have hz : decode code = ⟨0, 0, 0⟩ := by
      unfold decode
      congr <;> omega
    simp [hz, blockSaving_zero]
  · exact sumFrom_eq _ _ _
private def rowValue (s j : ℕ) : List ℕ → ℕ
  | [] => 0
  | code :: tail => runValue s j code + rowValue s (j + runLength code) tail
private theorem rowValue_eq (s j : ℕ) (row : List ℕ) :
    rowValue s j row = ∑ k ∈ Finset.range (rowLength row),
      blockSaving s (j + k) (rowPower k row) := by
  induction row generalizing j with
  | nil => simp [rowValue, rowLength]
  | cons code tail ih =>
    rw [rowValue, runValue_eq, ih, rowLength, Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      simp [rowPower, Finset.mem_range.mp hk]
    · apply Finset.sum_congr rfl
      intro k hk
      simp (disch := omega) [rowPower, add_assoc]
private def rowStart (s : ℕ) : ℕ := max 23 (3333 - s)
def value (s : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | row :: tail => rowValue s (rowStart s) row + value (s + 1) tail
def fits (s : ℕ) : List (List ℕ) → Bool
  | [] => true
  | row :: tail =>
    decide (rowStart s + rowLength row ≤ 409 ∧ s + rowStart s + rowLength row ≤ 3797)
      && fits (s + 1) tail
theorem value_append (s : ℕ) (a b : List (List ℕ)) :
    value s (a ++ b) = value s a + value (s + a.length) b := by
  induction a generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    simp only [List.cons_append, value, List.length_cons, ih, add_assoc, Nat.add_comm 1 tail.length]
theorem fits_append (s : ℕ) (a b : List (List ℕ)) :
    fits s (a ++ b) = (fits s a && fits (s + a.length) b) := by
  induction a generalizing s with
  | nil => simp [fits]
  | cons row tail ih =>
    simp only [List.cons_append, fits, List.length_cons, ih, Bool.and_assoc]
    rw [show s + 1 + tail.length = s + (tail.length + 1) by omega]
private theorem rows_eq (s : ℕ) (rows : List (List ℕ)) :
    value s rows = ∑ k ∈ Finset.range rows.length,
      rowValue (s + k) (rowStart (s + k)) (rows[k]?.getD []) := by
  induction rows generalizing s with
  | nil => simp [value]
  | cons row tail ih =>
    rw [value, List.length_cons, Finset.sum_range_succ', ih]
    simp only [add_zero, List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show s + 1 + k = s + (k + 1) by omega]
private theorem fit_row (s : ℕ) (rows : List (List ℕ)) (h : fits s rows = true)
    (k : ℕ) (hk : k < rows.length) :
    rowStart (s + k) + rowLength (rows[k]?.getD []) ≤ 409 ∧
      s + k + rowStart (s + k) + rowLength (rows[k]?.getD []) ≤ 3797 := by
  induction rows generalizing s k with
  | nil => simp at hk
  | cons row tail ih =>
    have hs := Bool.and_eq_true_iff.mp h
    cases k with
    | zero => simpa using (of_decide_eq_true hs.1)
    | succ k =>
      have he : s + (k + 1) = s + 1 + k := by omega
      simpa only [Nat.succ_eq_add_one, he, List.getElem?_cons_succ] using
        ih (s + 1) hs.2 k (by simpa using hk)
private def wrap (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩
private theorem wrap_val (n : ℕ) (hn : 0 < n) (i : Fin n) : wrap n hn i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt
private theorem sum_wrap (n : ℕ) (hn : 0 < n) (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = ∑ j ∈ Finset.range n, f (wrap n hn j) := by
  simpa only [wrap_val] using
    (Fin.sum_univ_eq_sum_range (fun j => f (wrap n hn j)) n)
private theorem sum_subinterval (f : ℕ → ℕ) {a b n : ℕ} (h : a + b ≤ n) :
    (∑ j ∈ Finset.range b, f (a + j)) ≤ ∑ j ∈ Finset.range n, f j := by
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun _ _ _ => Nat.zero_le _))
  rw [Finset.sum_range_add]
  exact Nat.le_add_left _ _
theorem value_le_savingsSum (start : ℕ) (rows : List (List ℕ))
    (hstart : 3012 ≤ start) (hend : start + rows.length ≤ 3514)
    (hfit : fits start rows = true) :
    ∃ p : BlockIndex → Powers, value start rows ≤ savingsSum w3 p := by
  let p : BlockIndex → Powers := fun i =>
    rowPower (i.2.val - rowStart i.1.val) (rows[i.1.val - start]?.getD [])
  refine ⟨p, ?_⟩
  unfold savingsSum
  rw [← Finset.univ_product_univ, Finset.sum_product, sum_wrap 4013 (by decide), rows_eq]
  apply le_trans _ (sum_subinterval _ (show start + rows.length ≤ 4013 by omega))
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  let s := start + k
  let row := rows[k]?.getD []
  have hs : 3012 ≤ s ∧ s < 3514 := by dsimp [s]; omega
  have hf := fit_row start rows hfit k hk'
  change rowStart s + rowLength row ≤ 409 ∧ s + rowStart s + rowLength row ≤ 3797 at hf
  rw [sum_wrap 4650 (by decide), rowValue_eq]
  apply le_trans _ (sum_subinterval _ (show rowStart s + rowLength row ≤ 4650 by omega))
  apply Finset.sum_le_sum
  intro k' hk'
  have hlt := Finset.mem_range.mp hk'
  change k' < rowLength row at hlt
  let j := rowStart s + k'
  have hj : j < 4650 := by dsimp [j]; omega
  let i : BlockIndex := (wrap 4013 (by decide) s, wrap 4650 (by decide) j)
  have his : i.1.val = s := Nat.mod_eq_of_lt (by omega)
  have hij : i.2.val = j := Nat.mod_eq_of_lt hj
  have hw : w3.Contains i := by
    change 3012 ≤ i.1.val ∧ i.1.val < 3514 ∧ 23 ≤ i.2.val ∧ i.2.val ≤ 408 ∧
      3333 ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ 3796
    rw [his, hij]
    have h₁ : 23 ≤ rowStart s := le_max_left _ _
    have h₂ : 3333 - s ≤ rowStart s := le_max_right _ _
    dsimp [j]
    omega
  have hp : p i = rowPower k' row := by
    dsimp only [p]
    rw [his, hij]
    have he : s - start = k := by dsimp [s]; omega
    simp only [he, j, Nat.add_sub_cancel_left, row]
  change blockSaving s j (rowPower k' row) ≤ if w3.Contains i then savings i (p i) else 0
  rw [ite_eq_left hw, hp, ← his, ← hij, blockSaving_eq i _ hw]
end K1_13_2_3_6
end
