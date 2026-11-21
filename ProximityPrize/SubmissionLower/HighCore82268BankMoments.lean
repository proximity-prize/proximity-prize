import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option maxRecDepth 18000

namespace HighCore82268BankMoments

open P1_7_1_3 (momentEstimate blockEstimate block_append)
open P1_7_1_3_2 (CheckedBlocks)
open private block_total from ProximityPrize.SubmissionLower.UpperBranch1

set_option maxHeartbeats 4000000

namespace M6714_1410

private def block0 : List (ℕ × ℕ) := [⟨220,0x2be4c51a1⟩, ⟨220,0x12818b3ba5⟩, ⟨220,0x3074b0b009⟩, ⟨220,0x5af4dacbcd⟩, ⟨220,0x905f27abf1⟩, ⟨220,0xcf10b56d75⟩, ⟨220,0x114f4ff0942⟩, ⟨220,0x159cc304d06⟩, ⟨220,0x197cb3d9d16⟩, ⟨220,0x1cecb40d2a6⟩]
private theorem part0 : blockEstimate 6714 1410 1410 2200 = 0x7d570ede886 := by
  have h : CheckedBlocks 6714 1410 1410 block0 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 6714) (J := 1410) block0 1410 h

private def block1 : List (ℕ × ℕ) := [⟨220,0x1fecc39edb6⟩, ⟨220,0x227ce28ee46⟩, ⟨220,0x249d10dd456⟩, ⟨220,0x264d4e89fe6⟩, ⟨220,0x278d9b950f6⟩, ⟨220,0x285df7fe786⟩, ⟨220,0x28be63c6396⟩, ⟨220,0x28aedeec526⟩, ⟨220,0x282f6970c36⟩, ⟨220,0x274003538c6⟩]
private theorem part1 : blockEstimate 6714 1410 3610 2200 = 0x17e1c489f66c := by
  have h : CheckedBlocks 6714 1410 3610 block1 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 6714) (J := 1410) block1 3610 h

private def block2 : List (ℕ × ℕ) := [⟨220,0x25e0ac94ad6⟩, ⟨220,0x24116534266⟩, ⟨220,0x21d22d31f76⟩, ⟨220,0x1f23048e206⟩, ⟨220,0x1c0d9aef13e⟩, ⟨220,0x18ccd37e6e1⟩, ⟨220,0x15838cecb60⟩, ⟨220,0x12437f339ef⟩, ⟨220,0xf1d5915c55⟩, ⟨220,0xc20c416c93⟩]
private theorem part2 : blockEstimate 6714 1410 5810 2200 = 0x102c6db4350e := by
  have h : CheckedBlocks 6714 1410 5810 block2 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 6714) (J := 1410) block2 5810 h

private def block3 : List (ℕ × ℕ) := [⟨220,0x95b431dfda⟩, ⟨220,0x6d762ef90d⟩, ⟨220,0x4aa7d45ef3⟩, ⟨220,0x2de813031f⟩, ⟨220,0x17b9d17c81⟩, ⟨220,0x89ff66209⟩, ⟨204,0x11d4e7177⟩]
private theorem part3 : blockEstimate 6714 1410 8010 1524 = 0x19d315e8afa := by
  have h : CheckedBlocks 6714 1410 8010 block3 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 6714) (J := 1410) block3 8010 h

private theorem join1 : blockEstimate 6714 1410 1410 4400 = 0x1fb73577def2 :=
  block_append part0 part1 rfl rfl rfl

private theorem join2 : blockEstimate 6714 1410 1410 6600 = 0x2fe3a32c1400 :=
  block_append join1 part2 rfl rfl rfl

private theorem join3 : blockEstimate 6714 1410 1410 8124 = 0x3180d48a9efa :=
  block_append join2 part3 rfl rfl rfl

theorem proof : momentEstimate 6714 1410 = 0x3180d48a9efa := join3

end M6714_1410

namespace M8413_1776

private def block0 : List (ℕ × ℕ) := [⟨220,0x374794475⟩, ⟨220,0x1772ecf4e9⟩, ⟨220,0x3dd79534fd⟩, ⟨220,0x74ff9021b1⟩, ⟨220,0xbb47fbd805⟩, ⟨220,0x10f0df674f9⟩, ⟨220,0x16eae9e158d⟩, ⟨220,0x1d88710d6c1⟩, ⟨220,0x248d18db0be⟩, ⟨220,0x2b3c5696bd2⟩]
private theorem part0 : blockEstimate 8413 1776 1776 2200 = 0xadbe123e5e8 := by
  have h : CheckedBlocks 8413 1776 1776 block0 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 8413) (J := 1776) block0 1776 h

private def block1 : List (ℕ × ℕ) := [⟨220,0x315e9ebea22⟩, ⟨220,0x36f3ed02cf2⟩, ⟨220,0x3bfc4163442⟩, ⟨220,0x40779be0012⟩, ⟨220,0x4465fc79062⟩, ⟨220,0x47c7632e532⟩, ⟨220,0x4a9bcfffe82⟩, ⟨220,0x4ce342edc52⟩, ⟨220,0x4e9dbbf7ea2⟩, ⟨220,0x4fcb3b1e572⟩]
private theorem part1 : blockEstimate 8413 1776 3976 2200 = 0x2a6dbd2affe4 := by
  have h : CheckedBlocks 8413 1776 3976 block1 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 8413) (J := 1776) block1 3976 h

private def block2 : List (ℕ × ℕ) := [⟨220,0x506bc0610c2⟩, ⟨220,0x507f4bc0092⟩, ⟨220,0x5005dd3b4e2⟩, ⟨220,0x4eff74d2db2⟩, ⟨220,0x4d6c1286b02⟩, ⟨220,0x4b4bb656cd2⟩, ⟨220,0x489e6043322⟩, ⟨220,0x4564104bdf2⟩, ⟨220,0x419cc670d42⟩, ⟨220,0x3d4882b2112⟩]
private theorem part2 : blockEstimate 8413 1776 6176 2200 = 0x2e58fe0beb24 := by
  have h : CheckedBlocks 8413 1776 6176 block2 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 8413) (J := 1776) block2 6176 h

private def block3 : List (ℕ × ℕ) := [⟨220,0x3870fc56770⟩, ⟨220,0x335b94711c1⟩, ⟨220,0x2e32e5faca1⟩, ⟨220,0x290929ac799⟩, ⟨220,0x23efb637324⟩, ⟨220,0x1ef712dbfb8⟩, ⟨220,0x1a2ef76bf87⟩, ⟨220,0x15a64c4810a⟩, ⟨220,0x1166e75959c⟩, ⟨220,0xd7da7f3f3e⟩]
private theorem part3 : blockEstimate 8413 1776 8376 2200 = 0x154a93c835b2 := by
  have h : CheckedBlocks 8413 1776 8376 block3 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 8413) (J := 1776) block3 8376 h

private def block4 : List (ℕ × ℕ) := [⟨220,0xa02f4b9e37⟩, ⟨220,0x6ff85e6132⟩, ⟨220,0x47b89e1f1f⟩, ⟨220,0x27f2f16eee⟩, ⟨220,0x112a3ee78f⟩, ⟨220,0x3e16d1ff2⟩, ⟨69,0xe9512bf⟩]
private theorem part4 : blockEstimate 8413 1776 10576 1389 = 0x194ed7aa7b6 := by
  have h : CheckedBlocks 8413 1776 10576 block4 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 8413) (J := 1776) block4 10576 h

private theorem join1 : blockEstimate 8413 1776 1776 4400 = 0x35499e4ee5cc :=
  block_append part0 part1 rfl rfl rfl

private theorem join2 : blockEstimate 8413 1776 1776 6600 = 0x63a29c5ad0f0 :=
  block_append join1 part2 rfl rfl rfl

private theorem join3 : blockEstimate 8413 1776 1776 8800 = 0x78ed302306a2 :=
  block_append join2 part3 rfl rfl rfl

private theorem join4 : blockEstimate 8413 1776 1776 10189 = 0x7a821d9dae58 :=
  block_append join3 part4 rfl rfl rfl

theorem proof : momentEstimate 8413 1776 = 0x7a821d9dae58 := join4

end M8413_1776

namespace M9027_1904

private def block0 : List (ℕ × ℕ) := [⟨220,0x3b64f599d⟩, ⟨220,0x193c3880f1⟩, ⟨220,0x42ae063a65⟩, ⟨220,0x7e68d6a2f9⟩, ⟨220,0xcac9c7d7ad⟩, ⟨220,0x1262df7f581⟩, ⟨220,0x18ef2851975⟩, ⟨220,0x203748d6089⟩, ⟨220,0x281f25f6a92⟩, ⟨220,0x302524c00b6⟩]
private theorem part0 : blockEstimate 9027 1904 1904 2200 = 0xbe5ace26a60 := by
  have h : CheckedBlocks 9027 1904 1904 block0 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9027) (J := 1904) block0 1904 h

private def block1 : List (ℕ × ℕ) := [⟨220,0x37a16a02966⟩, ⟨220,0x3e868dc5696⟩, ⟨220,0x44d49008846⟩, ⟨220,0x4a8b70cbe76⟩, ⟨220,0x4fab300f926⟩, ⟨220,0x5433cdd3856⟩, ⟨220,0x58254a17c06⟩, ⟨220,0x5b7fa4dc436⟩, ⟨220,0x5e42de210e6⟩, ⟨220,0x606ef5e6216⟩]
private theorem part1 : blockEstimate 9027 1904 4104 2200 = 0x31bbdb97ab6c := by
  have h : CheckedBlocks 9027 1904 4104 block1 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9027) (J := 1904) block1 4104 h

private def block2 : List (ℕ × ℕ) := [⟨220,0x6203ec2b7c6⟩, ⟨220,0x6301c0f11f6⟩, ⟨220,0x636874370a6⟩, ⟨220,0x633805fd3d6⟩, ⟨220,0x62707643b86⟩, ⟨220,0x6111c50a7b6⟩, ⟨220,0x5f1bf251866⟩, ⟨220,0x5c8efe18d96⟩, ⟨220,0x596ae860746⟩, ⟨220,0x55afb128576⟩]
private theorem part2 : blockEstimate 9027 1904 6304 2200 = 0x3b9edec9242c := by
  have h : CheckedBlocks 9027 1904 6304 block2 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9027) (J := 1904) block2 6304 h

private def block3 : List (ℕ × ℕ) := [⟨220,0x515d5870826⟩, ⟨220,0x4c73de38f56⟩, ⟨220,0x46f79852f21⟩, ⟨220,0x4126d690cb7⟩, ⟨220,0x3b3b13264f8⟩, ⟨220,0x35479ae05cc⟩, ⟨220,0x2f5e1465f85⟩, ⟨220,0x298f64de595⟩, ⟨220,0x23ebaff0da3⟩, ⟨220,0x1e8257c4a13⟩]
private theorem part3 : blockEstimate 9027 1904 8504 2200 = 0x231cdd48dae8 := by
  have h : CheckedBlocks 9027 1904 8504 block3 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9027) (J := 1904) block3 8504 h

private def block4 : List (ℕ × ℕ) := [⟨220,0x1961fd014d5⟩, ⟨220,0x1490d4e6fb1⟩, ⟨220,0x10220eacea5⟩, ⟨220,0xc2b7d00109⟩, ⟨220,0x8b55094927⟩, ⟨220,0x5c7b7d3def⟩, ⟨220,0x36ae127651⟩, ⟨220,0x1a6faf893d⟩, ⟨220,0x8433b0da3⟩, ⟨151,0x9dc5e770⟩]
private theorem part4 : blockEstimate 9027 1904 10704 2131 = 0x5e5d522cfeb := by
  have h : CheckedBlocks 9027 1904 10704 block4 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9027) (J := 1904) block4 10704 h

private theorem join1 : blockEstimate 9027 1904 1904 4400 = 0x3da1887a15cc :=
  block_append part0 part1 rfl rfl rfl

private theorem join2 : blockEstimate 9027 1904 1904 6600 = 0x7940674339f8 :=
  block_append join1 part2 rfl rfl rfl

private theorem join3 : blockEstimate 9027 1904 1904 8800 = 0x9c5d448c14e0 :=
  block_append join2 part3 rfl rfl rfl

private theorem join4 : blockEstimate 9027 1904 1904 10931 = 0xa24319aee4cb :=
  block_append join3 part4 rfl rfl rfl

theorem proof : momentEstimate 9027 1904 = 0xa24319aee4cb := join4

end M9027_1904

namespace M9602_2029

private def block0 : List (ℕ × ℕ) := [⟨220,0x3f3f6e581⟩, ⟨220,0x1ae8782a05⟩, ⟨220,0x4735cd76e9⟩, ⟨220,0x873914e92d⟩, ⟨220,0xd94f6c9dd1⟩, ⟨220,0x13bd5f2b1d5⟩, ⟨220,0x1ad29c54239⟩, ⟨220,0x22ba8026bfd⟩, ⟨220,0x2b5adc84c21⟩, ⟨220,0x3482664fdea⟩]
private theorem part0 : blockEstimate 9602 2029 2029 2200 = 0xcd916a5b783 := by
  have h : CheckedBlocks 9602 2029 2029 block0 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block0 2029 h

private def block1 : List (ℕ × ℕ) := [⟨220,0x3d6530a7396⟩, ⟨220,0x45a77d10c06⟩, ⟨220,0x4d48bd4c376⟩, ⟨220,0x5448f1599e6⟩, ⟨220,0x5aa81938f56⟩, ⟨220,0x606634ea3c6⟩, ⟨220,0x6583446d736⟩, ⟨220,0x69ff47c29a6⟩, ⟨220,0x6dda3ee9b16⟩, ⟨220,0x711429e2b86⟩]
private theorem part1 : blockEstimate 9602 2029 4229 2200 = 0x38e1d9f7d78c := by
  have h : CheckedBlocks 9602 2029 4229 block1 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block1 4229 h

private def block2 : List (ℕ × ℕ) := [⟨220,0x73ad08adaf6⟩, ⟨220,0x75a4db4a966⟩, ⟨220,0x76fba1b96d6⟩, ⟨220,0x77b15bfa346⟩, ⟨220,0x77c60a0ceb6⟩, ⟨220,0x7739abf1926⟩, ⟨220,0x760c41a8296⟩, ⟨220,0x743dcb30b06⟩, ⟨220,0x71ce488b276⟩, ⟨220,0x6ebdb9b78e6⟩]
private theorem part2 : blockEstimate 9602 2029 6429 2200 = 0x491d4a6c5f4c := by
  have h : CheckedBlocks 9602 2029 6429 block2 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block2 6429 h

private def block3 : List (ℕ × ℕ) := [⟨220,0x6b0c1eb5e56⟩, ⟨220,0x66b977862c6⟩, ⟨220,0x61c5c428636⟩, ⟨220,0x5c31049c8a6⟩, ⟨220,0x55fee16d477⟩, ⟨220,0x4f6df7ff749⟩, ⟨220,0x48bd50a3e28⟩, ⟨220,0x4200c52617b⟩, ⟨220,0x3b4a23b4ddd⟩, ⟨220,0x34aa84e9805⟩]
private theorem part3 : blockEstimate 9602 2029 8629 2200 = 0x32fdbf6d613d := by
  have h : CheckedBlocks 9602 2029 8629 block3 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block3 8629 h

private def block4 : List (ℕ × ℕ) := [⟨220,0x2e324bc7925⟩, ⟨220,0x27f125bd446⟩, ⟨220,0x21f60aa2a00⟩, ⟨220,0x1c4dde0fb96⟩, ⟨220,0x16fbddc0130⟩, ⟨220,0x121e4be51a2⟩, ⟨220,0xdc2db9065e⟩, ⟨220,0x9f1bb2b654⟩, ⟨220,0x6b3191f874⟩, ⟨220,0x40f23d63ae⟩]
private theorem part4 : blockEstimate 9602 2029 10829 2200 = 0xdff8578dea7 := by
  have h : CheckedBlocks 9602 2029 10829 block4 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block4 10829 h

private def block5 : List (ℕ × ℕ) := [⟨220,0x20e09b8ef2⟩, ⟨220,0xb7f931130⟩, ⟨191,0x1510ccdd0⟩]
private theorem part5 : blockEstimate 9602 2029 13029 631 = 0x2db13b6df2 := by
  have h : CheckedBlocks 9602 2029 13029 block5 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 9602) (J := 2029) block5 13029 h

private theorem join1 : blockEstimate 9602 2029 2029 4400 = 0x45baf09d8f0f :=
  block_append part0 part1 rfl rfl rfl

private theorem join2 : blockEstimate 9602 2029 2029 6600 = 0x8ed83b09ee5b :=
  block_append join1 part2 rfl rfl rfl

private theorem join3 : blockEstimate 9602 2029 2029 8800 = 0xc1d5fa774f98 :=
  block_append join2 part3 rfl rfl rfl

private theorem join4 : blockEstimate 9602 2029 2029 11000 = 0xcfd57ff02e3f :=
  block_append join3 part4 rfl rfl rfl

private theorem join5 : blockEstimate 9602 2029 2029 11631 = 0xd003312b9c31 :=
  block_append join4 part5 rfl rfl rfl

theorem proof : momentEstimate 9602 2029 = 0xd003312b9c31 := join5

end M9602_2029

namespace M10182_2152

private def block0 : List (ℕ × ℕ) := [⟨220,0x43227b0f1⟩, ⟨220,0x1c987124b5⟩, ⟨220,0x4bc7aa77d9⟩, ⟨220,0x901cf1c75d⟩, ⟨220,0xe7f5653041⟩, ⟨220,0x151ae22cf85⟩, ⟨220,0x1cba448c229⟩, ⟨220,0x25434f5252d⟩, ⟨220,0x2e9bd461591⟩, ⟨220,0x38a91923629⟩]
private theorem part0 : blockEstimate 10182 2152 2152 2200 = 0xdca7ad347b2 := by
  have h : CheckedBlocks 10182 2152 2152 block0 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block0 2152 h

private def block1 : List (ℕ × ℕ) := [⟨220,0x42f58f2c3e0⟩, ⟨220,0x4cb0fe0a400⟩, ⟨220,0x55c19eaa4a0⟩, ⟨220,0x5e27710c5c0⟩, ⟨220,0x65e27530760⟩, ⟨220,0x6cf2ab16980⟩, ⟨220,0x735812bec20⟩, ⟨220,0x7912ac28f40⟩, ⟨220,0x7e2277552e0⟩, ⟨220,0x82877443700⟩]
private theorem part1 : blockEstimate 10182 2152 4352 2200 = 0x4037967b4860 := by
  have h : CheckedBlocks 10182 2152 4352 block1 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block1 4352 h

private def block2 : List (ℕ × ℕ) := [⟨220,0x8641a2f3ba0⟩, ⟨220,0x895103660c0⟩, ⟨220,0x8bb5959a660⟩, ⟨220,0x8d6f5990c80⟩, ⟨220,0x8e7e4f49320⟩, ⟨220,0x8ee276c3a40⟩, ⟨220,0x8e9bd0001e0⟩, ⟨220,0x8daa5afea00⟩, ⟨220,0x8c0e17bf2a0⟩, ⟨220,0x89c70641bc0⟩]
private theorem part2 : blockEstimate 10182 2152 6552 2200 = 0x57833a4916e0 := by
  have h : CheckedBlocks 10182 2152 6552 block2 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block2 6552 h

private def block3 : List (ℕ × ℕ) := [⟨220,0x86d52686560⟩, ⟨220,0x8338788cf80⟩, ⟨220,0x7ef0fc55a20⟩, ⟨220,0x79feb1e0540⟩, ⟨220,0x7461992d0e0⟩, ⟨220,0x6e19b23bd00⟩, ⟨220,0x672980748b3⟩, ⟨220,0x5fccf459c28⟩, ⟨220,0x584b168d678⟩, ⟨220,0x50b8e0b4c65⟩]
private theorem part3 : blockEstimate 10182 2152 8752 2200 = 0x4557304c29d8 := by
  have h : CheckedBlocks 10182 2152 8752 block3 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block3 8752 h

private def block4 : List (ℕ × ℕ) := [⟨220,0x492848fcb2b⟩, ⟨220,0x41aa9a5b4c3⟩, ⟨220,0x3a507490b48⟩, ⟨220,0x3329cc27c32⟩, ⟨220,0x2c45ea74daa⟩, ⟨220,0x25b36d967fe⟩, ⟨220,0x1f7a6ff46a8⟩, ⟨220,0x19a4c76eb60⟩, ⟨220,0x1451e48b7eb⟩, ⟨220,0xf8b0ab0834⟩]
private theorem part4 : blockEstimate 10182 2152 10952 2200 = 0x1a742a2baf37 := by
  have h : CheckedBlocks 10182 2152 10952 block4 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block4 10952 h

private def block5 : List (ℕ × ℕ) := [⟨220,0xb58684732b⟩, ⟨220,0x7c22bb8fc0⟩, ⟨220,0x4d0836f4e3⟩, ⟨220,0x28b9dd3984⟩, ⟨220,0xfba94f493⟩, ⟨220,0x28d44bd00⟩, ⟨14,0x2fd316⟩]
private theorem part5 : blockEstimate 10182 2152 13152 1334 = 0x1b9b35db5fb := by
  have h : CheckedBlocks 10182 2152 13152 block5 :=
    ⟨(by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), (by decide +kernel), trivial⟩
  exact block_total (B := 10182) (J := 2152) block5 13152 h

private theorem join1 : blockEstimate 10182 2152 2152 4400 = 0x4e02114e9012 :=
  block_append part0 part1 rfl rfl rfl

private theorem join2 : blockEstimate 10182 2152 2152 6600 = 0xa5854b97a6f2 :=
  block_append join1 part2 rfl rfl rfl

private theorem join3 : blockEstimate 10182 2152 2152 8800 = 0xeadc7be3d0ca :=
  block_append join2 part3 rfl rfl rfl

private theorem join4 : blockEstimate 10182 2152 2152 11000 = 0x10550a60f8001 :=
  block_append join3 part4 rfl rfl rfl

private theorem join5 : blockEstimate 10182 2152 2152 12334 = 0x1070a596d35fc :=
  block_append join4 part5 rfl rfl rfl

theorem proof : momentEstimate 10182 2152 = 0x1070a596d35fc := join5

end M10182_2152

end HighCore82268BankMoments
