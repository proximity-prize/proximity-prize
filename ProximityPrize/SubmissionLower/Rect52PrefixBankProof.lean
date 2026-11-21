import ProximityPrize.SubmissionLower.Rect52PrefixSource

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Rect52PrefixBankProof

open P3_7_1 (BankOK checked)
open P1_7_1 (groupedPoleMoment)
open P1_7_1_3 (momentEstimate blockEstimate block_append)
open Rect52Prefix

set_option maxHeartbeats 6000000

local notation "pass!" depth "," grade "," deriv "," nodes "," moment ";" witness =>
  checked _ (m := depth) (B := grade) (J := deriv) (N := nodes) (M := moment)
    rfl rfl rfl rfl rfl (by decide) (by decide) rfl (by decide) witness

private theorem part (B J s n v : ℕ) (h : blockEstimate B J s n = v) :
    blockEstimate B J s n = v := h

private theorem append {B J s t a b x y : ℕ}
    (lo : blockEstimate B J s a = x) (hi : blockEstimate B J t b = y) (next : s+a=t) :
    blockEstimate B J s (a+b) = x+y :=
  block_append lo hi next rfl rfl
private def c0 := part 8648 1834 1834 160 0x16191dba8 (by decide +kernel)
private def c1 := part 8648 1834 1994 160 0x9695e54a8 (by decide +kernel)
private def c2 := part 8648 1834 2154 160 0x1900590da8 (by decide +kernel)
private def c3 := part 8648 1834 2314 160 0x2fb15206a8 (by decide +kernel)
private def c4 := part 8648 1834 2474 160 0x4d07193fa8 (by decide +kernel)
private def c5 := part 8648 1834 2634 160 0x708c7eb8a8 (by decide +kernel)
private def c6 := part 8648 1834 2794 160 0x99cc5271a8 (by decide +kernel)
private def c7 := part 8648 1834 2954 160 0xc851646aa8 (by decide +kernel)
private def c8 := part 8648 1834 3114 160 0xfba684a3a8 (by decide +kernel)
private def c9 := part 8648 1834 3274 160 0x13356831ca8 (by decide +kernel)
private def c10 := part 8648 1834 3434 160 0x16eec2fd5a8 (by decide +kernel)
private def c11 := part 8648 1834 3594 160 0x1adc7b5a89e (by decide +kernel)
private def c12 := part 8648 1834 3754 160 0x1ec49fd43f0 (by decide +kernel)
private def c13 := part 8648 1834 3914 160 0x22767ec5ff0 (by decide +kernel)
private def c14 := part 8648 1834 4074 160 0x25f05dc7bf0 (by decide +kernel)
private def c15 := part 8648 1834 4234 160 0x29323cd97f0 (by decide +kernel)
private def c16 := part 8648 1834 4394 160 0x2c3c1bfb3f0 (by decide +kernel)
private def c17 := part 8648 1834 4554 160 0x2f0dfb2cff0 (by decide +kernel)
private def c18 := part 8648 1834 4714 160 0x31a7da6ebf0 (by decide +kernel)
private def c19 := part 8648 1834 4874 160 0x3409b9c07f0 (by decide +kernel)
private def c20 := part 8648 1834 5034 160 0x363399223f0 (by decide +kernel)
private def c21 := part 8648 1834 5194 160 0x38257893ff0 (by decide +kernel)
private def c22 := part 8648 1834 5354 160 0x39df5815bf0 (by decide +kernel)
private def c23 := part 8648 1834 5514 160 0x3b6137a77f0 (by decide +kernel)
private def c24 := part 8648 1834 5674 160 0x3cab17493f0 (by decide +kernel)
private def c25 := part 8648 1834 5834 160 0x3dbcf6faff0 (by decide +kernel)
private def c26 := part 8648 1834 5994 160 0x3e96d6bcbf0 (by decide +kernel)
private def c27 := part 8648 1834 6154 160 0x3f38b68e7f0 (by decide +kernel)
private def c28 := part 8648 1834 6314 160 0x3fa296703f0 (by decide +kernel)
private def c29 := part 8648 1834 6474 160 0x3fd47661ff0 (by decide +kernel)
private def c30 := part 8648 1834 6634 160 0x3fce5663bf0 (by decide +kernel)
private def c31 := part 8648 1834 6794 160 0x3f9036757f0 (by decide +kernel)
private def c32 := part 8648 1834 6954 160 0x3f1a16973f0 (by decide +kernel)
private def c33 := part 8648 1834 7114 160 0x3e6bf6c8ff0 (by decide +kernel)
private def c34 := part 8648 1834 7274 160 0x3d85d70abf0 (by decide +kernel)
private def c35 := part 8648 1834 7434 160 0x3c67b75c7f0 (by decide +kernel)
private def c36 := part 8648 1834 7594 160 0x3b1197be3f0 (by decide +kernel)
private def c37 := part 8648 1834 7754 160 0x3983782fff0 (by decide +kernel)
private def c38 := part 8648 1834 7914 160 0x37bd58b1bf0 (by decide +kernel)
private def c39 := part 8648 1834 8074 160 0x35bf39437f0 (by decide +kernel)
private def c40 := part 8648 1834 8234 160 0x338919e53f0 (by decide +kernel)
private def c41 := part 8648 1834 8394 160 0x311afa96ff0 (by decide +kernel)
private def c42 := part 8648 1834 8554 160 0x2e75516a2c6 (by decide +kernel)
private def c43 := part 8648 1834 8714 160 0x2ba925b4aa7 (by decide +kernel)
private def c44 := part 8648 1834 8874 160 0x28ceac76753 (by decide +kernel)
private def c45 := part 8648 1834 9034 160 0x25ec669d5d8 (by decide +kernel)
private def c46 := part 8648 1834 9194 160 0x23076fae52a (by decide +kernel)
private def c47 := part 8648 1834 9354 160 0x2024ba4ec5a (by decide +kernel)
private def c48 := part 8648 1834 9514 160 0x1d491044fda (by decide +kernel)
private def c49 := part 8648 1834 9674 160 0x1a791278616 (by decide +kernel)
private def c50 := part 8648 1834 9834 160 0x17b938f0a14 (by decide +kernel)
private def c51 := part 8648 1834 9994 160 0x150dd2d6bd3 (by decide +kernel)
private def c52 := part 8648 1834 10154 160 0x127b0673e00 (by decide +kernel)
private def c53 := part 8648 1834 10314 160 0x1004d13284d (by decide +kernel)
private def c54 := part 8648 1834 10474 160 0xdab2c97d3d (by decide +kernel)
private def c55 := part 8648 1834 10634 160 0xb73bd7c40c (by decide +kernel)
private def c56 := part 8648 1834 10794 160 0x96758a814c (by decide +kernel)
private def c57 := part 8648 1834 10954 160 0x7884ae228c (by decide +kernel)
private def c58 := part 8648 1834 11114 160 0x5d8de1a7cc (by decide +kernel)
private def c59 := part 8648 1834 11274 160 0x45b5c4110c (by decide +kernel)
private def c60 := part 8648 1834 11434 160 0x3120f45e4c (by decide +kernel)
private def c61 := part 8648 1834 11594 160 0x1ff4118f8c (by decide +kernel)
private def c62 := part 8648 1834 11754 160 0x1253baa4cc (by decide +kernel)
private def c63 := part 8648 1834 11914 160 0x8648e9e0c (by decide +kernel)
private def c64 := part 8648 1834 12074 160 0x24b2c7b4c (by decide +kernel)
private def c65 := part 8648 1834 12234 82 0x18e46735 (by decide +kernel)
private def a0 := append c0 c1 rfl
private def a1 := append c2 c3 rfl
private def a2 := append a0 a1 rfl
private def a3 := append c4 c5 rfl
private def a4 := append c6 c7 rfl
private def a5 := append a3 a4 rfl
private def a6 := append a2 a5 rfl
private def a7 := append c8 c9 rfl
private def a8 := append c10 c11 rfl
private def a9 := append a7 a8 rfl
private def a10 := append c12 c13 rfl
private def a11 := append c14 c15 rfl
private def a12 := append a10 a11 rfl
private def a13 := append a9 a12 rfl
private def a14 := append a6 a13 rfl
private def a15 := append c16 c17 rfl
private def a16 := append c18 c19 rfl
private def a17 := append a15 a16 rfl
private def a18 := append c20 c21 rfl
private def a19 := append c22 c23 rfl
private def a20 := append a18 a19 rfl
private def a21 := append a17 a20 rfl
private def a22 := append c24 c25 rfl
private def a23 := append c26 c27 rfl
private def a24 := append a22 a23 rfl
private def a25 := append c28 c29 rfl
private def a26 := append c31 c32 rfl
private def a27 := append c30 a26 rfl
private def a28 := append a25 a27 rfl
private def a29 := append a24 a28 rfl
private def a30 := append a21 a29 rfl
private def a31 := append a14 a30 rfl
private def a32 := append c33 c34 rfl
private def a33 := append c35 c36 rfl
private def a34 := append a32 a33 rfl
private def a35 := append c37 c38 rfl
private def a36 := append c39 c40 rfl
private def a37 := append a35 a36 rfl
private def a38 := append a34 a37 rfl
private def a39 := append c41 c42 rfl
private def a40 := append c43 c44 rfl
private def a41 := append a39 a40 rfl
private def a42 := append c45 c46 rfl
private def a43 := append c47 c48 rfl
private def a44 := append a42 a43 rfl
private def a45 := append a41 a44 rfl
private def a46 := append a38 a45 rfl
private def a47 := append c49 c50 rfl
private def a48 := append c51 c52 rfl
private def a49 := append a47 a48 rfl
private def a50 := append c53 c54 rfl
private def a51 := append c55 c56 rfl
private def a52 := append a50 a51 rfl
private def a53 := append a49 a52 rfl
private def a54 := append c57 c58 rfl
private def a55 := append c59 c60 rfl
private def a56 := append a54 a55 rfl
private def a57 := append c61 c62 rfl
private def a58 := append c64 c65 rfl
private def a59 := append c63 a58 rfl
private def a60 := append a57 a59 rfl
private def a61 := append a56 a60 rfl
private def a62 := append a53 a61 rfl
private def a63 := append a46 a62 rfl
private def a64 := append a31 a63 rfl

private theorem moment8648_1834 : momentEstimate 8648 1834 = 0x8944c1334160 := a64
private def c66 := part 97 21 21 118 0x284e2c (by decide +kernel)

private theorem moment97_21 : momentEstimate 97 21 = 0x284e2c := c66
private def c67 := part 530 111 111 160 0x1094bc1c (by decide +kernel)
private def c68 := part 530 111 271 160 0x371fe780 (by decide +kernel)
private def c69 := part 530 111 431 160 0x2e3e2330 (by decide +kernel)
private def c70 := part 530 111 591 160 0x9a2e2c8 (by decide +kernel)
private def c71 := part 530 111 751 1 530 (by decide +kernel)
private def a65 := append c67 c68 rfl
private def a66 := append c70 c71 rfl
private def a67 := append c69 a66 rfl
private def a68 := append a65 a67 rfl

private theorem moment530_111 : momentEstimate 530 111 = 0x7f95aba6 := a68
private def c72 := part 107 23 23 130 0x3ae575 (by decide +kernel)

private theorem moment107_23 : momentEstimate 107 23 = 0x3ae575 := c72
private def c73 := part 558 116 116 160 0x11d7b273 (by decide +kernel)
private def c74 := part 558 116 276 160 0x3e7a1820 (by decide +kernel)
private def c75 := part 558 116 436 160 0x3a4be090 (by decide +kernel)
private def c76 := part 558 116 596 160 0x10fecfac (by decide +kernel)
private def c77 := part 558 116 756 34 0x1ed4b5 (by decide +kernel)
private def a69 := append c73 c74 rfl
private def a70 := append c76 c77 rfl
private def a71 := append c75 a70 rfl
private def a72 := append a69 a71 rfl

private theorem moment558_116 : momentEstimate 558 116 = 0x9bbb4f84 := a72
private def c78 := part 115 25 25 140 0x4ed4ac (by decide +kernel)

private theorem moment115_25 : momentEstimate 115 25 = 0x4ed4ac := c78
private def c79 := part 675 142 142 160 0x17025f00 (by decide +kernel)
private def c80 := part 675 142 302 160 0x61c26580 (by decide +kernel)
private def c81 := part 675 142 462 160 0x78e37d80 (by decide +kernel)
private def c82 := part 675 142 622 160 0x4d4fc5d3 (by decide +kernel)
private def c83 := part 675 142 782 160 0x10af689a (by decide +kernel)
private def c84 := part 675 142 942 17 350525 (by decide +kernel)
private def a73 := append c80 c81 rfl
private def a74 := append c79 a73 rfl
private def a75 := append c83 c84 rfl
private def a76 := append c82 a75 rfl
private def a77 := append a74 a76 rfl

private theorem moment675_142 : momentEstimate 675 142 = 0x14facc9aa := a77
private def c85 := part 126 27 27 153 0x6fafa5 (by decide +kernel)

private theorem moment126_27 : momentEstimate 126 27 = 0x6fafa5 := c85
private def c86 := part 745 155 155 160 0x19f0c6b1 (by decide +kernel)
private def c87 := part 745 155 315 160 0x776902e0 (by decide +kernel)
private def c88 := part 745 155 475 160 0xa2da1ae0 (by decide +kernel)
private def c89 := part 745 155 635 160 0x826f64cb (by decide +kernel)
private def c90 := part 745 155 795 160 0x32fc934b (by decide +kernel)
private def c91 := part 745 155 955 100 0x3a0fcb4 (by decide +kernel)
private def a78 := append c87 c88 rfl
private def a79 := append c86 a78 rfl
private def a80 := append c90 c91 rfl
private def a81 := append c89 a80 rfl
private def a82 := append a79 a81 rfl

private theorem moment745_155 : momentEstimate 745 155 = 0x1ed40d93b := a82
private def c92 := part 147 32 32 160 0xcdec95 (by decide +kernel)
private def c93 := part 147 32 192 19 99195 (by decide +kernel)
private def a83 := append c92 c93 rfl

private theorem moment147_32 : momentEstimate 147 32 = 0xcf7010 := a83
private def c94 := part 791 166 166 160 0x1bd924c8 (by decide +kernel)
private def c95 := part 791 166 326 160 0x86f13322 (by decide +kernel)
private def c96 := part 791 166 486 160 0xc291b500 (by decide +kernel)
private def c97 := part 791 166 646 160 0xaca9c908 (by decide +kernel)
private def c98 := part 791 166 806 160 0x566cc4fe (by decide +kernel)
private def c99 := part 791 166 966 157 0xe338304 (by decide +kernel)
private def a84 := append c95 c96 rfl
private def a85 := append c94 a84 rfl
private def a86 := append c98 c99 rfl
private def a87 := append c97 a86 rfl
private def a88 := append a85 a87 rfl

private theorem moment791_166 : momentEstimate 791 166 = 0x276a61df4 := a88
private def c100 := part 166 37 37 160 0x144d580 (by decide +kernel)
private def c101 := part 166 37 197 43 0x1062e5 (by decide +kernel)
private def a89 := append c100 c101 rfl

private theorem moment166_37 : momentEstimate 166 37 = 0x1553865 := a89
private def c102 := part 933 196 196 160 0x21bc2908 (by decide +kernel)
private def c103 := part 933 196 356 160 0xb6029d95 (by decide +kernel)
private def c104 := part 933 196 516 160 0x12b30a5d0 (by decide +kernel)
private def c105 := part 933 196 676 160 0x1408851d0 (by decide +kernel)
private def c106 := part 933 196 836 160 0xf675a0ae (by decide +kernel)
private def c107 := part 933 196 996 160 0x74b4c3a9 (by decide +kernel)
private def c108 := part 933 196 1156 160 0x15077bf4 (by decide +kernel)
private def c109 := part 933 196 1316 9 88292 (by decide +kernel)
private def a90 := append c102 c103 rfl
private def a91 := append c104 c105 rfl
private def a92 := append a90 a91 rfl
private def a93 := append c106 c107 rfl
private def a94 := append c108 c109 rfl
private def a95 := append a93 a94 rfl
private def a96 := append a92 a95 rfl

private theorem moment933_196 : momentEstimate 933 196 = 0x4c3aaf76c := a96
private def c110 := part 197 43 43 160 0x22952db (by decide +kernel)
private def c111 := part 197 43 203 80 0x6babeb (by decide +kernel)
private def a97 := append c110 c111 rfl

private theorem moment197_43 : momentEstimate 197 43 = 0x294fec6 := a97
private def c112 := part 1141 240 240 160 0x2a5b9f08 (by decide +kernel)
private def c113 := part 1141 240 400 160 0xf9a8a3dc (by decide +kernel)
private def c114 := part 1141 240 560 160 0x1d92235f0 (by decide +kernel)
private def c115 := part 1141 240 720 160 0x247d289f0 (by decide +kernel)
private def c116 := part 1141 240 880 160 0x240d5ddf0 (by decide +kernel)
private def c117 := part 1141 240 1040 160 0x1c4eea199 (by decide +kernel)
private def c118 := part 1141 240 1200 160 0xfff3c3c2 (by decide +kernel)
private def c119 := part 1141 240 1360 160 0x55b29be1 (by decide +kernel)
private def c120 := part 1141 240 1520 101 0x5da3f23 (by decide +kernel)
private def a98 := append c112 c113 rfl
private def a99 := append c114 c115 rfl
private def a100 := append a98 a99 rfl
private def a101 := append c116 c117 rfl
private def a102 := append c119 c120 rfl
private def a103 := append c118 a102 rfl
private def a104 := append a101 a103 rfl
private def a105 := append a100 a104 rfl

private theorem moment1141_240 : momentEstimate 1141 240 = 0xaa63e2113 := a105
private def c121 := part 235 50 50 160 0x36fd067 (by decide +kernel)
private def c122 := part 235 50 210 125 0x1a7dd5c (by decide +kernel)
private def a106 := append c121 c122 rfl

private theorem moment235_50 : momentEstimate 235 50 = 0x517adc3 := a106
private def c123 := part 1435 304 304 160 0x368bc848 (by decide +kernel)
private def c124 := part 1435 304 464 160 0x1524e8f9c (by decide +kernel)
private def c125 := part 1435 304 624 160 0x2e644bbd0 (by decide +kernel)
private def c126 := part 1435 304 784 160 0x40a11e7d0 (by decide +kernel)
private def c127 := part 1435 304 944 160 0x498f213d0 (by decide +kernel)
private def c128 := part 1435 304 1104 160 0x492e53fd0 (by decide +kernel)
private def c129 := part 1435 304 1264 160 0x3f7eb6bd0 (by decide +kernel)
private def c130 := part 1435 304 1424 160 0x2d86f0e60 (by decide +kernel)
private def c131 := part 1435 304 1584 160 0x19c486c0a (by decide +kernel)
private def c132 := part 1435 304 1744 160 0x9bbadf38 (by decide +kernel)
private def c133 := part 1435 304 1904 139 0x12e0f201 (by decide +kernel)
private def a107 := append c123 c124 rfl
private def a108 := append c126 c127 rfl
private def a109 := append c125 a108 rfl
private def a110 := append a107 a109 rfl
private def a111 := append c129 c130 rfl
private def a112 := append c128 a111 rfl
private def a113 := append c132 c133 rfl
private def a114 := append c131 a113 rfl
private def a115 := append a112 a114 rfl
private def a116 := append a110 a115 rfl

private theorem moment1435_304 : momentEstimate 1435 304 = 0x1ac0470697 := a116
private def c134 := part 285 64 64 160 0x58ebb60 (by decide +kernel)
private def c135 := part 285 64 224 160 0x5d06899 (by decide +kernel)
private def c136 := part 285 64 384 29 642052 (by decide +kernel)
private def a117 := append c135 c136 rfl
private def a118 := append c134 a117 rfl

private theorem moment285_64 : momentEstimate 285 64 = 0xb68effd := a118
private def c137 := part 1452 305 305 160 0x37403328 (by decide +kernel)
private def c138 := part 1452 305 465 160 0x15732069c (by decide +kernel)
private def c139 := part 1452 305 625 160 0x2f37e9af0 (by decide +kernel)
private def c140 := part 1452 305 785 160 0x4206c7ef0 (by decide +kernel)
private def c141 := part 1452 305 945 160 0x4b7f062f0 (by decide +kernel)
private def c142 := part 1452 305 1105 160 0x4ba0a46f0 (by decide +kernel)
private def c143 := part 1452 305 1265 160 0x426ba2af0 (by decide +kernel)
private def c144 := part 1452 305 1425 160 0x309aac1ac (by decide +kernel)
private def c145 := part 1452 305 1585 160 0x1c4addd79 (by decide +kernel)
private def c146 := part 1452 305 1745 160 0xb5fdc3c2 (by decide +kernel)
private def c147 := part 1452 305 1905 157 0x1b4610fc (by decide +kernel)
private def a119 := append c137 c138 rfl
private def a120 := append c140 c141 rfl
private def a121 := append c139 a120 rfl
private def a122 := append a119 a121 rfl
private def a123 := append c143 c144 rfl
private def a124 := append c142 a123 rfl
private def a125 := append c146 c147 rfl
private def a126 := append c145 a125 rfl
private def a127 := append a124 a126 rfl
private def a128 := append a122 a127 rfl

private theorem moment1452_305 : momentEstimate 1452 305 = 0x1bdaae9c57 := a128
private def c148 := part 287 64 64 160 0x59f7540 (by decide +kernel)
private def c149 := part 287 64 224 160 0x5ffd0de (by decide +kernel)
private def c150 := part 287 64 384 31 780032 (by decide +kernel)
private def a129 := append c149 c150 rfl
private def a130 := append c148 a129 rfl

private theorem moment287_64 : momentEstimate 287 64 = 0xbab2d1e := a130
private def c151 := part 1833 385 385 160 0x470bac88 (by decide +kernel)
private def c152 := part 1833 385 545 160 0x1c4a08988 (by decide +kernel)
private def c153 := part 1833 385 705 160 0x445d780e0 (by decide +kernel)
private def c154 := part 1833 385 865 160 0x6b5537b70 (by decide +kernel)
private def c155 := part 1833 385 1025 160 0x86c6ae770 (by decide +kernel)
private def c156 := part 1833 385 1185 160 0x967085370 (by decide +kernel)
private def c157 := part 1833 385 1345 160 0x9a52bbf70 (by decide +kernel)
private def c158 := part 1833 385 1505 160 0x926d52b70 (by decide +kernel)
private def c159 := part 1833 385 1665 160 0x7ec049770 (by decide +kernel)
private def c160 := part 1833 385 1825 160 0x60a626b1c (by decide +kernel)
private def c161 := part 1833 385 1985 160 0x3fec47c57 (by decide +kernel)
private def c162 := part 1833 385 2145 160 0x229153ae8 (by decide +kernel)
private def c163 := part 1833 385 2305 160 0xca30fce4 (by decide +kernel)
private def c164 := part 1833 385 2465 138 0x17d9d5d9 (by decide +kernel)
private def a131 := append c152 c153 rfl
private def a132 := append c151 a131 rfl
private def a133 := append c154 c155 rfl
private def a134 := append c156 c157 rfl
private def a135 := append a133 a134 rfl
private def a136 := append a132 a135 rfl
private def a137 := append c159 c160 rfl
private def a138 := append c158 a137 rfl
private def a139 := append c161 c162 rfl
private def a140 := append c163 c164 rfl
private def a141 := append a139 a140 rfl
private def a142 := append a138 a141 rfl
private def a143 := append a136 a142 rfl

private theorem moment1833_385 : momentEstimate 1833 385 = 0x46a696e4a8 := a143
private def c165 := part 362 80 80 160 0x8ee9654 (by decide +kernel)
private def c166 := part 362 80 240 160 0x1164ddb1 (by decide +kernel)
private def c167 := part 362 80 400 122 0x2d4b162 (by decide +kernel)
private def a144 := append c166 c167 rfl
private def a145 := append c165 a144 rfl

private theorem moment362_80 : momentEstimate 362 80 = 0x1d282567 := a145
private def c168 := part 2333 490 490 160 0x5bc61208 (by decide +kernel)
private def c169 := part 2333 490 650 160 0x254303f08 (by decide +kernel)
private def c170 := part 2333 490 810 160 0x5d6092c08 (by decide +kernel)
private def c171 := part 2333 490 970 160 0xa32183747 (by decide +kernel)
private def c172 := part 2333 490 1130 160 0xdfe8be640 (by decide +kernel)
private def c173 := part 2333 490 1290 160 0x10db453e40 (by decide +kernel)
private def c174 := part 2333 490 1450 160 0x12c83f9640 (by decide +kernel)
private def c175 := part 2333 490 1610 160 0x13c57aee40 (by decide +kernel)
private def c176 := part 2333 490 1770 160 0x13d2f74640 (by decide +kernel)
private def c177 := part 2333 490 1930 160 0x12f0b49e40 (by decide +kernel)
private def c178 := part 2333 490 2090 160 0x111eb2f640 (by decide +kernel)
private def c179 := part 2333 490 2250 160 0xe60459d86 (by decide +kernel)
private def c180 := part 2333 490 2410 160 0xb13522e34 (by decide +kernel)
private def c181 := part 2333 490 2570 160 0x7c8e9d30d (by decide +kernel)
private def c182 := part 2333 490 2730 160 0x4cd805ab6 (by decide +kernel)
private def c183 := part 2333 490 2890 160 0x2602f84d0 (by decide +kernel)
private def c184 := part 2333 490 3050 160 0xbe34afd0 (by decide +kernel)
private def c185 := part 2333 490 3210 103 0xcf3b7d4 (by decide +kernel)
private def a146 := append c168 c169 rfl
private def a147 := append c170 c171 rfl
private def a148 := append a146 a147 rfl
private def a149 := append c172 c173 rfl
private def a150 := append c175 c176 rfl
private def a151 := append c174 a150 rfl
private def a152 := append a149 a151 rfl
private def a153 := append a148 a152 rfl
private def a154 := append c177 c178 rfl
private def a155 := append c179 c180 rfl
private def a156 := append a154 a155 rfl
private def a157 := append c181 c182 rfl
private def a158 := append c184 c185 rfl
private def a159 := append c183 a158 rfl
private def a160 := append a157 a159 rfl
private def a161 := append a156 a160 rfl
private def a162 := append a153 a161 rfl

private theorem moment2333_490 : momentEstimate 2333 490 = 0xb9375c1e10 := a162
private def c186 := part 359 79 79 160 0x8c77704 (by decide +kernel)
private def c187 := part 359 79 239 160 0x10c749d9 (by decide +kernel)
private def c188 := part 359 79 399 118 0x28ed0d1 (by decide +kernel)
private def a163 := append c187 c188 rfl
private def a164 := append c186 a163 rfl

private theorem moment359_79 : momentEstimate 359 79 = 0x1c1d91ae := a164
private def c189 := part 1980 416 416 160 0x4d23c128 (by decide +kernel)
private def c190 := part 1980 416 576 160 0x1eed58a28 (by decide +kernel)
private def c191 := part 1980 416 736 160 0x4bfd4d258 (by decide +kernel)
private def c192 := part 1980 416 896 160 0x7bed0c8a0 (by decide +kernel)
private def c193 := part 1980 416 1056 160 0xa009178a0 (by decide +kernel)
private def c194 := part 1980 416 1216 160 0xb76b528a0 (by decide +kernel)
private def c195 := part 1980 416 1376 160 0xc213bd8a0 (by decide +kernel)
private def c196 := part 1980 416 1536 160 0xc002588a0 (by decide +kernel)
private def c197 := part 1980 416 1696 160 0xb137238a0 (by decide +kernel)
private def c198 := part 1980 416 1856 160 0x95b6b4659 (by decide +kernel)
private def c199 := part 1980 416 2016 160 0x70a3b1d16 (by decide +kernel)
private def c200 := part 1980 416 2176 160 0x4abb4d5e8 (by decide +kernel)
private def c201 := part 1980 416 2336 160 0x292592b13 (by decide +kernel)
private def c202 := part 1980 416 2496 160 0xfe4f1b78 (by decide +kernel)
private def c203 := part 1980 416 2656 156 0x2503fa39 (by decide +kernel)
private def a165 := append c190 c191 rfl
private def a166 := append c189 a165 rfl
private def a167 := append c192 c193 rfl
private def a168 := append c194 c195 rfl
private def a169 := append a167 a168 rfl
private def a170 := append a166 a169 rfl
private def a171 := append c196 c197 rfl
private def a172 := append c198 c199 rfl
private def a173 := append a171 a172 rfl
private def a174 := append c200 c201 rfl
private def a175 := append c202 c203 rfl
private def a176 := append a174 a175 rfl
private def a177 := append a173 a176 rfl
private def a178 := append a170 a177 rfl

private theorem moment1980_416 : momentEstimate 1980 416 = 0x602dc09b83 := a178
private def c204 := part 407 91 91 160 0xb10b1c9 (by decide +kernel)
private def c205 := part 407 91 251 160 0x1ac92e24 (by decide +kernel)
private def c206 := part 407 91 411 160 0x90640c8 (by decide +kernel)
private def c207 := part 407 91 571 18 245510 (by decide +kernel)
private def a179 := append c204 c205 rfl
private def a180 := append c206 c207 rfl
private def a181 := append a179 a180 rfl

private theorem moment407_91 : momentEstimate 407 91 = 0x2ee3dfbb := a181
private def c208 := part 2100 445 445 160 0x521d4a28 (by decide +kernel)
private def c209 := part 2100 445 605 160 0x21149f328 (by decide +kernel)
private def c210 := part 2100 445 765 160 0x520515b5b (by decide +kernel)
private def c211 := part 2100 445 925 160 0x89d9e5750 (by decide +kernel)
private def c212 := part 2100 445 1085 160 0xb63156350 (by decide +kernel)
private def c213 := part 2100 445 1245 160 0xd4ec66f50 (by decide +kernel)
private def c214 := part 2100 445 1405 160 0xe60b17b50 (by decide +kernel)
private def c215 := part 2100 445 1565 160 0xe98d68750 (by decide +kernel)
private def c216 := part 2100 445 1725 160 0xdf7359350 (by decide +kernel)
private def c217 := part 2100 445 1885 160 0xc7bce9f50 (by decide +kernel)
private def c218 := part 2100 445 2045 160 0xa2e5da95f (by decide +kernel)
private def c219 := part 2100 445 2205 160 0x77b0acf6e (by decide +kernel)
private def c220 := part 2100 445 2365 160 0x4de301fc3 (by decide +kernel)
private def c221 := part 2100 445 2525 160 0x29d4db3cd (by decide +kernel)
private def c222 := part 2100 445 2685 160 0xf83ce6ac (by decide +kernel)
private def c223 := part 2100 445 2845 145 0x1fbe3c0a (by decide +kernel)
private def a182 := append c208 c209 rfl
private def a183 := append c210 c211 rfl
private def a184 := append a182 a183 rfl
private def a185 := append c212 c213 rfl
private def a186 := append c214 c215 rfl
private def a187 := append a185 a186 rfl
private def a188 := append a184 a187 rfl
private def a189 := append c216 c217 rfl
private def a190 := append c218 c219 rfl
private def a191 := append a189 a190 rfl
private def a192 := append c220 c221 rfl
private def a193 := append c222 c223 rfl
private def a194 := append a192 a193 rfl
private def a195 := append a191 a194 rfl
private def a196 := append a188 a195 rfl

private theorem moment2100_445 : momentEstimate 2100 445 = 0x7a7ca066ee := a196
private def c224 := part 612 138 138 160 0x146113ba (by decide +kernel)
private def c225 := part 612 138 298 160 0x51db5eb0 (by decide +kernel)
private def c226 := part 612 138 458 160 0x5a8da81c (by decide +kernel)
private def c227 := part 612 138 618 160 0x2b029a1d (by decide +kernel)
private def c228 := part 612 138 778 110 0x3dce212 (by decide +kernel)
private def a197 := append c224 c225 rfl
private def a198 := append c227 c228 rfl
private def a199 := append c226 a198 rfl
private def a200 := append a197 a199 rfl

private theorem moment612_138 : momentEstimate 612 138 = 0xefa996b5 := a200
private def c229 := part 2955 615 615 160 0x758f3a48 (by decide +kernel)
private def c230 := part 2955 615 775 160 0x306c75f48 (by decide +kernel)
private def c231 := part 2955 615 935 160 0x7b9494448 (by decide +kernel)
private def c232 := part 2955 615 1095 160 0xe1788cd02 (by decide +kernel)
private def c233 := part 2955 615 1255 160 0x15234a8840 (by decide +kernel)
private def c234 := part 2955 615 1415 160 0x1b3df19840 (by decide +kernel)
private def c235 := part 2955 615 1575 160 0x202bd0a840 (by decide +kernel)
private def c236 := part 2955 615 1735 160 0x23ece7b840 (by decide +kernel)
private def c237 := part 2955 615 1895 160 0x268136c840 (by decide +kernel)
private def c238 := part 2955 615 2055 160 0x27e8bdd840 (by decide +kernel)
private def c239 := part 2955 615 2215 160 0x28237ce840 (by decide +kernel)
private def c240 := part 2955 615 2375 160 0x273173f840 (by decide +kernel)
private def c241 := part 2955 615 2535 160 0x2512a30840 (by decide +kernel)
private def c242 := part 2955 615 2695 160 0x21c70a1840 (by decide +kernel)
private def c243 := part 2955 615 2855 160 0x1d50a181f7 (by decide +kernel)
private def c244 := part 2955 615 3015 160 0x1810405857 (by decide +kernel)
private def c245 := part 2955 615 3175 160 0x12b70321eb (by decide +kernel)
private def c246 := part 2955 615 3335 160 0xd9a331fbd (by decide +kernel)
private def c247 := part 2955 615 3495 160 0x8fda7ebf7 (by decide +kernel)
private def c248 := part 2955 615 3655 160 0x51e70a684 (by decide +kernel)
private def c249 := part 2955 615 3815 160 0x23e4646c4 (by decide +kernel)
private def c250 := part 2955 615 3975 160 0x84468b04 (by decide +kernel)
private def c251 := part 2955 615 4135 50 0x1fcf126 (by decide +kernel)
private def a201 := append c229 c230 rfl
private def a202 := append c232 c233 rfl
private def a203 := append c231 a202 rfl
private def a204 := append a201 a203 rfl
private def a205 := append c235 c236 rfl
private def a206 := append c234 a205 rfl
private def a207 := append c238 c239 rfl
private def a208 := append c237 a207 rfl
private def a209 := append a206 a208 rfl
private def a210 := append a204 a209 rfl
private def a211 := append c241 c242 rfl
private def a212 := append c240 a211 rfl
private def a213 := append c244 c245 rfl
private def a214 := append c243 a213 rfl
private def a215 := append a212 a214 rfl
private def a216 := append c247 c248 rfl
private def a217 := append c246 a216 rfl
private def a218 := append c250 c251 rfl
private def a219 := append c249 a218 rfl
private def a220 := append a217 a219 rfl
private def a221 := append a215 a220 rfl
private def a222 := append a210 a221 rfl

private theorem moment2955_615 : momentEstimate 2955 615 = 0x1d8f26a3eb9 := a222
private def c252 := part 832 186 186 160 0x1d8c44a8 (by decide +kernel)
private def c253 := part 832 186 346 160 0x982ace82 (by decide +kernel)
private def c254 := part 832 186 506 160 0xe95f70f0 (by decide +kernel)
private def c255 := part 832 186 666 160 0xdf62ccf0 (by decide +kernel)
private def c256 := part 832 186 826 160 0x8583edbf (by decide +kernel)
private def c257 := part 832 186 986 160 0x257b86b7 (by decide +kernel)
private def c258 := part 832 186 1146 58 0xd7a33e (by decide +kernel)
private def a223 := append c253 c254 rfl
private def a224 := append c252 a223 rfl
private def a225 := append c255 c256 rfl
private def a226 := append c257 c258 rfl
private def a227 := append a225 a226 rfl
private def a228 := append a224 a227 rfl

private theorem moment832_186 : momentEstimate 832 186 = 0x32a5068be := a228
private def c259 := part 4700 987 987 160 0xbde68d28 (by decide +kernel)
private def c260 := part 4700 987 1147 160 0x4fbced628 (by decide +kernel)
private def c261 := part 4700 987 1307 160 0xd05075f28 (by decide +kernel)
private def c262 := part 4700 987 1467 160 0x1864602828 (by decide +kernel)
private def c263 := part 4700 987 1627 160 0x26a4a93128 (by decide +kernel)
private def c264 := part 4700 987 1787 160 0x3750b27a28 (by decide +kernel)
private def c265 := part 4700 987 1947 160 0x499ed7eeb5 (by decide +kernel)
private def c266 := part 4700 987 2107 160 0x5b02b7b260 (by decide +kernel)
private def c267 := part 4700 987 2267 160 0x6a84e61a60 (by decide +kernel)
private def c268 := part 4700 987 2427 160 0x7824a88260 (by decide +kernel)
private def c269 := part 4700 987 2587 160 0x83e1feea60 (by decide +kernel)
private def c270 := part 4700 987 2747 160 0x8dbce95260 (by decide +kernel)
private def c271 := part 4700 987 2907 160 0x95b567ba60 (by decide +kernel)
private def c272 := part 4700 987 3067 160 0x9bcb7a2260 (by decide +kernel)
private def c273 := part 4700 987 3227 160 0x9fff208a60 (by decide +kernel)
private def c274 := part 4700 987 3387 160 0xa2505af260 (by decide +kernel)
private def c275 := part 4700 987 3547 160 0xa2bf295a60 (by decide +kernel)
private def c276 := part 4700 987 3707 160 0xa14b8bc260 (by decide +kernel)
private def c277 := part 4700 987 3867 160 0x9df5822a60 (by decide +kernel)
private def c278 := part 4700 987 4027 160 0x98bd0c9260 (by decide +kernel)
private def c279 := part 4700 987 4187 160 0x91a22afa60 (by decide +kernel)
private def c280 := part 4700 987 4347 160 0x88a4dd6260 (by decide +kernel)
private def c281 := part 4700 987 4507 160 0x7dc523ca60 (by decide +kernel)
private def c282 := part 4700 987 4667 160 0x7120832fde (by decide +kernel)
private def c283 := part 4700 987 4827 160 0x63a809b6a5 (by decide +kernel)
private def c284 := part 4700 987 4987 160 0x5606c97be9 (by decide +kernel)
private def c285 := part 4700 987 5147 160 0x488c952cbb (by decide +kernel)
private def c286 := part 4700 987 5307 160 0x3b840bc460 (by decide +kernel)
private def c287 := part 4700 987 5467 160 0x2f330dad72 (by decide +kernel)
private def c288 := part 4700 987 5627 160 0x23d3409a23 (by decide +kernel)
private def c289 := part 4700 987 5787 160 0x199ba8a048 (by decide +kernel)
private def c290 := part 4700 987 5947 160 0x10e5464e48 (by decide +kernel)
private def c291 := part 4700 987 6107 160 0x9d85be848 (by decide +kernel)
private def c292 := part 4700 987 6267 160 0x499886e48 (by decide +kernel)
private def c293 := part 4700 987 6427 160 0x14d6ae048 (by decide +kernel)
private def c294 := part 4700 987 6587 87 0x100a4416 (by decide +kernel)
private def a229 := append c259 c260 rfl
private def a230 := append c261 c262 rfl
private def a231 := append a229 a230 rfl
private def a232 := append c263 c264 rfl
private def a233 := append c266 c267 rfl
private def a234 := append c265 a233 rfl
private def a235 := append a232 a234 rfl
private def a236 := append a231 a235 rfl
private def a237 := append c268 c269 rfl
private def a238 := append c270 c271 rfl
private def a239 := append a237 a238 rfl
private def a240 := append c272 c273 rfl
private def a241 := append c275 c276 rfl
private def a242 := append c274 a241 rfl
private def a243 := append a240 a242 rfl
private def a244 := append a239 a243 rfl
private def a245 := append a236 a244 rfl
private def a246 := append c277 c278 rfl
private def a247 := append c279 c280 rfl
private def a248 := append a246 a247 rfl
private def a249 := append c281 c282 rfl
private def a250 := append c284 c285 rfl
private def a251 := append c283 a250 rfl
private def a252 := append a249 a251 rfl
private def a253 := append a248 a252 rfl
private def a254 := append c286 c287 rfl
private def a255 := append c288 c289 rfl
private def a256 := append a254 a255 rfl
private def a257 := append c290 c291 rfl
private def a258 := append c293 c294 rfl
private def a259 := append c292 a258 rfl
private def a260 := append a257 a259 rfl
private def a261 := append a256 a260 rfl
private def a262 := append a253 a261 rfl
private def a263 := append a245 a262 rfl

private theorem moment4700_987 : momentEstimate 4700 987 = 0xbe4d2da6f3f := a263
private def c295 := part 1283 285 285 160 0x303ea348 (by decide +kernel)
private def c296 := part 1283 285 445 160 0x1264bbb9f (by decide +kernel)
private def c297 := part 1283 285 605 160 0x267e5e4d0 (by decide +kernel)
private def c298 := part 1283 285 765 160 0x3330af8d0 (by decide +kernel)
private def c299 := part 1283 285 925 160 0x3728a0cd0 (by decide +kernel)
private def c300 := part 1283 285 1085 160 0x3266320d0 (by decide +kernel)
private def c301 := part 1283 285 1245 160 0x2565053a1 (by decide +kernel)
private def c302 := part 1283 285 1405 160 0x154714764 (by decide +kernel)
private def c303 := part 1283 285 1565 160 0x7d3b29ea (by decide +kernel)
private def c304 := part 1283 285 1725 128 0xd32d360 (by decide +kernel)
private def a264 := append c295 c296 rfl
private def a265 := append c298 c299 rfl
private def a266 := append c297 a265 rfl
private def a267 := append a264 a266 rfl
private def a268 := append c300 c301 rfl
private def a269 := append c303 c304 rfl
private def a270 := append c302 a269 rfl
private def a271 := append a268 a270 rfl
private def a272 := append a267 a271 rfl

private theorem moment1283_285 : momentEstimate 1283 285 = 0x11bf980276 := a272
private def c305 := part 7037 1492 1492 160 0x11ec8a608 (by decide +kernel)
private def c306 := part 7037 1492 1652 160 0x79ad05308 (by decide +kernel)
private def c307 := part 7037 1492 1812 160 0x141cb6c008 (by decide +kernel)
private def c308 := part 7037 1492 1972 160 0x262f4bed08 (by decide +kernel)
private def c309 := part 7037 1492 2132 160 0x3d5d5fda08 (by decide +kernel)
private def c310 := part 7037 1492 2292 160 0x5931c28708 (by decide +kernel)
private def c311 := part 7037 1492 2452 160 0x793743f408 (by decide +kernel)
private def c312 := part 7037 1492 2612 160 0x9cf8b42108 (by decide +kernel)
private def c313 := part 7037 1492 2772 160 0xc400e30e08 (by decide +kernel)
private def c314 := part 7037 1492 2932 160 0xed96401631 (by decide +kernel)
private def c315 := part 7037 1492 3092 160 0x1165727d0d0 (by decide +kernel)
private def c316 := part 7037 1492 3252 160 0x13c46dabcd0 (by decide +kernel)
private def c317 := part 7037 1492 3412 160 0x15f5d8ca8d0 (by decide +kernel)
private def c318 := part 7037 1492 3572 160 0x17f9b3d94d0 (by decide +kernel)
private def c319 := part 7037 1492 3732 160 0x19cffed80d0 (by decide +kernel)
private def c320 := part 7037 1492 3892 160 0x1b78b9c6cd0 (by decide +kernel)
private def c321 := part 7037 1492 4052 160 0x1cf3e4a58d0 (by decide +kernel)
private def c322 := part 7037 1492 4212 160 0x1e417f744d0 (by decide +kernel)
private def c323 := part 7037 1492 4372 160 0x1f618a330d0 (by decide +kernel)
private def c324 := part 7037 1492 4532 160 0x205404e1cd0 (by decide +kernel)
private def c325 := part 7037 1492 4692 160 0x2118ef808d0 (by decide +kernel)
private def c326 := part 7037 1492 4852 160 0x21b04a0f4d0 (by decide +kernel)
private def c327 := part 7037 1492 5012 160 0x221a148e0d0 (by decide +kernel)
private def c328 := part 7037 1492 5172 160 0x22564efccd0 (by decide +kernel)
private def c329 := part 7037 1492 5332 160 0x2264f95b8d0 (by decide +kernel)
private def c330 := part 7037 1492 5492 160 0x224613aa4d0 (by decide +kernel)
private def c331 := part 7037 1492 5652 160 0x21f99de90d0 (by decide +kernel)
private def c332 := part 7037 1492 5812 160 0x217f9817cd0 (by decide +kernel)
private def c333 := part 7037 1492 5972 160 0x20d802368d0 (by decide +kernel)
private def c334 := part 7037 1492 6132 160 0x2002dc454d0 (by decide +kernel)
private def c335 := part 7037 1492 6292 160 0x1f0026440d0 (by decide +kernel)
private def c336 := part 7037 1492 6452 160 0x1dcfe032cd0 (by decide +kernel)
private def c337 := part 7037 1492 6612 160 0x1c720a118d0 (by decide +kernel)
private def c338 := part 7037 1492 6772 160 0x1ae6a3e04d0 (by decide +kernel)
private def c339 := part 7037 1492 6932 160 0x192de57d288 (by decide +kernel)
private def c340 := part 7037 1492 7092 160 0x1754456d25d (by decide +kernel)
private def c341 := part 7037 1492 7252 160 0x156f2a387f2 (by decide +kernel)
private def c342 := part 7037 1492 7412 160 0x13853334e93 (by decide +kernel)
private def c343 := part 7037 1492 7572 160 0x119b68bd9ad (by decide +kernel)
private def c344 := part 7037 1492 7732 160 0xfb6a0f1d13 (by decide +kernel)
private def c345 := part 7037 1492 7892 160 0xddb7fb47e9 (by decide +kernel)
private def c346 := part 7037 1492 8052 160 0xc0e76ad00a (by decide +kernel)
private def c347 := part 7037 1492 8212 160 0xa53c54637f (by decide +kernel)
private def c348 := part 7037 1492 8372 160 0x8af7849798 (by decide +kernel)
private def c349 := part 7037 1492 8532 160 0x722a542fe4 (by decide +kernel)
private def c350 := part 7037 1492 8692 160 0x5b36f50ba4 (by decide +kernel)
private def c351 := part 7037 1492 8852 160 0x46808ba364 (by decide +kernel)
private def c352 := part 7037 1492 9012 160 0x342bb6f724 (by decide +kernel)
private def c353 := part 7037 1492 9172 160 0x245d1606e4 (by decide +kernel)
private def c354 := part 7037 1492 9332 160 0x173947d2a4 (by decide +kernel)
private def c355 := part 7037 1492 9492 160 0xce4eb5a64 (by decide +kernel)
private def c356 := part 7037 1492 9652 160 0x5849f9e24 (by decide +kernel)
private def c357 := part 7037 1492 9812 160 0x13d039de4 (by decide +kernel)
private def c358 := part 7037 1492 9972 49 0x47bf523 (by decide +kernel)
private def a273 := append c306 c307 rfl
private def a274 := append c305 a273 rfl
private def a275 := append c309 c310 rfl
private def a276 := append c308 a275 rfl
private def a277 := append a274 a276 rfl
private def a278 := append c312 c313 rfl
private def a279 := append c311 a278 rfl
private def a280 := append c314 c315 rfl
private def a281 := append c316 c317 rfl
private def a282 := append a280 a281 rfl
private def a283 := append a279 a282 rfl
private def a284 := append a277 a283 rfl
private def a285 := append c319 c320 rfl
private def a286 := append c318 a285 rfl
private def a287 := append c321 c322 rfl
private def a288 := append c323 c324 rfl
private def a289 := append a287 a288 rfl
private def a290 := append a286 a289 rfl
private def a291 := append c326 c327 rfl
private def a292 := append c325 a291 rfl
private def a293 := append c328 c329 rfl
private def a294 := append c330 c331 rfl
private def a295 := append a293 a294 rfl
private def a296 := append a292 a295 rfl
private def a297 := append a290 a296 rfl
private def a298 := append a284 a297 rfl
private def a299 := append c333 c334 rfl
private def a300 := append c332 a299 rfl
private def a301 := append c336 c337 rfl
private def a302 := append c335 a301 rfl
private def a303 := append a300 a302 rfl
private def a304 := append c339 c340 rfl
private def a305 := append c338 a304 rfl
private def a306 := append c341 c342 rfl
private def a307 := append c343 c344 rfl
private def a308 := append a306 a307 rfl
private def a309 := append a305 a308 rfl
private def a310 := append a303 a309 rfl
private def a311 := append c346 c347 rfl
private def a312 := append c345 a311 rfl
private def a313 := append c348 c349 rfl
private def a314 := append c350 c351 rfl
private def a315 := append a313 a314 rfl
private def a316 := append a312 a315 rfl
private def a317 := append c353 c354 rfl
private def a318 := append c352 a317 rfl
private def a319 := append c355 c356 rfl
private def a320 := append c357 c358 rfl
private def a321 := append a319 a320 rfl
private def a322 := append a318 a321 rfl
private def a323 := append a316 a322 rfl
private def a324 := append a310 a323 rfl
private def a325 := append a298 a324 rfl

private theorem moment7037_1492 : momentEstimate 7037 1492 = 0x3c2eefe70454 := a325
private def c359 := part 1612 364 364 160 0x3de23f28 (by decide +kernel)
private def c360 := part 1612 364 524 160 0x1852c4828 (by decide +kernel)
private def c361 := part 1612 364 684 160 0x393dc42e5 (by decide +kernel)
private def c362 := part 1612 364 844 160 0x56344f1c0 (by decide +kernel)
private def c363 := part 1612 364 1004 160 0x6818a19c0 (by decide +kernel)
private def c364 := part 1612 364 1164 160 0x6ed9641c0 (by decide +kernel)
private def c365 := part 1612 364 1324 160 0x6a76969c0 (by decide +kernel)
private def c366 := part 1612 364 1484 160 0x5af2ba4b8 (by decide +kernel)
private def c367 := part 1612 364 1644 160 0x42af12924 (by decide +kernel)
private def c368 := part 1612 364 1804 160 0x291c65995 (by decide +kernel)
private def c369 := part 1612 364 1964 160 0x1328f6e8d (by decide +kernel)
private def c370 := part 1612 364 2124 160 0x4bbe4ab0 (by decide +kernel)
private def c371 := part 1612 364 2284 56 0x17f49f4 (by decide +kernel)
private def a326 := append c360 c361 rfl
private def a327 := append c359 a326 rfl
private def a328 := append c363 c364 rfl
private def a329 := append c362 a328 rfl
private def a330 := append a327 a329 rfl
private def a331 := append c366 c367 rfl
private def a332 := append c365 a331 rfl
private def a333 := append c368 c369 rfl
private def a334 := append c370 c371 rfl
private def a335 := append a333 a334 rfl
private def a336 := append a332 a335 rfl
private def a337 := append a330 a336 rfl

private theorem moment1612_364 : momentEstimate 1612 364 = 0x2cbc69abd7 := a337
private def c372 := part 9479 1991 1991 160 0x1840516c8 (by decide +kernel)
private def c373 := part 9479 1991 2151 160 0xa57f7abc8 (by decide +kernel)
private def c374 := part 9479 1991 2311 160 0x1b85fa00c8 (by decide +kernel)
private def c375 := part 9479 1991 2471 160 0x3498dc15c8 (by decide +kernel)
private def c376 := part 9479 1991 2631 160 0x551b6deac8 (by decide +kernel)
private def c377 := part 9479 1991 2791 160 0x7c987f7fc8 (by decide +kernel)
private def c378 := part 9479 1991 2951 160 0xaa9ae0d4c8 (by decide +kernel)
private def c379 := part 9479 1991 3111 160 0xdead61e9c8 (by decide +kernel)
private def c380 := part 9479 1991 3271 160 0x1185ad2bec8 (by decide +kernel)
private def c381 := part 9479 1991 3431 160 0x1572e0353c8 (by decide +kernel)
private def c382 := part 9479 1991 3591 160 0x19ab1c3a8c8 (by decide +kernel)
private def c383 := part 9479 1991 3751 160 0x1e270e3bdc8 (by decide +kernel)
private def c384 := part 9479 1991 3911 160 0x22dc23b5352 (by decide +kernel)
private def c385 := part 9479 1991 4071 160 0x278a0aa6340 (by decide +kernel)
private def c386 := part 9479 1991 4231 160 0x2bfcd40b340 (by decide +kernel)
private def c387 := part 9479 1991 4391 160 0x3032d2f0340 (by decide +kernel)
private def c388 := part 9479 1991 4551 160 0x342c0755340 (by decide +kernel)
private def c389 := part 9479 1991 4711 160 0x37e8713a340 (by decide +kernel)
private def c390 := part 9479 1991 4871 160 0x3b68109f340 (by decide +kernel)
private def c391 := part 9479 1991 5031 160 0x3eaae584340 (by decide +kernel)
private def c392 := part 9479 1991 5191 160 0x41b0efe9340 (by decide +kernel)
private def c393 := part 9479 1991 5351 160 0x447a2fce340 (by decide +kernel)
private def c394 := part 9479 1991 5511 160 0x4706a533340 (by decide +kernel)
private def c395 := part 9479 1991 5671 160 0x49565018340 (by decide +kernel)
private def c396 := part 9479 1991 5831 160 0x4b69307d340 (by decide +kernel)
private def c397 := part 9479 1991 5991 160 0x4d3f4662340 (by decide +kernel)
private def c398 := part 9479 1991 6151 160 0x4ed891c7340 (by decide +kernel)
private def c399 := part 9479 1991 6311 160 0x503512ac340 (by decide +kernel)
private def c400 := part 9479 1991 6471 160 0x5154c911340 (by decide +kernel)
private def c401 := part 9479 1991 6631 160 0x5237b4f6340 (by decide +kernel)
private def c402 := part 9479 1991 6791 160 0x52ddd65b340 (by decide +kernel)
private def c403 := part 9479 1991 6951 160 0x53472d40340 (by decide +kernel)
private def c404 := part 9479 1991 7111 160 0x5373b9a5340 (by decide +kernel)
private def c405 := part 9479 1991 7271 160 0x53637b8a340 (by decide +kernel)
private def c406 := part 9479 1991 7431 160 0x531672ef340 (by decide +kernel)
private def c407 := part 9479 1991 7591 160 0x528c9fd4340 (by decide +kernel)
private def c408 := part 9479 1991 7751 160 0x51c60239340 (by decide +kernel)
private def c409 := part 9479 1991 7911 160 0x50c29a1e340 (by decide +kernel)
private def c410 := part 9479 1991 8071 160 0x4f826783340 (by decide +kernel)
private def c411 := part 9479 1991 8231 160 0x4e056a68340 (by decide +kernel)
private def c412 := part 9479 1991 8391 160 0x4c4ba2cd340 (by decide +kernel)
private def c413 := part 9479 1991 8551 160 0x4a5510b2340 (by decide +kernel)
private def c414 := part 9479 1991 8711 160 0x4821b417340 (by decide +kernel)
private def c415 := part 9479 1991 8871 160 0x45b18cfc340 (by decide +kernel)
private def c416 := part 9479 1991 9031 160 0x43049b61340 (by decide +kernel)
private def c417 := part 9479 1991 9191 160 0x401adf46340 (by decide +kernel)
private def c418 := part 9479 1991 9351 160 0x3cf467bce00 (by decide +kernel)
private def c419 := part 9479 1991 9511 160 0x399d9e4b08a (by decide +kernel)
private def c420 := part 9479 1991 9671 160 0x363456eab6b (by decide +kernel)
private def c421 := part 9479 1991 9831 160 0x32c154194b2 (by decide +kernel)
private def c422 := part 9479 1991 9991 160 0x2f49c1242cf (by decide +kernel)
private def c423 := part 9479 1991 10151 160 0x2bd2a3b1f15 (by decide +kernel)
private def c424 := part 9479 1991 10311 160 0x2860dbc276a (by decide +kernel)
private def c425 := part 9479 1991 10471 160 0x24f923af340 (by decide +kernel)
private def c426 := part 9479 1991 10631 160 0x21a0102aeac (by decide +kernel)
private def c427 := part 9479 1991 10791 160 0x1e5a10420dd (by decide +kernel)
private def c428 := part 9479 1991 10951 160 0x1b2b6d5a067 (by decide +kernel)
private def c429 := part 9479 1991 11111 160 0x18184b32672 (by decide +kernel)
private def c430 := part 9479 1991 11271 160 0x1524a7e384e (by decide +kernel)
private def c431 := part 9479 1991 11431 160 0x12515716de4 (by decide +kernel)
private def c432 := part 9479 1991 11591 160 0xfa06eb75d4 (by decide +kernel)
private def c433 := part 9479 1991 11751 160 0xd1ddec9294 (by decide +kernel)
private def c434 := part 9479 1991 11911 160 0xacc4c7b354 (by decide +kernel)
private def c435 := part 9479 1991 12071 160 0x8ae01bd814 (by decide +kernel)
private def c436 := part 9479 1991 12231 160 0x6c548800d4 (by decide +kernel)
private def c437 := part 9479 1991 12391 160 0x5146ab2d94 (by decide +kernel)
private def c438 := part 9479 1991 12551 160 0x39db245e54 (by decide +kernel)
private def c439 := part 9479 1991 12711 160 0x2636929314 (by decide +kernel)
private def c440 := part 9479 1991 12871 160 0x167d94cbd4 (by decide +kernel)
private def c441 := part 9479 1991 13031 160 0xad4ca0894 (by decide +kernel)
private def c442 := part 9479 1991 13191 160 0x360d14954 (by decide +kernel)
private def c443 := part 9479 1991 13351 110 0x40e7ff16 (by decide +kernel)
private def a338 := append c372 c373 rfl
private def a339 := append c374 c375 rfl
private def a340 := append a338 a339 rfl
private def a341 := append c376 c377 rfl
private def a342 := append c379 c380 rfl
private def a343 := append c378 a342 rfl
private def a344 := append a341 a343 rfl
private def a345 := append a340 a344 rfl
private def a346 := append c381 c382 rfl
private def a347 := append c383 c384 rfl
private def a348 := append a346 a347 rfl
private def a349 := append c385 c386 rfl
private def a350 := append c388 c389 rfl
private def a351 := append c387 a350 rfl
private def a352 := append a349 a351 rfl
private def a353 := append a348 a352 rfl
private def a354 := append a345 a353 rfl
private def a355 := append c390 c391 rfl
private def a356 := append c392 c393 rfl
private def a357 := append a355 a356 rfl
private def a358 := append c394 c395 rfl
private def a359 := append c397 c398 rfl
private def a360 := append c396 a359 rfl
private def a361 := append a358 a360 rfl
private def a362 := append a357 a361 rfl
private def a363 := append c399 c400 rfl
private def a364 := append c401 c402 rfl
private def a365 := append a363 a364 rfl
private def a366 := append c403 c404 rfl
private def a367 := append c406 c407 rfl
private def a368 := append c405 a367 rfl
private def a369 := append a366 a368 rfl
private def a370 := append a365 a369 rfl
private def a371 := append a362 a370 rfl
private def a372 := append a354 a371 rfl
private def a373 := append c408 c409 rfl
private def a374 := append c410 c411 rfl
private def a375 := append a373 a374 rfl
private def a376 := append c412 c413 rfl
private def a377 := append c415 c416 rfl
private def a378 := append c414 a377 rfl
private def a379 := append a376 a378 rfl
private def a380 := append a375 a379 rfl
private def a381 := append c417 c418 rfl
private def a382 := append c419 c420 rfl
private def a383 := append a381 a382 rfl
private def a384 := append c421 c422 rfl
private def a385 := append c424 c425 rfl
private def a386 := append c423 a385 rfl
private def a387 := append a384 a386 rfl
private def a388 := append a383 a387 rfl
private def a389 := append a380 a388 rfl
private def a390 := append c426 c427 rfl
private def a391 := append c428 c429 rfl
private def a392 := append a390 a391 rfl
private def a393 := append c430 c431 rfl
private def a394 := append c433 c434 rfl
private def a395 := append c432 a394 rfl
private def a396 := append a393 a395 rfl
private def a397 := append a392 a396 rfl
private def a398 := append c435 c436 rfl
private def a399 := append c437 c438 rfl
private def a400 := append a398 a399 rfl
private def a401 := append c439 c440 rfl
private def a402 := append c442 c443 rfl
private def a403 := append c441 a402 rfl
private def a404 := append a401 a403 rfl
private def a405 := append a400 a404 rfl
private def a406 := append a397 a405 rfl
private def a407 := append a389 a406 rfl
private def a408 := append a372 a407 rfl

private theorem moment9479_1991 : momentEstimate 9479 1991 = 0xc4a19dc9e22d := a408

private theorem terminal_ok (b : Band) : BankOK (terminal b) := by
  cases b with
  | h2391 => exact (pass! 6220,8648,1834,0x193baf9f5c0000,0x8944c1334160; moment8648_1834)

private def StageOK (ss : List Stage) : Prop :=
  ∀ s ∈ ss, BankOK s.free ∧ BankOK s.moving

private theorem stages_nil : StageOK [] :=
  fun _ hs => (List.not_mem_nil hs).elim

private theorem stages_cons {s : Stage} {ss : List Stage}
    (hf : BankOK s.free) (hm : BankOK s.moving) (ht : StageOK ss) : StageOK (s :: ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf, hm⟩, ht⟩

private theorem stages_ok (b : Band) : StageOK (stages b) := by
  cases b with
  | h2391 =>
    rw [stages]
    refine stages_cons (pass! 70,97,21,0x28d4c0000,0x284e2c; moment97_21) (pass! 381,530,111,0x17d1c400000,0x7f95aba6; moment530_111) ?_
    refine stages_cons (pass! 77,107,23,0x35da00000,0x3ae575; moment107_23) (pass! 401,558,116,0x1b9a9440000,0x9bbb4f84; moment558_116) ?_
    refine stages_cons (pass! 83,115,25,0x439080000,0x4ed4ac; moment115_25) (pass! 485,675,142,0x312f66c0000,0x14facc9aa; moment675_142) ?_
    refine stages_cons (pass! 91,126,27,0x57a300000,0x6fafa5; moment126_27) (pass! 535,745,155,0x416e7300000,0x1ed40d93b; moment745_155) ?_
    refine stages_cons (pass! 106,147,32,0x8b45c0000,0xcf7010; moment147_32) (pass! 569,791,166,0x4f174840000,0x276a61df4; moment791_166) ?_
    refine stages_cons (pass! 120,166,37,0xcc31c0000,0x1553865; moment166_37) (pass! 671,933,196,0x81a8f600000,0x4c3aaf76c; moment933_196) ?_
    refine stages_cons (pass! 142,197,43,0x14bde80000,0x294fec6; moment197_43) (pass! 820,1141,240,0xecaf4280000,0xaa63e2113; moment1141_240) ?_
    refine stages_cons (pass! 169,235,50,0x222f040000,0x517adc3; moment235_50) (pass! 1033,1435,304,0x1da95f340000,0x1ac0470697; moment1435_304) ?_
    refine stages_cons (pass! 206,285,64,0x3fe4a40000,0xb68effd; moment285_64) (pass! 1043,1452,305,0x1e61e4680000,0x1bdaae9c57; moment1452_305) ?_
    refine stages_cons (pass! 207,287,64,0x4096600000,0xbab2d1e; moment287_64) (pass! 1319,1833,385,0x3d4d25c80000,0x46a696e4a8; moment1833_385) ?_
    refine stages_cons (pass! 261,362,80,0x8008bc0000,0x1d282567; moment362_80) (pass! 1679,2333,490,0x7e5359c00000,0xb9375c1e10; moment2333_490) ?_
    refine stages_cons (pass! 259,359,79,0x7cac400000,0x1c1d91ae; moment359_79) (pass! 1421,1980,416,0x4ccddb6c0000,0x602dc09b83; moment1980_416) ?_
    refine stages_cons (pass! 293,407,91,0xb694500000,0x2ee3dfbb; moment407_91) (pass! 1507,2100,445,0x5c32a3980000,0x7a7ca066ee; moment2100_445) ?_
    refine stages_cons (pass! 441,612,138,0x26ebe240000,0xefa996b5; moment612_138) (pass! 2121,2955,615,0xfd3f8e600000,0x1d8f26a3eb9; moment2955_615) ?_
    refine stages_cons (pass! 599,832,186,0x60b2db00000,0x32a5068be; moment832_186) (pass! 3373,4700,987,0x400ced8500000,0xbe4d2da6f3f; moment4700_987) ?_
    refine stages_cons (pass! 925,1283,285,0x161084780000,0x11bf980276; moment1283_285) (pass! 5067,7037,1492,0xda1220ce80000,0x3c2eefe70454; moment7037_1492) ?_
    refine stages_cons (pass! 1161,1612,364,0x2c2938540000,0x2cbc69abd7; moment1612_364) (pass! 6803,9479,1991,0x20d2fc74a00000,0xc4a19dc9e22d; moment9479_1991) ?_
    exact stages_nil

theorem listed_ok (b : Band) (t : Bank) (ht : Listed b t) : BankOK t := by
  rcases ht with rfl | ⟨s, hs, rfl | rfl⟩ | ⟨i, rfl⟩
  · exact terminal_ok b
  · exact (stages_ok b s hs).1
  · exact (stages_ok b s hs).2
  · exact ⟨(terminal_ok b).nodes, (terminal_ok b).moment⟩

theorem interpolation_sources : SourceExists :=
  source (fun b t ht => (listed_ok b t ht).nodes) (fun b t ht => (listed_ok b t ht).moment)

#print axioms interpolation_sources
end Rect52PrefixBankProof
