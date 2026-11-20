import ProximityPrize.SubmissionLower.SixRows2
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ6_7
open CJ6 (VectorDots belowZero belowSucc)
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
local notation "zero!" a => (⟨a,0,0,0,0⟩ : Lane)
local notation "rank!" q "," u => Matrix.rank (CJ0.blockMatrix CJ6.source q ((u : ℤ)-20))
local notation "cap!" q "," u "," w "," h =>
  le_trans (CJ6.block_rank_le q u) (CJ6.rank_of_dots (z := w) (by decide) h)
private def l1v0 : List Lane := [zero! 37,zero! 38,zero! 39,zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,⟨45,4,1,1,1⟩,⟨46,2,2,31,0x3f7fffff7f000000⟩,⟨47,1,2,2,14⟩,⟨48,0,2,31,0x3f8000007f000000⟩]
private def l1v1 : List Lane := [zero! 37,zero! 38,zero! 39,zero! 40,zero! 41,zero! 42,zero! 43,⟨44,6,1,1,1⟩,⟨45,5,1,31,0x7efffffe⟩,⟨46,2,3,31,0xff7fffffff000000⟩,⟨47,1,3,31,0x1fc000000000000200000003⟩,⟨48,0,2,31,0x3f7ffffffeffffff⟩]
private def l1v2 : List Lane := [zero! 37,zero! 38,zero! 39,zero! 40,zero! 41,zero! 42,⟨43,8,1,1,1⟩,⟨44,7,1,31,0x7efffffe⟩,⟨45,5,2,31,0x1fefffffe⟩,⟨46,2,4,31,0xfe0000000000001800000007f000000⟩,⟨47,1,3,31,0x1fbfffff8000000180000003⟩,⟨48,0,2,31,0x3f7fffff7efffffe⟩]
private def z1 : CJ1.Block where
  bank := .rightHigh
  cap := 36
  free := [(4,1),(6,1),(8,1)]
  vectors := [l1v0,l1v1,l1v2].map (vectorData false 57 3)
private def b1 := bands [(0,46,12),(1,47,10),(2,48,8),(3,49,6),(4,50,4),(5,51,2)]
private theorem k1v0 : good false 57 l1v0 b1 := rfl
private theorem v1j0 : VectorDots 57 3 z1 0 := v! false, 57, b1, l1v0, k1v0
private theorem k1v1 : good false 57 l1v1 b1 := rfl
private theorem v1j1 : VectorDots 57 3 z1 1 := v! false, 57, b1, l1v1, k1v1
private theorem k1v2 : good false 57 l1v2 b1 := rfl
private theorem v1j2 : VectorDots 57 3 z1 2 := v! false, 57, b1, l1v2, k1v2
theorem r1 : (rank! 57, 3) ≤ 36 :=
  cap! 57, 3, z1, (belowSucc (belowSucc (belowSucc belowZero v1j0) v1j1) v1j2)
private def l2v0 : List Lane := [⟨5,5,1,1,1⟩,⟨4,4,1,31,0x7effffdc⟩,⟨3,3,1,10,703⟩,⟨2,2,1,31,0x7effdc4e⟩,⟨1,1,1,17,91390⟩,⟨0,0,1,31,0x7ef490ab⟩]
private def z2 : CJ1.Block where
  bank := .leftHigh
  cap := 35
  free := [(5,0)]
  vectors := [l2v0].map (vectorData true 57 4)
private def b2 := bands [(49,57,1),(48,55,3),(47,53,4),(46,51,5),(45,49,5),(44,47,5),(43,45,5),(42,43,5),(41,41,5),(40,40,4),(39,39,3),(38,38,2),(37,37,1)]
private theorem k2v0 : good true 57 l2v0 b2 := rfl
private theorem v2j0 : VectorDots 57 4 z2 0 := v! true, 57, b2, l2v0, k2v0
theorem r2 : (rank! 57, 4) ≤ 35 :=
  cap! 57, 4, z2, (belowSucc belowZero v2j0)
private def l3v0 : List Lane := [zero! 5,⟨4,6,1,1,1⟩,⟨3,3,3,31,0x1fbffff67f7fffdb7effff75⟩,⟨2,2,3,14,0x3342f820e9⟩,⟨1,1,3,31,0x1fbff4ca7f7f84aefefc7a21⟩,⟨0,0,3,22,0x1e21236a743dcf70⟩]
private def l3v1 : List Lane := [zero! 5,⟨4,5,1,1,1⟩,⟨3,3,2,31,0x3f7fffed7effffb8⟩,⟨2,2,2,12,3197766⟩,⟨1,1,2,31,0x3f7feb2efeff1b7d⟩,⟨0,0,2,20,0x1b53ac5cb0⟩]
private def l3v2 : List Lane := [zero! 5,⟨4,4,1,1,1⟩,⟨3,3,1,31,0x7effffdb⟩,⟨2,2,1,10,741⟩,⟨1,1,1,31,0x7effd969⟩,⟨0,0,1,17,101270⟩]
private def l3v3 : List Lane := [⟨5,5,1,1,1⟩,zero! 4,⟨3,3,1,31,0x7efffd42⟩,⟨2,2,1,15,18278⟩,⟨1,1,1,31,0x7efbd107⟩,⟨0,0,1,22,2997592⟩]
private def z3 : CJ1.Block where
  bank := .leftHigh
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [l3v0,l3v1,l3v2,l3v3].map (vectorData true 58 3)
private def b3 := bands [(49,57,2),(48,55,3),(47,53,4),(46,51,4),(45,49,4),(44,47,4),(43,45,4),(42,43,4),(41,41,4),(40,40,3),(39,39,2),(38,38,1)]
private theorem k3v0 : good true 58 l3v0 b3 := rfl
private theorem v3j0 : VectorDots 58 3 z3 0 := v! true, 58, b3, l3v0, k3v0
private theorem k3v1 : good true 58 l3v1 b3 := rfl
private theorem v3j1 : VectorDots 58 3 z3 1 := v! true, 58, b3, l3v1, k3v1
private theorem k3v2 : good true 58 l3v2 b3 := rfl
private theorem v3j2 : VectorDots 58 3 z3 2 := v! true, 58, b3, l3v2, k3v2
private theorem k3v3 : good true 58 l3v3 b3 := rfl
private theorem v3j3 : VectorDots 58 3 z3 3 := v! true, 58, b3, l3v3, k3v3
theorem r3 : (rank! 58, 3) ≤ 32 :=
  cap! 58, 3, z3, (belowSucc (belowSucc (belowSucc (belowSucc belowZero v3j0) v3j1) v3j2) v3j3)
private def l4v0 : List Lane := [zero! 39,zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,⟨48,2,1,1,1⟩,⟨49,1,1,31,0x7effffff⟩,⟨50,0,1,1,1⟩]
private def l4v1 : List Lane := [zero! 39,zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,⟨47,4,1,1,1⟩,⟨48,3,1,31,0x7effffff⟩,⟨49,1,2,31,0xff000000⟩,⟨50,0,1,1,1⟩]
private def l4v2 : List Lane := [zero! 39,zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,⟨46,6,1,1,1⟩,⟨47,5,1,31,0x7effffff⟩,⟨48,3,2,31,0xfeffffff⟩,⟨49,2,1,2,2⟩,⟨50,0,1,1,1⟩]
private def z4 : CJ1.Block where
  bank := .rightHigh
  cap := 27
  free := [(2,1),(4,1),(6,1)]
  vectors := [l4v0,l4v1,l4v2].map (vectorData false 59 2)
private def b4 := bands [(0,49,11),(1,50,9),(2,51,7),(3,52,5),(4,53,3),(5,54,1)]
private theorem k4v0 : good false 59 l4v0 b4 := rfl
private theorem v4j0 : VectorDots 59 2 z4 0 := v! false, 59, b4, l4v0, k4v0
private theorem k4v1 : good false 59 l4v1 b4 := rfl
private theorem v4j1 : VectorDots 59 2 z4 1 := v! false, 59, b4, l4v1, k4v1
private theorem k4v2 : good false 59 l4v2 b4 := rfl
private theorem v4j2 : VectorDots 59 2 z4 2 := v! false, 59, b4, l4v2, k4v2
theorem r4 : (rank! 59, 2) ≤ 27 :=
  cap! 59, 2, z4, (belowSucc (belowSucc (belowSucc belowZero v4j0) v4j1) v4j2)
private def l5v0 : List Lane := [⟨4,5,1,1,1⟩,⟨3,3,2,31,0x3f7fffecfeffffb6⟩,⟨2,2,2,12,3361760⟩,⟨1,1,2,31,0x3f7fe994feff095d⟩,⟨0,0,2,20,0x1e212da9d0⟩]
private def l5v1 : List Lane := [⟨4,4,1,1,1⟩,⟨3,3,1,31,0x7effffda⟩,⟨2,2,1,10,780⟩,⟨1,1,1,31,0x7effd65d⟩,⟨0,0,1,17,111930⟩]
private def z5 : CJ1.Block where
  bank := .leftHigh
  cap := 28
  free := [(4,0),(4,1)]
  vectors := [l5v0,l5v1].map (vectorData true 59 3)
private def b5 := bands [(50,58,2),(49,56,3),(48,54,4),(47,52,4),(46,50,4),(45,48,4),(44,46,4),(43,44,4),(42,42,4),(41,41,3),(40,40,2),(39,39,1)]
private theorem k5v0 : good true 59 l5v0 b5 := rfl
private theorem v5j0 : VectorDots 59 3 z5 0 := v! true, 59, b5, l5v0, k5v0
private theorem k5v1 : good true 59 l5v1 b5 := rfl
private theorem v5j1 : VectorDots 59 3 z5 1 := v! true, 59, b5, l5v1, k5v1
theorem r5 : (rank! 59, 3) ≤ 28 :=
  cap! 59, 3, z5, (belowSucc (belowSucc belowZero v5j0) v5j1)
private def l6v0 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,zero! 48,zero! 49,⟨50,1,1,1,1⟩,⟨51,0,1,31,0x7f000000⟩]
private def l6v1 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,zero! 48,⟨49,2,1,1,1⟩,zero! 50,⟨51,0,1,31,0x7f000000⟩]
private def l6v2 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,zero! 48,⟨49,3,1,1,1⟩,⟨50,2,1,31,0x7f000000⟩,⟨51,0,1,31,0x7f000000⟩]
private def l6v3 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,⟨48,4,1,1,1⟩,zero! 49,⟨50,2,1,31,0x7f000000⟩,⟨51,0,1,31,0x7effffff⟩]
private def l6v4 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,⟨47,6,1,1,1⟩,⟨48,5,1,31,0x7effffff⟩,⟨49,4,1,1,1⟩,zero! 50,⟨51,0,1,31,0x7f000000⟩]
private def l6v5 : List Lane := [zero! 40,zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,⟨46,8,1,1,1⟩,⟨47,7,1,31,0x7effffff⟩,⟨48,5,2,31,0xfeffffff⟩,⟨49,4,1,2,2⟩,⟨50,2,1,1,1⟩,zero! 51]
private def z6 : CJ1.Block where
  bank := .rightHigh
  cap := 24
  free := [(1,0),(2,1),(3,0),(4,1),(6,1),(8,1)]
  vectors := [l6v0,l6v1,l6v2,l6v3,l6v4,l6v5].map (vectorData false 60 2)
private def b6 := bands [(0,51,10),(1,52,8),(2,53,6),(3,54,4),(4,55,2)]
private theorem k6v0 : good false 60 l6v0 b6 := rfl
private theorem v6j0 : VectorDots 60 2 z6 0 := v! false, 60, b6, l6v0, k6v0
private theorem k6v1 : good false 60 l6v1 b6 := rfl
private theorem v6j1 : VectorDots 60 2 z6 1 := v! false, 60, b6, l6v1, k6v1
private theorem k6v2 : good false 60 l6v2 b6 := rfl
private theorem v6j2 : VectorDots 60 2 z6 2 := v! false, 60, b6, l6v2, k6v2
private theorem k6v3 : good false 60 l6v3 b6 := rfl
private theorem v6j3 : VectorDots 60 2 z6 3 := v! false, 60, b6, l6v3, k6v3
private theorem k6v4 : good false 60 l6v4 b6 := rfl
private theorem v6j4 : VectorDots 60 2 z6 4 := v! false, 60, b6, l6v4, k6v4
private theorem k6v5 : good false 60 l6v5 b6 := rfl
private theorem v6j5 : VectorDots 60 2 z6 5 := v! false, 60, b6, l6v5, k6v5
theorem r6 : (rank! 60, 2) ≤ 24 :=
  cap! 60, 2, z6, (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc (belowSucc belowZero v6j0) v6j1) v6j2) v6j3) v6j4) v6j5)
private def l7v0 : List Lane := [⟨4,4,1,1,1⟩,⟨3,3,1,31,0x7effffd9⟩,⟨2,2,1,10,820⟩,⟨1,1,1,31,0x7effd329⟩,⟨0,0,1,17,123410⟩]
private def z7 : CJ1.Block where
  bank := .leftHigh
  cap := 24
  free := [(4,0)]
  vectors := [l7v0].map (vectorData true 60 3)
private def b7 := bands [(51,59,2),(50,57,3),(49,55,4),(48,53,4),(47,51,4),(46,49,4),(45,47,4),(44,45,4),(43,43,4),(42,42,3),(41,41,2),(40,40,1)]
private theorem k7v0 : good true 60 l7v0 b7 := rfl
private theorem v7j0 : VectorDots 60 3 z7 0 := v! true, 60, b7, l7v0, k7v0
theorem r7 : (rank! 60, 3) ≤ 24 :=
  cap! 60, 3, z7, (belowSucc belowZero v7j0)
end CJ6_7
end
section
namespace CJ6_7
open CJ6 (VectorDots belowZero belowSucc)
open CJ6.Fast
set_option maxRecDepth 4096
local notation "v!" side "," q "," b "," l "," h => CJ6.Fast.vector b (buckets side q l) rfl rfl rfl h
local notation "zero!" a => (⟨a,0,0,0,0⟩ : Lane)
local notation "rank!" q "," u => Matrix.rank (CJ0.blockMatrix CJ6.source q ((u : ℤ)-20))
local notation "cap!" q "," u "," w "," h =>
  le_trans (CJ6.block_rank_le q u) (CJ6.rank_of_dots (z := w) (by decide) h)
private def l8v0 : List Lane := [zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,zero! 48,zero! 49,⟨50,2,1,1,1⟩,⟨51,1,1,31,0x7f000000⟩]
private def l8v1 : List Lane := [zero! 41,zero! 42,zero! 43,zero! 44,zero! 45,zero! 46,zero! 47,zero! 48,⟨49,4,1,1,1⟩,⟨50,3,1,31,0x7f000000⟩,⟨51,1,1,31,0x7f000000⟩]
private def z8 : CJ1.Block where
  bank := .rightHigh
  cap := 18
  free := [(2,0),(4,0)]
  vectors := [l8v0,l8v1].map (vectorData false 61 1)
private def b8 := bands [(0,52,10),(1,53,8),(2,54,6),(3,55,4),(4,56,2)]
private theorem k8v0 : good false 61 l8v0 b8 := rfl
private theorem v8j0 : VectorDots 61 1 z8 0 := v! false, 61, b8, l8v0, k8v0
private theorem k8v1 : good false 61 l8v1 b8 := rfl
private theorem v8j1 : VectorDots 61 1 z8 1 := v! false, 61, b8, l8v1, k8v1
theorem r8 : (rank! 61, 1) ≤ 18 :=
  cap! 61, 1, z8, (belowSucc (belowSucc belowZero v8j0) v8j1)
private def l9v0 : List Lane := [zero! 4,⟨3,5,1,1,1⟩,⟨2,2,3,31,0x1fbffff5bf7fffd7feffff65⟩,⟨1,1,3,14,0x3b237c6760⟩,⟨0,0,3,31,0x1fbff224ff7f64ccfefb7b09⟩]
private def l9v1 : List Lane := [zero! 4,⟨3,4,1,1,1⟩,⟨2,2,2,31,0x3f7fffebfeffffb1⟩,⟨1,1,2,12,3702090⟩,⟨0,0,2,31,0x3f7fe622fefedec3⟩]
private def l9v2 : List Lane := [zero! 4,⟨3,3,1,1,1⟩,⟨2,2,1,31,0x7effffd8⟩,⟨1,1,1,10,861⟩,⟨0,0,1,31,0x7effcfcc⟩]
private def l9v3 : List Lane := [⟨4,4,1,1,1⟩,zero! 3,⟨2,2,1,31,0x7efffccd⟩,⟨1,1,1,15,22960⟩,⟨0,0,1,31,0x7efa59cb⟩]
private def z9 : CJ1.Block where
  bank := .leftHigh
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [l9v0,l9v1,l9v2,l9v3].map (vectorData true 61 2)
private def b9 := bands [(52,61,1),(51,59,2),(50,57,3),(49,55,3),(48,53,3),(47,51,3),(46,49,3),(45,47,3),(44,45,3),(43,43,3),(42,42,2),(41,41,1)]
private theorem k9v0 : good true 61 l9v0 b9 := rfl
private theorem v9j0 : VectorDots 61 2 z9 0 := v! true, 61, b9, l9v0, k9v0
private theorem k9v1 : good true 61 l9v1 b9 := rfl
private theorem v9j1 : VectorDots 61 2 z9 1 := v! true, 61, b9, l9v1, k9v1
private theorem k9v2 : good true 61 l9v2 b9 := rfl
private theorem v9j2 : VectorDots 61 2 z9 2 := v! true, 61, b9, l9v2, k9v2
private theorem k9v3 : good true 61 l9v3 b9 := rfl
private theorem v9j3 : VectorDots 61 2 z9 3 := v! true, 61, b9, l9v3, k9v3
theorem r9 : (rank! 61, 2) ≤ 21 :=
  cap! 61, 2, z9, (belowSucc (belowSucc (belowSucc (belowSucc belowZero v9j0) v9j1) v9j2) v9j3)
end CJ6_7
end
section
namespace CJ6_7
theorem proof : CJ6.c7 := ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, trivial⟩
end CJ6_7
end
