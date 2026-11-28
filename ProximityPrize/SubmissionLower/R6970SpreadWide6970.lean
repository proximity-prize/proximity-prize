import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts

set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace Research6969.SpreadWide6970
open Finset Polynomial
open K1_14 (L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)
open Research6966
open scoped Classical

def shape : Shape := ⟨2978, 4145, 900, 530820⟩
abbrev box := SpreadCatalogue.box
def nodes : ℕ := 794969684312064
def moment : ℕ := 8121946626507

private theorem node_cap : P1_7_1.nodeRows shape ≤ nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

private theorem moment0 :
    P1_7_1_3.blockEstimate 4145 900 900 128 = 1448838560 := by
  decide +kernel

private theorem moment1 :
    P1_7_1_3.blockEstimate 4145 900 1028 128 = 9736541600 := by
  decide +kernel

private theorem moment2 :
    P1_7_1_3.blockEstimate 4145 900 1156 128 = 25505834400 := by
  decide +kernel

private theorem moment3 :
    P1_7_1_3.blockEstimate 4145 900 1284 128 = 47951410592 := by
  decide +kernel

private theorem moment4 :
    P1_7_1_3.blockEstimate 4145 900 1412 128 = 76267963808 := by
  decide +kernel

private theorem moment5 :
    P1_7_1_3.blockEstimate 4145 900 1540 128 = 109650187680 := by
  decide +kernel

private theorem moment6 :
    P1_7_1_3.blockEstimate 4145 900 1668 128 = 147292775840 := by
  decide +kernel

private theorem moment7 :
    P1_7_1_3.blockEstimate 4145 900 1796 128 = 187388715045 := by
  decide +kernel

private theorem moment8 :
    P1_7_1_3.blockEstimate 4145 900 1924 128 = 224987455808 := by
  decide +kernel

private theorem moment9 :
    P1_7_1_3.blockEstimate 4145 900 2052 128 = 258807161152 := by
  decide +kernel

private theorem moment10 :
    P1_7_1_3.blockEstimate 4145 900 2180 128 = 288847798592 := by
  decide +kernel

private theorem moment11 :
    P1_7_1_3.blockEstimate 4145 900 2308 128 = 315109368128 := by
  decide +kernel

private theorem moment12 :
    P1_7_1_3.blockEstimate 4145 900 2436 128 = 337591869760 := by
  decide +kernel

private theorem moment13 :
    P1_7_1_3.blockEstimate 4145 900 2564 128 = 356295303488 := by
  decide +kernel

private theorem moment14 :
    P1_7_1_3.blockEstimate 4145 900 2692 128 = 371219669312 := by
  decide +kernel

private theorem moment15 :
    P1_7_1_3.blockEstimate 4145 900 2820 128 = 382364967232 := by
  decide +kernel

private theorem moment16 :
    P1_7_1_3.blockEstimate 4145 900 2948 128 = 389731197248 := by
  decide +kernel

private theorem moment17 :
    P1_7_1_3.blockEstimate 4145 900 3076 128 = 393318359360 := by
  decide +kernel

private theorem moment18 :
    P1_7_1_3.blockEstimate 4145 900 3204 128 = 393126453568 := by
  decide +kernel

private theorem moment19 :
    P1_7_1_3.blockEstimate 4145 900 3332 128 = 389155479872 := by
  decide +kernel

private theorem moment20 :
    P1_7_1_3.blockEstimate 4145 900 3460 128 = 381405438272 := by
  decide +kernel

private theorem moment21 :
    P1_7_1_3.blockEstimate 4145 900 3588 128 = 369876328768 := by
  decide +kernel

private theorem moment22 :
    P1_7_1_3.blockEstimate 4145 900 3716 128 = 354568151360 := by
  decide +kernel

private theorem moment23 :
    P1_7_1_3.blockEstimate 4145 900 3844 128 = 335480906048 := by
  decide +kernel

private theorem moment24 :
    P1_7_1_3.blockEstimate 4145 900 3972 128 = 312614592832 := by
  decide +kernel

private theorem moment25 :
    P1_7_1_3.blockEstimate 4145 900 4100 128 = 286087449821 := by
  decide +kernel

private theorem moment26 :
    P1_7_1_3.blockEstimate 4145 900 4228 128 = 257459504382 := by
  decide +kernel

private theorem moment27 :
    P1_7_1_3.blockEstimate 4145 900 4356 128 = 228167475834 := by
  decide +kernel

private theorem moment28 :
    P1_7_1_3.blockEstimate 4145 900 4484 128 = 198784914211 := by
  decide +kernel

private theorem moment29 :
    P1_7_1_3.blockEstimate 4145 900 4612 128 = 169839938333 := by
  decide +kernel

private theorem moment30 :
    P1_7_1_3.blockEstimate 4145 900 4740 128 = 141832066090 := by
  decide +kernel

private theorem moment31 :
    P1_7_1_3.blockEstimate 4145 900 4868 128 = 115232214166 := by
  decide +kernel

private theorem moment32 :
    P1_7_1_3.blockEstimate 4145 900 4996 128 = 90415449580 := by
  decide +kernel

private theorem moment33 :
    P1_7_1_3.blockEstimate 4145 900 5124 128 = 67727365328 := by
  decide +kernel

private theorem moment34 :
    P1_7_1_3.blockEstimate 4145 900 5252 128 = 47862479056 := by
  decide +kernel

private theorem moment35 :
    P1_7_1_3.blockEstimate 4145 900 5380 128 = 31105768656 := by
  decide +kernel

private theorem moment36 :
    P1_7_1_3.blockEstimate 4145 900 5508 128 = 17708892368 := by
  decide +kernel

private theorem moment37 :
    P1_7_1_3.blockEstimate 4145 900 5636 128 = 7923508432 := by
  decide +kernel

private theorem moment38 :
    P1_7_1_3.blockEstimate 4145 900 5764 128 = 2001275088 := by
  decide +kernel

private theorem moment39 :
    P1_7_1_3.blockEstimate 4145 900 5892 53 = 55556837 := by
  decide +kernel

private theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment := by
  apply (P1_7_1_3.grouped_bound _ _).trans
  exact (P1_7_1_3_2.moment_from_blocks
    [(128,1448838560),(128,9736541600),(128,25505834400),(128,47951410592),
     (128,76267963808),(128,109650187680),(128,147292775840),(128,187388715045),
     (128,224987455808),(128,258807161152),(128,288847798592),(128,315109368128),
     (128,337591869760),(128,356295303488),(128,371219669312),(128,382364967232),
     (128,389731197248),(128,393318359360),(128,393126453568),(128,389155479872),
     (128,381405438272),(128,369876328768),(128,354568151360),(128,335480906048),
     (128,312614592832),(128,286087449821),(128,257459504382),(128,228167475834),
     (128,198784914211),(128,169839938333),(128,141832066090),(128,115232214166),
     (128,90415449580),(128,67727365328),(128,47862479056),(128,31105768656),
     (128,17708892368),(128,7923508432),(128,2001275088),(53,55556837)]
    ⟨moment0, moment1, moment2, moment3, moment4, moment5, moment6, moment7, moment8, moment9, moment10, moment11, moment12, moment13, moment14, moment15, moment16, moment17, moment18, moment19, moment20, moment21, moment22, moment23, moment24, moment25, moment26, moment27, moment28, moment29, moment30, moment31, moment32, moment33, moment34, moment35, moment36, moment37, moment38, moment39, True.intro⟩ (by decide) (by decide)).le

private theorem from_fee22 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) (e a n : ℕ)
    (ep : 0 < e) (ap : 0 < a)
    (full : 2*131071*SpreadInterval.maxOrder shape e < shape.m*179730)
    (cost : SpreadInterval.costSum shape 179730 e a n 2308 2313 ≤ 1307671998) :
    PadeCutoff.excluded 179730 h e a n shape box nodes moment := by
  apply SpreadInterval.excluded (by decide) lower upper (by decide) (by decide)
    ap ep (by decide) full
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _).trans_lt <;>
    decide +kernel

private theorem case22_7_20 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 22 7 20 shape box nodes moment := by
  apply from_fee22 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case22_8_21 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 22 8 21 shape box nodes moment := by
  apply from_fee22 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case22_9_22 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 22 9 22 shape box nodes moment := by
  apply from_fee22 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case22_12_22 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 22 12 22 shape box nodes moment := by
  apply from_fee22 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case22_13_22 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 22 13 22 shape box nodes moment := by
  apply from_fee22 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

theorem classify22 {h : ℕ} {D : PoleData h}
    (lower : 2308 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q ∈ S, Parent q) (pass : ∀ q ∈ S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (whole : ProjectedProduct S f) (large : 22 ≤ f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree ≤ 6 ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  have left (a : ℕ) (lo : 6 < a) (hi : a ≤ 9) :
      PadeCutoff.excluded 179730 h 22 a (22-9+a) shape box nodes moment := by
    interval_cases a
    · exact case22_7_20 lower upper
    · exact case22_8_21 lower upper
    · exact case22_9_22 lower upper
  have right (a : ℕ) (lo : 12 ≤ a) (hi : a ≤ 13) :
      PadeCutoff.excluded 179730 h 22 a 22 shape box nodes moment := by
    interval_cases a
    · exact case22_12_22 lower upper
    · exact case22_13_22 lower upper
  have fits : TerminalBanks.inside shape SpreadCatalogue.shape := by unfold TerminalBanks.inside; decide
  have width : shape.B*(131071-h) ≤ shape.m*179730 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lower 131071)).trans (by decide)
  obtain ⟨g, proof, small | graph⟩ :=
    PadeCutoff.counted_packet (A:=179730) (e:=22) (c:=9) (amax:=6)
      (by omega) (by omega) (by change h < 2130706433; omega) Crt word box fits (by decide) (by decide)
      (by decide) (by decide) width node_cap pole_cap S live geo pass (by decide) (by decide) left right
  · exact (Nat.not_lt_of_ge (large.trans_eq (Research6966.NearTerminal.same_degree whole proof)) small).elim
  · exact graph

private theorem from_fee24 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) (e a n : ℕ)
    (ep : 0 < e) (ap : 0 < a)
    (full : 2*131071*SpreadInterval.maxOrder shape e < shape.m*179730)
    (cost : SpreadInterval.costSum shape 179730 e a n 2300 2313 ≤ 1298479684) :
    PadeCutoff.excluded 179730 h e a n shape box nodes moment := by
  apply SpreadInterval.excluded (by decide) lower upper (by decide) (by decide)
    ap ep (by decide) full
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _).trans_lt <;>
    decide +kernel

private theorem case24_6_21 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 6 21 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_7_22 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 7 22 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_8_23 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 8 23 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_9_24 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 9 24 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_13_24 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 13 24 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_14_24 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 14 24 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case24_15_24 {h : ℕ} (lower : 2300 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 24 15 24 shape box nodes moment := by
  apply from_fee24 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

theorem classify24 {h : ℕ} {D : PoleData h}
    (lower : 2300 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q ∈ S, Parent q) (pass : ∀ q ∈ S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (whole : ProjectedProduct S f) (large : 24 ≤ f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree ≤ 5 ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  have left (a : ℕ) (lo : 5 < a) (hi : a ≤ 9) :
      PadeCutoff.excluded 179730 h 24 a (24-9+a) shape box nodes moment := by
    interval_cases a
    · exact case24_6_21 lower upper
    · exact case24_7_22 lower upper
    · exact case24_8_23 lower upper
    · exact case24_9_24 lower upper
  have right (a : ℕ) (lo : 13 ≤ a) (hi : a ≤ 15) :
      PadeCutoff.excluded 179730 h 24 a 24 shape box nodes moment := by
    interval_cases a
    · exact case24_13_24 lower upper
    · exact case24_14_24 lower upper
    · exact case24_15_24 lower upper
  have fits : TerminalBanks.inside shape SpreadCatalogue.shape := by unfold TerminalBanks.inside; decide
  have width : shape.B*(131071-h) ≤ shape.m*179730 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lower 131071)).trans (by decide)
  obtain ⟨g, proof, small | graph⟩ :=
    PadeCutoff.counted_packet (A:=179730) (e:=24) (c:=9) (amax:=5)
      (by omega) (by omega) (by change h < 2130706433; omega) Crt word box fits (by decide) (by decide)
      (by decide) (by decide) width node_cap pole_cap S live geo pass (by decide) (by decide) left right
  · exact (Nat.not_lt_of_ge (large.trans_eq (Research6966.NearTerminal.same_degree whole proof)) small).elim
  · exact graph

/-- A stronger control for any already fixed primitive graph on the same sheets. -/
theorem tighten_nine22 {h : ℕ} {D : PoleData h}
    (lower : 2308 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q∈S, Parent q) (pass : ∀ q∈S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (project : ProjectedProduct S f) (large : 22 ≤ f.natDegree)
    {G : Pade.Row SeedField} (gp : G.primitive) {c : ℕ} (room : 9 ≤ c) (gap : 2*c < f.natDegree)
    (weak : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) c) :
    Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  classical
  obtain ⟨H, hp, _, strong⟩ := classify22 lower upper Crt word S live geo pass project large
  obtain ⟨f', T, v, project', size, on⟩ := Pade.Native.projected_sheets S live geo
  have eq : f.natDegree = T.card := (NearTerminal.same_degree project project').trans size.symm
  let emb : SeedField →+* Pade.Native.Sep := algebraMap _ _
  have relaxed : Pade.Controls (H.map emb) (Pade.Native.sheets S) c :=
    fun t v valid => (strong t v valid).trans room
  obtain ⟨t, nz, same⟩ := Pade.unique_control (Pade.Native.sheets S) T.card c
    (by omega) ⟨T,v,rfl,on⟩ ((Pade.Row.primitive_map emb).mpr hp)
    ((Pade.Row.primitive_map emb).mpr gp) relaxed weak
  change Pade.Controls (G.map emb) (Pade.Native.sheets S) 9
  rw [same]
  exact Pade.Controls.scale strong nz

/-- A stronger control for any already fixed primitive graph on the same sheets. -/
theorem tighten_nine24 {h : ℕ} {D : PoleData h}
    (lower : 2300 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q∈S, Parent q) (pass : ∀ q∈S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (project : ProjectedProduct S f) (large : 24 ≤ f.natDegree)
    {G : Pade.Row SeedField} (gp : G.primitive) {c : ℕ} (room : 9 ≤ c) (gap : 2*c < f.natDegree)
    (weak : Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) c) :
    Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  classical
  obtain ⟨H, hp, _, strong⟩ := classify24 lower upper Crt word S live geo pass project large
  obtain ⟨f', T, v, project', size, on⟩ := Pade.Native.projected_sheets S live geo
  have eq : f.natDegree = T.card := (NearTerminal.same_degree project project').trans size.symm
  let emb : SeedField →+* Pade.Native.Sep := algebraMap _ _
  have relaxed : Pade.Controls (H.map emb) (Pade.Native.sheets S) c :=
    fun t v valid => (strong t v valid).trans room
  obtain ⟨t, nz, same⟩ := Pade.unique_control (Pade.Native.sheets S) T.card c
    (by omega) ⟨T,v,rfl,on⟩ ((Pade.Row.primitive_map emb).mpr hp)
    ((Pade.Row.primitive_map emb).mpr gp) relaxed weak
  change Pade.Controls (G.map emb) (Pade.Native.sheets S) 9
  rw [same]
  exact Pade.Controls.scale strong nz

private theorem from_fee28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) (e a n : ℕ)
    (ep : 0 < e) (ap : 0 < a)
    (full : 2*131071*SpreadInterval.maxOrder shape e < shape.m*179730)
    (cost : SpreadInterval.costSum shape 179730 e a n 2308 2313 ≤ 1300774142) :
    PadeCutoff.excluded 179730 h e a n shape box nodes moment := by
  apply SpreadInterval.excluded (by decide) lower upper (by decide) (by decide)
    ap ep (by decide) full
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _).trans_lt <;>
    decide +kernel

private theorem case28_5_24 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 5 24 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_6_25 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 6 25 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_7_26 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 7 26 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_8_27 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 8 27 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_9_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 9 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_15_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 15 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_16_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 16 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_17_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 17 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_18_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 18 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case28_19_28 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 28 19 28 shape box nodes moment := by
  apply from_fee28 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

theorem classify28 {h : ℕ} {D : PoleData h}
    (lower : 2308 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q ∈ S, Parent q) (pass : ∀ q ∈ S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (whole : ProjectedProduct S f) (large : 28 ≤ f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree ≤ 4 ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  have left (a : ℕ) (lo : 4 < a) (hi : a ≤ 9) :
      PadeCutoff.excluded 179730 h 28 a (28-9+a) shape box nodes moment := by
    interval_cases a
    · exact case28_5_24 lower upper
    · exact case28_6_25 lower upper
    · exact case28_7_26 lower upper
    · exact case28_8_27 lower upper
    · exact case28_9_28 lower upper
  have right (a : ℕ) (lo : 15 ≤ a) (hi : a ≤ 28-9) :
      PadeCutoff.excluded 179730 h 28 a 28 shape box nodes moment := by
    interval_cases a
    · exact case28_15_28 lower upper
    · exact case28_16_28 lower upper
    · exact case28_17_28 lower upper
    · exact case28_18_28 lower upper
    · exact case28_19_28 lower upper
  have fits : TerminalBanks.inside shape SpreadCatalogue.shape := by unfold TerminalBanks.inside; decide
  have width : shape.B*(131071-h) ≤ shape.m*179730 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lower 131071)).trans (by decide)
  obtain ⟨g, proof, small | graph⟩ :=
    PadeCutoff.counted_packet (A:=179730) (e:=28) (c:=9) (amax:=4)
      (by omega) (by omega) (by change h < 2130706433; omega) Crt word box fits (by decide) (by decide)
      (by decide) (by decide) width node_cap pole_cap S live geo pass (by decide) (by decide) left right
  · exact (Nat.not_lt_of_ge (large.trans_eq (NearTerminal.same_degree whole proof)) small).elim
  · exact graph

private theorem from_fee37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) (e a n : ℕ)
    (ep : 0 < e) (ap : 0 < a)
    (full : 2*131071*SpreadInterval.maxOrder shape e < shape.m*179730)
    (cost : SpreadInterval.costSum shape 179730 e a n 2308 2313 ≤ 1307234228) :
    PadeCutoff.excluded 179730 h e a n shape box nodes moment := by
  apply SpreadInterval.excluded (by decide) lower upper (by decide) (by decide)
    ap ep (by decide) full
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _).trans_lt <;>
    decide +kernel

private theorem case37_4_32 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 4 32 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_5_33 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 5 33 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_6_34 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 6 34 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_7_35 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 7 35 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_8_36 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 8 36 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_9_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 9 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_19_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 19 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_20_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 20 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_21_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 21 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_22_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 22 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_23_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 23 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_24_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 24 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_25_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 25 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_26_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 26 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_27_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 27 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

private theorem case37_28_37 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 37 28 37 shape box nodes moment := by
  apply from_fee37 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

theorem classify37 {h : ℕ} {D : PoleData h}
    (lower : 2308 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q ∈ S, Parent q) (pass : ∀ q ∈ S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (whole : ProjectedProduct S f) (large : 37 ≤ f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree ≤ 3 ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  have left (a : ℕ) (lo : 3 < a) (hi : a ≤ 9) :
      PadeCutoff.excluded 179730 h 37 a (37-9+a) shape box nodes moment := by
    interval_cases a
    · exact case37_4_32 lower upper
    · exact case37_5_33 lower upper
    · exact case37_6_34 lower upper
    · exact case37_7_35 lower upper
    · exact case37_8_36 lower upper
    · exact case37_9_37 lower upper
  have right (a : ℕ) (lo : 19 ≤ a) (hi : a ≤ 37-9) :
      PadeCutoff.excluded 179730 h 37 a 37 shape box nodes moment := by
    interval_cases a
    · exact case37_19_37 lower upper
    · exact case37_20_37 lower upper
    · exact case37_21_37 lower upper
    · exact case37_22_37 lower upper
    · exact case37_23_37 lower upper
    · exact case37_24_37 lower upper
    · exact case37_25_37 lower upper
    · exact case37_26_37 lower upper
    · exact case37_27_37 lower upper
    · exact case37_28_37 lower upper
  have fits : TerminalBanks.inside shape SpreadCatalogue.shape := by unfold TerminalBanks.inside; decide
  have width : shape.B*(131071-h) ≤ shape.m*179730 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lower 131071)).trans (by decide)
  obtain ⟨g, proof, small | graph⟩ :=
    PadeCutoff.counted_packet (A:=179730) (e:=37) (c:=9) (amax:=3)
      (by omega) (by omega) (by change h < 2130706433; omega) Crt word box fits (by decide) (by decide)
      (by decide) (by decide) width node_cap pole_cap S live geo pass (by decide) (by decide) left right
  · exact (Nat.not_lt_of_ge (large.trans_eq (NearTerminal.same_degree whole proof)) small).elim
  · exact graph

private theorem from_fee64 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) (e a n : ℕ)
    (ep : 0 < e) (ap : 0 < a)
    (full : 2*131071*SpreadInterval.maxOrder shape e < shape.m*179730)
    (cost : SpreadInterval.costSum shape 179730 e a n 2308 2313 ≤ 1309392712) :
    PadeCutoff.excluded 179730 h e a n shape box nodes moment := by
  apply SpreadInterval.excluded (by decide) lower upper (by decide) (by decide)
    ap ep (by decide) full
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _).trans_lt <;>
    decide +kernel

private theorem case64_3_58 {h : ℕ} (lower : 2308 ≤ h) (upper : h ≤ 2313) :
    PadeCutoff.excluded 179730 h 64 3 58 shape box nodes moment := by
  apply from_fee64 lower upper _ _ _ (by decide) (by decide) (by decide)
  decide +kernel

theorem classify64 {h : ℕ} {D : PoleData h}
    (lower : 2308 ≤ h) (upper : h ≤ 2313) (Crt : CRTLift D) (word : K1.I → L)
    (S : Finset Surface) (live : S.Nonempty)
    (geo : ∀ q ∈ S, Parent q) (pass : ∀ q ∈ S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {f : Equation} (whole : ProjectedProduct S f) (large : 64 ≤ f.natDegree) :
    ∃ G : Pade.Row SeedField, G.primitive ∧ G.graphDegree ≤ 2 ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) 9 := by
  classical
  obtain ⟨G, gp, deg, strong⟩ :=
    classify37 lower upper Crt word S live geo pass whole ((by decide : 37 ≤ 64).trans large)
  refine ⟨G,gp,?_,strong⟩
  by_contra bad
  have eq : G.graphDegree = 3 := by omega
  obtain ⟨f', T, v, proj, size, onSheet⟩ := Pade.Native.projected_sheets S live geo
  let H := G.map (algebraMap SeedField Pade.Native.Sep)
  let on := T.filter (fun y => H.err v y = 0)
  let away := T \ on
  have miss := strong away v (by
    intro y hy
    obtain ⟨mem, out⟩ := mem_sdiff.mp hy
    exact ⟨onSheet y mem, fun zero => out (mem_filter.mpr ⟨mem,zero⟩)⟩)
  rw [Pade.Row.degree_map,eq] at miss
  have total : on.card + away.card = T.card := by
    rw [Nat.add_comm]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have sz : 64 ≤ T.card := large.trans_eq ((NearTerminal.same_degree whole proj).trans size.symm)
  obtain ⟨kept, subset, keepSize⟩ := exists_subset_card_eq (show 58 ≤ on.card by omega)
  let emb : Pade.Native.Sep →+* K1_14_3.SeedClosure :=
    (separableClosure SeedField K1_14_3.SeedClosure).val.toRingHom
  let pts := kept.image emb
  let slope (z : K1_14_3.SeedClosure) := if t : ∃ y∈kept, emb y=z then emb (v t.choose) else 0
  have atPoint y (hy : y∈kept) : slope (emb y) = emb (v y) := by
    have t : ∃ z∈kept, emb z=emb y := ⟨y,hy,rfl⟩
    simp only [slope,dite_eq_left t,emb.injective t.choose_spec.2]
  have keptCount : pts.card = 58 := (card_image_of_injective _ emb.injective).trans keepSize
  have fits : TerminalBanks.inside shape SpreadCatalogue.shape := by unfold TerminalBanks.inside; decide
  have width : shape.B*(131071-h) ≤ shape.m*179730 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lower 131071)).trans (by decide)
  have price := PadeCutoff.not_excluded (h:=h) (A:=179730) (e:=64)
    (by omega) (by omega) (by change h < 2130706433; omega) Crt word box fits (by decide) (by decide)
    (by decide) (by decide) width node_cap pole_cap geo pass whole (by decide) large pts slope
    ((H.primitive_map emb).mpr ((G.primitive_map (algebraMap SeedField Pade.Native.Sep)).mpr gp)) (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      rw [atPoint z hz]
      obtain ⟨mem, hit⟩ := mem_filter.mp (subset hz)
      refine ⟨(Pade.Native.sheets_iff ..).mp (onSheet z mem),?_⟩
      change (H.a.map emb).eval (emb z)*slope (emb z) - (H.b.map emb).eval (emb z) = 0
      rw [atPoint z hz]
      simpa only [Pade.Row.err,map_sub,map_mul,eval_map_apply,map_zero] using congrArg emb hit)
  have hd : H.graphDegree = 3 := (Pade.Row.degree_map _ _).trans eq
  apply price
  rw [Pade.Row.degree_map,hd,keptCount]
  exact case64_3_58 lower upper

end Research6969.SpreadWide6970
