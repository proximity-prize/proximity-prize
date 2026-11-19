/- P33Base: window infrastructure for the 68.33 packet route (DRAFT, not compiled).
   Engine names are those of the port (lower-6833p/ProximityPrize/SubmissionLower/Packet6833P0*.lean);
   every declaration cites the 68.19 declaration it transcribes (B = lower-6819 CoreB.lean, A = CoreA.lean)
   and the port location (P07:<line>).  Requires the engine patch of MANIFEST.md §3 (QE : Fin 52, CN : Fin 2,
   fallback = CN 0, thigh 7200, helper bound 3e15, A-literals 181059/81085/...). -/
import ProximityPrize.SubmissionLower.Packet6833P07

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open MvPolynomial CW DJ DC BD DU EF CB HI DR LV AED ADB OZ CP PA RCN095 RCN234 RCN156
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- A packet window: the cell bound `(r, y, t)`, the factor-total floor `low`, the cap, and the H2 height
certificate `(Bh, Ch, qd, nh)` (FormalR.H2.Certificate, B 23108 / P06:5567). -/
structure Window where
  r : ℕ
  y : ℕ
  t : ℕ
  low : ℕ
  cap : ℕ
  Bh : ℕ
  Ch : ℕ
  qd : ℕ
  nh : ℕ
  deriving DecidableEq

/-- `ADD.decodeReceipts` (B 31366): `n` little-endian chunks of 132 bits. -/
def decodeReceipts : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, c => c % 2 ^ 132 :: decodeReceipts n (c / 2 ^ 132)

/-- `ADD.receiptBox` (B 31346), unchanged (box in bits 33..128, 8 × 12 bits). -/
def receiptBox (code : ℕ) : Box :=
  let x := code / 8589934592
  ⟨x % 4096, x / 4096 % 4096, x / 4096 ^ 2 % 4096, x / 4096 ^ 3 % 4096,
   x / 4096 ^ 4 % 4096, x / 4096 ^ 5 % 4096, x / 4096 ^ 6 % 4096, x / 4096 ^ 7 % 4096⟩

/-- `ADD.root` (B 31447) with the repaired root source `QE0 = ⟨38,438,16,7,52,0,1⟩`: `thi` 365 → 438. -/
def root (m : ℕ) : Box := ⟨max 1 m, 7, 2 * max 1 m, 16, 0, 52, 0, 438⟩

/-! ### The BandValid split (AED.BandValid, B 31190 / P07:4206) -/

/-- Window-independent part: checked once per shared leaf. -/
def BandPart (a : DR.Box) (m : ℕ) (i : Fin 52) (N : ℕ) : Prop :=
  let p := QE.profile i
  0 < m ∧ m ≤ a.slo ∧ 2 * a.slo ≤ a.bhi ∧
  a.shi ≤ 64 ∧ a.bhi ≤ 256 ∧ a.uhi ≤ 512 ∧ a.thi ≤ 4096 ∧
  DA.Impossible (ZGL.caps p) {powerBox p a m with q := N} ∧
  (∑ e ∈ Finset.range N, ZZ.bandCount (ZGL.caps p) (powerBox p a m) m e) < QE.kernel i ∧
  flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag < 2130706433 ∧
  flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag < 2130706433

instance (a : DR.Box) (m : ℕ) (i : Fin 52) (N : ℕ) : Decidable (BandPart a m i N) := by
  unfold BandPart; infer_instance

/-- Window part. -/
def PricePart (fixed : Degrees) (a : DR.Box) (m low t y r cap : ℕ) (i : Fin 52) (useOwner : Bool)
    (Bh Ch qd : ℕ) : Prop :=
  let p := QE.profile i
  let z := AED.pricing fixed a m useOwner
  a.thi < low ∧ p.L < low ∧ SN.Common z low t y r ∧ MG t y r ≤ cap ∧
  FormalR.H2.pairCostEH z 1 (ownerFlag a) (flag p.B p.U p.L p.s) Bh Ch qd t y r + leading z t y r ≤ cap

instance (fixed : Degrees) (a : DR.Box) (m low t y r cap : ℕ) (i : Fin 52) (useOwner : Bool) (Bh Ch qd : ℕ) :
    Decidable (PricePart fixed a m low t y r cap i useOwner Bh Ch qd) := by
  unfold PricePart SN.Common ER.Gates; infer_instance   -- as the BandValid instance (B 31205) unfolds `SN.Common Gates`

/-- The split is a re-association of the conjunction of `AED.BandValid` (after the engine patch to `Fin 53`). -/
theorem bandValid_of_parts (fixed : Degrees) (a : DR.Box) (m low t y r cap : ℕ) (i : Fin 52)
    (useOwner : Bool) (N Bh Ch qd : ℕ) (hb : BandPart a m i N)
    (hp : PricePart fixed a m low t y r cap i useOwner Bh Ch qd) :
    AED.BandValid fixed a m low t y r cap i useOwner N Bh Ch qd := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hb
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  exact ⟨h1, h2, h3, h4, h5, h6, h7, p1, p2, p3, p4, h8, h9, h10, h11, p5⟩

/-! ### Receipt tests, layout v2 (leandata/README.md §2) -/

/-- Window-free test. Kinds 0 (native) and 1 (linear) have no band part. -/
def bandTest (m code : ℕ) : Bool :=
  if code % 4 = 2 then
    if h : code / 4 % 64 < 52 then decide (BandPart (receiptBox code) m ⟨code / 4 % 64, h⟩ (code / 131072 % 65536))
    else false
  else true

/-- Window test: `ADD.receiptTest` (B 31350) with the pair branch restricted to `PricePart`,
profile index in bits 2..7, `useOwner` bit 8, CN index in bits 9..12 (< 2 after the patch). -/
def priceTest (W : Window) (m code : ℕ) : Bool :=
  let a := receiptBox code
  if code % 4 = 0 then BH.check .native (degrees OZ.fallback) a m W.low W.t W.y W.r W.cap
  else if code % 4 = 1 then decide (LinearValid a W.low W.t W.y W.r W.cap)
  else if code % 4 = 2 then
    if h : code / 4 % 64 < 52 ∧ code / 512 % 16 < 2 then
      decide ((CN.profile ⟨code / 512 % 16, h.2⟩).L < W.low ∧
        PricePart (degrees ⟨code / 512 % 16, h.2⟩) a m W.low W.t W.y W.r W.cap ⟨code / 4 % 64, h.1⟩
          (code / 256 % 2 = 1) W.Bh W.Ch W.qd)
    else false
  else false

/-- `ADD.receipt_sound` (B 31357) with both tests. -/
theorem receipt_sound (W : Window) (hcert : FormalR.H2.Certificate W.r W.y W.low W.Bh W.Ch W.qd W.nh)
    (m code : ℕ) (hb : bandTest m code = true) (hp : priceTest W m code = true) :
    OZ.Valid m W.low W.t W.y W.r W.cap (receiptBox code) := by
  unfold priceTest at hp
  unfold bandTest at hb
  split_ifs at hp with h0 h1 h2 h3
  · exact Or.inl hp
  · exact Or.inr (Or.inl (of_decide_eq_true hp))
  · have hh := of_decide_eq_true hp
    rw [if_pos h2, dif_pos h3.1] at hb
    have hbb := of_decide_eq_true hb
    exact Or.inr (Or.inr ⟨⟨code / 4 % 64, h3.1⟩, decide (code / 256 % 2 = 1), ⟨code / 512 % 16, h3.2⟩,
      code / 131072 % 65536, W.Bh, W.Ch, W.qd, W.nh, hh.1, hcert,
      bandValid_of_parts _ _ _ _ _ _ _ _ _ _ _ _ _ _ hbb hh.2⟩)

/-- Validity of the boxes of a shared list from the two `List.all` theorems (`ADD.boxesvalid*`, B 31440). -/
theorem boxes_valid (W : Window) (hcert : FormalR.H2.Certificate W.r W.y W.low W.Bh W.Ch W.qd W.nh)
    (m : ℕ) (codes : List ℕ) (hb : codes.all (bandTest m) = true) (hp : codes.all (priceTest W m) = true) :
    ∀ a ∈ codes.map receiptBox, OZ.Valid m W.low W.t W.y W.r W.cap a := by
  intro a ha
  obtain ⟨code, hc, rfl⟩ := List.mem_map.mp ha
  exact receipt_sound W hcert m code (List.all_eq_true.mp hb code hc) (List.all_eq_true.mp hp code hc)

/-- Coverage of `root m` from a shared tree whose `CP.check` was decided once (window-free):
`CP.sound` (B 30797 / P07:3903) + `CP.listBox_valid` (P07:3926). -/
theorem covered_of (W : Window) (hcert : FormalR.H2.Certificate W.r W.y W.low W.Bh W.Ch W.qd W.nh)
    (m : ℕ) (codes : List ℕ) (tree : Tree)
    (hb : codes.all (bandTest m) = true) (hp : codes.all (priceTest W m) = true)
    (htree : CP.check (CP.listBox (codes.map receiptBox)) (codes.map receiptBox).length m tree (root m) = true) :
    PA.Covered m (OZ.Valid m W.low W.t W.y W.r W.cap) (root m) :=
  CP.sound (CP.listBox (codes.map receiptBox)) (codes.map receiptBox).length m _
    (CP.listBox_valid _ _ (boxes_valid W hcert m codes hb hp)) tree (root m) htree

/-! ### The count of one window: `from_sources` + `packet_count` of a 68.19 window (B 31517–31565) -/

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

/-- The statement every window module proves. -/
def WindowCount (W : Window) : Prop :=
  ∀ {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] (nodes : I ↪ K) (_ : Fintype.card I = 262144)
    (P : DU.Packet (nodes : I → K) W.t W.y W.r),
    W.low ≤ wt ProximityPrize.SubmissionLower.RCN156.residualTotalWeights P.F → P.seeds.card ≤ W.cap

/- Transcription of `from_sources` (B 31517): `ADD.root` → `root`, `2985 < low` → `912 < low`
(BLH after the fallback patch), root profile `Profile S 16 52 365 7 0 1` → `… 438 …`. -/
section Sources
-- the 68.19 context of `from_sources` (B 31497-31507): these opens make the 68.19 short names resolve to the
-- port's declarations (GZ.ADG, GZ.AHY, GZ.Profile, NX.ADQ, LK.NT, LK.QC, YY.AVL, CB._Q15, CB.order,
-- ON.multiplicity, LV.point, FF.VT, KY.helper_count; port namespaces of 2026-11-19).
open DC FN DU ER EF BD GF NX GZ LK HI LV BH DR FF ZGL ON YY CB
open ProximityPrize.SubmissionLower.MovingFiberThreeSources6811 (Source Source.d)
open ProximityPrize.SubmissionLower.SecondJetCoefficients (asS)
open ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy (ratio)

/-- Transcription of `from_sources` (B 31517-31552). Changes: `ADD.root` → `root` (thi 365 → 438),
`2985 < low` → `912 < low` (patched `OZ.BLH`), root profile `Profile S 16 52 438 7 0 1`. -/
theorem from_sources {t y r cap low : ℕ} (hLow : 1700 < low) (nodes : I ↪ K) (hI : Fintype.card I = 262144)
    (P : DU.Packet (nodes : I → K) t y r) [Fact (Irreducible P.F)]
    (hFT : low ≤ wt ProximityPrize.SubmissionLower.RCN156.residualTotalWeights P.F)
    (S : ProximityPrize.SubmissionLower.MovingFiberThreeSources6811.Source P.F) (hS : GZ.Profile S 16 52 438 7 0 1)
    (hcap : 6000000000000000 ≤ cap) (hid : MG t y r ≤ cap)
    (hcov : ∀ m, 0 < m → m ≤ 7 → PA.Covered m (OZ.Valid m low t y r cap) (root m)) :
    P.seeds.card ≤ cap := by
  classical
  have hchar : P.F.degreeOf 2 < 2130706433 := P.IZ.2.1.trans_lt (by have := P.rhigh; omega)
  have hST : S.T = 438 := hS.2.2.1
  have hs := ADG P.F S (by rw [hST]; omega) P.rdegree hchar (by rw [hS.2.2.2.2.1]; decide)
  have hpow : (Polynomial.X - Polynomial.C (ratio (carrierMap P.F) P.F)) ^ 1 ∣ QC (carrierMap P.F) S.P := by
    change (Polynomial.X - Polynomial.C (ratio (carrierMap P.F) P.F)) ^ 1 ∣ (asS S.P).map (carrierMap P.F)
    simpa only [Source.d, hS.2.2.2.2.1, Nat.zero_add] using hs.2
  have hroot : NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P = 0 :=
    Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
  obtain ⟨J, hJ, hJS, hJroot, _⟩ :=
    ADQ (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
  obtain ⟨hJne, hm, hms, hJb, hJu, hJt, hJs⟩ := AVL P.F S (by rw [hST]; omega) J hJ hJS hJroot
  rw [hS.1] at hJb
  rw [hS.2.1] at hJu
  rw [hS.2.2.1] at hJt
  rw [hS.2.2.2.1] at hJs
  let m := multiplicity P.F J
  have hn := _Q15 J
  have horder : 1 ≤ order J := Nat.succ_le_of_lt (hm.trans_le hms)
  have hadm : PA.Admissible m (point J) := ⟨hms, horder, hn.2.2.1, hn.2.1, hn.2.2.2, hn.1⟩
  have hx : Contains (root m) (point J) := by
    dsimp only [Contains, root, point]
    refine ⟨max_le horder hms, hJs, ?_, hJb, Nat.zero_le _, hJu, Nat.zero_le _, hJt⟩
    have hh := hn.2.2.1
    omega
  obtain ⟨a, hvalid, ha⟩ := hcov m hm (hms.trans hJs) (point J) hadm hx
  exact OZ.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

/-- Transcription of the window `packet_count` (B 31553-31565), generic in the window: the root source from
`VT` at the repaired QE0 (`QE.q0 = ⟨38,438,16,7,52,0,1⟩`, kernel 48998482, P33Profiles1), the helper branch by
`KY.helper_count` with the patched bound `< 3·10^15`. The three `VT` size arguments are discharged as in
`GI.AGF` (B 30725-30727). -/
theorem window_count (W : Window) (hLow : 1700 < W.low) (hcap : 6000000000000000 ≤ W.cap)
    (hid : MG W.t W.y W.r ≤ W.cap)
    (hcov : ∀ m, 0 < m → m ≤ 7 → PA.Covered m (OZ.Valid m W.low W.t W.y W.r W.cap) (root m)) :
    WindowCount W := by
  intro K I _ _ _ nodes hI P hFT
  classical
  letI : Fact (Irreducible P.F) := ⟨P.irreducible⟩
  rcases VT QE.q0 QE.shape_q0 48998482 (by decide) QE.dimension_q0 nodes P.u0 P.u1 hI P.F P.irreducible
      (by change 438 < _; omega) W.r W.y W.t (by have := P.rlow; omega)
      (by have := P.rlow; have := P.ylow; omega) (by have := P.rlow; have := P.ylow; have := P.yt; omega)
      ⟨P.r_weight, P.y_weight, P.total_weight⟩ with ⟨Q, hQ⟩ | ⟨S, hS⟩
  · have hsmall : (QE.q0).B ≤ 256 ∧ (QE.q0).U ≤ 512 ∧ (QE.q0).L ≤ 4096 ∧ (QE.q0).s ≤ 64 := by decide
    have hh := KY.helper_count QE.q0 nodes P hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2 Q hQ
    -- hh : P.seeds.card < 3000000000000000 (patched DZN bound, MANIFEST §3.1)
    omega
  · exact from_sources hLow nodes hI P hFT S hS hcap hid hcov

end Sources

end P33
end SubmissionLower
end ProximityPrize
