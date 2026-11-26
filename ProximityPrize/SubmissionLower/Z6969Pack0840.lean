import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6969Pack0832
import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight
import ProximityPrize.SubmissionLower.Z6969Pack0838
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969RetainedTariffs
section Z6969Source2297
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Research6969.Low6969RetainedTariffs

open K1_13 (Shape)
open Low6969CubicTariff (fatPrice)

def splitFee (b j b₁ j₁ : ℕ) : ℕ :=
  let b₂ := b - b₁
  let j₂ := j - j₁
  if 0 < b₁ ∧ b₁ < b ∧ 3 ≤ j₁ ∧ j₁ + 3 ≤ j ∧
      j₁ ≤ 3 * b₁ ∧ j₂ ≤ 3 * b₂ then
    fatPrice ⟨b₁, j₁, 1⟩ + fatPrice ⟨b₂, j₂, 1⟩
  else 0

/-- The retained tariff takes the largest fee over the single-factor and two-factor possibilities. -/
def price (x : Shape) : ℕ :=
  if x.t = 0 then 0
  else if x.t = 1 then fatPrice x
  else
    (List.range x.b).foldl
      (fun p b => (List.range x.j).foldl (fun q j => max q (splitFee x.b x.j b j)) p)
      (fatPrice x)

private def checked (r : Shape × ℕ) : Bool := decide (price r.1 = r.2)

private def block0 : List (Shape × ℕ) :=
  [(⟨0, 0, 0⟩, 0), (⟨1, 3, 1⟩, 2434031833947685),
   (⟨2, 3, 1⟩, 2434031833947685), (⟨3, 3, 1⟩, 2434031833947685),
   (⟨4, 3, 1⟩, 2802886806337058), (⟨5, 3, 1⟩, 3179034030225272)]

private theorem block0_ok : block0.all checked = true := by decide +kernel

private def block1 : List (Shape × ℕ) :=
  [(⟨6, 3, 1⟩, 3564607820391845), (⟨7, 3, 1⟩, 3961742491616299),
   (⟨8, 3, 1⟩, 4372572358678153), (⟨9, 3, 1⟩, 4799231736356926),
   (⟨10, 3, 1⟩, 5243854939432141), (⟨11, 3, 1⟩, 5708576282683314)]

private theorem block1_ok : block1.all checked = true := by decide +kernel

private def block2 : List (Shape × ℕ) :=
  [(⟨12, 3, 1⟩, 6195530080889967), (⟨13, 3, 1⟩, 6706850648831621),
   (⟨14, 3, 1⟩, 7244672301287795), (⟨15, 3, 1⟩, 7811129353038009),
   (⟨16, 3, 1⟩, 8408356118861782), (⟨17, 3, 1⟩, 9038486913538637)]

private theorem block2_ok : block2.all checked = true := by decide +kernel

private def block3 : List (Shape × ℕ) :=
  [(⟨18, 3, 1⟩, 9703656051848090), (⟨19, 3, 1⟩, 10405997848569663),
   (⟨20, 3, 1⟩, 11147646618482877), (⟨21, 3, 1⟩, 11930736676367251),
   (⟨22, 3, 1⟩, 12757402337002305), (⟨23, 3, 1⟩, 13629777915167558)]

private theorem block3_ok : block3.all checked = true := by decide +kernel

private def block4 : List (Shape × ℕ) :=
  [(⟨24, 3, 1⟩, 14549997725642532), (⟨25, 3, 1⟩, 15520196083206746),
   (⟨26, 3, 1⟩, 16542507302639719), (⟨27, 3, 1⟩, 17619065698720973),
   (⟨2, 4, 1⟩, 5571830351553982), (⟨3, 4, 1⟩, 5571830351553982)]

private theorem block4_ok : block4.all checked = true := by decide +kernel

private def block5 : List (Shape × ℕ) :=
  [(⟨4, 4, 1⟩, 5571830351553982), (⟨5, 4, 1⟩, 6484175345816099),
   (⟨6, 4, 1⟩, 7405946906356576), (⟨7, 4, 1⟩, 8339279347954934),
   (⟨8, 4, 1⟩, 9286306985390691), (⟨9, 4, 1⟩, 10249164133443368)]

private theorem block5_ok : block5.all checked = true := by decide +kernel

private def block6 : List (Shape × ℕ) :=
  [(⟨10, 4, 1⟩, 11229985106892486), (⟨11, 4, 1⟩, 12230904220517563),
   (⟨12, 4, 1⟩, 13254055789098120), (⟨13, 4, 1⟩, 14301574127413678),
   (⟨14, 4, 1⟩, 15375593550243755), (⟨15, 4, 1⟩, 16478248372367872)]

private theorem block6_ok : block6.all checked = true := by decide +kernel

private def block7 : List (Shape × ℕ) :=
  [(⟨16, 4, 1⟩, 17611672908565549), (⟨17, 4, 1⟩, 18778001473616307),
   (⟨18, 4, 1⟩, 19979368382299664), (⟨19, 4, 1⟩, 21217907949395141),
   (⟨20, 4, 1⟩, 22495754489682259), (⟨21, 4, 1⟩, 23815042317940536)]

private theorem block7_ok : block7.all checked = true := by decide +kernel

private def block8 : List (Shape × ℕ) :=
  [(⟨22, 4, 1⟩, 25177905748949493), (⟨23, 4, 1⟩, 26586479097488651),
   (⟨24, 4, 1⟩, 28042896678337528), (⟨25, 4, 1⟩, 29549292806275645),
   (⟨2, 5, 1⟩, 11725843896239803), (⟨3, 5, 1⟩, 11725843896239803)]

private theorem block8_ok : block8.all checked = true := by decide +kernel

private def block9 : List (Shape × ℕ) :=
  [(⟨4, 5, 1⟩, 11725843896239803), (⟨5, 5, 1⟩, 11725843896239803),
   (⟨6, 5, 1⟩, 13421814296103709), (⟨7, 5, 1⟩, 15129345577025494),
   (⟨8, 5, 1⟩, 16850572053784679), (⟨9, 5, 1⟩, 18587628041160784)]

private theorem block9_ok : block9.all checked = true := by decide +kernel

private def block10 : List (Shape × ℕ) :=
  [(⟨10, 5, 1⟩, 20342647853933330), (⟨11, 5, 1⟩, 22117765806881835),
   (⟨12, 5, 1⟩, 23915116214785820), (⟨13, 5, 1⟩, 25736833392424805),
   (⟨14, 5, 1⟩, 27585051654578311), (⟨15, 5, 1⟩, 29461905316025856)]

private theorem block10_ok : block10.all checked = true := by decide +kernel

private def block11 : List (Shape × ℕ) :=
  [(⟨16, 5, 1⟩, 31369528691546961), (⟨17, 5, 1⟩, 33310056095921146),
   (⟨18, 5, 1⟩, 35285621843927932), (⟨19, 5, 1⟩, 37298360250346837),
   (⟨20, 5, 1⟩, 39350405629957382), (⟨21, 5, 1⟩, 41443892297539087)]

private theorem block11_ok : block11.all checked = true := by decide +kernel

private def block12 : List (Shape × ℕ) :=
  [(⟨22, 5, 1⟩, 43580954567871473), (⟨2, 6, 1⟩, 20223082787486900),
   (⟨3, 6, 1⟩, 20223082787486900), (⟨4, 6, 1⟩, 20223082787486900),
   (⟨5, 6, 1⟩, 20223082787486900), (⟨6, 6, 1⟩, 20223082787486900)]

private theorem block12_ok : block12.all checked = true := by decide +kernel

private def block13 : List (Shape × ℕ) :=
  [(⟨7, 6, 1⟩, 22644618279627392), (⟨8, 6, 1⟩, 25079848967605284),
   (⟨9, 6, 1⟩, 27530909166200097), (⟨10, 6, 1⟩, 29999933190191349),
   (⟨11, 6, 1⟩, 32489055354358562), (⟨12, 6, 1⟩, 35000409973481254)]

private theorem block13_ok : block13.all checked = true := by decide +kernel

private def block14 : List (Shape × ℕ) :=
  [(⟨13, 6, 1⟩, 37536131362338947), (⟨14, 6, 1⟩, 40098353835711159),
   (⟨15, 6, 1⟩, 42689211708377411), (⟨16, 6, 1⟩, 45310839295117224),
   (⟨17, 6, 1⟩, 47965370910710116), (⟨18, 6, 1⟩, 50654940869935609)]

private theorem block14_ok : block14.all checked = true := by decide +kernel

private def block15 : List (Shape × ℕ) :=
  [(⟨19, 6, 1⟩, 53381683487573221), (⟨2, 6, 2⟩, 65508508111169778),
   (⟨3, 6, 2⟩, 65508508111169788), (⟨4, 6, 2⟩, 65508508111169802),
   (⟨5, 6, 2⟩, 65508508111169820), (⟨6, 6, 2⟩, 65508508111169842)]

private theorem block15_ok : block15.all checked = true := by decide +kernel

private def block16 : List (Shape × ℕ) :=
  [(⟨7, 6, 2⟩, 74691876499336123), (⟨8, 6, 2⟩, 83929673187181927),
   (⟨9, 6, 2⟩, 93230435945950776), (⟨10, 6, 2⟩, 102602702546886188),
   (⟨11, 6, 2⟩, 112055010761231685), (⟨12, 6, 2⟩, 121595898360230785)]

private theorem block16_ok : block16.all checked = true := by decide +kernel

private def block17 : List (Shape × ℕ) :=
  [(⟨13, 6, 2⟩, 131233903115127010), (⟨14, 6, 2⟩, 140977562797163878),
   (⟨15, 6, 2⟩, 150835415177584910), (⟨16, 6, 2⟩, 160815998027633626),
   (⟨17, 6, 2⟩, 170927849118553547), (⟨18, 6, 2⟩, 181179506221588191)]

private theorem block17_ok : block17.all checked = true := by decide +kernel

private def block18 : List (Shape × ℕ) :=
  [(⟨19, 6, 2⟩, 191579507107981080), (⟨3, 7, 1⟩, 31212314796680660),
   (⟨4, 7, 1⟩, 31212314796680660), (⟨5, 7, 1⟩, 31212314796680660),
   (⟨6, 7, 1⟩, 31212314796680660), (⟨7, 7, 1⟩, 31212314796680660)]

private theorem block18_ok : block18.all checked = true := by decide +kernel

private def block19 : List (Shape × ℕ) :=
  [(⟨8, 7, 1⟩, 34361549695877260), (⟨9, 7, 1⟩, 37526614105690780),
   (⟨10, 7, 1⟩, 40709642340900739), (⟨11, 7, 1⟩, 43912768716286659),
   (⟨12, 7, 1⟩, 47138127546628058), (⟨13, 7, 1⟩, 50387853146704458)]

private theorem block19_ok : block19.all checked = true := by decide +kernel

private def block20 : List (Shape × ℕ) :=
  [(⟨14, 7, 1⟩, 53664079831295379), (⟨3, 7, 2⟩, 118134619821897815),
   (⟨4, 7, 2⟩, 118134619821897829), (⟨5, 7, 2⟩, 118134619821897847),
   (⟨6, 7, 2⟩, 118134619821897869), (⟨7, 7, 2⟩, 118134619821897895)]

private theorem block20_ok : block20.all checked = true := by decide +kernel

private def block21 : List (Shape × ℕ) :=
  [(⟨8, 7, 2⟩, 132045962365354734), (⟨9, 7, 2⟩, 146020270979734619),
   (⟨10, 7, 2⟩, 160066083436281068), (⟨11, 7, 2⟩, 174191937506237599),
   (⟨12, 7, 2⟩, 188406370960847736), (⟨13, 7, 2⟩, 202717921571354995)]

private theorem block21_ok : block21.all checked = true := by decide +kernel

private def block22 : List (Shape × ℕ) :=
  [(⟨14, 7, 2⟩, 217135127109002900), (⟨3, 8, 1⟩, 44695674238600604),
   (⟨4, 8, 1⟩, 44695674238600604), (⟨5, 8, 1⟩, 44695674238600604),
   (⟨6, 8, 1⟩, 44695674238600604), (⟨3, 8, 2⟩, 167699524331809257)]

private theorem block22_ok : block22.all checked = true := by decide +kernel

private def block23 : List (Shape × ℕ) :=
  [(⟨4, 8, 2⟩, 187908208046024844), (⟨5, 8, 2⟩, 187908208046024862), (⟨6, 8, 2⟩, 187908208046024884)]

private theorem block23_ok : block23.all checked = true := by decide +kernel

def rows : List (Shape × ℕ) :=
  block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++
    block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++
    block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++
    block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23

theorem row_count : rows.length = 141 := by decide +kernel

theorem row_price {r : Shape × ℕ} (h : r ∈ rows) : price r.1 = r.2 := by
  have checks : rows.all checked = true := by
    simp only [rows, List.all_append, Bool.and_true, block0_ok, block1_ok, block2_ok, block3_ok, block4_ok, block5_ok, block6_ok, block7_ok, block8_ok, block9_ok, block10_ok, block11_ok, block12_ok, block13_ok, block14_ok, block15_ok, block16_ok, block17_ok, block18_ok, block19_ok, block20_ok, block21_ok, block22_ok, block23_ok]
  exact of_decide_eq_true (List.all_eq_true.mp checks _ h)

theorem covers_shape {x : Shape} (box : Low6969Retained.Box x)
    (valid : K1_13_8.Valid x) : x ∈ rows.map Prod.fst := by
  rcases x with ⟨b, j, t⟩
  obtain ⟨hb, hj, h4, h5, h6, h7, h8⟩ := box
  obtain ⟨ht, htj, hjb⟩ := valid
  change b ≤ 27 at hb
  change j ≤ 8 at hj
  change 4 ≤ j → b ≤ 25 at h4
  change 5 ≤ j → b ≤ 22 at h5
  change 6 ≤ j → b ≤ 19 at h6
  change 7 ≤ j → b ≤ 14 at h7
  change 8 ≤ j → b ≤ 6 at h8
  change 0 < t at ht
  change 3 * t ≤ j at htj
  change j ≤ 3 * b at hjb
  have hjlo : 3 ≤ j := by omega
  have htmax : t ≤ 2 := by omega
  interval_cases j <;> interval_cases t <;> interval_cases b <;>
    first | (exfalso; omega) | decide +kernel

theorem covers_empty : (⟨0, 0, 0⟩ : Shape) ∈ rows.map Prod.fst := by decide +kernel

private def lookup (x : Shape) : List (Shape × ℕ) → ℕ
  | [] => 0
  | r :: rs => if r.1 = x then r.2 else lookup x rs

def tariff (x : Shape) : ℕ := lookup x rows

private theorem lookup_eq (x : Shape) (l : List (Shape × ℕ))
    (valid : ∀ r ∈ l, price r.1 = r.2) (mem : x ∈ l.map Prod.fst) :
    lookup x l = price x := by
  induction l with
  | nil => exact (List.not_mem_nil mem).elim
  | cons r rs ih =>
    by_cases h : r.1 = x
    · rw [lookup, ite_eq_left h, ← h]
      exact (valid r (List.mem_cons_self ..)).symm
    · rw [lookup, ite_eq_right h]
      exact ih (fun y hy => valid y (List.mem_cons_of_mem _ hy))
        ((List.mem_cons.mp mem).resolve_left (Ne.symm h))

theorem tariff_eq (x : Shape) (mem : x ∈ rows.map Prod.fst) :
    tariff x = price x :=
  lookup_eq x rows (fun _ h => row_price h) mem


end Research6969.Low6969RetainedTariffs
end Z6969Source2297

-- Source: ProximityPrize.SubmissionLower.Low6969AllocCore
section Z6969Source2298
set_option autoImplicit true
set_option Elab.async false

namespace Low6969MassCheck
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open P3_6_8_1 (sumBelow sumBelow_eq sumBelow_add)
theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]
def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs
theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]
end Low6969MassCheck

-- merged module R6960Low6969AllocCore
section Merged_R6960Low6969AllocCore

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Low6969Allocation
open Finset
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape Valid)
open K1_13_8_2 (Threshold orderFor)
open Final50PriceLayer (availableMass fastLayer layerTerm)
open LowProfile6966 (lowDegreeCap degree_bound)
open Low6969Retained (Box)
open LowProfile6969 (need layerCount)

open Low6969MassCheck (check check_sum mass_eq)
open P3_6_8_1 (sumBelow)
open scoped BigOperators Classical

abbrev Band := Fin 40
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData := [
  ⟨0,0,0,0,0⟩,
  ⟨1,1,3,1,2434031833947685⟩,
  ⟨2,2,3,1,2434031833947685⟩,
  ⟨3,3,3,1,2434031833947685⟩,
  ⟨4,4,3,1,2802886806337058⟩,
  ⟨5,5,3,1,3179034030225272⟩,
  ⟨6,6,3,1,3564607820391845⟩,
  ⟨7,7,3,1,3961742491616299⟩,
  ⟨8,8,3,1,4372572358678153⟩,
  ⟨9,9,3,1,4799231736356926⟩,
  ⟨2,2,4,1,5571830351553982⟩,
  ⟨3,3,4,1,5571830351553982⟩,
  ⟨4,4,4,1,5571830351553982⟩,
  ⟨5,13,4,1,14301574127413678⟩,
  ⟨10,20,3,1,11147646618482877⟩,
  ⟨21,27,3,1,17619065698720973⟩,
  ⟨14,25,4,1,29549292806275645⟩,
  ⟨2,9,5,1,18587628041160784⟩,
  ⟨10,16,5,1,31369528691546961⟩,
  ⟨17,22,5,1,43580954567871473⟩,
  ⟨2,19,6,1,53381683487573221⟩,
  ⟨2,4,6,2,65508508111169802⟩,
  ⟨5,7,6,2,74691876499336123⟩,
  ⟨8,10,6,2,102602702546886188⟩,
  ⟨11,12,6,2,121595898360230785⟩,
  ⟨13,14,6,2,140977562797163878⟩,
  ⟨15,16,6,2,160815998027633626⟩,
  ⟨17,18,6,2,181179506221588191⟩,
  ⟨19,19,6,2,191579507107981080⟩,
  ⟨3,14,7,1,53664079831295379⟩,
  ⟨3,5,7,2,118134619821897847⟩,
  ⟨6,8,7,2,132045962365354734⟩,
  ⟨9,10,7,2,160066083436281068⟩,
  ⟨11,11,7,2,174191937506237599⟩,
  ⟨12,12,7,2,188406370960847736⟩,
  ⟨13,13,7,2,202717921571354995⟩,
  ⟨14,14,7,2,217135127109002900⟩,
  ⟨3,6,8,1,44695674238600604⟩,
  ⟨3,3,8,2,167699524331809257⟩,
  ⟨4,6,8,2,187908208046024884⟩]

def retainedTariff (b j t : ℕ) : ℕ :=
  Research6969.Low6969RetainedTariffs.tariff ⟨b,j,t⟩

def band (k : Band) : BandData := bands.get ⟨k.val,k.isLt⟩

def start (k : Band) : Shape := ⟨(band k).lo,(band k).index,(band k).top⟩

def endWidth (k : Band) : ℕ := (band k).hi

def reserve (k : Band) : ℕ := (band k).charge

def Admits (k : Band) (r : Shape) : Prop :=
  (start k).b≤r.b ∧ r.b≤endWidth k ∧ r.j=(start k).j ∧ r.t=(start k).t

instance (k : Band) (r : Shape) : Decidable (Admits k r) := by unfold Admits; infer_instance

theorem start_flat (k : Band) : start k=zeroShape ∨ 0<(start k).j := by
  fin_cases k <;> decide +kernel

theorem empty_admits : Admits empty zeroShape := by decide +kernel

theorem admits_floor {k : Band} {r : Shape} (hr : Admits k r) : InBox (start k) r :=
  ⟨hr.1,hr.2.2.1.symm.le,hr.2.2.2.symm.le⟩

private theorem checked_cover (b : Fin 28) :
    ∀ (j : Fin 9) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      b.val≤lowDegreeCap j.val → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<28 := Nat.lt_succ_of_le box.1
  have hj : j<9 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 (degree_bound v box)

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 28,(start k).b≤b.val → b.val≤endWidth k →
      retainedTariff b.val (start k).j (start k).t≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    retainedTariff r.b r.j r.t≤reserve k := by
  have hm : endWidth k<28 := by fin_cases k <;> decide +kernel
  rw [hr.2.2.1,hr.2.2.2]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 274784969259454674

def factorCap (top : ℕ) : ℕ := budget-Low6969Prices.lowerCap top

def tiered (k : Band) : Bool := k.val == 1 || k.val == 38

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6969AllocWeight.weight b j t else if tiered k then Research6966.LowTierWeight.weight (58-(start k).j) j else j

def pricingDenom (k : Band) : ℕ := if k=empty then 374 else if tiered k then 5*(58-(start k).j) else 58-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤15) (k : Band) : reserve k≤factorCap top := by
  interval_cases top <;> fin_cases k <;> decide +kernel

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using Low6969AllocWeight.mono hb hj ht
  · by_cases t : tiered k
    · simpa [pricingWeight,h,t] using Research6966.LowTierWeight.mono (58-(start k).j) hj
    · simpa [pricingWeight,h,t] using hj

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤15) :
    allowance k a w j t≤allowance k b w j t := by
  have pos : factorCap a≤factorCap b := by
    have ha := h.trans hb
    interval_cases a <;> interval_cases b <;> decide +kernel
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right pos _))

def MassCell (k : Band) :=
  {q : Threshold // 0<q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1)<need}

theorem mass_cell (k : Band) (b j l N : ℕ) (hj : 0<j)
    (hN : (l-1)+1650/((start k).j+j)=N) (vals : List ℕ)
    (worked : check (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals=true)
    (small : vals.sum<need) :
    0<(⟨b,j,l⟩ : Threshold).j ∧
      availableMass (start k) ⟨b,j,0⟩ (l-1)<need := by
  refine ⟨hj,?_⟩
  rw [mass_eq _ _ _ (start_flat k) (by change 0<(start k).j+j; omega),hN]
  have sum := check_sum (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals worked
  have eq : P3_6_8_1.sumBelow (fastLayer (start k) ⟨b,j,0⟩ (l-1)) N=vals.sum := by
    simpa only [Nat.zero_add,P3_6_8_1.sumBelow] using sum
  rwa [eq]

def order {k : Band} (cells : List (MassCell k)) (x : Shape) : ℕ :=
  orderFor x.b x.j (cells.map Subtype.val)

def orderN {k : Band} (b j : ℕ) (cells : List (MassCell k)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun s _ ih => let a := cond (Nat.ble s.val.b b && Nat.ble s.val.j j) s.val.l 1
                   cond (Nat.ble a ih) ih a) cells

theorem orderN_eq {k : Band} (b j : ℕ) (cells : List (MassCell k)) :
    orderN b j cells = orderFor b j (cells.map Subtype.val) := by
  induction cells with
  | nil => rfl
  | cons s rest ih =>
    show cond (Nat.ble (cond (Nat.ble s.val.b b && Nat.ble s.val.j j) s.val.l 1) (orderN b j rest))
        (orderN b j rest) (cond (Nat.ble s.val.b b && Nat.ble s.val.j j) s.val.l 1) =
      max (if s.val.b ≤ b ∧ s.val.j ≤ j then s.val.l else 1) (orderFor b j (rest.map Subtype.val))
    rw [ih]
    by_cases h1 : s.val.b ≤ b <;> by_cases h2 : s.val.j ≤ j <;>
      simp [h1, h2, Nat.ble_eq, Nat.max_def]

def orderF {k : Band} (cells : List (MassCell k)) (x : Shape) : ℕ := orderN x.b x.j cells

theorem orderF_eq {k : Band} (cells : List (MassCell k)) (x : Shape) : orderF cells x = order cells x :=
  orderN_eq _ _ _

theorem order_pos {k : Band} (cells : List (MassCell k)) (x : Shape) : 0<order cells x :=
  (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).1

theorem order_mono {k : Band} (cells : List (MassCell k)) {x y : Shape}
    (hb : x.b≤y.b) (hj : x.j≤y.j) : order cells x≤order cells y :=
  P0_9_8.orderFor_mono hb hj _

theorem order_valid {k : Band} (cells : List (MassCell k)) (x : Shape) : order cells x=1 ∨
    availableMass (start k) x (order cells x-1)<need := by
  rcases (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).2 with h | ⟨q,hq,hb,hj,eq⟩
  · exact Or.inl h
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
    refine Or.inr ?_
    change order cells x=c.val.l at eq
    rw [eq]
    have pos : 0<(start k).j+c.val.j := by have := c.property.1; omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y:=⟨c.val.b,c.val.j,0⟩)
      (start_flat k) pos hb hj).trans_lt c.property.2

theorem layer_le_available {r y : Shape} {L : ℕ}
    (hr : r=zeroShape ∨ 0<r.j) (hj : 0<r.j+y.j) :
    (∑ k∈range layerCount,layerTerm r y L k)≤availableMass r y L := by
  exact Final50PriceLayer.layerSum_le_available_n _ hr hj


end Low6969Allocation

end
end Merged_R6960Low6969AllocCore
end Z6969Source2298

-- Source: ProximityPrize.SubmissionLower.Low6969Rectangle
section Z6969Source2299
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969Rectangle
section Merged_R6960Low6969Rectangle

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Low6969Rectangle
open K1_13 (Shape InBox ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open Low6969RetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Low6969Prices (physicalPrice physicalPriceOld)
open Low6969GeometryCut (chargedPrice)
open Low6969Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber scale_mono scale_chamber chart_mono chart_chamber)
open Low6969Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber
  scale_mono scale_chamber chart_mono chart_chamber)

/-- `physicalPriceOld` with the mixed surface numerator left free. -/
def charge (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := Low6969Prices.primaryBox
  let h := K1_13.chart Low6969Prices.taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((Low6969Prices.errors + 2 * Low6969Prices.incidenceGap) * x.b * q.b *
      (K1_13.chart (Low6969Prices.taylorLength + 1) p).b) Low6969Prices.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := K1_13.mixed32 p q auxBox h + 2 * x.t * K1_13.mixed32 p p p h
  let points := K1_13.mixed32 p q auxBox p + 2 * x.t * K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Low6969Prices.physicalDegree * x.b * q.b +
    ceilDiv (Low6969Prices.errors * curves + 2 * Low6969Prices.incidenceGap * points)
      (32 * Low6969Prices.incidenceGap)

theorem cut_eq (x : Shape) (l scale S : ℕ) : cutPrice x l scale S = charge x l scale S := by
  simp only [cutPrice, charge, chargedPrice, Low6969GeometryCut.auxCurves32,
    Low6969GeometryCut.auxPoints32, Low6969GeometryCut.membershipDegree, Nat.mul_assoc]
  rfl

theorem charge_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l scale : ℕ) {S S' : ℕ} (hS : S ≤ S') : charge x l scale S ≤ charge y l scale S' := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6969Prices.primaryBox
  let L := Low6969Prices.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Low6969Prices.errors + 2*Low6969Prices.incidenceGap) * y.b * q.b * (K1_13.chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6969Prices.errors hc)
    (Nat.mul_le_mul_left (2*Low6969Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6969Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Low6969Monotone.ceil_mono (Nat.add_le_add
      (Low6969Monotone.ceil_mono hS _) (Low6969Monotone.ceil_mono hmain _)) l) hraw)
    (Low6969Monotone.ceil_mono hgeom _)

open Low6969Allocation (Band start MassCell order allowance weight_mono order_mono)

abbrev hullOf (k : Band) (l : ℕ) : Shape := chamberHull (residualBox (start k) l)

def PaidFour {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ order cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t

instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFour cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))

theorem four {k : Band} {cells : List (MassCell k)} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : PaidFour cells t bl jl bh jh l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    ∃ l, 0 < l ∧ l ≤ order cells a ∧ contractedPrice a (start k) l 178 ≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨hl, hlo, hq, hbill⟩ := h
  have hu : l ≤ order cells a := hlo.trans (order_mono cells hb hj)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨hb', hj', ht.le⟩
  have hallow : allowance k ((start k).t+t) bl jl t ≤ allowance k ((start k).t+t) a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hb hj ht.ge))
  refine ⟨l, hl, hu, ?_⟩
  have hqc : Chamber (hullOf k l) := by
    have := hull_valid (residualBox (start k) l)
    exact ⟨this.1, this.2.1⟩
  have hp := normalize_mono hbox
  have hpc' : Chamber (Shape.chamber ⟨bh,jh,t⟩) := normalize_chamber _ hi
  have hsurf : fourSurface a.chamber (hullOf k l) ≤
      fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l) :=
    mixed_mono hp (box_refl _) (chart_mono _ hp) (chart_mono _ hp) hpc' hqc
      (chart_chamber _ _) hqc (chart_chamber _ _) (chart_chamber _ _)
  have hcut : cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) ≤
      cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) := by
    rw [cut_eq, cut_eq]
    exact charge_mono hbox ha hi l 32 hsurf
  have hc : contractedPrice a (start k) l 178 ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
    unfold contractedPrice
    dsimp only
    rw [if_pos hq]
    split
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  exact hc.trans (hcut.trans (hbill.trans (by simpa only [ht] using hallow)))

end Low6969Rectangle

end Merged_R6960Low6969Rectangle
end Z6969Source2299

-- Source: ProximityPrize.SubmissionLower.Low6969Encoding
section Z6969Source2300
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969TiltedRectangle
section Merged_Low6969TiltedRectangle

-- merged module R6960Low6969SurfaceLinearFive
section Merged_R6960Low6969SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low6969SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low6969Prices (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
open Low48BentLattice (Chamber)

open Final50SharedPrice (signedFive signed_five_linear signed_five_nonneg)

/-- The tilted signed surface is linear in the cutter shape. Chamber positivity
also certifies the exact natural-number coefficients in the price ledger. -/
theorem surface_tilted_eq_weights {f : Shape} (hf : Valid f) (ht : tiltedFits f) (q : Shape) :
    surface .tilted f q = (weights .tilted f).b*q.b + (weights .tilted f).j*q.j +
      (weights .tilted f).t*q.t := by
  let p := f.chamber
  let g := bentGraph p
  let l := bentLift (taylorLength-4) p
  let r := bentLift (taylorLength-3) p
  have hb : p.j ≤ p.b := le_max_right _ _
  have hp : Chamber (p,0) := ⟨hb,hf.2.1,Nat.zero_le _⟩
  have hg : Chamber g := Low48BentSupport.graph_chamber hf.1 ht.1
  have hl : Chamber l := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-4)
  have hr : Chamber r := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-3)
  have hnonneg (u : Shape) : 0 ≤ signedFive (p,0) (u,0) g l r :=
    signed_five_nonneg u _ _ _ _ hp hg hl hr
  refine surface_eq_weights_of_signed .tilted f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedFive (p,0) (u,0) g l r).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (hnonneg u)]
  exact signed_five_linear u _ _ _ _

end Low6969SharedPrice

end Merged_R6960Low6969SurfaceLinearFive

-- merged module R6960Low6969WidthAffine
section Merged_R6960Low6969WidthAffine

set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Low6969WidthAffine
open K1_13 (Shape)
open Low6969Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
  bentGraph bentLift taylorLength)
open Final50SharedPrice (signedFive signed_five_nonneg)

private abbrev Slot := BentCap × ℕ
private def atWidth (x : ℕ) (s : Slot) : BentCap :=
  (⟨s.1.1.b+x*s.2,s.1.1.j,s.1.1.t⟩,s.1.2)
private def add (a b : Slot) : Slot := (addBent a.1 b.1,a.2+b.2)
private def zero : Slot := ((⟨0,0,0⟩,0),0)

private theorem at_add (x : ℕ) (a b : Slot) :
    atWidth x (add a b) = addBent (atWidth x a) (atWidth x b) := by
  simp only [atWidth,add,addBent,Shape.plus,Prod.mk.injEq,Shape.mk.injEq,and_true]
  ring

private theorem fold_slots (x : ℕ) (s : List Slot) :
    (s.map (atWidth x)).foldl addBent (⟨0,0,0⟩,0) = atWidth x (s.foldl add zero) := by
  change (s.map (atWidth x)).foldl addBent (atWidth x zero) = _
  rw [List.foldl_map]
  exact List.foldl_hom (atWidth x) (fun a b => (at_add x a b).symm)

private def raw (s : List BentCap) : ℤ :=
  s.sublists.foldl (fun acc boxes =>
    let p := boxes.foldl addBent (⟨0,0,0⟩,0)
    acc + (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2) 0

private theorem integral_affine (B x W J T H : ℤ) :
    bentIntegral (B+x*W) J T H = bentIntegral B J T H + x *
      (bentIntegral (B+W) J T H-bentIntegral B J T H) := by
  simp only [bentIntegral]
  ring

private def integralTerm (boxes : List Slot) (x : ℕ) : ℤ :=
  let p := atWidth x (boxes.foldl add zero)
  (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2

private theorem term_affine (boxes : List Slot) (x : ℕ) :
    integralTerm boxes x = integralTerm boxes 0 + (x : ℤ) *
      (integralTerm boxes 1-integralTerm boxes 0) := by
  simp only [integralTerm, atWidth, Nat.cast_add, Nat.cast_mul, zero_mul, one_mul, add_zero, integral_affine]
  ring

private theorem raw_eq_sum (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = (s.sublists.map (fun a => integralTerm a x)).sum := by
  simp only [raw,List.sublists_map,List.sum_eq_foldl]
  rw [List.foldl_map,List.foldl_map]
  simp only [fold_slots,List.length_map,integralTerm]

private theorem raw_affine (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = raw (s.map (atWidth 0)) + (x : ℤ) *
      (raw (s.map (atWidth 1))-raw (s.map (atWidth 0))) := by
  simp only [raw_eq_sum]
  generalize s.sublists = rows
  induction rows with
  | nil => simp
  | cons boxes rows ih =>
    simp only [List.map_cons,List.sum_cons,term_affine boxes x,ih]
    ring

private def slots (j t : ℕ) (q : Shape) : List Slot :=
  let p : Shape := ⟨j+1,j,t⟩
  [((p,0),1), ((q,0),0), (bentGraph p,1),
    (bentLift (taylorLength-4) p,taylorLength-4),
    (bentLift (taylorLength-3) p,taylorLength-3)]

private theorem map_slots (j t x : ℕ) (q : Shape) :
    (slots j t q).map (atWidth x) =
      let p : Shape := ⟨j+1+x,j,t⟩
      [(p,0),(q,0),bentGraph p,bentLift (taylorLength-4) p,bentLift (taylorLength-3) p] := by
  simp [slots, atWidth, bentGraph, bentLift, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

private theorem raw_nonneg (j t x : ℕ) (q : Shape) (ht : 1≤t) (hj : 3*t+3≤j) :
    0 ≤ raw ((slots j t q).map (atWidth x)) := by
  rw [map_slots]
  let p : Shape := ⟨j+1+x,j,t⟩
  have hb : p.j ≤ p.b := by dsimp [p]; omega
  change 0 ≤ signedFive (p,0) (q,0) (bentGraph p) (bentLift (taylorLength-4) p)
    (bentLift (taylorLength-3) p)
  have hch : 3*p.t≤p.j := by dsimp [p]; omega
  exact signed_five_nonneg _ _ _ _ _ ⟨hb,hch,Nat.zero_le _⟩
    (Low48BentSupport.graph_chamber ht hj)
    (Low48BentSupport.lifted_chamber hb hj (by decide))
    (Low48BentSupport.lifted_chamber hb hj (by decide))

/-- Within one index and top degree, the tilted surface increases with width. -/
theorem tilted_width_mono (q : Shape) {b B j t : ℕ} (hb : j+1≤b) (hB : b≤B)
    (ht : 1≤t) (hj : 3*t+3≤j) :
    tiltedSurface (⟨b,j,t⟩ : Shape).chamber q ≤ tiltedSurface (⟨B,j,t⟩ : Shape).chamber q := by
  let s := slots j t q
  let f (x : ℕ) := raw (s.map (atWidth x))
  have ha (x : ℕ) : f x = f 0 + (x : ℤ) * (f 1-f 0) := raw_affine s x
  have hp (x : ℕ) : 0≤f x := raw_nonneg j t x q ht hj
  have hs : 0≤f 1-f 0 := by
    by_contra! h
    have hle : f 1-f 0 ≤ -1 := by omega
    let wid := (f 0).toNat+1
    have hwid : (wid : ℤ)=f 0+1 := by simp [wid,Int.toNat_of_nonneg (hp 0)]
    have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg wid)
    have hx := hp wid
    rw [ha wid,hwid] at hx
    rw [hwid] at hmul
    simp only [mul_neg,mul_one] at hmul
    omega
  have hr (a : ℕ) (h : j+1≤a) :
      tiltedSurface (⟨a,j,t⟩ : Shape).chamber q = (f (a-(j+1))).toNat := by
    have hmax : max a j = a := max_eq_left (by omega)
    have eq : j+1+(a-(j+1))=a := Nat.add_sub_of_le h
    simp only [f,s,map_slots,eq,tiltedSurface,Shape.chamber,hmax,ambientMix,raw]
  rw [hr _ hb,hr _ (hb.trans hB)]
  apply Int.toNat_le_toNat
  rw [ha (b-(j+1)),ha (B-(j+1))]
  have hw : ((b-(j+1) : ℕ) : ℤ) ≤ ((B-(j+1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hB (j+1)
  exact add_le_add (le_refl (f 0)) (mul_le_mul_of_nonneg_right hw hs)

end Low6969WidthAffine

end Merged_R6960Low6969WidthAffine

-- merged module R6960Low6969TiltedRectangle
section Merged_R6960Low6969TiltedRectangle

set_option Elab.async false
set_option maxRecDepth 2400
namespace Low6969Rectangle
open K1_13 (Shape InBox)
open Low6969RetainedCut (cutPrice contractedPrice)
open Low6969Prices (tiltedSurface tiltedFits)
open Low6969Allocation (Band MassCell start order allowance weight_mono order_mono)

/-- A tilted-surface price certificate for a width interval of one index and degree. -/
def PaidTilted {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t

instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTilted cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))

theorem tilted {k : Band} {cells : List (MassCell k)} {a : Shape} {b j B t l : ℕ}
    (h : PaidTilted cells t b j B l) (hb : b≤a.b) (hB : a.b≤B)
    (hj : a.j=j) (ht : a.t=t) :
    ∃ l, 0<l ∧ l≤order cells a ∧ contractedPrice a (start k) l 178≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨lp,lo,ht',hj',hw,fee⟩ := h
  cases a with
  | mk a d z =>
    change d=j at hj
    change z=t at ht
    subst d z
    have geom : tiltedFits ⟨a,j,t⟩ := ⟨hj',hw.trans hb⟩
    have hprice : contractedPrice ⟨a,j,t⟩ (start k) l 178 ≤
        cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) := by
      unfold contractedPrice
      dsimp only
      rw [ite_eq_left geom]
      exact min_le_right _ _
    have ha : 3*t≤j := by omega
    have mono := Low6969WidthAffine.tilted_width_mono (hullOf k l) (hw.trans hb) hB ht' hj'
    have hcut : cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) ≤
        cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) := by
      have box : InBox ⟨a,j,t⟩ ⟨B,j,t⟩ := ⟨hB,le_rfl,le_rfl⟩
      rw [cut_eq,cut_eq]
      exact charge_mono box ha ha l 1920 mono
    exact ⟨l,lp,lo.trans (order_mono cells hb le_rfl), hprice.trans
      (hcut.trans (fee.trans (Nat.div_le_div_right
        (Nat.mul_le_mul_left _ (weight_mono k hb le_rfl le_rfl)))))⟩

end Low6969Rectangle

end Merged_R6960Low6969TiltedRectangle

end Merged_Low6969TiltedRectangle

-- merged module Low6969FastPrice
section Merged_Low6969FastPrice

-- merged module R6960Low6969WeightedRate
section Merged_R6960Low6969WeightedRate

set_option Elab.async false

namespace Low6969WeightedRate
open K1_13 (Shape)
open Low6969SharedPrice (Rate weights)

abbrev unit : ℕ := 1000000000
abbrev split : ℕ := 10

def boxFee (w x : Shape) : ℕ := w.b * max x.b x.j + w.j * x.j + w.t * min x.t (x.j / 3)
def sepBox (x : Shape) : Shape := ⟨x.b - 1, x.j - 3, x.t - 1⟩
def charge (r a d e : ℕ) : ℕ := e * (24 * (r - e*a) + d * (e - 1))

structure Envelope where
  widthLow : ℕ
  indexLow : ℕ
  topLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
  taperLow : ℕ
  taperHigh : ℕ
  coeff : Shape
  sep : ℕ

def Fits (p : Envelope) (x : Shape) : Prop :=
  p.widthLow ≤ x.b ∧ x.b ≤ p.widthHigh ∧ p.indexLow ≤ x.j ∧ x.j ≤ p.indexHigh ∧
    p.topLow ≤ x.t ∧ p.taperLow ≤ 26*x.b ∧ min (26*x.b+25*x.j) (x.b+25*178) ≤ p.taperHigh

def RayBounds (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weights .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

def Pays (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = split ∧ 0 < u.amount ∧ Low6969Prices.tiltedFits x ∧
    RayBounds p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (Pays p x u) := by
  unfold Pays Fits RayBounds
  infer_instance

def first : Envelope := ⟨106,48,4,132,53,2756,4257,⟨4886433,26118015,6676780⟩,1966580209⟩

def Allowed (x : Shape) (u : Rate) : Prop :=
  Low6969SharedPrice.RateFits x u

instance (x : Shape) (u : Rate) : Decidable (Allowed x u) := by unfold Allowed; infer_instance

private theorem ray_expansion (w : Shape) (b j t : ℕ) (hb : j ≤ b) (ht : 3*t ≤ j) :
    w.b*b+w.j*j+w.t*t = w.b*(b-j)+(w.b+w.j)*(j-3*t)+(3*(w.b+w.j)+w.t)*t := by
  let B := b-j
  let J := j-3*t
  change w.b*b+w.j*j+w.t*t = w.b*B+(w.b+w.j)*J+(3*(w.b+w.j)+w.t)*t
  have hB : b = B+J+3*t := by dsimp [B,J]; omega
  have hJ : j = J+3*t := by dsimp [J]; omega
  rw [hB, hJ]
  ring

theorem fee_le {p : Envelope} {x : Shape} {amount : ℕ} (h : RayBounds p x amount) (y : Shape) :
    unit * boxFee (weights .tilted x) y ≤ (1920 * amount) * boxFee p.coeff y := by
  let b := max y.b y.j
  let j := y.j
  let t := min y.t (y.j/3)
  let w := weights .tilted x
  have hb : j ≤ b := le_max_right _ _
  have ht : 3*t ≤ j := by
    have hd : t ≤ y.j/3 := min_le_right _ _
    dsimp only [j]
    omega
  change unit*(w.b*b+w.j*j+w.t*t) ≤ (1920*amount)*(p.coeff.b*b+p.coeff.j*j+p.coeff.t*t)
  rw [ray_expansion w b j t hb ht, ray_expansion p.coeff b j t hb ht]
  calc
    _ = (unit*w.b)*(b-j) + (unit*(w.b+w.j))*(j-3*t) + (unit*(3*(w.b+w.j)+w.t))*t := by ring
    _ ≤ _ := by
      rw [show (1920*amount)*(p.coeff.b*(b-j)+(p.coeff.b+p.coeff.j)*(j-3*t)+
          (3*(p.coeff.b+p.coeff.j)+p.coeff.t)*t) =
          ((1920*amount)*p.coeff.b)*(b-j) + ((1920*amount)*(p.coeff.b+p.coeff.j))*(j-3*t) +
          ((1920*amount)*(3*(p.coeff.b+p.coeff.j)+p.coeff.t))*t by ring]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (Nat.mul_le_mul_right _ h.2.1))
        (Nat.mul_le_mul_right _ h.2.2.1)

theorem transfer {p : Envelope} {x : Shape} {u : Rate} (h : Pays p x u) (y : Shape) (r a d e : ℕ)
    (hp : (split+1-e)*(24*boxFee p.coeff y+d*p.sep) ≤ split*unit*charge r a d e) :
    (u.split+1-e)*(24*boxFee (weights u.kind x) y+d*boxFee (weights u.kind x) (sepBox x)) ≤
      (Low6969SharedPrice.surfaceScale u.kind*(u.split*u.amount))*charge r a d e := by
  obtain ⟨_, hk, hs, _, _, hw⟩ := h
  rw [hk, hs]
  let w := weights .tilted x
  let z := 24*boxFee w y+d*boxFee w (sepBox x)
  let cap := 1920*u.amount
  let bound := 24*boxFee p.coeff y+d*p.sep
  have hz : unit*z ≤ cap*bound := by
    calc
      _ = 24*(unit*boxFee w y)+d*(unit*boxFee w (sepBox x)) := by dsimp [z]; ring
      _ ≤ 24*(cap*boxFee p.coeff y)+d*(cap*p.sep) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (fee_le hw y)) (Nat.mul_le_mul_left _ hw.2.2.2)
      _ = _ := by dsimp [bound]; ring
  change (split+1-e)*z ≤ (1920*(split*u.amount))*charge r a d e
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < unit)
  calc
    unit*((split+1-e)*z) = (split+1-e)*(unit*z) := by ring
    _ ≤ (split+1-e)*(cap*bound) := Nat.mul_le_mul_left _ hz
    _ = cap*((split+1-e)*bound) := by ring
    _ ≤ cap*(split*unit*charge r a d e) := Nat.mul_le_mul_left _ hp
    _ = _ := by dsimp [cap]; ring

end Low6969WeightedRate

end Merged_R6960Low6969WeightedRate

-- merged module R6960Low6969FastPrice
section Merged_R6960Low6969FastPrice
set_option autoImplicit false
set_option Elab.async false
namespace Low6969FastPrice
open K1_13 (Shape mixed32 volume32 difference chart liftedChart ceilDiv)
open Low6969Prices (BentCap bentIntegral addBent ambientMix tiltedSurface bentGraph bentLift
  taylorLength primaryBox errors incidenceGap physicalDegree tiltedFits activeFitsPrice activeLoss
  activeClips surfaceNumerator32 physicalPriceOld physicalPriceWith physicalPriceTilted
  physicalPriceActive physicalPrice tiltedSurfaceActive)
def mixPos (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  16 * pb * qj * rj * st +
    16 * pb * qj * rt * sj +
    16 * pb * qt * rj * sj +
    144 * pb * qt * rt * st +
    16 * pj * qb * rj * st +
    16 * pj * qb * rt * sj +
    16 * pj * qj * rb * st +
    16 * pj * qj * rt * sb +
    56 * pj * qj * rt * st +
    16 * pj * qt * rb * sj +
    16 * pj * qt * rj * sb +
    56 * pj * qt * rj * st +
    56 * pj * qt * rt * sj +
    16 * pt * qb * rj * sj +
    144 * pt * qb * rt * st +
    16 * pt * qj * rb * sj +
    16 * pt * qj * rj * sb +
    56 * pt * qj * rj * st +
    56 * pt * qj * rt * sj +
    144 * pt * qt * rb * st +
    56 * pt * qt * rj * sj +
    144 * pt * qt * rt * sb +
    216 * pt * qt * rt * st
def mixNeg (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  48 * pb * qj * rt * st +
    48 * pb * qt * rj * st +
    48 * pb * qt * rt * sj +
    48 * pj * qb * rt * st +
    24 * pj * qj * rj * st +
    24 * pj * qj * rt * sj +
    48 * pj * qt * rb * st +
    24 * pj * qt * rj * sj +
    48 * pj * qt * rt * sb +
    120 * pj * qt * rt * st +
    48 * pt * qb * rj * st +
    48 * pt * qb * rt * sj +
    48 * pt * qj * rb * st +
    24 * pt * qj * rj * sj +
    48 * pt * qj * rt * sb +
    120 * pt * qj * rt * st +
    48 * pt * qt * rb * sj +
    48 * pt * qt * rj * sb +
    120 * pt * qt * rj * st +
    120 * pt * qt * rt * sj
def mix4 (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  mixPos pb pj pt qb qj qt rb rj rt sb sj st - mixNeg pb pj pt qb qj qt rb rj rt sb sj st
def mixF (p q r s : Shape) : ℕ :=
  mix4 p.b p.j p.t q.b q.j q.t r.b r.j r.t s.b s.j s.t
theorem mixF_eq (p q r s : Shape) : mixF p q r s = mixed32 p q r s := by
  obtain ⟨pb,pj,pt⟩ := p
  obtain ⟨qb,qj,qt⟩ := q
  obtain ⟨rb,rj,rt⟩ := r
  obtain ⟨sb,sj,st⟩ := s
  have key : difference (difference (difference (difference volume32 ⟨pb,pj,pt⟩) ⟨qb,qj,qt⟩)
      ⟨rb,rj,rt⟩) ⟨sb,sj,st⟩ ⟨0,0,0⟩ = (mixPos pb pj pt qb qj qt rb rj rt sb sj st : ℤ) -
        (mixNeg pb pj pt qb qj qt rb rj rt sb sj st : ℤ) := by
    simp only [difference, volume32, K1_13.Shape.plus, mixPos, mixNeg]
    push_cast
    ring
  unfold mixF mix4 mixed32
  dsimp only
  rw [key]
  omega
def bentPos (B J T H : ℕ) : ℕ :=
  H * (160*T^2*H^2 + 540*T^4 + 960*J*H^3 + 960*J*T^2*H + 840*J^2*T^2 + 240*J^3*H +
    640*B*T*H^2 + 1440*B*T^3 + 640*B*J*H^2 + 960*B*J*T*H + 480*B*J^2*T)
def bentNeg (B J T H : ℕ) : ℕ :=
  H * (576*H^4 + 480*T^3*H + 320*J*T*H^2 + 1200*J*T^3 + 480*J^2*H^2 + 480*J^2*T*H +
    240*J^3*T + 960*B*H^3 + 1440*B*T^2*H + 1440*B*J*T^2 + 480*B*J^2*H)
theorem bent_eq (B J T H : ℕ) :
    bentIntegral B J T H = (bentPos B J T H : ℤ) - (bentNeg B J T H : ℤ) := by
  simp only [bentIntegral, bentPos, bentNeg]
  push_cast
  ring
def mixStep (acc : ℕ × ℕ) (boxes : List BentCap) : ℕ × ℕ :=
  let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
  let a := bentPos s.1.b s.1.j s.1.t s.2
  let n := bentNeg s.1.b s.1.j s.1.t s.2
  if (5 - boxes.length) % 2 = 0 then (acc.1 + a, acc.2 + n) else (acc.1 + n, acc.2 + a)
def ambientMixF (caps : List BentCap) : ℕ :=
  let r := caps.sublists.foldl mixStep (0,0)
  r.1 - r.2
private theorem fold_eq (Ls : List (List BentCap)) (a : ℤ) (acc : ℕ × ℕ)
    (h : a = acc.1 - acc.2) :
    Ls.foldl (fun acc boxes =>
      let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
      acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) a =
      ((Ls.foldl mixStep acc).1 : ℤ) - (Ls.foldl mixStep acc).2 := by
  induction Ls generalizing a acc with
  | nil => simpa using h
  | cons boxes rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [bent_eq, h, neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (5 - boxes.length) with e | e
    · simp only [mixStep, e, ↓reduceIte, pow_zero, one_mul]
      push_cast; ring
    · simp only [mixStep, e, Nat.one_ne_zero, ↓reduceIte, pow_one]
      push_cast; ring
theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = ambientMixF caps := by
  have key := fold_eq caps.sublists 0 (0,0) (by simp)
  unfold ambientMix ambientMixF
  dsimp only at key ⊢
  rw [key]
  omega
def tiltFRef (p q : Shape) : ℕ :=
  ambientMixF [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]
theorem tiltFRef_eq (p q : Shape) : tiltFRef p q = tiltedSurface p q := by
  unfold tiltFRef tiltedSurface
  rw [ambientMix_eq]
/-! Kernel-friendly unrolled evaluator for the five-cap inclusion-exclusion. -/
def bentPosN (B J T H : ℕ) : ℕ := Nat.mul H (Nat.add (Nat.mul T (Nat.add (Nat.mul T (Nat.add (Nat.mul H (Nat.add (Nat.mul H (160)) (Nat.mul J (960)))) (Nat.add (Nat.mul T (Nat.add (Nat.mul T (540)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (840)))))) (Nat.mul B (Nat.add (Nat.mul H (Nat.add (Nat.mul H (640)) (Nat.mul J (960)))) (Nat.mul J (Nat.mul J (480))))))) (Nat.mul H (Nat.mul J (Nat.add (Nat.mul H (Nat.add (Nat.mul H (960)) (Nat.mul B (640)))) (Nat.mul J (Nat.mul J (240)))))))
def bentNegN (B J T H : ℕ) : ℕ := Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (Nat.add (Nat.mul H (576)) (Nat.mul B (960)))) (Nat.mul J (Nat.add (Nat.mul T (320)) (Nat.mul J (480)))))) (Nat.add (Nat.mul T (Nat.add (Nat.mul T (Nat.add (Nat.mul T (480)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (480))))) (Nat.mul J (Nat.mul J (Nat.mul B (480))))))) (Nat.mul T (Nat.mul J (Nat.add (Nat.mul T (Nat.add (Nat.mul T (1200)) (Nat.mul B (1440)))) (Nat.mul J (Nat.mul J (240)))))))
def ambN (fa fn : ℕ → ℕ → ℕ → ℕ → ℕ) (b0 j0 t0 h0 b1 j1 t1 h1 b2 j2 t2 h2 b3 j3 t3 h3 b4 j4 t4 h4 : ℕ) : ℕ :=
  Nat.sub (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (fn 0 0 0 0)) (fa (Nat.add 0 b0) (Nat.add 0 j0) (Nat.add 0 t0) (Nat.add 0 h0))) (fa (Nat.add 0 b1) (Nat.add 0 j1) (Nat.add 0 t1) (Nat.add 0 h1))) (fn (Nat.add (Nat.add 0 b0) b1) (Nat.add (Nat.add 0 j0) j1) (Nat.add (Nat.add 0 t0) t1) (Nat.add (Nat.add 0 h0) h1))) (fa (Nat.add 0 b2) (Nat.add 0 j2) (Nat.add 0 t2) (Nat.add 0 h2))) (fn (Nat.add (Nat.add 0 b0) b2) (Nat.add (Nat.add 0 j0) j2) (Nat.add (Nat.add 0 t0) t2) (Nat.add (Nat.add 0 h0) h2))) (fn (Nat.add (Nat.add 0 b1) b2) (Nat.add (Nat.add 0 j1) j2) (Nat.add (Nat.add 0 t1) t2) (Nat.add (Nat.add 0 h1) h2))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) (Nat.add (Nat.add (Nat.add 0 h0) h1) h2))) (fa (Nat.add 0 b3) (Nat.add 0 j3) (Nat.add 0 t3) (Nat.add 0 h3))) (fn (Nat.add (Nat.add 0 b0) b3) (Nat.add (Nat.add 0 j0) j3) (Nat.add (Nat.add 0 t0) t3) (Nat.add (Nat.add 0 h0) h3))) (fn (Nat.add (Nat.add 0 b1) b3) (Nat.add (Nat.add 0 j1) j3) (Nat.add (Nat.add 0 t1) t3) (Nat.add (Nat.add 0 h1) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) (Nat.add (Nat.add (Nat.add 0 h0) h1) h3))) (fn (Nat.add (Nat.add 0 b2) b3) (Nat.add (Nat.add 0 j2) j3) (Nat.add (Nat.add 0 t2) t3) (Nat.add (Nat.add 0 h2) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) (Nat.add (Nat.add (Nat.add 0 h0) h2) h3))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) (Nat.add (Nat.add (Nat.add 0 h1) h2) h3))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3))) (fa (Nat.add 0 b4) (Nat.add 0 j4) (Nat.add 0 t4) (Nat.add 0 h4))) (fn (Nat.add (Nat.add 0 b0) b4) (Nat.add (Nat.add 0 j0) j4) (Nat.add (Nat.add 0 t0) t4) (Nat.add (Nat.add 0 h0) h4))) (fn (Nat.add (Nat.add 0 b1) b4) (Nat.add (Nat.add 0 j1) j4) (Nat.add (Nat.add 0 t1) t4) (Nat.add (Nat.add 0 h1) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b1) b4) (Nat.add (Nat.add (Nat.add 0 j0) j1) j4) (Nat.add (Nat.add (Nat.add 0 t0) t1) t4) (Nat.add (Nat.add (Nat.add 0 h0) h1) h4))) (fn (Nat.add (Nat.add 0 b2) b4) (Nat.add (Nat.add 0 j2) j4) (Nat.add (Nat.add 0 t2) t4) (Nat.add (Nat.add 0 h2) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b2) b4) (Nat.add (Nat.add (Nat.add 0 j0) j2) j4) (Nat.add (Nat.add (Nat.add 0 t0) t2) t4) (Nat.add (Nat.add (Nat.add 0 h0) h2) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b2) b4) (Nat.add (Nat.add (Nat.add 0 j1) j2) j4) (Nat.add (Nat.add (Nat.add 0 t1) t2) t4) (Nat.add (Nat.add (Nat.add 0 h1) h2) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h4))) (fn (Nat.add (Nat.add 0 b3) b4) (Nat.add (Nat.add 0 j3) j4) (Nat.add (Nat.add 0 t3) t4) (Nat.add (Nat.add 0 h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b0) b3) b4) (Nat.add (Nat.add (Nat.add 0 j0) j3) j4) (Nat.add (Nat.add (Nat.add 0 t0) t3) t4) (Nat.add (Nat.add (Nat.add 0 h0) h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b1) b3) b4) (Nat.add (Nat.add (Nat.add 0 j1) j3) j4) (Nat.add (Nat.add (Nat.add 0 t1) t3) t4) (Nat.add (Nat.add (Nat.add 0 h1) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h3) h4))) (fa (Nat.add (Nat.add (Nat.add 0 b2) b3) b4) (Nat.add (Nat.add (Nat.add 0 j2) j3) j4) (Nat.add (Nat.add (Nat.add 0 t2) t3) t4) (Nat.add (Nat.add (Nat.add 0 h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h1) h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3) h4)))
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (fa 0 0 0 0)) (fn (Nat.add 0 b0) (Nat.add 0 j0) (Nat.add 0 t0) (Nat.add 0 h0))) (fn (Nat.add 0 b1) (Nat.add 0 j1) (Nat.add 0 t1) (Nat.add 0 h1))) (fa (Nat.add (Nat.add 0 b0) b1) (Nat.add (Nat.add 0 j0) j1) (Nat.add (Nat.add 0 t0) t1) (Nat.add (Nat.add 0 h0) h1))) (fn (Nat.add 0 b2) (Nat.add 0 j2) (Nat.add 0 t2) (Nat.add 0 h2))) (fa (Nat.add (Nat.add 0 b0) b2) (Nat.add (Nat.add 0 j0) j2) (Nat.add (Nat.add 0 t0) t2) (Nat.add (Nat.add 0 h0) h2))) (fa (Nat.add (Nat.add 0 b1) b2) (Nat.add (Nat.add 0 j1) j2) (Nat.add (Nat.add 0 t1) t2) (Nat.add (Nat.add 0 h1) h2))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) (Nat.add (Nat.add (Nat.add 0 h0) h1) h2))) (fn (Nat.add 0 b3) (Nat.add 0 j3) (Nat.add 0 t3) (Nat.add 0 h3))) (fa (Nat.add (Nat.add 0 b0) b3) (Nat.add (Nat.add 0 j0) j3) (Nat.add (Nat.add 0 t0) t3) (Nat.add (Nat.add 0 h0) h3))) (fa (Nat.add (Nat.add 0 b1) b3) (Nat.add (Nat.add 0 j1) j3) (Nat.add (Nat.add 0 t1) t3) (Nat.add (Nat.add 0 h1) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) (Nat.add (Nat.add (Nat.add 0 h0) h1) h3))) (fa (Nat.add (Nat.add 0 b2) b3) (Nat.add (Nat.add 0 j2) j3) (Nat.add (Nat.add 0 t2) t3) (Nat.add (Nat.add 0 h2) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) (Nat.add (Nat.add (Nat.add 0 h0) h2) h3))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) (Nat.add (Nat.add (Nat.add 0 h1) h2) h3))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3))) (fn (Nat.add 0 b4) (Nat.add 0 j4) (Nat.add 0 t4) (Nat.add 0 h4))) (fa (Nat.add (Nat.add 0 b0) b4) (Nat.add (Nat.add 0 j0) j4) (Nat.add (Nat.add 0 t0) t4) (Nat.add (Nat.add 0 h0) h4))) (fa (Nat.add (Nat.add 0 b1) b4) (Nat.add (Nat.add 0 j1) j4) (Nat.add (Nat.add 0 t1) t4) (Nat.add (Nat.add 0 h1) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b1) b4) (Nat.add (Nat.add (Nat.add 0 j0) j1) j4) (Nat.add (Nat.add (Nat.add 0 t0) t1) t4) (Nat.add (Nat.add (Nat.add 0 h0) h1) h4))) (fa (Nat.add (Nat.add 0 b2) b4) (Nat.add (Nat.add 0 j2) j4) (Nat.add (Nat.add 0 t2) t4) (Nat.add (Nat.add 0 h2) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b2) b4) (Nat.add (Nat.add (Nat.add 0 j0) j2) j4) (Nat.add (Nat.add (Nat.add 0 t0) t2) t4) (Nat.add (Nat.add (Nat.add 0 h0) h2) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b2) b4) (Nat.add (Nat.add (Nat.add 0 j1) j2) j4) (Nat.add (Nat.add (Nat.add 0 t1) t2) t4) (Nat.add (Nat.add (Nat.add 0 h1) h2) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h4))) (fa (Nat.add (Nat.add 0 b3) b4) (Nat.add (Nat.add 0 j3) j4) (Nat.add (Nat.add 0 t3) t4) (Nat.add (Nat.add 0 h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b0) b3) b4) (Nat.add (Nat.add (Nat.add 0 j0) j3) j4) (Nat.add (Nat.add (Nat.add 0 t0) t3) t4) (Nat.add (Nat.add (Nat.add 0 h0) h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b1) b3) b4) (Nat.add (Nat.add (Nat.add 0 j1) j3) j4) (Nat.add (Nat.add (Nat.add 0 t1) t3) t4) (Nat.add (Nat.add (Nat.add 0 h1) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h3) h4))) (fn (Nat.add (Nat.add (Nat.add 0 b2) b3) b4) (Nat.add (Nat.add (Nat.add 0 j2) j3) j4) (Nat.add (Nat.add (Nat.add 0 t2) t3) t4) (Nat.add (Nat.add (Nat.add 0 h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h2) h3) h4))) (fa (Nat.add (Nat.add (Nat.add (Nat.add 0 b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add 0 j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add 0 t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add 0 h1) h2) h3) h4))) (fn (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 b0) b1) b2) b3) b4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 j0) j1) j2) j3) j4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 t0) t1) t2) t3) t4) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 h0) h1) h2) h3) h4)))
theorem bentPosN_eq (B J T H : ℕ) : bentPosN B J T H = bentPos B J T H := by
  unfold bentPosN bentPos
  simp only [Nat.add_eq, Nat.mul_eq]
  ring
theorem bentNegN_eq (B J T H : ℕ) : bentNegN B J T H = bentNeg B J T H := by
  unfold bentNegN bentNeg
  simp only [Nat.add_eq, Nat.mul_eq]
  ring
set_option maxRecDepth 100000 in
theorem ambN_ref (c0 c1 c2 c3 c4 : BentCap) :
    ambientMixF [c0,c1,c2,c3,c4] = ambN bentPos bentNeg c0.1.b c0.1.j c0.1.t c0.2 c1.1.b c1.1.j c1.1.t c1.2
      c2.1.b c2.1.j c2.1.t c2.2 c3.1.b c3.1.j c3.1.t c3.2 c4.1.b c4.1.j c4.1.t c4.2 := by
  with_unfolding_all exact rfl
def tiltF (p q : Shape) : ℕ :=
  ambN bentPosN bentNegN p.b p.j p.t 0 q.b q.j q.t 0
    (bentGraph p).1.b (bentGraph p).1.j (bentGraph p).1.t (bentGraph p).2
    (bentLift (taylorLength - 4) p).1.b (bentLift (taylorLength - 4) p).1.j (bentLift (taylorLength - 4) p).1.t (bentLift (taylorLength - 4) p).2
    (bentLift (taylorLength - 3) p).1.b (bentLift (taylorLength - 3) p).1.j (bentLift (taylorLength - 3) p).1.t (bentLift (taylorLength - 3) p).2
theorem tiltF_eq (p q : Shape) : tiltF p q = tiltedSurface p q := by
  rw [← tiltFRef_eq]
  unfold tiltF tiltFRef
  rw [ambN_ref]
  have h1 : bentPosN = bentPos := funext fun a => funext fun b => funext fun c => funext fun d => bentPosN_eq a b c d
  have h2 : bentNegN = bentNeg := funext fun a => funext fun b => funext fun c => funext fun d => bentNegN_eq a b c d
  rw [h1, h2]
def surfaceNumerator32F (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixF p q (chart (L + 1) p) (chart (L + 2) p))
    (mixF p q a b + (L + 1) * mixF p q g b + (L + 2) * mixF p q g a)
def physicalPriceOldF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32F p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceWithF (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceF (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOldF x l) (physicalPriceWithF x l (tiltF x.chamber primaryBox))
    if activeFitsPrice x K then
      min base (physicalPriceWithF x l (tiltF x.chamber primaryBox - activeLoss (activeClips x.chamber K)))
    else base
  else physicalPriceOldF x l
theorem physicalPriceOldF_eq (x : Shape) (l : ℕ) : physicalPriceOldF x l = physicalPriceOld x l := by
  simp only [physicalPriceOldF, physicalPriceOld, surfaceNumerator32F, surfaceNumerator32, mixF_eq]
theorem physicalPriceWithF_eq (x : Shape) (l s : ℕ) : physicalPriceWithF x l s = physicalPriceWith x l s := by
  simp only [physicalPriceWithF, physicalPriceWith, mixF_eq]
theorem physicalPriceF_eq (x : Shape) (l K : ℕ) : physicalPriceF x l K = physicalPrice x l K := by
  simp only [physicalPriceF, physicalPrice, physicalPriceTilted, physicalPriceActive,
    tiltedSurfaceActive, physicalPriceOldF_eq, physicalPriceWithF_eq, tiltF_eq]
def chargeF (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b *
      (chart (taylorLength + 1) p).b) incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
theorem chargeF_eq (x : Shape) (l scale S : ℕ) :
    chargeF x l scale S = Low6969RetainedCut.cutPrice x l scale S := by
  rw [Low6969Rectangle.cut_eq]
  simp only [chargeF, Low6969Rectangle.charge, mixF_eq]
def fourSurfaceF (p q : Shape) : ℕ :=
  mixF p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)
theorem fourSurfaceF_eq (p q : Shape) : fourSurfaceF p q = Low6969RetainedCut.fourSurface p q := by
  simp only [fourSurfaceF, Low6969RetainedCut.fourSurface, mixF_eq]
def contractedPriceF (x h : Shape) (l active : ℕ) : ℕ :=
  let q := Low6969RetainedCut.chamberHull (Low6969RetainedCut.residualBox h l)
  let old := physicalPriceF x l active
  let four := if 0 < q.t then min old (chargeF x l 32 (fourSurfaceF x.chamber q)) else old
  if tiltedFits x then min four (chargeF x l (60*32) (tiltF x.chamber q)) else four
theorem contractedPriceF_eq (x h : Shape) (l active : ℕ) :
    contractedPriceF x h l active = Low6969RetainedCut.contractedPrice x h l active := by
  simp only [contractedPriceF, Low6969RetainedCut.contractedPrice, physicalPriceF_eq, chargeF_eq,
    fourSurfaceF_eq, tiltF_eq]
open Low6969SharedPrice (Surface Rate surfaceScale coord expression deficit slope)
def surfaceF (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixF p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltF f.chamber q
theorem surfaceF_eq (kind : Surface) (f q : Shape) :
    surfaceF kind f q = Low6969SharedPrice.surface kind f q := by
  cases kind <;> simp only [surfaceF, Low6969SharedPrice.surface, mixF_eq, tiltF_eq]
def weightsF (kind : Surface) (f : Shape) : Shape :=
  let b := surfaceF kind f ⟨1,0,0⟩
  let j := surfaceF kind f ⟨1,1,0⟩ - b
  let t := surfaceF kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
theorem weightsF_eq (kind : Surface) (f : Shape) :
    weightsF kind f = Low6969SharedPrice.weights kind f := by
  simp only [weightsF, Low6969SharedPrice.weights, surfaceF_eq]
def RateFitsF (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weightsF u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFitsF f u) := by
  unfold RateFitsF
  infer_instance
theorem rateFitsF_iff (f : Shape) (u : Rate) : RateFitsF f u ↔ Low6969SharedPrice.RateFits f u := by
  simp only [RateFitsF, Low6969SharedPrice.RateFits, weightsF_eq]
def additiveBaseF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixF p q z h + 2*x.t*mixF p p p h
  let pt := mixF p q z p + 2*x.t*mixF p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def priceF (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPriceF x l K + u.split*additiveBaseF x l + u.split*u.amount + 1)
    (u.split+1) + Low6969SharedPrice.nonsharedFee x l
theorem priceF_eq (x : Shape) (l K : ℕ) (u : Rate) :
    priceF x l K u = Low6969SharedPrice.price x l K u := by
  simp only [priceF, Low6969SharedPrice.price, Low6969SharedPrice.additiveBase, additiveBaseF,
    physicalPriceF_eq, mixF_eq]
open Low6969WeightedRate (Envelope Fits unit boxFee sepBox first)
def RayBoundsF (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsF .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep
def PaysF (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = Low6969WeightedRate.split ∧ 0 < u.amount ∧
    tiltedFits x ∧ RayBoundsF p x u.amount
instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (PaysF p x u) := by
  unfold PaysF Fits RayBoundsF
  infer_instance
def AllowedF (x : Shape) (u : Rate) : Prop :=
  RateFitsF x u
instance (x : Shape) (u : Rate) : Decidable (AllowedF x u) := by unfold AllowedF; infer_instance
theorem allowedF_iff (x : Shape) (u : Rate) : AllowedF x u ↔ Low6969WeightedRate.Allowed x u := by
  simp only [AllowedF, Low6969WeightedRate.Allowed, rateFitsF_iff]
open Low6969Allocation (Band MassCell start order orderF orderF_eq allowance)
open Low6969Rectangle (hullOf)
def PaidFourF {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ orderF cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    chargeF ⟨bh,jh,t⟩ l 32 (fourSurfaceF (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t
instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFourF cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidFourF_iff {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    PaidFourF cells t bl jl bh jh l ↔ Low6969Rectangle.PaidFour cells t bl jl bh jh l := by
  simp only [PaidFourF, Low6969Rectangle.PaidFour, chargeF_eq, fourSurfaceF_eq, orderF_eq]
def PaidTiltedF {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤orderF cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    chargeF ⟨B,j,t⟩ l 1920 (tiltF (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t
instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTiltedF cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidTiltedF_iff {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    PaidTiltedF cells t b j B l ↔ Low6969Rectangle.PaidTilted cells t b j B l := by
  simp only [PaidTiltedF, Low6969Rectangle.PaidTilted, chargeF_eq, tiltF_eq, orderF_eq]
end Low6969FastPrice

end Merged_R6960Low6969FastPrice

end Merged_Low6969FastPrice

-- merged module Low6969Encoding
section Merged_Low6969Encoding
namespace Low6969Encoding
open Low6969SharedPrice (Rate)
inductive Tile where
  | rectangle (widthLow indexLow widthHigh indexHigh order : ℕ)
  | point (width index order : ℕ)
  | shared (width index order : ℕ) (rate : Rate)
structure Rectangle where
  widthLow : ℕ
  indexLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
def Tile.bounds : Tile → Rectangle
  | .rectangle b j B J _ => ⟨b,j,B,J⟩
  | .point b j _ | .shared b j _ _ => ⟨b,j,b,j⟩
def InRectangle (r : Rectangle) (width index : ℕ) : Prop :=
  r.widthLow ≤ width ∧ width ≤ r.widthHigh ∧ r.indexLow ≤ index ∧ index ≤ r.indexHigh
def step (index firstMissing : ℕ) (tile : Tile) : ℕ :=
  let r := tile.bounds
  if r.indexLow ≤ index ∧ index ≤ r.indexHigh ∧ r.widthLow ≤ firstMissing then
    max firstMissing (r.widthHigh+1)
  else firstMissing
private theorem step_cover {tile : Tile} {j first b : ℕ}
    (hFirst : first ≤ b) (h : b < step j first tile) : InRectangle tile.bounds b j := by
  dsimp only [step] at h
  split at h
  · rename_i hit
    obtain ⟨hj,hJ,hb⟩ := hit
    exact ⟨hb.trans hFirst, by omega, hj, hJ⟩
  · omega
theorem fold_cover (tiles : List Tile) (j first b : ℕ)
    (hFirst : first ≤ b) (h : b < tiles.foldl (step j) first) :
    ∃ tile ∈ tiles, InRectangle tile.bounds b j := by
  induction tiles generalizing first with
  | nil => simp only [List.foldl_nil] at h; omega
  | cons tile rest ih =>
    rw [List.foldl_cons] at h
    by_cases hb : step j first tile ≤ b
    · obtain ⟨r,hr,hrb⟩ := ih _ hb h
      exact ⟨r,List.mem_cons_of_mem _ hr,hrb⟩
    · exact ⟨tile,List.mem_cons_self,step_cover hFirst (by omega)⟩
def checks (tiles : List Tile) (maxWidth first count : ℕ) : Bool :=
  (List.range count).all fun i =>
    let j := first+i
    decide (maxWidth < tiles.foldl (step j) ((j+2)/3))
theorem checks_join {tiles : List Tile} {maxWidth first left right : ℕ}
    (hl : checks tiles maxWidth first left = true)
    (hr : checks tiles maxWidth (first+left) right = true) :
    checks tiles maxWidth first (left+right) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hn := List.mem_range.mp hi
  by_cases h : i < left
  · exact (List.all_eq_true.mp hl) i (List.mem_range.mpr h)
  · have he : first + i = first + left + (i-left) := by omega
    change decide (maxWidth < tiles.foldl (step (first+i)) ((first+i+2)/3)) = true
    rw [he]
    exact (List.all_eq_true.mp hr) (i-left) (List.mem_range.mpr (by omega))
def decode (word : ℕ) : List Tile :=
  let z := word / 4
  let b := z % 256
  let j := z / 256 % 64
  let l := z / 16384 % 256
  let q := z / 4194304
  match word % 4 with
  | 0 => (List.range (q+1)).map fun i => .point b (j+i) l
  | 1 => [.rectangle b j (b+q%256) (j+q/256) l]
  | _ =>
    let pivot : Fin 3 := ⟨q / 4 % 4 % 3, Nat.mod_lt _ (by decide)⟩
    let split := match q / 16 % 4 with | 0 => 1 | 1 => 2 | _ => 10
    [.shared b j l ⟨if q%2=1 then .tilted else .ordinary, pivot, split, q/2%2=1, q/64⟩]



end Low6969Encoding

end Merged_Low6969Encoding
end Z6969Source2300

-- Source: ProximityPrize.SubmissionLower.Low6969RetainedAggregate
section Z6969Source2301
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Research6969.Low6969RetainedTariffs

open Finset
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Low6969CubicTariff (fatPrice)
open scoped BigOperators

private theorem fold_base {α : Type} (f : ℕ → α → ℕ) (increase : ∀ a x, a ≤ f a x)
    (xs : List α) (a : ℕ) : a ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (increase a x).trans (ih (f a x))

private theorem fold_at {α : Type} (f : ℕ → α → ℕ) (increase : ∀ a x, a ≤ f a x)
    (xs : List α) {x : α} (mem : x ∈ xs) (d a : ℕ) (step : ∀ k, d ≤ f k x) :
    d ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact (List.not_mem_nil mem).elim
  | cons u us ih =>
    rcases List.mem_cons.mp mem with h | h
    · subst u
      exact (step a).trans (fold_base f increase us (f a x))
    · exact ih h (f a u)

theorem single_le_price (x : Shape) (hx : 0 < x.t) : fatPrice x ≤ price x := by
  unfold price
  rw [ite_eq_right hx.ne']
  split
  · exact le_rfl
  · exact fold_base _ (fun k b => fold_base _ (fun _ _ => le_max_left _ _) _ k) _ _

theorem pair_le_price (b c j k : ℕ) (hj : 3 ≤ j) (hk : 3 ≤ k)
    (hb : j ≤ 3 * b) (hc : k ≤ 3 * c) :
    fatPrice ⟨b, j, 1⟩ + fatPrice ⟨c, k, 1⟩ ≤ price ⟨b + c, j + k, 2⟩ := by
  unfold price
  simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ite_false]
  apply fold_at _ (fun a b => fold_base _ (fun _ _ => le_max_left _ _) _ a)
    _ (List.mem_range.mpr (show b < b + c by omega))
  intro a
  apply fold_at _ (fun _ _ => le_max_left _ _) _
    (List.mem_range.mpr (show j < j + k by omega))
  intro v
  apply le_trans _ (le_max_right v (splitFee (b + c) (j + k) b j))
  unfold splitFee
  rw [show b + c - b = c by omega, show j + k - j = k by omega]
  rw [ite_eq_left ⟨by omega, by omega, hj, by omega, hb, hc⟩]

theorem retained_family_fee (n : ℕ) (a : Fin n → Shape) (hv : ∀ i, Valid (a i))
    (hj : (∑ i, (a i).j) ≤ 8) :
    (∑ i, fatPrice (a i)) ≤ price ⟨∑ i, (a i).b, ∑ i, (a i).j, ∑ i, (a i).t⟩ := by
  have hsum : 3 * (∑ i, (a i).t) ≤ ∑ i, (a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _ => (hv i).2.1
  have hn' : n ≤ ∑ i, (a i).t := calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i, (a i).t := sum_le_sum fun i _ => (hv i).1
  have hn : n ≤ 2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one]
    have h : a 0 = ⟨(a 0).b, (a 0).j, (a 0).t⟩ := by cases a 0; rfl
    rw [← h]
    exact single_le_price _ (hv 0).1
  · simp only [Fin.sum_univ_two] at hsum hj ⊢
    have ht0 : (a 0).t = 1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t = 1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i = ⟨(a i).b, (a i).j, (a i).t⟩ := by cases a i; rfl
    have h0 : a 0 = ⟨(a 0).b, (a 0).j, 1⟩ := (he 0).trans
      (congrArg (fun t => (⟨(a 0).b, (a 0).j, t⟩ : Shape)) ht0)
    have h1 : a 1 = ⟨(a 1).b, (a 1).j, 1⟩ := (he 1).trans
      (congrArg (fun t => (⟨(a 1).b, (a 1).j, t⟩ : Shape)) ht1)
    have hj0 : 3 ≤ (a 0).j := by simpa only [ht0, Nat.mul_one] using (hv 0).2.1
    have hj1 : 3 ≤ (a 1).j := by simpa only [ht1, Nat.mul_one] using (hv 1).2.1
    have bound := pair_le_price _ _ _ _ hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [← h0, ← h1] at bound
    rw [ht0, ht1]
    exact bound

end Research6969.Low6969RetainedTariffs

namespace LowProfile6969

open Finset
open P3 (K)
open Polynomial
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)
open Research6969.Low6969CubicTariff (fatPrice)
open Research6969.Low6969RetainedTariffs (price retained_family_fee)
open scoped BigOperators



end LowProfile6969
end Z6969Source2301

-- Source: ProximityPrize.SubmissionLower.Low6969AllocTotal
section Z6969Source2302
set_option autoImplicit true
set_option Elab.async false

-- merged module R6960Low6969GateShapes
section Merged_R6960Low6969GateShapes
set_option Elab.async false

/-! The shapes of the two bands (empty retained shape, and retained shape (w,3,1) with w <= 5) that
the tile cover leaves to the two-cut gates: 13176 shapes. They are exactly the shapes whose
positive-order price exceeds the allowance in the pointwise replay. -/
namespace Low6969Gate
open K1_13 (Shape)
open Low6969SharedPrice (additiveBase nonsharedFee)

/-- Retained floor of gate band `id` (0 = empty, w in 1..9 = (w,3,1), 10 and 11 = (2,4,1), (3,4,1)). -/
def floorShape : ℕ → Shape
  | 0 => ⟨0, 0, 0⟩
  | 1 => ⟨1, 3, 1⟩
  | 2 => ⟨2, 3, 1⟩
  | 3 => ⟨3, 3, 1⟩
  | 4 => ⟨4, 3, 1⟩
  | 5 => ⟨5, 3, 1⟩
  | 6 => ⟨6, 3, 1⟩
  | 7 => ⟨7, 3, 1⟩
  | 8 => ⟨8, 3, 1⟩
  | 9 => ⟨9, 3, 1⟩
  | 10 => ⟨2, 4, 1⟩
  | 11 => ⟨3, 4, 1⟩
  | 12 => ⟨4, 4, 1⟩
  | 13 => ⟨5, 4, 1⟩
  | _ => ⟨0, 0, 0⟩

def gateList : ℕ → ℕ → List (ℕ × ℕ)
  | 0, 2 => [(104, 55), (105, 55), (106, 55), (107, 54), (107, 55), (108, 54), (108, 55), (109, 53), (109, 54), (109, 55), (110, 53), (110, 54), (110, 55), (111, 53), (111, 54), (111, 55), (112, 52), (112, 53),
      (112, 54), (112, 55), (113, 52), (113, 53), (113, 54), (113, 55), (113, 58), (114, 52), (114, 53), (114, 54), (114, 55), (114, 58), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56),
      (115, 58), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 51),
      (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 50), (120, 51),
      (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 49), (122, 50),
      (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58),
      (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56),
      (125, 57), (125, 58), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53),
      (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 48), (129, 49),
      (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56),
      (130, 57), (130, 58), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 47), (132, 48), (132, 49), (132, 50),
      (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56),
      (133, 57), (133, 58), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 47), (135, 48), (135, 49), (135, 50),
      (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55),
      (136, 56), (136, 57), (136, 58), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 46), (138, 47),
      (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52),
      (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57),
      (140, 58), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 46), (142, 47), (142, 48), (142, 49),
      (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 3 => [(108, 55), (109, 55), (110, 55), (111, 54), (111, 55), (112, 54), (112, 55), (112, 58), (113, 54), (113, 55), (113, 58), (114, 53), (114, 54), (114, 55), (114, 58), (115, 53), (115, 54), (115, 55),
      (115, 57), (115, 58), (116, 53), (116, 54), (116, 55), (116, 57), (116, 58), (117, 52), (117, 53), (117, 54), (117, 55), (117, 57), (117, 58), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56),
      (118, 57), (118, 58), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 51), (121, 52),
      (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 51), (123, 52), (123, 53), (123, 54),
      (123, 55), (123, 56), (123, 57), (123, 58), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55),
      (125, 56), (125, 57), (125, 58), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55),
      (127, 56), (127, 57), (127, 58), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54),
      (129, 55), (129, 56), (129, 57), (129, 58), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 49), (131, 50), (131, 51), (131, 52),
      (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 49), (133, 50),
      (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57),
      (134, 58), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53),
      (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 48), (138, 49),
      (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55),
      (139, 56), (139, 57), (139, 58), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 47), (141, 48), (141, 49),
      (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55),
      (142, 56), (142, 57), (142, 58)]
  | 0, 4 => [(102, 55), (103, 55), (104, 55), (105, 54), (105, 55), (106, 54), (106, 55), (107, 54), (107, 55), (108, 53), (108, 54), (108, 55), (108, 58), (109, 53), (109, 54), (109, 55), (109, 58), (110, 53),
      (110, 54), (110, 55), (110, 58), (111, 52), (111, 53), (111, 54), (111, 55), (111, 57), (111, 58), (112, 52), (112, 53), (112, 54), (112, 55), (112, 57), (112, 58), (113, 52), (113, 53), (113, 54),
      (113, 55), (113, 57), (113, 58), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57),
      (115, 58), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 50),
      (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 50),
      (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 50),
      (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58),
      (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56),
      (125, 57), (125, 58), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53),
      (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 48), (129, 49),
      (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56),
      (130, 57), (130, 58), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52),
      (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58),
      (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52),
      (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58),
      (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52),
      (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57),
      (139, 58), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 46), (141, 47), (141, 48), (141, 49),
      (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54),
      (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 5 => [(97, 55), (98, 55), (99, 55), (100, 54), (100, 55), (101, 54), (101, 55), (102, 54), (102, 55), (103, 53), (103, 54), (103, 55), (104, 53), (104, 54), (104, 55), (104, 58), (105, 53), (105, 54),
      (105, 55), (105, 58), (106, 52), (106, 53), (106, 54), (106, 55), (106, 58), (107, 52), (107, 53), (107, 54), (107, 55), (107, 57), (107, 58), (108, 52), (108, 53), (108, 54), (108, 55), (108, 57),
      (108, 58), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 57), (109, 58), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 51), (111, 52),
      (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 50), (113, 51), (113, 52), (113, 53),
      (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 50), (115, 51), (115, 52), (115, 53),
      (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 50), (117, 51), (117, 52), (117, 53),
      (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 49), (119, 50), (119, 51),
      (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 49),
      (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56),
      (122, 57), (122, 58), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52),
      (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 48),
      (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55),
      (127, 56), (127, 57), (127, 58), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 47), (129, 48), (129, 49),
      (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55),
      (130, 56), (130, 57), (130, 58), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 47), (132, 48), (132, 49),
      (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54),
      (133, 55), (133, 56), (133, 57), (133, 58), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 46),
      (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56),
      (137, 57), (137, 58), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 46), (139, 47), (139, 48),
      (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56),
      (141, 57), (141, 58), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 6 => [(93, 55), (94, 55), (95, 55), (96, 54), (96, 55), (97, 54), (97, 55), (98, 54), (98, 55), (99, 53), (99, 54), (99, 55), (100, 53), (100, 54), (100, 55), (101, 53), (101, 54), (101, 55),
      (101, 58), (102, 52), (102, 53), (102, 54), (102, 55), (102, 58), (103, 52), (103, 53), (103, 54), (103, 55), (103, 58), (104, 52), (104, 53), (104, 54), (104, 55), (104, 57), (104, 58), (105, 51),
      (105, 52), (105, 53), (105, 54), (105, 55), (105, 57), (105, 58), (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 57), (106, 58), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54),
      (107, 55), (107, 56), (107, 57), (107, 58), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55),
      (109, 56), (109, 57), (109, 58), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54),
      (111, 55), (111, 56), (111, 57), (111, 58), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 49), (113, 50), (113, 51), (113, 52),
      (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 49), (115, 50),
      (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57),
      (116, 58), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53),
      (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 48), (120, 49),
      (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55),
      (121, 56), (121, 57), (121, 58), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 47), (123, 48), (123, 49),
      (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 47), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55),
      (124, 56), (124, 57), (124, 58), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 46), (126, 47), (126, 48),
      (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53),
      (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58),
      (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50),
      (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55),
      (131, 56), (131, 57), (131, 58), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 45), (133, 46),
      (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51),
      (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56),
      (135, 57), (135, 58), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 45), (137, 46),
      (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54),
      (139, 55), (139, 56), (139, 57), (139, 58), (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58),
      (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 45), (142, 46), (142, 47), (142, 48),
      (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 7 => [(90, 55), (91, 55), (92, 54), (92, 55), (93, 54), (93, 55), (94, 54), (94, 55), (95, 53), (95, 54), (95, 55), (96, 53), (96, 54), (96, 55), (97, 53), (97, 54), (97, 55), (98, 52),
      (98, 53), (98, 54), (98, 55), (98, 58), (99, 52), (99, 53), (99, 54), (99, 55), (99, 58), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 58), (101, 51), (101, 52), (101, 53),
      (101, 54), (101, 55), (101, 57), (101, 58), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55), (102, 57), (102, 58), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 57), (103, 58),
      (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55), (104, 57), (104, 58), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 50),
      (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 49),
      (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 56), (109, 57),
      (109, 58), (110, 49), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54), (111, 55),
      (111, 56), (111, 57), (111, 58), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 48), (113, 49), (113, 50), (113, 51),
      (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 48), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58),
      (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54),
      (116, 55), (116, 56), (116, 57), (116, 58), (117, 47), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 47), (118, 48),
      (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54),
      (119, 55), (119, 56), (119, 57), (119, 58), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 47), (121, 48),
      (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54),
      (122, 55), (122, 56), (122, 57), (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 46),
      (124, 47), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 46), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51),
      (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56),
      (126, 57), (126, 58), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 46), (128, 47), (128, 48),
      (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 45), (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52),
      (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56),
      (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 45), (132, 46),
      (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50),
      (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 45), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54),
      (134, 55), (134, 56), (134, 57), (134, 58), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58),
      (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47),
      (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54),
      (139, 55), (139, 56), (139, 57), (139, 58), (140, 44), (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57),
      (140, 58), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 44), (142, 45),
      (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 8 => [(18, 54), (19, 55), (20, 55), (21, 55), (22, 55), (23, 55), (87, 55), (88, 55), (89, 54), (89, 55), (90, 54), (90, 55), (91, 54), (91, 55), (92, 53), (92, 54), (92, 55), (93, 53),
      (93, 54), (93, 55), (94, 52), (94, 53), (94, 54), (94, 55), (95, 52), (95, 53), (95, 54), (95, 55), (96, 52), (96, 53), (96, 54), (96, 55), (96, 58), (97, 51), (97, 52), (97, 53),
      (97, 54), (97, 55), (97, 58), (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 58), (99, 51), (99, 52), (99, 53), (99, 54), (99, 55), (99, 57), (99, 58), (100, 51), (100, 52),
      (100, 53), (100, 54), (100, 55), (100, 57), (100, 58), (101, 50), (101, 51), (101, 52), (101, 53), (101, 54), (101, 55), (101, 57), (101, 58), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54),
      (102, 55), (102, 57), (102, 58), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55),
      (104, 56), (104, 57), (104, 58), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 49), (106, 50), (106, 51), (106, 52), (106, 53),
      (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 49), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 49), (108, 50), (108, 51),
      (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 48),
      (110, 49), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 48), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54), (111, 55),
      (111, 56), (111, 57), (111, 58), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 48), (113, 49), (113, 50), (113, 51),
      (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 48), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58),
      (115, 47), (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52),
      (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 47), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58),
      (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52),
      (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58),
      (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 46), (122, 47), (122, 48), (122, 49), (122, 50),
      (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55),
      (123, 56), (123, 57), (123, 58), (124, 46), (124, 47), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 46), (125, 47),
      (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52),
      (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56),
      (127, 57), (127, 58), (128, 45), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 45), (129, 46),
      (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50),
      (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54),
      (131, 55), (131, 56), (131, 57), (131, 58), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58),
      (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 44), (134, 45), (134, 46), (134, 47),
      (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50),
      (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53),
      (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56),
      (137, 57), (137, 58), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 44),
      (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 44), (140, 45), (140, 46), (140, 47),
      (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50),
      (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53),
      (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 9 => [(18, 53), (18, 54), (19, 53), (19, 54), (19, 55), (20, 53), (20, 54), (20, 55), (21, 54), (21, 55), (22, 54), (22, 55), (23, 55), (24, 55), (25, 55), (26, 55), (27, 55), (28, 55),
      (85, 55), (86, 55), (87, 54), (87, 55), (88, 54), (88, 55), (89, 54), (89, 55), (90, 53), (90, 54), (90, 55), (91, 53), (91, 54), (91, 55), (92, 52), (92, 53), (92, 54), (92, 55),
      (93, 52), (93, 53), (93, 54), (93, 55), (94, 52), (94, 53), (94, 54), (94, 55), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54), (95, 55), (95, 58), (96, 51), (96, 52), (96, 53),
      (96, 54), (96, 55), (96, 58), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 58), (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 57), (98, 58), (99, 50), (99, 51),
      (99, 52), (99, 53), (99, 54), (99, 55), (99, 57), (99, 58), (100, 50), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 57), (100, 58), (101, 50), (101, 51), (101, 52), (101, 53),
      (101, 54), (101, 55), (101, 56), (101, 57), (101, 58), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55), (102, 56), (102, 57), (102, 58), (103, 49), (103, 50), (103, 51), (103, 52),
      (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55), (104, 56), (104, 57), (104, 58), (105, 49), (105, 50),
      (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 49), (106, 50), (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58),
      (107, 49), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 48), (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55),
      (108, 56), (108, 57), (108, 58), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 48), (110, 49), (110, 50), (110, 51),
      (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 48), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58),
      (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53),
      (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 47), (114, 48), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 47),
      (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53),
      (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 47), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 47),
      (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 46), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52),
      (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 46), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57),
      (120, 58), (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 46), (122, 47), (122, 48), (122, 49),
      (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54),
      (123, 55), (123, 56), (123, 57), (123, 58), (124, 46), (124, 47), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 46),
      (125, 47), (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50),
      (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54),
      (127, 55), (127, 56), (127, 57), (127, 58), (128, 45), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58),
      (129, 45), (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48),
      (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52),
      (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56),
      (132, 57), (132, 58), (133, 44), (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 44),
      (134, 45), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 44), (135, 45), (135, 46), (135, 47),
      (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50),
      (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53),
      (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56),
      (138, 57), (138, 58), (139, 44), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 44),
      (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 43), (141, 44), (141, 45), (141, 46),
      (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48),
      (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 10 => [(17, 51), (18, 52), (18, 53), (18, 54), (19, 52), (19, 53), (19, 54), (19, 55), (20, 52), (20, 53), (20, 54), (20, 55), (21, 53), (21, 54), (21, 55), (22, 54), (22, 55), (23, 54),
      (23, 55), (24, 54), (24, 55), (25, 54), (25, 55), (26, 55), (27, 55), (28, 55), (29, 55), (30, 55), (83, 55), (84, 55), (85, 55), (86, 54), (86, 55), (87, 53), (87, 54), (87, 55),
      (88, 53), (88, 54), (88, 55), (89, 53), (89, 54), (89, 55), (90, 52), (90, 53), (90, 54), (90, 55), (91, 52), (91, 53), (91, 54), (91, 55), (92, 52), (92, 53), (92, 54), (92, 55),
      (93, 52), (93, 53), (93, 54), (93, 55), (93, 58), (94, 51), (94, 52), (94, 53), (94, 54), (94, 55), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54), (95, 55), (95, 58), (96, 51),
      (96, 52), (96, 53), (96, 54), (96, 55), (96, 57), (96, 58), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 57), (97, 58), (98, 50), (98, 51), (98, 52), (98, 53), (98, 54),
      (98, 55), (98, 57), (98, 58), (99, 50), (99, 51), (99, 52), (99, 53), (99, 54), (99, 55), (99, 57), (99, 58), (100, 50), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 56),
      (100, 57), (100, 58), (101, 50), (101, 51), (101, 52), (101, 53), (101, 54), (101, 55), (101, 56), (101, 57), (101, 58), (102, 49), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55),
      (102, 56), (102, 57), (102, 58), (103, 49), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53),
      (104, 54), (104, 55), (104, 56), (104, 57), (104, 58), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 49), (106, 50), (106, 51),
      (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 48), (107, 49), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58),
      (108, 48), (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54),
      (109, 55), (109, 56), (109, 57), (109, 58), (110, 48), (110, 49), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 48), (111, 49), (111, 50),
      (111, 51), (111, 52), (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58), (112, 47), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56),
      (112, 57), (112, 58), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 47), (114, 48), (114, 49), (114, 50),
      (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 47), (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56),
      (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 47), (117, 48), (117, 49), (117, 50),
      (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 46), (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55),
      (118, 56), (118, 57), (118, 58), (119, 46), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 46), (120, 47),
      (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52),
      (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 46), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57),
      (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 46), (124, 47), (124, 48), (124, 49),
      (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 45), (125, 46), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53),
      (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57),
      (126, 58), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 45), (128, 46), (128, 47),
      (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 45), (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51),
      (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55),
      (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 44),
      (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 44), (133, 45), (133, 46), (133, 47),
      (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 44), (134, 45), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50),
      (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53),
      (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56),
      (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 44),
      (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 44), (139, 45), (139, 46), (139, 47),
      (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 44), (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50),
      (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 43), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52),
      (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52), (142, 53), (142, 54),
      (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 11 => [(17, 51), (18, 51), (18, 52), (18, 53), (18, 54), (19, 52), (19, 53), (19, 54), (19, 55), (20, 52), (20, 53), (20, 54), (20, 55), (21, 52), (21, 53), (21, 54), (21, 55), (22, 53),
      (22, 54), (22, 55), (23, 53), (23, 54), (23, 55), (24, 54), (24, 55), (25, 54), (25, 55), (26, 54), (26, 55), (27, 55), (28, 55), (29, 55), (30, 55), (31, 55), (32, 55), (82, 55),
      (83, 55), (84, 54), (84, 55), (85, 54), (85, 55), (86, 53), (86, 54), (86, 55), (87, 53), (87, 54), (87, 55), (88, 53), (88, 54), (88, 55), (89, 52), (89, 53), (89, 54), (89, 55),
      (90, 52), (90, 53), (90, 54), (90, 55), (91, 52), (91, 53), (91, 54), (91, 55), (92, 52), (92, 53), (92, 54), (92, 55), (92, 58), (93, 51), (93, 52), (93, 53), (93, 54), (93, 55),
      (93, 58), (94, 51), (94, 52), (94, 53), (94, 54), (94, 55), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54), (95, 55), (95, 57), (95, 58), (96, 51), (96, 52), (96, 53), (96, 54),
      (96, 55), (96, 57), (96, 58), (97, 50), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 57), (97, 58), (98, 50), (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 57),
      (98, 58), (99, 50), (99, 51), (99, 52), (99, 53), (99, 54), (99, 55), (99, 56), (99, 57), (99, 58), (100, 50), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 56), (100, 57),
      (100, 58), (101, 49), (101, 50), (101, 51), (101, 52), (101, 53), (101, 54), (101, 55), (101, 56), (101, 57), (101, 58), (102, 49), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55),
      (102, 56), (102, 57), (102, 58), (103, 49), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53),
      (104, 54), (104, 55), (104, 56), (104, 57), (104, 58), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 48), (106, 49), (106, 50),
      (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 48), (107, 49), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57),
      (107, 58), (108, 48), (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53),
      (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 48), (110, 49), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 47), (111, 48),
      (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58), (112, 47), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54),
      (112, 55), (112, 56), (112, 57), (112, 58), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 47), (114, 48),
      (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 47), (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54),
      (115, 55), (115, 56), (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 46), (117, 47),
      (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 46), (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52),
      (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 46), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57),
      (119, 58), (120, 46), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 46), (121, 47), (121, 48), (121, 49),
      (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 46), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54),
      (122, 55), (122, 56), (122, 57), (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 45),
      (124, 46), (124, 47), (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 45), (125, 46), (125, 47), (125, 48), (125, 49),
      (125, 50), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53),
      (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57),
      (127, 58), (128, 45), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 45), (129, 46), (129, 47),
      (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51),
      (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55),
      (131, 56), (131, 57), (131, 58), (132, 44), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58),
      (133, 44), (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 44), (134, 45), (134, 46),
      (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49),
      (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55),
      (137, 56), (137, 57), (137, 58), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58),
      (139, 44), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 44), (140, 45), (140, 46),
      (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 43), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48),
      (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50),
      (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 12 => [(17, 51), (18, 51), (18, 52), (18, 53), (18, 54), (19, 51), (19, 52), (19, 53), (19, 54), (19, 55), (20, 52), (20, 53), (20, 54), (20, 55), (21, 52), (21, 53), (21, 54), (21, 55),
      (22, 52), (22, 53), (22, 54), (22, 55), (23, 52), (23, 53), (23, 54), (23, 55), (24, 53), (24, 54), (24, 55), (25, 54), (25, 55), (26, 54), (26, 55), (27, 54), (27, 55), (28, 54),
      (28, 55), (29, 55), (30, 55), (31, 55), (32, 55), (33, 55), (34, 55), (35, 55), (81, 55), (82, 55), (83, 55), (84, 54), (84, 55), (85, 53), (85, 54), (85, 55), (86, 53), (86, 54),
      (86, 55), (87, 53), (87, 54), (87, 55), (88, 52), (88, 53), (88, 54), (88, 55), (89, 52), (89, 53), (89, 54), (89, 55), (90, 52), (90, 53), (90, 54), (90, 55), (91, 52), (91, 53),
      (91, 54), (91, 55), (91, 58), (92, 51), (92, 52), (92, 53), (92, 54), (92, 55), (92, 58), (93, 51), (93, 52), (93, 53), (93, 54), (93, 55), (93, 58), (94, 51), (94, 52), (94, 53),
      (94, 54), (94, 55), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54), (95, 55), (95, 57), (95, 58), (96, 50), (96, 51), (96, 52), (96, 53), (96, 54), (96, 55), (96, 57), (96, 58),
      (97, 50), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 57), (97, 58), (98, 50), (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 56), (98, 57), (98, 58), (99, 50),
      (99, 51), (99, 52), (99, 53), (99, 54), (99, 55), (99, 56), (99, 57), (99, 58), (100, 50), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 56), (100, 57), (100, 58), (101, 49),
      (101, 50), (101, 51), (101, 52), (101, 53), (101, 54), (101, 55), (101, 56), (101, 57), (101, 58), (102, 49), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55), (102, 56), (102, 57),
      (102, 58), (103, 49), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55),
      (104, 56), (104, 57), (104, 58), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 48), (106, 49), (106, 50), (106, 51), (106, 52),
      (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 48), (107, 49), (107, 50), (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 48),
      (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55),
      (109, 56), (109, 57), (109, 58), (110, 48), (110, 49), (110, 50), (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 47), (111, 48), (111, 49), (111, 50),
      (111, 51), (111, 52), (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58), (112, 47), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56),
      (112, 57), (112, 58), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 47), (114, 48), (114, 49), (114, 50),
      (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 47), (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56),
      (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 46), (117, 47), (117, 48), (117, 49),
      (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 46), (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54),
      (118, 55), (118, 56), (118, 57), (118, 58), (119, 46), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 46),
      (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51),
      (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 46), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56),
      (122, 57), (122, 58), (123, 46), (123, 47), (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 45), (124, 46), (124, 47),
      (124, 48), (124, 49), (124, 50), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 45), (125, 46), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51),
      (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55),
      (126, 56), (126, 57), (126, 58), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 45),
      (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 45), (129, 46), (129, 47), (129, 48), (129, 49),
      (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53),
      (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57),
      (131, 58), (132, 44), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 44), (133, 45),
      (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 44), (134, 45), (134, 46), (134, 47), (134, 48),
      (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54),
      (136, 55), (136, 56), (136, 57), (136, 58), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57),
      (137, 58), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 44), (139, 45),
      (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 44), (140, 45), (140, 46), (140, 47), (140, 48),
      (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 43), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50),
      (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52),
      (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 13 => [(17, 51), (18, 51), (18, 52), (18, 53), (18, 54), (19, 51), (19, 52), (19, 53), (19, 54), (19, 55), (20, 51), (20, 52), (20, 53), (20, 54), (20, 55), (21, 52), (21, 53), (21, 54),
      (21, 55), (22, 52), (22, 53), (22, 54), (22, 55), (23, 52), (23, 53), (23, 54), (23, 55), (24, 53), (24, 54), (24, 55), (25, 53), (25, 54), (25, 55), (26, 54), (26, 55), (27, 54),
      (27, 55), (28, 54), (28, 55), (29, 54), (29, 55), (30, 55), (31, 55), (32, 55), (33, 55), (34, 55), (35, 55), (36, 55), (37, 55), (80, 55), (81, 54), (81, 55), (82, 55), (83, 54),
      (83, 55), (84, 54), (84, 55), (85, 53), (85, 54), (85, 55), (86, 53), (86, 54), (86, 55), (87, 53), (87, 54), (87, 55), (88, 52), (88, 53), (88, 54), (88, 55), (89, 52), (89, 53),
      (89, 54), (89, 55), (90, 52), (90, 53), (90, 54), (90, 55), (91, 52), (91, 53), (91, 54), (91, 55), (91, 58), (92, 51), (92, 52), (92, 53), (92, 54), (92, 55), (92, 58), (93, 51),
      (93, 52), (93, 53), (93, 54), (93, 55), (93, 58), (94, 51), (94, 52), (94, 53), (94, 54), (94, 55), (94, 57), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54), (95, 55), (95, 57),
      (95, 58), (96, 50), (96, 51), (96, 52), (96, 53), (96, 54), (96, 55), (96, 57), (96, 58), (97, 50), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 57), (97, 58), (98, 50),
      (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 56), (98, 57), (98, 58), (99, 50), (99, 51), (99, 52), (99, 53), (99, 54), (99, 55), (99, 56), (99, 57), (99, 58), (100, 50),
      (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 56), (100, 57), (100, 58), (101, 49), (101, 50), (101, 51), (101, 52), (101, 53), (101, 54), (101, 55), (101, 56), (101, 57), (101, 58),
      (102, 49), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55), (102, 56), (102, 57), (102, 58), (103, 49), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56),
      (103, 57), (103, 58), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55), (104, 56), (104, 57), (104, 58), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54),
      (105, 55), (105, 56), (105, 57), (105, 58), (106, 48), (106, 49), (106, 50), (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 48), (107, 49), (107, 50),
      (107, 51), (107, 52), (107, 53), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 48), (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57),
      (108, 58), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 48), (110, 49), (110, 50), (110, 51), (110, 52), (110, 53),
      (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 47), (111, 48), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54), (111, 55), (111, 56), (111, 57), (111, 58), (112, 47),
      (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53),
      (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 47), (114, 48), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 47),
      (115, 48), (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51), (116, 52), (116, 53),
      (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 47), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 41),
      (118, 46), (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 41), (119, 46), (119, 47), (119, 48), (119, 49),
      (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58), (120, 41), (120, 46), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53),
      (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 41), (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57),
      (121, 58), (122, 41), (122, 46), (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 41), (123, 46), (123, 47),
      (123, 48), (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 41), (124, 46), (124, 47), (124, 48), (124, 49), (124, 50), (124, 51),
      (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 41), (125, 45), (125, 46), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51), (125, 52), (125, 53), (125, 54),
      (125, 55), (125, 56), (125, 57), (125, 58), (126, 40), (126, 41), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56),
      (126, 57), (126, 58), (127, 40), (127, 41), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57), (127, 58),
      (128, 40), (128, 41), (128, 45), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56), (128, 57), (128, 58), (129, 40), (129, 41),
      (129, 45), (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 40), (130, 41), (130, 45), (130, 46),
      (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 40), (131, 41), (131, 45), (131, 46), (131, 47), (131, 48),
      (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57), (131, 58), (132, 40), (132, 41), (132, 44), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49),
      (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 40), (133, 41), (133, 44), (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50),
      (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 40), (134, 41), (134, 44), (134, 45), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51),
      (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 40), (135, 41), (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52),
      (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 39), (136, 40), (136, 41), (136, 44), (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 39), (137, 40), (137, 41), (137, 44), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52),
      (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 39), (138, 40), (138, 41), (138, 44), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52),
      (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 39), (139, 40), (139, 41), (139, 44), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52),
      (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 39), (140, 40), (140, 41), (140, 44), (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 39), (141, 40), (141, 41), (141, 43), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49), (141, 50), (141, 51),
      (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 39), (142, 40), (142, 41), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50),
      (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 14 => [(17, 51), (18, 51), (18, 52), (18, 53), (18, 54), (19, 51), (19, 52), (19, 53), (19, 54), (19, 55), (20, 52), (20, 53), (20, 54), (20, 55), (21, 52), (21, 53), (21, 54), (21, 55),
      (22, 52), (22, 53), (22, 54), (22, 55), (23, 52), (23, 53), (23, 54), (23, 55), (24, 53), (24, 54), (24, 55), (25, 53), (25, 54), (25, 55), (26, 54), (26, 55), (27, 54), (27, 55),
      (28, 54), (28, 55), (29, 54), (29, 55), (30, 55), (31, 55), (32, 55), (33, 55), (34, 55), (35, 55), (36, 55), (37, 55), (38, 55), (80, 55), (81, 54), (81, 55), (82, 55), (83, 54),
      (83, 55), (84, 53), (84, 54), (84, 55), (85, 53), (85, 54), (85, 55), (86, 53), (86, 54), (86, 55), (87, 53), (87, 54), (87, 55), (88, 52), (88, 53), (88, 54), (88, 55), (89, 52),
      (89, 53), (89, 54), (89, 55), (90, 52), (90, 53), (90, 54), (90, 55), (90, 58), (91, 52), (91, 53), (91, 54), (91, 55), (91, 58), (92, 51), (92, 52), (92, 53), (92, 54), (92, 55),
      (92, 58), (93, 51), (93, 52), (93, 53), (93, 54), (93, 55), (93, 58), (94, 51), (94, 52), (94, 53), (94, 54), (94, 55), (94, 57), (94, 58), (95, 51), (95, 52), (95, 53), (95, 54),
      (95, 55), (95, 57), (95, 58), (96, 50), (96, 51), (96, 52), (96, 53), (96, 54), (96, 55), (96, 57), (96, 58), (97, 50), (97, 51), (97, 52), (97, 53), (97, 54), (97, 55), (97, 56),
      (97, 57), (97, 58), (98, 50), (98, 51), (98, 52), (98, 53), (98, 54), (98, 55), (98, 56), (98, 57), (98, 58), (99, 44), (99, 50), (99, 51), (99, 52), (99, 53), (99, 54), (99, 55),
      (99, 56), (99, 57), (99, 58), (100, 44), (100, 50), (100, 51), (100, 52), (100, 53), (100, 54), (100, 55), (100, 56), (100, 57), (100, 58), (101, 44), (101, 49), (101, 50), (101, 51), (101, 52),
      (101, 53), (101, 54), (101, 55), (101, 56), (101, 57), (101, 58), (102, 44), (102, 49), (102, 50), (102, 51), (102, 52), (102, 53), (102, 54), (102, 55), (102, 56), (102, 57), (102, 58), (103, 44),
      (103, 49), (103, 50), (103, 51), (103, 52), (103, 53), (103, 54), (103, 55), (103, 56), (103, 57), (103, 58), (104, 44), (104, 49), (104, 50), (104, 51), (104, 52), (104, 53), (104, 54), (104, 55),
      (104, 56), (104, 57), (104, 58), (105, 43), (105, 44), (105, 49), (105, 50), (105, 51), (105, 52), (105, 53), (105, 54), (105, 55), (105, 56), (105, 57), (105, 58), (106, 43), (106, 44), (106, 48),
      (106, 49), (106, 50), (106, 51), (106, 52), (106, 53), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 43), (107, 44), (107, 48), (107, 49), (107, 50), (107, 51), (107, 52), (107, 53),
      (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 43), (108, 44), (108, 48), (108, 49), (108, 50), (108, 51), (108, 52), (108, 53), (108, 54), (108, 55), (108, 56), (108, 57), (108, 58),
      (109, 43), (109, 44), (109, 48), (109, 49), (109, 50), (109, 51), (109, 52), (109, 53), (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 43), (110, 44), (110, 48), (110, 49), (110, 50),
      (110, 51), (110, 52), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 42), (111, 43), (111, 44), (111, 48), (111, 49), (111, 50), (111, 51), (111, 52), (111, 53), (111, 54),
      (111, 55), (111, 56), (111, 57), (111, 58), (112, 42), (112, 43), (112, 44), (112, 47), (112, 48), (112, 49), (112, 50), (112, 51), (112, 52), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57),
      (112, 58), (113, 42), (113, 43), (113, 44), (113, 47), (113, 48), (113, 49), (113, 50), (113, 51), (113, 52), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 42), (114, 43),
      (114, 44), (114, 47), (114, 48), (114, 49), (114, 50), (114, 51), (114, 52), (114, 53), (114, 54), (114, 55), (114, 56), (114, 57), (114, 58), (115, 42), (115, 43), (115, 44), (115, 47), (115, 48),
      (115, 49), (115, 50), (115, 51), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 42), (116, 43), (116, 44), (116, 47), (116, 48), (116, 49), (116, 50), (116, 51),
      (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 42), (117, 43), (117, 44), (117, 47), (117, 48), (117, 49), (117, 50), (117, 51), (117, 52), (117, 53), (117, 54),
      (117, 55), (117, 56), (117, 57), (117, 58), (118, 42), (118, 43), (118, 44), (118, 46), (118, 47), (118, 48), (118, 49), (118, 50), (118, 51), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56),
      (118, 57), (118, 58), (119, 42), (119, 43), (119, 44), (119, 46), (119, 47), (119, 48), (119, 49), (119, 50), (119, 51), (119, 52), (119, 53), (119, 54), (119, 55), (119, 56), (119, 57), (119, 58),
      (120, 42), (120, 43), (120, 44), (120, 46), (120, 47), (120, 48), (120, 49), (120, 50), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 42), (121, 43),
      (121, 44), (121, 46), (121, 47), (121, 48), (121, 49), (121, 50), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55), (121, 56), (121, 57), (121, 58), (122, 42), (122, 43), (122, 44), (122, 46),
      (122, 47), (122, 48), (122, 49), (122, 50), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 42), (123, 43), (123, 44), (123, 46), (123, 47), (123, 48),
      (123, 49), (123, 50), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55), (123, 56), (123, 57), (123, 58), (124, 42), (124, 43), (124, 44), (124, 46), (124, 47), (124, 48), (124, 49), (124, 50),
      (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 42), (125, 43), (125, 44), (125, 45), (125, 46), (125, 47), (125, 48), (125, 49), (125, 50), (125, 51),
      (125, 52), (125, 53), (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 42), (126, 43), (126, 44), (126, 45), (126, 46), (126, 47), (126, 48), (126, 49), (126, 50), (126, 51), (126, 52),
      (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 42), (127, 43), (127, 44), (127, 45), (127, 46), (127, 47), (127, 48), (127, 49), (127, 50), (127, 51), (127, 52), (127, 53),
      (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 42), (128, 43), (128, 44), (128, 45), (128, 46), (128, 47), (128, 48), (128, 49), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54),
      (128, 55), (128, 56), (128, 57), (128, 58), (129, 42), (129, 43), (129, 44), (129, 45), (129, 46), (129, 47), (129, 48), (129, 49), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55),
      (129, 56), (129, 57), (129, 58), (130, 42), (130, 43), (130, 44), (130, 45), (130, 46), (130, 47), (130, 48), (130, 49), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (130, 56),
      (130, 57), (130, 58), (131, 42), (131, 43), (131, 44), (131, 45), (131, 46), (131, 47), (131, 48), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57),
      (131, 58), (132, 42), (132, 43), (132, 44), (132, 45), (132, 46), (132, 47), (132, 48), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58),
      (133, 42), (133, 43), (133, 44), (133, 45), (133, 46), (133, 47), (133, 48), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 42),
      (134, 43), (134, 44), (134, 45), (134, 46), (134, 47), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (134, 56), (134, 57), (134, 58), (135, 42), (135, 43),
      (135, 44), (135, 45), (135, 46), (135, 47), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 42), (136, 43), (136, 44),
      (136, 45), (136, 46), (136, 47), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 42), (137, 43), (137, 44), (137, 45),
      (137, 46), (137, 47), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 42), (138, 43), (138, 44), (138, 45), (138, 46),
      (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (138, 56), (138, 57), (138, 58), (139, 42), (139, 43), (139, 44), (139, 45), (139, 46), (139, 47),
      (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58), (140, 42), (140, 43), (140, 44), (140, 45), (140, 46), (140, 47), (140, 48),
      (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 42), (141, 43), (141, 44), (141, 45), (141, 46), (141, 47), (141, 48), (141, 49),
      (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 42), (142, 43), (142, 44), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50),
      (142, 51), (142, 52), (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 0, 15 => [(90, 58), (91, 58), (92, 58), (93, 57), (93, 58), (94, 57), (94, 58), (95, 57), (95, 58), (96, 57), (96, 58), (97, 56), (97, 57), (97, 58), (98, 56), (98, 57), (98, 58), (99, 56),
      (99, 57), (99, 58), (100, 56), (100, 57), (100, 58), (101, 55), (101, 56), (101, 57), (101, 58), (102, 55), (102, 56), (102, 57), (102, 58), (103, 55), (103, 56), (103, 57), (103, 58), (104, 55),
      (104, 56), (104, 57), (104, 58), (105, 55), (105, 56), (105, 57), (105, 58), (106, 54), (106, 55), (106, 56), (106, 57), (106, 58), (107, 54), (107, 55), (107, 56), (107, 57), (107, 58), (108, 54),
      (108, 55), (108, 56), (108, 57), (108, 58), (109, 54), (109, 55), (109, 56), (109, 57), (109, 58), (110, 53), (110, 54), (110, 55), (110, 56), (110, 57), (110, 58), (111, 53), (111, 54), (111, 55),
      (111, 56), (111, 57), (111, 58), (112, 53), (112, 54), (112, 55), (112, 56), (112, 57), (112, 58), (113, 53), (113, 54), (113, 55), (113, 56), (113, 57), (113, 58), (114, 53), (114, 54), (114, 55),
      (114, 56), (114, 57), (114, 58), (115, 52), (115, 53), (115, 54), (115, 55), (115, 56), (115, 57), (115, 58), (116, 52), (116, 53), (116, 54), (116, 55), (116, 56), (116, 57), (116, 58), (117, 52),
      (117, 53), (117, 54), (117, 55), (117, 56), (117, 57), (117, 58), (118, 52), (118, 53), (118, 54), (118, 55), (118, 56), (118, 57), (118, 58), (119, 47), (119, 52), (119, 53), (119, 54), (119, 55),
      (119, 56), (119, 57), (119, 58), (120, 47), (120, 51), (120, 52), (120, 53), (120, 54), (120, 55), (120, 56), (120, 57), (120, 58), (121, 47), (121, 51), (121, 52), (121, 53), (121, 54), (121, 55),
      (121, 56), (121, 57), (121, 58), (122, 47), (122, 51), (122, 52), (122, 53), (122, 54), (122, 55), (122, 56), (122, 57), (122, 58), (123, 47), (123, 51), (123, 52), (123, 53), (123, 54), (123, 55),
      (123, 56), (123, 57), (123, 58), (124, 47), (124, 51), (124, 52), (124, 53), (124, 54), (124, 55), (124, 56), (124, 57), (124, 58), (125, 46), (125, 47), (125, 50), (125, 51), (125, 52), (125, 53),
      (125, 54), (125, 55), (125, 56), (125, 57), (125, 58), (126, 46), (126, 47), (126, 50), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (126, 56), (126, 57), (126, 58), (127, 46), (127, 47),
      (127, 50), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (127, 56), (127, 57), (127, 58), (128, 46), (128, 47), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (128, 56),
      (128, 57), (128, 58), (129, 46), (129, 47), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (129, 56), (129, 57), (129, 58), (130, 46), (130, 47), (130, 50), (130, 51), (130, 52),
      (130, 53), (130, 54), (130, 55), (130, 56), (130, 57), (130, 58), (131, 45), (131, 46), (131, 47), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (131, 56), (131, 57),
      (131, 58), (132, 45), (132, 46), (132, 47), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (132, 56), (132, 57), (132, 58), (133, 45), (133, 46), (133, 47), (133, 49),
      (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (133, 56), (133, 57), (133, 58), (134, 45), (134, 46), (134, 47), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54),
      (134, 55), (134, 56), (134, 57), (134, 58), (135, 45), (135, 46), (135, 47), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (135, 56), (135, 57), (135, 58), (136, 45),
      (136, 46), (136, 47), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (136, 56), (136, 57), (136, 58), (137, 45), (137, 46), (137, 47), (137, 48), (137, 49), (137, 50),
      (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (137, 56), (137, 57), (137, 58), (138, 45), (138, 46), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55), (138, 56), (138, 57), (138, 58), (139, 45), (139, 46), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (139, 56), (139, 57), (139, 58),
      (140, 45), (140, 46), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (140, 56), (140, 57), (140, 58), (141, 45), (141, 46), (141, 47), (141, 48),
      (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55), (141, 56), (141, 57), (141, 58), (142, 45), (142, 46), (142, 47), (142, 48), (142, 49), (142, 50), (142, 51), (142, 52),
      (142, 53), (142, 54), (142, 55), (142, 56), (142, 57), (142, 58)]
  | 1, 2 => [(134, 55), (135, 55), (136, 54), (136, 55), (137, 54), (137, 55), (138, 53), (138, 54), (138, 55), (139, 53), (139, 54), (139, 55), (140, 53), (140, 54), (140, 55), (141, 52), (141, 53), (141, 54),
      (141, 55)]
  | 1, 3 => [(129, 55), (130, 55), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 53), (135, 54), (135, 55), (136, 53), (136, 54), (136, 55), (137, 52), (137, 53),
      (137, 54), (137, 55), (138, 52), (138, 53), (138, 54), (138, 55), (139, 52), (139, 53), (139, 54), (139, 55), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 51), (141, 52), (141, 53),
      (141, 54), (141, 55)]
  | 1, 4 => [(126, 55), (127, 55), (128, 54), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55),
      (134, 52), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 50),
      (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 5 => [(123, 55), (124, 55), (125, 54), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 52),
      (131, 53), (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52),
      (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 50), (138, 51), (138, 52), (138, 53),
      (138, 54), (138, 55), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 49), (141, 50), (141, 51),
      (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 6 => [(120, 55), (121, 55), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54),
      (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50),
      (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55),
      (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 48), (141, 49), (141, 50), (141, 51),
      (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 7 => [(118, 55), (119, 55), (120, 55), (121, 54), (121, 55), (122, 54), (122, 55), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55),
      (127, 52), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51),
      (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52),
      (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50),
      (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54),
      (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 8 => [(117, 55), (118, 55), (119, 54), (119, 55), (120, 54), (120, 55), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 52),
      (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52),
      (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53),
      (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 9 => [(115, 55), (116, 55), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55),
      (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51),
      (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53),
      (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53),
      (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50),
      (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51),
      (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53),
      (141, 54), (141, 55)]
  | 1, 10 => [(114, 55), (115, 55), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55),
      (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53),
      (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55),
      (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55),
      (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55),
      (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 48),
      (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 11 => [(114, 55), (115, 55), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55),
      (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51), (127, 52),
      (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54),
      (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54),
      (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55),
      (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 12 => [(113, 55), (114, 55), (115, 55), (116, 54), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53),
      (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52), (126, 53), (126, 54),
      (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51),
      (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51),
      (133, 52), (133, 53), (133, 54), (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51),
      (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 13 => [(113, 55), (114, 55), (115, 55), (116, 54), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53),
      (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55),
      (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51), (130, 52),
      (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52),
      (133, 53), (133, 54), (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49),
      (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52),
      (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54),
      (140, 55), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53), (141, 54), (141, 55)]
  | 1, 14 => [(113, 55), (114, 55), (115, 55), (116, 54), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53),
      (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55),
      (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53),
      (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 44), (133, 50), (133, 51), (133, 52),
      (133, 53), (133, 54), (133, 55), (134, 44), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 44), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 44), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 43), (137, 44), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 43),
      (138, 44), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 43), (139, 44), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55),
      (140, 43), (140, 44), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55), (141, 43), (141, 44), (141, 48), (141, 49), (141, 50), (141, 51), (141, 52), (141, 53),
      (141, 54), (141, 55)]
  | 2, 2 => [(136, 55), (137, 55), (138, 54), (138, 55), (139, 54), (139, 55), (140, 53), (140, 54), (140, 55)]
  | 2, 3 => [(132, 55), (133, 55), (134, 54), (134, 55), (135, 54), (135, 55), (136, 52), (136, 53), (136, 54), (136, 55), (137, 52), (137, 53), (137, 54), (137, 55), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 4 => [(129, 55), (130, 53), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 50), (138, 51), (138, 52),
      (138, 53), (138, 54), (138, 55), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 5 => [(125, 54), (126, 55), (127, 53), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55),
      (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49),
      (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55)]
  | 2, 6 => [(123, 54), (123, 55), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54), (128, 55),
      (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53),
      (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52),
      (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48),
      (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 48), (140, 49), (140, 50),
      (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 7 => [(121, 54), (121, 55), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 52),
      (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55),
      (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54),
      (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50),
      (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52),
      (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55)]
  | 2, 8 => [(117, 55), (118, 55), (119, 54), (120, 54), (120, 55), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 52),
      (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50),
      (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49),
      (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53),
      (134, 54), (134, 55), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55),
      (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47),
      (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 9 => [(116, 55), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55),
      (124, 52), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55),
      (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50),
      (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54),
      (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49),
      (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50),
      (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 10 => [(115, 55), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 52),
      (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52), (126, 53), (126, 54), (126, 55), (127, 51),
      (127, 52), (127, 53), (127, 54), (127, 55), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 50), (130, 51),
      (130, 52), (130, 53), (130, 54), (130, 55), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55),
      (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 48), (135, 49), (135, 50),
      (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49), (137, 50), (137, 51), (137, 52),
      (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52),
      (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 11 => [(114, 55), (115, 55), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 53), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 52), (122, 53),
      (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52), (126, 53),
      (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54),
      (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49), (132, 50), (132, 51), (132, 52),
      (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55),
      (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49),
      (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49),
      (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 12 => [(114, 55), (115, 55), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 53), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 52), (122, 53),
      (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52), (126, 53),
      (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50), (129, 51), (129, 52), (129, 53), (129, 54),
      (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49), (132, 50), (132, 51), (132, 52),
      (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 48), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55),
      (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49),
      (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 47), (139, 48), (139, 49),
      (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 13 => [(114, 55), (115, 55), (116, 54), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 53), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 52),
      (122, 53), (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52),
      (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 50), (129, 51), (129, 52), (129, 53),
      (129, 54), (129, 55), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 49), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 49), (132, 50), (132, 51),
      (132, 52), (132, 53), (132, 54), (132, 55), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55),
      (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 48), (137, 49),
      (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 47), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 41), (139, 47), (139, 48),
      (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 41), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52), (140, 53), (140, 54), (140, 55)]
  | 2, 14 => [(114, 55), (115, 55), (116, 54), (116, 55), (117, 54), (117, 55), (118, 54), (118, 55), (119, 53), (119, 54), (119, 55), (120, 53), (120, 54), (120, 55), (121, 53), (121, 54), (121, 55), (122, 52),
      (122, 53), (122, 54), (122, 55), (123, 52), (123, 53), (123, 54), (123, 55), (124, 52), (124, 53), (124, 54), (124, 55), (125, 51), (125, 52), (125, 53), (125, 54), (125, 55), (126, 51), (126, 52),
      (126, 53), (126, 54), (126, 55), (127, 51), (127, 52), (127, 53), (127, 54), (127, 55), (128, 50), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 44), (129, 50), (129, 51), (129, 52),
      (129, 53), (129, 54), (129, 55), (130, 44), (130, 50), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 44), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 43),
      (132, 44), (132, 49), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 43), (133, 44), (133, 49), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 43),
      (134, 44), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 43), (135, 44), (135, 48), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 42), (136, 43), (136, 44), (136, 48), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 42), (137, 43), (137, 44), (137, 48), (137, 49), (137, 50), (137, 51),
      (137, 52), (137, 53), (137, 54), (137, 55), (138, 42), (138, 43), (138, 44), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 42), (139, 43), (139, 44),
      (139, 47), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55), (140, 42), (140, 43), (140, 44), (140, 47), (140, 48), (140, 49), (140, 50), (140, 51), (140, 52),
      (140, 53), (140, 54), (140, 55)]
  | 3, 2 => [(136, 55), (137, 55), (138, 54), (138, 55), (139, 54), (139, 55)]
  | 3, 3 => [(132, 55), (133, 55), (134, 54), (134, 55), (135, 54), (135, 55), (136, 53), (136, 54), (136, 55), (137, 53), (137, 54), (137, 55), (138, 52), (138, 53), (138, 54), (138, 55), (139, 52), (139, 53),
      (139, 54), (139, 55)]
  | 3, 4 => [(129, 55), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 52), (136, 53),
      (136, 54), (136, 55), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 5 => [(126, 55), (127, 55), (128, 54), (128, 55), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53),
      (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51),
      (137, 52), (137, 53), (137, 54), (137, 55), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 6 => [(124, 55), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 52), (131, 53),
      (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 7 => [(122, 55), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54),
      (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53),
      (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53),
      (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 49), (139, 50),
      (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 8 => [(120, 55), (121, 55), (122, 54), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55),
      (128, 52), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55),
      (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50),
      (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54),
      (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 9 => [(119, 55), (120, 55), (121, 54), (121, 55), (122, 54), (122, 55), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55),
      (127, 52), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55),
      (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50),
      (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54),
      (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49),
      (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 10 => [(118, 55), (119, 55), (120, 55), (121, 54), (121, 55), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 52), (126, 53),
      (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55), (130, 51), (130, 52), (130, 53),
      (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50), (133, 51), (133, 52), (133, 53),
      (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 49), (136, 50), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 11 => [(118, 55), (119, 55), (120, 54), (120, 55), (121, 54), (121, 55), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53), (125, 54), (125, 55),
      (126, 52), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53), (129, 54), (129, 55),
      (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 50),
      (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 49), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54),
      (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 12 => [(117, 55), (118, 55), (119, 55), (120, 54), (120, 55), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53),
      (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53),
      (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53),
      (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49),
      (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 13 => [(117, 55), (118, 55), (119, 55), (120, 54), (120, 55), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53),
      (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 51), (129, 52), (129, 53),
      (129, 54), (129, 55), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 50), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 50), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53),
      (135, 54), (135, 55), (136, 49), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 48), (138, 49),
      (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 41), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 3, 14 => [(117, 55), (118, 55), (119, 55), (120, 54), (120, 55), (121, 54), (121, 55), (122, 53), (122, 54), (122, 55), (123, 53), (123, 54), (123, 55), (124, 53), (124, 54), (124, 55), (125, 52), (125, 53),
      (125, 54), (125, 55), (126, 52), (126, 53), (126, 54), (126, 55), (127, 52), (127, 53), (127, 54), (127, 55), (128, 51), (128, 52), (128, 53), (128, 54), (128, 55), (129, 44), (129, 51), (129, 52),
      (129, 53), (129, 54), (129, 55), (130, 44), (130, 51), (130, 52), (130, 53), (130, 54), (130, 55), (131, 44), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 43), (132, 44), (132, 50),
      (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 43), (133, 44), (133, 50), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 43), (134, 44), (134, 50), (134, 51), (134, 52),
      (134, 53), (134, 54), (134, 55), (135, 43), (135, 44), (135, 49), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 42), (136, 43), (136, 44), (136, 49), (136, 50), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55), (137, 42), (137, 43), (137, 44), (137, 49), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 42), (138, 43), (138, 44), (138, 48),
      (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55), (139, 42), (139, 43), (139, 44), (139, 48), (139, 49), (139, 50), (139, 51), (139, 52), (139, 53), (139, 54), (139, 55)]
  | 4, 3 => [(135, 55), (136, 55), (137, 54), (137, 55), (138, 54), (138, 55)]
  | 4, 4 => [(131, 55), (132, 55), (133, 55), (134, 54), (134, 55), (135, 54), (135, 55), (136, 53), (136, 54), (136, 55), (137, 53), (137, 54), (137, 55), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 5 => [(129, 55), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 52), (136, 53),
      (136, 54), (136, 55), (137, 52), (137, 53), (137, 54), (137, 55), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 6 => [(126, 55), (127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52),
      (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 7 => [(124, 55), (125, 55), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52), (132, 53),
      (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 8 => [(123, 55), (124, 55), (125, 54), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55),
      (131, 52), (131, 53), (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55),
      (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 50),
      (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 9 => [(122, 55), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55),
      (130, 52), (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55),
      (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50),
      (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 10 => [(121, 55), (122, 55), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53),
      (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53),
      (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54),
      (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 4, 11 => [(120, 55), (121, 55), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53), (128, 54),
      (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55)]
  | 4, 12 => [(120, 55), (121, 55), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53),
      (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53),
      (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 50), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54),
      (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53),
      (138, 54), (138, 55)]
  | 4, 13 => [(120, 55), (121, 55), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 53), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 52), (128, 53),
      (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 51), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53),
      (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54),
      (138, 55)]
  | 4, 14 => [(120, 55), (121, 55), (122, 55), (123, 54), (123, 55), (124, 54), (124, 55), (125, 54), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55),
      (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 44), (131, 52), (131, 53), (131, 54), (131, 55), (132, 44), (132, 51), (132, 52), (132, 53), (132, 54),
      (132, 55), (133, 44), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 43), (134, 44), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 43), (135, 44), (135, 50), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (136, 43), (136, 44), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 43), (137, 44), (137, 50), (137, 51), (137, 52), (137, 53),
      (137, 54), (137, 55), (138, 42), (138, 43), (138, 44), (138, 49), (138, 50), (138, 51), (138, 52), (138, 53), (138, 54), (138, 55)]
  | 5, 3 => [(137, 55)]
  | 5, 4 => [(134, 55), (135, 55), (136, 54), (136, 55), (137, 54), (137, 55)]
  | 5, 5 => [(131, 55), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55), (135, 52), (135, 54), (135, 55), (136, 53), (136, 54), (136, 55), (137, 53), (137, 54), (137, 55)]
  | 5, 6 => [(129, 55), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 52), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 7 => [(127, 55), (128, 55), (129, 53), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52),
      (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54),
      (137, 55)]
  | 5, 8 => [(126, 55), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 52), (132, 53), (132, 54), (132, 55),
      (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 9 => [(125, 55), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54),
      (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51),
      (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 10 => [(124, 55), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52), (130, 53), (130, 54),
      (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51), (134, 52), (134, 53),
      (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51), (137, 52), (137, 53),
      (137, 54), (137, 55)]
  | 5, 11 => [(123, 54), (123, 55), (124, 55), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52),
      (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51),
      (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51),
      (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 12 => [(123, 54), (123, 55), (124, 55), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52),
      (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51),
      (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51),
      (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 13 => [(123, 54), (123, 55), (124, 55), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52),
      (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55), (134, 51),
      (134, 52), (134, 53), (134, 54), (134, 55), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 50), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55), (137, 50), (137, 51),
      (137, 52), (137, 53), (137, 54), (137, 55)]
  | 5, 14 => [(123, 54), (123, 55), (124, 55), (125, 55), (126, 53), (126, 54), (126, 55), (127, 53), (127, 54), (127, 55), (128, 53), (128, 54), (128, 55), (129, 52), (129, 53), (129, 54), (129, 55), (130, 52),
      (130, 53), (130, 54), (130, 55), (131, 52), (131, 53), (131, 54), (131, 55), (132, 51), (132, 52), (132, 53), (132, 54), (132, 55), (133, 44), (133, 51), (133, 52), (133, 53), (133, 54), (133, 55),
      (134, 44), (134, 51), (134, 52), (134, 53), (134, 54), (134, 55), (135, 44), (135, 50), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 44), (136, 50), (136, 51), (136, 52), (136, 53),
      (136, 54), (136, 55), (137, 43), (137, 44), (137, 50), (137, 51), (137, 52), (137, 53), (137, 54), (137, 55)]
  | 6, 4 => [(134, 55), (135, 55), (136, 54), (136, 55)]
  | 6, 5 => [(132, 55), (133, 55), (134, 54), (134, 55), (135, 54), (135, 55), (136, 53), (136, 54), (136, 55)]
  | 6, 6 => [(129, 55), (130, 55), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 53), (135, 54), (135, 55), (136, 52), (136, 53), (136, 54), (136, 55)]
  | 6, 7 => [(128, 55), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54),
      (135, 55), (136, 52), (136, 53), (136, 54), (136, 55)]
  | 6, 8 => [(126, 55), (127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53),
      (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55)]
  | 6, 9 => [(125, 55), (126, 55), (127, 55), (128, 54), (128, 55), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53),
      (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55)]
  | 6, 10 => [(124, 55), (125, 55), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52), (132, 53),
      (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52), (136, 53),
      (136, 54), (136, 55)]
  | 6, 11 => [(124, 55), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52),
      (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55)]
  | 6, 12 => [(124, 55), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55), (132, 52),
      (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51), (136, 52),
      (136, 53), (136, 54), (136, 55)]
  | 6, 13 => [(123, 55), (124, 55), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55),
      (132, 52), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55), (136, 51),
      (136, 52), (136, 53), (136, 54), (136, 55)]
  | 6, 14 => [(123, 55), (124, 55), (125, 55), (126, 54), (126, 55), (127, 54), (127, 55), (128, 54), (128, 55), (129, 53), (129, 54), (129, 55), (130, 53), (130, 54), (130, 55), (131, 53), (131, 54), (131, 55),
      (132, 52), (132, 53), (132, 54), (132, 55), (133, 52), (133, 53), (133, 54), (133, 55), (134, 52), (134, 53), (134, 54), (134, 55), (135, 44), (135, 51), (135, 52), (135, 53), (135, 54), (135, 55),
      (136, 44), (136, 51), (136, 52), (136, 53), (136, 54), (136, 55)]
  | 7, 5 => [(134, 55), (135, 55)]
  | 7, 6 => [(132, 55), (133, 55), (134, 54), (134, 55), (135, 54), (135, 55)]
  | 7, 7 => [(130, 55), (131, 55), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55), (135, 53), (135, 54), (135, 55)]
  | 7, 8 => [(129, 55), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 53), (135, 54), (135, 55)]
  | 7, 9 => [(128, 55), (129, 55), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 53), (135, 54), (135, 55)]
  | 7, 10 => [(127, 55), (128, 55), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52), (135, 53), (135, 54),
      (135, 55)]
  | 7, 11 => [(127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52),
      (135, 53), (135, 54), (135, 55)]
  | 7, 12 => [(127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55), (135, 52),
      (135, 53), (135, 54), (135, 55)]
  | 7, 13 => [(126, 55), (127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55),
      (135, 52), (135, 53), (135, 54), (135, 55)]
  | 7, 14 => [(126, 55), (127, 55), (128, 55), (129, 54), (129, 55), (130, 54), (130, 55), (131, 54), (131, 55), (132, 53), (132, 54), (132, 55), (133, 53), (133, 54), (133, 55), (134, 53), (134, 54), (134, 55),
      (135, 44), (135, 52), (135, 53), (135, 54), (135, 55)]
  | 8, 7 => [(133, 55), (134, 55)]
  | 8, 8 => [(132, 55), (133, 55), (134, 54), (134, 55)]
  | 8, 9 => [(131, 55), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 8, 10 => [(130, 55), (131, 55), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 8, 11 => [(130, 55), (131, 55), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 8, 12 => [(130, 55), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 8, 13 => [(130, 55), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 8, 14 => [(130, 55), (131, 55), (132, 54), (132, 55), (133, 54), (133, 55), (134, 54), (134, 55)]
  | 9, 10 => [(133, 55)]
  | 9, 11 => [(133, 55)]
  | 9, 12 => [(133, 55)]
  | 9, 13 => [(133, 55)]
  | 9, 14 => [(133, 55)]
  | 10, 7 => [(139, 54), (140, 54)]
  | 10, 8 => [(137, 54), (138, 54), (139, 54), (140, 53), (140, 54)]
  | 10, 9 => [(136, 54), (137, 54), (138, 54), (139, 53), (139, 54), (140, 53), (140, 54)]
  | 10, 10 => [(135, 54), (136, 54), (137, 54), (138, 53), (138, 54), (139, 53), (139, 54), (140, 53), (140, 54)]
  | 10, 11 => [(135, 54), (136, 54), (137, 54), (138, 53), (138, 54), (139, 53), (139, 54), (140, 53), (140, 54)]
  | 10, 12 => [(134, 54), (135, 54), (136, 54), (137, 53), (137, 54), (138, 53), (138, 54), (139, 53), (139, 54), (140, 53), (140, 54)]
  | 10, 13 => [(134, 54), (135, 54), (136, 54), (137, 53), (137, 54), (138, 53), (138, 54), (139, 53), (139, 54), (140, 53), (140, 54)]
  | 10, 14 => [(134, 54), (135, 54), (136, 54), (137, 54), (138, 53), (138, 54), (139, 53), (139, 54), (140, 44), (140, 53), (140, 54)]
  | 11, 9 => [(139, 53), (139, 54)]
  | 11, 10 => [(139, 53), (139, 54)]
  | 11, 11 => [(138, 53), (138, 54), (139, 53), (139, 54)]
  | 11, 12 => [(138, 53), (138, 54), (139, 53), (139, 54)]
  | 11, 13 => [(138, 53), (138, 54), (139, 53), (139, 54)]
  | 11, 14 => [(138, 53), (138, 54), (139, 53), (139, 54)]
  | 12, 13 => [(138, 54)]
  | 13, 11 => [(137, 54)]
  | 13, 12 => [(137, 54)]
  | 13, 13 => [(137, 54)]
  | 13, 14 => [(137, 54)]
  | _, _ => []

def Gated (id : ℕ) (x : Shape) : Prop := id < 14 ∧ (x.b,x.j) ∈ gateList id x.t

instance (id : ℕ) (x : Shape) : Decidable (Gated id x) := by unfold Gated; infer_instance

/-- Price of a factor of shape `x` at order `l` under the gate charge `G`. -/
def gatePrice (G : Shape → ℕ) (x : Shape) (l : ℕ) : ℕ := additiveBase x l + nonsharedFee x l + G x

end Low6969Gate
end Merged_R6960Low6969GateShapes

-- merged module R6960Low6969AllocTiles
section Merged_R6960Low6969AllocTiles
set_option Elab.async false
set_option maxHeartbeats 2800000
set_option maxRecDepth 18000
namespace Low6969Allocation
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (Tile checks)
open Low6969Prices (physicalPrice physicalPriceOld tiltedFits activeFitsPrice)
open Low6969RetainedCut (contractedPrice)
open Low6969WeightedRate (Allowed)
open Low6969Gate (Gated gatePrice)
open Low6969Monotone (physicalPrice_le_old physical_mono)
open Low6969Encoding (InRectangle fold_cover step)
def actualRate (u : Low6969SharedPrice.Rate) := u
def Covered {k : Band} (cells : List (MassCell k)) (x : Shape) : Prop :=
  (∃ l,0<l ∧ l≤order cells x ∧ contractedPrice x (start k) l 178 ≤
    allowance k ((start k).t+x.t) x.b x.j x.t) ∨
  ∃ u l,k=empty ∧ 0<l ∧ l≤order cells x ∧ Allowed x u ∧
    Low6969SharedPrice.price x l 178 u ≤ allowance k x.t x.b x.j x.t
def decode (word : ℕ) : List Tile :=
  if word % 4 = 3 then
    let z := word / 4
    let b := z % 256
    let j := z / 256 % 64
    let l := z / 16384 % 256
    let q := z / 4194304
    let marker := if 65536≤q then 512 else 256
    [.rectangle b j (b+q%256) (j+q%65536/256) (marker+l)]
  else Low6969Encoding.decode word
def unpack (words : List ℕ) : List Tile := words.flatMap decode
def Paid {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6969Rectangle.PaidTilted cells t b j B (l-512)
      else if 256≤l then Low6969Rectangle.PaidFour cells t b j B J (l-256)
      else 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => (l=0 ∧ Gated k.val ⟨b,j,t⟩) ∨ (0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      contractedPrice ⟨b,j,t⟩ (start k) l 178 ≤ allowance k ((start k).t+t) b j t)
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Allowed ⟨b,j,t⟩ (actualRate u) ∧
      Low6969SharedPrice.price ⟨b,j,t⟩ l 178 (actualRate u) ≤ allowance k t b j t
instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (Paid cells t tile) := by cases tile <;> unfold Paid <;> infer_instance
def PaidF {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6969FastPrice.PaidTiltedF cells t b j B (l-512)
      else if 256≤l then Low6969FastPrice.PaidFourF cells t b j B J (l-256)
      else 0<l ∧ l≤orderF cells ⟨b,j,0⟩ ∧
        Low6969FastPrice.physicalPriceOldF ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => (l=0 ∧ Gated k.val ⟨b,j,t⟩) ∨ (0<l ∧ l≤orderF cells ⟨b,j,t⟩ ∧
      Low6969FastPrice.contractedPriceF ⟨b,j,t⟩ (start k) l 178 ≤ allowance k ((start k).t+t) b j t)
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤orderF cells ⟨b,j,t⟩ ∧
      Low6969FastPrice.AllowedF ⟨b,j,t⟩ (actualRate u) ∧
      Low6969FastPrice.priceF ⟨b,j,t⟩ l 178 (actualRate u) ≤ allowance k t b j t
instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (PaidF cells t tile) := by cases tile <;> unfold PaidF <;> infer_instance
theorem paidF_iff {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    PaidF cells t tile ↔ Paid cells t tile := by
  cases tile <;> simp only [PaidF, Paid, Low6969Allocation.orderF_eq, Low6969FastPrice.paidTiltedF_iff,
    Low6969FastPrice.paidFourF_iff, Low6969FastPrice.physicalPriceOldF_eq,
    Low6969FastPrice.contractedPriceF_eq, Low6969FastPrice.allowedF_iff, Low6969FastPrice.priceF_eq]
def pays {k : Band} (cells : List (MassCell k)) (t : ℕ) (tiles : List Tile) : Bool :=
  tiles.all (fun tile=>decide (PaidF cells t tile))
abbrev PaidBatch {k : Band} (cells : List (MassCell k)) (t : ℕ) :=
  {tiles : List Tile // pays cells t tiles=true}
def tilesOf {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) : List Tile :=
  batches.flatMap Subtype.val
private theorem batches_pay {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) :
    pays cells t (tilesOf batches)=true := by
  induction batches with
  | nil => rfl
  | cons head tail ih =>
    change pays cells t (head.val ++ tilesOf tail)=true
    rw [show pays cells t (head.val ++ tilesOf tail)=
      (pays cells t head.val && pays cells t (tilesOf tail)) by simp [pays,List.all_append]]
    rw [head.property,ih]
    rfl
private theorem contracted_le (x h : Shape) (l : ℕ) :
    contractedPrice x h l 178 ≤ physicalPrice x l 178 := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl
private theorem tile_cover {tile : Tile} {k : Band} {cells : List (MassCell k)} {t : ℕ} {a : Shape}
    (paid : Paid cells t tile) (bounds : InRectangle tile.bounds a.b a.j)
    (ht : a.t=t) (hi : 3*a.t≤a.j) : Covered cells a ∨ Gated k.val a := by
  rcases tile with ⟨b,j,B,J,l⟩ | ⟨b,j,l⟩ | ⟨b,j,l,u⟩
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    by_cases tilted : 512 ≤ l
    · have receipt : J=j ∧ Low6969Rectangle.PaidTilted cells t b j B (l-512) := by
        simpa only [Paid,ite_eq_left tilted] using paid
      have hja : a.j≤J := hJ
      exact Or.inl (Or.inl (Low6969Rectangle.tilted receipt.2 hb hB
        (Nat.le_antisymm (hja.trans_eq receipt.1) hj) ht))
    by_cases h : 256 ≤ l
    · have receipt : Low6969Rectangle.PaidFour cells t b j B J (l-256) := by
        simpa only [Paid, ite_eq_right tilted, ite_eq_left h] using paid
      exact Or.inl (Or.inl (Low6969Rectangle.four receipt hb hj hB hJ ht hi))
    have receipt : 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t := by
      simpa only [Paid, ite_eq_right tilted, ite_eq_right h] using paid
    obtain ⟨lp,lo,fee⟩ := receipt
    have ord := lo.trans (order_mono cells hb hj)
    have box : InBox a ⟨B,J,t⟩ := ⟨hB,hJ,ht.le⟩
    have charge : allowance k ((start k).t+t) b j t≤allowance k ((start k).t+t) a.b a.j a.t :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hb hj ht.ge))
    exact Or.inl (Or.inl ⟨l,lp,ord,
      ((contracted_le _ _ _).trans (physicalPrice_le_old _ _ _)).trans
        ((physical_mono box hi (ht ▸ hi.trans hJ) l).trans (fee.trans (by simpa only [ht] using charge)))⟩)
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    rcases paid with ⟨-,hg⟩ | paid
    · exact Or.inr hg
    · exact Or.inl (Or.inl ⟨l,paid⟩)
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    exact Or.inl (Or.inr ⟨actualRate u,l,paid⟩)
theorem cover_at {k : Band} {cells : List (MassCell k)} {t maxWidth maxIndex : ℕ}
    {batches : List (PaidBatch cells t)}
    (hcover : Low6969Encoding.checks (tilesOf batches) maxWidth (3*t) (maxIndex+1-3*t) = true)
    (a : Shape) (ha : Valid a) (ht : a.t=t) (hb : a.b≤maxWidth) (hj : a.j≤maxIndex) :
    Covered cells a ∨ Gated k.val a := by
  let i := a.j-3*t
  have hleft : 3*t≤a.j := ht ▸ ha.2.1
  have hi : i∈List.range (maxIndex+1-3*t) := List.mem_range.mpr (by dsimp [i]; omega)
  have eq : 3*t+i=a.j := by dsimp [i]; omega
  have row := List.all_eq_true.mp hcover i hi
  change decide (maxWidth < (tilesOf batches).foldl (step (3*t+i)) ((3*t+i+2)/3))=true at row
  rw [eq] at row
  obtain ⟨tile,mem,bounds⟩ := fold_cover (tilesOf batches) a.j ((a.j+2)/3) a.b
    (by have := ha.2.2; omega) (hb.trans_lt (of_decide_eq_true row))
  have proof := (List.all_eq_true.mp (batches_pay batches)) tile mem
  exact tile_cover ((paidF_iff cells t tile).mp (of_decide_eq_true proof)) bounds ht ha.2.1
structure Receipt (k : Band) where
  orders : List (MassCell k)
  covers : ∀ a : Shape,Valid a → InBox ((start k).plus a) (Low6969Prices.fullCap 15) →
    Covered orders a ∨ Gated k.val a
def GateTable (orders : ∀ k : Band, List (MassCell k)) (G : Shape → ℕ) : Prop :=
  ∀ k : Band, ∀ x : Shape, Valid x → InBox ((start k).plus x) (Low6969Prices.fullCap 15) →
    Gated k.val x → ∃ l, 0<l ∧ l≤order (orders k) x ∧
      gatePrice G x l ≤ allowance k ((start k).t+x.t) x.b x.j x.t
end Low6969Allocation

end Merged_R6960Low6969AllocTiles

-- merged module R6960Low6969AllocTotal
section Merged_R6960Low6969AllocTotal

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Low6969AllocTotal
open K1_13 (Shape InBox FatEligible)
open Low6969RetainedCut (contractedPrice)
open K1_13_8 (Valid zeroShape)
open Final50PriceLayer (availableMass)
open Low6969Prices (physicalPrice fatPrice)
open Low6969Prices (layerNeed LayerBudget fullCap Fits)
open Low6969Allocation
open Low6969Retained (Box)
open Low6969Gate (Gated gatePrice)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_insert shapeSum_union shapeSum_mono inBox_trans inBox_shapeSum shapeSum_valid_or_empty)

def retainedShape {n : ℕ} (a : Fin n → Shape) (l : Fin n → ℕ) : Shape :=
  P3_6_8.shapeSum a (Finset.univ.filter fun i => l i = 0)

private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} {k : Band} (ha : ∀ i, Valid (a i)) (hr : Valid (P3_6_8.shapeSum a z))
    (hbox : Box (P3_6_8.shapeSum a z)) (hk : Admits k (P3_6_8.shapeSum a z))
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ reserve k := by
  let r := P3_6_8.shapeSum a z
  let er := z.equivFin.symm
  let ar : Fin z.card → Shape := fun i => a (er i).val
  have sums (g : Shape → ℕ) : (∑ i, g (ar i)) = ∑ i ∈ z, g (a i) := by
    rw [← Finset.sum_attach z (fun i => g (a i))]
    exact Fintype.sum_equiv er _ _ fun _ => rfl
  have hj : (∑ i, (ar i).j) ≤ 8 := by rw [sums]; exact hbox.2.1
  have hp := Research6969.Low6969RetainedTariffs.retained_family_fee z.card ar
    (fun i => ha (er i).val) hj
  rw [sums, sums, sums, sums] at hp
  have covers := Research6969.Low6969RetainedTariffs.covers_shape hbox hr
  have price : Research6969.Low6969RetainedTariffs.price r = retainedTariff r.b r.j r.t :=
    (Research6969.Low6969RetainedTariffs.tariff_eq r covers).symm
  refine (Finset.sum_le_sum fun i hi => hfat i ?_).trans
    (hp.trans (price.le.trans (admits_fee hk)))
  have h := P3_6_8.inBox_shapeSum a hi
  exact ⟨(h.1.trans hbox.1).trans (by decide), (h.2.1.trans hbox.2.1).trans (by decide)⟩

/-- Total cost of all factors in the low-height cover. -/
theorem total (receipts : ∀ k : Band, Receipt k) (G : Shape → ℕ)
    (htab : GateTable (fun k => (receipts k).orders) G) (top : ℕ) (htop : top ≤ 15) (n : ℕ) (a : Fin n → Shape) (l cost : Fin n → ℕ)
    (hfits : Fits top a) (hlayers : LayerBudget a l)
    (hphys : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) →
      cost i ≤ contractedPrice (a i) (start k) m 178)
    (hshared : ∀ i m u, 0 < m → m ≤ l i → Low6969WeightedRate.Allowed (a i) u →
      cost i ≤ Low6969SharedPrice.price (a i) m 178 u)
    (hgate : ∀ i m, 0 < m → m ≤ l i → ∀ k, Admits k (retainedShape a l) → Gated k.val (a i) →
      cost i ≤ gatePrice G (a i) m)
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ fatPrice (a i)) :
    (∑ i, cost i) ≤ factorCap top := by
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := P3_6_8.shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ k : Band, Admits k r ∧
      (∑ i ∈ z, cost i) ≤ reserve k := by
    rcases Low6969Retained.no_cut_shape a l ha hlayers z hz with hempty | ⟨hret, htr, _⟩
    · have hr0 : r = zeroShape := by simp [r, hempty, P3_6_8.shapeSum_empty]
      refine ⟨empty,hr0.symm ▸ empty_admits,?_⟩
      rw [hempty,Finset.sum_empty]
      omega
    · have hr : Valid r := (P3_6_8.shapeSum_valid_or_empty ha z).resolve_left (by
        intro he
        have heq : P3_6_8.shapeSum a z = zeroShape := he ▸ P3_6_8.shapeSum_empty a
        have hpos : 1 ≤ (P3_6_8.shapeSum a z).t := htr
        rw [heq] at hpos
        exact (by decide : ¬ (1 ≤ zeroShape.t)) hpos)
      obtain ⟨k,hk⟩ := choose_band r hr hret
      exact ⟨k,hk,retained_cost ha hr hret hk hfat⟩
  obtain ⟨k,hk,hcost⟩ := account
  let q := start k
  have hqr : InBox q r := admits_floor hk
  have massKind : q = zeroShape ∨ 0 < q.j := start_flat k
  have hreserve : reserve k ≤ factorCap top := reserve_fits top htop k
  have hall : InBox (P3_6_8.shapeSum a Finset.univ) (fullCap top) := hfits.2
  have member_cap {s : Finset (Fin n)} (hs : s ⊆ pos) :
      InBox (q.plus (P3_6_8.shapeSum a s)) (fullCap top) := by
    have hb := P3_6_8.shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [P3_6_8.shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (P3_6_8.shapeSum a s)) (r.plus (P3_6_8.shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _, Nat.add_le_add_right hqr.2.2 _⟩
    exact P3_6_8.inBox_trans hle (P3_6_8.inBox_trans hb hall)
  have positive_fee (i : Fin n) (hi : i ∈ pos) :
      cost i ≤ allowance k top (a i).b (a i).j (a i).t := by
    have hone : P3_6_8.shapeSum a {i} = a i := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl,
        P3_6_8.shapeSum_insert a (by simp),P3_6_8.shapeSum_empty]
      cases a i
      simp [zeroShape, Shape.plus]
    have hsingle : ({i} : Finset (Fin n)) ⊆ pos := Finset.singleton_subset_iff.mpr hi
    have hL : 0 < l i := hpos i hi
    have hj0 : 0 < (a i).j := by
      obtain ⟨ht, hj, _⟩ := ha i
      omega
    have hj : 0 < q.j + (a i).j := by omega
    have hmass0 := Low6969Retained.mass_le hlayers hz
      (s := {i}) (L := l i) (by simp) (hdisj hsingle) hqr
    rw [hone] at hmass0
    have hmass := hmass0.trans (layer_le_available massKind hj)
    have horder : order (receipts k).orders (a i) ≤ l i := by
      rcases order_valid (receipts k).orders (a i) with h | h
      · omega
      · by_contra! hn
        have hmono := Final50PriceLayer.availableMass_mono massKind hj
          (show l i ≤ order (receipts k).orders (a i) - 1 by omega)
        exact (not_lt_of_ge (hmass.trans hmono)) h
    have hc := member_cap hsingle
    rw [hone] at hc
    have goal : InBox ((start k).plus (a i)) (fullCap 15) :=
      ⟨hc.1,hc.2.1,hc.2.2.trans htop⟩
    have ht : (start k).t+(a i).t≤top := hc.2.2
    rcases (receipts k).covers (a i) (ha i) goal with (⟨m,hm,hmo,hfee⟩ | ⟨u,m,he,hm,hmo,hu,hfee⟩) | hg
    · exact (hphys i m hm (hmo.trans horder) k hk).trans
        (hfee.trans (allowance_mono k ht htop))
    · exact (hshared i m u hm (hmo.trans horder) hu).trans
        (hfee.trans (allowance_mono k (ht.trans' (Nat.le_add_left _ _)) htop))
    · obtain ⟨m,hm,hmo,hfee⟩ := htab k (a i) (ha i) goal hg
      exact (hgate i m hm (hmo.trans horder) k hk hg).trans
        (hfee.trans (allowance_mono k ht htop))
  have hfits_pos := member_cap (s := pos) (Finset.Subset.rfl)
  have hwidth : (∑ i ∈ pos, (a i).b) ≤ 142 - q.b := by
    have hh := hfits_pos.1
    change q.b + (∑ i ∈ pos, (a i).b) ≤ 142 at hh
    omega
  have hindex : (∑ i ∈ pos, (a i).j) ≤ 58 - q.j := by
    have hh := hfits_pos.2.1
    change q.j + (∑ i ∈ pos, (a i).j) ≤ 58 at hh
    omega
  have hDen : 0 < pricingDenom k := denom_pos k
  have hweights : (∑ i ∈ pos, pricingWeight k (a i).b (a i).j (a i).t) ≤ pricingDenom k := by
    by_cases he : k = empty
    · subst k
      change (∑ i∈pos,Low6969AllocWeight.weight (a i).b (a i).j (a i).t) ≤ 374
      exact Low6969AllocWeight.sum_le htop a hfits pos
    · by_cases htier : tiered k
      · simpa [q, pricingWeight, pricingDenom, he, htier] using
          (Research6966.LowTierWeight.total pos (fun i => (a i).j) hindex)
      · simpa [q, pricingWeight, pricingDenom, he, htier] using hindex
  let C := factorCap top - reserve k
  let M := pricingDenom k
  have fees (i : Fin n) (hi : i ∈ pos) : M*cost i ≤ C * pricingWeight k (a i).b (a i).j (a i).t := by
    have h := Nat.mul_le_mul_left M (positive_fee i hi)
    change M*cost i ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) at h
    calc
      _ ≤ M*(C*pricingWeight k (a i).b (a i).j (a i).t / M) := h
      _ = (C*pricingWeight k (a i).b (a i).j (a i).t / M)*M := Nat.mul_comm _ _
      _ ≤ _ := Nat.div_mul_le_self _ _
  have hweighted : M * (∑ i ∈ pos, cost i) ≤ M*C := by
    rw [Finset.mul_sum, mul_comm M C]
    refine (Finset.sum_le_sum fees).trans ?_
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left _ hweights
  have hp : (∑ i ∈ pos, cost i) ≤ C := Nat.le_of_mul_le_mul_left hweighted hDen
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap top
  dsimp [C] at hp
  omega

end Low6969AllocTotal

end Merged_R6960Low6969AllocTotal
end Z6969Source2302
