-- Ported from public PR657, e07f14a81dfe2cf1bda985e67040ad4d31fe81ab, HighCore82258Data.lean.
import ProximityPrize.SubmissionLower.KoalaH2429Banks
import ProximityPrize.SubmissionLower.KoalaH2429TerminalBankB

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258

abbrev agreement:ℕ:=179876
abbrev heightCap:ℕ:=33443
abbrev Bank:=P1_7.Bank
abbrev Stage:=P1_7.Stage
abbrev Grade:=P1_7.Grade
abbrev debit:=P1_7.debit

inductive Band where
  | h2367
  | h2430
  | h2429
  | h2429B
  deriving DecidableEq

open K1_14 (Shape shapeSum triangle slots)
def start : Band → ℕ
  | .h2367 => 2431
  | .h2430 => 2430
  | .h2429 | .h2429B => 2429
def finish : Band → ℕ
  | .h2367 => 2695
  | .h2430 => 2430
  | .h2429 | .h2429B => 2429
def terminal : Band → Bank
  | .h2367 => ⟨⟨4600,6398,1353,415799⟩,0xa30a49bf40000,0x290bd5ec7938⟩
  | .h2430 => KoalaH2430Banks.terminal
  | .h2429 => KoalaH2429Banks.terminal
  | .h2429B => KoalaH2429TerminalB.terminal
def grades : Band → List Grade
  | .h2367 => []
  | .h2430 => []
  | .h2429 | .h2429B => []
def stages : Band → List Stage
  | .h2367 => [⟨0,⟨⟨70,97,21,1045⟩,0x28d4c0000,0x284e2c⟩,⟨⟨417,580,122,17574⟩,0x1f4b8940000,0xb758706b⟩⟩,
    ⟨1,⟨⟨77,107,23,1159⟩,0x35da00000,0x3ae575⟩,⟨⟨436,606,128,20348⟩,0x23d8b880000,0xdb115372⟩⟩,
    ⟨2,⟨⟨86,119,26,1174⟩,0x4b3780000,0x5a8245⟩,⟨⟨523,727,154,20490⟩,0x3de60680000,0x1c5b77ce0⟩⟩,
    ⟨3,⟨⟨93,129,28,1278⟩,0x5e72c0000,0x7bb5e0⟩,⟨⟨497,691,144,25411⟩,0x347eb240000,0x16dd8a416⟩⟩,
    ⟨4,⟨⟨103,143,31,1292⟩,0x7fa800000,0xb978d4⟩,⟨⟨525,731,154,27846⟩,0x3e6d7fc0000,0x1cdc7da38⟩⟩,
    ⟨5,⟨⟨111,154,33,1393⟩,0x9dd080000,0xf64733⟩,⟨⟨652,906,191,25654⟩,0x773dc800000,0x43fc612ca⟩⟩,
    ⟨7,⟨⟨126,175,39,1509⟩,0xec9f00000,0x1a458a5⟩,⟨⟨695,966,204,30493⟩,0x90934f00000,0x57ee6dc45⟩⟩,
    ⟨10,⟨⟨142,197,43,1977⟩,0x14bde80000,0x294fec6⟩,⟨⟨865,1202,254,34321⟩,0x1166fe340000,0xd28832ce8⟩⟩,
    ⟨16,⟨⟨171,237,50,3725⟩,0x2316e80000,0x53b7f45⟩,⟨⟨1059,1473,310,46798⟩,0x1fd33c580000,0x1d8ad324e3⟩⟩,
    ⟨10,⟨⟨178,247,55,1419⟩,0x2932d00000,0x66c8fdf⟩,⟨⟨827,1150,242,35505⟩,0xf2bf9c80000,0xafe167953⟩⟩,
    ⟨20,⟨⟨215,299,66,2831⟩,0x47ec700000,0xd9f9f46⟩,⟨⟨1350,1878,396,50248⟩,0x41f8149c0000,0x4e1409a395⟩⟩,
    ⟨20,⟨⟨250,347,77,2229⟩,0x71041c0000,0x18b7e486⟩,⟨⟨1360,1893,399,50070⟩,0x4373e8600000,0x509300a57a⟩⟩,
    ⟨26,⟨⟨230,318,70,5254⟩,0x575d000000,0x115d6f33⟩,⟨⟨1450,2018,424,65568⟩,0x5186864c0000,0x67c5a7c1f4⟩⟩,
    ⟨32,⟨⟨256,355,79,8006⟩,0x7978e00000,0x1b1f653e⟩,⟨⟨1467,2041,430,96167⟩,0x549403e80000,0x6ccf71d82e⟩⟩,
    ⟨31,⟨⟨340,471,106,3028⟩,0x11d7aac0000,0x544a4209⟩,⟨⟨1790,2489,526,69841⟩,0x99da4d600000,0xf10deb594c⟩⟩,
    ⟨38,⟨⟨340,471,104,4636⟩,0x1196c380000,0x53100efb⟩,⟨⟨2059,2864,605,82690⟩,0xea109ad80000,0x1a640ee22cd⟩⟩,
    ⟨50,⟨⟨420,584,129,5916⟩,0x212bb440000,0xc3b69b6e⟩,⟨⟨2720,3784,799,100085⟩,0x21b2df4c00000,0x5055cdfca34⟩⟩,
    ⟨70,⟨⟨574,794,177,7396⟩,0x54ac1b40000,0x29ef4219f⟩,⟨⟨3487,4851,1023,136386⟩,0x46e7550000000,0xd8a91833248⟩⟩,
    ⟨70,⟨⟨450,626,134,133643⟩,0x27d33980000,0xfbef358d⟩,⟨⟨2820,3926,832,179195⟩,0x25ad525a80000,0x5d58d7fc090⟩⟩,
    ⟨84,⟨⟨650,904,200,9511⟩,0x7aa2ccc0000,0x45f662bb3⟩,⟨⟨4200,5843,1234,157910⟩,0x7c020ca840000,0x1c86bbc42d5b⟩⟩,
    ⟨103,⟨⟨790,1096,237,11616⟩,0xd7b5b1c0000,0x9443175ae⟩,⟨⟨4765,6631,1396,197280⟩,0xb4aacea6c0000,0x2f3124f90909⟩⟩,
    ⟨61,⟨⟨398,554,118,288997⟩,0x1b800f00000,0x9a361749⟩,⟨⟨2164,3012,632,283229⟩,0x10e708bd80000,0x201c0863f68⟩⟩]
  | .h2430 => KoalaH2430Banks.stages
  | .h2429 | .h2429B => KoalaH2429Banks.stages
def fees : Band → P1_7.PrefixFees
  | .h2367 => ⟨109475923649793959,226219551202,1054546277047582,6632,27077674872813,39671623094646⟩
  | .h2430 => ⟨111192823856840915,236508407164,1058671324708468,6626,26511801161182,39950745637500⟩
  | .h2429 => ⟨113020176354291149,240477389799,1063635870722311,6626,26511602573753,40234129593222⟩
  | .h2429B => ⟨120164436715100968,283388640121,1063635870722311,6626,26511602573753,40234129593222⟩
def retainedCap : Band → ℕ
  | .h2367 => 163841818704532544
  | .h2430 => 163839264384240038
  | .h2429 => 165605558594776236
  | .h2429B => 0
def highBound : Band → ℕ
  | .h2367 => 274439264148899379

  | .h2430 => 276157458621001894
  | .h2429 => 279756357029353097
  | .h2429B => 121295101706637002
def gradedLoss (b : Band) (e : ℕ) : ℕ :=
  match b with
  | .h2367 => if e=16 then 107856077532044291 else
      if e=17 then 107786612382081432 else (fees b).loss
  | .h2430 => if e=16 then 109152438654258292 else if e=17 then 109029995493639078 else (fees b).loss
  | .h2429 => if e=16 then 110909364763073880 else if e=17 then 110781052727958233 else (fees b).loss
  | .h2429B => (fees b).loss

def gradedRetained (e : ℕ) : ℕ :=
  if e=16 then 163594332406260760 else if e=17 then 163841818704532544 else 159028691991780124

def gradedPrefix (b : Band) (e : ℕ) : ℕ :=
  gradedLoss b e + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
    (fees b).fixedODE+(fees b).content

theorem gradedLoss_le (b : Band) (e : ℕ) : gradedLoss b e ≤ (fees b).loss := by
  by_cases h : e = 16
  · cases b <;> simp [gradedLoss, h, fees]
  by_cases h' : e = 17
  · cases b <;> simp [gradedLoss, h, h', fees]
  · cases b <;> simp [gradedLoss, h, h', fees]

theorem graded_budget (e : ℕ) :
    gradedPrefix .h2367 e+gradedRetained e+1≤273002714226794744:=by
  by_cases h:e=16
  · subst e
    decide
  · by_cases h' : e = 17
    · subst e
      decide
    · simp [gradedPrefix,gradedLoss,gradedRetained,h,h', fees]


def subbank (b : Band) (g : Grade) : Bank :=
  let t:=terminal b
  { t with shape := { t.shape with U:=g.slots } }

abbrev GradeIndex (b:Band):=Fin (grades b).length

def Listed (b : Band) (t : Bank) : Prop :=
  t = terminal b ∨ (∃ s ∈ stages b, t = s.free ∨ t = s.moving) ∨
    ∃ i:GradeIndex b,t=subbank b ((grades b).get i)

abbrev Test (b:Band):=Option (GradeIndex b)

def tested (b : Band) : Test b → Bank
  | none => terminal b
  | some i => subbank b ((grades b).get i)

def threshold (b : Band) : Test b → ℕ
  | none => (grades b).length+1
  | some i => i.val+1

def seedThreshold (b : Band) : Test b → ℕ
  | none => 0
  | some i => ((grades b).get i).seedCap+1

def jointGain (h : ℕ) (s : Shape) (E v : ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g:=(q-j)/E
    let x:=s.m*agreement+j - q*(131071-h)
    let c:=fun a => slots s.U (a*v)
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g*(x - 2*h*(j+g))

def cutoffCount (h r : ℕ) (s : Shape) : ℕ :=
  s.m*agreement - 2*h*r

def rawWidth (h r : ℕ) (s : Shape) (q j : ℕ) : ℕ :=
  cutoffCount h r s+j - q*(131071 - h)

def WidthGuard (h r : ℕ) (s : Shape) : Prop :=
  s.B*(131071-h) < cutoffCount h r s

def gain (h r : ℕ) (s : Shape) (mode : ℕ) : ℕ :=
  triangle s.U*shapeSum s (fun q j => rawWidth h r s q j - mode*(2*h*j))

theorem height_cover {h : ℕ} (lo : 2431 ≤ h) (hi : h ≤ 2695) :
    ∃ b,start b≤h ∧ h≤finish b :=
  ⟨.h2367,lo,hi⟩

theorem accounting (b : Band) :
    (fees b).loss + (fees b).point + (fees b).lowSeed + (fees b).lowJet +
       (fees b).fixedODE+(fees b).content+retainedCap b+1=highBound b := by
  cases b <;> decide +kernel

theorem accounting_stock : highBound .h2367 ≤ 274439264148899379 := by decide

end HighCore82258
