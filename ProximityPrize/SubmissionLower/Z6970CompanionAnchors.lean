import ProximityPrize.SubmissionLower.Z6970CompanionValue

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

def anchors : List Anchor := [⟨0,14,8,5⟩,⟨0,21,6,2⟩,⟨0,17,9,11⟩,⟨0,29,6,10⟩,⟨0,1,10,7⟩,⟨0,25,5,3⟩,⟨0,30,3,4⟩,⟨0,2,9,3⟩,⟨0,10,8,2⟩,⟨0,16,7,2⟩,⟨0,21,10,16⟩,⟨0,48,3,20⟩,⟨0,7,14,21⟩,⟨0,27,4,3⟩,⟨0,32,9,19⟩,⟨0,1,11,11⟩,⟨0,4,9,4⟩,⟨0,6,9,5⟩,⟨0,10,10,11⟩,⟨0,18,7,3⟩,⟨0,19,7,4⟩,⟨0,22,7,7⟩,⟨0,24,5,2⟩,⟨0,33,10,21⟩,⟨2,2,6,5⟩,⟨2,3,9,22⟩,⟨2,14,4,2⟩,⟨2,1,7,11⟩,⟨2,1,11,27⟩,⟨2,1,12,30⟩,⟨2,4,6,7⟩,⟨2,7,5,2⟩,⟨2,9,5,4⟩,⟨2,11,6,12⟩,⟨2,11,13,34⟩,⟨3,1,10,25⟩,⟨3,3,6,7⟩,⟨3,6,5,2⟩,⟨3,13,4,2⟩,⟨3,1,6,5⟩,⟨3,1,9,22⟩,⟨3,1,12,30⟩,⟨3,8,5,4⟩,⟨3,9,6,12⟩,⟨3,13,13,35⟩,⟨4,12,4,2⟩,⟨4,1,9,22⟩,⟨4,1,12,31⟩,⟨4,2,6,7⟩,⟨4,5,5,2⟩,⟨4,7,5,4⟩,⟨4,7,6,11⟩,⟨5,4,5,2⟩,⟨5,1,8,19⟩,⟨5,1,10,27⟩,⟨5,3,6,9⟩,⟨5,5,5,3⟩,⟨5,11,4,2⟩,⟨6,3,5,2⟩,⟨6,1,6,8⟩,⟨6,1,8,20⟩,⟨6,1,10,27⟩,⟨7,7,13,37⟩,⟨7,1,6,9⟩,⟨7,1,9,25⟩,⟨7,1,10,28⟩,⟨7,2,5,2⟩,⟨7,2,13,36⟩,⟨7,3,5,3⟩,⟨8,1,6,11⟩,⟨8,1,8,22⟩,⟨8,1,9,26⟩,⟨8,2,5,3⟩,⟨8,4,11,33⟩,⟨9,1,5,3⟩,⟨10,7,4,2⟩,⟨10,1,5,5⟩,⟨10,1,6,13⟩,⟨10,1,8,24⟩,⟨10,1,9,28⟩,⟨10,6,12,37⟩,⟨11,2,5,7⟩,⟨11,1,8,25⟩,⟨11,1,9,29⟩,⟨11,2,12,37⟩,⟨12,1,5,7⟩,⟨13,1,5,9⟩,⟨13,1,7,22⟩,⟨13,1,9,30⟩,⟨13,3,12,39⟩,⟨14,1,5,5⟩,⟨20,1,3,8⟩,⟨20,1,4,20⟩,⟨20,1,6,35⟩,⟨20,1,9,46⟩]

theorem anchor0 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 5 ≤ f 14 8 :=
  h.2 (⟨0,14,8,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor1 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 2 ≤ f 21 6 :=
  h.2 (⟨0,21,6,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor2 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 11 ≤ f 17 9 :=
  h.2 (⟨0,17,9,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor3 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 10 ≤ f 29 6 :=
  h.2 (⟨0,29,6,10⟩ : Anchor) (by decide +kernel) rfl

theorem anchor4 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 7 ≤ f 1 10 :=
  h.2 (⟨0,1,10,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor5 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 3 ≤ f 25 5 :=
  h.2 (⟨0,25,5,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor6 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 4 ≤ f 30 3 :=
  h.2 (⟨0,30,3,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor7 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 3 ≤ f 2 9 :=
  h.2 (⟨0,2,9,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor8 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 2 ≤ f 10 8 :=
  h.2 (⟨0,10,8,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor9 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 2 ≤ f 16 7 :=
  h.2 (⟨0,16,7,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor10 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 16 ≤ f 21 10 :=
  h.2 (⟨0,21,10,16⟩ : Anchor) (by decide +kernel) rfl

theorem anchor11 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 20 ≤ f 48 3 :=
  h.2 (⟨0,48,3,20⟩ : Anchor) (by decide +kernel) rfl

theorem anchor12 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 21 ≤ f 7 14 :=
  h.2 (⟨0,7,14,21⟩ : Anchor) (by decide +kernel) rfl

theorem anchor13 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 3 ≤ f 27 4 :=
  h.2 (⟨0,27,4,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor14 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 19 ≤ f 32 9 :=
  h.2 (⟨0,32,9,19⟩ : Anchor) (by decide +kernel) rfl

theorem anchor15 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 11 ≤ f 1 11 :=
  h.2 (⟨0,1,11,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor16 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 4 ≤ f 4 9 :=
  h.2 (⟨0,4,9,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor17 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 5 ≤ f 6 9 :=
  h.2 (⟨0,6,9,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor18 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 11 ≤ f 10 10 :=
  h.2 (⟨0,10,10,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor19 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 3 ≤ f 18 7 :=
  h.2 (⟨0,18,7,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor20 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 4 ≤ f 19 7 :=
  h.2 (⟨0,19,7,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor21 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 7 ≤ f 22 7 :=
  h.2 (⟨0,22,7,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor22 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 2 ≤ f 24 5 :=
  h.2 (⟨0,24,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor23 (f : ℕ → ℕ → ℕ) (h : Supports anchors 0 f) : 21 ≤ f 33 10 :=
  h.2 (⟨0,33,10,21⟩ : Anchor) (by decide +kernel) rfl

theorem anchor24 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 5 ≤ f 2 6 :=
  h.2 (⟨2,2,6,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor25 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 22 ≤ f 3 9 :=
  h.2 (⟨2,3,9,22⟩ : Anchor) (by decide +kernel) rfl

theorem anchor26 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 2 ≤ f 14 4 :=
  h.2 (⟨2,14,4,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor27 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 11 ≤ f 1 7 :=
  h.2 (⟨2,1,7,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor28 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 27 ≤ f 1 11 :=
  h.2 (⟨2,1,11,27⟩ : Anchor) (by decide +kernel) rfl

theorem anchor29 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 30 ≤ f 1 12 :=
  h.2 (⟨2,1,12,30⟩ : Anchor) (by decide +kernel) rfl

theorem anchor30 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 7 ≤ f 4 6 :=
  h.2 (⟨2,4,6,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor31 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 2 ≤ f 7 5 :=
  h.2 (⟨2,7,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor32 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 4 ≤ f 9 5 :=
  h.2 (⟨2,9,5,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor33 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 12 ≤ f 11 6 :=
  h.2 (⟨2,11,6,12⟩ : Anchor) (by decide +kernel) rfl

theorem anchor34 (f : ℕ → ℕ → ℕ) (h : Supports anchors 2 f) : 34 ≤ f 11 13 :=
  h.2 (⟨2,11,13,34⟩ : Anchor) (by decide +kernel) rfl

theorem anchor35 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 25 ≤ f 1 10 :=
  h.2 (⟨3,1,10,25⟩ : Anchor) (by decide +kernel) rfl

theorem anchor36 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 7 ≤ f 3 6 :=
  h.2 (⟨3,3,6,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor37 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 2 ≤ f 6 5 :=
  h.2 (⟨3,6,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor38 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 2 ≤ f 13 4 :=
  h.2 (⟨3,13,4,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor39 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 5 ≤ f 1 6 :=
  h.2 (⟨3,1,6,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor40 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 22 ≤ f 1 9 :=
  h.2 (⟨3,1,9,22⟩ : Anchor) (by decide +kernel) rfl

theorem anchor41 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 30 ≤ f 1 12 :=
  h.2 (⟨3,1,12,30⟩ : Anchor) (by decide +kernel) rfl

theorem anchor42 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 4 ≤ f 8 5 :=
  h.2 (⟨3,8,5,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor43 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 12 ≤ f 9 6 :=
  h.2 (⟨3,9,6,12⟩ : Anchor) (by decide +kernel) rfl

theorem anchor44 (f : ℕ → ℕ → ℕ) (h : Supports anchors 3 f) : 35 ≤ f 13 13 :=
  h.2 (⟨3,13,13,35⟩ : Anchor) (by decide +kernel) rfl

theorem anchor45 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 2 ≤ f 12 4 :=
  h.2 (⟨4,12,4,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor46 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 22 ≤ f 1 9 :=
  h.2 (⟨4,1,9,22⟩ : Anchor) (by decide +kernel) rfl

theorem anchor47 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 31 ≤ f 1 12 :=
  h.2 (⟨4,1,12,31⟩ : Anchor) (by decide +kernel) rfl

theorem anchor48 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 7 ≤ f 2 6 :=
  h.2 (⟨4,2,6,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor49 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 2 ≤ f 5 5 :=
  h.2 (⟨4,5,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor50 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 4 ≤ f 7 5 :=
  h.2 (⟨4,7,5,4⟩ : Anchor) (by decide +kernel) rfl

theorem anchor51 (f : ℕ → ℕ → ℕ) (h : Supports anchors 4 f) : 11 ≤ f 7 6 :=
  h.2 (⟨4,7,6,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor52 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 2 ≤ f 4 5 :=
  h.2 (⟨5,4,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor53 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 19 ≤ f 1 8 :=
  h.2 (⟨5,1,8,19⟩ : Anchor) (by decide +kernel) rfl

theorem anchor54 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 27 ≤ f 1 10 :=
  h.2 (⟨5,1,10,27⟩ : Anchor) (by decide +kernel) rfl

theorem anchor55 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 9 ≤ f 3 6 :=
  h.2 (⟨5,3,6,9⟩ : Anchor) (by decide +kernel) rfl

theorem anchor56 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 3 ≤ f 5 5 :=
  h.2 (⟨5,5,5,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor57 (f : ℕ → ℕ → ℕ) (h : Supports anchors 5 f) : 2 ≤ f 11 4 :=
  h.2 (⟨5,11,4,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor58 (f : ℕ → ℕ → ℕ) (h : Supports anchors 6 f) : 2 ≤ f 3 5 :=
  h.2 (⟨6,3,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor59 (f : ℕ → ℕ → ℕ) (h : Supports anchors 6 f) : 8 ≤ f 1 6 :=
  h.2 (⟨6,1,6,8⟩ : Anchor) (by decide +kernel) rfl

theorem anchor60 (f : ℕ → ℕ → ℕ) (h : Supports anchors 6 f) : 20 ≤ f 1 8 :=
  h.2 (⟨6,1,8,20⟩ : Anchor) (by decide +kernel) rfl

theorem anchor61 (f : ℕ → ℕ → ℕ) (h : Supports anchors 6 f) : 27 ≤ f 1 10 :=
  h.2 (⟨6,1,10,27⟩ : Anchor) (by decide +kernel) rfl

theorem anchor62 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 37 ≤ f 7 13 :=
  h.2 (⟨7,7,13,37⟩ : Anchor) (by decide +kernel) rfl

theorem anchor63 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 9 ≤ f 1 6 :=
  h.2 (⟨7,1,6,9⟩ : Anchor) (by decide +kernel) rfl

theorem anchor64 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 25 ≤ f 1 9 :=
  h.2 (⟨7,1,9,25⟩ : Anchor) (by decide +kernel) rfl

theorem anchor65 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 28 ≤ f 1 10 :=
  h.2 (⟨7,1,10,28⟩ : Anchor) (by decide +kernel) rfl

theorem anchor66 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 2 ≤ f 2 5 :=
  h.2 (⟨7,2,5,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor67 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 36 ≤ f 2 13 :=
  h.2 (⟨7,2,13,36⟩ : Anchor) (by decide +kernel) rfl

theorem anchor68 (f : ℕ → ℕ → ℕ) (h : Supports anchors 7 f) : 3 ≤ f 3 5 :=
  h.2 (⟨7,3,5,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor69 (f : ℕ → ℕ → ℕ) (h : Supports anchors 8 f) : 11 ≤ f 1 6 :=
  h.2 (⟨8,1,6,11⟩ : Anchor) (by decide +kernel) rfl

theorem anchor70 (f : ℕ → ℕ → ℕ) (h : Supports anchors 8 f) : 22 ≤ f 1 8 :=
  h.2 (⟨8,1,8,22⟩ : Anchor) (by decide +kernel) rfl

theorem anchor71 (f : ℕ → ℕ → ℕ) (h : Supports anchors 8 f) : 26 ≤ f 1 9 :=
  h.2 (⟨8,1,9,26⟩ : Anchor) (by decide +kernel) rfl

theorem anchor72 (f : ℕ → ℕ → ℕ) (h : Supports anchors 8 f) : 3 ≤ f 2 5 :=
  h.2 (⟨8,2,5,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor73 (f : ℕ → ℕ → ℕ) (h : Supports anchors 8 f) : 33 ≤ f 4 11 :=
  h.2 (⟨8,4,11,33⟩ : Anchor) (by decide +kernel) rfl

theorem anchor74 (f : ℕ → ℕ → ℕ) (h : Supports anchors 9 f) : 3 ≤ f 1 5 :=
  h.2 (⟨9,1,5,3⟩ : Anchor) (by decide +kernel) rfl

theorem anchor75 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 2 ≤ f 7 4 :=
  h.2 (⟨10,7,4,2⟩ : Anchor) (by decide +kernel) rfl

theorem anchor76 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 5 ≤ f 1 5 :=
  h.2 (⟨10,1,5,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor77 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 13 ≤ f 1 6 :=
  h.2 (⟨10,1,6,13⟩ : Anchor) (by decide +kernel) rfl

theorem anchor78 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 24 ≤ f 1 8 :=
  h.2 (⟨10,1,8,24⟩ : Anchor) (by decide +kernel) rfl

theorem anchor79 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 28 ≤ f 1 9 :=
  h.2 (⟨10,1,9,28⟩ : Anchor) (by decide +kernel) rfl

theorem anchor80 (f : ℕ → ℕ → ℕ) (h : Supports anchors 10 f) : 37 ≤ f 6 12 :=
  h.2 (⟨10,6,12,37⟩ : Anchor) (by decide +kernel) rfl

theorem anchor81 (f : ℕ → ℕ → ℕ) (h : Supports anchors 11 f) : 7 ≤ f 2 5 :=
  h.2 (⟨11,2,5,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor82 (f : ℕ → ℕ → ℕ) (h : Supports anchors 11 f) : 25 ≤ f 1 8 :=
  h.2 (⟨11,1,8,25⟩ : Anchor) (by decide +kernel) rfl

theorem anchor83 (f : ℕ → ℕ → ℕ) (h : Supports anchors 11 f) : 29 ≤ f 1 9 :=
  h.2 (⟨11,1,9,29⟩ : Anchor) (by decide +kernel) rfl

theorem anchor84 (f : ℕ → ℕ → ℕ) (h : Supports anchors 11 f) : 37 ≤ f 2 12 :=
  h.2 (⟨11,2,12,37⟩ : Anchor) (by decide +kernel) rfl

theorem anchor85 (f : ℕ → ℕ → ℕ) (h : Supports anchors 12 f) : 7 ≤ f 1 5 :=
  h.2 (⟨12,1,5,7⟩ : Anchor) (by decide +kernel) rfl

theorem anchor86 (f : ℕ → ℕ → ℕ) (h : Supports anchors 13 f) : 9 ≤ f 1 5 :=
  h.2 (⟨13,1,5,9⟩ : Anchor) (by decide +kernel) rfl

theorem anchor87 (f : ℕ → ℕ → ℕ) (h : Supports anchors 13 f) : 22 ≤ f 1 7 :=
  h.2 (⟨13,1,7,22⟩ : Anchor) (by decide +kernel) rfl

theorem anchor88 (f : ℕ → ℕ → ℕ) (h : Supports anchors 13 f) : 30 ≤ f 1 9 :=
  h.2 (⟨13,1,9,30⟩ : Anchor) (by decide +kernel) rfl

theorem anchor89 (f : ℕ → ℕ → ℕ) (h : Supports anchors 13 f) : 39 ≤ f 3 12 :=
  h.2 (⟨13,3,12,39⟩ : Anchor) (by decide +kernel) rfl

theorem anchor90 (f : ℕ → ℕ → ℕ) (h : Supports anchors 14 f) : 5 ≤ f 1 5 :=
  h.2 (⟨14,1,5,5⟩ : Anchor) (by decide +kernel) rfl

theorem anchor91 (f : ℕ → ℕ → ℕ) (h : Supports anchors 20 f) : 8 ≤ f 1 3 :=
  h.2 (⟨20,1,3,8⟩ : Anchor) (by decide +kernel) rfl

theorem anchor92 (f : ℕ → ℕ → ℕ) (h : Supports anchors 20 f) : 20 ≤ f 1 4 :=
  h.2 (⟨20,1,4,20⟩ : Anchor) (by decide +kernel) rfl

theorem anchor93 (f : ℕ → ℕ → ℕ) (h : Supports anchors 20 f) : 35 ≤ f 1 6 :=
  h.2 (⟨20,1,6,35⟩ : Anchor) (by decide +kernel) rfl

theorem anchor94 (f : ℕ → ℕ → ℕ) (h : Supports anchors 20 f) : 46 ≤ f 1 9 :=
  h.2 (⟨20,1,9,46⟩ : Anchor) (by decide +kernel) rfl

end Height2307Companion
