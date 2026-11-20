import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

def fastChannelCount (T YS S : Nat) : Nat :=
  let M := min T YS
  let B := min S M
  let E := M-B
  (B+1)*((E+1)*(T+1)-chooseTwo (E+1))-(E+1)*chooseTwo (B+1) +
    (T+1-M)*chooseTwo (B+1)+chooseThree (B+1)

def fastPowerBandBudget (width dt dy dr T YS R : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => width * fastChannelCount T YS R +
      fastPowerBandBudget width dt dy dr (T-dt) (YS-dy) (R-dr) k


def chooseFour (n : Nat) : Nat :=
  n * (n - 1) * (n - 2) * (n - 3) / 24

def cubicIntervalSum (f : Nat → Int) (low high : Nat) : Int :=
  let n := high - low
  if n = 0 then 0 else
  let a := f low
  let first := if 2 ≤ n then
    let b := f (low + 1)
    (chooseTwo n : Int) * (b - a)
    else 0
  let second := if 3 ≤ n then
    let b := f (low + 1)
    let c := f (low + 2)
    (chooseThree n : Int) * (c - 2 * b + a)
    else 0
  let third := if 4 ≤ n then
    let b := f (low + 1)
    let c := f (low + 2)
    let d := f (low + 3)
    (chooseFour n : Int) * (d - 3 * c + 3 * b - a)
    else 0
  (n : Int) * a + first + second + third

structure FirstJetShape where
  m : Nat
  L : Nat
  s : Nat
  q : Nat
  deriving DecidableEq, Repr

def primaryShape : FirstJetShape := ⟨601, 43009, 185, 745⟩
def firstRoomShape : FirstJetShape := ⟨2000, 1000000, 600, 2400⟩
def secondRoomShape : FirstJetShape := ⟨2000, 204634, 600, 2495⟩
def firstAdaptiveShape : FirstJetShape := ⟨2000, 200000, 600, 2400⟩
def secondAdaptiveShape : FirstJetShape := ⟨60000, 3600000, 18480, 78816⟩

def firstRoomCut : Nat := 146894
def secondRoomCut : Nat := 120186

def flowWidth : Nat := 2 * poleWidth

def firstJetCutoff (shape : FirstJetShape) (room : Nat) : Nat :=
  shape.m * agreements - room

def firstJetFlag (f : FirstJetShape) (room : Nat) : Flag :=
  ⟨f.s, (firstJetCutoff f room + f.s - 1) / degree, f.L + f.q⟩


def firstJetAffineColumns (cut slope : Nat) (constant : Bool) : Int :=
  if cut = 0 then 0 else
    let cap := (cut - 1) / degree
    let turn := degree - (cut - 1) % degree
    let begin := min turn (min (slope + 1) (cap + 1))
    let finish := min slope (cap + 1) + 1
    let row := fun (u j : Nat) =>
      let first := chooseTwo (u + 1) - chooseTwo j
      let second := squares (u + 1) - squares j
      let count := ((u - j + 1) : Int) * (cut + j : Nat) - (degree : Int) * first
      let moment := (cut + j : Nat) * (first : Int) - (degree : Int) * second
      if constant then count - moment else count
    cubicIntervalSum (row cap) 0 begin +
      cubicIntervalSum (row (cap + 1)) turn finish

def firstJetRankTwelve (m s L : Nat) : Int :=
  let k := min s (m / 2)
  let p0 : Int := (m + 1) * (s + 1)
  let p1 : Int := -((m + 2 * s + 3 : Nat) : Int)
  let c : Int := 2 * (L : Int) + 2 - m - s
  let base : Int := (s + 1) * (m : Int) * (m + 1) *
    (6 * ((L + 1 : Nat) : Int) - 2 * ((m - 1 : Nat) : Int) - 3 * s)
  let removed : Int :=
    6 * p0 * c * k + 3 * (p0 + p1 * c) * k * (k + 1 : Nat) +
    (p1 + 2 * c) * k * (k + 1 : Nat) * (2 * k + 1 : Nat) + 3 * k * k * (k + 1 : Nat)^2
  base - removed

def firstJetRankSlopeTwelve (m s : Nat) : Int :=
  firstJetRankTwelve m s 1 - firstJetRankTwelve m s 0

def firstJetAuxContribution (shape : FirstJetShape) (room j : Nat) : Int :=
  let cut := firstJetCutoff shape room
  12 * firstJetAffineColumns (cut - (j + 1) * (degree + poleWidth)) shape.s false -
    if j + 1 < shape.m then (nodes : Int) * firstJetRankSlopeTwelve (shape.m - (j + 1)) shape.s
    else 0

def firstJetGapTwelve (shape : FirstJetShape) (room : Nat) : Int :=
  let cut := firstJetCutoff shape room
  12 * (firstJetAffineColumns cut shape.s false * shape.L + firstJetAffineColumns cut shape.s true) -
    (nodes : Int) * firstJetRankTwelve shape.m shape.s shape.L +
    ((List.range shape.q).map (firstJetAuxContribution shape room)).sum

def firstJetGap (shape : FirstJetShape) (room : Nat) : Nat :=
  (firstJetGapTwelve shape room / 12).toNat

def firstAdaptiveGap : Nat := 35242887168131852
def secondAdaptiveGap : Nat := 22546934432454279662090

def remainingAfterRoom (old : Flag) (source : FirstJetShape) (room : Nat) : Flag :=
  let g := firstJetFlag source room
  let n := room / flowWidth + 1
  ⟨min old.r (g.r / n), min old.y (g.y / n), min old.t (g.t / n)⟩

def roomPartnerFlag (source : FirstJetShape) (room : Nat) : Flag :=
  let f := firstJetFlag source room
  ⟨f.r, f.y, f.t + room / flowWidth⟩

def primaryFlag : Flag := firstJetFlag primaryShape 0
def firstResidualFlag : Flag := remainingAfterRoom primaryFlag firstRoomShape firstRoomCut
def afterRooms : Flag := remainingAfterRoom firstResidualFlag secondRoomShape secondRoomCut

theorem afterRooms_eq : afterRooms = ⟨50, 230, 20712⟩ := by decide +kernel





def bandFuel (f g : Flag) : Nat :=
  min (f.r / g.r) (min (f.y / g.y) (f.t / g.t))

def bandCovers (source target : Flag) (gap : Nat) : Bool :=
  decide (fastPowerBandBudget flowWidth target.t target.y target.r
    (source.t-target.t) (source.y-target.y) (source.r-target.r)
    (bandFuel source target) < gap)


def firstAdaptiveFlag : Flag := firstJetFlag firstAdaptiveShape 0
def secondAdaptiveFlag : Flag := firstJetFlag secondAdaptiveShape 0






def adaptivePartnerFlag (source : Flag) : Flag :=
  ⟨source.r, source.y, source.t + source.r⟩









end ProximityPrize.SubmissionLower.Koala6844Receipts
