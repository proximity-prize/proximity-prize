import ProximityPrize.SubmissionLower.Koala6844ReceiptsSource

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

structure FlagIncrements where
  total : Nat
  middle : Nat
  slope : Nat
  deriving DecidableEq, Repr

def Flag.increments (f : Flag) : FlagIncrements :=
  ⟨f.t - f.y, f.y - f.r, f.r⟩

def FlagIncrements.axis (f : FlagIncrements) (i : Nat) : Nat :=
  if i = 0 then f.total else if i = 1 then f.middle else f.slope

def FlagIncrements.map (f : Nat → Nat) : FlagIncrements :=
  ⟨f 0, f 1, f 2⟩

def FlagIncrements.all (f : FlagIncrements) (p : Nat → Nat → Bool) : Bool :=
  p 0 f.total && p 1 f.middle && p 2 f.slope

def axisFlag (j : Nat) : FlagIncrements :=
  if j = 0 then ⟨1, 0, 0⟩ else if j = 1 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩

def mixedRate (i : Nat) (f g : FlagIncrements) : Nat :=
  let constant := f.slope * g.slope
  let middleSlope := f.middle * g.slope + g.middle * f.slope
  let totalSlope := f.total * g.slope + g.total * f.slope
  if i = 0 then constant + middleSlope
  else if i = 1 then constant + middleSlope + totalSlope
  else constant + middleSlope + totalSlope + f.middle * g.middle +
    f.total * g.middle + g.total * f.middle

def dot (a b : FlagIncrements) : Nat :=
  a.total * b.total + a.middle * b.middle + a.slope * b.slope

def mixed (f g h : Flag) : Nat :=
  dot f.increments (FlagIncrements.map (fun i => mixedRate i g.increments h.increments))

def errorsAllowed : Nat := nodes - agreements
def pencilLimit : Nat := errorsAllowed + 1
def agreementGap : Nat := agreements - degree

def padFlag (f : Flag) (extra : Nat := 0) : Flag :=
  let r := max 3 f.r
  let y := max f.y (r + 2)
  ⟨r, y, max f.t (y + extra)⟩

def wellOrdered (f : Flag) : Bool :=
  decide (1 ≤ f.r ∧ f.r ≤ f.y ∧ f.y ≤ f.t)

def earlyCut (f : Flag) : FlagIncrements :=
  ⟨2 * (degree + 1) * (f.t - f.y),
    1 + 2 * (degree + 1) * (f.y - f.r), 2 * (degree + 1) * (f.r - 1)⟩

def normalCut (f : Flag) : FlagIncrements :=
  ⟨(degree + 3) * (f.t - f.y),
    (degree + 3) * (f.y - f.r) - (degree + 1),
    (degree + 3) * (f.r - 1)⟩

def rawMovingCut (f : Flag) : FlagIncrements :=
  ⟨(degree + 3) * (f.t - f.y), (degree + 3) * (f.y - f.r),
    (degree + 3) * f.r - 1⟩

def rawIdentity (f : Flag) : FlagIncrements :=
  ⟨393219 + 262146 * (f.r - 2), 786438 + 524292 * (f.r - 2),
    1048586 + 262146 * (f.t - f.y) + 524292 * (f.y - f.r - 1)
      + 524292 * (f.r - 2)⟩

def rawGeometryGate (f : Flag) : Bool :=
  let g := padFlag f
  let early := earlyCut g
  let normal := normalCut g
  wellOrdered f && decide
    (2 * g.t * (g.t + 1) < prime ∧
     g.r * early.middle + g.y * early.slope < prime ∧
     pencilLimit ≤ normal.middle ∧
     g.r * ((2 * (g.y - g.r) - 1) * degree + 1) + g.y * (2 * g.r - 1) * degree < prime)

def rawGeometryRates (f : Flag) : Option FlagIncrements :=
  let g := padFlag f
  let moving : FlagIncrements := ⟨g.t - g.y, g.y - g.r, g.r + 1⟩
  let rates := FlagIncrements.map fun i =>
    mixedRate i (earlyCut g) (normalCut g) + 65539 * mixedRate i moving (rawMovingCut g)
  if rawGeometryGate f &&
      (rawIdentity g).all (fun i cost => decide
        ((nodes - degree) * pencilLimit * cost ≤ agreementGap * rates.axis i)) then
    some rates
  else none

def goodGraph (f : Flag) : Bool :=
  let early := earlyCut f
  decide
    (f.t ≤ 9678 ∧ 2 * f.t * (f.t + 1) < prime ∧
     f.r * early.middle + f.y * early.slope < prime ∧
     f.r * ((2 * (f.y - f.r) - 1) * degree + 1) +
       f.y * (2 * f.r - 1) * degree < prime ∧
     pencilLimit ≤ (normalCut f).middle)

structure Rates where
  numerator : FlagIncrements
  denominator : Nat
  deriving Repr

def Rates.bill (rates : Rates) (f : Flag) : Nat :=
  (dot f.increments rates.numerator + rates.denominator - 1) / rates.denominator

def geometryScale : Nat :=
  agreements * agreementGap

def shortRates (f : Flag) : Rates :=
  match rawGeometryRates f with
  | some rate => ⟨rate, 1⟩
  | none =>
    let linear := 2 * nodes * degree * agreementGap
    let eta := (nodes - degree) * agreements
    let direction : Flag := ⟨linear * (f.r - 1), linear * (f.y - 1) + eta,
      linear * (f.t - 1) + eta⟩
    let later : Flag := ⟨direction.r, direction.y, direction.t + pencilLimit * geometryScale⟩
    ⟨FlagIncrements.map (fun i => mixedRate i direction.increments later.increments),
      geometryScale * geometryScale⟩

def graphScale : Nat :=
  Nat.lcm geometryScale 1081080

def graphDirection (f : Flag) : FlagIncrements :=
  let lam := graphScale / agreements * nodes * degree
  let rho := graphScale / agreementGap * (nodes - degree)
  ⟨2 * lam * (f.t - f.y) + pencilLimit * graphScale,
    2 * lam * (f.y - f.r) + rho, 2 * lam * (f.r - 1)⟩

def graphNormal (g : Flag) : FlagIncrements :=
  ⟨131074 * (g.t - g.y), 131074 * (g.y - g.r - 2) + 131076,
    131074 * (g.r - 3) + 262148⟩

def graphRaw (g : Flag) : FlagIncrements :=
  ⟨131073 * (g.t - g.y), 131073 * (g.y - g.r - 2) + 262146,
    131073 * (g.r - 3) + 393218⟩

def graphFirstCut (g : Flag) (j : Nat) : FlagIncrements :=
  let a := g.r - 3
  let b := g.y - g.r - 2
  let c := g.t - g.y
  let zRate := 262144 * c
  let valueRate := 262144 * b
  let cut : FlagIncrements :=
    if a = 0 then
      if j = 0 then ⟨zRate, valueRate, 3⟩ else if j = 1 then ⟨zRate, valueRate + 393216, 3⟩
      else ⟨zRate, valueRate + 131072, 262147⟩
    else
      let R := 262144 * (a - 1)
      if j = 0 then ⟨zRate, valueRate + 131072, R + 131075⟩
      else if j = 1 then ⟨zRate, valueRate + 524288, R + 131075⟩
      else ⟨zRate, valueRate + 131072, R + 524291⟩
  cut

def graphBasis (g : Flag) : FlagIncrements :=
  let norm := graphNormal g
  FlagIncrements.map (fun i =>
    (norm.total * mixedRate i (graphFirstCut g 0) (axisFlag 0) +
      norm.middle * mixedRate i (graphFirstCut g 1) (axisFlag 1) +
      norm.slope * mixedRate i (graphFirstCut g 2) (axisFlag 2)) * (graphScale / 3))

def graphIdentity (g : Flag) : FlagIncrements :=
  let a := g.r - 3
  let b := g.y - g.r - 2
  let c := g.t - g.y
  let factor := graphScale / agreementGap * (nodes - degree) * pencilLimit
  ⟨factor * (655365 + 262146 * a), factor * (1310730 + 524292 * a),
    factor * (2097170 + 524292 * a + 524292 * b + 262146 * c)⟩

def germDegreeY (f g : Flag) : Nat :=
  g.r * f.y + f.r * g.y - f.r * g.r

def germDegreeT (f g : Flag) : Nat :=
  g.r * f.t + f.r * g.t - f.r * g.r

def germPrice (f g : Flag) : Nat :=
  germDegreeT f g + prime * germDegreeY f g


def helperFlag (g : Flag) (src : SourceShape) : Flag :=
  let f := src.carrierFlag
  ⟨f.r + src.s * (g.r - 1), f.y + src.s * (g.y - 1), f.t + src.s * (g.t - 1)⟩

def pairGate (f g : Flag) : Bool :=
  decide (f.r * g.t + f.t * g.r < prime ∧
    f.y * g.t + f.t * g.y < prime ∧ f.y * g.r + f.r * g.y < prime)

def graphPairRates (partner : Flag) (direction : FlagIncrements) : FlagIncrements :=
  FlagIncrements.map fun i => mixedRate i partner.increments direction

def SourceShape.graphIncrement (src : SourceShape) : FlagIncrements :=
  let f := src.carrierFlag
  ⟨f.t - f.y, f.y - f.r + src.n0, f.r - 2 * (src.n0 - src.k - 1)⟩

structure GraphCharge where
  move : FlagIncrements
  lead : FlagIncrements
  helper : FlagIncrements

def graphCharge (_f g : Flag) (src : SourceShape) (j : Nat) : Option GraphCharge :=
  let right := src.carrierFlag
  let helper := helperFlag g src
  if pairGate g right && pairGate g helper then
    let normal := (graphNormal g).axis j
    let raw := (graphRaw g).axis j
    let weight := (524288 * normal + 3 * 65539 * raw) * (graphScale / 3)
    let move := FlagIncrements.map fun i =>
      weight / (src.k + 1) * mixedRate i (axisFlag j) src.graphIncrement
    let dir := graphDirection g
    some ⟨move, graphPairRates right dir, graphPairRates helper dir⟩
  else none

structure Sources where
  z : SourceShape
  yz : SourceShape
  all : SourceShape
  deriving Repr

def Sources.totalCap (sources : Sources) : Nat :=
  max (sources.z.L + sources.z.q) (max (sources.yz.L + sources.yz.q) (sources.all.L + sources.all.q))

def longRates (f : Flag) (sources : Sources) : Option Rates := do
  let g := padFlag f 2
  if !goodGraph g then none else
    let axis0 ← graphCharge f g sources.z 0
    let axis1 ← graphCharge f g sources.yz 1
    let axis2 ← graphCharge f g sources.all 2
    let basis := graphBasis g
    let identity := graphIdentity g
    let numer := FlagIncrements.map fun i =>
      let graph := axis0.lead.axis i + axis1.lead.axis i + axis2.lead.axis i +
        max (identity.axis i) (basis.axis i + axis0.move.axis i + axis1.move.axis i + axis2.move.axis i)
      max graph (max (axis0.helper.axis i) (max (axis1.helper.axis i) (axis2.helper.axis i)))
    if numer.total ≤ numer.middle ∧ numer.middle ≤ numer.slope then some ⟨numer, graphScale⟩
    else none

def shortSplitCharge (f : Flag) (left right : Rates) (r y otherR otherY t : Nat) : Nat :=
  left.bill ⟨r, y, t⟩ + right.bill ⟨otherR, otherY, f.t - t⟩

def splitCharge (f : Flag) (src : Sources) (L r y best : Nat) : Option Nat := do
  let otherY := f.y - y
  let otherR := min otherY (f.r - r)
  let short := shortRates ⟨r, y, L⟩
  let upper := min L (f.t - otherY)
  let best :=
    if y ≤ upper then
      let other := shortRates ⟨otherR, otherY, L⟩
      max best (max (shortSplitCharge f short other r y otherR otherY y)
        (shortSplitCharge f short other r y otherR otherY upper))
    else best
  let upper := f.t - max (L + 1) otherY
  if y ≤ upper then
    let other ← longRates ⟨otherR, otherY, f.t⟩ src
    return max best (max (shortSplitCharge f short other r y otherR otherY y)
      (shortSplitCharge f short other r y otherR otherY upper))
  else return best

def terminalPrice (f : Flag) (src : Sources) : Option Nat := do
  let L := src.totalCap
  if !wellOrdered f || !(f.y ≤ L ∧ L < f.t ∧ L + f.y ≤ f.t) then none else
    let long ← longRates f src
    let short := shortRates ⟨f.r, f.y, L⟩
    let base := max (long.bill f) (short.bill ⟨f.r, f.y, L⟩)
    (List.range (f.r - 1)).foldlM (fun best r =>
      let r := r + 1
      (List.range (f.y - r)).foldlM (fun acc dy => splitCharge f src L r (r + dy) acc) best) base

def scaledDirection (f : Flag) : Flag :=
  let lam := nodes * degree * agreementGap
  let eta := (nodes - degree) * agreements
  ⟨2 * lam * (f.r - 1), 2 * lam * (f.y - 1) + eta, 2 * lam * (f.t - 1) + eta⟩

def scaledLater (f : Flag) : Flag :=
  let g := scaledDirection f
  ⟨g.r, g.y, g.t + pencilLimit * geometryScale⟩

def shortenedPairPrice (f g : Flag) : Nat :=
  mixed f g (scaledLater f) / geometryScale


def primaryWeight : Nat :=
  601 * agreements + 744 * poleWidth

def intrinsicPrice (f : Flag) : Nat :=
  let one := mixed f (scaledDirection f) (scaledLater f) / (geometryScale * geometryScale)
  let tail : Flag := ⟨2 * (degree + 1) * (f.r - 1),
    1 + 2 * (degree + 1) * (f.y - 1), 1 + 2 * (degree + 1) * (f.t - 1)⟩
  let tailNext : Flag := ⟨tail.r + 2 * (f.r - 1), tail.y + 2 * (f.y - 1),
    tail.t + 2 * (f.t - 1)⟩
  let surface := (nodes - degree) * pencilLimit * (4 * degree * f.r * f.t + f.r) / agreementGap
  let curve := (nodes - degree) * (4 * primaryWeight * f.r * f.t + f.t) / agreementGap
  let pencil := pencilLimit * mixed f tail ⟨0, 0, 1⟩
  let generic := min one <| min (shortenedPairPrice f tail + surface)
    (mixed f tail tailNext + surface + curve + pencil)
  match rawGeometryRates f with
  | none => generic
  | some raw => min generic (dot f.increments raw)

def terminalBudget : Nat := 260000000000000000

inductive EndpointReceipt (f : Flag) (price : Nat) : Type
  | intrinsic (bound : intrinsicPrice f = price)
      (fits : price ≤ terminalBudget)
  | terminal (sources : Sources) (bound : terminalPrice f sources = some price)
      (fits : price ≤ terminalBudget)

structure CertifiedEndpoint where
  flag : Flag
  price : Nat
  receipt : EndpointReceipt flag price

end ProximityPrize.SubmissionLower.Koala6844Receipts
