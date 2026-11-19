/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
/- Derived from Lucieno (PR 618), and BitWonka (PR 581) for additional interpolation profiles.
   New 68.32 source parameters, adaptive schedule, cell assignments and integer receipts. Apache-2.0. -/
import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.K6833Residual

open RCN095

structure Envelope where
  slope : ℕ
  middle : ℕ
  total : ℕ
  deriving DecidableEq

def Envelope.flag (f : Envelope) : FlagDegree :=
  ⟨f.total - f.middle, f.middle - f.slope, f.slope⟩

def Envelope.pad (f : Envelope) (tailRoom : ℕ) : Envelope :=
  let r := max 3 f.slope
  let y := max f.middle (r + 2)
  ⟨r, y, max f.total (y + tailRoom)⟩

structure JetProfile where
  order : ℕ
  secondCap : ℕ
  slopeCap : ℕ
  middleCap : ℕ
  totalCap : ℕ
  derivativeOrder : ℕ
  minimumOrder : ℕ
  deriving DecidableEq

private def n : ℕ := 262144
private def w : ℕ := 131071
private def agreement : ℕ := 181068
private def fieldPrime : ℕ := 2130706433
def pencilBudget : ℕ := n - agreement + 1
private def agreementGap : ℕ := agreement - w
private def scale : ℕ := 62736297596280

def residualPriceScale : ℕ := scale

def unit (j : Fin 3) : FlagDegree :=
  ![⟨1,0,0⟩, ⟨0,1,0⟩, ⟨0,0,1⟩] j

def byAxis (f : FlagDegree) (j : Fin 3) : ℕ :=
  ![f.zOnly, f.yz, f.all] j

def shortenedDirection (f : Envelope) (extraSeed : ℕ) : FlagDegree :=
  let slopeScale := (scale / agreement) * n * w
  let nodeScale := (scale / agreementGap) * (n - w)
  ⟨2*slopeScale*(f.total-f.middle) + extraSeed,
    2*slopeScale*(f.middle-f.slope) + nodeScale,
    2*slopeScale*(f.slope-1)⟩

def pairPrice (left right geometry : Envelope) : ℕ :=
  flagMixed left.flag right.flag (shortenedDirection geometry (pencilBudget * scale)) / scale

def firstTail (f : Envelope) : FlagDegree :=
  ⟨2*(w+1)*(f.total-f.middle),
    1+2*(w+1)*(f.middle-f.slope), 2*(w+1)*(f.slope-1)⟩

structure TailCorrections where
  normal : ℕ
  moving : ℕ
  cusp : ℕ
  incumbentOrdinary : Bool

def TailCorrections.original : TailCorrections := ⟨0,0,0,true⟩

def normalTail (shift : ℕ) (f : Envelope) : FlagDegree :=
  ⟨(w+3)*(f.total-f.middle),
    (w+3)*(f.middle-f.slope)-(w+1)+shift,
    (w+3)*(f.slope-1)-shift⟩

def movingFiber (f : Envelope) : FlagDegree :=
  ⟨f.total-f.middle, f.middle-f.slope, f.slope+1⟩

def rawMovingTail (shift : ℕ) (f : Envelope) : FlagDegree :=
  ⟨(w+2)*(f.total-f.middle),
    (w+2)*(f.middle-f.slope)+shift,
    (w+2)*f.slope-1-shift⟩

def ordinaryMovingTail (f : Envelope) : FlagDegree :=
  ⟨(w+3)*(f.total-f.middle), (w+3)*(f.middle-f.slope), (w+3)*f.slope-1⟩

def rawChargeWithCorrections (cuts : TailCorrections) (support : Envelope) (left : FlagDegree) : ℕ :=
  flagMixed left (firstTail support) (normalTail cuts.normal support) +
    65539 * flagMixed left (movingFiber support)
      (if cuts.incumbentOrdinary then ordinaryMovingTail support else rawMovingTail cuts.moving support)

def identityRaw (f : Envelope) : FlagDegree :=
  ⟨393219+262146*(f.slope-2),
    786438+524292*(f.slope-2),
    1048586+262146*(f.total-f.middle)+
      524292*(f.middle-f.slope-1)+524292*(f.slope-2)⟩

def identityGraph (f : Envelope) : FlagDegree :=
  ⟨655365+262146*(f.slope-3),
    1310730+524292*(f.slope-3),
    2097170+524292*(f.slope-3)+524292*(f.middle-f.slope-2)+262146*(f.total-f.middle)⟩

private def characteristicGates (cuts : TailCorrections) (f : Envelope) : Bool :=
  let r := f.slope
  let y := f.middle
  let t := f.total
  let v := y-r
  decide (2*t*(t+1) < fieldPrime ∧
    r*(1+2*(w+1)*v) + y*(2*(w+1)*(r-1)) < fieldPrime ∧
    r*((2*v-1)*w+1) + y*((2*r-1)*w) < fieldPrime ∧
    pencilBudget ≤ (normalTail cuts.normal f).yz)

def rawGatesWithCorrections (cuts : TailCorrections) (support : Envelope) : Bool :=
  characteristicGates cuts support &&
    (List.finRange 3).all (fun j =>
      decide ((n-w)*pencilBudget*byAxis (identityRaw support) j ≤
        agreementGap * rawChargeWithCorrections cuts support (unit j)))

def cusp (maxShift : ℕ) (f : Envelope) (j : Fin 3) : FlagDegree :=
  let r := f.slope
  let v := f.middle-r
  let z := f.total-f.middle
  let old := (![⟨2*z, 2*v-3-(7-2*r), 2*r-7⟩,
    ⟨2*z, 2*v-(7-2*r), 2*r-7⟩, ⟨2*z,2*v-3,2*r-4⟩] : Fin 3 → FlagDegree) j
  let shift := min maxShift old.all
  ⟨old.zOnly, old.yz+shift, old.all-shift⟩

def weightedCusp (shift : ℕ) (f : Envelope) (j : Fin 3) : FlagDegree :=
  (w+1) • cusp shift f j + 3 • unit 2

def graphFixed (cuts : TailCorrections) (support : Envelope) (u : FlagDegree) : ℕ :=
  ((List.finRange 3).map fun j =>
    byAxis (normalTail cuts.normal support) j *
      flagMixed u (weightedCusp cuts.cusp support j) (unit j)).sum *
    (scale / 3)

def JetProfile.leading (s : JetProfile) : Envelope :=
  ⟨s.secondCap, s.middleCap, s.totalCap⟩

def JetProfile.helper (s : JetProfile) (support : Envelope) : Envelope :=
  ⟨s.secondCap + s.slopeCap*(support.slope-1),
    s.middleCap + s.slopeCap*(support.middle-1),
    s.totalCap + s.slopeCap*(support.total-1)⟩

def JetProfile.moving (s : JetProfile) : FlagDegree :=
  ⟨s.totalCap-s.middleCap,
    s.middleCap-s.secondCap+s.minimumOrder,
    s.secondCap-2*(s.minimumOrder-s.derivativeOrder-1)⟩

private def pairGate (f g : Envelope) : Bool :=
  decide (f.slope*g.total+f.total*g.slope < fieldPrime ∧
    f.middle*g.total+f.total*g.middle < fieldPrime ∧
    f.middle*g.slope+f.slope*g.middle < fieldPrime)

private def JetProfile.shapeGate (s : JetProfile) : Bool :=
  decide (2*s.slopeCap ≤ s.secondCap ∧ s.secondCap ≤ s.middleCap ∧
    s.middleCap ≤ s.totalCap ∧
    s.derivativeOrder ≤ s.slopeCap ∧ s.slopeCap < s.order ∧
    s.derivativeOrder+1 ≤ s.minimumOrder ∧
    2*(s.minimumOrder-s.derivativeOrder-1) ≤ s.secondCap ∧
    s.slopeCap < fieldPrime ∧ s.secondCap ≤ s.order ∧
    s.order+s.slopeCap ≤ s.middleCap ∧ s.order+s.secondCap+s.slopeCap ≤ s.totalCap ∧
    scale % (3*(s.derivativeOrder+1)) = 0)

def jetSourceCap (cfg : Fin 3 → JetProfile) : ℕ :=
  max (cfg 0).totalCap (max (cfg 1).totalCap (cfg 2).totalCap)

def jetGatesWithCorrections (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) : Bool :=
  let support := f.pad 2
  let short := (⟨f.slope, f.middle, jetSourceCap cfg⟩ : Envelope).pad 0
  characteristicGates cuts support && decide (jetSourceCap cfg < f.total) &&
    rawGatesWithCorrections cuts short && (List.finRange 3).all (fun j =>
      (cfg j).shapeGate && pairGate support (cfg j).leading &&
        pairGate support ((cfg j).helper support))

def movingCharge (cuts : TailCorrections) (support : Envelope) (s : JetProfile) (u : FlagDegree) (j : Fin 3) : ℕ :=
  (((4*(w+1)*byAxis (normalTail cuts.normal support) j +
    3*65539*byAxis (rawMovingTail cuts.moving support) j) * (scale / 3)) /
      (s.derivativeOrder+1)) * flagMixed u (unit j) s.moving

def jetGraphNumerator (cuts : TailCorrections) (support : Envelope)
    (cfg : Fin 3 → JetProfile) (left : FlagDegree) : ℕ :=
  graphFixed cuts support left +
    ((List.finRange 3).map fun j => movingCharge cuts support (cfg j) left j).sum

def jetChargeAxisWithCorrections (cuts : TailCorrections) (f : Envelope)
    (cfg : Fin 3 → JetProfile) (i : Fin 3) : ℕ :=
  let support := f.pad 2
  let short := (⟨f.slope, f.middle, jetSourceCap cfg⟩ : Envelope).pad 0
  let direction := shortenedDirection f (pencilBudget * scale)
  let u := unit i
  let lead := ((List.finRange 3).map (fun j => flagMixed u (cfg j).leading.flag direction)).sum
  let identity := (scale / agreementGap) * (n-w) * pencilBudget * byAxis (identityGraph support) i
  let helper := ((List.finRange 3).map fun j =>
    flagMixed u ((cfg j).helper support).flag direction).foldl max 0
  max (rawChargeWithCorrections cuts short u * scale)
    (max (lead + max (jetGraphNumerator cuts support cfg u) identity) helper)

def jetPriceWithCorrections (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) : ℕ :=
  ((List.finRange 3).map
    (fun i => byAxis f.flag i * jetChargeAxisWithCorrections cuts f cfg i)).sum / scale

def jetMonotoneWithCorrections (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) : Bool :=
  decide (jetChargeAxisWithCorrections cuts f cfg 0 ≤ jetChargeAxisWithCorrections cuts f cfg 1 ∧
    jetChargeAxisWithCorrections cuts f cfg 1 ≤ jetChargeAxisWithCorrections cuts f cfg 2)

def roomCredit (f : Envelope) : ℕ :=
  let credit : Envelope := ⟨f.slope, f.middle, f.middle⟩
  pairPrice credit ⟨522,2318,153524⟩ ⟨93,418,41882⟩ +
    pairPrice credit ⟨464,2084,816263⟩ ⟨52,231,15351⟩

def paid : ℕ := 39317112195672787

end ProximityPrize.SubmissionLower.K6833Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
