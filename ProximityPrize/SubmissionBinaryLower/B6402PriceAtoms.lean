import ProximityPrize.SubmissionBinaryLower.B6402PriceTarget

/-! Keep the global sums and local ranks behind explicit equalities.
Evaluating a certified price from its eleven moment inputs then takes
constant arithmetic work, independent of the interpolation multiplicity. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PriceAtoms
open B6401Params B6401ContactKerD B6402EndpointBudget B6402PriceTarget B6402DimensionBudget
open B6402LocalMoments B6402InterpolationPrice B6402OrderProfile
set_option autoImplicit false
set_option maxHeartbeats 1200000

structure Moment where
  size : ℕ
  grade : ℕ
deriving DecidableEq,Repr

def global (W s : ℕ) : Moment := ⟨varsKerDExact wY W s,gMoment wY W s⟩
def localM (m s : ℕ) : Moment := ⟨rankKerD m s,localMoment m s⟩

structure Shape where
  cols : Moment
  cof : Moment
  light : Moment
  heavy : Moment
  at0 : Moment
  at1 : Moment
  at2 : Moment
  at3 : Moment
  previous : ℕ
  upperLo : ℚ
  upperHi : ℚ
deriving DecidableEq,Repr

def shapeAt (W WFhi m0 s b : ℕ) (lo hi : ℚ) : Shape :=
  let m:=m0-b
  let s':=s-1
  ⟨global W s,global (W-WFhi) s',localM m s,localM m0 s,
   localM (m-0) s',localM (m-1) s',localM (m0-2) s',localM (m-3) s',rankKerD (m-2) s',
   varsKerDUpperQ wY ((W:ℚ)-lo*wY) s',varsKerDUpperQ wY ((W:ℚ)-hi*wY) s'⟩

def shape (p : Plan) := shapeAt p.W p.WFhi p.m p.s p.b p.lo p.hi

theorem moment_eq (a b : Moment) (h : a.size=b.size) (g : a.grade=b.grade) : a=b := by
  cases a; cases b; simp_all

theorem shape_eq (a b : Shape) (c : a.cols=b.cols) (f : a.cof=b.cof) (l : a.light=b.light)
    (h : a.heavy=b.heavy) (x0 : a.at0=b.at0) (x1 : a.at1=b.at1) (x2 : a.at2=b.at2)
    (x3 : a.at3=b.at3) (pr : a.previous=b.previous) (u : a.upperLo=b.upperLo) (v : a.upperHi=b.upperHi) : a=b := by
  cases a; cases b; simp_all

def costOf (base aux : Moment) (t h q : ℚ) := ((base.size:ℚ)-aux.size)*(t+1)+h*aux.size-q*((base.grade:ℚ)-aux.grade)

def evaluate (p : Plan) (h : ℚ) (a : Shape) : Values :=
  let t := (p.cap:ℚ)-p.s*h
  let m2 := (p.m:ℚ)*p.m
  let den := (N:ℚ)*p.m*p.m
  let vl := ((a.cols.size:ℚ)-a.upperLo)/den
  let vh := ((a.cols.size:ℚ)-a.upperHi)/den
  let tilt := (vh-vl)/(p.hi-p.lo)
  ⟨costOf a.light a.at0 t h p.q/m2,costOf a.light a.at1 t h p.q/m2,
   (costOf a.heavy a.at2 t h p.q+regCost p t h)/m2,costOf a.light a.at3 t h p.q/m2,
   (a.previous-a.at3.size:ℕ)*(t+1)/m2,-(tilt*(t+1)),(badCost p t h-regCost p t h)/m2,
   (vl-tilt*p.lo)*(t+1)+(h*a.cof.size-(p.q:ℚ)*((a.cols.grade:ℚ)-a.cof.grade))/den⟩

theorem values_eq (p : Plan) (h : ℚ) : values p h=evaluate p h (shape p) := by
  rfl

#print axioms values_eq
end ProximityPrize.SubmissionBinaryLower.B6402PriceAtoms
