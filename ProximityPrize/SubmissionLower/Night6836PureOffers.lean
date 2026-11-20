/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836OfferData
import ProximityPrize.SubmissionLower.Night6836GridData
import ProximityPrize.SubmissionLower.Night6836Room
namespace Koala6836.PureOffers
open Koala6835.Offers
open Koala6836.Offers
open Koala6836.Tables Koala6836.Room
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
structure FlagDegree where
  zOnly : Nat
  yz : Nat
  all : Nat
structure Envelope where
  slope : Nat
  middle : Nat
  total : Nat
private def w : Nat := 131071
def Envelope.pad (f : Envelope) (tailRoom : Nat) : Envelope :=
  let r := max 3 f.slope
  let y := max f.middle (r + 2)
  ⟨r, y, max f.total (y + tailRoom)⟩


def flagMixed (p q r:FlagDegree):Nat:=
 p.all*q.all*r.all+
 (p.zOnly*q.all*r.all+q.zOnly*p.all*r.all+
   r.zOnly*p.all*q.all)+
 (p.yz*q.all*r.all+q.yz*p.all*r.all+
   r.yz*p.all*q.all)+
 (p.all*q.yz*r.yz+q.all*p.yz*r.yz+
   r.all*p.yz*q.yz)+
 (p.zOnly*q.yz*r.all+p.zOnly*r.yz*q.all+
   q.zOnly*p.yz*r.all+q.zOnly*r.yz*p.all+
   r.zOnly*p.yz*q.all+r.zOnly*q.yz*p.all)

def firstTail (f : Envelope) : FlagDegree :=
  ⟨2*(w+1)*(f.total-f.middle),
    1+2*(w+1)*(f.middle-f.slope), 2*(w+1)*(f.slope-1)⟩


def normalTail (shift : Nat) (f : Envelope) : FlagDegree :=
  ⟨(w+3)*(f.total-f.middle),
    (w+3)*(f.middle-f.slope)-(w+1)+shift,
    (w+3)*(f.slope-1)-shift⟩

def movingFiber (f : Envelope) : FlagDegree :=
  ⟨f.total-f.middle, f.middle-f.slope, f.slope+1⟩


def ordinaryMovingTail (f : Envelope) : FlagDegree :=
  ⟨(w+3)*(f.total-f.middle), (w+3)*(f.middle-f.slope), (w+3)*f.slope-1⟩


def rowRaw (r e z : Nat) : Nat :=
  let f := (⟨r,r+e,r+e+z⟩ : Envelope).pad 0
  let a : FlagDegree := ⟨z,e,r⟩
  flagMixed a (firstTail f) (normalTail 0 f) + 65539 * flagMixed a (movingFiber f) (ordinaryMovingTail f)

def stepOK (bank : Nat → Offer) (raw : Nat → Nat → Nat → Nat) (r e lo hi cap id : Nat) : Bool :=
  if id = 0 then decide (raw r e (hi-(r+e)) ≤ cap)
  else let w := bank (id-1); decide (valid w r e lo hi ∧ w.fee ≤ cap)

def check (bank : Nat → Offer) (raw : Nat → Nat → Nat → Nat) (r e hi cap : Nat) : Nat → Nat → Nat → Bool
  | 0,lo,_ => decide (hi < lo)
  | fuel+1,lo,code =>
    if hi < lo then true else
      let stop := min hi (lo + code % 16777216 / 1024)
      stepOK bank raw r e lo stop cap (code % 1024) &&
        check bank raw r e hi cap fuel (stop+1) (code/16777216)


def binOK (r e k : Nat) : Bool :=
  check bank rowRaw r e (min 9352 (r+e+100*k+99)) (oneUnits r e k*10000000000000)
    5 (r+e+100*k) (binPlan r e k)
def singleOK (r e : Nat) : Bool :=
  if maxTotal r e=0 then true else
    (if r+e<split r e then check bank rowRaw r e (split r e-1) (lowBudget r e) 12 (r+e) (bottomPlan r e) else true) &&
    check bank rowRaw r e (maxTotal r e) (highBudget r e) 12 (split r e) (topPlan r e)
def rowOK (r e : Nat) : Bool := singleOK r e && (List.range 94).all fun k =>
  if r+e+100*k≤9352 then binOK r e k else true
end Koala6836.PureOffers
