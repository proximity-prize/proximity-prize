import ProximityPrize.SubmissionLower.MovingFiberDataTypes6814
import ProximityPrize.SubmissionLower.MovingFiberPackingData6814S7
import ProximityPrize.SubmissionLower.MovingFiberShape6814

/-! Lossless, kernel-readable data constructors. No bound is trusted here:
the ordinary receipt predicates are checked on the decoded values. -/
namespace ProximityPrize.SubmissionLower.CompactReceiptData6814
open MovingFiberReceiptTypes6814 LocatorPhase6800Oracle
open Lower80889.PhaseRows Lower80889.LedgerAudit
set_option autoImplicit false
set_option maxRecDepth 100000

def dataGet : List Nat → Nat → Nat
  | [],_ => 0
  | x::_,0 => x
  | _::xs,n+1 => dataGet xs n

def dataSlope : Nat → Nat
  | 0 => 0 | 1 => 4000000000000 | 2 => 10000000000000 | 3 => 20000000000000
  | 4 => 40000000000000 | 5 => 80000000000000 | 6 => 160000000000000 | _ => 320000000000000

def dataPacked (j r v : Nat) : Nat :=
  let a := match j with
    | 0 => MovingFiberPackingData6814.S0.packedRow r
    | 1 => MovingFiberPackingData6814.S1.packedRow r
    | 2 => MovingFiberPackingData6814.S2.packedRow r
    | 3 => MovingFiberPackingData6814.S3.packedRow r
    | 4 => MovingFiberPackingData6814.S4.packedRow r
    | 5 => MovingFiberPackingData6814.S5.packedRow r
    | 6 => MovingFiberPackingData6814.S6.packedRow r
    | _ => MovingFiberPackingData6814.S7.packedRow r
  dataGet a.toList v

def words (width : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,code => code % 2^width :: words width n (code / 2^width)

def runs {α : Type} (width : Nat) (make : Nat → α) (code : Nat) : List α :=
  (words width (code % 256) (code / 256)).map make

def nested {α : Type} (width : Nat) (make : Nat → α) : Nat → Nat → List (List α)
  | 0,_ => []
  | n+1,code => runs width make code :: nested width make n (code / 2^(8+width*(code % 256)))

def repeatPhases {α : Type} [Inhabited α] (xs : List α) : Array α :=
  let a := xs.toArray
  a ++ #[(a[3]?).getD default,(a[4]?).getD default,(a[5]?).getD default]

def baseRun (n : Nat) : BaseRun := ⟨n % 16384,n / 16384⟩
def singleRun (n : Nat) : MovingFiberSingleCore6814.Run := ⟨n % 16384,n / 16384⟩
def phaseRun (n : Nat) : PhaseRun := ⟨n % 16384,n / 16384⟩
def ledgerRun (n : Nat) : LedgerRun := ⟨n % 16384,n / 16384 % 16,n / 262144⟩
def thresholdRun (n : Nat) : Lower80889.CompressedBand.Run := ⟨n % 32768,n / 32768⟩

def baseValue (r v z : Nat) : List BaseRun → Nat
  | [] => 0
  | x::xs => if z<x.stop then dataSlope x.sheet*z+dataPacked x.sheet r v else baseValue r v z xs

def baseSegments (r v : Nat) : Nat → List BaseRun → List BaseSegment
  | _,[] => []
  | lo,x::xs =>
      if 3≤lo then
        ⟨lo,dataSlope x.sheet*lo+dataPacked x.sheet r v,dataSlope x.sheet⟩ :: baseSegments r v x.stop xs
      else baseSegments r v x.stop xs

def decodeRow (r v b t p s f l h : Nat) : Numbers :=
  let bc := runs 17 baseRun b
  { carrier := ⟨MovingFiberShape6814.cost r v 0,MovingFiberShape6814.cost r v 1,
      MovingFiberShape6814.cost r v 2,MovingFiberShape6814.cost r v 3,MovingFiberShape6814.cost r v 4⟩
    base := ⟨r,v,baseValue r v 0 bc,baseValue r v 1 bc,baseValue r v 2 bc,baseSegments r v 0 bc⟩
    threshold := repeatPhases (words 14 7 t)
    prefixValues := (words 64 10 p).toArray
    singletons := runs 21 singleRun s
    baseChoices := bc
    phaseRuns := (nested 18 phaseRun 10 f).toArray
    ledgerRuns := runs 20 ledgerRun l
    thresholdRuns := repeatPhases (nested 19 thresholdRun 7 h) }

end ProximityPrize.SubmissionLower.CompactReceiptData6814
