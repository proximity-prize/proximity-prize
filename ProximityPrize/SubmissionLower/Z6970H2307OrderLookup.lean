import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_18af1e93c2c85f1a
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da
import ProximityPrize.SubmissionLower.Bundle6970_be63a5e74efda8da

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Height2307Orders

def rawThresholds : Nat → List Threshold
  | 0 => band0
  | 1 => band1
  | 2 => band2
  | 3 => band3
  | 4 => band4
  | 5 => band5
  | 6 => band6
  | 7 => band7
  | 8 => band8
  | 9 => band9
  | 10 => band10
  | 11 => band11
  | 12 => band12
  | 13 => band13
  | 14 => band14
  | 15 => band15
  | 16 => band16
  | 17 => band17
  | 18 => band18
  | 19 => band19
  | 20 => band20
  | 21 => band21
  | 22 => band22
  | 23 => band23
  | 24 => band24
  | 25 => band25
  | 26 => band26
  | 27 => band27
  | 28 => band28
  | 29 => band29
  | 30 => band30
  | 31 => band31
  | 32 => band32
  | 33 => band33
  | 34 => band34
  | 35 => band35
  | 36 => band36
  | 37 => band37
  | 38 => band38
  | 39 => band39
  | 40 => band40
  | 41 => band41
  | _ => []

def thresholds {n : Nat} (k : Fin n) : List Threshold := rawThresholds k.val

def order {n : Nat} (k : Fin n) (b j : Nat) : Nat := lookup b j (thresholds k)

end Height2307Orders
