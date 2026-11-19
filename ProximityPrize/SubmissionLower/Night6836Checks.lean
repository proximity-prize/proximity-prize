/- Apache-2.0. Bome2017. Physical charging thresholds and packed convolution receipts. -/
import ProximityPrize.SubmissionLower.Night6836GridData
import ProximityPrize.SubmissionLower.Night6836Fast
namespace Koala6836.Fast
open Koala6836.Grid
def dataOK (r e:Nat) : Bool :=
  (allRow r e < bigB && compRow r e < bigB) &&
  (List.range N).all fun k=> decide (
    lane (oneRow r e) k≤M ∧ lane (allRow r e) k≤M ∧ lane (compRow r e) k≤G ∧
    lane (oneRow r e) k≤lane (allRow r e) k ∧ G-lane (compRow r e) k≤lane (allRow r e) k)
def rounded (r e:Nat) : Bool :=
  (List.range N).all fun k=> decide (Koala6836.Tables.oneUnits r e k≤77*lane (oneRow r e) k)
def block (r start count:Nat) : Bool :=
  (List.range count).all fun i=> (dataOK r (start+i) && checks r (start+i)) && rounded r (start+i)
end Koala6836.Fast
