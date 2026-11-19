/- Apache-2.0. Simultaneously check all 94 by 94 allocations of total degree. -/
import ProximityPrize.SubmissionLower.Night6836GridPacked
namespace Koala6836.Fast
open Koala6836.Grid
def pack (b:Nat) : Nat → (Nat→Nat) → Nat
 | 0,_=>0
 | n+1,f=> f 0 + b*pack b n (fun i=>f (i+1))
def B : Nat := 16384
def G : Nat := 8191
def M : Nat := 4095
def N : Nat := 94
def rep : Nat := (B^N-1)/(B-1)
def bigB : Nat := B^N
def repRows : Nat := (bigB^N-1)/(bigB-1)
def lane (x k:Nat) := (x >>> (14*k)) &&& 16383
def xBlock (x : Nat) : Nat := pack bigB N (fun h=>lane x h*rep)
def yBlock (y : Nat) : Nat := y*repRows
def cBlock (c : Nat) : Nat := pack bigB N (fun h=>c >>> (14*h))
def blockMask : Nat := G*rep*repRows
def checkSplit (r e a m:Nat) : Bool :=
 let z:=xBlock (oneRow a m)+yBlock (allRow (r-a) (e-m))+cBlock (compRow r e)
 z &&& blockMask == z
def checks (r e:Nat) : Bool :=
 (List.range (r/2)).all fun i=> (List.range (e+1)).all fun m => checkSplit r e (i+1) m
end Koala6836.Fast
