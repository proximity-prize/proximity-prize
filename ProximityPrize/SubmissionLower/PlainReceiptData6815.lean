import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.PlainReceiptData6815

def read92 (s : String) : ℕ := s.toList.foldl (fun n c =>
  let x := c.toNat
  92*n+(x-33-(if 34<x then 1 else 0)-(if 92<x then 1 else 0))) 0

def variableNatAux : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,code,out,_ => (out,code)
  | fuel+1,code,out,scale =>
    let d := code%64
    if d<32 then (out+d*scale,code/64)
    else variableNatAux fuel (code/64) (out+(d%32)*scale) (scale*32)
def variableNat (code : ℕ) := variableNatAux 16 code 0 1

def relativeFields : List ℕ → ℕ → List ℕ × ℕ
  | [],code => ([],code)
  | p::ps,code =>
    let z := variableNat code
    let value := if z.1%2=0 then p+z.1/2 else p-z.1/2
    let rest := relativeFields ps z.2
    (value::rest.1,rest.2)

def packRelative (a b c d : ℕ) : List ℕ → ℕ
  | [hi,profile,length,delta,k,lhs,rhs] =>
    hi+a*(profile+b*(length+c*(delta+d*(k+256*lhs+65536*rhs))))
  | _ => 0

def relativeAux (a b c d : ℕ) : ℕ → List ℕ → ℕ → List ℕ
  | 0,_,_ => []
  | n+1,previous,code =>
    let f := relativeFields previous code
    packRelative a b c d f.1 :: relativeAux a b c d n f.1 f.2
def relativeData (n a b c d : ℕ) (payload : String) : List ℕ :=
  relativeAux a b c d n [0,0,0,0,0,0,0] (read92 payload)
def relativeNat (n a b c d code : ℕ) : List ℕ :=
  relativeAux a b c d n [0,0,0,0,0,0,0] code

def seriesAux : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0,_,_,_ => []
  | n+1,previous,older,code =>
    let z := variableNat code
    let prediction := 2*previous-older
    let value := if z.1%2=0 then prediction+z.1/2 else prediction-z.1/2
    value::seriesAux n value previous z.2
def series (n code : ℕ) : Array ℕ := (seriesAux n 0 0 code).toArray

end ProximityPrize.SubmissionLower.PlainReceiptData6815
