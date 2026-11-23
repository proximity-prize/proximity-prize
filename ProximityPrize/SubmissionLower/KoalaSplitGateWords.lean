import ProximityPrize.SubmissionLower.FadicVarCert

set_option Elab.async false
namespace KoalaSplitGateWords

private def digit (c : Char) : ℕ :=
  let b:=c.toNat
  b - if b < 35 then 33 else if b < 93 then 34 else 35

def words (code : String) : List ℕ :=
  let (n, xs) := code.toList.foldl
    (fun (state : ℕ × List ℕ) c =>
      if c = ' ' then (0,state.1 :: state.2)
      else (92*state.1+digit c,state.2)) (0,[])
  (n :: xs).reverse

private def box (r : ℕ) : FadicGate.Entry :=
  if r = 0 then none else
    let n:=r - 1
    some (n % 4096,n / 4096 % 2048,n / (4096*2048))

def unpack (code:String):List FadicGate.Entry:=(words code).map box

def powers (code : String) : List ℕ :=
  let (_, _, xs) := code.toList.foldl (fun (state : ℕ × ℕ × List ℕ) c =>
    let (remaining,acc,out):=state
    let d:=digit c
    if remaining > 1 then (remaining - 1,d,out)
    else if remaining=1 then (0,0,(92*acc+d) :: out)
    else if d=91 then (2,0,out)
    else (0,0,d :: out)) (0,0,[])
  xs.reverse

end KoalaSplitGateWords
