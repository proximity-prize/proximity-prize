import ProximityPrize.SubmissionLower.Z6jV1pb
import ProximityPrize.SubmissionLower.Zy3W3oe
import ProximityPrize.SubmissionLower.ZCvigsb
set_option Elab.async false
section
section
set_option autoImplicit true
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
namespace qJrKOKe
open qMHqmcc (GG receipt appendGrades)
set_option quotPrecheck false in
local notation "az" => (receipt 2575 rfl (by decide +kernel) (by decide +kernel))
private theorem r1 :GG b11 60 4 :=⟨az,az,az,az,True.intro⟩
private theorem r2 :GG b11 64 4 :=⟨az,az,az,az,True.intro⟩
private theorem r3:GG b11 68 4 :=⟨az,az,az,az,True.intro⟩
private theorem r4 :GG b11 72 4 :=⟨az,az,az,az,True.intro⟩
private theorem r5:GG b11 76 2 :=⟨az,az,True.intro⟩
theorem h:GG b11 60 18 :=
  appendGrades (appendGrades (appendGrades (appendGrades r1 r2) r3) r4) r5
end qJrKOKe
end
end
section
section
set_option autoImplicit true
namespace qJ7OoZd
open xE Finset


open private Cc from ProximityPrize.SubmissionLower.CM


open scoped BigOperators
private def correction (r :ℤ) :ℤ :=
 if r=0 then 0 else if r=3 then 9 else if r % 2=0 then 16 else 25
private def fastPrefix (t:ℤ) :ℤ :=
 if t<0 then 0 else
  (t*(t*(t*(t+12)+46)+60)+correction (t%6))/6
private def rawPrefix (d t:ℤ) :ℤ :=
  let a :=fastPrefix t
  if t≤d+1 then a else
    let b:=a - fastPrefix (t-(d+1)) - fastPrefix (t-(d+2)) - fastPrefix (t-(d+3))
    if t≤2*d+3 then b else
      b+fastPrefix (t-2*d-3)+fastPrefix (t-2*d-4) +
        fastPrefix (t-2*d-5) - fastPrefix (t-3*d-6)
private def cumPrefix (d t:ℤ) :ℤ :=
 if d<0∨t≤0 then 0 else
  let m:=3*d+1
  rawPrefix d (min t m)+(if t≤ m then 0 else 24*(t-m)*Cc d (3*d))
private def span (d a :ℤ) (l h:ℕ) :ℤ:=cumPrefix d (a-l) - cumPrefix d (a-h)
end qJ7OoZd
end
end
