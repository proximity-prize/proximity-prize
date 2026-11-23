import ProximityPrize.SubmissionLower.Z4WdLEc
set_option Elab.async false
namespace P4_6_5_1_1
open aR (Shape)

open yz (aCt)



private theorem gre (s :Shape) (h:ℕ)
    (hb:1≤ s.b) (hj:2≤ s.j) (ht:1≤ s.t) (hh:1≤h)
    (i:Fin 4) :Finsupp.single i 1∈aCt s h:= by
  change (Finsupp.single i 1) 0+(Finsupp.single i 1) 1+(Finsupp.single i 1) 2 ≤
    s.b∧(Finsupp.single i 1) 1+2*(Finsupp.single i 1) 2≤ s.j ∧
    (Finsupp.single i 1) 2≤ s.t∧(Finsupp.single i 1) 3≤h
  fin_cases i <;> norm_num [Finsupp.single_apply] <;> omega
end P4_6_5_1_1
