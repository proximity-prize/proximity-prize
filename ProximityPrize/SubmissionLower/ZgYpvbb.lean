import ProximityPrize.SubmissionLower.BG
set_option Elab.async false
set_option autoImplicit true
namespace dna
noncomputable section
open aR oR we yz aA2 MvPolynomial
private theorem b8V {f :af 3} {P:Ideal (eT 3)} [P.IsPrime]
    (hsep:sep f∉P) (a :eT 3) :
    a∈P ↔ ∀ x∈D7 f P,eval x a=0:= by
  refine ⟨fun ha _ hx=>hx.1 a ha,fun ha => ?_⟩
  have hz :sep f*a∈vanishingIdeal cH (zeroLocus cH P) := by
    intro x hx
    change eval x (sep f*a)=0
    rw [map_mul]
    by_cases hs :eval x (sep f)=0
    · rw [hs,zero_mul]
    · rw [ha x ⟨hx,hs⟩,mul_zero]
  rw [IsPrime.vanishingIdeal_zeroLocus P] at hz
  exact (‹P.IsPrime›.mem_or_mem hz).resolve_left hsep
end
end dna
