import ProximityPrize.SubmissionLower.BG
set_option Elab.async false
namespace aA2
noncomputable section
open aR oR we yz MvPolynomial
private theorem cT7 {f :af 3} {P:Ideal (eT 3)} {y :oe}
    (hy :y∈S3 f P) :F3 f P≤oF y :=
  vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hy)
private theorem ddv {f :af 3} {P:Ideal (eT 3)} {y :oe}
    (hy :y∈S3 f P) :S7 f∉oF y := by
  obtain ⟨x,hx,rfl⟩:=hy
  intro hs
  apply hx.2
  rw [← ahz f x (sep f)]
  exact (mem_vanishingIdeal_singleton_iff _ _).mp hs
end
end aA2
