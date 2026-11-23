import ProximityPrize.SubmissionLower.ZpAvArb
import ProximityPrize.SubmissionLower.CgH03
set_option Elab.async false
set_option autoImplicit true
namespace q9aDOab
open Cu
open qX9S3Pd (seed_bounds)
theorem proof :qvWbALd.c1 := by
  intro C₀ _ J H T z s S
  have hF:=(seed_bounds C₀).2.1
  obtain ⟨a,w,hw⟩:=height_family C₀ J 2 S.n S.root S.bY hF
  exact ⟨hF,rank_bound S.n H (EF S.bY) (RingHom.ker_isPrime _) S.height a _ w hw⟩
end q9aDOab
