import ProximityPrize.SubmissionLower.M2
namespace ProximityPrize.SubmissionLower.ContactSylvesterCokernelQuotient6732Research
noncomputable section
set_option autoImplicit false
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
def intersectionIdeal (P Q:Polynomial R):Ideal (Polynomial R):=
 Ideal.span {P,Q}
structure PrimaryPiecesCertificate
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (multiplicity:J → ℕ) where
 pieces:J → Ideal (Polynomial R)
 coprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j)
 contains:∀ j,intersectionIdeal P Q ≤ pieces j
 length_le:∀ j,(multiplicity j:ℕ∞) ≤
   Module.length R (Polynomial R ⧸ pieces j)
end
end ProximityPrize.SubmissionLower.ContactSylvesterCokernelQuotient6732Research
