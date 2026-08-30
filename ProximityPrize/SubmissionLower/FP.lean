import ProximityPrize.SubmissionLower.X6
import ProximityPrize.SubmissionLower.S
import ProximityPrize.SubmissionLower.CE
namespace ProximityPrize.SubmissionLower.RCN236
open RCN014
open RCN225
open RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {J:Type*} [Fintype J]
noncomputable def primaryPiecesCertificateOfMembershipWeighted
   [IsLocalRing R]
   (surface tail:Polynomial R)
   [hSurfacePrime:(Ideal.span {surface}).IsPrime]
   (relation:J → Ideal (Polynomial R))
   (relationBar:J → Ideal (SurfaceQuotient surface))
   [∀ j,(relationBar j).IsMaximal]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBar:∀ j,relationBar j=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) (relation j))
   (hrelationBarNe:∀ j,relationBar j≠⊥)
   [∀ j,IsLocalHom
     (algebraMap R (Localization.AtPrime (relationBar j)))]
   [∀ j,FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))]
   (mu:J → ℕ)
   (htail:∀ j,tail∈Ideal.span {surface} ⊔ relation j^mu j)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j)):
   PrimaryPiecesCertificate surface tail (fun j↦
     mu j*Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))) where
 pieces j:=mappedPrimaryPiece (RingHom.id (Polynomial R)) relation
   surface mu j
 coprime:=mappedPrimaryPiece_pairwise_coprime
   (RingHom.id (Polynomial R)) relation hcoprime surface mu
 contains j:=by
   apply span_pair_le_mappedPrimaryPiece
     (RingHom.id (Polynomial R)) relation surface tail mu j
   simpa only [mappedPrimaryPiece,Ideal.map_id] using htail j
 length_le j:=by
   have hmap:Ideal.map (RingHom.id (Polynomial R)) (relation j)=relation j:=
     Ideal.map_id (relation j)
   have hbound:=
     exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
       (R:=R) surface (relation j) (relationBar j)
         (hrelationBar j) (hrelationBarNe j) (mu j)
   change ((mu j*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j))):ℕ):ℕ∞) ≤
       Module.length R (Polynomial R ⧸ (Ideal.span {surface} ⊔
         Ideal.map (RingHom.id (Polynomial R)) (relation j)^mu j))
   rw [hmap]
   exact hbound
end
end ProximityPrize.SubmissionLower.RCN236
