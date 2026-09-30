import ProximityPrize.SubmissionLower.MovingSourceThickCuts6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairPrimary6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN225 RCN307 RCN309

def thickPiece {R I : Type*} [CommRing R]
    (surface : I → R) (relation : I → Ideal R) (d : I → ℕ) (i : I) : Ideal R :=
  Ideal.span {surface i} ⊔ relation i^d i

theorem thickPieces_coprime {R I : Type*} [CommRing R]
    (surface : I → R) (relation : I → Ideal R) (d : I → ℕ)
    (hcop : Pairwise fun i j => IsCoprime (relation i) (relation j)) :
    Pairwise fun i j => IsCoprime (thickPiece surface relation d i) (thickPiece surface relation d j) := by
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [←Ideal.pow_sup_pow_eq_top (hcop hij).sup_eq (m:=d i) (n:=d j)]
  exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)

section Certificates
variable {R I : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [Fintype I]

def sourcePairCertificate
    (P Q : Polynomial R) (surface : I → Polynomial R)
    [∀ i,(Ideal.span {surface i}).IsPrime]
    (relation : I → Ideal (Polynomial R))
    (relationBar : ∀ i, Ideal (SurfaceQuotient (surface i)))
    [∀ i,(relationBar i).IsMaximal]
    [∀ i,IsNoetherianRing (SurfaceQuotient (surface i))]
    (hbar : ∀ i, relationBar i=Ideal.map (Ideal.Quotient.mk (Ideal.span {surface i})) (relation i))
    (hbarNe : ∀ i,relationBar i≠⊥)
    [∀ i,IsLocalHom (algebraMap R (Localization.AtPrime (relationBar i)))]
    [∀ i,FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))]
    (d : I → ℕ)
    (hP : ∀ i,P∈thickPiece surface relation d i)
    (hQ : ∀ i,Q∈thickPiece surface relation d i)
    (hcop : Pairwise fun i j => IsCoprime (relation i) (relation j)) :
    PrimaryPiecesCertificate P Q (fun i => d i*Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (Localization.AtPrime (relationBar i)))) where
  pieces := thickPiece surface relation d
  coprime := thickPieces_coprime surface relation d hcop
  contains i := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ hP i
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hQ i
  length_le i := exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
    (R:=R) (surface i) (relation i) (relationBar i) (hbar i) (hbarNe i) (d i)

theorem thickPiece_finite
    (surface : I → Polynomial R) (relation : I → Ideal (Polynomial R)) (d : I → ℕ)
    (hmonic : ∀ i, ∃ M : Polynomial R, M.Monic ∧ M∈relation i) (i : I) :
    Module.Finite R (Polynomial R ⧸ thickPiece surface relation d i) := by
  obtain ⟨M,hM,hmem⟩ := hmonic i
  exact moduleFinite_quotient_of_monic_mem (thickPiece surface relation d i)
    (M^d i) (hM.pow _) ((show relation i^d i≤thickPiece surface relation d i from le_sup_right)
      (Ideal.pow_mem_pow hmem (d i)))

def swapCertificate {P Q : Polynomial R} {d : I → ℕ} (C : PrimaryPiecesCertificate P Q d) :
    PrimaryPiecesCertificate Q P d where
  pieces := C.pieces
  coprime := C.coprime
  contains i := by simpa only [intersectionIdeal,Set.pair_comm] using C.contains i
  length_le := C.length_le
end Certificates

end
end ProximityPrize.SubmissionLower.MovingSourcePairPrimary6814
