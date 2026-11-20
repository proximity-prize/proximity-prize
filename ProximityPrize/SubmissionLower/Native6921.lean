import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Protocol6921
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Native6921
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark Principal Native
local instance : NeZero (131072 : ℕ) := ⟨by decide⟩
abbrev radius := Protocol6921.radius
theorem native_IsMCA_badSlope (U : Fin 2 → I → K) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U Native6921.radius) :
    BadSlope IRSProfile.domain (U 0) (U 1) 131072 180120 γ := by
  change IsMCA (AffineLineGenerator K) (ReedSolomon.code IRSProfile.domain 131072)
    γ U Native6921.radius at hγ
  apply isMCA_implies_badSlope IRSProfile.domain U 131072 180120 Native6921.radius ?_ γ hγ
  intro T hT
  norm_num [IRSProfile.card_index, radius, Protocol6921.radius, List6921.Native.radius6921, claimedRadius] at hT ⊢
  by_contra! h
  have he : (T.card : ℝ) ≤ 180119 := by exact_mod_cast (show T.card ≤ 180119 by omega)
  linarith

theorem native_type_one_MCA_count (U : Fin 2 → I → K)
    (htype : TypeOneSyndromes IRSProfile.domain (U 0) (U 1) 131072 p)
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U Native6921.radius) : Γ.card ≤ 1 := by
  apply type_one_bad_count IRSProfile.domain IRSProfile.domain.injective
    (U 0) (U 1) 131072 180120 p
    (by norm_num only [IRSProfile.card_index]) (by norm_num [p]) htype Γ
  intro γ hγ
  exact Native6921.native_IsMCA_badSlope U γ (hΓ γ hγ)

def PrincipalCert (u v : I → K) : Prop :=
  ∃ a q : ℕ, a+q=82024 ∧ Nonempty (PrincipalAt
    (fun b j => genericSlopeEmbedding (parameterSyndromes p IRSProfile.domain u v b j))
    131072 a q)

/-- Native any-nullity principal-kernel theorem from bare principality
over K(Z), without a separately supplied cofactor or normal-fiber package. -/
theorem native_generic_principal_MCA_count (U : Fin 2 → I → K)
    (hprincipal : PrincipalCert (U 0) (U 1))
    (Γ : Finset K) (hΓ : ∀ γ ∈ Γ,
      IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ U Native6921.radius) :
    Γ.card ≤ 733323102339177 := by
  obtain ⟨a,q,hsum,⟨P⟩⟩ := hprincipal
  have hbad : ∀ γ ∈ Γ,
      BadSlope IRSProfile.domain (U 0) (U 1) 131072 (131072+(131072-(a+q))) γ := by
    intro γ hγ
    rw [hsum]
    exact Native6921.native_IsMCA_badSlope U γ (hΓ γ hγ)
  have hh := generic_principal_bad_count_coarse genericSlopeEmbedding
    (IsFractionRing.injective K[X] GenericSlopeField) p (by norm_num [p])
    IRSProfile.domain IRSProfile.domain.injective native_domain_fixed (U 0) (U 1)
    131072 131072 a q (by norm_num only [IRSProfile.card_index]) (by omega) P Γ hbad
  rw [IRSProfile.card_index] at hh
  exact hh.trans (calc
    _ ≤ p*(262144+82025) := Nat.mul_le_mul_left p (by omega)
    _ = _ := by norm_num [p])


end
end FrobeniusLocator.Native6921
namespace FrobeniusLocator.Strata6921
noncomputable section
open Polynomial Matrix Finset Strata
open ProximityPrize.Benchmark
theorem native_relation_height_fits_field (H : ℕ) (hH : H≤32970) :
    (2*H+2)*Native.p<Fintype.card Native.K := by
  change (2*H+2)*2130706433<Fintype.card KoalaBear.Ext6
  rw [KoalaBear.card_ext6]
  have hle := Nat.mul_le_mul_right 2130706433 (show 2*H+2≤2*32970+2 by omega)
  exact hle.trans_lt (by norm_num)

/-- Native primitive polynomial Lemma T with all size/degree guards
proved. The binary level Hilbert function remains an EXPLICIT premise. -/
def native_lemmaT_of_two_active_level (U : Fin 2 → Native.I → Native.K)
    (r a b c : ℕ) (hr7 : 7≤r) (ha : a≤b) (hb : b≤82024) (hc : 82024<c)
    (hcm : c≤131072) (hsum : a+b+c=262146) (hr : r+a+b=164050)
    (hHF : HasLevelHilbertFunction
      (fun b j => algebraMap Native.K[X] (GenericLayer.GenericField Native.K)
        (Principal.parameterSyndromes Native.p IRSProfile.domain (U 0) (U 1) b j)) 131072 a b c) :
    PolynomialRelationCertificate Native.p IRSProfile.domain (U 0) (U 1) 131072 (131073-c) := by
  have hH : 131073-c ≤ 32970 := by omega
  have hline := generic_relation_line_of_level Native.p IRSProfile.domain (U 0) (U 1)
    131072 a b c hcm hsum ha (by omega) (by omega) hHF
  exact polynomialRelationCertificate_of_nullity_one Native.p (by norm_num [Native.p])
    IRSProfile.domain (U 0) (U 1) IRSProfile.domain.injective Native.native_domain_fixed
    131072 131072 (131073-c) (by rw [IRSProfile.card_index]) (by omega)
    (Strata6921.native_relation_height_fits_field _ hH) hline

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
theorem native_rank_exception_count [ExpChar F 2130706433]
    (x u v : ι → F) (r : ℕ) (hr7 : 7≤r)
    (hr : GenericLayer.genericRank (stacked 2130706433 x u v 49048 82024)=82025-r)
    (hfirst : GenericLayer.genericRank (hankel x u v 49048 82024)=49048)
    (Γ : Finset F) (hΓ : ∀ γ∈Γ,
      ((stacked 2130706433 x u v 49048 82024).map (evalRingHom γ)).rank ≠ 82025-r) :
    Γ.card ≤ 70249391145058 := by
  have hb := two_block_rank_exception_count 2130706433 x u v 49048 82024 r hr hfirst Γ hΓ
  have hs : 82024+1-r-49048 ≤ 32970 := by omega
  have hm := Nat.mul_le_mul_left 2130706433 hs
  omega

end
end FrobeniusLocator.Strata6921
