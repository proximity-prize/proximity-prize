import ProximityPrize.SubmissionLower.BI
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
open _root_ renaming Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.mul_mem_mul → zgK, LinearMap.ker → z83, Module.length → zKQ, Nat.cast_add → z6H
set_option autoImplicit true
namespace OO
noncomputable section
open IsLocalRing
open aR (af)
open dN (GeoJets GeoField bC oA kC)
open agL (afc)
open aFY (triangle a5U aV1 ce2)
open private bih from ProximityPrize.SubmissionLower.BC
private theorem gEj (i h:ℕ) :
    triangle (i+h)=i*h+(triangle i+triangle h) := by
  nlinarith only [bih i,bih h,bih (i+h)]
private theorem eOZ {R:Type*} [CommRing R] (m:Ideal R)
    (hh : ∀ n,zKQ R (R ⧸ m^n)=(triangle n:ℕ∞))
    {f g:R} {i h:ℕ} (hf :f∈m^i) (hg:g∈m^h) :
    (↑(i*h) :ℕ∞)≤zKQ R (R ⧸ Ideal.span {f,g}) := by
  let T:=m^(i+h)
  let J:Ideal R:=Ideal.span {f,g}
  have hmulF (r :R) (hr :r∈m^h) :r*f∈T:= by
    have hmem:=zgK hr hf
    rwa [← pow_add,Nat.add_comm h i] at hmem
  have hmulG (r :R) (hr :r∈m^i) :r*g∈T:= by
    have hmem:=zgK hr hg
    rwa [← pow_add] at hmem
  let F:=a5U (m^h) T f hmulF
  let G:=a5U (m^i) T g hmulG
  let H :=LinearMap.coprod F G
  let q:=Submodule.factor (show (T:Submodule R R)≤T ⊔ J from le_sup_left)
  have hker :z83 q=LinearMap.range H := by
    ext z
    obtain ⟨z,rfl⟩:=zld z
    change zVv (T ⊔ J) z=0↔zVv T z∈LinearMap.range H
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro hz
      obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp hz
      obtain ⟨c,d,rfl⟩:=Ideal.mem_span_pair.mp hb
      refine ⟨(zVv _ c,zVv _ d),?_⟩
      simp [H,F,G,aV1,map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · rintro ⟨⟨c,d⟩,he⟩
      obtain ⟨c,rfl⟩:=zld c
      obtain ⟨d,rfl⟩:=zld d
      have he' : zVv T (c*f+d*g)=zVv T z := by
        simpa [H,F,G,aV1,map_add] using he
      rw [Ideal.Quotient.eq] at he'
      have hz :z=(-(c*f+d*g - z))+(c*f+d*g) := by ring
      rw [hz]
      exact (T ⊔ J).add_mem (Ideal.mem_sup_left (T.neg_mem he'))
        (Ideal.mem_sup_right (Ideal.mem_span_pair.mpr ⟨c,d,rfl⟩))
  have hq:=Module.length_eq_add_of_exact (z83 q).subtype q
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map q)
  have hsmall:=Module.length_le_of_surjective H.rangeRestrict H.surjective_rangeRestrict
  rw [← hker,Module.length_prod] at hsmall
  simp only [hh] at hsmall
  have hsum: (↑(i*h) :ℕ∞)+((triangle i:ℕ∞)+triangle h) ≤
      zKQ R (R ⧸ (T ⊔ J:Ideal R))+((triangle i:ℕ∞)+triangle h) := by
    rw [← z6H,← z6H,← gEj,← hh]
    change zKQ R (R ⧸ T)≤_
    rw [hq,z6H,add_comm (zKQ R ↥(z83 q))]
    exact add_le_add_right (by simpa only [add_comm (triangle h:ℕ∞)] using hsmall) _
  exact ((ENat.add_le_add_iff_right (by rw [← Nat.cast_add]; exact ENat.natCast_ne_top _)).mp hsum).trans
    (Module.length_le_of_surjective (Submodule.factor (show J≤T ⊔ J from le_sup_right))
      (Submodule.factor_surjective _))
theorem bsc {f Q:af 4} {z :Ideal GeoJets} [hp:z.IsPrime]
    (hheight:z.height=2) {i h:ℕ}
    (hf :afc z (bC f) i) (hQ:afc z (bC Q) h) :
    (↑(i*h) :ℕ∞)≤oA (kC f Q) z hp:= by
  let R:=Localization.AtPrime z
  let φ:=algebraMap GeoJets R
  have hdim:ringKrullDim R=2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height z R,hheight]
    rfl
  have hbase :IsRegularRing GeoField:=inferInstance
  have hambient:IsRegularRing GeoJets :=MvPolynomial.isRegularRing_of_isRegularRing GeoField
  have hregular :IsRegularLocalRing R :=
    IsRegularRing.isRegularLocalRing_localization z
  have hfactor :UniqueFactorizationMonoid GeoJets :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  have hlocalFactor :UniqueFactorizationMonoid R :=
    UniqueFactorizationMonoid.of_isLocalization z.primeCompl R
  have hdomain:IsDomain R:=inferInstanceAs (IsDomain (Localization.AtPrime z))
  change (↑(i*h) :ℕ∞)≤zKQ R (R ⧸ (kC f Q).map φ)
  rw [kC,Ideal.map_span,Set.image_insert_eq,Set.image_singleton]
  exact eOZ (maximalIdeal R) (ce2 (R:=R) hdim) hf hQ
end
end OO
