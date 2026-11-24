import ProximityPrize.SubmissionLower.ZFKrBre
set_option Elab.async false
open _root_ renaming Finsupp.optionElim_some → zX5, Finsupp.weight_optionElim → zVB, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.optionEquivLeft_coeff_coeff → z9x, MvPolynomial.optionEquivRight_coeff_coeff → zi3, MvPolynomial.uniqueFactorizationMonoid → zhK, Polynomial → zM1, Polynomial.coeff_map → z0b, Polynomial.mapEquiv → zNc
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qVx0j9b
noncomputable section
open Polynomial
open cu (L FX Jet)
open DP (Source Fg U4)



open MvPolynomial (optionEquivLeft optionEquivRight)
open private dPW azk from ProximityPrize.SubmissionLower.Z
open scoped nonZeroDivisors
local notation "Dmax" => P5_7_1.degree
private abbrev Vars :=Option (Option (Fin 2))
private abbrev Raw:=z3y Vars L[X]
private abbrev Generic:=z3y Vars FX
private def flat (R:Type*) [CommSemiring R] :
   zM1 (zM1 (z3y (Fin 2) R)) ≃ₐ[R] z3y Vars R :=
 (Polynomial.mapAlgEquiv (optionEquivLeft R (Fin 2)).symm).trans
   (optionEquivLeft R (Option (Fin 2))).symm
private theorem flat_coeff {R:Type*} [CommSemiring R]
  (P:zM1 (zM1 (z3y (Fin 2) R))) (j i:ℕ) (e :Fin 2 →₀ ℕ) :
  (flat R P).coeff ((e.optionElim i).optionElim j)=((P.coeff j).coeff i).coeff e := by
 rw [← z9x,flat,AlgEquiv.trans_apply,
  AlgEquiv.apply_symm_apply]
 change (((P.map (optionEquivLeft R (Fin 2)).symm.toRingHom).coeff j).coeff
  (e.optionElim i))= _
 rw [z0b,← z9x]
 change ((((optionEquivLeft R (Fin 2)) ((optionEquivLeft R (Fin 2)).symm (P.coeff j))).coeff i).coeff e)= _
 rw [AlgEquiv.apply_symm_apply]
private def commuteCoeffs :zM1 (z3y (Fin 2) L) ≃ₐ[L] z3y (Fin 2) L[X] :=
 (optionEquivLeft L (Fin 2)).symm.trans (optionEquivRight L (Fin 2))
private def rawFlat :Source ≃+* Raw :=
 (zNc (zNc commuteCoeffs.toRingEquiv)).trans
   (flat L[X]).toRingEquiv
private theorem rawFlat_coeff (A:Source) (j i a :ℕ) (e :Fin 2 →₀ ℕ) :
  ((rawFlat A).coeff ((e.optionElim i).optionElim j)).coeff a=Fg A j i a e := by
 change ((flat L[X] (A.map (Polynomial.mapRingHom commuteCoeffs.toRingHom))).coeff
  ((e.optionElim i).optionElim j)).coeff a= _
 rw [flat_coeff,z0b,Polynomial.coe_mapRingHom,z0b]
 change ((optionEquivRight L (Fin 2) ((optionEquivLeft L (Fin 2)).symm
  ((A.coeff j).coeff i))).coeff e).coeff a= _
 rw [zi3,← z9x,
  AlgEquiv.apply_symm_apply]
 rfl
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem center_flat (A:Source) :
   flat FX (U4 A)=algebraMap Raw Generic (rawFlat A) := by
 ext m
 have hm: (m.some.some.optionElim (m.some none)).optionElim (m none)=m:= by
   rw [zX5,zX5]
 rw [← hm]
 rw [flat_coeff]
 change azk (U4 A) (m none,m.some none,m.some.some) =
   (MvPolynomial.map (algebraMap L[X] FX) (rawFlat A)).coeff
     ((m.some.some.optionElim (m.some none)).optionElim (m none))
 rw [dPW,MvPolynomial.coeff_map]
 congr 1
 apply Polynomial.ext
 intro a
 exact (rawFlat_coeff A (m none) (m.some none) a m.some.some).symm
private theorem flat_scalar (u:FX) :
   flat FX (algebraMap FX Jet u)=znf u :=
 (flat FX).commutes u
private abbrev Denom:Submonoid Raw :=
 (L[X])⁰.map (znf:L[X] →+* Raw)
private theorem lift_factor {f :Generic} (hf :Irreducible f) (A:Raw)
    (hA:A≠0) (hd:f∣algebraMap Raw Generic A) :
    ∃ q:Raw,q∣A ∧ ∃ u:FX,u≠0 ∧
      algebraMap Raw Generic q=znf u*f := by
  let rawFactors :UniqueFactorizationMonoid Raw:=zhK Vars
  let genericFactors :UniqueFactorizationMonoid Generic:=zhK Vars
  have hfp:Prime f :=
    (@UniqueFactorizationMonoid.irreducible_iff_prime Generic _ genericFactors f).mp hf
  revert hA hd
  induction A using WfDvdMonoid.induction_on_irreducible with
  | zero=>exact fun hn _=>(hn rfl).elim
  | unit a ha =>
    exact fun _ hd=>(hf.not_isUnit (isUnit_of_dvd_unit hd (ha.map (algebraMap Raw Generic)))).elim
  | mul a i ha hi ih =>
    intro _ hd
    rw [map_mul,mul_comm] at hd
    rcases hfp.dvd_mul.mp hd with hd | hd
    · obtain ⟨q,hqa,u,hu,he⟩:=ih ha hd
      exact ⟨q,hqa.trans (dvd_mul_left a i),u,hu,he⟩
    · have hn:algebraMap Raw Generic i≠0:= by
        change MvPolynomial.map (algebraMap L[X] FX) i≠0
        exact (map_ne_zero_iff _ (MvPolynomial.map_injective _
          (IsFractionRing.injective L[X] FX))).mpr hi.ne_zero
      have hu : ¬ IsUnit (algebraMap Raw Generic i) :=
        fun h=>hf.not_isUnit (isUnit_of_dvd_unit hd h)
      have hip:Prime i :=
        (@UniqueFactorizationMonoid.irreducible_iff_prime Raw _ rawFactors i).mp hi
      have hir :=((IsLocalization.toLocalizationMap Denom Generic).map_prime hip hn hu).irreducible
      obtain ⟨r,hr⟩:=hd
      have hunit :=(hir.isUnit_or_isUnit hr).resolve_left hf.not_isUnit
      obtain ⟨u,hu,rfl⟩:=MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
      exact ⟨i,dvd_mul_right i a,u,hu.ne_zero,hr.trans (mul_comm _ _)⟩
private def expand:Raw ≃+* z3y (Option Vars) L :=
 (optionEquivRight L Vars).symm.toRingEquiv
private def weight (y v :ℕ) :Option Vars→ℕ :=
 fun o=>o.elim 1 (fun o=>o.elim v (fun o=>o.elim y (fun _=>0)))
private theorem weight_index (y v j i a :ℕ) (e :Fin 2 →₀ ℕ) :
   Finsupp.weight (weight y v) (((e.optionElim i).optionElim j).optionElim a) =
     a+y*i+v*j:= by
 unfold weight
 rw [zVB,zVB,zVB]
 simp [Finsupp.weight_apply,Nat.add_assoc,Nat.add_comm]
private theorem aNF (A:Source) (j i a :ℕ) (e :Fin 2 →₀ ℕ) :
   (expand (rawFlat A)).coeff (((e.optionElim i).optionElim j).optionElim a) =
     Fg A j i a e := by
 rw [← zi3]
 change (((optionEquivRight L Vars) ((optionEquivRight L Vars).symm (rawFlat A))).coeff
   ((e.optionElim i).optionElim j)).coeff a= _
 rw [AlgEquiv.apply_symm_apply,rawFlat_coeff]
private theorem bounded_iff (A:Source) (y v N :ℕ) :
   (expand (rawFlat A)).weightedTotalDegree (weight y v)≤N ↔
     ∀ j i a e,Fg A j i a e≠0→a+y*i+v*j≤N := by
 simp only [MvPolynomial.weightedTotalDegree,Finset.sup_le_iff,MvPolynomial.mem_support_iff]
 constructor
 · intro h j i a e hc
   rw [← weight_index y v j i a e]
   apply h
   rwa [aNF]
 · intro h m hm
   have he : ((m.some.some.some.optionElim (m.some.some none)).optionElim
     (m.some none)).optionElim (m none)=m:= by
     rw [zX5,zX5,zX5]
   rw [← he,weight_index]
   apply h
   rwa [← aNF,he]
end
end qVx0j9b
