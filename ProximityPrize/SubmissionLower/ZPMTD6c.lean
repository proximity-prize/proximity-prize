import ProximityPrize.SubmissionLower.ZFKrBre
set_option Elab.async false
open _root_ renaming Function.comp_apply → z3s, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.map → zDK, MvPolynomial.optionEquivLeft → zpj, MvPolynomial.rename → zHw, Polynomial.map_mul → zNl
set_option maxHeartbeats 800000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qwWTALb
noncomputable section
open Polynomial
open P5 (p)
open P5_7_1
open qaySLPd
open cu (L)
open scoped nonZeroDivisors
open private b0u from ProximityPrize.SubmissionLower.A3
abbrev X3:=z3y (Fin 3) L[X]
abbrev YN (R:Type) [CommSemiring R] :
   z3y (Fin 4) R ≃ₐ[R] Polynomial (z3y (Fin 3) R) :=
 (MvPolynomial.renameEquiv R finSuccEquivLast).trans (zpj R (Fin 3))
abbrev cut (B:TopRow) :X3 :=
 aeA.elimination B
theorem view_map {R S:Type} [CommSemiring R] [CommSemiring S]
  (φ:R →+* S) (B:z3y (Fin 4) R) :
  (YN R B).map (zDK φ)=YN S (zDK φ B) := by
 change (_:Polynomial (z3y (Fin 3) S)) =
  zpj S _ (zHw _ (zDK φ B))
 rw [← MvPolynomial.map_rename]
 exact MvPolynomial.map_optionEquivLeft φ _
private theorem squarefree_fraction {R:Type} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    (f :R[X]) (hf :Squarefree f) :
    Squarefree (f.map (algebraMap R (FractionRing R))) := by
  classical
  let F:=FractionRing R
  let ι:=algebraMap R F
  let:NormalizedGCDMonoid R:=Classical.choice inferInstance
  intro g hg
  have hg0:g≠0:=ne_zero_of_dvd_ne_zero
    ((Polynomial.map_ne_zero_iff (zxb R F)).mpr hf.ne_zero)
    ((dvd_mul_right g g).trans hg)
  let r :=IsLocalization.integerNormalization R⁰ g
  obtain ⟨a,ha,hr⟩:=IsLocalization.integerNormalization_spec R⁰ g
  change r.map ι=a•g at hr
  have ha' : IsUnit (C (ι a)) :=
    (IsUnit.mk0 _ ((map_ne_zero_iff ι (zxb R F)).mpr
      (nonZeroDivisors.ne_zero ha))).map C
  rw [Algebra.smul_def,Polynomial.algebraMap_apply] at hr
  change r.map ι=C (ι a)*g at hr
  let q:=r.primPart
  have hp:q.IsPrimitive :=r.isPrimitive_primPart
  have hqr :q.map ι∣r.map ι:= by
    rw [r.eq_C_content_mul_primPart,zNl,mul_comm]
    exact dvd_mul_right _ _
  have hqg:q.map ι∣g:=ha'.dvd_mul_left.mp (hr ▸ hqr)
  have hsq:q*q∣f :=(hp.mul hp).dvd_of_fraction_map_dvd_fraction_map (K:=F)
    (by rw [zNl]; exact (mul_dvd_mul hqg hqg).trans hg)
  have hr0:r≠0:= by
    intro h
    rw [h,Polynomial.map_zero] at hr
    exact (mul_ne_zero ha'.ne_zero hg0) hr.symm
  have hu:IsUnit (r.map ι) := by
    rw [r.eq_C_content_mul_primPart,zNl,Polynomial.map_C]
    exact ((IsUnit.mk0 _ ((map_ne_zero_iff ι (zxb R F)).mpr
      (content_eq_zero_iff.not.mpr hr0))).map C).mul
        ((hf q hsq).map (Polynomial.mapRingHom ι))
  exact isUnit_of_mul_isUnit_right (hr ▸ hu)
private theorem separable_of_squarefree_small {F:Type} [Field F] [CharP F p]
   (f :F[X]) (hf :Squarefree f) (hd:f.natDegree<p) :f.Separable := by
 rw [separable_def,← isRelPrime_iff_isCoprime]
 apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors (fun h=>hf.ne_zero h.1)
 intro g hg hgf hgd
 obtain ⟨q,hq⟩:=hgf
 have hq' : ¬ g∣q:= by
   intro h
   exact hg.not_isUnit (hf g (hq ▸ mul_dvd_mul_left g h))
 have hprime :Prime g:=UniqueFactorizationMonoid.irreducible_iff_prime.mp hg
 rw [hq,derivative_mul] at hgd
 have hdiv :g∣g.derivative*q:= by
   simpa only [add_sub_cancel_right] using dvd_sub hgd (dvd_mul_right g q.derivative)
 have hgdeg:0<g.natDegree := by
   by_contra! h
   have hz :g.natDegree=0:=Nat.eq_zero_of_le_zero h
   have hc:g.coeff 0≠0:= by
     rw [← hz,coeff_natDegree]
     exact leadingCoeff_ne_zero.mpr hg.ne_zero
   exact hg.not_isUnit ((eq_C_of_natDegree_eq_zero hz) ▸ (IsUnit.mk0 _ hc).map C)
 exact b0u g hgdeg ((natDegree_le_of_dvd ⟨q,hq⟩ hf.ne_zero).trans_lt hd)
   ((hprime.dvd_mul.mp hdiv).resolve_right hq')
private theorem squarefree_equiv {R S:Type} [Monoid R] [Monoid S]
  (e :R ≃* S) {f :R} (hf :Squarefree f) :Squarefree (e f) := by
 intro q hq
 have h:=map_dvd e.symm hq
 rw [map_mul,MulEquiv.symm_apply_apply] at h
 simpa only [MulEquiv.apply_symm_apply] using (hf _ h).map e
private theorem map_cut_ne {R S:Type} [CommRing R] [CommRing S] [IsDomain S]
  [IsGCDMonoid S] [CharP S p] (ι:R →+* S) (hi:Function.Injective ι)
  (f :R[X]) (hs :Squarefree (f.map ι)) (hd:f.natDegree<p) :
  f.resultant f.derivative f.natDegree (f.natDegree - 1)≠0:= by
 let F:=FractionRing S
 let φ:=algebraMap S F
 let:CharP F p:=charP_of_injective_ringHom (zxb S F) p
 have hdeg: ((f.map ι).map φ).natDegree<p:= by
  rw [natDegree_map_eq_of_injective (zxb S F),natDegree_map_eq_of_injective hi]
  exact hd
 have hsep:=separable_of_squarefree_small ((f.map ι).map φ) (squarefree_fraction _ hs) hdeg
 have hn:=resultant_derivative_ne_zero_of_separable_map_fractionField (K:=F) (f.map ι) hsep
 rw [natDegree_map_eq_of_injective hi,derivative_map,resultant_map_map] at hn
 exact fun h=>hn (by rw [h,map_zero])
private theorem coefficient_zero_ne {R:Type} [Semiring R]
  (f :R[X]) (hf :f≠0) (hz :f.natDegree=0) :f.coeff 0≠0:= by
 simpa only [leadingCoeff,hz] using leadingCoeff_ne_zero.mpr hf
end
end qwWTALb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qkLbbMe
noncomputable section
open Polynomial Finset PolynomialDifferential
open P5 (K)
open P5_7_1 (atTop)

open cu (L FX j9 kr)
open scoped Classical
open private aQw from ProximityPrize.SubmissionLower.BG
local notation "D" => P5_7_1.degree
abbrev af :=z3y (Fin 2) L[X]
abbrev flatten:=ana.flatten
def keep (i:Fin 2) :Fin 4 :=i.succ.castSucc
theorem solves (B:af) (S:K[X])
   (h:atTop (zHw keep B) 0 S=0) :
   differentialSpecialization (flatten B) (j9 S)=0:= by
 rw [aQw,aR.cK]
 apply (zxb L[X] FX)
 change (algebraMap L[X] FX) (MvPolynomial.eval₂ (RingHom.id _) _ B)= _
 rw [map_zero,MvPolynomial.hom_eval₂,RingHom.comp_id]
 rw [atTop,MvPolynomial.eval₂_rename] at h
 convert h using 2
 funext i
 fin_cases i
 · simp only [z3s,keep,aR.jet,hasseDeriv_zero']
   rfl
 · simp only [z3s,keep,aR.jet,hasseDeriv_one']
   change (algebraMap L[X] FX) (j9 S).derivative=kr S.derivative
   rw [j9,derivative_map]
   rfl
end
end qkLbbMe
end
