import ProximityPrize.SubmissionLower.ZR3mCBd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace qcuqT2c
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open P5_7_7 (Dg seedDerivative)
open qGnV2ac (EquationBounds coeff_seedDerivative)
open qbjv5ec
open scoped WithZero nonZeroDivisors
def c1 :Prop :=
  ∀ y :EC,IsSeparable lN y →
    ∀ (x :L) (a :Simple y),∃ c:Fin p→Fin p→Simple y,
      a = ∑ j,∑ i,c j i^p*zIn y ^(i:ℕ)*tIn y x^(j:ℕ)
def c2 :Prop :=
  ∀ {E :Type} [Field E] [CharP E p] (v :Valuation E ℤᵐ⁰) {z t:E},
    TamePlace v z t → ∀ (c:Fin p→Fin p→E) (i j:Fin p),
      v (c j i^p*z^(i:ℕ)*t^(j:ℕ)) ≤
        v (∑ j,∑ i,c j i^p*z^(i:ℕ)*t^(j:ℕ))
def c3:Prop :=
  ∀ (y :EC),IsSeparable lN y→Module.finrank lN (Simple y)<p →
    ∀ (x :L) (a :Simple y),
      (∀ v :Valuation (Simple y) ℤᵐ⁰,TamePlace v (zIn y) (tIn y x)→v a≤1) →
      IsIntegral (NodeRing x) a
private def swapped:Dg ≃+* Dg :=
 Polynomial.mapEquiv Bivariate.swap.toRingEquiv
section Generic
local instance coeffAlgebra :Algebra Coeff aQ[X] :=Polynomial.algebra L[X] aQ
local instance genericAlgebra :Algebra Coeff lN :=
 ((algebraMap aQ[X] lN).comp (algebraMap Coeff aQ[X])).toAlgebra
private theorem genericAlgebra_eq :
 algebraMap Coeff lN =
  (algebraMap aQ[X] lN).comp (algebraMap Coeff aQ[X]) :=rfl
set_option backward.isDefEq.respectTransparency true in
local instance : @IsScalarTower Coeff aQ[X] lN coeffAlgebra.toSMul
   (inferInstance :Algebra aQ[X] lN).toSMul genericAlgebra.toSMul :=
 @IsScalarTower.of_algebraMap_eq' Coeff aQ[X] lN _ _ _ coeffAlgebra
   (inferInstance :Algebra aQ[X] lN) genericAlgebra genericAlgebra_eq
local instance :IsFractionRing Coeff lN := by
  let M:=(L[X]⁰).map (C:L[X] →+* Coeff)
  have :IsLocalization M aQ[X] :=Polynomial.isLocalization (L[X]⁰) aQ
  have hi:Function.Injective (algebraMap Coeff aQ[X]) :=
    Polynomial.map_injective _ (IsFractionRing.injective L[X] aQ)
  have he : (aQ[X]⁰).comap (algebraMap Coeff aQ[X])=Coeff⁰:= by
    ext q
    rw [Submonoid.mem_comap,mem_nonZeroDivisors_iff_ne_zero,
      mem_nonZeroDivisors_iff_ne_zero,map_ne_zero_iff _ hi]
  rw [IsFractionRing,← he]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (aQ[X]⁰) lN (fun _ h=>h.mem_nonZeroDivisors)
private theorem generic_data {F:Dg} {l h:ℕ} (H :EquationBounds F l h) :
  Irreducible (F.map qY)∧(F.map qY).natDegree=l:= by
 have hi:Irreducible (swapped F) :=
  (MulEquiv.irreducible_iff swapped.toMulEquiv).mpr H.irreducible
 have hd: (swapped F).natDegree=l :=
  (natDegree_map_eq_of_injective Bivariate.swap.injective _).trans H.jU
 have hl:l≠0:= by have :=H.two_le; omega
 have he : (swapped F).map (algebraMap Coeff lN)=F.map qY :=
  Polynomial.map_map _ _ _
 rw [← he]
 exact ⟨((hi.isPrimitive (hd ▸ hl)).irreducible_iff_irreducible_map_fraction_map
  (K:=lN)).mp hi,
  (natDegree_map_eq_of_injective (IsFractionRing.injective Coeff lN) _).trans hd⟩
end Generic
private theorem aNu {R E :Type} [CommRing R] [Field E] (D:Derivation ℤ E E)
   (f :R →+* E) (a :E) (P Q:R[X])
   (hc : ∀ i,D (f (P.coeff i))=f (Q.coeff i)) :
   D (P.eval₂ f a)= Q.eval₂ f a+P.derivative.eval₂ f a*D a := by
 let n:=max P.natDegree Q.natDegree+1
 have hP:P.natDegree<n:=Nat.lt_succ_of_le (le_max_left _ _)
 have hQ:Q.natDegree<n:=Nat.lt_succ_of_le (le_max_right _ _)
 have hd:P.derivative.eval₂ f a =
     ∑ i∈Finset.range n,f (P.coeff i)*(i:E)*a^(i-1) := by
   simp_rw [derivative_apply,eval₂_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_mul,map_natCast]
   exact P.sum_over_range' (fun i=> by simp) n hP
 rw [eval₂_eq_sum_range' f hP,eval₂_eq_sum_range' f hQ,hd,map_sum,
   Finset.sum_mul,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i _
 rw [D.leibniz,D.leibniz_pow,hc]
 simp only [smul_eq_mul,nsmul_eq_mul]
 ring
private def physHom:L[X] →+* lN :=
 (algebraMap aQ[X] lN).comp (mapRingHom ((algebraMap L[X] aQ).comp C))
private theorem coeff_eval :qY=eval₂RingHom physHom seed := by
 apply Polynomial.ringHom_ext
 · intro a
   simp [qY,physHom,Bivariate.swap_C,map_map]
 · simp [qY,seed,Bivariate.swap_Y]
private def coeffIn (y :EC) :Coeff →+* Simple y :=
 (algebraMap lN (Simple y)).comp qY
private theorem derive_phys (y :EC) (D:Derivation ℤ (Simple y) (Simple y))
   (hc : ∀ a,D (cIn y a)=0) (hx :D (xIn y)=0) (b:L[X]) :
   D ((algebraMap lN (Simple y)).comp physHom b)=0:= by
 let m:L →+* Simple y :=(algebraMap lN (Simple y)).comp
   (physHom.comp (C:L →+* L[X]))
 have hr : (algebraMap lN (Simple y)).comp physHom=eval₂RingHom m (xIn y) := by
   apply Polynomial.ringHom_ext
   · intro a
     simp [m]
   · simp [physHom,amm]
 rw [hr,coe_eval₂RingHom,aNu D m (xIn y) b 0]
 · simp [hx]
 · intro i
   simpa [m,cIn,constant,physHom] using hc (b.coeff i)
private theorem derive_coeff (y :EC) (D:Derivation ℤ (Simple y) (Simple y))
   (hc : ∀ a,D (cIn y a)=0) (hx :D (xIn y)=0) (hz :D (zIn y)=1)
   (b:Coeff) :D (coeffIn y b)=coeffIn y b.derivative := by
 let m:=(algebraMap lN (Simple y)).comp physHom
 have hr :coeffIn y=eval₂RingHom m (zIn y) := by
   unfold coeffIn
   rw [coeff_eval]
   apply RingHom.ext
   intro b
   exact hom_eval₂ b physHom (algebraMap lN (Simple y)) seed
 rw [hr]
 simp only [coe_eval₂RingHom]
 rw [aNu D m (zIn y) b 0]
 · simp [hz]
 · intro i
   simpa only [coeff_zero,map_zero] using derive_phys y D hc hx (b.coeff i)
private theorem derive_order (orthogonal:c2) {E :Type} [Field E] [CharP E p]
   (D:Derivation ℤ E E) (v :Valuation E ℤᵐ⁰) {z t a :E}
   (hv :TamePlace v z t) (hz :D z=1) (ht:D t=0)
   (c:Fin p→Fin p→E)
   (ha :a = ∑ j,∑ i,c j i^p*z^(i:ℕ)*t^(j:ℕ)) :
   v (D a)≤v a := by
 have hpow (b:E) :D (b^p)=0:= by
   rw [D.leibniz_pow,← Nat.cast_smul_eq_nsmul E,CharP.cast_eq_zero,zero_smul]
 have hn (n:ℕ) :v (n:E)≤1 := by
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [Nat.cast_succ]
     exact (v.map_add _ _).trans (max_le ih (by rw [map_one]))
 rw [ha,map_sum]
 apply v.map_sum_le
 intro j _
 rw [map_sum]
 apply v.map_sum_le
 intro i _
 refine le_trans ?_ (orthogonal v hv c i j)
 have hterm :D (c j i^p*z^(i:ℕ)*t^(j:ℕ)) =
     (c j i^p*((i:ℕ) :E)*z^((i:ℕ)-1))*t^(j:ℕ) := by
   simp only [D.leibniz,D.leibniz_pow t,D.leibniz_pow z,hpow,ht,hz,
     smul_eq_mul,nsmul_eq_mul,mul_one,mul_zero,add_zero,zero_add]
   ring
 rw [hterm]
 simp only [map_mul,map_pow,hv.seed_unit,one_pow,mul_one]
 simpa only [mul_one] using
   mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left (hn (i:ℕ)) (show 0≤v (c j i)^p from zero_le))
     (show 0≤v t^(j:ℕ) from zero_le)
private theorem root_data {F:Dg} {l h:ℕ} (H :EquationBounds F l h)
   {y :EC} (hy :cTD F y=0) :
   IsSeparable lN y∧Module.finrank lN (Simple y)=l ∧
     cTD F.derivative y≠0 ∧
     ∀ a :lN,y≠algebraMap lN EC a := by
 let G:=F.map qY
 obtain ⟨hi,hd⟩:=generic_data H
 have hroot :aeval y G=0:= by
   simpa only [G,aeval_def,eval₂_map,cTD] using hy
 let e :L →+* lN :=physHom.comp C
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP lN p:=charP_of_injective_ringHom e.injective p
 have hl:0<l:= by have :=H.two_le; omega
 have hcast: (l:lN)≠0:= fun he =>
   (not_le_of_gt H.tame) (Nat.le_of_dvd hl ((CharP.cast_eq_zero_iff _ p _).mp he))
 have hder :G.derivative≠0:= by
   intro hz
   have he :=coeff_derivative G (l-1)
   rw [hz,coeff_zero,← Nat.cast_succ,show (l-1).succ=l by omega] at he
   rw [show l-1+1=l by omega] at he
   have hc:G.coeff l≠0:=hd ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
   exact (mul_ne_zero hc hcast) he.symm
 have hs :G.Separable :=(separable_iff_derivative_ne_zero hi).mpr hder
 have hm: (minpoly lN y).natDegree=l:= by
   rw [← minpoly.eq_of_irreducible hi hroot,
     natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hi.ne_zero)),hd]
 refine ⟨hs.of_dvd (minpoly.dvd _ _ hroot),
   (IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y)).trans hm,?_,?_⟩
 · simpa only [G,derivative_map,aeval_def,eval₂_map,cTD]
     using hs.aeval_derivative_ne_zero hroot
 · intro a ha
   rw [ha,minpoly.eq_X_sub_C,natDegree_X_sub_C] at hm
   have :=H.two_le
   omega
theorem of_children (cLN :c1) (orthogonal:c2) (places :c3) :
   qbjv5ec.c1 := by
 intro F l h H x r y hy
 obtain ⟨hsep,hdeg,hder,hnr⟩:=root_data H hy
 let a :Simple y :=⟨y,IntermediateField.mem_adjoin_simple_self lN y⟩
 let A:=cIn y r
 let ev :Dg →+* Simple y :=eval₂RingHom (coeffIn y) a
 let ι:Simple y →+* EC:=(Simple y).val.toRingHom
 have he (Q:Dg) :ι (ev Q)=cTD Q y :=
   hom_eval₂ Q (coeffIn y) ι a
 have ha :a - A≠0:=sub_ne_zero.mpr
   (fun h=>hnr (constant r) (congrArg ι h))
 have hF:ev F=0:=ι.injective ((he F).trans (hy.trans (map_zero ι).symm))
 have hd:ev F.derivative≠0:= fun h=>hder ((he _).symm.trans ((congrArg ι h).trans (map_zero ι)))
 have hp:ev (polar F r)=(a-A)*ev F.derivative := by
   change ((Polynomial.X - C (C (C r)))*F.derivative).eval₂ (coeffIn y) a= _
   rw [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C]
   congr 2
   simp [coeffIn,qY,A,constant,Bivariate.swap_C_C]
 refine ⟨?_,?_⟩
 · rw [← he,hp]
   exact (map_ne_zero_iff _ ι.injective).2 (mul_ne_zero ha hd)
 obtain ⟨D,hc,hz,hx⟩:=exists_derivation y hsep
 have ht:D (tIn y x)=0:= by simp [hx,hc]
 have Hchain:ev (seedDerivative F)+ev F.derivative*D a=0:= by
   have hchain:=aNu D (coeffIn y) a F (seedDerivative F) (fun i=> by
     rw [coeff_seedDerivative]
     exact derive_coeff y D hc hx hz _)
   change D (ev F)=ev (seedDerivative F)+ev F.derivative*D a at hchain
   simpa only [hF,map_zero] using hchain.symm
 have hquot:ev (seedDerivative F)/ev (polar F r) = -(D (a-A))/(a-A) := by
   rw [hp,map_sub,show D A=0 from hc r,sub_zero]
   field_simp [ha,hd]
   linear_combination Hchain
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP (Simple y) p:=charP_of_injective_ringHom
   ((algebraMap lN (Simple y)).comp (physHom.comp C)).injective p
 have hi:IsIntegral (NodeRing x) (ev (seedDerivative F)/ev (polar F r)) := by
   rw [hquot]
   apply places y hsep (hdeg ▸ H.tame) x
   intro v hv
   obtain ⟨c,heq⟩:=cLN y hsep x (a-A)
   have hvle :=derive_order orthogonal D v hv hz ht c heq
   rw [map_div₀,v.map_neg]
   exact (div_le_one₀ (pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha))).2 hvle
 let:IsScalarTower (NodeRing x) (Simple y) EC :=
   IsScalarTower.of_algebraMap_eq (fun _=>rfl)
 have him:IsIntegral (NodeRing x) (ι (ev (seedDerivative F)/ev (polar F r))) :=
   hi.algebraMap
 simpa only [map_div₀,he] using him
end
end qcuqT2c
