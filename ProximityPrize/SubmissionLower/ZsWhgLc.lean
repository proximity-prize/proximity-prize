import ProximityPrize.SubmissionLower.Znkyowe
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, Nat.mul_le_mul_right → ztf, Polynomial.map_injective → zTo
namespace qGnV2ac
noncomputable section
open Polynomial Finset
open scoped Classical
open P5 (K I p)
open P5_7 (NativeSeedBound)
open P5_7_7
open cu (L FX jz)
open private c8H from ProximityPrize.SubmissionLower.ZmepBre
private theorem embed_coeff_degree (F:Dg) (i:ℕ) :
  ((embed F).coeff i).natDegree=(F.coeff i).natDegree := by
 simp only [embed,coe_mapRingHom,coeff_map,
  natDegree_map_eq_of_injective (zxb L[X] FX)]
private theorem embed_inj:Function.Injective embed :=
 zTo _ (zTo _ (zxb L[X] FX))
private theorem embed_degree (F:Dg) : (embed F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (zTo _ (zxb L[X] FX)) F
private theorem embed_bound (F:Dg) {h:ℕ} (hh : ∀ i,(F.coeff i).natDegree≤h) :
 NativeSeedBound (embed F) h:= fun i=>(embed_coeff_degree F i).trans_le (hh i)
private theorem ordinate_height {F:Dg} {h:ℕ}
  (hh : ∀ i,(F.coeff i).natDegree≤h) :
  NativeSeedBound (embed F.derivative) h:= by
 intro i
 rw [embed_coeff_degree,coeff_derivative,← Nat.cast_succ,← C_eq_natCast]
 exact (natDegree_mul_C_le _ _).trans (hh (i+1))
private theorem co6 {F:Dg} {h:ℕ}
  (hh : ∀ i,(F.coeff i).natDegree≤h) :
  NativeSeedBound (embed (seedDerivative F)) (h-1) := by
 intro i
 rw [embed_coeff_degree,coeff_seedDerivative]
 exact (natDegree_derivative_le _).trans (Nat.sub_le_sub_right (hh i) 1)
private theorem ordinate_nonzero {F:Dg} {l h:ℕ}
  (H :EquationBounds F l h) :F.derivative≠0:= by
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 have hpos :0<l:= by have :=H.two_le; omega
 have hc: (l:L[X][X])≠0:= fun h =>
  (not_le_of_gt H.tame) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff _ p _).mp h))
 intro hz
 have hh:=coeff_derivative F (l-1)
 have he :l-1+1=l:= by omega
 rw [hz,coeff_zero,← Nat.cast_succ,he,show (l-1).succ=l by omega] at hh
 have hn:F.coeff l≠0:= by
  rw [← H.jU]
  exact leadingCoeff_ne_zero.mpr H.irreducible.ne_zero
 exact (mul_eq_zero.mp hh.symm).elim hn hc
private theorem generic_embed_ne {F:Dg} (h:F≠0) :ek (embed F)≠0:= by
 change mapRingHom (algebraMap FX[X] (FractionRing FX[X])) (embed F)≠0
 exact (map_ne_zero_iff _ (zTo _ (zxb FX[X] _))).mpr
  ((map_ne_zero_iff _ embed_inj).mpr h)
private theorem generic_irred {F:Dg} (hi:Irreducible (embed F))
   (hdeg:0<F.natDegree) :Irreducible (ek (embed F)) :=
 ((hi.isPrimitive (by rw [embed_degree]; omega)).irreducible_iff_irreducible_map_fraction_map
   (K:=FractionRing FX[X])).mp hi
private theorem ordinate_coprime {F:Dg} {l h:ℕ}
  (H :EquationBounds F l h) (hi:Irreducible (embed F)) :
  IsCoprime (ek (embed F)) (ek (embed F.derivative)) := by
 have hl:0<F.natDegree := by rw [H.jU]; have :=H.two_le; omega
 apply (generic_irred hi hl).coprime_iff_not_dvd.mpr
 rintro ⟨q,hq⟩
 have hne :=generic_embed_ne (ordinate_nonzero H)
 have hn:q≠0:=right_ne_zero_of_mul (hq ▸ hne)
 have he (G:Dg) : (ek (embed G)).natDegree=G.natDegree :=
  (natDegree_map_eq_of_injective (zxb FX[X] _ ) _).trans (embed_degree G)
 have hd:=natDegree_mul (generic_embed_ne H.irreducible.ne_zero) hn
 rw [← hq,he,he] at hd
 have hlt:=natDegree_derivative_lt hl.ne'
 omega
private theorem seed_coprime {F:Dg} {l h:ℕ}
   (H :EquationBounds F l h) (hi:Irreducible (embed F)) :
   IsCoprime (ek (embed F)) (ek (embed (seedDerivative F))) := by
 have hl:0<F.natDegree := by rw [H.jU]; have :=H.two_le; omega
 apply (generic_irred hi hl).coprime_iff_not_dvd.mpr
 intro hf
 have hp:=hi.isPrimitive (by rw [embed_degree]; omega)
 obtain ⟨q,hq⟩:=hp.dvd_of_fraction_map_dvd_fraction_map hf
 have hne :embed (seedDerivative F)≠0:=(map_ne_zero_iff _ embed_inj).mpr H.moving
 have hn:q≠0:=right_ne_zero_of_mul (hq ▸ hne)
 let H₀:=gY (embed F)
 have hh₀ (i:ℕ) : (F.coeff i).natDegree≤H₀ :=
   (embed_coeff_degree F i).symm.trans_le ((bv9 _ _).mp le_rfl i)
 have hpos :0<H₀:= by
   by_contra! hz
   apply H.moving
   ext i
   rw [coeff_seedDerivative,coeff_zero,
     eq_C_of_natDegree_eq_zero ((hh₀ i).trans hz |> Nat.eq_zero_of_le_zero),derivative_C]
 have hlt:=(bv9 (embed (seedDerivative F)) (H₀-1)).mpr (co6 hh₀)
 rw [hq,acG hi.ne_zero hn] at hlt
 change H₀+gY q≤H₀-1 at hlt
 omega
private theorem ce1 {F G:Dg}
  (hc:IsCoprime (ek (embed F)) (ek (embed G))) :
  (embed F).resultant (embed G)≠0:= by
 have hi:=zxb FX[X] (FractionRing FX[X])
 unfold ek at hc
 have hne :=resultant_ne_zero _ _ hc
 rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,
  resultant_map_map] at hne
 exact fun h=>hne (by rw [h,map_zero])
private theorem resultant_at_common {F G:Dg} {l:ℕ}
  {h:ℕ} (H :EquationBounds F l h) {D:ℕ} {w:I→K} {U:Finset K}
  {S:K→K[X]} (J:DualWord D w U S) (z γ:K)
  (hf :atDual J F z γ=0) (hg:atDual J G z γ=0) :
  ((embed F).resultant (embed G)).eval (jz z)=0:= by
 have hpos :0<(embed F).natDegree := by
  rw [embed_degree,H.jU]
  have :=H.two_le
  omega
 obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant (embed F) (embed G)
  (le_refl _) (le_refl _) (Or.inl hpos.ne')
 have he :=congrArg (nativeEval z (dualValue J γ)) hab
 change nativeEval z (dualValue J γ) (embed F)=0 at hf
 change nativeEval z (dualValue J γ) (embed G)=0 at hg
 rw [map_add,map_mul,map_mul,hf,hg,zero_mul,zero_mul,zero_add] at he
 simpa only [nativeEval,coe_eval₂RingHom,eval₂_C,coe_evalRingHom] using he.symm
private theorem reduced_pair {v :FX} (hv :v≠0) :
    ∃ A B:L[X],A≠0∧B≠0∧IsCoprime A B∧phys A/phys B=v := by
  obtain ⟨P,Q,hreg,rfl⟩:=IsFractionRing.div_surjective L[X] v
  have hQ:Q≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hreg
  have hP:P≠0:= fun he=>hv (by simp [he])
  let g:=GCDMonoid.gcd P Q
  have hg:g≠0:=gcd_ne_zero_of_right hQ
  have he (A:L[X]) (ha :g∣A) :g*(A/g)=A:=EuclideanDomain.mul_div_cancel' hg ha
  refine ⟨P/g,Q/g,left_div_gcd_ne_zero hP,right_div_gcd_ne_zero hQ,
    isCoprime_div_gcd_div_gcd hQ,?_⟩
  unfold phys
  calc
    _=(algebraMap L[X] FX g*algebraMap L[X] FX (P/g)) /
        (algebraMap L[X] FX g*algebraMap L[X] FX (Q/g)) :=
      (mul_div_mul_left _ _ ((map_ne_zero_iff _ (zxb L[X] FX)).mpr hg)).symm
    _ = _:= by rw [← map_mul,← map_mul,he P (gcd_dvd_left _ _),he Q (gcd_dvd_right _ _)]
theorem choose_sections {D:ℕ} {w:I→K} {U T:Finset K}
   {S₀:K→K[X]} (J:DualWord D w U S₀) {z :K→K}
   {F:Dg} {l h:ℕ} (H :EquationBounds F l h)
   (hi:Irreducible (embed F)) (ht:T⊆U)
   (hz :Set.InjOn z (T:Set K))
   (hr : ∀ γ∈T,atDual J F (z γ) γ=0) :
   ∃ C:Sections F,C.CF⊆T∧(T \ C.CF).card≤exclusions l*h ∧
     C.seed=z∧C.P=J.P∧C.Q=J.Q:= by
 let Δ (G:Dg) :=(embed F).resultant (embed G)
 let bad (G:Dg) :=T.filter fun γ=>(Δ G).eval (jz (z γ))=0
 have hbad (G:Dg) (hd:G.natDegree≤l) (hb:NativeSeedBound (embed G) h)
     (hc:IsCoprime (ek (embed F)) (ek (embed G))) :
     (bad G).card≤l*h+l*h:= by
   refine (countRoots (bad G) (jz ∘ z)
     (seedEmbedding_injective.comp_injOn (hz.mono (filter_subset _ _)))
     (Δ G) (ce1 hc) (fun γ hγ=>(mem_filter.mp hγ).2)).trans
     ((c8H (embed_bound F H.height) hb).trans ?_)
   rw [embed_degree,embed_degree,H.jU]
   exact Nat.add_le_add_left (ztf _ hd) _
 let badY:=bad F.derivative
 let badZ:=bad (seedDerivative F)
 have hY:=hbad F.derivative ((natDegree_derivative_le _).trans (by rw [H.jU]; omega))
   (ordinate_height H.height) (ordinate_coprime H hi)
 have hZ:=hbad (seedDerivative F) (natDegree_le_iff_coeff_eq_zero.mpr fun i hg=> by
     rw [coeff_seedDerivative,coeff_eq_zero_of_natDegree_lt (H.jU.symm ▸ hg),derivative_zero])
   (fun i=>(co6 H.height i).trans (Nat.sub_le _ _)) (seed_coprime H hi)
 let good:=T \ (badY∪badZ)
 have hkept:good⊆T:=sdiff_subset
 have hout: (T \ good).card≤exclusions l*h:= calc
   _≤(badY∪badZ).card:=card_le_card (by
     intro γ hγ
     by_contra hm
     exact (mem_sdiff.mp hγ).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hγ).1,hm⟩))
   _≤badY.card+badZ.card:=card_union_le _ _
   _≤(l*h+l*h)+(l*h+l*h) :=Nat.add_le_add hY hZ
   _=(4*l)*h:= by ring
   _≤_:=ztf _ (by unfold exclusions; omega)
 have hyreg (γ:K) (hg:γ∈good) : (Δ F.derivative).eval (jz (z γ))≠0 :=
   fun he=>(mem_sdiff.mp hg).2 (mem_union_left _ (mem_filter.mpr ⟨hkept hg,he⟩))
 have hy (γ:K) (hg:γ∈good) :atDual J F.derivative (z γ) γ≠0 :=
   fun he=>hyreg γ hg (resultant_at_common H J _ _ (hr γ (hkept hg)) he)
 have hz' (γ:K) (hg:γ∈good) :atDual J (seedDerivative F) (z γ) γ≠0:= by
   intro he
   exact (mem_sdiff.mp hg).2 (mem_union_right _
     (mem_filter.mpr ⟨hkept hg,resultant_at_common H J _ _ (hr γ (hkept hg)) he⟩))
 have haq (γ:K) (hg:γ∈good) :zD F (z γ) (J.P γ) (J.Q γ)≠0 :=
   mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (hz' γ hg) (hy γ hg)))
     (pow_ne_zero _ ((map_ne_zero_iff phys (zxb L[X] FX)).mpr (J.denominator γ (ht (hkept hg)))))
 have hex : ∀ γ:K,∃ A B:L[X],γ∈good →
     A≠0∧B≠0∧IsCoprime A B∧phys A/phys B=zD F (z γ) (J.P γ) (J.Q γ) := by
   intro γ
   by_cases hg:γ∈good
   · obtain ⟨A,B,hv⟩:=reduced_pair (haq γ hg)
     exact ⟨A,B,fun _=>hv⟩
   · exact ⟨0,1,fun he=>(hg he).elim⟩
 choose A B hAB using hex
 exact ⟨{
   CF:=good
   seed :=z
   injective :=hz.mono hkept
   P:=J.P
   Q:=J.Q
   denominator := fun γ hg=>J.denominator γ (ht (hkept hg))
   coprime := fun γ hg=>J.coprime γ (ht (hkept hg))
   root := fun γ hg=>hr γ (hkept hg)
   regular_ordinate :=hyreg
   simple :=hy
   A:=A
   B:=B
   nonzero := fun γ hg=>(hAB γ hg).1
   pole_denominator := fun γ hg=>(hAB γ hg).2.1
   reduced:= fun γ hg=>(hAB γ hg).2.2.1
   formula := fun γ hg=>(hAB γ hg).2.2.2 },hkept,hout,rfl,rfl,rfl⟩
end
end qGnV2ac
