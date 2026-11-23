import ProximityPrize.SubmissionLower.ZO7Azpb
import ProximityPrize.SubmissionLower.ZOb5aoe
import ProximityPrize.SubmissionLower.ZPiv0na
import ProximityPrize.SubmissionLower.ZwtWMfa
import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZGDv7Ub
set_option Elab.async false
section
namespace qrU3rOc
noncomputable section
open Polynomial TrivSqZeroExt
open qb0hmCe (cLN specialize zD)
open q82zwcd (DualSheet)
open qwGrtCa (transform transform_sum)
open qFe6O4d
open q1kuFjb (IntSeries Ua mapTwice map_liftAt)
open qbnx7gb (targetA targetB)
open qxDtRld (Go nY resA resB markP markQ mark_zero correction)
open qJai0ob (pair scalar seriesJet evalAt eval_seriesJet)
open P5_7_7 (phys)
open cu (L FX)
open private constant τ center center_poly jet_constant jet_linear from ProximityPrize.SubmissionLower.ZFdiUYb
open scoped Classical WithZero
private theorem phys_ne {g:L[X]} (h:g≠0) :phys g≠0 :=
 (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr h
private theorem scaled_change {E :Type} [Field E] (u t A B x :E)
   (n:ℕ) (f :E[X][X]) :
   transform (C t) (C A) 1 (C B) n ((nY u f).map (taylorAlgHom x).toRingHom) =
     nY u (transform (C t) (C A) 1 (C B) n (f.map (taylorAlgHom x).toRingHom)) := by
 have h: (nY u f).map (taylorAlgHom x).toRingHom =
     nY u (f.map (taylorAlgHom x).toRingHom) := by
   rw [show nY u f=C (C u)*f from rfl,Polynomial.map_mul,Polynomial.map_C]
   change C (taylor x (C u))*_ = _
   rw [taylor_C]
 rw [h]
 simp only [nY,transform_sum,coeff_C_mul,C_mul,Finset.mul_sum,mul_assoc]
private theorem lift_congr {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) {f g:E[X][X]} (h:f=g) (hf hg) :
  Ua a f hf=Ua a g hg:= by
 subst g
 rfl
theorem proof :qxDtRld.c2 := by
  intro D₀ word U s z q J F V R t ht γ hγ hr
  have hU:=(Finset.mem_filter.mp (V.Bp hγ)).1
  let a :=F.atPlace γ hU
  let c:F.curve.E :=F.scale γ
  let f :=nY c F.f
  let G:=nY c (Go F R t)
  let P:=markP J R z γ
  let Q:=markQ J R t γ
  change specialize (cLN a 0 G) P Q=0 ∧
    specialize (cLN a 0 G).derivative P Q≠0 ∧
    zD a G P Q =
      phys (C (t*resB R z γ - resA R z γ)) *
        (phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ))) +
      phys (correction F R t γ)
  let hG i j:=(F.value γ hU ((G.coeff i).coeff j)).symm.trans_le
    (show (F.place γ).value ((G.coeff i).coeff j)≤1 by
      simpa only [Nat.cast_zero,WithZero.exp_zero] using ht.integral γ hγ hr i j)
  let hf i j:=(F.value γ hU ((f.coeff i).coeff j)).symm.trans_le
    (show (F.place γ).value ((f.coeff i).coeff j)≤1 by
      simpa only [f,nY,coeff_C_mul] using F.integral γ hU i j)
  let p₀:=phys (taylor R.center (J.P γ))
  let q₀:=phys (taylor R.center (J.Q γ))
  let a₀:=scalar (resA R z γ)
  let b₀:=scalar (resB R z γ)
  let a₁:=scalar (R.b*F.direction γ R.coord)
  let b₁:=scalar (R.d*F.direction γ R.coord)
  let T:=scalar t
  let m:=T*q₀-p₀
  let D:=T*b₀-a₀
  let k :=(b₁*p₀-a₁*q₀)*m
  let w:=(b₀*p₀-a₀*q₀)/m
  let y :=p₀/q₀
  have hq:q₀≠0 :=
    phys_ne (fun h=>J.denominator γ hU ((taylor_eq_zero R.center _).mp h))
  have hM:phys Q=m:= by
    simp only [Q,markQ,m,T,p₀,q₀,scalar,RingHom.comp_apply,map_mul,map_sub]
  have hP:phys P=b₀*p₀-a₀*q₀:= by
    simp only [P,markP,a₀,b₀,p₀,q₀,scalar,RingHom.comp_apply,map_mul,map_sub]
  have hm:m≠0:=hM ▸ phys_ne (fun h=>(mark_zero ht hγ hr).2
    (by change Q.coeff 0=0; rw [h,coeff_zero]))
  have hDmap :phys (C (t*resB R z γ-resA R z γ))=D:= by
    simp only [D,a₀,b₀,T,← map_mul,← map_sub,scalar,RingHom.comp_apply]
  have hD:D ≠0:=hDmap ▸ phys_ne (C_ne_zero.mpr (ht.avoids γ hγ hr))
  have hz :b₀+w≠0:= by
    change b₀+(b₀*p₀-a₀*q₀)/(T*q₀-p₀)≠0
    rw [change_denominator p₀ q₀ a₀ b₀ T hm]
    exact div_ne_zero (mul_ne_zero hD hq) hm
  obtain ⟨g,hg,hg₀,_⟩:=F.arc γ hU
  have hg₁ :PowerSeries.coeff 1 (g R.coord)=F.direction γ R.coord:= by
    rw [DualSheet.direction,dite_eq_left hU,hg]
    exact (LaurentSeries.coeff_coe_powerSeries (g R.coord) 1).symm
  let g' := (LaurentSeries.powerSeriesEquivSubring L) (g R.coord)
  let A:=constant R.a+constant R.b*g'
  let B:=constant R.c+constant R.d*g'
  have hA: (A:LaurentSeries L)=a (targetA F.curve R) := by
    simp only [A,g',targetA,Subring.coe_add,Subring.coe_mul,constant_coe a,
      LaurentSeries.powerSeriesEquivSubring_coe_apply,a,hg,map_add,map_mul]
  have hB: (B:LaurentSeries L)=a (targetB F.curve R) := by
    simp only [B,g',targetB,Subring.coe_add,Subring.coe_mul,constant_coe a,
      LaurentSeries.powerSeriesEquivSubring_coe_apply,a,hg,map_add,map_mul]
  have hAj:seriesJet A=pair a₀ a₁:= by
    simpa only [A,g',a₀,a₁,resA,hg₀,hg₁] using jet_linear (g R.coord) R.a R.b
  have hBj:seriesJet B=pair b₀ b₁:= by
    simpa only [B,g',b₀,b₁,resB,hg₀,hg₁] using jet_linear (g R.coord) R.c R.d
  let x :=algebraMap L F.curve.E R.center
  let t' := algebraMap L F.curve.E t
  have hchart:transform (C t') (C (targetA F.curve R)) 1 (C (targetB F.curve R))
      F.d (f.map (taylorAlgHom x).toRingHom)=G :=
    scaled_change c t' (targetA F.curve R) (targetB F.curve R) x F.d F.f
  have hLift₀:=lift_change a f hf x t' (targetA F.curve R) (targetB F.curve R)
    (constant R.center) (constant t) A B F.d
    (constant_coe a _) (constant_coe a _) hA hB (hchart.symm ▸ hG)
  have hLift:=(lift_congr a hchart _ hG).symm.trans hLift₀
  have hfd:f.natDegree=F.d :=
    natDegree_C_mul (C_ne_zero.mpr (Units.ne_zero (F.scale γ)))
  have hdeg: (Ua a f hf).natDegree≤F.d:= by
    have hi:=Polynomial.map_injective (f :=IntSeries.subtype) Subtype.val_injective
    have h:=natDegree_map_eq_of_injective (f :=mapRingHom IntSeries.subtype) hi (Ua a f hf)
    change (mapTwice IntSeries.subtype (Ua a f hf)).natDegree= _ at h
    rw [map_liftAt] at h
    rw [← h,← hfd]
    exact natDegree_map_le
  let ev₀:=eval₂RingHom scalar (τ+scalar R.center)
  let J₀ (i:ℤ) :=(cLN a i f).eval₂ ev₀ y
  let j:=(cLN a 0 f).derivative.eval₂ ev₀ y
  let ev₁:=eval₂RingHom scalar τ
  let I₀ (i:ℤ) :=(cLN a i G).eval₂ ev₁ w
  let i:=(cLN a 0 G).derivative.eval₂ ev₁ w
  let φ:=phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ))
  have hj₀:J₀ 0=0:= by
    simpa only [J₀,a,ev₀,y,p₀,q₀,center_specialize,map_zero] using
      congrArg (center R.center) (F.root γ hU)
  have hj:j≠0:= by
    simpa only [j,a,ev₀,y,p₀,q₀,center_specialize,map_zero] using
      (center R.center).injective.ne (V.simple γ hγ)
  have hφ:φ = -(J₀ 1/j)*q₀^2 := by
    simpa only [φ,a,J₀,j,ev₀,y,p₀,q₀,zD,map_mul,map_neg,map_div₀,map_pow,
      center_poly,center_specialize] using congrArg (center R.center) (V.formula γ hγ)
  have he (u:FX) :
      pair (I₀ 0) (I₀ 1+u*i) =
        (pair b₀ b₁+pair w u)^F.d*pair 0 (J₀ 1+((m^2*u-k)/(D*q₀^2))*j) := by
    let W:=pair w u
    let Y' := pair y ((m^2*u-k)/(D*q₀^2))
    have h:=parameter_change p₀ q₀ a₀ b₀ a₁ b₁ T u hq hm hD
    have heval :seriesJet A+seriesJet (constant t)*W=(seriesJet B+W)*Y' := by
      rw [hAj,hBj,jet_constant]
      exact h
    have h' := congrArg (evalAt seriesJet (inl τ) W) hLift
    change evalAt seriesJet (inl τ) W (Ua a G hG)= _ at h'
    rw [eval_change seriesJet (inl τ) W Y' _ hdeg _ _ _ _ heval,
      jet_constant,← inl_add] at h'
    dsimp only [W,Y'] at h'
    rw [eval_seriesJet,eval_seriesJet,hBj] at h'
    change pair (I₀ 0) (I₀ 1+u*i) =
      (pair b₀ b₁+pair w u)^F.d*pair (J₀ 0) (J₀ 1+((m^2*u-k)/(D*q₀^2))*j) at h'
    simpa only [hj₀] using h'
  obtain ⟨hi₀,hi,htan⟩:=first_order F.d b₀ b₁ w q₀ m D k φ (J₀ 1) j (I₀ 0) (I₀ 1) i
    hz hq hm hD hj hφ he
  have hw:w=phys P/phys Q:= by rw [hP,hM]
  have hk :phys (correction F R t γ)=k := by
    dsimp only [correction,k,a₁,b₁,p₀,q₀]
    rw [map_mul,map_mul,map_sub,map_mul,map_mul,hM]
    simp only [map_mul,scalar,RingHom.comp_apply]
    ring
  refine ⟨?_,?_,?_⟩
  · simpa only [I₀,ev₁,eval_phys,hw,specialize] using hi₀
  · simpa only [i,ev₁,eval_phys,hw,specialize] using hi
  · simpa only [i,I₀,φ,ev₁,eval_phys,hw,← hM,← hDmap,← hk,zD,specialize] using htan
end
end qrU3rOc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qYbkOtc
noncomputable section
open Polynomial
open cu (L)
open P5 (K p)
open q2TwyLa (i5 aQ PhysicalField ek)
open qJFdYUc (generic_inj)
open qziIa4d (seedDerivative)
open qnyP9Da (PowerExpansion LX seedField a8p seed_derivation frobRoot)
open private btE from ProximityPrize.SubmissionLower.ZPiv0na
open private diff coeff_diff lift_poly implicit_eq derive_sum from ProximityPrize.SubmissionLower.Z3PNGOd
open scoped WithZero
private theorem derivative_bound {n:ℕ} (hp:n.Prime) {A M Γ:Type} [Field A] [Field M]
   [CharP M n] [LinearOrderedCommGroupWithZero Γ] (v :Valuation M Γ)
   (ι:A[X] →+* M) (F:Subfield M) (π:A) (d:A→A) (hd0:d 0=0)
   (hexp:PowerExpansion n π d) (hpow : ∀ a :A,ι (C (a^n))∈F)
   (hphys :ι Polynomial.X∈F) (hnot:ι (C π)∉F) (hs :v (ι (C π))=1)
   (G:A[X][X]) (r :M) (hr :G.eval₂ ι r=0) (hsep:G.derivative.eval₂ ι r≠0)
   (b:Fin n→F) (hb:r = ∑ i,(b i:M)*(ι (C π))^(i:ℕ))
   (hcoeff : ∀ i,v (b i:M)≤v r) :
   v (-((diff (diff d) G).eval₂ ι r/G.derivative.eval₂ ι r))≤v r := by
 let s :=ι (C π)
 let E :=seedField F s
 let t:E :=a8p F s
 let σ:E →+* M:=E.val.toRingHom
 let f :F →+* E :=algebraMap F E
 have hsp:s^n∈F:= by simpa only [s,map_pow] using hpow π
 obtain ⟨D,hD⟩:=seed_derivation hp F s hnot hsp
 have hσf (u:F) :σ (f u)=(u:M) :=rfl
 have hσt:σ t=s :=rfl
 obtain ⟨j,hj,hdiff⟩:=lift_poly F ι π d hd0 hexp hpow hphys E t hσt D hD
 let a :E := ∑ i,f (b i)*t^(i:ℕ)
 have ha :σ a=r := by
   simpa only [a,map_sum,map_mul,map_pow,hσf,hσt,s] using hb.symm
 have hq:=implicit_eq D σ j a G (diff (diff d) G) r ι hj ha hr hsep (fun i=> by
   rw [coeff_diff (diff d) (by simp [diff])]
   exact hdiff _)
 have hnat (k :ℕ) :v (k :M)≤1 := by
   induction k with
   | zero=>simp
   | succ k ih =>
     rw [Nat.cast_succ]
     exact v.map_add_le ih (by rw [map_one])
 rw [← neg_div,← hq]
 dsimp only [a]
 rw [derive_sum D t hD,map_sum]
 apply v.map_sum_le
 intro i _
 simp only [map_mul,map_pow,map_natCast]
 change v (b i:M)*v ((i:ℕ) :M)*v (ι (C π))^((i:ℕ)-1)≤v r
 rw [hs,one_pow,mul_one]
 exact (mul_le_of_le_one_right' (hnat i)).trans (hcoeff i)
private theorem tangent_le {M Γ:Type} [Field M] [LinearOrderedCommGroupWithZero Γ]
  (v :Valuation M Γ) (ι:aQ[X] →+* M) (hi:Function.Injective ι)
  (hc : ∀ a :aQ,a≠0→v (ι (C a))=1) (hx :v (ι Polynomial.X)<1)
  (G:aQ[X][X]) (r :M) (hG:G≠0) (hd:G.natDegree<p)
  (hr :G.eval₂ ι r=0) (hsep:G.derivative.eval₂ ι r≠0) :
  v (-((seedDerivative G).eval₂ ι r/G.derivative.eval₂ ι r))≤v r := by
 let Kw:=qaUrXTd.Kw
 obtain ⟨hfin,hdim,b,hb⟩:=qaUrXTd.roots Kw ι hi G r hG hd hr
 obtain ⟨hnot,horth⟩:=qitLgnc.orthogonal v ι hi hc hx Kw.1
  (frobRoot ι r) hfin (hdim.trans_lt hd)
 let F:=(frobRoot ι r).toSubfield
 have hpow (a :aQ) :ι (C (a^p))∈F :=
  (frobRoot ι r).algebraMap_mem ⟨_,Subfield.subset_closure (Or.inl ⟨a,rfl⟩)⟩
 have hphys :ι Polynomial.X∈F :=
  (frobRoot ι r).algebraMap_mem ⟨_,Subfield.subset_closure (Or.inr rfl)⟩
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP M p :=
  charP_of_injective_ringHom ((ι.comp C).comp (algebraMap L aQ)).injective p
 have hs :v (ι (C LX))=1 :=hc _ (HahnSeries.single_ne_zero one_ne_zero)
 have hd0:LaurentSeries.derivative L (0:aQ)=0:=map_zero _
 exact derivative_bound KoalaBear.is_prime v ι F LX _ hd0 Kw.2 hpow hphys hnot hs
  G r hr hsep b hb (fun i=>(horth b i).trans_eq (congrArg v hb.symm))
private theorem tame :q2TwyLa.c1 := by
  intro f hpos hdeg hpolar
  let j:aQ[X] →+* PhysicalField:=algebraMap _ _
  let m:i5[X] →+* aQ[X] :=mapRingHom (algebraMap i5 aQ)
  let G:=f.map m
  let H :=f.map ek
  let S:=H.SplittingField
  let k :PhysicalField →+* S:=algebraMap _ _
  let ι:=k.comp j
  let e :=k.comp ek
  let Q:=f.map e
  have hi:=k.injective.comp (Polynomial.algebraMap_hahnSeries_injective ℤ)
  have he :=k.injective.comp generic_inj
  have hQ:Q=H.map k :=(Polynomial.map_map _ _ _).symm
  have hm:ι.comp m=e :=rfl
  have hs :Q.Splits :=hQ ▸ (SplittingField.splits H)
  obtain ⟨A,hA⟩:=btE k
  refine ⟨{ S:=S,incl:=k,place :=A,restricts :=hA,splits :=hs,tame := ?_ }⟩
  intro r hr
  change r∈Q.roots at hr
  have hdQ:Q.natDegree=f.natDegree :=natDegree_map_eq_of_injective he _
  have hposQ:0<Q.natDegree :=hdQ.symm ▸ hpos
  have hrQ:Q.eval r=0:=(mem_roots (ne_zero_of_natDegree_gt hposQ)).mp hr
  have hsepQ:Q.derivative.eval r≠0:= by
    intro hz
    have hp:Q.resultant Q.derivative Q.natDegree (Q.natDegree-1)≠0:= by
      dsimp only [Q]
      rw [derivative_map,resultant_map_map,hdQ]
      exact (map_ne_zero_iff e he).mpr hpolar
    apply hp
    rw [resultant_eq_prod_eval _ _ _ (natDegree_derivative_le _) hs,mul_eq_zero]
    exact Or.inr (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨r,hr,hz⟩))
  have hdG:G.natDegree=f.natDegree :=natDegree_map_eq_of_injective
    (Polynomial.map_injective _ HahnSeries.ofPowerSeries_injective) _
  let v :=A.valuation
  let w:Valuation PhysicalField ℤᵐ⁰:=Valued.v
  have hv : (v.comap k).IsEquiv w:=Valuation.isEquiv_of_val_le_one fun x =>
    (A.valuation_le_one_iff _).trans (hA x)
  have hle (b:aQ[X]) :w (j b)≤1 :=
    (LaurentSeries.val_le_one_iff_eq_coe aQ _).mpr ⟨(b:PowerSeries aQ),
      (Polynomial.algebraMap_hahnSeries_apply ℤ b).symm⟩
  have hc (b:aQ) (hb:b≠0) :v (ι (C b))=1 := by
    apply (Valuation.isEquiv_iff_val_eq_one.mp hv).mpr
    change w (j (C b))=1
    refine le_antisymm (hle _) ?_
    calc
      1=w (j (C b))*w (j (C b⁻¹)) := by
        rw [← map_mul,← map_mul,← C_mul,mul_inv_cancel₀ hb,map_one,map_one,map_one]
      _≤w (j (C b)) :=mul_le_of_le_one_right' (hle _)
  have hx :v (ι Polynomial.X)<1 := by
    apply hv.lt_one_iff_lt_one.mpr
    change w (j Polynomial.X)<1
    rw [Polynomial.algebraMap_hahnSeries_apply,Polynomial.coe_X,HahnSeries.ofPowerSeries_X,
      LaurentSeries.valuation_single_zpow]
    exact WithZero.exp_lt_one_iff.mpr (by decide : (-1 :ℤ)<0)
  have hrG:G.eval₂ ι r=0:= by
    simpa only [Q,G,eval_map,eval₂_map,hm] using hrQ
  have hsepG:G.derivative.eval₂ ι r≠0:= by
    simp only [Q,derivative_map,eval_map] at hsepQ
    simpa only [G,derivative_map,eval₂_map,hm] using hsepQ
  have hdiff :seedDerivative G=(q2TwyLa.diff f).map m :=
    (qU1uHGd.diff_embed f).symm
  have h:=tangent_le v ι hi hc hx G r (ne_zero_of_natDegree_gt (hdG.symm ▸ hpos))
    (hdG.symm ▸ hdeg) hrG hsepG
  simpa only [hdiff,G,derivative_map,eval₂_map,hm] using h
theorem proof :qxDtRld.c3 :=
 q2TwyLa.of_children tame qJFdYUc.proof
end
end qYbkOtc
end
