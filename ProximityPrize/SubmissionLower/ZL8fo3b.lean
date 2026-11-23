import Mathlib.RingTheory.Valuation.Extension
import ProximityPrize.SubmissionLower.Z8IF1id
import ProximityPrize.SubmissionLower.Z3PNGOd
import ProximityPrize.SubmissionLower.ZJbAGBd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Field → zrb, Function.Injective → zq4, IsScalarTower.algebraMap_apply → zG3, LinearIndependent → z14, MvPolynomial.eval → zY9, Nat.mul_le_mul_right → ztf, Polynomial.X → z7y, RingHom.comp_apply → zQb
section
namespace qitLgnc
noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators
theorem kummer_powers {A E :Type} [zrb A] [zrb E] [zZE A E]
   {q:ℕ} [CharP E q] (hq:q.Prime) (z :E) (a :A)
   (hpow:z^q=algebraMap A E a) (hn : ∀ b:A,algebraMap A E b≠z) :
   z14 A (fun i:Fin q=>z^(i:ℕ)) := by
 let:Fact q.Prime :=⟨hq⟩
 have hirr :Irreducible ((z7y:A[X])^q - C a) :=
   X_pow_sub_C_irreducible_of_prime hq (fun b hb=>hn b
     ((frobenius E q).injective (by simpa only [frobenius_def,← map_pow,hb] using hpow.symm)))
 have hmin:=minpoly.eq_of_irreducible_of_monic hirr
   (x :=z) (by simpa only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero] using hpow)
   (monic_X_pow_sub_C a hq.ne_zero)
 have hd: (minpoly A z).natDegree=q:= by rw [← hmin,natDegree_X_pow_sub_C]
 exact (linearIndependent_pow (K:=A) z).comp (Fin.cast hd.symm) (Fin.cast_injective _)
section Residues
variable {A E Γ:Type} [zrb A] [zrb E] [zZE A E]
 [LinearOrderedCommGroupWithZero Γ] (v :Valuation E Γ)
 (vA:Valuation A Γ) [Valuation.HasExtension vA v]
local notation "O" => Valuation.valuationSubring vA
local notation "V" => Valuation.valuationSubring v
theorem coeff_le_of_residue_independent {I:Type} [Fintype I] (x :I→V)
   (hx :z14 (ResidueField O) (fun j=>residue V (x j)))
   (b:I→A) (i:I) :
   v (algebraMap A E (b i))≤v (∑ j,algebraMap A E (b j)*(x j:E)) := by
 classical
 obtain ⟨k,_,hk⟩:=Finset.exists_max_image Finset.univ (fun j=>vA (b j))
   ⟨i,Finset.mem_univ i⟩
 have hmax (j:I) :v (algebraMap A E (b j))≤v (algebraMap A E (b k)) :=
   (Valuation.HasExtension.val_map_le_iff vA v _ _).mpr (hk j (Finset.mem_univ j))
 by_cases h0:b k=0
 · have hi:=hmax i
   rw [h0,map_zero,map_zero] at hi
   exact hi.trans zero_le
 let c (j:I) :O:=⟨b j/b k,by
   apply (Valuation.HasExtension.val_map_le_one_iff vA v _).mp
   rw [map_div₀,map_div₀,div_le_one₀ (pos_iff_ne_zero.mpr
     (v.ne_zero_iff.mpr ((map_ne_zero_iff _ (algebraMap A E).injective).mpr h0)))]
   exact hmax j⟩
 let s :V := ∑ j,algebraMap O V (c j)*x j
 have hc:c k=1 :=Subtype.ext (div_self h0)
 have hs :residue V s≠0:= by
   intro hz
   have h:=(Fintype.linearIndependent_iff.mp hx) (fun j=>residue O (c j)) ?_ k
   · exact one_ne_zero (by simpa only [hc,map_one] using h)
   · simpa only [s,map_sum,map_mul,Algebra.smul_def,Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap] using hz
 have hunit :v (s :E)=1 :=le_antisymm s.property
   (le_of_not_gt fun h=>hs ((residue_eq_zero_iff s).2 (v.mem_maximalIdeal_iff.2 h)))
 have hscale : (∑ j,algebraMap A E (b j)*(x j:E)) =
     algebraMap A E (b k)*(s :E) := by
   have hs' : (s :E) = ∑ j,algebraMap A E (b j/b k)*(x j:E) := by
     change ValuationSubring.subtype V s= _
     simp only [s,map_sum,map_mul]
     rfl
   rw [hs',Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j _
   rw [← mul_assoc,← map_mul,mul_div_cancel₀ _ h0]
 rw [hscale,map_mul,hunit,mul_one]
 exact hmax i
theorem residue_independent_lift {I:Type} [Fintype I] (x :I→V)
  (hx :z14 (ResidueField O) (fun j=>residue V (x j))) :
  z14 A (fun j=>(x j:E)) := by
 apply Fintype.linearIndependent_iff.mpr
 intro b hb i
 have h:=coeff_le_of_residue_independent v vA x hx b i
 simp only [Algebra.smul_def] at hb
 rw [hb,map_zero,nonpos_iff_eq_zero] at h
 exact (algebraMap A E).injective (by rw [map_zero,v.zero_iff.mp h])
end Residues
section Tower
variable {A B E Γ:Type} [zrb A] [zrb B] [zrb E]
 [zZE A B] [zZE A E] [zZE B E] [IsScalarTower A B E]
 [LinearOrderedCommGroupWithZero Γ] (v :Valuation E Γ)
local notation "vA" => v.comap (algebraMap A E)
local notation "vB" => v.comap (algebraMap B E)
local notation "O" => Valuation.valuationSubring vA
local notation "R" => Valuation.valuationSubring vB
local notation "V" => Valuation.valuationSubring v
local instance :Valuation.HasExtension vA v :=⟨fun _ _=>Iff.rfl⟩
local instance :Valuation.HasExtension vB v :=⟨fun _ _=>Iff.rfl⟩
local instance :Valuation.HasExtension vA vB where
 val_isEquiv_comap := by
  intro x y
  simp only [Valuation.comap_apply,zG3 A B E]
local instance :IsScalarTower O R V :=
 IsScalarTower.of_algebraMap_eq fun _=>Subtype.ext (zG3 A B E _)
private theorem charP_source {S T:Type} [CommRing S] [CommRing T] {q:ℕ} [CharP T q]
   (f :S →+* T) (hf :zq4 f) :CharP S q :=
 ⟨fun n=> by rw [← CharP.cast_eq_zero_iff T q n,← map_natCast f n,map_eq_zero_iff f hf]⟩
theorem residue_independent_in_small_extension {q:ℕ} [CharP E q] (hq:q.Prime)
    [FiniteDimensional A B] (hd:Module.finrank A B<q) (z :V) (a :ResidueField O)
    (hpow: (residue V z)^q=algebraMap (ResidueField O) (ResidueField V) a)
    (ha : ∀ c:ResidueField O,algebraMap (ResidueField O) (ResidueField V) c≠residue V z) :
    (∀ b:ResidueField R,algebraMap (ResidueField R) (ResidueField V) b≠residue V z) ∧
    z14 (ResidueField R) (fun i:Fin q=>residue V (z^(i:ℕ))) := by
  let:CharP V q:=charP_source (ValuationSubring.subtype V) Subtype.val_injective
  let:CharP (ResidueField V) q:=CharP.of_ringHom_of_ne_zero (residue V) q hq.ne_zero
  let:CharP (ResidueField R) q :=
    charP_source (algebraMap (ResidueField R) (ResidueField V)) (algebraMap (ResidueField R) (ResidueField V)).injective
  have hnR (b:ResidueField R) :algebraMap (ResidueField R) (ResidueField V) b≠residue V z := by
    intro hb
    have hbpow:b^q=algebraMap (ResidueField O) (ResidueField R) a :=
      (algebraMap (ResidueField R) (ResidueField V)).injective (by
        rw [map_pow,hb,← zG3,hpow])
    have hn (c:ResidueField O) :algebraMap (ResidueField O) (ResidueField R) c≠b:= by
      intro hc
      exact ha c (by rw [zG3 (ResidueField O) (ResidueField R),hc,hb])
    have hLI:=kummer_powers hq b _ hbpow hn
    obtain ⟨w,hw⟩:=residue_surjective b
    have hLI' : z14 A (fun j:Fin q=>((w^(j:ℕ) :R) :B)) := by
      apply residue_independent_lift vB vA (fun j:Fin q=>w^(j:ℕ))
      simpa only [map_pow,hw] using hLI
    exact (not_le_of_gt hd) (by simpa only [Fintype.card_fin] using hLI'.fintype_card_le_finrank)
  refine ⟨hnR,?_⟩
  simp only [map_pow]
  exact kummer_powers hq (residue V z) ((algebraMap (ResidueField O) (ResidueField R)) a)
    (by rw [← zG3]; exact hpow) hnR
end Tower
end
end qitLgnc
end
section
namespace qitLgnc
noncomputable section
open Polynomial
section Physical
variable {S M Γ:Type} [zrb S] [zrb M] [LinearOrderedCommGroupWithZero Γ]
 (v :Valuation M Γ) (ρ:S[X] →+* M)
 (hC : ∀ a :S,a≠0→v (ρ (C a))=1) (hX:v (ρ z7y)<1)
include hC hX in
private theorem value_poly (a :S[X]) :v (ρ a)≤1 := by
 induction a using Polynomial.induction_on' with
 | add a b ha hb =>
   rw [map_add]
   exact (v.map_add _ _).trans (max_le ha hb)
 | monomial n a =>
   by_cases ha :a=0
   · simp [ha]
   rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow,map_mul,map_pow,hC a ha,one_mul]
   exact pow_le_one₀ zero_le hX.le
include hC hX in
private theorem value_small (a :S[X]) (ha :a.coeff 0=0) :v (ρ a)<1 := by
 obtain ⟨b,rfl⟩:=X_dvd_iff.mpr ha
 rw [map_mul,map_mul]
 exact (mul_le_of_le_one_right zero_le (value_poly v ρ hC hX b)).trans_lt hX
include hC hX in
private theorem value_unit (a :S[X]) (ha :a.coeff 0≠0) :v (ρ a)=1 := by
 have hs :=value_small v ρ hC hX (a - C (a.coeff 0)) (by simp)
 rw [map_sub] at hs
 have h:=v.map_add_eq_of_lt_left (x :=ρ (C (a.coeff 0))) (y :=ρ a-ρ (C (a.coeff 0)))
  (by rwa [hC _ ha])
 rwa [add_comm (ρ (C (a.coeff 0))),sub_add_cancel,hC _ ha] at h
private theorem strip (a :S[X]) (ha :a≠0) :
  ∃ A:S[X],a=z7y ^a.natTrailingDegree*A∧A.coeff 0≠0:= by
 obtain ⟨A,hA⟩:=X_pow_dvd_iff.mpr (fun i hi=>coeff_eq_zero_of_lt_natTrailingDegree hi :
  ∀ i<a.natTrailingDegree,a.coeff i=0)
 refine ⟨A,hA,?_⟩
 have h:=coeff_natTrailingDegree_ne_zero.mpr ha
 have he :=coeff_X_pow_mul A a.natTrailingDegree 0
 rw [Nat.zero_add] at he
 rwa [congrArg (fun b:S[X]=>b.coeff a.natTrailingDegree) hA,he] at h
include hC hX in
theorem fraction_approx (hi:zq4 ρ) (a b:S[X])
   (h:v (ρ a/ρ b)≤1) : ∃ c:S,v (ρ a/ρ b-ρ (C c))<1 := by
 by_cases ha :a=0
 · exact ⟨0,by simp [ha]⟩
 by_cases hb:b=0
 · exact ⟨0,by simp [hb]⟩
 have hx :0<v (ρ z7y) :=
   pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr (hi.ne X_ne_zero |> fun h=> by rwa [map_zero] at h))
 obtain ⟨A,hA,hA₀⟩:=strip a ha
 obtain ⟨B,hB,hB₀⟩:=strip b hb
 have hvA:=value_unit v ρ hC hX A hA₀
 have hvB:=value_unit v ρ hC hX B hB₀
 have hBne :ρ B≠0:= fun h=> by simp [h] at hvB
 have hv :v (ρ a/ρ b)=v (ρ z7y)^a.natTrailingDegree /
     v (ρ z7y)^b.natTrailingDegree := by
   conv_lhs=>rw [hA,hB]
   simp only [map_div₀,map_mul,map_pow,hvA,hvB,mul_one]
 have hdeg:b.natTrailingDegree≤a.natTrailingDegree :=
   (pow_le_pow_iff_right_of_lt_one₀ hx hX).mp
     ((div_le_one₀ (pow_pos hx _)).mp (hv ▸ h))
 rcases lt_or_eq_of_le hdeg with hlt | he
 · refine ⟨0,?_⟩
   rw [C_0,map_zero,sub_zero,hv,div_lt_one₀ (pow_pos hx _)]
   exact pow_lt_pow_right_of_lt_one₀ hx hX hlt
 have hdiv :ρ a/ρ b=ρ A/ρ B:= by
   conv_lhs=>rw [hA,hB]
   rw [he,map_mul,map_mul,map_pow,mul_div_mul_left _ _ (pow_ne_zero _ (v.ne_zero_iff.mp hx.ne'))]
 let c:=A.coeff 0/B.coeff 0
 have hdiff : (A - C c*B).coeff 0=0:= by
   simp [c,div_mul_cancel₀ _ hB₀]
 refine ⟨c,?_⟩
 have hd:ρ A/ρ B-ρ (C c)=ρ (A - C c*B)/ρ B:= by
   rw [map_sub,map_mul,sub_div,mul_div_cancel_right₀ _ hBne]
 rw [hdiv,hd,map_div₀,hvB,div_one]
 exact value_small v ρ hC hX _ hdiff
end Physical
end
end qitLgnc
end
section
namespace qitLgnc
noncomputable section
open Polynomial IsLocalRing
open Valuation.HasExtension (algebraMap_residue_eq_residue_algebraMap)
section Frobenius
variable {S M Γ:Type} [zrb S] [zrb M] [LinearOrderedCommGroupWithZero Γ]
 {q:ℕ} [CharP S q] (v :Valuation M Γ) (ι:S[X] →+* M)
 (hi:zq4 ι)
 (hC : ∀ a :S,a≠0→v (ι (C a))=1) (hX:v (ι z7y)<1)
local notation "F₀" => Subfield.closure
 (Set.range (fun a :S=>ι (C (a^q))) ∪ {ι z7y})
include hi hC hX in
private theorem base_residue (hq:q.Prime) (x :F₀) (hx :v (x :M)≤1) :
   ∃ a :S,v ((x :M)-ι (C (a^q)))<1 := by
 let:Fact q.Prime :=⟨hq⟩
 let ρ:=ι.comp (mapRingHom (frobenius S q))
 have hρ:zq4 ρ:=hi.comp (map_injective _ (frobenius S q).injective)
 have hρC (a :S) (ha :a≠0) :v (ρ (C a))=1 := by
   simp only [ρ,zQb,coe_mapRingHom,map_C,frobenius_def]
   exact hC _ (pow_ne_zero _ ha)
 have hρX:v (ρ z7y)<1 := by simpa [ρ] using hX
 have hr :Subring.closure (Set.range (fun a :S=>ι (C (a^q))) ∪ {ι z7y}) ≤
     ρ.range := by
   apply Subring.closure_le.mpr
   rintro x (⟨a,rfl⟩ | hx)
   · exact ⟨C a,by simp [ρ,frobenius_def]⟩
   · have he :x=ι Polynomial.X:=hx
     exact ⟨z7y,by simp [ρ,he]⟩
 obtain ⟨u,hu,w,hw,he⟩:=Subfield.mem_closure_iff.mp x.property
 obtain ⟨g,hg⟩:=hr hu
 obtain ⟨f,hf⟩:=hr hw
 rw [← he,← hg,← hf] at hx ⊢
 simpa only [ρ,zQb,coe_mapRingHom,map_C,frobenius_def] using
   fraction_approx v ρ hρC hρX hρ g f hx
include hi hC hX in
theorem field_orthogonal (hq:q.Prime) {s :S} (hs : ∀ a :S,a^q≠s)
   (F:IntermediateField F₀ M) [FiniteDimensional F₀ F] (hd:Module.finrank F₀ F<q) :
   ι (C s)∉F ∧ ∀ (b:Fin q→F) (i:Fin q),
     v (b i:M)≤v (∑ j,(b j:M)*ι (C s)^(j:ℕ)) := by
 let:CharP M q:=charP_of_injective_ringHom ((ι.comp C).injective) q
 let B:=F₀
 let vB:=v.comap (algebraMap B M)
 let vF:=v.comap (algebraMap F M)
 let O:=vB.valuationSubring
 let R:=vF.valuationSubring
 let V:=v.valuationSubring
 let:vB.HasExtension v :=⟨fun _ _=>Iff.rfl⟩
 let:vF.HasExtension v :=⟨fun _ _=>Iff.rfl⟩
 let emb:S →+* V:=(ι.comp C).codRestrict V.toSubring (fun a=> by
   change v (ι (C a))≤1
   by_cases ha :a=0
   · simp [ha]
   · exact (hC a ha).le)
 let z :=emb s
 have hzne :s≠0:= fun h=>hs 0 (by rw [h,zero_pow hq.ne_zero])
 have hval :v (z :M)=1 :=hC s hzne
 have hp: (ι (C s))^q=ι (C (s^q)) := by rw [map_pow,map_pow]
 let a :O:=⟨⟨(ι (C s))^q,hp.symm ▸ Subfield.subset_closure (Or.inl ⟨s,rfl⟩)⟩,by
   change v ((ι (C s))^q)≤1
   rw [map_pow,hC s hzne,one_pow]⟩
 have hpow:residue V z^q=algebraMap (ResidueField O) (ResidueField V) (residue O a) := by
   rw [← map_pow,algebraMap_residue_eq_residue_algebraMap]
   congr 1
 have hn (c:ResidueField O) :algebraMap (ResidueField O) (ResidueField V) c≠residue V z := by
   obtain ⟨w,rfl⟩:=residue_surjective c
   obtain ⟨b,hb⟩:=base_residue v ι hi hC hX hq (w:B) w.property
   have hdiff : (algebraMap O V w-emb (b^q) :V)∈maximalIdeal V :=
     v.mem_maximalIdeal_iff.mpr hb
   have heq :residue V (algebraMap O V w)=residue V (emb (b^q)) := by
     rw [← sub_eq_zero,← map_sub]
     exact (residue_eq_zero_iff _).mpr hdiff
   rw [algebraMap_residue_eq_residue_algebraMap,heq]
   exact ((residue V).comp emb).injective.ne (hs b)
 obtain ⟨hnF,hLI⟩:=residue_independent_in_small_extension (A:=B) (B:=F)
   v hq hd z _ hpow hn
 refine ⟨fun hz => ?_,fun b i => ?_⟩
 · let zF:R:=⟨⟨ι (C s),hz⟩,hval.le⟩
   exact hnF (residue R zF) (by rw [algebraMap_residue_eq_residue_algebraMap]; rfl)
 · have h:=coeff_le_of_residue_independent v vF
     (fun j:Fin q=>z^(j:ℕ)) hLI b i
   have hz :V.subtype z=ι (C s) :=rfl
   simpa only [IntermediateField.algebraMap_apply,← ValuationSubring.subtype_apply,map_pow,hz] using h
end Frobenius
end
end qitLgnc
end
section
namespace qitLgnc
open P5 (K p)
open cu (L)
open qziIa4d (SeedSeries)
theorem orthogonal:qnyP9Da.c3:= by
 intro M Γ _ _ v ι hi hC hX hs F hF hd
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP SeedSeries p:=charP_of_injective_ringHom (algebraMap L SeedSeries).injective p
 exact @field_orthogonal SeedSeries M Γ _ _ _ p _ v ι hi hC hX
  (show p.Prime from KoalaBear.is_prime) _ hs F hF hd
end qitLgnc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qRoCwuc
noncomputable section
open Polynomial Finset
open P5 (K p)
open qAxtVye (wX branchDegree)
open cu (L FX j9 jz)
open DQ (DT specialize)
open Cu
open quN7Z4a (Sheet physicalWeight compressionWidth)
open private cK5 from ProximityPrize.SubmissionLower.CR
open private cTM parameter_eval from ProximityPrize.SubmissionLower.ZFh47Da
open scoped BigOperators
variable {C₀:sQ} [Fact (Irreducible C₀)] {J g H T z s}
private theorem cut_iff (S:Sheet C₀ J g H T z s) (q:DT S.n) :
  aa4 S.n (MvPolynomial.map (algebraMap L FX) q)∈EF S.bY ↔
  coord S q=0:= by
 change W8 S.bY _=0↔_
 rw [cTM]
 exact map_eq_zero_iff _ (Mu C₀).injective
theorem marked_zero (S:Sheet C₀ J g H T z s) (q:DT S.n)
  (hq:coord S q=0) {γ:K} (hγ:γ∈T) :zY9 (S.parameter γ) q=0:= by
 have h:=S.onBase γ hγ _ ((cut_iff S q).mpr hq)
 rw [parameter_eval,← map_zero (algebraMap L FX)] at h
 exact (algebraMap L FX).injective h
theorem dSG (S:Sheet C₀ J g H T z s) (hz :Set.InjOn z (T:Set K))
   (q:DT S.n) (hq:coord S q≠0) (V:Finset K) (hV:V⊆T)
   (hzeros : ∀ γ∈V,zY9 (S.parameter γ) q=0) :
   V.card≤q.totalDegree*H := by
 let pt (γ:K) :=aCn (z γ) (S.parameter γ)
 refine (cK5 S.n H (EF S.bY) (RingHom.ker_isPrime (W8 S.bY))
   S.height (MvPolynomial.map (algebraMap L FX) q) (fun h=>hq ((cut_iff S q).mp h)) V pt ?_ ?_).trans ?_
 · intro γ hγ η hη he
   exact hz (hV hγ) (hV hη) (jz.injective (congrFun he (Sum.inl 0)))
 · exact fun γ hγ=>⟨S.onBase γ (hV hγ),by rw [parameter_eval,hzeros γ hγ,map_zero]⟩
 · exact ztf H (Finset.sup_mono (MvPolynomial.support_map_subset _ _))
theorem coeff_generic (S:Sheet C₀ J g H T z s) (j:ℕ) :
  (coeff S j).map (coord S)=C (S.bY.scale :oO C₀)*S.root.equation.coeff j:= by
 have h:=congrArg (fun f : ((oO C₀)[X])[X]=>f.coeff j) S.bY.generic_eq
 change (_: ((oO C₀)[X])[X]).coeff j=(_: ((oO C₀)[X])[X]).coeff j at h
 rw [coeff_map,coeff_C_mul] at h
 exact h
theorem quad_form {R:Type*} [Semiring R] {f :R[X]} (hf :f.natDegree≤2) :
  f=C (f.coeff 2)*z7y^2+C (f.coeff 1)*z7y+C (f.coeff 0) := by
 conv_lhs=>rw [f.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hf)]
 simp [sum_range_succ,add_comm,add_assoc]
theorem marked_eq (S:Sheet C₀ J 2 H T z s) {γ:K} (hγ:γ∈T) :
  let e :=zY9 (S.parameter γ)
  (coeff S 2).map e*(j9 (s γ))^2 +
    (coeff S 1).map e*j9 (s γ)+(coeff S 0).map e=0:= by
 have h:=S.identity γ hγ
 unfold specialize at h
 nth_rw 1 [quad_form S.bY.degree.1] at h
 simpa only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,
  Polynomial.map_X,eval_add,eval_mul,eval_C,eval_pow,eval_X,coe_mapRingHom,coeff] using h
theorem disc_square (S:Sheet C₀ J 2 H T z s) {γ:K} (hγ:γ∈T) :
   IsSquare ((disc S).map (zY9 (S.parameter γ))) := by
 let e :=mapRingHom (zY9 (S.parameter γ))
 refine ⟨2*e (coeff S 2)*j9 (s γ)+e (coeff S 1),?_⟩
 change e (disc S)= _
 have h:e (coeff S 2)*(j9 (s γ))^2 +
     e (coeff S 1)*j9 (s γ)+e (coeff S 0)=0:=marked_eq S hγ
 simpa only [disc,discrim,map_sub,map_mul,map_pow,map_ofNat,← pow_two] using
   (discrim_eq_sq_of_quadratic_eq_zero (by rwa [← pow_two]) :
     discrim (e (coeff S 2)) (e (coeff S 1)) (e (coeff S 0))= _)
private theorem bBM {n a b:ℕ} {P Q: (DT n)[X]}
  (hP : ∀ j,(P.coeff j).totalDegree≤a) (hQ : ∀ j,(Q.coeff j).totalDegree≤b) (j:ℕ) :
  ((P*Q).coeff j).totalDegree≤a+b:= by
 rw [coeff_mul]
 apply MvPolynomial.totalDegree_finsetSum_le
 exact fun i _=>(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hP _) (hQ _))
theorem disc_height (S:Sheet C₀ J 2 H T z s) (j:ℕ) :
   ((disc S).coeff j).totalDegree≤2 := by
 have hC (i:ℕ) : ((4 : (DT S.n)[X]).coeff i).totalDegree≤0:= by
   have h: (4 : (DT S.n)[X])=C (MvPolynomial.C (4 :L)) := by
     rw [map_ofNat MvPolynomial.C,map_ofNat Polynomial.C]
   rw [h,coeff_C]
   split <;> simp
 unfold disc discrim
 rw [coeff_sub,pow_two]
 exact (MvPolynomial.totalDegree_sub _ _).trans (max_le
   (bBM (S.bY.degree.2 1) (S.bY.degree.2 1) j)
   (bBM (bBM hC (S.bY.degree.2 2)) (S.bY.degree.2 0) j))
theorem disc_tame (S:Sheet C₀ J 2 H T z s) {b:P5_7_3.fO}
    (hw:physicalWeight (wX b) S.root.equation<compressionWidth (wX b) 2)
    (hb:branchDegree b 2<p) : (genericDisc S).natDegree<p:= by
  set D:=wX b
  have hw' : physicalWeight D S.root.equation<12*D:= by
    convert hw using 1
    simp only [compressionWidth]
    omega
  have hb' : 22*D <p:= by
    change 2*2*(2*D*2*(2+1))-2*2*D <p at hb
    omega
  let c (j:ℕ) :=(coeff S j).map (coord S)
  have hc (j:ℕ) (hj:j≤2) : (c j).natDegree+j*D <12*D:= by
    rw [show c j= _ from coeff_generic S j,natDegree_C_mul S.bY.scale.ne_zero]
    by_cases hz :S.root.equation.coeff j=0
    · rw [hz,natDegree_zero,zero_add]
      have h:=ztf D hj
      omega
    · exact (Finset.le_sup (f := fun i=>(S.root.equation.coeff i).natDegree+i*D)
        (mem_support_iff.mpr hz)).trans_lt hw'
  have hd:genericDisc S=(c 1)^2 - 4*c 2*c 0:= by simp [genericDisc,disc,discrim,c]
  have ha :=hc 2 le_rfl
  have hβ:=hc 1 (by decide)
  have hγ:=hc 0 (by decide)
  have h₁: ((c 1)^2).natDegree≤2*(c 1).natDegree :=natDegree_pow_le
  have h₂: (4*c 2*c 0).natDegree≤(c 2).natDegree+(c 0).natDegree := by
    apply natDegree_mul_le_of_le _ le_rfl
    rw [← Polynomial.C_ofNat]
    exact natDegree_C_mul_le _ _
  rw [hd]
  apply (natDegree_sub_le _ _).trans_lt
  exact max_lt (h₁.trans_lt (by omega)) (h₂.trans_lt (by omega))
end
end qRoCwuc
end
section
set_option autoImplicit true
namespace qDhaEec
theorem proof :qnyP9Da.c3 :=
 qitLgnc.orthogonal
end qDhaEec
end
