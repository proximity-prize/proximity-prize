import ProximityPrize.SubmissionLower.ZxrVYla
import Mathlib.RingTheory.PowerSeries.Expand
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZwDGfQd
import ProximityPrize.SubmissionLower.ZxKiVod
set_option Elab.async false
open _root_ renaming AlgHom.id → zhD, Algebra → zZE, Algebra.TensorProduct.lift → zdo, Algebra.TensorProduct.lift_tmul → z5s, Algebra.TensorProduct.map → zv2, Algebra.ofId → zNX, Algebra.smul_def → zd5, CommRing → za6, Field → zrb, Fintype → z85, Function.Injective → zq4, Ideal.Quotient.mk → zVv, IsFractionRing.injective → zxb, IsLocalization.exist_integer_multiples_of_finite → zrh, LinearIndependent → z14, LinearIndependent.of_comp → zCu, LinearMap.mulLeft → zzN, Module.Finite → zAa, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.rename → zHw, Nat.mul_le_mul_left → zBI, Polynomial.C → z1z, Polynomial.basisMonomials → zWl, Polynomial.coeff_zero → zO6, TensorProduct.inductionOn → z2P
set_option maxHeartbeats 550000
section
set_option backward.isDefEq.respectTransparency false
namespace qX9S3Pd
noncomputable section
open cu (L FX)
open gT (kM)
open Cu
open akS (tu)
open E7 (CurveField Gb)
attribute [local instance] gRK
def c1 :Prop :=
  ∀ (n H :ℕ) (B:Ideal (Gc n)),B.IsPrime→a9K B H →
    ∀ (a :Fin n→FX) (r :ℕ) (w:Fin r→tu B),
      IndependentPowers B a w→ r≤H
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)] (J:Ideal kM)
    (g n:ℕ) (R:wJ C₀ J g) (A:yI R n),
    CurveField L (oO C₀) →
    ∃ (a :Fin n→FX)
      (w:Fin (Gb L (oO C₀) A.coordinate)→tu (EF A)),
      IndependentPowers (EF A) a w
theorem of_children (h1 :c1) (h2 :c2) :qBajpRb.c1 := by
 intro C₀ _ J g n H R A hH V z t hV hz k j q hq hq0 hcut
 obtain ⟨⟨i,hi⟩,hF,hd⟩:=seed_bounds C₀
 obtain ⟨a,w,hw⟩:=h2 C₀ J g n R A hF
 have hB: (EF A).IsPrime :=RingHom.ker_isPrime _
 have ht:=h1 n H (EF A) hB hH a _ w hw
 exact (bYX A hF hi V z t hV hz hq0 hcut).trans ((pole_budget A hF hq).trans
  (Nat.add_le_add (zBI k hd) (zBI j ht)))
end
end qX9S3Pd
end
section
set_option backward.isDefEq.respectTransparency false
namespace q9aDOab
noncomputable section
open cu (L FX)
open Cu
open akS (tu)
open aFZ (RB bK7)
open E7
open agN (O7 d4p
 gDD bGE)
open qBajpRb (ek)
open qX9S3Pd (principal gRK sectionValue IndependentPowers)
open private constant_base from ProximityPrize.SubmissionLower.ZJbAGBd
open private b1t from ProximityPrize.SubmissionLower.ZgdIx1d
open private dc8 from ProximityPrize.SubmissionLower.Z3EWiUc
open scoped nonZeroDivisors Polynomial
private theorem powers_basis {F E :Type} [zrb F] [zrb E] [zZE F E] {x :E}
   (hx :Transcendental F x) {r :ℕ}
   (v :Fin r→E) (hv :z14 (IntermediateField.adjoin F {x}) v) (m:ℕ) :
   z14 F (fun ij:Fin (m+1)×Fin r=>x^(ij.1 :ℕ)*v ij.2) := by
 let A:=IntermediateField.adjoin F {x}
 let t:A:=⟨x,IntermediateField.mem_adjoin_simple_self F x⟩
 have ht:Transcendental F t:=(transcendental_algebraMap_iff (algebraMap A E).injective).mp hx
 have hpow:z14 F (fun i:Fin (m+1)=>t^(i:ℕ)) := by
   have h:=((zWl F).linearIndependent.comp (Fin.val :Fin (m+1)→ℕ) Fin.val_injective).map'
     (Polynomial.aeval t).toLinearMap
     (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
   change z14 F (fun i:Fin (m+1) =>
     Polynomial.aeval t (zWl F i.val)) at h
   simpa only [Polynomial.coe_basisMonomials,Polynomial.aeval_monomial,map_one,one_mul] using h
 simpa [zd5,t] using linearIndependent_smul hpow hv
private theorem independent_insert {F E ι:Type} [zrb F] [zrb E] [zZE F E]
   [z85 ι] (v :ι→E) (hv :z14 F v) :
   letI:zZE (FractionRing F[X]) (FractionRing E[X]) :=
     (RB (algebraMap F E)).toAlgebra
   z14 (FractionRing F[X]) (bK7 ∘ v) := by
 let FX' := FractionRing F[X]
 let EX:=FractionRing E[X]
 let f :=algebraMap F E
 let e :=algebraMap E[X] EX
 let α:=RB f
 let:zZE FX' EX:= α.toAlgebra
 have hm (q:F[X]) :α (algebraMap F[X] FX' q)=e (q.map f) := by
   dsimp only [α]
   rw [RB,IsFractionRing.map,IsLocalization.map_eq]
   rfl
 refine Fintype.linearIndependent_iff.mpr fun b hb i => ?_
 obtain ⟨d,hd⟩:=zrh (F[X]⁰) b
 choose a ha using hd
 have hterm (j:ι) :e ((a j).map f*z1z (v j)) =
     α (algebraMap F[X] FX' d.val)*(b j•bK7 (v j)) := by
   rw [map_mul,← hm,ha j,zd5 (R:=F[X]),map_mul,mul_assoc]
   rfl
 have hsum : ∑ j,(a j).map f*z1z (v j)=0:= by
   apply zxb E[X] EX
   change e (∑ j,(a j).map f*z1z (v j))=e 0
   simp only [map_zero,map_sum,hterm,← Finset.mul_sum]
   change α (algebraMap F[X] FX' d.val)*(∑ j,b j•(bK7 ∘ v) j)=0
   rw [hb,mul_zero]
 have hc (k :ℕ) : ∑ j,(a j).coeff k•v j=0:= by
   simpa only [Polynomial.finsetSum_coeff,Polynomial.coeff_mul_C,Polynomial.coeff_map,
     zO6,zd5] using congrArg (fun q:E[X]=>q.coeff k) hsum
 have hz :a i=0:=Polynomial.ext fun k =>
   (Fintype.linearIndependent_iff.mp hv _ (hc k) i).trans (zO6 _).symm
 have hh:=ha i
 rw [hz,map_zero,zd5] at hh
 exact (mul_eq_zero.mp hh.symm).resolve_left
   ((map_ne_zero_iff _ (zxb F[X] FX')).mpr (nonZeroDivisors.ne_zero d.property))
private theorem scaled_powers {k D E :Type} [zrb k] [za6 D] [IsDomain D]
    [zrb E] [zZE D E] [IsFractionRing D E] [zZE k E] {x :E}
    (hx :Transcendental k x) (hfinite :zAa (IntermediateField.adjoin k {x}) E) :
    ∃ u:Fin (Module.finrank (IntermediateField.adjoin k {x}) E)→D,∀ m:ℕ,
      z14 k (fun ij:Fin (m+1)×_ =>
        x^(ij.1 :ℕ)*algebraMap D E (u ij.2)) := by
  let F:=IntermediateField.adjoin k {x}
  let:zAa F E :=hfinite
  let v :=Module.finBasis F E
  obtain ⟨d,hd⟩:=zrh (D⁰) v
  choose u hu using hd
  have hscaled:z14 F (fun i=>algebraMap D E (u i)) := by
    have he :IsUnit (algebraMap D E (d:D)) :=
      ((map_ne_zero_iff _ (zxb D E)).mpr (nonZeroDivisors.ne_zero d.prop)).isUnit
    let l:=zzN F (algebraMap D E (d:D))
    have hl:zq4 l:= fun _ _ hh=>he.mul_left_cancel hh
    have h:=v.linearIndependent.map' l (LinearMap.ker_eq_bot.mpr hl)
    change z14 F (fun i=>(algebraMap D E (d:D))*v i) at h
    convert h using 1
    exact funext (fun i=>(hu i).trans (zd5 _ _))
  exact ⟨u,(powers_basis hx _ hscaled :)⟩
private theorem linear_eval {k F E B D σ:Type} [zrb k] [zrb F] [za6 E]
  [za6 B] [za6 D] [zZE k E] [zZE F B] [zZE F D] [z85 σ]
  (j:B →ₐ[F] D) (e :E →+* D) (φ:k→F) (a :σ→k) (x :σ→B) (y :σ→E)
  (hc : ∀ c,algebraMap F D (φ c)=e (algebraMap k E c)) (hx : ∀ i,j (x i)=e (y i)) :
  j (∑ i,φ (a i)•x i)=e (∑ i,a i•y i) := by
 rw [map_sum j,map_sum e]
 refine Finset.sum_congr rfl fun i _ => ?_
 simp only [zd5,map_mul,j.commutes,hc,hx]
set_option backward.isDefEq.respectTransparency true in
theorem height_family :qX9S3Pd.c2 := by
 classical
 intro C₀ _ J g n R A hF
 let E :=oO C₀
 let:zZE L E :=gRK C₀
 let B:=EF A
 let r :=Gb L E A.coordinate
 by_cases hr :r=0
 · change ∃ (a :Fin n→FX) (w:Fin r→tu B),IndependentPowers B a w
   rw [hr]
   exact ⟨0,Fin.elim0,fun _=>linearIndependent_empty_type⟩
 have hd:=principal hF
 obtain ⟨a,ha,_⟩:=d4p hd A.coordinate
 let x :=O7 a A.coordinate
 have hp: (∑ᶠ v :CurvePlace L E,poleOrder v.value x)=r :=finsum_congr ha
 have hx :Transcendental L x :=gDD (hp.symm ▸ Nat.pos_of_ne_zero hr)
 have hfinite :=bGE hF hx
 have hf :=((hd x).2.2.2 hx).symm.trans hp
 let D:=abz C₀
 have hu:=scaled_powers (D:=D) hx hfinite
 rw [hf] at hu
 obtain ⟨u,hu⟩:=hu
 let j:tu B →+* y7 C₀:=RingHom.kerLift (W8 A)
 let:zZE FX (y7 C₀) :=(Mr C₀).toAlgebra
 let jₐ:tu B →ₐ[FX] y7 C₀:=⟨j,by
   intro b
   change W8 A (MvPolynomial.C b)=Mr C₀ b
   exact MvPolynomial.eval₂Hom_C _ _ _⟩
 let b:Fin n→FX:= fun i=>algebraMap L FX (a i)
 have hcoord (i:Fin n) :
     jₐ (zVv B (z9v (Sum.inr i)))=Mu C₀ (A.coordinate i) := by
   exact MvPolynomial.eval₂Hom_X' ..
 have hform :jₐ (sectionValue B b)=Mu C₀ x := by
   dsimp only [sectionValue,b,x,O7]
   exact linear_eval (k :=L) (F:=FX) (B:=tu B) (E :=E) (D:=y7 C₀)
     jₐ (Mu C₀) (algebraMap L FX) a
     (fun i=>zVv B (z9v (Sum.inr i))) A.coordinate
     (b1t C₀) hcoord
 have hq (i:Fin r) : ∃ q:sQ,zVv (auG C₀) q=u i :=
   Ideal.Quotient.mk_surjective _
 choose q hq using hq
 let w (i:Fin r) :tu B :=
   zVv B (MvPolynomial.map (algebraMap L FX) (zHw Sum.inl (q i)))
 have hw (i:Fin r) :jₐ (w i)=Mu C₀ (algebraMap D E (u i)) := by
   change (W8 A).comp (MvPolynomial.map (algebraMap L FX))
     (zHw Sum.inl (q i))= _
   rw [constant_base]
   apply congrArg (Mu C₀)
   unfold ek
   rw [MvPolynomial.eval₂Hom_rename]
   change zIe (Wt C₀) (q i)= _
   rw [dc8,hq]
 refine ⟨b,w,fun m=>zCu jₐ.toLinearMap ?_⟩
 let q (ij:Fin (m+1)×Fin r) :=x^(ij.1 :ℕ)*algebraMap D E (u ij.2)
 have h:=independent_insert q (hu m)
 have he : (fun ij:Fin (m+1)×Fin r =>
     jₐ (sectionValue B b^(ij.1 :ℕ)*w ij.2))=Mu C₀ ∘ q:= by
   funext ij
   dsimp only [Function.comp_apply,q]
   rw [map_mul jₐ,map_pow jₐ,hform,hw,map_mul (Mu C₀),map_pow (Mu C₀)]
 change z14 FX (fun ij:Fin (m+1)×Fin r =>
   jₐ (sectionValue B b^(ij.1 :ℕ)*w ij.2))
 rw [he]
 exact h
end
end q9aDOab
end
section
set_option backward.isDefEq.respectTransparency false
namespace q9aDOab
noncomputable section
open cu (FX)
open Cu (Gc)
open akS
open qX9S3Pd (IndependentPowers)
open scoped TensorProduct
private def contract {F:Type} [zrb F] (P:Type) [za6 P] [zZE F P]
   {B:Type} [AddCommGroup B] [Module F B] (f :B →ₗ[F] F) :P ⊗[F] B →ₗ[P] P :=
 (TensorProduct.AlgebraTensorModule.rid F P P).toLinearMap.comp (f.baseChange P)
@[simp] private theorem contract_tmul {F:Type} [zrb F] {P:Type} [za6 P]
   [zZE F P] {B:Type} [AddCommGroup B] [Module F B] (f :B →ₗ[F] F)
   (p:P) (b:B) :contract P f (p ⊗ₜ[F] b)=f b•p:= by
  simp [contract]
private theorem specialize_independent {F P S B ι:Type}
    [zrb F] [za6 P] [zrb S] [za6 B] [zZE F P] [zZE F S]
    [zZE F B] [z85 ι] (α:P →ₐ[F] S) (hα:zq4 α)
    (β:P →ₐ[F] F) (v :ι→P ⊗[F] B)
    (hv :z14 F (fun j =>
      zdo ((zNX F B).comp β) (zhD F B)
        (fun _ _=>Commute.all _ _) (v j))) :
    z14 S (fun j=>zv2 α (zhD F B) (v j)) := by
  classical
  let e :=zdo ((zNX F B).comp β) (zhD F B)
    (fun _ _=>Commute.all _ _)
  let l:=Fintype.linearCombination F (fun j=>e (v j))
  have hl:zq4 l:=linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  obtain ⟨g,hg⟩:=l.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hl)
  let f (i:ι) :B →ₗ[F] F:=(LinearMap.proj i).comp g
  have hf (i j:ι) :f i (e (v j))=if i=j then 1 else 0:= by
    have h:=DFunLike.congr_fun hg (Pi.single j (1 :F))
    change g (l (Pi.single j (1 :F)))=Pi.single j (1 :F) at h
    rw [show l (Pi.single j (1 :F))=e (v j) by
      simp [l,Fintype.linearCombination_apply_single]] at h
    simpa [f,Pi.single_apply,eq_comm] using congrFun h i
  have hβ (f' : B →ₗ[F] F) (x :P ⊗[F] B) :β (contract P f' x)=f' (e x) := by
    refine z2P x ?_ ?_
    · intro p b
      simp only [contract_tmul,z5s,AlgHom.comp_apply,
        Algebra.ofId_apply,AlgHom.id_apply,e]
      calc
        β (f' b•p)=β p*f' b:= by
          rw [zd5,map_mul,AlgHom.commutes]
          simp [mul_comm]
        _=f' ((algebraMap F B) (β p)*b) := by
          rw [← zd5,map_smul,smul_eq_mul]
    · intro x y hx hy
      simp [hx,hy]
  have hα' (f' : B →ₗ[F] F) (x :P ⊗[F] B) :
      α (contract P f' x) =
        contract S f' (zv2 α (zhD F B) x) := by
    refine z2P x ?_ ?_
    · intro p b
      simp [zd5]
    · intro x y hx hy
      simp [hx,hy]
  let D:Matrix ι ι P:= fun i j=>contract P (f i) (v j)
  have hD:D.map β=1 := by
    ext i j
    exact (hβ _ _).trans ((hf i j).trans Matrix.one_apply.symm)
  have hn: (D.map α).det≠0:= by
    intro hz
    have hd:=hα (α.map_det D |>.trans hz |>.trans (map_zero α).symm)
    have hd' : β D.det=(D.map β).det:=β.map_det D
    rw [hd,map_zero,hD,Matrix.det_one] at hd'
    exact zero_ne_one hd'
  let F' : S ⊗[F] B →ₗ[S] (ι→S) :=LinearMap.pi (fun i=>contract S (f i))
  apply zCu F'
  convert Matrix.linearIndependent_cols_of_det_ne_zero hn using 1
  ext j i
  exact (hα' _ _).symm
private theorem generic_family {F B σ ι:Type} [zrb F] [za6 B] [zZE F B]
    [z85 σ] [z85 ι] (x :σ→B) (a :σ→F) (w:ι→B) (k :ι→ℕ)
    (hw:z14 F (fun j=>(∑ i,a i•x i)^k j*w j)) :
    let S:=FractionRing (z3y σ F)
    z14 S (fun j =>
      (∑ i,algebraMap (z3y σ F) S (z9v i)•((1 :S) ⊗ₜ[F] x i))^k j *
        ((1 :S) ⊗ₜ[F] w j)) := by
  let P:=z3y σ F
  let S:=FractionRing P
  let α:=IsScalarTower.toAlgHom F P S
  let β:P →ₐ[F] F:=zIe a
  let t:P ⊗[F] B := ∑ i,z9v i ⊗ₜ[F] x i
  let v (j:ι) :=t^k j*(1 ⊗ₜ[F] w j)
  let e :P ⊗[F] B →ₐ[F] B :=
    zdo ((zNX F B).comp β) (zhD F B)
      (fun _ _=>Commute.all _ _)
  have he :e t = ∑ i,a i•x i:= by
    change e (∑ i,z9v i ⊗ₜ[F] x i) = ∑ i,a i•x i
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e (z9v i ⊗ₜ[F] x i)=algebraMap F B (β (z9v i))*x i
      from z5s ..]
    rw [show β (z9v i)=a i from MvPolynomial.aeval_X a i]
    exact (zd5 _ _).symm
  have hv :z14 F (fun j=>e (v j)) := by
    simpa only [v,map_mul,map_pow,he,e,z5s,map_one,
      AlgHom.id_apply,one_mul] using hw
  let h:=zv2 α (zhD F B)
  have ht:h t = ∑ i,α (z9v i)•((1 :S) ⊗ₜ[F] x i) := by
    simp [h,t,TensorProduct.smul_tmul',smul_eq_mul]
  have hi:z14 S (fun j=>h (v j)) :=
    specialize_independent α (zxb P S) β v hv
  have hone (y :B) :h ((1 :P) ⊗ₜ[F] y)=(1 :S) ⊗ₜ[F] y := by simp [h]
  change z14 S (fun j =>
    (∑ i,α (z9v i)•((1 :S) ⊗ₜ[F] x i))^k j*((1 :S) ⊗ₜ[F] w j))
  simpa only [v,map_mul,map_pow,ht,hone] using hi
private theorem generic_powers {n r :ℕ} (B:Ideal (Gc n)) (a :Fin n→FX)
    (w:Fin r→tu B) (hw:IndependentPowers B a w) (m:ℕ) :
    z14 (e7 n)
      (fun ij:Fin (m+1)×Fin r =>
        aoe B^(ij.1 :ℕ)*ajy B (w ij.2)) :=
  generic_family (F:=FX) (B:=tu B) (ι:=Fin (m+1)×Fin r)
    (fun i=>zVv B (z9v (Sum.inr i))) a
    (fun j=>w j.2) (fun j=>j.1.val) (hw m)
private theorem pow_mul_mem {F A:Type} [zrb F] [za6 A] [zZE F A]
    (a :A) (W:Submodule F A) {w:A} (hw:w∈W) (m i:ℕ) (hi:i≤ m) :
    a^i*w∈abb a W m:= by
  induction m generalizing i with
  | zero=>simpa [abb,Nat.eq_zero_of_le_zero hi] using hw
  | succ m ih =>
    change a^i*w∈W ⊔ (abb a W m).map (zzN F a)
    cases i with
    | zero=>simpa using (le_sup_left:W≤W ⊔ _) hw
    | succ i =>
      exact (le_sup_right:_≤W ⊔ _) (Submodule.mem_map.mpr
        ⟨_,ih i (Nat.le_of_succ_le_succ hi),by simp [pow_succ',mul_assoc]⟩)
theorem rank_bound:qX9S3Pd.c1 := by
 classical
 intro n H B hB hH a r w hw
 let W:=Submodule.span (e7 n) (Set.range (ajy B ∘ w))
 have hW:zAa (e7 n) W :=
   Module.Finite.span_of_finite _ (Set.finite_range _)
 obtain ⟨C,hC⟩:=aR1.proof n H B hB hH W hW
 let U:=abb (F:=e7 n) (aoe B) W C
 let u (ij:Fin (C+1)×Fin r) :U :=
   ⟨_,pow_mul_mem (F:=e7 n) (aoe B) W (Submodule.subset_span (Set.mem_range_self ij.2)) C _
     (Nat.le_of_lt_succ ij.1.isLt)⟩
 have hu:z14 (e7 n) u :=
   zCu U.subtype (generic_powers B a w hw C)
 have hc: (C+1)*r≤C+C*H := by
   simpa [Fintype.card_prod] using hu.fintype_card_le_finrank.trans (hC C)
 by_contra! hn
 have h:=(zBI (C+1) (Nat.succ_le_of_lt hn)).trans hc
 rw [Nat.mul_succ,Nat.succ_mul] at h
 omega
end
end q9aDOab
end
