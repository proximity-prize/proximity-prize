import ProximityPrize.SubmissionLower.ZPYr4Qd
import ProximityPrize.SubmissionLower.ZLVq30b
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.ZdFBqnb
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZalmDpd
import ProximityPrize.SubmissionLower.Zt62ONe
import ProximityPrize.SubmissionLower.ZmJja2a
import ProximityPrize.SubmissionLower.ZKgVGSb
import ProximityPrize.SubmissionLower.ZDbTvLe
import ProximityPrize.SubmissionLower.ZRYXIua
import ProximityPrize.SubmissionLower.ZflC1Fd
import ProximityPrize.SubmissionLower.ZPKTqyb
import ProximityPrize.SubmissionLower.Z32V4rd
set_option Elab.async false
open _root_ renaming Algebra.IsSeparable → zw7, Ideal.Quotient.mk → zVv, Ideal.Quotient.mkₐ → zvR, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.X → z9v, RingHom.ker → zdq
section
set_option autoImplicit true
namespace qpmLJKb
noncomputable section

open OH (N8)
open qPP0zte (slice)
def freeIdx (k :Fin 3) :Fin 4 :=if k=0 then 0 else 1
def coord (k :Fin 3) (Q:Ideal gT.Ambient) (i:Fin 4) :N8 ⧸ slice k Q :=
  zVv _ (z9v i)
end
end qpmLJKb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace q36SZud
noncomputable section
open K1 cu gT OH
open Rk (KR taylor)
open MvPolynomial
theorem separable_of_small {F E :Type} [Field F] [CharP F p] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h:zsE F E<p) :zw7 F E := by
  let:Fact (Nat.Prime p) :=⟨(CharP.char_is_prime_or_zero F p).resolve_right (by decide)⟩
  obtain ⟨n,hn⟩:=finInsepDegree_eq_pow F E p
  apply (isSeparable_iff_finInsepDegree_eq_one F E).mpr
  cases n with
  | zero=>simpa using hn
  | succ n =>
    have hle :p≤p^(n+1) := by
      rw [pow_succ']
      exact Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
    have hdvd:p^(n+1)∣zsE F E := by
      rw [← hn,← Field.finSepDegree_mul_finInsepDegree F E]
      exact dvd_mul_left _ _
    exact (not_lt_of_ge (hle.trans (Nat.le_of_dvd Module.finrank_pos hdvd)) h).elim
theorem taylor_eval {K T:Type*} [CommRing K] [CommRing T] [Algebra K T]
    (c u:Fin 4→T) (F:z3y (Fin 4) K) :
    aeval (fun i=>c i+u i) F =
      ∑ d∈(taylor F).support,aeval c (KR d F) * ∏ i∈d.support,u i^d i:= by
  let Ψ:z3y (Fin 4) (z3y (Fin 4) K) →+* T :=
    eval₂Hom (aeval c:z3y (Fin 4) K →ₐ[K] T).toRingHom u
  have h:Ψ.comp (taylor (σ:=Fin 4) (R:=K))=(aeval (fun i=>c i+u i)).toRingHom:= by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Ψ,taylor]
    · intro i
      simp [Ψ,taylor,add_comm]
  have h2 :aeval (fun i=>c i+u i) F=Ψ (taylor F) :=(RingHom.congr_fun h F).symm
  rw [h2]
  change eval₂ _ u (taylor F)= _
  rw [MvPolynomial.eval₂_eq]
  rfl
theorem prod_mem_pow {S:Type*} [CommRing S] (I:Ideal S) (t:Finset (Fin 4)) (r :Fin 4→S)
    (d:Fin 4→ℕ) (h : ∀ i∈t,r i∈I) : ∏ i∈t,r i^d i∈I ^(∑ i∈t,d i) := by
  classical
  induction t using Finset.induction_on with
  | empty=>simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (h a (by simp)) _)
      (ih fun i hi=>h i (by simp [hi]))
section
variable {K:Type} [Field K] [CharP K p]
local notation "R" => MvPolynomial (Fin 4) K
theorem main (I:Ideal R)
    [I.IsMaximal] [Module.Finite K (R ⧸ I)] (f :R)
    (v :ℕ) (hlen:zsE K (R ⧸ I)<p)
    (hh : ∀ a :Fin 4 →₀ ℕ,(∑ i,a i)≤v→KR a f∈I) :f∈I ^(v+1) := by
  letI:Field (R ⧸ I) :=Ideal.Quotient.field I
  have hlen' : zsE K (R ⧸ I)<p:=hlen
  have :zw7 K (R ⧸ I) :=separable_of_small hlen'
  have :Algebra.FormallyEtale K (R ⧸ I) :=Algebra.FormallyEtale.of_isSeparable K (R ⧸ I)
  let b:R →ₐ[K] R ⧸ I ^(v+1) :=zvR K (I ^(v+1))
  let q:R →ₐ[K] R ⧸ I:=zvR K I
  have hle :I ^(v+1)≤I:=Ideal.pow_le_self (Nat.succ_ne_zero v)
  let g:R ⧸ I ^(v+1) →ₐ[K] R ⧸ I:=Ideal.Quotient.factorₐ K hle
  have hker :zdq g=I.map b:= by
    change zdq (Ideal.Quotient.factor hle)=I.map (zVv _)
    calc
      _=(zdq (zVv I)).map (zVv (I ^(v+1))) :=
        Ideal.ker_quotient_lift (zVv I) _
      _ = _:= by rw [Ideal.mk_ker]
  have hnil: (zdq g)^(v+1) = ⊥ := by
    rw [hker,← Ideal.map_pow]
    exact Ideal.map_quotient_self (I ^(v+1))
  have hn:IsNilpotent (zdq g) :=⟨v+1,hnil⟩
  have hg:Function.Surjective g:=Ideal.Quotient.factor_surjective hle
  let s :=Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K (R ⧸ I)) g hg hn
  have hs (x :R ⧸ I) :g (s x)=x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K (R ⧸ I)) g hg hn x
  let c (i:Fin 4) :R ⧸ I ^(v+1) :=s (q (z9v i))
  let u (i:Fin 4) :R ⧸ I ^(v+1) :=b (z9v i) - c i
  have hu : ∀ i,∃ r∈I,u i=b r := by
    intro i
    obtain ⟨r0,hr0⟩:=Ideal.Quotient.mk_surjective (c i)
    have hbr :b r0=c i:=hr0
    have hui:u i=b (z9v i - r0) := by
      change b (z9v i) - c i= _
      rw [map_sub,hbr]
    refine ⟨z9v i - r0,?_,hui⟩
    have hz :g (u i)=0:= by
      change g (b (z9v i) - s (q (z9v i)))=0
      rw [map_sub,hs]
      exact sub_self _
    rw [hui] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hfun: (fun i=>c i+u i)=fun i=>b (z9v i) := by
    funext i
    simp [u]
  have hbf :b f=aeval (fun i=>c i+u i) f := by
    rw [hfun]
    exact congrArg (fun φ:R →ₐ[K] R ⧸ I ^(v+1)=>φ f) (aeval_unique b)
  have hc : ∀ h∈I,aeval c h=0:= by
    intro h hI'
    have e :aeval c=s.comp q:=(aeval_unique (s.comp q)).symm
    rw [e]
    change s (zVv I h)=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hI',map_zero]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change b f=0
  rw [hbf,taylor_eval]
  apply Finset.sum_eq_zero
  intro d _
  by_cases hd: (∑ i,d i)≤v
  · rw [hc _ (hh d hd),zero_mul]
  · choose r hrI hr using hu
    have hprod : ∏ i∈d.support,u i^d i=b (∏ i∈d.support,r i^d i) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun i _=> by rw [hr i,map_pow]
    have hmem : ∏ i∈d.support,r i^d i∈I ^(v+1) := by
      have h1 :=prod_mem_pow I d.support r (fun i=>d i) (fun i _=>hrI i)
      have h2 : ∑ i∈d.support,d i = ∑ i,d i :=
        Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=> by simpa using hi)
      rw [h2] at h1
      exact Ideal.pow_le_pow_right (by omega) h1
    have hz :b (∏ i∈d.support,r i^d i)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hprod,hz,mul_zero]
end
theorem proof :qPP0zte.c2 := by
  intro I f v hI hfin hlen hh
  have :CharP aQ p:=charP_of_injective_ringHom
    ((algebraMap FX aQ).comp jz).injective p
  exact main (K:=aQ) I f v hlen hh
end
end q36SZud
end
section
set_option autoImplicit true
namespace q6mIPod
theorem proof :qwRB2oc.c3 :=
  qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof) qU1uHGd.proof
end q6mIPod
end
section
set_option autoImplicit true
namespace qwDmyCd
theorem proof :qV3aOCd.c1 :=
  q6CrDDe.of_children q978Lma.proof P5_7_1_5_4_2_1_2.proof
end qwDmyCd
end
section
set_option autoImplicit true
namespace qJ2rffd
theorem proof :qV3aOCd.c2 :=
  qvWbALd.of_children q9aDOab.proof qmpFDTd.proof
end qJ2rffd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qaVSQCe
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P6 (K p)
open cu (L)
open E7 (CurvePlace poleOrder KB)
open qb0hmCe (CurveModel)
open q1kuFjb (principal)
open qFD8jve (aFA sheetPole)
open P5_7_3_5_2 (Sheet)
open qxPDCsa (discDegree Good)
open qLXroAb (chargeCoeff)
open qxtWb5a (polarDegree poleFee)
open private choose_variation restrict zJ pole_sum height_zero from ProximityPrize.SubmissionLower.Zay1XCa
private theorem disc_le {D e W:ℕ} (he :0<e) (hW:e*D ≤W) :
    discDegree D e W≤polarDegree D e W:= by
  have h₁: (2*e-1)*W=(2*e-2)*W+W:= by
    rw [← Nat.add_one_mul,show 2*e-2+1=2*e-1 by omega]
  have h₂:e*e*D =e*(e-1)*D + e*D:= calc
    _=e*(e-1+1)*D:= by rw [Nat.sub_add_cancel he]
    _ = _:= by ring
  rw [discDegree,polarDegree,h₁,h₂]
  omega
private theorem sum_charge {q:qkgz7gb.PlaneCurve} {Cq:CurveModel q} {z :K→K}
    {S:K→K[X]} (F:Sheet Cq z S) {g:Cq.E} (hg:g≠0)
    {T:Finset K} (hT:T⊆F.marks) {k :ℕ}
    (h : ∀ w:CurvePlace L Cq.E,w.value g≤WithZero.exp ((k*sheetPole w.value F.f :ℕ) :ℤ)) :
    ∑ γ∈T,KB (F.place γ).value g≤k*F.h:= by
  let Ju (w:CurvePlace L Cq.E) :=KB w.value g
  have hf :=(principal Cq g).2.1
  calc
    _ = ∑ w∈T.image F.place,Ju w:= by rw [sum_image (F.distinct.mono hT)]
    _ ≤ ∑ w∈hf.toFinset∪T.image F.place,Ju w :=
      sum_le_sum_of_subset_of_nonneg subset_union_right fun _ _ _=>Nat.zero_le _
    _ = ∑ᶠ w,Ju w:=(finsum_eq_finsetSum_of_support_subset Ju
      (s :=hf.toFinset∪T.image F.place) (fun w hw=>mem_union_left _ (hf.mem_toFinset.mpr hw))).symm
    _ = ∑ᶠ w:CurvePlace L Cq.E,poleOrder w.value g:=(principal Cq g).2.2.1.symm
    _≤_:=pole_sum F hg h
theorem proof :qxtWb5a.c4 := by
  have disc:qLXroAb.c1 :=qTLMB9a.proof
  have refs :qLXroAb.c2 :=qoyAGrd.proof
  have infty :qLXroAb.c3:=(qb1WXKc.of_children qB4SPFa.proof qvlURsa.proof)
  have bY:qLXroAb.c4 :=(q9uVqha.of_children qGnKhWc.proof qralmib.proof qBMP0Kd.proof qi87Bgb.proof q2ANK6b.proof qk9SLHb.proof)
  have elim:qLXroAb.c5:=(qfzuawb.of_children (qHJDQEb.of_children qK8v0ue.proof qIPidRd.proof q1XnGpd.proof) (qnSUPza.of_children P5_7_1_5Q.c434521 P5_7_1_5Q.c434522) qkEA7Vd.proof)
  have orders :qLXroAb.c6:=(qZn79Eb.of_children qOHrlse.proof qydrhVa.proof qi1t4Ta.proof P5_7_1_5Q.c43464)
  have norm:qLXroAb.c7:=qXARP7c.proof
  intro Q Cq z S F D e W hD hDp hd he hp hW hguard hw hS
  have he' : 3≤F.d:=hd ▸ he
  have hp' : F.d<p:=hd ▸ hp
  obtain ⟨hδ,hδd,hδb,hsimple⟩:=disc F D W hp' hw
  have hδp:F.f.discr.natDegree<p :=
    (hδd.trans (hd.symm ▸ disc_le (by omega) hW)).trans_lt hguard
  obtain ⟨V,hV⟩:=choose_variation F hsimple
  obtain ⟨A⟩:=refs V D W hw
  let T:=F.marks.filter (Good A)
  have hT:T⊆F.marks :=filter_subset _ _
  have ht:T⊆V.marks := by
    rw [hV]
    exact fun γ hγ=>mem_filter.mpr ⟨hT hγ,(mem_filter.mp hγ).2.1⟩
  let U:=restrict V ht
  obtain ⟨P,hchart⟩:=bY U he' hp'
  obtain ⟨R,hR,hb,hdiv⟩:=elim P D W he' hD hDp (hd ▸ hW) hw
  have hc:chargeCoeff R≠0:=leadingCoeff_ne_zero.mpr (trailingCoeff_nonzero_iff_nonzero.mpr hR)
  have hbound:=sum_charge F hc hT (fun w=>hb w R.natTrailingDegree R.trailingCoeff.natDegree)
  have hlocal (γ:K) (hγ:γ∈T) :D*U.DG D γ ≤
      KB (F.place γ).value (chargeCoeff R) := by
    have hg:=(mem_filter.mp hγ).2
    have hi:=infty A hp' hw γ (ht hγ) hg (hS γ (hT hγ))
    have hv :=orders U P hp' hδ hδp γ hγ hg.1 (hchart γ hγ).some
    have hbr :aFA (F.place γ).value R 0:= by
      simpa only [height_zero (hT hγ),Nat.mul_zero] using hb (F.place γ)
    have hn:=norm P (F.place γ) (U.den γ) R D (U.den_ne γ hγ) hR hbr hdiv hv
    change D *max (U.den γ).natDegree ((U.num γ).natDegree-D)≤_
    rw [max_eq_left (by change (V.num γ).natDegree-D ≤(V.den γ).natDegree; omega)]
    exact hn
  refine ⟨U,(zJ A hδ hδb).trans (Nat.mul_le_mul_right _ (by omega)),?_⟩
  apply Nat.le_of_mul_le_mul_left _ hD
  change D*(∑ γ∈T,U.DG D γ)≤D*(poleFee D e W*F.h)
  rw [mul_sum]
  refine (sum_le_sum hlocal).trans (hbound.trans_eq ?_)
  rw [hd]
  exact mul_assoc D (poleFee D e W) F.h
end
end qaVSQCe
end
section
set_option autoImplicit true
namespace qVOLyRb
theorem proof :qwRB2oc.c4 :=qaVSQCe.proof
end qVOLyRb
end
