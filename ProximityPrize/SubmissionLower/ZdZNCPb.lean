import ProximityPrize.SubmissionLower.ZeFfOZc
import ProximityPrize.SubmissionLower.ZrIiE0d
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.A
set_option Elab.async false
open _root_ renaming Fintype.card_fin → zgY, Fintype.linearCombination → z3d, LinearMap.ker → z83, LinearMap.range → zWl, Module.finrank → zsE, Module.finrank_pi → zJ6
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace agU
noncomputable section
open Polynomial
open cu (L Shape triangle)
open DP Ge aY9
open P1 (K I)
open scoped BigOperators Polynomial
open private cb9 from ProximityPrize.SubmissionLower.Z
open private c7U from ProximityPrize.SubmissionLower.B4
def c1 :Prop :=
  ∀ (F:Type) [Field F] [CharP F K1.p] (s :Shape),
    s.B<K1.p →
    ∀ (H :F[X]) (lift: (kq F)[X])
      (α:F) (side :Fin 2) (a b c:F),
      H.eval α=0→H.derivative.eval α≠0→b≠0 →
      lift.eval (algebraMap F (kq F) α)=residue side a b c →
      ∃ d:Fin (arY s)→ℕ,
        (∑ r,d r)≤ajD s.B s.J ∧
        ∃ tests :Fin (arY s)→Gm F →ₗ[F] i5 F,
          (∀ r P,adk s P→bbs s.U (d r) side (tests r P)) ∧
          ∀ P,adk s P→(∀ r,tests r P=0) →
            (pW ((Polynomial.X (R:=kq F) -
                Polynomial.C (algebraMap F (kq F) α))^(s.B+s.J)) :
              EM (kq F))∣forward H lift P
private abbrev a1b {h:ℕ} (s :Shape) (d:Fin (2*h)→Fin (arY s)→ℕ) :=
 Σ t:Fin (2*h),Σ r :Fin (arY s),Fin (triangle s.U + (s.U+1)*d t r)
private theorem glT {h:ℕ} (s :Shape)
    (d:Fin (2*h)→Fin (arY s)→ℕ) (hd : ∀ t,(∑ r,d t r)≤ajD s.B s.J) :
    Fintype.card (a1b s d)≤azS h s+2*h*(s.U+1)*ajD s.B s.J:= by
  classical
  simp only [a1b,Fintype.card_sigma,zgY]
  calc
    (∑ t:Fin (2*h),∑ r :Fin (arY s),(triangle s.U + (s.U+1)*d t r)) ≤
        ∑ _:Fin (2*h),(arY s*triangle s.U + (s.U+1)*ajD s.B s.J) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,zgY,nsmul_eq_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _=azS h s+2*h*(s.U+1)*ajD s.B s.J:= by
      simp only [Finset.sum_const,Finset.card_univ,zgY,nsmul_eq_mul]
      change (2*h)*(arY s*triangle s.U + (s.U+1)*ajD s.B s.J)= _
      unfold azS arY
      ring
private theorem deb (hlocal:c1)
    {F ι:Type} [Field F] [CharP F K1.p] [Fintype ι] {h:ℕ}
    {H :F[X]} {lift: (kq F)[X]}
    (G:bk5 h H lift) (s :Shape) (hs :s.B<K1.p) (P:ι→Gm F)
    (hP : ∀ k,adk s (P k)) {n:ℕ} (M:Matrix (Fin n) ι F)
    (hM : ∀ v,M.mulVec v=0↔a0X s H lift (z3d F P v)) :
    M.rank≤azS h s+2*h*(s.U+1)*ajD s.B s.J:= by
  classical
  have ht (t:Fin (2*h)) :=hlocal F s hs H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.aiq t) (G.simple t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  have hread (t:Fin (2*h)) (r :Fin (arY s)) :=dc6 F s.U (d t r) (G.side t)
  choose read hread using hread
  let f : (ι→F) →ₗ[F] (a1b s d→F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1).comp (z3d F P))
  have hker :z83 f≤z83 M.mulVecLin:= by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply cb9 s G
    intro t
    have hv' := ddL hP v
    apply htest t _ hv'
    intro r
    apply hread t r _ (hwindow t r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t,r,k⟩
  have hn:=Submodule.finrank_mono hker
  have hr :zsE F (zWl f) ≤
      azS h s+2*h*(s.U+1)*ajD s.B s.J:= by
    refine (zWl f).finrank_le.trans ?_
    rw [zJ6]
    exact glT s d hd
  have hf :=f.finrank_range_add_finrank_ker
  have hm:=M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega
private theorem c4y (hlocal:c1) {h:ℕ} (hpos :0<h) (hchar :h<K1.p)
    {D:jF h} (Crt:zG D) (word:I→L) (s :Shape) (hs :s.B<K1.p) (W:ℕ) :
    zsE L (aq7 h word s W) ≤
      azS h s+2*h*(s.U+1)*ajD s.B s.J +
        zsE L (complete Crt word s W) := by
  classical
  obtain ⟨E⟩:=c7U hpos hchar D Crt
  let A:=aq7 h word s W
  let _:Module.Finite L A:=dPs h word s W
  let d:=zsE L A
  let basis :=Module.finBasis L A
  let P:Fin d→Source := fun k=>basis k
  have hP (k :Fin d) :adk s (P k) :=dPt (basis k).property
  obtain ⟨n,M,hspecial,hg⟩:=bzR.proof E s (Fin d) P hP
  let embed:=genericPoint.comp (Polynomial.C (R:=L))
  let _:CharP L K1.p:=charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _:CharP lN K1.p :=
    charP_of_injective_ringHom (f :=embed) (b4F.comp Polynomial.C_injective) K1.p
  have hgen:=deb hlocal E.genericPoles s hs _
    (fun k=>gp2 embed (hP k)) _ hg
  have hrank :=(gtP M).trans hgen
  let f :=(M.map Uv).mulVecLin
  have hf : ∀ v :Fin d→L,
      z3d L P v=((basis.equivFun.symm v :A) :Source) := by
    intro v
    rw [Fintype.linearCombination_apply,Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul,Submodule.subtype_apply,P] using
      map_sum A.subtype (fun k=>v k•basis k) Finset.univ
  have hk (v :z83 f) :
      ((basis.equivFun.symm (v :Fin d→L) :A) :Source)∈complete Crt word s W:= by
    have hv :=(hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property,hv⟩
  let g:z83 f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (z83 f).subtype) hk
  let _:Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj:Function.Injective g:= by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x :complete Crt word s W=>(x :Source)) hvw
  have hkd:=LinearMap.finrank_le_finrank_of_injective hginj
  have hdf :=f.finrank_range_add_finrank_ker
  rw [zJ6,zgY] at hdf
  change zsE L (zWl f)≤_ at hrank
  change d≤_
  omega
end
end agU
end
section
set_option backward.isDefEq.respectTransparency false
namespace aeL
noncomputable section
open Polynomial Matrix
open cu (Shape)
open Ge anc
open agU (Bb)
open scoped BigOperators Matrix Polynomial
def c1 :Prop :=
  ∀ (F:Type) [Field F] (s :Shape) (α:F) (z :kq F),
    (∀ (t:Offset s) (q:jJ s),
      bTl (kq F) (Gv s t) (Bb s.B s.J t.val q.val)
        (aIN s t q)) →
    ∀ P:Gm F,adk s P →
      (∀ t:Offset s,Pa s t z *ᵥ
        (fun u=>algebraMap (i5 F) (kq F) (input α u P))=0) →
      ∀ (q:jJ s) (k :NQ s q.val),
        (Polynomial.X (R:=kq F))^(s.B+s.J) ∣
          aRi s q.val (aVG s α z P q) k
def c2 :Prop :=
  ∀ (F ι κ:Type) [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M:Matrix ι κ (Ru F)) (D:ℕ),bQp M D →
    ∃ (Q:Matrix ι κ F[X]) (L:Matrix ι ι (Ru F)) (d:ι→ℕ),
      M=L*Q.map (algebraMap F[X] (Ru F)) ∧
      (∀ r u,(Q r u).natDegree≤d r)∧(∑ r,d r)≤D
theorem of_children (hLocal:c1) (hBasis :c2) :
    agU.c1 := by
  classical
  intro F _ _ s _ H lift α side a b c hH _ hb hz
  have hRows (t:Offset s) :=
    hBasis F (Pivot s t) (Lh s t) _ _ (dAa F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t:Offset s) (r :Pivot s t) :=btV α side (Q t r)
  let e :=aJo s
  refine ⟨fun k=>d (e k).1 (e k).2,fY5 s d hsum,
    fun k=>tests (e k).1 (e k).2,?_,?_⟩
  · intro k P hP
    exact eMZ α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t:Offset s) (r :Pivot s t) :tests t r P=0:= by
      let testAt (k :Σ t:Offset s,Pivot s t) :=tests k.1 k.2 P
      have hk :testAt (e (e.symm ⟨t,r⟩))=0:=hzero (e.symm ⟨t,r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z :=residue side a b c
    have hslots :=hLocal F s α z
      (fun t q=>eKM (kq F) (Gv s t)
        (Bb s.B s.J t.val q.val) (aIN s t q)) P hP
      (fun t=>eM0 t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd:=cyV.proof F s (aVG s α z P) hslots
    rw [← cyU.proof F s α z P hP] at hd
    exact gDE H lift α z (s.B+s.J) P hH hz
      (exa α z (s.B+s.J) P hd)
end
end aeL
end
