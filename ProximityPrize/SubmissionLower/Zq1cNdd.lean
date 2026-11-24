import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZTOdMMe
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P5_7_4
noncomputable section
open P5 (K I p)

open cu (L Shape)
open DP Ge aY9 Polynomial
open scoped Polynomial BigOperators
open private cb9 from ProximityPrize.SubmissionLower.Z
open private c7U from ProximityPrize.SubmissionLower.B4
private theorem deb (hlocal:LocalPole)
    {F ι:Type} [Field F] [CharP F K1.p] [Fintype ι] {h:ℕ}
    {H :F[X]} {lift: (kq F)[X]}
    (G:bk5 h H lift) (s :Shape)
    (hJ:s.J≤ s.B) (hU:s.B≤ s.U) (hs :s.B<K1.p)
    (P:ι→Gm F) (hP : ∀ k,adk s (P k))
    {n:ℕ} (M:Matrix (Fin n) ι F)
    (hM : ∀ v,M.mulVec v=0↔a0X s H lift (Fintype.linearCombination F P v)) :
    M.rank≤2*h*poleRank s := by
  classical
  choose tests htests using fun t =>
    hlocal F s hJ hU hs (G.root t) (G.side t) (G.a t) (G.b t) (G.c t) (G.b_ne t)
  let f : (ι→F) →ₗ[F] ((Fin (2*h)×Fin (poleRank s))→F) :=
    LinearMap.pi fun r =>
      (LinearMap.proj r.2).comp ((tests r.1).comp (Fintype.linearCombination F P))
  have hker :LinearMap.ker f≤LinearMap.ker M.mulVecLin:= by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply cb9 s G
    intro t
    apply anc.gDE _ _ _ _ _ _ (G.aiq t) (G.centre t)
    apply htests t _ (ddL hP v)
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) (t,k)
  have hn:=Submodule.finrank_mono hker
  have hr :=(LinearMap.range f).finrank_le
  simp only [Module.finrank_pi,Fintype.card_prod,Fintype.card_fin] at hr
  have hf :=f.finrank_range_add_finrank_ker
  have hm:=M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega
private theorem c4y (hlocal:LocalPole) {h:ℕ} (hpos :0<h) (hchar :h<K1.p)
    {D:jF h} (Crt:zG D) (word:I→L) (s :Shape)
    (hJ:s.J≤ s.B) (hU:s.B≤ s.U) (hs :s.B<K1.p) (W:ℕ) :
    Module.finrank L (aq7 h word s W) ≤
      2*h*poleRank s +
        Module.finrank L (complete Crt word s W) := by
  classical
  obtain ⟨E⟩:=c7U hpos hchar D Crt
  let A:=aq7 h word s W
  let _:Module.Finite L A:=dPs h word s W
  let d:=Module.finrank L A
  let basis :=Module.finBasis L A
  let P:Fin d→Source := fun k=>basis k
  have hP (k :Fin d) :adk s (P k) :=dPt (basis k).property
  obtain ⟨n,M,hspecial,hg⟩:=bzR.proof E s (Fin d) P hP
  let embed:=genericPoint.comp (Polynomial.C (R:=L))
  let _:CharP L K1.p:=charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _:CharP lN K1.p :=
    charP_of_injective_ringHom (f :=embed) (b4F.comp Polynomial.C_injective) K1.p
  have hgen:=deb hlocal E.genericPoles s hJ hU hs _
    (fun k=>gp2 embed (hP k)) _ hg
  have hrank :=(gtP M).trans hgen
  let f :=(M.map Uv).mulVecLin
  have hf : ∀ v :Fin d→L,
      Fintype.linearCombination L P v=((basis.equivFun.symm v :A) :Source) := by
    intro v
    rw [Fintype.linearCombination_apply,Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul,Submodule.subtype_apply,P] using
      map_sum A.subtype (fun k=>v k•basis k) Finset.univ
  have hk (v :LinearMap.ker f) :
      ((basis.equivFun.symm (v :Fin d→L) :A) :Source)∈complete Crt word s W:= by
    have hv :=(hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property,hv⟩
  let g:LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
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
  rw [Module.finrank_pi,Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f)≤_ at hrank
  change d≤_
  omega
end
end P5_7_4
