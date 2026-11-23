import ProximityPrize.SubmissionLower.ZCIcQjc
import ProximityPrize.SubmissionLower.ZU4mhUb
import ProximityPrize.SubmissionLower.Zqmzf9b
import ProximityPrize.SubmissionLower.ZWZGjEc
import ProximityPrize.SubmissionLower.ZBRA0Kc
set_option Elab.async false
set_option autoImplicit true
namespace qSCPCwb
noncomputable section
open P6 (K)
open P6_6 (Messages m6 gZ)
open P6_6_5 (Zl Fb R4 acg)
open aR (af ao cK extend)
open oR (qg Rr separant)
open we (cH fW qY Yk zq D7 a3H cVV)
open Polynomial
open scoped BigOperators
open private bcJ bI4 cLF from ProximityPrize.SubmissionLower.ZBRA0Kc
def c1 :Prop :=
  ∀ v,v≤ m6.t → ∀ n (f :Fin n→af 3),Zl v f →
    ∀ T : ∀ i,Gf v (f i),Nonempty (bAb v f T)
def c2 :Prop :=
  ∀ v,v≤ m6.t → ∀ n (f :Fin n→af 3),Zl v f →
    ∀ a∈Ji f,aGt (f a.1) a.2 →
      ∃ Q:Bk,acU (f a.1) Q ∧
        ∀ S:ao[X],S.natDegree≤gZ →
          zq S∈D7 (f a.1) a.2 →
            afs S∈MvPolynomial.zeroLocus cH Q
private theorem d4G {v n:ℕ} {f :Fin n→af 3}
    (T : ∀ i,Gf v (f i)) {i:Fin n} {S:ao[X]}
    (hS:S.natDegree≤gZ) (hr :qg 2 (f i) S) (hw : ¬ Fb (f i)) :
    ∃ P,(i,P)∈Ji f∧zq S∈D7 (f i) P:= by
  have hzero :zq S∈MvPolynomial.zeroLocus cH (BW (f i)) := by
    apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
    apply Ideal.span_le.mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    change g∈RingHom.ker (MvPolynomial.aeval (zq S))
    rw [RingHom.mem_ker]
    change MvPolynomial.eval (zq S) g=0
    rcases hg with rfl | rfl
    · rw [a3H,hr.1,map_zero]
    · rw [a3H,(T i).actual S hS hr |>.1,map_zero]
  have hsep:MvPolynomial.eval (zq S) (fW (separant (f i)))≠0:= by
    rw [a3H]
    exact fun h=>hr.2 ((map_eq_zero_iff qY Yk).mp h)
  obtain ⟨P,hP,hy⟩:=MvPolynomial.exists_retainedMinimalPrime_of_mem_zeroLocus
    (BW (f i)) (fW (separant (f i))) (zq S) hzero hsep
  exact ⟨P,azC.mpr ⟨hw,hP⟩,⟨hy,hsep⟩⟩
private theorem bLf {n:ℕ} {f :Fin n→af 3} {a :aap n}
    {S:ao[X]} (ha :a∈Ji f) (hS:zq S∈D7 (f a.1) a.2) :
    qg 2 (f a.1) S:= by
  have hp:=(Ideal.mem_retainedMinimalPrimes.mp (azC.mp ha).2).1.le
  have hz :fW (f a.1)∈BW (f a.1) :=Ideal.subset_span (by simp)
  have he :MvPolynomial.eval (zq S) (fW (f a.1))=0 :=
    hS.1 _ (hp hz)
  have hsep:=hS.2
  rw [a3H] at he hsep
  refine ⟨?_,fun h=>hsep (by rw [show cK (separant (f a.1)) S=0 from h,map_zero])⟩
  exact (map_eq_zero_iff qY Yk).mp he
private theorem eAG {w Γ s v n f} (hm:Messages w Γ s)
    {T : ∀ i,Gf v (f i)} (M:bAb v (n:=n) f T)
    {a :aap n} (ha :a∈Ji f) (hi : ¬ aGt (f a.1) a.2) :
    (bcJ f Γ s a).card≤M.length a*M.degree a := by
  classical
  have hsub:bcJ f Γ s a⊆Γ:= fun _ hg=>(bI4.mp hg).1
  have hdeg (γ:K) (hγ:γ∈Γ) : (extend (s γ)).natDegree≤gZ:= by
    simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
  by_cases hlen:M.length a=1
  · have hsimp :Lx (f a.1) a.2=1 := by rw [← M.length_eq a ha,hlen,Nat.cast_one]
    have hn:fW (Vk (f a.1))∉a.2 := fun hn=>hi ⟨hsimp,hn⟩
    obtain ⟨hfinite,hcard⟩:=M.points a ha hn
    let pt:= fun γ=>zq (n:=3) (extend (s γ))
    have hpts : ↑((bcJ f Γ s a).image pt)⊆avD (f a.1) a.2 := by
      intro y hy
      obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hy
      obtain ⟨hmem,hy⟩:=bI4.mp hγ
      have hreg:=bLf ha hy
      exact ⟨hy,by rw [a3H,((T a.1).actual _ (hdeg γ hmem) hreg).2.1,map_zero]⟩
    have hle :=(Set.ncard_le_ncard hpts hfinite).trans hcard
    rw [Set.ncard_coe_finset,Finset.card_image_of_injOn ((cVV s Γ hm.distinct).mono hsub)] at hle
    simpa [hlen] using hle
  · have htwo:2≤M.length a := by have :=M.length_pos a ha; omega
    obtain ⟨Q,hprime,hdim,hd,hdegree,hrec⟩:=M.qv a ha htwo
    have hm' := hm.mono hsub
    have hcap:=c1x hm' Q hprime hdim hdegree (by
      intro γ hγ
      obtain ⟨hmem,hy⟩:=bI4.mp hγ
      have hreg:=bLf ha hy
      rw [← ((T a.1).actual _ (hdeg γ hmem) hreg).2.2]
      exact hrec _ hy)
    exact (dRT hm' hd hcap).trans (Nat.mul_le_mul_right _ htwo)
private theorem coefficient_family {w Γ s} (hm:Messages w Γ s)
    (C:Finset Bk) (d:Bk→ℕ)
    (hcut : ∀ Q∈C,Q.IsPrime∧(MvPolynomial.affineHilbertPolynomial Q).natDegree≤1 ∧
      MvPolynomial.affineDegree Q≤(d Q:ℚ)) :
    ∃ F:Rr w Γ s,F.n=C.card∧F.BJ=(∑ Q∈C,d Q) ∧
      ∀ γ∈Γ,∀ Q∈C,afs (extend (s γ))∈MvPolynomial.zeroLocus cH Q →
        γ∈F.CF:= by
  classical
  let e :Fin C.card ≃ C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
  let part:Fin C.card→Finset K:= fun i=>Γ.filter fun γ =>
    afs (extend (s γ))∈MvPolynomial.zeroLocus cH (e i).val
  have hs : ∀ i,part i⊆Γ:= fun _=>Finset.filter_subset _ _
  let F:Rr w Γ s :=⟨C.card,part,fun i=>d (e i).val,hs,fun i=> by
    obtain ⟨hp,hdim,hd⟩:=hcut (e i).val (e i).property
    exact c1x (hm.mono (hs i)) (e i).val hp hdim hd
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)⟩
  refine ⟨F,rfl,?_,?_⟩
  · change (∑ i:Fin C.card,d (e i).val) = ∑ Q∈C,d Q
    rw [Equiv.sum_comp e (fun P:C=>d P.val),Finset.sum_coe_sort]
  · intro γ hγ Q hQ hy
    let i:=e.symm ⟨Q,hQ⟩
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hγ,?_⟩⟩
    simpa [i] using hy
theorem of_children (h1 :c1) (h2 :c2) :P6_6_5.c1 := by
  classical
  intro w Γ s hm v hv n f hf marks
  let T (i:Fin n) :=Classical.choice (qP f hf i)
  obtain ⟨M⟩:=h1 v hv n f hf T
  let direct :=(Ji f).filter fun a => ¬ aGt (f a.1) a.2
  let isolated:=direct.biUnion (bcJ f Γ s)
  have hmixed:isolated.card≤R4 v := by
    calc
      _ ≤ ∑ a∈direct,(bcJ f Γ s a).card:=Finset.card_biUnion_le
      _ ≤ ∑ a∈direct,M.length a*M.degree a :=Finset.sum_le_sum fun a ha =>
        eAG hm M (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a∈Ji f,M.length a*M.degree a :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _≤_:=M.total
  let stable :=(Ji f).filter fun a=>aGt (f a.1) a.2
  have heach (a :stable) :=h2 v hv n f hf a.val (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp a.property).2
  choose Q hQ hrec using heach
  let C:=stable.attach.image Q
  have hfresh : ∀ P∈C,∃ i,¬ Fb (f i)∧acU (f i) P:= by
    intro P hp
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hp
    have ha :=(Finset.mem_filter.mp a.property).1
    exact ⟨a.val.1,(azC.mp ha).1,hQ a⟩
  obtain ⟨d,hd,hsum⟩:=ed8 hf C hfresh
  have hcut (P:Bk) (hp:P∈C) :P.IsPrime ∧
      (MvPolynomial.affineHilbertPolynomial P).natDegree≤1 ∧
      MvPolynomial.affineDegree P≤(d P:ℚ) := by
    obtain ⟨i,_,h⟩:=hfresh P hp
    exact ⟨h.solution.prime,h.solution.dimension.le,(hd P hp).2⟩
  obtain ⟨F,hn,hcap,hmem⟩:=coefficient_family hm C d hcut
  have hFnum :F.n≤acg v := by
    calc
      F.n = ∑ P∈C,1 :=hn.trans (Finset.card_eq_sum_ones C)
      _ ≤ ∑ P∈C,d P:=Finset.sum_le_sum fun P hp=>(hd P hp).1
      _≤_:=hsum
  refine ⟨⟨isolated,cLF w Γ s,F,?_,?_,?_,?_⟩⟩
  · intro γ hγ
    obtain ⟨i,hi,hw⟩:=marks γ hγ
    have hdeg: (extend (s γ)).natDegree≤gZ:= by
      simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
    obtain ⟨P,hp,hy⟩:=d4G T hdeg hi hw
    by_cases hs :aGt (f i) P
    · let a :stable :=⟨(i,P),Finset.mem_filter.mpr ⟨hp,hs⟩⟩
      have hQC:Q a∈C:=Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩
      exact Finset.mem_union_right _ (hmem γ hγ (Q a) hQC (hrec a _ hdeg hy))
    · have hγiso:γ∈isolated:=Finset.mem_biUnion.mpr
        ⟨(i,P),Finset.mem_filter.mpr ⟨hp,hs⟩,bI4.mpr ⟨hγ,hy⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hγiso)
  · have hz : (cLF w Γ s).BJ=0:= by
      change (∑ i:Fin 0,(Fin.elim0 i:ℕ))=0
      exact Finset.sum_eq_zero fun i _=>Fin.elim0 i
    simpa [hz] using hmixed
  · exact hcap.trans_le hsum
  · change 0+F.n≤2*acg v
    omega
end
end qSCPCwb
