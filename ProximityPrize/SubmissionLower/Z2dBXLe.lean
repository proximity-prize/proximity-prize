import ProximityPrize.SubmissionLower.ZikYn6c
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.Zb3VwYd
import ProximityPrize.SubmissionLower.ZedfuCc
import ProximityPrize.SubmissionLower.ZZBDV9b
import ProximityPrize.SubmissionLower.ZnMb5gd
import ProximityPrize.SubmissionLower.E3
set_option Elab.async false
open _root_ renaming Finset.filter_subset → zT0, Finset.single_le_sum → zfK, Finset.sum_eq_zero → zYF, Finset.sum_le_sum → zQk, Ideal.mem_span_singleton → zxV, Ideal.span → zye, Ideal.subset_span → zCn, Int.toNat_le_toNat → z0Z, IsFractionRing.injective → zxb, Multiset.prod_eq_zero_iff → z03, Multiset.toFinset_prod_dvd_prod → zc7, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.zeroLocus → zSD, Nat.zero_le → zD0, Polynomial.coeff_map → z0b, Polynomial.hasseDeriv → z75, Polynomial.map_zero → zgY, Polynomial.natDegree_prod_le → z8u, RingHom.ker → zdq, RingHom.ker_isPrime → zgL, Set.mem_singleton → zT1
section
set_option autoImplicit true
namespace qwbsesc
open P6_6_2
open xE (Flag oldCount m5 BH Jd AO)
open scoped BigOperators
def aak (lo hi cap:ℕ) :Prop :=
  ∃ p:kJ,rankBand p lo hi≤ cap
theorem aGH {lo mid hi a b:ℕ} (hl:lo≤ mid) (hr :mid≤hi)
    (ha :aak lo mid a) (hb:aak mid hi b) :aak lo hi (a+b) := by
  obtain ⟨p,hp⟩:=ha
  obtain ⟨q,hq⟩:=hb
  let aji:kJ:= fun s=>if s< mid then p s else q s
  have hL:rankBand aji lo mid=rankBand p lo mid := by
    unfold rankBand
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [show aji s=p s from ite_eq_left (Finset.mem_Ico.mp hs).2]
  have hR:rankBand aji mid hi=rankBand q mid hi:= by
    unfold rankBand
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [show aji s=q s from ite_eq_right (not_lt.mpr (Finset.mem_Ico.mp hs).1)]
  exact ⟨aji,calc
    _=rankBand aji lo mid+rankBand aji mid hi :=
      (Finset.sum_Ico_consecutive (fun s=>al2 s (aji s)) hl hr).symm
    _≤a+b:= by rw [hL,hR]; exact Nat.add_le_add hp hq⟩
theorem b3v (q:ℕ) (r :Offset) :pT q r =
    ⟨iO q,1710-(r.val :ℤ),1710,570,4710-(q:ℤ) - r.val⟩:= by
  simp only [pT,aQj]
  change xE.Flag.mk _ (-((r.val :ℤ) - 1710)) 1710 570
    (3000-(q:ℤ)-((r.val :ℤ) - 1710))= _
  congr 1 <;> ring
def pairPowers (i j:Fin 11) (a b:ℕ) (k :Fin 11) :ℕ :=
  (if k=i then a else 0)+(if k=j then b else 0)
theorem residual_pair (F:Flag) (i j:Fin 11) (a b:ℕ) :
    BH F (pairPowers i j a b) =
      ⟨F.degree-(a*(Jd i).degree+b*(Jd j).degree),
       F.lower-(a*(Jd i).lower+b*(Jd j).lower),
       F.upper-(a*(Jd i).upper+b*(Jd j).upper),
       F.cap-(a*(Jd i).cap+b*(Jd j).cap),
       F.order-(a*(Jd i).order+b*(Jd j).order)⟩:= by
  have h (f :Fin 11→ℤ) :
      (∑ k,(pairPowers i j a b k :ℤ)*f k)=(a :ℤ)*f i+(b:ℤ)*f j:= by
    simp only [pairPowers,Nat.cast_add,add_mul,Finset.sum_add_distrib]
    have h' (c:ℕ) (l:Fin 11) :
        (∑ k,((if k=l then c else 0:ℕ) :ℤ)*f k)=(c:ℤ)*f l:= by
      simp only [apply_ite (Nat.cast:ℕ→ℤ),Nat.cast_zero,ite_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [h' a i,h' b j]
  unfold BH
  rw [h (fun k=>(Jd k).degree),h (fun k=>(Jd k).lower),
    h (fun k=>(Jd k).upper),h (fun k=>(Jd k).cap),
    h (fun k=>(Jd k).order)]
theorem block_le_residual (q:ℕ) (r :Offset) (p:Fin 11→ℕ) :
    xR q r p≤(oldCount (pT q r) -
      m5 (BH (pT q r) p)).toNat := by
  refine (min_le_left _ _).trans ?_
  unfold prescribedBound
  dsimp only
  split
  · exact zD0 _
  · apply z0Z
    exact (min_le_right _ _).trans
      (sub_le_sub_left ((le_max_right _ _).trans (le_max_right _ _)) _)
theorem block_le_old (q:ℕ) (r :Offset) (p:Fin 11→ℕ) :
    xR q r p≤(oldCount (pT q r)).toNat := by
  refine (min_le_left _ _).trans ?_
  unfold prescribedBound
  dsimp only
  split
  · exact zD0 _
  · exact z0Z ((min_le_right _ _).trans (sub_le_self _ (le_max_left _ _)))
private theorem tail_degree {q:ℕ} (hq:4020≤q) :iO q≤1000:= by
  unfold iO P6_6.Dj
  simp only [show ¬ q<3307 by omega,show ¬ q<3335 by omega,
    show ¬ q<3407 by omega,show ¬ q<3470 by omega,show ¬ q<3537 by omega,
    show ¬ q<3585 by omega,show ¬ q<3630 by omega,show ¬ q<3678 by omega,
    show ¬ q<3733 by omega,show ¬ q<3781 by omega,show ¬ q<3830 by omega,
    show ¬ q<3878 by omega,show ¬ q<3927 by omega,show ¬ q<3975 by omega,
    show ¬ q<4020 by omega,ite_false]
  split <;> exact (min_le_right q _).trans (by decide)
private theorem tail_block {q:ℕ} (hq:4020≤q) (r :Offset) (p:Fin 11→ℕ) :
    xR q r p=0:= by
  let F:=pT q r
  have hdeg:=tail_degree hq
  have ht:AO F=0:= by
    rw [show F=pT q r from rfl,b3v]
    unfold AO
    dsimp only
    rw [ite_eq_left (by omega)]
  have hk :m5 F=oldCount F:= by
    have hflags : ¬ (F.degree<0 || F.upper<0 || F.cap<0)=true := by
      rw [show F=pT q r from rfl,b3v]
      simp
    simp only [m5,hflags,Bool.false_eq_true,ite_false,ht,sub_zero]
  apply Nat.eq_zero_of_le_zero
  refine (min_le_left _ _).trans ?_
  unfold prescribedBound
  change (if F.order≤0 then 0 else
    (min (oldCount (alp q r))
      (oldCount F - max 0 (max (m5 F) (m5 (BH F p))))).toNat)≤0
  split
  · exact le_rfl
  · have hm:oldCount F≤ max 0 (max (m5 F) (m5 (BH F p))) := calc
      _=m5 F:=hk.symm
      _≤_:=(le_max_left _ _).trans (le_max_right _ _)
    have hz :min (oldCount (alp q r))
        (oldCount F - max 0 (max (m5 F) (m5 (BH F p))))≤(0:ℤ) :=
      (min_le_right _ _).trans (sub_nonpos.mpr hm)
    exact z0Z hz
theorem tail_cap:aak 4020 4026 0:= by
  refine ⟨fun _ _ _=>0,le_of_eq ?_⟩
  unfold rankBand
  apply zYF
  intro q hq
  unfold al2
  exact zYF fun r _=>tail_block (Finset.mem_Ico.mp hq).1 r _
end qwbsesc
end
section
set_option autoImplicit true
namespace P6_6_5
noncomputable section
open aR (ao af cK jet qE)
open oR (qg)
open aeA
open P6_6 (axx mW)
open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators
open private aio from ProximityPrize.SubmissionLower.Zb3VwYd
open private bAW from ProximityPrize.SubmissionLower.CD
theorem bFR (v :ℕ) (g:af 3) (hg:axx v g) :
    ∃ (n:ℕ) (f :Fin n→af 3) (q:af 2),Zl v f∧a93 v q ∧
      ∀ S:ao[X],cK g S=0 →
        cK q S=0 ∨ ∃ i,qg 2 (f i) S:= by
  classical
  obtain ⟨hg₀,hgt,hgi,hgw⟩:=hg
  let p:=mW v
  have hgt' : g.totalDegree≤p.b:= by
    have ht:g.totalDegree≤133 - v := by
      change g.totalDegree+v≤133 at hgt
      omega
    exact ht.trans (le_max_left _ _)
  have hgi' : qE g≤p.j:= by
    change qE g+3*v≤56 at hgi
    change qE g≤56-3*v
    omega
  have hpb:p.j≤p.b:=(Nat.le_add_right _ 3).trans (le_max_right _ _)
  have hpt:2*p.t≤p.j:= by
    change 2*(p.j/2)≤p.j
    omega
  let _:StrongNormalizationMonoid (af 3) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let A:=normalizedFactors g
  let T:=A.toFinset
  let c (f :af 3) :=(view f).natDegree
  let P:=T.filter fun f=>0<c f
  let n:=Fintype.card ↥P
  let e :Fin n ≃ ↥P:=(Fintype.equivFin ↥P).symm
  let f :Fin n→af 3:= fun i=>(e i).val
  let q:af 2 := ∏ a∈T,elimination a
  have hmem (a :af 3) (ha :a∈T) :a∈A:=Multiset.mem_toFinset.mp ha
  have hirr (a :af 3) (ha :a∈T) :Irreducible a :=
    irreducible_of_normalized_factor a (hmem a ha)
  have hf (i:Fin n) :f i∈T∧0<c (f i) :=Finset.mem_filter.mp (e i).property
  have hdvd: (∏ a∈T,a)∣g :=
    (zc7 A).trans (prod_normalizedFactors hg₀).dvd
  have hsum (w:Fin 3→ℕ) :
      (∑ a∈T,a.weightedTotalDegree w)≤g.weightedTotalDegree w :=
    sum_weightedTotalDegree_le_of_prod_dvd w T id hg₀ hdvd
  have htop (a :af 3) :c a=a.degreeOf 2 :=gLc a
  have hc : ∑ a∈T,c a≤p.t:= by
    have hbound:g.weightedTotalDegree (fun i=>i.val)≤p.j :=
      (Ex.C6 g) ▸ hgi'
    have h:2*(∑ a∈T,c a)≤p.j:= calc
      _ = ∑ a∈T,(2*c a) :=Finset.mul_sum T c 2
      _ ≤ ∑ a∈T,a.weightedTotalDegree (fun i=>i.val) := by
        apply zQk
        intro a _
        exact (Nat.le_add_left _ _).trans (biB (fun i=>i.val) a (c a) le_rfl)
      _≤_:=(hsum _).trans hbound
    change (∑ a∈T,c a)≤p.j/2
    omega
  have he₀ (a :af 3) (ha :a∈T) :elimination a≠0:= by
    have hca :=(zfK (fun i _=>zD0 (c i)) ha).trans hc
    exact d02 (hirr a ha)
      ((hca.trans (a5C v)).trans_lt (by decide))
  have hq (w:Fin 3→ℕ) (B:ℕ) (hb:g.weightedTotalDegree w≤B)
      (hB:w 2*p.t≤B) :
      q.weightedTotalDegree (fun i=>w i.castSucc)≤ max B ((2*p.t - 1)*B - w 2*p.t^2) := by
    let u:Fin 2→ℕ:= fun i=>w i.castSucc
    rw [show q = ∏ a∈T,elimination a from rfl,weightedTotalDegree_prod u T _ he₀]
    apply bAW T (fun a=>a.weightedTotalDegree w) c
      (fun a=>(elimination a).weightedTotalDegree u) B (w 2) p.t ((hsum w).trans hb) hc hB
    · intro a _
      exact (Nat.le_add_left _ _).trans (biB w a (c a) le_rfl)
    · intro a _ ha
      exact cLA w a ha
    · intro a _ ha
      exact cLz w a ha
  have hqtotal:q.totalDegree≤O1 v := by
    have htb:p.t≤p.b:=(by omega :p.t≤p.j).trans hpb
    have h:=hq (1 :Fin 3→ℕ) p.b (by simpa only [weightedTotalDegree_one] using hgt')
      (by simpa only [Pi.one_apply,one_mul] using htb)
    simp only [Pi.one_apply,one_mul] at h
    have hconst: (fun _:Fin 2=>(1 :ℕ))=(1 :Fin 2→ℕ) := by
      funext i
      simp only [Pi.one_apply]
    rw [hconst,weightedTotalDegree_one] at h
    exact h
  have hqindex :qE q≤ayY v := by
    rw [Ex.C6] at hgi' ⊢
    exact hq (fun i=>i.val) p.j hgi' hpt
  have hsub (d:af 3→ℕ) : (∑ i,d (f i)) ≤ ∑ a∈T,d a := by
    calc
      _ = ∑ a : ↥P,d a.val :=e.sum_comp _
      _ = ∑ a∈P,d a :=Finset.sum_coe_sort P d
      _≤_:=Finset.sum_le_sum_of_subset (zT0 _ _)
  refine ⟨n,f,q,⟨fun i=>hirr _ (hf i).1,fun i=>htop _ ▸ (hf i).2,?_,?_,?_,?_⟩,
    ⟨Finset.prod_ne_zero_iff.mpr he₀,hqtotal,hqindex⟩,?_⟩
  · intro i
    let E :=MvPolynomial.optionEquivRight ao (Fin 3)
    have hdi:=map_dvd E.symm (dvd_of_mem_normalizedFactors (hmem _ (hf i).1))
    have hgn:E.symm g≠0:= fun hz=>hg₀ (E.symm.injective (hz.trans (map_zero _).symm))
    exact (aio _).mpr
      ((weightedTotalDegree_le_of_dvd _ hdi hgn).trans ((aio _).mp hgw))
  · exact (hsub _).trans ((by simpa only [weightedTotalDegree_one] using hsum (1 :Fin 3→ℕ) :
      (∑ a∈T,a.totalDegree)≤g.totalDegree).trans hgt')
  · exact (hsub _).trans ((by simpa only [← Ex.C6] using hsum (fun i=>i.val) :
      (∑ a∈T,qE a)≤qE g).trans hgi')
  · simpa only [htop] using (hsub c).trans hc
  · intro S hS
    have hz :=map_dvd (eval (jet S)) (prod_normalizedFactors hg₀).symm.dvd
    change cK g S∣eval (jet S) A.prod at hz
    rw [hS,zero_dvd_iff,map_multiset_prod,z03,Multiset.mem_map] at hz
    obtain ⟨a,ha,hzero⟩:=hz
    have haT:a∈T:=Multiset.mem_toFinset.mpr ha
    rcases d0Z a S hzero with h | ⟨hp,hr⟩
    · left
      change eval (jet S) (∏ a∈T,elimination a)=0
      rw [map_prod]
      exact Finset.prod_eq_zero haT h
    · right
      let j : ↥P:=⟨a,Finset.mem_filter.mpr ⟨haT,hp⟩⟩
      refine ⟨e.symm j,?_⟩
      change qg 2 ((e (e.symm j)).val) S
      rw [Equiv.apply_symm_apply]
      exact hr
open private QI from ProximityPrize.SubmissionLower.AH
open private bpk from ProximityPrize.SubmissionLower.CD
theorem ebE (v :ℕ) (hv :v≤P6_6.m6.t) (q:af 2) (hq:a93 v q) :
    ∃ (n:ℕ) (f :Fin n→af 2) (u:ao[X][X]),bjg v f∧u≠0 ∧
      u.natDegree≤O1 v*(O1 v - 1) ∧
      ∀ S:ao[X],cK q S=0 →
        u.eval S=0 ∨ ∃ i,qg 1 (f i) S:= by
  classical
  let _:StrongNormalizationMonoid (af 2) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors q
  let A:=M.toFinset
  let T:=A.filter fun g=>0<g.degreeOf 1
  let n:=Fintype.card ↥T
  let e :Fin n ≃ ↥T:=(Fintype.equivFin ↥T).symm
  let f :Fin n→af 2 := fun i=>(e i).val
  have hA : ∀ g∈A,Irreducible g:= fun g hg =>
    irreducible_of_normalized_factor g (Multiset.mem_toFinset.mp hg)
  have hdiv : (∏ g∈A,g)∣q :=
    (zc7 M).trans (prod_normalizedFactors hq.ne_zero).dvd
  have hcap: (∑ g∈A,g.totalDegree)≤O1 v := by
    have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) A id hq.ne_zero hdiv
    simp only [id_eq,weightedTotalDegree_one] at h
    exact h.trans hq.total
  have hfactor : ∀ i,f i∈A∧0<(f i).degreeOf 1 := fun i =>
    Finset.mem_filter.mp (e i).property
  have hfdiv : (∏ i,f i)∣q:= by
    rw [show (∏ i,f i) = ∏ g : ↥T,id g.val from e.prod_comp Subtype.val,
      Finset.prod_coe_sort T id]
    exact (Finset.prod_dvd_prod_of_subset T A id (zT0 _ _)).trans hdiv
  have hf :bjg v f := by
    refine ⟨fun i=>hA _ (hfactor i).1,fun i=>(hfactor i).2,?_,?_⟩
    · have h:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) Finset.univ f hq.ne_zero hfdiv
      simp only [weightedTotalDegree_one] at h
      exact h.trans hq.total
    · have h:=sum_weightedTotalDegree_le_of_prod_dvd (fun i:Fin 2=>i.val)
        Finset.univ f hq.ne_zero hfdiv
      simp only [← Ex.C6] at h
      exact h.trans hq.index
  have hspec (g:af 2) (hg:g∈A) :=
    bpk (cSk hv) (ebv v) g (hA g hg)
      ((zfK (fun x _=>zD0 x.totalDegree) hg).trans hcap)
  let u := ∏ g∈A,QI g
  refine ⟨n,f,u,hf,Finset.prod_ne_zero_iff.mpr (fun g hg=>(hspec g hg).1),?_,?_⟩
  · calc
      u.natDegree ≤ ∑ g∈A,(QI g).natDegree :=z8u _ _
      _ ≤ ∑ g∈A,g.totalDegree*(O1 v - 1) :=zQk fun g hg=>(hspec g hg).2.1
      _≤O1 v*(O1 v - 1) := by
        rw [← Finset.sum_mul]
        exact Nat.mul_le_mul_right _ hcap
  · intro S hS
    have hroot :zY9 (jet S) M.prod=0:= by
      have hd:=map_dvd (zY9 (jet S)) (prod_normalizedFactors hq.ne_zero).symm.dvd
      change cK q S∣ _ at hd
      rwa [hS,zero_dvd_iff] at hd
    rw [map_multiset_prod,z03,Multiset.mem_map] at hroot
    obtain ⟨g,hgM,hgS⟩:=hroot
    have hgA:g∈A:=Multiset.mem_toFinset.mpr hgM
    rcases (hspec g hgA).2.2 S hgS with hzero | ⟨hpos,hreg⟩
    · left
      change Polynomial.evalRingHom S u=0
      rw [show u = ∏ g∈A,QI g from rfl,map_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨g,hgA,hzero⟩
    · right
      let j:=e.symm ⟨g,Finset.mem_filter.mpr ⟨hgA,hpos⟩⟩
      have hj:f j=g:=congrArg Subtype.val (e.apply_symm_apply _)
      exact ⟨j,hj ▸ hreg⟩
end
end P6_6_5
end
section
set_option autoImplicit true
namespace qwzqCne
noncomputable section
abbrev Ground :=ZMod P1.p
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev Triple :=ℕ×ℕ×ℕ
abbrev aY := {e :Exponent // e.degree=54}
abbrev gU (cut:ℕ) :=qK9H6va.Lh 54 cut
def aD (e :Exponent) :Triple :=(e 1,e 2,e 3)
def cP:Triple→ℕ
  | (b,c,f)=>4*(54-(b+c+f))+b+2*c+3*f
def dZ (e :aY) :ℕ :=
  ((cP (aD e.val)*55+e.val 3)*55+e.val 2)*55+e.val 1
def yv {κ:Type*} (column:κ→Exponent) (v :Triple) (m:κ) :Ground :=
  (v.1.choose (column m 1) :Ground) *
    (v.2.1.choose (column m 2) :Ground)*(v.2.2.choose (column m 3) :Ground)
def cE (cut:ℕ) (v :Triple) :gU cut→Ground :=
  yv Subtype.val v
abbrev Pivot:=Σ gap:Fin 99,Σ i:Fin 57,Fin (groupCount gap.val i.val)
def Ug (j:Pivot) :Triple :=ZX j.1.val j.2.1.val j.2.2.val
def Nx (j:Pivot) :ℕ:=j.2.1.val
def c37 (j:Pivot) :ℕ:=j.1.val+Nx j
abbrev iw (e :aY) := {v :aY // dZ v<dZ e}
def bk1 (e :aY) :Prop :=
  ∃ cut:ℕ,
    (cut≤ cP (aD e.val)-98 ∨
      ∃ j:Pivot,Ug j=aD e.val ∧
        c37 j=cP (aD e.val)∧cut≤Nx j+1) ∧
    cE cut (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
def aGq (lo hi:ℕ) :Prop :=
  ∀ e :aY,lo≤ cP (aD e.val)→cP (aD e.val)≤hi →
    bk1 e
abbrev PrefixPivot (g w:ℤ) :=
  {j:Pivot // (c37 j:ℤ)<w ∧ -g≤(Nx j:ℤ)}
instance (g w:ℤ) :Fintype (PrefixPivot g w) :=Fintype.ofFinite _
abbrev bk9 (cut:ℕ) := {j:Pivot // c37 j<tailCost∧cut≤Nx j}
end
end qwzqCne
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qkZfm9d
noncomputable section
open Polynomial aR dN rW Rl as9
open MvPolynomial (affineDegree affineDegree_bot principalCut_sum_affineDegree_minimalPrimes_le
  natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton)
open ap9 (aFs)
open scoped BigOperators
open private Rl.SZ from ProximityPrize.SubmissionLower.J
open private beg from ProximityPrize.SubmissionLower.J
open private bPa bDc from ProximityPrize.SubmissionLower.J
open private ed2 enH from ProximityPrize.SubmissionLower.A2
private theorem b4G {f :af 4} (hf :Irreducible f) :bC f≠0 :=
  (map_ne_zero_iff (MvPolynomial.map j8)
    (MvPolynomial.map_injective _ Rl.SZ)).mpr hf.ne_zero
theorem bPZ {f :af 4} {component:n8} (hf :Irreducible f)
    (hZ: (zye {bC f}).IsMinimalPrime component) :dimension component=3:= by
  have h:=natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (b4G hf) hZ
  rw [Nat.card_eq_fintype_card,Fintype.card_fin] at h
  change dimension component+1=4 at h
  omega
theorem bP0 {f :af 4} (hf :Irreducible f) :
    ∑ component∈aFs f,affineDegree component≤((shape f).iU.b:ℚ) := by
  have hn:bC f∉(⊥ : n8) := fun h=>b4G hf ((Ideal.mem_bot).mp h)
  have hd: (bC f).totalDegree≤(shape f).iU.b :=
    (beg f).trans (Nat.le_max_left _ _)
  simpa only [aFs,bot_sup_eq,affineDegree_bot,mul_one] using
    principalCut_sum_affineDegree_minimalPrimes_le (P:=(⊥ : n8)) hn hd
private theorem gMs {f :af 4} (hf :Irreducible f) {P:n8}
    (hP: (zye {bC f}).IsMinimalPrime P) :
    contraction P=zye {f} := by
  let:P.IsPrime :=hP.isPrime
  have hmem:bC f∈P:=hP.le (zCn (zT1 _))
  have hne :P ≠ ⊥ := fun h=>b4G hf (Ideal.mem_bot.mp (h ▸ hmem))
  have hheight:P.height = 1 := by
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
    exact Order.one_le_iff_ne_zero.mpr (fun h=>hne (Ideal.height_eq_zero_iff_eq_bot.mp h))
  obtain ⟨r,hrP,hr⟩:=hP.isPrime.exists_mem_prime_of_ne_bot hne
  have he :=P.eq_span_singleton_of_height_eq_one hheight hrP hr
  have hrf :r∣bC f :=Ideal.mem_span_singleton.mp (he ▸ hmem)
  obtain ⟨a,ha,haeq⟩:=agP.bYh hr hf.ne_zero hrf
  have hc:contraction P=zye {a} := by
    rw [contraction,he,haeq]
  have had:a∣f :=Ideal.mem_span_singleton.mp (hc ▸ (show f∈contraction P from hmem))
  have hassoc:=ha.irreducible.associated_of_dvd hf had
  exact hc.trans (le_antisymm
    (Ideal.span_singleton_le_span_singleton.mpr hassoc.dvd')
    (Ideal.span_singleton_le_span_singleton.mpr hassoc.dvd))
private theorem dl7 {f :af 4} (hf :Irreducible f) {P:n8}
    (hP: (zye {bC f}).IsMinimalPrime P) :Invariant f P:= by
  have hc:=gMs hf hP
  intro Q hQ
  have hmem:Q∈contraction P:=hQ
  rw [hc,zxV] at hmem
  obtain ⟨R,rfl⟩:=hmem
  change u6 f (f*R)∈contraction P
  rw [hc,agP.ZF,agP.cSN,mul_zero,add_zero,
    zxV]
  exact dvd_mul_right _ _
theorem dPz (f :af 4) (hf :P6_6.wm f) (P:n8)
    (hP: (zye {bC f}).IsMinimalPrime P)
    (hs :bC (separant f)∉P) (htest :bC (vU f)∈P) :
    ∃ A:kT,akB f A∧lA A≤P:= by
  let:P.IsPrime :=hP.isPrime
  have hfP:bC f∈P:=hP.le (zCn (zT1 _))
  obtain ⟨δ,hδ⟩:=bRC.proof f P hP.isPrime hs (dl7 hf.1 hP)
  let U:=(RH f P).map (afJ f P hs)
  have hd:U.natDegree<bf :=ezp _
  have hj (i:Fin 4) : (hasseDeriv i.val U).eval (K4 P (MvPolynomial.C rI)) =
      K4 P (z9v i) := by
    simpa only [U,CW,bef,rI,
      bC,MvPolynomial.map_C,MvPolynomial.map_X] using
      bpA (afJ f P hs) i
  have hsolve :jW (CX P) f U=0 :=
    qs56oUd.bN8 hs hf hfP htest δ hδ
  have hregular :jW (CX P) (separant f) U≠0:= by
    intro hzero
    apply bDc hs
    rw [← bPa P U (separant f) hj,hzero,eval_zero]
  let A:=Zv (CX P) U
  have hAP:lA A≤P:=ed2 P U hd hj
  have hdim:dimension P≤dimension A :=
    (MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le hAP).trans (enH A)
  rw [bPZ hf.1 hP] at hdim
  refine ⟨A,⟨zgL _,(by decide :2≤3).trans hdim,?_,?_⟩,hAP⟩
  · intro j
    change zOD (CX P)
      (fun i:Fin bf=>U.coeff i.val) ((aip f).coeff j)=0
    rw [← z0b,map_universalEval _ _ hd,hsolve,coeff_zero]
  · obtain ⟨j,hj⟩:=not_forall.mp (mt Polynomial.ext_iff.mpr hregular)
    refine ⟨j,?_⟩
    change zOD (CX P)
      (fun i:Fin bf=>U.coeff i.val) ((aip (separant f)).coeff j)≠0
    rw [← z0b,map_universalEval _ _ hd]
    simpa only [coeff_zero] using hj
end
end qkZfm9d
end
section
set_option autoImplicit true
namespace qSCPCwb
noncomputable section
open aR (ao af cK)
open oR (qg AR separant)
open we (cH eT fW graph JZ
  DO ag9 zq D7)
open P6_6 (bf gZ mW LN)
open P6_6_5 (Fb R4 tC)
open Polynomial
open scoped BigOperators
export we (GD Bk aap afs JC)
def Dm (f :af 3) :af 3:=AR f (bf-3)
def Vk (f :af 3) :af 3:=AR f (bf - 2)
open private cHq from ProximityPrize.SubmissionLower.BG
theorem btd (f :af 3) :
    (Dm f).totalDegree≤1+(2*(bf+1) - 7)*(f.totalDegree - 1) :=
  cHq f (bf-3)
def BW (f :af 3) :Ideal (eT 3) :=
  zye {fW f,fW (Dm f)}
def Ji {n:ℕ} (f :Fin n→af 3) :Finset (aap n) := by
  classical
  exact Finset.univ.biUnion fun i =>
    if Fb (f i) then ∅ else
      ((BW (f i)).retainedMinimalPrimes (fW (separant (f i)))).image
        (fun P=>(i,P))
theorem azC {n:ℕ} {f :Fin n→af 3} {i:Fin n}
    {P:Ideal (eT 3)} : (i,P)∈Ji f ↔
    ¬ Fb (f i)∧P∈(BW (f i)).retainedMinimalPrimes (fW (separant (f i))) := by
  classical
  simp only [Ji,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,hk⟩
    by_cases hw:Fb (f k)
    · simp [hw] at hk
    · simp only [hw,ite_false] at hk
      obtain ⟨P',hP',he⟩:=Finset.mem_image.mp hk
      cases he
      exact ⟨hw,hP'⟩
  · rintro ⟨hw,hP⟩
    exact ⟨i,by simpa only [hw,ite_false] using Finset.mem_image.mpr ⟨P,hP,rfl⟩⟩
def Lx (f :af 3) (P:Ideal (eT 3)) :ℕ∞ := by
  classical
  exact if hp:P.IsPrime then
    letI:=hp
    let A:=Localization.AtPrime P
    Module.length A (A ⧸ (BW f).map (algebraMap (eT 3) A))
  else 0
def aGt (f :af 3) (P:Ideal (eT 3)) :Prop :=
  Lx f P=1∧fW (Vk f)∈P
def avD (f :af 3) (P:Ideal (eT 3)) :Set (Fin 3→cH) :=
  {y | y∈D7 f P∧zY9 y (fW (Vk f))=0}
def Uj (f :af 3) (numerator :Fin aR.bf→eT 4)
    (y :Fin 3→cH) :GD :=
  fun i=>zY9 (JZ f y) (numerator i) /
    zY9 y (fW (separant f))^(bf-4)
structure Gf (v :ℕ) (f :af 3) where
  cut:eT 4
  next:eT 4
  numerator :Fin aR.bf→eT 4
  graph_box :DO (graph f) (tC (mW v)) 1
  cut_box :DO cut (LN (bf+1) (mW v)) (bf - 1)
  next_box :DO next (LN (bf+2) (mW v)) bf
  coefficient_box : ∀ i,
    DO (numerator i) (LN bf (mW v)) (bf - 2)
  cut_represents :ag9 f (Dm f) cut
  next_represents :ag9 f (Vk f) next
  actual : ∀ S:ao[X],S.natDegree≤gZ→qg 2 f S →
    cK (Dm f) S=0∧cK (Vk f) S=0 ∧
      Uj f numerator (zq S)=afs S
structure bAb (v :ℕ) {n:ℕ} (f :Fin n→af 3)
    (T : ∀ i,Gf v (f i)) where
  length:aap n→ℕ
  degree :aap n→ℕ
  length_eq : ∀ a∈Ji f,(length a :ℕ∞)=Lx (f a.1) a.2
  length_pos : ∀ a∈Ji f,0<length a
  total: (∑ a∈Ji f,length a*degree a)≤R4 v
  points : ∀ a∈Ji f,fW (Vk (f a.1))∉a.2 →
    (avD (f a.1) a.2).Finite∧(avD (f a.1) a.2).ncard≤degree a
  qv : ∀ a∈Ji f,2≤length a →
    ∃ Q:Bk,Q.IsPrime∧(MvPolynomial.affineHilbertPolynomial Q).natDegree≤1 ∧
      0<degree a∧MvPolynomial.affineDegree Q≤(degree a :ℚ) ∧
      ∀ y∈D7 (f a.1) a.2,
        Uj (f a.1) (T a.1).numerator y∈zSD cH Q
structure acU (f :af 3) (Q:Bk) :Prop where
  solution :we.acU f Q
  short : ∀ a∈zSD cH Q,
    (JC a).natDegree≤gZ
end
end qSCPCwb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace qXTnXJe
noncomputable section
open aR (ao af cK)
open oR (qg separant)
open B7 ac1
open P6_6 (bf gZ tB M8)
open P6_6_5 (Fb)
open scoped Polynomial
open private cFt from ProximityPrize.SubmissionLower.CT
open private ddz from ProximityPrize.SubmissionLower.E3
def bjP (P:Ideal jo) :Prop :=
  ∀ i:rS,bf≤ i.val→z9v i∈P
private theorem cJ9 {F:Type} [Field F] (k :ao →+* F) {U:F[X]}
    (hU:U.natDegree<bf) (f :af 3) (hf :tB f M8) :
    (jW k U f).natDegree≤M8:= by
  classical
  unfold jW
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hprod: (∏ i∈m.support,z75 i.val U^m i).natDegree ≤
      m.sum (fun i e=>(gZ - i.val)*e) := by
    unfold Finsupp.sum
    apply (z8u _ _).trans
    apply zQk
    intro i _
    change ((z75 i.val U)^m i).natDegree≤(gZ - i.val)*m i
    rw [Nat.mul_comm]
    exact Polynomial.natDegree_pow_le_of_le _ ((Polynomial.natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right (Nat.le_of_lt_succ hU) _))
  exact (Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_map_le hprod).trans (hf m hm)
theorem dIK (f :af 3) (hf :Irreducible f)
    (hd:0<f.degreeOf 2) (hmax :f.degreeOf 2<K1.p)
    (hw:tB f M8) (hwhole :Fb f) :
    ∃ P:Ideal jo,XP P (GZ f) (GZ (separant f)) ∧
      bjP P ∧ ∀ S:ao[X],S.natDegree≤gZ→qg 2 f S →
        Gp S∈zSD ao P:= by
  let hp: (Jy f).IsPrime :=dIP f hf hd
  have hs :=ddz f hf hd hmax
  have hweight (U: (WE f)[X]) (hU:U.natDegree<bf) :
      (jW (Jb f) U f).natDegree<K1.p :=
    (cJ9 _ hU f hw).trans_lt (by decide :M8<K1.p)
  obtain ⟨U,hsmall,hsol,hinit⟩ :=
    cFt f bf (by decide) (by decide) hs hweight hwhole
  have length_le :bf≤aR.bf := by decide
  have hU:=hsmall.trans_le length_le
  obtain ⟨m,v,hv⟩:=bam.proof f
  let k :=Jb f
  let point :rS→WE f := fun a=>U.coeff a.val
  let P:=zdq (ajk k point)
  have hbase :=cS8 k point
  have himage :=ed4 f hf hd U hU hsol hinit
  have hD:y3 f (GZ (separant f))≠0 :=
    fun h=>hs ((aO5 f _).mp h)
  have hUreg:jW k U (separant f)≠0:= by
    intro hz
    have h:=bdt k U (CW f) (separant f)
    rw [hz,Polynomial.eval_zero,hinit,bvd] at h
    exact hD h.symm
  refine ⟨P,⟨zgL _,?_,?_,hs,?_⟩,?_,?_⟩
  · exact fun h=>hf.ne_zero (fZd (h.trans (map_zero _).symm))
  · change (oV P).comap tO.toRingHom=Jy f
    rw [hbase,RingHom.comap_ker]
    exact himage
  · intro a
    refine ⟨GZ (v a),m,?_⟩
    have hU' : (U.map (newConstants :WE f →+* aar (WE f))).natDegree <
        aR.bf :=Polynomial.natDegree_map_le.trans_lt hU
    have hsol' : jW (newConstants.comp k) (U.map newConstants) f=0:= by
      rw [← aVM,hsol,zgY]
    have hs' : ee (newConstants.comp k) amg
        (rD amg (U.map newConstants)) (separant f)≠0:= by
      rw [bJF]
      exact fun h=>hUreg ((zxb _ _) (h.trans (map_zero _).symm))
    have h:=hv (aar (WE f)) (newConstants.comp k) (U.map newConstants) amg
      hU' hsol' hs' a
    rw [bJF,bJF,z0b,
      ← bGY k U hU,← bGY k U hU] at h
    exact eee k U a m _ _ h
  · intro a ha
    change ajk k point (z9v a)=0
    rw [ajk,MvPolynomial.eval₂Hom_X']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hsmall.trans_le ha)
  · intro S hS hreg
    let e :nW →+* WE f :=y3 f
    let g:nW →+* dF :=
      zY9 (rD PV (S.map QM))
    let b:ao →+* nW:=MvPolynomial.C.comp QM
    have hg (q:af 3) :g (GZ q)=algebraMap ao[X] dF (cK q S) := by
      rw [← drX,bTU]
      rfl
    have hreg' : g (GZ (separant f))≠0:= by
      rw [hg]
      exact fun h=>hreg.2 ((zxb _ _) (h.trans (map_zero _).symm))
    have hker :zdq e≤zdq g:= by
      rw [show zdq e=Jy f by
        ext q
        exact aO5 f q]
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      rw [RingHom.mem_ker,hg,hreg.1,map_zero]
    have hS' : (S.map QM).natDegree<aR.bf :=
      Polynomial.natDegree_map_le.trans_lt ((Nat.lt_succ_of_le hS).trans_le length_le)
    have hsolS:jW QM (S.map QM) f=0:= by
      simpa only [dhO,hreg.1,zgY,RingHom.comp_id] using
        (aVM (RingHom.id ao) QM S f).symm
    have hrecU (a :rS) :
        e (GZ (separant f))^m*point a=e (GZ (v a)) := by
      have hc:=hv (WE f) k U (CW f) hU hsol
        (by rwa [hinit,bvd]) a
      rwa [hinit,bvd] at hc
    have hrecS (a :rS) :
        g (GZ (separant f))^m*QM (S.coeff a.val)=g (GZ (v a)) := by
      have hc:=hv dF QM (S.map QM) PV hS' hsolS
        (by rwa [bTU]) a
      rwa [bTU,z0b] at hc
    have hle :=d2y b e g hker (GZ (separant f)) m
      (fun a=>GZ (v a)) hD hreg' point (QM ∘ Gp S) hrecU hrecS
    intro q hq
    have hz :=hle hq
    change zOD (g.comp b) (QM ∘ Gp S) q=0 at hz
    have hqmap :zOD (g.comp b) (QM ∘ Gp S) =
        QM.comp (MvPolynomial.aeval (Gp S)).toRingHom:= by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [b,g]
      · intro a
        simp
    rw [hqmap] at hz
    exact QM.injective (hz.trans (map_zero _).symm)
end
end qXTnXJe
end
