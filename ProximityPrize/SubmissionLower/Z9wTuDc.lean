import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.ZasomWd
import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.ZGvZzVd
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, IsFractionRing.injective → zxb, IsScalarTower.toAlgHom → zE2, MvPolynomial.C → znf, MvPolynomial.eval → zY9, MvPolynomial.totalDegree_mul_of_isDomain → zzD, Nat.add_le_add → z9f, Nat.le_add_right → z8K, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl, Polynomial.eval₂ → zmH, Polynomial.ext → zXJ, Polynomial.mapRingHom → zhd
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qcOrJya
noncomputable section
open Polynomial DP
open cu (L Shape)
open scoped Polynomial
abbrev entry (Q:Source) (j i a :ℕ) :qC:=((Q.coeff j).coeff i).coeff a
private abbrev Sl (d:qC) :Source :=C (C (C d))
private theorem entry_mul (d:qC) (Q:Source) (j i a :ℕ) :
    entry (Sl d*Q) j i a=d*entry Q j i a := by
  simp only [entry,Sl,coeff_C_mul]
private theorem bKs (x r :L) (d:qC) :
    Km x r (Sl d)=Sl d:= by
  change zmH _ _ (C (C (C d)))= _
  rw [eval₂_C]
  change zmH _ _ (C (C d))= _
  rw [eval₂_C]
  change (algebraMap qC[X] Source) (zmH _ _ (C d))= _
  rw [eval₂_C]
  rfl
private theorem cSV {h} {D:jF h} (crt:zG D) (d:qC) :
    forward crt (Sl d)=C (C (C (algebraMap qC aQ d))) := by
  change zmH _ _ (C (C (C d)))= _
  rw [eval₂_C]
  change zmH _ _ (C (C d))= _
  rw [eval₂_C]
  change (algebraMap aQ[X] US) (Polynomial.map _ (C d))= _
  rw [Polynomial.map_C]
  rfl
theorem entry_caps {h} {s :Shape} {W j i a :ℕ} {Q:Source}
    (hq:Q∈Aw h s W) (he :entry Q j i a≠0) :
    i+j≤ s.B∧j≤ s.J∧(entry Q j i a).totalDegree≤ s.U ∧
      a+(i+j)*(131071+h)≤W+(s.B+s.J)*(2*h)+j:= by
  have elig (e) (hm:e∈(entry Q j i a).support) :awN h s W j i a e := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hm) (hq j i a e hn)
  obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr he
  exact ⟨(elig e he).1,(elig e he).2.1,
    Finset.sup_le (fun f hf=>(elig f hf).2.2.1),(elig e he).2.2.2⟩
private theorem divide_complete {h} {D:jF h} (crt:zG D) {word s W}
    {P Q:Source} {d:qC} (hd:d≠0) (hp:P∈complete crt word s W)
    (he :P=Sl d*Q) :Q∈complete crt word s W:= by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j i a e hn
    by_contra hz
    change (entry Q j i a).coeff e≠0 at hz
    have hq:entry Q j i a≠0:= fun h=>hz (by simp [h])
    have hm:=mul_ne_zero hd hq
    have hentry :entry P j i a=d*entry Q j i a := by rw [he,entry_mul]
    have hPne :entry P j i a≠0:= fun h=>hm (hentry.symm.trans h)
    obtain ⟨hb,hj,hu,hw⟩:=entry_caps hp.1.1 hPne
    rw [hentry] at hu
    have hdeg: (entry Q j i a).totalDegree≤ s.U :=
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (dvd_mul_left _ _) hm).trans
        hu
    exact hn ⟨hb,hj,(MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hz)).trans hdeg,hw⟩
  · intro i a b j e hab
    have hz :entry (Km (ad0 i) (word i) P) j b a=0 :=
      MvPolynomial.ext _ _ fun f=> by
        rw [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
        change Fg (Km (ad0 i) (word i) P) j b a f=0
        exact hp.1.2 i a b j f hab
    rw [he,map_mul,bKs,entry_mul] at hz
    change (entry (Km (ad0 i) (word i) Q) j b a).coeff e=0
    simp [(mul_eq_zero.mp hz).resolve_left hd]
  · have hn:algebraMap qC aQ d≠0:= by
      simpa only [map_zero] using (zxb qC aQ).ne hd
    have hu:IsUnit (C (C (C (algebraMap qC aQ d))) :US) :=
      (((isUnit_iff_ne_zero.mpr hn).map C).map C).map C
    have hc:=hp.2
    change (pW ((IE D)^(s.B+s.J)) :US)∣forward crt P at hc
    rw [he,map_mul,cSV] at hc
    exact hu.dvd_mul_left.mp hc
private theorem degree_pos {d:qC} (hd:Irreducible d) :0<d.totalDegree := by
  apply zOl
  intro h
  have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
  apply hd.not_isUnit
  rw [he]
  apply (isUnit_iff_ne_zero.mpr ?_).map znf
  intro hz
  exact hd.ne_zero (by rw [he,hz,map_zero])
theorem primitive_entries {h} {D:jF h} (crt:zG D) {word s W}
    (nonzero : ∃ Q∈complete crt word s W,Q≠0) :
    ∃ f :qC,f≠0 ∧
      (∃ Q∈complete crt word s W,∃ j i a,entry Q j i a=f) ∧
      ∀ d:qC,Irreducible d→d∣f →
        ∃ Q∈complete crt word s W,∃ j i a,¬ d∣entry Q j i a := by
  classical
  let deg (n:ℕ) := ∃ Q∈complete crt word s W,∃ j i a,
    entry Q j i a≠0∧(entry Q j i a).totalDegree=n
  have hex : ∃ n,deg n:= by
    obtain ⟨Q,hQ,hne⟩:=nonzero
    have hc : ∃ j i a,entry Q j i a≠0:= by
      by_contra! hz
      exact hne (zXJ fun j=>zXJ fun i=>zXJ fun a=> by
        simpa only [Polynomial.coeff_zero] using hz j i a)
    obtain ⟨j,i,a,hc⟩:=hc
    exact ⟨_,Q,hQ,j,i,a,hc,rfl⟩
  obtain ⟨Q,hQ,j,i,a,hq,hn⟩:=Nat.find_spec hex
  refine ⟨_,hq,⟨Q,hQ,j,i,a,rfl⟩,?_⟩
  intro d hd _
  by_contra! hall
  have hdiv :Sl d∣Q:=(C_dvd_iff_dvd_coeff _ _).mpr (fun j =>
    (C_dvd_iff_dvd_coeff _ _).mpr (fun i =>
      (C_dvd_iff_dvd_coeff _ _).mpr (fun a=>hall Q hQ j i a)))
  obtain ⟨Q',he⟩:=hdiv
  have hnew :=divide_complete crt hd.ne_zero hQ he
  have hc:entry Q j i a=d*entry Q' j i a := by rw [he,entry_mul]
  rw [hc] at hq
  have hq' := right_ne_zero_of_mul hq
  have hmin:=Nat.find_min' hex ⟨Q',hnew,j,i,a,hq',rfl⟩
  rw [hc,zzD hd.ne_zero hq'] at hn
  have hp:=degree_pos hd
  omega
end
end qcOrJya
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qcOrJya
noncomputable section
open Finset DP
open cu (L)
open scoped Classical
open private eLU from ProximityPrize.SubmissionLower.G
private theorem count {U:ℕ} (f :qC) (hn:f≠0) (S:Finset (Fin 2→L))
    (hz : ∀ x∈S,zY9 x f=0)
    (cut : ∀ d:qC,Irreducible d→d∣f → ∃ g:qC,
      ¬ d∣g∧g.totalDegree≤U ∧ ∀ x∈S,zY9 x g=0) :
    S.card≤f.totalDegree*U:= by
  let:UniqueFactorizationMonoid L:=PrincipalIdealRing.to_uniqueFactorizationMonoid
  let:UniqueFactorizationMonoid qC:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  revert hn S hz cut
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero=>exact fun h=>(h rfl).elim
  | unit f hu =>
    intro _ S hz _
    have hS:S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx =>
      (hu.map (zY9 x)).ne_zero (hz x hx))
    simp [hS]
  | mul f d hf hd ih =>
    intro _ S hz cut
    let D:=S.filter fun x=>zY9 x d=0
    let T:=S \ D
    obtain ⟨g,hg,hU,hgz⟩:=cut d hd (dvd_mul_right _ _)
    have hD:D.card≤d.totalDegree*U :=
      (eLU d g hd (fun h=>hg (Ideal.mem_span_singleton.mp h)) D
        (fun x hx=>⟨(mem_filter.mp hx).2,hgz x (mem_filter.mp hx).1⟩)).trans
        (zBI _ hU)
    have hT:=ih hf T (fun x hx=> by
      obtain ⟨hm,hn⟩:=mem_sdiff.mp hx
      have he :=hz x hm
      rw [map_mul] at he
      exact (mul_eq_zero.mp he).resolve_left (fun h=>hn (mem_filter.mpr ⟨hm,h⟩)))
      (fun a ha haf=> by
        obtain ⟨g,hg,hU,hgz⟩:=cut a ha (haf.trans (dvd_mul_left _ _))
        exact ⟨g,hg,hU,fun x hx=>hgz x (mem_sdiff.mp hx).1⟩)
    rw [← card_sdiff_add_card_eq_card (filter_subset _ _:D⊆S),
      zzD hd.ne_zero hf,Nat.add_mul,
      Nat.add_comm (d.totalDegree*U) (f.totalDegree*U)]
    exact z9f hT hD
theorem bank_base {h} {D:jF h} (crt:zG D) {word s W}
    (nonzero : ∃ Q∈complete crt word s W,Q≠0) (S:Finset (Fin 2→L))
    (hz : ∀ x∈S,∀ Q∈complete crt word s W,∀ j i a,
      zY9 x (entry Q j i a)=0) :S.card≤ s.U^2 := by
  obtain ⟨f,hf,⟨Q,hQ,j,i,a,he⟩,prim⟩:=primitive_entries crt nonzero
  have hfn :entry Q j i a≠0:= by rwa [he]
  have hdeg:=(entry_caps hQ.1.1 hfn).2.2.1
  rw [he] at hdeg
  have hc:S.card≤f.totalDegree*s.U:= by
    refine count f hf S (fun x hx=> by rw [← he]; exact hz x hx Q hQ j i a) ?_
    intro d hd hdf
    obtain ⟨B,hB,j,i,a,hdiv⟩:=prim d hd hdf
    have hb:entry B j i a≠0:= fun h=>hdiv (by rw [h]; exact dvd_zero d)
    exact ⟨_,hdiv,(entry_caps hB.1.1 hb).2.2.1,fun x hx=>hz x hx B hB j i a⟩
  exact hc.trans (by rw [pow_two]; exact ztf _ hdeg)
end
end qcOrJya
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qcOrJya
noncomputable section
open Polynomial Finset
open P6 (K)
open P6_7_1
open qBPZs8a (fixedContentFee)
open cu (L FX aZ Jet qD jz)
open DP (Source qC Z7 U4 complete)
open gT (FW)
open pI (NO)
open qQ (IW)
open aF0 (BJ YM)
open akZ (aSK)
open scoped Classical Polynomial
private theorem graph_coefficients (z :K) :
    (qD z).comp (MvPolynomial.map (algebraMap L FX) :qC →+* aZ) =
      ((algebraMap L[X] FX).comp C).comp (zY9 (Z7 z)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [qD,RingHom.comp_apply]
    rfl
  · intro i
    fin_cases i <;> simp [qD,Z7,jz]
private theorem entry_zero {Q:Source} {z :K} (hz :seedSpecialize (U4 Q) z=0)
    (j i a :ℕ) :zY9 (Z7 z) (entry Q j i a)=0:= by
  let g:=(Q.coeff j).coeff i
  let φ:=zY9 (Z7 z)
  let ξ:=algebraMap L[X] FX (Polynomial.X (R:=L))
  have he :qD z (((U4 Q).coeff j).coeff i)=0:= by
    have hh:=congrArg (fun f :IW=>(f.coeff j).coeff i) hz
    simpa only [seedSpecialize,coeff_map,coe_mapRingHom,coeff_zero] using hh
  simp only [U4,Polynomial.coeff_mapAlgHom_apply] at he
  change qD z (g.eval₂ (MvPolynomial.map (algebraMap L FX)) (znf ξ))=0 at he
  rw [Polynomial.hom_eval₂,graph_coefficients,show qD z (znf ξ)=ξ
    from MvPolynomial.eval_C _] at he
  have hm:algebraMap L[X] FX (g.map φ)=0:= by
    change (zE2 L L[X] FX) (g.map φ)=0
    rw [← Polynomial.eval₂_algebraMap_X (g.map φ) (zE2 L L[X] FX),
      Polynomial.eval₂_map]
    exact he
  have hg:g.map φ=0:=(zxb L[X] FX) (hm.trans (map_zero _).symm)
  simpa only [g,φ,coeff_map,coeff_zero] using congrArg (fun f :L[X]=>f.coeff a) hg
private theorem content_zero {x :Input} {P:Poles x} {R:EarlyPicks x P}
    {A:NO R.anchorRow anchor} (a :aSK A) {z :K}
    (hz :qD z a.content=0) :seedSpecialize R.anchorRow z=0:= by
  let ev :=zhd (zhd (qD z))
  change ev R.anchorRow=0
  rw [A.factorization,a.bu2,map_mul,map_mul]
  have he :ev (C (C a.content) :Jet)=0:= by
    simp [ev,hz]
  rw [he,zero_mul,mul_zero]
private theorem seed_marks (x :Input) (P:Poles x) (R:EarlyPicks x P)
    {A:NO R.anchorRow anchor} (a :aSK A) :
    (x.Γ.filter fun γ=>qD (x.M.label γ) a.content=0).card≤1183^2 := by
  let S:=x.Γ.filter fun γ=>qD (x.M.label γ) a.content=0
  let W:=buffer x.h 0 anchor
  let V:=complete P.crt x.word anchor W
  have nonzero : ∃ Q∈V,Q≠0:= by
    by_contra! hz
    have hb:P.rows anchor W ≤ ⊥ := Submodule.span_le.mpr (by
      rintro _ ⟨Q,hQ,rfl⟩
      rw [hz Q hQ,map_zero]
      exact Submodule.zero_mem _)
    exact (R.free ⟨0,by decide⟩).ne_zero ((Submodule.mem_bot _).mp
      (hb (R.free ⟨0,by decide⟩).mem))
  have hi:zq4 (fun γ:K=>Z7 (x.M.label γ)) := fun _ _ h =>
    sub_left_inj.mp ((algebraMap K L).injective (congrFun h 0))
  have hc:=bank_base P.crt nonzero (S.image (fun γ=>Z7 (x.M.label γ))) (by
    intro y hy Q hQ j i a₀
    obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
    obtain ⟨hΓ,hz⟩:=mem_filter.mp hγ
    have ha :=(R.free ⟨0,by decide⟩).avoids γ hΓ (content_zero a hz) (U4 Q)
      (Submodule.subset_span ⟨Q,hQ,rfl⟩)
    exact entry_zero ha j i a₀)
  rwa [card_image_of_injective _ hi] at hc
theorem proof :qBPZs8a.c1 := by
  intro x P R A a
  let T:=x.Γ.filter fun γ=>FW A.equation (x.F.scalar γ)=0
  let S:=x.Γ.filter fun γ=>qD (x.M.label γ) a.content=0
  refine ⟨S∪T,(card_union_le _ _).trans
    ((z9f (seed_marks x P R a) (fixed_marks x _ A.equation_caps)).trans ?_),?_⟩
  · change 1183^2+(3*((115-25)*YM degree 115 25+25*BJ degree 115)+115^2)≤fixedContentFee
    exact (show 0xf150c713≤0x1b61671120 by decide)
  · intro γ hγ hz
    exact mem_union.mpr (hz.imp (fun h=>mem_filter.mpr ⟨hγ,h⟩) (fun h=>mem_filter.mpr ⟨hγ,h⟩))
end
end qcOrJya
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 12
namespace q9scLLa
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
open P6 (K p)
open P6_7_1 (Input)
open qBPZs8a (Mark eHB)
open qQ9yWTb (Curve Usable)
open qHEUR1a (Raw embed height threshold)
open cu (L Jet Equation yq)
open Qt (gY Qc)
open atc (bri bg3)
open akZ (ajz yE)
open scoped Classical BigOperators
open private c2O from ProximityPrize.SubmissionLower.K
def c1 :Prop :=
  ∀ (x :Input) (T:Finset K),T⊆x.Γ →
    ∀ F:Raw,Sheet F→weight F≤threshold →
      (∀ γ∈T,Zk x (embed F) γ) →
      ∀ q:Curve,Irreducible q →
        ((T.filter fun γ=>Usable q (site x γ)).card:ℚ) ≤
          ((slope :ℚ)*(height F:ℚ))*q.totalDegree
def c2 :Prop :=qQ9yWTb.c5
private theorem site_inj (x :Input) :zq4 (site x) := by
  intro a b h
  have hz :=congrFun h 0
  change algebraMap K L (x.M.label a)=algebraMap K L (x.M.label b) at hz
  exact sub_left_inj.mp (FaithfulSMul.algebraMap_injective K L hz)
private theorem lift_factor {f :Equation} (hf :Irreducible f) :
    ∃ F:Raw,Irreducible F∧Associated (embed F) f := by
  obtain ⟨Q,a,ha,hQ,_,_,_⟩:=Y3.normalize f _ _ hf.ne_zero le_rfl
    ((Qc f _).mp le_rfl)
  have hu:IsUnit (Y3.constant a) :=(isUnit_iff_ne_zero.mpr ha).map _
  have haQ:Associated (embed Q) f :=hQ ▸ (associated_unit_mul_left _ _ hu)
  have hn:Q≠0:= by
    intro h
    rw [h,map_zero] at haQ
    exact hf.ne_zero ((associated_zero_iff_eq_zero _).mp haQ.symm)
  have find (N :Multiset Raw) (h:Associated (embed N.prod) f) :
      ∃ F∈N,Associated (embed F) f := by
    induction N using Multiset.induction_on with
    | empty =>
      rw [Multiset.prod_zero,map_one] at h
      exact (hf.not_isUnit (h.isUnit isUnit_one)).elim
    | cons F N ih =>
      rw [Multiset.prod_cons,map_mul] at h
      rcases (h.symm.irreducible hf).isUnit_or_isUnit rfl with huF | huN
      · obtain ⟨G,hG,ha⟩:=ih ((associated_unit_mul_right _ _ huF).trans h)
        exact ⟨G,Multiset.mem_cons_of_mem hG,ha⟩
      · exact ⟨F,Multiset.mem_cons_self _ _,(associated_mul_unit_right _ _ huN).trans h⟩
  let _:StrongNormalizationMonoid Raw:=UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨F,hF,ha⟩:=find (normalizedFactors Q) (((prod_normalizedFactors hn).map embed).trans haQ)
  exact ⟨F,irreducible_of_normalized_factor F hF,ha⟩
private theorem root_dvd {x :Input} {f g:Equation} {γ:K} (h:f∣g)
    (hr :Zk x f γ) :Zk x g γ:= by
  obtain ⟨a,rfl⟩:=h
  unfold Zk at *
  unfold yq at *
  rw [eval₂_mul,hr,zero_mul]
private theorem low_count {a v :ℕ} (hv :v≤142)
    (h:3*(a :ℚ)≤10*(slope*(v :ℚ))^2) :a≤ rate*v := by
  have h' : 3*a≤10*slope^2*v*v := by
    have he : (10 :ℚ)*(slope*(v :ℚ))^2=(10*slope^2)*(v :ℚ)*v := by ring
    rw [he] at h
    exact_mod_cast h
  have h'' : 10*slope^2*v*v≤3*(rate*v) := calc
    _≤10*slope^2*142*v :=
      ztf v (zBI _ hv)
    _≤_:= by
      rw [← Nat.mul_assoc]
      exact ztf v (by decide)
  exact Nat.le_of_mul_le_mul_left (h'.trans h'') (by decide)
private theorem d5P (qv :c1) (u7:c2)
    (x :Input) (T:Finset K) (hT:T⊆x.Γ) {f :Equation}
    (hi:Irreducible f) (hpos :0<f.natDegree) (he :f.natDegree≤12)
    (hu:gY f≤142) (hr : ∀ γ∈T,Zk x f γ) :
    T.card≤f.natDegree+rate*gY f := by
  have hz :zq4 x.M.label := fun _ _ h=>sub_left_inj.mp h
  by_cases hzero :gY f=0
  · have hs :=(Qc f 0).mp hzero.le
    obtain ⟨g,hg,hd,hv,hgraph⟩:=P5_7.native_restriction hi.ne_zero (by decide) hs
    exact (P5_7_7.seed_zero_count (z :=x.M.label) (x.F.distinct.mono hT) hg
      (by simpa only [Nat.mul_zero] using hv) (fun γ hγ=>(hgraph _ _).trans (hr γ hγ))).trans
      (hd.trans (z8K _ _))
  obtain ⟨F,hF,hassoc⟩:=lift_factor hi
  have hirr :=hassoc.symm.irreducible hi
  have hdeg: (embed F).natDegree=f.natDegree :=
    le_antisymm (natDegree_le_of_dvd hassoc.dvd hi.ne_zero)
      (natDegree_le_of_dvd hassoc.dvd' hirr.ne_zero)
  have hs :height F=gY f := by
    have aux {g h:Equation} (hne :h≠0) (hd:g∣h) :gY g≤gY h:= by
      obtain ⟨a,rfl⟩:=hd
      rw [Qt.acG (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)]
      exact z8K _ _
    exact le_antisymm (aux hi.ne_zero hassoc.dvd) (aux hirr.ne_zero hassoc.dvd')
  have hdeg' : (embed F).natDegree=F.natDegree :=
    natDegree_map_eq_of_injective (MvPolynomial.map_injective _
      (zxb cu.L[X] cu.FX)) F
  have hsheet:Sheet F :=
    ⟨hF,hirr,(hdeg'.symm.trans hdeg) ▸ hpos,(hdeg'.symm.trans hdeg) ▸ he,
      hs ▸ zOl hzero,hs ▸ hu⟩
  have hroots : ∀ γ∈T,Zk x (embed F) γ:= fun γ hγ=>root_dvd hassoc.dvd' (hr γ hγ)
  suffices hc:T.card≤ rate*height F by
    rw [hs] at hc
    exact hc.trans (Nat.le_add_left _ _)
  by_cases hw:threshold<weight F
  · obtain ⟨g,hg,hp,hgc,hgr⟩:=emK x T hT F hsheet hw hroots
    have hf :=(Qc _ _).mp (le_refl (height F))
    have hdigit : (12*(1000+1)+14)*height F<p :=
      (zBI _ hsheet.2.2.2.2.2).trans_lt (by decide)
    have hh:=qQ9yWTb.count_resultant (e :=12) (E :=14) (cz :=1000) (ct :=1)
      (hdeg.symm ▸ hpos) (hdeg.symm ▸ he) hg hf hgc hp hdigit hz.injOn hroots hgr
    exact hh.trans (calc
      _=((12*(1000+1)+14)+p*(12*(1+1)+14))*height F:= by ring
      _≤_:=ztf _ (by decide))
  · exact low_count hsheet.2.2.2.2.2
      (u7 T (site x) (site_inj x).injOn _ (by positivity)
        (qv x T hT F hsheet (le_of_not_gt hw) hroots))
theorem of_children (qv :c1) (u7:c2) :qBPZs8a.c2 := by
  intro x G D hD hv hcap
  let slice (f :Jet) :=x.Γ.filter (Mark x f)
  let gH :=D.biUnion slice
  refine ⟨gH,?_,fun f hf γ hγ hm=>mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨hγ,hm⟩⟩⟩
  have hb:ajz D 0≤12 :=(hcap 0).trans_eq (by decide)
  have hu:ajz D 2≤142 :=(hcap 2).trans_eq (by decide)
  have hcount (f :Jet) (hf :f∈D) :
      (slice f).card≤yE f 0+rate*yE f 2 := by
    obtain ⟨hi,_,_,hseed,_⟩:=hD.factors f hf
    obtain ⟨hC,hF,hp⟩:=c2O hi (hv f hf) hseed
    have h₀:yE f 0=(f.coeff 0).natDegree := by
      change atc.jetDegree f= _
      exact (congrArg atc.jetDegree hC).symm.trans (bri _)
    have h₂:yE f 2=gY (f.coeff 0) := by
      change atc.gY f= _
      rw [← congrArg atc.gY hC,bg3]
      apply le_antisymm
      · exact Finset.sup_le fun j _=>(Qc _ _).mp le_rfl j
      · apply (Qc _ _).mpr
        intro j
        by_cases hj:j∈(f.coeff 0).support
        · exact Finset.le_sup (f := fun i=>((f.coeff 0).coeff i).totalDegree) hj
        · simp [notMem_support_iff.mp hj]
    rw [h₀,h₂]
    refine d5P qv u7 x (slice f) (filter_subset _ _) hF hp ?_ ?_ ?_
    · exact h₀ ▸ ((single_le_sum (f := fun g=>yE g 0) (fun _ _=>Nat.zero_le _) hf).trans hb)
    · exact h₂ ▸ ((single_le_sum (f := fun g=>yE g 2) (fun _ _=>Nat.zero_le _) hf).trans hu)
    · intro γ hγ
      have h:=(mem_filter.mp hγ).2
      unfold Mark cu.rD at h
      rw [← hC,eval₂_C] at h
      exact h
  calc
    gH.card ≤ ∑ f∈D,(slice f).card:=card_biUnion_le
    _ ≤ ∑ f∈D,(yE f 0+rate*yE f 2) :=
      sum_le_sum hcount
    _=ajz D 0+rate*ajz D 2 := by
      rw [sum_add_distrib,← mul_sum]
      rfl
    _≤12+rate*142 :=z9f hb (zBI _ hu)
    _≤12+rate*142+p*142 :=z8K _ _
    _≤eHB:= by decide
end
end q9scLLa
end
