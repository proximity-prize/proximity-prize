import ProximityPrize.SubmissionLower.ZwuC0Sd
set_option Elab.async false
open _root_ renaming Ideal → znc, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.Quotient.mk_surjective → zld, Ideal.isCoprime_iff_sup_eq → zDt, Ideal.map_le_iff_le_comap → zo0, Ideal.map_pow → zXb, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_right → zs0, Ideal.mk_ker → zlC, Ideal.pow_le_pow_right → zdr, Ideal.pow_mem_pow → z2s, Ideal.quotientEquivAlgOfEq → z9k, Ideal.span → zye, Module.Finite → zAa, Module.Finite.of_surjective → zIU, Module.finrank → zsE, Module.length_eq_finrank → z1C, Nat.mul_le_mul_left → zBI, Polynomial.uniqueFactorizationMonoid → zV6, RingHom.ker_eq_comap_bot → zPx
set_option maxHeartbeats 1500000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q7Huoga
noncomputable section
open Finset Polynomial
open P6 (p dw)
open P6_7 (RectTail)
open P6_7_2 P6_7_2_3
open cu (Jet aZ Equation)
open DP (d3q d3r)
open gT (Ambient aQ iJ)
open pI (xN dual oU O9)
open ac2 (bp3 dLt aVL Ih)
open XY (ag6)
open TD (GM auN J2 bfw cZV)
open akZ (yE cN4 caQ)
open P5_7_1 (wD)
open scoped Classical
open private emz from ProximityPrize.SubmissionLower.ZUkTKja
open private pass_free from ProximityPrize.SubmissionLower.ZffaUPa
open private dfc ddV from ProximityPrize.SubmissionLower.U
open private b6z from ProximityPrize.SubmissionLower.D7
open private positive_spend from ProximityPrize.SubmissionLower.Zc1KtHb
private theorem free_checks (b:RectTail) (i:Ls) :
    dI i<p∧(free b i).J≤(free b i).B ∧
      2*(Bs b).hi*dI i≤(free b i).m*dw-1 := by
  cases b <;> fin_cases i <;> exact ⟨by decide,by decide,by decide⟩
variable {b:RectTail} {x :Input b} (P:Poles x) (pick :Picks (b:=b) x.h P.rows)
private theorem free_order (i:Ls) {Q:znc Ambient} (ha :xN Q) (hd:dual Q)
    (hv :freePass P i Q) :O9 Q (pick.freeRow i) (dI i+1) := by
  obtain ⟨hr,_,hroom⟩:=free_checks b i
  have ht:=(Nat.mul_le_mul_right (dI i)
    (zBI 2 (emz x).2)).trans hroom
  have hcut:cutoff x.h (dI i) (free b i)+2*x.h*dI i=cutoff x.h 0 (free b i) := by
    simpa only [cutoff,mul_zero,Nat.sub_zero] using Nat.sub_add_cancel ht
  have hs :qQ.bk4 x.h P.rows (free b i) :=
    fun _ _ h t a=>atp.d3s P.crt x.word h t a
  let a :=algebraMap aZ aQ
  have hc:bp3 (Q.map (Ih a)) (Ih a (iJ (pick.freeRow i))) (dI i) := by
    intro t ht
    rw [← dfc]
    apply Ideal.mem_map_of_mem
    apply hv
    exact d3q P.crt x.word rfl rfl rfl le_rfl
      ((Nat.add_le_add_left (zBI _ ht) _).trans_eq hcut)
      (ddV hs (pick.free_mem i) t)
  change bp3 (Q.map (Ih (algebraMap aZ aQ)))
    (Ih (algebraMap aZ aQ) (iJ (pick.freeRow i))) (dI i) at hc
  rw [← aVL] at hc
  exact dLt hd (cy0.proof Q ha.prime ha.jet_finite hd ha.jet_lt _ _ hr hc)
private abbrev tests (s :bAL) :=(List.ofFn fun i:FreeTest=>freeStage i).take (s.val-1)
private def freeBound (b:RectTail) (o:Origin) (i:Ls) (k :Fin 4) :ℚ :=
  kK (auN (free b i)) (refShape b o) k/(dI i+1 :ℕ)
private theorem fold_coord (b:RectTail) (o:Origin) (L:List Ls) (a :GM) (k :Fin 4) :
    L.foldl (fun c i j=>min (c j) (freeBound b o i j)) a k =
      L.foldl (fun c i=>min c (freeBound b o i k)) (a k) := by
  induction L generalizing a with
  | nil=>rfl
  | cons i L ih=>exact ih _
private theorem cap_fold (o:Origin) (s :bAL) (k :Fin 4) :
    liveCap b o s k=(tests s).foldl (fun c i=>min c (freeBound b o i k)) (originBox b o k) :=
  fold_coord b o _ _ k
private theorem passed_test {s :bAL} {i:Ls} (hi:i∈tests s) {Q:znc Ambient}
    (hQ : ∀ t<s,passes P t Q) :dual Q∧freePass P i Q:= by
  obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp hi
  have hl:=hn
  simp only [tests,List.length_take,List.length_ofFn,lt_min_iff] at hl
  let j:FreeTest:=⟨n,hl.2⟩
  have hj:freeStage j=i:= by simpa only [tests,List.getElem_take,List.getElem_ofFn] using he
  have hs :freeStop j<s := by
    have h:=hl.1
    change n+1<s.val
    omega
  have hp: (0:bAL)<s := by
    change 0<s.val
    have h:n+1<s.val :=hs
    omega
  exact ⟨by simpa only [passes,ite_true] using hQ 0 hp,
    hj ▸ (pass_free P j Q).mp (hQ _ hs)⟩
include pick in
private theorem live_bound (o:Origin) (s :bAL) (S:Finset (znc Ambient))
    {F G:Jet} (hp:ag6 F G) (hF:oU F (refShape b o)) (hG:oU G (refShape b o))
    (hS : ∀ Q∈S,xN Q∧iJ F∈Q∧iJ G∈Q ∧ ∀ t<s,passes P t Q)
    (k :Fin 4) (h0:J2 S k≤originBox b o k) :J2 S k≤liveCap b o s k := by
  rw [cap_fold]
  apply q54LkTb.le_folds _ _ _ _ h0
  intro i hi
  exact q41fOQb.proof _ F G _ _ S _ (Nat.succ_pos _) (pick.free_ne i) hp
    (free_checks b i).2.1 (ref_J b o) (d3r P.crt x.word (pick.free_mem i))
    hF hG (fun Q hQ=> by
      obtain ⟨ha,hf,hg,hs⟩:=hS Q hQ
      obtain ⟨hd,hb⟩:=passed_test P hi hs
      exact ⟨ha,hd,hf,hg,free_order P pick i ha hd hb⟩) k
variable {P pick} (O:OriginCover P pick)
private theorem assigned {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤ stock b (O.origin f) f (O.line f) k := by
  refine mass_cut_rat O hf k ?_ (O.cut_caps f hf)
  unfold anZ
  split
  · exact caQ (O.proper f hf).1.ne_zero
  · exact origin_J b _
private theorem origin_mass {f :Jet} (hf :f∈O.factors) (k :Fin 4) :
    J2 (O.parents f) k≤kK (wD f) (originShape b (O.origin f)) k :=
  mass_cut_rat O hf k (origin_J b _) (cut_origin O hf)
private theorem factor_live {f :Jet} (hf :f∈O.factors) (s :bAL)
    (S:Finset (znc Ambient)) (hS:S⊆QV O f s) (k :Fin 4) :
    J2 S k≤liveCap b (O.origin f) s k := by
  have hp:=O.proper f hf
  refine live_bound P pick _ s S (b6z hp.1 hp.2.2)
    (spend_ref (spend_cap O hf)) (cut_ref (cut_origin O hf)) ?_ k ?_
  · intro Q hQ
    obtain ⟨hQ,ht⟩:=mem_filter.mp (hS hQ)
    obtain ⟨ha,_,hf,hg⟩:=O.geometric f hf Q hQ
    exact ⟨ha,hf,hg,ht⟩
  · exact (bfw (hS.trans (filter_subset _ _)) k).trans
      ((origin_mass O hf k).trans (tD (spend_cap O hf) _ _))
private def bin (o:Origin) :Finset Jet:=O.factors.filter fun f=>O.origin f=o
private theorem bin_spend (o:Origin) (j:Fin 3) :
    (∑ f∈bin O o,wD f j)≤ introCap b o j:= by
  refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>Nat.zero_le _)).trans (O.nested o j)
  intro f hf
  obtain ⟨hf,he⟩:=mem_filter.mp hf
  exact mem_filter.mpr ⟨hf,he.ge⟩
private theorem pool_nonlast (o:Origin) (ho:o≠last) (k :Fin 4) :
    (∑ f∈bin O o,J2 (QV O f terminalStop) k)≤liveCap b o terminalStop k := by
  let D:=bin O o
  by_cases he :D.Nonempty
  · obtain ⟨f,hf⟩:=he
    let F:Jet := ∏ g∈D,g
    let S:=D.biUnion fun g=>QV O g terminalStop
    have hcuts (g:Jet) (hg:g∈D) :O.cut g=O.cut f := by
      obtain ⟨hg,hgo⟩:=mem_filter.mp hg
      obtain ⟨hf,hfo⟩:=mem_filter.mp hf
      exact O.shared_cut g hg f hf (hgo.symm ▸ ho) (hgo.trans hfo.symm)
    have hn (g:Jet) (hg:g∈D) :g≠0:=(O.proper g (mem_filter.mp hg).1).1.ne_zero
    have hpair :ag6 F (O.cut f) := by
      refine ⟨(Finset.prod_ne_zero_iff (s :=D) (f := fun g:Jet=>g)).mpr hn,
        (b6z (O.proper f (mem_filter.mp hf).1).1 (O.proper f (mem_filter.mp hf).1).2.2).right_ne,?_⟩
      intro H hH hd hc
      let:UniqueFactorizationMonoid aZ:=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
      let:UniqueFactorizationMonoid Equation :=zV6 (D:=aZ)
      let:UniqueFactorizationMonoid Jet:=zV6 (D:=Equation)
      change H ∣ ∏ g∈D,g at hd
      obtain ⟨g,hg,hgd⟩:=(hH.prime.dvd_finsetProd_iff (S:=D) (fun g:Jet=>g)).mp hd
      have hg' := O.proper g (mem_filter.mp hg).1
      exact hg'.2.2 ((hH.associated_of_dvd hg'.1 hgd).dvd'.trans ((hcuts g hg).symm ▸ hc))
    have hF:oU F (refShape b o) :=spend_ref (fun j=> by
      change yE (∏ g∈D,g) j≤ introCap b o j
      rw [cN4 (S:=D) (f := fun g:Jet=>g) hn]
      exact bin_spend O o j)
    have hG:oU (O.cut f) (refShape b o) :=
      cut_ref ((mem_filter.mp hf).2 ▸ cut_origin O (mem_filter.mp hf).1)
    have hd: (D:Set Jet).PairwiseDisjoint (fun g=>QV O g terminalStop) := by
      intro g hg g' hg' hn
      exact (O.disjoint g (mem_filter.mp hg).1 g' (mem_filter.mp hg').1 hn).mono
        (filter_subset _ _) (filter_subset _ _)
    have hsum:J2 S k = ∑ g∈D,J2 (QV O g terminalStop) k := by
      simp only [S,J2,pI.mass,sum_biUnion hd,Nat.cast_sum]
    refine hsum ▸ live_bound P pick o terminalStop S hpair hF hG ?_ k ?_
    · intro Q hQ
      obtain ⟨g,hg,hQ⟩:=mem_biUnion.mp hQ
      obtain ⟨hp,ht⟩:=mem_filter.mp hQ
      obtain ⟨ha,_,haF,haG⟩:=O.geometric g (mem_filter.mp hg).1 Q hp
      exact ⟨ha,Q.mem_of_dvd (map_dvd iJ (dvd_prod_of_mem (fun a=>a) hg)) haF,hcuts g hg ▸ haG,ht⟩
    · rw [hsum]
      calc
        _ ≤ ∑ g∈D,kK (wD g) (originShape b o) k := by
          apply sum_le_sum
          intro g hg
          obtain ⟨hg,he⟩:=mem_filter.mp hg
          rw [← he]
          exact (bfw (filter_subset _ _) k).trans (origin_mass O hg k)
        _=kK (fun j => ∑ g∈D,wD g j) (originShape b o) k := by
          simp only [kK,Nat.cast_sum,sum_mul]
          exact sum_comm
        _≤_:=tD (bin_spend O o) _ _
  · rw [show bin O o = ∅ from not_nonempty_iff_eq_empty.mp he,sum_empty,cap_fold]
    exact q54LkTb.le_folds _ _ _ _ (b9i _ _ _) fun i _ =>
      div_nonneg (b9i _ _ _) (Nat.cast_nonneg _)
private theorem pool (o:Origin) (k :Fin 4) :
    (∑ f∈bin O o,J2 (QV O f terminalStop) k)≤endCap b o k := by
  by_cases ho:o=last
  · have hc: (bin O o).card ≤ ∑ j,introCap b o j:= by
      calc
        _ = ∑ f∈bin O o,(1 :ℕ) := by simp
        _ ≤ ∑ f∈bin O o,∑ j,wD f j :=
          sum_le_sum fun f hf=>positive_spend (O.proper f (mem_filter.mp hf).1).1
        _ = ∑ j,∑ f∈bin O o,wD f j:=sum_comm
        _≤_:=sum_le_sum fun j _=>bin_spend O o j
    have hn:0≤liveCap b o terminalStop k := by
      rw [cap_fold]
      exact q54LkTb.le_folds _ _ _ _ (b9i _ _ _) fun i _ =>
        div_nonneg (b9i _ _ _) (Nat.cast_nonneg _)
    rw [endCap,ite_eq_left ho]
    calc
      _ ≤ ∑ f∈bin O o,liveCap b o terminalStop k := by
        apply sum_le_sum
        intro f hf
        obtain ⟨hf,he⟩:=mem_filter.mp hf
        rw [← he]
        exact factor_live O hf _ _ (Subset.refl _) k
      _=liveCap b o terminalStop k*((bin O o).card:ℚ) := by rw [sum_const,nsmul_eq_mul,mul_comm]
      _≤_:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) hn
  · simpa only [endCap,ite_eq_right ho,Nat.cast_one,mul_one] using pool_nonlast O o ho k
theorem proof :P6_7_2_3.c2 := by
  intro b x P pick O
  refine ⟨fun f hf=>caQ (O.proper f hf).1.ne_zero,fun _=>assigned O,bAW O,?_,pool O⟩
  intro f hf s Q hQ k
  have hS: ({Q} : Finset (znc Ambient))⊆QV O f s :=singleton_subset_iff.mpr hQ
  have hs :J2 {Q} k=sectionMass Q k := by simp [J2,pI.mass,sectionMass]
  rw [memberCap,← hs]
  exact le_min (factor_live O hf s _ hS k)
    ((bfw (hS.trans (filter_subset _ _)) k).trans
      ((single_le_sum (fun _ _=>cZV _ k) hf).trans (bAW O k)))
end
end q7Huoga
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qcYgGze
noncomputable section
open private gwL from ProximityPrize.SubmissionLower.U
open scoped Classical BigOperators
private theorem thick_bound {k R:Type} [Field k] [CommRing R] [IsNoetherianRing R] [Algebra k R]
    {H M:znc R} (hH :H.IsPrime) (hM:M.IsMaximal) (hHM:H<M)
    {n:ℕ} (hn:0<n) [zAa k (R ⧸ (H ⊔ M^n))] :
    n*zsE k (R ⧸ M)≤zsE k (R ⧸ (H ⊔ M^n)) := by
  let:M.IsMaximal:=hM
  let D:=H ⊔ M^n
  let B:=R ⧸ D
  let q:=Ideal.Quotient.mk D
  let m:=M.map q
  have hDM:D ≤M:=sup_le hHM.le (Ideal.pow_le_self hn.ne')
  have hc:m.comap q=M:= by
    rw [Ideal.comap_map_of_surjective _ zld,
      ← zPx,zlC,sup_eq_left.mpr hDM]
  have hm:m.IsMaximal:= by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective q zld hM).resolve_left ?_
    intro h
    change m = ⊤ at h
    exact hM.ne_top (by rw [← hc,h,Ideal.comap_top])
  let:IsLocalRing B:=IsLocalRing.of_unique_max_ideal ⟨m,hm,fun N hN=> by
    let:N.IsMaximal:=hN
    have hN' : (N.comap q).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective q zld
    have hl:D ≤N.comap q:= by
      intro x hx
      change q x∈N
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact N.zero_mem
    apply (Ideal.comap_injective_of_surjective q zld)
    rw [hc]
    exact (hM.eq_of_le hN'.ne_top fun x hx =>
      hN'.isPrime.mem_of_pow_mem n (hl (zs0 (z2s hx n)))).symm⟩
  have hnil:m^n = ⊥ := by
    rw [← zXb]
    exact le_antisymm ((zo0).mpr
      (show M^n≤(⊥ : znc B).comap q from by
        rw [← zPx,zlC]; exact le_sup_right)) bot_le
  have hnonzero (i:ℕ) (hi:i<n) :m^i ≠ ⊥ := by
    intro hh
    have hle :M^i≤(⊥ : znc B).comap q:= by
      rw [← zo0,zXb,hh]
    have hpow:M^i≤H ⊔ M^n:= by
      rw [← zPx,show RingHom.ker q=D from zlC] at hle
      exact hle
    have he :H ⊔ M^i=H ⊔ M^n :=
      le_antisymm (sup_le le_sup_left hpow)
        (sup_le_sup_left (zdr hi.le) H)
    have hloc:=congrArg (Ideal.map (algebraMap R (Localization.AtPrime M))) he
    let A:=Localization.AtPrime M
    let phi:=algebraMap R A
    let P:=H.map phi
    let t:=IsLocalRing.maximalIdeal A
    have he' : P ⊔ t^i=P ⊔ t^n:= by
      simpa only [Ideal.map_sup,zXb,Localization.AtPrime.map_eq_maximalIdeal] using hloc
    have hle' : t^i≤P ⊔ t•t^i:= by
      rw [smul_eq_mul,← pow_succ']
      exact (show t^i≤P ⊔ t^i from le_sup_right).trans
        (he'.trans_le (sup_le_sup_left (zdr (Nat.succ_le_of_lt hi)) P))
    have htP:t^i≤P:=Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian _) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle'
    obtain ⟨x,hx,hxH⟩:=(SetLike.lt_iff_le_and_exists.mp hHM).2
    have hxA:phi x∈t:=(IsLocalization.AtPrime.to_map_mem_maximal_iff A M x).mpr hx
    have hxP:phi (x^i)∈P:= by rw [map_pow]; exact htP (z2s hxA i)
    change algebraMap R A (x^i)∈H.map (algebraMap R A) at hxP
    obtain ⟨a,ha,hax⟩:=(IsLocalization.algebraMap_mem_map_algebraMap_iff M.primeCompl A H _).mp hxP
    exact hxH (hH.mem_of_pow_mem i
      ((hH.mem_or_mem hax).resolve_left (fun haH=>ha (hHM.le haH))))
  have hstrict (i:ℕ) (hi:i<n) :m^(i+1)< m^i:= by
    refine lt_of_le_of_ne (zdr (Nat.le_succ i)) ?_
    intro he
    apply hnonzero i hi
    have heq (j:ℕ) :m^(i+j)=m^i:= by
      induction j with
      | zero=>simp
      | succ j ih=>rw [← Nat.add_assoc,pow_succ,ih,← pow_succ,he]
    rw [← heq (n-i),Nat.add_sub_of_le hi.le,hnil]
  have hh (i:ℕ) (hi:i≤n) : (i:ℕ∞)≤Order.coheight ((m^i:znc B) :Submodule B B) := by
    induction i with
    | zero=>simp
    | succ i ih =>
      rw [Nat.cast_succ]
      exact (add_le_add_left (ih (Nat.le_of_succ_le hi)) 1).trans
        (Order.coheight_add_one_le
          (show ((m^(i+1) :znc B) :Submodule B B)<((m^i:znc B) :Submodule B B) from
            hstrict i (Nat.lt_of_succ_le hi)))
  have hlen: (n:ℕ∞)≤Module.length B B:= by
    simpa only [hnil,Module.length_eq_coheight] using hh n le_rfl
  have e :IsLocalRing.ResidueField B ≃ₐ[k] R ⧸ M :=
    (z9k k (IsLocalRing.eq_maximalIdeal hm).symm).trans
      ((DoubleQuot.quotQuotEquivQuotSupₐ k D M).trans
        (z9k k (sup_eq_right.mpr hDM)))
  let ek :k ≃ₐ[k] IsLocalRing.ResidueField k :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k k _)
      ⟨(algebraMap k (IsLocalRing.ResidueField k)).injective,IsLocalRing.residue_surjective⟩
  have hk :zsE k (IsLocalRing.ResidueField k)=1 :=
    ek.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self k)
  have htower :=Module.finrank_mul_finrank k (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField B)
  rw [hk,one_mul] at htower
  have hlen' := IsLocalRing.length_restrictScalars k B B
  rw [z1C,z1C,htower,e.toLinearEquiv.finrank_eq] at hlen'
  exact ENat.natCast_le_natCast.mp (by
    push_cast
    rw [hlen']
    by_cases hz :zsE k (R ⧸ M)=0
    · simp [hz]
    · exact ENat.mul_le_mul_of_le_right hlen (by simpa) (by simp))
private theorem pow_of_mul_mem {R:Type} [CommRing R] {M:znc R} (hM:M.IsMaximal)
    {a f :R} {n:ℕ} (ha :a∉M) (h:a*f∈M^n) :f∈M^n:= by
  have hcp:IsCoprime (zye {a}) M:= by
    rw [zDt,sup_comm]
    by_contra hn
    have he :=hM.eq_of_le hn le_sup_left
    exact ha (he.symm ▸ zs0 (z5J a))
  obtain ⟨u,hu,v,hv,he⟩:=Ideal.isCoprime_iff_exists.mp (hcp.pow_right (n:=n))
  obtain ⟨z,rfl⟩:=Ideal.mem_span_singleton.mp hu
  have hf :f=z*(a*f)+f*v := calc
    _=f*(a*z+v) := by rw [he,mul_one]
    _ = _:= by ring
  rw [hf]
  exact (M^n).add_mem ((M^n).mul_mem_left z h) ((M^n).mul_mem_left f hv)
theorem dlW {k R ι:Type} [Field k] [CommRing R] [IsNoetherianRing R] [Algebra k R]
    [Fintype ι] {H :znc R} (hH :H.IsPrime) {f :R} (hf :f∉H)
    (M:ι→ znc R) (w:ι→ℕ)
    (hM : ∀ i,M i = ⊤ ∨ (M i).IsPrime)
    (hdis : ∀ i j,i≠j→M i ≠ ⊤ → M j ≠ ⊤ → M i≠M j)
    (hle : ∀ i,H ⊔ zye {f} ≤ M i)
    (hw : ∀ i,0<w i)
    (hpaid : ∀ i,M i ≠ ⊤ → ∃ a :R,a∉M i∧a*f∈M i^w i)
    [zAa k (R ⧸ (H ⊔ zye {f}))] :
    (∑ i,w i*zsE k (R ⧸ M i)) ≤
      zsE k (R ⧸ (H ⊔ zye {f})) := by
  let D:=H ⊔ zye {f}
  let J (i:ι) :=H ⊔ M i^w i
  have hmax (i:ι) (hi:M i ≠ ⊤) : (M i).IsMaximal:= by
    let: (M i).IsPrime :=(hM i).resolve_left hi
    let:zAa k (R ⧸ M i) :=
      zIU (z5F k (hle i)).toLinearMap
        (zuo (hle i))
    exact Ideal.Quotient.maximal_of_isField _ (IsField.of_isDomain_of_finite k (R ⧸ M i))
  have htop (i:ι) (hi:M i = ⊤) :J i = ⊤ := by
    have hpow: (⊤ : znc R)^w i = ⊤ := by rw [← Ideal.one_eq_top,one_pow]
    simp only [J,hi,hpow,sup_top_eq]
  have hD (i:ι) :D ≤J i:= by
    by_cases hi:M i = ⊤
    · rw [htop i hi]; exact le_top
    · obtain ⟨a,ha,hm⟩:=hpaid i hi
      exact sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (zs0 (pow_of_mul_mem (hmax i hi) ha hm)))
  have hp:Pairwise fun i j=>IsCoprime (J i) (J j) := by
    intro i j hij
    by_cases hi:M i = ⊤
    · simp [htop i hi,zDt]
    by_cases hj:M j = ⊤
    · simp [htop j hj,zDt]
    let _: (M i).IsMaximal:=hmax i hi
    let _: (M j).IsMaximal:=hmax j hj
    have h:IsCoprime (M i^w i) (M j^w j) :=
      (Ideal.isCoprime_of_isMaximal (hdis i j hij hi hj)).pow
    rw [zDt] at h ⊢
    exact top_unique (h ▸ sup_le_sup (show M i^w i≤J i from le_sup_right)
      (show M j^w j≤J j from le_sup_right))
  refine (Finset.sum_le_sum fun i _ => ?_).trans (gwL D J hD hp)
  by_cases hi:M i = ⊤
  · have hz :zsE k (R ⧸ M i)=0:= by
      rw [hi]
      exact Module.finrank_zero_of_subsingleton
    simp [hz]
  · have hproper :H<M i:=lt_of_le_of_ne (le_sup_left.trans (hle i)) (fun h =>
      hf (h.symm ▸ hle i (zs0 (z5J f))))
    let:zAa k (R ⧸ J i) :=
      zIU (z5F k (hD i)).toLinearMap
        (zuo (hD i))
    exact thick_bound hH (hmax i hi) hproper (hw i)
end
end qcYgGze
end
