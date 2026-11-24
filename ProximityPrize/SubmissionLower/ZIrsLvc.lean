import ProximityPrize.SubmissionLower.ZIBb1mb
set_option Elab.async false
set_option autoImplicit true
namespace P6_6_7_3
noncomputable section
open P6_6 P6_6_7
open aR (af Shape shape aO cK extend)
open dN (GeoJets bC kC oA Ch
  YR separant Invariant AX)
open BO (Ue bsq Uy bhO)
open agL (BV EY a4B)
open lB (amo)
open scoped BigOperators
def c1 :Prop :=
  ∀ (R G f :af 4) (z :Ideal GeoJets) (hz : (kC R G).IsMinimalPrime z)
      (ell v a :ℕ),Irreducible R→(¬ R∣G)→0<ell→0<genericOrder R z →
    ell≤genericOrder G z→ oA (kC R G) z hz.isPrime=(v :ℕ∞) →
    v<K1.p→YR f z a →
    let g:=(separant^[a]) f
    ¬ Invariant g z →
    ∃ (H :af 4) (d:ℕ),0<d∧min (genericOrder R z) ell*d≤v ∧
      ((∃ u,EY u<genericOrder R z∧H=BV u R) ∨
        (∃ u,EY u<ell∧H=BV u G)) ∧
      bC (Uy g H d)∉z
def c2 :Prop :=
  ∀ (R G f :af 4) (z :Ideal GeoJets) a,
    Irreducible R→(¬ R∣G)→(shape R).b<K1.p →
    (kC R G).IsMinimalPrime z→YR f z a →
    genericOrder R z≤ max 1 (shape R).t
def c3:Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (zs :Finset (Ideal GeoJets)) (v :Ideal GeoJets→ℕ) (F:Ideal GeoJets→af 4),
      let p:=chartBody C R cs
      let r :=firstSlot C R cs
      let q:=cutterBody C ell
      let b:=commonBody C R ell cs
      let cap:=topBound C R cs
      (∀ z∈zs,(∃ hz : (kC R G).IsMinimalPrime z,
          oA (kC R G) z hz.isPrime=(v z :ℕ∞)) ∧
        ell*genericOrder R z≤v z∧PaidCut p b ell cap (genericOrder R z) (v z) z (F z)) →
      ∀ h:Shape,(h=weightedChart bf p∨h=p) →
        (32 :ℤ)*(↑(∑ z∈zs,(ell*genericOrder R z)*an0 h z (F z)) :ℤ) ≤
          6*(wP r q p h+wP r q b h +
            2*(max ell cap:ℕ)*wP r q p h)
def c4 :Prop :=
  ∀ (C:Context) R G ell cs,PairInput C R G ell cs →
    ∀ (Γ:Finset P6.K) (D:Ideal GeoJets),Γ⊆C.Δ →
      (∀ γ∈Γ,0<ord C R γ∧D ≤Ch (extend (C.s γ))) →
      D.IsPrime→ ringKrullDim (GeoJets ⧸ D)=1 →
      6*mV*Γ.card≤ curveCharge (chartBody C R cs) D
private theorem tangent_rate {i ell d cap v :ℕ}
    (htop:i≤ max ell cap) (hd:min i ell*d≤v) :
    ell*i*d≤ max ell cap*v := by
  by_cases he :i≤ell
  · rw [min_eq_left he] at hd
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left ell hd).trans (Nat.mul_le_mul_right v (le_max_left _ _))
  · rw [min_eq_right (Nat.le_of_not_ge he)] at hd
    rw [Nat.mul_comm ell i,Nat.mul_assoc]
    exact (Nat.mul_le_mul_left i hd).trans (Nat.mul_le_mul_right v htop)
private theorem one_cut (h1 :c1) (h2 :c2) {C:Context} {R G ell cs}
    (h:PairInput C R G ell cs) (assigned:SurfaceAssignment C R G)
    (Γ:Finset P6.K)
    (hΓ : ∀ γ∈Γ,γ∈C.Δ∧0<ord C R γ ∧
      ell≤genericOrder G (assigned.aI γ) ∧
      ¬ RegularInvariant C cs (assigned.aI γ) γ∧0<genericOrder R (assigned.aI γ))
    (z :Ideal GeoJets) (hz :z∈Γ.image assigned.aI) :
    ∃ (v :ℕ) (F:af 4),
      (∃ hZ: (kC R G).IsMinimalPrime z,
        oA (kC R G) z hZ.isPrime=(v :ℕ∞)) ∧
      ell*genericOrder R z≤v ∧
      PaidCut (chartBody C R cs) (commonBody C R ell cs) ell (topBound C R cs)
        (genericOrder R z) v z F ∧
      ∀ γ∈Γ,assigned.aI γ=z→cK F (extend (C.s γ))=0:= by
  classical
  obtain ⟨γ₀,hγ₀,heq⟩:=Finset.mem_image.mp hz
  obtain ⟨hin₀,ho₀,hhigh,_,hpos₀⟩:=hΓ γ₀ hγ₀
  obtain ⟨hZ,hm₀⟩:=heq ▸ assigned.valid γ₀ hin₀ ho₀
  have high:ell≤genericOrder G z :=heq ▸ hhigh
  have hpos :0<genericOrder R z :=heq ▸ hpos₀
  have hm (γ) (hγ:γ∈Γ) (he :assigned.aI γ=z) :z≤Ch (extend (C.s γ)) :=
    he ▸ (assigned.valid γ (hΓ γ hγ).1 (hΓ γ hγ).2.1).2
  obtain ⟨v,vb,vlen,vw⟩:=local_weight h.factor.1 h.proper hZ high
  refine ⟨v,?_⟩
  let T:=(chartIndices C cs).filter fun k=>bC (C.f k)∈z
  by_cases hn:T.Nonempty
  · let k :=T.min' hn
    obtain ⟨hk,hfk⟩:=Finset.mem_filter.mp (T.min'_mem hn)
    have hmin (j) (hj:j∈chartIndices C cs) (hjz :bC (C.f j)∈z) :k≤j :=
      T.min'_le j (Finset.mem_filter.mpr ⟨hj,hjz⟩)
    have hsmall:=C.marks.factors k (charter h hk)
    have hon :aR.Dd (C.f k) (extend (C.s γ₀)) :=
      ⟨Ue.mp (hm₀ hfk),C.marks.leading γ₀ hin₀ k (charter h hk)⟩
    obtain ⟨a,ha,hb⟩:=bAm.bmF
      (hsmall.2.2.1.2.2.trans_lt (by decide :16<K1.p)) hon hfk hm₀
    let g:=(separant^[a]) (C.f k)
    have hfbox :=(bW2 h).2 k hk
    have hanchor :aO (shape (C.f k)).iU (chartBody C R cs) := by
      have ch: (chartBody C R cs).j≤(chartBody C R cs).b:= by
        cases cs <;> exact le_max_right _ _
      exact ⟨max_le hfbox.1 (hfbox.2.1.trans ch),hfbox.2⟩
    by_cases hi:Invariant g z
    · refine ⟨separant g,⟨hZ,vlen⟩,vw,⟨ha.2.2,Or.inl (cDD hb hanchor)⟩,?_⟩
      intro γ hγ hzγ
      by_contra hreg
      exact (hΓ γ hγ).2.2.2.1 (hzγ.symm ▸
        ⟨k,hk,hfk,hmin,a,ha,hreg,hi⟩)
    · have hc:=char_fits h
      have hcR:=hc.1.trans_lt (by decide :4025<K1.p)
      have hcv :=(vb.trans (Nat.mul_le_mul hc.1 hc.2)).trans_lt
        (by decide :4025*4025<K1.p)
      obtain ⟨H,d,hd,hdv,hH,hF⟩ :=
        h1 R G (C.f k) z hZ ell v a h.factor.1 h.proper h.positive hpos high vlen hcv ha hi
      let p:=chartBody C R cs
      let b:=commonBody C R ell cs
      have hgbox :=cDD (akM.bc7 (C.f k) a) hanchor
      have ht:0<p.t:=hsmall.2.1.trans_le hfbox.2.2
      have hj:0<p.j :=
        (show 0<(shape (C.f k)).j from
          (Nat.mul_pos (by decide :0<3) hsmall.2.1).trans_le
            (lB.Tn (C.f k)).2).trans_le hfbox.2.1
      have hcap:=h2 R G (C.f k) z a h.factor.1 h.proper hcR hZ ha
      have hmax' : genericOrder R z≤ max ell (topBound C R cs) :=
        hcap.trans (max_le ((Nat.succ_le_iff.mpr h.positive).trans (le_max_left _ _))
          ((top_fits h).trans (le_max_right _ _)))
      have hR:aO (shape R) b:=cDD (first_fits h)
        ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _⟩
      have hG:aO (shape G) b:=cDD h.H6
        ⟨le_max_right _ _,le_max_right _ _,le_max_right _ _⟩
      have hdata :aO (shape H) b ∧ ∀ γ∈Γ,assigned.aI γ=z →
          cK H (extend (C.s γ))=0:= by
        rcases hH with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
        · exact ⟨a4B u hR,fun γ hγ he =>
            Ue.mp (hm γ hγ he (order_mem R z hu))⟩
        · exact ⟨a4B u hG,fun γ hγ he =>
            Ue.mp (hm γ hγ he (order_mem G z (hu.trans_le high)))⟩
      refine ⟨Uy g H d,⟨hZ,vlen⟩,vw,
        ⟨hF,Or.inr ⟨d,hd,tangent_rate hmax' hdv,
          akM.bhQ ht hj hgbox hdata.1 d⟩⟩,?_⟩
      intro γ hγ he
      exact bhO g H _ d
        (Ue.mp (hm γ hγ he (ha.2.1 a le_rfl))) (hdata.2 γ hγ he)
  · have hproper :bC (GW C cs)∉z := by
      intro hprod
      let:=hZ.isPrime
      change MvPolynomial.map dN.j8 (∏ i∈chartIndices C cs,C.f i)∈z at hprod
      rw [map_prod] at hprod
      obtain ⟨k,hk,hz'⟩:=Ideal.IsPrime.prod_mem_iff.mp hprod
      exact hn ⟨k,Finset.mem_filter.mpr ⟨hk,hz'⟩⟩
    exact ⟨GW C cs,⟨hZ,vlen⟩,vw,⟨hproper,Or.inl (bW2 h).1⟩,
      fun γ hγ _=>chart_product_vanishes h (hΓ γ hγ).1 (hΓ γ hγ).2.1⟩
private theorem dRZ (h4 :c4) {C:Context} {R G ell cs}
    (h:PairInput C R G ell cs) (assigned:SurfaceAssignment C R G)
    (Γ:Finset P6.K) (hΓ : ∀ γ∈Γ,γ∈C.Δ∧0<ord C R γ)
    {z :Ideal GeoJets} {F:af 4} (hz : (kC R G).IsMinimalPrime z)
    (hF:bC F∉z) (hv : ∀ γ∈Γ,assigned.aI γ=z→cK F (extend (C.s γ))=0) :
    let p:=chartBody C R cs
    6*mV*(Γ.filter fun γ=>assigned.aI γ=z).card ≤
      P6.t*an0 (weightedChart bf p) z F+2*mV*an0 p z F:= by
  classical
  intro p
  let M:=Γ.filter fun γ=>assigned.aI γ=z
  let Ds :=(AX z F).minimalPrimesFinset
  let marks (D:Ideal GeoJets) :=M.filter fun γ=>D ≤Ch (extend (C.s γ))
  have hcover :M⊆Ds.biUnion marks := by
    intro γ hγ
    obtain ⟨hγ,he⟩:=Finset.mem_filter.mp hγ
    have hm:=he ▸ (assigned.valid γ (hΓ γ hγ).1 (hΓ γ hγ).2).2
    obtain ⟨D,hD,hM⟩:=bsq hm (hv γ hγ he)
    exact Finset.mem_biUnion.mpr ⟨D,Ideal.mem_minimalPrimesFinset.mpr hD,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hγ,he⟩,hM⟩⟩
  have hdim:=GJ.bf6 (agr h.factor.1.ne_zero)
    (amo R G h.factor.1 h.proper) hz
  have hR:bC R∈z :=hz.le (Ideal.subset_span (by simp))
  have hcount (D) (hD:D∈Ds) :6*mV*(marks D).card≤ curveCharge p D:= by
    have hd:=GJ.bZi hz.isPrime hdim hR hF
      (Ideal.mem_minimalPrimesFinset.mp hD)
    have inside (γ) (hγ:γ∈marks D) :γ∈Γ∧D ≤Ch (extend (C.s γ)) := by
      obtain ⟨hγ,hv⟩:=Finset.mem_filter.mp hγ
      exact ⟨(Finset.mem_filter.mp hγ).1,hv⟩
    exact h4 C R G ell cs h _ D (fun γ hγ=>(hΓ γ (inside γ hγ).1).1)
      (fun γ hγ=>⟨(hΓ γ (inside γ hγ).1).2,(inside γ hγ).2⟩) hd.prime hd.dim
  calc
    _≤6*mV * ∑ D∈Ds,(marks D).card :=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcover).trans Finset.card_biUnion_le)
    _ = ∑ D∈Ds,6*mV*(marks D).card:=Finset.mul_sum ..
    _ ≤ ∑ D∈Ds,curveCharge p D:=Finset.sum_le_sum hcount
    _ = _:= by rw [an0,an0,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]; rfl
private theorem combine {e g N U V:ℕ} {A B:ℤ}
    (hn:6*g*N≤e*U + 2*g*V)
    (hu: (32 :ℤ)*U≤6*A) (hv : (32 :ℤ)*V≤6*B) :
    (32 :ℤ)*g*N≤e*A+2*g*B:= by
  have hn' : (6:ℤ)*g*N≤e*U + 2*g*V:= by exact_mod_cast hn
  have h:=mul_le_mul_of_nonneg_left hn' (show (0:ℤ)≤32 by decide)
  have hu' := mul_le_mul_of_nonneg_left hu (show 0≤(e :ℤ) by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0≤2*(g:ℤ) by positivity)
  nlinarith only [h,hu',hv']
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :P6_6_7.c3:= by
  classical
  intro C R G ell cs h assn p r q a
  let Γ:=C.Δ.filter fun γ=>0<ord C R γ ∧
    ell≤genericOrder G (assn.aI γ) ∧ ¬ RegularInvariant C cs (assn.aI γ) γ ∧
      0<genericOrder R (assn.aI γ)
  let zs :=Γ.image assn.aI
  have hΓ (γ) (hγ:γ∈Γ) :=Finset.mem_filter.mp hγ
  have hex (z :Ideal GeoJets) :
      ∃ (v :ℕ) (F:af 4),z∈zs →
        (∃ hZ: (kC R G).IsMinimalPrime z,
          oA (kC R G) z hZ.isPrime=(v :ℕ∞)) ∧
        ell*genericOrder R z≤v ∧
        PaidCut p (commonBody C R ell cs) ell (topBound C R cs) (genericOrder R z) v z F ∧
        ∀ γ∈Γ,assn.aI γ=z→cK F (extend (C.s γ))=0:= by
    by_cases hz :z∈zs
    · obtain ⟨v,F,hv⟩:=one_cut h1 h2 h assn Γ hΓ z hz
      exact ⟨v,F,fun _=>hv⟩
    · exact ⟨0,0,fun hh=>(hz hh).elim⟩
  choose v F hf using hex
  let i:=genericOrder R
  let u:=weightedChart bf p
  let N :=highAux C R G ell cs assn
  have hN :N = ∑ z∈zs,(Γ.filter fun γ=>assn.aI γ=z).card*i z := by
    have heq :N = ∑ γ∈Γ,i (assn.aI γ) := by
      unfold N highAux
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      by_cases ho:0<ord C R γ
      · by_cases hi:0<genericOrder R (assn.aI γ)
        · simp [surfaceOrder,ho,i,hi]
        · have hz :=Nat.eq_zero_of_not_pos hi
          simp [surfaceOrder,ho,hz,i]
      · simp [surfaceOrder,ho]
    rw [heq,← Finset.sum_fiberwise_of_maps_to' (fun γ hγ=>Finset.mem_image_of_mem assn.aI hγ)]
    simp [zs]
  let sumDegree (b:Shape) := ∑ z∈zs,(ell*i z)*an0 b z (F z)
  have hsum:6*mV*(ell*N)≤P6.t*sumDegree u+2*mV*sumDegree p:= by
    rw [hN]
    simp only [sumDegree,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    obtain ⟨⟨hZ,_⟩,_,hcut,hvan⟩:=hf z hz
    have hb:=dRZ h4 h assn Γ (fun γ hγ=>⟨(hΓ γ hγ).1,(hΓ γ hγ).2.1⟩)
      hZ hcut.1 hvan
    calc
      _=(ell*i z)*(6*mV*(Γ.filter fun γ=>assn.aI γ=z).card) := by ac_rfl
      _≤(ell*i z)*(P6.t*an0 u z (F z)+2*mV*an0 p z (F z)) :=
        Nat.mul_le_mul_left _ hb
      _ = _:= by ring
  have hg:=h3 C R G ell cs h zs v F fun z hz =>
    ⟨(hf z hz).1,(hf z hz).2.1,(hf z hz).2.2.1⟩
  have hprice :=combine hsum (hg u (Or.inl rfl)) (hg p (Or.inr rfl))
  simp only [Nat.cast_mul] at hprice
  change (feeScale :ℤ)*ell*N≤a+curve32 p r q (commonBody C R ell cs) +
      2*(max ell (topBound C R cs) :ℕ)*a
  simp only [a,curve32,feeScale,Nat.cast_mul,Nat.cast_ofNat]
  dsimp only [p,r,q,u] at hprice ⊢
  convert hprice using 1 <;> ring
end
end P6_6_7_3
