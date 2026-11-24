import ProximityPrize.SubmissionLower.ZcOMvde
set_option Elab.async false
section
set_option autoImplicit true
namespace qje58fc
noncomputable section
open Finset Polynomial
open scoped Polynomial BigOperators
open P5_7_2 (fO row topDonors)
open q7IA62d (Aw cutoff profile btN eMG mem_ambient capColumns
 oneNumerator oneDenominator a6h oneNumerator_small oneNumerator_congruence)
open cu (L)
open DP (jF zG)
open jA (jK kS jH)
open NR (TT O8 Lq)
open aFO (bu4 bu5)
open private bCP cFT from ProximityPrize.SubmissionLower.DG
open private cxQ.aQ3 b8G from ProximityPrize.SubmissionLower.A2
def c1 :Prop :=
  ∀ (b:fO) (e :Bool) (α a d c:L),a≠0→d≠0 →
    let t:=profile b e
    ∀ V:Submodule L jK,Module.Finite L V →
      (∀ F∈V,∀ m∈F.support,capColumns t m) →
      TT V (testSpace (Polynomial.X-C α) (C (seedValue a d c))
        (O8 α) (t.shape.B+t.shape.J))≤(modelMatrix t).rank
def c2 :Prop :=
  ∀ (b:fO) (e :Bool),
    let t:=profile b e
    t.shape.B≤t.shape.U→(modelMatrix t).rank≤windowDebit t
def c3:Prop :=
 ∀ (b:fO) (e :Bool),windowDebit (profile b e)≤eMG 1 (profile b e)
private theorem separable_cost (h1 :c1) (b:fO) (e :Bool)
   {H q A B:L[X]} {R:kS[X]} (hm:H.Monic) (hs :H.Separable)
   (hA:IsCoprime A H) (hq:IsCoprime q H)
   (hc:jH H∣bu4 1 A B*R+bu5 q)
   (V:Submodule L jK) [hv :Module.Finite L V]
   (hcap : ∀ F∈V,∀ m∈F.support,capColumns (profile b e) m) :
   let n:=(profile b e).shape.B+(profile b e).shape.J
   TT V (testSpace H R (jH H) n)≤H.natDegree*(modelMatrix (profile b e)).rank := by
 classical
 let n:=(profile b e).shape.B+(profile b e).shape.J
 change TT V (testSpace H R (jH H) n)≤_
 let T:Finset L:=⟨H.roots,nodup_roots hs⟩
 let W:L→Submodule L jK:= fun α=>testSpace H R (O8 α) n
 have hcard:T.card=H.natDegree :=IsAlgClosed.card_roots_eq_natDegree
 have hprod: (∏ α∈T,O8 α)=jH H := by
   have he : (∏ α∈T,(Polynomial.X - C α))=H :=
     ((IsAlgClosed.splits H).eq_prod_roots_of_monic hm).symm
   change _=Polynomial.mapRingHom (algebraMap L kS) H
   rw [← he,map_prod]
   simp [O8]
 have hlocal (α:L) (hα:α∈T) :
     TT V (W α)≤(modelMatrix (profile b e)).rank := by
   have hr :H.IsRoot α:=(mem_roots hm.ne_zero).mp hα
   have hd:=hs.eval₂_derivative_ne_zero (RingHom.id L) hr
   change TT V (testSpace H R (O8 α) n)≤_
   rw [normalize hr hd hA hc]
   exact h1 b e α _ _ _ (neg_ne_zero.mpr (coprime_at_root hq hr))
     (coprime_at_root hA hr) V hv hcap
 have hsub:T.inf W≤testSpace H R (jH H) n:= by
   intro F hF
   have hcop:=Polynomial.pairwise_coprime_X_sub_C
     (FaithfulSMul.algebraMap_injective L kS)
   have hh:=Finset.prod_dvd_of_coprime (t:=T)
     (s := fun α=>(MvPolynomial.C (O8 α) :Lq)^n)
     (fun α _ β _ hne=>(IsCoprime.map (f :=MvPolynomial.C) (hcop hne)).pow)
     (fun α hα=>mem_testSpace.mp ((Finset.inf_le hα:T.inf W≤W α) hF))
   rw [Finset.prod_pow,← map_prod MvPolynomial.C,hprod] at hh
   exact mem_testSpace.mpr hh
 have hsum:=bCP V T W _ hlocal
 rw [hcard] at hsum
 exact (cFT V hsub).trans hsum
private theorem congruence {h:ℕ} {D:jF h} (Crt:zG D) :
    jH (D.block 0)∣bu4 1 (D.constant 0) (D.slope 0)*a6h Crt +
      bu5 (D.offset 0) := by
  let f :=algebraMap L[X] kS
  have hd:f (oneDenominator Crt)≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective L[X] kS)).mpr
      (Crt.denominator_ne_zero 0)
  have hg:=Polynomial.map_dvd f (oneNumerator_congruence Crt)
  simp only [f,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,b8G] at hg
  rw [map_mul (algebraMap L[X] kS) (oneDenominator Crt) Polynomial.X] at hg
  have hOne :jH (1 :L[X])=1 :=Polynomial.map_one _
  have hg' : jH (D.block 0) ∣
      bu4 1 (D.constant 0) (D.slope 0)*(oneNumerator Crt).map f +
        C (f (oneDenominator Crt))*bu5 (D.offset 0) := by
    simpa only [f,bu4,bu5,hOne,one_mul,
      ← mul_assoc,← Polynomial.C_mul] using hg
  exact cxQ.aQ3 hd hg'
private theorem profile_width (b:fO) (e :Bool) :
  (profile b e).shape.B≤(profile b e).shape.U:= by
 by_cases hb:b.val<7 <;> cases e <;> simp [profile,topDonors,hb]
private theorem band_height (b:fO) : (row b).declaredHi<K1.p:= by
 fin_cases b <;> decide
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q7IA62d.c3:= by
  classical
  intro b e h hp hh D Crt
  let t:=profile b e
  let V:=Aw h t (cutoff t)
  change TT V (btN Crt t)≤eMG h t
  by_cases hV:Module.Finite L V
  · let:Module.Finite L V:=hV
    have hcap (F:jK) (hF:F∈V) (a :jA.mA →₀ ℕ)
        (ha :a∈F.support) :capColumns t a := by
      have hf :=mem_ambient.mp hF
      exact ⟨(MvPolynomial.le_weightedTotalDegree _ ha).trans hf.1,
        (MvPolynomial.le_weightedTotalDegree _ ha).trans hf.2.1,
        (MvPolynomial.monomial_le_degreeOf _ ha).trans hf.2.2.1,
        (MvPolynomial.monomial_le_degreeOf _ ha).trans hf.2.2.2.1⟩
    have hdet:=D.determinant 0
    have hdeg:=D.degree 0
    have hR: (a6h Crt).natDegree<(D.block 0).natDegree := by
      rw [hdeg]
      exact ((natDegree_C_mul_le _ _).trans natDegree_map_le).trans_lt (oneNumerator_small Crt hp)
    have hd: (D.block 0).natDegree<K1.p:= by rw [hdeg]; exact hh.trans_lt (band_height b)
    have hbound:=deform V (D.monic 0) (by rwa [hdeg]) hd hdet.of_mul_left_right
      hdet.of_mul_left_left hR (congruence Crt)
      (r :=h*(modelMatrix t).rank) (n:=t.shape.B+t.shape.J) (by
        intro H R hm hs he hA hq hc
        have hr :=separable_cost h1 b e hm hs hA hq hc V hcap
        rw [he,hdeg] at hr
        exact hr)
    have hrank :=(h2 b e (profile_width b e)).trans (h3 b e)
    refine hbound.trans ?_
    simpa only [eMG,one_mul] using Nat.mul_le_mul_left h hrank
  · let:Module.Free L ↥V:=Module.Free.of_divisionRing (K:=L) (V := ↥V)
    simp [TT,Module.finrank_of_not_finite hV]
end
end qje58fc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qAzyIze
noncomputable section
open Polynomial Finset q7IA62d
open P5_7_2 (TopRow)
open q7F2qKe (weakAgreement)

open DP (jF zG)
open jA (jK ko iP ahb bC jH)
open private multiples mem_multiples from ProximityPrize.SubmissionLower.S
def c1 :Prop :=
  ∀ (h:ℕ),0<h → ∀ (D:jF h) (Crt:zG D) (T:ℕ) (P:jK),
    ahb h T P → ∀ a∈(forward Crt P).support,
      ((forward Crt P).coeff a).natDegree+aWN a≤T
def c2 :Prop :=
  ∀ (h:ℕ) (D:jF h) (Crt:zG D)
    (s :Set jK) (A:RawExp→Prop),
    (∀ P∈s,∀ a∈(forward Crt P).support,A a) →
    ∀ Q∈Submodule.span iP (bC '' s),Q≠0 →
      ∃ a∈Q.support,a (some 2)= Q.degreeOf (some 2)∧A (jetExp a)
private theorem raw_width (h1 :c1) {h} (hh:0<h) {D:jF h}
  (Crt:zG D) {t T P} (hP:ahb h T P) (hp:P∈btN Crt t)
  {a :RawExp} (ha :a∈(forward Crt P).support) :
  aWN a+clearance h t≤T:= by
 have hdeg:=h1 h hh D Crt T P hP a ha
 obtain ⟨Q,hQ⟩:=mem_poleSpace.mp hp
 let H :=jH (D.block 0)
 have hm:H.Monic:=(D.monic 0).map _
 have hd:H.natDegree=h:=(natDegree_map _).trans (D.degree 0)
 have he : (forward Crt P).coeff a=H^(t.shape.B+t.shape.J)*Q.coeff a := by
  rw [hQ,← map_pow,MvPolynomial.coeff_C_mul]
 have hn:Q.coeff a≠0:= fun hz=>MvPolynomial.mem_support_iff.mp ha
  (by rw [he,hz,mul_zero])
 rw [he,natDegree_mul (pow_ne_zero _ hm.ne_zero) hn,natDegree_pow,hd] at hdeg
 unfold clearance
 omega
private theorem Ly (h1 :c1) (h2 :c2) {h} (hh:0<h) {D:jF h}
   (Crt:zG D) word t (P:jK) (hP:P∈source Crt word t 0)
   (hs : ∀ a∈P.support,(P.coeff a).natDegree+kO h a<clearance h t) :
   P=0:= by
 classical
 by_contra hn
 obtain ⟨a,ha⟩:=Finset.nonempty_iff_ne_empty.mpr
   (fun he=>hn (MvPolynomial.support_eq_empty.mp he))
 have hp:=hs a ha
 have hT:ahb h (clearance h t - 1) P:= fun a ha=> by
   have hl:=hs a ha
   change _+kO h a≤_
   omega
 let A:RawExp→Prop := fun a=>aWN a+clearance h t≤ clearance h t - 1
 have hA (R:jK) (hR:R∈({P} : Set jK)) :
     ∀ a∈(forward Crt R).support,A a := by
   obtain rfl :=Set.mem_singleton_iff.mp hR
   exact fun a ha=>raw_width h1 hh Crt hT hP.2.2 ha
 have hmem:bC P∈Submodule.span iP (bC '' ({P} : Set jK)) :=
   Submodule.subset_span ⟨P,Set.mem_singleton P,rfl⟩
 obtain ⟨a,_,_,hfalse⟩:=h2 h D Crt {P} A hA _ hmem (acZ.agr hn)
 dsimp [A] at hfalse
 omega
private def eligible (h N W q c j:ℕ) :Prop :=
 131071*q≤W+j+2*c∧N≤W+3*h*c
private instance (h N W q c j:ℕ) :Decidable (eligible h N W q c j) := by
 unfold eligible
 infer_instance
private def positions (t:TopRow) (h N W:ℕ) :Finset (Σ _:ℕ,Σ _:ℕ,ℕ) :=
 ((range (t.shape.B+1)).sigma fun q =>
   (range (min q (min t.YM (t.shape.J/2))+1)).sigma fun c =>
     range (min (q-c) (t.shape.J-2*c)+1)).filter
   (fun x=>eligible h N W x.1 x.2.1 x.2.2)
private theorem card_positions (t:TopRow) (h N W:ℕ) :
  (positions t h N W).card=ama t (fun q c j=>if eligible h N W q c j then 1 else 0) := by
 unfold positions ama
 simp only [card_filter,sum_sigma]
private def column (q c j u:ℕ) :Exp :=
 Finsupp.equivFunOnFinite.symm (fun i=>i.elim u ![q-c-j,j,c])
private theorem euV (h1 :c1) (h2 :c2) {h} (hh:0<h) {D:jF h}
    (Crt:zG D) word t {W} (hw:W≤ cutoff t) {f :ko}
    (hf :0<f.degreeOf (some 2))
    (hdiv : ∀ P∈source Crt word t W,f^(1+(cutoff t-W)/(3*h))∣bC P) :
    Module.finrank iP (genericSpan (source Crt word t W)) ≤
      (t.shape.U+1)*ama t (fun q c j=>if eligible h (cutoff t+1) W q c j then 1 else 0) := by
  classical
  let V:=source Crt word t W
  let G:=genericSpan V
  let S:=positions t h (cutoff t+1) W
  let U:=S×Fin (t.shape.U+1)
  let proj:G →ₗ[iP] (U→iP) :=LinearMap.pi fun x =>
    (MvPolynomial.lcoeff iP (column x.1.val.1 x.1.val.2.1 x.1.val.2.2 x.2.val)).comp G.subtype
  have hinj:Function.Injective proj:= by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro P hz
    apply Subtype.ext
    by_contra hn
    change P.val≠(0:ko) at hn
    let A:RawExp→Prop := fun a=>aWN a≤W
    have hA (R:jK) (hR:R∈V) (a :RawExp) (ha :a∈(forward Crt R).support) :
        A a := by
      have hr :=raw_width h1 hh Crt (mem_ambient.mp hR.1).2.2.2.2 hR.2.2 ha
      change aWN a≤W
      omega
    obtain ⟨a,ha,ht,hraw⟩:=h2 h D Crt _ A hA P.val P.property hn
    have hc:capColumns t a := by
      by_contra hbad
      have hz :G≤LinearMap.ker (MvPolynomial.lcoeff iP a) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨R,hR,rfl⟩
        apply LinearMap.mem_ker.mpr
        change (MvPolynomial.map jA.qV R).coeff a=0
        rw [MvPolynomial.coeff_map,← map_zero jA.qV]
        apply congrArg jA.qV
        apply MvPolynomial.notMem_support_iff.mp
        intro hmem
        exact hbad (column_caps hR.1 hmem)
      exact MvPolynomial.mem_support_iff.mp ha (LinearMap.mem_ker.mp (hz P.property))
    let k :=1+(cutoff t-W)/(3*h)
    have hmult:G≤ multiples (f^k) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨R,hR,rfl⟩
      exact mem_multiples.mpr (hdiv R hR)
    obtain ⟨g,hg⟩:=mem_multiples.mp (hmult P.property)
    have hf0:f≠0:= by rintro rfl; simp at hf
    have hg0:g≠0:= fun h=>hn (by rw [hg,h,mul_zero])
    have htop:=ht
    rw [hg,MvPolynomial.degreeOf_mul_eq (pow_ne_zero _ hf0) hg0,
      MvPolynomial.degreeOf_pow_eq _ _ _ hf0] at htop
    let q:=a (some 0)+a (some 1)+a (some 2)
    let c:=a (some 2)
    let j:=a (some 1)
    let u:=a none
    obtain ⟨hB,hJ,hC,hU⟩:=hc
    rw [jet_total] at hB
    rw [jet_index] at hJ
    have hk :k≤ c:= by
      have hl:=Nat.mul_le_mul_left k hf
      change c= _ at htop
      omega
    have hlt: (cutoff t-W)/(3*h)<c:= by
      change 1+(cutoff t-W)/(3*h)≤ c at hk
      omega
    have hd:=(Nat.div_lt_iff_lt_mul (by omega :0<3*h)).mp hlt
    rw [Nat.mul_comm c] at hd
    have hel:eligible h (cutoff t+1) W q c j:= by
      refine ⟨?_,by omega⟩
      have he :=raw_weight a
      change aWN (jetExp a)≤W at hraw
      dsimp [q,c,j]
      omega
    have hpos : (⟨q,⟨c,j⟩⟩:Σ _:ℕ,Σ _:ℕ,ℕ)∈S:= by
      simp only [S,positions,mem_filter,mem_sigma,mem_range_succ_iff,hel,and_true,le_min_iff]
      dsimp [q,c,j]
      omega
    have he :column q c j u=a := by
      ext i
      change i.elim u ![q-c-j,j,c]=a i
      cases i with
      | none=>rfl
      | some i =>
        fin_cases i
        · change q-c-j=a (some 0)
          dsimp [q,c,j]
          omega
        · rfl
        · rfl
    let x :U:=⟨⟨_,hpos⟩,⟨u,Nat.lt_succ_of_le hU⟩⟩
    have hz' := congrFun hz x
    change P.val.coeff (column q c j u)=0 at hz'
    exact MvPolynomial.mem_support_iff.mp ha (he ▸ hz')
  calc
    _≤Module.finrank iP (U→iP) :=LinearMap.finrank_le_finrank_of_injective hinj
    _ = _:= by
      rw [Module.finrank_fintype_fun_eq_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,
        Nat.mul_comm,card_positions]
private theorem bKE (h N q c j:ℕ) (hj:j+2*c≤131071*q) :
   (∑ W∈range N,if eligible h N W q c j then 1 else 0) =
     min (N+j+2*c-131071*q) (3*h*c) := by
 rw [← card_filter]
 have he : (range N).filter (fun W=>eligible h N W q c j) =
     Ico (max (131071*q-(j+2*c)) (N-3*h*c)) N := by
   ext W
   simp only [mem_filter,mem_range,eligible,mem_Ico,max_le_iff]
   omega
 rw [he,Nat.card_Ico]
 omega
private theorem counts (t:TopRow) (h d N :ℕ) (hd:h≤d)
   (hN :N=t.shape.m*weakAgreement) :
   (∑ W∈range N,(t.shape.U+1)*ama t
     (fun q c j=>if eligible h N W q c j then 1 else 0))≤layerCeiling d t:= by
 have hswap :
     (∑ W∈range N,ama t (fun q c j=>if eligible h N W q c j then 1 else 0)) =
     ama t (fun q c j => ∑ W∈range N,if eligible h N W q c j then 1 else 0) := by
   unfold ama
   rw [sum_comm]
   apply sum_congr rfl
   intro q _
   rw [sum_comm]
   apply sum_congr rfl
   intro c _
   rw [sum_comm]
 rw [← mul_sum,hswap]
 apply Nat.mul_le_mul_left
 unfold ama
 apply sum_le_sum
 intro q _
 apply sum_le_sum
 intro c hc
 apply sum_le_sum
 intro j hj
 have hcq:=(mem_range_succ_iff.mp hc).trans (min_le_left _ _)
 have hjq:=(mem_range_succ_iff.mp hj).trans (min_le_left _ _)
 change (∑ W∈range N,if eligible h N W q c j then 1 else 0) ≤
   min (width t q c j) (3*d*c)
 rw [bKE h N q c j (by omega),hN]
 exact min_le_min (by rfl) (Nat.mul_le_mul_right c (Nat.mul_le_mul_left 3 hd))
theorem of_children (h1 :c1) (h2 :c2) :q7IA62d.c6:= by
 intro b h hh hd D _ Crt word f hf
 let t:=profile b true
 change (∀ W≤ cutoff t,∀ P∈source Crt word t W,
     f^(1+(cutoff t-W)/(3*h))∣bC P)→_
 intro hdiv
 have hm:0<t.shape.m:= by
   change 0<(profile b true).shape.m
   by_cases hb:b.val<7 <;> simp [profile,P5_7_2.topDonors,hb]
 have hN :cutoff t+1=t.shape.m*weakAgreement :=
   Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.mul_pos hm (by decide)))
 calc
   _ ≤ ∑ W∈range (cutoff t+1),Module.finrank iP (genericSpan (source Crt word t W)) :=
     telescope Crt word t (cutoff t) (Ly h1 h2 hh Crt word t)
   _ ≤ ∑ W∈range (cutoff t+1),(t.shape.U+1)*ama t
         (fun q c j=>if eligible h (cutoff t+1) W q c j then 1 else 0) := by
     apply sum_le_sum
     intro W hW
     have hw:W≤ cutoff t:=mem_range_succ_iff.mp hW
     exact euV h1 h2 hh Crt word t hw hf (hdiv W hw)
   _≤_:=counts t h _ _ hd hN
end
end qAzyIze
end
