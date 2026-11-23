import ProximityPrize.SubmissionLower.Z3gZttb
import ProximityPrize.SubmissionLower.ZiWgK3c
import ProximityPrize.SubmissionLower.ZIrsLvc
set_option Elab.async false
open _root_ renaming Finsupp.single → zhf, Function.iterate_fixed → zeB, Ideal → znc, Ideal.Quotient.eq_zero_iff_mem → z1Q, Ideal.Quotient.mk → zVv, Ideal.mul_mem_left → zBG, Nat.le_of_lt_succ → zeh, Nat.lt_succ_self → zTO, Polynomial.coeff_X_pow_mul' → zT3, Polynomial.coeff_mul → zMz, Set.image_insert_eq → z6c, Set.image_singleton → zyk
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem xL6fd0:total 2620 4=0xbfaf34a90a0:=r! 0x3005de57880,r! 0x2ff47dfdff0,r! 0x2fe31930c10,r! 0x2fd1bf22c20,rfl
private theorem xL6fd1:total 2624 4=0xbe998d3f620:=r! 0x2fc0614b840,r! 0x2faf0d0dd30,r! 0x2f9db5bfbd0,r! 0x2f8c69264e0,rfl
private theorem xL6fd2:total 2628 4=0xbd84b23fb30:=r! 0x2f7b1711000,r! 0x2f69d0c8940,r! 0x2f588528160,r! 0x2f47453e090,rfl
private theorem r1:total 2620 12=0x23bcd74281f0:=total_append xL6fd0 (total_append xL6fd1 xL6fd2)
private theorem xL6fd3:total 2632 4=0xbc70a64cb80:=r! 0x2f3600d2730,r! 0x2f24c694030,r! 0x2f1388adcc0,r! 0x2f025638760,rfl
private theorem xL6fd4:total 2636 4=0xbb5d66e3780:=r! 0x2ef11d69860,r! 0x2edff141040,r! 0x2ecebf09070,r! 0x2ebd992fe70,rfl
private theorem xL6fd5:total 2640 4=0xba4af03a3f0:=r! 0x2eac6e3d490,r! 0x2e9b4dfb5f0,r! 0x2e8a2998a00,r! 0x2e790a68f70,rfl
private theorem r2:total 2632 12=0x23218fd6a6f0:=total_append xL6fd3 (total_append xL6fd4 xL6fd5)
private theorem xL6fd6:total 2644 4=0xb93946afbf0:=r! 0x2e67f1e0040,r! 0x2e56d906b90,r! 0x2e45c709c10,r! 0x2e34b4bf410,rfl
private theorem xL6fd7:total 2648 4=0xb82873f4680:=r! 0x2e23aa2a9a0,r! 0x2e129d6c700,r! 0x2e0198f7b50,r! 0x2df09365a90,rfl
private theorem xL6fd8:total 2652 3=0x896bc9bb670:=r! 0x2ddf94dde90,r! 0x2dce95dde70,r! 0x2dbd9eff970,rfl
private theorem r3:total 2644 11=0x1facd845f8e0:=total_append xL6fd6 (total_append xL6fd7 xL6fd8)
theorem acE :total 2620 35=0x668b3f5f21c0 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
section
set_option autoImplicit true
namespace qOuMLEd
noncomputable section
open aR (af ao)
open dN (GeoJets bC j8 separant u6 Invariant)
open BO (Uy)
open agL (BV)
open private delta aT8 cVI epp from ProximityPrize.SubmissionLower.H
open private translate translate_coeff hasse_one from ProximityPrize.SubmissionLower.ZiWgK3c
open private hasse_zero from ProximityPrize.SubmissionLower.ZX4kd1a
open scoped Polynomial
private abbrev residue (z :znc GeoJets) :af 4 →+* GeoJets ⧸ z :=
  (zVv z).comp (MvPolynomial.map j8)
private theorem residue_eq_zero {z :znc GeoJets} {P:af 4} :
    residue z P=0↔bC P∈z :=
  z1Q
private def a80 (g:af 4) (z :znc GeoJets) (n:ℕ) :znc (af 4) where
  carrier := {P | ∀ k<n,residue z (Uy g P k)=0}
  zero_mem' := by
    intro k _
    change residue z (((delta g)^[k]) 0)=0
    rw [zeB (map_zero (delta g)),map_zero]
  add_mem' := by
    intro P Q hP hQ k hk
    change residue z (((delta g)^[k]) (P+Q))=0
    rw [iterate_map_add,map_add]
    exact (congrArg₂ (· + ·) (hP k hk) (hQ k hk)).trans (add_zero 0)
  smul_mem' := by
    intro P Q hQ k hk
    change residue z (((delta g)^[k]) (P*Q))=0
    rw [cVI _ _ (aT8 g) _ _ _ (fun j hj=>hQ j (hj.trans hk))]
    exact (congrArg ((residue z) P * ·) (hQ k hk)).trans (mul_zero _)
private theorem tangent_anti (g:af 4) (z :znc GeoJets) :
    Antitone (a80 g z) :=
  fun _ _ h _ hP k hk=>hP k (hk.trans_le h)
private theorem tangent_chart (g:af 4) (z :znc GeoJets)
    (hg:bC g∈z) (d:ℕ) :g∈a80 g z d:= by
  intro k _
  change residue z (((delta g)^[k]) g)=0
  cases k with
  | zero=>exact residue_eq_zero.mpr hg
  | succ k =>
    have hDg:delta g g=0:= by
      change u6 g g=0
      rw [u6,mul_comm (separant g),sub_self]
    rw [Function.iterate_succ_apply,hDg,zeB (map_zero (delta g)),map_zero]
abbrev topTaylor :af 4 →+* (af 4)[X] :=translate 3
theorem topTaylor_coeff (P:af 4) (a :ℕ) :
    (topTaylor P).coeff a=BV (zhf 3 a) P :=
  translate_coeff 3 P a
private theorem topTaylor_zero (P:af 4) : (topTaylor P).coeff 0=P:= by
  rw [topTaylor_coeff,Finsupp.single_zero,hasse_zero]
private theorem topTaylor_one (P:af 4) : (topTaylor P).coeff 1=separant P :=
  (topTaylor_coeff P 1).trans (hasse_one 3 P)
def front (g:af 4) (z :znc GeoJets) (d a b:ℕ) :znc (af 4) where
  carrier := {P | (∀ k<a,(topTaylor P).coeff k∈a80 g z d) ∧
    (topTaylor P).coeff a∈a80 g z (min b d)}
  zero_mem' := by simp only [map_zero,Polynomial.coeff_zero,Set.mem_ofPred_eq,Ideal.zero_mem,
    implies_true,and_self]
  add_mem' := by
    intro P Q hP hQ
    refine ⟨fun k hk => ?_,?_⟩ <;> rw [map_add,Polynomial.coeff_add]
    · exact (a80 g z d).add_mem (hP.1 k hk) (hQ.1 k hk)
    · exact (a80 g z (min b d)).add_mem hP.2 hQ.2
  smul_mem' := by
    intro P Q hQ
    refine ⟨fun k hk => ?_,?_⟩ <;> change (topTaylor (P*Q)).coeff _∈_
    · rw [map_mul,zMz]
      refine Ideal.sum_mem _ fun ij hij=>zBG _ _ (hQ.1 _ ?_)
      have he :=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      omega
    · rw [map_mul,zMz]
      refine Ideal.sum_mem _ fun ij hij=>zBG _ _ ?_
      have he :=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases h:ij.2<a
      · exact tangent_anti g z (min_le_right _ _) (hQ.1 _ h)
      · rw [show ij.2=a by omega]
        exact hQ.2
private theorem front_raw {g:af 4} {z :znc GeoJets} {d a b:ℕ} {P:af 4} :
    P∈front g z d a b ↔
      (∀ k<a,(topTaylor P).coeff k∈a80 g z d) ∧
        (topTaylor P).coeff a∈a80 g z (min b d) :=
  Iff.rfl
private theorem gAs {g:af 4} {z :znc GeoJets} {n:ℕ} {P:af 4} :
    P∈a80 g z n ↔ ∀ k<n,residue z (Uy g P k)=0 :=
  Iff.rfl
theorem front_mem {g:af 4} {z :znc GeoJets} {d a b:ℕ} {P:af 4} :
    P∈front g z d a b ↔
      (∀ k<a,∀ j<d,bC (Uy g ((topTaylor P).coeff k) j)∈z) ∧
        (∀ j< min b d,bC (Uy g ((topTaylor P).coeff a) j)∈z) := by
  simp only [front_raw,gAs,residue_eq_zero]
theorem front_step_le (g:af 4) (z :znc GeoJets) (d a b:ℕ) :
    front g z d a (b+1)≤front g z d a b :=
  fun _ h=>front_raw.mpr ⟨(front_raw.mp h).1,
    tangent_anti g z (min_le_min_right d (Nat.le_succ b)) (front_raw.mp h).2⟩
theorem front_next (g:af 4) (z :znc GeoJets) (d a :ℕ) :
    front g z d (a+1) 0=front g z d a d:= by
  ext P
  rw [front_mem,front_mem,Nat.zero_min,min_self]
  simp only [Nat.not_lt_zero,false_implies,implies_true,and_true]
  exact ⟨fun h=>⟨fun k hk=>h k (Nat.lt_succ_of_lt hk),h a (zTO _)⟩,
    fun h k hk=>(Nat.lt_or_eq_of_le (zeh hk)).elim (h.1 k) (fun e=>e ▸ h.2)⟩
private theorem coeff_witness (g:af 4) (z :znc GeoJets) {d:ℕ}
    (hg:bC g∈z) (s t:af 4) (a b:ℕ) :
    (∀ k<a,(topTaylor (s*(g^a*t^b))).coeff k∈a80 g z d) ∧
    (topTaylor (s*(g^a*t^b))).coeff a - s*separant g^a*t^b ∈
      a80 g z d:= by
  let I:=a80 g z d
  let π:=zVv I
  let E :=(Polynomial.mapRingHom π).comp topTaylor
  have hc (P:af 4) (k :ℕ) : (E P).coeff k=π ((topTaylor P).coeff k) :=
    Polynomial.coeff_map π k
  obtain ⟨U,hU⟩:=Polynomial.X_dvd_iff.mpr
    (show (E g).coeff 0=0 by rw [hc,topTaylor_zero]; exact
      Ideal.Quotient.eq_zero_iff_mem.mpr (tangent_chart g z hg d))
  have hU0:U.coeff 0=π (separant g) := by
    rw [← topTaylor_one,← hc,hU]
    exact (Polynomial.coeff_X_mul _ 0).symm
  have hE :E (s*(g^a*t^b))=Polynomial.X ^a*(E s*U^a*E t^b) := by
    simp only [map_mul,map_pow,hU]
    rw [(Polynomial.commute_X U).mul_pow]
    simp only [← mul_assoc]
    rw [(Polynomial.commute_X_pow (E s) a).eq]
  constructor
  · intro k hk
    apply (z1Q (I:=I)).mp
    rw [← hc,hE,zT3,ite_eq_right (not_le.mpr hk)]
  · apply (z1Q (I:=I)).mp
    rw [map_sub,sub_eq_zero,← hc,hE,zT3,ite_eq_left le_rfl,
      Nat.sub_self]
    have hp (P: (af 4 ⧸ I)[X]) (i:ℕ) : (P^i).coeff 0=P.coeff 0^i :=
      map_pow Polynomial.constantCoeff P i
    simp only [Polynomial.mul_coeff_zero,hp,hc,topTaylor_zero,hU0,map_mul,map_pow,π]
theorem strict_witness (g:af 4) (z :znc GeoJets) [z.IsPrime]
    (hg:bC g∈z) (hs :bC (separant g)∉z) (hi : ¬ Invariant g z)
    {d a b:ℕ} (hb:b<d) (hp:b<K1.p) :
    ∃ w∈front g z d a b,∀ s :af 4,bC s∉z →
      s*w∉front g z d a (b+1) := by
  classical
  have ht' : ∃ t:af 4,bC t∈z∧bC (u6 g t)∉z := by
    unfold Invariant at hi
    push Not at hi
    exact hi
  obtain ⟨t,ht,hDt⟩:=ht'
  let w:=g^a*t^b
  let ρ:=residue z
  have diag (s :af 4) :
      (∀ k<a,(topTaylor (s*w)).coeff k∈a80 g z d) ∧
      (topTaylor (s*w)).coeff a - s*separant g^a*t^b∈a80 g z d :=
    coeff_witness g z hg s t a b
  have hpow:=epp (delta g) ρ (aT8 g) t (residue_eq_zero.mpr ht) b
  refine ⟨w,?_,fun s hs' hmem => ?_⟩
  · obtain ⟨hlo,heq⟩:=diag 1
    simp only [one_mul] at hlo heq
    refine front_raw.mpr ⟨hlo,?_⟩
    have ht' : separant g^a*t^b∈a80 g z (min b d) :=
      gAs.mpr fun k hk=>hpow.1 k (hk.trans_le (min_le_left _ _)) _
    exact (Submodule.sub_mem_iff_left _ ht').mp (tangent_anti g z (min_le_right _ _) heq)
  · have htop:=hmem.2
    have hdiff :=tangent_anti g z (min_le_right (b+1) d) (diag s).2
    have hw:s*separant g^a*t^b∈a80 g z (min (b+1) d) :=
      (Submodule.sub_mem_iff_right _ htop).mp hdiff
    have hzero :=gAs.mp hw b (lt_min (zTO _) hb)
    change ρ (((delta g)^[b]) ((s*separant g^a)*t^b))=0 at hzero
    rw [hpow.2] at hzero
    let ψ:ao →+* GeoJets ⧸ z :=ρ.comp (MvPolynomial.C.comp Polynomial.C)
    have hf : (b.factorial:GeoJets ⧸ z)≠0:= by
      intro h
      apply lB.ahA hp
      apply ψ.injective
      simpa only [map_natCast,map_zero] using h
    have hnz (P:af 4) (h:bC P∉z) :ρ P≠0 :=
      fun e=>h (residue_eq_zero.mp e)
    have hleft:ρ (s*separant g^a)≠0:= by
      rw [map_mul,map_pow]
      exact mul_ne_zero (hnz _ hs') (pow_ne_zero _ (hnz _ hs))
    exact (mul_ne_zero (mul_ne_zero hleft hf)
      (pow_ne_zero _ (hnz _ hDt))) hzero
end
end qOuMLEd
end
section
set_option autoImplicit true
namespace qOuMLEd
noncomputable section
open aR (af)
open dN (GeoJets bC separant Invariant oA kC)
open BO (Uy)
open agL (BV EY)
open akM (aLR a2V aFg)
open aY1 (Be exx ccg)
open P6_6_7 (genericOrder)
open private A loc exo bCF gBN from ProximityPrize.SubmissionLower.H
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem grid_cost {B:Type*} [CommRing B] (I:ℕ→ℕ→ znc B) (d:ℕ)
    (hnext : ∀ a,I (a+1) 0=I a d)
    (hstep : ∀ a b,b<d→ I a (b+1)<I a b) :
    ∀ a b,b≤d→(↑(a*d+b) :ℕ∞)≤Order.coheight (I a b) := by
  have row (a :ℕ) (h0: (↑(a*d) :ℕ∞)≤Order.coheight (I a 0)) :
      ∀ b≤d,(↑(a*d+b) :ℕ∞)≤Order.coheight (I a b) := by
    intro b
    induction b with
    | zero=>simpa using fun _:0≤d=>h0
    | succ b ih =>
      intro hb
      rw [← Nat.add_assoc,Nat.cast_add,Nat.cast_one]
      exact (add_le_add_left (ih (Nat.le_of_succ_le hb)) 1).trans
        (Order.coheight_add_one_le (hstep a b hb))
  intro a
  induction a with
  | zero=>exact row 0 (by simp)
  | succ a ih =>
    apply row
    rw [hnext,Nat.succ_mul]
    exact ih d le_rfl
private theorem yC {R G g:af 4} {z :znc GeoJets} [hp:z.IsPrime]
    {m d:ℕ} (hg:bC g∈z) (hs :bC (separant g)∉z)
    (hi : ¬ Invariant g z) (hd:d≤K1.p)
    (hR:R∈front g z d m 0) (hG:G∈front g z d m 0) :
    (↑(m*d) :ℕ∞)≤oA (kC R G) z hp:= by
  let I:ℕ→ℕ→ znc (A z) := fun a b=>(front g z d a b).map (loc z)
  have hnext (a :ℕ) :I (a+1) 0=I a d :=
    congrArg (fun J:znc (af 4)=>J.map (loc z)) (front_next g z d a)
  have hstep (a b:ℕ) (hb:b<d) :I a (b+1)<I a b:= by
    refine lt_of_le_not_ge (Ideal.map_mono (front_step_le g z d a b)) ?_
    intro hle
    obtain ⟨w,hw,hnot⟩:=strict_witness g z hg hs hi (a :=a) hb (hb.trans_le hd)
    obtain ⟨s,hs',hsw⟩:=bCF z (hle (Ideal.mem_map_of_mem (loc z) hw))
    exact hnot s hs' hsw
  have hpair :Ideal.span ({R,G} : Set (af 4))≤front g z d m 0:= by
    rw [Ideal.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
    exact ⟨hR,hG⟩
  have hgrid := @grid_cost (A z) inferInstance I d
  have hcost:=hgrid hnext hstep m 0 (Nat.zero_le d)
  dsimp only [I] at hcost
  have hc:=hcost.trans (Order.coheight_anti (Ideal.map_mono (f :=loc z) hpair))
  let J:znc aLR:=Ideal.span {aFg R,aFg G}
  let F:=algebraMap aLR GeoJets
  have hF (P:af 4) :F (aFg P)=bC P:=gBN P
  have hmap :J.map F=kC R G:= by
    simp only [J,Ideal.map_span,z6c,zyk,hF,kC]
  have hf :Module.Flat aLR GeoJets :=ccg
  have hbase :=exx z J
  change Be (a2V z) J≤Be z (J.map F) at hbase
  rw [hmap] at hbase
  apply le_trans ?_ hbase
  change (↑(m*d) :ℕ∞)≤Be (a2V z) J
  simpa only [Be,Module.length_quotient,J,Nat.add_zero,Ideal.map_span,
    z6c,zyk,exo] using hc
theorem proof :P6_6_7_3.c1 := by
  classical
  intro R G f z hz ell v a _ _ he hi hG hlen hv hchart
  dsimp only
  intro hinv
  let:=hz.isPrime
  let g:=(separant^[a]) f
  let m:=min (genericOrder R z) ell
  let d:=v/m+1
  have hm:0< m:=lt_min hi he
  have hd:d≤K1.p:=Nat.succ_le_of_lt ((Nat.div_le_self _ _).trans_lt hv)
  change ¬ Invariant g z at hinv
  by_contra hnone
  have hvanish (P:af 4) (k j:ℕ) (hj:j<d)
      (hpartial:bC (BV (zhf 3 k) P)∈z)
      (hchoice : (∃ u,EY u<genericOrder R z ∧
          BV (zhf 3 k) P=BV u R) ∨
        (∃ u,EY u<ell∧BV (zhf 3 k) P=BV u G)) :
      bC (Uy g ((topTaylor P).coeff k) j)∈z := by
    rw [topTaylor_coeff]
    cases j with
    | zero=>exact hpartial
    | succ j =>
      by_contra hproper
      apply hnone
      have hpay :=(Nat.le_div_iff_mul_le hm).mp (zeh hj)
      exact ⟨_,j+1,Nat.succ_pos _,mul_comm (j+1) m ▸ hpay,hchoice,hproper⟩
  have hmem (P:af 4) (cutoff :ℕ) (hcut:m≤ cutoff)
      (horder :cutoff≤genericOrder P z)
      (hchoice : ∀ k<cutoff,
        (∃ u,EY u<genericOrder R z ∧
          BV (zhf 3 k) P=BV u R) ∨
        (∃ u,EY u<ell∧BV (zhf 3 k) P=BV u G)) :
      P∈front g z d m 0:= by
    rw [front_mem,Nat.zero_min]
    refine ⟨fun k hk j hj=>hvanish P k j hj ?_ (hchoice k (hk.trans_le hcut)),
      fun j hj=>(Nat.not_lt_zero j hj).elim⟩
    apply P6_6_7_3.order_mem
    simpa [EY] using (hk.trans_le (hcut.trans horder))
  have hR' := hmem R (genericOrder R z) (min_le_left _ _) le_rfl
    (fun k hk=>Or.inl ⟨zhf 3 k,by simpa [EY] using hk,rfl⟩)
  have hG' := hmem G ell (min_le_right _ _) hG
    (fun k hk=>Or.inr ⟨zhf 3 k,by simpa [EY] using hk,rfl⟩)
  have hc:=yC (z :=z) (hchart.2.1 a le_rfl) hchart.2.2 hinv hd hR' hG'
  rw [hlen] at hc
  have hn:v< m*d:= by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul hm).mp (zTO (v/m))
  exact (not_le_of_gt hn) (ENat.natCast_le_natCast.mp hc)
end
end qOuMLEd
end
