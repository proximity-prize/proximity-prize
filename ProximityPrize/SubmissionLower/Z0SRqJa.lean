import ProximityPrize.SubmissionLower.ZGa2w7a
import ProximityPrize.SubmissionLower.ZdBkMOd
import ProximityPrize.SubmissionLower.ZPoBc3d
import ProximityPrize.SubmissionLower.ZQmiAIb
set_option Elab.async false
open _root_ renaming Fin.sum_univ_eq_sum_range → zdx, Fintype.card_fin → zgY, Fintype.linearCombination → z3d, Function.Injective → zq4, LinearMap.ker → z83, LinearMap.mulLeft → zzN, LinearMap.range → zWl, LinearMap.range_comp_le_range → z0A, Module.Finite → zAa, Module.finrank → zsE, Module.finrank_pi → zJ6, Nat.add_le_add_right → zlr, Nat.lt_succ_of_le → zB1, Submodule.finrank_mono → zFM
section
set_option autoImplicit true
namespace qzM5sEd
noncomputable section
open aR (ao)
open Rj (Flat Exp lK adf acw J6 La oH)
open qlc9qed (Bank)
open qPQ4nYa
open MvPolynomial
open scoped BigOperators
open private bhx bhy y NH dcj gmr gms blU a8I a6A aid cwS aQH bv2 cva caB eLE from ProximityPrize.SubmissionLower.S
def cbQ (b : Bank) (q : ℕ) (g : ℤ) : Set adf :=
  {e | e.weight (fun _ => 1) = iO b q ∧
    -g ≤ (e.weight Fin.val : ℤ) ∧ e.weight Fin.val ≤ b.box.j ∧ e 2 ≤ b.box.t}
def aqz (b : Bank) (q : ℕ) (g : ℤ) : Submodule ao lK :=
  restrictSupport ao (cbQ b q g)
def aPi (b : Bank) (q : ℕ) (g : ℤ) : aqz b q g →ₗ[ao] lK :=
  ((weightedTruncation a6A (Ic b q g).toNat).comp
    (bind₁ acw).toLinearMap).domRestrict (aqz b q g)
instance gRv (b : Bank) (q : ℕ) (g : ℤ) : zAa ao (aqz b q g) := by
  apply restrictSupport_finite
  refine (Finsupp.finite_of_nat_weight_le (fun _ : Fin 3 => 1)
    (by simp) (iO b q)).subset ?_
  intro e he
  exact (show e.weight (fun _ => 1) = iO b q from he.1).le
private def jO (b : Bank) (q : ℕ) : ℕ := q - iO b q
private def Ra (b : Bank) (q : ℕ) (e : Exp) : adf :=
  Finsupp.equivFunOnFinite.symm ![e (some 0) - jO b q, e (some 1), e (some 2)]
private theorem buZ (b : Bank) {q k : ℕ} (e : TO b q k) :
    jO b q ≤ e.val (some 0) := by
  have hd := e.property.2.1
  have hj := e.property.1.2.1
  rw [bhx] at hd
  rw [bhy] at hj
  simp only [jO, iO]
  omega
private theorem cqD (b : Bank) {q k : ℕ} (e : TO b q k) :
    Ra b q e ∈ cbQ b q (offset b k) := by
  have hd := e.property.2.1
  have hj := e.property.1.2.1
  have ht := e.property.1.2.2
  have hg := e.property.2.2
  have ha := buZ b e
  rw [bhx] at hd
  rw [bhy] at hj hg
  change (Ra b q e).weight (fun _ => 1) = iO b q ∧
    -offset b k ≤ ((Ra b q e).weight Fin.val : ℤ) ∧
    (Ra b q e).weight Fin.val ≤ b.box.j ∧ (Ra b q e) 2 ≤ b.box.t
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, Ra, smul_eq_mul, Nat.mul_comm]
  simp only [jO, iO] at *
  omega
private def bpl (b : Bank) (q k : ℕ) (e : TO b q k) :
    aqz b q (offset b k) :=
  ⟨monomial (Ra b q e) 1,
    (monomial_mem_restrictSupport ao).mpr (Or.inl (cqD b e))⟩
private def encode (b : Bank) (q k : ℕ) : Block b q k →ₗ[ao] aqz b q (offset b k) :=
  (basisRestrictSupport ao (TO b q k)).constr ao (bpl b q k)
private theorem b1y (b : Bank) (q k : ℕ) (e : TO b q k) :
    ((encode b q k (basisRestrictSupport ao (TO b q k) e)) : lK) =
      monomial (Ra b q e) 1 :=
  congrArg Subtype.val
    ((basisRestrictSupport ao (TO b q k)).constr_basis ao (bpl b q k) e)
local notation "T" => (MvPolynomial.X (none : Option (Fin 3)) : Flat)
private theorem cqE (b : Bank) (q : ℕ) (e : Exp) :
    bind₁ NH (bind₁ acw (monomial (Ra b q e) 1)) =
      La (some 0) ^ (e (some 0) - jO b q) *
        (T * y 1) ^ e (some 1) * (T ^ 2 * y 2) ^ e (some 2) := by
  rw [bind₁_bind₁, blU, Fin.prod_univ_three]
  simp [dcj, gmr, gms, Ra, mul_assoc]
private theorem cpw (b : Bank) (q k : ℕ) (e : TO b q k) :
    T ^ (-offset b k).toNat * J6 (monomial e.val 1) =
      T ^ (offset b k).toNat * La (some 0) ^ jO b q *
        bind₁ NH (bind₁ acw (monomial (Ra b q e) 1)) := by
  have hi := e.property.2.2
  rw [bhy] at hi
  have ht : (-offset b k).toNat + e.val none =
      (offset b k).toNat + e.val (some 1) + 2 * e.val (some 2) := by omega
  have ha : jO b q + (e.val (some 0) - jO b q) = e.val (some 0) := by
    have := buZ b e
    omega
  have hT : T ^ (-offset b k).toNat * T ^ e.val none =
      T ^ (offset b k).toNat * T ^ e.val (some 1) * T ^ (2 * e.val (some 2)) := by
    simpa only [pow_add] using congrArg (T ^ ·) ht
  have hA : La (some 0) ^ e.val (some 0) =
      La (some 0) ^ jO b q * La (some 0) ^ (e.val (some 0) - jO b q) := by
    rw [← pow_add, ha]
  rw [a8I, cqE]
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (T ^ (-offset b k).toNat * T ^ e.val none) *
        (La (some 0) ^ e.val (some 0) * y 1 ^ e.val (some 1) * y 2 ^ e.val (some 2)) := by
      ring
    _ = _ := by rw [hT, hA]; ring
private theorem gqH (b : Bank) (q k : ℕ) (p : Block b q k) :
    T ^ (-offset b k).toNat * J6 (p : Flat) =
      T ^ (offset b k).toNat * La (some 0) ^ jO b q *
        bind₁ NH (bind₁ acw (encode b q k p : lK)) := by
  let l := (zzN ao (T ^ (-offset b k).toNat)).comp
    (J6.toLinearMap.comp (Block b q k).subtype)
  let r := (zzN ao (T ^ (offset b k).toNat * La (some 0) ^ jO b q)).comp
    ((bind₁ NH).toLinearMap.comp ((bind₁ acw).toLinearMap.comp
      ((aqz b q (offset b k)).subtype.comp (encode b q k))))
  have h : l = r := by
    apply (basisRestrictSupport ao (TO b q k)).ext
    intro e
    change T ^ (-offset b k).toNat *
      J6 (↑(basisRestrictSupport ao (TO b q k) e) : Flat) =
        T ^ (offset b k).toNat * La (some 0) ^ jO b q *
          bind₁ NH (bind₁ acw
            (↑(encode b q k (basisRestrictSupport ao (TO b q k) e)) : lK))
    rw [b1y, coe_basisRestrictSupport_apply]
    exact cpw b q k e
  exact LinearMap.congr_fun h p
private theorem brp (b : Bank) (q k : ℕ) :
    z83 ((aPi b q (offset b k)).comp (encode b q k)) ≤
      z83 (af3 b q k) := by
  intro p hp
  let L : aqz b q (offset b k) := encode b q k p
  let S : lK := bind₁ acw (L : lK)
  let cut := (Ic b q (offset b k)).toNat
  have hz : weightedTruncation a6A cut S = 0 := LinearMap.mem_ker.mp hp
  have hcontact := (weightedTruncation_eq_zero_iff _ _ _).mp hz
  have hgrade : (L : lK).IsWeightedHomogeneous (fun _ : Fin 3 => 1) (iO b q) :=
    fun e he => (L.property (mem_support_iff.mpr he)).1
  have hS : S.IsWeightedHomogeneous (fun _ : Fin 3 => 1) (iO b q) :=
    hgrade.bind₁ eLE
  have hscaled : S ∈ restrictWeightedOrder aid (cut + iO b q) := by
    intro e he
    have hg := hS (mem_support_iff.mp he)
    have hc := mem_restrictWeightedOrder.mp hcontact e he
    change cut + iO b q ≤ e.weight aid
    rw [cwS, hg]
    exact zlr hc _
  have hprod := mul_mem_restrictWeightedOrder
    (mul_mem_restrictWeightedOrder (aQH (offset b k).toNat)
      (by simpa using pow_mem_restrictWeightedOrder cva (jO b q)))
    (bind₁_mem_restrictWeightedOrder bv2 hscaled)
  have hbound : b.m + (-offset b k).toNat ≤
      (offset b k).toNat + jO b q + (cut + iO b q) := by
    change b.m + (-offset b k).toNat ≤ (offset b k).toNat + jO b q +
      (((b.m : ℤ) - (q : ℤ) - offset b k).toNat + iO b q)
    have hd : iO b q ≤ q := min_le_left ..
    unfold jO
    omega
  have hshift : T ^ (-offset b k).toNat * J6 (p : Flat) ∈
      restrictWeightedOrder oH (b.m + (-offset b k).toNat) := by
    rw [gqH]
    exact restrictWeightedOrder_anti _ hbound hprod
  apply LinearMap.mem_ker.mpr
  exact (weightedTruncation_eq_zero_iff _ _ _).mpr (caB hshift)
theorem fTp (b : Bank) (q k : ℕ) :
    zsE ao (zWl (af3 b q k)) ≤
      zsE ao (zWl (aPi b q (offset b k))) := by
  let f := (aPi b q (offset b k)).comp (encode b q k)
  have hker := zFM (brp b q k)
  change zsE ao (z83 f) ≤
    zsE ao (z83 (af3 b q k)) at hker
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := (af3 b q k).finrank_range_add_finrank_ker
  exact (show zsE ao (zWl (af3 b q k)) ≤
      zsE ao (zWl f) by omega).trans
    (zFM (z0A _ _))
end
end qzM5sEd
end
section
section
set_option autoImplicit true
namespace qlHk46d
open P5_7_2 (Aux fO introduction stages)
open qMNIwTb (Filed)
open cu (Shape)
open private c4y from ProximityPrize.SubmissionLower.Zq1cNdd
open private height_guard from ProximityPrize.SubmissionLower.ZQmiAIb
private def dM (s :Shape) :Prop :=s.J≤ s.B∧s.B≤ s.U∧s.B<K1.p
private instance (s :Shape) :Decidable (dM s) :=
 inferInstanceAs (Decidable (_∧_∧_))
private theorem stage_fits (b:fO) : ∀ s∈stages b,dM s.free∧dM s.moving:= by
 fin_cases b <;> simp only [stages,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨by decide,?_⟩
private theorem aux_fits (b:fO) : ∀ a∈introduction b,dM a.shape := by
 fin_cases b <;> simp only [introduction,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first
  | exact fun _ h=>(List.not_mem_nil h).elim
  | refine ⟨by decide,?_⟩
private theorem filed_fits {b:fO} {move :Bool} {a :Aux} (ha :Filed b move a) :dM a.shape := by
 rcases ha with ⟨_,hm⟩ | ⟨s,hm,rfl⟩
 · exact aux_fits b a hm
 · cases move
   · exact (stage_fits b s hm).1
   · exact (stage_fits b s hm).2
def c1 :Prop :=qQCEOid.c1
def c2 :Prop :=qQCEOid.c2
theorem of_children (h1 :c1) (h2 :c2) :qMNIwTb.c1 := by
 intro b h hlo hhi _ move a ha _ D _ Crt word
 obtain ⟨hJ,hU,hB⟩:=filed_fits ha
 obtain ⟨hlo',hhi'⟩:=height_guard b
 exact c4y (qQCEOid.of_children h1 h2) (hlo'.trans_le hlo)
  (hhi.trans_lt (hhi'.trans_lt (by decide))) Crt word a.shape hJ hU hB _
end qlHk46d
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qBZoH8d
noncomputable section
open P5 (I)


open qQCEOid (seedMatrix sourceVector normalized windowMatrix WindowCol)
open aeL (Offset)
open cu (L Shape)
open DP Ge Polynomial Finset
open private packed_tests from ProximityPrize.SubmissionLower.ZPoBc3d
open private cb9 from ProximityPrize.SubmissionLower.Z
open private c7U from ProximityPrize.SubmissionLower.B4


def c1 :Prop :=
  ∀ (F:Type) [Field F] (s :Shape) (t:Offset s) (u:ℕ) (a b c:F),b≠0 →
    (seedMatrix s t u a b c).rank ≤ ∑ k∈range (s.B+u+1),xR s t.val u k
private theorem grade_card_le {B:ℕ} (n N :ℕ→ℕ)
   (p: (Σ q:Fin (B+1),Fin (n q.val))→Prop) [Fintype (Subtype p)]
   (T:Finset ℕ) (hp : ∀ v :Subtype p,v.val.1.val∈T)
   (hN : ∀ q,n q≤N q) :
   Fintype.card (Subtype p) ≤ ∑ q∈T,N q:= by
 let f (v :Subtype p) :Σ q:T,Fin (N q.val) :=
   ⟨⟨v.val.1.val,hp v⟩,Fin.castLE (hN _) v.val.2⟩
 have hi:zq4 f := by
   intro v w h
   have hq:v.val.1=w.val.1 :=
     Fin.ext (congrArg (fun z :Σ q:T,Fin (N q.val)=>z.1.val) h)
   apply Subtype.ext
   refine Sigma.ext hq ((Fin.heq_ext_iff (congrArg (fun q:Fin (B+1)=>n q.val) hq)).2 ?_)
   exact congrArg (fun z :Σ q:T,Fin (N q.val)=>z.2.val) h
 simpa only [Fintype.card_sigma,zgY,Finset.sum_coe_sort] using
   Fintype.card_le_of_injective f hi
private theorem window_bound (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ) :
    (windowMatrix F s t u k).rank≤xR s t.val u k := by
  classical
  unfold xR
  apply le_min
  · refine (Matrix.rank_le_card_width _).trans ?_
    change Fintype.card (WindowCol s t u k)≤_
    refine grade_card_le _ _ _ _ (fun v => ?_) (fun q => ?_)
    · have hq:=v.val.1.isLt
      obtain ⟨hl,hu⟩:=v.property
      exact mem_Ico.mpr ⟨by omega,zB1 (le_min hl (by omega))⟩
    · unfold paddedColumns agU.Bb
      exact Nat.sub_le_sub_right
        (zlr (min_le_min_left q (min_le_left _ _)) 1) _
  · let S:=(univ :Finset (aeL.Pivot s t)).filter (fun r=>r.1.val≤k)
    refine (Matrix.rank_le_card_of_support_subset _ S ?_).trans ?_
    · intro r hr
      by_contra h
      have hq:k< r.1.val := by simpa [S] using h
      apply hr
      funext v
      change aeL.Pa s t (1 :F) r v.val=0
      exact ite_eq_right (fun hrv=>(not_le_of_gt hq) (hrv.1.trans v.property.1))
    · rw [← Fintype.card_coe S]
      refine grade_card_le _ _ _ _ (fun v => ?_) (fun _=>le_rfl)
      exact mem_range.mpr (zB1
        (le_min (mem_filter.mp v.property).2 (Nat.lt_succ_iff.mp v.val.1.isLt)))
theorem from_projective (hp:qQCEOid.c1) :c1 := by
 intro F _ s t u a b c hb
 exact (hp F s t u a b c hb).trans (sum_le_sum fun k _=>window_bound F s t u k)
private theorem local_tests (hl:c1) {F:Type} [Field F] (s :Shape)
    (α:F) (side :Fin 2) (a b c:F) (hb:b≠0) :
    ∃ tests :Gm F →ₗ[F] (Fin (paddedRank s)→F),∀ P,adk s P→tests P=0 →
      (pW ((Polynomial.X - C (algebraMap F (kq F) α))^(s.B+s.J)) :
        EM (kq F))∣forward (Polynomial.X - C α) (C (residue side a b c)) P:= by
  classical
  let T:=Offset s×Fin (s.U+1)
  let M (i:T) :=seedMatrix s i.1 (s.U-i.2.val) a b c
  let f (i:T) :=(M i).mulVecLin.comp (sourceVector (t:=i.1) α side i.2)
  let d (i:T) := ∑ k∈range (s.B+(s.U-i.2.val)+1),xR s i.1.val (s.U-i.2.val) k
  have hd (i:T) :zsE F (zWl (f i))≤d i :=
    (zFM (z0A _ (M i).mulVecLin)).trans
      (hl F s i.1 _ a b c hb)
  have hn: (∑ i:T,d i)≤paddedRank s := by
    rw [Fintype.sum_prod_type]
    let S (t r :ℕ) := ∑ k∈range (s.B+(s.U-r)+1),xR s t (s.U-r) k
    change (∑ t:Fin (s.B+2*s.J),∑ r :Fin (s.U+1),S t.val r.val) ≤
      ∑ t∈range (s.B+2*s.J),∑ r∈range (s.U+1),S t r
    rw [← zdx (fun t => ∑ r∈range (s.U+1),S t r)]
    exact sum_le_sum fun t _=>(zdx (S t.val) _).le
  obtain ⟨tests,ht⟩:=packed_tests f d hd hn
  exact ⟨tests,fun P hP hz=>normalized s α side a b c hb P hP (fun t r=>ht P hz (t,r))⟩
private theorem simple_bound (hl:c1)
   {F ι:Type} [Field F] [Fintype ι] {h:ℕ}
   {H :F[X]} {lift: (kq F)[X]}
   (G:bk5 h H lift) (s :Shape)
   (P:ι→Gm F) (hP : ∀ k,adk s (P k))
   {n:ℕ} (M:Matrix (Fin n) ι F)
   (hM : ∀ v,M.mulVec v=0↔a0X s H lift (z3d F P v)) :
   M.rank≤2*h*paddedRank s := by
 classical
 choose tests ht using fun t =>
   local_tests hl s (G.root t) (G.side t) (G.a t) (G.b t) (G.c t) (G.b_ne t)
 let f : (ι→F) →ₗ[F] ((Fin (2*h)×Fin (paddedRank s))→F) :=
   LinearMap.pi fun r =>
     (LinearMap.proj r.2).comp ((tests r.1).comp (z3d F P))
 have hker :f.ker≤M.mulVecLin.ker := by
   intro v hv
   apply LinearMap.mem_ker.mpr
   apply (hM v).mpr
   apply cb9 s G
   intro t
   apply anc.gDE _ _ _ _ _ _ (G.aiq t) (G.centre t)
   apply ht t _ (ddL hP v)
   funext k
   exact congrFun (LinearMap.mem_ker.mp hv) (t,k)
 have hn:=zFM hker
 have hr :=f.range.finrank_le
 simp only [zJ6,Fintype.card_prod,zgY] at hr
 have hf :=f.finrank_range_add_finrank_ker
 have hm:=M.mulVecLin.finrank_range_add_finrank_ker
 unfold Matrix.rank
 omega
theorem c4y (hl:c1) {h:ℕ} (hh:0<h) (hp:h<K1.p)
   {D:jF h} (Crt:zG D) (word:I→L) (s :Shape) (W:ℕ) :
   zsE L (aq7 h word s W) ≤
     2*h*paddedRank s+Module.finrank L (complete Crt word s W) := by
 classical
 obtain ⟨E⟩:=c7U hh hp D Crt
 let A:=aq7 h word s W
 let _:zAa L A:=dPs h word s W
 let d:=zsE L A
 let basis :=Module.finBasis L A
 let P:Fin d→Source := fun k=>basis k
 have hP (k :Fin d) :adk s (P k) :=dPt (basis k).property
 obtain ⟨n,M,hs,hg⟩:=bzR.proof E s (Fin d) P hP
 have hgen:=simple_bound hl E.genericPoles s _
   (fun k=>gp2 (genericPoint.comp (Polynomial.C (R:=L))) (hP k)) _ hg
 have hrank :=(gtP M).trans hgen
 let f :=(M.map Uv).mulVecLin
 have hf : ∀ v :Fin d→L,
     z3d L P v=((basis.equivFun.symm v :A) :Source) := by
   intro v
   rw [Fintype.linearCombination_apply,Module.Basis.equivFun_symm_apply]
   symm
   simpa only [map_smul,Submodule.subtype_apply,P] using
     map_sum A.subtype (fun k=>v k•basis k) Finset.univ
 have hk (v :f.ker) :
     ((basis.equivFun.symm (v :Fin d→L) :A) :Source)∈complete Crt word s W:= by
   have hv :=(hs v.val).mp (LinearMap.mem_ker.mp v.property)
   rw [hf] at hv
   exact ⟨(basis.equivFun.symm v.val).property,hv⟩
 let g:f.ker →ₗ[L] complete Crt word s W :=
   LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp f.ker.subtype) hk
 let _:zAa L (complete Crt word s W) :=
   Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
 have hginj:zq4 g:= by
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
end qBZoH8d
end
end
