import ProximityPrize.SubmissionLower.P6Front
import ProximityPrize.SubmissionLower.Zx0Npsd
import ProximityPrize.SubmissionLower.P6Split
import ProximityPrize.SubmissionLower.Zu4k70a
import ProximityPrize.SubmissionLower.ZUCbske
import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.ZY18Mqc
import ProximityPrize.SubmissionLower.AZ
import ProximityPrize.SubmissionLower.ZzeWNbd
import ProximityPrize.SubmissionLower.B0
set_option Elab.async false
open _root_ renaming Finset → zJe, Finset.sum_apply → zpH, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.rename → zHw, Nat.cast_mul → z2R, Nat.choose_eq_zero_of_lt → zsx, Set.mem_range_self → zWL, Submodule.smul_mem → zc2, Submodule.span → zLD, Submodule.subset_span → zBO, Submodule.sum_mem → zo3
section
set_option autoImplicit true
namespace P6_3
noncomputable section
open P6 gR ProximityPrize.Benchmark Polynomial
open Rv (Adjugate)
open private aDT from ProximityPrize.SubmissionLower.B3
theorem cZP {u:e9} {T:qo u} {R:Relation T} (D:Reduction u T R)
    {γ:K} (hn:Normal u γ) (M:B5 u γ) :
    Disjoint M.support (pJ R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.lg i hi)
theorem eEU {u:e9} (T:qo u) {R:Relation T}
    (D:Reduction u T R) (J:Adjugate u (pJ R) D.height)
    (hsmall:2*D.height<P6.L) {γ:K} (hn:Normal u γ) (M:B5 u γ) :False := by
  classical
  let F:=J.Fr 0+C γ*J.Fr 1-J.denom*M.decoder
  have hfit :P6.k+2*D.height<P6.dw:= by
    have hsum:P6.k+P6.L=P6.dw:= by decide
    omega
  have hdeg:F.natDegree<P6.dw:= by
    have hj (j:Fin 2) : (J.Fr j).natDegree<P6.k+2*D.height :=
      aDT (by
        have hk :0<P6.k := by decide
        omega) (J.numer_degree j)
    have hP:M.decoder.natDegree<P6.k :=aDT (by decide) M.degree
    have hnum :=(natDegree_add_le (J.Fr 0) (C γ*J.Fr 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.Fr 1)))
    have hprod:=natDegree_mul_le (p:=J.denom) (q:=M.decoder)
    have hsub:=natDegree_sub_le (J.Fr 0+C γ*J.Fr 1) (J.denom*M.decoder)
    change (J.Fr 0+C γ*J.Fr 1-J.denom*M.decoder).natDegree<P6.dw
    have :=J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have :=hj 0; omega) (by have :=hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF:F=0:= by
    by_contra hf
    have hroot :=kL.agd node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd:i∉pJ R:= fun h=>(Finset.disjoint_left.mp (cZP D hn M)) hi h
        simp only [F,eval_sub,eval_add,eval_mul,eval_C,← J.nodes i hd,M.lg i hi]
        ring)
    have :=M.dw
    omega
  let Ju:=Finset.univ.filter (fun i:I=>J.denom.eval (node i)=0)
  let E :=pJ R∪Ju
  have hZ:Ju.card≤J.denom.natDegree :=kL.agd node
    IRSProfile.domain.injective _ J.nonzero Ju (fun _ hi=>(Finset.mem_filter.mp hi).2)
  have hE :E.card≤(pJ R).card+2*D.height:=(Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i:I) (hi:i∉E) :u 0 i+γ*u 1 i=M.decoder.eval (node i) := by
    have hd:i∉pJ R:= fun h=>hi (Finset.mem_union_left _ h)
    have hz :J.denom.eval (node i)≠0 :=
      fun h=>hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    have hf :F.eval (node i)=0:= by rw [hF,eval_zero]
    simp only [F,eval_sub,eval_add,eval_mul,eval_C,← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal:=a7J T
  have hheight:=D.height_eq
  have hs :=aSO u
  have hcard:P6.k+P6.L+P6.t≤Fintype.card I:= by
    rw [IRSProfile.card_index]
    decide
  have hfix (b:Fin 2) (i:I) :iterateFrobenius K p b.val (node i)=node i:= by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.ahU i)
  change ((AI p node (u 0) (u 1) P6.L P6.t).map (evalRingHom γ)).rank=Vv u at hn
  rw [kL.dfp,kL.cTe,
    kL.cHH _ node _ IRSProfile.domain.injective hfix M.decoder
      P6.k P6.L P6.t M.degree hcard E (by omega) hoff] at hn
  have hr :=Matrix.rank_le_card_width (kL.bcN
    (fun b:Fin 2=>iterateFrobenius K p b.val) (fun i:E=>node i.val)
    (fun i:E=>u 0 i.val+γ*u 1 i.val-M.decoder.eval (node i.val)) P6.L)
  rw [Fintype.card_coe,hn] at hr
  have hsize :2*D.height+(pJ R).card<Vv u:= by
    omega
  omega
end
end P6_3
end
section
set_option autoImplicit true
namespace P6_3
noncomputable section
open P6 Polynomial
open Rv (Bank lK adh)
def c1 :Prop :=
  ∀ aV u deleted h U V,lK u deleted h U V→24378≤h →
    h+deleted.card≤DY→aPB aV (blockLength - deleted.card) h →
    ∃ A:adh aV,∀ γ (M:B5 u γ),Disjoint M.support deleted →
      A.aSV γ M.decoder=0
def c2 :Prop :=
  ∀ aV u (A:adh aV) (Γ:zJe K),
    (∀ γ∈Γ,A.auh γ≠0 ∧ ∃ M:B5 u γ,A.aSV γ M.decoder=0) →
    Γ.card≤aPP
private theorem gNw {aV:Bank} (A:adh aV) (Γ:zJe K)
    (hΓ : ∀ γ∈Γ,A.auh γ=0) :Γ.card≤aV.b5A:= by
  obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr A.nonzero
  have hlt:aV.first+5<p:= by cases aV <;> decide
  apply BN.bqt p (aV.first+5) aV.second
    (by decide) (A.poly.coeff e) (MvPolynomial.mem_support_iff.mp he)
    (A.s_degree e he) hlt (A.t_degree e he) Γ
  intro γ hγ
  have hh:=congrArg (fun P:MvPolynomial (Fin 2) K=>P.coeff e) (hΓ γ hγ)
  simpa only [adh.auh,MvPolynomial.coeff_map,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hh
theorem dQD (h1 :c1) (h2 :c2) (aV:Bank)
    (u:e9) (hu:abC u) (T:qo u) (R:Relation T)
    (D:Reduction u T R) (B:KJ u T R D) (hnp:baQ B)
    (Γ:zJe K) (hΓ:Tt u Γ) (hn : ∀ γ∈Γ,Normal u γ) :
    Γ.card≤aPP+aV.b5A:= by
  classical
  obtain ⟨W⟩:=cbU B
  have hh:D.height+(pJ R).card≤DY :=
    D.height_eq ▸ aEz hu T
  by_cases hsmall:2*D.height<L
  · have hshort:=(dd8 D hu).1
    have hcap:DY≤blockLength:= by decide
    have hroom:k+3*D.height+(pJ R).card≤blockLength:= by omega
    obtain ⟨J⟩:=dsk B hnp W hroom
    have hempty :Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩:=aCl u Γ hΓ γ hγ
      exact eEU T D J hsmall (hn γ hγ) M)
    simp [hempty]
  have hmin:24378≤D.height:= by
    change ¬ 2*D.height<48755 at hsmall
    omega
  obtain ⟨A,hA⟩:=h1 aV u _ D.height _ _ W hmin hh
    (bVn aV _ _ (Nat.sub_le _ _) hmin)
  let good:=Γ.filter (fun γ=>A.auh γ≠0)
  let exc:=Γ.filter (fun γ => ¬ A.auh γ≠0)
  have hexc:exc.card≤aV.b5A:=gNw A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood:good.card≤aPP:=h2 aV u A good (by
    intro γ hγ
    obtain ⟨hγΓ,hnonzero⟩:=Finset.mem_filter.mp hγ
    obtain ⟨M⟩:=aCl u Γ hΓ γ hγΓ
    exact ⟨hnonzero,M,hA γ M (cZP D (hn γ hγΓ) M)⟩)
  have hsum:good.card+exc.card=Γ.card :=
    Finset.card_filter_add_card_filter_not (s :=Γ) (p:= fun γ=>A.auh γ≠0)
  exact hsum ▸ Nat.add_le_add hgood hexc
theorem of_children (h1 :c1) (h2 :c2) :P6.c3:= by
  intro u hu T R D B _ hnp Γ hΓ hn
  exact (dQD h1 h2 .ts u hu T R D B hnp Γ hΓ hn).trans (dyt .ts)
end
end P6_3
end
section
set_option autoImplicit true
namespace P6_6_8_3
open aR (Shape)
open P6_6
inductive Box
  | emptyWide | emptyTall | bX | middle | narrow
def caps :Box→Shape
  | .emptyWide=>⟨132,28,9⟩
  | .emptyTall=>⟨90,35,11⟩
  | .bX=>⟨88,20,6⟩
  | .middle=>⟨64,15, 5⟩
  | .narrow=>⟨32,6,2⟩
def retainedBox (v :Shape) :Box :=
  if v.j=3 then (if v.b≤17 then .bX else .middle)
  else if v.j=4 then (if v.b≤7 then .bX else if 22≤v.b then .narrow else .middle)
  else if v.j=5 then (if v.b≤5 then .bX else if 19≤v.b then .narrow else .middle)
  else if v.j=6 then (if v.b≤2 then .bX else if 15≤v.b then .narrow else .middle)
  else if 9≤v.b then .narrow else .middle
def bgt:Box→Shape
  | .emptyWide=>⟨0x196e61a06ac00,0x12254a276c2c00,0⟩
  | .emptyTall=>⟨0x287b4abd2c000,0x11821009d32000,0⟩
  | .bX=>⟨0xbc543dcb2c00,0x84e4572d5a800,0⟩
  | .middle=>⟨0x5f7f37b39000,0x449d08e85c800,0⟩
  | .narrow=>⟨0x779de2e1800,0x8e9e2c58e400,0⟩
end P6_6_8_3
end
section
set_option autoImplicit true
namespace q2w4Sxc
open aR (Shape aO)
open P6_6 P6_6_8
def meet (a b:Shape) :Shape :=⟨min a.b b.b,min a.j b.j,min a.t b.t⟩
def refineBox (lo hi:Shape) :Shape×Shape :=
  let hi' : Shape :=⟨hi.b,min hi.j (2*hi.b+hi.t),min hi.t (min hi.b (hi.j/3))⟩
  (⟨max lo.b (max lo.t ((lo.j+1 - hi'.t)/2)),max lo.j (3*lo.t),lo.t⟩,hi')
def trimBox (lo hi:Shape) :Shape×Shape :=
  let p:=refineBox lo hi
  let q:=refineBox p.1 p.2
  refineBox q.1 q.2
abbrev cap (v :Shape) :=meet (remainingLiteral v) (firstCaps v (Cj v))
def Usable (v low:Shape) (k :ℕ) :Prop :=
  0<k∧k≤132∧(CompanionTest v low k∨k=1)
inductive Certificate (v :Shape) :Shape→Shape→Prop where
  | empty {lo hi} : ¬ aO lo hi→Certificate v lo hi
  | prune {lo hi} : CompanionTest v lo (sharedOrder v)→Certificate v lo hi
  | trim {lo hi} : Certificate v (trimBox lo hi).1 (trimBox lo hi).2→Certificate v lo hi
  | regular {lo hi k} :
      Usable v lo k→(hi.t=1∨2≤lo.t)→3*hi.t≤hi.j →
      selfFee v hi k false≤dot (Lw v) lo →
      Certificate v lo hi
  | splitB {lo hi} (m:ℕ) :
      Certificate v lo {hi with b:=m} → Certificate v {lo with b:=m+1} hi→Certificate v lo hi
  | rK {lo hi} (m:ℕ) :
      Certificate v lo {hi with j:=m} → Certificate v {lo with j:=m+1} hi→Certificate v lo hi
  | splitT {lo hi} (m:ℕ) :
      Certificate v lo {hi with t:=m} → Certificate v {lo with t:=m+1} hi→Certificate v lo hi
def fO (j:ℕ) :Prop :=
  ∀ v,W0 v→v.j=j→Certificate v ⟨1,3,1⟩ (cap v)
end q2w4Sxc
end
section
set_option autoImplicit true
namespace q90NBie
noncomputable section
open P6_6_7
open aR (af wU extend)
open dN (GeoJets bC kC AX)
open BO (bsq bfW aYz)
open agL (BV EY a4B)
variable {C:Context} {R G:af 4} {ell:ℕ} {cs :ChartCase C.n}
variable {A:SurfaceAssignment C R G} {z D:Ideal GeoJets}
theorem low_mark {γ} (hγ:γ∈lowMarks C R G ell A) :
    γ∈C.Δ∧0<ord C R γ∧genericOrder G (A.aI γ)<ell :=
  Finset.mem_filter.mp hγ
private theorem surface_mem {γ} (hγ:γ∈lowMarks C R G ell A) :A.aI γ∈uG A ell:= by
  classical exact Finset.mem_image_of_mem _ hγ
theorem surface_spec (hZ:z∈uG A ell) :
    (kC R G).IsMinimalPrime z∧genericOrder G z<ell:= by
  classical
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hZ
  obtain ⟨hΔ,ho,hl⟩:=low_mark hγ
  exact ⟨(A.valid γ hΔ ho).1,hl⟩
theorem curve_mark {F:Cuts A ell} {γ} (hγ:γ∈aHl F z D) :
    γ∈lowMarks C R G ell A∧A.aI γ=z∧F.curve γ=D:= by
  classical
  obtain ⟨hs,hc⟩:=Finset.mem_filter.mp hγ
  obtain ⟨h,hz⟩:=Finset.mem_filter.mp hs
  exact ⟨h,hz,hc⟩
theorem curve_spec {F:Cuts A ell} (hD:D∈qv F z) :
    (AX z (F.first z)).IsMinimalPrime D:= by
  classical
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hD
  obtain ⟨h,hz⟩:=Finset.mem_filter.mp hγ
  simpa only [hz] using (F.valid γ h).1
theorem curve_on (h:PairInput C R G ell cs) {F:Cuts A ell}
    (hZ:z∈uG A ell) (hD:D∈qv F z) :aYz R D:= by
  have hz :=(surface_spec hZ).1
  have hf :bC R≠0:= fun e =>
    h.factor.1.ne_zero (lB.aFf (e.trans (map_zero _).symm))
  have hdim:=GJ.bf6 hf (lB.amo R G h.factor.1 h.proper) hz
  exact GJ.bZi hz.isPrime hdim (hz.le (Ideal.subset_span (by simp)))
    (F.proper z hZ) (curve_spec hD)
theorem make_cuts (h:PairInput C R G ell cs) (A:SurfaceAssignment C R G) :Nonempty (Cuts A ell) := by
  classical
  have hn:G≠0:= fun hz=>h.proper (hz.symm ▸ dvd_zero R)
  have hex (z) (hZ:z∈uG A ell) :=ePB hn (surface_spec hZ).1.isPrime
  let a (z) :=if hZ:z∈uG A ell then (hex z hZ).choose else 0
  have ha (z) (hZ:z∈uG A ell) :
      EY (a z)=genericOrder G z∧bC (BV (a z) G)∉z := by
    simpa only [a,dite_eq_left hZ] using (hex z hZ).choose_spec
  let first (z) :=BV (a z) G
  have ho γ (hγ:γ∈lowMarks C R G ell A) :
      wU (first (A.aI γ)) (extend (C.s γ)) (ell - genericOrder G (A.aI γ)) := by
    rw [← (ha (A.aI γ) (surface_mem hγ)).1]
    exact cUA G _ _ _ (h.order γ (low_mark hγ).1)
  have hc γ (hγ:γ∈lowMarks C R G ell A) :=
    bsq (A.valid γ (low_mark hγ).1 (low_mark hγ).2.1).2
      (bfW (Nat.sub_pos_of_lt (low_mark hγ).2.2) (ho γ hγ))
  refine ⟨⟨first,fun γ=>if hγ:γ∈lowMarks C R G ell A then (hc γ hγ).choose else ⊥,
    fun z hZ=>(ha z hZ).2,fun z _=>a4B (a z) h.H6,ho,?_⟩⟩
  intro γ hγ
  simpa only [dite_eq_left hγ] using (hc γ hγ).choose_spec
theorem second_cuts (F:Cuts A ell) :SecondCuts F:= by
  intro z hZ D hD _
  have hn:F.first z≠0:= fun hz=>F.proper z hZ (by simp [bC,hz])
  obtain ⟨a,ha,hp⟩:=ePB hn (curve_spec hD).isPrime
  refine ⟨BV a (F.first z),hp,a4B a (F.fits z hZ),?_⟩
  intro γ hγ
  obtain ⟨hl,hZγ,_⟩:=curve_mark hγ
  have ho:=F.order γ hl
  rw [hZγ] at ho
  simpa only [ha] using cUA (F.first z) _ a _ ho
theorem orders_pos (h:PairInput C R G ell cs) {F:Cuts A ell}
    (hZ:z∈uG A ell) (hD:D∈qv F z) :
    0<genericOrder G z∧0<curveOrder F z D:= by
  have hz :=(surface_spec hZ).1
  have hd:=curve_spec hD
  exact ⟨generic_positive (fun e=>h.proper (e.symm ▸ dvd_zero R)) hz.isPrime
    (hz.le (Ideal.subset_span (by simp))),
    generic_positive (fun e=>F.proper z hZ (by simp [bC,e])) hd.isPrime
      (hd.le (Ideal.mem_sup_right (Ideal.subset_span (by simp))))⟩
end
end q90NBie
end
section
set_option autoImplicit true
namespace qCj6p1d
noncomputable section
open Polynomial qAzl5me
open P6_6 (gZ bf weightedChart)
open aR (ao af Shape cK extend)
open dN (GeoJets GeoField bC An Ch separant pK
  kC oA)
open vS (g9 VE)
open aeM (FH azb aco)
abbrev memberBox (p:Shape) :=weightedChart (bf+1) p
abbrev sliceBox (p:Shape) :=weightedChart (bf+2) p
abbrev sigma (g:af 4) :=bC (separant g)
def graph (g:af 4) :g9 :=
  zHw Fin.castSucc (bC (pK g)) +
    znf (4 :GeoField)*zHw Fin.castSucc (sigma g) *
      z9v (Fin.last 4)
abbrev ChartRing (g:af 4) :=Localization.Away (sigma g)
abbrev qR (g:af 4) :=algebraMap GeoJets (ChartRing g)
def yu (g:af 4) :g9 →+* ChartRing g :=
  MvPolynomial.eval₂Hom ((qR g).comp znf)
    (Fin.lastCases
      (qR g (znf (-(4 :GeoField)⁻¹)*bC (pK g)) *
        IsLocalization.Away.invSelf (sigma g))
      (fun i=>qR g (z9v i)))
def aJf (g:af 4) (U:ao[X]) (h:An U (sigma g)≠0) :
    ChartRing g →+* GeoField :=
  IsLocalization.Away.lift (sigma g) (isUnit_iff_ne_zero.mpr h)
abbrev afU (g:af 4) (U:ao[X]) (h:An U (sigma g)≠0) :=
  (aJf g U h).comp (yu g)
def qg (g:af 4) (U:ao[X]) :Prop :=
  cK g U=0∧An U (sigma g)≠0
def Represents (g:af 4) (original representative :GeoJets) :Prop :=
  ∃ a :ℕ,original=sigma g^a*representative
structure Member4 (g:af 4) (p:Shape) where
  polynomial:GeoJets
  fits :VE (memberBox p) polynomial
  aEA:Represents g (bC (memberTest g)) polynomial
structure dmL (g:af 4) (p:Shape) extends Member4 g p where
  next:GeoJets
  next_fits :VE (sliceBox p) next
  next_represents :Represents g (bC (ZV g)) next
  values : ∀ x a :P6.K,∃ D,VE (sliceBox p) D ∧
    ∀ S:P6.K[X],S.natDegree≤gZ→qg g (extend S) →
      (An (extend S) D =0↔S.eval x=a)
structure Member5 (g:af 4) (p:Shape) where
  graph_fits :FH (azb p) 1 (graph g)
  polynomial:g9
  fits :FH (aco (bf+1) p) (bf+1) polynomial
  aEA:Associated (yu g polynomial) (qR g (bC (memberTest g)))
structure dmM (g:af 4) (p:Shape) extends Member5 g p where
  next:g9
  next_fits :FH (aco (bf+2) p) (bf+2) next
  next_represents :Associated (yu g next) (qR g (bC (ZV g)))
  values : ∀ x a :P6.K,∃ D,FH (aco (bf+2) p) (bf+2) D ∧
    ∀ S:P6.K[X],S.natDegree≤gZ→cK g (extend S)=0 →
      ∀ h:An (extend S) (sigma g)≠0,
        (afU g (extend S) h D =0↔S.eval x=a)
structure Branch (R G:af 4) (ell:ℕ) where
  aI:Ideal GeoJets
  base : (kC R G).IsMinimalPrime aI
  gH : (↑(ell*P6_6_7.genericOrder R aI) :ℕ∞) ≤
    oA (kC R G) aI base.isPrime
  g:af 4
  curve :Ideal GeoJets
  member :MemberCurve g aI curve
  regular :sigma g∉curve
  terminal:member.simple→bC (ZV g)∉curve
namespace Branch
variable {R G:af 4} {ell:ℕ}
abbrev Simple (b:Branch R G ell) :=b.member.simple
def demandWeight (b:Branch R G ell) :ℕ:= by
  classical
  exact if b.Simple then 1 else 2
def extra (b:Branch R G ell) :ℕ:= by
  classical
  exact if b.Simple then 0 else 1
abbrev weight (b:Branch R G ell) :ℕ:=ell*P6_6_7.genericOrder R b.aI
def dY (b:Branch R G ell) (U:ao[X]) :Prop :=
  b.curve≤Ch U∧qg b.g U
abbrev a5x (b:Branch R G ell) :=b.curve.map (qR b.g)
end Branch
variable {R G:af 4} {ell:ℕ}
def SameChart (F:zJe (Branch R G ell)) :Prop :=
  ∀ b∈F,∀ c∈F,b.aI=c.aI→b.g=c.g
def aSG (p:Shape) (b:Branch R G ell) (s :P6.K→P6.K[X]) (T:zJe P6.K) :Prop :=
  T.card≤1 ∨ ∃ D,VE (sliceBox p) D ∧D∉b.curve ∧
    ∀ γ∈T,An (extend (s γ)) D =0
def bMD (p:Shape) (b:Branch R G ell) (s :P6.K→P6.K[X]) (T:zJe P6.K) :Prop :=
  T.card≤1 ∨ ∃ D,FH (aco (bf+2) p) (bf+2) D ∧
    yu b.g D∉b.a5x ∧
    ∀ γ∈T,∀ h:b.dY (extend (s γ)),afU b.g (extend (s γ)) h.2.2 D =0
def demandCost (F:zJe (Branch R G ell)) (T:Branch R G ell→zJe P6.K) :ℕ :=
  ∑ b∈F,b.weight*(b.demandWeight*(T b).card)
def additiveCost (F:zJe (Branch R G ell)) :ℕ :=
  ∑ b∈F,b.weight*b.extra
end
end qCj6p1d
end
section
set_option autoImplicit true
namespace qKhY0Ke
open qHde8fc
open fP (cF xH oG)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem cast_ne_zero {n:ℕ} (hn:0<n) (h:n≤56) :
    (n:Ground)≠0:= by
  intro hz
  have hn' : n<P1.p:=h.trans_lt (by decide)
  have hv :=congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hn',ZMod.val_zero] at hv
  omega
private theorem shifted_pascal_span (k l s a :ℕ) (hl:k≤l) (h:l+s+a≤50+k)
    (hsize :l+s+a≤57) (y :Fin a→Ground) :
    ∃ u:Fin a→Ground,∀ j:Fin a,
      (∑ i:Fin a,u i*((l+s+i.val).choose (l+j.val) :Ground))=y j:= by
  induction k generalizing l y with
  | zero=>exact bAj.a6t l s a (by omega) y
  | succ k ih =>
    cases l with
    | zero=>omega
    | succ l =>
      let C (i:Fin a) :Ground :=(l+s+i.val+1 :ℕ)
      let D (j:Fin a) :Ground :=(l+j.val+1 :ℕ)
      have hC (i:Fin a) :C i≠0 :=
        cast_ne_zero (n:=l+s+i.val+1) (by omega) (by omega)
      have hD (j:Fin a) :D j≠0 :=
        cast_ne_zero (n:=l+j.val+1) (by omega) (by omega)
      have hscale (i j:Fin a) :
          ((l.succ+s+i.val).choose (l.succ+j.val) :Ground)*D j =
            C i*((l+s+i.val).choose (l+j.val) :Ground) := by
        have hc:=congrArg (fun n:ℕ=>(n:Ground))
          (Nat.add_one_mul_choose_eq (l+s+i.val) (l+j.val))
        simp only [z2R] at hc
        rw [show l.succ+s+i.val=l+s+i.val+1 by omega,
          show l.succ+j.val=l+j.val+1 by omega]
        exact hc.symm
      obtain ⟨w,hw⟩:=ih l (by omega) (by omega) (by omega) (fun j=>y j*D j)
      refine ⟨fun i=>w i/C i,fun j=>mul_right_cancel₀ (hD j) ?_⟩
      rw [Finset.sum_mul,← hw j]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc,hscale,← mul_assoc,div_mul_cancel₀ _ (hC i)]
private def exponent (b c f :ℕ) :Exponent :=
  Finsupp.equivFunOnFinite.symm ![56-(b+c+f),b,c,f]
@[simp] private theorem ayO (b c f :ℕ) (j:Fin 4) :
    exponent b c f j = ![56-(b+c+f),b,c,f] j:= by
  simp [exponent]
private def kg (b c f :ℕ) (h:b+c+f≤56) :aY :=
  ⟨exponent b c f,by simp [cF]; omega⟩
private theorem aNn {e v :aY}
    (h:cP (aD v.val)<cP (aD e.val)) :
    dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  unfold dZ
  omega
private theorem i7 {cut:ℕ} (m:gU cut) :
    cut≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
      m.val 1+2*m.val 2 + 3*m.val 3≤56:= by
  obtain ⟨_,hl,hu,_⟩:=m.property
  rw [xH] at hl hu
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
private theorem a2O {cut:ℕ} {m n:gU cut}
    (hb:m.val 1=n.val 1) (hc:m.val 2=n.val 2) (hf :m.val 3=n.val 3) :
    m=n:= by
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · change m.val 0=n.val 0
    omega
  · exact hb
  · exact hc
  · exact hf
private theorem R0 {ι:Type*} [Fintype ι] [DecidableEq ι]
    (S:Submodule Ground (ι→Ground)) (v :ι→Ground)
    (h : ∀ m,v m≠0→Pi.single m (1 :Ground)∈S) :v∈S:= by
  have hsum: (∑ m,v m•Pi.single m (1 :Ground))=v := by
    funext n
    simp [zpH,Pi.single_apply,smul_eq_mul,mul_ite]
  rw [← hsum]
  apply S.sum_mem
  intro m _
  by_cases hm:v m=0
  · simp [hm]
  · exact S.smul_mem _ (h m hm)
private theorem iN {cut b c f :ℕ} (m:gU cut)
    (h:c< m.val 2∨f< m.val 3) :cE cut (b,c,f) m=0:= by
  rcases h with h | h
  · simp [cE,yv,zsx h]
  · simp [cE,yv,zsx h]
theorem c5k (e :aY)
    (hbox :e.val 0+2*e.val 2 + 3*e.val 3≤57)
    (hshift:e.val 0+e.val 2+2*e.val 3≤50) :
    cE (57-e.val 0) (aD e.val) ∈
      zLD Ground
        (Set.range fun v :iw e=>cE (57-e.val 0) (aD v.val.val)) := by
  classical
  let a :=e.val 0
  let cut:=57-a
  let S:=zLD Ground
    (Set.range fun v :iw e=>cE cut (aD v.val.val))
  change cE cut (aD e.val)∈S
  have hs :cut+a=57:= by dsimp [cut,a]; omega
  have hb:2*e.val 2 + 3*e.val 3≤ cut:= by dsimp [cut,a]; omega
  have abO (r :ℕ) : ∀ m:gU cut,m.val 2+m.val 3=r →
      m.val 2≤e.val 2→m.val 3≤e.val 3→Pi.single m (1 :Ground)∈S:= by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro m hr hc hf
      let c:=m.val 2
      let f :=m.val 3
      let l:=cut - (2*c+3*f)
      let s :=c+2*f
      have hl:l+2*c+3*f=cut:= by dsimp only [l,c,f]; omega
      have hls :l+s+a+c+f=57:= by dsimp only [s]; omega
      let w (i:Fin a) :aY:=kg (l+s+i.val) c f (by omega)
      have hw (i:Fin a) :aD (w i).val=(l+s+i.val,c,f) := by
        simp [w,kg,aD]
      have hwEarlier (i:Fin a) :dZ (w i)<dZ e := by
        apply aNn
        rw [Sj,Sj,oG,oG]
        change 56+(3*(56-(l+s+i.val+c+f))+c+2*f) <
          56+(3*a+e.val 2+2*e.val 3)
        omega
      let y (j:Fin a) :Ground :=if l+j.val=m.val 1 then 1 else 0
      let k :=7-(c+f)
      have hkl:k≤l:= by dsimp only [k,l,cut,a,c,f]; omega
      obtain ⟨u,hu⟩:=shifted_pascal_span k l s a hkl
        (by dsimp only [k]; omega) (by omega) y
      let W := ∑ i:Fin a,u i•cE cut (l+s+i.val,c,f)
      have hW:W∈S:= by
        apply S.sum_mem
        intro i _
        apply S.smul_mem
        have hi:cE cut (aD (w i).val)∈S :=
          zBO ⟨⟨w i,hwEarlier i⟩,rfl⟩
        rwa [hw i] at hi
      have hOutside (n:gU cut) (hn:c<n.val 2∨f<n.val 3) :
          W n=0:= by
        simp [W,zpH,iN n hn]
      let δ:gU cut→Ground :=Pi.single m (1 :Ground)
      have hMatch (n:gU cut) (hnc:n.val 2=c) (hnf :n.val 3=f) :
          W n=δ n:= by
        obtain ⟨hlo,hhi⟩:=i7 n
        let j:Fin a :=⟨n.val 1-l,by omega⟩
        have hj:l+j.val=n.val 1 := by dsimp [j]; omega
        have hvalue :W n=y j:= by
          simpa [W,zpH,cE,yv,hnc,hnf,← hj,smul_eq_mul] using hu j
        rw [hvalue]
        change (if l+j.val=m.val 1 then 1 else 0)= _
        rw [hj]
        by_cases hnm:n=m
        · subst n
          simp [δ]
        · have hfirst:n.val 1≠m.val 1 := fun h =>
            hnm (a2O h hnc hnf)
          simp [hfirst,δ,hnm]
      let rem:=δ-W
      have hrem:rem∈S:= by
        apply R0 S
        intro n hn
        have hinside :n.val 2≤ c∧n.val 3≤f := by
          by_contra hnle
          have hout:c<n.val 2∨f<n.val 3:= by omega
          have hnm:n≠m:= by
            intro h
            subst n
            simp [c,f] at hout
          apply hn
          change δ n-W n=0
          rw [hOutside n hout]
          simp [δ,hnm]
        have hlt:n.val 2+n.val 3< r := by
          by_contra hlt
          have hnc:n.val 2=c:= by omega
          have hnf :n.val 3=f := by omega
          apply hn
          change δ n-W n=0
          rw [hMatch n hnc hnf,sub_self]
        exact ih _ hlt n rfl (hinside.1.trans hc) (hinside.2.trans hf)
      have hsum:=S.add_mem hrem hW
      change δ-W+W∈S at hsum
      rwa [sub_add_cancel] at hsum
  apply R0 S
  intro m hm
  have hle :m.val 2≤e.val 2∧m.val 3≤e.val 3:= by
    by_contra hn
    exact hm (iN m (by omega))
  exact abO _ m rfl hle.1 hle.2
end
end qKhY0Ke
end
section
set_option autoImplicit true
namespace qKhY0Ke
open qHde8fc
open fP (cF oG)
theorem proof :qHde8fc.c1 := by
  intro e _ hhi
  let a :=e.val 0
  let b:=e.val 1
  let c:=e.val 2
  let f :=e.val 3
  have hd:a+b+c+f=56:= by
    simpa only [cF] using e.property
  have hcost:cP (aD e.val)=56+(3*a+c+2*f) := by
    rw [Sj,oG]
  have hweight:3*a+c+2*f≤27:= by omega
  obtain ⟨j,hj,hIndex,hPivotCost⟩:=eLq a b c f hd hweight
  refine ⟨57-a,Or.inr ⟨j,hj,hPivotCost.trans hcost.symm,?_⟩,c5k e ?_ ?_⟩
  · rw [hIndex]
    omega
  · change a+2*c+3*f≤57
    omega
  · change a+c+2*f≤50
    omega
end qKhY0Ke
end
section
set_option autoImplicit true
namespace qhonTAe
open qHde8fc MvPolynomial
open GN (Interpolant ord weights b9)
open fP (m9 oG)
noncomputable section
abbrev cost (e :aY) :ℕ:=cP (aD e.val)
theorem nG (e :aY) :cost e=56+ord e.val := by
  rw [cost,Sj,oG,ord]
def jZ (e :aY) (cut:ℕ) :Submodule Ground (gU cut→Ground) :=
  zLD Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
def Md (m:Exponent) :Prop :=m.weight m9≤56∧m 0≤16
abbrev Bounded (d:ℕ) :=restrictWeightedDegree (R:=Ground) weights d
def Ak (e :aY) (P:Interpolant) :Prop :=
  b9 e.val P≠0 ∧
    ∀ v :aY,Md v.val→dZ e<dZ v→b9 v.val P=0
def cutBudget (e :aY) :ℕ:=3*(56 - ord e.val)+2*e.val 0+e.val 2/2
theorem abJ (m:Exponent) :Md m↔ord m≤56∧m 0≤16:= by
  rw [Md,oG,ord]
end
end qhonTAe
end
section
set_option autoImplicit true
namespace qhonTAe
open qHde8fc MvPolynomial
open axE (Form raw basis adB a1y a1z blP aTx ao9)
open fP (lP m9 oG cF)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def project (cut:ℕ) :Form →ₗ[Ground] (gU cut→Ground) :=
  LinearMap.pi fun col=>lcoeff Ground col.val
private theorem ad7 (cut:ℕ) (v :aY) :
    project cut (bind₁ raw (monomial v.val 1))=cE cut (aD v.val) := by
  funext m
  exact ao9 v.val m.val (v.property.trans m.property.1.symm)
private theorem bt7 {cut:ℕ} {F:Form} (hc:0<cut)
    (h:F∈restrictWeightedDegree lP (cut - 1)) :
    project cut F=0:= by
  funext m
  apply coeff_eq_zero_of_mem_restrictWeightedDegree h
  have hl:=m.property.2.1
  omega
private theorem ccT {cut:ℕ} {v :Exponent} (h : ¬ Md v) :
    project cut (bind₁ basis (monomial v 1))=0:= by
  funext m
  apply notMem_support_iff.mp
  intro hm
  obtain ⟨hw,ha⟩:=blP v m.val hm
  have hi:=m.property.2.2.1
  have ht:=m.property.2.2.2
  exact h ⟨by omega,ha.trans ht⟩
private theorem b65 {v e :aY}
    (h:v.val.weight m9<e.val.weight m9) :dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  rw [oG,oG] at h
  unfold dZ
  rw [Sj,Sj,oG,oG]
  omega
private theorem amf (m:Exponent) (z :Ground) :
    (monomial m z :Form)=z•monomial m 1 := by
  rw [smul_monomial,smul_eq_mul,mul_one]
private theorem relation (e :aY) (cut:ℕ) :
    ∃ z :Ground,z≠0 ∧
      ∃ q∈jZ e cut,
        project cut (bind₁ basis (monomial e.val 1)) =
          z•cE cut (aD e.val)+q:= by
  obtain ⟨z,hz,F,hF,he⟩:=aTx e.val
  refine ⟨z,hz,project cut (bind₁ raw F),?_,?_⟩
  · rw [F.as_sum,map_sum,map_sum]
    apply zo3
    intro m hm
    obtain ⟨hd,hw⟩:=hF m hm
    let v :aY:=⟨m,hd.trans e.property⟩
    have hlt:dZ v<dZ e :=b65 hw
    rw [amf,map_smul,map_smul,show m=v.val from rfl,ad7]
    exact zc2 _ _ (zBO (zWL (⟨v,hlt⟩:iw e)))
  · rw [a1y,he,map_add,map_add,amf,map_smul,map_smul,ad7]
private theorem d0u {e v :aY} (h:dZ v<dZ e) (cut:ℕ) :
    jZ v cut≤jZ e cut:= by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  exact zBO (zWL (⟨w.val,w.property.trans h⟩:iw e))
private theorem ccS (e :aY) (cut:ℕ) (v :iw e) :
    project cut (bind₁ basis (monomial v.val.val 1))∈jZ e cut:= by
  obtain ⟨z,_,q,hq,h⟩:=relation v.val cut
  rw [h]
  exact Submodule.add_mem _ (zc2 _ _ (zBO (zWL v)))
    (d0u v.property cut hq)
private theorem b2n (F:Form) (h:F.IsHomogeneous 56) :
    (adB F).IsHomogeneous 56:= by
  apply IsWeightedHomogeneous.bind₁ (w:=(1 :Fin 4→ℕ)) _ h
  intro i
  have hx :=isHomogeneous_X (σ:=Fin 4) Ground
  fin_cases i
  · exact (((hx 1).sub (hx 2)).sub (hx 3)).sub (hx 0)
  · exact ((hx 2).add (hx 3)).add (hx 0)
  · exact (hx 3).add (hx 0)
  · exact hx 0
theorem gtu (e :aY) (cut:ℕ) (F:Form) (hc:0<cut)
    (hhom:F.IsHomogeneous 56) (hlow:F∈restrictWeightedDegree lP (cut - 1))
    (hlead: (adB F).coeff e.val≠0 ∧
      ∀ v :aY,Md v.val→dZ e<dZ v→(adB F).coeff v.val=0) :
    cE cut (aD e.val)∈jZ e cut:= by
  classical
  let t:=(adB F).coeff e.val
  let G:=adB F - monomial e.val t
  have hg:G.IsHomogeneous 56 :=
    (b2n F hhom).sub (isHomogeneous_monomial t e.property)
  have hG:project cut (bind₁ basis G)∈jZ e cut:= by
    rw [G.as_sum,map_sum,map_sum]
    apply zo3
    intro m hm
    by_cases hlive :Md m
    · have hd:m.degree=56:= by
        rw [Finsupp.degree_eq_weight_one]
        exact hg (mem_support_iff.mp hm)
      let v :aY:=⟨m,hd⟩
      have hlt:dZ v<dZ e := by
        apply lt_of_not_ge
        intro h
        apply (mem_support_iff.mp hm)
        change G.coeff v.val=0
        dsimp only [G]
        rw [MvPolynomial.coeff_sub,coeff_monomial]
        by_cases hv :e.val=v.val
        · rw [ite_eq_left hv,← hv,sub_self]
        · have hkey :dZ e<dZ v := by
            have he :=e.property
            rw [cF] at he hd
            have hdif :e.val 1≠v.val 1∨e.val 2≠v.val 2∨e.val 3≠v.val 3:= by
              by_contra! hsame
              apply hv
              ext i
              fin_cases i
              · change e.val 0=v.val 0
                change v.val 0+v.val 1+v.val 2+v.val 3=56 at hd
                omega
              · exact hsame.1
              · exact hsame.2.1
              · exact hsame.2.2
            unfold dZ at h ⊢
            change v.val 0+v.val 1+v.val 2+v.val 3=56 at hd
            omega
          rw [ite_eq_right hv,hlead.2 v hlive hkey,sub_zero]
      rw [amf,map_smul,map_smul]
      exact zc2 _ _ (ccS e cut ⟨v,hlt⟩)
    · rw [amf,map_smul,map_smul,ccT hlive,smul_zero]
      exact Submodule.zero_mem _
  have hB:t•project cut (bind₁ basis (monomial e.val 1))∈jZ e cut:= by
    dsimp only [G] at hG
    rw [map_sub,a1z,map_sub,bt7 hc hlow,zero_sub,
      amf,map_smul,map_smul] at hG
    exact (jZ e cut).neg_mem_iff.mp hG
  have hB' := (jZ e cut).smul_mem t⁻¹ hB
  rw [smul_smul,inv_mul_cancel₀ hlead.1,one_smul] at hB'
  obtain ⟨z,hz,q,hq,he⟩:=relation e cut
  rw [he] at hB'
  have hv :=Submodule.sub_mem (jZ e cut) hB' hq
  rw [add_sub_cancel_right] at hv
  have hv' := zc2 (jZ e cut) z⁻¹ hv
  rw [smul_smul,inv_mul_cancel₀ hz,one_smul] at hv'
  exact hv'
end
end qhonTAe
end
section
set_option autoImplicit true
namespace qhonTAe
open qHde8fc MvPolynomial
open GN (Form Interpolant weights b9 wc)
open fP (lP)
open private biP a7a cDc cKq bnm dmk dmj c5Q from ProximityPrize.SubmissionLower.B0
open private aNF bg1 from ProximityPrize.SubmissionLower.B0
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem ePF (j:Fin 3) {Q:Form} (hQ:Q.IsHomogeneous 56) :
    (a7a j Q).IsHomogeneous 55:= by
  have hd (i:Fin 4) : (pderiv i Q).IsHomogeneous 55:=hQ.pderiv
  fin_cases j
  · exact hd 0
  · exact (hd 0).sub (hd 1)
  · exact ((hd 0).sub (hd 1)).sub (hd 2)
private theorem dMi (v :aY) :
    (bind₁ wc ((z9v 0:Form)^56)).coeff v.val=(v.val.multinomial:Ground) := by
  rw [map_pow,bind₁_X_right]
  have hv :wc 0=(∑ j:Fin 4,z9v j) := by simp [wc,Fin.sum_univ_four,add_assoc]
  rw [hv,coeff_sum_X_pow_of_fintype]
  rw [ite_eq_left (show v.val.sum (fun _ m=>m)=56 from v.property)]
private def Lift (d:ℕ) (P:Interpolant) :Prop :=
  ∃ Q:Form,Q.IsHomogeneous 56∧Q∈restrictWeightedDegree lP d ∧
    ∀ v :aY,(bind₁ wc Q).coeff v.val =
      b9 v.val P*(v.val.multinomial:Ground)
private theorem bIr (a :Ground) :Lift 0 (C a) := by
  refine ⟨C a*(z9v 0:Form)^56,(isHomogeneous_X_pow _ _).C_mul _,?_,?_⟩
  · simpa only [zero_add] using mul_mem_restrictWeightedDegree
      (C_mem_restrictWeightedDegree lP 0 a)
      (X_pow_mem_restrictWeightedDegree_zero (R:=Ground) (i:=0) rfl 56)
  · intro v
    rw [map_mul,bind₁_C_right,coeff_C_mul,dMi,b9,aeval_C]
    simp
private theorem ewe {d:ℕ} {P:Interpolant} (h:Lift d P) (j:Fin 3) :
    Lift (d+weights j) (P*z9v j) := by
  obtain ⟨Q,hQ,hd,hc⟩:=h
  refine ⟨biP j*a7a j Q,(dmk j).mul (ePF j hQ),
    ?_,?_⟩
  · rw [add_comm]
    exact mul_mem_restrictWeightedDegree (dmj j) (c5Q j hd)
  · intro v
    rw [map_mul,cDc,← cKq,bnm,hc,map_mul]
    rw [show b9 v.val (z9v j)=(v.val j.succ:Ground) by simp [b9]]
    ring
private theorem bfc (m:Fin 3 →₀ ℕ) (a :Ground) :
    Lift (m.weight weights) (monomial m a) := by
  induction m using Finsupp.induction₂ with
  | zero=>simpa only [map_zero,← C_apply] using bIr a
  | add_single j n m _ hnz ih =>
    clear hnz
    rw [map_add,Finsupp.weight_single,smul_eq_mul,monomial_add_single]
    induction n with
    | zero=>simpa only [zero_mul,add_zero,pow_zero,mul_one] using ih
    | succ n hn =>
      rw [Nat.succ_mul,← add_assoc,pow_succ,← mul_assoc]
      exact ewe hn j
private theorem ajL (cut:ℕ) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) :
    ∃ Q:Form,Q.IsHomogeneous 56∧Q∈restrictWeightedDegree lP (cut - 1) ∧
      ∀ v :aY,(bind₁ wc Q).coeff v.val =
        b9 v.val P*(v.val.multinomial:Ground) := by
  classical
  have h:= fun m:Fin 3 →₀ ℕ=>bfc m (P.coeff m)
  unfold Lift at h
  choose Q hQ hd hc using h
  refine ⟨∑ m∈P.support,Q m,IsHomogeneous.sum _ _ _ (fun m _=>hQ m),?_,?_⟩
  · apply zo3
    intro m hm
    exact restrictWeightedDegree_mono _ (mem_restrictWeightedDegree.mp hP m hm) (hd m)
  · intro v
    calc
      _ = ∑ m∈P.support,(b9 v.val (monomial m (P.coeff m))) *
          (v.val.multinomial:Ground) := by
        simp only [map_sum,coeff_sum,hc]
      _ = _:= by rw [← Finset.sum_mul,← map_sum,← P.as_sum]
theorem cEo {a b:ℕ} (ha :a≤56) (hb:b≤56) (hab:a≠b) :
    (a :Ground)≠(b:Ground) := by
  have hp:56<P1.p:= by decide
  intro h
  rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (ha.trans_lt hp),
    Nat.mod_eq_of_lt (hb.trans_lt hp)] at h
  exact hab h
theorem factorial_ne_zero {n:ℕ} (h:n≤56) : (n.factorial:Ground)≠0:= by
  induction n with
  | zero=>simp
  | succ n ih =>
    rw [Nat.factorial_succ,z2R]
    exact mul_ne_zero (by simpa using cEo h (b:=0) (by decide) (by omega))
      (ih (by omega))
private theorem aoy (v :aY) : (v.val.multinomial:Ground)≠0:= by
  have h:=congrArg (fun n:ℕ=>(n:Ground)) (Nat.multinomial_spec Finset.univ v.val)
  rw [z2R,← Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ v.val.support),← Finsupp.degree_eq_sum,v.property] at h
  intro hz
  simp only [hz,mul_zero] at h
  exact factorial_ne_zero le_rfl h.symm
theorem Ae (e :aY) (cut:ℕ) (hc:0<cut) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) (hsep:Ak e P) :
    cE cut (aD e.val)∈jZ e cut:= by
  obtain ⟨Q,hhom,hlow,hcoeff⟩:=ajL cut P hP
  apply gtu e cut Q hc hhom hlow
  constructor
  · rw [aNF,hcoeff]
    exact mul_ne_zero (bg1 _) (mul_ne_zero hsep.1 (aoy e))
  · intro v hlive hv
    rw [aNF,hcoeff,hsep.2 v hlive hv,zero_mul,mul_zero]
end
end qhonTAe
end
