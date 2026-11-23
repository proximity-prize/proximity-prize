import ProximityPrize.SubmissionLower.ZTbQzvb
import ProximityPrize.SubmissionLower.ZK15T2b
import ProximityPrize.SubmissionLower.ZIbuJkc
import ProximityPrize.SubmissionLower.ZlfuKwd
import ProximityPrize.SubmissionLower.Z35X4Rc
import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.ZjZ6ihd
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, LinearMap.mulRight → zBm, Module.finrank → zsE, Module.finrank_fintype_fun_eq_card → zvt, MvPolynomial.X → z9v, MvPolynomial.map_C → zpw, Nat.add_le_add → z9f, Nat.le_of_lt_succ → zeh, Nat.lt_succ_of_le → zB1, Polynomial.X → z7y
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
section
set_option autoImplicit true
set_option Elab.async false
namespace P5_7_2_3Q1322
open qgNKTHc
def tot : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: l, q => cV q (c % 256, c / 256) + tot l (q+1)
def win : ∀ (l : List ℕ) (q : ℕ), Window q l.length (tot l q)
  | [], _ => ⟨Fin.elim0, by simp [tot]⟩
  | c :: l, q => by
    rw [List.length_cons, Nat.add_comm]
    exact (row q _ _ _ rfl).join (win l (q+1))
def w (l : List ℕ) (q r : ℕ) (h : tot l q = r) : Window q l.length r := h ▸ win l q
set_option quotPrecheck false in
local notation "c!" l => w l _ _ (by decide +kernel)
def c0 : Window 0 30 150384 := c! [0,0,0x200055,0x20000300052,0x200003000040004f,0x20000300004000050004c,0x20000300004000050000600049,0x2000030000400005000060000700046,0x200003000040000500006000070000800043,0x20000300004000050000600007000080000900040,0x2000030000400005000060000700008000090000a0003d,0x2000030000400005000060000700008000090000a0000b0003a,0x2000030000400005000060000700008000090000a0000b0000c00037,0x2000030000400005000060000700008000090000a0000b0000c00035,0x2000030000400005000060000700008000090000a0000b0000c00033,0x2000030000400005000060000700008000090000a0000b0000c08031,0x2000030000400005000060000700008000090000a0000b08030,0x2000030000400005000060000700008000090000a0802f,0x2000030000400005000060000700008000090802e,0x20000300004000050000600007000080802d,0x200003000040000500006000070802c,0x2000030000400005000060802b,0x20000300004000050802a,0x2000030000408029,0x20000308028,0x208027,0x8026,0x8025,0x8024,0x8023]
def c1 : Window 30 30 126453 := c! [0x8022,0x8021,0x8020,0x801f,0x801e,0x801d,0x801c,0x801b,0x801a,0x8019,0x2008018,0x2008017,0x3008016,0x200005008015,0x200006008014,0x300006008013,0x20000500007008012,0x20000600008008011,0x30000600009008010,0x200005000070000b00800f,0x2000060000800000f,0x3000060000900000e,0x2000050000700000e,0x2000060000800000d,0x30000600000d,0x2000050000700000c,0x20000600000c,0x30000600000b,0x20000500000b,0x20000600000a]
def c2 : Window 60 28 15419 := c! [0x300000a,0x200005000109,0x2000009,0x3020208,0x2000108,0x2020307,0x20207,0x12040406,0x20306,0x2020040505,0x10040405,0x2030060604,0x2020040504,0x1004040070703,0x2030060603,0x202004050070802,0x1004040070702,0x203006060090901,0x202004050070801,0x1004040070700a2a00,0x203006060092900,0x202004050072800,0x1004040072700,0x2030062600,0x2020042500,0x10042400,0x22300,0x22200]
theorem proof : qPQ4nYa.c2 := (Window.join c0 <| Window.join c1 <| c2 : Window 0 88 292256).close
end P5_7_2_3Q1322
end
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
namespace qAxtVye
noncomputable section
open Polynomial
open P5 (jG)
open P5_7 (midAgreement Qn)
open P5_7_3 (fO)





open scoped BigOperators Classical
def c3:Prop :=
  ∀ (b:fO) u del (M:jG u del) Γ (F:P1.bje midAgreement M Γ),
    Qn b.jX.lo b.jX.hi M.iF→aKd b M F
def c5:Prop := ∀ b:fO,Cv b
end
end qAxtVye
end
section
set_option autoImplicit true
namespace qt5AtZa
noncomputable section
open cu (L)
open Y3 (Dg embed aka)
open qkgz7gb (Witness physicalStock)
def HeightLE (D W:ℕ) (F:Dg) :Prop :=
 ∀ j m,(F.coeff j).coeff m≠0→((F.coeff j).coeff m).natDegree+j*D ≤W
def HeightLT (D M:ℕ) (G:Dg) :Prop :=
 ∀ j m,(G.coeff j).coeff m≠0→((G.coeff j).coeff m).natDegree+j*D <M
structure Remainders (D e u:ℕ) (w:Witness) (Q:Dg)
  (V:Submodule L Dg) :Prop where
 rank :physicalStock (w.modulus-w.weight-1) D *(w.stock.cUr u).size<zsE L V
 jU : ∀ G∈V,G.natDegree≤e+w.g
 seed : ∀ G∈V,(w.stock.cUr u).fits (embed G)
 height : ∀ G∈V,HeightLT D w.modulus G
 congruence : ∀ G∈V,∃ H B:Dg,
  H*Q=G+aka (z7y ^w.modulus)*B
end
end qt5AtZa
end
section
set_option autoImplicit true
namespace qCexLpd
noncomputable section
open P5 (K)
open cu (L triangle)
open qkgz7gb (PlaneCurve SmoothAt SmoothCount rV)
open Finset MvPolynomial
open scoped Classical
private abbrev Deg (s :ℕ) :=restrictTotalDegree (Fin 2) L s
private theorem deg_finrank (s :ℕ) :zsE L (Deg s)=triangle s := by
 rw [show Deg s=restrictTotalDegree (Fin 2) L s from rfl,restrictTotalDegree,
  Module.finrank_eq_nat_card_basis (basisRestrictSupport L _),Nat.card_coe_set_eq]
 change {e :Fin 2 →₀ ℕ | e.degree≤ s}.ncard=triangle s
 rw [Finsupp.ncard_setOf_degree_le]
 simp [triangle,Nat.choose_two_right,Nat.mul_comm (s+2)]
private theorem select_marks {α F V:Type*} [Field F] [AddCommGroup V] [Module F V]
    (e :α→V →ₗ[F] F) (T:Finset α) :
    ∃ U⊆T,(∀ f :α→F,∃ v :V,∀ b∈U,e b v=f b) ∧
      ∀ v,(∀ b∈U,e b v=0) → ∀ b∈T,e b v=0:= by
  classical
  induction T using Finset.induction_on with
  | empty=>exact ⟨∅,Subset.rfl,fun _=>⟨0,by simp⟩,by simp⟩
  | insert a T _ ih =>
    obtain ⟨U,hUT,Ay,detect⟩:=ih
    by_cases h : ∃ v,(∀ b∈U,e b v=0)∧e a v≠0
    · obtain ⟨v,hv,hva⟩:=h
      refine ⟨insert a U,insert_subset_insert _ hUT,?_,?_⟩
      · intro f
        obtain ⟨w,hw⟩:=Ay f
        refine ⟨w+((f a-e a w)/e a v)•v,?_⟩
        intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · rw [map_add,map_smul,smul_eq_mul,div_mul_cancel₀ _ hva,add_sub_cancel]
        · rw [map_add,map_smul,hv b hb,smul_zero,add_zero,hw b hb]
      · intro w hw b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact hw _ (mem_insert_self _ _)
        · exact detect w (fun c hc=>hw c (mem_insert_of_mem hc)) b hb
    · refine ⟨U,hUT.trans (subset_insert _ _),Ay,?_⟩
      intro w hw b hb
      rcases mem_insert.mp hb with rfl | hb
      · by_contra hn
        exact h ⟨w,hw,hn⟩
      · exact detect w hw b hb
private def valAt (z :K→K) (γ:K) :PlaneCurve →ₗ[L] L :=
 (aeval (rV z γ)).toLinearMap
@[simp] private theorem valAt_apply (z :K→K) (γ:K) (q:PlaneCurve) :
   valAt z γ q=q.eval (rV z γ) := by
  simp [valAt]
private theorem exists_smooth (z :K→K) (U:Finset K) (s :ℕ)
    (Ay : ∀ f :K→L,∃ v :Deg s,∀ γ∈U,(v :PlaneCurve).eval (rV z γ)=f γ) :
    ∃ q:PlaneCurve,q.totalDegree≤ s+1 ∧ ∀ γ∈U,SmoothAt q (rV z γ) := by
  classical
  let W:Submodule L PlaneCurve :=Deg (s+1) ⊓ ⨅ γ:U,LinearMap.ker (valAt z γ)
  let d (γ:U) :Module.Dual L PlaneCurve :=(valAt z γ).comp (pderiv (0:Fin 2)).toLinearMap
  have hW (q:PlaneCurve) :
      q∈W↔q.totalDegree≤ s+1 ∧ ∀ γ∈U,q.eval (rV z γ)=0:= by
    simp only [W,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
      valAt_apply,mem_restrictTotalDegree,Subtype.forall]
  have witness (γ:U) : ∃ q∈W,d γ q≠0:= by
    obtain ⟨v,hv⟩:=Ay (fun b=>if b=γ.val then 1 else 0)
    let a :PlaneCurve :=z9v 0 - C (rV z γ.val 0)
    have ha :a.totalDegree≤1 :=(totalDegree_sub_C_le _ _).trans_eq (totalDegree_X _)
    have hd:=(mem_restrictTotalDegree _ _ _).mp v.property
    refine ⟨v.val*a,(hW _).2 ⟨(totalDegree_mul _ _).trans (z9f hd ha),?_⟩,?_⟩
    · intro b hb
      by_cases h:b=γ.val
      · subst b
        simp [a]
      · simp [hv b hb,h]
    · change valAt z γ (pderiv 0 (v.val*a))≠0
      rw [pderiv_mul]
      simp [a,hv γ γ.property]
  obtain ⟨q,hq,hder⟩:=Module.Dual.exists_forall_mem_ne_zero_of_forall_exists W d witness
  obtain ⟨hd,hq⟩:=(hW q).mp hq
  exact ⟨q,hd,fun γ hγ=>⟨hq γ hγ,0,by simpa [d] using hder ⟨γ,hγ⟩⟩⟩
private theorem smooth_mul (a b:PlaneCurve) (x :Fin 2→L)
   (h:SmoothAt (a*b) x) :SmoothAt a x∨SmoothAt b x := by
 obtain ⟨hz,i,hi⟩:=h
 rw [map_mul] at hz
 rcases mul_eq_zero.mp hz with ha | hb
 · exact Or.inl ⟨ha,i,fun hd=>hi (by rw [pderiv_mul]; simp [ha,hd])⟩
 · exact Or.inr ⟨hb,i,fun hd=>hi (by rw [pderiv_mul]; simp [hb,hd])⟩
private theorem smooth_all {T:Finset K} {z :K→K} {B:ℕ}
   (hs :SmoothCount T z B) (q:PlaneCurve) :
   (T.filter fun γ=>SmoothAt q (rV z γ)).card≤B*q.totalDegree := by
 classical
 induction q using WfDvdMonoid.induction_on_irreducible with
 | zero=>simp [SmoothAt]
 | unit q hq =>
   have he :T.filter (fun γ=>SmoothAt q (rV z γ)) = ∅ := by
     apply eq_empty_iff_forall_notMem.mpr
     intro γ hγ
     exact (hq.map (MvPolynomial.eval (rV z γ))).ne_zero (mem_filter.mp hγ).2.1
   simp [he]
 | mul a q ha hq ih =>
   rw [totalDegree_mul_of_isDomain hq.ne_zero ha,Nat.mul_add]
   apply le_trans _ (z9f (hs q hq) ih)
   refine (card_le_card ?_).trans (card_union_le _ _)
   intro γ hγ
   obtain ⟨hγ,h⟩:=mem_filter.mp hγ
   exact mem_union.mpr ((smooth_mul q a _ h).imp
     (fun hq' => mem_filter.mpr ⟨hγ,hq'⟩) (fun ha' => mem_filter.mpr ⟨hγ,ha'⟩))
theorem proof :qkgz7gb.c3:= by
  classical
  intro T z B _ hB _ hs
  let s :=2*B-1
  have hs1 :s+1=2*B:= by dsimp [s]; omega
  let e (γ:K) :Deg s →ₗ[L] L:=(valAt z γ).comp (Deg s).subtype
  obtain ⟨U,hUT,Ay,detect⟩:=select_marks e T
  obtain ⟨q,hq,hqu⟩:=exists_smooth z U s (by simpa [e] using Ay)
  have hsub:U⊆T.filter (fun γ=>SmoothAt q (rV z γ)) :=
    fun γ hγ=>mem_filter.mpr ⟨hUT hγ,hqu γ hγ⟩
  have hU:U.card≤B*(2*B) :=(card_le_card hsub).trans
    ((smooth_all hs q).trans (Nat.mul_le_mul_left B (hq.trans_eq hs1)))
  let M:Deg s →ₗ[L] (U→L) :=LinearMap.pi fun γ=>e γ
  have hdim:zsE L (U→L)<zsE L (Deg s) := by
    rw [zvt,Fintype.card_coe,deg_finrank]
    have ht:triangle s=B*(2*B+1) := by
      rw [triangle,hs1,show s+2=2*B+1 by omega,
        show 2*B*(2*B+1)=B*(2*B+1)*2 by ring]
      simp
    rw [ht,Nat.mul_add,Nat.mul_one]
    omega
  obtain ⟨v,hv,hn⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (M.ker_ne_bot_of_finrank_lt hdim)
  refine ⟨v.val,fun hz=>hn (Subtype.ext hz),(mem_restrictTotalDegree _ _ _).mp v.property,?_⟩
  have hu (γ:K) (hγ:γ∈U) :e γ v=0 :=
    congrFun (LinearMap.mem_ker.mp hv) ⟨γ,hγ⟩
  simpa [e] using detect v hu
end
end qCexLpd
end
end
section
section
set_option autoImplicit true
namespace q65qCJc
open P5_7_3 (terminal)
open qqf9uAa (Signs GradeSigns)
open scoped q65qCJc
theorem ordinary2950:Signs (terminal .s5) 2950 22 0 :=
  receipt! 2950 205763 22 0 82 78 17 4 11 3 0x52803d9d5f9b8
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s5) 2950 e ((((P5_7_3.fO.s5).schedule.gw).drop a).take 1)
theorem yQc0:gZ! 1 0:=⟨receipt! 2950 163851 1 302 77 77 22 4 3 4 0x2f000888200b7d23a73bb0,trivial⟩
theorem yQc1:gZ! 2 1:=⟨receipt! 2950 165107 2 297 76 77 23 4 4 4 0x4a800449d802e39674fbc22,trivial⟩
theorem yQc2:gZ! 3 2:=⟨receipt! 2950 166727 3 292 76 77 23 4 4 4 0x6e8004530002eb577515dfa,trivial⟩
theorem yQc3:gZ! 4 3:=⟨receipt! 2950 168809 4 287 77 77 22 4 5 4 0x9c0008c1a00bde0ba9bc30,trivial⟩
theorem yQc4:gZ! 5 4:=⟨receipt! 2950 170553 5 281 76 77 23 4 6 4 0xcd000463b003008075544f0,trivial⟩
theorem grades2950A:GradeSigns (terminal .s5) 2950 1 (((P5_7_3.fO.s5).schedule.gw).take 5) :=⟨yQc0.1,yQc1.1,yQc2.1,yQc3.1,yQc4.1,trivial⟩
end q65qCJc
end
section
set_option autoImplicit true
namespace q65qCJc
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped q65qCJc
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s5) 2950 e ((((P5_7_3.fO.s5).schedule.gw).drop a).take 1)
theorem yQc5:gZ! 6 5:=⟨receipt! 2950 173021 6 275 75 77 24 4 7 4 0x106400237b000c4244eafa1fc,trivial⟩
theorem yQc6:gZ! 7 6:=⟨receipt! 2950 176521 7 269 77 77 22 5 8 4 0xa44002446001957642dbaec,trivial⟩
theorem yQc7:gZ! 8 7:=⟨receipt! 2950 180469 8 262 77 77 22 5 10 4 0xc40002528001a52d42fd378,trivial⟩
theorem yQc8:gZ! 9 8:=⟨receipt! 2950 185628 9 254 75 77 24 5 12 4 0xe110009a56801bb9150ca7cf6,trivial⟩
theorem yQc9:gZ! 10 9:=⟨receipt! 2950 194052 10 245 71 77 28 5 3 5 0x80000fd42000a7543801e447812dd4c6d6,trivial⟩
theorem grades2950B:GradeSigns (terminal .s5) 2950 6 ((((P5_7_3.fO.s5).schedule.gw).drop 5).take 5) :=⟨yQc5.1,yQc6.1,yQc7.1,yQc8.1,yQc9.1,trivial⟩
end q65qCJc
end
section
set_option autoImplicit true
namespace q65qCJc
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped q65qCJc
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s5) 2950 e ((((P5_7_3.fO.s5).schedule.gw).drop a).take 1)
theorem yQc10:gZ! 11 10:=⟨receipt! 2950 205763 11 234 73 77 26 5 7 5 0xff90002ebbc002216b953e32f5c,trivial⟩
theorem yQc11:gZ! 12 11:=⟨receipt! 2950 205763 12 221 76 77 23 5 5 5 0x9de00156020086caea7ca4f0,trivial⟩
theorem yQc12:gZ! 13 12:=⟨receipt! 2950 205763 13 206 77 77 22 5 2 5 0x5100026dd002157b53e6fd6,trivial⟩
theorem yQc13:gZ! 14 13:=⟨receipt! 2950 205763 14 188 77 78 22 4 11 4 0x3d8008cbc01085eabe8994,trivial⟩
theorem yQc14:gZ! 15 14:=⟨receipt! 2950 205763 15 168 77 78 22 4 9 4 0xb8007e1a0106342bea1a4,trivial⟩
theorem grades2950C:GradeSigns (terminal .s5) 2950 11 ((((P5_7_3.fO.s5).schedule.gw).drop 10).take 5) :=⟨yQc10.1,yQc11.1,yQc12.1,yQc13.1,yQc14.1,trivial⟩
end q65qCJc
end
section
set_option autoImplicit true
namespace q65qCJc
open P5_7_3 (terminal)
open qqf9uAa (GradeSigns)
open scoped q65qCJc
set_option quotPrecheck false in
local notation "gZ!" e:arg a:arg => GradeSigns (terminal .s5) 2950 e ((((P5_7_3.fO.s5).schedule.gw).drop a).take 1)
theorem yQc15:gZ! 16 15:=⟨receipt! 2950 205763 16 146 77 78 22 4 7 4 0x6fcc010438abeb814,trivial⟩
theorem yQc16:gZ! 17 16:=⟨receipt! 2950 205763 17 121 75 78 24 4 5 4 0x18a520102984afb2f14,trivial⟩
theorem yQc17:gZ! 18 17:=⟨receipt! 2950 205763 18 95 77 78 22 4 4 4 0x55e80100e6abedf40,trivial⟩
theorem yQc18:gZ! 19 18:=⟨receipt! 2950 205763 19 66 77 78 22 4 2 4 0x4a6600ff812bef056,trivial⟩
theorem yQc19:gZ! 20 19:=⟨receipt! 2950 205763 20 35 76 78 23 4 1 4 0x1fdf803f8be57e0086,trivial⟩
theorem yQc20:gZ! 21 20:=⟨receipt! 2950 205763 21 2 77 78 22 4 12 3 0x35f000fced2bf0f18,trivial⟩
theorem grades2950D:GradeSigns (terminal .s5) 2950 16 (((P5_7_3.fO.s5).schedule.gw).drop 15) :=⟨yQc15.1,yQc16.1,yQc17.1,yQc18.1,yQc19.1,yQc20.1,trivial⟩
end q65qCJc
end
section
set_option autoImplicit true
open MvPolynomial renaming mem_support_iff→qz0,degreeOf_le_iff→qz1,C→qz2,ext→qz4,uniqueAlgEquiv→qz5,map→qz6,mapAlgEquiv→qz7
open Finsupp renaming zero_apply→qz3
set_option backward.isDefEq.respectTransparency false
namespace qHDgEWd
noncomputable section
open Polynomial Finset
open cu (L)
open qQ9yWTb (Raw)
open q4Pefpa (amm sk Padded stock j3 inputSize)
open qbIP9ia hiding amm
open private bg6 from ProximityPrize.SubmissionLower.BJ
private abbrev xvar :=qbIP9ia.amm
private def unflat :Flat ≃ₐ[L] Raw :=
 AlgEquiv.ofRingEquiv (f :=flatten.symm) (fun c=> by
  change (Polynomial.mapEquiv bg6)
   (MvPolynomial.optionEquivLeft L (Fin 2 ⊕ Unit) (qz2 c)) =
   C (qz2 (C c))
  rw [MvPolynomial.optionEquivLeft_C]
  change (C (qz2 c)).map bg6.toRingHom= _
  rw [Polynomial.map_C]
  congr 1
  change qz6 (qz5 L Unit).toRingHom
   (MvPolynomial.sumRingEquiv L (Fin 2) Unit (qz2 c))= _
  rw [MvPolynomial.sumRingEquiv_C,zpw]
  exact congrArg qz2 ((qz5 L Unit).commutes c))
private abbrev shift (c:L) :Raw ≃ₐ[L] Raw :=
 Polynomial.mapAlgEquiv (qz7 (Fin 2) (taylorEquiv c))
private theorem aXJ (c:L) (F:Raw) (j:ℕ) (m:Fin 2 →₀ ℕ) :
  ((shift c F).coeff j).coeff m=taylor c ((F.coeff j).coeff m) := by
 change (((F.map (qz6 (taylorEquiv c).toRingHom)).coeff j).coeff m)= _
 rw [Polynomial.coeff_map,MvPolynomial.coeff_map]
 rfl
private theorem asl (c:L) (F:Raw) : (shift c F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (qz7 (σ:=Fin 2) (taylorEquiv c)).injective F
private theorem shift_rect (c:L) {z t:ℕ} {F:Raw} (h:sk z t F) :
  sk z t (shift c F) := by
 intro i j
 apply qz1.mpr
 intro m hm
 apply qz1.mp (h i j) m
 apply qz0.mpr
 intro hz
 exact qz0.mp hm (by rw [aXJ,hz,map_zero])
private theorem shift_pad (c:L) {a b E M:ℕ} {F:Raw} (h:Padded a b E M F) :
  Padded a b E M (shift c F) := by
 refine ⟨(asl c F).trans_le h.1,fun j m hm => ?_⟩
 rw [aXJ,natDegree_taylor]
 exact h.2 j m (fun hz=>hm (by rw [aXJ,hz,map_zero]))
private theorem shift_shift (c:L) (F:Raw) :shift (-c) (shift c F)=F:= by
 apply Polynomial.ext
 intro j
 apply qz4
 intro m
 rw [aXJ,aXJ,taylor_taylor,neg_add_cancel,taylor_zero]
private theorem shift_physical (c:L) (d:L[X]) :
  shift c (amm d)=amm (taylor c d) := by
 change (C (qz2 d)).map (qz6 (taylorEquiv c).toRingHom) =
  C (qz2 (taylor c d))
 rw [Polynomial.map_C,zpw]
 rfl
private theorem fresh {F:Raw} (hF:F≠0) :
  ∃ c:L,¬ z9v xvar∣flatten (shift c F) := by
 classical
 have h : ∃ j m,(F.coeff j).coeff m≠0:= by
  by_contra! hn
  apply hF
  apply Polynomial.ext
  intro j
  apply qz4
  intro m
  simpa only [coeff_zero,AddMonoidAlgebra.coeff_zero,qz3] using hn j m
 obtain ⟨j,m,hm⟩:=h
 have hc : ∃ c:L,((F.coeff j).coeff m).eval c≠0:= by
  by_contra! hz
  exact hm (Polynomial.funext fun c=> by simpa only [eval_zero] using hz c)
 obtain ⟨c,hc⟩:=hc
 refine ⟨c,fun h => ?_⟩
 rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at h
 let v :=exps j 0 m
 have hv : ¬ Finsupp.single xvar 1≤v := by
  rw [Finsupp.single_le_iff]
  simp [v,exps_x]
 have hz :=congrArg (fun A:Flat=>A.coeff v) h
 rw [MvPolynomial.coeff_modMonomial_of_not_le _ hv,AddMonoidAlgebra.coeff_zero,
  qz3] at hz
 change (flatten (shift c F)).coeff (exps j 0 m)=0 at hz
 rw [flat_coeff,aXJ,taylor_coeff_zero] at hz
 exact hc hz
private theorem lead_mem {F:Raw} {j:ℕ} {m:Fin 2 →₀ ℕ} (hm: (F.coeff j).coeff m≠0) :
  exps j ((F.coeff j).coeff m).natDegree m∈(flatten F).support :=
 qz0.mpr (by rw [flat_coeff]; exact leadingCoeff_ne_zero.mpr hm)
private theorem in_caps {F:Raw} {e z t:ℕ} (he :F.natDegree≤e) (hr :sk z t F)
  {m:Exps} (hm:m∈(flatten F).support) :
  m none≤e∧m (seed 0)≤z∧m (seed 1)≤t:= by
 have h:=qz0.mp hm
 rw [flat_coeff'] at h
 have hh: (F.coeff (m none)).coeff (ao8 m)≠0:= fun hz=>h (by rw [hz,coeff_zero])
 have hj:F.coeff (m none)≠0:= fun hz =>
  hh (by simp only [hz,AddMonoidAlgebra.coeff_zero,qz3])
 have hs (i:Fin 2) :m (seed i)≤ if i=0 then z else t :=
  qz1.mp (hr i (m none)) _ (qz0.mpr hh)
 exact ⟨(le_natDegree_of_ne_zero hj).trans he,by simpa using hs 0,by simpa using hs 1⟩
private theorem out_caps {F:Raw} {E z t:ℕ}
   (h : ∀ m∈(flatten F).support,m none≤E∧m (seed 0)≤z∧m (seed 1)≤t) :
   F.natDegree≤E∧sk z t F:= by
 have q0 {j:ℕ} {m:Fin 2 →₀ ℕ} (hm: (F.coeff j).coeff m≠0) :
     j≤E∧m 0≤z∧m 1≤t:= by
   simpa only [exps_y,exps_s] using h _ (lead_mem hm)
 refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_,?_⟩
 · apply qz4
   intro m
   simp only [AddMonoidAlgebra.coeff_zero,qz3]
   by_contra hm
   exact hj.not_ge (q0 hm).1
 · intro i j
   apply qz1.mpr
   intro m hm
   have hk :=q0 (qz0.mp hm)
   fin_cases i
   · simpa using hk.2.1
   · simpa using hk.2.2
private theorem product_coord {P Q:Flat} {m:Exps} {i:Vars} {a b:ℕ}
   (hm:m∈(P*Q).support) (hp : ∀ t∈P.support,t i≤a)
   (hq : ∀ t∈Q.support,t i≤b) :m i≤a+b :=
 (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans
   ((MvPolynomial.degreeOf_mul_le _ _ _).trans
     (z9f (qz1.mpr hp) (qz1.mpr hq)))
private theorem jO (a b E :ℕ) (hab:a≤b) :
   (∑ j:Fin (E+1),(E*a+j.val*(b-a)))=j3 (a+b) E := by
 let s := ∑ j:Fin (E+1),j.val
 have hs :s*2=E*(E+1) := by
   dsimp only [s]
   rw [Fin.sum_univ_eq_sum_range (fun j:ℕ=>j),sum_range_id_mul_two,
     Nat.add_sub_cancel,Nat.mul_comm]
 rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,← sum_mul]
 change (E+1)*(E*a)+s*(b-a)= _
 have hab' : b-a+a=b:=Nat.sub_add_cancel hab
 have hdouble : ((E+1)*(E*a)+s*(b-a))*2=(a+b)*E*(E+1) := calc
   _=(E*(E+1))*a*2+(s*2)*(b-a) := by ring
   _=(s*2)*(a+(b-a+a)) := by rw [← hs]; ring
   _ = _:= by rw [hs,hab']; ring
 unfold j3
 omega
private theorem remainder_injective {g M z t:ℕ} {f :Flat}
   (hf : ¬ z9v xvar∣f) :
   zq4 ((rem M).comp ((zBm L f).comp
     (@rows (g+1) z t (fun _=>M)))) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro H hz
 have hd:=rem_eq M (rows H*f)
 change rem M (rows H*f)=0 at hz
 rw [hz,zero_add] at hd
 have hh:=(MvPolynomial.X_prime (R:=L) (i:=xvar)).pow_dvd_of_dvd_mul_right M hf ⟨_,hd⟩
 rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero] at hh
 apply rows_inj
 rw [map_zero]
 apply qz4
 intro m
 by_cases hm:m∈(rows H).support
 · have hb:=(mem_coord.mp (rows_support H hm)).2.1
   have he :=congrArg (fun A:Flat=>A.coeff m) hh
   rwa [MvPolynomial.coeff_modMonomial_of_not_le _ (Finsupp.single_le_iff.not.mpr hb.not_ge),
     AddMonoidAlgebra.coeff_zero,qz3] at he
 · exact MvPolynomial.notMem_support_iff.mp hm
theorem proof :q4Pefpa.c1 := by
  classical
  intro a b e g M z t h hab hM F hF he hr
  obtain ⟨c,hc⟩:=fresh hF
  let f :=flatten (shift c F)
  let E :=e+g
  let I:=Idx (g+1) z t (fun _=>M)
  let w (j:ℕ) :=E*a+j*(b-a)
  let J:=Idx (E+1) (z+h) (t+h) w
  let cut: (I →₀ L) →ₗ[L] Flat :=(rem M).comp ((zBm L f).comp rows)
  let q2 (j:J) :Exps :=exps j.1.1 (M-1-j.1.2) (seedMon j.2.1 j.2.2)
  let q0: (I →₀ L) →ₗ[L] (J→L) :=
    (LinearMap.pi fun j=>MvPolynomial.lcoeff L (q2 j)).comp cut
  let out:=(unflat.trans (shift (-c))).toLinearMap.comp (cut.comp q0.ker.subtype)
  have ho:zq4 out :=
    (unflat.trans (shift (-c))).injective.comp ((remainder_injective hc).comp Subtype.val_injective)
  let d:L[X] :=(z7y - C c)^M
  have hd:d.natDegree=M:= by simp [d,natDegree_pow]
  refine ⟨d,hd,out.range,?_,?_⟩
  · have hI:zsE L (I →₀ L)=inputSize g M z t:= by
      rw [Module.finrank_finsupp_self,idx_card]
      simp only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,stock,inputSize]
      ac_rfl
    have hJ:zsE L (J→L)=stock (z+h) (t+h)*j3 (a+b) E := by
      rw [zvt,idx_card]
      dsimp only [w]
      rw [jO _ _ _ hab,stock]
      ac_rfl
    rw [LinearMap.finrank_range_of_inj ho]
    have htest :=q0.finrank_range_add_finrank_ker
    have hle :=q0.range.finrank_le
    rw [hI] at htest
    rw [hJ] at hle
    change inputSize g M z t≤zsE L q0.ker+stock (z+h) (t+h)*j3 (a+b) E
    omega
  · intro G hG
    obtain ⟨H,rfl⟩:=hG
    have hs {m:Exps} (hm:m∈(rows H.val).support) :=
      mem_coord.mp (rows_support H.val hm)
    have hf {m:Exps} (hm:m∈f.support) :=
      in_caps ((asl c F).trans_le he) (shift_rect c hr) hm
    have q1 {m:Exps} (hm:m∈(cut H.val).support) :
        m none<E+1∧m xvar<M∧m (seed 0)≤z+h∧m (seed 1)≤t+h:= by
      have hh:=rem_support hm
      have hy :=product_coord hh.1 (fun _ ht=>zeh (hs ht).1)
        (fun _ ht=>(hf ht).1)
      refine ⟨zB1 (by simpa only [E,Nat.add_comm] using hy),hh.2,?_,?_⟩
      · exact product_coord hh.1 (fun _ ht=>(hs ht).2.2.1) (fun _ ht=>(hf ht).2.1)
      · exact product_coord hh.1 (fun _ ht=>(hs ht).2.2.2) (fun _ ht=>(hf ht).2.2)
    have narrow {m:Exps} (hm:m∈(cut H.val).support) :m xvar+w (m none)<M:= by
      obtain ⟨hy,hx,hz,ht⟩:=q1 hm
      by_contra! hn
      have htop:M-1-m xvar<w (m none) := by omega
      let j:J:=⟨⟨⟨m none,hy⟩,⟨M-1-m xvar,htop⟩⟩,
        ⟨m (seed 0),zB1 hz⟩,⟨m (seed 1),zB1 ht⟩⟩
      have hj:q2 j=m:= by
        change exps (m none) (M-1-(M-1-m xvar)) _=m
        rw [show M-1-(M-1-m xvar)=m xvar by omega]
        exact exps_eta m
      have hz :=congrFun (LinearMap.mem_ker.mp H.property) j
      change (cut H.val).coeff (q2 j)=0 at hz
      exact qz0.mp hm (hj ▸ hz)
    let P:=unflat (rows H.val)
    let Q:=unflat (cut H.val)
    let B:=unflat ((rows H.val*f).divMonomial (Finsupp.single xvar M))
    have hp:P.natDegree≤g:=(out_caps (z :=z) (t:=t) (F:=P) (by
      change ∀ m∈(flatten (flatten.symm (rows H.val))).support,_
      rw [RingEquiv.apply_symm_apply]
      intro m hm
      exact ⟨zeh (hs hm).1,(hs hm).2.2⟩)).1
    have hq (m:Exps) (hm:m∈(flatten Q).support) :m∈(cut H.val).support := by
      change m∈(flatten (flatten.symm (cut H.val))).support at hm
      rwa [RingEquiv.apply_symm_apply] at hm
    obtain ⟨hqdeg,hqr⟩:=out_caps (F:= Q) (E :=E) (z :=z+h) (t:=t+h) (fun m hm =>
      ⟨zeh (q1 (hq m hm)).1,(q1 (hq m hm)).2.2⟩)
    have hpad:Padded a b E M Q:=⟨hqdeg,fun j m hm=> by
      have hh:=narrow (hq _ (lead_mem hm))
      rw [exps_x,exps_y] at hh
      simpa only [w,Nat.add_assoc] using hh⟩
    have hX:flatten (amm (z7y^M))=z9v xvar^M:= by
      rw [map_pow,map_pow]
      exact congrArg (fun x :Flat=>x^M) flatten_X
    have q3:shift c F*P= Q+amm (z7y^M)*B:= by
      apply flatten.injective
      rw [map_mul,map_add,map_mul,hX]
      change f*flatten (flatten.symm (rows H.val)) =
        flatten (flatten.symm (cut H.val))+_ *flatten (flatten.symm _)
      simp only [RingEquiv.apply_symm_apply]
      rw [mul_comm f]
      exact rem_eq M _
    have hB:B.natDegree≤E := by
      have hpq: (shift c F*P).natDegree≤E :=
        natDegree_mul_le_of_le ((asl c F).trans_le he) hp
      have hm: (amm (z7y^M)*B).natDegree≤E := by
        rw [show amm (z7y^M)*B=shift c F*P-Q by rw [q3]; abel]
        simpa only [max_self] using natDegree_sub_le_of_le hpq hqdeg
      change (C (qz2 ((z7y:L[X])^M))*B).natDegree≤E at hm
      rwa [natDegree_C_mul (MvPolynomial.C_ne_zero.mpr (pow_ne_zero _ X_ne_zero))] at hm
    change Padded a b E M (shift (-c) Q)∧sk (z+h) (t+h) (shift (-c) Q)∧_
    refine ⟨shift_pad (-c) hpad,shift_rect (-c) hqr,shift (-c) P,shift (-c) B,
      (asl _ _).trans_le hB,?_⟩
    have hh:=congrArg (shift (-c)) q3
    rw [map_mul,shift_shift,map_add,map_mul,shift_physical,
      taylor_X_pow,C_neg,← sub_eq_add_neg] at hh
    exact hh
end
end qHDgEWd
end
end
