import ProximityPrize.SubmissionLower.ZGtaALd
set_option Elab.async false
set_option autoImplicit true
namespace qkgz7gb
noncomputable section
open Polynomial Finset
open P5 (K p)


open Dt (Reduced)
open cu (Equation vm yq)
open Y3 (ek)




open scoped Classical
def c1 :Prop :=
  ∀ D e u (w:Witness),FilterOK D e u w →
    ∀ (T:Finset K) (z :K→K) (S:K→K[X]),
      (∀ γ∈T,(S γ).natDegree≤D) →
      ∀ f :Equation,Reduced f→f.natDegree≤e→vm f u →
        (∀ γ∈T,yq f (z γ) (S γ)=0) →
        ∃ low high G:Equation,
          f=low*high∧LowWeight D w.weight low∧G≠0∧G.natDegree≤e+w.g ∧
          (w.stock.cUr u).fits G∧IsCoprime (ek high) (ek G) ∧
          ∀ γ∈T,yq G (z γ) (S γ)=0
def c2 :Prop :=
  ∀ D e u W s,CurveOK D e W s →
    ∀ word (T:Finset K) z S,UJ D word T z S →
      ∀ f :Equation,Reduced f→f.natDegree≤e→vm f u→LowWeight D W f →
        (∀ γ∈T,yq f (z γ) (S γ)=0)→SmoothCount T z (smoothRate D e u W s)
def c3:Prop :=
  ∀ (T:Finset K) z B,Set.InjOn z (T:Set K)→0<B→2*B<p→SmoothCount T z B →
    ∃ q:PlaneCurve,q≠0∧q.totalDegree≤2*B-1 ∧ ∀ γ∈T,q.eval (rV z γ)=0
def c4 :Prop :=
  ∀ (T:Finset K) z,Set.InjOn z (T:Set K) →
    ∀ q:PlaneCurve,Irreducible q→q.totalDegree<p →
      (T.filter fun γ=>q.eval (rV z γ)=0 ∧ ¬ SmoothAt q (rV z γ)).card ≤
        (q.totalDegree-1)*(q.totalDegree-2)/2
private theorem singular_add (a b:ℕ) :
    (a-1)*(a-2)/2+(b-1)*(b-2)/2≤(a+b-1)*(a+b-2)/2 := by
  have h (x y :ℕ) :x/2+y/2≤(x+y)/2 := by omega
  apply (h _ _).trans (Nat.div_le_div_right ?_)
  calc
    _≤(a-1)*(a+b-2)+(b-1)*(a+b-2) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ (by omega))
    _=((a-1)+(b-1))*(a+b-2) :=(Nat.add_mul _ _ _).symm
    _≤_:=Nat.mul_le_mul_right _ (by omega)
private theorem eLM (interpolate :c3) (singular :c4)
    {T:Finset K} {z :K→K} {B:ℕ} (hz :Set.InjOn z (T:Set K))
    (hB:0<B) (hp:2*B<p) (hs :SmoothCount T z B) :
    T.card≤planeFee B:= by
  obtain ⟨q,hq,hd,hr⟩:=interpolate T z B hz hB hp hs
  have count (q:PlaneCurve) (hq:q≠0) (hd:q.totalDegree<p)
      (U:Finset K) (hU:U⊆T) (hr : ∀ γ∈U,q.eval (rV z γ)=0) :
      U.card≤B*q.totalDegree+(q.totalDegree-1)*(q.totalDegree-2)/2 := by
    revert hq hd U hU hr
    induction q using WfDvdMonoid.induction_on_irreducible with
    | zero =>
      intro h
      exact (h rfl).elim
    | unit q hu =>
      intro _ _ U _ hU
      have he :U = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ =>
        (hu.map (MvPolynomial.eval (rV z γ))).ne_zero (hU γ hγ)
      simp [he]
    | mul a q ha hq ih =>
      intro _ hd U hU hr
      let V:=U.filter fun γ=>q.eval (rV z γ)=0
      have hV:V⊆U:=filter_subset _ _
      let W:=U \ V
      have hW:W⊆U:=sdiff_subset
      have ht:=MvPolynomial.totalDegree_mul_of_isDomain hq.ne_zero ha
      rw [ht] at hd ⊢
      have hR (γ:K) (hγ:γ∈W) :a.eval (rV z γ)=0:= by
        have hm:=hr γ (hW hγ)
        rw [map_mul] at hm
        exact (mul_eq_zero.mp hm).resolve_left fun h =>
          (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hW hγ,h⟩)
      have hA:=ih ha (by omega) W (hW.trans hU) hR
      have hS:=singular V z (hz.mono (hV.trans hU)) q hq (by omega)
      have hSm: (V.filter fun γ=>SmoothAt q (rV z γ)).card≤B*q.totalDegree :=
        (card_le_card (filter_subset_filter _ (hV.trans hU))).trans (hs q hq)
      have hbad:V.filter (fun γ => ¬ SmoothAt q (rV z γ)) =
          V.filter (fun γ=>q.eval (rV z γ)=0 ∧ ¬ SmoothAt q (rV z γ)) := by
        ext γ
        simp only [mem_filter]
        exact ⟨fun ⟨hv,hn⟩=>⟨hv,(mem_filter.mp hv).2,hn⟩,fun ⟨hv,_,hn⟩=>⟨hv,hn⟩⟩
      have hpart:=card_filter_add_card_filter_not (s :=V) (fun γ=>SmoothAt q (rV z γ))
      rw [hbad] at hpart
      have hVb:V.card≤B*q.totalDegree+(q.totalDegree-1)*(q.totalDegree-2)/2 :=
        hpart ▸ Nat.add_le_add hSm hS
      have hC:W.card+V.card=U.card:=card_sdiff_add_card_eq_card hV
      have hab:=hC ▸ Nat.add_le_add hA hVb
      have hsum:=singular_add q.totalDegree a.totalDegree
      rw [Nat.mul_add]
      omega
  have hcount:=count q hq (hd.trans_lt (by omega)) T (Subset.refl _) hr
  have hsing: (q.totalDegree-1)*(q.totalDegree-2)≤(2*B-1-1)*(2*B-1-2) :=
    Nat.mul_le_mul (Nat.sub_le_sub_right hd 1) (Nat.sub_le_sub_right hd 2)
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.div_le_div_right hsing))
end
end qkgz7gb
