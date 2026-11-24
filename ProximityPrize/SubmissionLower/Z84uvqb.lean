import ProximityPrize.SubmissionLower.ZPSk6xb
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qZCRTge
noncomputable section
open Polynomial
open P5_7 (WitnessOK normalWidth)
open P5_7_7
open cu (L)
open private embed_bound from ProximityPrize.SubmissionLower.ZsWhgLc
def c1 :Prop :=
  ∀ (F:Dg) (g h v M:ℕ),
    F≠0→0<M→(∀ i,(F.coeff i).natDegree≤h) →
    ∃ (a :L) (R: (ax0 g v (fun _=>M)→L) →ₗ[L] Dg),
      Function.Injective R ∧ ∀ q,
        Boxed (R q) (F.natDegree+g) (v+h) (fun _=>M) ∧
        ∃ B:Dg,B.natDegree≤F.natDegree+g ∧
          pack g v (fun _=>M) q*F =
            R q+C (C (((Polynomial.X:L[X]) - C a)^M))*B
def c2 :Prop :=
  ∀ (F G:Dg) (g T u s W M:ℕ),
    Irreducible F→ Irreducible (embed F)→0<F.natDegree →
    (∃ i j,(F.coeff i).coeff j≠0 ∧
      W<((F.coeff i).coeff j).natDegree+F.natDegree*u+i*s) →
    G.natDegree≤F.natDegree+g→(∀ i,(G.coeff i).natDegree≤T) →
    P5_7_7R.atm G (F.natDegree+g) u s M →
    ¬ IsCoprime (ek (embed F)) (ek (embed G)) →
    ∃ Q:Dg,G=F*Q∧Boxed Q g T (fun i=>M-(W+1)-(g*u+i*s))
private theorem boxed_bounds {G:Dg} {e T M:ℕ}
  (hb:Boxed G e T (fun _=>M)) :
  G.natDegree≤e ∧ ∀ i,(G.coeff i).natDegree≤T:= by
 have h (i j:ℕ) (hn: (G.coeff i).coeff j≠0) :i≤e∧j≤T :=
  let ⟨hi,hj,_⟩:=hb i j _ (leadingCoeff_ne_zero.mpr hn)
  ⟨hi,hj⟩
 exact ⟨natDegree_le_iff_coeff_eq_zero.mpr fun i hi=> by
  by_contra hn
  exact hi.not_ge (h i _ (leadingCoeff_ne_zero.mpr hn)).1,
  fun i=>natDegree_le_iff_coeff_eq_zero.mpr fun j hj=> by
    by_contra hn
    exact hj.not_ge (h i j hn).2⟩
private theorem narrow {G:Dg} {e T u s M:ℕ}
   (hb:Boxed G e T (fun _=>M))
   (hz : ∀ r :ax0 e T (fun i=>e*u+i*s),
     cf G r.1.1 r.2 (M-(e*u+(r.1.1 :ℕ)*s)+(r.1.2 :ℕ))=0) :
   P5_7_7R.atm G e u s M:= by
 intro i j h
 let k :=((G.coeff i).coeff j).natDegree
 have hn:cf G i j k≠0:=leadingCoeff_ne_zero.mpr h
 obtain ⟨hi,hj,hk⟩:=hb i j k hn
 change k<M at hk
 by_contra hh
 change ¬ k+e*u+i*s<M at hh
 let a :=M-(e*u+i*s)
 let r :ax0 e T (fun i=>e*u+i*s) :=
   (⟨⟨i,by omega⟩,⟨k-a,by dsimp [a]; omega⟩⟩,⟨j,by omega⟩)
 have hr :=hz r
 change cf G i j (a+(k-a))=0 at hr
 rw [show a+(k-a)=k by dsimp [a]; omega] at hr
 exact hn hr
theorem of_children (h₁:c1) (h₂:c2) :qyWKMud.c2 := by
 classical
 intro D w U S J F l h x hf he hl hl₂ hh hF hok hbelow
 dsimp only
 subst l
 let l:=F.natDegree
 let g:=x.g
 let u:=J.u₀
 let s :=J.u₁-J.u₀
 let E :=l+g
 let M:=x.W+1+x.j*normalWidth D
 let v :=x.c*h
 let T:=v+h
 have hw:2*u+s=normalWidth D:= by
   have :=J.width
   have :=J.order
   dsimp [u,s]
   omega
 have hn:F.natDegree≠1 := by omega
 rw [WitnessOK,ite_eq_right hn] at hok
 obtain ⟨_,hj,_,_,hs,_,_,_⟩:=hok
 have hM:0<M:= by dsimp only [M]; omega
 have hT:T=(x.c+1)*h:= by dsimp [T,v]; ring
 have hlarge : ∃ i j,(F.coeff i).coeff j≠0 ∧
     x.W<((F.coeff i).coeff j).natDegree+l*u+i*s := by
   unfold Jm at hbelow
   push Not at hbelow
   exact hbelow
 obtain ⟨a,R,hR,hrem⟩:=h₁ F g h v M hf.ne_zero hM hF
 let top:= fun i:ℕ=>E*u+i*s
 let tail:= fun i:ℕ=>M-(x.W+1)-(g*u+i*s)
 let cuts : (ax0 g v (fun _=>M)→L) →ₗ[L] (ax0 E T top→L) :=
   LinearMap.pi fun r =>
     (cF0 r.1.1 r.2 (M-top r.1.1+(r.1.2 :ℕ))).comp R
 let good:cuts.ker →ₗ[L] Dg:=R.comp cuts.ker.subtype
 let bad: (ax0 g T tail→L) →ₗ[L] Dg :=
   (LinearMap.mulLeft L F).comp (pack g T tail)
 have narrow_good (q:cuts.ker) :P5_7_7R.atm (R q.val) E u s M:= by
   apply narrow (hrem q.val).1
   exact congrFun (LinearMap.mem_ker.mp q.property)
 suffices hex : ∃ q:cuts.ker,IsCoprime (ek (embed F)) (ek (embed (R q.val))) by
   obtain ⟨q,hq⟩:=hex
   obtain ⟨hb,B,hB,hrel⟩:=hrem q.val
   obtain ⟨hG,hseed⟩:=boxed_bounds hb
   refine ⟨a,pack g v (fun _=>M) q.val,R q.val,B,hrel,hG,hB,?_,narrow_good q,hq⟩
   apply embed_bound
   intro i
   rw [← hT]
   exact hseed i
 by_contra hnone
 have hsub:LinearMap.range good≤LinearMap.range bad:= by
   rintro G ⟨q,rfl⟩
   have hnot : ¬ IsCoprime (ek (embed F)) (ek (embed (R q.val))) :=
     fun hq=>hnone ⟨q,hq⟩
   obtain ⟨hdeg,hseed⟩:=boxed_bounds (hrem q.val).1
   obtain ⟨Q,hQ,hbox⟩:=h₂ F (R q.val) g T u s x.W M hf he (by omega)
     hlarge hdeg hseed (narrow_good q) hnot
   obtain ⟨b,hb⟩:=exists_pack hbox
   exact ⟨b,by change F*pack g T tail b=R q.val; rw [hb,← hQ]⟩
 have hdim:=cuts.finrank_range_add_finrank_ker
 have hcon :=cuts.range.finrank_le
 have hbadrank :Module.finrank L cuts.ker≤Module.finrank L (ax0 g T tail→L) := by
   rw [← LinearMap.finrank_range_of_inj (f :=good) (hR.comp Subtype.val_injective)]
   exact (Submodule.finrank_mono hsub).trans bad.finrank_range_le
 rw [slot_rank] at hdim hcon hbadrank
 have ht:=top_count E u s
 rw [hw] at ht
 change (∑ i:Fin (E+1),top i)= _ at ht
 rw [ht] at hcon
 have hb:=tail_count g x.j u s hj
 rw [hw] at hb
 have htail: (∑ i:Fin (g+1),tail i)≤normalWidth D*x.j*(x.j+1)/2 := by
   simpa only [tail,M,Nat.add_sub_cancel_left] using hb
 have hbd:=hbadrank.trans (Nat.mul_le_mul_right (T+1) htail)
 simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hdim
 change (x.c+1)*(normalWidth D*E*(E+1)/2+normalWidth D*x.j*(x.j+1)/2) <
   (g+1)*x.c*M at hs
 have hstrict :=scale_surplus ((g+1)*M)
   (normalWidth D*E*(E+1)/2+normalWidth D*x.j*(x.j+1)/2) x.c h hh
   (by simpa only [mul_assoc,mul_left_comm x.c] using hs)
 rw [Nat.add_mul,← hT] at hstrict
 change _<((g+1)*M)*(v+1) at hstrict
 omega
end
end qZCRTge
