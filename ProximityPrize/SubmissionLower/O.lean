import ProximityPrize.SubmissionLower.B
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix gR ProximityPrize.Benchmark
open scoped BigOperators
theorem a7J {u:e9} (T:qo u) :
  L+T.height+R5 u=t+1 := by
 exact kL.c75 k L t (R5 u) T.a T.b T.c
  (by decide) T.top T.degreeSum (by have :=T.nullitySum; omega)
theorem aEz {u:e9} (hu:abC u) (T:qo u) :
  T.height≤DY:= by
 have h:=a7J T
 have hr :=hu.1
 dsimp only [L,t,DY,blockLength,dw,k,b39] at h hr ⊢
 omega
def c78 {u:e9} (hu:abC u) (T:qo u) :
    Relation T:= by
  have hline :=kL.b4H p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1≤t by decide).trans_lt T.inactive) T.level
  have hH :=aEz hu T
  apply kL.c4L p (by decide)
    node (u 0) (u 1) node.injective Native.ahU
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [yP.FM.a5W]
  exact (Nat.mul_le_mul_right p (show 2*T.height+2≤2*DY+2 by omega)).trans_lt
    (by decide)
private theorem diA {F ι:Type}
  [Field F] [Fintype ι] [DecidableEq ι] (x u v :ι→F) (hx :Function.Injective x)
  (k a p:ℕ) (hk :k≤Fintype.card ι) (hp:1<p)
  (htype :Principal.bTJ x u v k p)
  (Γ:Finset F) (hΓ : ∀ γ∈Γ,Principal.akD x u v k a γ) :
  Γ.card≤1 :=
 Principal.gE1 x hx u v k a p hk hp htype Γ hΓ
variable {F ι:Type} [Field F] [Fintype ι] [DecidableEq ι]
private theorem dMQ (p:ℕ) (x u v :ι→F) (L t:ℕ)
    (c:Fin (t+1)→F) (hc: (ayo p x u v L t).mulVec c=0) :
    (AI p x u v L t).mulVec (fun j=>C (c j))=0:= by
  funext i
  have h0:=congrFun hc (0,i.2)
  have h1 :=congrFun hc (1,i.2)
  have h2 :=congrFun hc (2,i.2)
  have h3:=congrFun hc (3,i.2)
  simp only [Matrix.mulVec,dotProduct,ayo,Fin.reduceEq,
    ite_true,ite_false,Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi:i.1=0
  · simp only [Matrix.mulVec,dotProduct,AI,hi,ite_true,QO,Pi.zero_apply]
    calc
      _=C (∑ j,oX x u (i.2.val+j.val)*c j) +
          Polynomial.X (R:=F)*C (∑ j,oX x v (i.2.val+j.val)*c j) := by
        rw [map_sum,map_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _=0:= by simp only [h0,h1,map_zero,mul_zero,add_zero]
  · simp only [Matrix.mulVec,dotProduct,AI,hi,ite_false,Pi.zero_apply]
    calc
      _=C (∑ j,oX x u (i.2.val+j.val)^p*c j) +
          Polynomial.X (R:=F)^p*C (∑ j,oX x v (i.2.val+j.val)^p*c j) := by
        rw [map_sum,map_sum,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _=0:= by simp only [h2,h3,map_zero,mul_zero,add_zero]
private theorem cHO {E :Type} [Field E]
   (φ:F[X] →+* E) (hφ:Function.Injective φ) (p:ℕ) [ExpChar F p] (hp:1≤p)
   (x :ι→F) (hx :Function.Injective x) (hfixed : ∀ i,x i^p=x i)
   (u v :ι→F) (k A L t:ℕ) (hkA:k<A) (hL:k+L=A)
   (ht:A+t=Fintype.card ι)
   (r :ℕ) (hgeneric: ((AI p x u v L t).map φ).rank=r)
   (hconstant: (ayo p x u v L t).rank=r)
   (Γ:Finset F) (hΓ : ∀ γ∈Γ,Principal.akD x u v k A γ) :Γ.card≤p*r := by
 let M:=AI p x u v L t
 let C₀:=ayo p x u v L t
 let W:=LinearMap.ker C₀.mulVecLin
 obtain ⟨B⟩:=zQ.a3O φ M r hgeneric
 have hWdim:Module.finrank F W=t+1 - r := by
   have h:=LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
   change (ayo p x u v L t).rank+Module.finrank F W= _ at h
   rw [hconstant,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h
   omega
 have hW (c:Fin (t+1)→F) (hc:c∈W) :
     M.mulVec (fun j=>C (c j))=0 :=
   dMQ p x u v L t c hc
 have hminor : (zQ.pivot B).det.natDegree≤p*r := by
   have h:=zQ.aVV φ M r B (fun _=>p) (by
     intro i j
     exact (a8L p x u v L t i j).trans (by split_ifs <;> omega))
   simpa [Nat.mul_comm] using h
 exact Principal.cHT p x hx hfixed u v k A L t (p*r) hkA hL ht
   _ B.minor_ne hminor (Principal.cHM φ hφ p x u v L t r B W hWdim hW)
   Γ hΓ
open bai
private def aDU (u:e9) :Fin 2→ℕ→kB :=
 fun b j=>algebraMap K[X] kB (Principal.P8 p node (u 0) (u 1) b j)
private theorem cU4 (u:e9)
  (h : ¬ aB8 u) :bzl (aDU u) k := by
 classical
 unfold bzl
 by_contra! hall
 apply h
 unfold aB8 Principal.bTJ
 rw [IRSProfile.card_index]
 intro i j
 apply IsFractionRing.injective K[X] kB
 simpa [aDU,Principal.P8,map_mul] using hall i j
end
end P0
end
