import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.AW
set_option Elab.async false
set_option autoImplicit true
section
namespace baV
open ac5

open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bhG {α R:Type*} [Fintype α] [AddCommMonoid R]
   (P:α→Prop) [DecidablePred P] (f :α→R) (a :α) [DecidableEq α] :
   (∑ b : {x // P x},if b.val=a then f b.val else 0) =
     if P a then f a else 0:= by
 by_cases ha :P a
 · rw [ite_eq_left ha,Fintype.sum_eq_single (⟨a,ha⟩ : {x // P x})]
   · simp
   · intro b hb
     exact ite_eq_right (fun h=>hb (Subtype.ext h))
 · rw [ite_eq_right ha]
   refine Finset.sum_eq_zero fun b _=>ite_eq_right ?_
   exact fun h=>ha (h ▸ b.property)
private theorem ao5 {α β F:Type*} [Fintype α] [Fintype β] [Field F]
    (M:Matrix α β F) (P:α→Prop) (Q:β→Prop) [DecidablePred P] [DecidablePred Q]
    (hM : ∀ a b,M a b≠0→P a∨Q b) :
    M.rank≤Fintype.card {a // P a} + Fintype.card {b // Q b} := by
  classical
  let W := {a // P a} ⊕ {b // Q b}
  let A:Matrix α W F:= fun a=>Sum.elim
    (fun i=>if i.val=a then 1 else 0)
    (fun j=>if P a then 0 else M a j.val)
  let B:Matrix W β F:= fun i b=>i.elim
    (fun j=>M j.val b)
    (fun j=>if j.val=b then 1 else 0)
  have hAB:A*B=M:= by
    ext a b
    rw [Matrix.mul_apply,Fintype.sum_sum_type]
    simp only [A,B,Sum.elim_inl,Sum.elim_inr,
      ite_mul,mul_ite,one_mul,zero_mul,mul_one,mul_zero]
    rw [bhG P (fun i=>M i b),bhG Q (fun j=>if P a then 0 else M a j)]
    by_cases ha :P a
    · simp [ha]
    · by_cases hb:Q b
      · simp [ha,hb]
      · have hz :M a b=0:= by
          by_contra hn
          exact (hM a b hn).elim ha hb
        simp [ha,hb,hz]
  calc
    M.rank=(A*B).rank :=congrArg Matrix.rank hAB.symm
    _≤A.rank :=Matrix.rank_mul_le_left A B
    _≤Fintype.card W:=Matrix.rank_le_card_width A
    _ = _:=Fintype.card_sum
def above (t u v w z c:ℕ) :Prop :=w≤z - 2*c∧(v≤ c∨(t≤z∧u≤ c))
instance (t u v w z c:ℕ) :Decidable (above t u v w z c) := by
 unfold above
 infer_instance
private def order (e :Fin 4 →₀ ℕ) :ℕ:=e 2+2*e 3
end baV
end
section
namespace axF
open ac5 baV
open scoped BigOperators Matrix
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
abbrev F:=ZMod P1.p
private theorem av7 {A B K:Type*} [Fintype A] [Fintype B] [Field K]
   [DecidableEq A] (M:Matrix A B K) (i:A) (l:A→K) (hi:l i=1) :
   (M.updateRow i (l ᵥ* M)).rank=M.rank := by
 have he : (1 :Matrix A A K).updateRow i l*M=M.updateRow i (l ᵥ* M) := by
   rw [Matrix.updateRow_mul,Matrix.one_mul]
 have hd: ((1 :Matrix A A K).updateRow i l).det≠0:= by
   have hs : (∑ k :A,l k•(1 :Matrix A A K) k)=l:= by
     funext j
     simp [Matrix.one_apply,mul_ite,eq_comm]
   rw [← hs,Matrix.det_updateRow_sum,hi,one_smul,Matrix.det_one]
   exact one_ne_zero
 rw [← he,Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hd]
private theorem aPK {A B K:Type*} [Fintype A] [Fintype B] [Field K]
  [DecidableEq B] (M:Matrix A B K) (j:B) (v :B→K) (hj:v j=1) :
  (M.updateCol j (M *ᵥ v)).rank=M.rank := by
 rw [← Matrix.rank_transpose (M.updateCol j _),← Matrix.updateRow_transpose,
  ← Matrix.vecMul_transpose,av7 _ _ _ hj,Matrix.rank_transpose]
private theorem ajw {A:Type*} [Fintype A] (P:A→Prop)
  [DecidablePred P] [DecidableEq A] (i:A) (hi:P i) :
  Fintype.card {a // P a∧a≠i} < Fintype.card {a // P a} := by
 refine Fintype.card_lt_of_injective_of_notMem
  (fun a : {a // P a∧a≠i} => (⟨a.val,a.property.1⟩ : {a // P a}))
  (fun a b h=>Subtype.ext (congrArg (fun a : {a // P a} => a.val) h)) (b:=⟨i,hi⟩) ?_
 rintro ⟨a,ha⟩
 exact a.property.2 (congrArg (fun a : {a // P a} => a.val) ha)
end
end axF
end
section
namespace axF
open scoped BigOperators
open ac5 baV
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000
def aaN (b c b' c' : ℕ) :ℤ :=
 ju.n9 b b' * (ju.n9 c c' : ℤ)
end axF
end
section
namespace axF
open ac5
open scoped Matrix BigOperators
noncomputable section
private def XA {ι α:Type*} [Fintype ι] (f :ι→α) (w:ι→F) (a :α) :F :=
 by classical exact ∑ i,if f i=a then w i else 0
private theorem asf {ι α:Type*} [Fintype ι] (f :ι→α) (w:ι→F)
   (hf :Function.Injective f) (i:ι) :XA f w (f i)=w i:= by
 classical
 simp only [ XA,hf.eq_iff]
 rw [Finset.sum_eq_single i]
 · simp
 · simp +contextual
 · simp
private theorem ab7 {ι α:Type*} [Fintype ι] [Fintype α]
   (f :ι→α) (w:ι→F) (v :α→F) :
   XA f w ⬝ᵥ v = ∑ i,w i*v (f i) := by
 classical
 simp only [dotProduct,XA,Finset.sum_mul]
 rw [Finset.sum_comm]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [Finset.sum_eq_single (f i)]
 · simp
 · intro a _ ha
   simp [Ne.symm ha]
 · simp
private theorem awG {A:Type*} [AddCommMonoid A] (n:ℕ) (width :ℕ→ℕ)
   (f :ℕ→ℕ→A) :
   (∑ i:Σ a :Fin n,Fin (width a.val),f i.1 i.2) =
     ju.total (fun a=>ju.total (f a) (width a)) n:= by
 rw [← Finset.univ_sigma_univ,Finset.sum_sigma,ju.abt,← Fin.sum_univ_eq_sum_range]
 exact Finset.sum_congr rfl fun a _=> by
   rw [ju.abt,← Fin.sum_univ_eq_sum_range]
private theorem cast_zero {a :ℤ} (h:a % (P1.p:ℤ)=0) : (a :F)=0 :=
 (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h)
end
end axF
end
