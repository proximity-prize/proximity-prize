import ProximityPrize.SubmissionLower.Z9Rfpte
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.ZVQ2TVd
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qQCEOid
noncomputable section
open Polynomial Matrix
open cu (Shape)


open aeL (Offset)
open scoped BigOperators Polynomial Matrix
def c1 :Prop :=
  ∀ (F:Type) [Field F] (s :Shape) (t:Offset s) (u:ℕ) (a b c:F),b≠0 →
    (seedMatrix s t u a b c).rank ≤ ∑ k∈Finset.range (s.B+u+1),
      (windowMatrix F s t u k).rank
def c2 :Prop :=
  ∀ (F:Type) [Field F] [CharP F K1.p] (s :Shape) (t:Offset s) (u k :ℕ),
    s.J≤ s.B→s.B<K1.p→(windowMatrix F s t u k).rank≤windowBudget s t u k
private theorem packed_tests {F V I:Type} [Field F] [AddCommMonoid V] [Module F V]
    [Fintype I] {R:I→Type} [∀ i,Fintype (R i)]
    (f : (i:I)→V →ₗ[F] (R i→F)) (d:I→ℕ)
    (hd : ∀ i,Module.finrank F (LinearMap.range (f i))≤d i)
    {n:ℕ} (hn: (∑ i,d i)≤n) :
    ∃ tests :V →ₗ[F] (Fin n→F),∀ P,tests P=0 → ∀ i,f i P=0:= by
  classical
  let T:=Σ i:I,Fin (Module.finrank F (LinearMap.range (f i)))
  have hT:Fintype.card T≤n:= by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact (Finset.sum_le_sum fun i _=>hd i).trans hn
  let e :T ↪ Fin n :=
    (Fintype.equivFin T).toEmbedding.trans (Fin.castLEEmb hT)
  let g (i:I) :=(Module.finBasis F (LinearMap.range (f i))).equivFun
  let eval (t:T) :V →ₗ[F] F :=
    (LinearMap.proj t.2).comp ((g t.1).toLinearMap.comp (f t.1).rangeRestrict)
  let tests :V →ₗ[F] (Fin n→F) :=
    LinearMap.pi (Function.extend e eval (fun _=>0))
  refine ⟨tests,?_⟩
  intro P hP i
  have h (j:Fin (Module.finrank F (LinearMap.range (f i)))) :
      g i ((f i).rangeRestrict P) j=0:= by
    have hj:=congrFun hP (e ⟨i,j⟩)
    change Function.extend e eval (fun _=>0) (e ⟨i,j⟩) P=0 at hj
    rw [e.injective.extend_apply] at hj
    exact hj
  have hz :=(g i).injective (show g i ((f i).rangeRestrict P)=g i 0 by
    rw [map_zero]
    exact funext h)
  exact congrArg Subtype.val hz
theorem of_children (h1 :c1) (h2 :c2) :P5_7_4.c1 := by
  classical
  intro F _ _ s hJ hU hB α side a b c hb
  let I:=Offset s×Fin (s.U+1)
  let M (i:I) :=seedMatrix s i.1 (s.U-i.2.val) a b c
  let f (i:I) :=(M i).mulVecLin.comp (sourceVector (t:=i.1) α side i.2)
  have h (i:I) :Module.finrank F (LinearMap.range (f i)) ≤
      seedBudget s i.1 (s.U-i.2.val) := by
    refine (Submodule.finrank_mono (LinearMap.range_comp_le_range
      (sourceVector (t:=i.1) α side i.2) (M i).mulVecLin)).trans ?_
    change (M i).rank≤_
    exact (h1 F s i.1 _ a b c hb).trans
      (Finset.sum_le_sum fun k _=>h2 F s i.1 _ k hJ hB)
  have hn: (∑ i:I,seedBudget s i.1 (s.U-i.2.val))≤P5_7_4.poleRank s := by
    rw [Fintype.sum_prod_type]
    exact (count_budget s hU).le
  obtain ⟨tests,htests⟩:=packed_tests f _ h hn
  exact ⟨tests,fun P hP hz =>
    normalized s α side a b c hb P hP (fun t r=>htests P hz (t,r))⟩
end
end qQCEOid
