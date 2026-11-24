import ProximityPrize.SubmissionLower.Z1qPXJc
set_option Elab.async false
section
namespace qHJDQEb
noncomputable section
open scoped Classical
open Finset
open cu (L)
open q8Z6NHc (Slot)
open qAW6lac (Index jo aMp Vanishes)
section
variable {F:Type} [CommRing F] {d D W:ℕ}
private theorem eval_split (u:Slot d D W→F) (x y :F) :
    aMp u x y =
      (∑ i∈univ.erase (zeroSlot d D W),u i*x^i.val.2.val*y^i.val.1.val) +
        u (zeroSlot d D W) := by
  have h:=sum_erase_add univ (fun i:Slot d D W=>u i*x^i.val.2.val*y^i.val.1.val)
    (mem_univ (zeroSlot d D W))
  simp [aMp,zeroSlot] at *
private theorem eval_adjust (u:Slot d D W→F) (x y :F) :
   aMp (adjust u x y) x y=0:= by
 rw [eval_split]
 have hh: (∑ i∈univ.erase (zeroSlot d D W),
     adjust u x y i*x^i.val.2.val*y^i.val.1.val) =
     ∑ i∈univ.erase (zeroSlot d D W),u i*x^i.val.2.val*y^i.val.1.val := by
   apply sum_congr rfl
   intro i hi
   simp [adjust,(mem_erase.mp hi).1]
 have hconst:adjust u x y (zeroSlot d D W) =
     u (zeroSlot d D W)-aMp u x y := by simp [adjust]
 rw [hh,hconst,eval_split u]
 ring
private theorem eval_unique {u v :Slot d D W→F} {x y :F}
    (hu:aMp u x y=0) (hv :aMp v x y=0)
    (he : ∀ i,i≠zeroSlot d D W→u i=v i) :u=v := by
  funext i
  by_cases hi:i=zeroSlot d D W
  · subst i
    have hh: (∑ j∈univ.erase (zeroSlot d D W),u j*x^j.val.2.val*y^j.val.1.val) =
        ∑ j∈univ.erase (zeroSlot d D W),v j*x^j.val.2.val*y^j.val.1.val := by
      apply sum_congr rfl
      intro j hj
      rw [he j (mem_erase.mp hj).1]
    rw [eval_split,hh] at hu
    rw [eval_split] at hv
    exact add_left_cancel (hu.trans hv.symm)
  · exact he i hi
end
private theorem map_blockEval {A F:Type} [CommRing A] [CommRing F] (φ:A →+* F)
  {d D W:ℕ} (u:Slot d D W→A) (x y :A) :
  φ (aMp u x y)=aMp (fun i=>φ (u i)) (φ x) (φ y) := by
 simp [aMp,map_sum,map_mul,map_pow]
private theorem map_adjust {A F:Type} [CommRing A] [CommRing F] (φ:A →+* F)
  {d D W:ℕ} (u:Slot d D W→A) (x y :A) (i:Slot d D W) :
  φ (adjust u x y i)=adjust (fun j=>φ (u j)) (φ x) (φ y) i:= by
 by_cases hi:i=zeroSlot d D W <;> simp [adjust,hi,map_blockEval]
theorem incidence_roots (d D W:ℕ) :
    aMp (fun i=>atInc (.inl i)) (pointX d D W) (pointY d D W)=0 ∧
    aMp (fun i=>atInc (.inr (.inl i))) (pointX d D W) (pointY d D W)=0 ∧
    aMp (fun i=>atInc (.inr (.inr i))) (pointX d D W) (pointY d D W)=0:= by
  let j:=algebraMap (IncRing d D W) (Incident d D W)
  have root {e a :ℕ} (v :Slot e D a→ IncRing d D W) :
      aMp (fun i=>j (adjust v (coordX d D W) (coordY d D W) i))
        (j (coordX d D W)) (j (coordY d D W))=0:= by
    rw [← map_blockEval,eval_adjust,map_zero]
  exact ⟨root _,root _,root _⟩
theorem vanishes_iff_incidence {d D W:ℕ} (Q:jo d D W) :
    Vanishes Q↔incidence d D W Q=0:= by
  constructor
  · intro h
    exact h incCoeff (coordX d D W) (coordY d D W)
      (eval_adjust _ _ _) (eval_adjust _ _ _) (eval_adjust _ _ _)
  · intro h F _ _ u x y h0 h1 h2
    let φ:IncRing d D W →ₐ[L] F:=MvPolynomial.aeval fun
      | .inl false=>x
      | .inl true=>y
      | .inr j=>u j.val
    have hx :φ (coordX d D W)=x := by simp [φ,coordX]
    have hy :φ (coordY d D W)=y := by simp [φ,coordY]
    have bgA (i:Index d D W) (hi:IsFree i) :φ (raw i)=u i:= by
      simp [raw,hi,φ]
    have recover {e a :ℕ} (emb:Slot e D a→ Index d D W)
        (hf : ∀ i,i≠zeroSlot e D a→ IsFree (emb i))
        (hz :aMp (fun i=>u (emb i)) x y=0) (i:Slot e D a) :
        φ (adjust (fun j=>raw (emb j)) (coordX d D W) (coordY d D W) i)=u (emb i) := by
      have hm:φ (adjust (fun j=>raw (emb j)) (coordX d D W) (coordY d D W) i) =
          adjust (fun j=>φ (raw (emb j))) (φ (coordX d D W)) (φ (coordY d D W)) i :=
        map_adjust φ.toRingHom _ _ _ _
      rw [hm,hx,hy]
      refine congrFun (eval_unique (eval_adjust _ x y) hz (fun j hj => ?_)) i
      simp [adjust,hj,bgA _ (hf j hj)]
    have hu (i) :φ (incCoeff i)=u i:= by
      rcases i with i | (i | i)
      · exact recover Sum.inl (fun _ h' => h') h0 i
      · exact recover (fun j => .inr (.inl j)) (fun _ h' => h') h1 i
      · exact recover (fun j => .inr (.inr j)) (fun _ h' => h') h2 i
    have hh:=congrArg φ h
    change φ (MvPolynomial.aeval incCoeff Q)=φ 0 at hh
    rwa [MvPolynomial.comp_aeval_apply,show (fun i=>φ (incCoeff i))=u from funext hu,
      map_zero] at hh
theorem incidence_over_field {d D W:ℕ} (Q:jo d D W) :
  MvPolynomial.aeval atInc Q=0↔incidence d D W Q=0:= by
 let j:=IsScalarTower.toAlgHom L (IncRing d D W) (Incident d D W)
 have h:j (incidence d D W Q)=MvPolynomial.aeval atInc Q :=
  MvPolynomial.comp_aeval_apply incCoeff j Q
 rw [← h,← map_zero j]
 exact (IsFractionRing.injective (IncRing d D W) (Incident d D W)).eq_iff
end
end qHJDQEb
end
section
namespace qHJDQEb
noncomputable section
open scoped Classical
open cu (L)
open qAW6lac (Index block spectral)
private theorem fixed_or_free {d D W:ℕ} (i : {i:Index d D W // i≠spectral d D W})
   (hi : ¬IsFree i.val) :
   i.val = .inl (zeroSlot d D W)∨i.val = .inr (.inl (zeroSlot d D W)) := by
 rcases i with ⟨i,hs⟩
 rcases i with i | (i | i)
 · exact Or.inl (congrArg Sum.inl (by simpa [IsFree] using hi))
 · exact Or.inr (congrArg (fun j=>(Sum.inr (Sum.inl j) :Index d D W)) (by simpa [IsFree] using hi))
 · have he :i=zeroSlot (d-1) D (W-D) := by simpa [IsFree] using hi
   subst i
   exact (hs rfl).elim
private theorem projected_card_le (d D W:ℕ) :
   Cardinal.mk {i:Index d D W // i≠spectral d D W} ≤
     Cardinal.mk (Bool ⊕ Free d D W) := by
 let f : {i:Index d D W // i≠spectral d D W} → Bool ⊕ Free d D W:= fun i =>
   if h:IsFree i.val then .inr ⟨i.val,h⟩ else .inl (decide (block i.val=1))
 apply Cardinal.mk_le_of_injective (f :=f)
 intro i j hij
 by_cases hi:IsFree i.val <;> by_cases hj:IsFree j.val <;> simp [f,hi,hj] at hij
 · exact Subtype.ext hij
 · apply Subtype.ext
   rcases fixed_or_free i hi with h₁ | h₁ <;> rcases fixed_or_free j hj with h₂ | h₂
   · exact h₁.trans h₂.symm
   · simp [h₁,h₂,block] at hij
   · simp [h₁,h₂,block] at hij
   · exact h₁.trans h₂.symm
private theorem free_image {d D W:ℕ} (i:Free d D W) :
  atInc i.val=algebraMap (IncRing d D W) (Incident d D W) (MvPolynomial.X (.inr i)) := by
 rcases i with ⟨i,hi⟩
 rcases i with i | (i | i)
 all_goals
  have h' := hi
  simp only [IsFree] at h'
  simp [atInc,incCoeff,adjust,raw,h',hi]
theorem projected_independent {d D W:ℕ}
    (hx :IsIntegral (pairField d D W 2) (pointX d D W))
    (hy :pointY d D W∈pointField d D W 2) :
    AlgebraicIndependent L (projectedCoeff (d:=d) (D:=D) (W:=W)) := by
  let E :=Incident d D W
  let K:=pairField d D W 2
  let u:=projectedCoeff (d:=d) (D:=D) (W:=W)
  let H :=IntermediateField.adjoin L (Set.range u)
  have hle :K≤H := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,hi,rfl⟩
    have hs :i≠spectral d D W:= fun he=>hi (he.symm ▸ rfl)
    exact IntermediateField.subset_adjoin _ _ ⟨⟨i,hs⟩,rfl⟩
  let:Algebra K H :=(IntermediateField.inclusion hle).toRingHom.toAlgebra
  let:IsScalarTower K H E :=IsScalarTower.of_algebraMap_eq fun _=>rfl
  have hX:IsAlgebraic H (pointX d D W) :=hx.isAlgebraic.tower_top H
  have hY:IsAlgebraic H (pointY d D W) := by
    let:FiniteDimensional K (pointField d D W 2) :=
      IntermediateField.adjoin.finiteDimensional hx
    have h:=IsAlgebraic.of_finite K (⟨pointY d D W,hy⟩:pointField d D W 2)
    exact ((IntermediateField.isAlgebraic_iff).mp h).tower_top H
  let C:=(algebraicClosure H E).restrictScalars L
  let j:=IsScalarTower.toAlgHom L (IncRing d D W) E
  have hvar (i:Bool ⊕ Free d D W) :j (MvPolynomial.X i)∈C:= by
    rcases i with (_ | _) | i
    · exact mem_algebraicClosure_iff.mpr hX
    · exact mem_algebraicClosure_iff.mpr hY
    · have hs :i.val≠spectral d D W:= by
        intro hi
        have h:=hi ▸ i.property
        exact h rfl
      rw [show j (MvPolynomial.X (.inr i))=atInc i.val from (free_image i).symm]
      exact (algebraicClosure H E).algebraMap_mem
        ⟨_,IntermediateField.subset_adjoin _ _ ⟨⟨i.val,hs⟩,rfl⟩⟩
  have hr (q:IncRing d D W) :j q∈C:= by
    induction q using MvPolynomial.induction_on with
    | C a=>exact C.algebraMap_mem a
    | add p q hp hq=>simpa only [map_add] using C.add_mem hp hq
    | mul_X p i hp=>simpa only [map_mul] using C.mul_mem hp (hvar i)
  have halg:Algebra.IsAlgebraic H E := by
    apply (algebraicClosure.eq_top_iff H E).mp
    refine top_unique fun z _ => ?_
    obtain ⟨a,b,_,rfl⟩:=IsFractionRing.div_surjective (IncRing d D W) z
    exact C.div_mem (hr a) (hr b)
  let:Algebra.IsAlgebraic (Algebra.adjoin L (Set.range u)) E :=
    (IntermediateField.isAlgebraic_adjoin_iff_top (F:=L)).mp halg
  have hj:Function.Injective j:=IsFractionRing.injective (IncRing d D W) E
  have hind:=(MvPolynomial.algebraicIndependent_X (Bool ⊕ Free d D W) L).map' hj
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite L u
    ((projected_card_le d D W).trans hind.cardinalMk_le_trdeg)).1
end
end qHJDQEb
end
