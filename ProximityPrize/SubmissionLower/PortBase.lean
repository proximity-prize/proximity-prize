import ProximityPrize.SubmissionLower.Fast068
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L+T.height+nullity u=t+1:=by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have:=T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height≤heightCap:=by
  have h:=relation_height_balance T
  have hr:=hu.1
  dsimp only [L,t,heightCap,blockLength,agreement,k,frontLimit] at h hr ⊢
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T:=by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1≤t by decide).trans_lt T.inactive) T.level
  have hH:=relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
private theorem type_one_bad_count_of_syndromes {F ι : Type}
    [Field F] [Fintype ι] [DecidableEq ι] (x u v:ι→F) (hx:Function.Injective x)
    (k a p:ℕ) (hk:k≤Fintype.card ι) (hp:1 < p)
    (htype:Principal.TypeOneSyndromes x u v k p)
    (Γ:Finset F) (hΓ : ∀ γ ∈ Γ,Principal.BadSlope x u v k a γ) :
    Γ.card≤1 :=
  Principal.type_one_bad_count x hx u v k a p hk hp htype Γ hΓ
variable {F ι:Type} [Field F] [Fintype ι] [DecidableEq ι]
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c:Fin (t+1)→F) (hc:(coefficientBlocks p x u v L t).mulVec c=0) :
    (stacked p x u v L t).mulVec (fun j => C (c j))=0:=by
  funext i
  have h0:=congrFun hc (0,i.2)
  have h1:=congrFun hc (1,i.2)
  have h2:=congrFun hc (2,i.2)
  have h3:=congrFun hc (3,i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientBlocks, Fin.reduceEq,
    ite_true,ite_false,Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi:i.1=0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R:=F)*C (∑ j,syndrome x v (i.2.val+j.val)*c j):=by
        rw [map_sum,map_sum,Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _=0:=by simp only [h0,h1,map_zero,mul_zero,add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R:=F) ^ p*C (∑ j,syndrome x v (i.2.val+j.val) ^ p*c j):=by
        rw [map_sum,map_sum,Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _=0:=by simp only [h2,h3,map_zero,mul_zero,add_zero]
private theorem constantRankCount {E : Type} [Field E]
    (φ:F[X] →+* E) (hφ:Function.Injective φ) (p:ℕ) [ExpChar F p] (hp:1≤p)
    (x:ι→F) (hx:Function.Injective x) (hfixed : ∀ i,x i ^ p=x i)
    (u v:ι→F) (k A L t:ℕ) (hkA:k < A) (hL:k+L=A)
    (ht:A+t=Fintype.card ι)
    (r:ℕ) (hgeneric:((stacked p x u v L t).map φ).rank=r)
    (hconstant:(coefficientBlocks p x u v L t).rank=r)
    (Γ:Finset F) (hΓ : ∀ γ ∈ Γ,Principal.BadSlope x u v k A γ):Γ.card≤p*r:=by
  let M:=stacked p x u v L t
  let C₀:=coefficientBlocks p x u v L t
  let W:=LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩:=NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h:=LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientBlocks p x u v L t).rank+Module.finrank F W=_ at h
    rw [hconstant,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j))=0 :=
    coefficientKernel_annihilates p x u v L t c hc
  have hminor : (NormalFiber.pivot B).det.natDegree ≤ p * r := by
    have h := NormalFiber.minor_degree_le φ M r B (fun _ => p) (by
      intro i j
      exact (stacked_entry_natDegree p x u v L t i j).trans (by split_ifs <;> omega))
    simpa [Nat.mul_comm] using h
  exact Principal.constant_kernel_count p x hx hfixed u v k A L t (p * r) hkA hL ht
    _ B.minor_ne hminor (Principal.constantCertificateOfRowBasis φ hφ p x u v L t r B W hWdim hW)
    Γ hΓ
open K1_1
private def nativeMoments (u : Words) : Fin 2 → ℕ → Frac :=
  fun b j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) b j)
private theorem independent_nativeMoments (u : Words)
    (h : ¬ TypeAtMostOne u):IndependentMoments (nativeMoments u) k:=by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective K[X] Frac
  simpa [nativeMoments,Principal.parameterSyndromes,map_mul] using hall i j
end
end P0
end
