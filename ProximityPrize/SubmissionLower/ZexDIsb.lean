import ProximityPrize.SubmissionLower.ZG9rwXd
import ProximityPrize.SubmissionLower.ZrU0ida
set_option Elab.async false
namespace qgbTAnb
noncomputable section
open Finset Polynomial qe6nVeb qE3Ebna
open P5 (K)
open cu (L)
open E7 (CurvePlace axV poleOrder KB)
open qb0hmCe (CurveModel)
open qFD8jve (sheetPole)
open private sum_le_all finite_tuple from ProximityPrize.SubmissionLower.ZG9rwXd
open scoped Classical WithZero
theorem padded_ne {F:Type*} [Field F] {a b:F[X]} {m n:ℕ}
   (ha :a≠0) (hab:IsCoprime a b) (hm:a.natDegree≤ m) (hn:b.natDegree≤n)
   (ht:a.natDegree=m∨b.natDegree=n∧b≠0) :
   resultant a b m n≠0:= by
 have hr :=resultant_ne_zero a b hab
 rcases ht with rfl | ⟨rfl,hb⟩
 · rw [← Nat.add_sub_of_le hn,resultant_add_right_deg _ _ _ _ _ (le_refl _)]
   exact mul_ne_zero (pow_ne_zero _ (by simpa using ha)) hr
 · rw [← Nat.add_sub_of_le hm,resultant_add_left_deg _ _ _ _ _ (le_refl _)]
   exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp))
     (pow_ne_zero _ (by simpa using hb))) hr
private theorem coeff_le_pole {E :Type} [Field E] (v :Valuation E ℤᵐ⁰)
    (f :E[X][X]) (i j:ℕ) :
    v ((f.coeff i).coeff j)≤WithZero.exp (sheetPole v f :ℤ) := by
  by_cases h: (f.coeff i).coeff j=0
  · simp [h]
  have hi:i∈f.support :=mem_support_iff.mpr (fun hz=>h (by simp [hz]))
  have hj:=le_natDegree_of_ne_zero h
  have hj' : j≤f.support.sup (fun i=>(f.coeff i).natDegree) :=
    hj.trans (le_sup (f := fun i=>(f.coeff i).natDegree) hi)
  have hsup:poleOrder v ((f.coeff i).coeff j)≤ sheetPole v f :=
    le_sup (f := fun ij:Fin (f.natDegree+1) ×
      Fin ((f.support.sup fun i=>(f.coeff i).natDegree)+1) =>
        poleOrder v ((f.coeff ij.1).coeff ij.2))
      (mem_univ (⟨⟨i,Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hi)⟩,
        ⟨j,Nat.lt_succ_of_le hj'⟩⟩))
  apply (WithZero.log_le_iff_le_exp (by simpa using h)).mp
  unfold poleOrder at hsup
  omega
private theorem resultant_le {E :Type} [Field E] (v :Valuation E ℤᵐ⁰)
   (f :E[X][X]) (m n:ℕ) :
   v (resultant (f.coeff 1) (f.coeff 0) m n) ≤
     WithZero.exp (((m+n)*sheetPole v f :ℕ) :ℤ) := by
 let M:=sylvester (f.coeff 1) (f.coeff 0) m n
 let c:=WithZero.exp (sheetPole v f :ℤ)
 have he (i j) :v (M i j)≤ c:= by
   refine Fin.addCases ?_ ?_ j
   · intro j
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_left]
     split
     · exact coeff_le_pole v f 0 _
     · simp
   · intro j
     simp only [M,sylvester,Matrix.of_apply,Fin.addCases_right]
     split
     · exact coeff_le_pole v f 1 _
     · simp
 change v M.det≤_
 rw [show WithZero.exp (((m+n)*sheetPole v f :ℕ) :ℤ)=c^(m+n) by
   simp [c,← WithZero.exp_nsmul]]
 rw [Matrix.det_apply]
 apply v.map_sum_le
 intro π _
 have hπ:v (∏ j,M (π j) j)≤ c^(m+n) := by
   rw [map_prod]
   calc
     _ ≤ ∏ _j:Fin (m+n),c:=Finset.prod_le_prod fun j _=>he (π j) j
     _ = _:= by simp
 rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;>
   simpa [hs,Valuation.map_neg] using hπ
theorem charge {J:Input} {U:Finset K} {B:DualWord J U} {q:SeedPlane}
   {C:CurveModel q} (S:Sheet B C) (m n:ℕ)
   (hne :resultant (S.f.coeff 1) (S.f.coeff 0) m n≠0)
   (hmark : ∀ γ∈S.marks,poleOrderAt S γ ≤
     KB (S.place γ).value (resultant (S.f.coeff 1) (S.f.coeff 0) m n)) :
   ∑ γ∈S.marks,poleOrderAt S γ≤(m+n)*S.h:= by
 let g:=resultant (S.f.coeff 1) (S.f.coeff 0) m n
 let H (v :CurvePlace L C.E) :=sheetPole v.value S.f
 let P (v :CurvePlace L C.E) :=poleOrder v.value g
 let zord (v :CurvePlace L C.E) :=KB v.value g
 have divs :axV L C.E :=
   aFU.of_children
     bRt.proof bRu.proof L C.E C.curve
 obtain ⟨hp,hz,he,_⟩:=divs g
 have hH :H.HasFiniteSupport:=finite_tuple divs _
 have hb (v :CurvePlace L C.E) :P v≤(m+n)*H v :=
   Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (by simpa [g] using hne)).2
     (resultant_le v.value S.f m n))
 calc
   _ ≤ ∑ γ∈S.marks,zord (S.place γ) :=sum_le_sum hmark
   _ = ∑ v∈S.marks.image S.place,zord v :=(sum_image S.distinct).symm
   _ ≤ ∑ᶠ v,zord v :=sum_le_all _ hz _
   _ = ∑ᶠ v,P v :=he.symm
   _ = ∑ v∈hp.toFinset,P v :=finsum_eq_finsetSum_of_support_subset _
     (fun _ hv=>(Set.Finite.mem_toFinset _).mpr hv)
   _ ≤ ∑ v∈hp.toFinset,(m+n)*H v :=sum_le_sum fun v _=>hb v
   _≤(m+n)*S.h:= by
     rw [← mul_sum]
     exact Nat.mul_le_mul_left _ (sum_le_all H hH _)
end
end qgbTAnb
