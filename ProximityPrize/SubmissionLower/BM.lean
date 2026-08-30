import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactIdentityPencil
noncomputable section
variable {K L:Type*} [Field K] [Field L]
theorem degree_lt_card_of_natDegree_le {ι:Type*}
   (I:Finset ι) (w:ℕ) (hw:w < I.card) (P:Polynomial L)
   (hP:P.natDegree ≤ w):P.degree < (I.card:WithBot ℕ):=
 lt_of_le_of_lt Polynomial.degree_le_natDegree
   (WithBot.coe_lt_coe.mpr (hP.trans_lt hw))
theorem mapped_affine_pencil_natDegree_le
   (coefficients:K →+*L) (P₀ P₁:Polynomial K) (w:ℕ)
   (h₀:P₀.natDegree ≤ w) (h₁:P₁.natDegree ≤ w) (γ:L):
   (P₀.map coefficients+Polynomial.C γ*P₁.map coefficients).natDegree ≤ w:=by
 apply (Polynomial.natDegree_add_le _ _).trans
 exact max_le (Polynomial.natDegree_map_le.trans h₀)
   ((Polynomial.natDegree_C_mul_le γ _).trans (Polynomial.natDegree_map_le.trans h₁))
theorem exists_basefield_affine_pencil_of_identity_nodes {ι τ:Type*}
   (coefficients:K →+*L) (I:Finset ι) (x u₀ u₁:ι → K)
   (w:ℕ) (hw:w < I.card) (hinj:Set.InjOn x I)
   (γ:τ → L) (P:τ → Polynomial L)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I →
     (P t).eval (coefficients (x i))=coefficients (u₀ i)+γ t*coefficients (u₁ i)):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀.map coefficients+Polynomial.C (γ t)*P₁.map coefficients:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 obtain ⟨S,hSI,hcard⟩:=Finset.exists_subset_card_eq (show w+1 ≤ I.card by omega)
 have hxS:Set.InjOn x S:=by
   intro i hi j hj hij
   exact hinj (hSI hi) (hSI hj) hij
 let P₀:Polynomial K:=Lagrange.interpolate S x u₀
 let P₁:Polynomial K:=Lagrange.interpolate S x u₁
 have h₀:P₀.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₀ hxS
 have h₁:P₁.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   simpa only [hcard,Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₁ hxS
 have heval₀:∀ i∈S,P₀.eval (x i)=u₀ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₀ hxS hi
 have heval₁:∀ i∈S,P₁.eval (x i)=u₁ i:=by
   intro i hi
   exact Lagrange.eval_interpolate_at_node u₁ hxS hi
 have hnodes:Set.InjOn (fun i => coefficients (x i)) S:=by
   intro i hi j hj hij
   exact hxS hi hj (coefficients.injective hij)
 have hws:w < S.card:=by omega
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hnodes
   (degree_lt_card_of_natDegree_le S w hws (P t) (hdegree t))
   (degree_lt_card_of_natDegree_le S w hws _
     (mapped_affine_pencil_natDegree_le coefficients P₀ P₁ w h₀ h₁ (γ t)))
 intro i hi
 simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply,heval₀ i hi,heval₁ i hi] using hvalues t i (hSI hi)
theorem exists_affine_pencil_of_identity_nodes {ι τ:Type*}
   (I:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:w < I.card)
   (hinj:Set.InjOn x I) (γ:τ → K) (P:τ → Polynomial K)
   (hdegree:∀ t,(P t).natDegree ≤ w)
   (hvalues:∀ t i,i∈I → (P t).eval (x i)=u₀ i+γ t*u₁ i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     ∀ t,P t=P₀+Polynomial.C (γ t)*P₁:=by
 obtain ⟨P₀,P₁,h₀,h₁,hfamily⟩:=
   exists_basefield_affine_pencil_of_identity_nodes (RingHom.id K) I x u₀ u₁
     w hw hinj γ P hdegree hvalues
 refine ⟨P₀,P₁,h₀,h₁,?_⟩
 intro t
 simpa only [Polynomial.map_id] using hfamily t
end
end ProximityPrize.SubmissionLower.ContactIdentityPencil
