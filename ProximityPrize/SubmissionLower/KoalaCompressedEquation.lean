import ProximityPrize.SubmissionLower.KoalaCompression
import ProximityPrize.SubmissionLower.KoalaNodeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SplitCut.Compression
noncomputable section

open BoxDegree
open scoped Polynomial

variable {F:Type*} [Field F]

abbrev SeedPoly (F:Type*) [CommRing F]:=MvPolynomial (Fin 2) F
abbrev FreshEquation (F:Type*) [CommRing F]:=Polynomial (Polynomial (SeedPoly F))

def pack {e v w : ℕ} (W : exps e v w → F[X]) : FreshEquation F :=
  ∑ m : exps e v w,
    (W m).map (Polynomial.C.comp MvPolynomial.C) *
      Polynomial.C (Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1))

theorem pack_coeff {e v w : ℕ} (W : exps e v w → F[X]) (i j : ℕ) :
    ((pack W).coeff i).coeff j =
      ∑ m:exps e v w,if m.val none=j then MvPolynomial.monomial m.val.some ((W m).coeff i) else 0:=by
  classical
  rw [pack,Polynomial.finsetSum_coeff,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, RingHom.comp_apply, Polynomial.coeff_C_mul,
    Polynomial.coeff_monomial]
  by_cases h:m.val none=j
  · simp [h,MvPolynomial.C_mul_monomial]
  · simp [h,Ne.symm h]

theorem pack_recover {e v w : ℕ} (W : exps e v w → F[X]) (m : exps e v w) (i : ℕ) :
    (((pack W).coeff i).coeff (m.val none)).coeff m.val.some=(W m).coeff i:=by
  classical
  rw [pack_coeff,MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro n _ hn
    by_cases h:n.val none=m.val none
    · have hs : n.val.some ≠ m.val.some := by
        intro he
        apply hn
        apply Subtype.ext
        ext j
        cases j with
        | none => exact h
        | some k => exact DFunLike.congr_fun he k
      simp [h,MvPolynomial.coeff_monomial,hs,Ne.symm hs]
    · simp [h]
  · intro h
    exact (h (Finset.mem_univ m)).elim

theorem pack_ne_zero {e v w : ℕ} {W : exps e v w → F[X]} (hW : W ≠ 0) : pack W ≠ 0 := by
  intro h
  apply hW
  funext m
  apply Polynomial.ext
  intro i
  rw [← pack_recover W m,h]
  simp

theorem pack_x_bound {e v w b : ℕ} (W : exps e v w → F[X])
    (hW : ∀ m,(W m).natDegree≤b):(pack W).natDegree≤b:=by
  unfold pack
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C,add_zero]
    exact Polynomial.natDegree_map_le.trans (hW m))

theorem pack_y_bound {e v w : ℕ} (W : exps e v w → F[X]) (i : ℕ) :
    ((pack W).coeff i).natDegree≤e:=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pack_coeff]
  apply Finset.sum_eq_zero
  intro m _
  simp [show m.val none≠j from ne_of_lt (m.property.1.trans_lt hj)]

theorem pack_seed_bound {e v w : ℕ} (W : exps e v w → F[X]) (i j : ℕ) (a : Fin 2) :
    (((pack W).coeff i).coeff j).degreeOf a≤(![v,w]:Fin 2→ℕ) a:=by
  classical
  rw [pack_coeff]
  refine (MvPolynomial.degreeOf_sum_le a _ _).trans (Finset.sup_le ?_)
  intro m _
  split_ifs
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro n hn
    obtain rfl:=Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
    fin_cases a
    · exact m.property.2.1
    · exact m.property.2.2
  · simp

theorem pack_substitute {A : Type*} [CommRing A] (ι : F →+* A) (z : Fin 2 → A) (S : A[X])
    {e v w:ℕ} (W:exps e v w→F[X]) :
    StableNode.substitute S ((pack W).map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))) =
      ∑ m : exps e v w, (W m).map ι *
        (S^m.val none*Polynomial.C (z 0^m.val (some 0)*z 1^m.val (some 1))):=by
  rw [pack,Polynomial.map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.map_mul,Polynomial.map_C,map_mul]
  congr 1
  · rw [Polynomial.map_map]
    change ((W m).map _).eval₂
      (Polynomial.eval₂RingHom Polynomial.C S) (Polynomial.X:A[X])=_
    rw [Polynomial.eval₂_map]
    rw [show ((Polynomial.eval₂RingHom Polynomial.C S).comp
      (((Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))).comp
        (Polynomial.C.comp MvPolynomial.C))) = Polynomial.C.comp ι by
          apply RingHom.ext
          intro q
          simp [Polynomial.map_C]]
    rw [← Polynomial.eval₂_map,Polynomial.eval₂_C_X]
  · simp only [StableNode.substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom]
    change ((Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1)).map
        (MvPolynomial.eval₂Hom ι z)).eval₂ Polynomial.C S=_
    rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fin.prod_univ_two,map_one,one_mul]
    exact mul_comm _ _

theorem compressed_polynomial {α : Type*} [Finite α] (S : α → F[X]) (z : α → Fin 2 → F)
    {f:MvPolynomial Idx (Rational F)} (hf:f≠0) {e v w b d p:ℕ}
    (hfit:f ∈ space (Rational F) e v w) (hS : ∀ g,(S g).natDegree≤d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap F[X] (Rational F) (S g))
      (fun j => algebraMap F[X] (Rational F) (Polynomial.C (z g j)))) f=0)
    (hguard:Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p)
    (hp:e*d < p) :
    ∃ G : FreshEquation F, G ≠ 0 ∧ G.natDegree + e*d < p ∧
      (∀ i,(G.coeff i).natDegree≤e) ∧
      (∀ i j,(((G.coeff i).coeff j).degreeOf 0≤v+b) ∧ (((G.coeff i).coeff j).degreeOf 1≤w+b)) ∧
      (∀ g, StableNode.substitute (S g)
        (G.map (Polynomial.mapRingHom (MvPolynomial.eval (z g))))=0):=by
  classical
  obtain ⟨W,hW,hWzero⟩:=compress_box S z hf hfit hS hroot hguard
  let U:exps e (v+b) (w+b)→F[X]:=fun m => W m
  have hU : U ≠ 0 := by
    intro h
    apply hW
    funext m
    exact Subtype.ext (congrFun h m)
  have hdeg (m : exps e (v+b) (w+b)) : (U m).natDegree ≤ p-e*d-1 := by
    by_cases hz:U m=0
    · simp [hz]
    · have h := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (W m).property)
      omega
  refine ⟨pack U,pack_ne_zero hU, ?_,pack_y_bound U, ?_, ?_⟩
  · have h := pack_x_bound U hdeg
    omega
  · intro i j
    exact ⟨pack_seed_bound U i j 0,pack_seed_bound U i j 1⟩
  · intro g
    rw [show MvPolynomial.eval (z g) = MvPolynomial.eval₂Hom (RingHom.id F) (z g) from rfl,
      pack_substitute]
    simp only [Polynomial.map_id]
    simpa only [evalRow,U,mul_comm] using hWzero g

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compressed_polynomial
