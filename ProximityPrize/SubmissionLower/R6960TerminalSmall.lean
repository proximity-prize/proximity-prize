import ProximityPrize.SubmissionLower.KoalaStableNode
import Mathlib.Algebra.Polynomial.Taylor
import ProximityPrize.SubmissionLower.KoalaCompression
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import ProximityPrize.SubmissionLower.R6960TerminalDegrees

-- merged module KoalaNodeTranslation
section Merged_KoalaNodeTranslation

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SplitCut.StableNode
noncomputable section
open Polynomial






end
end SplitCut.StableNode


end Merged_KoalaNodeTranslation

-- merged module KoalaCompressedEquation
section Merged_KoalaCompressedEquation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SplitCut.Compression
noncomputable section

open BoxDegree
open scoped Polynomial

variable {F : Type*} [Field F]

abbrev SeedPoly (F : Type*) [CommRing F] := MvPolynomial (Fin 2) F
abbrev FreshEquation (F : Type*) [CommRing F] := Polynomial (Polynomial (SeedPoly F))

def pack {e v w : ℕ} (W : exps e v w → (Polynomial F)) : FreshEquation F :=
  ∑ m : exps e v w,
    (W m).map (Polynomial.C.comp MvPolynomial.C) *
      Polynomial.C (Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1))

theorem pack_coeff {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i j : ℕ) :
    ((pack W).coeff i).coeff j =
      ∑ m : exps e v w, if m.val none = j then MvPolynomial.monomial m.val.some ((W m).coeff i) else 0 := by
  classical
  rw [pack, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, RingHom.comp_apply, Polynomial.coeff_C_mul,
    Polynomial.coeff_monomial]
  by_cases h : m.val none = j
  · simp [h, MvPolynomial.C_mul_monomial]
  · simp [h, Ne.symm h]

theorem pack_recover {e v w : ℕ} (W : exps e v w → (Polynomial F)) (m : exps e v w) (i : ℕ) :
    (((pack W).coeff i).coeff (m.val none)).coeff m.val.some = (W m).coeff i := by
  classical
  rw [pack_coeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro n _ hn
    by_cases h : n.val none = m.val none
    · have hs : n.val.some ≠ m.val.some := by
        intro he
        apply hn
        apply Subtype.ext
        ext j
        cases j with
        | none => exact h
        | some k => exact DFunLike.congr_fun he k
      simp [h, MvPolynomial.coeff_monomial, hs, Ne.symm hs]
    · simp [h]
  · intro h
    exact (h (Finset.mem_univ m)).elim

theorem pack_ne_zero {e v w : ℕ} {W : exps e v w → (Polynomial F)} (hW : W ≠ 0) : pack W ≠ 0 := by
  intro h
  apply hW
  funext m
  apply Polynomial.ext
  intro i
  rw [← pack_recover W m, h]
  simp

theorem pack_x_bound {e v w b : ℕ} (W : exps e v w → (Polynomial F))
    (hW : ∀ m, (W m).natDegree ≤ b) : (pack W).natDegree ≤ b := by
  unfold pack
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (by
    rw [Polynomial.natDegree_C, add_zero]
    exact Polynomial.natDegree_map_le.trans (hW m))

theorem pack_y_bound {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i : ℕ) :
    ((pack W).coeff i).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [pack_coeff]
  apply Finset.sum_eq_zero
  intro m _
  simp [show m.val none ≠ j from ne_of_lt (m.property.1.trans_lt hj)]

theorem pack_seed_bound {e v w : ℕ} (W : exps e v w → (Polynomial F)) (i j : ℕ) (a : Fin 2) :
    (((pack W).coeff i).coeff j).degreeOf a ≤ (![v,w] : Fin 2 → ℕ) a := by
  classical
  rw [pack_coeff]
  refine (MvPolynomial.degreeOf_sum_le a _ _).trans (Finset.sup_le ?_)
  intro m _
  split_ifs
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro n hn
    obtain rfl := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
    fin_cases a
    · exact m.property.2.1
    · exact m.property.2.2
  · simp

theorem pack_substitute {A : Type*} [CommRing A] (ι : F →+* A) (z : Fin 2 → A) (S : (Polynomial A))
    {e v w : ℕ} (W : exps e v w → (Polynomial F)) :
    StableNode.substitute S ((pack W).map (Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))) =
      ∑ m : exps e v w, (W m).map ι *
        (S^m.val none * Polynomial.C (z 0^m.val (some 0) * z 1^m.val (some 1))) := by
  rw [pack, Polynomial.map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul]
  congr 1
  · rw [Polynomial.map_map]
    change ((W m).map _).eval₂
      (Polynomial.eval₂RingHom Polynomial.C S) (Polynomial.X : (Polynomial A)) = _
    rw [Polynomial.eval₂_map]
    rw [show ((Polynomial.eval₂RingHom Polynomial.C S).comp
      (((Polynomial.mapRingHom (MvPolynomial.eval₂Hom ι z))).comp
        (Polynomial.C.comp MvPolynomial.C))) = Polynomial.C.comp ι by
          apply RingHom.ext
          intro q
          simp [Polynomial.map_C]]
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_C_X]
  · simp only [StableNode.substitute, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom]
    change ((Polynomial.monomial (m.val none) (MvPolynomial.monomial m.val.some 1)).map
        (MvPolynomial.eval₂Hom ι z)).eval₂ Polynomial.C S = _
    rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, map_one, one_mul]
    exact mul_comm _ _

theorem compressed_polynomial {α : Type*} [Finite α] (S : α → (Polynomial F)) (z : α → Fin 2 → F)
    {f : MvPolynomial Idx (Rational F)} (hf : f ≠ 0) {e v w b d p : ℕ}
    (hfit : f ∈ space (Rational F) e v w) (hS : ∀ g, (S g).natDegree ≤ d)
    (hroot : ∀ g, MvPolynomial.eval (fun i : Idx => i.elim (algebraMap (Polynomial F) (Rational F) (S g))
      (fun j => algebraMap (Polynomial F) (Rational F) (Polynomial.C (z g j)))) f = 0)
    (hguard : Fintype.card (exps e (v+b) (w+b))*(e*d) < ((b+1)*(b+1))*p)
    (hp : e*d < p) :
    ∃ G : FreshEquation F, G ≠ 0 ∧ G.natDegree + e*d < p ∧
      (∀ i, (G.coeff i).natDegree ≤ e) ∧
      (∀ i j, (((G.coeff i).coeff j).degreeOf 0 ≤ v+b) ∧ (((G.coeff i).coeff j).degreeOf 1 ≤ w+b)) ∧
      (∀ g, StableNode.substitute (S g)
        (G.map (Polynomial.mapRingHom (MvPolynomial.eval (z g)))) = 0) := by
  classical
  obtain ⟨W, hW, hWzero⟩ := compress_box S z hf hfit hS hroot hguard
  let U : exps e (v+b) (w+b) → (Polynomial F) := fun m => W m
  have hU : U ≠ 0 := by
    intro h
    apply hW
    funext m
    exact Subtype.ext (congrFun h m)
  have hdeg (m : exps e (v+b) (w+b)) : (U m).natDegree ≤ p-e*d-1 := by
    by_cases hz : U m = 0
    · simp [hz]
    · have h := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (W m).property)
      omega
  refine ⟨pack U, pack_ne_zero hU, ?_, pack_y_bound U, ?_, ?_⟩
  · have h := pack_x_bound U hdeg
    omega
  · intro i j
    exact ⟨pack_seed_bound U i j 0, pack_seed_bound U i j 1⟩
  · intro g
    rw [show MvPolynomial.eval (z g) = MvPolynomial.eval₂Hom (RingHom.id F) (z g) from rfl,
      pack_substitute]
    simp only [Polynomial.map_id]
    simpa only [evalRow, U, mul_comm] using hWzero g

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compressed_polynomial

end Merged_KoalaCompressedEquation

-- merged module R6960QuadraticCount
section Merged_R6960QuadraticCount
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Lower6960
open Polynomial CurvatureSquares K1_14 RetainedShortening CurvatureVotes
open SplitCut.Compression
open scoped Polynomial Classical
private abbrev onSeeds := (K1_10.frobeniusGraph (F := L) K1.p).toRingHom
private def project : FreshEquation L →+* Ordinate :=
  Bivariate.swap.toRingHom.comp (mapRingHom (mapRingHom onSeeds))
private theorem project_coeff (G : FreshEquation L) (i j : ℕ) :
    ((project G).coeff j).coeff i = onSeeds ((G.coeff i).coeff j) := by
  change ((Bivariate.swap _).coeff j).coeff i = _
  rw [coeff_swap]
  simp
private theorem project_ne {G : FreshEquation L} (ne : G≠0)
    (cap : ∀ i j, ((G.coeff i).coeff j).degreeOf 0 < K1.p) : project G≠0 := by
  intro bad
  apply ne
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  by_contra h
  have hzero := project_coeff G i j
  rw [bad] at hzero
  exact K1_10.frobeniusGraph_ne_zero _ (by decide) _ (by simpa using h) (cap i j)
    (by simpa using hzero.symm)
private theorem project_x (G : FreshEquation L) : (xView (project G)).natDegree ≤ G.natDegree := by
  change (Bivariate.swap (Bivariate.swap _)).natDegree ≤ _
  rw [Bivariate.swap_swap_apply]
  exact natDegree_map_le
private theorem project_y {G : FreshEquation L} {e : ℕ} (cap : ∀ i, (G.coeff i).natDegree≤e) :
    (project G).natDegree≤e := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext i
  rw [project_coeff,coeff_eq_zero_of_natDegree_lt ((cap i).trans_lt hj)]
  simp
private theorem project_z {G : FreshEquation L} {v w : ℕ}
    (axes : ∀ i j, ((G.coeff i).coeff j).degreeOf 0≤v ∧ ((G.coeff i).coeff j).degreeOf 1≤w) :
    (zView (project G)).natDegree ≤ v+K1.p*w := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext j i
  change (((Bivariate.swap ((project G).map Bivariate.swap.toRingHom)).coeff n).coeff j).coeff i = _
  rw [coeff_swap,coeff_map]
  change ((Bivariate.swap ((project G).coeff j)).coeff n).coeff i = _
  rw [coeff_swap,project_coeff]
  simpa using coeff_eq_zero_of_natDegree_lt
    ((K1_10.frobeniusGraph_degree _ _ _ _ (axes i j).1 (axes i j).2).trans_lt hn)
private theorem cover_root (P : Ordinate) (ne : P≠0) {z : L} {S : (Polynomial L)}
    (hit : ordEval z S P=0) :
    ∃ f : Ordinate, Irreducible f ∧ f∣P ∧ f.natDegree≤P.natDegree ∧ ordEval z S f=0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (ne rfl).elim
  | unit u hu => exact ((hu.map (ordEval z S)).ne_zero hit).elim
  | mul q f hq hf ih =>
    rw [map_mul,mul_eq_zero] at hit
    rcases hit with h|h
    · exact ⟨f,hf,dvd_mul_right ..,natDegree_le_of_dvd (dvd_mul_right ..) ne,h⟩
    · obtain ⟨g,hg,dv,_,zr⟩ := ih hq h
      have dv' : g∣f*q := dv.trans (show q∣f*q from ⟨f,by rw [mul_comm f q]⟩)
      exact ⟨g,hg,dv',natDegree_le_of_dvd dv' ne,zr⟩
private theorem eval_project (G : FreshEquation L) (z : L) (S : (Polynomial L)) :
    ordEval z S (project G) = SplitCut.StableNode.substitute S
      (G.map (mapRingHom (MvPolynomial.eval ![z,z^K1.p]))) := by
  let left := (ordEval z S).comp project
  let right := (SplitCut.StableNode.substitute S).comp
    (mapRingHom (mapRingHom (MvPolynomial.eval ![z,z^K1.p])))
  have eq : left=right := by
    apply Polynomial.ringHom_ext
    · intro a
      suffices h : left.comp C = right.comp C from RingHom.congr_fun h a
      apply Polynomial.ringHom_ext
      · intro b
        suffices h : (left.comp C).comp C = (right.comp C).comp C from RingHom.congr_fun h b
        apply MvPolynomial.ringHom_ext
        · intro a
          simp [left,right,project,ordEval,SplitCut.StableNode.substitute,onSeeds,
            K1_10.frobeniusGraph,Bivariate.swap_C_C]
        · intro i
          fin_cases i <;> simp [left,right,project,ordEval,SplitCut.StableNode.substitute,
            onSeeds,K1_10.frobeniusGraph,Bivariate.swap_C_C,Polynomial.eval₂_pow]
      · simp [left,right,project,ordEval,SplitCut.StableNode.substitute,Bivariate.swap_X]
    · simp [left,right,project,ordEval,SplitCut.StableNode.substitute,Bivariate.swap_Y]
  exact DFunLike.congr_fun eq G
theorem small_ordinate_count_at_scale {A d k w s T} (W : Word A d w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (hd : d<A) (scale : VoteScale A d k)
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2) {v u b : ℕ}
    (axes : ∀ i, (f.coeff i).degreeOf 0≤v ∧ (f.coeff i).degreeOf 1≤u)
    (small : v+b<K1.p)
    (guard : 3*(v+b+1)*(u+b+1)*(2*d)<(b+1)*(b+1)*(K1.p/2))
    (width : 2*d<K1.p/2)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤max 8 k*((v+b)+K1.p*(u+b))+4 := by
  classical
  let φ := algebraMap K1.K L
  let z (g : K1.K) := φ (label g)
  let S (g : ↥T) := liftPoly (s g)
  let pair (g : ↥T) : Fin 2 → L := ![z g,(z g)^K1.p]
  let f' := K1_14_6_1.flatten f
  have hn : f'≠0 := by
    intro h
    exact ne ((MvPolynomial.optionEquivLeft FX (Fin 2)).symm.injective (h.trans (map_zero _).symm))
  have box : f' ∈ SplitCut.BoxDegree.space FX 2 v u := by
    intro m hm
    change m ∈ f'.support at hm
    have hc : m.some ∈ (f.coeff (m none)).support := by
      rw [MvPolynomial.mem_support_iff] at hm ⊢
      have h := MvPolynomial.optionEquivLeft_coeff_coeff FX f' (m none) m.some
      simp only [f',K1_14_6_1.flatten,AlgEquiv.apply_symm_apply,Finsupp.optionElim_some] at h
      exact h.trans_ne hm
    have hne : f.coeff (m none) ≠ 0 := by intro h; simp [h] at hc
    exact ⟨(Polynomial.le_natDegree_of_ne_zero hne).trans degree,
      (MvPolynomial.le_degreeOf_of_mem_support 0 hc).trans (axes _).1,
      (MvPolynomial.le_degreeOf_of_mem_support 1 hc).trans (axes _).2⟩
  have hit (g : ↥T) : MvPolynomial.eval (fun i : Option (Fin 2) => i.elim
      (algebraMap (Polynomial L) FX (S g)) (fun j => algebraMap (Polynomial L) FX (C (pair g j)))) f'=0 := by
    have eq : (fun i : Option (Fin 2) => i.elim (algebraMap (Polynomial L) FX (S g))
      (fun j => algebraMap (Polynomial L) FX (C (pair g j)))) = K1_14_6.rootPoint (label g) (s g) := by
      funext i
      cases i with
      | none => rfl
      | some j => fin_cases j <;> simp [K1_14_6.rootPoint,pair,z,φ,seedEmbedding]
    rw [eq]
    exact (K1_14_6_1.eval_flatten ..).trans (marks _ g.property)
  have hguard : Fintype.card (SplitCut.BoxDegree.exps 2 (v+b) (u+b)) * (2*d) <
      ((b+1)*(b+1))*(K1.p/2) := by
    rw [Fintype.card_congr (SplitCut.BoxDegree.slots _ _ _),Fintype.card_prod,
      Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin]
    simpa only [Nat.mul_assoc] using guard
  obtain ⟨G,ng,wx,wy,wz,atWords⟩ := compressed_polynomial S pair hn box
    (fun g => Polynomial.natDegree_map_le.trans (W.degree _ g.property)) hit hguard width
  let P := project G
  have pn : P≠0 := project_ne ng (fun i j => ((wz i j).1).trans_lt small)
  have tame : 2*(xView P).natDegree<K1.p := by have := project_x G; dsimp [P]; omega
  have dy := project_y wy
  have hz_inj : Set.InjOn z (T:Set K1.K) := fun _ h _ h' eq => inj h h' (φ.injective eq)
  have count := projected_low_count W φ z hz_inj hd scale P pn tame
    (fun γ mem => by
      have hz := (eval_project G (z γ) ((s γ).map φ)).trans (atWords ⟨γ,mem⟩)
      obtain ⟨q,irr,dv,deg,root⟩ := cover_root P pn hz
      exact ⟨q,irr,dv,deg.trans dy,root⟩)
  have dz := project_z wz
  exact count.trans (Nat.add_le_add (Nat.mul_le_mul_left _ dz) (Nat.mul_le_mul_left 2 dy))
theorem small_ordinate_count {A d w s T} (W : Word A d w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (hd : d<A) (scale : VoteScale A d 5)
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2) {v u b : ℕ}
    (axes : ∀ i, (f.coeff i).degreeOf 0≤v ∧ (f.coeff i).degreeOf 1≤u)
    (small : v+b<K1.p)
    (guard : 3*(v+b+1)*(u+b+1)*(2*d)<(b+1)*(b+1)*(K1.p/2))
    (width : 2*d<K1.p/2)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤8*((v+b)+K1.p*(u+b))+4 :=
  small_ordinate_count_at_scale W label inj hd scale f ne degree axes small guard width marks
theorem first_band_small_ordinate {w s T} (W : Word 179798 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2)
    (axes : ∀ i, (f.coeff i).degreeOf 0≤2400 ∧ (f.coeff i).degreeOf 1≤2400)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤43091406921220 := by
  have h := small_ordinate_count (v:=2400) (u:=2400) (b:=128) W label inj
    (by decide) (Or.inr (by decide)) f ne degree axes (by decide) (by decide) (by decide) marks
  exact h.trans (by decide)
#print axioms first_band_small_ordinate
abbrev axis (f : Equation) (i : Fin 2) := (K1_14_6_1.flatten f).degreeOf (some i)
private theorem axis_mul {f g : Equation} (hf : f≠0) (hg : g≠0) (i : Fin 2) :
    axis (f*g) i=axis f i+axis g i := by
  unfold axis K1_14_6_1.flatten
  rw [map_mul,MvPolynomial.degreeOf_mul_eq (by simpa using hf) (by simpa using hg)]
private theorem coeff_axis (f : Equation) (i : Fin 2) (j : ℕ) :
    (f.coeff j).degreeOf i≤axis f i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  let n := m.optionElim j
  have hi : n ∈ (K1_14_6_1.flatten f).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h := MvPolynomial.optionEquivLeft_coeff_coeff FX (K1_14_6_1.flatten f) j m
    simp only [K1_14_6_1.flatten,AlgEquiv.apply_symm_apply] at h
    exact h ▸ hm
  simpa [n,axis] using MvPolynomial.le_degreeOf_of_mem_support (some i) hi
private def lowFee (f : Equation) : ℕ :=
  8*(axis f 0+K1.p*axis f 1)+(8*128*(K1.p+1)+4)*f.natDegree
theorem low_component_count {w s T} (W : Word 179798 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K)) (f : Equation) :
    f≠0 → (∀ i, axis f i≤2400) →
    (∀ γ∈T, ∃ q : Equation, Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤lowFee f := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f unit =>
    intro _ _ cover
    have empty : T=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ mem
      obtain ⟨q,hq,dv,_⟩ := cover γ mem
      exact hq.not_isUnit (isUnit_of_dvd_unit dv unit)
    simp [empty]
  | mul g q ng irr ih =>
    intro ne caps cover
    let U := T.filter (fun γ => ∃ l : Equation, Irreducible l ∧ l∣g ∧ 0<l.natDegree ∧
      l.natDegree≤2 ∧ atMark l (label γ) (s γ)=0)
    let V := T \ U
    have us : U⊆T := Finset.filter_subset _ _
    have vs : V⊆T := Finset.sdiff_subset
    have subword (R) (sub : R⊆T) : Word 179798 133606 w s R :=
      ⟨W.distinct.mono sub,fun γ h => W.degree _ (sub h),fun γ h => W.hits _ (sub h)⟩
    have ax (i : Fin 2) := axis_mul irr.ne_zero ng i
    have upper (i : Fin 2) : axis q i+axis g i≤2400 := (ax i) ▸ caps i
    have uc := ih (subword U us) (inj.mono us) ng (fun i => (Nat.le_add_left ..).trans (upper i))
      (fun γ h => (Finset.mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,hl,dv,pos,deg,zr⟩ := cover γ (vs h)
      have dl : l∣q := ((UniqueFactorizationMonoid.irreducible_iff_prime.mp hl).dvd_mul.mp dv).resolve_right
        (fun u => (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨vs h,l,hl,u,pos,deg,zr⟩))
      have assoc := hl.associated_of_dvd irr dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl irr.ne_zero),
        (natDegree_le_of_dvd assoc.symm.dvd hl.ne_zero).trans deg,?_⟩
      obtain ⟨b,hb⟩ := dl
      change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [hb,atMark,eval₂_mul,zr,zero_mul]
    have vc : V.card≤lowFee q := by
      obtain em|⟨γ,hm⟩ := V.eq_empty_or_nonempty
      · simp [em]
      have hq (i : Fin 2) : axis q i≤2400 := (Nat.le_add_right ..).trans (upper i)
      have fit := small_ordinate_count (b:=128) (subword V vs) label (inj.mono vs)
        (by decide) (Or.inr (by decide)) q irr.ne_zero (rest γ hm).2.1
        (fun j => ⟨coeff_axis q 0 j,coeff_axis q 1 j⟩)
        (by have := hq 0; change _<2130706433; omega)
        (by exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 3
          (Nat.add_le_add_right (Nat.add_le_add_right (hq 0) 128) 1))
          (Nat.add_le_add_right (Nat.add_le_add_right (hq 1) 128) 1))).trans_lt (by decide))
        (by decide) (fun a h => (rest a h).2.2)
      apply fit.trans
      unfold lowFee
      have pos := (rest γ hm).1
      change _ ≤ 8 * (axis q 0 + 2130706433 * axis q 1) + (8*128*(2130706433+1)+4)*q.natDegree
      change 8*(axis q 0+128+2130706433*(axis q 1+128))+4 ≤ _
      omega
    have card := Finset.card_sdiff_add_card_eq_card us
    change V.card+U.card=T.card at card
    rw [←card]
    apply (Nat.add_le_add vc uc).trans
    unfold lowFee
    rw [ax 0,ax 1,natDegree_mul irr.ne_zero ng]
    exact le_of_eq (by ring)
#print axioms low_component_count
def smallMarks (T : Finset K1.K) (label : K1.K → K1.K) (s : K1.K → (Polynomial K1.K)) (f : Equation) :
    Finset K1.K := T.filter (fun γ => ∃ q : Equation, Irreducible q ∧ q∣f ∧
      0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0)
theorem small_marks_at_first_band {w s T} (W : Word 179798 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤47) (caps : ∀ i, axis f i≤2400) :
    (smallMarks T label s f).card≤8*((2400+47*128)+K1.p*(2400+47*128))+4*47 := by
  let U:=smallMarks T label s f
  have sub : U⊆T := Finset.filter_subset _ _
  have word : Word 179798 133606 w s U :=
    ⟨W.distinct.mono sub,fun γ h => W.degree _ (sub h),fun γ h => W.hits _ (sub h)⟩
  have h:=low_component_count word label (inj.mono sub) f ne caps
    (fun γ h => (Finset.mem_filter.mp h).2)
  apply h.trans
  unfold lowFee
  calc
    _ ≤ 8*(2400+K1.p*2400)+(8*128*(K1.p+1)+4)*47 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add (caps 0) (Nat.mul_le_mul_left _ (caps 1))))
        (Nat.mul_le_mul_left _ degree)
    _ = _ := by ring
#print axioms small_marks_at_first_band
end Lower6960

end
end Merged_R6960QuadraticCount

-- merged module R6960TerminalSmall
section Merged_R6960TerminalSmall
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalSmall
open Polynomial Finset
open K1 (K)
open K1_14 (Equation atMark atX graphEval)
open RetainedShortening (Word)
open KoalaRect (axisDegree axisDegree_le_iff axisDegree_mul)
open RescueGeometry (Model Family)
def fee (f : Equation) : ℕ :=
  18*(axisDegree f 0+K1.p*axisDegree f 1)+(K1.p+1)*(axisDegree f 0+axisDegree f 1)+4*f.natDegree
private theorem one {w s T} (W : Word 179798 164690 w s T)
    (label : K→K) (inj : Set.InjOn label (T:Set K)) (q : Equation)
    (nq : q≠0) (pos : 0<q.natDegree) (dy : q.natDegree≤2)
    (cap : axisDegree q 0+axisDegree q 1≤2400)
    (roots : ∀ γ∈T,atMark q (label γ) (s γ)=0) : T.card≤fee q := by
  let v:=axisDegree q 0
  let u:=axisDegree q 1
  let b:=(v+u)/18
  have vmax : v+b+1≤19*(b+1) := by dsimp [b]; omega
  have umax : u+b+1≤19*(b+1) := by dsimp [b]; omega
  have shape : 3*(v+b+1)*(u+b+1)*(2*164690) < (b+1)*(b+1)*(K1.p/2) := by
    calc _ ≤ 3*(19*(b+1))*(19*(b+1))*(2*164690) := by gcongr
         _ = (b+1)*(b+1)*(3*19*19*(2*164690)) := by ring
         _ < _ := Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
  have sz : v+u≤2400 := cap
  have charge := small_ordinate_count_at_scale (k:=18) (b:=b) W label inj (by decide)
    (Or.inl (by decide)) q nq dy
    (fun i=>⟨(axisDegree_le_iff q 0 _).mp le_rfl i,(axisDegree_le_iff q 1 _).mp le_rfl i⟩)
    (by change v+b<2130706433; dsimp [b]; omega) shape (by decide) roots
  have hb : 18*b≤v+u := by dsimp [b]; omega
  have hpay := Nat.mul_le_mul_left (K1.p+1) hb
  change T.card≤18*(v+b+K1.p*(u+b))+4 at charge
  change T.card≤18*(v+K1.p*u)+(K1.p+1)*(v+u)+4*q.natDegree
  calc _ ≤ _ := charge
       _ = 18*(v+K1.p*u)+(K1.p+1)*(18*b)+4 := by ring
       _ ≤ _ := by omega
theorem covered {w s T} (W : Word 179798 164690 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) (f : Equation) :
    f≠0 → axisDegree f 0+axisDegree f 1≤2400 →
    (∀ γ∈T,∃ q : Equation,Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤fee f := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f hu =>
    intro _ _ cover
    have empty : T=∅ := eq_empty_iff_forall_notMem.mpr (fun γ h=>by
      obtain ⟨q,ir,dv,_⟩ := cover γ h
      exact ir.not_isUnit (isUnit_of_dvd_unit dv hu))
    simp [empty]
  | mul g q ng ir ih =>
    intro nz cap cover
    let U:=smallMarks T label s g
    let V:=T\U
    have us : U⊆T := filter_subset _ _
    have vs : V⊆T := sdiff_subset
    have word (R) (sub : R⊆T) : Word 179798 164690 w s R :=
      ⟨W.distinct.mono sub, fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
    have a0 := axisDegree_mul ir.ne_zero ng 0
    have a1 := axisDegree_mul ir.ne_zero ng 1
    have ca := ih (word U us) (inj.mono us) ng (by omega) (fun γ h=>(mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,il,dv,pos,dg,zr⟩ := cover γ (vs h)
      have dl : l∣q := (il.prime.dvd_mul.mp dv).resolve_right
        (fun d=>(mem_sdiff.mp h).2 (mem_filter.mpr ⟨vs h,l,il,d,pos,dg,zr⟩))
      have asso:=il.associated_of_dvd ir dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl ir.ne_zero),
        (natDegree_le_of_dvd asso.symm.dvd il.ne_zero).trans dg,?_⟩
      obtain ⟨a,eq⟩ := dl
      change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [eq,atMark,eval₂_mul,zr,zero_mul]
    have cb : V.card≤fee q := by
      rcases V.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
      · simp [empty]
      exact one (word V vs) label (inj.mono vs) q ir.ne_zero (rest γ hγ).1 (rest γ hγ).2.1
        (by omega) (fun t ht=>(rest t ht).2.2)
    have card : V.card+U.card=T.card := card_sdiff_add_card_eq_card us
    calc T.card = V.card+U.card := card.symm
         _ ≤ fee q+fee g := Nat.add_le_add cb ca
         _ = _ := by unfold fee; rw [a0,a1,natDegree_mul ir.ne_zero ng]; ring
def smallCap : ℕ := (19*K1.p+1)*2400+4*47
theorem small_marks {w s T} (W : Word 179798 164690 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) {f : Equation} (ne : f≠0) (deg : f.natDegree<48)
    (axes : axisDegree f 0+axisDegree f 1≤2400) :
    (smallMarks T label s f).card≤smallCap := by
  classical
  let U:=smallMarks T label s f
  have sub : U⊆T := filter_subset _ _
  have word : Word 179798 164690 w s U :=
    ⟨W.distinct.mono sub,fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
  have paid:=covered word label (inj.mono sub) f ne axes (fun γ h=>(mem_filter.mp h).2)
  refine paid.trans ?_
  unfold fee smallCap
  change 18*(_+2130706433*_)+2130706434*(_+_)+4*_ ≤ (19*2130706433+1)*2400+4*47
  omega
#print axioms small_marks
private theorem root_factor {f : Equation} (nf : f≠0) (z : K) (S : (Polynomial K))
    (root : atMark f z S=0) : ∃ q : Equation,Irreducible q ∧ q∣f ∧ atMark q z S=0 := by
  let ev := eval₂RingHom (graphEval z) (atX S)
  change ev f=0 at root
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (nf rfl).elim
  | unit u hu => exact ((hu.map ev).ne_zero root).elim
  | mul g q ng ir ih =>
    rw [map_mul,mul_eq_zero] at root
    rcases root with r | r
    · exact ⟨q,ir,dvd_mul_right ..,r⟩
    · obtain ⟨a,ia,dv,hit⟩ := ih ng r
      exact ⟨a,ia,dv.trans (dvd_mul_left ..),hit⟩
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open TerminalReceipts (witness)
theorem higher_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2402≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33619) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (T : Finset K) (f : Equation), T⊆Γ ∧ Γ.card≤MainGeometry.prefixCap+smallCap+T.card ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈T, ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ)=0 := by
  classical
  rcases TerminalDegrees.retained_equation F Crt lo hi regular residues with closed |
    ⟨paid,f,cost,primitive,sep,pos,deg,axes,graded,roots⟩
  · exact Or.inl closed
  let U:=Γ\paid
  let L:=smallMarks U M.label F.scalar f
  let T:=U\L
  have us : U⊆Γ := sdiff_subset
  have ls : L⊆U := filter_subset _ _
  have ts : T⊆U := sdiff_subset
  have W : Word 179798 164690 M.word F.scalar U := by
    refine ⟨F.distinct.mono us,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (us hγ)).scalar_degree with zero | degree
      · simp [zero]
      · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at degree
        omega
    · intro γ hγ
      let B:=F.mark γ (us hγ)
      exact ⟨B.bad.support,B.bad.agreement,B.scalar_hits⟩
  have lc := small_marks W M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq) primitive.ne_zero deg axes
  have card : T.card+L.card=U.card := card_sdiff_add_card_eq_card ls
  have base : Γ.card≤U.card+paid.card := by
    calc Γ.card ≤ (U∪paid).card := Finset.card_le_card (by
           intro γ hγ; by_cases hit : γ∈paid
           · exact mem_union_right _ hit
           · exact mem_union_left _ (mem_sdiff.mpr ⟨hγ,hit⟩))
         _ ≤ _ := card_union_le ..
  refine Or.inr ⟨T,f,ts.trans us,by change L.card≤_ at lc; omega,primitive,sep,deg,axes,graded,?_⟩
  intro γ hγ
  obtain ⟨q,ir,dv,hit⟩ := root_factor primitive.ne_zero _ _ (roots γ (us (ts hγ)) (mem_sdiff.mp (ts hγ)).2)
  have positive : 0<q.natDegree := by
    by_contra! zero
    have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero zero)
    exact ir.not_isUnit (eq ▸ (primitive _ (eq ▸ dv)).map C)
  refine ⟨q,ir,dv,?_,hit⟩
  by_contra! sm
  exact (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨ts hγ,q,ir,dv,positive,by omega,hit⟩)
#print axioms higher_remainder
end Lower6960.TerminalSmall

end
end Merged_R6960TerminalSmall
