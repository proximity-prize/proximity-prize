import ProximityPrize.SubmissionLower.MinimumPoleTwoBlockFrame
import ProximityPrize.SubmissionLower.ResidualReconstruction

open scoped BigOperators Polynomial
open Polynomial

namespace PeriodTwoPrefixReconstruction

variable {F : Type*} [Field F]

/-- Keep the ambient degree bound and remove one dimension for each
persistent site, up to the number of unrestricted quotient coefficients. -/
theorem residual_frame (G : F[X]) (n d : ℕ) (R : Fin 2 → F[X])
    (sites : Finset F) (off : ∀ x ∈ sites, G.eval x ≠ 0)
    (hdegree : ResidueSpace.space G n R ≤ degreeLT F d) :
    ∃ V : Submodule F F[X],
      V ≤ degreeLT F d ∧ Module.finrank F V ≤ n + 2 - min sites.card n ∧
      ∀ Q : F[X], Q ∈ ResidueSpace.space G n R →
        (∀ x ∈ sites, Q.eval x = 0) → Q ∈ V := by
  classical
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq
    (s := sites) (min_le_left sites.card n)
  let W := ResidueSpace.space G n R
  let U := LinearMap.ker (ResidueSpace.evaluate G n R T)
  let V := U.map W.subtype
  have hsize : T.card ≤ n := hcard.trans_le (min_le_right sites.card n)
  have hr := ResidueSpace.remaining_finrank G n R T hsize
    (fun x hx => off x (hT hx))
  refine ⟨V, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨P, _, rfl⟩ := Submodule.mem_map.mp hQ
    exact hdegree P.property
  · change Module.finrank F V ≤ _
    rw [← (Submodule.equivMapOfInjective W.subtype W.subtype_injective U).finrank_eq]
    simpa only [U,hcard,Fintype.card_fin] using hr
  · intro Q hQ hzero
    refine Submodule.mem_map.mpr ⟨⟨Q,hQ⟩, ?_, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext x
    exact hzero x.val (hT x.property)

/-- At height 2429 the affine residual space has a basis of size at most
one plus the shortened Taylor order. Its degree window stays at 133501. -/
theorem residual_frame_2429 (G : F[X]) (R : Fin 2 → F[X]) (sites : Finset F)
    (off : ∀ x ∈ sites, G.eval x ≠ 0)
    (hdegree : ResidueSpace.space G 128643 R ≤ degreeLT F 133501) :
    ∃ V : Submodule F F[X],
      V ≤ degreeLT F 133501 ∧
      Module.finrank F V ≤ max 1 (128644-sites.card) + 1 ∧
      ∀ Q : F[X], Q ∈ ResidueSpace.space G 128643 R →
        (∀ x ∈ sites, Q.eval x = 0) → Q ∈ V := by
  obtain ⟨V,hV,hr,hmem⟩ := residual_frame G 128643 133501 R sites off hdegree
  refine ⟨V,hV,hr.trans ?_,hmem⟩
  omega

/-- Affine weights for a fixed word, valid for every polynomial in the
two-block frame that hits the given sites. The target field and symbolic
center can be those used by either high Taylor section constructor. -/
theorem interpolation_weights_2429 {L : Type*} [Field L] {p : ℕ} [CharP F p]
    (G : F[X]) (R : Fin 2 → F[X]) (sites : Finset F) (w : F → F)
    (off : ∀ x ∈ sites, G.eval x ≠ 0)
    (hdegree : ResidueSpace.space G 128643 R ≤ degreeLT F 133501)
    (hp : 133501 ≤ p) (e : F →+* L) (center : L)
    (injective : Function.Injective (Polynomial.eval₂RingHom e center)) :
    let t := max 1 (128644 - sites.card)
    ∃ c : F → L, ∃ A : F → Fin (t+1) → L,
      ∀ (x : F) (Q : F[X]), Q ∈ ResidueSpace.space G 128643 R →
        (∀ z ∈ sites, Q.eval z = w z) →
        e (Q.eval x) = c x + ∑ j, A x j * (taylor center (Q.map e)).coeff j := by
  classical
  let t := max 1 (128644 - sites.card)
  change ∃ c : F → L, ∃ A : F → Fin (t+1) → L,
    ∀ (x : F) (Q : F[X]), Q ∈ ResidueSpace.space G 128643 R →
      (∀ z ∈ sites, Q.eval z = w z) →
      e (Q.eval x) = c x + ∑ j, A x j * (taylor center (Q.map e)).coeff j
  by_cases hex : ∃ Q : F[X], Q ∈ ResidueSpace.space G 128643 R ∧
      ∀ z ∈ sites, Q.eval z = w z
  · obtain ⟨Q₀,hQ₀,hfix⟩ := hex
    obtain ⟨V,hV,hr,hres⟩ := residual_frame_2429 G R sites off hdegree
    let φ := Polynomial.eval₂RingHom e center
    obtain ⟨B,hB⟩ := ResidualReconstruction.at_node V (hV.trans (degreeLT_mono hp))
      φ injective
    let r := Module.finrank F V
    let ι : Fin r ↪ Fin (t+1) := Fin.castLEEmb hr
    let A (x : F) (j : Fin (t+1)) : L :=
      if hj : j.val < r then B x ⟨j.val,hj⟩ else 0
    have hpad (x : F) (f : Fin (t+1) → L) :
        (∑ j, A x j * f j) = ∑ j : Fin r, B x j * f (ι j) := by
      let T := (Finset.univ : Finset (Fin r)).map ι
      calc
        _ = ∑ j ∈ T, A x j * f j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ T)
          intro j _ hj
          have h : ¬j.val < r := by
            intro hij
            apply hj
            exact Finset.mem_map.mpr ⟨⟨j.val,hij⟩,Finset.mem_univ _,Fin.ext rfl⟩
          simp [A,h]
        _ = _ := by
          rw [show T = (Finset.univ : Finset (Fin r)).map ι from rfl, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j _
          change (if h : j.val < r then B x ⟨j.val,h⟩ else 0) * f (ι j) = _
          rw [dif_pos j.isLt]
    have hTaylor (Q : F[X]) (j : ℕ) :
        φ (hasseDeriv j Q) = (taylor center (Q.map e)).coeff j := by
      change eval₂ e center (hasseDeriv j Q) = _
      rw [taylor_coeff,hasseDeriv_map,eval_map]
    have hC (y : F) : φ (C y) = e y := by
      change eval₂ e center (C y) = _
      rw [eval₂_C]
    let sum (x : F) (Q : F[X]) :=
      ∑ j : Fin (t+1), A x j * (taylor center (Q.map e)).coeff j
    refine ⟨fun x => e (Q₀.eval x) - sum x Q₀,A,?_⟩
    intro x Q hQ hsites
    have hdiff : Q - Q₀ ∈ V := by
      apply hres _ (Submodule.sub_mem _ hQ hQ₀)
      intro z hz
      rw [eval_sub,hsites z hz,hfix z hz,sub_self]
    have heval : sum x (Q - Q₀) = e ((Q - Q₀).eval x) := by
      dsimp only [sum]
      rw [hpad, ← hC]
      change (∑ j : Fin r, B x j * (taylor center ((Q-Q₀).map e)).coeff j.val) =
        φ (C ((Q-Q₀).eval x))
      simpa only [hTaylor] using hB x ⟨Q - Q₀,hdiff⟩
    have hsum : sum x Q - sum x Q₀ = e (Q.eval x) - e (Q₀.eval x) := by
      simpa only [sum,← hTaylor,map_sub,eval_sub,mul_sub,Finset.sum_sub_distrib]
        using heval
    change e (Q.eval x) = e (Q₀.eval x) - sum x Q₀ + sum x Q
    calc
      _ = (e (Q.eval x) - e (Q₀.eval x)) + e (Q₀.eval x) := (sub_add_cancel _ _).symm
      _ = _ := by
        rw [← hsum]
        simp only [sub_eq_add_neg]
        ac_rfl
  · refine ⟨fun _ => 0,fun _ _ => 0,?_⟩
    intro _ Q hQ hsites
    exact (hex ⟨Q,hQ,hsites⟩).elim

/-- Indexed physical sites, in the form required by the section constructors. -/
theorem indexed_interpolation_weights_2429
    {I L : Type*} [Field L] {p : ℕ} [CharP F p]
    (G : F[X]) (R : Fin 2 → F[X]) (node : I ↪ F) (sites : Finset I) (w : I → F)
    (off : ∀ i ∈ sites, G.eval (node i) ≠ 0)
    (hdegree : ResidueSpace.space G 128643 R ≤ degreeLT F 133501)
    (hp : 133501 ≤ p) (e : F →+* L) (center : L)
    (injective : Function.Injective (Polynomial.eval₂RingHom e center)) :
    let t := max 1 (128644 - sites.card)
    ∃ c : F → L, ∃ A : F → Fin (t+1) → L,
      ∀ (x : F) (Q : F[X]), Q ∈ ResidueSpace.space G 128643 R →
        (∀ i ∈ sites, Q.eval (node i) = w i) →
        e (Q.eval x) = c x + ∑ j, A x j * (taylor center (Q.map e)).coeff j := by
  classical
  let word (z : F) : F :=
    if h : ∃ i, node i = z then w (Classical.choose h) else 0
  have hword (i : I) : word (node i) = w i := by
    have h : ∃ j, node j = node i := ⟨i,rfl⟩
    rw [show word (node i) = w (Classical.choose h) from dif_pos h]
    exact congrArg w (node.injective (Classical.choose_spec h))
  have hoff : ∀ z ∈ sites.map node, G.eval z ≠ 0 := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
    exact off i hi
  have hw := interpolation_weights_2429 G R (sites.map node) word hoff hdegree hp e center injective
  dsimp only at hw
  rw [Finset.card_map] at hw
  obtain ⟨c,A,hA⟩ := hw
  refine ⟨c,A,?_⟩
  intro x Q hQ hs
  refine hA x Q hQ ?_
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hz
  rw [hs i hi,hword]

/-- Injectivity at the symbolic abscissa follows from the ordinary
coefficient map and the embedding into the rational function field. -/
theorem eval₂_symbol_injective {E L : Type*} [Field E] [Field L]
    (lift : F →+* E) (toCenter : E[X] →+* L) (hinj : Function.Injective toCenter) :
    Function.Injective (Polynomial.eval₂RingHom
      (toCenter.comp ((C : E →+* E[X]).comp lift)) (toCenter (Polynomial.X : Polynomial E))) := by
  have heq : Polynomial.eval₂RingHom
      (toCenter.comp ((C : E →+* E[X]).comp lift)) (toCenter (Polynomial.X : Polynomial E)) =
        toCenter.comp (Polynomial.mapRingHom lift) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [Polynomial.coe_eval₂RingHom,eval₂_C,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_C]
    · simp only [Polynomial.coe_eval₂RingHom,eval₂_X,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_X]
  rw [heq]
  exact hinj.comp (Polynomial.map_injective lift lift.injective)

end PeriodTwoPrefixReconstruction

#print axioms PeriodTwoPrefixReconstruction.indexed_interpolation_weights_2429
