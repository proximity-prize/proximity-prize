import ProximityPrize.SubmissionLower.KoalaCompressedEquation
import ProximityPrize.SubmissionLower.R6960QuadraticProjection

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

/-- Compress the marked relation using half the characteristic as the degree
budget, then count every projected factor, including factors of lower degree. -/
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

/-- Small-ordinate retained row for the first 69.60 high band. -/
theorem first_band_small_ordinate {w s T} (W : Word 179827 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤2)
    (axes : ∀ i, (f.coeff i).degreeOf 0≤2400 ∧ (f.coeff i).degreeOf 1≤2400)
    (marks : ∀ γ∈T, atMark f (label γ) (s γ)=0) :
    T.card≤43091406921220 := by
  have h := small_ordinate_count (v:=2400) (u:=2400) (b:=128) W label inj
    (by decide) (Or.inr (by decide)) f ne degree axes (by decide) (by decide) (by decide) marks
  exact h.trans (by decide)

#print axioms first_band_small_ordinate

/-- Seed degree with the ordinate treated as a separate variable. -/
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

/-- All marks of a projected product assigned to a linear or quadratic factor
share the original seed budget. The other factors may have any degree. -/
theorem low_component_count {w s T} (W : Word 179827 133606 w s T)
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
    have subword (R) (sub : R⊆T) : Word 179827 133606 w s R :=
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

/-- The actual subset of marks lying on small positive-ordinate factors. -/
def smallMarks (T : Finset K1.K) (label : K1.K → K1.K) (s : K1.K → (Polynomial K1.K)) (f : Equation) :
    Finset K1.K := T.filter (fun γ => ∃ q : Equation, Irreducible q ∧ q∣f ∧
      0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0)

theorem small_marks_at_first_band {w s T} (W : Word 179827 133606 w s T)
    (label : K1.K → K1.K) (inj : Set.InjOn label (T : Set K1.K))
    (f : Equation) (ne : f≠0) (degree : f.natDegree≤47) (caps : ∀ i, axis f i≤2400) :
    (smallMarks T label s f).card≤8*((2400+47*128)+K1.p*(2400+47*128))+4*47 := by
  let U:=smallMarks T label s f
  have sub : U⊆T := Finset.filter_subset _ _
  have word : Word 179827 133606 w s U :=
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
