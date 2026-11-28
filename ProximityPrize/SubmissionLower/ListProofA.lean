import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast074

set_option Elab.async false

-- merged module PortHighBase
section Merged_PortHighBase

-- merged module PortBase
section Merged_PortBase
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
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  dsimp only [L, t, heightCap, blockLength, agreement, k, frontLimit] at h hr ⊢
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
theorem type_one_bad_count_of_syndromes {F ι : Type}
    [Field F] [Fintype ι] [DecidableEq ι] (x u v : ι → F) (hx : Function.Injective x)
    (k a p : ℕ) (hk : k ≤ Fintype.card ι) (hp : 1 < p)
    (htype : Principal.TypeOneSyndromes x u v k p)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k a γ) :
    Γ.card ≤ 1 :=
  Principal.type_one_bad_count x hx u v k a p hk hp htype Γ hΓ
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
private theorem coefficientKernel_annihilates (p : ℕ) (x u v : ι → F) (L t : ℕ)
    (c : Fin (t + 1) → F) (hc : (coefficientBlocks p x u v L t).mulVec c = 0) :
    (stacked p x u v L t).mulVec (fun j => C (c j)) = 0 := by
  funext i
  have h0 := congrFun hc (0, i.2)
  have h1 := congrFun hc (1, i.2)
  have h2 := congrFun hc (2, i.2)
  have h3 := congrFun hc (3, i.2)
  simp only [Matrix.mulVec, dotProduct, coefficientBlocks, Fin.reduceEq,
    ite_true, ite_false, Pi.zero_apply] at h0 h1 h2 h3
  by_cases hi : i.1 = 0
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_true, hankel, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) * c j) +
          Polynomial.X (R := F) * C (∑ j, syndrome x v (i.2.val + j.val) * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h0, h1, map_zero, mul_zero, add_zero]
  · simp only [Matrix.mulVec, dotProduct, stacked, hi, ite_false, Pi.zero_apply]
    calc
      _ = C (∑ j, syndrome x u (i.2.val + j.val) ^ p * c j) +
          Polynomial.X (R := F) ^ p * C (∑ j, syndrome x v (i.2.val + j.val) ^ p * c j) := by
        rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul]
        ring
      _ = 0 := by simp only [h2, h3, map_zero, mul_zero, add_zero]
theorem constantRankCount {E : Type} [Field E]
    (φ : (Polynomial F) →+* E) (hφ : Function.Injective φ) (p : ℕ) [ExpChar F p] (hp : 1 ≤ p)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L t : ℕ) (hkA : k < A) (hL : k + L = A)
    (ht : A + t = Fintype.card ι)
    (r : ℕ) (hgeneric : ((stacked p x u v L t).map φ).rank = r)
    (hconstant : (coefficientBlocks p x u v L t).rank = r)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, Principal.BadSlope x u v k A γ) : Γ.card ≤ p * r := by
  let M := stacked p x u v L t
  let C₀ := coefficientBlocks p x u v L t
  let W := LinearMap.ker C₀.mulVecLin
  obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ M r hgeneric
  have hWdim : Module.finrank F W = t + 1 - r := by
    have h := LinearMap.finrank_range_add_finrank_ker C₀.mulVecLin
    change (coefficientBlocks p x u v L t).rank + Module.finrank F W = _ at h
    rw [hconstant, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hW (c : Fin (t + 1) → F) (hc : c ∈ W) :
      M.mulVec (fun j => C (c j)) = 0 :=
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
def nativeMoments (u : Words) : Fin 2 → ℕ → Frac :=
  fun b j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) b j)
theorem independent_nativeMoments (u : Words)
    (h : ¬ TypeAtMostOne u) : IndependentMoments (nativeMoments u) k := by
  classical
  unfold IndependentMoments
  by_contra! hall
  apply h
  unfold TypeAtMostOne Principal.TypeOneSyndromes
  rw [IRSProfile.card_index]
  intro i j
  apply IsFractionRing.injective (Polynomial K) Frac
  simpa [nativeMoments, Principal.parameterSyndromes, map_mul] using hall i j
end
end P0
end

end Merged_PortBase

-- merged module PortHighBase
section Merged_PortHighBase
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K k p node twist agreement t heightCap highPrefix)
open K1_14 (L FX Seeds Equation Jet Shape Band Banks liftPoly graphEval atX
  triangle slots shapeSum sourceDebit seedHasse SeedBound)
open K1_14_3 (Surface Parent NoMovingCommon Compatible RowCaps ProjectedProduct)
open scoped BigOperators
def AdjacentChart {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
def band (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554,6,188,1024,1422,290,28962⟩
  else if w ≤ 8249 then ⟨8249,4,96,582,809,165,11805⟩
  else if w ≤ 23999 then ⟨23999,4,46,582,809,165,8216⟩
  else ⟨heightCap, 4,35,582,809,165,7295⟩
def freeShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨55,76,17,1036⟩,⟨82,113,25,1601⟩] i
  else ![⟨34,47,10,515⟩,⟨58,80,17,940⟩] i
def movingShape (w : ℤ) (i : Fin 2) : Shape :=
  if w ≤ 3554 then ![⟨138,191,39,4990⟩,⟨203,282,58,7726⟩] i
  else ![⟨67,93,18,1857⟩,⟨124,172,35,3138⟩] i
def reserve (i : Fin 2) : ℕ := ![0,5] i
def terminalShape (w : ℤ) : Shape :=
  let b := band w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩
def fullShape (w : ℤ) : Shape :=
  { terminalShape w with U := if w ≤ 3554 then 141471 else 59515 }
def fullCutoff (s : Shape) : ℕ := s.m * agreement - 1
def reserveCutoff (w : ℤ) (s : Shape) (i : Fin 2) : ℕ :=
  fullCutoff s - 2 * w.toNat * reserve i
structure BufferedPair (w : ℤ) (rows : Banks) (i : Fin 2) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows (freeShape w i) (reserveCutoff w (freeShape w i) i)
  moving_mem : moving ∈ rows (movingShape w i) (reserveCutoff w (movingShape w i) i)
  no_moving : NoMovingCommon free moving
def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal
def PairPass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ Compatible pair.free pair.moving q
def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))
def rawWidth (w : ℤ) (q j : ℕ) : ℕ :=
  (band w).multiplicity * agreement + j - q * (131071 - w.toNat)
def rawVolume (w : ℤ) : ℕ :=
  triangle (band w).subbankSeeds * shapeSum (terminalShape w) (rawWidth w)
def forcedPower (w : ℤ) (W j : ℕ) : ℕ :=
  1 + (fullCutoff (terminalShape w) - W) / (2 * w.toNat) - j
def TerminalDivisibility (w : ℤ) (rows : Banks) (f : Equation) : Prop :=
  ∀ W < (band w).multiplicity * agreement, ∀ P ∈ rows (terminalShape w) W, P ≠ 0 →
    f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff
def curveFactor (d : ℕ) : ℕ := t / (agreement - d) + 1
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, PairPass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily K p node twist agreement )
open K1_14 (L FX Seeds Equation Banks liftPoly graphEval atX atMark
  seedEmbedding SeedBound frobenius_coefficient_exception_count)
open scoped BigOperators
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset Polynomial
open P0 (agreement)
open K1_14 (FX Jet Equation shapeSum slots triangle SeedBound)
open K1_14_4 (gradeWidth seedDegree seedDegree_le_iff seedDegree_pow )
open K1_14_4 (shapeSum_swap gradeWidth_card position_sum)
open K1_14_4 (gradeMap mem_filtered finrank_le_grades)
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open P0 (K I node agreement)
open K1_14_6 (occupancy)
structure FixedWord (w : I → K) (T : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩
theorem incidence_arithmetic (errors m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x) (he : 0 < errors)
    (hsecond : (m*x)^2 ≤ (x+errors) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+errors)*cap) :
    gap*m ≤ errors*cap + gap := by
  have hcancel : m*x^2 ≤ (x+errors) * (x + (m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsecond
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := Int.ofNat_sub (by omega)
  have hX : ((x - gap : ℕ) : ℤ) = (x : ℤ)-gap := Int.ofNat_sub hx
  have hcancelZ := Int.ofNat_le.mpr hcancel
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*errors - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*errors*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (errors : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*errors < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*errors - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*errors := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*errors*x ≤ (cap : ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible, bigger]
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < agreement) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (agreement - d) * T.card ≤ P0.t * cap + (agreement - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (agreement - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : agreement ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := agreement - common.card
  let t := d - common.card
  have ht : t = x - (agreement - d) := by dsimp [t, x]; omega
  have hx : agreement - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + P0.t := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change 262144 - common.card = (180217 - common.card) + 81927
    have hbound : common.card ≤ 180217 := hcommon.trans hd.le
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic P0.t _ _ _ _ (by omega) (by omega) hx (by decide) second first
end
end P0_10
end
section
namespace P0_10
noncomputable section
open Finset MvPolynomial
open P0 (K I node agreement)
open K1_14_6 (LinearCover LinearRing ClosedField mixedDegree)
open K1_14_6 (card_le_sum_cover curve_degree_nat)
open K1_14_6.LinearCover (slice «section» cut_data zero_dim_count)
open scoped BigOperators Polynomial
private theorem curve_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < agreement)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hδdeg⟩ := curve_degree_nat P hP hdim
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ δ := by
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := LinearCover.section C P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := LinearCover.cut_data C hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((LinearCover.slice C V Q).card : ℚ) ≤ affineDegree Q := by
      have hQdim := (dims Q hQ).2
      rw [hdim] at hQdim
      exact LinearCover.zero_dim_count C ((filter_subset _ _).trans ((filter_subset _ _).trans hU))
        Q (by omega) (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((LinearCover.slice C V Q).card : ℚ) := by
      exact_mod_cast hsum
    have hbound := hsumQ.trans ((sum_le_sum hone).trans (degree.trans_eq hδdeg))
    exact_mod_cast hbound
  have hcount := section_capacity hword hd δ hsection
  let gap := agreement - d
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hfactor : P0.t < gap * curveFactor d := by
    change P0.t < gap * (P0.t / gap + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have heq := Nat.mod_add_div P0.t gap
    have hr := Nat.mod_lt P0.t hgap
    omega
  suffices hcard : U.card ≤ curveFactor d * δ by
    rw [hδdeg, ← Nat.cast_mul]
    exact_mod_cast hcard
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left gap (show curveFactor d * δ + 1 ≤ U.card by omega)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hfactor hδ
  change gap * U.card ≤ P0.t * δ + gap at hcount
  omega
end
end P0_10
end
section
namespace P0_10
noncomputable section
open P0
open K1_14 (Equation SeedBound atMark)
open K1_14_6 (mixedDegree)
end
end P0_10
end
section
set_option backward.isDefEq.respectTransparency false
namespace P0_10_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10 (AdjacentChart)
open K1_14 (L liftPoly)
open K1_14_1 Polynomial
open scoped Polynomial
open K1_14_1_1 (blockContribution)
set_option maxHeartbeats 800000 in
theorem crt_lift {h : ℕ} (D : PoleData h) : Nonempty (CRTLift D) := by
  choose d N hN using blockContribution D
  exact ⟨⟨d, N, fun i => (hN i).1, fun i => (hN i).2.1, fun i => (hN i).2.2.1,
    fun i => (hN i).2.2.2.1, fun i => (hN i).2.2.2.2⟩⟩
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I K node)
open K1_14 (L Shape Jet liftPoly jetAt shapeSum)
open K1_14_1 K1_14_1_5 Polynomial
open K1_14_1_2 (span_vanish composed composed_degree specialized_poles composed_contact)
open scoped Polynomial BigOperators
open K1_14_1_5 (finrank_ambient trueWidth trueWidth_eq_add)
private theorem zero_of_poles_and_hits {h A : ℕ} {D : PoleData h}
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    {s : Shape} {W : ℕ} {Q : (Polynomial L)}
    (hdeg : Q.natDegree ≤ W+(s.B+s.J)*(2*h))
    (hpole : poleProduct D ^ (s.B+s.J) ∣ Q)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hcontact : ∀ k ∈ hits, (Polynomial.X-C (nodeL k)) ^ s.m ∣ Q)
    (hW : W < s.m*A) : Q = 0 := by
  by_contra hne
  obtain ⟨T, hT⟩ := hpole
  have hTne : T ≠ 0 := by intro he; simp [hT, he] at hne
  have hmonic : (poleProduct D).Monic := (D.monic 0).mul (D.monic 1)
  have hDdeg : (poleProduct D).natDegree = 2*h := by
    rw [poleProduct, natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero, D.degree, D.degree]
    omega
  have hTdeg : T.natDegree ≤ W := by
    rw [hT, natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne, natDegree_pow, hDdeg] at hdeg
    omega
  have hroot (k : I) : IsCoprime (Polynomial.X-C (nodeL k)) (poleProduct D) := by
    refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    simpa [IsRoot, poleProduct] using mul_ne_zero (hnode 0 k) (hnode 1 k)
  have hcontacts (k : I) (hk : k ∈ hits) : (Polynomial.X-C (nodeL k)) ^ s.m ∣ T :=
    ((hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hcontact k hk))
  have hinj : Function.Injective nodeL := (algebraMap K L).injective.comp node.injective
  have hh := K1_11.eq_zero_of_many_contacts hits nodeL hinj s.m T hcontacts
    (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard)))
  exact hTne hh
theorem contact_vanish {h A : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (hnode : ∀ i k, (D.block i).eval (nodeL k) ≠ 0)
    (z : K) (S : (Polynomial K)) (hres : MarkResidues D z S)
    (hdeg : (liftPoly S).natDegree ≤ 131071+h)
    (hits : Finset I) (hcard : A ≤ hits.card)
    (hhits : ∀ k ∈ hits, (liftPoly S).eval (nodeL k) = word k)
    (s : Shape) (W : ℕ) (hW : W < s.m*A) (P : Jet)
    (hP : P ∈ evaluated Crt word s W) : jetAt P z S = 0 := by
  apply span_vanish z S _ hP
  intro Q hQ
  obtain ⟨⟨ha, hc⟩, hp⟩ := hQ
  exact zero_of_poles_and_hits hnode (composed_degree ha _ _ hdeg)
    (specialized_poles Crt hres hp) hits hcard
    (fun k hk => composed_contact hc _ _ k (hhits k hk)) hW
theorem ambient_bound {h : ℕ} (hhi : h ≤ 131071) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) :
    rawVolumeAt h s W + poleCredit h s ≤ Module.finrank L (ambient h s W) := by
  rw [finrank_ambient]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W + 1 + j - q * (131071 - h)) +
        2 * h * shapeSum s (fun q _ => s.B + s.J - q) := by
    unfold shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add hhi hw (by simpa using hq) (by simpa using hj)
  simp only [hsum, rawVolumeAt, poleCredit, Nat.mul_add, Nat.mul_assoc, Nat.le_refl]
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L Shape Jet)
open K1_14_1 Polynomial
open K1_14_1_4 (Bounded forward_apply rawBlock_degree quotient_positions rawOrdinate rawVelocity
  substitute_C substitute_X)
open scoped Polynomial BigOperators
open K1_14_1_4 (bounded_mono bounded_add bounded_sum bounded_mul bounded_jetConstant bounded_y bounded_v bounded_pow crt_degree ambient_degree)
open K1_14_1_4 (rawPosition specialized_center specialized_leading specialized doubleMap)
private theorem forward_bounded {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    {s W P} (hp : P ∈ ambient h s W) :
    Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) (forward Crt P) := by
  let u := 131071-h
  let v := u-1
  have huv : v+1 = u := by dsimp [u, v]; omega
  have hd : 131071+h = 2*h+u := by dsimp [u]; omega
  have hy : Bounded u v (2*h+u) (rawOrdinate D Crt) :=
    bounded_add (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_y u v))
      (bounded_jetConstant ((crt_degree D Crt).trans (by omega)))
  have hv : Bounded u v (2*h+v) (rawVelocity D Crt) := by
    have hh' : (rawBlock D).derivative.natDegree ≤ 2*h-1 :=
      (natDegree_derivative_le _).trans (by rw [rawBlock_degree])
    refine bounded_add (bounded_add
      (bounded_mul (bounded_jetConstant (rawBlock_degree D).le) (bounded_v u v)) ?_) ?_
    · exact bounded_mono (bounded_mul (bounded_jetConstant hh') (bounded_y u v)) (by omega)
    · exact bounded_jetConstant (((natDegree_derivative_le _).trans
        (Nat.sub_le_sub_right (crt_degree D Crt) 1)).trans (by omega))
  change Bounded u v _ (forward Crt P)
  rw [forward_apply, P.as_sum_support_C_mul_X_pow, map_sum]
  apply bounded_sum
  intro j hj
  rw [map_mul, map_pow, (P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [substitute_C, substitute_X]
  simp only [map_sum, map_mul, map_pow, Finset.sum_mul]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X, RingHom.comp_apply]
  apply bounded_sum
  intro i hi
  have hdeg := ambient_degree hp (mem_support_iff.mp hi)
  have hw : ((P.coeff j).coeff i).natDegree + (2*h+u)*i + (2*h+v)*j ≤
      W+(s.B+s.J)*(2*h) := by
    have hjmul : j*(2*h+u) = (2*h+v)*j+j := by
      rw [show 2*h+u = (2*h+v)+1 by omega, Nat.mul_add, Nat.mul_one, Nat.mul_comm j (2*h+v)]
    rw [hd, Nat.add_mul, hjmul, Nat.mul_comm i (2*h+u)] at hdeg
    omega
  apply bounded_mono (bounded_mul (bounded_mul ?_ (bounded_pow hy i)) (bounded_pow hv j)) hw
  exact bounded_jetConstant natDegree_map_le

/-- Remove the actual CRT pole divisor while keeping the bound on every
physical coefficient of the quotient. -/
theorem complete_raw_bounded {h} (hpos : 0<h) (hh : h≤131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) {s W P} (mem : P∈complete Crt word s W) :
    ∃ Q : RawSource, forward Crt P = jetConstant ((rawBlock D)^(s.B+s.J))*Q ∧
      Bounded (131071-h) (131071-h-1) W Q := by
  obtain ⟨Q,eq⟩ := mem.2
  refine ⟨Q,eq,?_⟩
  intro j i a nz
  have qn : (Q.coeff j).coeff i≠0 := by
    intro zero;exact nz (by rw [zero,coeff_zero])
  have product : ((forward Crt P).coeff j).coeff i =
      (rawBlock D)^(s.B+s.J)*(Q.coeff j).coeff i := by
    rw [eq]
    change ((C (C ((rawBlock D)^(s.B+s.J)))*Q).coeff j).coeff i=_
    rw [coeff_C_mul,coeff_C_mul]
  have nonzero : ((forward Crt P).coeff j).coeff i ≠ 0 := by
    rw [product]
    exact mul_ne_zero ((K1_14_1_4.rawBlock_monic D).pow (s.B+s.J)).ne_zero qn
  have cap := forward_bounded hpos hh Crt mem.1.1 j i
    (((forward Crt P).coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr nonzero)
  rw [product,((K1_14_1_4.rawBlock_monic D).pow _).natDegree_mul' qn,
    natDegree_pow,rawBlock_degree] at cap
  have small := le_natDegree_of_ne_zero nz
  omega

theorem rawPosition_zero {h} (hpos : 0 < h) (hh : h ≤ 131070) {D : PoleData h} (Crt : CRTLift D)
    (word : I → L) {s W P} (hP : P ∈ evaluated Crt word s W) (j i : ℕ)
    (hw : W < (131071-h)*i+(131071-h-1)*j) : rawPosition Crt j i P = 0 := by
  have hsub : evaluated Crt word s W ≤ LinearMap.ker (rawPosition Crt j i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    apply LinearMap.mem_ker.mpr
    rcases hA.2 with ⟨Q, hQ⟩
    have hz := quotient_positions s W (forward_bounded hpos hh Crt hA.1.1) hQ j i hw
    change ((specialized Crt (centerEval A)).coeff j).coeff i = 0
    rw [specialized_center, hQ]
    simp only [map_mul, doubleMap, coe_mapRingHom, Polynomial.map_C, jetConstant,
      RingHom.comp_apply, coeff_C_mul, coeff_map, hz, map_zero, mul_zero]
  exact LinearMap.mem_ker.mp (hsub hP)
theorem leading_bound {h : ℕ} (hl : 0 < h) (hh : h ≤ 131070)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (P : Jet) (hP : P ∈ evaluated Crt word s W) (hn : P ≠ 0) :
    (P.leadingCoeff.natDegree + P.natDegree)*(131071-h) ≤ W+P.natDegree := by
  let j := P.natDegree
  let i := P.leadingCoeff.natDegree
  change (i+j)*(131071-h) ≤ W+j
  have huv : 131071-h = (131071-h-1)+1 := by omega
  have he : (i+j)*(131071-h) = (131071-h)*i+(131071-h-1)*j+j := by
    have hj : j*(131071-h) = (131071-h-1)*j+j := by
      calc
        j*(131071-h) = j*((131071-h-1)+1) := congrArg (j*·) huv
        _ = (131071-h-1)*j+j := by ring
    rw [Nat.add_mul, hj, Nat.mul_comm i]
    omega
  rw [he]
  by_contra! hw
  have hz := rawPosition_zero hl hh Crt word hP j i (by omega)
  obtain ⟨hj, hi, hn'⟩ := specialized_leading Crt hn
  change ((specialized Crt P).coeff j).coeff i = 0 at hz
  have hj' : (specialized Crt P).natDegree = j := hj
  have hi' : (specialized Crt P).leadingCoeff.natDegree = i := hi
  rw [← hj', coeff_natDegree, ← hi', coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')) hz
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1
noncomputable section
open K1 (I)
open K1_14 (L FX Shape Jet shapeSum triangle seedHasse)
open K1_14_1 K1_14_1_3 Polynomial
open scoped Polynomial BigOperators
open K1_14_1_6 (Low localSpan generators nodeMap localSpan_finrank)
open K1_14_1_3 (evaluatedHasse evaluatedHasse_eq centerEval_clear)
theorem physical_bound (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (ambient h s W) ≤
      physicalDebit s + Module.finrank L (contacted h word s W) := by
  classical
  by_cases hzero : Module.finrank L (ambient h s W) = 0
  · simp [hzero]
  have : Module.Finite L (ambient h s W) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have : Module.Finite L (localSpan s) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s))
  let f : ambient h s W →ₗ[L] (I → localSpan s) :=
    LinearMap.pi (K1_14_1_6.nodeMap h word s W)
  let g : LinearMap.ker f →ₗ[L] contacted h word s W :=
    LinearMap.codRestrict (contacted h word s W)
      ((ambient h s W).subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨P.val.property, ?_⟩
        intro i a b j e hab
        have hz := LinearMap.mem_ker.mp P.property
        exact congrArg (fun z : I → localSpan s => (z i).val (Low.mk j b a e hab)) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : contacted h word s W => R.val) hPQ
  have hle : contacted h word s W ≤ ambient h s W := inf_le_left
  have : Module.Finite L (contacted h word s W) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hnull := f.finrank_range_add_finrank_ker
  have htarget : Module.finrank L (I → localSpan s) ≤ physicalDebit s := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _ : I, Module.finrank L (localSpan s)) ≤
          ∑ _ : I, (shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))) * triangle s.U :=
        Finset.sum_le_sum (fun _ _ => localSpan_finrank s)
      _ = physicalDebit s := by
        rw [Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul, physicalDebit]
        ac_rfl
  have hrange := (LinearMap.range f).finrank_le.trans htarget
  omega
theorem evaluated_shift {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    {s : Shape} {W : ℕ} {P : Jet} (hP : P ∈ evaluated Crt word s W) (i : Fin 2) (r : ℕ) :
    seedHasse i r P ∈ evaluated Crt word s (W+2*h*r) := by
  let target := evaluated Crt word s (W+2*h*r)
  have hsub : evaluated Crt word s W ≤ target.comap (evaluatedHasse i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q, hQ, rfl⟩
      change evaluatedHasse i r (centerEval Q) ∈ target
      have hmem : cleared D i r Q ∈ complete Crt word s (W+2*h*r) :=
        ⟨⟨ambient_cleared D hQ.1.1 i r, K1_14_1_3_1.proof h D word s Q hQ.1.2 i r⟩,
          K1_14_1_3_2.proof h D Crt s Q hQ.2 i r⟩
      have he : centerEval (cleared D i r Q) ∈ target :=
        Submodule.subset_span ⟨cleared D i r Q, hmem, rfl⟩
      rw [centerEval_clear] at he
      have hn : algebraMap (Polynomial L) FX (D.block i ^ (2*r)) ≠ 0 := by
        rw [← map_zero (algebraMap (Polynomial L) FX)]
        exact (IsFractionRing.injective (Polynomial L) FX).ne (pow_ne_zero (2*r) (D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp he)
  rw [← evaluatedHasse_eq]
  exact hsub hP
end
end P0_10_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace P0_10_1_1
noncomputable section
open K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_3 Polynomial
open scoped BigOperators Polynomial
open K1_14_1_7_3 (generic_den generic_centre)
theorem regular_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) : Nonempty (RegularDeformation D Crt) := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, ?_⟩⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]
  · apply simplePoles hh hp D _
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb
end
end P0_10_1_1
end
section
namespace P0_10_5
open K1_14 (Shape slots shapeSum sourceDebit)
open Finset
open scoped BigOperators
open K1_14_5 (shape_sum_flip)
def cut (s : Shape) (v lo t : ℕ) : ℕ :=
  min (s.B + 1)
    ((s.m * P0.agreement + (t - min t (s.U / v)) - 2 * lo * t - 1) / (131071 - lo) + 1)
def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)
end P0_10_5
end
section
namespace P0_10_5
open K1_14 (Shape slots triangle)
open Finset
open scoped BigOperators
private def ValidCut (s : Shape) (v lo t : ℕ) : Prop :=
  let k := cut s v lo t
  min t s.J ≤ k ∧ (k-1) * (131071-lo) + 2*lo*t < s.m*P0.agreement + (t - min t (s.U/v))
private instance (s : Shape) (v lo t : ℕ) : Decidable (ValidCut s v lo t) := by
  unfold ValidCut
  infer_instance
private def moments (s : Shape) (v i : ℕ) : ℕ × ℕ × ℕ :=
  let R := s.U / v
  let n := min R i
  let a := weight s v 0
  let b := v*v
  let s₁ := n*(n-1)/2
  let s₂ := n*(n-1)*(2*n-1)/6
  let last := if R < i then slots s.U (R*v) else 0
  ⟨a*n - b*s₁ + last, a*s₁ - b*s₂ + last*R, a*s₂ - b*s₁*s₁ + last*R*R⟩
private def MomentStep (s : Shape) (v r : ℕ) : Prop :=
  let w := weight s v r
  let p := moments s v r
  let q := moments s v (r+1)
  q.1 = p.1 + w ∧ q.2.1 = p.2.1 + w*r ∧ q.2.2 = p.2.2 + w*r*r
private instance (s : Shape) (v r : ℕ) : Decidable (MomentStep s v r) := by
  unfold MomentStep
  infer_instance
structure Row where
  ok : Bool
  base : ℤ
  slope : ℤ
def Row.add (x y : Row) : Row := ⟨x.ok && y.ok, x.base + y.base, x.slope + y.slope⟩
theorem Row.eq_of_check {x y : Row}
    (h : ((x.ok == y.ok) && (x.base == y.base) && (x.slope == y.slope)) = true) : x = y := by
  cases x
  cases y
  simp only [Bool.and_eq_true, beq_iff_eq, Row.mk.injEq] at h ⊢
  tauto
def scan (f : ℕ → Row) (a : ℕ) : ℕ → Row
  | 0 => ⟨true, 0, 0⟩
  | n+1 => (scan f a n).add (f (a+n))
private theorem scan_add (f : ℕ → Row) (a n m : ℕ) :
    scan f a (n+m) = (scan f a n).add (scan f (a+n) m) := by
  induction m with
  | zero => cases scan f a n; simp [scan, Row.add]
  | succ m ih =>
    change (scan f a (n+m)).add (f (a+(n+m))) =
      (scan f a n).add ((scan f (a+n) m).add (f ((a+n)+m)))
    rw [ih]
    simp only [Row.add, Bool.and_assoc, add_assoc]
theorem joinRows {f : ℕ → Row} (a n m : ℕ) (x y : Row) {z : Row}
    (hx : scan f a n = x) (hy : scan f (a+n) m = y) (hz : x.add y = z) :
    scan f a (n+m) = z := by rw [scan_add, hx, hy, hz]
theorem scan_sum (f : ℕ → Row) (a n : ℕ) (slope : Bool) :
    (if slope then (scan f a n).slope else (scan f a n).base) =
      ∑ i ∈ range n, if slope then (f (a+i)).slope else (f (a+i)).base := by
  cases slope <;> induction n with
  | zero => simp [scan]
  | succ n ih => simp_all only [scan, Row.add, Bool.false_eq_true, ite_false, ite_true,
      sum_range_succ]
end P0_10_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2_5 Polynomial
open K1_14_3 (Slice)
open K1_14_2_2_3 (seedPresentation specializeJets mapGenericJets_eq)
local instance : Algebra (MvPolynomial (Fin 2) Seeds) FibreRing :=
  MvPolynomial.algebraMvPolynomial
end
end K1_14_2_2_2_5_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_2_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_2_5
open K1_14_3_2 (ProperPair)
theorem properPair_height {P Q : Jet} (h : ProperPair P Q)
    (I : Ideal Jet) [I.IsPrime] (hP : P ∈ I) (hQ : Q ∈ I) : 2 ≤ I.height := by
  have hne : I ≠ ⊥ := fun e => h.left_ne (by simpa [e] using hP)
  obtain ⟨D, hD, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hne
  let J : Ideal Jet := Ideal.span {D}
  have : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hJ₀ : J ≠ ⊥ := fun e => hp.ne_zero (Ideal.span_singleton_eq_bot.mp e)
  have hJ₁ : 1 ≤ J.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
  have hJI : J < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro e
    exact h.no_common D hp.irreducible
      (Ideal.mem_span_singleton.mp (e ▸ hP : P ∈ J))
      (Ideal.mem_span_singleton.mp (e ▸ hQ : Q ∈ J))
  calc
    2 = 1 + 1 := by decide
    _ ≤ J.height + 1 := add_le_add hJ₁ le_rfl
    _ ≤ I.height := Ideal.height_add_one_le_of_lt_of_isPrime hJI
end
end K1_14_2_2_2_5_1
end

end Merged_PortHighBase

end Merged_PortHighBase

-- merged module ListProofA
section Merged_ListProofA
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
theorem source_dimension (A : ℕ) (s : Source) (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A - N*s.B) :
    Fintype.card (ColumnIndex A s) + N*(∑ j ∈ s.E, j.q) =
      s.m*A*s.E.card + ∑ j ∈ s.E, j.v := by
  classical
  have hbase : N*s.B ≤ s.m*A := by have := hs.multiplicity; omega
  have hone (j : Jet) (hj : j ∈ s.E) :
      width A s j + N*j.q = s.m*A + j.v := by
    have h := (Nat.mul_le_mul_left N (hs.support j hj).1).trans hbase
    unfold width
    omega
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Finset.sum_coe_sort]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ s.E, (s.m*A + j.v) := Finset.sum_congr rfl hone
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm s.E.card]
private theorem column_injective (A : ℕ) (s : Source) : Function.Injective (column A s) := by
  rintro ⟨⟨⟨c, b, a⟩, hj⟩, x⟩ ⟨⟨⟨c', b', a'⟩, hj'⟩, x'⟩ he
  have hc : c = c' := congrArg (fun z : SourceColumn 2 => z.higher 1) he
  have hb : b = b' := congrArg (fun z : SourceColumn 2 => z.higher 0) he
  have ha : a = a' := congrArg SourceColumn.y₀ he
  subst c'; subst b'; subst a'
  have hx : x.val = x'.val := congrArg SourceColumn.x he
  rw [Fin.ext hx]
theorem interpolant {A : ℕ} {s : Source} (hs : ShapeOK s)
    (hw : s.m ≤ s.m*A-N*s.B) (w : Node → K)
    (hr : stackRank A s w < Fintype.card (ColumnIndex A s)) :
    ∃ Q : DifferentialPolynomial K 2, OrderTwo s Q ∧
      differentialWeightedDegree N Q < s.m*A ∧
      ∀ i, SatisfiesLocalConstraints s.m (node i) (w i) Q := by
  classical
  let cols := column A s
  let M := localConstraintMatrix s.m (fun i => node i) w cols
  have hdep : ¬ LinearIndependent K M.col := by
    intro hi
    have he : M.rank = Fintype.card (ColumnIndex A s) :=
      M.rank_eq_finrank_span_cols.trans (finrank_span_eq_card hi)
    exact (Nat.ne_of_lt hr) he
  obtain ⟨v, hv, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let Q := SourceColumn.interpolant cols v
  have hQ : Q ≠ 0 := fun hz => hj (congrFun ((SourceColumn.interpolant_eq_zero_iff
    (column_injective A s)).mp hz) j)
  have hker : M.mulVec v = 0 := by
    funext row
    have h := congrFun hv row
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm, Matrix.col_apply] using h
  have hlocal := (localConstraintMatrix_mulVec_eq_zero_iff _ _ _ _ _).mp hker
  have hbase : N*s.B ≤ s.m*A := by have := hs.multiplicity; omega
  have hpos : 0 < s.m*A := by have := hs.multiplicity; omega
  have hsupp (u) (hu : u ∈ Q.support) : ∃ i, u = (cols i).exponent := by
    apply Astra7.generic_source_support (RingHom.id K) cols v u
    simpa only [MvPolynomial.map_id] using hu
  have ht : jetTotalDegree Q ≤ s.B := by
    apply (jetTotalDegree_le_iff _ _).mpr
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    simpa [cols, column, Jet.q, Fin.sum_univ_two, Nat.add_assoc] using (hs.support _ i.1.property).1
  have hi : Q.weightedTotalDegree indexWeight ≤ s.J := by
    apply Finset.sup_le
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    simpa [cols, column, indexWeight, SourceColumn.weight_exponent, Fin.sum_univ_two,
      Jet.v, Nat.mul_comm] using (hs.support _ i.1.property).2.1
  have hc : jetDegree Q (Fin.last 2) ≤ s.C := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    obtain ⟨i, rfl⟩ := hsupp u hu
    change (cols i).exponent (some (1 : Fin 2).succ) ≤ s.C
    rw [SourceColumn.exponent_succ]
    exact (hs.support _ i.1.property).2.2
  refine ⟨Q, ⟨hQ, ht, hi, hc⟩, ?_, hlocal⟩
  apply (Finset.sup_lt_iff hpos).mpr
  intro u hu
  obtain ⟨i, rfl⟩ := hsupp u hu
  have hx := i.2.isLt
  have hq := (Nat.mul_le_mul_left N (hs.support _ i.1.property).1).trans hbase
  simp only [width, Jet.q, Jet.v, N] at hx hq
  rw [SourceColumn.weight_exponent]
  simp [cols, column, differentialWeight, Fin.sum_univ_two, N]
  omega
theorem specializes {A : ℕ} {s : Source} {w : Node → K} {Q : DifferentialPolynomial K 2}
    (hwt : differentialWeightedDegree N Q < s.m*A)
    (hlocal : ∀ i, SatisfiesLocalConstraints s.m (node i) (w i) Q) :
    ∀ f ∈ close A w, differentialSpecialization Q f = 0 := by
  intro f hf
  have hd : f.natDegree ≤ N := by
    by_cases hz : f = 0
    · simp [hz]
    · have h := (natDegree_lt_iff_degree_lt hz).2 hf.1
      exact Nat.le_of_lt_succ h
  let hits := ReedSolomon.polynomialAgreementSet node w f
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    node w hits hwt (fun i _ => hlocal i) f hd node.injective.injOn hf.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open K1_14_6 (occupancy)
open P0_10 (incidence_arithmetic)
theorem section_capacity {A : ℕ} {w : Node → K} {T : Finset (Polynomial K)}
    (h : (T : Set (Polynomial K)) ⊆ close A w) (hA : AgreementOK A) (cap : ℕ)
    (hsection : ∀ i : Node, (∃ γ ∈ T, γ.eval (node i) ≠ w i) →
      (T.filter fun γ => γ.eval (node i) = w i).card ≤ cap) :
    (gap A) * T.card ≤ errors A * cap + (gap A) := by
  classical
  have hd := hA.gt_degree
  have hn := hA.lt_length
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (gap A) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : (Polynomial K)) : Finset Node := univ.filter fun i => γ.eval (node i) = w i
  let common : Finset Node := univ.filter fun i => ∀ γ ∈ T, γ.eval (node i) = w i
  let nodes : Finset Node := univ \ common
  have common_le (γ : (Polynomial K)) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : (Polynomial K)) (hγ : γ ∈ T) : A ≤ (hits γ).card := by
    exact (h hγ).2
  have degree (a : (Polynomial K)) (ha : a ∈ T) : a.natDegree ≤ N := by
    by_cases hz : a = 0
    · simp [hz]
    · have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hz).2 (h ha).1
      exact Nat.le_of_lt_succ hdeg
  have pair_count (a : (Polynomial K)) (ha : a ∈ T) (b : (Polynomial K)) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ N := by
    refine (FrobeniusLocator.Strata.root_nodes_card_le node node.injective
      (a-b) (sub_ne_zero.mpr hab) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (a-b).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ N :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := A - common.card
  let t := N - common.card
  have ht : t = x - (gap A) := by dsimp [t, x, gap]; omega
  have hx : gap A ≤ x := by dsimp [x, gap]; omega
  have hnodes : nodes.card = x + errors A := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    change n - common.card = (A-common.card) + (n-A)
    have hbound := hcommon.trans hd.le
    omega
  have exists_trim (γ : (Polynomial K)) : ∃ B : Finset Node, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : (Polynomial K)) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : (Polynomial K)) (ha : a ∈ T) (b : (Polynomial K)) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : Node) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, γ.eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic (errors A) _ _ _ _ (by omega) (Nat.sub_pos_of_lt hd) hx (Nat.sub_pos_of_lt hn) second first
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Finset MvPolynomial
open scoped Polynomial BigOperators
open K1_14_6 (curve_degree_nat)
def valueCut (x a : K) : CoeffRing :=
  (∑ i : Fin k, C (embed x ^ i.val) * MvPolynomial.X i) - C (embed a)
theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro i _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    (totalDegree_mul (C (embed x ^ i.val)) (MvPolynomial.X i))
private theorem natDegree_bound {f : (Polynomial K)} (h : f.degree < k) : f.natDegree < k := by
  by_cases hz : f = 0
  · rw [hz, Polynomial.natDegree_zero]
    exact Nat.zero_lt_succ _
  · exact (Polynomial.natDegree_lt_iff_degree_lt hz).2 h
theorem valueCut_eval {f : (Polynomial K)} (h : f.degree < k) (x a : K) :
    aeval (coeffPoint f) (valueCut x a) = 0 ↔ f.eval x = a := by
  have heval : f.eval x = ∑ j : Fin k, f.coeff j.val * x ^ j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f.coeff j * x ^ j)]
    exact Polynomial.eval_eq_sum_range' (natDegree_bound h) x
  have hmap : embed (∑ j : Fin k, f.coeff j.val * x ^ j.val) =
      ∑ j : Fin k, embed x ^ j.val * embed (f.coeff j.val) := by
    rw [map_sum]
    exact sum_congr rfl fun _ _ => by rw [map_mul, map_pow, mul_comm]
  simp only [valueCut, coeffPoint, map_sub, map_sum, map_mul, aeval_C, aeval_X, sub_eq_zero,
    Algebra.algebraMap_self_apply]
  rw [heval, ← hmap]
  exact embed.injective.eq_iff
private theorem coeffPoint_injOn {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) :
    Set.InjOn coeffPoint (Γ : Set (Polynomial K)) := by
  intro f hf g hg heq
  apply Polynomial.ext
  intro j
  by_cases hj : j < k
  · exact embed.injective (congrFun heq ⟨j, hj⟩)
  · have hfj := (natDegree_bound (h hf).1).trans_le (Nat.le_of_not_gt hj)
    have hgj := (natDegree_bound (h hg).1).trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hfj, Polynomial.coeff_eq_zero_of_natDegree_lt hgj]
private theorem zeroDim_count {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) (P : Ideal CoeffRing)
    (hdim : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ Γ, coeffPoint γ ∈ zeroLocus Geo P) :
    (Γ.card : ℚ) ≤ affineDegree P := by
  classical
  let A := Γ.image (coeffPoint)
  have hA : A.card = Γ.card := card_image_of_injOn (coeffPoint_injOn h)
  have hsub : (A : Set _) ⊆ zeroLocus Geo P := by
    intro y hy
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hy
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ :=
    finite_zeroLocus_and_ncard_le_affineDegree (K := Geo) P hdim
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hA] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree
private theorem section_count {A w} {Γ : Finset (Polynomial K)} (h : (Γ : Set (Polynomial K)) ⊆ close A w) {P : Ideal CoeffRing}
    (hP : P.IsPrime) (hpoints : ∀ γ ∈ Γ, coeffPoint γ ∈ zeroLocus Geo P)
    (x a : K) (hmiss : ∃ γ ∈ Γ, γ.eval x ≠ a)
    {c : ℚ} (hc : 0 ≤ c)
    (bound : ∀ (V : Finset (Polynomial K)), V ⊆ Γ → ∀ (Q : Ideal CoeffRing), Q.IsPrime →
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree →
      (∀ γ ∈ V, coeffPoint γ ∈ zeroLocus Geo Q) →
      (V.card : ℚ) ≤ c * affineDegree Q) :
    ((Γ.filter fun γ => γ.eval x = a).card : ℚ) ≤ c * affineDegree P := by
  classical
  let prime := hP
  let cut := valueCut x a
  let Ps := (P ⊔ Ideal.span {cut}).minimalPrimesFinset
  let U := Γ.filter fun γ => γ.eval x = a
  let part (Q : Ideal CoeffRing) := U.filter fun f => coeffPoint f ∈ zeroLocus Geo Q
  have hproper : cut ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hm
    exact hv ((valueCut_eval (h hγ).1 x a).mp (hpoints γ hγ _ hm))
  have hcover : U ⊆ Ps.biUnion part := by
    intro γ hγ
    obtain ⟨hγΓ, hv⟩ := mem_filter.mp hγ
    have hp : coeffPoint γ ∈ zeroLocus Geo (P ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ, (valueCut_eval (h hγΓ).1 x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  have hsum : U.card ≤ ∑ Q ∈ Ps, (part Q).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hdeg : (∑ Q ∈ Ps, affineDegree Q) ≤ affineDegree P := by
    simpa only [Ps, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
  change (U.card : ℚ) ≤ c * affineDegree P
  calc
    _ ≤ ∑ Q ∈ Ps, ((part Q).card : ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q ∈ Ps, c * affineDegree Q := by
      apply sum_le_sum
      intro Q hQ
      have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((filter_subset _ _).trans (filter_subset _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ => (mem_filter.mp hγ).2)
    _ ≤ c * affineDegree P := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hdeg hc
theorem curve_capacity {A w} {T : Finset (Polynomial K)} (hT : (T : Set (Polynomial K)) ⊆ close A w)
    (hA : AgreementOK A) {P : Ideal CoeffRing} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ f ∈ T, coeffPoint f ∈ zeroLocus Geo P) :
    ((gap A : ℕ) : ℚ)*T.card ≤ (errors A : ℚ)*affineDegree P + gap A ∧
    (T.card : ℚ) ≤ 2*affineDegree P := by
  classical
  obtain ⟨δ, hδ, hdeg⟩ := curve_degree_nat P hp hd
  have hcap := section_capacity hT hA δ fun i hi => by
    have hc := section_count hT hp hpoints (node i) (w i) hi (c := 1) zero_le_one
      (fun _ hV Q _ hdim hpts => by
        rw [one_mul]
        exact zeroDim_count (fun _ hf => hT (hV hf)) Q (by omega) hpts)
    rw [one_mul, hdeg] at hc
    exact_mod_cast hc
  rw [hdeg]
  refine ⟨by exact_mod_cast hcap, ?_⟩
  suffices hn : T.card ≤ 2*δ by exact_mod_cast hn
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left (gap A) (show 2*δ + 1 ≤ T.card by omega)
  rw [Nat.mul_add, Nat.mul_one] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hA.beta_lt_two hδ
  rw [mul_comm 2 (gap A), mul_assoc] at hstrict
  omega
private theorem surface_capacity {A w} {T : Finset (Polynomial K)} (hT : (T : Set (Polynomial K)) ⊆ close A w)
    (hA : AgreementOK A) {P : Ideal CoeffRing} (hp : P.IsPrime)
    (hd : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ f ∈ T, coeffPoint f ∈ zeroLocus Geo P) :
    (gap A : ℚ)*T.card ≤ (errors A : ℚ)*(2*affineDegree P) + gap A := by
  classical
  let cost := 2*affineDegree P
  have hcost : 0 ≤ cost := mul_nonneg (by decide) (affineDegree_nonneg P)
  have hn := section_capacity hT hA ⌊cost⌋₊ fun i hi => by
    apply (Nat.le_floor_iff hcost).mpr
    apply section_count hT hp hpoints (node i) (w i) hi (c := 2) (by decide)
    exact fun _ hV _ hprime hdim hpts =>
      (curve_capacity (fun _ hf => hT (hV hf)) hA hprime (by omega) hpts).2
  have hq : (gap A : ℚ)*T.card ≤ (errors A : ℚ)*(⌊cost⌋₊ : ℚ) + gap A := by exact_mod_cast hn
  exact hq.trans (add_le_add (mul_le_mul_of_nonneg_left (Nat.floor_le hcost)
    (Nat.cast_nonneg (errors A))) le_rfl)
end
end CJ0
end
section
namespace CJ0
noncomputable section
open Polynomial PolynomialDifferential Finset
open scoped BigOperators
def c1 : Prop :=
  ∀ A s cut, ShapeOK s → s.m ≤ s.m*A - N*s.B → cut ≤ s.B+1 → SilentTail s cut →
    originRank A s ≤ prefixRank s cut
def c2 : Prop :=
  ∀ A s, ShapeOK s → s.m ≤ s.m*A - N*s.B → ∀ w : Node → K,
    stackRank A s w ≤ n * originRank A s
def c5 : Prop :=
  ∀ s, ShapeOK s → ∀ Q, OrderTwo s Q →
    ∃ Q₁, OrderOne s Q₁ ∧ ∀ f : (Polynomial K), f.degree < k →
      differentialSpecialization Q f = 0 → ¬ RegularRoot Q f →
      differentialSpecialization Q₁ f = 0
def c6 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ F : Family 1, Family₁ s F ∧ CoversRegular F Q₁
def c7 : Prop :=
  ∀ s, ShapeOK s → ∀ F : Family 1, Family₁ s F → ImageDegrees F (R₁ s)
def c8 : Prop :=
  ∀ s, ShapeOK s → ∀ Q₁, OrderOne s Q₁ →
    ∃ G : Polynomial (Polynomial K), G ≠ 0 ∧ G.natDegree ≤ H s*(H s-1) ∧
      ∀ f : (Polynomial K), f.degree < k → differentialSpecialization Q₁ f = 0 →
        ¬ RegularRoot Q₁ f → G.eval f = 0
end
end CJ0
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Jet blockEntry)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
abbrev LocalExponent := LocalVariable 2 →₀ ℕ
def rowJet (e : LocalExponent) : Jet :=
  ⟨e (localY (1 : Fin 2)), e (localY (0 : Fin 2)), e (localE 2)⟩
def rowBalance (e : LocalExponent) : ℤ :=
  (e (localT 2) : ℤ) - (rowJet e).a - (rowJet e).v
def colBalance (x : ℕ) (j : Jet) : ℤ := (x : ℤ) - j.v
private def exponent (t h d l : ℕ) : LocalExponent :=
  Finsupp.single (localT 2) t + Finsupp.single (localE 2) h +
    Finsupp.single (localY (0 : Fin 2)) d + Finsupp.single (localY (1 : Fin 2)) l
private theorem exponent_eq_iff (t h d l : ℕ) (e : LocalExponent) :
    exponent t h d l = e ↔
      t = e (localT 2) ∧ h = (rowJet e).a ∧ d = (rowJet e).b ∧ l = (rowJet e).c := by
  classical
  constructor
  · intro he
    have atVar (v : LocalVariable 2) := DFunLike.congr_fun he v
    exact ⟨by simpa [exponent, localT, localE, localAux, localY] using atVar (localT 2),
      by simpa [exponent, rowJet, Jet.a, localT, localE, localAux, localY] using atVar (localE 2),
      by simpa [exponent, rowJet, Jet.b, localT, localE, localAux, localY] using
        atVar (localY (0 : Fin 2)),
      by simpa [exponent, rowJet, Jet.c, localT, localE, localAux, localY] using
        atVar (localY (1 : Fin 2))⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext v
    rcases v with _ | (_ | j)
    · simp [exponent, localT, localE, localAux, localY]
    · simp [exponent, rowJet, Jet.a, localT, localE, localAux, localY]
    · fin_cases j <;> simp [exponent, rowJet, Jet.b, Jet.c, localT, localE, localAux, localY]
variable {F : Type*} [CommRing F]
private theorem origin_substitution (x a b c : ℕ) :
    unscaledLocalSubstitution 2 (0 : F) 0 (sourceMonomial x a ![b,c]) =
      ∑ h ∈ Finset.range (a+1), ∑ j ∈ Finset.range (a-h+1),
        monomial (exponent (x+h+j+2*(a-h-j)) h (b+j) (c+(a-h-j)))
          ((-1 : F)^(a-h-j) * (a.choose h : F) * ((a-h).choose j : F)) := by
  classical
  let localX : LocalPolynomial F 2 := MvPolynomial.X (localT 2)
  let hiddenTerm : LocalPolynomial F 2 := localX * MvPolynomial.X (localE 2)
  let jetOne : LocalPolynomial F 2 := MvPolynomial.X (localY (0 : Fin 2))
  let jetTwo : LocalPolynomial F 2 := MvPolynomial.X (localY (1 : Fin 2))
  let firstTerm := localX * jetOne
  let secondTerm := -(localX^2 * jetTwo)
  have h₀ : unscaledLocalSubstitution 2 (0 : F) 0 (MvPolynomial.X (some 0)) = hiddenTerm + (firstTerm + secondTerm) := by
    simp [localCorrection, Fin.sum_univ_two, hiddenTerm, firstTerm, secondTerm, localX, jetOne, jetTwo]
    ac_rfl
  rw [sourceMonomial, Fin.prod_univ_two, map_mul, map_mul, map_mul,
    map_pow, map_pow, map_pow, map_pow, h₀]
  simp only [unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_succ, C_0, zero_add,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change localX^x * (hiddenTerm+(firstTerm+secondTerm))^a * (jetOne^b*jetTwo^c) = _
  rw [add_pow hiddenTerm (firstTerm+secondTerm), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [add_pow firstTerm secondTerm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hW : secondTerm = monomial (Finsupp.single (localT 2) 2 +
      Finsupp.single (localY (1 : Fin 2)) 1) (-1) := by
    change -(MvPolynomial.X (localT 2)^2 * MvPolynomial.X (localY (1 : Fin 2))) = _
    rw [ X_pow_eq_monomial]
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul, map_neg]
  have hE : hiddenTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localE 2) 1) 1 := by simp [hiddenTerm, localX, MvPolynomial.X]
  have hV : firstTerm = monomial (Finsupp.single (localT 2) 1 +
      Finsupp.single (localY (0 : Fin 2)) 1) 1 := by simp [firstTerm, localX, jetOne, MvPolynomial.X]
  have hcast (n : ℕ) : (n : LocalPolynomial F 2) = monomial 0 (n : F) := by
    rw [monomial_zero', map_natCast]
  rw [hE, hV, hW]
  simp only [localX, jetOne, jetTwo, X_pow_eq_monomial, monomial_pow,
    hcast, monomial_mul_monomial, one_mul, mul_one, one_pow]
  apply congrArg₂ (fun a b => (monomial a b : LocalPolynomial F 2))
  · apply Finsupp.ext
    intro v
    rcases v with _ | (_ | u)
    · simp [exponent, localT, localE, localAux, localY, Nat.mul_comm, Nat.add_assoc]
    · simp [exponent, localT, localE, localAux, localY]
    · fin_cases u <;>
        simp [exponent, localT, localE, localAux, localY, Nat.add_comm]
  · ring
theorem origin_coefficient (x : ℕ) (j : Jet) (e : LocalExponent) :
    (unscaledLocalSubstitution 2 (0 : ZMod CJ0.p) 0
       (sourceMonomial x j.a ![j.b,j.c])).coeff e =
      if rowBalance e = colBalance x j then blockEntry (rowJet e) j else 0 := by
  classical
  let r := rowJet e
  let P : Prop := rowBalance e = colBalance x j ∧
    (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)
  have hexp (h u : ℕ) (hh : h ≤ j.a) (hu : u ≤ j.a-h) :
      exponent (x+h+u+2*(j.a-h-u)) h (j.b+u) (j.c+(j.a-h-u)) = e ↔
        P ∧ h = r.a ∧ u = r.b-j.b := by
    rw [exponent_eq_iff]
    change (x+h+u+2*(j.a-h-u) = e (localT 2) ∧
      h = r.a ∧ j.b+u = r.b ∧ j.c+(j.a-h-u) = r.c) ↔
      ((e (localT 2) : ℤ) - r.a - (r.b+2*r.c : ℕ) =
       (x : ℤ) - (j.b+2*j.c : ℕ) ∧
         (j.b ≤ r.b ∧ j.c ≤ r.c ∧ r.a + (r.b-j.b) + (r.c-j.c) = j.a)) ∧
       h = r.a ∧ u = r.b-j.b
    omega
  rw [origin_substitution]
  simp_rw [coeff_sum, coeff_monomial]
  by_cases hp : P
  · obtain ⟨hg, hb, hc, ha⟩ := hp
    have hh : r.a ≤ j.a := by omega
    have hu : r.b-j.b ≤ j.a-r.a := by omega
    rw [Finset.sum_eq_single_of_mem r.a (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem (r.b-j.b) (Finset.mem_range.mpr (by omega))]
      · rw [ite_eq_left ((hexp _ _ hh hu).2 ⟨⟨hg, hb, hc, ha⟩, rfl, rfl⟩), ite_eq_left hg]
        change _ = blockEntry r j
        rw [blockEntry, ite_eq_left ⟨hb, hc, ha⟩, show j.a-r.a-(r.b-j.b) = r.c-j.c by omega]
      · intro u hmem hne
        rw [ite_eq_right (fun he => hne ((hexp _ _ hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))).1 he).2.2)]
    · intro h hmem hne
      apply Finset.sum_eq_zero
      intro u humem
      rw [ite_eq_right (fun he => hne ((hexp _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem))).1 he).2.1)]
  · have hz := fun h u (hh : h ≤ j.a) (hu : u ≤ j.a-h) he =>
      hp ((hexp h u hh hu).1 he).1
    have hzero : (if rowBalance e = colBalance x j then blockEntry r j else 0) = 0 := by
      split
      · rename_i hg
        exact ite_eq_right (fun hb => hp ⟨hg, hb⟩)
      · rfl
    rw [hzero]
    apply Finset.sum_eq_zero
    intro h hmem
    apply Finset.sum_eq_zero
    intro u humem
    rw [ite_eq_right (hz h u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem)))]
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open scoped BigOperators Matrix
theorem rank_blockDiagonal_le {F I : Type*} [Field F] [Fintype I]
    {R C : I → Type*} [∀ i, Fintype (C i)] [DecidableEq I]
    (M : ∀ i, Matrix (R i) (C i) F) :
    (Matrix.blockDiagonal' M).rank ≤ ∑ i, (M i).rank := by
  let Φ := (Matrix.blockDiagonal' M).mulVecLin
  let φ := fun i => (M i).mulVecLin
  let project : Φ.range →ₗ[F] ∀ i, (φ i).range :=
    { toFun y i := ⟨fun r => y.val ⟨i,r⟩, by
        obtain ⟨v, hv⟩ := y.property
        refine ⟨fun c => v ⟨i,c⟩, ?_⟩
        rw [← hv]
        funext r
        change (∑ c : C i, M i r c * v ⟨i,c⟩) =
          ∑ j : Sigma C, Matrix.blockDiagonal' M ⟨i,r⟩ j * v j
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.sum_eq_single i]
        · simp [Matrix.blockDiagonal'_apply_eq]
        · intro j _ hji
          apply Finset.sum_eq_zero
          intro c _
          rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji), zero_mul]
        · simp⟩
      map_add' x y := by ext i r; rfl
      map_smul' t x := by ext i r; rfl }
  have hinj : Function.Injective project := by
    intro x y h
    apply Subtype.ext
    funext ⟨i,r⟩
    exact congrFun (congrArg Subtype.val (congrFun h i)) r
  change Module.finrank F Φ.range ≤ ∑ i, Module.finrank F (φ i).range
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq
    (Module.finrank_pi_fintype F)
end
end CJ0_1
end
section
namespace CJ0_1
noncomputable section
open CJ0 (Source ShapeOK SilentTail Jet ColumnIndex column blockRows blockCols blockMatrix
  blockEntry prefixRank p)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix
local instance : Fact (Nat.Prime p) := ⟨KoalaBear.is_prime⟩
abbrev OriginRow (s : Source) := Unit × LowContactIndex 2 s.m
abbrev OriginCol (A : ℕ) (s : Source) := ColumnIndex A s
private def origin (A : ℕ) (s : Source) : Matrix (OriginRow s) (OriginCol A s) (ZMod p) :=
  localConstraintMatrix s.m (fun _ : Unit => 0) (fun _ => 0) (column A s)
private theorem origin_entry {A s} (r : OriginRow s) (j : OriginCol A s) :
    origin A s r j =
      if rowBalance r.2.val = colBalance j.2.val j.1.val then
        blockEntry (rowJet r.2.val) j.1.val else 0 := by
  rw [origin, localConstraintMatrix_apply, SourceColumn.polynomial_eq_sourceMonomial]
  exact origin_coefficient j.2.val j.1.val r.2.val
abbrev BlockIndex (s : Source) (cut : ℕ) := (q : Fin cut) × Fin (s.m+s.J-q.val)
private def balance {s cut} (i : BlockIndex s cut) : ℤ := (i.2.val : ℤ) - s.J
private structure InPrefix (s : Source) (cut q : ℕ) (g : ℤ) : Prop where
  grade : q < cut
  lower : -(s.J : ℤ) ≤ g
  upper : g + q < (s.m : ℤ)
private def blockIndex {s cut q g} (h : InPrefix s cut q g) : BlockIndex s cut :=
  ⟨⟨q, h.grade⟩, ⟨(g + s.J).toNat, by
    change (g + s.J).toNat < s.m+s.J-q
    have := h.lower
    have := h.upper
    omega⟩⟩
private theorem balance_blockIndex {s cut q g} (h : InPrefix s cut q g) :
    balance (blockIndex h) = g := by
  have := h.lower
  simp only [balance, blockIndex]
  omega
private theorem blockIndex_ext {s cut} {i j : BlockIndex s cut}
    (hq : i.1.val = j.1.val) (hg : balance i = balance j) : i = j := by
  rcases i with ⟨qi, ui⟩
  rcases j with ⟨qj, uj⟩
  have hgrade : qi = qj := Fin.ext hq
  subst qj
  have hoffset : ui = uj := Fin.ext (by simp only [balance] at hg; omega)
  subst uj
  rfl
private theorem row_mem {s : Source} (r : OriginRow s) :
    rowJet r.2.val ∈ blockRows s.m (rowJet r.2.val).q (rowBalance r.2.val) := by
  let j := rowJet r.2.val
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*j.a < s.m at hcontact
  have hweight : rowBalance r.2.val + (j.v : ℤ) + 3*(j.a : ℤ) =
      (r.2.val (localT 2) : ℤ) + 2*(j.a : ℤ) := by
    change (r.2.val (localT 2) : ℤ) - j.a - j.v + j.v + 3*j.a = _
    omega
  refine Finset.mem_filter.mpr ⟨?_, by rw [hweight]; omega⟩
  change j ∈ (Finset.range (j.q+1)).sigma
    (fun c => (Finset.range (j.q-c+1)).sigma fun b => {j.q-(b+c)})
  generalize j = i
  rcases i with ⟨c,b,a⟩
  simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_singleton, Jet.q, Jet.a, Jet.b, Jet.c]
  omega
private theorem origin_support {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : OriginRow s) (j : OriginCol A s) (hn : origin A s r j ≠ 0) :
    (rowJet r.2.val).q = j.1.val.q ∧ rowBalance r.2.val = colBalance j.2.val j.1.val ∧
      InPrefix s cut j.1.val.q (colBalance j.2.val j.1.val) := by
  let i := rowJet r.2.val
  let c := j.1.val
  have hg : rowBalance r.2.val = colBalance j.2.val c := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_right hn'])
  have hbc : c.b ≤ i.b ∧ c.c ≤ i.c ∧ i.a + (i.b-c.b) + (i.c-c.c) = c.a := by
    by_contra hn'
    exact hn (by rw [origin_entry, ite_eq_left hg, blockEntry, ite_eq_right hn'])
  obtain ⟨hb, hc, ha⟩ := hbc
  have hq : i.q = c.q := by simp only [Jet.q]; omega
  have hcontact := r.2.property
  rw [localContactOrder_eq] at hcontact
  change r.2.val (localT 2) + 2*i.a < s.m at hcontact
  have heq : (r.2.val (localT 2) : ℤ) - i.a - (i.b + 2*i.c : ℕ) =
      (j.2.val : ℤ) - (c.b + 2*c.c : ℕ) := hg
  have hsmall : c.a < s.m := by omega
  have hgrade : c.q < cut := by
    by_contra! hbig
    exact (Nat.not_le_of_gt hsmall) (htail c j.1.property hbig)
  have hv := (hs.support c j.1.property).2.1
  refine ⟨hq, hg, hgrade, ?_, ?_⟩
  · change -(s.J : ℤ) ≤ (j.2.val : ℤ) - c.v
    change c.v ≤ s.J at hv
    omega
  · change (j.2.val : ℤ) - (c.b+2*c.c : ℕ) + (c.a+c.b+c.c : ℕ) < (s.m : ℤ)
    omega
private def activeRows (A : ℕ) (s : Source) : Finset (OriginRow s) :=
  localConstraintSupportedRows s.m (fun _ : Unit => (0 : ZMod p)) (fun _ => 0) (column A s)
private def activeCols (A : ℕ) (s : Source) : Finset (OriginCol A s) := by
  classical
  exact Finset.univ.filter fun j => ∃ r, origin A s r j ≠ 0
private theorem active_row_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (r : activeRows A s) :
    InPrefix s cut (rowJet r.val.2.val).q (rowBalance r.val.2.val) := by
  obtain ⟨j, hj⟩ := (mem_localConstraintSupportedRows_iff _ _ _ _ _).mp r.property
  obtain ⟨hq, hg, h⟩ := origin_support hs htail r.val j hj
  rwa [hq, hg]
private theorem active_col_inPrefix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut)
    (j : activeCols A s) :
    InPrefix s cut j.val.1.val.q (colBalance j.val.2.val j.val.1.val) := by
  classical
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp j.property).2
  exact (origin_support hs htail r j.val hr).2.2
private abbrev BlockRow {s cut} (i : BlockIndex s cut) : Type := ↥(blockRows s.m i.1.val (balance i))
private abbrev BlockCol {s cut} (i : BlockIndex s cut) : Type := ↥(blockCols s i.1.val (balance i))
private def rowRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (r : activeRows A s) :
    Sigma (BlockRow (s := s) (cut := cut)) :=
  let h := active_row_inPrefix hs htail r
  ⟨blockIndex h, ⟨rowJet r.val.2.val, by
    change rowJet r.val.2.val ∈
      blockRows s.m (rowJet r.val.2.val).q (balance (blockIndex h))
    rw [balance_blockIndex]
    exact row_mem r.val⟩⟩
private def colRep {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) (j : activeCols A s) :
    Sigma (BlockCol (s := s) (cut := cut)) :=
  let h := active_col_inPrefix hs htail j
  ⟨blockIndex h, ⟨j.val.1.val, by
    apply Finset.mem_filter.mpr
    refine ⟨j.val.1.property, rfl, ?_⟩
    rw [balance_blockIndex]
    simp [colBalance]⟩⟩
private def packet (s : Source) (cut : ℕ) :
    Matrix (Sigma (BlockRow (s := s) (cut := cut))) (Sigma (BlockCol (s := s) (cut := cut)))
      (ZMod p) :=
  Matrix.blockDiagonal' fun i => blockMatrix s i.1.val (balance i)
private theorem packet_entry {s cut} (r : Sigma (BlockRow (s := s) (cut := cut)))
    (c : Sigma (BlockCol (s := s) (cut := cut))) (h : r.1 = c.1) :
    packet s cut r c = blockEntry r.2.val c.2.val := by
  rcases r with ⟨i,r⟩
  rcases c with ⟨j,c⟩
  change i = j at h
  subst j
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _
private theorem origin_submatrix {A s cut} (hs : ShapeOK s) (htail : SilentTail s cut) :
    (origin A s).submatrix (Subtype.val : activeRows A s → _) (Subtype.val : activeCols A s → _) =
      (packet s cut).submatrix (rowRep hs htail) (colRep hs htail) := by
  ext r c
  let i := rowRep hs htail r
  let j := colRep hs htail c
  change origin A s r.val c.val = packet s cut i j
  have hr : balance i.1 = rowBalance r.val.2.val :=
    balance_blockIndex (active_row_inPrefix hs htail r)
  have hc : balance j.1 = colBalance c.val.2.val c.val.1.val :=
    balance_blockIndex (active_col_inPrefix hs htail c)
  by_cases hij : i.1 = j.1
  · rw [packet_entry i j hij, origin_entry, ite_eq_left (hr.symm.trans ((congrArg balance hij).trans hc))]
    rfl
  · have hz : origin A s r.val c.val = 0 := by
      by_contra hn
      obtain ⟨hq, hg, _⟩ := origin_support hs htail r.val c.val hn
      exact hij (blockIndex_ext hq (hr.trans (hg.trans hc.symm)))
    rw [hz]
    exact (Matrix.blockDiagonal'_apply_ne _ _ _ hij).symm
private theorem origin_rank_eq_supported (A : ℕ) (s : Source) :
    (origin A s).rank =
      ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank := by
  symm
  apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
  exact localConstraintMatrix_ne_zero_mem_range _ _ _ _
private theorem supported_rank_le (A : ℕ) (s : Source) :
    ((origin A s).submatrix (Subtype.val : activeRows A s → _) id).rank ≤
      ((origin A s).submatrix (Subtype.val : activeRows A s → _)
        (Subtype.val : activeCols A s → _)).rank := by
  classical
  apply Sol1.C52.rank_le_col_representatives
  intro j
  by_cases hj : j ∈ activeCols A s
  · exact Or.inr ⟨⟨j, hj⟩, rfl⟩
  · left
    funext r
    change origin A s r.val j = 0
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.val, hn⟩)
private theorem packet_rank_le (s : Source) (cut : ℕ) : (packet s cut).rank ≤ prefixRank s cut := by
  calc
    (packet s cut).rank ≤ ∑ i : BlockIndex s cut, (blockMatrix s i.1.val (balance i)).rank :=
      rank_blockDiagonal_le (fun i : BlockIndex s cut => blockMatrix s i.1.val (balance i))
    _ = prefixRank s cut := by
      rw [Fintype.sum_sigma]
      simp only [prefixRank, balance, Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [dite_eq_left (Finset.mem_range.mp hq)]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [dite_eq_left (Finset.mem_range.mp hu)]
      rfl
theorem proof : CJ0.c1 := by
  intro A s cut hs _ _ htail
  change (origin A s).rank ≤ prefixRank s cut
  rw [origin_rank_eq_supported]
  apply (supported_rank_le A s).trans
  rw [origin_submatrix hs htail]
  exact (Matrix.rank_submatrix_le _ _ _).trans (packet_rank_le s cut)
end
end CJ0_1
end
section
namespace CJ0_2
noncomputable section
open CJ0 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem lower_mem {s : Source} (hs : ShapeOK s) {c b a : ℕ}
    (h : (⟨c, b, a⟩ : Jet) ∈ s.E) {a' : ℕ} (ha : a' ≤ a) :
    (⟨c, b, a'⟩ : Jet) ∈ s.E := by
  induction a with
  | zero =>
    rw [Nat.eq_zero_of_le_zero ha]
    exact h
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le ha with hEq | hlt
    · rw [hEq]
      exact h
    · exact ih (hs.lower _ h (Nat.succ_pos a)) (Nat.le_of_lt_succ hlt)
private def sourceSpan (F : Type*) [Field F] (A : ℕ) (s : Source) :
    Submodule F (DifferentialPolynomial F 2) :=
  Submodule.span F (Set.range fun i : ColumnIndex A s => (column A s i).polynomial)
private theorem column_mem_sourceSpan {F : Type*} [Field F] {A : ℕ} {s : Source}
    (i : ColumnIndex A s) : (column A s i).polynomial ∈ sourceSpan F A s :=
  Submodule.subset_span (Set.mem_range_self i)
private theorem translated_column_mem {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) (i : ColumnIndex A s) :
    globalPointTranslation center received (column A s i).polynomial ∈ sourceSpan F A s := by
  classical
  let col := column A s i
  change globalPointTranslation center received col.polynomial ∈ sourceSpan F A s
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  simp only [sourceMonomial, map_mul, map_pow, map_prod, globalPointTranslation_X,
    globalPointTranslation_Y_zero, globalPointTranslation_Y_succ]
  rw [add_comm (MvPolynomial.C center), add_comm (MvPolynomial.C received), add_pow, add_pow,
    Finset.sum_mul, Finset.sum_mul]
  apply Submodule.sum_mem
  intro x hx
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro a ha
  have hx' : x ≤ i.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have ha' : a ≤ i.1.val.a := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  let j : Jet := ⟨i.1.val.c, i.1.val.b, a⟩
  have hj : j ∈ s.E := by
    rcases i with ⟨⟨⟨c, b, a₀⟩, hi⟩, i⟩
    exact lower_mem hs hi ha'
  have hq : j.q ≤ i.1.val.q :=
    Nat.add_le_add_right (Nat.add_le_add_right ha' _) _
  have hwidth : width A s i.1.val ≤ width A s j :=
    Nat.add_le_add_right (Nat.sub_le_sub_left (Nat.mul_le_mul_left N hq) _) _
  let l : ColumnIndex A s := ⟨⟨j, hj⟩, ⟨x, (hx'.trans_lt i.2.isLt).trans_le hwidth⟩⟩
  let coeff : F := center ^ (col.x - x) * (col.x.choose x : F) *
    received ^ (col.y₀ - a) * (col.y₀.choose a : F)
  have hterm :
      (MvPolynomial.X none ^ x * MvPolynomial.C center ^ (col.x - x) * (col.x.choose x : DifferentialPolynomial F 2) *
        (MvPolynomial.X (some 0) ^ a * MvPolynomial.C received ^ (col.y₀ - a) *
          (col.y₀.choose a : DifferentialPolynomial F 2))) *
        (∏ j, MvPolynomial.X (some j.succ) ^ col.higher j) =
      coeff • (column A s l).polynomial := by
    rw [smul_eq_C_mul, SourceColumn.polynomial_eq_sourceMonomial]
    change _ = MvPolynomial.C coeff * sourceMonomial x a col.higher
    simp only [coeff, sourceMonomial, map_mul, map_pow, map_natCast]
    ac_rfl
  rw [hterm]
  exact (sourceSpan F A s).smul_mem coeff (column_mem_sourceSpan l)
private def pointMatrix {F : Type*} [Field F] (A : ℕ) (s : Source)
    (center received : F) : Matrix (LowContactIndex 2 s.m) (ColumnIndex A s) F :=
  fun row i => localConstraintCoordinatesAt s.m center received (column A s i).polynomial row
private theorem point_rank_le_origin {F : Type*} [Field F] {A : ℕ} {s : Source}
    (hs : ShapeOK s) (center received : F) :
    (pointMatrix A s center received).rank ≤ (pointMatrix A s (0 : F) 0).rank := by
  classical
  let L := localConstraintCoordinatesAt (R := F) (d := 2) s.m 0 0
  have hmap : (sourceSpan F A s).map L =
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hspan : Submodule.span F (Set.range (pointMatrix A s center received).col) ≤
      Submodule.span F (Set.range (pointMatrix A s (0 : F) 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hmap]
    exact ⟨globalPointTranslation center received (column A s i).polynomial,
      translated_column_mem hs center received i,
      (Sol1.C42.coordinates_translation s.m center received (column A s i).polynomial).symm⟩
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix A s (0 : F) 0).col)
  exact Submodule.finrank_mono hspan
private theorem constraint_matrix_map {R S ι κ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : ℕ) (centers received : ι → R) (cols : κ → SourceColumn 2) :
    (localConstraintMatrix m centers received cols).map φ =
      localConstraintMatrix m (fun i => φ (centers i)) (fun i => φ (received i)) cols := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]
set_option maxHeartbeats 800000 in
private theorem native_origin_rank (A : ℕ) (s : Source) :
    (pointMatrix A s (0 : K) 0).rank ≤ originRank A s := by
  let φ : KoalaBear.Field →+* K := algebraMap KoalaBear.Field K
  let P := localConstraintMatrix s.m
    (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  let row : LowContactIndex 2 s.m → Unit × LowContactIndex 2 s.m := fun r => ((), r)
  have hmap : P.map φ =
      localConstraintMatrix s.m (fun _ : Unit => (0 : K)) (fun _ => 0) (column A s) := by
    simpa only [map_zero] using
      constraint_matrix_map φ s.m (fun _ : Unit => (0 : KoalaBear.Field)) (fun _ => 0) (column A s)
  calc
    _ = ((P.map φ).submatrix row (id : ColumnIndex A s → ColumnIndex A s)).rank := by
      rw [hmap]
      rfl
    _ ≤ (P.map φ).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ P.rank := Matrix.rank_map_le φ P
    _ = _ := rfl
private theorem sum_const_card {ι : Type*} [Fintype ι] (r : ℕ) :
    (∑ _ : ι, r) = Fintype.card ι * r := by
  simp
theorem proof : CJ0.c2 := by
  intro A s hs _ w
  let M := localConstraintMatrix s.m (fun i => node i) w (column A s)
  change M.rank ≤ n * originRank A s
  apply (Matrix.rank_prod_rows_le_sum M).trans
  calc
    _ ≤ ∑ _ : Node, originRank A s := by
      apply Finset.sum_le_sum
      intro i _
      change (pointMatrix A s (node i) (w i)).rank ≤ originRank A s
      exact (point_rank_le_origin hs (node i) (w i)).trans (native_origin_rank A s)
    _ = _ := by rw [sum_const_card, ProximityPrize.Benchmark.IRSProfile.card_index]
end
end CJ0_2
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators Polynomial
abbrev Equation := DifferentialPolynomial K 2
def centerMap : (Polynomial K) →+* Geo :=
  (algebraMap FX Geo).comp (algebraMap (Polynomial K) FX)
def lifted (G : Equation) : DifferentialPolynomial Geo 2 :=
  MvPolynomial.map embed G
def initial (G : Equation) : InitialRing 2 :=
  initialJetEquation center (lifted G)
def initialSep (G : Equation) : InitialRing 2 :=
  initialJetSeparant center (lifted G)
def nativeJet (f : (Polynomial K)) : Fin 3 → Geo :=
  polynomialJet center (f.map embed)
structure FactorFamily (Q : Equation) where
  count : ℕ
  source : Fin count → Equation
  equation : Fin count → InitialRing 2
  source_irreducible : ∀ i, Irreducible (source i)
  source_dvd : ∀ i, source i ∣ Q
  irreducible : ∀ i, Irreducible (equation i)
  component : ∀ i, equation i ∣ initial (source i)
  regular : ∀ i, ¬ equation i ∣ initialSep (source i)
  product_dvd : (∏ i, equation i) ∣ initial Q
  covers : ∀ f : (Polynomial K), RegularRoot Q f →
    ∃ i, differentialSpecialization (source i) f = 0 ∧
      MvPolynomial.eval (nativeJet f) (equation i) = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (source i)) ≠ 0
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 Polynomial PolynomialDifferential
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
theorem centerMap_injective : Function.Injective centerMap :=
  (algebraMap FX Geo).injective.comp (IsFractionRing.injective (Polynomial K) FX)
theorem initial_eq_map (G : Equation) :
    initial G = MvPolynomial.map centerMap (MvPolynomial.optionEquivRight K (Fin 3) G) := by
  let a : Equation →+* InitialRing 2 :=
    (MvPolynomial.aeval (fun j : Option (Fin 3) => j.elim (MvPolynomial.C center)
      MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
  let b : Equation →+* InitialRing 2 := (MvPolynomial.map centerMap).comp
    (MvPolynomial.optionEquivRight K (Fin 3)).toAlgHom.toRingHom
  have he : a = b := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change a (MvPolynomial.C c) = b (MvPolynomial.C c)
      simp [a, b]
      rfl
    · intro j
      cases j with
      | none =>
        simp [a, b]
        rfl
      | some j => simp [a, b]
  exact DFunLike.congr_fun he G
theorem initial_injective : Function.Injective initial := by
  intro P Q h
  rw [initial_eq_map, initial_eq_map] at h
  exact (MvPolynomial.optionEquivRight K (Fin 3)).injective
    (MvPolynomial.map_injective _ centerMap_injective h)
theorem initial_ne_zero {G : Equation} (hG : G ≠ 0) : initial G ≠ 0 := by
  intro h
  apply hG
  exact initial_injective (h.trans (by simp [initial, lifted, initialJetEquation]))
theorem eval_at_center (P : (Polynomial K)) : (P.map embed).eval center = centerMap P := by
  rw [eval_map]
  change eval₂RingHom embed center P = centerMap P
  have h : eval₂RingHom embed center = centerMap := by
    apply Polynomial.ringHom_ext
    · intro a
      change eval₂ embed center (Polynomial.C a) = centerMap (Polynomial.C a)
      rw [eval₂_C]
      rfl
    · change eval₂ embed center Polynomial.X = centerMap Polynomial.X
      rw [eval₂_X]
      rfl
  rw [h]
theorem initial_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initial G) =
      centerMap (differentialSpecialization G f) := by
  rw [initial, ← MvPolynomial.aeval_eq_eval, aeval_initialJetEquation, nativeJet,
    ← eval_differentialSpecialization, lifted, ← map_differentialSpecialization, eval_at_center]
theorem initialSep_eval (G : Equation) (f : (Polynomial K)) :
    MvPolynomial.eval (nativeJet f) (initialSep G) =
      centerMap (differentialSpecialization (separant G (Fin.last 2)) f) := by
  have he : initialSep G = initial (separant G (Fin.last 2)) := by
    rw [initialSep, initialJetSeparant, initial, lifted, lifted, map_separant]
    rfl
  rw [he, initial_eval]
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
theorem indexWeight_eq : Astra7.jetWeight 0 1 3 = CJ0.indexWeight := by
  funext i
  cases i <;> simp [Astra7.jetWeight, CJ0.indexWeight]
end
end CJ0_3
end
section
namespace CJ0_3
noncomputable section
open CJ0 PolynomialDifferential
open scoped BigOperators
set_option maxRecDepth 4000
def c1 : Prop :=
  ∀ Q : Equation, Q ≠ 0 → Nonempty (FactorFamily Q)
end
end CJ0_3
end
section
namespace CJ0_3_1
noncomputable section
open CJ0 CJ0_3 Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance : StrongNormalizationMonoid Equation :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : StrongNormalizationMonoid (InitialRing 2) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
private def initialHom : Equation →+* InitialRing 2 :=
  (MvPolynomial.aeval (fun j : Option (Fin 3) =>
    j.elim (MvPolynomial.C center) MvPolynomial.X)).toRingHom.comp (MvPolynomial.map embed)
private theorem root_of_associated {G G' : Equation} {f : (Polynomial K)}
    (ha : Associated G G') (hG : differentialSpecialization G f = 0)
    (hS : differentialSpecialization (separant G (Fin.last 2)) f ≠ 0) :
    differentialSpecialization G' f = 0 ∧
      differentialSpecialization (separant G' (Fin.last 2)) f ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  let ev := differentialSpecializationHom f (d := 2)
  have hu : ev (u : Equation) ≠ 0 := (u.isUnit.map ev).ne_zero
  change ev G = 0 at hG
  change ev (separant G (Fin.last 2)) ≠ 0 at hS
  change ev (G * u) = 0 ∧ ev (separant (G * u) (Fin.last 2)) ≠ 0
  refine ⟨by rw [map_mul, hG, zero_mul], ?_⟩
  rw [separant, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hG, zero_mul, add_zero]
  exact mul_ne_zero hS hu
private theorem root_in_factor {P : InitialRing 2} (hP : P ≠ 0) (u : Fin 3 → Geo)
    (h : MvPolynomial.eval u P = 0) :
    ∃ g ∈ normalizedFactors P, MvPolynomial.eval u g = 0 := by
  have hd := map_dvd (MvPolynomial.eval u) (prod_normalizedFactors hP).symm.dvd
  rw [h, zero_dvd_iff, map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hd
  exact hd
theorem proof : CJ0_3.c1 := by
  classical
  intro Q hQ
  let native := (normalizedFactors Q).toFinset
  let geometric (G : Equation) :=
    (normalizedFactors (initial G)).toFinset.filter fun g => ¬ g ∣ initialSep G
  let pairs := native.sigma geometric
  let n := pairs.card
  let e : Fin n ≃ ↥pairs := (Fintype.equivFinOfCardEq (Fintype.card_coe pairs)).symm
  let entry (i : Fin n) := (e i).val
  have hmember (i : Fin n) : (entry i).1 ∈ native ∧ (entry i).2 ∈ geometric (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hnative (i : Fin n) : (entry i).1 ∈ normalizedFactors Q :=
    Multiset.mem_toFinset.mp (hmember i).1
  have hgeometric (i : Fin n) :
      (entry i).2 ∈ normalizedFactors (initial (entry i).1) ∧
        ¬ (entry i).2 ∣ initialSep (entry i).1 := by
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp (hmember i).2
    exact ⟨Multiset.mem_toFinset.mp hm, hd⟩
  have hprod : (∏ a ∈ pairs, a.2) ∣ initial Q := by
    have hnativeProd : (∏ G ∈ native, G) ∣ Q :=
      (Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hQ).dvd
    have hm := map_dvd initialHom hnativeProd
    rw [map_prod] at hm
    change (∏ a ∈ native.sigma geometric, a.2) ∣ initialHom Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hG => ?_)).trans hm
    have hGne := initial_ne_zero (ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hG))
    change (∏ g ∈ geometric G, g) ∣ initial G
    exact (Finset.prod_dvd_prod_of_subset _ _ id (Finset.filter_subset _ _)).trans
      ((Multiset.toFinset_prod_dvd_prod _).trans (prod_normalizedFactors hGne).dvd)
  refine ⟨⟨n, fun i => (entry i).1, fun i => (entry i).2,
    fun i => irreducible_of_normalized_factor _ (hnative i),
    fun i => dvd_of_mem_normalizedFactors (hnative i),
    fun i => irreducible_of_normalized_factor _ (hgeometric i).1,
    fun i => dvd_of_mem_normalizedFactors (hgeometric i).1,
    fun i => (hgeometric i).2, ?_, ?_⟩⟩
  · have heq : (∏ i : Fin n, (entry i).2) = ∏ a ∈ pairs, a.2 := by
      calc
        _ = ∏ a : ↥pairs, a.val.2 := e.prod_comp (fun a : ↥pairs => a.val.2)
        _ = _ := Finset.prod_coe_sort pairs (fun a => a.2)
    rw [heq]
    exact hprod
  · intro f hreg
    obtain ⟨G, hGir, hGdvd, hGroot, hGsep⟩ := hreg
    obtain ⟨G', hGnative, hGassoc⟩ := exists_mem_normalizedFactors_of_dvd hQ hGir hGdvd
    obtain ⟨hroot, hsep⟩ := root_of_associated hGassoc hGroot hGsep
    have hinitial : MvPolynomial.eval (nativeJet f) (initial G') = 0 := by
      rw [initial_eval, hroot, map_zero]
    have hinitialSep : MvPolynomial.eval (nativeJet f) (initialSep G') ≠ 0 := by
      rw [initialSep_eval]
      exact map_ne_zero_iff centerMap centerMap_injective |>.mpr hsep
    have hne := initial_ne_zero (ne_zero_of_mem_normalizedFactors hGnative)
    obtain ⟨g, hgmem, hgroot⟩ := root_in_factor hne (nativeJet f) hinitial
    have hgreg : ¬ g ∣ initialSep G' := by
      intro hdvd
      have hm := map_dvd (MvPolynomial.eval (nativeJet f)) hdvd
      rw [hgroot, zero_dvd_iff] at hm
      exact hinitialSep hm
    have hpair : (⟨G', g⟩ : Sigma fun _ : Equation => InitialRing 2) ∈ pairs :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGnative,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgmem, hgreg⟩⟩
    let a : ↥pairs := ⟨⟨G', g⟩, hpair⟩
    refine ⟨e.symm a, ?_⟩
    change differentialSpecialization (e (e.symm a)).val.1 f = 0 ∧
      MvPolynomial.eval (nativeJet f) (e (e.symm a)).val.2 = 0 ∧
      MvPolynomial.eval (nativeJet f) (initialSep (e (e.symm a)).val.1) ≠ 0
    rw [e.apply_symm_apply]
    exact ⟨hroot, hgroot, hinitialSep⟩
end
end CJ0_3_1
end
section
namespace CJ0_3_2
noncomputable section
open CJ0 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxRecDepth 4000
private def coeffWeight {L : ℕ} (i : Fin L) : ℕ := i.val - 1
private def jetWeight (L : ℕ) : Option (Fin L) → ℕ :=
  fun i => i.elim 0 coeffWeight
section Field
variable {F : Type*} [Field F]
end Field
end
end CJ0_3_2
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
def sourceIdeal {r : ℕ} (T : Chart r) : Ideal (InitialRing r) :=
  Ideal.span {T.equation}
def bandSpace (a d e : ℕ) : Submodule Geo (InitialRing 2) :=
  restrictSupport Geo
    {u : Fin 3 →₀ ℕ | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
theorem mem_bandSpace {a d e : ℕ} {P : InitialRing 2} :
    P ∈ bandSpace a d e ↔
      P.totalDegree ≤ a ∧ P.weightedTotalDegree Fin.val ≤ d ∧ P.degreeOf (Fin.last 2) ≤ e := by
  rw [bandSpace, mem_restrictSupport_iff, totalDegree, weightedTotalDegree,
    Finset.sup_le_iff, Finset.sup_le_iff, degreeOf_le_iff]
  exact ⟨fun h => ⟨fun _ hu => (h hu).1, fun _ hu => (h hu).2.1, fun _ hu => (h hu).2.2⟩,
    fun ⟨ha, hd, he⟩ _ hu => ⟨ha _ hu, hd _ hu, he _ hu⟩⟩
theorem bandSpace_mono {a d e a' d' e' : ℕ} (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    bandSpace a d e ≤ bandSpace a' d' e' := by
  intro P hP
  obtain ⟨h₁, h₂, h₃⟩ := mem_bandSpace.mp hP
  exact mem_bandSpace.mpr ⟨h₁.trans ha, h₂.trans hd, h₃.trans he⟩
instance (a d e : ℕ) : Module.Finite Geo (bandSpace a d e) :=
  Module.Finite.of_injective
    (Submodule.inclusion (show bandSpace a d e ≤ restrictTotalDegree (Fin 3) Geo a from
      fun _ hP => (mem_restrictTotalDegree _ _ _).mpr (mem_bandSpace.mp hP).1))
    (Submodule.inclusion_injective _)
theorem mul_mem_bandSpace {a d e b j c : ℕ} {P Q : InitialRing 2}
    (hP : P ∈ bandSpace a d e) (hQ : Q ∈ bandSpace b j c) :
    P * Q ∈ bandSpace (a + b) (d + j) (e + c) := by
  obtain ⟨hP₁, hP₂, hP₃⟩ := mem_bandSpace.mp hP
  obtain ⟨hQ₁, hQ₂, hQ₃⟩ := mem_bandSpace.mp hQ
  exact mem_bandSpace.mpr
    ⟨(totalDegree_mul _ _).trans (Nat.add_le_add hP₁ hQ₁),
     (weightedTotalDegree_mul_le _ _ _).trans (Nat.add_le_add hP₂ hQ₂),
     (degreeOf_mul_le _ _ _).trans (Nat.add_le_add hP₃ hQ₃)⟩
def quotientBand (T : Chart 2) (a d e : ℕ) :
    Submodule Geo (InitialRing 2 ⧸ sourceIdeal T) :=
  (bandSpace a d e).map (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap
theorem quotientBand_mono (T : Chart 2) {a d e a' d' e' : ℕ}
    (ha : a ≤ a') (hd : d ≤ d') (he : e ≤ e') :
    quotientBand T a d e ≤ quotientBand T a' d' e' :=
  Submodule.map_mono (bandSpace_mono ha hd he)
instance (T : Chart 2) (a d e : ℕ) : Module.Finite Geo (quotientBand T a d e) := by
  unfold quotientBand
  infer_instance
def bandCount (a d e : ℚ) : ℚ :=
  (e + 1) * (d + 1 - e) * (2 * a + 2 - d) / 2
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial
section
variable {r : ℕ}
abbrev ChartOpen (T : Chart r) :=
  Localization.Away (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def localize (T : Chart r) : InitialRing r →ₐ[Geo] ChartOpen T :=
  (IsScalarTower.toAlgHom Geo (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)).comp
    (Ideal.Quotient.mkₐ Geo (sourceIdeal T))
def invDenom (T : Chart r) : ChartOpen T :=
  IsLocalization.Away.invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
theorem denom_mul_inv (T : Chart r) :
    localize T T.denominator * invDenom T = 1 :=
  IsLocalization.Away.mul_invSelf (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
def chartMap (T : Chart r) : CoeffRing →ₐ[Geo] ChartOpen T :=
  aeval fun i => localize T (T.numerator i) * invDenom T
private theorem in_zeroLocus {T : Chart r} {y : Fin (r+1) → Geo}
    (hy : y ∈ T.locus) : y ∈ zeroLocus Geo (sourceIdeal T) := by
  apply mem_zeroLocus_iff_le_ker_aeval.mpr
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact RingHom.mem_ker.mpr hy.1
private def pointEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    (InitialRing r ⧸ sourceIdeal T) →ₐ[Geo] Geo :=
  Ideal.Quotient.liftₐ (sourceIdeal T) (aeval y) fun q hq => in_zeroLocus hy q hq
def openEval {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus) :
    ChartOpen T →ₐ[Geo] Geo :=
  IsLocalization.Away.liftAlgHom (f := pointEval hy)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
theorem openEval_localize {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : InitialRing r) : openEval hy (localize T q) = eval y q :=
  IsLocalization.Away.lift_eq (g := (pointEval hy).toRingHom)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
    (Ideal.Quotient.mk (sourceIdeal T) q)
theorem openEval_chartMap {T : Chart r} {y : Fin (r+1) → Geo} (hy : y ∈ T.locus)
    (q : CoeffRing) : openEval hy (chartMap T q) = eval (T.output y) q := by
  have hu := congrArg (openEval hy) (denom_mul_inv T)
  rw [map_mul, openEval_localize, map_one] at hu
  have hi : openEval hy (invDenom T) = (eval y T.denominator)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hy.2).mpr ((mul_comm _ _).trans hu)
  have h : (openEval hy).comp (chartMap T) = aeval (T.output y) := by
    apply MvPolynomial.algHom_ext
    intro i
    change openEval hy (chartMap T (MvPolynomial.X i)) = aeval (T.output y) (MvPolynomial.X i)
    rw [chartMap, aeval_X, map_mul, openEval_localize, hi, aeval_X, Chart.output, div_eq_mul_inv]
  exact DFunLike.congr_fun h q
private theorem eq_zero_of_openEval {T : Chart r} [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) {z : ChartOpen T}
    (hz : ∀ y (hy : y ∈ T.locus), openEval hy z = 0) : z = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator) z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  change z * localize T T.denominator ^ m = localize T q at ha
  have hq : q ∈ sourceIdeal T := by
    have hmul : T.denominator * q ∈ sourceIdeal T := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := Geo) (sourceIdeal T)]
      intro y hy
      change eval y (T.denominator * q) = 0
      by_cases hyD : eval y T.denominator = 0
      · rw [map_mul, hyD, zero_mul]
      · have hy' : y ∈ T.locus := ⟨hy _ (Ideal.subset_span (by simp)), hyD⟩
        have he := congrArg (openEval hy') ha
        rw [map_mul, map_pow, openEval_localize, openEval_localize, hz y hy', zero_mul] at he
        rw [map_mul, ← he, mul_zero]
    exact (‹(sourceIdeal T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0 : localize T q = 0 := by
    change algebraMap (InitialRing r ⧸ sourceIdeal T) (ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
  rw [hq0] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
    (Ideal.Quotient.mk (sourceIdeal T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (zero_mul _).symm)
theorem imageIdeal_eq_ker (T : Chart r) [(sourceIdeal T).IsPrime]
    (hD : T.denominator ∉ sourceIdeal T) : T.ideal = RingHom.ker (chartMap T).toRingHom := by
  ext q
  change q ∈ vanishingIdeal Geo T.imageSet ↔ chartMap T q = 0
  constructor
  · intro hq
    apply eq_zero_of_openEval hD
    intro y hy
    rw [openEval_chartMap hy]
    exact hq _ ⟨y, hy, rfl⟩
  · intro hq
    rintro _ ⟨y, hy, rfl⟩
    change eval (T.output y) q = 0
    rw [← openEval_chartMap hy, hq, map_zero]
private def jetForm (j : ℕ) : CoeffRing :=
  ∑ i : Fin k, C ((i.val.choose j : Geo) * center^(i.val-j)) * MvPolynomial.X i
end
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4
noncomputable section
open CJ0 MvPolynomial Filter
open scoped BigOperators
def c1 : Prop :=
  ∀ (T : Chart 2) (a d e : ℕ), ChartOK T →
    T.denominator ∈ bandSpace a d e →
    (∀ i, T.numerator i ∈ bandSpace a d e) →
    ∀ m : ℕ, affineHilbertFunction T.ideal m ≤
      Module.finrank Geo (quotientBand T (m * a) (m * d) (m * e))
def c2 : Prop :=
  ∀ (a d e : ℕ), d ≤ a → 2 * e ≤ d →
    (Module.finrank Geo (bandSpace a d e) : ℚ) = bandCount a d e
private theorem quotientBand_add_finrank_le (T : Chart 2) (a d e b j c : ℕ)
    (hn : T.equation ≠ 0) (hf : T.equation ∈ bandSpace b j c) :
    Module.finrank Geo (quotientBand T (a+b) (d+j) (e+c)) +
      Module.finrank Geo (bandSpace a d e) ≤
      Module.finrank Geo (bandSpace (a+b) (d+j) (e+c)) := by
  let W := bandSpace (a+b) (d+j) (e+c)
  let F := (Ideal.Quotient.mkₐ Geo (sourceIdeal T)).toLinearMap.domRestrict W
  have hF : LinearMap.range F = quotientBand T (a+b) (d+j) (e+c) :=
    LinearMap.range_domRestrict W _
  let mul := (LinearMap.mulLeft Geo T.equation).domRestrict (bandSpace a d e)
  have hmul (p : bandSpace a d e) : mul p ∈ W := by
    simpa only [mul, W, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, Nat.add_comm]
      using mul_mem_bandSpace hf p.property
  let g : bandSpace a d e →ₗ[Geo] W := mul.codRestrict W hmul
  have hg (p : bandSpace a d e) : g p ∈ LinearMap.ker F := by
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (sourceIdeal T) (T.equation * p.val) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val, rfl⟩)
  let G := g.codRestrict (LinearMap.ker F) hg
  have hG : Function.Injective G := by
    intro p q hpq
    have he : T.equation * p.val = T.equation * q.val :=
      congrArg (fun x : LinearMap.ker F => x.val.val) hpq
    exact Subtype.ext (mul_left_cancel₀ hn he)
  have hRank := F.finrank_range_add_finrank_ker
  rw [hF] at hRank
  exact (Nat.add_le_add_left (LinearMap.finrank_le_finrank_of_injective hG) _).trans_eq hRank
def surfaceBound (a d e b j c : ℚ) : ℚ :=
  2 * e * (d-e) * b + e * (2*a-2*d+e) * j + (d-2*e) * (2*a-d) * c
private abbrev indexDegree (P : InitialRing 2) : ℕ :=
  P.weightedTotalDegree Fin.val
private theorem band_difference (a d e b j c : ℚ) :
    ∃ u v : ℚ, ∀ x : ℚ,
      bandCount (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
        bandCount (x*a+j+2*c) (x*d+2*c) (x*e) =
      (surfaceBound a d e b j c / 2) * x^2 + u*x + v := by
  let f (x : ℚ) :=
    bandCount (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
      bandCount (x*a+j+2*c) (x*d+2*c) (x*e)
  refine ⟨f 1 - f 0 - surfaceBound a d e b j c / 2, f 0, fun x => ?_⟩
  dsimp [f, bandCount, surfaceBound]
  ring
private theorem degree_le_of_quadratic
    (I : Ideal CoeffRing) (hdim : (affineHilbertPolynomial I).natDegree = 2)
    (q u v : ℚ) (hle : ∀ᶠ m : ℕ in atTop,
      (affineHilbertPolynomial I).eval (m : ℚ) ≤ q * (m : ℚ)^2 + u * (m : ℚ) + v) :
    affineDegree I ≤ 2 * q := by
  let P : Polynomial ℚ := Polynomial.C q * Polynomial.X^2 +
    Polynomial.C u * Polynomial.X + Polynomial.C v
  have hP : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial I).eval (m : ℚ) ≤ P.eval (m : ℚ) := by
    filter_upwards [hle] with m hm
    simpa [P] using hm
  obtain ⟨hnat, hlead⟩ := Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hP
  have hdeg : P.natDegree = 2 := by
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      have h₀ : i ≠ 0 := by omega
      have h₁ : i ≠ 1 := by omega
      have h₂ : i ≠ 2 := by omega
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      simp [h₀, h₁, h₂]
    · simpa only [hdim] using hnat
  have hc : P.leadingCoeff = q := by
    rw [Polynomial.leadingCoeff, hdeg]
    simp [P]
  have hcoeff := hlead (hdim.trans hdeg.symm)
  rw [hc] at hcoeff
  rw [affineDegree, hdim]
  exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
theorem chart_degree (h1 : c1) (h2 : c2)
    (T : Chart 2) (hT : ChartOK T) (hdim : (affineHilbertPolynomial T.ideal).natDegree = 2)
    (a d e : ℕ) (hda : d ≤ a) (hed : 2*e ≤ d)
    (hD : T.denominator ∈ bandSpace a d e) (hN : ∀ i, T.numerator i ∈ bandSpace a d e) :
    affineDegree T.ideal ≤ surfaceBound a d e T.equation.totalDegree
      (indexDegree T.equation)
      (T.equation.degreeOf (Fin.last 2)) := by
  let b := T.equation.totalDegree
  let j := indexDegree T.equation
  let c := T.equation.degreeOf (Fin.last 2)
  have hf : T.equation ∈ bandSpace b j c := mem_bandSpace.mpr ⟨le_rfl, le_rfl, le_rfl⟩
  obtain ⟨u, v, hexpand⟩ := band_difference a d e b j c
  have hle : ∀ᶠ m : ℕ in atTop, (affineHilbertPolynomial T.ideal).eval (m : ℚ) ≤
      (surfaceBound a d e b j c / 2) * (m : ℚ)^2 + u * (m : ℚ) + v := by
    filter_upwards [eventually_eval_affineHilbertPolynomial T.ideal] with m hm
    have hma := Nat.mul_le_mul_left m hda
    have hme : 2*(m*e) ≤ m*d := by
      simpa only [Nat.mul_left_comm 2 m e] using Nat.mul_le_mul_left m hed
    have hmono : Module.finrank Geo (quotientBand T (m*a) (m*d) (m*e)) ≤
        Module.finrank Geo (quotientBand T (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c)) :=
      Submodule.finrank_mono (quotientBand_mono T (by omega) (by omega) (by omega))
    have hdimNat := (Nat.add_le_add_right ((h1 T a d e hT hD hN m).trans hmono) _).trans
      (quotientBand_add_finrank_le T (m*a+j+2*c) (m*d+2*c) (m*e) b j c hT.irreducible.ne_zero hf)
    have hdimRat := (Nat.cast_le (α := ℚ)).mpr hdimNat
    rw [Nat.cast_add,
      h2 (m*a+j+2*c) (m*d+2*c) (m*e) (by omega) (by omega),
      h2 (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c) (by omega) (by omega)] at hdimRat
    push_cast at hdimRat
    rw [hm, ← hexpand (m : ℚ)]
    exact le_sub_iff_add_le.mpr hdimRat
  calc
    _ ≤ 2 * (surfaceBound a d e b j c / 2) :=
      degree_le_of_quadratic T.ideal hdim (surfaceBound a d e b j c / 2) u v hle
    _ = _ := by ring
end
end CJ0_4
end
section
set_option autoImplicit false
namespace CJ0_4_1
noncomputable section
open CJ0 CJ0_4 MvPolynomial
theorem proof : CJ0_4.c1 := by
  intro T a d e hT hD hN m
  let : (sourceIdeal T).IsPrime :=
    (Ideal.span_singleton_prime hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator ∉ sourceIdeal T :=
    fun h => hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [imageIdeal_eq_ker T hD']
  let j := IsScalarTower.toAlgHom Geo (InitialRing 2 ⧸ sourceIdeal T) (ChartOpen T)
  let δ := localize T T.denominator
  have hδ : IsUnit δ :=
    IsLocalization.Away.algebraMap_isUnit (S := ChartOpen T)
      (Ideal.Quotient.mk (sourceIdeal T) T.denominator)
  let y (i : Fin k) := localize T (T.numerator i) * invDenom T
  have hy (i : Fin k) : δ * y i = localize T (T.numerator i) := by
    change localize T T.denominator * (localize T (T.numerator i) * invDenom T) = _
    rw [mul_left_comm _ (localize T (T.numerator i)), denom_mul_inv, mul_one]
  let V (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (quotientBand T (n * a) (n * d) (n * e)).map j.toLinearMap
  let W (n : ℕ) : Submodule Geo (ChartOpen T) :=
    (V n).comap (LinearMap.mulLeft Geo (δ ^ n))
  have hW (n : ℕ) (z : ChartOpen T) :
      z ∈ W n ↔ ∃ P ∈ bandSpace (n * a) (n * d) (n * e), localize T P = δ ^ n * z := by
    change δ ^ n * z ∈ V n ↔ _
    simp only [V, quotientBand, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap,
      Submodule.mem_map, AlgHom.toLinearMap_apply, localize, j]
  have hOne : (1 : InitialRing 2) ∈ bandSpace 0 0 0 := by
    have hw : weightedTotalDegree Fin.val (1 : InitialRing 2) = 0 := by
      rw [← C_1, weightedTotalDegree_C]
    exact mem_bandSpace.mpr ⟨totalDegree_one.le, hw.le, (degreeOf_one _).le⟩
  have hpow (n : ℕ) :
      T.denominator ^ n ∈ bandSpace (n * a) (n * d) (n * e) := by
    induction n with
    | zero => simpa only [pow_zero, Nat.zero_mul] using hOne
    | succ n ih => simpa only [pow_succ, Nat.succ_mul] using mul_mem_bandSpace ih hD
  have hmono : Monotone W := by
    intro n l hnl z hz
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator ^ (l - n) * P, ?_, ?_⟩
    · simpa only [← Nat.add_mul, Nat.sub_add_cancel hnl] using
        mul_mem_bandSpace (hpow (l - n)) hP
    · rw [map_mul, map_pow, heq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnl]
  have hmul (i : Fin k) (n : ℕ) (z : ChartOpen T) (hz : z ∈ W n) :
      y i * z ∈ W (n + 1) := by
    obtain ⟨P, hP, heq⟩ := (hW _ _).mp hz
    refine (hW _ _).mpr ⟨P * T.numerator i, ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.one_mul] using mul_mem_bandSpace hP (hN i)
    · rw [map_mul, heq, ← hy i, pow_succ]
      ac_rfl
  have h0 : (1 : ChartOpen T) ∈ W 0 :=
    (hW _ _).mpr ⟨1, by simpa only [Nat.zero_mul] using hOne, by simp⟩
  have hclear (P : CoeffRing) (hP : P.totalDegree ≤ m) : chartMap T P ∈ W m := by
    change aeval y P ∈ W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q := RingHom.ker (chartMap T).toRingHom
  let ι : (CoeffRing ⧸ Q) →ₐ[Geo] ChartOpen T := Ideal.kerLiftAlg (chartMap T)
  have hmem (x : quotientDegreeLE Q m) : δ ^ m * ι x.val ∈ V m := by
    obtain ⟨P, hP, heq⟩ := mem_quotientDegreeLE.mp x.property
    change ι x.val ∈ W m
    rw [← heq]
    change chartMap T P ∈ W m
    exact hclear P hP
  let L : quotientDegreeLE Q m →ₗ[Geo] V m :=
    (((LinearMap.mulLeft Geo (δ ^ m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL : Function.Injective L := by
    intro x z hxz
    have h : δ ^ m * ι x.val = δ ^ m * ι z.val := congrArg Subtype.val hxz
    exact Subtype.ext (Ideal.kerLiftAlg_injective (chartMap T) ((hδ.pow m).mul_left_cancel h))
  exact (LinearMap.finrank_le_finrank_of_injective hL).trans (Submodule.finrank_map_le _ _)
end
end CJ0_4_1
end
section
set_option autoImplicit false
namespace CJ0_4_2
noncomputable section
open CJ0 CJ0_4 MvPolynomial
open scoped BigOperators
private abbrev BandExponents (a d e : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {u | u.degree ≤ a ∧ u.weight Fin.val ≤ d ∧ u (Fin.last 2) ≤ e}
private theorem degree_fin_three (u : Fin 3 →₀ ℕ) :
    u.degree = u 0 + u 1 + u 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc]
private theorem degree_fin_two (u : Fin 2 →₀ ℕ) : u.degree = u 0 + u 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
private theorem index_fin_three (u : Fin 3 →₀ ℕ) :
    u.weight Fin.val = u 1 + 2 * u 2 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_three, Nat.mul_comm]
private def bandFibers (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    BandExponents a d e ≃ Σ z : Fin (e + 1),
      cappedDegreeExponents (Fin 2) 1 (a - z) (d - 2 * z) where
  toFun u := by
    have htotal := u.property.1
    have hindex := u.property.2.1
    have htop := u.property.2.2
    rw [degree_fin_three] at htotal
    rw [index_fin_three] at hindex
    change u.val 2 ≤ e at htop
    let z : Fin (e + 1) := ⟨u.val 2, Nat.lt_succ_of_le htop⟩
    refine ⟨z, ⟨Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1], ?_⟩⟩
    rw [mem_cappedDegreeExponents, degree_fin_two]
    change u.val 0 + u.val 1 ≤ a - u.val 2 ∧ u.val 1 ≤ d - 2 * u.val 2
    omega
  invFun p := by
    obtain ⟨z, u⟩ := p
    have htotal := u.property.1
    rw [degree_fin_two] at htotal
    have hindex := u.property.2
    have hz := z.isLt
    let v : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u.val 0, u.val 1, z.val]
    refine ⟨v, ?_⟩
    change v.degree ≤ a ∧ v.weight Fin.val ≤ d ∧ v (Fin.last 2) ≤ e
    rw [degree_fin_three, index_fin_three]
    change u.val 0 + u.val 1 + z.val ≤ a ∧ u.val 1 + 2 * z.val ≤ d ∧ z.val ≤ e
    omega
  left_inv u := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨z, hz⟩, u⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
private theorem sum_widths (d e : ℕ) (hed : 2 * e ≤ d) :
    (∑ z ∈ Finset.range (e + 1), (d - 2 * z + 1)) = (e + 1) * (d + 1 - e) := by
  calc
    _ = ∑ z ∈ Finset.range (e + 1), (d - 2 * (e - z) + 1) := by
      symm
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun z => d - 2 * z + 1) (e + 1)
    _ = ∑ z ∈ Finset.range (e + 1), ((d - 2 * e + 1) + 2 * z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hz' := Finset.mem_range.mp hz
      omega
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
        ← Finset.mul_sum, mul_comm 2 (∑ z ∈ Finset.range (e + 1), z),
        Finset.sum_range_id_mul_two, Nat.add_sub_cancel, ← Nat.mul_add]
      congr 1
      omega
private theorem two_mul_finrank_band (a d e : ℕ) (hda : d ≤ a) (hed : 2 * e ≤ d) :
    2 * Module.finrank Geo (bandSpace a d e) = (e + 1) * (d + 1 - e) * (2 * a + 2 - d) := by
  rw [bandSpace, Module.finrank_eq_nat_card_basis (basisRestrictSupport Geo _),
    Nat.card_congr (bandFibers a d e hda hed), Nat.card_sigma, Finset.mul_sum]
  calc
    _ = ∑ z : Fin (e + 1), (d - 2 * z.val + 1) * (2 * a + 2 - d) := by
      apply Finset.sum_congr rfl
      intro z _
      have hz := z.isLt
      have hcap : d - 2 * z.val ≤ a - z.val := by omega
      rw [Nat.card_coe_set_eq, two_mul_ncard_cappedDegreeExponents_fin_two _ _ hcap]
      congr 1
      omega
    _ = _ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun z => d - 2 * z + 1),
        sum_widths d e hed]
theorem proof : CJ0_4.c2 := by
  intro a d e hda hed
  have he : e ≤ d + 1 := by omega
  have hd : d ≤ 2 * a + 2 := by omega
  have h := congrArg (fun n : ℕ => (n : ℚ)) (two_mul_finrank_band a d e hda hed)
  push_cast [Nat.cast_sub he, Nat.cast_sub hd] at h
  unfold bandCount
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  rw [mul_comm]
  exact h
end
end CJ0_4_2
end

end Merged_ListProofA
