import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.PortLowBase
import ProximityPrize.SubmissionLower.Fast077

set_option Elab.async false

-- merged module PortFrontA
section Merged_PortFrontA
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
namespace P0_4
noncomputable section
open Polynomial P0
private theorem threeUAt_eq (q : ℕ) (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) :
    threeUAt q a β = K1_8.threeUAt q a β := by
  delta threeUAt K1_8.threeUAt P0.liftX K1.liftX P0.seed K1.seed P0.twist K1.twist P0.p K1.p
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem relationOnAt_eq (q : ℕ) (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOnAt q u S U V W = K1_8.relationOnAt q u S U V W := by
  delta relationOnAt K1_8.relationOnAt P0.node K1.node P0.Words K1.Words P0.I K1.I
    P0.Bivar K1.Bivar P0.K K1.K
  rfl
private theorem columnRankAt_eq (q : ℕ) (U V : Bivar) :
    columnRankAt q U V = K1_8.columnRankAt q U V := by
  delta columnRankAt K1_8.columnRankAt P0.seed K1.seed P0.extendSeed K1.extendSeed
    P0.Bivar K1.Bivar P0.Frac K1.Frac P0.K K1.K
  rfl
open K1_8 (threeUAt_native)
private theorem native_threeU :
    threeUAt P0.p = (P0.threeU : (Polynomial K) → (Fin 2 → (Polynomial K)) → Bivar) := by
  unfold threeUAt P0.threeU
  rfl
theorem threeU_eq (a : (Polynomial K)) (β : Fin 2 → (Polynomial K)) :
    P0.threeU a β = K1.threeU a β := by
  calc
    P0.threeU a β = threeUAt P0.p a β := congrFun (congrFun native_threeU.symm a) β
    _ = K1_8.threeUAt P0.p a β := threeUAt_eq P0.p a β
    _ = K1_8.threeUAt K1.p a β := congrArg (fun q => K1_8.threeUAt q a β) (show P0.p = K1.p from rfl)
    _ = K1.threeU a β := congrFun (congrFun K1_8.threeUAt_native a) β
theorem relationOn_eq (u : Words) (S : Finset I) (U V W : Bivar) :
    relationOn u S U V W = K1_8.relationOnAt K1.p u S U V W := by
  calc
    _ = relationOnAt P0.p u S U V W := by delta P0.relationOn relationOnAt; rfl
    _ = K1_8.relationOnAt P0.p u S U V W := relationOnAt_eq P0.p u S U V W
    _ = K1_8.relationOnAt K1.p u S U V W :=
      congrArg (fun q => K1_8.relationOnAt q u S U V W) (show P0.p = K1.p from rfl)
theorem columnRank_eq (U V : Bivar) : columnRank U V = K1.columnRank U V := by
  calc
    _ = columnRankAt P0.p U V := by delta P0.columnRank columnRankAt; rfl
    _ = K1_8.columnRankAt P0.p U V := columnRankAt_eq P0.p U V
    _ = K1_8.columnRankAt K1.p U V := congrArg (fun q => K1_8.columnRankAt q U V) (show P0.p = K1.p from rfl)
    _ = _ := by delta K1_8.columnRankAt K1.columnRank; rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P0_4
noncomputable section
open Polynomial P0 FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open K1_8 (transfer_at)
open K1_8 (threeU_height threeV_height common_multiplier multiplier_degree_zero seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU)
theorem sameDirection_eq (U V P Q : Bivar) :
    sameDirection U V P Q = K1.sameDirection U V P Q := by
  delta P0.sameDirection K1.sameDirection
  rfl
theorem threeV_eq (b : (Polynomial K)) (α : Fin 2 → (Polynomial K)) :
    threeV b α = K1.threeV b α := by
  delta P0.threeV K1.threeV P0.liftX K1.liftX P0.seed K1.seed
  rfl
end
end P0_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace P0_5
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P0 (Words k amplitudeDegree)
open K1_9 (K I node twist pencil fold pencil_degree
  seedCoeff crossValue CoefficientIdentities sixNorm_mul sixNorm_ne_zero)
open K1_9 (seedCoeff_degree)
abbrev heightBound : ℕ := 32781
structure PolarData (u : Words) where
  a : (Polynomial K)
  b : (Polynomial K)
  A : Fin 2 → (Polynomial K)
  Q : K → K → (Polynomial K)
  a_ne : a ≠ 0
  norms_ne : K1.sixNorm a ≠ K1.sixNorm b
  primitive : IsCoprime (A 0) (A 1)
  a_bound : a.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  b_bound : b.natDegree + amplitudeDegree (A 0) (A 1) ≤ heightBound
  Q_degree : ∀ r s, (Q r s).degree < (k + heightBound : ℕ)
  nodes : ∀ r s i,
    (Q r s).eval (node i) =
      a.eval (node i) * twist ((pencil (A 0) (A 1) r).eval (node i)) * fold u s i -
      b.eval (node i) * (pencil (A 0) (A 1) s).eval (node i) * twist (fold u r i)
theorem pow_eq_twist (z : K) : z ^ P0.p = twist z :=
  (frobenius_def P0.p z).symm
theorem threeUAt_native : threeUAt P0.p = P0.threeU := by
  unfold threeUAt P0.threeU
  rfl
theorem relationOnAt_native : relationOnAt P0.p = P0.relationOn := by
  unfold relationOnAt P0.relationOn
  rfl
theorem coefficientsAt (q : ℕ) (hq : 1 < q) (hσ : ∀ z : K, z ^ q = twist z)
    (u : Words) (deleted : Finset I) (a b : (Polynomial K)) (A B : Fin 2 → (Polynomial K))
    (output : P0.Bivar) (hp : A = B)
    (hn : relationOnAt q u deleted (threeUAt q a B) (P0.threeV b A) output)
    (i : I) (hi : i ∉ deleted) :
    (seedCoeff output 0).eval (node i) = crossValue u a b A i 0 0 ∧
    (seedCoeff output 1).eval (node i) = crossValue u a b A i 0 1 ∧
    (seedCoeff output q).eval (node i) = crossValue u a b A i 1 0 ∧
    (seedCoeff output (q + 1)).eval (node i) = crossValue u a b A i 1 1 := by
  subst B
  exact K1_9.coefficients_at_node u a b A i q hq hσ output (threeUAt q a A)
    (K1_9.eval_first a A i q) (hn i hi).symm
end
end P0_5
end
section
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 900000
namespace P0_7
open P0 Finset
open K1_11 (V J)
def countRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (s + 1 - i) * (t + 1 - j)
def gradeRow (B s t i : ℕ) : ℕ :=
  ∑ j ∈ range (B + 1 - i), (i + j) * ((s + 1 - i) * (t + 1 - j))
def count (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), countRow B s t i
def grade (B s t : ℕ) : ℕ := ∑ i ∈ range (B + 1), gradeRow B s t i
def contactRow (m s t i : ℕ) : ℕ :=
  ∑ j ∈ range (m - i), (m - i - j) * (s + 1 - i) * (t + 1 - j)
theorem V_affine (D w B s t : ℕ) (hB : w * B ≤ D + 1) :
    V D w B s t + w * grade B s t = (D + 1) * count B s t := by
  unfold V count grade countRow gradeRow
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hij : i + j ≤ B := by
    simp only [mem_range] at hi hj
    omega
  have hw := (Nat.mul_le_mul_left w hij).trans hB
  calc
    _ = ((D + 1 - w * (i + j)) + w * (i + j)) * ((s + 1 - i) * (t + 1 - j)) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hw]
theorem rational_fee (E M exceptionFee limit a b : ℕ) (hb : 0 < b)
    (h : exceptionFee * b^2 + 5 * E * (a*M)^2 ≤ limit * b^2) :
    (exceptionFee : ℚ) + 5 * ((E : ℚ) * (((a : ℚ) / b) * M)^2) ≤ limit := by
  have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
  have h' : (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 ≤
      (limit : ℚ) * (b : ℚ)^2 := by exact_mod_cast h
  refine le_of_mul_le_mul_right ?_ (pow_pos hb' 2)
  calc
    _ = (exceptionFee : ℚ) * (b : ℚ)^2 + 5 * (E : ℚ) * ((a : ℚ) * M)^2 := by
      field_simp
    _ ≤ _ := h'
end P0_7
end

end Merged_PortFrontA

-- merged module RungFront
section Merged_RungFront
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace P1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open K1_8 (certificate_output_zero)
theorem eval_liftX (f : (Polynomial K)) (x : K) : (liftX f).eval (C x) = C (f.eval x) :=
  K1_8.eval_liftX f x
def constantsInFrac : K →+* Frac :=
  K1_8.seedInclusion.comp Polynomial.C
theorem extend_liftX (G : (Polynomial K)) :
    extendSeed (liftX G) = G.map constantsInFrac :=
  Polynomial.map_map Polynomial.C seedInclusion G
end
end P1
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
open P0 (type_one_bad_count_of_syndromes)
open P0 (constantRankCount nativeMoments independent_nativeMoments)
open K1_1
theorem excludes_full_rank {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (q : ℕ) [ExpChar F q] (x : ι → F) (hx : Function.Injective x)
    (hfixed : ∀ i, x i ^ q = x i) (u v : ι → F) (γ : F) (k l t : ℕ)
    (hsize : k + l + t ≤ Fintype.card ι) (P : (Polynomial F)) (hp : P.degree < k)
    (S : Finset ι) (hs : S.card ≤ t) (hagree : ∀ i ∉ S, u i + γ * v i = P.eval (x i)) :
    ((stacked q x u v l t).map (evalRingHom γ)).rank ≠ t + 1 := by
  classical
  let E := locator x S
  have hd : E.natDegree ≤ t := (locator_natDegree x S).le.trans hs
  let z : Fin (t+1) → F := fun j => E.coeff j.val
  let B := (stacked q x u v l t).map (evalRingHom γ)
  have hv : B.mulVecLin z = 0 :=
    locator_annihilates_stacked q x hx hfixed u v γ k l t hsize P hp S hs hagree
  intro hr
  have hi := Strata.matrix_injective_of_full_column_rank B (by rwa [Fintype.card_fin])
  have hz : z = 0 := hi (hv.trans (map_zero B.mulVecLin).symm)
  have h := congrFun hz (⟨E.natDegree, by omega⟩ : Fin (t+1))
  change E.coeff E.natDegree = 0 at h
  exact one_ne_zero ((locator_monic x S).coeff_natDegree.symm.trans h)
end
end P1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace P1
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open K1_6 (certificate_shifts_annihilate_generic)
open K1_6 (lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator common_node_count)
theorem count_bound {c n n' H b : ℕ}
    (hn : n = n') (hc : c ≤ n * H) (hb : n' * H = b) : c ≤ b :=
  hb ▸ hn ▸ hc
end P1
end

end Merged_RungFront

-- merged module PortLow8
section Merged_PortLow8
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible)
open K1_13_8 (Valid zeroShape  availableMass)
open K1_13_8_2 (Threshold orderFor)
abbrev oneStart : Shape := ⟨1, 3, 1⟩
abbrev twoStart : Shape := ⟨2, 6, 2⟩
def oneOrder (x : Shape) : ℕ := if x.j ≤ 3 then 1 else (3 * x.j - 4) / 2
def indexBudget (r : Shape) (cap j : ℕ) : ℕ := cap * j / (48 - r.j)
end P0_9_8
end
section
namespace P0_9_8
open K1_13 (Shape InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape  availableMass layerTerm)
open K1_13_8_2 (Threshold orderFor)
open scoped BigOperators
theorem symbol_count : ∀ b j, remaining b j = K1_13_8.fastRemaining b j :=
  K1_13_8_1.proof
theorem availableMass_anti_prefix {r y x : Shape} {L : ℕ}
    (hr : r = zeroShape ∨ 0 < r.j) (hj : 0 < r.j + y.j)
    (hb : y.b ≤ x.b) (hidx : y.j ≤ x.j) :
    availableMass r x L ≤ availableMass r y L := by
  let N := max (L + 1650 / (r.j + x.j)) (L + 1650 / (r.j + y.j))
  have hjx : 0 < r.j + x.j := by omega
  rw [← K1_13_8.availableMass_eq_sum symbol_count hr hjx (N := N) (le_max_left _ _),
    ← K1_13_8.availableMass_eq_sum symbol_count hr hj (N := N) (le_max_right _ _)]
  exact Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hb) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_left (k + 1 - L) hidx) _)
theorem orderFor_select (b j : ℕ) (ss : List Threshold) :
    1 ≤ orderFor b j ss ∧
    (orderFor b j ss = 1 ∨ ∃ s ∈ ss, s.b ≤ b ∧ s.j ≤ j ∧ orderFor b j ss = s.l) := by
  induction ss with
  | nil => simp [orderFor]
  | cons s ss ih =>
    unfold orderFor
    let p := if s.b ≤ b ∧ s.j ≤ j then s.l else 1
    change 1 ≤ max p (orderFor b j ss) ∧
      (max p (orderFor b j ss) = 1 ∨ ∃ q ∈ s :: ss,
        q.b ≤ b ∧ q.j ≤ j ∧ max p (orderFor b j ss) = q.l)
    refine ⟨ih.1.trans (le_max_right _ _), ?_⟩
    rcases le_total p (orderFor b j ss) with h | h
    · rw [max_eq_right h]
      rcases ih.2 with h1 | ⟨q, hq, hb, hj, hl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hb, hj, hl⟩
    · rw [max_eq_left h]
      by_cases hbox : s.b ≤ b ∧ s.j ≤ j
      · exact Or.inr ⟨s, List.mem_cons_self, hbox.1, hbox.2, ite_eq_left hbox⟩
      · exact Or.inl (ite_eq_right hbox)
theorem orderFor_mono {b b' j j' : ℕ} (hb : b ≤ b') (hj : j ≤ j') (ss : List Threshold) :
    orderFor b j ss ≤ orderFor b' j' ss := by
  induction ss with
  | nil => exact le_rfl
  | cons s ss ih =>
    unfold orderFor
    by_cases h : s.b ≤ b ∧ s.j ≤ j
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.trans hb, h.2.trans hj⟩]
      exact max_le_max le_rfl ih
    · rw [ite_eq_right h, max_eq_right (orderFor_select b j ss).1]
      exact ih.trans (le_max_right _ _)
end P0_9_8
end
section
namespace P0_9_8_3
open K1_13
open K1_13_8_2 (Chamber mixed_mono)
end P0_9_8_3
end
section
namespace P0_9_8_5
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9 ( physicalDegree  primaryBox taylorLength )
end P0_9_8_5
end

end Merged_PortLow8

-- merged module PortHighFinish
section Merged_PortHighFinish
set_option Elab.async false
set_option autoImplicit true
section
namespace P0_10R
noncomputable section
open P0 (AnchorModel AnchoredFamily K highPrefix)
open P0_10 (BufferedPair BankVanishes freeShape movingShape fullShape MarkOn band TerminalDivisibility)
open K1_14 (Banks Equation)
open K1_14_3 (Surface Parent ProjectedProduct)
def SurfacePass {w : ℤ} {rows : Banks} {i : Fin 2} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ K1_14_3R.compatible pair.free pair.moving q
structure RetainedCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} (pairs : ∀ i : Fin 2, BufferedPair M.overhead rows i) where
  kept : Finset K
  subset : kept ⊆ Γ
  paid : (Γ \ kept).card ≤ highPrefix M.overhead
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, (pairs 0).free ∈ q.asIdeal ∧ (pairs 0).moving ∈ q.asIdeal
  survives : ∀ q ∈ parents, SurfacePass (pairs 1) q
  terminal : ∀ q ∈ parents, BankVanishes rows (fullShape M.overhead) q
  covers : ∀ γ ∈ kept, ∃ q ∈ parents, MarkOn M F q γ
  equation : Equation
  projected : ProjectedProduct parents equation
  y_bound : equation.natDegree ≤ (band M.overhead).yBound
  divides : TerminalDivisibility M.overhead rows equation
end
end P0_10R
namespace P0_10R.Bridge
noncomputable section
open P0 (AnchorModel AnchoredFamily agreement p K t)
open P0_10 (BufferedPair)
open K1_14 (Banks Equation Jet Shape)
open K1_14_2 (Ambient ODE OnJet SmallRootCurve OnRoot endpointDegree)
open K1_14_2_2 (Active Fits)
open Polynomial
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def initialCap : Fin 4 → ℕ := ![5548, 125234, 577116, 5169640]
def initialE₀ : ℕ := 6242936
def initialFee : ℕ := (p+1)*577116 + initialE₀ + 5548 + (p+1)*(1036+4990)
structure InitialCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (P Q : Jet) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  initial : ∀ I ∈ parents, K1_14_2.toJet P ∈ I ∧ K1_14_2.toJet Q ∈ I
  masses : Fits parents initialCap
  direct : Finset K
  paid : direct.card ≤ initialFee
  cover : ∀ γ ∈ Γ, γ ∈ direct ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end P0_10R.Bridge
namespace P0_10R.Later
noncomputable section
open Polynomial
open P0 (agreement)
open K1_14 (Jet Shape atX jetAt)
open K1_14_3 (Surface Parent MassCap mass JetPlane JetCaps SeedCover fixedAt)
open K1_14_3_2 (AtSurface)
structure InitialCover (P Q : Jet) where
  parents : Finset Surface
  geometric : ∀ q ∈ parents, Parent q
  initial : ∀ q ∈ parents, P ∈ q.asIdeal ∧ Q ∈ q.asIdeal
  masses : MassCap parents 1643 28355 183584
  jetMass : mass parents .jets ≤ 1221580
  seeds : SeedCover
  seedDegree : seeds.curve.totalDegree ≤ 183584 + 515 + 1857
  seedPoints : seeds.points.card ≤ 1221580
  ordinates : Finset K1_14.FX
  ordinateCount : ordinates.card ≤ 1643
  lowJet : JetPlane
  fixedFree : JetPlane
  fixedMoving : JetPlane
  lowJet_ne : lowJet ≠ 0
  fixedFree_ne : fixedFree ≠ 0
  fixedMoving_ne : fixedMoving ≠ 0
  lowJet_caps : JetCaps lowJet 183584 28355
  fixedFree_caps : JetCaps fixedFree 47 10
  fixedMoving_caps : JetCaps fixedMoving 93 18
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    seeds.Covers z ∨ atX S ∈ ordinates ∨ fixedAt lowJet S = 0 ∨
    fixedAt fixedFree S = 0 ∨ fixedAt fixedMoving S = 0 ∨
    ∃ q ∈ parents, AtSurface q z S
end
end P0_10R.Later
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 900000
namespace P0_10R.Bridge
noncomputable section
open Polynomial
open P0 (AnchorModel AnchoredFamily agreement p lowCutoff)
open P0_10 (  terminalShape fullShape fullCutoff)
open K1_14 (Banks Shape Jet Equation Seeds FX seedHasse)
open K1_14_2 (Ambient toJet FibreRing mapGenericSeed mapGenericJets eval_toJet generic)
open K1_14_2_2 (Active dual)
open K1_14_3 (Surface Parent SeedClosure SeedField JetField JetClosure JetPlane seedFibreEval
  seedGeneric jetGeneric fixedEmbedding OrderAt ProjectedProduct)
open K1_14_2_6 (genericSeedPoint genericJetPoint)
open K1_14_2_2_4_1 (ambientToJet toJet_equiv)
open K1_14_2_6_1 (fibreHom seedMap jetMap seedPoint jetPoint)
open K1_14_3R_1 (seed_chart toJet_C toJet_y toJet_v toJet_seed jetCoordinates fractionCoordinates generic_C generic_Y generic_V seedGeneric_C)
def surfaceOf (I : Ideal Ambient) (hI : I.IsPrime) : Surface :=
  ⟨I.comap toJet, hI.comap _⟩
private theorem fixed_chart (a b : SeedClosure) :
    (genericJetPoint a b).comp (toJet.comp fixedEmbedding) =
      seedGeneric.comp jetCoordinates.symm.toRingHom := by
  have hV : ((genericJetPoint a b).comp (toJet.comp fixedEmbedding)) (Polynomial.X (R := (Polynomial FX))) =
      (seedGeneric.comp jetCoordinates.symm.toRingHom) Polynomial.X := by
    simp [fixedEmbedding, generic_V, toJet_v, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hV
  have hY : (((genericJetPoint a b).comp (toJet.comp fixedEmbedding)).comp C)
      (Polynomial.X (R := FX)) =
      ((seedGeneric.comp jetCoordinates.symm.toRingHom).comp C) Polynomial.X := by
    simp [fixedEmbedding, generic_Y, toJet_y, genericJetPoint, seedGeneric, generic]
  apply Polynomial.ringHom_ext' _ hY
  ext x
  simp [fixedEmbedding, generic_C, toJet_C, genericJetPoint, seedGeneric_C]
private theorem surface_height {I : Ideal Ambient} (hI : I.IsPrime) (hh : I.height = 2) :
    (surfaceOf I hI).asIdeal.height = 2 := by
  change (I.comap toJet).height = 2
  rw [toJet_equiv]
  exact (ambientToJet.symm.height_comap I).trans hh
private theorem seed_side_of_active {I : Ideal Ambient} (hI : Active I) :
    ∃ y v, K1_14_3.OnSeedFibre (surfaceOf I hI.prime) y v ∧
      IsSeparable SeedField y ∧ IsSeparable SeedField v := by
  obtain ⟨f, hf, hsep⟩ := @fibreHom mapGenericSeed _ seedMap I hI.prime
    hI.seed_finite hI.seed_size.1 hI.seed_size.2
  refine ⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), ?_, hsep _, hsep _⟩
  unfold K1_14_3.OnSeedFibre
  rw [← seed_chart, ← RingHom.comap_ker, seedPoint, hf]
  rfl
private theorem jet_side_transport {I : Ideal Ambient} (hI : I.IsPrime)
    (a b : SeedClosure) (hjker : RingHom.ker (genericJetPoint a b) = I)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) :
    ∃ g : Jet →+* JetClosure,
      g.comp fixedEmbedding = jetGeneric ∧ RingHom.ker g = (surfaceOf I hI).asIdeal ∧
      ∀ i : Fin 2, IsSeparable JetField (g (C (C (MvPolynomial.X i)))) := by
  let e := fractionCoordinates.symm
  let top : JetField →+* JetClosure := algebraMap JetField JetClosure
  let : Algebra SeedField JetClosure := (top.comp e.toRingHom).toAlgebra
  let l : SeedClosure →ₐ[SeedField] JetClosure :=
    IsAlgClosed.lift (R := SeedField) (S := SeedClosure) (M := JetClosure)
  let F := l.toRingHom.comp ((genericJetPoint a b).comp toJet)
  have hscalar (x : SeedField) :
      l (algebraMap SeedField SeedClosure x) = algebraMap JetField JetClosure (e x) := by
    exact l.commutes x
  refine ⟨F, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    change l ((genericJetPoint a b).comp (toJet.comp fixedEmbedding) x) = _
    rw [fixed_chart, RingHom.comp_apply]
    change l (algebraMap SeedField SeedClosure (algebraMap Seeds SeedField
      (jetCoordinates.symm x))) = _
    rw [hscalar]
    change top (e (algebraMap Seeds SeedField (jetCoordinates.symm x))) =
      top (algebraMap JetPlane JetField x)
    apply congrArg top
    apply fractionCoordinates.injective
    rw [RingEquiv.apply_symm_apply]
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane)
      (K := JetField) (B := Seeds) (L := SeedField) jetCoordinates.symm x).symm
  · change RingHom.ker (l.toRingHom.comp ((genericJetPoint a b).comp toJet)) = _
    rw [RingHom.ker_comp_of_injective _ l.injective, ← RingHom.comap_ker, hjker]
    rfl
  · have hs (x : SeedClosure) (hx : IsSeparable SeedField x) : IsSeparable JetField (l x) := by
      have hx' : (minpoly SeedField x).Separable := hx
      apply (hx'.map (f := e.toRingHom)).of_dvd
      apply minpoly.dvd
      rw [aeval_def, Polynomial.eval₂_map]
      change (minpoly SeedField x).eval₂ (algebraMap SeedField JetClosure) (l x) = 0
      rw [← aeval_def, aeval_algHom_apply l, minpoly.aeval, map_zero]
    intro i
    fin_cases i
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 0))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs a ha
    · change IsSeparable JetField (l ((genericJetPoint a b) (toJet (C (C (MvPolynomial.X 1))))))
      rw [toJet_seed]
      simpa [genericJetPoint] using hs b hb
theorem parent_of_dual {I : Ideal Ambient} (hI : Active I) (hh : I.height = 2) (hj : dual I) :
    Parent (surfaceOf I hI.prime) := by
  obtain ⟨g, hg, hsep⟩ := @fibreHom mapGenericJets _ jetMap I hI.prime hI.jet_finite hj hI.jet_lt
  have hker : RingHom.ker (genericJetPoint (g (MvPolynomial.X 0)) (g (MvPolynomial.X 1))) = I := by
    rw [jetPoint, hg]
  exact ⟨surface_height hI.prime hh, seed_side_of_active hI,
    jet_side_transport hI.prime _ _ hker (hsep _) (hsep _)⟩
end
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_2_1 : K1_14_2_2_7_2.c1 :=
  K1_14_2_2_7_2_1.proof
private theorem donor_2_2_1 : K1_14_2_2_7_2_2.c1 :=
  K1_14_2_2_7_2_2_1.proof
private theorem donor_2_2_2 : K1_14_2_2_7_2_2.c2 :=
  K1_14_2_2_7_2_2_2.proof
private theorem donor_2_2_3 : K1_14_2_2_7_2_2.c3 :=
  K1_14_2_2_7_2_2_3.proof
private theorem donor_2_2 : K1_14_2_2_7_2.c2 :=
  K1_14_2_2_7_2_2.of_children donor_2_2_1 donor_2_2_2 donor_2_2_3
private theorem donor_2_3 : K1_14_2_2_7_2.c3 :=
  K1_14_2_2_7_2_3.proof
private theorem donor_2_4 : K1_14_2_2_7_2.c4 :=
  K1_14_2_2_7_2_4.proof
private theorem donor_2_5 : K1_14_2_2_7_2.c5 :=
  K1_14_2_2_7_2_5.proof
theorem cut_seed_mass : K1_14_2_2_7.c2 :=
  K1_14_2_2_7_2.of_children donor_2_1 donor_2_2 donor_2_3 donor_2_4 donor_2_5
private theorem donor_3_1 : K1_14_2_2_7_3.c1 :=
  K1_14_2_2_7_3_1.proof
private theorem donor_3_2 : K1_14_2_2_7_3.c2 :=
  K1_14_2_2_7_3_2.proof
private theorem donor_3_3_1_1 : K1_14_2_2_7_3_3_1.c1 :=
  K1_14_2_2_7_3_3_1_1.proof
private theorem donor_3_3_1_2 : K1_14_2_2_7_3_3_1.c2 :=
  K1_14_2_2_7_3_3_1_2.proof
private theorem donor_3_3_1_3 : K1_14_2_2_7_3_3_1.c3 :=
  K1_14_2_2_7_3_3_1_3.proof
private theorem donor_3_3_1_4 : K1_14_2_2_7_3_3_1.c4 :=
  K1_14_2_2_7_3_3_1_4.proof
private theorem donor_3_3_1 : K1_14_2_2_7_3_3.c1 :=
  K1_14_2_2_7_3_3_1.of_children donor_3_3_1_1 donor_3_3_1_2 donor_3_3_1_3 donor_3_3_1_4
private theorem donor_3_3_2 : K1_14_2_2_7_3_3.c2 :=
  K1_14_2_2_7_3_3_2.proof
private theorem donor_3_3 : K1_14_2_2_7_3.c3 :=
  K1_14_2_2_7_3_3.of_children donor_3_3_1 donor_3_3_2
theorem cut_ordinate_mass : K1_14_2_2_7.c3 :=
  K1_14_2_2_7_3.of_children donor_3_1 donor_3_2 donor_3_3
private theorem donor_4_1 : K1_14_2_2_7_4.c1 :=
  K1_14_2_2_7_4_1.proof
private theorem donor_4_2 : K1_14_2_2_7_4.c2 :=
  K1_14_2_2_7_4_2.proof
private theorem donor_4_3 : K1_14_2_2_7_4.c3 :=
  K1_14_2_2_7_4_3.proof
private theorem donor_4_4_1 : K1_14_2_2_7_4_4.c1 :=
  K1_14_2_2_7_4_4_1.proof
private theorem donor_4_4_2 : K1_14_2_2_7_4_4.c2 :=
  K1_14_2_2_7_4_4_2.proof
private theorem donor_4_4_3 : K1_14_2_2_7_4_4.c3 :=
  K1_14_2_2_7_4_4_3.proof
private theorem donor_4_4_4 : K1_14_2_2_7_4_4.c4 :=
  K1_14_2_2_7_4_4_4.proof
private theorem donor_4_4_5 : K1_14_2_2_7_4_4.c5 :=
  K1_14_2_2_7_4_4_5.proof
private theorem donor_4_4_6 : K1_14_2_2_7_4_4.c6 :=
  K1_14_2_2_7_4_4_6.proof
private theorem donor_4_4_7_1 : K1_14_2_2_7_4_4_7.c1 :=
  K1_14_2_2_7_4_4_7_1.proof
private theorem donor_4_4_7_2 : K1_14_2_2_7_4_4_7.c2 :=
  K1_14_2_2_7_4_4_7_2.proof
private theorem donor_4_4_7 : K1_14_2_2_7_4_4.c7 :=
  K1_14_2_2_7_4_4_7.of_children donor_4_4_7_1 donor_4_4_7_2
private theorem donor_4_4_8 : K1_14_2_2_7_4_4.c8 :=
  K1_14_2_2_7_4_4_8.proof
private theorem donor_4_4 : K1_14_2_2_7_4.c4 :=
  K1_14_2_2_7_4_4.of_children
    donor_4_4_1 donor_4_4_2 donor_4_4_3 donor_4_4_4 donor_4_4_5 donor_4_4_6 donor_4_4_7 donor_4_4_8
theorem cut_constant_count : K1_14_2_2_7.c4 :=
  K1_14_2_2_7_4.of_children donor_4_1 donor_4_2 donor_4_3 donor_4_4
end P0_10R.Bridge
end
section
namespace P0_10R.Bridge
private theorem donor_1_1_1 : K1_14_2_4_1_1.c1 :=
  K1_14_2_4_1_1_1.proof
private theorem donor_1_1_2 : K1_14_2_4_1_1.c2 :=
  K1_14_2_4_1_1_2.proof
theorem donor_1_1 : K1_14_2_4_1.c1 :=
  K1_14_2_4_1_1.of_children donor_1_1_1 donor_1_1_2
private theorem donor_1_2_1 : K1_14_2_4_1_2.c1 :=
  K1_14_2_4_1_2_1.proof
private theorem donor_1_2_2 : K1_14_2_4_1_2.c2 :=
  K1_14_2_4_1_2_2.proof
theorem donor_1_2 : K1_14_2_4_1.c2 :=
  K1_14_2_4_1_2.of_children donor_1_2_1 donor_1_2_2
private theorem donor_1_3_1 : K1_14_2_4_1_3.c1 :=
  K1_14_2_4_1_3_1.proof
private theorem donor_1_3_2_1 : K1_14_2_4_1_3_2.c1 :=
  K1_14_2_4_1_3_2_1.proof
private theorem donor_1_3_2_2 : K1_14_2_4_1_3_2.c2 :=
  K1_14_2_4_1_3_2_2.proof
private theorem donor_1_3_2 : K1_14_2_4_1_3.c2 :=
  K1_14_2_4_1_3_2.of_children donor_1_3_2_1 donor_1_3_2_2
private theorem donor_1_3_3_1 : K1_14_2_4_1_3_3.c1 :=
  K1_14_2_4_1_3_3_1.proof
private theorem donor_1_3_3_2 : K1_14_2_4_1_3_3.c2 :=
  K1_14_2_4_1_3_3_2.proof
private theorem donor_1_3_3_3 : K1_14_2_4_1_3_3.c3 :=
  K1_14_2_4_1_3_3_3.proof
private theorem donor_1_3_3 : K1_14_2_4_1_3.c3 :=
  K1_14_2_4_1_3_3.of_children donor_1_3_3_1 donor_1_3_3_2 donor_1_3_3_3
theorem donor_1_3 : K1_14_2_4_1.c3 :=
  K1_14_2_4_1_3.of_children donor_1_3_1 donor_1_3_2 donor_1_3_3
private theorem donor_1_4_1 : K1_14_2_4_1_4.c1 :=
  K1_14_2_4_1_4_1.proof
private theorem donor_1_4_2 : K1_14_2_4_1_4.c2 :=
  K1_14_2_4_1_4_2.proof
private theorem donor_1_4_3 : K1_14_2_4_1_4.c3 :=
  K1_14_2_4_1_4_3.proof
theorem donor_1_4 : K1_14_2_4_1.c4 :=
  K1_14_2_4_1_4.of_children donor_1_4_1 donor_1_4_2 donor_1_4_3
private theorem donor_1_5_1 : K1_14_2_4_1_5.c1 :=
  K1_14_2_4_1_5_1.proof
private theorem donor_1_5_2 : K1_14_2_4_1_5.c2 :=
  K1_14_2_4_1_5_2.proof
theorem donor_1_5 : K1_14_2_4_1.c5 :=
  K1_14_2_4_1_5.of_children donor_1_5_1 donor_1_5_2
private theorem donor_3_1_1 : K1_14_2_4_3_1.c1 :=
  K1_14_2_4_3_1_1.proof
private theorem donor_3_1_2 : K1_14_2_4_3_1.c2 :=
  K1_14_2_4_3_1_2.proof
private theorem donor_3_1_P0_10RBridgeRootDonors : K1_14_2_4_3.c1 :=
  K1_14_2_4_3_1.of_children donor_3_1_1 donor_3_1_2
private theorem donor_3_2_1 : K1_14_2_4_3_2.c1 :=
  K1_14_2_4_3_2_1.proof
private theorem donor_3_2_2 : K1_14_2_4_3_2.c2 :=
  K1_14_2_4_3_2_2.proof
private theorem donor_3_2_P0_10RBridgeRootDonors : K1_14_2_4_3.c2 :=
  K1_14_2_4_3_2.of_children donor_3_2_1 donor_3_2_2
theorem root_embedding : K1_14_2_4.c3 :=
  K1_14_2_4_3.of_children donor_3_1_P0_10RBridgeRootDonors donor_3_2_P0_10RBridgeRootDonors
end P0_10R.Bridge
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace P0_10R_1
noncomputable section
open P0 (AnchorModel AnchoredFamily K p)
open P0_10R.Bridge (InitialCover OnParent initialCap initialE₀ initialFee)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover seed_count joinCovers joinCovers_degree joinCovers_points
  joinCovers_covers scalar_atX_injective)
open scoped BigOperators Classical
open K1_14_2_2_2_3 (jetEquiv jetEquiv_apply)
open K1_14_2_2_2_5_1 (properPair_height)
theorem section_bound : K1_14_2_2_2.c4 :=
  K1_14_2_2_2_4.of_children K1_14_2_2_2_4_1.proof K1_14_2_2_2_4_2.proof K1_14_2_2_2_4_3.proof
theorem seed_projection : K1_14_2_2_2.c6 :=
  K1_14_2_2_2_6.of_children K1_14_2_2_2_6_1.proof K1_14_2_2_2_6_2.proof
private theorem height_le {I : Ideal Ambient} (hI : I.IsPrime)
    (hdim : ringKrullDim (CoordinateRing I) = 2) : I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, hI⟩
  have hc : Order.coheight x = 2 := by
    rw [ringKrullDim_quotient] at hdim
    change Order.krullDim (Set.Ici x) = 2 at hdim
    rw [← Order.coheight_eq_krullDim_Ici] at hdim
    exact WithBot.coe_injective hdim
  have hd : ringKrullDim Ambient = 4 := by simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'
theorem component_height {P Q : Jet} {I : Ideal Ambient} (hp : ProperPair P Q)
    (hI : I.IsPrime) (hdim : ringKrullDim (CoordinateRing I) = 2)
    (hP : toJet P ∈ I) (hQ : toJet Q ∈ I) : I.height = 2 := by
  let J := I.comap K1_14_2_2_2_3.jetEquiv.toRingHom
  let : J.IsPrime := hI.comap _
  have hP' : P ∈ J := by change K1_14_2_2_2_3.jetEquiv P ∈ I; rwa [jetEquiv_apply]
  have hQ' : Q ∈ J := by change K1_14_2_2_2_3.jetEquiv Q ∈ I; rwa [jetEquiv_apply]
  exact le_antisymm (height_le hI hdim)
    ((K1_14_2_2_2_3.jetEquiv.height_comap I) ▸ properPair_height hp J hP' hQ')
theorem ordinary_cover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient),
      (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨g, a, hclear, hproper, hfCaps, hgCaps⟩ := K1_14_3_4_2.proof f hi hd hp
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hproper
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hproper
    ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
    exact ⟨hprime, hdim, component_height hproper hprime hdim hrow hcut, hfinite I hI, hrow⟩
  · intro k
    have h := hfits k
    fin_cases k <;> simpa [residualBudget, ordinaryBudget, two_mul, Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [jetAt, atMark] using hz) (K1_14_3R.chainCutter_zero hclear hz)
end
end P0_10R_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P0_10R_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open K1_14_2_2_4_1 (factor_caps natDegree_zero_of_factors dvd_of_dvd_residual toJet_equiv ambientToJet)
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)
theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩
end
end P0_10R_2
end

end Merged_PortHighFinish
