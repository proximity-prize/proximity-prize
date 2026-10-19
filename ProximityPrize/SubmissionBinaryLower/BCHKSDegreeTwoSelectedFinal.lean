import ProximityPrize.SubmissionBinaryLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionBinaryLower.BCHKSSelectedHenselData
import ProximityPrize.SubmissionBinaryLower.BCHKSSelectedNonpole
import ProximityPrize.SubmissionBinaryLower.BCHKSHenselBaseZAlignment
import ProximityPrize.SubmissionBinaryLower.BCHKSBaseZGoodFibers
import ProximityPrize.SubmissionBinaryLower.BCHKSParameters

namespace ProximityPrize.SubmissionBinaryLower
open ProximityPrize.Benchmark Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem exists_large_domain_fibers
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (T : Finset BinaryIRSProfile.Field)
    (A : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (P : T → Polynomial BinaryIRSProfile.Field)
    (dH d D q : ℕ)
    (hrow : ∀ z ∈ T, 2097152 - 613925 ≤ (A z).card)
    (hT : 5059283 * dH * d * D + 613925 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + (z : BinaryIRSProfile.Field) ^ q * U 1 i) :
    ∃ A' : Finset BinaryIRSProfile.Field, 1048576 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 1048575 + 4) * dH * d * D < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : BinaryIRSProfile.Index,
          BinaryIRSProfile.domain i = (x : BinaryIRSProfile.Field) ∧
          Polynomial.eval (x : BinaryIRSProfile.Field) (P z) =
            U 0 i + (z : BinaryIRSProfile.Field) ^ q * U 1 i := by
  classical
  let G : Finset BinaryIRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 1048575 + 4) * dH * d * D <
      (T.filter fun z => i ∈ A z).card
  have hG : 1048576 ≤ G.card := by
    simpa [G] using concrete_many_large_fibers_plus T A dH d D
      (by norm_num [BinaryIRSProfile.Index]) hrow hT
  let A' : Finset BinaryIRSProfile.Field := G.image BinaryIRSProfile.domain
  have hA' : A'.card = G.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab => BinaryIRSProfile.domain.injective hab
  let idx : A' → BinaryIRSProfile.Index := fun x => Classical.choose
    (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧ BinaryIRSProfile.domain (idx x) = (x : BinaryIRSProfile.Field) := by
    have hs := Classical.choose_spec (Finset.mem_image.mp x.property)
    exact hs
  let Fib : A' → Finset T := fun x => T.attach.filter fun z =>
    idx x ∈ A (z : BinaryIRSProfile.Field)
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 1048575 + 4) * dH * d * D <
      (T.attach.filter (fun z : T => idx x ∈ A (z : BinaryIRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : BinaryIRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : BinaryIRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA


/-- Linear bookkeeping for the leading-coefficient filter, kept free of the
large concrete constants so that `omega` never sees them. -/
theorem degree_two_card_arith (X1 X2 Tc Tg bad DZ e : ℕ)
    (h1 : X1 + e < Tc) (h2 : X2 + DZ ≤ X1) (h3 : Tg + bad = Tc) (h4 : bad ≤ DZ) :
    X2 + e < Tg := by
  omega

theorem degree_two_selected_final
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (P : BinaryIRSProfile.Field → BinaryIRSProfile.Field[X])
    (Arow : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (R : BinaryIRSProfile.Field[X][X][Y]) (H : BinaryIRSProfile.Field[X][Y])
    (T : Finset BinaryIRSProfile.Field) (x₀ : BinaryIRSProfile.Field) (Bad : Finset BinaryIRSProfile.Field)
    (q : ℕ) (hq : q ≤ 1180364)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 1048575)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0 ∧ biEval H ((P z).eval x₀) z = 0)
    (hTbad : ∀ z ∈ T, z ∉ Bad)
    (hmargin : 5059283 * 1288 * 1180364 * H.natDegree +
      (bchksErrors + 1) < T.card) (hRd : R.natDegree ≤ 1288)
    (hRi : Irreducible R) (hHi : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hHtot : Bivariate.totalDegree H ≤ 1180364)
    (hYZ : YZCap R 1180364)
    (hsimple : ∀ z ∉ Bad, ∀ y,
      Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
      Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0)
    (hrow : ∀ z ∈ T, 2097152 - 613925 ≤ (Arow z).card)
    (hagree : ∀ z ∈ T, ∀ i ∈ Arow z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) = U 0 i + z ^ q * U 1 i)
    (hRdeg : 2 ≤ R.natDegree) :
    ∃ Tgood : Finset BinaryIRSProfile.Field, Tgood ⊆ T ∧ bchksErrors + 1 < Tgood.card ∧
      ∃ p₀ p₁ : BinaryIRSProfile.Field[X], p₀.natDegree ≤ 1048575 ∧
        p₁.natDegree ≤ 1048575 ∧ ∀ z ∈ Tgood,
          P z = p₀ + Polynomial.C (z ^ q) * p₁ := by
  classical
  letI : Fact (Irreducible H) := ⟨hHi⟩
  letI : Fact (0 < H.natDegree) := ⟨hHpos⟩
  have hle : 5059283 * H.natDegree * R.natDegree * 1180364 ≤
      5059283 * 1288 * 1180364 * H.natDegree := by
    calc 5059283 * H.natDegree * R.natDegree * 1180364 =
          (5059283 * 1180364 * H.natDegree) * R.natDegree := by ring
      _ ≤ (5059283 * 1180364 * H.natDegree) * 1288 := Nat.mul_le_mul_left _ hRd
      _ = 5059283 * 1288 * 1180364 * H.natDegree := by ring
  have hT : 5059283 * H.natDegree * R.natDegree * 1180364 + 613925 + 1 ≤ T.card := by
    dsimp [bchksErrors] at hmargin
    generalize 5059283 * 1288 * 1180364 * H.natDegree = X1 at hmargin hle
    generalize 5059283 * H.natDegree * R.natDegree * 1180364 = X2 at hle ⊢
    omega
  obtain ⟨A, hA, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers U T Arow (fun z : T => P z) H.natDegree R.natDegree
      1180364 q hrow hT (fun z i hi => hagree z z.property i hi)
  let Tgood := T.filter fun z => H.leadingCoeff.eval z ≠ 0
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHi.ne_zero
  have hbadW : (T.filter fun z => H.leadingCoeff.eval z = 0).card ≤ 1180364 - H.natDegree := by
    calc
      _ ≤ H.leadingCoeff.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hWne]
        exact (Finset.mem_filter.mp hz).2
      _ ≤ H.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ H.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ 1180364 - H.natDegree := leadingCoeff_natDegree_le_of_totalDegree_le hHtot
  have hpart : Tgood.card + (T.filter fun z => H.leadingCoeff.eval z = 0).card = T.card := by
    simpa [Tgood] using Finset.filter_card_add_filter_neg_card_eq_card
      (s:=T) (p:=fun z => H.leadingCoeff.eval z ≠ 0)
  have hprod : 1180364 ≤ 5059283 * 1288 * 1180364 * H.natDegree := by
    calc 1180364 ≤ 5059283 * 1288 * 1180364 * 1 := by norm_num
      _ ≤ 5059283 * 1288 * 1180364 * H.natDegree := Nat.mul_le_mul_left _ hHpos
  have hTgood_card : bchksErrors + 1 < Tgood.card := by
    have hlarge : 1180364 + (bchksErrors + 1) < T.card :=
      lt_of_le_of_lt (Nat.add_le_add_right hprod _) hmargin
    omega
  let Fibgood : A → Finset Tgood := fun x =>
    let E : {z // z ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0} ↪ Tgood :=
      ⟨fun z => ⟨(z.1 : BinaryIRSProfile.Field), Finset.mem_filter.mpr
          ⟨z.1.property, (Finset.mem_filter.mp z.2).2⟩⟩,
        by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun w => ((w : Tgood) : BinaryIRSProfile.Field)) hab⟩
    (((Fib x).filter fun z : T => H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0).attach).map E
  have hFibgood : ∀ x : A,
      (((2 * 1048575 + 1) * Bivariate.natDegreeY R * 1180364) + q) * H.natDegree <
        (Fibgood x).card := by
    intro x
    have hc := coarse_fiber_filter_leadingCoeff_card_exact H 1180364 1048577
      R.natDegree H.natDegree rfl (by norm_num) (by omega) (by omega) hHtot
      ((Fib x).image fun z : T => (z : BinaryIRSProfile.Field)) (by
        rw [Finset.card_image_iff.mpr (fun a _ b _ hab => Subtype.ext hab)]
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hFib x)
    have hc' := hc.1
    have himage :
        (((Fib x).image fun z : T => (z : BinaryIRSProfile.Field)).filter fun z =>
          H.leadingCoeff.eval z ≠ 0) =
        (((Fib x).filter fun z : T =>
          H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0).image (fun z : T =>
            (z : BinaryIRSProfile.Field))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨w, hw, rfl⟩, hz⟩
        exact ⟨w, ⟨hw, hz⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨w, hw.1, rfl⟩, hw.2⟩
    rw [himage] at hc'
    rw [Finset.card_image_iff.mpr (fun a _ b _ hab => Subtype.ext hab)] at hc'
    dsimp [Fibgood]
    rw [Finset.card_map]
    change _ < (((Fib x).filter fun z : T => H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0).attach).card
    rw [Finset.card_attach]
    calc (((2 * 1048575 + 1) * Bivariate.natDegreeY R * 1180364) + q) * H.natDegree
        ≤ (((2 * (1048577 - 1) + 1) * R.natDegree * 1180364) + 1) * H.natDegree := by
          apply Nat.mul_le_mul_right
          unfold Bivariate.natDegreeY
          nlinarith [hRdeg, hq]
      _ < _ := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc'
  have hFibgood_mem (x : A) (z : Tgood) (hz : z ∈ Fibgood x) :
      (⟨(z : BinaryIRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ : T) ∈ Fib x := by
    dsimp [Fibgood] at hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : w.1 ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : BinaryIRSProfile.Field) ≠ 0 := by
      simpa using hw
    exact (Finset.mem_filter.mp hw').1
  have hz0 : ∃ z : Tgood, True := by
    exact ⟨⟨Classical.choose (Finset.card_pos.mp (by omega : 0 < Tgood.card)),
      Classical.choose_spec (Finset.card_pos.mp (by omega : 0 < Tgood.card))⟩, trivial⟩
  obtain ⟨z₀, -⟩ := hz0
  have hz₀T : (z₀ : BinaryIRSProfile.Field) ∈ T := (Finset.mem_filter.mp z₀.property).1
  have hz₀W : H.leadingCoeff.eval (z₀ : BinaryIRSProfile.Field) ≠ 0 :=
    (Finset.mem_filter.mp z₀.property).2
  let root₀ := rationalRootOfPair H hHpos (z₀ : BinaryIRSProfile.Field) ((P z₀).eval x₀) (by
    have hv := (hvan z₀ hz₀T).2
    exact (eval_map_eval_eq_eval_eval_C H ((P z₀).eval x₀) (z₀ : BinaryIRSProfile.Field)).symm.trans hv)
  have hx₀ := GoodAt.fieldTo𝕃 (H:=H) (z₀ : BinaryIRSProfile.Field) root₀ x₀
  have hy₀ : GoodAt (z₀ : BinaryIRSProfile.Field) root₀ (initialValue (H:=H)) ((P z₀).eval x₀) := by
    have hT : GoodAt (z₀ : BinaryIRSProfile.Field) root₀ (functionFieldT (H:=H))
        (H.leadingCoeff.eval (z₀ : BinaryIRSProfile.Field) * (P z₀).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root₀] using (piZ_mk_X_rationalRootOfPair H hHpos
          (z₀ : BinaryIRSProfile.Field) ((P z₀).eval x₀) (by
            exact (eval_map_eval_eq_eval_eval_C H ((P z₀).eval x₀)
              (z₀ : BinaryIRSProfile.Field)).symm.trans (hvan z₀ hz₀T).2)).symm
    have hWgood := GoodAt.liftToFunctionField (H:=H) (z₀ : BinaryIRSProfile.Field) root₀ H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ hz₀W] using
      GoodAt.div hT hWgood hz₀W
  have hslope_eval (z x y : BinaryIRSProfile.Field) :
      FiniteHensel.ySlope (triSpecializeZ R z) x y =
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x) z) := by
    simp only [FiniteHensel.ySlope, triSpecializeZ, triSpecializeX, biSpecializeZ,
      Polynomial.derivative_map]
    induction Polynomial.derivative R using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a =>
      simp [eval_map_eval_eq_eval_eval_C]
  have hs₀ : FiniteHensel.ySlope (triSpecializeZ R (z₀ : BinaryIRSProfile.Field)) x₀
      ((P z₀).eval x₀) ≠ 0 := by
    rw [hslope_eval]
    exact hsimple z₀ (hTbad z₀ (Finset.mem_filter.mp z₀.property).1) ((P z₀).eval x₀) (by
        exact (eval_triEval_eq_biEval_triSpecializeX R (P z₀) x₀
          (z₀ : BinaryIRSProfile.Field)).symm.trans
            (by simpa using (congrArg (fun q => q.eval x₀) (hvan z₀ hz₀T).1)))
  have hzeta := zeta_ne_zero_of_selected_slope x₀ R (z₀ : BinaryIRSProfile.Field) root₀ x₀
    ((P z₀).eval x₀) hx₀ hy₀ hs₀
  let PT : Tgood → BinaryIRSProfile.Field[X] := fun z => P z
  have hfactor : ∀ z : Tgood, Polynomial.evalEval (z : BinaryIRSProfile.Field)
      ((PT z).eval x₀) H = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C H ((P z).eval x₀)
      (z : BinaryIRSProfile.Field)).symm.trans
        (hvan z (Finset.mem_filter.mp z.property).1).2
  have hExact : ∀ z : Tgood, (triSpecializeZ R (z : BinaryIRSProfile.Field)).eval (PT z) = 0 := by
    intro z
    simpa [PT, triEval_eq_eval_triSpecializeZ] using
      (hvan z (Finset.mem_filter.mp z.property).1).1
  let root : ∀ z : Tgood, rationalRoot (monicize H) (z : BinaryIRSProfile.Field) := fun z =>
    rationalRootOfPair H hHpos (z : BinaryIRSProfile.Field) ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : Tgood, GoodAt (z : BinaryIRSProfile.Field) (root z)
      (fieldTo𝕃 (H:=H) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H:=H) (z : BinaryIRSProfile.Field) (root z) x₀
  have hy : ∀ z : Tgood, GoodAt (z : BinaryIRSProfile.Field) (root z)
      (initialValue (H:=H)) ((PT z).eval x₀) := by
    intro z
    have hT : GoodAt (z : BinaryIRSProfile.Field) (root z) (functionFieldT (H:=H))
        (H.leadingCoeff.eval (z : BinaryIRSProfile.Field) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using (piZ_mk_X_rationalRootOfPair H hHpos
          (z : BinaryIRSProfile.Field) ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H:=H) (z : BinaryIRSProfile.Field) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (Finset.mem_filter.mp z.property).2] using
      GoodAt.div hT hWgood (Finset.mem_filter.mp z.property).2
  have hsimp : ∀ z : Tgood, FiniteHensel.ySlope
      (triSpecializeZ R (z : BinaryIRSProfile.Field)) x₀ ((PT z).eval x₀) ≠ 0 := by
    intro z
    rw [hslope_eval]
    exact hsimple z (hTbad z (Finset.mem_filter.mp z.property).1) ((P z).eval x₀) (by
        exact (eval_triEval_eq_biEval_triSpecializeX R (P z) x₀
          (z : BinaryIRSProfile.Field)).symm.trans
            (by simpa using (congrArg (fun q => q.eval x₀)
              (hvan z (Finset.mem_filter.mp z.property).1).1)))
  have hNP : ∀ z : Tgood, SelectedNonpoleData x₀ R H hHyp (z : BinaryIRSProfile.Field)
      (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ R hHyp hzeta (z : BinaryIRSProfile.Field) (root z) x₀
      ((PT z).eval x₀) (hx z) (hy z) (Finset.mem_filter.mp z.property).2 (hsimp z)
  have hRdegY : 2 ≤ Bivariate.natDegreeY R := by
    exact hRdeg
  have hRdegYle : Bivariate.natDegreeY R ≤ R.natDegree := by
    exact le_rfl
  let S := selectedHenselData_of_pair x₀ R hHyp hzeta 1180364 R.natDegree 1048575
    1048576 Tgood PT hfactor hExact hsimp (hNP z₀).hsL
    (fun z => (hNP z).hslope) (fun z => (Finset.mem_filter.mp z.property).2)
    (fun z => by simpa [root] using (hNP z).hxi)
    (fun _ _ _ z => by simpa [root] using (hNP z).hden _)
    hHtot hYZ hRdegY hRdegYle
  have hcard : 2 * 1048576 * H.natDegree * R.natDegree * 1180364 +
      (bchksErrors - 1180364) + 1 < Tgood.card := by
    have hle2 : 2 * 1048576 * H.natDegree * R.natDegree * 1180364 + 1180364 ≤
        5059283 * 1288 * 1180364 * H.natDegree := by
      have h1 : 2 * 1048576 * H.natDegree * R.natDegree * 1180364 ≤
          2 * 1048576 * 1288 * 1180364 * H.natDegree := by
        calc 2 * 1048576 * H.natDegree * R.natDegree * 1180364 =
              (2 * 1048576 * 1180364 * H.natDegree) * R.natDegree := by ring
          _ ≤ (2 * 1048576 * 1180364 * H.natDegree) * 1288 := Nat.mul_le_mul_left _ hRd
          _ = 2 * 1048576 * 1288 * 1180364 * H.natDegree := by ring
      have h2 : 1180364 ≤ 2962131 * 1288 * 1180364 * H.natDegree := by
        calc 1180364 ≤ 2962131 * 1288 * 1180364 * 1 := by norm_num
          _ ≤ 2962131 * 1288 * 1180364 * H.natDegree := Nat.mul_le_mul_left _ hHpos
      have h3 : 5059283 * 1288 * 1180364 * H.natDegree =
          2 * 1048576 * 1288 * 1180364 * H.natDegree +
            2962131 * 1288 * 1180364 * H.natDegree := by ring
      generalize 5059283 * 1288 * 1180364 * H.natDegree = Y1 at h3 ⊢
      generalize 2 * 1048576 * 1288 * 1180364 * H.natDegree = Y2 at h3 h1
      generalize 2962131 * 1288 * 1180364 * H.natDegree = Y3 at h3 h2
      generalize 2 * 1048576 * H.natDegree * R.natDegree * 1180364 = Y4 at h1 ⊢
      omega
    have hbad' : (T.filter fun z => H.leadingCoeff.eval z = 0).card ≤ 1180364 :=
      hbadW.trans (Nat.sub_le _ _)
    have he : bchksErrors - 1180364 = 0 := by norm_num [bchksErrors]
    rw [he, Nat.add_zero]
    have key := degree_two_card_arith _ _ _ _ _ _ _ hmargin hle2 hpart hbad'
    exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left 1 bchksErrors) _) key
  have hPdegT : ∀ z : Tgood, (PT z).natDegree ≤ 1048575 := by
    intro z
    exact hPdeg z (Finset.mem_filter.mp z.property).1
  have hne : ∀ x : A, (Fib x).Nonempty := fun x =>
    Finset.card_pos.mp (Nat.zero_lt_of_lt (hFib x))
  let zpick : ∀ x : A, T := fun x => Classical.choose (hne x)
  have hzpick (x : A) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : A → BinaryIRSProfile.Index := fun x =>
    Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : A) : BinaryIRSProfile.domain (idx x) = (x : BinaryIRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀ : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hx : x ∈ A then U 0 (idx ⟨x, hx⟩) else 0
  let U₁ : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hx : x ∈ A then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : A, ∀ z ∈ Fibgood x,
      (PT z).eval (x : BinaryIRSProfile.Field) = U₀ x + (z : BinaryIRSProfile.Field) ^ q * U₁ x := by
    intro x z hz
    have hzFib := hFibgood_mem x z hz
    obtain ⟨i, hi, he⟩ := hinc x
      ⟨(z : BinaryIRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ hzFib
    have hii : i = idx x := BinaryIRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [PT, U₀, U₁, x.property] using he
  obtain ⟨_, p₀, p₁, hp₀, hp₁, hp⟩ := hensel_baseZ_alignment_final_exact_yz
    x₀ R hHyp hzeta 1180364 R.natDegree 1048575 1048576 (bchksErrors - 1180364) q
    (by norm_num) hHtot hYZ hRdegY Tgood S.root PT hPdegT S.hx S.hy S.hsL
    S.hsimple S.hExact S.hslope S.hW S.hxi (fun t _ z => (hNP z).hden t)
    S.hweight hcard (by norm_num [BinaryIRSProfile.Field]) A (by simpa using hA) U₀ U₁
    Fibgood hFibgood halign
  exact ⟨Tgood, Finset.filter_subset _ _, hTgood_card, p₀, p₁, hp₀, hp₁,
    fun z hz => hp ⟨z, hz⟩⟩

end ProximityPrize.SubmissionBinaryLower
