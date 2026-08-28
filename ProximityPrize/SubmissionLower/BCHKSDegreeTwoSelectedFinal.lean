import ProximityPrize.SubmissionLower.BCHKSDoubleCounting
import ProximityPrize.SubmissionLower.BCHKSSelectedHenselData
import ProximityPrize.SubmissionLower.BCHKSSelectedNonpole
import ProximityPrize.SubmissionLower.BCHKSHenselBaseZAlignment
import ProximityPrize.SubmissionLower.BCHKSBaseZGoodFibers
import ProximityPrize.SubmissionLower.BCHKSParameters

namespace ProximityPrize.SubmissionLower
open ProximityPrize.Benchmark Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem exists_large_domain_fibers
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : T → Polynomial IRSProfile.Field)
    (dH d D : ℕ)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 2 * 111624646 * dH * d * D + 76721 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + (z : IRSProfile.Field) * U 1 i) :
    ∃ A' : Finset IRSProfile.Field, 131072 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 131071 + 2) * dH * d * D < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : IRSProfile.Index,
          IRSProfile.domain i = (x : IRSProfile.Field) ∧
          Polynomial.eval (x : IRSProfile.Field) (P z) =
            U 0 i + (z : IRSProfile.Field) * U 1 i := by
  classical
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 131071 + 2) * dH * d * D <
      (T.filter fun z => i ∈ A z).card
  have hG : 131072 ≤ G.card := by
    simpa [G] using concrete_many_large_fibers_plus T A dH d D
      (by norm_num [IRSProfile.Index]) hrow hT
  let A' : Finset IRSProfile.Field := G.image IRSProfile.domain
  have hA' : A'.card = G.card := by
    exact Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
  let idx : A' → IRSProfile.Index := fun x => Classical.choose
    (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧ IRSProfile.domain (idx x) = (x : IRSProfile.Field) := by
    have hs := Classical.choose_spec (Finset.mem_image.mp x.property)
    exact hs
  let Fib : A' → Finset T := fun x => T.attach.filter fun z =>
    idx x ∈ A (z : IRSProfile.Field)
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 131071 + 2) * dH * d * D <
      (T.attach.filter (fun z : T => idx x ∈ A (z : IRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : IRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : IRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA

/-- The same coordinate extractor with the exact 63.94 incidence budget. -/
theorem exists_large_domain_fibers_6394
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (P : T → Polynomial IRSProfile.Field)
    (dH d D : Nat)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (A z).card)
    (hT : 632176 * dH * d * D + 76721 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ A z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + (z : IRSProfile.Field) * U 1 i) :
    ∃ A' : Finset IRSProfile.Field, 131072 ≤ A'.card ∧
      ∃ Fib : A' → Finset T,
        (∀ x : A', (2 * 131071 + 2) * dH * d * D < (Fib x).card) ∧
        ∀ x : A', ∀ z ∈ Fib x, ∃ i : IRSProfile.Index,
          IRSProfile.domain i = (x : IRSProfile.Field) ∧
          Polynomial.eval (x : IRSProfile.Field) (P z) =
            U 0 i + (z : IRSProfile.Field) * U 1 i := by
  classical
  let G : Finset IRSProfile.Index := Finset.univ.filter fun i =>
    (2 * 131071 + 2) * dH * d * D < (T.filter fun z => i ∈ A z).card
  have hG : 131072 ≤ G.card := by
    simpa [G] using many_large_fibers_6394 T A dH d D
      (by norm_num [IRSProfile.Index]) hrow hT
  let A' : Finset IRSProfile.Field := G.image IRSProfile.domain
  have hA' : A'.card = G.card :=
    Finset.card_image_iff.mpr fun a _ b _ hab => IRSProfile.domain.injective hab
  let idx : A' → IRSProfile.Index := fun x =>
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : A') : idx x ∈ G ∧ IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let Fib : A' → Finset T := fun x => T.attach.filter fun z => idx x ∈ A z
  refine ⟨A', by simpa [hA'] using hG, Fib, ?_, ?_⟩
  · intro x
    have hx := (Finset.mem_filter.mp (hidx x).1).2
    change (2 * 131071 + 2) * dH * d * D <
      (T.attach.filter (fun z : T => idx x ∈ A (z : IRSProfile.Field))).card
    rw [Finset.filter_attach (fun z : IRSProfile.Field => idx x ∈ A z) T,
      Finset.card_map, Finset.card_attach]
    exact hx
  · intro x z hz
    have hzA : idx x ∈ A (z : IRSProfile.Field) := by
      simpa [Fib] using (Finset.mem_filter.mp hz).2
    refine ⟨idx x, (hidx x).2, ?_⟩
    rw [← (hidx x).2]
    exact hagree z (idx x) hzA


theorem degree_ge_two_selected_adapter
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    {H : IRSProfile.Field[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : IRSProfile.Field) (R : IRSProfile.Field[X][X][Y])
    (hHyp : RationalFunctions.HenselNumerators.Hypotheses x₀ R H)
    (hzeta : RationalFunctions.HenselNumerators.zeta R x₀ H ≠ 0)
    (D d k DX e : ℕ) (hkDX : k < DX)
    (hHD : Polynomial.Bivariate.totalDegree H ≤ D)
    (hRD : YZCap R D)
    (hRdeg : 2 ≤ Polynomial.Bivariate.natDegreeY R)
    (hd : Polynomial.Bivariate.natDegreeY R ≤ d)
    (T : Finset IRSProfile.Field) (P : T → Polynomial IRSProfile.Field)
    (S : SelectedHenselData x₀ R H hHyp hzeta D d k DX T P)
    (hNP : ∀ z : T, SelectedNonpoleData x₀ R H hHyp (z : IRSProfile.Field)
      (S.root z) x₀ ((P z).eval x₀))
    (hPdeg : ∀ z, (P z).natDegree ≤ k)
    (hcard : 2*DX*H.natDegree*d*D + e + 1 < T.card)
    (hkF : k < Fintype.card IRSProfile.Field)
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (Arow z).card)
    (hT : 2 * 111624646 * H.natDegree * d * D + 76721 + 1 ≤ T.card)
    (hagree : ∀ z : T, ∀ i ∈ Arow z,
      Polynomial.eval (IRSProfile.domain i) (P z) =
        U 0 i + (z : IRSProfile.Field) * U 1 i)
    (hk : k = 131071) :
    (∀ t, k < t → t < DX →
      finiteAlpha (R:=R) (H:=H) x₀ DX t = 0) ∧
    ∃ p₀ p₁ : IRSProfile.Field[X], p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z : T, P z = p₀ + Polynomial.C (z : IRSProfile.Field) * p₁ := by
  classical
  obtain ⟨A, hA, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers U T Arow P H.natDegree d D hrow hT hagree
  have hne : ∀ x : A, (Fib x).Nonempty := by
    intro x
    exact Finset.card_pos.mp (Nat.zero_lt_of_lt (hFib x))
  let zpick : ∀ x : A, T := fun x => Classical.choose (hne x)
  have hzpick (x : A) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : A → IRSProfile.Index := fun x => Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : A) : IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 0 (idx ⟨x, hx⟩) else 0
  let U₁ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : A, ∀ z ∈ Fib x,
      (P z).eval (x : IRSProfile.Field) = U₀ x + (z : IRSProfile.Field) * U₁ x := by
    intro x z hz
    obtain ⟨i, hi, he⟩ := hinc x z hz
    have hii : i = idx x := IRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [U₀, U₁, x.property] using he
  exact hensel_baseZ_alignment_final x₀ R hHyp hzeta D d k DX e hkDX hHD hRD hRdeg
    T S.root P hPdeg S.hx S.hy S.hsL S.hsimple S.hExact S.hslope S.hW S.hxi
    (fun t _ z => (hNP z).hden t) S.hweight hcard hkF A (by simpa [hk] using hA)
    U₀ U₁ Fib (by
      intro x
      calc
        (2*k+2) * Bivariate.natDegreeY R * D * H.natDegree ≤
            (2*k+2) * d * D * H.natDegree := by gcongr
        _ < (Fib x).card := by
          simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hFib x) halign


theorem degree_two_selected_final
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → IRSProfile.Field[X])
    (Arow : IRSProfile.Field → Finset IRSProfile.Index)
    (R : IRSProfile.Field[X][X][Y]) (H : IRSProfile.Field[X][Y])
    (T : Finset IRSProfile.Field) (x₀ : IRSProfile.Field) (Bad : Finset IRSProfile.Field)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0 ∧ biEval H ((P z).eval x₀) z = 0)
    (hTbad : ∀ z ∈ T, z ∉ Bad)
    (hmargin : 632176 * 519142 * R.natDegree * H.natDegree +
      (bchksErrors + 1) < T.card)
    (hRi : Irreducible R) (hHi : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hHtot : Bivariate.totalDegree H ≤ 519142)
    (hYZ : YZCap R 519142)
    (hsimple : ∀ z ∉ Bad, ∀ y,
      Polynomial.eval y (biSpecializeZ (triSpecializeX R x₀) z) = 0 →
      Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x₀) z) ≠ 0)
    (hrow : ∀ z ∈ T, 262144 - 76721 ≤ (Arow z).card)
    (hagree : ∀ z ∈ T, ∀ i ∈ Arow z,
      Polynomial.eval (IRSProfile.domain i) (P z) = U 0 i + z * U 1 i)
    (hRdeg : 2 ≤ R.natDegree) :
    ∃ Tgood : Finset IRSProfile.Field, Tgood ⊆ T ∧ bchksErrors + 1 < Tgood.card ∧
      ∃ p₀ p₁ : IRSProfile.Field[X], p₀.natDegree ≤ 131071 ∧
        p₁.natDegree ≤ 131071 ∧ ∀ z ∈ Tgood,
          P z = p₀ + Polynomial.C z * p₁ := by
  classical
  letI : Fact (Irreducible H) := ⟨hHi⟩
  letI : Fact (0 < H.natDegree) := ⟨hHpos⟩
  have hT : 632176 * H.natDegree * R.natDegree * 519142 + 76721 + 1 ≤ T.card := by
    dsimp [bchksErrors] at hmargin
    ring_nf at hmargin ⊢
    omega
  obtain ⟨A, hA, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers_6394 U T Arow (fun z : T => P z) H.natDegree R.natDegree
      519142 hrow hT (fun z i hi => hagree z z.property i hi)
  let Tgood := T.filter fun z => H.leadingCoeff.eval z ≠ 0
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHi.ne_zero
  have hbadW : (T.filter fun z => H.leadingCoeff.eval z = 0).card ≤ 519142 - H.natDegree := by
    calc
      _ ≤ H.leadingCoeff.roots.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hWne]
        exact (Finset.mem_filter.mp hz).2
      _ ≤ H.leadingCoeff.roots.card := Multiset.toFinset_card_le _
      _ ≤ H.leadingCoeff.natDegree := Polynomial.card_roots' _
      _ ≤ 519142 - H.natDegree := leadingCoeff_natDegree_le_of_totalDegree_le hHtot
  have hpart : Tgood.card + (T.filter fun z => H.leadingCoeff.eval z = 0).card = T.card := by
    simpa [Tgood] using Finset.filter_card_add_filter_neg_card_eq_card
      (s:=T) (p:=fun z => H.leadingCoeff.eval z ≠ 0)
  have hprod : 519142 ≤ 632176 * 519142 * R.natDegree * H.natDegree := by
    nlinarith
  have hTgood_card : bchksErrors + 1 < Tgood.card := by
    have hlarge : 519142 + (76721 + 1) < T.card :=
      lt_of_le_of_lt (Nat.add_le_add_right hprod _) hmargin
    dsimp [bchksErrors]
    omega
  let Fibgood : A → Finset Tgood := fun x =>
    let E : {z // z ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0} ↪ Tgood :=
      ⟨fun z => ⟨(z.1 : IRSProfile.Field), Finset.mem_filter.mpr
          ⟨z.1.property, (Finset.mem_filter.mp z.2).2⟩⟩,
        by
          intro a b hab
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun w => ((w : Tgood) : IRSProfile.Field)) hab⟩
    (((Fib x).filter fun z : T => H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).attach).map E
  have hFibgood : ∀ x : A,
      (((2 * 131071 + 1) * Bivariate.natDegreeY R * 519142) + 1) * H.natDegree <
        (Fibgood x).card := by
    intro x
    have hc := coarse_fiber_filter_leadingCoeff_card_exact H 519142 131072
      R.natDegree H.natDegree rfl (by norm_num) (by omega) (by omega) hHtot
      ((Fib x).image fun z : T => (z : IRSProfile.Field)) (by
        rw [Finset.card_image_iff.mpr (fun a _ b _ hab => Subtype.ext hab)]
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hFib x)
    have hc' := hc.1
    have himage :
        (((Fib x).image fun z : T => (z : IRSProfile.Field)).filter fun z =>
          H.leadingCoeff.eval z ≠ 0) =
        (((Fib x).filter fun z : T =>
          H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).image (fun z : T =>
            (z : IRSProfile.Field))) := by
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
    change _ < (((Fib x).filter fun z : T => H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0).attach).card
    rw [Finset.card_attach]
    simpa [Bivariate.natDegreeY, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc' 
  have hFibgood_mem (x : A) (z : Tgood) (hz : z ∈ Fibgood x) :
      (⟨(z : IRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ : T) ∈ Fib x := by
    dsimp [Fibgood] at hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : w.1 ∈ (Fib x).filter fun z : T =>
        H.leadingCoeff.eval (z : IRSProfile.Field) ≠ 0 := by
      simpa using hw
    exact (Finset.mem_filter.mp hw').1
  have hz0 : ∃ z : Tgood, True := by
    exact ⟨⟨Classical.choose (Finset.card_pos.mp (by omega : 0 < Tgood.card)),
      Classical.choose_spec (Finset.card_pos.mp (by omega : 0 < Tgood.card))⟩, trivial⟩
  obtain ⟨z₀, -⟩ := hz0
  have hz₀T : (z₀ : IRSProfile.Field) ∈ T := (Finset.mem_filter.mp z₀.property).1
  have hz₀W : H.leadingCoeff.eval (z₀ : IRSProfile.Field) ≠ 0 :=
    (Finset.mem_filter.mp z₀.property).2
  let root₀ := rationalRootOfPair H hHpos (z₀ : IRSProfile.Field) ((P z₀).eval x₀) (by
    have hv := (hvan z₀ hz₀T).2
    exact (eval_map_eval_eq_eval_eval_C H ((P z₀).eval x₀) (z₀ : IRSProfile.Field)).symm.trans hv)
  have hx₀ := GoodAt.fieldTo𝕃 (H:=H) (z₀ : IRSProfile.Field) root₀ x₀
  have hy₀ : GoodAt (z₀ : IRSProfile.Field) root₀ (initialValue (H:=H)) ((P z₀).eval x₀) := by
    have hT : GoodAt (z₀ : IRSProfile.Field) root₀ (functionFieldT (H:=H))
        (H.leadingCoeff.eval (z₀ : IRSProfile.Field) * (P z₀).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root₀] using (piZ_mk_X_rationalRootOfPair H hHpos
          (z₀ : IRSProfile.Field) ((P z₀).eval x₀) (by
            exact (eval_map_eval_eq_eval_eval_C H ((P z₀).eval x₀)
              (z₀ : IRSProfile.Field)).symm.trans (hvan z₀ hz₀T).2)).symm
    have hWgood := GoodAt.liftToFunctionField (H:=H) (z₀ : IRSProfile.Field) root₀ H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ hz₀W] using
      GoodAt.div hT hWgood hz₀W
  have hslope_eval (z x y : IRSProfile.Field) :
      FiniteHensel.ySlope (triSpecializeZ R z) x y =
        Polynomial.eval y (biSpecializeZ (triSpecializeX R.derivative x) z) := by
    simp only [FiniteHensel.ySlope, triSpecializeZ, triSpecializeX, biSpecializeZ,
      Polynomial.derivative_map]
    induction Polynomial.derivative R using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a =>
      simp [eval_map_eval_eq_eval_eval_C]
  have hs₀ : FiniteHensel.ySlope (triSpecializeZ R (z₀ : IRSProfile.Field)) x₀
      ((P z₀).eval x₀) ≠ 0 := by
    rw [hslope_eval]
    exact hsimple z₀ (hTbad z₀ (Finset.mem_filter.mp z₀.property).1) ((P z₀).eval x₀) (by
        exact (eval_triEval_eq_biEval_triSpecializeX R (P z₀) x₀
          (z₀ : IRSProfile.Field)).symm.trans
            (by simpa using (congrArg (fun q => q.eval x₀) (hvan z₀ hz₀T).1)))
  have hzeta := zeta_ne_zero_of_selected_slope x₀ R (z₀ : IRSProfile.Field) root₀ x₀
    ((P z₀).eval x₀) hx₀ hy₀ hs₀
  let PT : Tgood → IRSProfile.Field[X] := fun z => P z
  have hfactor : ∀ z : Tgood, Polynomial.evalEval (z : IRSProfile.Field)
      ((PT z).eval x₀) H = 0 := by
    intro z
    exact (eval_map_eval_eq_eval_eval_C H ((P z).eval x₀)
      (z : IRSProfile.Field)).symm.trans
        (hvan z (Finset.mem_filter.mp z.property).1).2
  have hExact : ∀ z : Tgood, (triSpecializeZ R (z : IRSProfile.Field)).eval (PT z) = 0 := by
    intro z
    simpa [PT, triEval_eq_eval_triSpecializeZ] using
      (hvan z (Finset.mem_filter.mp z.property).1).1
  let root : ∀ z : Tgood, rationalRoot (monicize H) (z : IRSProfile.Field) := fun z =>
    rationalRootOfPair H hHpos (z : IRSProfile.Field) ((PT z).eval x₀) (hfactor z)
  have hx : ∀ z : Tgood, GoodAt (z : IRSProfile.Field) (root z)
      (fieldTo𝕃 (H:=H) x₀) x₀ := fun z =>
    GoodAt.fieldTo𝕃 (H:=H) (z : IRSProfile.Field) (root z) x₀
  have hy : ∀ z : Tgood, GoodAt (z : IRSProfile.Field) (root z)
      (initialValue (H:=H)) ((PT z).eval x₀) := by
    intro z
    have hT : GoodAt (z : IRSProfile.Field) (root z) (functionFieldT (H:=H))
        (H.leadingCoeff.eval (z : IRSProfile.Field) * (PT z).eval x₀) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) Polynomial.X, 1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using (piZ_mk_X_rationalRootOfPair H hHpos
          (z : IRSProfile.Field) ((PT z).eval x₀) (hfactor z)).symm
    have hWgood := GoodAt.liftToFunctionField (H:=H) (z : IRSProfile.Field) (root z) H.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ (Finset.mem_filter.mp z.property).2] using
      GoodAt.div hT hWgood (Finset.mem_filter.mp z.property).2
  have hsimp : ∀ z : Tgood, FiniteHensel.ySlope
      (triSpecializeZ R (z : IRSProfile.Field)) x₀ ((PT z).eval x₀) ≠ 0 := by
    intro z
    rw [hslope_eval]
    exact hsimple z (hTbad z (Finset.mem_filter.mp z.property).1) ((P z).eval x₀) (by
        exact (eval_triEval_eq_biEval_triSpecializeX R (P z) x₀
          (z : IRSProfile.Field)).symm.trans
            (by simpa using (congrArg (fun q => q.eval x₀)
              (hvan z (Finset.mem_filter.mp z.property).1).1)))
  have hNP : ∀ z : Tgood, SelectedNonpoleData x₀ R H hHyp (z : IRSProfile.Field)
      (root z) x₀ ((PT z).eval x₀) := by
    intro z
    exact selectedNonpoleData x₀ R hHyp hzeta (z : IRSProfile.Field) (root z) x₀
      ((PT z).eval x₀) (hx z) (hy z) (Finset.mem_filter.mp z.property).2 (hsimp z)
  have hRdegY : 2 ≤ Bivariate.natDegreeY R := by
    exact hRdeg
  have hRdegYle : Bivariate.natDegreeY R ≤ R.natDegree := by
    exact le_rfl
  let S := selectedHenselData_of_pair x₀ R hHyp hzeta 519142 R.natDegree 131071
    131072 Tgood PT hfactor hExact hsimp (hNP z₀).hsL
    (fun z => (hNP z).hslope) (fun z => (Finset.mem_filter.mp z.property).2)
    (fun z => by simpa [root] using (hNP z).hxi)
    (fun _ _ _ z => by simpa [root] using (hNP z).hden _)
    hHtot hYZ hRdegY hRdegYle
  have hcard : 2 * 131072 * H.natDegree * R.natDegree * 519142 +
      (bchksErrors - 519142) + 1 < Tgood.card := by
    dsimp [bchksErrors] at *
    ring_nf at hmargin ⊢
    omega
  have hPdegT : ∀ z : Tgood, (PT z).natDegree ≤ 131071 := by
    intro z
    exact hPdeg z (Finset.mem_filter.mp z.property).1
  have hne : ∀ x : A, (Fib x).Nonempty := fun x =>
    Finset.card_pos.mp (Nat.zero_lt_of_lt (hFib x))
  let zpick : ∀ x : A, T := fun x => Classical.choose (hne x)
  have hzpick (x : A) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : A → IRSProfile.Index := fun x =>
    Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : A) : IRSProfile.domain (idx x) = (x : IRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 0 (idx ⟨x, hx⟩) else 0
  let U₁ : IRSProfile.Field → IRSProfile.Field := fun x =>
    if hx : x ∈ A then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : A, ∀ z ∈ Fibgood x,
      (PT z).eval (x : IRSProfile.Field) = U₀ x + (z : IRSProfile.Field) * U₁ x := by
    intro x z hz
    have hzFib := hFibgood_mem x z hz
    obtain ⟨i, hi, he⟩ := hinc x
      ⟨(z : IRSProfile.Field), (Finset.mem_filter.mp z.property).1⟩ hzFib
    have hii : i = idx x := IRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [PT, U₀, U₁, x.property] using he
  obtain ⟨_, p₀, p₁, hp₀, hp₁, hp⟩ := hensel_baseZ_alignment_final_exact_yz
    x₀ R hHyp hzeta 519142 R.natDegree 131071 131072 (bchksErrors - 519142)
    (by norm_num) hHtot hYZ hRdegY Tgood S.root PT hPdegT S.hx S.hy S.hsL
    S.hsimple S.hExact S.hslope S.hW S.hxi (fun t _ z => (hNP z).hden t)
    S.hweight hcard (by norm_num [IRSProfile.Field]) A (by simpa using hA) U₀ U₁
    Fibgood hFibgood halign
  exact ⟨Tgood, Finset.filter_subset _ _, hTgood_card, p₀, p₁, hp₀, hp₁,
    fun z hz => hp ⟨z, hz⟩⟩

end ProximityPrize.SubmissionLower
