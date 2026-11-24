import ProximityPrize.SubmissionLower.R6961RetainedCompressionCut

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000

namespace Lower6961.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L liftPoly Equation atMark)
open Lower6961.RescueGeometry (Model Family)
open RetainedShortening (Word)
open CurvatureSquares (Ordinate ordEval xView zView)
open KoalaRect (axisDegree)
open scoped Polynomial
open CurvatureSquares (degree_two_count)

def FactorPriceAt (B : MarkedBand) (rate : ℕ → ℕ) : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179818 B.wordDegree M.word F.scalar T →
    ∀ f : Curve (Polynomial L), Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<B.maxOrd → 0<f.degreeOf parameter →
      height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)

private theorem word_roots {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ)
    (Q : Ordinate) (H : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    ∀ γ∈U, ordEval (scalar M γ) ((F.scalar γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (scalar M γ))) (liftPoly (F.scalar γ))=0
  rw [← eval_map]
  exact (H γ hγ).root

private theorem factor_price (B : MarkedBand) (rate : ℕ → ℕ) (mono : Monotone rate) (small : 24≤rate 3)
    (proper : ∀ e, 3≤e → e<B.maxOrd → 12*e≤rate e) (bounded : FactorPriceAt B rate)
    {u deleted} {M : Model u deleted} {Γ U : Finset K} (F : Family M Γ) (sub : U⊆Γ)
    (words : Word 179818 B.wordDegree M.word F.scalar U)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : n<B.maxOrd)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈U, MarkedFiber Q (scalar M γ) (liftPoly (F.scalar γ))) :
    U.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases U.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 24≤rate n := small.trans (mono lo)
  have vRate : 18≤rate n := (by decide : 18≤24).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn (scalar M) (U : Set K) := (scalar_injective M).injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (F.scalar x)) (U:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q U (scalar M) (fun x=>liftPoly (F.scalar x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots F Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) (scalar M) inj
      B.lt_A B.vote_scale Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e B.wordDegree < height B.wordDegree q
  · let parameter (j : U) := scalar M j.val
    let root (j : U) := liftPoly (F.scalar j.val)
    have d (j : U) : (root j).natDegree≤B.wordDegree := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : U) : evaluate (parameter j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape parameter root B.wordDegree B.pos_d B.dvd4 d q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price U (scalar M) (fun w=>liftPoly (F.scalar w))
      inj q G qp nondiv pos y z gy gz (fun γ hγ=>rootsF ⟨γ,hγ⟩)
      (fun γ hγ=>rootsG ⟨γ,hγ⟩)
    have ceiling : 12*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using tRate
      have three : 3≤e := by omega
      exact (proper e three (degree.trans_lt hi)).trans (mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q B.wordDegree
        rw [RingEquiv.apply_symm_apply] at a
        exact (Nat.mul_le_mul_left 2 (a.trans wt)).trans_lt (by rw [two]; exact B.deg2_tame)
      have count := degree_two_count words (algebraMap K L) (scalar M) inj
        B.lt_A B.vote_scale Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have charge := bounded F U sub words q qp three (y.symm ▸ degree.trans_lt hi)
      (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt)
      (fun γ hγ => by simpa only [q,RingEquiv.apply_symm_apply] using mark γ hγ)
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))

theorem retained_of_tariff (B : MarkedBand) (hMax axesCap retainedCap : ℕ)
    (witnessBound : ℕ → ℕ)
    (haxesSmall : axesCap < p) (hdegFit : 131071 + hMax ≤ B.wordDegree)
    (rate : ℕ → ℕ) (mono : Monotone rate) (small : 24≤rate 3)
    (proper : ∀ e, 3≤e → e<B.maxOrd → 12*e≤rate e)
    (paid : ∀ e a b, 3≤e → e<B.maxOrd → a+b≤axesCap → b<witnessBound e →
      rate e*(a+p*b)+(e-1)*e≤retainedCap)
    (bounded : FactorPriceAt B rate)
    {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat ≤ hMax) (T : Finset K) (f : Equation) (sub : T⊆Γ)
    (emin : 3≤f.natDegree) (emax : f.natDegree<B.maxOrd)
    (axes : axisDegree f 0+axisDegree f 1≤axesCap)
    (graded : ∀ j : Fin 2, axisDegree f j < witnessBound f.natDegree)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    T.card ≤ retainedCap := by
  obtain ⟨W,P,pn,deg,seed,fibre⟩ :=
    marked_projection F f sub B.wordDegree hMax axesCap haxesSmall hdegFit emin axes hi marks
  have pmin : 3≤P.natDegree := deg.symm ▸ emin
  have pmax : P.natDegree<B.maxOrd := deg.symm ▸ emax
  have count := aggregate P T (scalar M) (fun γ=>liftPoly (F.scalar γ))
    (rate P.natDegree) (P.natDegree-1) pn fibre (by
      intro Q ir dvd U us qmark
      have words : Word 179818 B.wordDegree M.word F.scalar U :=
        ⟨W.distinct.mono us,fun γ hγ=>W.degree γ (us hγ),fun γ hγ=>W.hits γ (us hγ)⟩
      exact factor_price B rate mono small proper bounded F (us.trans sub) words ir _ pmin pmax
        (natDegree_le_of_dvd dvd pn) qmark)
  rw [deg] at count
  have priced := Nat.add_le_add_right (Nat.mul_le_mul_left (rate f.natDegree) seed)
    ((f.natDegree-1)*f.natDegree)
  exact count.trans (priced.trans (paid f.natDegree _ _ emin emax axes (graded 1)))

end
end Lower6961.RetainedCompression
