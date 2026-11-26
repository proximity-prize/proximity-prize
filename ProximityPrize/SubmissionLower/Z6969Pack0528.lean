import ProximityPrize.SubmissionLower.Z6969Pack0526
import ProximityPrize.SubmissionLower.Z6969Pack0527
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
import Mathlib.LinearAlgebra.Lagrange
import ProximityPrize.SubmissionLower.Z6969Pack0520
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree

set_option Elab.async false

-- Source: Research6969.OdeEmbedding
section Z6969Source0541
set_option autoImplicit true
namespace Research6969.OdeEmbedding
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966 Research6966.NonlinearMarkRows Research6966.NonlinearMarkDegrees
open MvPolynomial Finset Polynomial
open scoped Polynomial Differential BigOperators
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds

def point {σ:Type*} (z:σ→FX) (y:FX) : Option σ→FX := fun i=>i.elim y z
def poly {σ:Type*} (Q:Eqn σ FX) : MvPolynomial (Option σ) FX :=
  (optionEquivLeft FX σ).symm Q

theorem evaluate_poly {σ:Type*} (Q:Eqn σ FX) (z:σ→FX) (y:FX) :
    MvPolynomial.aeval (point z y) (poly Q)=evaluate z y Q := by
  change MvPolynomial.eval (fun i=>i.elim y z) (poly Q)=_
  rw [optionEquivLeft_elim_eval]
  simp only [poly,AlgEquiv.apply_symm_apply,Polynomial.eval_map]
  rfl

theorem poly_bound {σ:Type*} {Q:Eqn σ FX} {h v:ℕ} (y:Q.natDegree≤h)
    (seed:cap (fun _=>1) v Q) : poly Q∈restrictBidegree σ FX h v := by
  apply mem_restrictBidegree.mpr
  intro m hm
  have nz : (Q.coeff (m none)).coeff m.some≠0 := by
    have eq:=optionEquivLeft_coeff_some_coeff_none FX σ m (poly Q)
    simpa [poly] using (eq.trans_ne (MvPolynomial.mem_support_iff.mp hm))
  have coeff_ne : Q.coeff (m none)≠0 :=fun eq=>nz (by simp [eq])
  have weight:=MvPolynomial.mem_restrictWeightAtMost.mp (seed (m none)) m.some
    (MvPolynomial.mem_support_iff.mpr nz)
  refine ⟨(Polynomial.le_natDegree_of_ne_zero coeff_ne).trans y,?_⟩
  simpa [Finsupp.weight_apply,Finsupp.degree_apply,Finsupp.sum] using weight

theorem exists_cut (sites:Finset I) (recv:I→K) (d t:ℕ) (short:d≤sites.card+t)
    (tame:t<p) {r u:ℕ} (rp:1≤r) (A B:Eqn (Fin 2) FX)
    (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) u A) (bz:cap (fun _=>1) u B) (i:I) :
    ∃ cut:MvPolynomial (bidegreeExponents (Fin 2) r u) FX, cut.totalDegree≤max 1 (2*t) ∧
      ∀ (z:Fin 2→FX) (S:Polynomial K), (∀ j,Differential.deriv (z j)=0) → S.natDegree≤d →
        (∀ k∈sites,S.eval (node k)=recv k) →
        evaluate z (atX S) A * atX S.derivative = evaluate z (atX S) B →
        evaluate z (atX S) A ≠ 0 →
        (MvPolynomial.aeval (monomialPoint (bidegreeExponents (Fin 2) r u) (point z (atX S))) cut=0 ↔
          S.eval (node i)=recv i) := by
  obtain ⟨Q,degree,axes,detect⟩:=ShortenedOdeRows.exists_test sites recv d t short tame rp A B ay byDeg i
  have y : (2*t-1)*r+1≤r*max 1 (2*t) := by
    cases t with
    | zero=>simpa using rp
    | succ t=>
      rw [max_eq_right (by omega:1≤2*(t+1)),Nat.mul_comm r]
      have eq:2*(t+1)=(2*(t+1)-1)+1:=by omega
      calc _ ≤ (2*(t+1)-1)*r+r := by omega
        _ = (2*(t+1))*r := by
          rw [← Nat.succ_mul]
          exact congrArg (fun s=>s*r) (by omega)
  have seeds : (2*t-1)*u≤u*max 1 (2*t) :=
    (Nat.mul_le_mul_right _ ((Nat.sub_le ..).trans (le_max_right 1 (2*t)))).trans_eq (Nat.mul_comm ..)
  have box:=mem_restrictBidegree_mono (poly_bound degree (axes _ _ az bz)) y seeds
  obtain ⟨cut,hcut,image⟩:=ScaledBidegree.exists_lift r u (max 1 (2*t)) (poly Q) box
  refine ⟨cut,hcut,?_⟩
  intro z S fixed deg common law regular
  rw [MvPolynomial.aeval_monomialPoint]
  rw [← bidegreeMap_eq_monomialMap r u, image, evaluate_poly]
  exact detect z S fixed deg common law regular

end
end Research6969.OdeEmbedding
end Z6969Source0541

-- Source: Research6969.KnownGraphShortening
section Z6969Source0542
set_option autoImplicit true
namespace Research6969.KnownGraphShortening
noncomputable section
open Polynomial Finset
open scoped Polynomial

variable {K I : Type*} [Field K] {nodes : I → K} (T : Finset I)

/-- Remove the evaluations shared with one fixed word on the chosen nodes. -/
def residual (nodes : I → K) (base word : K[X]) : K[X] :=
  (word-base) /ₘ Lagrange.nodal T nodes

theorem recover (inj : Function.Injective nodes) (base word : K[X])
    (same : ∀ i ∈ T, word.eval (nodes i) = base.eval (nodes i)) :
    word = base + Lagrange.nodal T nodes * residual T nodes base word := by
  let D := Lagrange.nodal T nodes
  have zero : (word-base) %ₘ D = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero T inj.injOn
    · simpa [D, Lagrange.degree_nodal] using
        (degree_modByMonic_lt (word-base) (Lagrange.nodal_monic (s:=T) (v:=nodes)))
    · intro i hi
      rw [modByMonic_eq_sub_mul_div, eval_sub, eval_mul]
      simp [D, Lagrange.eval_nodal_at_node hi, same i hi]
  have factor := modByMonic_add_div (word-base) D
  rw [zero, zero_add] at factor
  change word = base + D * ((word-base) /ₘ D)
  rw [factor]
  abel

theorem degree_bound (base word : K[X]) {d : ℕ}
    (hb : base.natDegree ≤ d) (hw : word.natDegree ≤ d) :
    (residual T nodes base word).natDegree ≤ d-T.card := by
  unfold residual
  rw [natDegree_divByMonic _ Lagrange.nodal_monic, Lagrange.natDegree_nodal]
  exact Nat.sub_le_sub_right ((natDegree_sub_le ..).trans (max_le hw hb)) _

theorem detects (inj : Function.Injective nodes) (base word : K[X])
    (same : ∀ i ∈ T, word.eval (nodes i) = base.eval (nodes i))
    {j : I} (outside : j ∉ T) (received : K) :
    (residual T nodes base word).eval (nodes j) =
      (received-base.eval (nodes j))/(Lagrange.nodal T nodes).eval (nodes j) ↔
      word.eval (nodes j) = received := by
  have nz : (Lagrange.nodal T nodes).eval (nodes j) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (by
      intro i hi eq
      exact outside (inj eq ▸ hi))
  have eq := congrArg (fun p : K[X] => p.eval (nodes j)) (recover T inj base word same)
  simp only [eval_add, eval_mul] at eq
  rw [eq_div_iff nz, mul_comm, eq]
  rw [eq_sub_iff_add_eq, add_comm]

theorem common_card_le (inj : Function.Injective nodes) {base word : K[X]}
    (distinct : word ≠ base) (same : ∀ i ∈ T, word.eval (nodes i) = base.eval (nodes i))
    {d : ℕ} (hb : base.natDegree ≤ d) (hw : word.natDegree ≤ d) : T.card ≤ d := by
  have dvd : Lagrange.nodal T nodes ∣ word-base := by
    refine ⟨residual T nodes base word, ?_⟩
    have h := recover T inj base word same
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm ..))
  have h := natDegree_le_of_dvd dvd (sub_ne_zero.mpr distinct)
  rw [Lagrange.natDegree_nodal] at h
  exact h.trans ((natDegree_sub_le ..).trans (max_le hw hb))

theorem derivative_residual (inj : Function.Injective nodes) (base word : K[X])
    (same : ∀ i ∈ T, word.eval (nodes i) = base.eval (nodes i)) :
    derivative word = derivative base +
      (derivative (Lagrange.nodal T nodes) * residual T nodes base word +
        Lagrange.nodal T nodes * derivative (residual T nodes base word)) := by
  calc derivative word = derivative (base + Lagrange.nodal T nodes * residual T nodes base word) :=
        congrArg derivative (recover T inj base word same)
    _ = _ := by rw [derivative_add, derivative_mul]

theorem residual_hits [DecidableEq K] [DecidableEq I] (inj : Function.Injective nodes) (S : Finset I) (recv : I → K)
    (base word : K[X]) (same : ∀ i ∈ T, word.eval (nodes i) = base.eval (nodes i))
    (a : ℕ) (enough : a ≤ (S.filter (fun i => word.eval (nodes i) = recv i)).card) :
    a - T.card ≤ ((S \ T).filter (fun i => (residual T nodes base word).eval (nodes i) =
      (recv i-base.eval (nodes i))/(Lagrange.nodal T nodes).eval (nodes i))).card := by
  classical
  let good := S.filter (fun i => word.eval (nodes i) = recv i)
  have sub : good \ T ⊆ (S \ T).filter (fun i => (residual T nodes base word).eval (nodes i) =
      (recv i-base.eval (nodes i))/(Lagrange.nodal T nodes).eval (nodes i)) := by
    intro i hi
    obtain ⟨hit,out⟩ := mem_sdiff.mp hi
    obtain ⟨mem,agree⟩ := mem_filter.mp hit
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem,out⟩,(detects T inj base word same out _).mpr agree⟩
  have bound : good.card ≤ (good \ T).card + T.card := card_le_card_sdiff_add_card
  exact (Nat.sub_le_of_le_add (enough.trans bound)).trans (card_le_card sub)

end
end Research6969.KnownGraphShortening
end Z6969Source0542

-- Source: Research6969.MarkedAdaptive
section Z6969Source0543
set_option autoImplicit true
namespace Research6969.MarkedAdaptive
noncomputable section
open K1 (K I node p)
open K1_14 (FX atX)
open Research6966 Research6966.NonlinearMarkRows Research6966.NonlinearMarkDegrees
open MvPolynomial Finset
open scoped BigOperators Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 900000

def price (n d A:ℕ) : ℚ := 2*(n:ℚ)*d/A

theorem ratio {n d A l:ℕ} (dp:0<d) (gap:d<A) (ld:l≤d) :
    ((n-l:ℕ):ℚ)*(max 1 (2*(d-l)):ℕ)≤price n d A*(A-l:ℕ) := by
  have apos : (0:ℚ)<A := by exact_mod_cast dp.trans gap
  dsimp [price]
  rw [div_mul_eq_mul_div,le_div_iff₀ apos]
  suffices h:(n-l)*max 1 (2*(d-l))*A≤2*n*d*(A-l) by exact_mod_cast h
  by_cases atEnd:l=d
  · subst l
    simp only [Nat.sub_self,Nat.mul_zero,Nat.max_zero,mul_one]
    have rest : 0<A-d := by omega
    have left : d≤d*(A-d) := Nat.le_mul_of_pos_right _ rest
    have right : A-d≤d*(A-d) := Nat.le_mul_of_pos_left _ dp
    have bound : A≤2*d*(A-d) := by
      have id:=Nat.sub_add_cancel (Nat.le_of_lt gap)
      nlinarith only [left,right,id]
    calc (n-d)*A ≤ n*A := Nat.mul_le_mul_right _ (Nat.sub_le ..)
      _ ≤ n*(2*d*(A-d)) := Nat.mul_le_mul_left n bound
      _ = _ := by ring
  · have t:1≤2*(d-l):=by omega
    rw [max_eq_right t]
    have scaled : (d-l)*A≤d*(A-l) := by
      rw [Nat.sub_mul,Nat.mul_sub]
      apply Nat.sub_le_sub_left
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left l gap.le
    calc (n-l)*(2*(d-l))*A = 2*((n-l)*((d-l)*A)) := by ring
      _ ≤ 2*(n*(d*(A-l))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le ..) scaled)
      _ = _ := by ring

abbrev Coordinates (r u:ℕ) := bidegreeExponents (Fin 2) r u → FX

/-- Common-node counting for a bounded-degree readout in any one fixed embedding. -/
theorem supplies_from_nodes {σ:Type*} {d agreement:ℕ} (dp:0<d) (gap:d<agreement)
    (W:Finset (σ→FX)) (words:(σ→FX)→Polynomial K) (received:I→K)
    (distinct:Set.InjOn words (W:Set _)) (degree:∀ x∈W,(words x).natDegree≤d)
    (enough:∀ x∈W,agreement≤(univ.filter (fun i=>(words x).eval (node i)=received i)).card)
    (make:∀ (sites:Finset I) (t:ℕ), d≤sites.card+t → t≤d → ∀ i:I,
      ∃ cut:MvPolynomial σ FX, cut.totalDegree≤max 1 (2*t) ∧
        ∀ x∈W,(∀ k∈sites,(words x).eval (node k)=received k) →
        (aeval x cut=0 ↔ (words x).eval (node i)=received i)) :
    AdaptiveIncidence.Tests (ι:=I) W (price (Fintype.card I) d agreement) := by
  classical
  intro T sub large
  let sites:Finset I:=univ.filter (fun i=>∀ x∈T,(words x).eval (node i)=received i)
  have common {x} (hx:x∈T) (i) (hi:i∈sites) : (words x).eval (node i)=received i :=
    (mem_filter.mp hi).2 x hx
  obtain ⟨x,hx,y,hy,ne⟩:=Finset.one_lt_card.mp large
  have diff : words x ≠ words y := fun eq=>ne (distinct (sub hx) (sub hy) eq)
  have ld : sites.card≤d :=
    KnownGraphShortening.common_card_le sites ProximityPrize.Benchmark.IRSProfile.domain.injective diff
      (fun i hi=>(common hx i hi).trans (common hy i hi).symm) (degree y (sub hy)) (degree x (sub hx))
  let t:=d-sites.card
  have short : d≤sites.card+t := by dsimp [t];omega
  choose cut bound detect using fun i=>make sites t short (Nat.sub_le ..) i
  have actual {x} (hx:x∈T) (i:I) : aeval x (cut i)=0 ↔ (words x).eval (node i)=received i :=
    detect i x (sub hx) (common hx)
  refine ⟨sitesᶜ,agreement-sites.card,max 1 (2*t),cut,by omega,?_,?_,?_⟩
  · rw [card_compl]
    exact ratio dp gap ld
  · intro i hi
    have no:=mem_compl.mp hi
    have ex : ∃ x∈T,(words x).eval (node i)≠received i := by
      by_contra! same
      exact no (mem_filter.mpr ⟨mem_univ i,same⟩)
    obtain ⟨x,hx,miss⟩:=ex
    exact ⟨bound i,x,hx,fun zero=>miss ((actual hx i).mp zero)⟩
  · intro x hx
    let hits:Finset I:=univ.filter (fun i=>(words x).eval (node i)=received i)
    have required : agreement≤hits.card:=enough x (sub hx)
    have h : hits.card≤(hits \ sites).card+sites.card:=card_le_card_sdiff_add_card
    have left : agreement-sites.card≤(hits \ sites).card:=Nat.sub_le_of_le_add (required.trans h)
    apply left.trans
    apply card_le_card
    intro i hi
    obtain ⟨yes,no⟩:=mem_sdiff.mp hi
    apply (@Finset.mem_filter I (fun j=>aeval x (cut j)=0)
      (fun _=>Classical.propDecidable _) sitesᶜ i).mpr
    exact ⟨mem_compl.mpr no,(actual hx i).mpr (mem_filter.mp yes).2⟩

/-- Every finite subset of genuine regular marked words supplies the proper
cuts needed by the dimension induction, with price 2*n*d/agreement. -/
theorem supplies_tests {r u d agreement:ℕ} (rp:1≤r) (dp:0<d) (gap:d<agreement) (tame:d<p)
    (A B:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) u A) (bz:cap (fun _=>1) u B)
    (W:Finset (Coordinates r u)) (words:Coordinates r u→Polynomial K)
    (params:Coordinates r u→Fin 2→FX) (received:I→K)
    (original:∀ x∈W,x=monomialPoint (bidegreeExponents (Fin 2) r u)
      (OdeEmbedding.point (params x) (atX (words x))))
    (distinct:Set.InjOn words (W:Set _)) (degree:∀ x∈W,(words x).natDegree≤d)
    (fixed:∀ x∈W,∀ j,Differential.deriv (params x j)=0)
    (law:∀ x∈W,evaluate (params x) (atX (words x)) A * atX (words x).derivative =
      evaluate (params x) (atX (words x)) B)
    (regular:∀ x∈W,evaluate (params x) (atX (words x)) A≠0)
    (enough:∀ x∈W,agreement≤(univ.filter (fun i=> (words x).eval (node i)=received i)).card) :
    AdaptiveIncidence.Tests (ι:=I) W (price (Fintype.card I) d agreement) := by
  apply supplies_from_nodes dp gap W words received distinct degree enough
  intro sites t short td i
  obtain ⟨cut,bound,detect⟩:=OdeEmbedding.exists_cut sites received d t short
    (td.trans_lt tame) rp A B ay byDeg az bz i
  refine ⟨cut,bound,?_⟩
  intro x hx common
  have eq:=detect (params x) (words x) (fixed x hx) (degree x hx) common (law x hx) (regular x hx)
  rwa [← original x hx] at eq

end
end Research6969.MarkedAdaptive
end Z6969Source0543

-- Source: Research6969.NonlinearSurface
section Z6969Source0544
set_option autoImplicit true
namespace Research6969.NonlinearSurface
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966 Research6966.NonlinearMarkRows Research6966.NonlinearMarkDegrees
open Research6969.MarkedAdaptive
open MvPolynomial Finset
open scoped BigOperators Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 900000

/-- The coefficient of a hypersurface in the fixed embedding counts the
whole regular marked family, including constant-seed components of its cuts. -/
theorem count {r u d agreement g v:ℕ} (rp:1≤r) (up:0<u) (dp:0<d) (gap:d<agreement)
    (possible:agreement≤Fintype.card I) (tame:d<p)
    (A B H:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) u A) (bz:cap (fun _=>1) u B)
    (nonzero:H≠0) (hy:H.natDegree≤g) (hz:cap (fun _=>1) v H)
    (W:Finset (Coordinates r u)) (words:Coordinates r u→Polynomial K)
    (params:Coordinates r u→Fin 2→FX) (received:I→K)
    (original:∀ x∈W,x=monomialPoint (bidegreeExponents (Fin 2) r u)
      (OdeEmbedding.point (params x) (atX (words x))))
    (distinct:Set.InjOn words (W:Set _)) (degree:∀ x∈W,(words x).natDegree≤d)
    (fixed:∀ x∈W,∀ j,Differential.deriv (params x j)=0)
    (law:∀ x∈W,evaluate (params x) (atX (words x)) A * atX (words x).derivative =
      evaluate (params x) (atX (words x)) B)
    (regular:∀ x∈W,evaluate (params x) (atX (words x)) A≠0)
    (surface:∀ x∈W,evaluate (params x) (atX (words x)) H=0)
    (enough:∀ x∈W,agreement≤(univ.filter (fun i=> (words x).eval (node i)=received i)).card) :
    (W.card:ℚ) ≤ ((g*u^2+2*v*r*u:ℕ):ℚ) * price (Fintype.card I) d agreement ^ 2 := by
  classical
  let R:=price (Fintype.card I) d agreement
  have apos : (0:ℚ)<agreement:=by exact_mod_cast dp.trans gap
  have one : 1≤R := by
    change 1≤2*(Fintype.card I:ℚ)*d/agreement
    rw [le_div_iff₀ apos,one_mul]
    exact_mod_cast (show agreement≤2*Fintype.card I*d from
      possible.trans ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ dp)))
  rcases W.eq_empty_or_nonempty with empty|⟨x₀,h₀⟩
  · rw [empty,card_empty,Nat.cast_zero]
    positivity
  let raw:=OdeEmbedding.poly H
  let J:Ideal (MvPolynomial (Option (Fin 2)) FX):=Ideal.span {raw}
  let M:=bidegreeMap (Fin 2) FX r u
  let D:=J.comap M
  have actual (x) (hx:x∈W) : OdeEmbedding.point (params x) (atX (words x))∈zeroLocus FX J := by
    apply mem_zeroLocus_iff_le_ker_aeval.mpr
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact RingHom.mem_ker.mpr ((OdeEmbedding.evaluate_poly H ..).trans (surface x hx))
  have proper : J≠⊤ := by
    intro top
    have zero:=actual x₀ h₀ (1:MvPolynomial (Option (Fin 2)) FX) (by simp [top])
    simpa using zero
  have nz : raw≠0 := fun eq=>nonzero ((optionEquivLeft FX (Fin 2)).symm.injective (by simpa [raw,OdeEmbedding.poly] using eq))
  have dims : (affineHilbertPolynomial D).natDegree=2 := by
    have h:=natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton (σ:=Fin 2) rp up nz proper
    simpa [D,J,M,Nat.card_eq_fintype_card] using h
  have sumBound : (∑ Q∈D.minimalPrimesFinset,affineDegree Q)≤((g*u^2+2*v*r*u:ℕ):ℚ) := by
    apply (sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le rp up raw).trans
    have bound:=affineDegree_comap_bidegreeMap_span_singleton_le rp up nz (OdeEmbedding.poly_bound hy hz)
    simpa [Nat.card_eq_fintype_card] using bound
  have tests:=supplies_tests rp dp gap tame A B ay byDeg az bz W words params received
    original distinct degree fixed law regular enough
  apply card_le_mul_pow_of_forall_mem_zeroLocus D.minimalPrimesFinset
    (fun Q hQ=>(natDegree_affineHilbertPolynomial_le_of_le (Ideal.mem_minimalPrimesFinset.mp hQ).le).trans_eq dims)
    sumBound one W
  · intro x hx
    have on : x∈zeroLocus FX D := by
      intro f hf
      rw [original x hx,aeval_monomialPoint,←bidegreeMap_eq_monomialMap r u]
      exact actual x hx _ hf
    obtain ⟨Q,hQ,yes⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus D 1 x on (by simp)
    exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,yes⟩
  · intro Q hQ
    have : Q.IsPrime := (Ideal.mem_minimalPrimesFinset.mp hQ).isPrime
    rw [K1_11.ncard_inter_filter]
    exact AdaptiveIncidence.prime_count W one tests Q _ (filter_subset _ _)
      (fun x hx=>(mem_filter.mp hx).2)

end
end Research6969.NonlinearSurface
end Z6969Source0544
