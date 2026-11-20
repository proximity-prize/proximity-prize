import ProximityPrize.SubmissionLower.Fast068
import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Nonparallel6921
set_option Elab.async false

/- Profile transport of Dadon's PR 627. -/
section Port_K1_12Defs
set_option autoImplicit true
namespace K21_12
noncomputable section

open Polynomial K21

/-- The homogeneous direction and four output coefficients on the puncture.
The numerator contents are U,V; den is a Hilbert-90 denominator with no domain zeros. -/
structure Direction (u : Words) (deleted : Finset I) where
  den : K[X]
  U : K[X]
  V : K[X]
  A : Fin 2 → K[X]
  out : Fin 2 → Fin 2 → K[X]
  den_nodes : ∀ i, den.eval (node i) ≠ 0
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ den
  coprime : IsCoprime U V
  phase : U * den.map twist = V * den
  degrees_eq : V.natDegree = U.natDegree
  primitive : IsCoprime (A 0) (A 1)
  height : U.natDegree + amplitudeDegree (A 0) (A 1) + deleted.card ≤ 32872
  out_degree : ∀ i j, (out i j).degree <
    (131072 + U.natDegree + amplitudeDegree (A 0) (A 1) : ℕ)
  nodes : ∀ x ∉ deleted, ∀ i j, (out i j).eval (node x) =
    U.eval (node x) * ((A i).map twist).eval (node x) * u j x -
    V.eval (node x) * (A j).eval (node x) * twist (u i x)

variable {u : Words} {deleted : Finset I}

def Direction.s (F : Direction u deleted) := amplitudeDegree (F.A 0) (F.A 1)

def Direction.amp (F : Direction u deleted) (γ : K) := F.A 0 + C γ * F.A 1

/-- Guards on the original finite label for the one-anchor determinant proof. -/
structure Regular (F : Direction u deleted) (γ : K) : Prop where
  amp_ne : F.amp γ ≠ 0
  degree_eq : (F.amp γ).natDegree = F.s
  adjacent : IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit : IsCoprime (F.amp γ) F.U
  node_unit : ∀ i ∉ deleted, (F.amp γ).eval (node i) ≠ 0

def excluded (F : Direction u deleted) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Regular F γ)

/-- L/G interpolates A₀u₁−A₁u₀ on the puncture; the two pole conditions
retain full divisibility and the strict bound is an order-at-infinity bound. -/
structure CrossLift (F : Direction u deleted) where
  G : K[X]
  L : K[X]
  monic : G.Monic
  left : G ∣ F.U
  right : G.map twist ∣ F.V
  degree_lt : L.degree < (131072 + F.s + G.natDegree : ℕ)
  nodes : ∀ i ∉ deleted, L.eval (node i) = G.eval (node i) *
    ((F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i)

/-- After the affine translation by η and subtraction of its actual decoder,
the sole remaining rational offset is proper and reduced. -/
structure Offset (F : Direction u deleted) {η : K} (anchor : BadMark u η) where
  pencil : K[X]
  pencil_degree : pencil.degree < 131072
  E : K[X]
  Q : K[X]
  E_monic : E.Monic
  left : E ∣ F.U
  right : E.map twist ∣ F.V
  proper : Q.degree < E.degree
  reduced : IsCoprime Q E
  raw : I → K
  raw_fixed : ∀ i ∉ deleted, twist (raw i) = raw i
  first : ∀ i ∉ deleted, u 0 i + η * u 1 i - anchor.decoder.eval (node i) =
    (F.amp η).eval (node i) * raw i / F.den.eval (node i)
  second : ∀ i ∉ deleted, u 1 i - pencil.eval (node i) =
    Q.eval (node i) / E.eval (node i) + (F.A 1).eval (node i) * raw i / F.den.eval (node i)

end
end K21_12
end Port_K1_12Defs

section Port_K1_12Saturation
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_12
noncomputable section

open Polynomial K21 FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators

theorem eval_unit_of_dvd {P Q : K[X]} (h : P ∣ Q) {a : K}
    (hu : Q.eval a ≠ 0) : P.eval a ≠ 0 := by
  obtain ⟨L, rfl⟩ := h
  rw [eval_mul] at hu
  exact left_ne_zero_of_mul hu

private def conjugate : ℕ → K[X] → K[X]
  | 0, P => P
  | n+1, P => (conjugate n P).map twist

private theorem conjugate_six (P : K[X]) : conjugate 6 P = P := by
  have iter (n : ℕ) : conjugate n P = P.map (iterateFrobenius K p n) := by
    induction n with
    | zero => simp [conjugate]
    | succ n ih =>
      rw [conjugate, ih, map_map, add_comm n 1,
        iterateFrobenius_add K p 1 n, iterateFrobenius_one, twist]
  have card : Fintype.card K = p^6 := KoalaBear.card_ext6
  have hs : iterateFrobenius K p 6 = RingHom.id K := by
    apply RingHom.ext
    intro x
    change x ^ p ^ 6 = x
    rw [← card]
    exact FiniteField.pow_card x
  rw [iter, hs, map_id]

theorem twist_node (i : I) : twist (node i) = node i := Native.native_domain_fixed i

theorem eval_twist (P : K[X]) (i : I) : (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  Strata.eval_coefficient_map twist P (node i) (twist_node i)

private theorem conjugate_nodes {W : K[X]} (hu : ∀ i, W.eval (node i) ≠ 0)
    (n : ℕ) (i : I) : (conjugate n W).eval (node i) ≠ 0 := by
  induction n with
  | zero => exact hu i
  | succ n ih => rw [conjugate, eval_twist]; exact (map_ne_zero twist).mpr ih

private theorem conjugate_dvd {W T : K[X]} (h : W ∣ T) (ht : T.map twist = T)
    (n : ℕ) : conjugate n W ∣ T := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [conjugate, ← ht]
    exact map_dvd (Polynomial.mapRingHom twist) ih

/-- The monic lcm of the full conjugates divides every fixed multiple.
Its complementary factor accounts for all primary multiplicities. -/
theorem invariant_multiple (W : K[X]) (hu : ∀ i, W.eval (node i) ≠ 0) :
    ∃ L C₀ : K[X], L = W * C₀ ∧ L.map twist = L ∧ (∀ i, L.eval (node i) ≠ 0) ∧
      ∀ N : K[X], (W*N).map twist = W*N → ∃ S : K[X], S.map twist = S ∧ N = C₀*S := by
  classical
  let f := fun j : Fin 6 => conjugate j.val W
  let rawL := Finset.univ.lcm f
  let L := normalize rawL
  have hdiv (j : Fin 6) : f j ∣ L :=
    dvd_normalize_iff.mpr (Finset.dvd_lcm (Finset.mem_univ j))
  have hnode (i : I) : L.eval (node i) ≠ 0 := by
    apply eval_unit_of_dvd (normalize_dvd_iff.mpr (Finset.lcm_dvd_prod Finset.univ f))
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => conjugate_nodes hu j.val i)
  have hne : L ≠ 0 := fun h => hnode 0 (by rw [h, eval_zero])
  have hm : L.Monic := monic_normalize (by simpa [L] using hne)
  have hcross : L ∣ L.map twist := by
    apply normalize_dvd_iff.mpr
    apply Finset.lcm_dvd
    intro j _
    have step (i : Fin 6) : conjugate (i.val+1) W ∣ L.map twist :=
      map_dvd (Polynomial.mapRingHom twist) (hdiv i)
    by_cases hz : j.val = 0
    · change conjugate j.val W ∣ _
      rw [hz]
      change W ∣ _
      simpa only [show (5 : Fin 6).val+1 = 6 by decide, conjugate_six] using step 5
    · let i : Fin 6 := ⟨j.val-1, by omega⟩
      have hi : i.val+1 = j.val := by dsimp [i]; omega
      simpa only [hi, f] using step i
  have hfix : L.map twist = L := (eq_of_dvd_of_natDegree_le_of_leadingCoeff hcross
    natDegree_map_le (hm.trans (hm.map twist).symm)).symm
  obtain ⟨C₀, hc⟩ := hdiv 0
  change L = W * C₀ at hc
  refine ⟨L, C₀, hc, hfix, hnode, ?_⟩
  intro N ht
  have hL : L ∣ W*N := normalize_dvd_iff.mpr (Finset.lcm_dvd (fun j _ =>
    conjugate_dvd (dvd_mul_right W N) ht j.val))
  obtain ⟨S, hs⟩ := hL
  refine ⟨S, ?_, ?_⟩
  · apply mul_left_cancel₀ hne
    rw [hs, Polynomial.map_mul, hfix] at ht
    exact ht
  · have hW : W ≠ 0 := fun h => hu 0 (by rw [h, eval_zero])
    apply mul_left_cancel₀ hW
    simpa only [hc, mul_assoc] using hs

variable {u : Words} {deleted : Finset I} {F : Direction u deleted} {η γ : K}
  {anchor : BadMark u η}

def Offset.translated (O : Offset F anchor) (m : BadMark u γ) :=
  m.decoder - anchor.decoder - C (γ-η) * O.pencil

def Offset.numerator (O : Offset F anchor) (m : BadMark u γ) :=
  O.E * O.translated m - C (γ-η) * O.Q

theorem Offset.E_nodes (O : Offset F anchor) (i : I) : O.E.eval (node i) ≠ 0 :=
  eval_unit_of_dvd (O.left.trans F.U_dvd) (F.den_nodes i)

theorem Offset.translated_degree (O : Offset F anchor) (m : BadMark u γ) :
    (O.translated m).degree < 131072 := by
  unfold Offset.translated
  rw [C_mul']
  exact Principal.degree_sub_lt (Principal.degree_sub_lt m.degree anchor.degree)
    (Principal.degree_smul_lt _ O.pencil_degree)

theorem Offset.numerator_degree (O : Offset F anchor) (m : BadMark u γ) :
    (O.numerator m).natDegree < 131072 + O.E.natDegree := by
  have hQ := O.proper.trans_le (degree_le_natDegree (p := O.E))
  by_cases hz : O.numerator m = 0
  · simp [hz]
  apply (natDegree_lt_iff_degree_lt hz).mpr
  apply Principal.degree_sub_lt (Strata.degree_mul_lt_add O.E (O.translated m)
    O.E.natDegree 131072 le_rfl (O.translated_degree m))
  rw [C_mul']
  exact Principal.degree_smul_lt _ (hQ.trans_le (by exact_mod_cast Nat.le_add_left _ _))

theorem Offset.hits (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (i : I) (hi : i ∈ m.support) :
    W.eval (node i) * (O.numerator m).eval (node i) = (F.amp γ).eval (node i) * O.raw i := by
  have hd := Finset.disjoint_left.mp avoid hi
  have he := O.E_nodes i
  have hf := O.first i hd
  have hs := O.second i hd
  have hn := F.den_nodes i
  have hw : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by rw [hW, eval_mul]
  simp only [Direction.amp, eval_add, eval_C, eval_mul] at hf ⊢
  rw [eq_div_iff hn] at hf
  have hs' : O.E.eval (node i) * F.den.eval (node i) * (u 1 i - O.pencil.eval (node i)) =
      F.den.eval (node i) * O.Q.eval (node i) + O.E.eval (node i) * ((F.A 1).eval (node i) * O.raw i) := by
    rw [hs]
    field_simp [he, hn]
  simp only [Offset.numerator, Offset.translated, eval_sub, eval_mul, eval_C, m.hits i hi]
  apply mul_left_cancel₀ he
  rw [← mul_assoc, ← hw]
  linear_combination O.E.eval (node i) * hf + (γ - η) * hs'

/-- Clearing the small contents U/E and V/E^σ permits root counting at
the original agreement. The much larger den/E never enters the degree test. -/
theorem Offset.fixed_numerator (O : Offset F anchor) (W : K[X]) (hW : F.den = O.E * W)
    (m : BadMark u γ) (avoid : Disjoint m.support deleted) (reg : Regular F γ) :
    ∃ N : K[X], O.numerator m = F.amp γ * N ∧ (W*N).map twist = W*N := by
  classical
  obtain ⟨l, hl⟩ := O.left
  obtain ⟨r, hr⟩ := O.right
  have hl0 : l ≠ 0 := fun hz => F.U_ne (by simp [hl, hz])
  have hr0 : r ≠ 0 := fun hz => F.V_ne (by simp [hr, hz])
  have hWnodes (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  have hEσ : O.E.map twist ≠ 0 := (O.E_monic.map twist).ne_zero
  have hphase : l * W.map twist = r * W := by
    apply mul_left_cancel₀ (mul_ne_zero O.E_monic.ne_zero hEσ)
    have h := F.phase
    rw [hl, hr, hW, Polynomial.map_mul] at h
    linear_combination h
  let a := F.amp γ
  let P := O.numerator m
  let diff := l * a.map twist * P - r * a * P.map twist
  have zero_at (i : I) (hi : i ∈ m.support) : diff.eval (node i) = 0 := by
    have hrw := O.raw_fixed i (Finset.disjoint_left.mp avoid hi)
    have h1 := O.hits W hW m avoid i hi
    have h2 := congrArg twist h1
    simp only [map_mul, hrw] at h2
    have h3 := congrArg (eval (node i)) hphase
    simp only [eval_mul, eval_twist] at h3
    simp only [diff, eval_sub, eval_mul, eval_twist]
    change W.eval (node i) * P.eval (node i) = a.eval (node i) * O.raw i at h1
    change twist (W.eval (node i)) * twist (P.eval (node i)) =
      twist (a.eval (node i)) * O.raw i at h2
    apply (mul_eq_zero.mp (show W.eval (node i) * _ = 0 from ?_)).resolve_left (hWnodes i)
    linear_combination l.eval (node i) * twist (a.eval (node i)) * h1 -
      l.eval (node i) * a.eval (node i) * h2 +
      a.eval (node i) * twist (P.eval (node i)) * h3
  have ident : diff = 0 := by
    by_contra hne
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective diff hne m.support zero_at
    have hld : O.E.natDegree + l.natDegree = F.U.natDegree := by
      rw [hl, natDegree_mul O.E_monic.ne_zero hl0]
    have hrd : O.E.natDegree + r.natDegree = F.U.natDegree := by
      rw [← F.degrees_eq, hr, natDegree_mul hEσ hr0, natDegree_map_eq_of_injective twist.injective]
    have hP := O.numerator_degree m
    have hA := reg.degree_eq
    have hheight := F.height
    change F.U.natDegree + F.s + deleted.card ≤ 32872 at hheight
    have hdeg : diff.natDegree ≤ max (l.natDegree + a.natDegree + P.natDegree)
        (r.natDegree + a.natDegree + P.natDegree) := by
      apply (natDegree_sub_le _ _).trans
      exact max_le_max
        (natDegree_mul_le.trans (Nat.add_le_add_right
          (natDegree_mul_le.trans (Nat.add_le_add_left natDegree_map_le _)) _))
        (natDegree_mul_le.trans (Nat.add_le_add natDegree_mul_le natDegree_map_le))
    change P.natDegree < _ at hP
    change a.natDegree = _ at hA
    have hcount := m.agreement
    omega
  have eqn : l * a.map twist * P = r * a * P.map twist := sub_eq_zero.mp ident
  have hlU : l ∣ F.U := hl ▸ dvd_mul_left l O.E
  have cop : IsCoprime a (l * a.map twist) :=
    (reg.content_unit.of_isCoprime_of_dvd_right hlU).mul_right reg.adjacent
  have hdvd : a ∣ P := by
    apply cop.dvd_of_dvd_mul_left
    rw [eqn]
    exact (dvd_mul_left a r).mul_right _
  obtain ⟨N, hN⟩ := hdvd
  refine ⟨N, hN, ?_⟩
  have hred : l*N = r*N.map twist := by
    apply mul_left_cancel₀ (mul_ne_zero reg.amp_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr reg.amp_ne))
    rw [hN, Polynomial.map_mul] at eqn
    linear_combination eqn
  rw [Polynomial.map_mul]
  apply mul_left_cancel₀ hl0
  linear_combination N.map twist * hphase - W * hred

end
end K21_12
end Port_K1_12Saturation

section Port_K1_12Lift
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace K21_12
noncomputable section
open Polynomial K21 FrobeniusLocator ProximityPrize.Benchmark

theorem eq_on_puncture {deleted : Finset I} {P Q : K[X]} {d : ℕ}
    (hroom : d + deleted.card ≤ 262144) (hP : P.natDegree < d) (hQ : Q.natDegree < d)
    (hn : ∀ i ∉ deleted, P.eval (node i) = Q.eval (node i)) : P = Q := by
  classical
  apply sub_eq_zero.mp
  by_contra hne
  have hcount := Strata.root_nodes_card_le node IRSProfile.domain.injective (P-Q) hne
    (Finset.univ \ deleted) (by
      intro i hi
      rw [eval_sub, hn i (Finset.mem_sdiff.mp hi).2, sub_self])
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcount
  have h := natDegree_sub_le P Q
  omega

theorem natDegree_lt_of_degree_lt_pos {P : K[X]} {n : ℕ} (hn : 0 < n) (hd : P.degree < n) :
    P.natDegree < n := by
  by_cases h : P = 0
  · simpa [h] using hn
  exact (natDegree_lt_iff_degree_lt h).mpr hd

private theorem top_amplitude {A : Fin 2 → K[X]} (hp : IsCoprime (A 0) (A 1)) :
    ∃ j, A j ≠ 0 ∧ (A j).natDegree = max (A 0).natDegree (A 1).natDegree := by
  by_cases h0 : A 0 = 0
  · exact ⟨1,hp.ne_zero_or_ne_zero.resolve_left (not_not.mpr h0),by simp [h0]⟩
  by_cases h1 : A 1 = 0
  · exact ⟨0,h0,by simp [h1]⟩
  rcases le_total (A 0).natDegree (A 1).natDegree with h|h
  · exact ⟨1,h1,(max_eq_right h).symm⟩
  · exact ⟨0,h0,(max_eq_left h).symm⟩

/-- Cancel a primitive amplitude pair in two polynomial lifts of the
same word. The Bézout combination alone would give a worse degree. -/
private theorem cancel_pair (deleted : Finset I) (w : I → K) (A P : Fin 2 → K[X]) (d s : ℕ)
    (hs : max (A 0).natDegree (A 1).natDegree = s) (hcop : IsCoprime (A 0) (A 1))
    (hpos : 0 < d) (hroom : d+2*s+deleted.card ≤ 262144)
    (hP : ∀ j, (P j).natDegree < d+s)
    (hn : ∀ i ∉ deleted, ∀ j, (P j).eval (node i) = (A j).eval (node i) * w i) :
    ∃ leftLift : K[X], leftLift.natDegree < d ∧ ∀ i ∉ deleted, leftLift.eval (node i) = w i := by
  have hA0 : (A 0).natDegree ≤ s := hs ▸ le_max_left _ _
  have hA1 : (A 1).natDegree ≤ s := hs ▸ le_max_right _ _
  have cross : A 1 * P 0 = A 0 * P 1 := by
    apply eq_on_puncture hroom
    · exact natDegree_mul_le.trans_lt (by have := hP 0; omega)
    · exact natDegree_mul_le.trans_lt (by have := hP 1; omega)
    · intro i hi
      simp only [eval_mul, hn i hi]
      ring
  obtain ⟨j,hj,hjs⟩ := top_amplitude hcop
  obtain ⟨x,y,hxy⟩ := hcop
  let leftLift := x * P 0 + y * P 1
  have eqj : leftLift * A j = P j := by
    unfold leftLift
    fin_cases j
    · change (x*P 0 + y*P 1) * A 0 = P 0
      linear_combination P 0 * hxy - y * cross
    · change (x*P 0 + y*P 1) * A 1 = P 1
      linear_combination P 1 * hxy + x * cross
  refine ⟨leftLift, ?_, ?_⟩
  · by_cases hY : leftLift = 0
    · simpa [hY] using hpos
    have hd := natDegree_mul hY hj
    rw [eqj,hjs,hs] at hd
    have := hP j
    omega
  · intro i hi
    have h := congrArg (eval (node i)) hxy
    simp only [eval_add, eval_mul, eval_one] at h
    simp only [leftLift, eval_add, eval_mul, hn i hi]
    linear_combination w i * h

theorem cross_lift {u deleted} (F : Direction u deleted) : Nonempty (CrossLift F) := by
  classical
  let d := 131072 + F.U.natDegree + F.s
  let w (i : I) := (F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i
  let A' (j : Fin 2) := (F.A j).map twist
  let P (j : Fin 2) := F.A 0 * F.out j 1 - F.A 1 * F.out j 0
  let P' (j : Fin 2) := A' 1 * F.out 0 j - A' 0 * F.out 1 j
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ 32872 at hheight
  have hroom : d + 2*F.s + deleted.card ≤ 262144 := by dsimp [d]; omega
  have hpos : 0 < d := by dsimp [d]; omega
  have ha (j : Fin 2) : (F.A j).natDegree ≤ F.s := by
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have ha' (j : Fin 2) : (A' j).natDegree ≤ F.s := natDegree_map_le.trans (ha j)
  have hout (i j : Fin 2) : (F.out i j).natDegree < d :=
    natDegree_lt_of_degree_lt_pos hpos (F.out_degree i j)
  have hprod {a : K[X]} (ha : a.natDegree ≤ F.s) (i j : Fin 2) :
      (a * F.out i j).natDegree < d + F.s :=
    natDegree_mul_le.trans_lt (by have := hout i j; omega)
  obtain ⟨leftLift,hY,hYn⟩ := cancel_pair deleted (fun i => F.U.eval (node i)*w i) A' P d F.s
    (by simp only [A', natDegree_map_eq_of_injective twist.injective]; rfl)
    (F.primitive.map (Polynomial.mapRingHom twist)) hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha 0) j 1) (hprod (ha 1) j 0)))
    (by intro i hi j; simp only [P, A', w, eval_sub, eval_mul, F.nodes i hi]; ring)
  obtain ⟨rightLift,hZ,hZn⟩ := cancel_pair deleted (fun i => F.V.eval (node i)*twist (w i)) F.A P' d F.s
    rfl F.primitive hpos hroom
    (fun j => (natDegree_sub_le _ _).trans_lt (max_lt (hprod (ha' 1) 0 j) (hprod (ha' 0) 1 j)))
    (by intro i hi j
        simp only [P', A', w, eval_sub, eval_mul, F.nodes i hi, eval_twist, map_sub, map_mul]
        ring)
  let f : RatFunc K := algebraMap K[X] (RatFunc K) leftLift / algebraMap K[X] (RatFunc K) F.U
  have heq : f.num * F.U = leftLift * f.denom := (RatFunc.num_mul_eq_mul_denom_iff F.U_ne).mpr rfl
  have hn (i : I) (hi : i ∉ deleted) : f.num.eval (node i) = f.denom.eval (node i) * w i := by
    have h := congrArg (eval (node i)) heq
    simp only [eval_mul, hYn i hi] at h
    apply mul_left_cancel₀ (eval_unit_of_dvd F.U_dvd (F.den_nodes i))
    linear_combination h
  have hleft : f.denom ∣ F.U := RatFunc.denom_div_dvd _ _
  have hdegG := natDegree_le_of_dvd hleft F.U_ne
  have hnf : f.num.natDegree < 131072 + F.s + f.denom.natDegree := by
    by_cases hzero : f.num = 0
    · simp [hzero]
    have hy : leftLift ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at heq
      exact mul_ne_zero hzero F.U_ne heq
    have h := congrArg natDegree heq
    rw [natDegree_mul hzero F.U_ne, natDegree_mul hy f.denom_ne_zero] at h
    dsimp [d] at hY
    omega
  have heq' : f.denom.map twist * rightLift = f.num.map twist * F.V := by
    apply eq_on_puncture (deleted := deleted) (d := d+F.U.natDegree) (by dsimp [d]; omega)
    · apply natDegree_mul_le.trans_lt
      have hg : (f.denom.map twist).natDegree ≤ f.denom.natDegree := natDegree_map_le
      omega
    · apply natDegree_mul_le.trans_lt
      have hg : (f.num.map twist).natDegree ≤ f.num.natDegree := natDegree_map_le
      have hh := F.degrees_eq
      dsimp [d]
      omega
    · intro i hi
      simp only [eval_mul, eval_twist, hn i hi, hZn i hi, map_mul]
      ring
  have hcop : IsCoprime (f.denom.map twist) (f.num.map twist) :=
    f.isCoprime_num_denom.symm.map (Polynomial.mapRingHom twist)
  exact ⟨⟨f.denom, f.num, f.monic_denom, hleft,
    hcop.dvd_of_dvd_mul_left (by rw [← heq']; exact dvd_mul_right _ _),
    degree_le_natDegree.trans_lt (by exact_mod_cast hnf), hn⟩⟩

end
end K21_12
end Port_K1_12Lift

section Port_K1_12Offset
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace K21_12
noncomputable section
open Polynomial K21 FrobeniusLocator ProximityPrize.Benchmark

theorem offset_of_anchor {u deleted} (F : Direction u deleted) (H : CrossLift F)
    {η : K} (m : BadMark u η) (avoid : Disjoint m.support deleted) (reg : Regular F η) :
    Nonempty (Offset F m) := by
  classical
  let a := F.amp η
  let w (i : I) := u 0 i + η * u 1 i
  let r (j : Fin 2) := F.out 0 j + C (twist η) * F.out 1 j
  let out := r 0 + C η * r 1
  let d := 131072 + F.U.natDegree + F.s
  have hheight := F.height
  change F.U.natDegree + F.s + deleted.card ≤ 32872 at hheight
  have hpos : 0 < d := by dsimp [d]; omega
  have hA1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  have ha : a.natDegree = F.s := reg.degree_eq
  have ha' : (a.map twist).natDegree ≤ F.s := natDegree_map_le.trans ha.le
  have hr (j : Fin 2) : (r j).natDegree < d := by
    apply (natDegree_add_le _ _).trans_lt
    exact max_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 0 j))
      ((natDegree_C_mul_le _ _).trans_lt (natDegree_lt_of_degree_lt_pos hpos (F.out_degree 1 j)))
  have hout : out.natDegree < d := (natDegree_add_le _ _).trans_lt
    (max_lt (hr 0) ((natDegree_C_mul_le _ _).trans_lt (hr 1)))
  have hrn (j : Fin 2) (i : I) (hi : i ∉ deleted) : (r j).eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * u j i -
      F.V.eval (node i) * (F.A j).eval (node i) * twist (w i) := by
    simp only [r, w, a, Direction.amp, eval_twist, eval_add, eval_mul, eval_C,
      F.nodes i hi, eval_twist, map_add, map_mul]
    ring
  have hspec (i : I) (hi : i ∉ deleted) : out.eval (node i) =
      F.U.eval (node i) * (a.map twist).eval (node i) * w i -
      F.V.eval (node i) * a.eval (node i) * twist (w i) := by
    simp only [out, eval_add, eval_mul, eval_C, hrn _ i hi, a, Direction.amp, w, eval_add,
      eval_mul, eval_C]
    ring
  have hp := natDegree_lt_of_degree_lt_pos (by decide : 0 < 131072) m.degree
  have ident : F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist = out := by
    let left := F.U * a.map twist * m.decoder - F.V * a * m.decoder.map twist
    have hdeg : left.natDegree < d := by
      apply (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · apply natDegree_mul_le.trans_lt
        have h : (F.U * a.map twist).natDegree ≤ F.U.natDegree + (a.map twist).natDegree :=
          natDegree_mul_le
        dsimp [d]; omega
      · apply natDegree_mul_le.trans_lt
        have h : (F.V*a).natDegree ≤ F.V.natDegree+a.natDegree := natDegree_mul_le
        have h' : (m.decoder.map twist).natDegree ≤ m.decoder.natDegree := natDegree_map_le
        have := F.degrees_eq
        dsimp [d]; omega
    apply sub_eq_zero.mp
    by_contra hne
    have hc := Strata.root_nodes_card_le node IRSProfile.domain.injective (left-out) hne m.support
      (by intro i hi
          rw [eval_sub, hspec i (Finset.disjoint_left.mp avoid hi)]
          simp only [left, eval_sub, eval_mul, eval_twist, m.hits i hi, w, sub_self])
    have hd := natDegree_sub_le left out
    have hag := m.agreement
    dsimp [d] at hdeg hout
    omega
  have hG := natDegree_le_of_dvd H.left F.U_ne
  have hLd := natDegree_lt_of_degree_lt_pos (by omega : 0 < 131072+F.s+H.G.natDegree) H.degree_lt
  have determinant : H.G * (a * r 1 - F.A 1 * out) = F.U * a.map twist * H.L := by
    apply eq_on_puncture (deleted := deleted) (d := d+F.s+H.G.natDegree) (by dsimp [d]; omega)
    · apply natDegree_mul_le.trans_lt
      have h1 := @natDegree_mul_le _ _ a (r 1)
      have h2 := @natDegree_mul_le _ _ (F.A 1) out
      have h3 := natDegree_sub_le (a*r 1) (F.A 1*out)
      have := hr 1
      omega
    · apply natDegree_mul_le.trans_lt
      have h := @natDegree_mul_le _ _ F.U (a.map twist)
      dsimp [d]; omega
    · intro i hi
      simp only [eval_mul, eval_sub, hrn 1 i hi, hspec i hi, H.nodes i hi, a, Direction.amp,
        eval_add, eval_mul, eval_C, w]
      ring
  have div : a ∣ H.L + H.G * F.A 1 * m.decoder := by
    have cop : IsCoprime a (F.U * a.map twist) :=
      reg.content_unit.mul_right reg.adjacent
    apply cop.dvd_of_dvd_mul_left
    refine ⟨H.G * (r 1 + F.A 1 * F.V * m.decoder.map twist), ?_⟩
    linear_combination H.G * F.A 1 * ident - determinant
  obtain ⟨J,hJ⟩ := div
  have hjd : J.natDegree < 131072 + H.G.natDegree := by
    by_cases hj : J = 0
    · simp [hj]
    have h := natDegree_add_le H.L (H.G * F.A 1 * m.decoder)
    rw [hJ, natDegree_mul reg.amp_ne hj, ha] at h
    have h1 := @natDegree_mul_le _ _ H.G (F.A 1)
    have h2 := @natDegree_mul_le _ _ (H.G * F.A 1) m.decoder
    omega
  let f : RatFunc K := algebraMap K[X] (RatFunc K) J / algebraMap K[X] (RatFunc K) H.G
  have hfrac : f.num * H.G = J * f.denom := (RatFunc.num_mul_eq_mul_denom_iff H.monic.ne_zero).mpr rfl
  have hE : f.denom ∣ H.G := RatFunc.denom_div_dvd _ _
  let Q := f.num %ₘ f.denom
  let pencil := f.num /ₘ f.denom
  have division : Q + f.denom * pencil = f.num := modByMonic_add_div _ _
  have hn : f.num.natDegree < 131072 + f.denom.natDegree := by
    by_cases hn : f.num = 0
    · simp [hn]
    have hj : J ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hfrac
      exact mul_ne_zero hn H.monic.ne_zero hfrac
    have h := congrArg natDegree hfrac
    rw [natDegree_mul hn H.monic.ne_zero, natDegree_mul hj f.denom_ne_zero] at h
    omega
  have hpencil : pencil.degree < 131072 := by
    have hd : pencil.natDegree < 131072 := by
      rw [show pencil.natDegree = f.num.natDegree - f.denom.natDegree from
        natDegree_divByMonic _ f.monic_denom]
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hd)
  let raw (i : I) := F.den.eval (node i) * (w i - m.decoder.eval (node i)) / a.eval (node i)
  have hUn (i : I) := eval_unit_of_dvd F.U_dvd (F.den_nodes i)
  have hfixed (i : I) (hi : i ∉ deleted) : twist (raw i) = raw i := by
    have h1 := congrArg (eval (node i)) ident
    simp only [eval_sub, eval_mul, eval_twist, hspec i hi, eval_twist] at h1
    have h2 := congrArg (eval (node i)) F.phase
    simp only [eval_mul, eval_twist] at h2
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    have haσ : twist (a.eval (node i)) ≠ 0 := (map_ne_zero twist).mpr ha0
    simp only [raw, map_div₀, map_mul, map_sub]
    apply (div_eq_div_iff haσ ha0).mpr
    apply mul_left_cancel₀ (hUn i)
    linear_combination F.den.eval (node i) * h1 +
      a.eval (node i) * (twist (w i) - twist (m.decoder.eval (node i))) * h2
  refine ⟨{
    pencil := pencil
    pencil_degree := hpencil
    E := f.denom
    Q := Q
    E_monic := f.monic_denom
    left := hE.trans H.left
    right := (map_dvd (Polynomial.mapRingHom twist) hE).trans H.right
    proper := degree_modByMonic_lt _ f.monic_denom
    reduced := ?_
    raw := raw
    raw_fixed := hfixed
    first := ?_
    second := ?_ }⟩
  · obtain ⟨x,y,h⟩ := f.isCoprime_num_denom
    rw [← division] at h
    exact ⟨x,x*pencil+y,by linear_combination h⟩
  · intro i hi
    change w i - m.decoder.eval (node i) = a.eval (node i) * raw i / F.den.eval (node i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    simp only [raw]
    field_simp [ha0, F.den_nodes i]
  · intro i hi
    have h1 := congrArg (eval (node i)) hJ
    simp only [eval_add, eval_mul, H.nodes i hi] at h1
    have h2 := congrArg (eval (node i)) hfrac
    simp only [eval_mul, ← division, eval_add, eval_mul] at h2
    have hEn := eval_unit_of_dvd ((hE.trans H.left).trans F.U_dvd) (F.den_nodes i)
    have hGn := eval_unit_of_dvd (H.left.trans F.U_dvd) (F.den_nodes i)
    have ha0 : a.eval (node i) ≠ 0 := reg.node_unit i hi
    change u 1 i - pencil.eval (node i) = Q.eval (node i) / f.denom.eval (node i) +
      (F.A 1).eval (node i) * raw i / F.den.eval (node i)
    simp only [raw]
    field_simp [F.den_nodes i, hEn, ha0]
    apply mul_left_cancel₀ hGn
    have h3 : a.eval (node i) = (F.A 0).eval (node i) + η * (F.A 1).eval (node i) := by
      simp only [a,Direction.amp,eval_add,eval_mul,eval_C]
    dsimp [w]
    linear_combination f.denom.eval (node i) * h1 - a.eval (node i) * h2 +
      f.denom.eval (node i) * H.G.eval (node i) * u 1 i * h3

end
end K21_12
end Port_K1_12Offset

section Port_K1_12Family
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace K21_12
noncomputable section

open Polynomial K21 FrobeniusLocator

/-- A second decoder with the same scalar explains its own affine
combination on the FIRST decoder's support as well. -/
private theorem other_hits {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) (i : I) (hi : i ∈ m.bad.support) :
    n.bad.decoder.eval (node i) = u 0 i + δ * u 1 i := by
  have hd := Finset.disjoint_left.mp m.avoids_deleted hi
  have h0 := M.first_word i hd
  have h1 := M.second_word i hd
  have h := congrArg (eval (node i)) n.identity
  simp only [AnchorModel.decoder, AnchorModel.amplitude, AnchorModel.label, eval_sub,
    eval_mul, eval_C, eval_add, m.scalar_hits i hi] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show M.E.eval (node i) * _ = 0 from ?_)).resolve_left (M.E_nodes i)
  linear_combination h - h0 - (δ - M.shift) * h1

theorem same_scalar_label {u deleted} {M : AnchorModel u deleted} {γ δ : K} {S : K[X]}
    (m : AnchorMark M γ S) (n : AnchorMark M δ S) : γ = δ := by
  by_contra hne
  let V := (δ-γ)⁻¹ • (n.bad.decoder - m.bad.decoder)
  have hd : δ-γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hV : V.degree < 131072 := Principal.degree_smul_lt _
    (Principal.degree_sub_lt n.bad.degree m.bad.degree)
  have hv (i : I) (hi : i ∈ m.bad.support) : V.eval (node i) = u 1 i := by
    simp only [V, eval_smul, eval_sub, smul_eq_mul, other_hits m n i hi, m.bad.hits i hi]
    field_simp [hd]
    ring
  apply m.bad.nonjoint
  refine ⟨⟨m.bad.decoder - γ • V, Principal.degree_sub_lt m.bad.degree
    (Principal.degree_smul_lt _ hV), ?_⟩, ⟨V, hV, hv⟩⟩
  intro i hi
  simp only [eval_sub, eval_smul, smul_eq_mul, m.bad.hits i hi, hv i hi]
  ring

private theorem coprime_factor_of_label {E Q P c a S : K[X]} {z : K} (hz : z ≠ 0)
    (reduced : IsCoprime Q E) (hid : E * P - C z * Q = c * a * S) :
    IsCoprime E c := by
  obtain ⟨x,y,hxy⟩ := reduced
  have inv : C z⁻¹ * C z = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hz, C_1]
  have eqQ : Q = C z⁻¹ * (E * P - c * a * S) := by
    have he : C z * Q = E * P - c * a * S := by linear_combination -hid
    rw [← he, ← mul_assoc, inv, one_mul]
  rw [eqQ] at hxy
  exact ⟨x * C z⁻¹ * P + y, -(x * C z⁻¹ * a * S), by linear_combination hxy⟩

theorem family_of_offset {u deleted} (F : Direction u deleted) (Γ : Finset K)
    (reg : ∀ γ ∈ Γ, Regular F γ) (m : ∀ g : Γ, BadMark u g.val)
    (avoid : ∀ g, Disjoint (m g).support deleted) (η ζ : Γ) (hne : ζ.val ≠ η.val)
    (O : Offset F (m η)) : ∃ M : AnchorModel u deleted, Nonempty (AnchoredFamily M Γ) := by
  classical
  obtain ⟨W,hW⟩ := O.left.trans F.U_dvd
  have hWn (i : I) : W.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hW ▸ dvd_mul_left W O.E) (F.den_nodes i)
  obtain ⟨L,c,hL,hLf,hLn,hsplit⟩ := invariant_multiple W hWn
  have hcn (i : I) : c.eval (node i) ≠ 0 :=
    eval_unit_of_dvd (hL ▸ dvd_mul_left c W) (hLn i)
  have hscalar (g : Γ) : ∃ S : K[X], S.map twist = S ∧
      O.numerator (m g) = c * F.amp g.val * S := by
    obtain ⟨N, hN, hfix⟩ := O.fixed_numerator W hW (m g) (avoid g) (reg g.val g.property)
    obtain ⟨S,hS,hNS⟩ := hsplit N hfix
    exact ⟨S,hS,by rw [hN,hNS]; ring⟩
  choose S hS ident using hscalar
  let word (i : I) := if i ∈ deleted then 0 else O.raw i / L.eval (node i)
  have hword (i : I) (hi : i ∉ deleted) : word i = O.raw i / L.eval (node i) := by simp [word, hi]
  have hden (i : I) : F.den.eval (node i) = O.E.eval (node i) * W.eval (node i) := by
    rw [hW, eval_mul]
  have hLval (i : I) : L.eval (node i) = W.eval (node i) * c.eval (node i) := by rw [hL, eval_mul]
  have hs : amplitudeDegree (F.amp η.val) (F.A 1) = F.s := by
    unfold amplitudeDegree
    rw [(reg η.val η.property).degree_eq]
    exact max_eq_left (le_max_right _ _)
  have hcop : IsCoprime O.E c := coprime_factor_of_label (sub_ne_zero.mpr hne) O.reduced (ident ζ)
  let M : AnchorModel u deleted := {
    shift := η.val
    pencil₀ := (m η).decoder
    pencil₁ := O.pencil
    pencil₀_degree := (m η).degree
    pencil₁_degree := O.pencil_degree
    E := O.E
    factor := c
    Q := O.Q
    A₀ := F.amp η.val
    A₁ := F.A 1
    word := word
    word_fixed := by
      intro i
      by_cases hi : i ∈ deleted
      · simp [word,hi]
      · rw [hword i hi, map_div₀, O.raw_fixed i hi, ← eval_twist L i, hLf]
    word_deleted := fun i hi => by simp [word, hi]
    E_monic := O.E_monic
    E_nodes := O.E_nodes
    factor_nodes := fun i _ => hcn i
    coprime_factor := hcop
    offset_proper := O.proper
    offset_reduced := O.reduced
    adjacent_coprime := F.coprime.mono O.left O.right
    amplitudes_primitive := by
      obtain ⟨x,y,hxy⟩ := F.primitive
      exact ⟨x,y - x*C η.val,by unfold Direction.amp; linear_combination hxy⟩
    first_amplitude_unit := (reg η.val η.property).content_unit.of_isCoprime_of_dvd_right O.left
    height_bound := by
      rw [hs]
      have h := F.height
      change F.U.natDegree + F.s + deleted.card ≤ 32872 at h
      have hd := natDegree_le_of_dvd O.left F.U_ne
      omega
    first_word := by
      intro i hi
      rw [O.first i hi, hword i hi]
      field_simp [F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring
    second_word := by
      intro i hi
      rw [O.second i hi, hword i hi]
      field_simp [O.E_nodes i, F.den_nodes i, hLn i]
      rw [hden, hLval]
      ring }
  have amp_eq (g : Γ) : M.amplitude g.val = F.amp g.val := by
    change F.amp η.val + C (g.val-η.val) * F.A 1 = F.amp g.val
    simp only [Direction.amp, map_sub]
    ring
  let scalar (γ : K) := if h : γ ∈ Γ then S ⟨γ,h⟩ else 0
  have marks (g : Γ) : AnchorMark M g.val (scalar g.val) := by
    have hreg := reg g.val g.property
    rw [show scalar g.val = S g by simp [scalar, g.property]]
    refine {
      bad := m g
      avoids_deleted := avoid g
      scalar_fixed := hS g
      scalar_degree := ?_
      scalar_hits := ?_
      pole_unit := ?_
      identity := ?_ }
    · by_cases hz : S g = 0
      · exact Or.inl hz
      right
      have hc : c ≠ 0 := fun h => hcn 0 (by rw [h, eval_zero])
      have hd := O.numerator_degree (m g)
      rw [ident g, natDegree_mul (mul_ne_zero hc hreg.amp_ne) hz,
        natDegree_mul hc hreg.amp_ne, hreg.degree_eq] at hd
      change (S g).natDegree ≤ (131071 : ℤ) + (O.E.natDegree - c.natDegree -
        (amplitudeDegree (F.amp η.val) (F.A 1) : ℤ))
      rw [hs]
      omega
    · intro i hi
      have hits := O.hits W hW (m g) (avoid g) i hi
      rw [ident g, eval_mul, eval_mul] at hits
      change (S g).eval (node i) = word i
      have hd := Finset.disjoint_left.mp (avoid g) hi
      rw [hword i hd, eq_div_iff (hLn i), hLval]
      apply mul_left_cancel₀ (hreg.node_unit i hd)
      linear_combination hits
    · rw [amp_eq]
      exact hreg.content_unit.of_isCoprime_of_dvd_right O.left
    · rw [amp_eq]
      exact ident g
  refine ⟨M, ⟨⟨scalar, fun γ hγ => marks ⟨γ,hγ⟩, ?_⟩⟩⟩
  intro γ hγ δ hδ h
  exact same_scalar_label (marks ⟨γ,hγ⟩) (h ▸ marks ⟨δ,hδ⟩)

end
end K21_12
end Port_K1_12Family

section Port_K1_12Split
set_option autoImplicit true
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace K21_12
noncomputable section

open Polynomial K21

/-- Extract the normalized homogeneous rational direction on the actual puncture. -/
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    (∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) →
    Nonempty (Direction u (fixedNodes R))

/-- The resultant, reduced left content, domain-node, and leading-coefficient exclusions. -/
def c2 : Prop :=
  ∀ {u deleted} (F : Direction u deleted) (Γ : Finset K),
    (excluded F Γ).card ≤ (p+1) * F.s + F.U.natDegree + 262144 + 1

theorem of_children (h1 : c1) (h2 : c2) : K21.c12 := by
  classical
  intro u hu T R D B sat par unit Γ bad normal
  by_cases hsmall : Γ.card ≤ 70040582193466
  · exact Or.inl hsmall
  right
  obtain ⟨γ,hγ⟩ := Finset.card_pos.mp (show 0 < Γ.card by omega)
  obtain ⟨F⟩ := h1 u hu T R D B sat par unit ⟨γ, normal γ hγ, bad_mark u Γ bad γ hγ⟩
  let book := excluded F Γ
  have hbook : book ⊆ Γ := Finset.filter_subset _ _
  have hcard := h2 F Γ
  change book.card ≤ 2130706434 * F.s + F.U.natDegree + 262144 + 1 at hcard
  have hbudget : book.card + 1 ≤ 70040582193466 := by
    have height := F.height
    change F.U.natDegree + F.s + (fixedNodes R).card ≤ 32872 at height
    omega
  let Δ := Γ \ book
  have hbig : 1 < Δ.card := by
    have hpart := Finset.card_sdiff_add_card_eq_card hbook
    change Δ.card + book.card = Γ.card at hpart
    omega
  have regular (δ : K) (hd : δ ∈ Δ) : Regular F δ := by
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hd
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨hin,h⟩)
  let m (g : Δ) := Classical.choice (bad_mark u Γ bad g.val (Finset.mem_sdiff.mp g.property).1)
  have avoid (g : Δ) : Disjoint (m g).support (fixedNodes R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hid
    exact (D.deleted_error g.val (normal g.val (Finset.mem_sdiff.mp g.property).1) (m g) i hid)
      ((m g).hits i hi)
  obtain ⟨η,hη,ζ,hζ,hne⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨lift⟩ := cross_lift F
  obtain ⟨O⟩ := offset_of_anchor F lift (m ⟨η,hη⟩) (avoid ⟨η,hη⟩) (regular η hη)
  exact ⟨book, hbook, by omega, family_of_offset F Δ regular m avoid ⟨η,hη⟩ ⟨ζ,hζ⟩ hne.symm O⟩

end
end K21_12
end Port_K1_12Split

section Port_K1_12_1Descent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

namespace K21_12_1
noncomputable section

open Polynomial K21 ProximityPrize.Benchmark

section Cyclic

variable {F : Type*} [Field F] {q : ℕ} [ExpChar F q]

private def conjugate (q n : ℕ) [ExpChar F q] (P : F[X]) : F[X] :=
  P.map (iterateFrobenius F q n)

private theorem conjugate_zero (P : F[X]) : conjugate q 0 P = P := by simp [conjugate]

private theorem conjugate_succ (n : ℕ) (P : F[X]) :
    (conjugate q n P).map (frobenius F q) = conjugate q (n + 1) P := by
  rw [conjugate, conjugate, map_map, add_comm n 1,
    iterateFrobenius_add F q 1 n, iterateFrobenius_one]

variable [Fintype F]

private theorem conjugate_six (card : Fintype.card F = q ^ 6) (P : F[X]) :
    conjugate q 6 P = P := by
  have hs : iterateFrobenius F q 6 = RingHom.id F := by
    apply RingHom.ext
    intro x
    change x ^ q ^ 6 = x
    rw [← card]
    exact FiniteField.pow_card x
  rw [conjugate, hs, map_id]

/-- The six weights of the cyclic sum, with polynomial denominators cleared. -/
private def weights {S : Type*} [CommSemiring S] (A B : ℕ → S) (j : Fin 6) : S :=
  ∏ i : Fin 6, if i.val < j.val then A i.val else B i.val

private theorem weights_cycle {S : Type*} [CommSemiring S] (f : S →+* S) (A B : ℕ → S)
    (ha : ∀ n, f (A n) = A (n+1)) (hb : ∀ n, f (B n) = B (n+1))
    (hB : B 6 = B 0)
    (h : (∏ i : Fin 6, A i.val) = ∏ i : Fin 6, B i.val) (j : Fin 6) :
    A 0 * f (weights A B j) = B 0 * weights A B (j + 1) := by
  rw [Fin.prod_univ_six, Fin.prod_univ_six] at h
  change A 0 * A 1 * A 2 * A 3 * A 4 * A 5 = B 0 * B 1 * B 2 * B 3 * B 4 * B 5 at h
  fin_cases j <;> simp only [weights, Fin.prod_univ_six, Fin.add_def] <;>
    norm_num [ha, hb, hB]
  all_goals first | ac_rfl | (rw [← h]; ac_rfl)

private theorem frobenius_cycle (card : Fintype.card F = q ^ 6) (x : F) (j : Fin 6) :
    frobenius F q (x ^ q ^ j.val) = x ^ q ^ (j + 1).val := by
  have hpow : frobenius F q (x ^ q ^ j.val) = x ^ q ^ (j.val + 1) := by
    change (x ^ q ^ j.val) ^ q = _
    rw [← pow_mul, pow_succ q j.val]
  rw [hpow]
  by_cases hj : j.val = 5
  · have hj' : j = 5 := Fin.ext hj
    rw [hj', show (5 : Fin 6) + 1 = 0 by decide]
    change x ^ q ^ 6 = x ^ q ^ 0
    rw [pow_zero, pow_one, ← card, FiniteField.pow_card]
  · have hv : (j + 1).val = j.val + 1 := by
      change (j.val + 1) % 6 = j.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hv]

private theorem descent_nonzero (card : Fintype.card F = q ^ 6) (hq : 1 < q)
    {a b : F[X]} (hb : b ≠ 0)
    (h : (∏ i : Fin 6, conjugate q i.val a) = ∏ i : Fin 6, conjugate q i.val b) :
    ∃ Q : F[X], Q ≠ 0 ∧ a * Q.map (frobenius F q) = b * Q := by
  classical
  let W := weights (fun n => conjugate q n a) (fun n => conjugate q n b)
  let S : Polynomial F[X] := ∑ j : Fin 6, monomial (q ^ j.val) (W j)
  have hinj : Function.Injective (fun j : Fin 6 => q ^ j.val) := by
    intro i j hij
    exact Fin.ext ((pow_right_injective₀ (by omega : 0 < q) (ne_of_gt hq)) hij)
  have hW : W 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    change (if j.val < 0 then conjugate q j.val a else conjugate q j.val b) ≠ 0
    rw [ite_eq_right (Nat.not_lt_zero _)]
    exact (Polynomial.map_ne_zero_iff (iterateFrobenius F q j.val).injective).mpr hb
  have hS : S ≠ 0 := by
    intro hz
    apply hW
    have hc := congrArg (fun P : Polynomial F[X] => P.coeff (q ^ (0 : Fin 6).val)) hz
    simpa only [S, finsetSum_coeff, coeff_monomial, hinj.eq_iff, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, coeff_zero] using hc
  have hdeg : S.natDegree ≤ q ^ 5 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact natDegree_monomial_le _ |>.trans
      (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ 5))
  obtain ⟨x, hx⟩ : ∃ x : F, S.eval (C x) ≠ 0 := by
    by_contra! hall
    have hroots : (Finset.univ.map ⟨C, C_injective⟩ : Finset F[X]).val ⊆ S.roots := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_def.mpr hy)
      exact (mem_roots hS).mpr (hall x)
    have hcount := card_le_degree_of_subset_roots hroots
    rw [Finset.card_map, Finset.card_univ, card] at hcount
    exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 5 < 6))) (hcount.trans hdeg)
  refine ⟨S.eval (C x), hx, ?_⟩
  have hev : S.eval (C x) = ∑ j : Fin 6, W j * C (x ^ q ^ j.val) := by
    simp only [S, eval_finsetSum, eval_monomial, C_pow]
  have hstep (j : Fin 6) : a * (W j).map (frobenius F q) = b * W (j+1) := by
    change a * mapRingHom (frobenius F q) (W j) = b * W (j+1)
    simpa only [conjugate_zero] using
      weights_cycle (mapRingHom (frobenius F q)) _ _ (fun n => conjugate_succ n a)
        (fun n => conjugate_succ n b)
        ((conjugate_six card b).trans (conjugate_zero b).symm) h j
  rw [hev, Polynomial.map_sum, Finset.mul_sum, Finset.mul_sum]
  simp_rw [Polynomial.map_mul, map_C, ← mul_assoc, hstep, frobenius_cycle card]
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 6)) _ _ (fun _ => rfl)

end Cyclic

/-- A polynomial solution of least degree is a unit at all fixed domain nodes. -/
theorem denominator {a b : K[X]} (hb : b ≠ 0) (h : sixNorm a = sixNorm b) :
    ∃ Q : K[X], Q ≠ 0 ∧ a * Q.map twist = b * Q ∧ ∀ i, Q.eval (node i) ≠ 0 := by
  classical
  let P (d : ℕ) := ∃ Q : K[X], Q ≠ 0 ∧ a * Q.map twist = b * Q ∧ Q.natDegree = d
  have hex : ∃ d, P d := by
    obtain ⟨Q, hQ, hphase⟩ := descent_nonzero (F := K) (q := p) KoalaBear.card_ext6 (by decide) hb h
    exact ⟨Q.natDegree, Q, hQ, hphase, rfl⟩
  obtain ⟨Q, hQ, hphase, hdeg⟩ := Nat.find_spec hex
  refine ⟨Q, hQ, hphase, ?_⟩
  intro i hi
  let L : K[X] := Polynomial.X (R := K) - C (node i)
  have hL : L ≠ 0 := X_sub_C_ne_zero (node i)
  have hfix : L.map twist = L := by simp [L, K21_12.twist_node]
  obtain ⟨R, hR⟩ := (dvd_iff_isRoot.mpr hi : L ∣ Q)
  have hR0 : R ≠ 0 := fun hz => hQ (by rw [hR, hz, mul_zero])
  have hphaseR : a * R.map twist = b * R := by
    apply mul_left_cancel₀ hL
    rw [hR, Polynomial.map_mul, hfix] at hphase
    rw [← mul_left_comm L a, ← mul_left_comm L b] at hphase
    exact hphase
  have hmin := Nat.find_min' hex (show P R.natDegree from ⟨R, hR0, hphaseR, rfl⟩)
  rw [hR, natDegree_mul hL hR0, show L.natDegree = 1 from natDegree_X_sub_C _] at hdeg
  omega

end
end K21_12_1
end Port_K1_12_1Descent

section Port_K1_12_2Proof
set_option autoImplicit true
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

namespace K21_12_2
noncomputable section

open Polynomial K21 K21_12
open ProximityPrize.Benchmark
open scoped BigOperators

variable {u : Words} {deleted : Finset I}

private theorem coprime_amplitudes (F : Direction u deleted) {γ δ : K} (hne : γ ≠ δ) :
    IsCoprime (F.amp γ) (F.amp δ) := by
  have hd : F.amp δ - F.amp γ * 1 = C (δ - γ) * F.A 1 := by
    simp only [Direction.amp, mul_one, map_sub]
    ring
  have hunit : IsUnit (C (δ - γ)) :=
    isUnit_C.mpr (sub_ne_zero.mpr hne.symm).isUnit
  apply (IsCoprime.sub_mul_left_right_iff (x := F.amp γ) (y := F.amp δ) (z := 1)).mp
  rw [hd, isCoprime_mul_unit_left_right hunit]
  exact F.primitive.add_mul_right_left _

/-- Each failed coprimality test contributes a positive-degree factor of the
same nonzero polynomial. The factors are coprime across distinct labels. -/
private theorem card_of_failed_coprime (F : Direction u deleted) (S : Finset K)
    (Q : K → K[X]) {P : K[X]} (hP : P ≠ 0)
    (hbad : ∀ γ ∈ S, ¬ IsCoprime (F.amp γ) (Q γ))
    (hdiv : ∀ γ ∈ S, GCDMonoid.gcd (F.amp γ) (Q γ) ∣ P) :
    S.card ≤ P.natDegree := by
  classical
  let g (γ : K) := GCDMonoid.gcd (F.amp γ) (Q γ)
  have hne (γ : K) (hγ : γ ∈ S) : g γ ≠ 0 := by
    intro hz
    obtain ⟨H, hH⟩ := hdiv γ hγ
    change P = g γ * H at hH
    exact hP (by simpa only [hz, zero_mul] using hH)
  have hpos (γ : K) (hγ : γ ∈ S) : 1 ≤ (g γ).natDegree := by
    by_contra! h
    have hd : (g γ).natDegree = 0 := by omega
    have hu : IsUnit (g γ) := isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree (hne γ hγ), hd]
      rfl)
    exact hbad γ hγ ((gcd_isUnit_iff _ _).mp hu)
  have hpairs : (S : Set K).Pairwise (fun γ δ => IsCoprime (g γ) (g δ)) := by
    intro γ _ δ _ hne
    exact (coprime_amplitudes F hne).mono (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have hprod : (∏ γ ∈ S, g γ) ∣ P := Finset.prod_dvd_of_coprime hpairs hdiv
  calc
    S.card = ∑ γ ∈ S, (1 : ℕ) := by simp
    _ ≤ ∑ γ ∈ S, (g γ).natDegree := Finset.sum_le_sum hpos
    _ = (∏ γ ∈ S, g γ).natDegree := (natDegree_prod S g hne).symm
    _ ≤ P.natDegree := natDegree_le_of_dvd hprod hP

/-- Eliminate the label from an amplitude and its coefficient Frobenius
conjugate by taking the p-th power of the first amplitude. -/
private def eliminant (F : Direction u deleted) (q : ℕ) (σ : K →+* K) : K[X] :=
  ((F.A 0).map σ) * F.A 1 ^ q - (F.A 0 ^ q) * ((F.A 1).map σ)

private theorem gcd_dvd_eliminant (F : Direction u deleted) (q : ℕ) [ExpChar K q]
    (σ : K →+* K) (hσ : ∀ γ, σ γ = γ ^ q) (hq : q ≠ 0) (γ : K) :
    GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ eliminant F q σ := by
  have hpow : (F.amp γ)^q = F.A 0 ^ q + C (σ γ) * F.A 1 ^ q := by
    rw [Direction.amp, add_pow_expChar _ _ q, mul_pow, ← C_pow, ← hσ γ]
  have heq : eliminant F q σ =
      ((F.amp γ).map σ) * F.A 1 ^ q - (F.amp γ)^q * ((F.A 1).map σ) := by
    rw [hpow]
    simp only [eliminant, Direction.amp, Polynomial.map_add, Polynomial.map_mul, map_C]
    ring
  have hd : GCDMonoid.gcd (F.amp γ) ((F.amp γ).map σ) ∣ F.amp γ :=
    gcd_dvd_left _ _
  rw [heq]
  exact dvd_sub ((gcd_dvd_right _ _).mul_right _)
    ((hd.trans (dvd_pow_self _ hq)).mul_right _)

private theorem degree_zero_of_power_dvd_map {q : ℕ} (hq : 2 ≤ q) {σ : K →+* K}
    {P : K[X]} (hdiv : P ^ q ∣ P.map σ) : P.natDegree = 0 := by
  by_cases hP : P = 0
  · simp [hP]
  have h := natDegree_le_of_dvd hdiv (Polynomial.map_ne_zero hP)
  rw [natDegree_pow, natDegree_map_eq_of_injective σ.injective] at h
  have htwo := (Nat.mul_le_mul_right P.natDegree hq).trans h
  omega

private theorem eliminant_ne (F : Direction u deleted) {q : ℕ} (hq : 2 ≤ q)
    (σ : K →+* K) (hs : F.s ≠ 0) : eliminant F q σ ≠ 0 := by
  intro hz
  have hcross : ((F.A 0).map σ) * F.A 1 ^ q = F.A 0 ^ q * ((F.A 1).map σ) :=
    sub_eq_zero.mp hz
  have hp : IsCoprime (F.A 0 ^ q) (F.A 1 ^ q) := F.primitive.pow
  have h0 : F.A 0 ^ q ∣ (F.A 0).map σ := hp.dvd_of_dvd_mul_right
    (by rw [hcross]; exact dvd_mul_right _ _)
  have h1 : F.A 1 ^ q ∣ (F.A 1).map σ := hp.symm.dvd_of_dvd_mul_left
    (by rw [← hcross]; exact dvd_mul_left _ _)
  exact hs (by simp [Direction.s, amplitudeDegree, degree_zero_of_power_dvd_map hq h0,
    degree_zero_of_power_dvd_map hq h1])

private theorem eliminant_degree (F : Direction u deleted) (q : ℕ) (σ : K →+* K) :
    (eliminant F q σ).natDegree ≤ (q + 1) * F.s := by
  have h0 : (F.A 0).natDegree ≤ F.s := le_max_left _ _
  have h1 : (F.A 1).natDegree ≤ F.s := le_max_right _ _
  rw [eliminant, Nat.add_mul, one_mul]
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [add_comm]
    exact natDegree_mul_le_of_le (natDegree_map_le.trans h0) (natDegree_pow_le_of_le q h1)
  · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le q h0) (natDegree_map_le.trans h1)

private theorem same_label {a b γ δ : K} (hpair : a ≠ 0 ∨ b ≠ 0)
    (hγ : a + γ * b = 0) (hδ : a + δ * b = 0) : γ = δ := by
  have hb : b ≠ 0 := by
    intro hz
    exact hpair.elim (fun ha => ha (by simpa [hz] using hγ)) (fun hb => hb hz)
  apply sub_eq_zero.mp
  refine (mul_eq_zero.mp (show (γ - δ) * b = 0 from ?_)).resolve_right hb
  linear_combination hγ - hδ

private theorem top_pair (F : Direction u deleted) :
    (F.A 0).coeff F.s ≠ 0 ∨ (F.A 1).coeff F.s ≠ 0 := by
  have at_top (P : K[X]) (hp : P ≠ 0) (hd : P.natDegree = F.s) :
      P.coeff F.s ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  by_cases h0 : F.A 0 = 0
  · exact Or.inr (at_top _ (F.primitive.ne_zero_or_ne_zero.resolve_left (by simp [h0]))
      (by simp [Direction.s, amplitudeDegree, h0]))
  by_cases h1 : F.A 1 = 0
  · exact Or.inl (at_top _ h0 (by simp [Direction.s, amplitudeDegree, h1]))
  rcases le_total (F.A 0).natDegree (F.A 1).natDegree with h | h
  · exact Or.inr (at_top _ h1 (max_eq_right h).symm)
  · exact Or.inl (at_top _ h0 (max_eq_left h).symm)

private theorem amp_degree_le (F : Direction u deleted) (γ : K) :
    (F.amp γ).natDegree ≤ F.s :=
  natDegree_add_le_of_degree_le (le_max_left _ _)
    ((natDegree_C_mul_le _ _).trans (le_max_right _ _))

private theorem card_node_failures (F : Direction u deleted) (S : Finset K)
    (hS : ∀ γ ∈ S, ∃ i : I, (F.amp γ).eval (node i) = 0) : S.card ≤ 262144 := by
  classical
  choose f hf using fun γ : S => hS γ γ.property
  rw [← IRSProfile.card_index, ← Fintype.card_coe]
  apply Fintype.card_le_of_injective f
  intro γ δ he
  apply Subtype.ext
  have hγ := hf γ
  have hδ := hf δ
  rw [← he] at hδ
  exact same_label
    ((F.primitive.map (evalRingHom (node (f γ)))).ne_zero_or_ne_zero)
    (by simpa [Direction.amp] using hγ)
    (by simpa [Direction.amp] using hδ)

theorem proof : K21_12.c2 := by
  classical
  intro u deleted F Γ
  let A := Γ.filter (fun γ => F.amp γ ≠ 0 ∧ ¬ IsCoprime (F.amp γ) ((F.amp γ).map twist))
  let U := Γ.filter (fun γ => ¬ IsCoprime (F.amp γ) F.U)
  let N := Γ.filter (fun γ => ∃ i : I, (F.amp γ).eval (node i) = 0)
  let L := Γ.filter (fun γ => (F.amp γ).coeff F.s = 0)
  have ha : A.card ≤ (p + 1) * F.s := by
    by_cases hs : F.s = 0
    · have hempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro γ hγ
        obtain ⟨hamp, hbad⟩ := (Finset.mem_filter.mp hγ).2
        have hd := amp_degree_le F γ
        rw [hs, Nat.le_zero] at hd
        have hunit : IsUnit (F.amp γ) := isUnit_iff_degree_eq_zero.mpr (by
          rw [degree_eq_natDegree hamp, hd]
          rfl)
        exact hbad (by simpa only [mul_one] using
          (isCoprime_mul_unit_left_left hunit 1 _).mpr isCoprime_one_left)
      simp [hempty]
    · exact (card_of_failed_coprime F A (fun γ => (F.amp γ).map twist)
        (eliminant_ne F (by decide : 2 ≤ p) twist hs)
        (fun _ hγ => (Finset.mem_filter.mp hγ).2.2)
        (fun γ _ => gcd_dvd_eliminant F p twist (fun _ => rfl) (by decide) γ)).trans
          (eliminant_degree F p twist)
  have hu : U.card ≤ F.U.natDegree :=
    card_of_failed_coprime F U (fun _ => F.U) F.U_ne
      (fun _ hγ => (Finset.mem_filter.mp hγ).2) (fun _ _ => gcd_dvd_right _ _)
  have hn : N.card ≤ 262144 :=
    card_node_failures F N (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hl : L.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro γ hγ δ hδ
    exact same_label (top_pair F)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hγ).2)
      (by simpa only [Direction.amp, coeff_add, coeff_C_mul] using (Finset.mem_filter.mp hδ).2)
  have hsub : excluded F Γ ⊆ ((A ∪ U) ∪ N) ∪ L := by
    intro γ hγ
    obtain ⟨hΓ, hbad⟩ := Finset.mem_filter.mp hγ
    by_contra h
    simp only [Finset.mem_union, A, U, N, L, Finset.mem_filter, hΓ, true_and,
      not_or] at h
    obtain ⟨⟨⟨hA, hU⟩, hN⟩, hL⟩ := h
    have hne : F.amp γ ≠ 0 := by
      intro hz
      exact hL (by simp [hz])
    exact hbad ⟨hne, natDegree_eq_of_le_of_coeff_ne_zero (amp_degree_le F γ) hL,
      not_not.mp (fun hbadA => hA ⟨hne, hbadA⟩), not_not.mp hU,
      fun i _ hi => hN ⟨i, hi⟩⟩
  have hcount := Finset.card_le_card hsub
  have hAU := Finset.card_union_le A U
  have hAUN := Finset.card_union_le (A ∪ U) N
  have hAUNL := Finset.card_union_le ((A ∪ U) ∪ N) L
  omega

end
end K21_12_2
end Port_K1_12_2Proof

section Port_K1_12_1Proof
set_option autoImplicit true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace K21_12_1
noncomputable section

open Polynomial K21

/-- The two pencils in the shared plane are jointly primitive, so the
constant contents in the parallel presentation are coprime. -/
private theorem coprime_contents {u T R D} (B : RankThree u T R D)
    (P : K21_10.Plane u (fixedNodes R) D.height (K21_10.leftCoeff B) (K21_10.rightCoeff B)) :
    IsCoprime B.a B.b := by
  apply (gcd_isUnit_iff _ _).mp
  apply P.primitive
  · intro i
    exact (gcd_dvd_left B.a B.b).trans (dvd_mul_right _ _)
  · intro j
    rw [K21_10.rightCoeff, dvd_neg]
    exact (gcd_dvd_right B.a B.b).trans (dvd_mul_right _ _)

private theorem plane_height {u T R D} (B : RankThree u T R D)
    (P : K21_10.Plane u (fixedNodes R) D.height (K21_10.leftCoeff B) (K21_10.rightCoeff B))
    (par : Parallel B) (hdeg : B.b.natDegree = B.a.natDegree) :
    D.height = B.a.natDegree + amplitudeDegree (B.α 0) (B.α 1) := by
  let s := amplitudeDegree (B.α 0) (B.α 1)
  have hA (i : Fin 2) : (B.α i).natDegree ≤ s := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hL (i : Fin 2) : (K21_10.leftCoeff B i).natDegree ≤ B.a.natDegree + s := by
    change B.α = B.β at par
    unfold K21_10.leftCoeff
    rw [← par]
    exact natDegree_mul_le_of_le le_rfl (natDegree_map_le.trans (hA i))
  have hR (j : Fin 2) : (K21_10.rightCoeff B j).natDegree ≤ B.a.natDegree + s := by
    rw [K21_10.rightCoeff, natDegree_neg, ← hdeg]
    exact natDegree_mul_le_of_le le_rfl (hA j)
  have hmax := max_le (max_le (hL 0) (hL 1)) (max_le (hR 0) (hR 1))
  exact le_antisymm (P.height_eq ▸ hmax) (hdeg ▸ B.second_degree)

private theorem plane_nodes {u T R D} (B : RankThree u T R D)
    (P : K21_10.Plane u (fixedNodes R) D.height (K21_10.leftCoeff B) (K21_10.rightCoeff B))
    (par : Parallel B) (x : I) (hx : x ∉ fixedNodes R) (i j : Fin 2) :
    (P.output j i).eval (node x) =
      B.a.eval (node x) * ((B.α i).map twist).eval (node x) * u j x -
      B.b.eval (node x) * (B.α j).eval (node x) * twist (u i x) := by
  change B.α = B.β at par
  simpa only [K21_10.leftCoeff, K21_10.rightCoeff, eval_mul, eval_neg, neg_mul,
    ← sub_eq_add_neg, ← par, twist, frobenius_def] using (P.nodes x hx j i).symm

/-- Construct the homogeneous direction with the four output lifts on the
actual puncture. -/
theorem proof : K21_12.c1 := by
  intro u hu T R D B _ par hnorm _
  obtain ⟨P⟩ := K21_10.plane_of_rankThree B
  obtain ⟨den, hden, hphase, hnodes⟩ := denominator B.b_ne hnorm
  have hden' : den.map twist ≠ 0 := (Polynomial.map_ne_zero_iff twist.injective).mpr hden
  have hdeg := congrArg (fun Q : K[X] => Q.natDegree) hphase
  change (B.a * den.map twist).natDegree = (B.b * den).natDegree at hdeg
  rw [natDegree_mul B.a_ne hden', natDegree_mul B.b_ne hden,
    natDegree_map_eq_of_injective twist.injective] at hdeg
  have hdeg' : B.b.natDegree = B.a.natDegree := by omega
  have hcop := coprime_contents B P
  have hheight := plane_height B P par hdeg'
  have hdvd : B.a ∣ den := hcop.dvd_of_dvd_mul_left
    (hphase ▸ dvd_mul_right B.a (den.map twist))
  have hbudget : T.height ≤ 32872 := by
    have hr := hu.1
    have hd := T.degreeSum
    have hn := T.nullitySum
    unfold TwoActive.height
    omega
  exact ⟨{
    den := den
    U := B.a
    V := B.b
    A := B.α
    out := fun i j => P.output j i
    den_nodes := hnodes
    U_ne := B.a_ne
    V_ne := B.b_ne
    U_dvd := hdvd
    coprime := hcop
    phase := hphase
    degrees_eq := hdeg'
    primitive := B.α_primitive
    height := by rwa [← hheight, D.height_eq]
    out_degree := by
      intro i j
      simpa only [hheight, ← Nat.add_assoc] using P.output_degree j i
    nodes := plane_nodes B P par
  }⟩

end
end K21_12_1
end Port_K1_12_1Proof
