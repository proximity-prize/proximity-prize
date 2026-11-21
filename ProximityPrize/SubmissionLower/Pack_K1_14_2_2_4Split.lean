import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
import ProximityPrize.SubmissionLower.Fast051
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
def seedDegree (H : Equation) : ℕ :=
  H.support.sup fun j => (H.coeff j).totalDegree
def residualShape (s : Shape) (x z : ℕ) : Shape :=
  ⟨s.m, s.B - z, min s.J (s.B - z), s.U - x⟩
structure SharedGcd {w rows i} {B : RowPair w rows i} (A : FixedPair B) where
  ordinary : Equation
  cheapTail : Jet
  layeredTail : Jet
  ordinary_ne : ordinary ≠ 0
  cheap_ne : cheapTail ≠ 0
  layered_ne : layeredTail ≠ 0
  cheap_factor : B.cheap = fixedIncl A.cheap.equation * (C ordinary * cheapTail)
  layered_factor : B.layered = fixedIncl A.layered.equation * (C ordinary * layeredTail)
  relativelyPrime : IsRelPrime (toJet cheapTail) (toJet layeredTail)
  seed_le : seedDegree ordinary ≤ min (stageAt i).cheap.U (stageAt i).layered.U
  ordinate_le : ordinary.natDegree ≤ min (stageAt i).cheap.B (stageAt i).layered.B
  cheap_caps : RowCaps cheapTail
    (residualShape (stageAt i).cheap (seedDegree ordinary) ordinary.natDegree)
  layered_caps : RowCaps layeredTail
    (residualShape (stageAt i).layered (seedDegree ordinary) ordinary.natDegree)
def HighOn (H : Equation) (r : ℕ) (I : Ideal Ambient) : Prop :=
  ∃ f : Equation, Irreducible f ∧ 0 < f.natDegree ∧ f ^ r ∣ H ∧ toJet (C f) ∈ I
def highScale (r : ℕ) (k : Fin 4) : ℕ :=
  ![r, r, r ^ 2, r ^ 2] k
def highCap (x z : ℕ) (k : Fin 4) : ℕ :=
  ![z, x, 2 * x * z, x * x] k
def pairCap (s t : Shape) (k : Fin 4) : ℕ :=
  ![s.B * t.J + t.B * s.J - s.J * t.J, s.U * t.J + t.U * s.J,
    s.U * t.B + t.U * s.B, s.U * t.U] k
def localLength (P Q : Jet) (I : Ideal Ambient) (hp : I.IsPrime) : ℕ∞ :=
  letI : I.IsPrime := hp
  let R := Localization.AtPrime I
  letI : CommRing R := inferInstanceAs (CommRing (Localization.AtPrime I))
  let J : Ideal Ambient := Ideal.span {toJet P, toJet Q}
  let A : Ideal R := J.map (algebraMap Ambient R)
  Module.length R (R ⧸ (A : Submodule R R))
end
end K1_14_2_2_4
end
section
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
def residualScale (square : Bool) (k : Fin 4) (n : ℕ) : ℕ :=
  if square = true ∨ k = 3 then n ^ 2 else n
private def seedNumerator (s t : Shape) (d r z : ℕ) : ℕ :=
  d * z + r * pairCap (residualShape s 0 z) (residualShape t 0 z) 0
private def ordinateNumerator (s t : Shape) (d r x : ℕ) : ℕ :=
  d * x + r * ((s.U - x) * t.J + (t.U - x) * s.J)
private def mixedNumerator (s t : Shape) (d r x z : ℕ) : ℕ :=
  d * (2 * x * z) + r ^ 2 * ((s.U - x) * (t.B - z) + (t.U - x) * (s.B - z))
private def jetsNumerator (s t : Shape) (d r x : ℕ) : ℕ :=
  d * (x * x) + r ^ 2 * ((s.U - x) * (t.U - x))
private def numerator (s t : Shape) (d r x z : ℕ) (k : Fin 4) : ℕ :=
  ![seedNumerator s t d r z, ordinateNumerator s t d r x,
    mixedNumerator s t d r x z, jetsNumerator s t d r x] k
private theorem numerator_bound (s t : Shape) (d r x z : ℕ) (k : Fin 4) :
    d * highCap x z k + highScale r k *
      pairCap (residualShape s x z) (residualShape t x z) k ≤ numerator s t d r x z k := by
  fin_cases k
  · exact le_rfl
  · change d * x + r * ((s.U - x) * min t.J (t.B - z) +
      (t.U - x) * min s.J (s.B - z)) ≤ _
    exact Nat.add_le_add_left (Nat.mul_le_mul_left r (Nat.add_le_add
      (Nat.mul_le_mul_left _ (min_le_left _ _)) (Nat.mul_le_mul_left _ (min_le_left _ _)))) _
  · exact le_rfl
  · exact le_rfl
private theorem affine_bound {x bound a b c M : ℕ} (hx : x ≤ bound)
    (h0 : b * bound + c < M) (hX : a * bound + c < M) :
    a * x + b * (bound - x) + c < M := by
  by_cases hab : a ≤ b
  · calc
      a * x + b * (bound - x) + c ≤ b * x + b * (bound - x) + c :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right x hab) _) _
      _ = b * bound + c := by rw [← Nat.mul_add, Nat.add_sub_of_le hx]
      _ < M := h0
  · have hba : b ≤ a := by omega
    calc
      a * x + b * (bound - x) + c ≤ a * x + a * (bound - x) + c :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hba) _) _
      _ = a * bound + c := by rw [← Nat.mul_add, Nat.add_sub_of_le hx]
      _ < M := hX
private theorem affine_endpoints {F : ℕ → ℕ} {x bound a b c M : ℕ}
    (hx : x ≤ bound) (he : ∀ j ≤ bound, F j = a * j + b * (bound - j) + c)
    (h0 : F 0 < M) (hX : F bound < M) : F x < M := by
  rw [he x hx]
  apply affine_bound hx
  · rw [he 0 (Nat.zero_le bound)] at h0
    simpa using h0
  · rw [he bound le_rfl] at hX
    simpa using hX
private theorem ordinate_endpoints (s t : Shape) {d r x M : ℕ} (hx : x ≤ s.U)
    (hu : s.U ≤ t.U) (h0 : ordinateNumerator s t d r 0 < M)
    (hU : ordinateNumerator s t d r s.U < M) : ordinateNumerator s t d r x < M := by
  refine affine_endpoints (F := ordinateNumerator s t d r)
    (a := d) (b := r * (t.J + s.J)) (c := r * ((t.U - s.U) * s.J)) hx ?_ h0 hU
  intro j hj
  have hsub : t.U - j = (t.U - s.U) + (s.U - j) := by omega
  simp only [ordinateNumerator, hsub]
  ring
private theorem mixed_seed_endpoints (s t : Shape) {d r x z M : ℕ}
    (hx : x ≤ s.U) (hu : s.U ≤ t.U)
    (h0 : mixedNumerator s t d r 0 z < M) (hU : mixedNumerator s t d r s.U z < M) :
    mixedNumerator s t d r x z < M := by
  refine affine_endpoints (F := fun j => mixedNumerator s t d r j z)
    (a := d * 2 * z) (b := r ^ 2 * ((t.B - z) + (s.B - z)))
    (c := r ^ 2 * ((t.U - s.U) * (s.B - z))) hx ?_ h0 hU
  intro j hj
  have hsub : t.U - j = (t.U - s.U) + (s.U - j) := by omega
  simp only [mixedNumerator, hsub]
  ring
private theorem mixed_ordinate_endpoints (s t : Shape) {d r x z M : ℕ}
    (hz : z ≤ s.B) (hb : s.B ≤ t.B)
    (h0 : mixedNumerator s t d r x 0 < M) (hB : mixedNumerator s t d r x s.B < M) :
    mixedNumerator s t d r x z < M := by
  refine affine_endpoints (F := mixedNumerator s t d r x)
    (a := d * 2 * x) (b := r ^ 2 * ((s.U - x) + (t.U - x)))
    (c := r ^ 2 * ((s.U - x) * (t.B - s.B))) hz ?_ h0 hB
  intro j hj
  have hsub : t.B - j = (t.B - s.B) + (s.B - j) := by omega
  simp only [mixedNumerator, hsub]
  ring
private theorem jets_endpoints (s t : Shape) {d r x M : ℕ} (hx : x ≤ s.U)
    (h0 : jetsNumerator s t d r 0 < M) (hU : jetsNumerator s t d r s.U < M) :
    jetsNumerator s t d r x < M := by
  have hle : jetsNumerator s t d r x ≤ d * s.U * x + r ^ 2 * t.U * (s.U - x) := by
    unfold jetsNumerator
    rw [Nat.mul_assoc d, Nat.mul_assoc (r ^ 2), Nat.mul_comm t.U]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hx))
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
  apply lt_of_le_of_lt hle
  have h0' : (r ^ 2 * t.U) * s.U + 0 < M := by
    simpa [jetsNumerator, Nat.mul_assoc, Nat.mul_comm s.U t.U] using h0
  have hU' : (d * s.U) * s.U + 0 < M := by
    simpa [jetsNumerator, Nat.mul_assoc] using hU
  simpa using affine_bound (x := x) hx h0' hU'
private def checkNumerator (s t : Shape) (d r M : ℕ) (k : Fin 4) : Prop :=
  match k.val with
  | 0 => ∀ z : Fin (s.B + 1), seedNumerator s t d r z.val < M
  | 1 => ordinateNumerator s t d r 0 < M ∧ ordinateNumerator s t d r s.U < M
  | 2 => mixedNumerator s t d r 0 0 < M ∧ mixedNumerator s t d r 0 s.B < M ∧
      mixedNumerator s t d r s.U 0 < M ∧ mixedNumerator s t d r s.U s.B < M
  | _ => jetsNumerator s t d r 0 < M ∧ jetsNumerator s t d r s.U < M
private instance (s t : Shape) (d r M : ℕ) (k : Fin 4) :
    Decidable (checkNumerator s t d r M k) := by
  unfold checkNumerator
  split <;> infer_instance
private theorem checked_bound (s t : Shape) (d r M x z : ℕ) (k : Fin 4)
    (hu : s.U ≤ t.U) (hb : s.B ≤ t.B) (hx : x ≤ s.U) (hz : z ≤ s.B)
    (h : checkNumerator s t d r M k) : numerator s t d r x z k < M := by
  fin_cases k
  · exact h ⟨z, by omega⟩
  · exact ordinate_endpoints s t hx hu h.1 h.2
  · obtain ⟨h00, h0B, hU0, hUB⟩ := h
    exact mixed_seed_endpoints s t hx hu
      (mixed_ordinate_endpoints s t hz hb h00 h0B)
      (mixed_ordinate_endpoints s t hz hb hU0 hUB)
  · exact jets_endpoints s t hx h.1 h.2
private def linearThreshold (i : Fin 10) (k : Fin 4) : ℕ :=
  match i.val with
  | 3 => ![1,1,1,2] k
  | 4 => ![1,1,2,2] k
  | _ => 1
private def squareThreshold (i : Fin 10) (k : Fin 4) : ℕ :=
  match i.val with
  | 4 => ![1,1,3,2] k
  | 5 => ![1,1,4,3] k
  | 6 => ![1,1,5,5] k
  | 7 => ![2,2,7,7] k
  | 8 => ![3,3,11,10] k
  | _ => ![5,5,15,14] k
private def certificate (i : Fin 10) (square : Bool) (cap : Fin 4 → ℕ)
    (k : Fin 4) (r : ℕ) : Prop :=
  let s := (stageAt i).cheap
  let t := (stageAt i).layered
  let m := (stageAt i).reserve + 1
  let d := residualScale square k (m + 1 - r)
  budget (i.val - 1) k ≤ cap k ∨
    (0 < r ∧ r ≤ m ∧ checkNumerator s t d r (highScale r k * d * (cap k + 1)) k)
private instance (i : Fin 10) (square : Bool) (cap : Fin 4 → ℕ)
    (k : Fin 4) (r : ℕ) : Decidable (certificate i square cap k r) := by
  unfold certificate
  infer_instance
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem linear_checked :
    ∀ i : Fin 10, 0 < i.val → i.val ≤ 4 → ∀ k : Fin 4,
      certificate i false (exitBudget i) k (linearThreshold i k) := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem square_checked :
    ∀ i : Fin 10, 4 ≤ i.val → ∀ k : Fin 4,
      certificate i true (budget i.val) k (squareThreshold i k) := by
  decide +kernel
private theorem shape_order :
    ∀ i : Fin 10, (stageAt i).cheap.U ≤ (stageAt i).layered.U ∧
      (stageAt i).cheap.B ≤ (stageAt i).layered.B := by
  decide +kernel
theorem schedule_bound (i : Fin 10) (square : Bool) (k : Fin 4)
    (hstage : if square then 4 ≤ i.val else 0 < i.val ∧ i.val ≤ 4)
    (x z : ℕ) (hx : x ≤ (stageAt i).cheap.U) (hz : z ≤ (stageAt i).cheap.B) :
    let s := (stageAt i).cheap
    let t := (stageAt i).layered
    let m := (stageAt i).reserve + 1
    let cap := (if square then budget i.val else exitBudget i) k
    budget (i.val - 1) k ≤ cap ∨
      ∃ r, 0 < r ∧ r ≤ m ∧
        let d := residualScale square k (m + 1 - r)
        d * highCap x z k + highScale r k *
          pairCap (residualShape s x z) (residualShape t x z) k <
          highScale r k * d * (cap + 1) := by
  let s := (stageAt i).cheap
  let t := (stageAt i).layered
  let m := (stageAt i).reserve + 1
  let cap := if square then budget i.val else exitBudget i
  let r := if square then squareThreshold i k else linearThreshold i k
  have hc : certificate i square cap k r := by
    cases square
    · exact linear_checked i hstage.1 hstage.2 k
    · exact square_checked i hstage k
  change budget (i.val - 1) k ≤ cap k ∨
    (0 < r ∧ r ≤ m ∧
      checkNumerator s t (residualScale square k (m + 1 - r)) r
        (highScale r k * residualScale square k (m + 1 - r) * (cap k + 1)) k) at hc
  rcases hc with hc | ⟨hr, hm, hc⟩
  · exact Or.inl hc
  · apply Or.inr
    refine ⟨r, hr, hm, (numerator_bound s t _ r x z k).trans_lt ?_⟩
    exact checked_bound s t _ r _ x z k (shape_order i).1 (shape_order i).2 hx hz hc
end
end K1_14_2_2_4
end
section
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped Classical BigOperators
def c1 : Prop :=
  ∀ w rows (i : Fin 10) (B : RowPair w rows i) (A : FixedPair B),
    Nonempty (SharedGcd A)
def c2 : Prop :=
  ∀ (H : Equation) (P Q : Jet) (S : Finset (Ideal Ambient)) (r : ℕ),
    H ≠ 0 → seedDegree H < p → H.natDegree < p → 0 < r →
    C H ∣ P → C H ∣ Q →
    (∀ I ∈ S, Active I ∧ compatible P Q I ∧ HighOn H r I) →
    ∀ k, highScale r k * mass S k ≤ highCap (seedDegree H) H.natDegree k
def c3 : Prop :=
  ∀ (H : Equation) (P : Jet) (I : Ideal Ambient) (m r : ℕ),
    H ≠ 0 → seedDegree H < p → H.natDegree < p →
    Active I → 0 < r → r ≤ m → ¬ HighOn H r I →
    orderOn I (C H * P) m → orderOn I P (m + 1 - r)
def c4 : Prop :=
  ∀ (P Q : Jet) (I : Ideal Ambient) (hI : Active I) (n : ℕ),
    0 < n → orderOn I P n → orderOn I Q n →
    ((if dual I then n ^ 2 else n : ℕ) : ℕ∞) ≤ localLength P Q I hI.prime
def c5 : Prop :=
  ∀ (P Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient)) (k : Fin 4) (d : ℕ),
    P ≠ 0 → Q ≠ 0 → IsRelPrime (toJet P) (toJet Q) →
    s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t → 0 < d →
    (∀ I ∈ S, ∃ hI : Active I,
      sectionDegree I k ≠ 0 → (d : ℕ∞) ≤ localLength P Q I hI.prime) →
    d * mass S k ≤ pairCap s t k
private theorem cancel_fixed {I : Ideal Ambient} (hp : I.IsPrime) (G : ODE) (P : Jet)
    (m : ℕ) (hG : ¬ fixedOn G I) (ho : orderOn I (fixedIncl G * P) m) :
    orderOn I P m := by
  obtain ⟨a, ha, h⟩ := ho
  refine ⟨a * toJet (fixedIncl G), fun hn => (hp.mem_or_mem hn).elim ha hG, ?_⟩
  simpa only [map_mul, mul_assoc] using h
private theorem cheap_small :
    ∀ i : Fin 10, (stageAt i).cheap.U < p ∧ (stageAt i).cheap.B < p := by
  decide +kernel
private theorem from_paired_bounds {S : Finset (Ideal Ambient)} {k : Fin 4}
    (H : Equation) (r g d high low cap : ℕ)
    (hh : g * mass (S.filter (HighOn H r)) k ≤ high)
    (hl : d * mass (S.filter fun I => ¬ HighOn H r I) k ≤ low)
    (hnum : d * high + g * low < g * d * (cap + 1)) :
    mass S k ≤ cap := by
  have hadd : mass (S.filter (HighOn H r)) k +
      mass (S.filter fun I => ¬ HighOn H r I) k = mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hscaled : g * d * mass S k ≤ d * high + g * low := by
    calc
      g * d * mass S k =
          d * (g * mass (S.filter (HighOn H r)) k) +
            g * (d * mass (S.filter fun I => ¬ HighOn H r I) k) := by
              rw [← hadd]
              ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hh) (Nat.mul_le_mul_left _ hl)
  by_contra! hbad
  have hge := Nat.mul_le_mul_left (g * d) (show cap + 1 ≤ mass S k by omega)
  exact (not_lt_of_ge hge) (hscaled.trans_lt hnum)
private theorem paired_stage (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    {w rows} (i : Fin 10) {B : RowPair w rows i} {A : FixedPair B} (G : SharedGcd A)
    (S : Finset (Ideal Ambient)) (square : Bool)
    (hstage : if square then 4 ≤ i.val else 0 < i.val ∧ i.val ≤ 4)
    (hdual : square = true → ∀ I ∈ S, dual I)
    (hin : Fits S (budget (i.val - 1)))
    (hpass : ∀ I ∈ S, Active I ∧ pairGood A I ∧
      orderOn I B.cheap ((stageAt i).reserve + 1) ∧
      orderOn I B.layered ((stageAt i).reserve + 1)) :
    Fits S (if square then budget i.val else exitBudget i) := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let m := (stageAt i).reserve + 1
  let s := residualShape (stageAt i).cheap x z
  let t := residualShape (stageAt i).layered x z
  let cap := if square then budget i.val else exitBudget i
  have hx : x ≤ (stageAt i).cheap.U := G.seed_le.trans (min_le_left _ _)
  have hz : z ≤ (stageAt i).cheap.B := G.ordinate_le.trans (min_le_left _ _)
  have hxp : x < p := hx.trans_lt (cheap_small i).1
  have hzp : z < p := hz.trans_lt (cheap_small i).2
  intro k
  rcases schedule_bound i square k hstage x z hx hz with hclip | ⟨r, hr, hrm, hnum⟩
  · exact (hin k).trans hclip
  let n := m + 1 - r
  let d := residualScale square k n
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d residualScale
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply h2 G.ordinary B.cheap B.layered _ r G.ordinary_ne hxp hzp hr
    · refine ⟨fixedIncl A.cheap.equation * G.cheapTail, G.cheap_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl A.layered.equation * G.layeredTail, G.layered_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    have hp := hpass I hm
    exact ⟨hp.1, hp.2.1.1.2.2, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤ pairCap s t k := by
    apply h5 G.cheapTail G.layeredTail s t _ k d G.cheap_ne G.layered_ne
      G.relativelyPrime (min_le_right _ _) (min_le_right _ _) G.cheap_caps G.layered_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, hg, hP, hQ⟩ := hpass I hm
    rw [G.cheap_factor] at hP
    rw [G.layered_factor] at hQ
    have hlP := h3 G.ordinary G.cheapTail I m r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hg.2.1 hP)
    have hlQ := h3 G.ordinary G.layeredTail I m r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ m hg.2.2 hQ)
    have hlen := h4 G.cheapTail G.layeredTail I ha n hn hlP hlQ
    refine ⟨ha, fun hdegree => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d residualScale
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square ≠ true := fun he => hIdual (hdual he I hm)
      have hk : k ≠ 3 := fun he => hIdual (show 0 < sectionDegree I 3 by
        rw [← he]
        exact Nat.pos_of_ne_zero hdegree)
      simpa [d, residualScale, hs, hk, hIdual] using hlen
  exact from_paired_bounds G.ordinary r (highScale r k) d _ _ (cap k) hh hl hnum
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_14_2_2.c4 := by
  intro w rows i B A S hi hin hpass
  obtain ⟨G⟩ := h1 w rows i B A
  have hlin (hi4 : i.val ≤ 4) : Fits S (exitBudget i) :=
    paired_stage h2 h3 h4 h5 i G S false ⟨hi, hi4⟩ (by simp) hin hpass
  refine ⟨hlin, ?_⟩
  by_cases hi4 : 4 ≤ i.val
  · exact paired_stage h2 h3 h4 h5 i G (S.filter dual) true hi4
      (fun _ I hI => (Finset.mem_filter.mp hI).2)
      (fits_mono (Finset.filter_subset _ _) hin)
      (fun I hI => hpass I (Finset.mem_filter.mp hI).1)
  · have he : exitBudget i = budget i.val := by
      simp [exitBudget, show i.val ≠ 4 by omega]
    rw [← he]
    exact fits_mono (Finset.filter_subset _ _) (hlin (by omega))
end
end K1_14_2_2_4
end
