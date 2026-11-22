import ProximityPrize.SubmissionLower.Pack_K1_14_2_2Split
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
end
end K1_14_2_2_4
end
section
set_option maxHeartbeats 1000000
namespace K1_14_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped Classical BigOperators
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
end
end K1_14_2_2_4
end
