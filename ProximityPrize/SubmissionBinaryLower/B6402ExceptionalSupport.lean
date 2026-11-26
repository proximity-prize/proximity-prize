import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSystem

/-! The finite rectangular support for the exceptional-fibre recursion,
including all positive t-slices that feed the next constant term. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSupport
open Polynomial P64Found B6402ExceptionalSystem
set_option autoImplicit false
set_option maxHeartbeats 1200000
variable {K : Type*} [Field K]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing ((Fibre K)[X]) := AddMonoidAlgebra.commRing

structure Bounds (p : Fibre K) (r w z : ℕ) : Prop where
  slope : WtLE 1 0 0 r p
  ordinate : WtLE 0 1 0 w p
  seed : WtLE 0 0 1 z p

theorem in_box (p : Fibre K) (r w z : ℕ) : p∈supp (box r w z) ↔ Bounds p r w z := by
  constructor
  · intro h
    have limits (a b l : ℕ) (hn : c3 p a b l≠0) : a≤r ∧ b≤w ∧ l≤z := by
      have hp : (a,b,l)∈box r w z := by
        by_contra ha
        exact hn (h a b l ha)
      simpa [box] using hp
    exact ⟨fun a b l h => by simpa using (limits a b l h).1,
      fun a b l h => by simpa using (limits a b l h).2.1,
      fun a b l h => by simpa using (limits a b l h).2.2⟩
  · intro h a b l ha
    by_contra hn
    apply ha
    have a1 := h.slope a b l hn
    have a2 := h.ordinate a b l hn
    have a3 := h.seed a b l hn
    simpa [box] using (show a≤r ∧ b≤w ∧ l≤z by simp at a1 a2 a3; exact ⟨a1,a2,a3⟩)

theorem Bounds.mul {p q : Fibre K} {r w z r' w' z' : ℕ} (h : Bounds p r w z)
    (h' : Bounds q r' w' z') : Bounds (p*q) (r+r') (w+w') (z+z') :=
  ⟨h.slope.mul h'.slope,h.ordinate.mul h'.ordinate,h.seed.mul h'.seed⟩

theorem Bounds.mono {p : Fibre K} {r w z r' w' z' : ℕ} (h : Bounds p r w z)
    (hr : r≤r') (hw : w≤w') (hz : z≤z') : Bounds p r' w' z' :=
  ⟨h.slope.mono hr,h.ordinate.mono hw,h.seed.mono hz⟩

theorem Bounds.sub {p q : Fibre K} {r w z : ℕ} (h : Bounds p r w z) (h' : Bounds q r w z) :
    Bounds (p-q) r w z := by
  apply (in_box _ _ _ _).mp
  intro a b l ho
  have hp := (in_box _ _ _ _).mpr h a b l ho
  have hq := (in_box _ _ _ _).mpr h' a b l ho
  change ((p.coeff b).coeff a).coeff l=0 at hp
  change ((q.coeff b).coeff a).coeff l=0 at hq
  simp only [c3,coeff_sub,hp,hq,sub_self]

variable {U : Type*} [AddCommGroup U] [Module K U]

theorem covered (F : (Fibre K)[X]) (a L : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K) (u : U)
    (mR J T H d b : ℕ) (hT : H≤T) (hd : d≤J)
    (hF : ∀ j, Bounds (F.coeff (j+1)) (3*(j+1)) 5 H)
    (ha : Bounds a 0 5 0) (hL : Bounds L 0 d H)
    (hG : ∀ j, Bounds ((g u).coeff j) (mR+3*j) J T)
    (hQ : ∀ i<b, Bounds (Q i u) (mR+3*i) (J+5*i-d) (T+i*H-H)) :
    ∀ i<b, errorTerm F a L g Q i u ∈ supp (testBox mR J T H i) := by
  have step (i : ℕ) (hi : i≤b) (j : ℕ) :
      Bounds ((layer F a g Q i u).coeff j) (mR+3*(i+j)) (J+5*i) (T+i*H) := by
    induction i generalizing j with
    | zero => simpa [layer] using hG j
    | succ i ih =>
      have ha' := ha.mul (ih (by omega) (j+1))
      have hf' := (hF j).mul (hQ i (by omega))
      change Bounds (((C a*(layer F a g Q i u)-F*C (Q i u)).divX).coeff j) _ _ _
      rw [coeff_divX,coeff_sub,coeff_C_mul,coeff_mul_C]
      apply (ha'.mono (by omega) (by omega) (by rw [Nat.succ_mul]; omega)).sub
      apply hf'.mono (by omega) (by omega) (by rw [Nat.succ_mul]; omega)
  intro i hi
  apply (in_box _ _ _ _).mpr
  have one := step i hi.le 0
  have two := hL.mul (hQ i hi)
  change Bounds (((layer F a g Q i u).coeff 0)-L*(Q i u)) _ _ _
  apply (one.mono (by omega) le_rfl le_rfl).sub
  exact two.mono (by omega) (by omega) (by omega)

#print axioms covered
end ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSupport
