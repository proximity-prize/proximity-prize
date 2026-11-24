import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false

/-! Seed-contact algebra for source rows chosen after separating the unique helper prime. -/
noncomputable section
namespace Lower6960.DifferentialContact
open MvPolynomial K1_14_2_2_3
open K1_14_2_2_3_1 (partial_append)

variable {K : Type*} [CommRing K]
abbrev A (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K

/-- Every seed derivative of order less than n lies in the test ideal. -/
def Contact (I : Ideal (A K)) (n : ℕ) (f : A K) : Prop :=
  ∀ w : List (Fin 2),w.length<n → partialWord f w∈I

theorem zero_order (I : Ideal (A K)) (f : A K) : Contact I 0 f := by
  intro w h; omega

theorem succ_iff (I : Ideal (A K)) (n : ℕ) (f : A K) :
    Contact I (n+1) f ↔ f∈I ∧ ∀ i, Contact I n (pderiv i f) := by
  constructor
  · intro h; refine ⟨h [] (by simp),?_⟩
    intro i w hw
    rw [←partial_append]
    exact h _ (by simp; omega)
  · rintro ⟨hf,hd⟩ w hw
    induction w using List.reverseRecOn with
    | nil => exact hf
    | append_singleton ws i _ =>
      rw [partial_append]
      apply hd i ws
      simpa using hw

theorem weaken {I : Ideal (A K)} {n m : ℕ} {f : A K} (h : Contact I n f) (le : m≤n) :
    Contact I m f := fun w hw => h w (hw.trans_le le)

def testIdeal (I : Ideal (A K)) (n : ℕ) : Ideal (A K) where
  carrier := {f | Contact I n f}
  zero_mem' := by
    change Contact I n 0
    induction n with
    | zero => exact zero_order I _
    | succ n ih => exact (succ_iff I n 0).2 ⟨I.zero_mem, fun i=>by simpa using ih⟩
  add_mem' := by
    intro f g hf hg
    change Contact I n f at hf
    change Contact I n g at hg
    change Contact I n (f+g)
    induction n generalizing f g with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      obtain ⟨g0,dg⟩ := (succ_iff ..).1 hg
      exact (succ_iff ..).2 ⟨I.add_mem f0 g0, fun i=>by rw [map_add];exact ih (df i) (dg i)⟩
  smul_mem' := by
    intro a f hf
    change Contact I n f at hf
    change Contact I n (a*f)
    induction n generalizing a f with
    | zero => exact zero_order I _
    | succ n ih =>
      obtain ⟨f0,df⟩ := (succ_iff ..).1 hf
      refine (succ_iff ..).2 ⟨I.mul_mem_left _ f0,?_⟩
      intro i; rw [pderiv_mul]
      have h1:=ih (pderiv i a) (weaken (m:=n) hf (by omega))
      have h2:=ih a (df i)
      -- Derivatives are additive on each iterated word.
      intro w hw
      have distrib (g h : A K) : partialWord (g+h) w=partialWord g w+partialWord h w := by
        clear hw
        induction w with
        | nil => rfl
        | cons j w ih => simp only [partialWord,ih,map_add]
      rw [distrib]
      exact I.add_mem (h1 _ hw) (h2 _ hw)

theorem product {I : Ideal (A K)} (n m : ℕ) (f g : A K)
    (hf : Contact I n f) (hg : Contact I m g) : Contact I (n+m) (f*g) := by
  induction n generalizing m f g with
  | zero =>
    rw [Nat.zero_add]
    exact (testIdeal I m).mul_mem_left f hg
  | succ n ih =>
    induction m generalizing g with
    | zero =>
      rw [Nat.add_zero,mul_comm];exact (testIdeal I (n+1)).mul_mem_left g hf
    | succ m jh =>
      have df := ((succ_iff ..).1 hf).2
      have dg := ((succ_iff ..).1 hg).2
      refine (succ_iff ..).2 ⟨I.mul_mem_left f ((succ_iff ..).1 hg).1,?_⟩
      intro i; rw [pderiv_mul]
      apply (testIdeal I (n+1+m)).add_mem
      · change Contact I (n+1+m) ((pderiv i f)*g)
        simpa only [Nat.succ_add,Nat.add_succ] using ih (m+1) (pderiv i f) g (df i) hg
      · change Contact I (n+1+m) (f*(pderiv i g))
        exact jh (pderiv i g) (dg i)

theorem row_power {I : Ideal (A K)} {f : A K} {n : ℕ} (hf : Contact I n f) (k : ℕ) :
    Contact I (k*n) (f^k) := by
  induction k with
  | zero => rw [Nat.zero_mul]; exact zero_order I _
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact product _ _ _ _ ih hf

theorem row_strip {I : Ideal (A K)} (prime : I.IsPrime) (n : ℕ) (g f : A K)
    (unit : g∉I) (h : Contact I n (g*f)) : Contact I n f := by
  induction n generalizing f with
  | zero => exact zero_order I _
  | succ n ih =>
    obtain ⟨prod0,dprod⟩ := (succ_iff ..).1 h
    refine (succ_iff ..).2 ⟨(prime.mem_or_mem prod0).resolve_left unit,?_⟩
    have low := ih f (weaken h (by omega))
    intro i
    apply ih
    have data:=dprod i
    rw [pderiv_mul] at data
    have first := (testIdeal I n).mul_mem_left (pderiv i g) low
    have diff := (testIdeal I n).sub_mem data first
    change g*(pderiv i f) ∈ testIdeal I n
    simpa only [add_sub_cancel_left] using diff

open K1_14 (Jet Seeds)
open K1_14_2 (Ambient toJet)
open K1_14_2_2_3 (shiftedWord specialize_shiftedWord)

def Native (J : Ideal Ambient) (n : ℕ) (P : Jet) : Prop :=
  ∀ w : List (Fin 2),w.length<n → toJet (shiftedWord P w)∈J

private def coords : Jet →+* A Seeds := seedPresentation.toRingHom.comp toJet

private theorem native_iff (J : Ideal Ambient) (n : ℕ) (P : Jet) :
    Native J n P ↔ Contact (J.comap seedPresentation.symm.toRingHom) n (coords P) := by
  have commute (w : List (Fin 2)) : partialWord (coords P) w=coords (shiftedWord P w) := by
    have hh:=specialize_shiftedWord (RingHom.id Seeds) P w
    simpa [coords,specializeJets,MvPolynomial.map_id] using hh.symm
  constructor
  · intro h w hw
    rw [commute]
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J
    simpa using h w hw
  · intro h w hw
    have mem:=h w hw
    rw [commute] at mem
    change seedPresentation.symm (seedPresentation (toJet (shiftedWord P w)))∈J at mem
    simpa using mem

theorem native_power {J : Ideal Ambient} {n k r : ℕ} {P : Jet} (h : Native J n P)
    (fit : r≤k*n) : Native J r (P^k) := by
  apply (native_iff ..).2
  rw [map_pow]
  exact weaken (row_power ((native_iff ..).1 h) k) fit

theorem native_strip {J : Ideal Ambient} (hJ : J.IsPrime) {G P : Jet} (n : ℕ)
    (outside : toJet G∉J) (h : Native J n (G*P)) : Native J n P := by
  let I := J.comap seedPresentation.symm.toRingHom
  let _ : J.IsPrime := hJ
  have mem := (native_iff ..).1 h
  rw [map_mul] at mem
  apply (native_iff ..).2
  apply row_strip (I:=I) (Ideal.IsPrime.comap seedPresentation.symm.toRingHom) n (coords G) (coords P) _ mem
  change seedPresentation.symm (seedPresentation (toJet G))∉J
  simpa using outside

#print axioms native_power
#print axioms native_strip
#print axioms row_power
#print axioms row_strip
end Lower6960.DifferentialContact
