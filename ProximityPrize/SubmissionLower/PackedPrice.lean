/- Apache-2.0. Exact packed parallel comparisons, with a proof for every digit. -/
import Mathlib.Tactic
namespace Koala6835.Packed
set_option autoImplicit false
def pack (base : ℕ) : ℕ → (ℕ→ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + base * pack base n (fun i => f (i+1))

def digit (s x j:ℕ) := (x >>> (s*j)) &&& (2^s-1)

theorem digit_div (s x j:ℕ) : digit s x j = x/(2^s)^j%(2^s) := by
  rw [digit,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,pow_mul]

theorem get_pack (s n:ℕ) (f:ℕ→ℕ) (bounded : ∀i<n,f i<2^s) (j:ℕ) (hj:j<n) :
    digit s (pack (2^s) n f) j=f j := by
  rw [digit_div]
  induction n generalizing f j with
  | zero => omega
  | succ n ih =>
    rw [pack]
    have h0 := bounded 0 (Nat.zero_lt_succ _)
    cases j with
    | zero => simp [Nat.add_mod, Nat.mod_eq_of_lt h0]
    | succ j =>
      rw [pow_succ', ←Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt h0,zero_add]
      exact ih (fun j=>f (j+1)) (fun i h=>bounded _ (by omega)) _ (by omega)

theorem pack_add (base n:ℕ) (f g:ℕ→ℕ) :
    pack base n f + pack base n g = pack base n (fun i=>f i+g i) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [show (f 0+base*pack base n (fun i=>f (i+1)))+(g 0+base*pack base n (fun i=>g (i+1)))=
        (f 0+g 0)+base*(pack base n (fun i=>f (i+1))+pack base n (fun i=>g (i+1))) by ring]
    rw [ih]

theorem digit_and (s x y j:ℕ) :
    digit s (x &&& y) j = digit s x j &&& digit s y j := by
  simp only [digit,Nat.shiftRight_and_distrib]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  simp [Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

theorem lanes (s n G:ℕ) (f g c:ℕ→ℕ) (hg:G<2^s)
    (safe:∀i<n,f i+g i+c i<2^s)
    (check : let z:=pack (2^s) n f+pack (2^s) n g+pack (2^s) n c
             z &&& pack (2^s) n (fun _=>G)=z) (j:ℕ) (hj:j<n) : f j+g j+c j≤G := by
  dsimp only at check
  rw [pack_add,pack_add] at check
  have eqn := congrArg (fun z=>digit s z j) check
  rw [digit_and,get_pack _ _ _ safe _ hj,get_pack _ _ _ (fun _ _ => hg) _ hj] at eqn
  exact eqn ▸ Nat.and_le_right

theorem pack_congr (base n:ℕ) (f g:ℕ→ℕ) (h:∀i<n,f i=g i) :
    pack base n f=pack base n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pack,pack,h 0 (Nat.zero_lt_succ _),ih _ _ (fun i hi => h _ (by omega))]

theorem pack_const_mul (B n x:ℕ) : pack B n (fun _=>x)=x*pack B n (fun _=>1) := by
  induction n with
  | zero => simp [pack]
  | succ n ih => simp only [pack,ih]; ring

#print axioms lanes
end Koala6835.Packed
