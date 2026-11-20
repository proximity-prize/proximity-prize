import ProximityPrize.SubmissionLower.PackedPrice
namespace Koala6835.Packed
set_option autoImplicit false

theorem digit0 (s x:ℕ) : digit s x 0=x%(2^s) := by simp [digit_div]
theorem digit_succ (s x j:ℕ) : digit s x (j+1)=digit s (x/(2^s)) j := by
  rw [digit_div,digit_div,pow_succ',Nat.div_div_eq_div_mul]

theorem pack_small (base n:ℕ) (f:ℕ→ℕ) (_pos : 0<base) (bd : ∀i<n,f i<base) :
    pack base n f<base^n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have h := ih (fun i=>f (i+1)) (fun i hi => bd _ (by omega))
    have hn : base*(pack base n (fun i=>f (i+1))+1)≤base*base^n :=
      Nat.mul_le_mul_left _ h
    have h0 := bd 0 (Nat.zero_lt_succ _)
    rw [pack,pow_succ']
    rw [Nat.mul_add,mul_one] at hn
    omega

theorem repack (s n x:ℕ) (bd:x<(2^s)^n) : pack (2^s) n (digit s x)=x := by
  induction n generalizing x with
  | zero => simp only [pow_zero] at bd; simp [pack,show x=0 by omega]
  | succ n ih =>
    have b : x/2^s < (2^s)^n := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).mpr; simpa only [pow_succ] using bd
    rw [pack,digit0]
    simp_rw [digit_succ]
    rw [ih _ b,Nat.mod_add_div]

def rowA (s n x : ℕ) :=
  pack ((2^s)^n) n (fun h=>digit s x h * pack (2^s) n (fun _=>1))
def rowB (s n y : ℕ) := y*pack ((2^s)^n) n (fun _=>1)
def rowC (s n c : ℕ) :=
  pack ((2^s)^n) n (fun h=>c >>> (s*h))
def mask (s n G : ℕ) := pack (2^s) n (fun _=>G)

def passes (s n G x y c : ℕ) :=
  let z:=rowA s n x+rowB s n y+rowC s n c
  z &&& rowB s n (mask s n G) == z

theorem shift_digit (s x h j:ℕ) :
    digit s (x >>> (s*h)) j = digit s x (h+j) := by
  simp only [digit,Nat.shiftRight_add,Nat.mul_add]

theorem pass_sound (s n M G x y c:ℕ)
    (packedY : y<(2^s)^n) (packedC : c<(2^s)^n)
    (small : ∀i<n,digit s x i≤M ∧ digit s y i≤M)
    (comp : ∀i, digit s c i≤G)
    (room : M+M+G<2^s) (valid : passes s n G x y c=true)
    (h j:ℕ) (hh:h<n) (hj:j<n) :
    digit s x h + digit s y j + digit s c (h+j) ≤ G := by
  let b:=2^s
  let u (h j:ℕ) := digit s x h+digit s y j+digit s c (h+j)
  have su (h:ℕ) (hh:h<n) (j:ℕ) (hj:j<n) : u h j<b := by
    have l:=(small _ hh).1; have r:=(small _ hj).2; have e:=comp (h+j)
    dsimp [u,b]; omega
  have gsmall : G<b := by dsimp [b]; omega
  have Cfun (h:ℕ) : c >>> (s*h) = pack b n (fun j=>digit s c (h+j)) := by
    rw [←repack s n (c >>> (s*h)) ((Nat.shiftRight_le ..).trans_lt packedC)]
    apply pack_congr
    intro i _; exact shift_digit _ _ _ _
  have roweq : rowA s n x+rowB s n y+rowC s n c =
      pack (b^n) n (fun h=>pack b n (u h)) := by
    unfold rowA rowB rowC
    rw [←pack_const_mul,pack_add,pack_add]
    apply pack_congr; intro k _
    rw [←pack_const_mul,←repack s n y packedY,Cfun,pack_add,pack_add]
  have hg := eq_of_beq (a:=_) (b:=_) valid
  change (_ &&& rowB s n (mask s n G))=_ at hg
  rw [roweq,rowB,←pack_const_mul] at hg
  have maskbd : mask s n G<b^n :=
    pack_small _ _ _ (Nat.two_pow_pos s) (fun _ _ => gsmall)
  have rowbd (i:ℕ) (hi:i<n) : pack b n (u i)<b^n :=
    pack_small _ _ _ (Nat.two_pow_pos s) (su i hi)
  have bigpow : b^n=2^(s*n) := (pow_mul _ _ _).symm
  rw [bigpow] at hg maskbd
  have he := congrArg (fun z => digit (s*n) z h) hg
  have rowok (i:ℕ) (hi:i<n) : pack b n (u i)<2^(s*n) := bigpow ▸ rowbd i hi
  rw [digit_and,get_pack _ _ _ rowok _ hh,get_pack _ _ _ (fun _ _=>maskbd) _ hh] at he
  have he' := congrArg (fun z=>digit s z j) he
  change digit s (pack (2^s) n (u h) &&& pack (2^s) n (fun _=>G)) j=_ at he'
  rw [digit_and,get_pack _ _ _ (su h hh) _ hj,get_pack _ _ _ (fun _ _=>gsmall) _ hj] at he'
  change u h j≤G
  exact he'.symm.le.trans Nat.and_le_right

#print axioms pass_sound
end Koala6835.Packed
