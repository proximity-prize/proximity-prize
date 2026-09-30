import ProximityPrize.SubmissionLower.SingletonCertificate6815
namespace ProximityPrize.SubmissionLower.CompactAllN6815
open SingletonCertificate6815
set_option autoImplicit false

theorem allN_block (p : ℕ → Bool) (k : ℕ) (h : allN (fun j => p (16*k+j)) 16=true)
    (v : ℕ) (h0 : 16*k≤v) (h1 : v<16*k+16) : p v=true := by
  have := allN_sound _ 16 h (v-16*k) (by omega)
  simpa only [Nat.add_sub_cancel' h0] using this

theorem allN_blockN (p : ℕ → Bool) (B k : ℕ) (h : allN (fun j => p (B*k+j)) B=true)
    (v : ℕ) (h0 : B*k≤v) (h1 : v<B*k+B) : p v=true := by
  have := allN_sound _ B h (v-B*k) (by omega)
  simpa only [Nat.add_sub_cancel' h0] using this

theorem allN_zero (p : ℕ → Bool) : allN p 0=true := rfl

theorem allN_snoc (p : ℕ → Bool) (n : ℕ) (h : allN p n=true) (h' : p n=true) : allN p (n+1)=true := by
  simp only [allN,h,h',Bool.and_self]

end ProximityPrize.SubmissionLower.CompactAllN6815
