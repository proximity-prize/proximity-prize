import ProximityPrize.SubmissionLower.R6960RescueSourceArithmetic
import ProximityPrize.SubmissionLower.R6960FreeSource

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open P1_7 (Bank debit)
open P1_7_1_3 (evaluate evaluate_append)
open HelperSource (WidthGuard cutoffCount surplus)

def phaseBlock (f : ℕ→ℕ) (start len : ℕ) : ℕ :=
  evaluate (fun i => f (start+i)) len

theorem phaseBlock_append {f : ℕ→ℕ} {start next a b n x y z : ℕ}
    (ha : phaseBlock f start a=x) (hb : phaseBlock f next b=y)
    (hs : start+a=next) (hn : a+b=n) (hz : x+y=z) :
    phaseBlock f start n=z := by
  unfold phaseBlock at *
  rw [← hs] at hb
  exact evaluate_append ha (by simpa only [Nat.add_assoc] using hb) hn hz

theorem phase_of_block {s : K1_14.Shape} {A h r d c v δ n z : ℕ}
    (len : s.J/d+1=n) (block : phaseBlock (fastLayer s A h r d c v δ) 0 n=z) :
    fastPhase s A h r d c v δ=z := by
  unfold fastPhase
  rw [len]
  simpa only [phaseBlock, Nat.zero_add] using block

def fastSurplus (t : Bank) (h r c v : ℕ) : ℤ :=
  (fastPhase t.shape 179827 h r 1 c v 0 - fastPhase t.shape 179827 h r 1 c v 1 : ℕ) -
    (debit h t : ℤ)

theorem fastSurplus_eq (t : Bank) (h r c v : ℕ)
    (hJ : t.shape.J<131071-h) (hshift : 2*h*(r+t.shape.J)<t.shape.m*179827) :
    fastSurplus t h r c v = surplus t 179827 h r 1 c v := by
  unfold fastSurplus surplus
  rw [fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    fastPhase_eq _ _ _ _ _ _ _ _ hJ (by simpa using hshift),
    HelperSource.gain_eq_compressed _ _ _ _ _ _ _ (by decide)]

structure Checked (t : Bank) (r c v : ℕ) : Prop where
  bank_ok : P3_7_1.BankOK t
  seed_ok : t.shape.U<K1.p
  reserve_ok : 2*r≤t.shape.B
  width_first : WidthGuard t 179827 2339 r
  first : 0<surplus t 179827 2339 r 1 c v
  next : surplus t 179827 2339 r 1 c v ≤ surplus t 179827 2340 r 1 c v

theorem checked_from_values (t : Bank) (r c v : ℕ) (hb : P3_7_1.BankOK t)
    (seed : t.shape.U<K1.p) (reserve : 2*r≤t.shape.B) (width : WidthGuard t 179827 2339 r)
    (slope : t.shape.J<131071-2340) (shift : 2*2340*(r+t.shape.J)<t.shape.m*179827)
    {a b x y : ℕ} (a0 : fastPhase t.shape 179827 2339 r 1 c v 0 = a)
    (a1 : fastPhase t.shape 179827 2339 r 1 c v 1 = b)
    (b0 : fastPhase t.shape 179827 2340 r 1 c v 0 = x)
    (b1 : fastPhase t.shape 179827 2340 r 1 c v 1 = y)
    (pos : 0<((a-b : ℕ) : ℤ)-(debit 2339 t : ℤ))
    (inc : ((a-b : ℕ) : ℤ)-(debit 2339 t : ℤ) ≤ ((x-y : ℕ) : ℤ)-(debit 2340 t : ℤ)) :
    Checked t r c v := by
  have h1 := fastSurplus_eq t 2339 r c v (by omega)
    ((Nat.mul_le_mul_right (r+t.shape.J) (by decide : 2*2339≤2*2340)).trans_lt shift)
  have h2 := fastSurplus_eq t 2340 r c v slope shift
  unfold fastSurplus at h1 h2
  rw [a0,a1] at h1
  rw [b0,b1] at h2
  refine ⟨hb,seed,reserve,width,?_,?_⟩
  · rwa [← h1]
  · rwa [← h1, ← h2]

def buffered (t : Bank) (h r : ℕ) : ℕ := cutoffCount t.shape 179827 h r-1

theorem Checked.width {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2339≤h) (hi : h≤33561) : WidthGuard t 179827 h r :=
  HelperSource.width_at_height t 179827 2339 h r lo (by omega) cert.reserve_ok cert.width_first

theorem Checked.cutoff_fit {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    (lo : 2339≤h) (hi : h≤33561) : buffered t h r+2*h*r<t.shape.m*179827 :=
  FreeSource.buffered_fit t 179827 h r (cert.width lo hi)

/-- Only the actual moving prime's lower degree bounds enter avoidance. -/
theorem Checked.avoids {t : Bank} {r c v h : ℕ} (cert : Checked t r c v)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2339≤h) (hi : h≤33561) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 1≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (buffered t h r), ¬ G∣Q :=
  HelperSource.crt_avoiding_row Crt word t 179827 r 1 c v (by omega) (by omega) (by decide)
    cert.bank_ok.nodes cert.bank_ok.moment.1 cert.bank_ok.moment.2 cert.seed_ok
    (cert.width lo hi)
    (HelperSource.surplus_positive t 179827 2339 h r 1 c v lo (by omega) cert.first cert.next)
    irr seeded slope seed excess

#print axioms Checked.avoids

end Lower6960.RescueSource
