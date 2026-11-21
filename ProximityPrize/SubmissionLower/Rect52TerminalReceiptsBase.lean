import ProximityPrize.SubmissionLower.Rect52TerminalArithmetic

set_option Elab.async false
set_option maxRecDepth 18000

namespace Rect52Terminal

open High52TerminalArithmetic (Parts)
open P0_10_5 (Row scan)
open private scan_sum from ProximityPrize.SubmissionLower.PortHighBase

def scanRow (f : ℕ → ℕ → ℤ) (t : ℕ) : Row := ⟨true, f 2391 t, f 2392 t⟩

theorem terms_of_parts {f : ℕ → ℕ → ℤ} {last n : ℕ} {gain next : ℤ}
    (parts : Parts (scanRow f) last 0 n gain next) :
    (∑ t ∈ Finset.range n, f 2391 t) = gain ∧
      (∑ t ∈ Finset.range n, f 2392 t) = next := by
  have h₁ := scan_sum (scanRow f) 0 n false
  have h₂ := scan_sum (scanRow f) 0 n true
  rw [parts.scan_eq] at h₁ h₂
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.zero_add, scanRow] at h₁ h₂
  exact ⟨h₁.symm, h₂.symm⟩

def rectRow (e n : ℕ) : ℕ → ℕ → ℤ := fun h t =>
  blockTerm bank.shape h e (long e) (short e) (n/2) ((n+1)/2) t

def stockRow (h t : ℕ) : ℤ :=
  High52TerminalArithmetic.phaseBlock bank.shape h 23 0 0 t -
    High52TerminalArithmetic.phaseBlock bank.shape h 23 0 1 t

theorem rectangle_of_parts {e k n last : ℕ} {gain next cost costNext : ℤ}
    (parts : Parts (scanRow (rectRow e k)) last 0 n gain next)
    (hn : n = bank.shape.J + orderEnd bank.shape e (long e) (short e) (k/2) ((k+1)/2))
    (he : 0<e) (hL : 120 * (rectangleDebit 2391 (long e) (short e) : ℤ) = cost)
    (hR : 120 * (rectangleDebit 2392 (long e) (short e) : ℤ) = costNext)
    (hp : cost < gain) (hr : gain + costNext ≤ next + cost) :
    0 < rectangleSurplus 2391 e (long e) (short e) (k/2) ((k+1)/2) ∧
      rectangleSurplus 2391 e (long e) (short e) (k/2) ((k+1)/2) ≤
        rectangleSurplus 2392 e (long e) (short e) (k/2) ((k+1)/2) := by
  obtain ⟨h₁,h₂⟩ := terms_of_parts parts
  rw [hn] at h₁ h₂
  unfold rectRow at h₁ h₂
  rw [block_sum _ _ _ _ _ _ _ (by decide) (by decide) he (by decide)] at h₁ h₂
  unfold rectangleSurplus
  constructor <;> omega

theorem stock_of_parts {n last : ℕ} {gain next cost costNext : ℤ}
    (parts : Parts (scanRow stockRow) last 0 n gain next)
    (hn : n = bank.shape.J + High52TerminalArithmetic.orderEnd bank.shape 23 0)
    (hL : High52TerminalArithmetic.scaledDebit bank.shape bank.nodeRows bank.poleMoment 2391 = cost)
    (hR : High52TerminalArithmetic.scaledDebit bank.shape bank.nodeRows bank.poleMoment 2392 = costNext)
    (hp : cost < gain) (hr : gain+costNext ≤ next+cost) :
    High52TerminalArithmetic.BlockChecks bank.shape bank.nodeRows bank.poleMoment 2391 23 0 := by
  obtain ⟨h₁,h₂⟩ := terms_of_parts parts
  rw [hn] at h₁ h₂
  unfold stockRow at h₁ h₂
  unfold High52TerminalArithmetic.BlockChecks High52TerminalArithmetic.blockSurplus
  rw [h₁,h₂,hL,hR]
  constructor <;> omega

end Rect52Terminal
