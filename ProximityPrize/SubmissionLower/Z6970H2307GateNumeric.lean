import ProximityPrize.SubmissionLower.Z6970H2307GateRay

set_option autoImplicit false
set_option Elab.async false

namespace ExpandedGate6970.Numeric
open K1_13 (Shape)
open Low6969GateCell
open Low6969GateBilinear (tpOf opOf)

def DEN : ℕ := 10000000
def kT : ℕ := Low6969Prices.taylorLength - 4
def rayT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p kT (Low6969Prices.bentLift kT p).2 (Low6969Prices.bentLift (kT + 1) p).2).ray
def rayO (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart (Low6969Prices.taylorLength + 1) p.chamber)
    (K1_13.chart (Low6969Prices.taylorLength + 2) p.chamber)).ray


def cd (x y : ℤ) : ℕ := if y ≤ 0 then 0 else (((DEN : ℤ) * x).toNat + y.toNat - 1) / y.toNat

def thNum (rx rh : Fin 3 → Fin 3 → ℤ) : ℕ :=
  ((List.finRange 3).flatMap fun i => (List.finRange 3).map fun k => cd (rx i k) (rh i k)).foldl max 0

def thOK (rx rh : Fin 3 → Fin 3 → ℤ) : Bool :=
  decide (∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k)

theorem thOK_spec {rx rh : Fin 3 → Fin 3 → ℤ} (h : thOK rx rh = true) :
    ∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k := of_decide_eq_true h

def hiS (G : Gt) : Shape := ⟨G.xb, G.xj, G.xt⟩
def inR (G : Gt) (x : Shape) : Bool :=
  Nat.ble G.lb x.b && Nat.ble G.lj x.j && Nat.ble G.lt x.t && Nat.ble x.b G.xb && Nat.ble x.j G.xj && Nat.ble x.t G.xt
def tfB (x : Shape) : Bool := Nat.ble (3 * x.t + 3) x.j && Nat.ble (x.j + 1) x.b

def numT (G : Gt) (x : Shape) : ℕ := thNum (rayT x) (Gt.mat G)
def numO (G : Gt) (x : Shape) : ℕ := thNum (rayO x) (Gt.mat G)
def Ax (num A : ℕ) : ℕ := (num * A + DEN - 1) / DEN

def valid (x : Shape) : Bool := Nat.ble x.j (2 * x.b + x.t)


theorem ceil_le (N D : ℕ) (hD : 0 < D) : N ≤ D * ((N + D - 1) / D) := by
  have hd := Nat.div_add_mod (N+D-1) D
  have hr := Nat.mod_lt (N+D-1) hD
  omega

theorem inR_props {G : Gt} {x : Shape} (h : inR G x = true) :
    G.lb ≤ x.b ∧ G.lj ≤ x.j ∧ G.lt ≤ x.t ∧ x.b ≤ G.xb ∧ x.j ≤ G.xj ∧ x.t ≤ G.xt := by
  simp only [inR, Bool.and_eq_true, Nat.ble_eq] at h
  tauto

theorem tfB_true {x : Shape} (h : tfB x = true) : 3 * x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b := by
  simpa [tfB, Nat.ble_eq] using h

def quote (G : Gt) (x : Shape) : ℕ :=
  Ax (if G.lift then numO G x else numT G x) G.A

end ExpandedGate6970.Numeric
