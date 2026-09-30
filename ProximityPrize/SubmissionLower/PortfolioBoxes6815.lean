import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.PortfolioBoxes6815
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

structure Point where
  s : ℕ
  b : ℕ
  u : ℕ
  t : ℕ
  deriving DecidableEq
structure Box where
  slo : ℕ
  shi : ℕ
  blo : ℕ
  bhi : ℕ
  ulo : ℕ
  uhi : ℕ
  tlo : ℕ
  thi : ℕ
  deriving DecidableEq

def Contains (a : Box) (p : Point) : Prop :=
  a.slo≤p.s ∧ p.s≤a.shi ∧ a.blo≤p.b ∧ p.b≤a.bhi ∧
  a.ulo≤p.u ∧ p.u≤a.uhi ∧ a.tlo≤p.t ∧ p.t≤a.thi
def Admissible (m : ℕ) (p : Point) : Prop :=
  m≤p.s ∧ 2≤p.s ∧ (3≤m → 5≤p.s) ∧ 2*p.s≤p.b ∧ p.s≤p.u ∧ p.b≤p.u+p.s ∧ p.u≤p.t
def Empty (a : Box) : Prop := a.shi<a.slo ∨ a.bhi<a.blo ∨ a.uhi<a.ulo ∨ a.thi<a.tlo
instance (a : Box) : Decidable (Empty a) := by unfold Empty; infer_instance

def step (m : ℕ) (a : Box) : Box :=
  let sl := max (max (max (max a.slo m) 2) (if 3≤m then 5 else 2)) (a.blo-a.uhi)
  let sh := min a.shi (a.bhi/2)
  let bl := max a.blo (2*sl)
  let bh := min a.bhi (a.uhi+sh)
  let ul := max (max a.ulo sl) (bl-sh)
  let uh := min a.uhi a.thi
  let tl := max a.tlo ul
  ⟨sl,sh,bl,bh,ul,uh,tl,a.thi⟩

def normalize (m : ℕ) : ℕ → Box → Box
  | 0,a => a
  | n+1,a => normalize m n (step m a)

theorem step_contains (m : ℕ) (a : Box) (p : Point)
    (ha : Admissible m p) (hp : Contains a p) : Contains (step m a) p := by
  unfold Admissible Contains at *
  dsimp only [step]
  split_ifs with hm <;> omega

theorem normalize_contains (m n : ℕ) (a : Box) (p : Point)
    (ha : Admissible m p) (hp : Contains a p) : Contains (normalize m n a) p := by
  induction n generalizing a with
  | zero => exact hp
  | succ n ih => exact ih (step m a) (step_contains m a p ha hp)

def coordinate (p : Point) (axis : Fin 4) : ℕ := ![p.s,p.b,p.u,p.t] axis
def lower (a : Box) (axis : Fin 4) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with shi:=v}
  | 1 => {a with bhi:=v}
  | 2 => {a with uhi:=v}
  | _ => {a with thi:=v}
def upper (a : Box) (axis : Fin 4) (v : ℕ) : Box :=
  match axis.val with
  | 0 => {a with slo:=v+1}
  | 1 => {a with blo:=v+1}
  | 2 => {a with ulo:=v+1}
  | _ => {a with tlo:=v+1}

theorem split_contains (a : Box) (p : Point) (axis : Fin 4) (v : ℕ) (hp : Contains a p) :
    Contains (lower a axis v) p ∨ Contains (upper a axis v) p := by
  fin_cases axis <;> simp [lower,upper,Contains] at * <;> omega

def Covered (m : ℕ) (valid : Box → Prop) (a : Box) : Prop :=
  ∀ p, Admissible m p → Contains a p → ∃ b, valid b ∧ Contains b p

theorem covered_leaf (m : ℕ) (valid : Box → Prop) (a : Box) (h : valid a) : Covered m valid a := by
  intro p _ hp
  exact ⟨a,h,hp⟩
theorem covered_normalize (m : ℕ) (valid : Box → Prop) (a b : Box)
    (he : normalize m 8 a=b) (h : Covered m valid b) : Covered m valid a := by
  intro p ha hp
  apply h p ha
  rw [←he]
  exact normalize_contains m 8 a p ha hp
theorem covered_split (m : ℕ) (valid : Box → Prop) (a : Box) (axis : Fin 4) (v : ℕ)
    (hl : Covered m valid (lower a axis v)) (hh : Covered m valid (upper a axis v)) :
    Covered m valid a := by
  intro p ha hp
  rcases split_contains a p axis v hp with hp | hp
  · exact hl p ha hp
  · exact hh p ha hp

end ProximityPrize.SubmissionLower.PortfolioBoxes6815
