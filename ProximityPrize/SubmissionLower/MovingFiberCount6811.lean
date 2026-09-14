import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811D

namespace ProximityPrize.SubmissionLower.MovingFiberCount6811
open scoped BigOperators
open RCN095 RCN130 RCN146 RCN260 RCN327
open MovingFiberProfile6811 MovingFiberArithmeticBase6811 MovingFiberCatalog6811 MovingFiberRegularData6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- Store each numerical row together with its proved inequalities. This avoids
kernel conversion through a table of large natural-number divisions. -/
structure Receipt (g : Fin 16) where
  scale : ℕ
  denominator : ℕ
  full : ℕ → ℕ → ℕ → ℕ
  rounded : ℕ → ℕ → ℕ → ℕ
  slope : ℕ → ℕ → ℕ
  intercept : ℕ → ℕ → ℕ
  rounded_formula : ∀ a b c, rounded a b c=slope a b*c+intercept a b
  positive : 0 < scale
  divides : ∀ j : Fin 3, (groups g j).d ∣ scale
  identity : ∀ (f : FlagDegree) (a b c : ℕ),
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph (groups g) scale f a b c
  helper : ∀ (a b c : ℕ) (j : Fin 3),
    MovingFiberArithmeticBase6811.helper (groups g j) a b c/50213 ≤ full a b c/denominator
  retained : ∀ a b c,
    graph (groups g) scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (groups g j) a b c/50213) ≤ full a b c/denominator
  rounded_bound : ∀ a b c, full a b c/denominator ≤ rounded a b c

def receipt0 : Receipt 0 where
  scale := MovingFiberArithmetic6811.G0.scale
  denominator := MovingFiberArithmetic6811.G0.denominator
  full := MovingFiberArithmetic6811.G0.full
  rounded := MovingFiberArithmetic6811.G0.rounded
  slope := fun a b => MovingFiberArithmetic6811.G0.slope a b/MovingFiberArithmetic6811.G0.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G0.intercept a b/MovingFiberArithmetic6811.G0.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G0.positive
  divides := MovingFiberArithmetic6811.G0.divides
  identity := MovingFiberArithmetic6811.G0.identity_absorption
  helper := MovingFiberArithmetic6811.G0.helper_cap
  retained := MovingFiberArithmetic6811.G0.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G0.full_cap_rounded

def receipt1 : Receipt 1 where
  scale := MovingFiberArithmetic6811.G1.scale
  denominator := MovingFiberArithmetic6811.G1.denominator
  full := MovingFiberArithmetic6811.G1.full
  rounded := MovingFiberArithmetic6811.G1.rounded
  slope := fun a b => MovingFiberArithmetic6811.G1.slope a b/MovingFiberArithmetic6811.G1.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G1.intercept a b/MovingFiberArithmetic6811.G1.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G1.positive
  divides := MovingFiberArithmetic6811.G1.divides
  identity := MovingFiberArithmetic6811.G1.identity_absorption
  helper := MovingFiberArithmetic6811.G1.helper_cap
  retained := MovingFiberArithmetic6811.G1.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G1.full_cap_rounded

def receipt2 : Receipt 2 where
  scale := MovingFiberArithmetic6811.G2.scale
  denominator := MovingFiberArithmetic6811.G2.denominator
  full := MovingFiberArithmetic6811.G2.full
  rounded := MovingFiberArithmetic6811.G2.rounded
  slope := fun a b => MovingFiberArithmetic6811.G2.slope a b/MovingFiberArithmetic6811.G2.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G2.intercept a b/MovingFiberArithmetic6811.G2.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G2.positive
  divides := MovingFiberArithmetic6811.G2.divides
  identity := MovingFiberArithmetic6811.G2.identity_absorption
  helper := MovingFiberArithmetic6811.G2.helper_cap
  retained := MovingFiberArithmetic6811.G2.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G2.full_cap_rounded

def receipt3 : Receipt 3 where
  scale := MovingFiberArithmetic6811.G3.scale
  denominator := MovingFiberArithmetic6811.G3.denominator
  full := MovingFiberArithmetic6811.G3.full
  rounded := MovingFiberArithmetic6811.G3.rounded
  slope := fun a b => MovingFiberArithmetic6811.G3.slope a b/MovingFiberArithmetic6811.G3.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G3.intercept a b/MovingFiberArithmetic6811.G3.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G3.positive
  divides := MovingFiberArithmetic6811.G3.divides
  identity := MovingFiberArithmetic6811.G3.identity_absorption
  helper := MovingFiberArithmetic6811.G3.helper_cap
  retained := MovingFiberArithmetic6811.G3.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G3.full_cap_rounded

def receipt4 : Receipt 4 where
  scale := MovingFiberArithmetic6811.G4.scale
  denominator := MovingFiberArithmetic6811.G4.denominator
  full := MovingFiberArithmetic6811.G4.full
  rounded := MovingFiberArithmetic6811.G4.rounded
  slope := fun a b => MovingFiberArithmetic6811.G4.slope a b/MovingFiberArithmetic6811.G4.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G4.intercept a b/MovingFiberArithmetic6811.G4.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G4.positive
  divides := MovingFiberArithmetic6811.G4.divides
  identity := MovingFiberArithmetic6811.G4.identity_absorption
  helper := MovingFiberArithmetic6811.G4.helper_cap
  retained := MovingFiberArithmetic6811.G4.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G4.full_cap_rounded

def receipt5 : Receipt 5 where
  scale := MovingFiberArithmetic6811.G5.scale
  denominator := MovingFiberArithmetic6811.G5.denominator
  full := MovingFiberArithmetic6811.G5.full
  rounded := MovingFiberArithmetic6811.G5.rounded
  slope := fun a b => MovingFiberArithmetic6811.G5.slope a b/MovingFiberArithmetic6811.G5.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G5.intercept a b/MovingFiberArithmetic6811.G5.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G5.positive
  divides := MovingFiberArithmetic6811.G5.divides
  identity := MovingFiberArithmetic6811.G5.identity_absorption
  helper := MovingFiberArithmetic6811.G5.helper_cap
  retained := MovingFiberArithmetic6811.G5.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G5.full_cap_rounded

def receipt6 : Receipt 6 where
  scale := MovingFiberArithmetic6811.G6.scale
  denominator := MovingFiberArithmetic6811.G6.denominator
  full := MovingFiberArithmetic6811.G6.full
  rounded := MovingFiberArithmetic6811.G6.rounded
  slope := fun a b => MovingFiberArithmetic6811.G6.slope a b/MovingFiberArithmetic6811.G6.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G6.intercept a b/MovingFiberArithmetic6811.G6.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G6.positive
  divides := MovingFiberArithmetic6811.G6.divides
  identity := MovingFiberArithmetic6811.G6.identity_absorption
  helper := MovingFiberArithmetic6811.G6.helper_cap
  retained := MovingFiberArithmetic6811.G6.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G6.full_cap_rounded

def receipt7 : Receipt 7 where
  scale := MovingFiberArithmetic6811.G7.scale
  denominator := MovingFiberArithmetic6811.G7.denominator
  full := MovingFiberArithmetic6811.G7.full
  rounded := MovingFiberArithmetic6811.G7.rounded
  slope := fun a b => MovingFiberArithmetic6811.G7.slope a b/MovingFiberArithmetic6811.G7.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G7.intercept a b/MovingFiberArithmetic6811.G7.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G7.positive
  divides := MovingFiberArithmetic6811.G7.divides
  identity := MovingFiberArithmetic6811.G7.identity_absorption
  helper := MovingFiberArithmetic6811.G7.helper_cap
  retained := MovingFiberArithmetic6811.G7.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G7.full_cap_rounded

def receipt8 : Receipt 8 where
  scale := MovingFiberArithmetic6811.G8.scale
  denominator := MovingFiberArithmetic6811.G8.denominator
  full := MovingFiberArithmetic6811.G8.full
  rounded := MovingFiberArithmetic6811.G8.rounded
  slope := fun a b => MovingFiberArithmetic6811.G8.slope a b/MovingFiberArithmetic6811.G8.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G8.intercept a b/MovingFiberArithmetic6811.G8.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G8.positive
  divides := MovingFiberArithmetic6811.G8.divides
  identity := MovingFiberArithmetic6811.G8.identity_absorption
  helper := MovingFiberArithmetic6811.G8.helper_cap
  retained := MovingFiberArithmetic6811.G8.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G8.full_cap_rounded

def receipt9 : Receipt 9 where
  scale := MovingFiberArithmetic6811.G9.scale
  denominator := MovingFiberArithmetic6811.G9.denominator
  full := MovingFiberArithmetic6811.G9.full
  rounded := MovingFiberArithmetic6811.G9.rounded
  slope := fun a b => MovingFiberArithmetic6811.G9.slope a b/MovingFiberArithmetic6811.G9.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G9.intercept a b/MovingFiberArithmetic6811.G9.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G9.positive
  divides := MovingFiberArithmetic6811.G9.divides
  identity := MovingFiberArithmetic6811.G9.identity_absorption
  helper := MovingFiberArithmetic6811.G9.helper_cap
  retained := MovingFiberArithmetic6811.G9.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G9.full_cap_rounded

def receipt10 : Receipt 10 where
  scale := MovingFiberArithmetic6811.G10.scale
  denominator := MovingFiberArithmetic6811.G10.denominator
  full := MovingFiberArithmetic6811.G10.full
  rounded := MovingFiberArithmetic6811.G10.rounded
  slope := fun a b => MovingFiberArithmetic6811.G10.slope a b/MovingFiberArithmetic6811.G10.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G10.intercept a b/MovingFiberArithmetic6811.G10.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G10.positive
  divides := MovingFiberArithmetic6811.G10.divides
  identity := MovingFiberArithmetic6811.G10.identity_absorption
  helper := MovingFiberArithmetic6811.G10.helper_cap
  retained := MovingFiberArithmetic6811.G10.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G10.full_cap_rounded

def receipt11 : Receipt 11 where
  scale := MovingFiberArithmetic6811.G11.scale
  denominator := MovingFiberArithmetic6811.G11.denominator
  full := MovingFiberArithmetic6811.G11.full
  rounded := MovingFiberArithmetic6811.G11.rounded
  slope := fun a b => MovingFiberArithmetic6811.G11.slope a b/MovingFiberArithmetic6811.G11.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G11.intercept a b/MovingFiberArithmetic6811.G11.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G11.positive
  divides := MovingFiberArithmetic6811.G11.divides
  identity := MovingFiberArithmetic6811.G11.identity_absorption
  helper := MovingFiberArithmetic6811.G11.helper_cap
  retained := MovingFiberArithmetic6811.G11.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G11.full_cap_rounded

def receipt12 : Receipt 12 where
  scale := MovingFiberArithmetic6811.G12.scale
  denominator := MovingFiberArithmetic6811.G12.denominator
  full := MovingFiberArithmetic6811.G12.full
  rounded := MovingFiberArithmetic6811.G12.rounded
  slope := fun a b => MovingFiberArithmetic6811.G12.slope a b/MovingFiberArithmetic6811.G12.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G12.intercept a b/MovingFiberArithmetic6811.G12.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G12.positive
  divides := MovingFiberArithmetic6811.G12.divides
  identity := MovingFiberArithmetic6811.G12.identity_absorption
  helper := MovingFiberArithmetic6811.G12.helper_cap
  retained := MovingFiberArithmetic6811.G12.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G12.full_cap_rounded

def receipt13 : Receipt 13 where
  scale := MovingFiberArithmetic6811.G13.scale
  denominator := MovingFiberArithmetic6811.G13.denominator
  full := MovingFiberArithmetic6811.G13.full
  rounded := MovingFiberArithmetic6811.G13.rounded
  slope := fun a b => MovingFiberArithmetic6811.G13.slope a b/MovingFiberArithmetic6811.G13.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G13.intercept a b/MovingFiberArithmetic6811.G13.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G13.positive
  divides := MovingFiberArithmetic6811.G13.divides
  identity := MovingFiberArithmetic6811.G13.identity_absorption
  helper := MovingFiberArithmetic6811.G13.helper_cap
  retained := MovingFiberArithmetic6811.G13.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G13.full_cap_rounded

def receipt14 : Receipt 14 where
  scale := MovingFiberArithmetic6811.G14.scale
  denominator := MovingFiberArithmetic6811.G14.denominator
  full := MovingFiberArithmetic6811.G14.full
  rounded := MovingFiberArithmetic6811.G14.rounded
  slope := fun a b => MovingFiberArithmetic6811.G14.slope a b/MovingFiberArithmetic6811.G14.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G14.intercept a b/MovingFiberArithmetic6811.G14.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G14.positive
  divides := MovingFiberArithmetic6811.G14.divides
  identity := MovingFiberArithmetic6811.G14.identity_absorption
  helper := MovingFiberArithmetic6811.G14.helper_cap
  retained := MovingFiberArithmetic6811.G14.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G14.full_cap_rounded

def receipt15 : Receipt 15 where
  scale := MovingFiberArithmetic6811.G15.scale
  denominator := MovingFiberArithmetic6811.G15.denominator
  full := MovingFiberArithmetic6811.G15.full
  rounded := MovingFiberArithmetic6811.G15.rounded
  slope := fun a b => MovingFiberArithmetic6811.G15.slope a b/MovingFiberArithmetic6811.G15.denominator+1
  intercept := fun a b => MovingFiberArithmetic6811.G15.intercept a b/MovingFiberArithmetic6811.G15.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6811.G15.positive
  divides := MovingFiberArithmetic6811.G15.divides
  identity := MovingFiberArithmetic6811.G15.identity_absorption
  helper := MovingFiberArithmetic6811.G15.helper_cap
  retained := MovingFiberArithmetic6811.G15.retained_cap
  rounded_bound := MovingFiberArithmetic6811.G15.full_cap_rounded

def receipt (g : Fin 16) : Receipt g := by
  exact (Fin.cases (motive := fun j : Fin 16 => Receipt j) receipt0 (Fin.cases (motive := fun j : Fin 15 => Receipt (j.succ)) receipt1 (Fin.cases (motive := fun j : Fin 14 => Receipt (j.succ.succ)) receipt2 (Fin.cases (motive := fun j : Fin 13 => Receipt (j.succ.succ.succ)) receipt3 (Fin.cases (motive := fun j : Fin 12 => Receipt (j.succ.succ.succ.succ)) receipt4 (Fin.cases (motive := fun j : Fin 11 => Receipt (j.succ.succ.succ.succ.succ)) receipt5 (Fin.cases (motive := fun j : Fin 10 => Receipt (j.succ.succ.succ.succ.succ.succ)) receipt6 (Fin.cases (motive := fun j : Fin 9 => Receipt (j.succ.succ.succ.succ.succ.succ.succ)) receipt7 (Fin.cases (motive := fun j : Fin 8 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ)) receipt8 (Fin.cases (motive := fun j : Fin 7 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt9 (Fin.cases (motive := fun j : Fin 6 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt10 (Fin.cases (motive := fun j : Fin 5 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt11 (Fin.cases (motive := fun j : Fin 4 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt12 (Fin.cases (motive := fun j : Fin 3 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt13 (Fin.cases (motive := fun j : Fin 2 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt14 (Fin.cases (motive := fun j : Fin 1 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt15 (fun i => Fin.elim0 i))))))))))))))))) g

def scales (g : Fin 16) : ℕ := (receipt g).scale
def denominators (g : Fin 16) : ℕ := (receipt g).denominator
def fulls (g : Fin 16) : ℕ → ℕ → ℕ → ℕ := (receipt g).full
def roundedCaps (g : Fin 16) : ℕ → ℕ → ℕ → ℕ := (receipt g).rounded
def sourceLimit (g : Fin 16) : ℕ := Finset.univ.sup (fun j : Fin 3 => (groups g j).L)

theorem scale_positive (g : Fin 16) : 0 < scales g := (receipt g).positive
theorem scale_divides (g : Fin 16) (j : Fin 3) : (groups g j).d ∣ scales g := (receipt g).divides j
theorem identity_absorption (g : Fin 16) (f : FlagDegree) (a b c : ℕ) :
    scales g*131073*80861*identityDegree f a b c ≤ 50213*graph (groups g) (scales g) f a b c :=
  (receipt g).identity f a b c
theorem helper_cap (g : Fin 16) (a b c : ℕ) (j : Fin 3) :
    helper (groups g j) a b c/50213 ≤ fulls g a b c/denominators g := (receipt g).helper a b c j
theorem retained_cap (g : Fin 16) (a b c : ℕ) :
    graph (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c/scales g+
      (∑ j : Fin 3, coeff (groups g j) a b c/50213) ≤ fulls g a b c/denominators g :=
  (receipt g).retained a b c
theorem rounded_cap (g : Fin 16) (a b c : ℕ) :
    fulls g a b c/denominators g ≤ roundedCaps g a b c := (receipt g).rounded_bound a b c

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem bound_le_full (S : Data nodes u0 u1) (hown : Own S) (g : Fin 16) :
    bound S (groups g) (scales g) ≤
      fulls g (S.r-3) (S.y-S.r-2) (S.t-S.y)/denominators g := by
  obtain ⟨a,ha⟩ : ∃ a, S.r=a+3 := ⟨S.r-3,by have := S.rpos; omega⟩
  obtain ⟨b,hb⟩ : ∃ b, S.y=a+3+(b+2) := ⟨S.y-S.r-2,by have := S.ry; omega⟩
  obtain ⟨c,hc⟩ : ∃ c, S.t=a+3+(b+2)+c := ⟨S.t-S.y,by have := S.yt; omega⟩
  have hv : S.y-S.r=b+2 := by omega
  have hz : S.t-S.y=c := by omega
  have har : S.r-3=a := by omega
  have hbr : S.y-S.r-2=b := by omega
  have hp (R U T : ℕ) : AsymmetricHelper.leftRegularCountCap (S.pair R U T)=
      pairNumerator a b c U R T/50213 := by
    unfold AsymmetricHelper.leftRegularCountCap
    rw [pair_numerator S a b c ha hb hc]
    norm_num only [Data.pair,UnequalParameters.gap]
  have hcoeff (j : Fin 3) : coefficientCap S (groups g j)=coeff (groups g j) a b c/50213 := hp _ _ _
  have hhelper (j : Fin 3) : helperCap S (groups g j)=helper (groups g j) a b c/50213 := by
    unfold helperCap
    rw [hp,ha,hb,hc]
    have h1 : a+3-1=a+2 := by omega
    have h2 : a+3+(b+2)-1=a+b+4 := by omega
    have h3 : a+3+(b+2)+c-1=a+b+c+4 := by omega
    simp only [h1,h2,h3,helper]
  have hn : number (groups g) (scales g) S.t S.y S.r (originalCumulativeFlag S.F)=
      graph (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c := by
    rw [hown,hv,hz,hc,hb,ha,number_coordinates]
  rw [har,hbr,hz]
  unfold bound
  apply max_le
  · apply Finset.sup_le
    intro j _
    rw [hhelper]
    exact helper_cap g a b c j
  · rw [hn]
    simp_rw [hcoeff]
    exact retained_cap g a b c

/-- Actual interpolants and all exceptional cases are supplied internally. -/
theorem count_group (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (g : Fin 16) (hL : sourceLimit g < S.t) :
    S.seeds.card ≤ roundedCaps g (S.r-3) (S.y-S.r-2) (S.t-S.y) := by
  obtain ⟨P,hP⟩ := exists_group nodes u0 u1 hI g
  have hLt (j : Fin 3) : (groups g j).L < RCN234.wt RCN156.residualTotalWeights S.F := by
    rw [own_total S hown]
    exact (Finset.le_sup (f := fun j : Fin 3 => (groups g j).L) (Finset.mem_univ j)).trans_lt hL
  have hid (f : FlagDegree) : scales g*131073*80861*
      identityCurveDegree f (LocatorHybridCells.cellA S.t S.y)
        (LocatorHybridCells.cellB S.y S.r) (LocatorHybridCells.cellS S.r) w ≤
        50213*number (groups g) (scales g) S.t S.y S.r f := by
    obtain ⟨a,ha⟩ : ∃ a, S.r=a+3 := ⟨S.r-3,by have := S.rpos; omega⟩
    obtain ⟨b,hb⟩ : ∃ b, S.y=a+3+(b+2) := ⟨S.y-S.r-2,by have := S.ry; omega⟩
    obtain ⟨c,hc⟩ : ∃ c, S.t=a+3+(b+2)+c := ⟨S.t-S.y,by have := S.yt; omega⟩
    rw [ha,hb,hc,identity_coordinates,number_coordinates]
    exact identity_absorption g f a b c
  have hcount := count_of_interpolants S hI (groups g) (wellFormed g) (scales g)
    (scale_positive g) (scale_divides g) P hP hLt
    (fun j => (catalog_gates S g j).1) (fun j => (catalog_gates S g j).2) hid
  exact (hcount.trans (bound_le_full S hown g)).trans (rounded_cap g _ _ _)

#print axioms count_group
end ProximityPrize.SubmissionLower.MovingFiberCount6811
