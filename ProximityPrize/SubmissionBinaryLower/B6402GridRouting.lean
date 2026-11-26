import ProximityPrize.SubmissionBinaryLower.Native6402Grid
import ProximityPrize.SubmissionBinaryLower.B6402RowTransport

namespace ProximityPrize.SubmissionBinaryLower.B6402GridRouting
open B6401Params hiding A
open B6402T4Rows B6402IntFarkas B6402GridProfile B6402Table4Common B6402Table4K B6402RowTransport
open Native6402Grid
set_option autoImplicit false
set_option maxHeartbeats 2400000

def arity : Branch → ℕ
| .inl a => t4aNumVars a
| .inr _ => 49

def rows (k : Key) : Array SparseRow × Array SparseRow :=
  let build := match k.branch with | .inl a => buildT4ARows a | .inr b => buildT4BRows b
  build k.cLoNum k.cLoDen k.cHiNum k.cHiDen k.gap.1 k.gap.2.1 k.gap.2.2.1 k.gap.2.2.2

def Point (D : KerD45Data) (n : ℕ) (data : Array SparseRow × Array SparseRow) : Prop :=
  ∃ h : 5<n, ∃ x : Fin (n) → ℚ,
    (∀ j,0≤x j) ∧ x ⟨0,by omega⟩=(D.n0:ℚ)/N ∧ x ⟨1,by omega⟩=(D.n1:ℚ)/N ∧
    x ⟨2,by omega⟩=(D.n2:ℚ)/N ∧ x ⟨3,by omega⟩=(D.n3:ℚ)/N ∧ x ⟨4,by omega⟩=(D.nt:ℚ)/N ∧
    x ⟨n-1,by omega⟩=(D.W_F:ℚ)/wY ∧
    (∀ r∈data.1.toList,RowValid (n) r ∧ RowSatLe x r) ∧
    (∀ r∈data.2.toList,RowValid (n) r ∧ RowSatEq x r)

def Feasible (D : KerD45Data) (k : Key) : Prop := Point D (arity k.branch) (rows k)

private theorem sameGap (k : Key) (r : Fin 5) (valid : coversGap k r) :
    let b:=B6401T4Grid.std5Bounds r
    (k.gap.1=b.1 ∧ k.gap.2.1=b.2.1 ∧ k.gap.2.2.1=b.2.2.1 ∧ k.gap.2.2.2=b.2.2.2) ∨
    (k.gap.1=0 ∧ k.gap.2.1=1 ∧ k.gap.2.2.1=1 ∧ k.gap.2.2.2=1) := by
  rcases valid with h|h
  · left; simp [h]
  · right; simp [h,single]

noncomputable def GapValue (D : KerD45Data) : ℤ :=
  (D.W_F:ℤ)-(wY-1:ℕ)-(D.a1+3*D.a2+5*D.a3:ℕ)+D.a0

theorem route (D : KerD45Data) (r : Fin 5) (upper : (D.W_F:ℚ)/wY≤28/5)
    (lowerGap : ((B6401T4Grid.std5Bounds r).2.1:ℤ)*GapValue D≥((B6401T4Grid.std5Bounds r).1:ℤ)*N)
    (upperGap : (B6401T4Grid.std5Bounds r).2.2.1<(B6401T4Grid.std5Bounds r).2.2.2 →
      ((B6401T4Grid.std5Bounds r).2.2.2:ℤ)*GapValue D≤((B6401T4Grid.std5Bounds r).2.2.1:ℤ)*N) :
    EscapeUZero D ∨ ∃ j : Fin 237,coversGap (key j) r ∧ lo (key j)≤(D.W_F:ℚ)/wY ∧
        (D.W_F:ℚ)/wY≤hi (key j) ∧ Feasible D (key j) := by
  let g:= B6401T4Grid.std5Bounds r
  have hd1 : 0<g.2.1 := by fin_cases r <;> decide
  have hd2 : 0<g.2.2.2 := by fin_cases r <;> decide
  have lw : 5*wY-1≤D.W_F := by have := D.hWF_lo; omega
  have left : ((5*wY-1:ℕ):ℚ)/wY≤(D.W_F:ℚ)/wY := div_le_div_of_nonneg_right (by exact_mod_cast lw) (by positivity)
  have startOk : first≤(D.W_F:ℚ)/wY := by
    have e : first=((5*wY-1:ℕ):ℚ)/wY := by norm_num [first,wY]
    rwa [e]
  have z := table4_algebra_dichotomy D (5*wY-1) wY 28 5 g.1 g.2.1 g.2.2.1 g.2.2.2
    (by decide) (by decide) hd1 hd2 left upper lowerGap upperGap
  rcases z with escape|⟨br,valid,x,nn,h0,h1,h2,h3,h4,hw,hu,he⟩|⟨br,hq,ho,x,nn,h0,h1,h2,h3,h4,hw,hu,he⟩
  · exact Or.inl escape
  · obtain ⟨tagId,et⟩ := tag_A br valid
    obtain ⟨j,ej,gap,ld,ud,lc,uc⟩ := select tagId r _ startOk upper
    have eq := ej.trans et
    have sat := buildT4ARows_transport br x ld ud (hw.symm ▸ lc) (hw.symm ▸ uc) (sameGap (key j) r gap) hu he
    right; refine ⟨j,gap,lc,uc,?_⟩
    unfold Feasible rows; rw [eq]
    exact ⟨by cases br <;> simp [arity,t4aNumVars],x,nn,h0,h1,h2,h3,h4,hw,sat⟩
  · obtain ⟨tagId,et⟩ := tag_B br hq ho
    obtain ⟨j,ej,gap,ld,ud,lc,uc⟩ := select tagId r _ startOk upper
    have eq := ej.trans et
    have sat := buildT4BRows_transport br x ld ud (hw.symm ▸ lc) (hw.symm ▸ uc) (sameGap (key j) r gap) hu he
    right; refine ⟨j,gap,lc,uc,?_⟩
    unfold Feasible rows; rw [eq]
    exact ⟨(by decide : 5<49),x,nn,h0,h1,h2,h3,h4,hw,sat⟩

#print axioms route
end ProximityPrize.SubmissionBinaryLower.B6402GridRouting
