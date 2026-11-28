import ProximityPrize.SubmissionLower.Z6970ExpandedPivotContact
import ProximityPrize.SubmissionLower.Z6970PlateauLines

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3500000

namespace ExpandedPlateauSum6970
open ExpandedPivotOpt6970 (Triple)
open KoalaPiecewiseTriangle (Line)

private theorem nat_from_lower {a b : ℕ} (h : ∀ n, n ≤ a ↔ n ≤ b) : a=b :=
  le_antisymm ((h a).mp le_rfl) ((h b).mpr le_rfl)

private theorem gain_closed (w k p q : ℕ) :
    let u := min k (min ((p-w)/2) ((q-w)/3))
    min (w+u) (min (p-u) (q-2*u)) =
      min (w+k) (min p (min q (min ((w+p)/2) ((2*w+q)/3)))) := by
  dsimp only
  apply nat_from_lower
  intro n
  let u := min k (min ((p-w)/2) ((q-w)/3))
  change n ≤ min (w+u) (min (p-u) (q-2*u)) ↔ _
  simp only [le_min_iff]
  have hcup : u ≤ k := min_le_left _ _
  have hp0 : u ≤ (p-w)/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hq0 : u ≤ (q-w)/3 := le_trans (min_le_right _ _) (min_le_right _ _)
  by_cases hp : p < w
  · have hz : u=0 := by omega
    rw [hz]
    omega
  by_cases hq : q < w
  · have hz : u=0 := by omega
    rw [hz]
    omega
  constructor
  · rintro ⟨ha,hb,hc⟩
    omega
  · rintro ⟨hk,hp',hq',hpq,hqq⟩
    have hcap : n-w ≤ u := by
      apply le_min (by omega) (le_min (by omega) (by omega))
    omega

theorem contact_gain (p : Triple) :
    p.contact = p.c+2*p.f+p.room +
      min (p.room + min (min (p.b/3) p.room) (500-p.f))
        (min (p.b+p.c) (min (p.b+(500-p.f))
          (min ((p.room+(p.b+p.c))/2) ((2*p.room+(p.b+(500-p.f)))/3)))) := by
  rw [ExpandedPivotOpt6970.contact_eq_gain]
  exact congrArg (fun z : ℕ => p.c+2*p.f+p.room+z)
    (gain_closed p.room p.fourthCap (p.b+p.c) (p.b+(500-p.f)))

private theorem amin (a b c : ℕ) : a+min b c = min (a+b) (a+c) := by omega
private theorem dmin (a : ℤ) (b c : ℕ) : a-((min b c : ℕ):ℤ) = max (a-b) (a-c) := by omega

theorem exact_argument (c f r x : ℕ) (hr : r < 3) (hf : f ≤ 500)
    (hi : 3*x+r+2*c+3*f ≤ 1679) :
    let p : Triple := ⟨3*x+r,c,f⟩
    let L := lines c f r
    3000+(p.index : ℤ)-(p.contact : ℤ)-1679 = ExpandedPlateauIntegral6970.value (L.1.at x) x L.2 := by
  let p : Triple := ⟨3*x+r,c,f⟩
  let a : ℤ := 1321+(p.index:ℤ)-((p.c+2*p.f+p.room:ℕ):ℤ)
  let w : ℤ := 1679-2*(c:ℤ)-3*(f:ℤ)
  let u : ℤ := 500-(f:ℤ)
  let z : ℤ := 1321+2*(r:ℤ)+c+f-w
  let b := p.b
  let v := p.room
  let C := 500-f
  let pr := fun n : ℕ => a-(n:ℤ)
  let A := pr (v+b/3)
  let B := pr (v+v)
  let D := pr (v+C)
  let E := pr (b+c)
  let F := pr (b+C)
  let G := pr ((v+(b+c))/2)
  let H := pr ((2*v+(b+C))/3)
  change 3000+(p.index:ℤ)-(p.contact:ℤ)-1679 = _
  have form : 3000+(p.index:ℤ)-(p.contact:ℤ)-1679 =
      max (max (max (max (max (max E F) G) H) A) D) B := by
    rw [contact_gain]
    push_cast only [Nat.cast_add]
    have h (t : ℕ) : 3000+(p.index:ℤ)-
        (((p.c:ℤ)+((2*p.f:ℕ):ℤ))+(p.room:ℤ)+(t:ℤ))-1679 = pr t := by
      dsimp [pr,a]
      push_cast
      ring
    rw [h]
    dsimp only [A,B,D,E,F,G,H,pr,b,v,C]
    simp only [amin,dmin]
    simp only [show p.c = c from rfl, show p.f = f from rfl]
    ac_rfl
  have cg : (p.room:ℤ) = w-(3*x+r:ℕ) := by dsimp [p,w,Triple.room,Triple.index];omega
  have ci : (p.index:ℤ) = 3*(x:ℤ)+r+2*c+3*f := by simp [p,Triple.index]
  have hA : A = z-w+r+8*(x:ℤ) := by dsimp [A,pr,a,z,b,v,w,p,Triple.room,Triple.index]; omega
  have hB : B = z-2*w+2*r+12*(x:ℤ) := by dsimp [B,pr,a,z,v,w,p,Triple.room,Triple.index]; omega
  have hD : D = z-w+r-u+9*(x:ℤ) := by dsimp [D,pr,a,z,b,v,u,w,p,C,Triple.room,Triple.index]; omega
  have hEF : max E F = z-r-min (c:ℤ) u+3*(x:ℤ) := by
    dsimp [E,F,pr,a,z,b,v,u,w,p,C,Triple.room,Triple.index]
    omega
  have hG : G = z-(w+c)/2+6*(x:ℤ) := by dsimp [G,pr,a,z,b,v,w,p,Triple.room,Triple.index]; omega
  have hH : H = z-(2*w-r+u)/3+7*(x:ℤ) := by dsimp [H,pr,a,z,b,v,w,u,C,p,Triple.room,Triple.index]; omega
  rw [form,hEF,hG,hH,hA,hD,hB]
  rfl

end ExpandedPlateauSum6970
