import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Union

set_option Elab.async false

/-! Scalar two-chart computations for the product of the abscissa and
parameter lines. Integer pairs are Laurent monomials on their common torus. -/
namespace Lower6960.ChartSections
abbrev Exponent := ℤ×ℤ
abbrev Chart := Bool×Bool

/-- At infinity the frame for the twist `-d` has highest exponent `-d`. -/
def fits (d : ℕ) (s : Bool) (i : ℤ) : Prop :=
  if s then i ≤ -(d:ℤ) else 0 ≤ i

def allowed (a b : ℕ) (s : Chart) (m : Exponent) : Prop :=
  fits a s.1 m.1 ∧ fits b s.2 m.2

def overlap (a b : ℕ) (s t : Chart) (m : Exponent) : Prop :=
  (s.1=t.1 → fits a s.1 m.1) ∧ (s.2=t.2 → fits b s.2 m.2)

private def opposite (i : ℤ) : Bool := decide (0 ≤ i)

private theorem excluded (d : ℕ) (hd : 0<d) (i : ℤ) : ¬fits d (opposite i) i := by
  by_cases hi : 0 ≤ i
  · simp [opposite,hi,fits]; omega
  · simp [opposite,hi,fits]

/-- The Cech first obstruction for a negative twist in both coordinates
vanishes. The four potentials and their correction all have finite support. -/
theorem negative_correction {k : Type*} [AddCommGroup k] (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (p : Chart→Exponent→₀k)
    (compatible : ∀ s t m,¬overlap a b s t m → (p s) m=(p t) m) :
    ∃ c : Exponent→₀k, ∀ s m,¬allowed a b s m → (p s-c) m=0 := by
  classical
  let coeff (m : Exponent) := p (opposite m.1,opposite m.2) m
  let support := Finset.univ.biUnion fun s : Chart=>(p s).support
  let c : Exponent→₀k := Finsupp.onFinset support coeff (fun m hm=>
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hm⟩)
  refine ⟨c,?_⟩
  rintro ⟨s,t⟩ ⟨i,j⟩ bad
  change ¬(fits a s i ∧ fits b t j) at bad
  change p (s,t) (i,j)-p (opposite i,opposite j) (i,j)=0
  apply sub_eq_zero.mpr
  by_cases bx : fits a s i
  · have bz : ¬fits b t j := fun z=>bad ⟨bx,z⟩
    calc p (s,t) (i,j) = p (opposite i,t) (i,j) := compatible (s,t) (opposite i,t) (i,j) (fun h=>bz (h.2 rfl))
         _ = _ := compatible (opposite i,t) (opposite i,opposite j) (i,j) (fun h=>excluded a ha i (h.1 rfl))
  · calc p (s,t) (i,j) = p (s,opposite j) (i,j) := compatible (s,t) (s,opposite j) (i,j) (fun h=>bx (h.1 rfl))
         _ = _ := compatible (s,opposite j) (opposite i,opposite j) (i,j) (fun h=>excluded b hb j (h.2 rfl))

/-- A negative twist in just one direction already has no global function. -/
theorem no_global {k : Type*} [Zero k] (a b : ℕ) (negative : 0<a ∨ 0<b)
    (f : Exponent→₀k) (regular : ∀ s m,¬allowed a b s m → f m=0) : f=0 := by
  ext m
  rcases negative with ha | hb
  · exact regular (opposite m.1,false) m (fun h=>excluded a ha m.1 h.1)
  · exact regular (false,opposite m.2) m (fun h=>excluded b hb m.2 h.2)

#print axioms negative_correction
#print axioms no_global

section
variable {k ι J : Type*} [CommRing k] [Fintype ι]

/-- A row of Laurent-polynomial coefficients acting on the coordinates of
a rational subspace. Only the finite supports of the coefficients matter. -/
def relation (column : ι→J) (coefficient : ι→k) (offset : ι→Exponent)
    (u : J→Exponent→₀k) (m : Exponent) : k :=
  ∑ i,coefficient i*u (column i) (m.1-(offset i).1,m.2-(offset i).2)

/-- If the coordinates of a section obey finitely supported linear
relations, the scalar corrections obey the same relations as soon as
the negative twist exceeds their abscissa widths. -/
theorem correction_with_relations {L : Type*} (a b B : ℕ) (wide : 2*B<a) (hb : 0<b)
    (col : L→ι→J) (coeff : L→ι→k) (off : L→ι→Exponent)
    (bound : ∀ l i,-(B:ℤ)≤(off l i).1 ∧ (off l i).1≤(B:ℤ))
    (u : Chart→J→Exponent→₀k)
    (compatible : ∀ j s t m,¬overlap a b s t m → u s j m=u t j m)
    (closed : ∀ l s m,relation (col l) (coeff l) (off l) (u s) m=0) :
    ∃ v : J→Exponent→₀k,
      (∀ s j m,¬allowed a b s m → (u s j-v j) m=0) ∧
      ∀ l m,relation (col l) (coeff l) (off l) v m=0 := by
  classical
  choose v hv using fun j=>negative_correction a b (by omega) hb (fun s=>u s j) (compatible j)
  refine ⟨v,fun s j=>hv j s,?_⟩
  intro l m
  let s : Chart := (decide (-(B:ℤ) ≤ m.1),false)
  have agree (i) : u s (col l i) (m.1-(off l i).1,m.2-(off l i).2)=
      v (col l i) (m.1-(off l i).1,m.2-(off l i).2) := by
    apply sub_eq_zero.mp
    apply hv (col l i) s
    intro h
    have x:=h.1
    obtain ⟨low,high⟩:=bound l i
    by_cases side : -(B:ℤ)≤m.1
    · simp [s,side,fits] at x; omega
    · simp [s,side,fits] at x; omega
  calc _ = relation (col l) (coeff l) (off l) (u s) m := by
             unfold relation
             exact Finset.sum_congr rfl (fun i _=>congrArg (coeff l i*·) (agree i).symm)
       _ = 0 := closed l s m

#print axioms correction_with_relations
end
end Lower6960.ChartSections
