import ProximityPrize.SubmissionLower.Low53At2389SurfaceLinearFour
import ProximityPrize.SubmissionLower.Low48BentSupport

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low53At2389SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low53At2389Price (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
open Low48BentLattice (Chamber)

/-- Apply the signed five-slot difference before clipping to natural numbers. -/
private def cube (F : ℤ → ℤ → ℤ → ℤ → ℤ) (p q r s t : BentCap) : ℤ :=
  ([p,q,r,s,t].sublists.foldl (fun acc boxes =>
    let x := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) * F x.1.b x.1.j x.1.t x.2) 0)

private def signedFive := cube bentIntegral

private theorem cube_add (F G : ℤ → ℤ → ℤ → ℤ → ℤ) (p q r s t : BentCap) :
    cube (fun b j t h => F b j t h + G b j t h) p q r s t =
      cube F p q r s t + cube G p q r s t := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_sub (F G : ℤ → ℤ → ℤ → ℤ → ℤ) (p q r s t : BentCap) :
    cube (fun b j t h => F b j t h - G b j t h) p q r s t =
      cube F p q r s t - cube G p q r s t := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_mul (c : ℤ) (F : ℤ → ℤ → ℤ → ℤ → ℤ) (p q r s t : BentCap) :
    cube (fun b j t h => c * F b j t h) p q r s t = c * cube F p q r s t := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring


/-- The homogeneous monomial contributes only terms with one coordinate from
each slot. Check the cancellations one monomial at a time. -/
private theorem cube_HHHHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ _ _ h => h^5) p (q,0) r s t =
    0 := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_TTHHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ _ t h => t^2 * h^3) p (q,0) r s t =
    (12 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 12 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_TTTHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ _ t h => t^3 * h^2) p (q,0) r s t =
    (12 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 12 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 12 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 12 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_TTTTH (q : Shape) (p r s t : BentCap) :
    cube (fun _ _ t h => t^4 * h) p (q,0) r s t =
    (24 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 24 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 24 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 24 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JHHHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j _ h => j * h^4) p (q,0) r s t =
    (24 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)) * (q.j : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JTHHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j * t * h^3) p (q,0) r s t =
    (6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)) * (q.j : ℤ)
    + (6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JTTHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j * t^2 * h^2) p (q,0) r s t =
    (4 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.j : ℤ)
    + (4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JTTTH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j * t^3 * h) p (q,0) r s t =
    (6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.j : ℤ)
    + (6 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JJHHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j _ h => j^2 * h^3) p (q,0) r s t =
    (12 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 12 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)) * (q.j : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JJTHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j^2 * t * h^2) p (q,0) r s t =
    (4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.j : ℤ)
    + (4 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JJTTH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j^2 * t^2 * h) p (q,0) r s t =
    (4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.j : ℤ)
    + (4 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JJJHH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j _ h => j^3 * h^2) p (q,0) r s t =
    (12 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 12 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 12 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 12 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 12 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 12 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.j : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_JJJTH (q : Shape) (p r s t : BentCap) :
    cube (fun _ j t h => j^3 * t * h) p (q,0) r s t =
    (6 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.j : ℤ)
    + (6 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BHHHH (q : Shape) (p r s t : BentCap) :
    cube (fun b _ _ h => b * h^4) p (q,0) r s t =
    (24 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)) * (q.b : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BTHHH (q : Shape) (p r s t : BentCap) :
    cube (fun b _ t h => b * t * h^3) p (q,0) r s t =
    (6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)) * (q.b : ℤ)
    + (6 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BTTHH (q : Shape) (p r s t : BentCap) :
    cube (fun b _ t h => b * t^2 * h^2) p (q,0) r s t =
    (4 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.b : ℤ)
    + (4 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BTTTH (q : Shape) (p r s t : BentCap) :
    cube (fun b _ t h => b * t^3 * h) p (q,0) r s t =
    (6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)) * (q.b : ℤ)
    + (6 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 6 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 6 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 6 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BJHHH (q : Shape) (p r s t : BentCap) :
    cube (fun b j _ h => b * j * h^3) p (q,0) r s t =
    (6 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)) * (q.b : ℤ)
    + (6 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ) + 6 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 6 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)) * (q.j : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BJTHH (q : Shape) (p r s t : BentCap) :
    cube (fun b j t h => b * j * t * h^2) p (q,0) r s t =
    (2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.b : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)) * (q.j : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BJTTH (q : Shape) (p r s t : BentCap) :
    cube (fun b j t h => b * j * t^2 * h) p (q,0) r s t =
    (2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)) * (q.b : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)) * (q.j : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BJJHH (q : Shape) (p r s t : BentCap) :
    cube (fun b j _ h => b * j^2 * h^2) p (q,0) r s t =
    (4 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.b : ℤ)
    + (4 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 4 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 4 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 4 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)) * (q.j : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

private theorem cube_BJJTH (q : Shape) (p r s t : BentCap) :
    cube (fun b j t h => b * j^2 * t * h) p (q,0) r s t =
    (2 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)) * (q.b : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)) * (q.j : ℤ)
    + (2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
      + 2 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
      + 2 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)) * (q.t : ℤ) := by
  simp only [cube,List.sublists_cons,List.sublists_nil,List.bind_eq_flatMap,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.cons_append,List.foldl_cons,List.foldl_nil,
    List.length_cons,List.length_nil,addBent,Shape.plus,Nat.cast_add,Nat.cast_zero,Nat.zero_add,Int.zero_add]
  ring

/-- Coefficients of the cutter coordinates in the signed difference. -/
private def coeffB (p r s t : BentCap) : ℤ :=
  960 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 23040 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)

private def coeffJ (p r s t : BentCap) : ℤ :=
  960 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 2880 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 2880 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 2880 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1440 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 2880 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 2880 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  + 2880 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 23040 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)

private def coeffT (p r s t : BentCap) : ℤ :=
  960 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.b : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.b : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 7200 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.j : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 960 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.1.j : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 12960 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 12960 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 2880 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 8640 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  - 7200 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 12960 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 3840 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.1.t : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.b : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 960 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  - 1440 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.1.j : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  + 8640 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  - 2880 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  + 3360 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  - 7200 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  + 8640 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  - 7200 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  + 12960 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  + 3840 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.1.t : ℤ) * (s.2 : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.1.t : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.b : ℤ) * (t.2 : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.j : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.1.t : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.j : ℤ) * (t.2 : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.b : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.j : ℤ)
  - 5760 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.1.t : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.1.t : ℤ) * (t.2 : ℤ)
  + 3840 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.b : ℤ)
  - 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.j : ℤ)
  + 1920 * (p.2 : ℤ) * (r.2 : ℤ) * (s.2 : ℤ) * (t.1.t : ℤ)

private theorem integral_factored (b j t h : ℤ) : bentIntegral b j t h =
  -576 * (h^5) + 160 * (t^2 * h^3) - 480 * (t^3 * h^2) + 540 * (t^4 * h)
    + 960 * (j * h^4) - 320 * (j * t * h^3) + 960 * (j * t^2 * h^2) - 1200 * (j * t^3 * h)
    - 480 * (j^2 * h^3) - 480 * (j^2 * t * h^2) + 840 * (j^2 * t^2 * h)
    + 240 * (j^3 * h^2) - 240 * (j^3 * t * h) - 960 * (b * h^4) + 640 * (b * t * h^3)
    - 1440 * (b * t^2 * h^2) + 1440 * (b * t^3 * h) + 640 * (b * j * h^3)
    + 960 * (b * j * t * h^2) - 1440 * (b * j * t^2 * h) - 480 * (b * j^2 * h^2)
    + 480 * (b * j^2 * t * h) := by
  unfold bentIntegral
  ring

private theorem signed_five_coeffs (q : Shape) (p r s t : BentCap) :
    signedFive p (q,0) r s t = coeffB p r s t*q.b +
      coeffJ p r s t*q.j + coeffT p r s t*q.t := by
  change cube (fun b j t h => bentIntegral b j t h) p (q,0) r s t = _
  simp only [integral_factored,cube_add,cube_sub,cube_mul,cube_HHHHH,cube_TTHHH,cube_TTTHH,cube_TTTTH,cube_JHHHH,cube_JTHHH,cube_JTTHH,cube_JTTTH,cube_JJHHH,cube_JJTHH,cube_JJTTH,cube_JJJHH,cube_JJJTH,cube_BHHHH,
    cube_BTHHH,cube_BTTHH,cube_BTTTH,cube_BJHHH,cube_BJTHH,cube_BJTTH,
    cube_BJJHH,cube_BJJTH,coeffB,coeffJ,coeffT]
  ring

private theorem signed_five_linear (q : Shape) (p r s t : BentCap) :
    signedFive p (q,0) r s t = signedFive p (⟨1,0,0⟩,0) r s t*q.b +
      signedFive p (⟨0,1,0⟩,0) r s t*q.j + signedFive p (⟨0,0,1⟩,0) r s t*q.t := by
  simp only [signed_five_coeffs,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,zero_add,add_zero]

private theorem chamber_coords (p : BentCap) (hp : Chamber p) :
    (p.1.b : ℤ) = (p.1.b-p.1.j : ℕ) + (p.1.j-3*p.1.t : ℕ) + 3*(p.1.t-2*p.2 : ℕ) + 6*p.2 ∧
    (p.1.j : ℤ) = (p.1.j-3*p.1.t : ℕ) + 3*(p.1.t-2*p.2 : ℕ) + 6*p.2 ∧
    (p.1.t : ℤ) = (p.1.t-2*p.2 : ℕ) + 2*p.2 := by
  obtain ⟨hb,hj,ht⟩ := hp
  exact ⟨by exact_mod_cast (by omega : p.1.b = _),
    by exact_mod_cast (by omega : p.1.j = _), by exact_mod_cast (by omega : p.1.t = _)⟩

/- The signed coefficients are positive combinations of the four independent
chamber coordinates of the other slots. The shape of the cutter is arbitrary. -/
set_option maxHeartbeats 2200000 in
private theorem signed_five_nonneg (q : Shape) (p r s t : BentCap)
    (hp : Chamber p) (hr : Chamber r) (hs : Chamber s) (ht : Chamber t) :
    0 ≤ signedFive p (q,0) r s t := by
  obtain ⟨hBp,hJp,hTp⟩ := chamber_coords p hp
  obtain ⟨hBr,hJr,hTr⟩ := chamber_coords r hr
  obtain ⟨hBs,hJs,hTs⟩ := chamber_coords s hs
  obtain ⟨hBt,hJt,hTt⟩ := chamber_coords t ht
  rw [signed_five_coeffs]
  refine add_nonneg (add_nonneg (mul_nonneg ?_ (Int.natCast_nonneg _))
    (mul_nonneg ?_ (Int.natCast_nonneg _))) (mul_nonneg ?_ (Int.natCast_nonneg _))
  all_goals
    simp only [coeffB,coeffJ,coeffT]
    simp only [hBp,hJp,hTp,hBr,hJr,hTr,hBs,hJs,hTs,hBt,hJt,hTt]
    ring_nf
    repeat' apply add_nonneg
    all_goals positivity

/-- The tilted signed surface is linear in the cutter shape. Chamber positivity
also certifies the exact natural-number coefficients in the price ledger. -/
theorem surface_tilted_eq_weights {f : Shape} (hf : Valid f) (ht : tiltedFits f) (q : Shape) :
    surface .tilted f q = (weights .tilted f).b*q.b + (weights .tilted f).j*q.j +
      (weights .tilted f).t*q.t := by
  let p := f.chamber
  let g := bentGraph p
  let l := bentLift (taylorLength-4) p
  let r := bentLift (taylorLength-3) p
  have hb : p.j ≤ p.b := le_max_right _ _
  have hp : Chamber (p,0) := ⟨hb,hf.2.1,Nat.zero_le _⟩
  have hg : Chamber g := Low48BentSupport.graph_chamber hf.1 ht.1
  have hl : Chamber l := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-4)
  have hr : Chamber r := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-3)
  have hnonneg (u : Shape) : 0 ≤ signedFive (p,0) (u,0) g l r :=
    signed_five_nonneg u _ _ _ _ hp hg hl hr
  refine surface_eq_weights_of_signed .tilted f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedFive (p,0) (u,0) g l r).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (hnonneg u)]
  exact signed_five_linear u _ _ _ _

#print axioms surface_tilted_eq_weights
end Low53At2389SharedPrice
