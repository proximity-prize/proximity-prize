import ProximityPrize.SubmissionLower.R6961ChartGlobalTests
import ProximityPrize.SubmissionLower.R6960ChartImage
import ProximityPrize.SubmissionLower.R6961MonicScalarCorrection

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.RetainedChartGluing
open Lower6960.ChartSections (Chart)
open Lower6960.MonicChart Lower6961.MonicChart MonicFourChartDescent MonicScalarCorrection ChartGlobalTests
open RetainedCompression (Curve ordinate view height heightCap MarkedBand)
open Polynomial
open K1_14 (L)
open Lower6961.MonicFourChartDescent (finite_inclusion infinity_inclusion)

private theorem frame_add (a b D : ℕ) (s : Chart) :
    frame (a+D) (b+D) s=frame a b s*frame D D s := by
  simp only [frame,pow_add]; ring

variable {E : Type*} [Field E] [Algebra ChartField E]

/-- High negative twists have a common correction in the root field itself. The threshold
is fixed by the factor's probe map and is uniform in the four potentials. -/
theorem high_twist (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<K1.p) (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0) :
    ∃ H : ℕ, ∀ a b, H<a → H<b →
      ∀ u : Chart→E, Compatible a b u → ∃ c, Correction a b u c := by
  classical
  obtain ⟨n,D,P,tests⟩:=simultaneous_tests f ir lo hi basis root
  let deq : DecidableEq ChartField := Classical.decEq _
  let : DecidableEq (RatFunc Scalar) := deq
  obtain ⟨k,image⟩:=@Lower6960.ChartImage.eventually_in_subspace Scalar (Fin n) _ _ deq (LinearMap.range P)
  refine ⟨k+D,fun a b ha hb u compatible => ?_⟩
  let i:=a-D
  let j:=b-D
  have ia : i+D=a := Nat.sub_add_cancel (by omega)
  have jb : j+D=b := Nat.sub_add_cancel (by omega)
  have ik : k < i := by dsimp [i]; omega
  have jpos : 0<j := by dsimp [j]; omega
  have frames (s) : frame a b s=frame i j s*frame D D s := by
    simpa only [ia,jb] using frame_add i j D s
  have transport (r : Fin n) : ScalarCompatible i j (fun s=>P (u s) r) := by
    intro s t
    let proj:= (LinearMap.proj r).comp P
    let test:= (frame D D s)⁻¹ • proj
    have regular (x:E) (hx:IsIntegral (baseChart s) x) : test x∈baseChart s := by
      simpa only [test,proj,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply,
        smul_eq_mul,div_eq_mul_inv,mul_comm] using (tests s x).mp hx r
    have m:=overlap_test s t test regular _ (compatible s t)
    change test (algebraMap ChartField E (frame a b s)*(u s-u t))∈_ at m
    rw [←Algebra.smul_def,map_smul,smul_eq_mul] at m
    change frame a b s*((frame D D s)⁻¹ * P (u s-u t) r)∈_ at m
    rw [frames,mul_assoc,←mul_assoc (frame D D s),mul_inv_cancel₀ (frame_ne _ _ _),one_mul,
      map_sub,Pi.sub_apply] at m
    exact m
  choose c sol using fun r => scalar_correction i j (by omega) jpos _ (transport r)
  have inField : c∈LinearMap.range P := by
    apply image i ik c (P (u (false,false))) (P (u (true,false))) ⟨_,rfl⟩ ⟨_,rfl⟩
    · intro r
      have h:=Lower6961.MonicFourChartDescent.finite_inclusion (sol r (false,false))
      simpa [frame] using (algebraMap (Polynomial Scalar) ChartField).range.neg_mem h
    · intro r
      have h:=@Lower6961.MonicFourChartDescent.infinity_inclusion deq _ (sol r (true,false))
      obtain ⟨v,eq⟩:=h
      have val : (v:ChartField)=RatFunc.X^i*(P (u (true,false)) r-c r) := by simpa [frame] using eq
      have vin : -(v:ChartField) ∈ @Infinity Scalar _ deq :=
        (@Infinity Scalar _ deq).toSubring.neg_mem v.property
      rw [val] at vin
      simpa only [←mul_neg,neg_sub] using vin
  obtain ⟨v,pv⟩:=inField
  refine ⟨v,fun s => (tests s _).mpr (fun r => ?_)⟩
  rw [←Algebra.smul_def,map_smul,map_sub,pv,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,frames,
    mul_right_comm,mul_div_cancel_right₀ _ (frame_ne D D s)]
  exact sol r s

/-- For an arbitrary bounded retained factor there is one root-field correction for every
compatible family on the four normalized charts, already at twist (-1,-1). -/
theorem common_correction (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (u : Chart→E) (compatible : Compatible a b u) :
    ∃ c : E, Correction a b u c := by
  obtain ⟨H,high⟩:=high_twist f ir lo (hi.trans B.small_E) basis root
  have large : H<K1.p^H := Nat.lt_pow_self KoalaBear.is_prime.one_lt
  have above {d : ℕ} (pos : 0<d) : H<d*K1.p^H :=
    large.trans_le (Nat.le_mul_of_pos_left _ pos)
  obtain ⟨c,hc⟩:=high _ _ (above ha) (above hb) _ (compatible_iterate a b u compatible H)
  obtain ⟨d,_,hd⟩ := descend_iterate B f ir lo hi bounded basis root a b ha u H c hc
  exact ⟨d,hd⟩

#print axioms high_twist
#print axioms common_correction

/-- Additive transition functions on the overlaps are differences of regular local
sections on the normalized four-chart cover. -/
theorem split_cocycle (B : MarkedBand) (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (hi : f.degreeOf ordinate<B.maxOrd) (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (basis : PowerBasis ChartField E)
    (root : aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap (Polynomial Scalar) ChartField))=0)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (g : Chart→Chart→E)
    (add : ∀ s t r, g s t+g t r=g s r)
    (regular : ∀ s t, IsIntegral (MonicChartLaurent.overlapRing s t)
      (algebraMap ChartField E (frame a b s)*g s t)) :
    ∃ w : Chart→E, (∀ s, IsIntegral (baseChart s) (algebraMap ChartField E (frame a b s)*w s)) ∧
      ∀ s t, g s t=w s-w t := by
  let u (s : Chart):=g s (false,false)
  have diff (s t) : u s-u t=g s t := sub_eq_of_eq_add (add s t (false,false)).symm
  obtain ⟨c,hc⟩:=common_correction B f ir lo hi bounded basis root a b ha hb u
    (fun s t=> by rw [diff]; exact regular s t)
  exact ⟨fun s=>u s-c,hc,fun s t=>by rw [←diff]; ring⟩

#print axioms split_cocycle
end Lower6961.RetainedChartGluing
