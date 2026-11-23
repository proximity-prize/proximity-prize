import ProximityPrize.SubmissionLower.R6960RetainedTwistedRestriction

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.RetainedTwistedRestriction
open K1_14 (L)
open ChartSections (Chart)
open MonicChart (ChartField)
open MonicFourChartDescent MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests RetainedSurfaceClass
open Module Submodule LinearMap Algebra Polynomial
open scoped Polynomial Lower6960.RetainedSurfaceClass
open private Lower6960.RetainedSurfaceClass.chartSpace Lower6960.RetainedSurfaceClass.congr_of_eq from ProximityPrize.SubmissionLower.R6960RetainedSurfaceClass
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def charts (i:ℕ) : Submodule L (Chart→Tor E) where
  carrier:={u | ∀ s t,Over s t i ((u s:E)-(u t:E))}
  zero_mem':=fun s t=>by simpa [Over] using (isIntegral_zero (R:=overlapRing s t) (B:=E))
  add_mem' {u v} hu hv s t:=by
    change IsIntegral _ (_*(((u s:E)+v s)-((u t:E)+v t)))
    convert (hu s t).add (hv s t) using 1 <;> ring
  smul_mem' r u hu s t:=by
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u s:E)-ι (constants r)*(u t:E)))
    have scalar:IsIntegral (overlapRing s t) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,into_cleared _ (edge s t) (chart_constant s r)⟩:overlapRing s t))
    convert scalar.mul (hu s t) using 1 <;> ring

def trivial (i:ℕ) : Submodule L (charts E i) where
  carrier:={u | ∃c:E,∀s,Regular s i ((u.1 s:E)-c)}
  zero_mem':=⟨0,fun s=>by simpa [Regular] using (isIntegral_zero (R:=baseChart s) (B:=E))⟩
  add_mem' {u v} hu hv:=by
    obtain ⟨a,ha⟩:=hu;obtain ⟨b,hb⟩:=hv
    refine ⟨a+b,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(((u.1 s:E)+v.1 s)-(a+b)))
    convert (ha s).add (hb s) using 1 <;> ring
  smul_mem' r u hu:=by
    obtain ⟨a,ha⟩:=hu; refine ⟨ι (constants r)*a,fun s=>?_⟩
    change IsIntegral _ ((fr s)⁻¹^i*(ι (constants r)*(u.1 s:E)-ι (constants r)*a))
    have scalar : IsIntegral (baseChart s) (ι (constants r):E) :=
      isIntegral_algebraMap (x:=(⟨_,chart_constant s r⟩:baseChart s))
    convert scalar.mul (ha s) using 1 <;> ring

private def shift (i:ℕ) (x:L) : charts E i →ₗ[L] charts E (i+1) where
  toFun u:=⟨fun s=>cut E false x*u.1 s, fun s t=>by
    have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
      have p : IsIntegral (baseChart s) (algebraMap (baseChart s) E (xcut s x)):=isIntegral_algebraMap
      change IsIntegral (baseChart s) (ι (xcut s x:ChartField)) at p
      rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
    change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*(u.1 t:E)))
    have loc : IsIntegral (overlapRing s t) (ι (divisor false x)*(fr s:E)⁻¹) :=
      order_mono (into_cleared _ (edge s t)) d
    convert loc.mul (u.property s t) using 1 <;> rw [pow_succ] <;> ring⟩
  map_add' a b:=by apply Subtype.ext; funext s; exact mul_add _ _ _
  map_smul' r a:=by
    apply Subtype.ext; funext s; apply Subtype.ext
    change ι (divisor false x)*(ι (constants r)*(a.1 s:E))=ι (constants r)*(ι (divisor false x)*(a.1 s:E))
    ring

private def lineMap (i:ℕ) (x:L) : charts E i→ₗ[L] LineObstructions E false x :=
  let ev (s:Chart) : (Chart→Tor E) →ₗ[L] Tor E := LinearMap.proj s
  let values := ev (false,false)-ev (false,true)
  (chartImage E false x false⊔chartImage E false x true).mkQ.comp
    ((red E false x).comp (values.comp (charts E i).subtype))

abbrev Budget (i n:ℕ) := RetainedCodimension.Fits (k:=L) (U:=↥(charts E i)) (trivial E i) n

theorem budget_subspace {J:Type} [Fintype J] (i n:ℕ) (H:Budget E i n)
    (f:(J→L) →ₗ[L] charts E i) :
    ∃ D:Submodule L (J→L),finrank L (J→L)≤n+finrank L D ∧
      ∀v:D,∃c:E,∀s,Regular s i (((f v.val).val s:E)-c) := by
  exact @RetainedCodimension.large_subspace L (J→L) ↥(charts E i) inferInstance inferInstance
    inferInstance (charts E i).addCommGroup (charts E i).module inferInstance
    (trivial E i) f n H

private theorem shift_trivial (i:ℕ) (x:L) : trivial E i ≤ (trivial E (i+1)).comap (shift E i x) := by
  rintro u ⟨c,hc⟩
  refine ⟨ι (divisor false x)*c,fun s=>?_⟩
  have d : IsIntegral (baseChart s) (ι (divisor false x)*(fr s:E)⁻¹) := by
    have p : IsIntegral (baseChart s) (ι (xcut s x:ChartField):E) := isIntegral_algebraMap (x:=xcut s x)
    rwa [xcut_value,map_div₀,div_eq_mul_inv] at p
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(ι (divisor false x)*(u.1 s:E)-ι (divisor false x)*c))
  convert d.mul (hc s) using 1 <;> rw [pow_succ] <;> ring

theorem grow [FiniteDimensional ChartField E] (i:ℕ) (x:L) (nx:x≠0)
    [FiniteDimensional L (LineObstructions E false x)] {n t:ℕ}
    (previous:Budget E i n)
    (width:finrank L (LineObstructions E false x)≤t) :
    Budget E (i+1) (n+t) := by
  apply RetainedCodimension.step (k:=L) (U:=↥(charts E i)) (V:=↥(charts E (i+1))) (W:=LineObstructions E false x)
    _ _ (shift E i x) (lineMap E (i+1) x) (shift_trivial E i x) _ previous width
  intro u hu
  change Submodule.Quotient.mk (p:=chartImage E false x false⊔chartImage E false x true)
    (red E false x (u.1 (false,false)-u.1 (false,true)))=0 at hu
  have res := (Submodule.Quotient.mk_eq_zero _).mp hu
  obtain ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,eq⟩:=Submodule.mem_sup.mp res
  let reps (j:Bool):E:=if j then -(b:E) else a
  have data:LineData false x (fun s=>(u.1 s:E)) reps := by
    refine ⟨fun j=>?_,?_⟩
    · cases j
      · exact ha
      · exact (show IsIntegral (baseChart (reference false true)) (b:E) from hb).neg
    · have e : red E false x (u.1 (false,false)-u.1 (false,true))=red E false x (a+b) :=
        eq.symm.trans (map_add ..).symm
      change Congruent false x ((u.1 (false,false):E)-u.1 (false,true)) ((a:E)- -(b:E))
      rw [sub_neg_eq_add]
      exact Lower6960.RetainedSurfaceClass.congr_of_eq E false x _ _ e
  obtain ⟨w,l,iw,lr,wr,eq⟩:=descend_line i x nx (fun s=>(u.1 s:E)) u.property reps data
  let y:charts E i:=⟨fun s=>⟨w s,iw s⟩,wr⟩
  refine ⟨y,u.1 (false,false)-reps false,fun s=>?_⟩
  change IsIntegral _ ((fr s)⁻¹^(i+1)*(((u.1 s:E)-ι (divisor false x)*w s)-((u.1 (false,false):E)-reps false)))
  rw [eq,add_sub_cancel_right]
  exact lr s

open RetainedCompression (Curve ordinate view height heightCap wordDegree)

theorem initial (f:Curve L[X]) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap MonicChart.Scalar[X] ChartField))=0)
    (x z:L) (nx:x≠0) (nz:z≠0) [FiniteDimensional L (Paired E x z)] {b:ℕ}
    (size:finrank L (Paired E x z)≤b) : Budget E 0 b := by
  have spaces:charts E 0=potentials E := by
    ext u; change (∀s t,Over s t 0 _ )↔_
    simp only [Over,pow_zero,one_mul]; rfl
  let e:=LinearEquiv.ofEq _ _ spaces
  let f₀:=(rawMap E x z).comp e.toLinearMap
  apply RetainedCodimension.from_map f₀ _ _ size
  ext u
  change e u∈(rawMap E x z).ker ↔ ∃ c:E,∀s, Regular s 0 ((u.1 s:E)-c)
  rw [restriction_kernel E f ir lo hi bounded basis root x z nx nz]
  simp only [Regular,pow_zero,one_mul]; rfl

#print axioms grow
#print axioms initial

/-- Uniform surface bound for every positive abscissa twist of the same actual
factor. The degrees s,t are measured on its own two specialized chart orders. -/
theorem actual_all_twists (f:Curve L[X]) (ir:Irreducible f) (lo:3≤f.degreeOf ordinate) (hi:f.degreeOf ordinate<48)
    (bounded:height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree) (basis:PowerBasis ChartField E)
    (root:aeval basis.gen ((RetainedLinear.toSeed (view f)).map (algebraMap MonicChart.Scalar[X] ChartField))=0) :
    ∃ (x z:L) (nx:x≠0) (nz:z≠0) (m n s t:ℕ),
      ∃ (xf:Basis (Fin m) L[X] (chartImage E false x false)) (xi:Basis (Fin m) L[X] (chartImage E false x true))
        (zf:Basis (Fin n) L[X] (chartImage E true z false)) (zi:Basis (Fin n) L[X] (chartImage E true z true)),
        (transition E false x nx xf xi).det.degree=((-(t:ℤ):ℤ):WithBot ℤ) ∧
        (transition E true z nz zf zi).det.degree=((-(s:ℤ):ℤ):WithBot ℤ) ∧
        Nonempty (Basis (Fin (f.degreeOf ordinate)) L (Crossing E x z)) ∧ IsReduced (Crossing E x z) ∧
        ∀ i:ℕ, Budget E i (s+(i+1)*t) := by
  have : FiniteDimensional ChartField E := basis.finite
  have : Algebra.IsSeparable ChartField E := MonicChartProbes.actual_separable f ir lo hi basis root
  obtain ⟨x,z,nx,nz,⟨B⟩,red⟩:=actual_crossing E f ir lo hi basis root
  have : FiniteDimensional L (Crossing E x z) := Module.Finite.of_basis B
  obtain ⟨m,⟨xf⟩,⟨xi⟩⟩:=native_frames E false x nx
  obtain ⟨n,⟨zf⟩,⟨zi⟩⟩:=native_frames E true z nz
  obtain ⟨finite,s,t,dt,ds,base⟩:=paired_bound E x z nx nz xf xi zf zi
  obtain ⟨fg,fo,d,ed,index⟩:=native_euler E false x nx xf xi
  have de : d= -(t:ℤ) := WithBot.coe_injective (ed.symm.trans dt)
  have : FiniteDimensional L (LineGlobals E false (atCoord false x z)) := fg
  have inject:=global_eval_injective E false x z nx nz xf
  have eRank := LinearMap.finrank_le_finrank_of_injective inject
  change finrank L (LineGlobals E false x)≤finrank L (Crossing E x z) at eRank
  have mrank:=node_rank_le E false x z nx nz xf
  have line : finrank L (LineObstructions E false x)≤t := by omega
  refine ⟨x,z,nx,nz,m,n,s,t,xf,xi,zf,zi,dt,ds,⟨B⟩,red,fun i=>?_⟩
  induction i with
  | zero => simpa only [zero_add,one_mul] using initial E f ir lo hi bounded basis root x z nx nz base
  | succ i ih =>
    simpa only [Nat.succ_eq_add_one,Nat.add_mul,one_mul,Nat.add_assoc] using grow E i x nx ih line

#print axioms actual_all_twists
end Lower6960.RetainedTwistedRestriction
