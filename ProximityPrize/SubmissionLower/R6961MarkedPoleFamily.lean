import ProximityPrize.SubmissionLower.R6961MarkedWordResidues
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open MonicFourChartDescent Lower6960.ChartSections MonicChartLaurent RetainedRestrictionTorus ChartOverlapTests
open RetainedSurfaceClass RetainedTwistedRestriction Module Submodule LinearMap Algebra Polynomial Finset
open scoped Polynomial Lower6961.RetainedSurfaceClass Lower6961.MarkedEvaluation BigOperators
local instance : DecidableEq L := Classical.decEq _
variable (E:Type) [Field E] [Algebra ChartField E]
local notation "ι" => algebraMap ChartField E

def denominator (T:Finset L) : Tor E:=∏z∈T,cut E true z
def chartDenom (T:Finset L) (s:Chart) : E:=∏z∈T,algebraMap (baseChart s) E (zcut s z)
def controlled (i:ℕ) (T:Finset L) (v:E) : Prop :=
  ∀s,Regular s i (chartDenom E T s*v)

theorem denom_integral (T:Finset L) (s:Chart) : IsIntegral (baseChart s) (chartDenom E T s) := by
  unfold chartDenom
  rw [←map_prod];exact isIntegral_algebraMap

private theorem eval_cut (z y:L) : red E true z (cut E true y)=algebraMap L (Axis E true z) (z-y) := by
  let π:=Ideal.Quotient.mk (axisIdeal E true z)
  have src:cut E true y=torVar E true false-algebraMap L (Tor E) y := by
    apply Subtype.ext;exact map_sub (algebraMap ChartField E) _ _
  change π _=_
  have fixed:π (torVar E true false)=algebraMap L _ z := fixed_value E true z
  rw [src,map_sub,fixed,map_sub];rfl

private theorem denom_value (T:Finset L) (z:L) :
    Ideal.Quotient.mk (axisIdeal E true z) (denominator E T)=algebraMap L (Axis E true z) (∏y∈T,(z-y)) := by
  rw [denominator,map_prod,map_prod]
  exact Finset.prod_congr rfl (fun y _=>eval_cut E z y)

theorem denom_zero (T:Finset L) (z:L) (hz:z∈T) :
    Ideal.Quotient.mk (axisIdeal E true z) (denominator E T)=0 := by
  rw [denom_value,Finset.prod_eq_zero (f:=fun u:L=>z-u) hz (sub_self z),map_zero]

private theorem cancel_one {T:Finset L} {z:L} (mem:z∈T) (v:E) :
    ((denominator E T:E))*(v/ι (divisor true z))=(denominator E (T.erase z):E)*v := by
  have dn : (ι (divisor true z):E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne true z)
  rw [show denominator E T=cut E true z*denominator E (T.erase z) from (Finset.mul_prod_erase _ _ mem).symm]
  change (ι (divisor true z)*(denominator E (T.erase z):E))*(v/ι (divisor true z))=_
  field_simp

private theorem cleared_charts (i:ℕ) {T:Finset L} {z:L} (mem:z∈T) (s:Chart) (v:E)
    (reg:Regular s i v) : Regular s i (chartDenom E T s*(v/ι (divisor true z))) := by
  let F:=localFrame s true
  have dn : (ι (divisor true z):E)≠0 :=
    (map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (divisor_ne true z)
  have atBase:F⁻¹∈baseChart s := by
    have h:chartCoordinate s.2 scalarCoordinate∈baseChart s:=Subring.subset_closure (Or.inr (Or.inr rfl))
    by_cases ht:s.2=true <;> simp [F,localFrame,axisBit,coordinate,ht,chartCoordinate] at * <;> assumption
  have inv:IsIntegral (baseChart s) (ι (F⁻¹):E) := isIntegral_algebraMap (x:=(⟨_,atBase⟩:baseChart s))
  have eq:chartDenom E T s=ι (divisor true z)/ι F*chartDenom E (T.erase z) s := by
    rw [show chartDenom E T s=algebraMap (baseChart s) E (zcut s z)*chartDenom E (T.erase z) s from
      (Finset.mul_prod_erase _ _ mem).symm]
    change ι (zcut s z:ChartField)*_=_
    rw [zcut_value,map_div₀]
  change IsIntegral _ ((fr s)⁻¹^i*(chartDenom E T s*(v/ι (divisor true z))))
  rw [eq]
  have algebra : (fr s)⁻¹^i*(ι (divisor true z)/ι F*chartDenom E (T.erase z) s*(v/ι (divisor true z)))=
      chartDenom E (T.erase z) s*ι F⁻¹*((fr s)⁻¹^i*v) := by
    rw [map_inv₀]; field_simp [dn,(map_ne_zero_iff _ (algebraMap ChartField E).injective).mpr (localFrame_ne s true)] <;> ring
  rw [algebra];exact ((denom_integral E _ _).mul inv).mul reg

private theorem scaled_sum {J:Type} [Fintype J] (p:J→Chart→E) (s:Chart) (d:J→L) :
    principalValue p s d=∑j,(ι (constants (d j)))*p j s := by
  classical
  simp [principalValue,Basis.constr_apply_fintype,Algebra.smul_def];rfl

/-- Lift actual marked fibre sections jointly. A nonzero lifted function has a
genuine scalar pole, so the lifted space is independent of every ordinary
abscissa polynomial. -/
theorem lift_fibres [FiniteDimensional ChartField E] (i n:ℕ) (budget:Budget E i n)
    (T:Finset L) (nz:∀z∈T,z≠0) (J:T→Type) [∀z,Fintype (J z)]
    (v:∀z:T,J z→Axis E true z.val)
    (regular:∀ (z:T) (j:J z),FibreSection (E:=E) i z.val (v z j)) (independent:∀z,LinearIndependent L (v z)) :
    ∃ D:Submodule L ((Σz:T,J z)→L), ∃ lift:D→ₗ[L]E,
      (∑z:T,Fintype.card (J z))≤n+finrank L D ∧ (∀d,controlled E i T (lift d)) ∧
      (∀ d, IsIntegral torus (lift d) → d=0) ∧
      ∀d:D,∃w:Tor E, w.val=(denominator E T:E)*lift d ∧
        ∀z:T,red E true z.val w=(∏ y∈T.erase z.val,(z.val-y)) • (∑j:J z,(d.val ⟨z,j⟩) • v z j) := by
  classical
  let Id:=Σz:T,J z
  choose W reg values compat using fun u:Id=>word_principal_parts (E:=E) i u.1.val (nz _ u.1.property) (v u.1 u.2) (regular u.1 u.2)
  let p (j:Id) (s:Chart):E:=(W j s:E)/ι (divisor true j.1.val)
  obtain ⟨D,lift,dim,part⟩:=lift_principal_parts (J:=Id) (E:=E) i n budget p compat
  have controls (d:D) (s:Chart): Regular s i (chartDenom E T s*lift d) := by
    let M:=chartDenom E T s
    let P:=principalValue p s d.val
    have hc : IsIntegral (baseChart s) ((fr s)⁻¹^i*(P-lift d)):=part d s
    have total : Regular s i (M*P) := by
      change IsIntegral _ ((fr s)⁻¹^i*(M*principalValue p s d.val))
      rw [scaled_sum,Finset.mul_sum,Finset.mul_sum]
      apply IsIntegral.sum;intro j _
      have sc:IsIntegral (baseChart s) (ι (constants (d.val j)):E) :=
        isIntegral_algebraMap (x:=(⟨_,chart_constant s (d.val j)⟩:baseChart s))
      have term:=sc.mul (cleared_charts E i j.1.property s (W j s:E) (reg j s))
      convert term using 1 <;> ring
    convert total.sub ((denom_integral E T s).mul hc) using 1 <;> ring
  have residues (d:D) : ∃w:Tor E,w.val=(denominator E T:E)*lift d ∧
      ∀z:T,red E true z.val w=(∏y∈T.erase z.val,(z.val-y)) • (∑j:J z,(d.val ⟨z,j⟩) • v z j) := by
    let a:Chart:=(false,false)
    let rem := principalValue p a d.val-lift d
    have remInt : IsIntegral torus rem := order_mono (base_torus a) (by
      simpa [a,Regular,fr,localFrame,axisBit] using part d a)
    let R:Tor E:=⟨rem,remInt⟩
    let w:Tor E:=(∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a))-denominator E T*R
    have sum_eq : (denominator E T:E)*principalValue p a d.val =
        ((∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a):Tor E):E) := by
      rw [scaled_sum,Finset.mul_sum]
      have castSum (f:Id→Tor E) : ((∑j,f j : Tor E):E)=∑j,(f j:E) := map_sum (Tor E).val f Finset.univ
      rw [castSum]
      apply Finset.sum_congr rfl;intro j _
      change (denominator E T:E)*(ι (constants (d.val j))*p j a)=ι (constants (d.val j))*(_*_)
      rw [mul_left_comm];exact congrArg (ι (constants (d.val j))*·) (cancel_one E j.1.property _)
    refine ⟨w,?_,fun z=>?_⟩
    · change ((∑j:Id,d.val j • (denominator E (T.erase j.1.val)*W j a):Tor E):E)-(denominator E T:E)*rem=_
      rw [←sum_eq];dsimp [rem];ring
    · let π:=Ideal.Quotient.mk (axisIdeal E true z.val)
      have vanish : π (denominator E T)=0 := denom_zero E T z.val z.property
      change π w=_
      simp only [w,map_sub,map_mul,map_sum,vanish,zero_mul,sub_zero]
      rw [Fintype.sum_sigma (fun j:Σz:T,J z=>π (d.val j • (denominator E (T.erase j.1.val)*W j a)))]
      rw [Finset.sum_eq_single z]
      · rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        change (red E true z.val) (d.val ⟨z,j⟩ • (denominator E (T.erase z.val)*W ⟨z,j⟩ a))=_
        rw [map_smul]
        change _ • (π (denominator E (T.erase z.val)*W ⟨z,j⟩ a))=_
        rw [map_mul,show π (W ⟨z,j⟩ a)=v z j from values ⟨z,j⟩ a]
        have weight := denom_value E (T.erase z.val) z.val
        change π (denominator E (T.erase z.val))=_ at weight
        rw [weight,←Algebra.smul_def,smul_comm]
      · intro other _ ne
        apply Finset.sum_eq_zero;intro j _
        change red E true z.val (_ • (denominator E (T.erase other.val)*W ⟨other,j⟩ a))=0
        rw [map_smul];change _ • π (_*_) = 0
        have vz : π (denominator E (T.erase other.val))=0 :=
          denom_zero E _ _ (Finset.mem_erase.mpr ⟨Ne.symm (Subtype.val_injective.ne ne),z.property⟩)
        rw [map_mul,vz,zero_mul,smul_zero]
      · simp
  refine ⟨D,lift,by simpa only [Id,Fintype.card_sigma] using dim,controls,?_,residues⟩
  intro d noPole
  obtain ⟨w,eq,test⟩:=residues d
  have exactValue : w=denominator E T*(⟨lift d,noPole⟩:Tor E) := Subtype.ext eq
  apply Subtype.ext
  funext j
  obtain ⟨z,j⟩:=j
  have weight:(∏y∈T.erase z.val,(z.val-y))≠0 := Finset.prod_ne_zero_iff.mpr (fun y hy=>sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)
  have zero:=test z
  rw [exactValue] at zero
  change Ideal.Quotient.mk _ (_*_)=_ at zero
  rw [map_mul,denom_zero E T z.val z.property,zero_mul] at zero
  let c:=∏y∈T.erase z.val,(z.val-y)
  have cleared:=congrArg (fun a:Axis E true z.val=>c⁻¹ • a) zero.symm
  change c⁻¹ • (c • (∑j:J z,d.val ⟨z,j⟩ • v z j))=c⁻¹ • 0 at cleared
  rw [smul_smul,inv_mul_cancel₀ weight,one_smul,smul_zero] at cleared
  exact Fintype.linearIndependent_iff.mp (independent z) _ cleared j

#print axioms lift_fibres
end Lower6961.MarkedEvaluation
