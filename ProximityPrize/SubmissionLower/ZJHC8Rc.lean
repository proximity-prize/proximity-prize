import ProximityPrize.SubmissionLower.ZwiFoca
import ProximityPrize.SubmissionLower.ZX4kd1a
import ProximityPrize.SubmissionLower.ZIBb1mb
set_option Elab.async false
set_option autoImplicit true
namespace q8kxiJa
noncomputable section
open P6_6 P6_6_7 q8NBBre Finset
open aR (af Shape shape aO)
open dN (GeoJets bC kC AX)
open agL (BV a4B)
open vS (VE)
open Dr
open yi (bF)
open lB (amo)
open P6_6_7_3 (first_fits cDD agr)
open private capCoeff_le_of_subset from ProximityPrize.SubmissionLower.BI
def c1 :Prop :=
  ∀ (J:Ideal GeoJets) (p:Shape) (boxes :List Shape),
    boxes.length≤2→bF p→(∀ q∈boxes,bF q) →
    dimension J≤boxes.length+1 →
    ∀ D:GeoJets,VE p D→ IsLeftRegular (Ideal.Quotient.mk J D) →
      tW (J ⊔ Ideal.span {D}) boxes≤tW J (p :: boxes)
def c2 :Prop :=
  ∀ (J:Ideal GeoJets) (boxes :List Shape),
    boxes.length≤2→(∀ q∈boxes,bF q)→dimension J≤boxes.length →
    ∀ S:Finset (Ideal GeoJets),(∀ P∈S,J.IsMinimalPrime P) →
      (∑ P∈S,(AN J P:ℚ)*tW P boxes)≤tW J boxes
def c3:Prop :=
  ∀ (R:af 4) (r q b h:Shape),R≠0→aO (shape R) r →
    bF q→bF b→bF h →
    32*tW (Ideal.span {bC R}) [q,b,h]≤(wP r q b h:ℚ)
private theorem clipped_chamber (b j t:ℕ) :
    bF ⟨max b j,j,min t (j/3)⟩:= by
  have ht:=min_le_right t (j/3)
  exact ⟨le_max_right _ _,by change 3*min t (j/3)≤j; omega⟩
private theorem literal_chamber (p:Shape) :bF (literalBody p).iU:= by
  have he (j:ℕ) :min p.t (min p.b (j/3))=min (min p.t p.b) (j/3) := by
    rw [min_assoc]
  dsimp only [literalBody,Shape.iU]
  rw [he]
  exact clipped_chamber _ _ _
private theorem join_chamber {p q:Shape} (hp:bF p) (hq:bF q) :
    bF (joinBody p q) := by
  refine ⟨max_le_max hp.1 hq.1,?_⟩
  change 3*max p.t q.t≤ max p.j q.j
  rw [← Nat.mul_max_mul_left]
  exact max_le_max hp.2 hq.2
private theorem weighted_chamber (L:ℕ) (p:Shape) :bF (weightedChart L p) := by
  unfold weightedChart
  split
  · exact clipped_chamber _ _ _
  · exact lB.A9 _ _
private theorem section_nonneg {T:Ideal GeoJets} (hd:dimension T≤1)
    {h:Shape} (hh:bF h) :0≤tW T [h] := by
  let base :Shape :=⟨3, 3,1⟩
  have hb:ChamberBox base :=⟨by decide,by decide,by decide⟩
  have hb' : ChamberBox (base.plus h) := by
    obtain ⟨h₁,h₂⟩:=hh
    change 3+h.j≤3+h.b∧3*(1+h.t)≤3+h.j∧0<1+h.t
    omega
  have hsub:capExponents base⊆capExponents (base.plus h) := fun _ hm =>
    ⟨hm.1.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)),
      hm.2.1.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)),
      hm.2.2.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))⟩
  change 0≤(capCoeff T 1 (base.plus h) - capCoeff T 1 base)/(2 :ℚ)^1
  exact div_nonneg (sub_nonneg.mpr (capCoeff_le_of_subset T hb hb' hsub hd)) (by positivity)
variable {C:Context} {R G:af 4} {assigned:SurfaceAssignment C R G}
private theorem branch_valid (A:Cuts assigned) {B:Branch} (hB:B∈A.branches) :
    (kC R G).IsMinimalPrime B.1 ∧
      bC (A.polynomial B)∉B.1∧(AX B.1 (A.polynomial B)).IsMinimalPrime B.2 := by
  classical
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hB
  obtain ⟨hm,he⟩:=mem_filter.mp hγ
  have ho:0<ord C R γ:=Nat.pos_of_ne_zero fun hz=> by simp [excessAt,hz] at he
  exact ⟨(assigned.valid γ hm ho).1,(A.valid γ hγ).2.1,(A.valid γ hγ).2.2.1⟩
private theorem fiber_budget (hcut:c1) (hcycle :c2) {ell cs} (hp:PairInput C R G ell cs)
    (A:Cuts assigned) {h:Shape} (hh:bF h)
    (hb:bF (commonBody C R ell cs)) {z :Ideal GeoJets}
    (hz :z∈A.branches.image Prod.fst) :
    let b:=commonBody C R ell cs
    let F:=A.branches.filter (fun B=>B.1=z)
    (kC R G).IsMinimalPrime z ∧
      0≤(∑ B∈F,(A.order B:ℚ)*tW B.2 [h]) ∧
      (∑ B∈F,(A.order B:ℚ)*tW B.2 [h])≤tW z [b,h] := by
  classical
  intro b F
  obtain ⟨ref,href,heq⟩:=mem_image.mp hz
  let U:=BV (A.first z) R
  let J:=AX z U
  obtain ⟨hZ,hU,_⟩:=branch_valid A href
  have hbase : (kC R G).IsMinimalPrime z :=heq ▸ hZ
  have hu:bC U∉z := by
    simpa only [U,Cuts.polynomial,heq] using hU
  have hd:=aQG (agr hp.factor.1.ne_zero)
    (amo R G hp.factor.1 hp.proper) hbase
  have hreg:=aPQ hbase.isPrime hu
  have hdim:dimension J≤1 := by simpa only [J,AX,hd] using aCR hreg
  have ht (B:Branch) (hB:B∈F) :J.IsMinimalPrime B.2 := by
    obtain ⟨hA,hz'⟩:=mem_filter.mp hB
    simpa only [J,U,Cuts.polynomial,hz'] using (branch_valid A hA).2.2
  have hn (B:Branch) (hB:B∈F) :0≤tW B.2 [h] :=
    section_nonneg ((MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le (ht B hB).le).trans hdim) hh
  have hbody :VE b (bC U) :=bHn (a4B _ (cDD (first_fits hp)
    ⟨le_max_left _ _,le_max_left _ _,le_max_left _ _⟩))
  refine ⟨hbase,sum_nonneg (fun B hB=>mul_nonneg (Nat.cast_nonneg _) (hn B hB)),?_⟩
  calc
    _ ≤ ∑ B∈F,(AN J B.2 :ℚ)*tW B.2 [h] := by
      apply sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_right _ (hn B hB)
      have he :=(mem_filter.mp hB).2
      have hle :=local_order_le hbase.isPrime hu (ht B hB)
      exact_mod_cast (show A.order B≤AN J B.2 by
        simpa only [Cuts.order,Cuts.polynomial,he,U] using hle)
    _ = ∑ T∈F.image Prod.snd,(AN J T:ℚ)*tW T [h] := by
      symm
      exact sum_image (f := fun T=>(AN J T:ℚ)*tW T [h]) (by
        intro B hB D hD hBD
        exact Prod.ext ((mem_filter.mp hB).2.trans (mem_filter.mp hD).2.symm) hBD)
    _≤tW J [h] :=
      hcycle J [h] (by simp) (by simpa using hh) (by simpa using hdim) _
        (fun T hT=> by obtain ⟨B,hB,rfl⟩:=mem_image.mp hT; exact ht B hB)
    _≤tW z [b,h] :=
      hcut z b [h] (by simp) hb (by simpa using hh) (by simp [hd]) _ hbody hreg
theorem of_children (hcut:c1) (hcycle :c2) (hfirst:c3) :q8NBBre.c1 := by
  classical
  intro C R G ell cs hp assigned A h
  dsimp only
  intro hh
  let p:=chartBody C R cs
  let q:=cutterBody C ell
  let b:=commonBody C R ell cs
  let r :=firstSlot C R cs
  let H :Ideal GeoJets :=Ideal.span {bC R}
  let J:=kC R G
  let uG:=A.branches.image Prod.fst
  let fiber (z :Ideal GeoJets) :=A.branches.filter (fun B=>B.1=z)
  let cost (B:Branch) :=(A.order B:ℚ)*tW B.2 [h]
  have hshape :bF (shape R).iU:=lB.Tn R
  have hp' : bF p:= by cases cs <;> first | exact literal_chamber _ | exact hshape
  have hq:bF q:=literal_chamber _
  have hb:bF b:=join_chamber (by cases cs <;> first | exact literal_chamber _ | exact hshape) hq
  have hh' : bF h:= by
    rcases hh with hh | hh | hh
    · exact hh.symm ▸ weighted_chamber _ p
    · exact hh.symm ▸ hp'
    · exact hh.symm ▸ hb
  have hr :aO (shape R) r := by
    cases cs with
    | union _=>exact ⟨le_rfl,le_rfl,le_rfl⟩
    | own _=>exact ⟨le_max_left _ _,le_rfl,le_rfl⟩
  have hboxes : ∀ u∈[b,h],bF u:= by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using And.intro hb hh'
  have hR0:=agr hp.factor.1.ne_zero
  have hregR:IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets) (bC R)) :=
    aPQ (by infer_instance) (by simpa using hR0)
  have hregG:=aIT R G (amo R G hp.factor.1 hp.proper)
  have hdimH :dimension H≤3:= by simpa [H,bEk] using aCR hregR
  have hJ:J=H ⊔ Ideal.span {bC G} := aIc R G
  have hdimJ:dimension J≤2 := by
    rw [hJ]
    exact (aCR hregG).trans (by change dimension H - 1≤2; omega)
  have hs (z) (hz :z∈uG) :=fiber_budget hcut hcycle hp A hh' hb hz
  have hbound:A.degree h≤tW H [q,b,h] := by
    calc
      _ = ∑ z∈uG,∑ B∈fiber z,cost B :=
        (sum_fiberwise_of_maps_to (fun _ hB=>mem_image_of_mem _ hB) cost).symm
      _ ≤ ∑ z∈uG,(AN J z :ℚ)*tW z [b,h] := by
        apply sum_le_sum
        intro z hz
        obtain ⟨hZ,hn,hle⟩:=hs z hz
        have hw: (1 :ℚ)≤AN J z := by
          exact_mod_cast Nat.succ_le_of_lt (aFq hZ)
        exact (le_mul_of_one_le_left hn hw).trans (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
      _≤tW J [b,h] :=
        hcycle J [b,h] (by simp) hboxes (by simpa using hdimJ) uG (fun z hz=>(hs z hz).1)
      _≤tW H [q,b,h] := by
        rw [hJ]
        exact hcut H q [b,h] (by simp) hq hboxes (by simpa using hdimH) _
          (bHn hp.H6) hregG
  exact (mul_le_mul_of_nonneg_left hbound (by norm_num)).trans
    (hfirst R r q b h hp.factor.1.ne_zero hr hq hb hh')
end
end q8kxiJa
