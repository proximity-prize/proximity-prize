import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0722
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- Source: Research6969.FarPoleChart
section Z6969Source1736
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960Front6960PoleChart

set_option Elab.async false
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Far6969PoleChart
noncomputable section
open Polynomial
open P1 (K I node twist p)
open K1_14 (L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open Far6969RescueGeometry (Model Family)
open scoped Polynomial

private def AdjacentChart {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
private theorem adjacent_chart {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
private theorem chart_poles {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      Fin.forall_fin_two.mpr ⟨hm, hm'⟩,
      Fin.forall_fin_two.mpr ⟨hd, hd'⟩,
      hcop, Fin.forall_fin_two.mpr ⟨hdet0, hdet1⟩⟩
  refine ⟨D, rfl, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
/-- The actual 69.60 family supplies both coprime pole blocks and all residues
for the same CRT lift used by the high interpolation banks. -/
theorem of_family {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ D : PoleData M.overhead.toNat, Nonempty (CRTLift D) ∧
      (∀ j i, (D.block j).eval (nodeL i) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  obtain ⟨H, chart⟩ := adjacent_chart M F
  obtain ⟨D, _, regular, residues⟩ := chart_poles M F H chart
  exact ⟨D, P0_10_1.crt_lift D, regular, residues⟩

end
end Lower6960.Far6969PoleChart

end Merged_R6960Front6960PoleChart
end Z6969Source1736

-- Source: Research6969.MiddleBudget
section Z6969Source1737
set_option autoImplicit true
namespace Research6969.MiddleBudget
open Finset Polynomial
open K1_14 (L)
open K1_14_1 (poleProduct nodeL)
open Lower6960
open Far6969RescueGeometry (Model Family)

theorem from_router {u del} (M:Model u del) {Γ} (F:Family M Γ)
    (lo:2390≤M.overhead) (hi:M.overhead≤2534)
    (route:∀{D:K1_14_1.PoleData M.overhead.toNat} (Crt:K1_14_1.CRTLift D),
      (∀j i,(D.block j).eval (nodeL i)≠0) →
      (∀z∈Γ,K1_14_1.MarkResidues D (M.label z) (F.scalar z)) →
      Nonempty (Prefix6969MiddleTransfer.Packet F Crt)) : Γ.card≤274784969259510674 := by
  obtain ⟨D,⟨Crt⟩,nodes,residues⟩:=Far6969PoleChart.of_family M F
  obtain ⟨P⟩:=route Crt nodes residues
  exact OrdinaryClaimMiddle.count F Crt P.toEarlyPacket (by omega) (by omega) (fun i=>by
    change (poleProduct D).eval (nodeL i)≠0
    rw [poleProduct,eval_mul];exact mul_ne_zero (nodes 0 i) (nodes 1 i)) residues

end Research6969.MiddleBudget
end Z6969Source1737

-- Source: Research6969.PrefixMiddleModel
section Z6969Source1738
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969MiddleTransfer
open Finset Polynomial
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family)
open Research6966

/-- At the actual middle model, exhaust the unit, affine and every
nonlinear outer-helper interval, producing the common terminal input. -/
theorem route_using
    (select : ∀ (a : Fin 6) (s : Fin 56),
      ∃ l u : ℕ, l≤s.val+1 ∧ s.val+1≤u ∧ Nonempty (Case (a.val+2) l u))
    {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2390≤M.overhead.toNat) (hi : M.overhead.toNat≤2534)
    (noPole : ∀j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Packet F Crt) := by
  obtain ⟨R, unit | ⟨phys, common, slope, jd, jmax, sd, smax, jbound, floor⟩⟩ :=
    Prefix6969MiddleOuter.split F Crt lo hi noPole residues
  · exact ordinary R hi noPole residues (Or.inl unit)
  by_cases linear : jetDegree R.out.exception=1
  · exact ordinary R hi noPole residues (Or.inr ⟨prime_of_irred common.1,slope,linear,smax⟩)
  have nonlinear : 2≤jetDegree R.out.exception := by omega
  have sm := jbound nonlinear
  let a : Fin 6 := ⟨jetDegree R.out.exception-2, by omega⟩
  let s : Fin 56 := ⟨seedDegree R.out.exception-1, by omega⟩
  have ae : a.val+2=jetDegree R.out.exception := by dsimp [a]; omega
  have se : s.val+1=seedDegree R.out.exception := by dsimp [s]; omega
  obtain ⟨l,h,lower,upper,⟨event⟩⟩ := select a s
  exact event.run F Crt lo hi noPole residues phys common slope ae.symm
    (by omega) (se ▸ lower) (se ▸ upper) (ae.symm ▸ floor)

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source1738

-- Source: Research6969.PhysicalChecks173
section Z6969Source1739
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2768 : Request := ⟨⟨⟨556,772,170,4853⟩,5255817068544,9968090926⟩,10,3,2,385609,27⟩
private theorem pass2768_2390 : (Triangular src2768) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2768_2391 : (Triangular src2768) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2768_2393 : (Triangular src2768) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2768_2399 : (Triangular src2768) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2768_2417 : (Triangular src2768) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2768_2469 : (Triangular src2768) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2768 : Cover (Triangular src2768) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2768_2390, by decide, by decide, pass2768_2391, by decide, by decide, pass2768_2393, by decide, by decide, pass2768_2399, by decide, by decide, pass2768_2417, by decide, by decide, pass2768_2469, rfl⟩
def src2769 : Request := ⟨⟨⟨556,772,170,4790⟩,5255817068544,9968090926⟩,10,3,2,385609,28⟩
private theorem pass2769_2390 : (Triangular src2769) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2769_2391 : (Triangular src2769) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2769_2393 : (Triangular src2769) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2769_2399 : (Triangular src2769) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2769_2417 : (Triangular src2769) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2769_2469 : (Triangular src2769) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2769 : Cover (Triangular src2769) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2769_2390, by decide, by decide, pass2769_2391, by decide, by decide, pass2769_2393, by decide, by decide, pass2769_2399, by decide, by decide, pass2769_2417, by decide, by decide, pass2769_2469, rfl⟩
def src2770 : Request := ⟨⟨⟨556,772,170,4729⟩,5255817068544,9968090926⟩,10,3,2,385609,29⟩
private theorem pass2770_2390 : (Triangular src2770) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2770_2391 : (Triangular src2770) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2770_2394 : (Triangular src2770) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2770_2402 : (Triangular src2770) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2770_2426 : (Triangular src2770) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2770_2496 : (Triangular src2770) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2770 : Cover (Triangular src2770) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2770_2390, by decide, by decide, pass2770_2391, by decide, by decide, pass2770_2394, by decide, by decide, pass2770_2402, by decide, by decide, pass2770_2426, by decide, by decide, pass2770_2496, rfl⟩
def src2771 : Request := ⟨⟨⟨556,772,170,4668⟩,5255817068544,9968090926⟩,10,3,2,385609,30⟩
private theorem pass2771_2390 : (Triangular src2771) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2771_2391 : (Triangular src2771) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2771_2393 : (Triangular src2771) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2771_2399 : (Triangular src2771) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2771_2417 : (Triangular src2771) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2771_2469 : (Triangular src2771) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2771 : Cover (Triangular src2771) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2771_2390, by decide, by decide, pass2771_2391, by decide, by decide, pass2771_2393, by decide, by decide, pass2771_2399, by decide, by decide, pass2771_2417, by decide, by decide, pass2771_2469, rfl⟩
def src2772 : Request := ⟨⟨⟨556,772,170,4609⟩,5255817068544,9968090926⟩,10,3,2,385609,31⟩
private theorem pass2772_2390 : (Triangular src2772) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2772_2391 : (Triangular src2772) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2772_2393 : (Triangular src2772) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2772_2399 : (Triangular src2772) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2772_2417 : (Triangular src2772) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2772_2469 : (Triangular src2772) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2772 : Cover (Triangular src2772) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2772_2390, by decide, by decide, pass2772_2391, by decide, by decide, pass2772_2393, by decide, by decide, pass2772_2399, by decide, by decide, pass2772_2417, by decide, by decide, pass2772_2469, rfl⟩
def src2773 : Request := ⟨⟨⟨556,772,170,4552⟩,5255817068544,9968090926⟩,10,3,2,385609,32⟩
private theorem pass2773_2390 : (Triangular src2773) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2773_2391 : (Triangular src2773) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2773_2394 : (Triangular src2773) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2773_2402 : (Triangular src2773) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2773_2426 : (Triangular src2773) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2773_2496 : (Triangular src2773) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2773 : Cover (Triangular src2773) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2773_2390, by decide, by decide, pass2773_2391, by decide, by decide, pass2773_2394, by decide, by decide, pass2773_2402, by decide, by decide, pass2773_2426, by decide, by decide, pass2773_2496, rfl⟩
def src2774 : Request := ⟨⟨⟨556,772,170,4496⟩,5255817068544,9968090926⟩,10,3,2,385609,33⟩
private theorem pass2774_2390 : (Triangular src2774) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2774_2391 : (Triangular src2774) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2774_2394 : (Triangular src2774) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2774_2402 : (Triangular src2774) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2774_2426 : (Triangular src2774) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2774_2496 : (Triangular src2774) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2774 : Cover (Triangular src2774) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2774_2390, by decide, by decide, pass2774_2391, by decide, by decide, pass2774_2394, by decide, by decide, pass2774_2402, by decide, by decide, pass2774_2426, by decide, by decide, pass2774_2496, rfl⟩
def src2775 : Request := ⟨⟨⟨556,772,170,4441⟩,5255817068544,9968090926⟩,10,3,2,385609,34⟩
private theorem pass2775_2390 : (Triangular src2775) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2775_2391 : (Triangular src2775) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2775_2393 : (Triangular src2775) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2775_2399 : (Triangular src2775) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2775_2417 : (Triangular src2775) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2775_2469 : (Triangular src2775) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2775 : Cover (Triangular src2775) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2775_2390, by decide, by decide, pass2775_2391, by decide, by decide, pass2775_2393, by decide, by decide, pass2775_2399, by decide, by decide, pass2775_2417, by decide, by decide, pass2775_2469, rfl⟩
def src2776 : Request := ⟨⟨⟨556,772,170,4388⟩,5255817068544,9968090926⟩,10,3,2,385609,35⟩
private theorem pass2776_2390 : (Triangular src2776) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2776_2391 : (Triangular src2776) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2776_2394 : (Triangular src2776) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2776_2402 : (Triangular src2776) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2776_2426 : (Triangular src2776) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2776_2496 : (Triangular src2776) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2776 : Cover (Triangular src2776) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2776_2390, by decide, by decide, pass2776_2391, by decide, by decide, pass2776_2394, by decide, by decide, pass2776_2402, by decide, by decide, pass2776_2426, by decide, by decide, pass2776_2496, rfl⟩
def src2777 : Request := ⟨⟨⟨556,772,170,4336⟩,5255817068544,9968090926⟩,10,3,2,385609,36⟩
private theorem pass2777_2390 : (Triangular src2777) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2777_2391 : (Triangular src2777) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2777_2393 : (Triangular src2777) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2777_2399 : (Triangular src2777) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2777_2417 : (Triangular src2777) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2777_2469 : (Triangular src2777) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2777 : Cover (Triangular src2777) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2777_2390, by decide, by decide, pass2777_2391, by decide, by decide, pass2777_2393, by decide, by decide, pass2777_2399, by decide, by decide, pass2777_2417, by decide, by decide, pass2777_2469, rfl⟩
def src2778 : Request := ⟨⟨⟨556,772,170,4286⟩,5255817068544,9968090926⟩,10,3,2,385609,37⟩
private theorem pass2778_2390 : (Triangular src2778) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2778_2391 : (Triangular src2778) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2778_2393 : (Triangular src2778) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2778_2399 : (Triangular src2778) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2778_2417 : (Triangular src2778) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2778_2469 : (Triangular src2778) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2778 : Cover (Triangular src2778) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2778_2390, by decide, by decide, pass2778_2391, by decide, by decide, pass2778_2393, by decide, by decide, pass2778_2399, by decide, by decide, pass2778_2417, by decide, by decide, pass2778_2469, rfl⟩
def src2779 : Request := ⟨⟨⟨556,772,170,4238⟩,5255817068544,9968090926⟩,10,3,2,385609,38⟩
private theorem pass2779_2390 : (Triangular src2779) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2779_2391 : (Triangular src2779) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2779_2394 : (Triangular src2779) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2779_2402 : (Triangular src2779) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2779_2426 : (Triangular src2779) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2779_2496 : (Triangular src2779) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2779 : Cover (Triangular src2779) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2779_2390, by decide, by decide, pass2779_2391, by decide, by decide, pass2779_2394, by decide, by decide, pass2779_2402, by decide, by decide, pass2779_2426, by decide, by decide, pass2779_2496, rfl⟩
def src2780 : Request := ⟨⟨⟨556,772,170,4190⟩,5255817068544,9968090926⟩,10,3,2,385609,39⟩
private theorem pass2780_2390 : (Triangular src2780) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2780_2391 : (Triangular src2780) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2780_2393 : (Triangular src2780) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2780_2399 : (Triangular src2780) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2780_2417 : (Triangular src2780) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2780_2469 : (Triangular src2780) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2780 : Cover (Triangular src2780) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2780_2390, by decide, by decide, pass2780_2391, by decide, by decide, pass2780_2393, by decide, by decide, pass2780_2399, by decide, by decide, pass2780_2417, by decide, by decide, pass2780_2469, rfl⟩
def src2781 : Request := ⟨⟨⟨556,772,170,4145⟩,5255817068544,9968090926⟩,10,3,2,385609,40⟩
private theorem pass2781_2390 : (Triangular src2781) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2781_2391 : (Triangular src2781) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2781_2394 : (Triangular src2781) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2781_2402 : (Triangular src2781) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2781_2426 : (Triangular src2781) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2781_2496 : (Triangular src2781) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2781 : Cover (Triangular src2781) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2781_2390, by decide, by decide, pass2781_2391, by decide, by decide, pass2781_2394, by decide, by decide, pass2781_2402, by decide, by decide, pass2781_2426, by decide, by decide, pass2781_2496, rfl⟩
def src2782 : Request := ⟨⟨⟨556,772,170,4101⟩,5255817068544,9968090926⟩,10,3,2,385609,41⟩
private theorem pass2782_2390 : (Triangular src2782) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2782_2391 : (Triangular src2782) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2782_2394 : (Triangular src2782) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2782_2402 : (Triangular src2782) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2782_2426 : (Triangular src2782) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2782_2496 : (Triangular src2782) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2782 : Cover (Triangular src2782) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2782_2390, by decide, by decide, pass2782_2391, by decide, by decide, pass2782_2394, by decide, by decide, pass2782_2402, by decide, by decide, pass2782_2426, by decide, by decide, pass2782_2496, rfl⟩
def src2783 : Request := ⟨⟨⟨556,772,170,4058⟩,5255817068544,9968090926⟩,10,3,2,385609,42⟩
private theorem pass2783_2390 : (Triangular src2783) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2783_2391 : (Triangular src2783) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2783_2393 : (Triangular src2783) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2783_2399 : (Triangular src2783) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2783_2417 : (Triangular src2783) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2783_2469 : (Triangular src2783) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2783 : Cover (Triangular src2783) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2783_2390, by decide, by decide, pass2783_2391, by decide, by decide, pass2783_2393, by decide, by decide, pass2783_2399, by decide, by decide, pass2783_2417, by decide, by decide, pass2783_2469, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1739

-- Source: Research6969.PrefixMainDataMiddle74
section Z6969Source1740
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle74
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 14, 20, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank65 2772, bank88 2372, bank87 3502, bank127 3031, bank131 10228, bank166 5048, bank199 7608, bank189 18034, bank176 24684, bank170 28384, bank214 8650] i
  head := src2783
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15875, 122681, 565459, 1911876],
    ![25417/2, 87814, 398755, 1399489],
    ![54680/9, 127490/3, 398755, 2627555/2],
    ![29433/8, 206587/8, 1871140/9, 633048],
    ![64334/25, 444196/25, 158046, 2223081/4],
    ![17323/9, 13243, 1073165/8, 3220023/8],
    ![18775/16, 268675/32, 2428982/25, 7499184/25],
    ![89110/121, 629100/121, 407440/7, 4618201/25],
    ![89110/121, 629100/121, 407440/7, 4618201/25],
    ![89110/121, 629100/121, 407440/7, 4618201/25],
    ![27452/49, 217738/49, 2159314/49, 28422232/169],
    ![27452/49, 1043687/242, 2159314/49, 878557/7],
    ![688141/1681, 1043687/242, 2159314/49, 878557/7],
    ![688141/1681, 6435560/1681, 1804125/49, 81939136/729],
    ![688141/1681, 1552100/441, 17331024/529, 100489],
    ![977501/2738, 1552100/441, 17331024/529, 100489],
    ![466774/1369, 1552100/441, 17331024/529, 100489],
    ![920087/2738, 1552100/441, 17331024/529, 100489],
    ![920087/2738, 4675419/1369, 84155302/2601, 2457119/25]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 41 257073 := by
  refine ⟨?_, rank154 4058, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2783⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free88_1
    · exact free87_3
    · exact free127_1
    · exact free131_1
    · exact free166_1
    · exact free199_1
    · exact free189_1
    · exact free176_1
    · exact free170_1
    · exact free214_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [234402742, 300066489, 298734563, 299280615, 299881531, 299873292, 299243369, 162619094, 162977905, 163046919, 162902837, 74177829, 74214949, 61350675, 87566734, 87661113, 143479721, 100000000, 218713614], [1578148, 1191277, 1198098, 1195301, 1192224, 1192266, 1195492, 2359630, 2353658, 2352509, 2354907, 5399928, 5396974, 6570642, 4542963, 4538199, 2696575, 3958949, 1707281],
  ![116097560583480, 1624514408796, 196842252600, 6702054840], 124586000707596822⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 4675419/1369, 84155302/2601, 2457119/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle74
end Z6969Source1740

-- Source: Research6969.PhysicalChecks143
section Z6969Source1741
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2288 : Request := ⟨⟨⟨560,781,172,4030⟩,5388141854720,10440670587⟩,4,2,1,257073,40⟩
private theorem pass2288_2390 : (Triangular src2288) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2288_2391 : (Triangular src2288) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2288_2393 : (Triangular src2288) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2288_2399 : (Triangular src2288) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2288_2417 : (Triangular src2288) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2288_2469 : (Triangular src2288) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2288 : Cover (Triangular src2288) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2288_2390, by decide, by decide, pass2288_2391, by decide, by decide, pass2288_2393, by decide, by decide, pass2288_2399, by decide, by decide, pass2288_2417, by decide, by decide, pass2288_2469, rfl⟩
def src2289 : Request := ⟨⟨⟨690,962,212,4737⟩,10065769922560,23997864317⟩,6,2,1,257073,40⟩
private theorem pass2289_2390 : (Triangular src2289) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2289_2391 : (Triangular src2289) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2289_2393 : (Triangular src2289) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2289_2399 : (Triangular src2289) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2289_2416 : (Triangular src2289) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2289_2464 : (Triangular src2289) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2289 : Cover (Triangular src2289) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2289_2390, by decide, by decide, pass2289_2391, by decide, by decide, pass2289_2393, by decide, by decide, pass2289_2399, by decide, by decide, pass2289_2416, by decide, by decide, pass2289_2464, rfl⟩
def src2290 : Request := ⟨⟨⟨825,1151,260,5750⟩,17518948515840,50057971890⟩,10,2,1,257073,40⟩
private theorem pass2290_2390 : (Triangular src2290) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2290_2391 : (Triangular src2290) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2290_2393 : (Triangular src2290) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2290_2399 : (Triangular src2290) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2290_2416 : (Triangular src2290) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2290_2463 : (Triangular src2290) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2290 : Cover (Triangular src2290) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2290_2390, by decide, by decide, pass2290_2391, by decide, by decide, pass2290_2393, by decide, by decide, pass2290_2399, by decide, by decide, pass2290_2416, by decide, by decide, pass2290_2463, rfl⟩
def src2291 : Request := ⟨⟨⟨1200,1674,368,8655⟩,52718727069696,218807905514⟩,20,2,1,257073,40⟩
private theorem pass2291_2390 : (Triangular src2291) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2291_2391 : (Triangular src2291) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2291_2393 : (Triangular src2291) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2291_2399 : (Triangular src2291) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2291_2415 : (Triangular src2291) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2291_2458 : (Triangular src2291) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2291 : Cover (Triangular src2291) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2291_2390, by decide, by decide, pass2291_2391, by decide, by decide, pass2291_2393, by decide, by decide, pass2291_2399, by decide, by decide, pass2291_2415, by decide, by decide, pass2291_2458, rfl⟩
def src2292 : Request := ⟨⟨⟨2600,3627,798,17855⟩,535425056505856,4812227595495⟩,50,2,1,257073,40⟩
private theorem pass2292_2390 : (Triangular src2292) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2292_2391 : (Triangular src2292) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2292_2393 : (Triangular src2292) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2292_2398 : (Triangular src2292) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2292_2412 : (Triangular src2292) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2292_2448 : (Triangular src2292) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2292 : Cover (Triangular src2292) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2292_2390, by decide, by decide, pass2292_2391, by decide, by decide, pass2292_2393, by decide, by decide, pass2292_2398, by decide, by decide, pass2292_2412, by decide, by decide, pass2292_2448, rfl⟩
def src2293 : Request := ⟨⟨⟨4800,6695,1512,33870⟩,3433136573644800,56953438854149⟩,110,2,1,257073,40⟩
private theorem pass2293_2390 : (Triangular src2293) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2391 : (Triangular src2293) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2393 : (Triangular src2293) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2398 : (Triangular src2293) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2411 : (Triangular src2293) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2445 : (Triangular src2293) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2293_2533 : (Triangular src2293) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2293 : Cover (Triangular src2293) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2293_2390, by decide, by decide, pass2293_2391, by decide, by decide, pass2293_2393, by decide, by decide, pass2293_2398, by decide, by decide, pass2293_2411, by decide, by decide, pass2293_2445, by decide, by decide, pass2293_2533, rfl⟩
def src2294 : Request := ⟨⟨⟨10000,13948,3070,72807⟩,30428373265940480,1050983571587703⟩,245,2,1,257073,40⟩
private theorem pass2294_2390 : (Triangular src2294) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2391 : (Triangular src2294) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2393 : (Triangular src2294) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2398 : (Triangular src2294) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2411 : (Triangular src2294) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2445 : (Triangular src2294) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2294_2532 : (Triangular src2294) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2294 : Cover (Triangular src2294) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2294_2390, by decide, by decide, pass2294_2391, by decide, by decide, pass2294_2393, by decide, by decide, pass2294_2398, by decide, by decide, pass2294_2411, by decide, by decide, pass2294_2445, by decide, by decide, pass2294_2532, rfl⟩
def src2295 : Request := ⟨⟨⟨400,558,123,2816⟩,1971918995456,2734096379⟩,0,2,1,257073,41⟩
private theorem pass2295_2390 : (Triangular src2295) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2295_2391 : (Triangular src2295) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2295_2394 : (Triangular src2295) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2295_2403 : (Triangular src2295) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2295_2431 : (Triangular src2295) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2295_2517 : (Triangular src2295) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2295 : Cover (Triangular src2295) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass2295_2390, by decide, by decide, pass2295_2391, by decide, by decide, pass2295_2394, by decide, by decide, pass2295_2403, by decide, by decide, pass2295_2431, by decide, by decide, pass2295_2517, rfl⟩
def src2296 : Request := ⟨⟨⟨470,655,144,3181⟩,3184589537280,5168862572⟩,1,2,1,257073,41⟩
private theorem pass2296_2390 : (Triangular src2296) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2296_2391 : (Triangular src2296) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2296_2394 : (Triangular src2296) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2296_2403 : (Triangular src2296) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2296_2430 : (Triangular src2296) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2296_2511 : (Triangular src2296) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2296 : Cover (Triangular src2296) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2296_2390, by decide, by decide, pass2296_2391, by decide, by decide, pass2296_2394, by decide, by decide, pass2296_2403, by decide, by decide, pass2296_2430, by decide, by decide, pass2296_2511, rfl⟩
def src2297 : Request := ⟨⟨⟨470,655,148,3295⟩,3250957582336,5279398867⟩,2,2,1,257073,41⟩
private theorem pass2297_2390 : (Triangular src2297) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2297_2391 : (Triangular src2297) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2297_2394 : (Triangular src2297) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2297_2403 : (Triangular src2297) 2403 2428 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2297_2429 : (Triangular src2297) 2429 2506 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2297_2507 : (Triangular src2297) 2507 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2297 : Cover (Triangular src2297) 2534 2390 [2390,2393,2402,2428,2506,2534] := by
  exact ⟨by decide, by decide, pass2297_2390, by decide, by decide, pass2297_2391, by decide, by decide, pass2297_2394, by decide, by decide, pass2297_2403, by decide, by decide, pass2297_2429, by decide, by decide, pass2297_2507, rfl⟩
def src2298 : Request := ⟨⟨⟨560,781,172,3778⟩,5388141854720,10440670587⟩,3,2,1,257073,41⟩
private theorem pass2298_2390 : (Triangular src2298) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2298_2391 : (Triangular src2298) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2298_2393 : (Triangular src2298) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2298_2399 : (Triangular src2298) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2298_2417 : (Triangular src2298) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2298_2469 : (Triangular src2298) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2298 : Cover (Triangular src2298) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2298_2390, by decide, by decide, pass2298_2391, by decide, by decide, pass2298_2393, by decide, by decide, pass2298_2399, by decide, by decide, pass2298_2417, by decide, by decide, pass2298_2469, rfl⟩
def src2299 : Request := ⟨⟨⟨560,781,172,3937⟩,5388141854720,10440670587⟩,4,2,1,257073,41⟩
private theorem pass2299_2390 : (Triangular src2299) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2299_2391 : (Triangular src2299) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2299_2393 : (Triangular src2299) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2299_2399 : (Triangular src2299) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2299_2417 : (Triangular src2299) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2299_2469 : (Triangular src2299) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2299 : Cover (Triangular src2299) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2299_2390, by decide, by decide, pass2299_2391, by decide, by decide, pass2299_2393, by decide, by decide, pass2299_2399, by decide, by decide, pass2299_2417, by decide, by decide, pass2299_2469, rfl⟩
def src2300 : Request := ⟨⟨⟨690,962,212,4971⟩,10065769922560,23997864317⟩,8,2,1,257073,41⟩
private theorem pass2300_2390 : (Triangular src2300) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2300_2391 : (Triangular src2300) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2300_2393 : (Triangular src2300) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2300_2399 : (Triangular src2300) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2300_2416 : (Triangular src2300) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2300_2465 : (Triangular src2300) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2300 : Cover (Triangular src2300) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2300_2390, by decide, by decide, pass2300_2391, by decide, by decide, pass2300_2393, by decide, by decide, pass2300_2399, by decide, by decide, pass2300_2416, by decide, by decide, pass2300_2465, rfl⟩
def src2301 : Request := ⟨⟨⟨1000,1395,307,7215⟩,30557599170560,105715278267⟩,16,2,1,257073,41⟩
private theorem pass2301_2390 : (Triangular src2301) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2301_2391 : (Triangular src2301) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2301_2393 : (Triangular src2301) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2301_2399 : (Triangular src2301) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2301_2415 : (Triangular src2301) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2301_2459 : (Triangular src2301) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2301 : Cover (Triangular src2301) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2301_2390, by decide, by decide, pass2301_2391, by decide, by decide, pass2301_2393, by decide, by decide, pass2301_2399, by decide, by decide, pass2301_2415, by decide, by decide, pass2301_2459, rfl⟩
def src2302 : Request := ⟨⟨⟨1450,2022,445,9976⟩,92998964346880,465769321795⟩,25,2,1,257073,41⟩
private theorem pass2302_2390 : (Triangular src2302) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2302_2391 : (Triangular src2302) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2302_2393 : (Triangular src2302) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2302_2399 : (Triangular src2302) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2302_2415 : (Triangular src2302) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2302_2458 : (Triangular src2302) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2302 : Cover (Triangular src2302) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2302_2390, by decide, by decide, pass2302_2391, by decide, by decide, pass2302_2393, by decide, by decide, pass2302_2399, by decide, by decide, pass2302_2415, by decide, by decide, pass2302_2458, rfl⟩
def src2303 : Request := ⟨⟨⟨2100,2929,645,14337⟩,282396798484480,2049139102608⟩,40,2,1,257073,41⟩
private theorem pass2303_2390 : (Triangular src2303) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2303_2391 : (Triangular src2303) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2303_2393 : (Triangular src2303) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2303_2398 : (Triangular src2303) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2303_2412 : (Triangular src2303) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2303_2449 : (Triangular src2303) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2303 : Cover (Triangular src2303) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2303_2390, by decide, by decide, pass2303_2391, by decide, by decide, pass2303_2393, by decide, by decide, pass2303_2398, by decide, by decide, pass2303_2412, by decide, by decide, pass2303_2449, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1741

-- Source: Research6969.PhysicalChecks144
section Z6969Source1742
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2304 : Request := ⟨⟨⟨4800,6695,1474,33692⟩,3367547627110400,55837558620681⟩,110,2,1,257073,41⟩
private theorem pass2304_2390 : (Triangular src2304) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2391 : (Triangular src2304) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2393 : (Triangular src2304) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2398 : (Triangular src2304) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2411 : (Triangular src2304) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2445 : (Triangular src2304) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2304_2533 : (Triangular src2304) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2304 : Cover (Triangular src2304) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2304_2390, by decide, by decide, pass2304_2391, by decide, by decide, pass2304_2393, by decide, by decide, pass2304_2398, by decide, by decide, pass2304_2411, by decide, by decide, pass2304_2445, by decide, by decide, pass2304_2533, rfl⟩
def src2305 : Request := ⟨⟨⟨10000,13948,3150,69781⟩,31027650042265600,1072221490229155⟩,245,2,1,257073,41⟩
private theorem pass2305_2390 : (Triangular src2305) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2391 : (Triangular src2305) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2393 : (Triangular src2305) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2398 : (Triangular src2305) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2411 : (Triangular src2305) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2444 : (Triangular src2305) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2305_2529 : (Triangular src2305) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2305 : Cover (Triangular src2305) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2305_2390, by decide, by decide, pass2305_2391, by decide, by decide, pass2305_2393, by decide, by decide, pass2305_2398, by decide, by decide, pass2305_2411, by decide, by decide, pass2305_2444, by decide, by decide, pass2305_2529, rfl⟩
def src2306 : Request := ⟨⟨⟨325,453,100,2189⟩,1061047500800,1193036697⟩,0,2,1,257073,51⟩
private theorem pass2306_2390 : (Triangular src2306) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2306_2391 : (Triangular src2306) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2306_2394 : (Triangular src2306) 2394 2403 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2306_2404 : (Triangular src2306) 2404 2435 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2306_2436 : (Triangular src2306) 2436 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2306 : Cover (Triangular src2306) 2534 2390 [2390,2393,2403,2435,2534] := by
  exact ⟨by decide, by decide, pass2306_2390, by decide, by decide, pass2306_2391, by decide, by decide, pass2306_2394, by decide, by decide, pass2306_2404, by decide, by decide, pass2306_2436, rfl⟩
def src2307 : Request := ⟨⟨⟨400,558,123,2544⟩,1971918995456,2734096379⟩,1,2,1,257073,51⟩
private theorem pass2307_2390 : (Triangular src2307) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2307_2391 : (Triangular src2307) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2307_2394 : (Triangular src2307) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2307_2403 : (Triangular src2307) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2307_2431 : (Triangular src2307) 2431 2517 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2307_2518 : (Triangular src2307) 2518 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2307 : Cover (Triangular src2307) 2534 2390 [2390,2393,2402,2430,2517,2534] := by
  exact ⟨by decide, by decide, pass2307_2390, by decide, by decide, pass2307_2391, by decide, by decide, pass2307_2394, by decide, by decide, pass2307_2403, by decide, by decide, pass2307_2431, by decide, by decide, pass2307_2518, rfl⟩
def src2308 : Request := ⟨⟨⟨400,558,120,2757⟩,1935519252480,2682384904⟩,2,2,1,257073,51⟩
private theorem pass2308_2390 : (Triangular src2308) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2308_2391 : (Triangular src2308) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2308_2394 : (Triangular src2308) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2308_2403 : (Triangular src2308) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2308_2431 : (Triangular src2308) 2431 2518 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2308_2519 : (Triangular src2308) 2519 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2308 : Cover (Triangular src2308) 2534 2390 [2390,2393,2402,2430,2518,2534] := by
  exact ⟨by decide, by decide, pass2308_2390, by decide, by decide, pass2308_2391, by decide, by decide, pass2308_2394, by decide, by decide, pass2308_2403, by decide, by decide, pass2308_2431, by decide, by decide, pass2308_2519, rfl⟩
def src2309 : Request := ⟨⟨⟨400,558,123,2805⟩,1971918995456,2734096379⟩,3,2,1,257073,51⟩
private theorem pass2309_2390 : (Triangular src2309) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2309_2391 : (Triangular src2309) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2309_2394 : (Triangular src2309) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2309_2403 : (Triangular src2309) 2403 2430 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2309_2431 : (Triangular src2309) 2431 2516 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2309_2517 : (Triangular src2309) 2517 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2309 : Cover (Triangular src2309) 2534 2390 [2390,2393,2402,2430,2516,2534] := by
  exact ⟨by decide, by decide, pass2309_2390, by decide, by decide, pass2309_2391, by decide, by decide, pass2309_2394, by decide, by decide, pass2309_2403, by decide, by decide, pass2309_2431, by decide, by decide, pass2309_2517, rfl⟩
def src2310 : Request := ⟨⟨⟨470,655,144,3112⟩,3184589537280,5168862572⟩,4,2,1,257073,51⟩
private theorem pass2310_2390 : (Triangular src2310) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2310_2391 : (Triangular src2310) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2310_2394 : (Triangular src2310) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2310_2403 : (Triangular src2310) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2310_2430 : (Triangular src2310) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2310_2511 : (Triangular src2310) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2310 : Cover (Triangular src2310) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2310_2390, by decide, by decide, pass2310_2391, by decide, by decide, pass2310_2394, by decide, by decide, pass2310_2403, by decide, by decide, pass2310_2430, by decide, by decide, pass2310_2511, rfl⟩
def src2311 : Request := ⟨⟨⟨470,655,144,3406⟩,3184589537280,5168862572⟩,6,2,1,257073,51⟩
private theorem pass2311_2390 : (Triangular src2311) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2311_2391 : (Triangular src2311) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2311_2394 : (Triangular src2311) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2311_2403 : (Triangular src2311) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2311_2430 : (Triangular src2311) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2311_2511 : (Triangular src2311) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2311 : Cover (Triangular src2311) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2311_2390, by decide, by decide, pass2311_2391, by decide, by decide, pass2311_2394, by decide, by decide, pass2311_2403, by decide, by decide, pass2311_2430, by decide, by decide, pass2311_2511, rfl⟩
def src2312 : Request := ⟨⟨⟨560,781,172,3893⟩,5388141854720,10440670587⟩,8,2,1,257073,51⟩
private theorem pass2312_2390 : (Triangular src2312) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2312_2391 : (Triangular src2312) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2312_2394 : (Triangular src2312) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2312_2402 : (Triangular src2312) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2312_2426 : (Triangular src2312) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2312_2496 : (Triangular src2312) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2312 : Cover (Triangular src2312) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2312_2390, by decide, by decide, pass2312_2391, by decide, by decide, pass2312_2394, by decide, by decide, pass2312_2402, by decide, by decide, pass2312_2426, by decide, by decide, pass2312_2496, rfl⟩
def src2313 : Request := ⟨⟨⟨690,962,217,4846⟩,10244384358400,24434817260⟩,13,2,1,257073,51⟩
private theorem pass2313_2390 : (Triangular src2313) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2313_2391 : (Triangular src2313) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2313_2393 : (Triangular src2313) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2313_2399 : (Triangular src2313) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2313_2416 : (Triangular src2313) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2313_2464 : (Triangular src2313) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2313 : Cover (Triangular src2313) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2313_2390, by decide, by decide, pass2313_2391, by decide, by decide, pass2313_2393, by decide, by decide, pass2313_2399, by decide, by decide, pass2313_2416, by decide, by decide, pass2313_2464, rfl⟩
def src2314 : Request := ⟨⟨⟨1000,1394,315,7278⟩,31157463285760,107596110457⟩,25,2,1,257073,51⟩
private theorem pass2314_2390 : (Triangular src2314) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2314_2391 : (Triangular src2314) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2314_2393 : (Triangular src2314) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2314_2399 : (Triangular src2314) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2314_2415 : (Triangular src2314) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2314_2459 : (Triangular src2314) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2314 : Cover (Triangular src2314) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2314_2390, by decide, by decide, pass2314_2391, by decide, by decide, pass2314_2393, by decide, by decide, pass2314_2399, by decide, by decide, pass2314_2415, by decide, by decide, pass2314_2459, rfl⟩
def src2315 : Request := ⟨⟨⟨2100,2928,662,15535⟩,288013660979200,2088662039796⟩,65,2,1,257073,51⟩
private theorem pass2315_2390 : (Triangular src2315) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2315_2391 : (Triangular src2315) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2315_2393 : (Triangular src2315) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2315_2398 : (Triangular src2315) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2315_2412 : (Triangular src2315) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2315_2449 : (Triangular src2315) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2315 : Cover (Triangular src2315) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2315_2390, by decide, by decide, pass2315_2391, by decide, by decide, pass2315_2393, by decide, by decide, pass2315_2398, by decide, by decide, pass2315_2412, by decide, by decide, pass2315_2449, rfl⟩
def src2316 : Request := ⟨⟨⟨5700,7948,1750,42285⟩,5637370734182400,110890906752819⟩,190,2,1,257073,51⟩
private theorem pass2316_2390 : (Triangular src2316) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2391 : (Triangular src2316) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2393 : (Triangular src2316) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2398 : (Triangular src2316) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2411 : (Triangular src2316) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2445 : (Triangular src2316) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2316_2533 : (Triangular src2316) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2316 : Cover (Triangular src2316) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2316_2390, by decide, by decide, pass2316_2391, by decide, by decide, pass2316_2393, by decide, by decide, pass2316_2398, by decide, by decide, pass2316_2411, by decide, by decide, pass2316_2445, by decide, by decide, pass2316_2533, rfl⟩
def src2317 : Request := ⟨⟨⟨1000,1395,301,28329⟩,30103476895744,104105680031⟩,0,3,1,385610,1⟩
private theorem pass2317_2390 : (Triangular src2317) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2317_2391 : (Triangular src2317) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2317_2393 : (Triangular src2317) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2317_2399 : (Triangular src2317) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2317_2415 : (Triangular src2317) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2317_2459 : (Triangular src2317) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2317 : Cover (Triangular src2317) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2317_2390, by decide, by decide, pass2317_2391, by decide, by decide, pass2317_2393, by decide, by decide, pass2317_2399, by decide, by decide, pass2317_2415, by decide, by decide, pass2317_2459, rfl⟩
def src2318 : Request := ⟨⟨⟨1000,1395,301,29915⟩,30103476895744,104105680031⟩,1,3,1,385610,1⟩
private theorem pass2318_2390 : (Triangular src2318) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2318_2391 : (Triangular src2318) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2318_2393 : (Triangular src2318) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2318_2399 : (Triangular src2318) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2318_2415 : (Triangular src2318) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2318_2459 : (Triangular src2318) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2318 : Cover (Triangular src2318) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2318_2390, by decide, by decide, pass2318_2391, by decide, by decide, pass2318_2393, by decide, by decide, pass2318_2399, by decide, by decide, pass2318_2415, by decide, by decide, pass2318_2459, rfl⟩
def src2319 : Request := ⟨⟨⟨1000,1395,296,32425⟩,29722184515584,102755930405⟩,2,3,1,385610,1⟩
private theorem pass2319_2390 : (Triangular src2319) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2319_2391 : (Triangular src2319) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2319_2393 : (Triangular src2319) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2319_2399 : (Triangular src2319) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2319_2416 : (Triangular src2319) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2319_2463 : (Triangular src2319) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2319 : Cover (Triangular src2319) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2319_2390, by decide, by decide, pass2319_2391, by decide, by decide, pass2319_2393, by decide, by decide, pass2319_2399, by decide, by decide, pass2319_2416, by decide, by decide, pass2319_2463, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1742

-- Source: Research6969.PrefixRescueDataMiddle74
section Z6969Source1743
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle74
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,50⟩
  bank i := ![bank134 2816, bank142 3181, bank143 3295, bank156 3778, bank156 3937, bank193 4971, bank222 7215, bank233 9976, bank249 14337, bank324 33692, bank376 69781] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 25, 40, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 41

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 2816
    · exact rank142 3181
    · exact rank143 3295
    · exact rank156 3778
    · exact rank156 3937
    · exact rank193 4971
    · exact rank222 7215
    · exact rank233 9976
    · exact rank249 14337
    · exact rank324 33692
    · exact rank376 69781
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2295⟩
    · exact ⟨_, cover2296⟩
    · exact ⟨_, cover2297⟩
    · exact ⟨_, cover2298⟩
    · exact ⟨_, cover2299⟩
    · exact ⟨_, cover2300⟩
    · exact ⟨_, cover2301⟩
    · exact ⟨_, cover2302⟩
    · exact ⟨_, cover2303⟩
    · exact ⟨_, cover2304⟩
    · exact ⟨_, cover2305⟩

def price : EarlyPrice := ⟨2, 50, 10, 65/100, 60/100, ![1359737842209, 237602810285, 61380235350, 1227627450], 968462971282643⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8549/123, 227281/246, 418481/123, 1744525/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle74
end Z6969Source1743

-- Source: Research6969.PrefixMiddleSaved74
section Z6969Source1744
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved74
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle74.price Lower6960.Prefix6969RescueData.Middle74.price :=
  ⟨336, 3415, 69, 923, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle74.plan Lower6960.Prefix6969RescueData.Middle74.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 41 50 :=
  ⟨Lower6960.Prefix6969MainCases.Middle74.plan, Lower6960.Prefix6969MainCases.Middle74.price, Lower6960.Prefix6969MainCases.Middle74.valid, Lower6960.Prefix6969MainCases.Middle74.priced, Lower6960.Prefix6969MainCases.Middle74.sources,
   Lower6960.Prefix6969RescueData.Middle74.plan, Lower6960.Prefix6969RescueData.Middle74.price, Lower6960.Prefix6969RescueData.Middle74.sources, Lower6960.Prefix6969RescueData.Middle74.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved74
end Z6969Source1744

-- Source: Research6969.PhysicalChecks174
section Z6969Source1745
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2784 : Request := ⟨⟨⟨556,772,170,3715⟩,5255817068544,9968090926⟩,10,3,2,385609,52⟩
private theorem pass2784_2390 : (Triangular src2784) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2784_2391 : (Triangular src2784) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2784_2393 : (Triangular src2784) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2784_2399 : (Triangular src2784) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2784_2417 : (Triangular src2784) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2784_2469 : (Triangular src2784) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2784 : Cover (Triangular src2784) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2784_2390, by decide, by decide, pass2784_2391, by decide, by decide, pass2784_2393, by decide, by decide, pass2784_2399, by decide, by decide, pass2784_2417, by decide, by decide, pass2784_2469, rfl⟩
def src2785 : Request := ⟨⟨⟨560,781,169,12950⟩,5316921262080,10299257375⟩,0,4,1,514147,1⟩
private theorem pass2785_2390 : (Triangular src2785) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2785_2391 : (Triangular src2785) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2785_2393 : (Triangular src2785) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2785_2399 : (Triangular src2785) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2785_2417 : (Triangular src2785) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2785_2469 : (Triangular src2785) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2785 : Cover (Triangular src2785) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2785_2390, by decide, by decide, pass2785_2391, by decide, by decide, pass2785_2393, by decide, by decide, pass2785_2399, by decide, by decide, pass2785_2417, by decide, by decide, pass2785_2469, rfl⟩
def src2786 : Request := ⟨⟨⟨560,781,169,14026⟩,5316921262080,10299257375⟩,1,4,1,514147,1⟩
private theorem pass2786_2390 : (Triangular src2786) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2786_2391 : (Triangular src2786) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2786_2393 : (Triangular src2786) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2786_2399 : (Triangular src2786) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2786_2417 : (Triangular src2786) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2786_2469 : (Triangular src2786) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2786 : Cover (Triangular src2786) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2786_2390, by decide, by decide, pass2786_2391, by decide, by decide, pass2786_2393, by decide, by decide, pass2786_2399, by decide, by decide, pass2786_2417, by decide, by decide, pass2786_2469, rfl⟩
def src2787 : Request := ⟨⟨⟨690,962,208,15626⟩,9921631092736,23645774460⟩,2,4,1,514147,1⟩
private theorem pass2787_2390 : (Triangular src2787) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2787_2391 : (Triangular src2787) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2787_2393 : (Triangular src2787) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2787_2399 : (Triangular src2787) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2787_2416 : (Triangular src2787) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2787_2465 : (Triangular src2787) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2787 : Cover (Triangular src2787) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2787_2390, by decide, by decide, pass2787_2391, by decide, by decide, pass2787_2393, by decide, by decide, pass2787_2399, by decide, by decide, pass2787_2416, by decide, by decide, pass2787_2465, rfl⟩
def src2788 : Request := ⟨⟨⟨560,781,169,16821⟩,5316921262080,10299257375⟩,3,4,1,514147,1⟩
private theorem pass2788_2390 : (Triangular src2788) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2788_2391 : (Triangular src2788) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2788_2393 : (Triangular src2788) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2788_2399 : (Triangular src2788) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2788_2417 : (Triangular src2788) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2788_2469 : (Triangular src2788) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2788 : Cover (Triangular src2788) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2788_2390, by decide, by decide, pass2788_2391, by decide, by decide, pass2788_2393, by decide, by decide, pass2788_2399, by decide, by decide, pass2788_2417, by decide, by decide, pass2788_2469, rfl⟩
def src2789 : Request := ⟨⟨⟨690,962,208,16643⟩,9921631092736,23645774460⟩,3,4,1,514147,1⟩
private theorem pass2789_2390 : (Triangular src2789) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2789_2391 : (Triangular src2789) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2789_2393 : (Triangular src2789) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2789_2399 : (Triangular src2789) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2789_2416 : (Triangular src2789) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2789_2465 : (Triangular src2789) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2789 : Cover (Triangular src2789) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2789_2390, by decide, by decide, pass2789_2391, by decide, by decide, pass2789_2393, by decide, by decide, pass2789_2399, by decide, by decide, pass2789_2416, by decide, by decide, pass2789_2465, rfl⟩
def src2790 : Request := ⟨⟨⟨825,1151,248,20519⟩,16903818182656,48256472894⟩,6,4,1,514147,1⟩
private theorem pass2790_2390 : (Triangular src2790) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2790_2391 : (Triangular src2790) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2790_2393 : (Triangular src2790) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2790_2399 : (Triangular src2790) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2790_2416 : (Triangular src2790) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2790_2463 : (Triangular src2790) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2790 : Cover (Triangular src2790) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2790_2390, by decide, by decide, pass2790_2391, by decide, by decide, pass2790_2393, by decide, by decide, pass2790_2399, by decide, by decide, pass2790_2416, by decide, by decide, pass2790_2463, rfl⟩
def src2791 : Request := ⟨⟨⟨1200,1674,368,26076⟩,52718727069696,218807905514⟩,10,4,1,514147,1⟩
private theorem pass2791_2390 : (Triangular src2791) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2791_2391 : (Triangular src2791) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2791_2393 : (Triangular src2791) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2791_2399 : (Triangular src2791) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2791_2415 : (Triangular src2791) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2791_2458 : (Triangular src2791) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2791 : Cover (Triangular src2791) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2791_2390, by decide, by decide, pass2791_2391, by decide, by decide, pass2791_2393, by decide, by decide, pass2791_2399, by decide, by decide, pass2791_2415, by decide, by decide, pass2791_2458, rfl⟩
def src2792 : Request := ⟨⟨⟨1450,2023,445,30498⟩,92998964346880,466511127281⟩,13,4,1,514147,1⟩
private theorem pass2792_2390 : (Triangular src2792) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2792_2391 : (Triangular src2792) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2792_2393 : (Triangular src2792) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2792_2399 : (Triangular src2792) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2792_2415 : (Triangular src2792) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2792_2457 : (Triangular src2792) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2792 : Cover (Triangular src2792) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2792_2390, by decide, by decide, pass2792_2391, by decide, by decide, pass2792_2393, by decide, by decide, pass2792_2399, by decide, by decide, pass2792_2415, by decide, by decide, pass2792_2457, rfl⟩
def src2793 : Request := ⟨⟨⟨2100,2930,632,46195⟩,278060332482560,2019119590628⟩,25,4,1,514147,1⟩
private theorem pass2793_2390 : (Triangular src2793) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2793_2391 : (Triangular src2793) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2793_2393 : (Triangular src2793) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2793_2398 : (Triangular src2793) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2793_2412 : (Triangular src2793) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2793_2449 : (Triangular src2793) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2793 : Cover (Triangular src2793) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2793_2390, by decide, by decide, pass2793_2391, by decide, by decide, pass2793_2393, by decide, by decide, pass2793_2398, by decide, by decide, pass2793_2412, by decide, by decide, pass2793_2449, rfl⟩
def src2794 : Request := ⟨⟨⟨4800,6697,1474,99689⟩,3367547627110400,55891290082931⟩,65,4,1,514147,1⟩
private theorem pass2794_2390 : (Triangular src2794) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2391 : (Triangular src2794) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2393 : (Triangular src2794) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2398 : (Triangular src2794) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2411 : (Triangular src2794) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2445 : (Triangular src2794) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2794_2532 : (Triangular src2794) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2794 : Cover (Triangular src2794) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2794_2390, by decide, by decide, pass2794_2391, by decide, by decide, pass2794_2393, by decide, by decide, pass2794_2398, by decide, by decide, pass2794_2411, by decide, by decide, pass2794_2445, by decide, by decide, pass2794_2532, rfl⟩
def src2795 : Request := ⟨⟨⟨6900,9626,2118,153698⟩,9997036108906496,238415548481346⟩,110,4,1,514147,1⟩
private theorem pass2795_2390 : (Triangular src2795) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2391 : (Triangular src2795) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2393 : (Triangular src2795) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2398 : (Triangular src2795) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2411 : (Triangular src2795) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2444 : (Triangular src2795) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2795_2529 : (Triangular src2795) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2795 : Cover (Triangular src2795) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2795_2390, by decide, by decide, pass2795_2391, by decide, by decide, pass2795_2393, by decide, by decide, pass2795_2398, by decide, by decide, pass2795_2411, by decide, by decide, pass2795_2444, by decide, by decide, pass2795_2529, rfl⟩
def src2796 : Request := ⟨⟨⟨690,963,212,13406⟩,10065769922560,24078187611⟩,0,4,1,514147,2⟩
private theorem pass2796_2390 : (Triangular src2796) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2796_2391 : (Triangular src2796) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2796_2393 : (Triangular src2796) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2796_2399 : (Triangular src2796) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2796_2416 : (Triangular src2796) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2796_2464 : (Triangular src2796) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2796 : Cover (Triangular src2796) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2796_2390, by decide, by decide, pass2796_2391, by decide, by decide, pass2796_2393, by decide, by decide, pass2796_2399, by decide, by decide, pass2796_2416, by decide, by decide, pass2796_2464, rfl⟩
def src2797 : Request := ⟨⟨⟨690,963,208,14303⟩,9921631092736,23724874690⟩,1,4,1,514147,2⟩
private theorem pass2797_2390 : (Triangular src2797) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2797_2391 : (Triangular src2797) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2797_2393 : (Triangular src2797) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2797_2399 : (Triangular src2797) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2797_2416 : (Triangular src2797) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2797_2464 : (Triangular src2797) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2797 : Cover (Triangular src2797) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2797_2390, by decide, by decide, pass2797_2391, by decide, by decide, pass2797_2393, by decide, by decide, pass2797_2399, by decide, by decide, pass2797_2416, by decide, by decide, pass2797_2464, rfl⟩
def src2798 : Request := ⟨⟨⟨690,962,208,16104⟩,9921631092736,23645774460⟩,3,4,1,514147,2⟩
private theorem pass2798_2390 : (Triangular src2798) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2798_2391 : (Triangular src2798) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2798_2393 : (Triangular src2798) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2798_2399 : (Triangular src2798) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2798_2416 : (Triangular src2798) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2798_2465 : (Triangular src2798) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2798 : Cover (Triangular src2798) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2798_2390, by decide, by decide, pass2798_2391, by decide, by decide, pass2798_2393, by decide, by decide, pass2798_2399, by decide, by decide, pass2798_2416, by decide, by decide, pass2798_2465, rfl⟩
def src2799 : Request := ⟨⟨⟨1000,1395,307,22243⟩,30557599170560,105715278267⟩,8,4,1,514147,2⟩
private theorem pass2799_2390 : (Triangular src2799) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2799_2391 : (Triangular src2799) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2799_2393 : (Triangular src2799) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2799_2399 : (Triangular src2799) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2799_2415 : (Triangular src2799) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2799_2459 : (Triangular src2799) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2799 : Cover (Triangular src2799) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2799_2390, by decide, by decide, pass2799_2391, by decide, by decide, pass2799_2393, by decide, by decide, pass2799_2399, by decide, by decide, pass2799_2415, by decide, by decide, pass2799_2459, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1745

-- Source: Research6969.PrefixMainDataMiddle75
section Z6969Source1746
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle75
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 10, 15, 14, 18, 19, 23, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank43 1688, bank50 1914, bank53 2196, bank58 2054, bank65 2772, bank82 2422, bank76 3214, bank106 2882, bank138 3222, bank161 5142, bank126 11206, bank199 7608, bank214 8650, bank183 20877, bank174 26788, bank169 29097] i
  head := src2784
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![15971, 121028, 557180, 1849491],
    ![25417/2, 338565/4, 397488, 1399489],
    ![54680/9, 368750/9, 397488, 4810925/4],
    ![29433/8, 398425/16, 1804598/9, 579540],
    ![64334/25, 17123, 158046, 2223081/4],
    ![73988/49, 487570/49, 823744/9, 2849344/9],
    ![81680/81, 60920/9, 618307/9, 915849/4],
    ![86808/121, 611080/121, 2750372/49, 4822416/25],
    ![86808/121, 609230/121, 2744768/49, 4218916/25],
    ![86808/121, 609230/121, 2744768/49, 4218916/25],
    ![86808/121, 609230/121, 2744768/49, 4218916/25],
    ![230520/361, 1724310/361, 2423356/49, 5970005/36],
    ![230520/361, 177489/40, 7993918/169, 2076481/16],
    ![230520/361, 177489/40, 7993918/169, 2076481/16],
    ![961376/1681, 6126780/1681, 2697836/75, 25470040/243],
    ![1355575/3362, 6126780/1681, 2697836/75, 25470040/243],
    ![1355575/3362, 497930/147, 17331024/529, 4710620/49],
    ![1355575/3362, 4497745/1369, 7594700/243, 32134750/343],
    ![954471/2738, 4497745/1369, 7594700/243, 32134750/343],
    ![462882/1369, 4497745/1369, 7594700/243, 32134750/343],
    ![459151/1369, 4497745/1369, 7594700/243, 32134750/343]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 51 257073 := by
  refine ⟨?_, rank154 3715, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2784⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free43_1
    · exact free50_1
    · exact free53_1
    · exact free58_1
    · exact free65_1
    · exact free82_1
    · exact free76_1
    · exact free106_1
    · exact free138_1
    · exact free161_1
    · exact free126_1
    · exact free199_1
    · exact free214_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [226911721, 288500443, 287625786, 287872981, 288089042, 287925285, 287671284, 288416897, 160293904, 160264392, 160331186, 160367572, 68797757, 79917065, 53836043, 77797652, 90234597, 90452611, 113805989, 100000000, 216950381], [1639805, 1250510, 1254990, 1253724, 1252617, 1253456, 1254757, 1250938, 2398331, 2398823, 2397711, 2397105, 5839829, 4997042, 7518389, 5143574, 4408285, 4397279, 3449641, 3958949, 1721794],
  ![115161601242420, 1626427742284, 195255342900, 5246445480], 119257290163211112⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4497745/1369, 7594700/243, 32134750/343] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle75
end Z6969Source1746

-- Source: Research6969.PrefixRescueDataMiddle75
section Z6969Source1747
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle75
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,56⟩
  bank i := ![bank101 2189, bank134 2544, bank133 2757, bank134 2805, bank142 3112, bank142 3406, bank156 3893, bank194 4846, bank219 7278, bank248 15535, bank336 42285] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 13, 25, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 51

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 2189
    · exact rank134 2544
    · exact rank133 2757
    · exact rank134 2805
    · exact rank142 3112
    · exact rank142 3406
    · exact rank156 3893
    · exact rank194 4846
    · exact rank219 7278
    · exact rank248 15535
    · exact rank336 42285
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2306⟩
    · exact ⟨_, cover2307⟩
    · exact ⟨_, cover2308⟩
    · exact ⟨_, cover2309⟩
    · exact ⟨_, cover2310⟩
    · exact ⟨_, cover2311⟩
    · exact ⟨_, cover2312⟩
    · exact ⟨_, cover2313⟩
    · exact ⟨_, cover2314⟩
    · exact ⟨_, cover2315⟩
    · exact ⟨_, cover2316⟩

def price : EarlyPrice := ⟨2, 56, 10, 60/100, 50/100, ![922831349655, 151745103489, 38192145250, 682015250], 583589530189279⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9698/191, 140285/191, 529658/191, 2367960/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle75
end Z6969Source1747
