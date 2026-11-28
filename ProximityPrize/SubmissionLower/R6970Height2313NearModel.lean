import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryBooks
import ProximityPrize.SubmissionLower.R6970Height2311NormalPacket
import ProximityPrize.SubmissionLower.R6970Height2313Outer
import ProximityPrize.SubmissionLower.Z6970H2313OrdinaryChoose
import ProximityPrize.SubmissionLower.Z6970NativeNearLightPacket

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0830
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open _root_.Lower6960.Prefix6969Rescue (graphShape)
open _root_.Lower6960.Prefix6969Early (Packet threshold seed)
open Research6969 Research6966
open _root_.Research6969.TransitionPacket (Pair)
open Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade savedRescueGrade)

abbrev NormalSeed := Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue.seed
abbrev NormalFloor := Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue.floor

inductive Outcome {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) : Type where
  | ordinary : Packet F Crt _root_.Research6970.Height2313.OrdinaryBooks.near.fee
      _root_.Research6970.Height2313.OrdinaryBooks.near.ordinateCredit _root_.Research6970.Height2313.OrdinaryBooks.near.seedCredit 351 _root_.Research6970.Height2313.OrdinaryBooks.near.seedMass → Outcome F Crt
  | quadratic19 : Packet F Crt _root_.Research6970.Height2313.OrdinaryBooks.nearQuadratic19.fee
      _root_.Research6970.Height2313.OrdinaryBooks.nearQuadratic19.ordinateCredit _root_.Research6970.Height2313.OrdinaryBooks.nearQuadratic19.seedCredit 337 _root_.Research6970.Height2313.OrdinaryBooks.nearQuadratic19.seedMass → Outcome F Crt
  | cubicWide : Packet F Crt _root_.Research6970.Height2313.OrdinaryBooks.nearCubic41.fee
      _root_.Research6970.Height2313.OrdinaryBooks.nearCubic41.ordinateCredit _root_.Research6970.Height2313.OrdinaryBooks.nearCubic41.seedCredit 337 _root_.Research6970.Height2313.OrdinaryBooks.nearCubic41.seedMass → Outcome F Crt
  | quinticMid : Packet F Crt _root_.Research6970.Height2313.OrdinaryBooks.nearQuintic26.fee
      _root_.Research6970.Height2313.OrdinaryBooks.nearQuintic26.ordinateCredit _root_.Research6970.Height2313.OrdinaryBooks.nearQuintic26.seedCredit 337 _root_.Research6970.Height2313.OrdinaryBooks.nearQuintic26.seedMass → Outcome F Crt
  | normal (i : Fin 18) (G : Jet) (prime : Prime G) (slope : G.natDegree=1)
      (degree : 2≤jetDegree G) (caps : RowCaps G (graphShape 2 (NormalSeed i)))
      (seedExact : seedDegree G=NormalSeed i)
      (packet : Pair F Crt G (mainBook i) (rescueBook i))
      (mainGrade : packet.mainGrade=savedMainGrade i) (rescueGrade : packet.rescueGrade=savedRescueGrade i) : Outcome F Crt

private def into56 (i : Fin 18) : Fin 56 := ⟨i.val,i.isLt.trans (by decide)⟩
private theorem floor_dom (i : Fin 18) : NormalFloor i≤threshold (into56 i) := by
  fin_cases i <;> decide +kernel

/-- The outer helper's actual degree, seed interval, and physical weight
choose between the native light/ordinary, early, and normal packets. -/
theorem route_using
    (choose : ∀ (a : Fin 6) (j : Fin 56), UniformAllowed (a.val+2) (seed j) →
      ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧
        w≤(if a.val=0 then threshold j else (a.val+2)*128758-1) ∧
        ∃ c : NearCase (a.val+2) l u w, c.uniform)
    {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Outcome F Crt) := by
  obtain ⟨R, unit | ⟨phys, common, slope, jd, jmax, sd, smax, jbound, floor⟩⟩ :=
    Research6970.Height2313.Lower6960.Prefix6969NearOuter.split F Crt (by omega) hi noPole residues
  · obtain ⟨raw⟩:=Research6970.Height2313.Lower6960.Prefix6969NearOuter.ordinary R (hi.trans (by decide)) noPole residues (Or.inl unit)
    obtain ⟨P⟩ := raw.reprice (fee' := _root_.Research6970.Height2313.OrdinaryBooks.near.fee)
      (ord' := _root_.Research6970.Height2313.OrdinaryBooks.near.ordinateCredit) (seed' := _root_.Research6970.Height2313.OrdinaryBooks.near.seedCredit)
      (e' := 351) (v' := 6143) (by decide) (by decide) (by decide)
    exact ⟨.ordinary P⟩
  let G := R.out.exception
  have prime : Prime G := Prefix6969MiddleTransfer.prime_of_irred common.1
  by_cases affine : jetDegree G=1
  · obtain ⟨raw⟩:=Research6970.Height2313.Lower6960.Prefix6969NearOuter.ordinary R (hi.trans (by decide)) noPole residues (Or.inr ⟨prime,slope,affine,smax⟩)
    obtain ⟨P⟩ := raw.reprice (fee' := _root_.Research6970.Height2313.OrdinaryBooks.near.fee)
      (ord' := _root_.Research6970.Height2313.OrdinaryBooks.near.ordinateCredit) (seed' := _root_.Research6970.Height2313.OrdinaryBooks.near.seedCredit)
      (e' := 351) (v' := 6143) (by decide) (by decide) (by decide)
    exact ⟨.ordinary P⟩
  change 1≤jetDegree G at jd
  change jetDegree G≤7 at jmax
  change 1≤seedDegree G at sd
  have nonlin : 2≤jetDegree G := by omega
  have sm : seedDegree G≤56 := jbound nonlin
  let a : Fin 6 := ⟨jetDegree G-2,by omega⟩
  let j : Fin 56 := ⟨seedDegree G-1,by omega⟩
  have ae : a.val+2=jetDegree G := by dsimp [a]; omega
  have se : seed j=seedDegree G := by dsimp [seed,j]; omega
  let W := RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw
  have high : jetDegree G=2 → threshold j≤W → Nonempty (Outcome F Crt) := by
    intro quad enough
    by_cases sm18 : seedDegree G≤18
    · let i : Fin 18 := ⟨seedDegree G-1,by omega⟩
      have ise : NormalSeed i=seedDegree G := by dsimp [NormalSeed,i]; omega
      have ie : into56 i=j := Fin.ext rfl
      have physical := (floor_dom i).trans (ie.symm ▸ enough)
      have shape : RowCaps G (graphShape 2 (NormalSeed i)) := by
        intro s k hn
        have h : G.coeff s≠0 := fun eq=>hn (by simp [eq])
        exact ⟨(K1_14_2_2_2_1.jetDegree_le G 2).mp quad.le s k hn,
          (le_natDegree_of_ne_zero h).trans slope.le,
          (K1_14_2_2_2_1.seedDegree_le G _).mp ise.ge s k⟩
      obtain ⟨P,mr,rr⟩ := Research6970.Height2313.Research6969.TransitionPacket.NormalCatalogue.packet_with_grades
        F Crt i lo hi noPole residues phys prime slope common.2.2.1 shape common
        quad.ge ise.le physical
      exact ⟨.normal i G prime slope quad.ge shape ise.symm P mr rr⟩
    by_cases seed19 : seedDegree G=19
    · have j19 : j=(18:Fin 56) := by apply Fin.ext; dsimp [j]; omega
      have physical : 307353≤W := by rw [j19] at enough; exact enough
      obtain ⟨P⟩ := NearSavedQuadraticSingletons0.data.run F Crt lo hi noPole residues
        phys common slope quad (by decide) seed19.ge seed19.le physical
      rw [NearSavedQuadraticSingletons0.fee_exact] at P
      exact ⟨.quadratic19 P⟩
    have allowed : UniformAllowed (a.val+2) (seed j) := by
      rw [ae,se,quad]
      unfold UniformAllowed
      omega
    obtain ⟨l,h,w,lower,upper,physfit,c,pay⟩ := choose a j allowed
    have first : a.val=0 := by omega
    have physical : w≤W := (by simpa only [if_pos first] using physfit : w≤threshold j).trans enough
    obtain ⟨P⟩ := c.run F Crt lo hi noPole residues phys common slope ae.symm
      (by omega) (se ▸ lower) (se ▸ upper) physical
    obtain ⟨Q⟩ := P.reprice pay.1 pay.2.1 pay.2.2
    exact ⟨.ordinary Q⟩
  by_cases quad : jetDegree G=2
  · by_cases low : W<threshold j
    · have stockCommon : PrefixRows.Common
          (evaluated Crt (word M) _root_.Lower6960.Prefix6969Helper.helperBank.shape
            (_root_.Lower6960.Prefix6969Helper.helperCutoff M.overhead.toNat)) G := by
        exact ⟨common.1, common.2.1, common.2.2.1, fun Q inside => common.2.2.2 Q
          (K1_14_1.evaluated_mono Crt (word M)
            (s := _root_.Lower6960.Prefix6969Helper.helperBank.shape)
            (s' := Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank.shape)
            rfl rfl rfl
            (by decide : 10007 ≤ 10281) le_rfl inside)⟩
      obtain ⟨raw⟩ := _root_.Lower6960.Prefix6969Early.native_light_packet_2308 F Crt (by omega) (hi.trans (by decide)) noPole residues phys stockCommon slope quad j sd se.ge low
      obtain ⟨P⟩ := raw.reprice (fee' := _root_.Research6970.Height2313.OrdinaryBooks.near.fee)
        (ord' := _root_.Research6970.Height2313.OrdinaryBooks.near.ordinateCredit) (seed' := _root_.Research6970.Height2313.OrdinaryBooks.near.seedCredit)
        (e' := 351) (v' := 6143) (by decide) (by decide) (by decide)
      exact ⟨.ordinary P⟩
    · exact high quad (Nat.le_of_not_gt low)
  by_cases cubic : jetDegree G=3 ∧ 41≤seedDegree G
  · have fw : 385979≤W := by have t:=floor; change jetDegree G*128758-1≤W at t; rw [cubic.1] at t; omega
    obtain ⟨P⟩ := NearSavedRepricedHelperCases0.data.run F Crt lo hi noPole residues phys common slope
      cubic.1 (by decide) cubic.2 sm fw
    rw [NearSavedRepricedHelperCases0.fee_exact] at P
    exact ⟨.cubicWide P⟩
  by_cases quintic : jetDegree G=5 ∧ 26≤seedDegree G ∧ seedDegree G≤40
  · have fw : 643299≤W := by have t:=floor; change jetDegree G*128758-1≤W at t; rw [quintic.1] at t; omega
    obtain ⟨P⟩ := NearSavedRepricedHelperCases1.data.run F Crt lo hi noPole residues phys common slope
      quintic.1 (by decide) quintic.2.1 quintic.2.2 fw
    rw [NearSavedRepricedHelperCases1.fee_exact] at P
    exact ⟨.quinticMid P⟩
  have allowed : UniformAllowed (a.val+2) (seed j) := by
    rw [ae,se]
    unfold UniformAllowed
    omega
  obtain ⟨l,h,w,lower,upper,physfit,c,pay⟩ := choose a j allowed
  have nz : a.val≠0 := by omega
  have physical : w≤W := by
    simp only [if_neg nz,ae] at physfit
    exact physfit.trans floor
  obtain ⟨P⟩ := c.run F Crt lo hi noPole residues phys common slope ae.symm
    (by omega) (se ▸ lower) (se ▸ upper) physical
  obtain ⟨Q⟩ := P.reprice pay.1 pay.2.1 pay.2.2
  exact ⟨.ordinary Q⟩

end
end Lower6960.Prefix6969Early
end Z6969Source0830


end Research6970.Height2313
