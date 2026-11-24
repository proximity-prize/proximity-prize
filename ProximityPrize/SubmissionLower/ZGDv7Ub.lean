import ProximityPrize.SubmissionLower.ZgoWlLc
set_option Elab.async false
open _root_ renaming CommRing → za6, Polynomial.ext → zXJ, Polynomial.map_injective → zTo, PowerSeries.constantCoeff → zbO
set_option backward.isDefEq.respectTransparency false
namespace qU1uHGd
noncomputable section
open Polynomial
open cu (L)
open qb0hmCe (cLN)
open q1kuFjb (coeff_liftAt expansion_coeff mapTwice)
open qFD8jve (polarResultant)
open q2TwyLa (i5 integral lift diff diff_coeff)
open qziIa4d (SeedSeries seedDerivative siteGuard)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open scoped WithZero
abbrev incl:i5 →+* SeedSeries :=HahnSeries.ofPowerSeries ℤ L
theorem coeff_mapTwice {R S:Type} [za6 R] [za6 S] (c:R →+* S)
  (F:R[X][X]) (i j:ℕ) : ((mapTwice c F).coeff i).coeff j=c ((F.coeff i).coeff j) :=
 by simp only [mapTwice,coe_mapRingHom,coeff_map]
theorem degree_mapTwice {R S:Type} [za6 R] [za6 S] {c:R →+* S}
  (hc:Function.Injective c) (F:R[X][X]) : (mapTwice c F).natDegree=F.natDegree :=
 natDegree_map_eq_of_injective (zTo c hc) _
theorem seedDerivative_coeff (F:SeedSeries[X][X]) (i j:ℕ) :
  ((seedDerivative F).coeff i).coeff j=LaurentSeries.derivative L ((F.coeff i).coeff j) := by
 unfold seedDerivative
 rw [sum_coeff _ (by simp [Polynomial.sum_def])]
 exact sum_coeff _ (map_zero _) _ _
private theorem cXH {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] SeedSeries)
  (G:E[X][X]) (h:integral a G) (i j:ℕ) :
  incl (((lift a G h).coeff i).coeff j)=a ((G.coeff i).coeff j) := by
 rw [lift,coeff_map,coe_mapRingHom,coeff_map]
 let s :=((q1kuFjb.Ua a G h).coeff i).coeff j
 change incl ((LaurentSeries.powerSeriesEquivSubring L).symm s)= _
 rw [← LaurentSeries.powerSeriesEquivSubring_coe_apply,
  RingEquiv.apply_symm_apply]
 exact coeff_liftAt a G h i j
private theorem diff_incl (s :i5) :
   incl (PowerSeries.derivative s)=LaurentSeries.derivative L (incl s) := by
 ext n
 simp only [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,Ring.choose_one_right]
 by_cases hn:0≤n
 · obtain ⟨k,rfl⟩:=Int.eq_ofNat_of_zero_le hn
   change ((PowerSeries.derivative s :i5) :LaurentSeries L).coeff (k :ℤ) =
     ((k+1 :ℕ) :ℤ)•((s :LaurentSeries L).coeff ((k+1 :ℕ) :ℤ))
   rw [LaurentSeries.coeff_coe_powerSeries,LaurentSeries.coeff_coe_powerSeries,
     PowerSeries.coeff_derivative,natCast_zsmul,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_comm]
 · change ((PowerSeries.derivative s :i5) :LaurentSeries L).coeff n =
     (n+1)•((s :LaurentSeries L).coeff (n+1))
   rw [PowerSeries.coeff_coe,ite_eq_left (lt_of_not_ge hn)]
   by_cases h:n+1=0
   · simp [h]
   · rw [PowerSeries.coeff_coe,ite_eq_left (by omega :n+1<0),smul_zero]
theorem lift_embed {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] SeedSeries)
  (G:E[X][X]) (h:integral a G) :mapTwice incl (lift a G h)=mapTwice a.toRingHom G:= by
 apply zXJ
 intro i
 apply zXJ
 intro j
 rw [coeff_mapTwice,coeff_mapTwice]
 exact cXH a G h i j
theorem lift_jet {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] SeedSeries)
   (G:E[X][X]) (h:integral a G) :
   mapTwice zbO (lift a G h)=cLN a 0 G ∧
     mapTwice zbO (diff (lift a G h))=cLN a 1 G:= by
 constructor
 · apply zXJ
   intro i
   apply zXJ
   intro j
   rw [coeff_mapTwice,expansion_coeff,← cXH a G h i j]
   exact (q1kuFjb.power_residue _ _ rfl).symm
 · apply zXJ
   intro i
   apply zXJ
   intro j
   rw [coeff_mapTwice,expansion_coeff,diff_coeff,← cXH a G h i j]
   change zbO (PowerSeries.derivative _)=((↑(_) :LaurentSeries L).coeff 1)
   rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_derivative]
   simpa only [Nat.cast_zero,Nat.cast_one,zero_add,mul_one,incl] using
     (LaurentSeries.coeff_coe_powerSeries ((lift a G h).coeff i |>.coeff j) 1).symm
theorem diff_embed (F:i5[X][X]) :
  mapTwice incl (diff F)=seedDerivative (mapTwice incl F) := by
 apply zXJ
 intro i
 apply zXJ
 intro j
 rw [coeff_mapTwice,diff_coeff,seedDerivative_coeff,coeff_mapTwice]
 exact diff_incl _
private theorem residue_nonzero {s :i5}
  (h: (Valued.v :Valuation SeedSeries ℤᵐ⁰) (incl s)=1) :
  zbO s≠0:= by
 intro hz
 have hh:=(q1kuFjb.small_valuation s).mpr hz
 rw [show (s :SeedSeries)=incl s from rfl,h] at hh
 exact (not_le_of_gt (show WithZero.exp (-1 :ℤ)<1 by
  exact WithZero.exp_lt_one_iff.mpr (by omega))) hh
theorem guard_residue {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] SeedSeries)
    (G:E[X][X]) (h:integral a G) (hd:0<G.natDegree)
    (hLead:G.leadingCoeff.coeff 0≠0) (hg: (Valued.v :Valuation SeedSeries ℤᵐ⁰) (a (siteGuard G))=1) :
    let F:=lift a G h
    let R:=qW F (diff F) G.natDegree
    let n:=(polarResultant G).natTrailingDegree
    zbO ((R.coeff 0).coeff n)≠0:= by
  dsimp only
  let F:=lift a G h
  let e :=mapRingHom incl
  let g:=mapRingHom a.toRingHom
  have ha :=degree_mapTwice a.injective G
  have hp: (mapTwice a.toRingHom G).resultant (mapTwice a.toRingHom G).derivative
      G.natDegree (G.natDegree-1)=g (polarResultant G) := by
    change (G.map g).resultant (G.map g).derivative G.natDegree (G.natDegree-1)= _
    rw [polarResultant,← resultant_map_map _ _ _ _ g,derivative_map]
  have he :e ((qW F (diff F) G.natDegree).coeff 0) =
      g (G.leadingCoeff*polarResultant G) := by
    rw [← coeff_map,mapped,show F.map e=mapTwice a.toRingHom G from lift_embed a G h,
      constant_pencil _ _ _ hd ha,hp,map_mul,
      show (mapTwice a.toRingHom G).leadingCoeff=g G.leadingCoeff from
        leadingCoeff_map_of_injective (zTo _ a.injective) G]
  apply residue_nonzero
  have hw:=coeff_mul_natTrailingDegree_add_natTrailingDegree (p:=G.leadingCoeff) (q:=polarResultant G)
  rw [natTrailingDegree_eq_zero.mpr (Or.inr hLead),Nat.zero_add,
    trailingCoeff_eq_coeff_zero hLead,mul_comm (G.leadingCoeff.coeff 0),← siteGuard] at hw
  change (Valued.v :Valuation SeedSeries ℤᵐ⁰)
    (incl (((qW F (diff F) G.natDegree).coeff 0).coeff (polarResultant G).natTrailingDegree))=1
  change ((qW F (diff F) G.natDegree).coeff 0).map incl =
    (G.leadingCoeff*polarResultant G).map a.toRingHom at he
  rw [← coeff_map,he,coeff_map,hw]
  exact hg
end
end qU1uHGd
