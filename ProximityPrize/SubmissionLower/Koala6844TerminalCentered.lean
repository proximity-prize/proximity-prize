import ProximityPrize.SubmissionLower.Koala6844TerminalFamily
import ProximityPrize.SubmissionLower.Koala6844VirtualShortCarrierReceipts


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical
open RCN081 RCN140 RCN156 RCN238 RCN266
open LocatorBatchProductRoute Koala6844Receipts Koala6844Normalization
open Koala6844VirtualShort

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K] [CharP K 2130706433] [DecidableEq K] [DecidableEq I] [Fintype I]
variable {x : I ↪ K} {domain : Finset I} {σ : K ≃+* K} {excess : Nat}

private theorem filter_subset_across_decisions {J : Type} {p : J → Prop} {a b : Finset J}
    (d₁ d₂ : DecidablePred p) (h : a ⊆ b) : @Finset.filter J p d₁ a ⊆ @Finset.filter J p d₂ b := by
  intro i hi
  obtain ⟨ha,hp⟩ := (@Finset.mem_filter J p d₁ a i).mp hi
  exact (@Finset.mem_filter J p d₂ b i).mpr ⟨h ha,hp⟩

omit [CharP K 2130706433] [Fintype I] in
theorem centered_terminalSeedData
    (data : CenteredVirtualData x domain σ 131071 180960 81184 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144) :
    TerminalSeedData full x (data.received 0) (data.received 1) data.selected data.seeds := by
  refine ⟨x.injective.injOn,hcount,data.selected_degree,?_,?_⟩
  · intro g hg
    exact (data.agreements g hg).trans (Finset.card_le_card (filter_subset_across_decisions _ _ hfull))
  · intro P0 P1 h0 h1
    refine le_trans ?_ (data.pencil P0 P1 h0 h1)
    exact Finset.card_le_card (filter_subset_across_decisions _ _ (fun _ hg => hg))

private theorem ordered_and_small (p : SourceShape) (hvalid : sourceWellFormed p = true) :
    p.carrierFlag.ordered ∧ p.k < 2130706433 := by
  have h := of_decide_eq_true ((Bool.and_eq_true_iff.mp hvalid).1)
  obtain ⟨_,hb,hu,hl,hk,_,_,_,hp,_⟩ := h
  have hord : p.B ≤ p.U ∧ p.U ≤ p.L+p.q := by omega
  exact ⟨hord,hk.trans_lt hp⟩

private theorem shape_total_le (src : Sources) (j : Fin 3) :
    (shapeAt src j).L + (shapeAt src j).q ≤ src.totalCap := by
  fin_cases j
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

private theorem centered_terminal_route
    (data : CenteredVirtualData x domain σ 131071 180960 81184 excess)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (p : SourceShape) (hvalid : sourceWellFormed p = true ∧ sourceMargin p)
    (H : MvPolynomial (Fin 4) K) (F : RegularIndex H)
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (g : Flag) (hr : 1 ≤ g.r) (hy : 1 ≤ g.y) (ht : 1 ≤ g.t)
    (hfit : (physicalFlag F.1).cumulativeLE g)
    (hFT : p.L+p.q < (physicalFlag F.1).t) :
    Route F.1 g p (regularSeeds H data.selected seeds F) data.selected := by
  have hseed : regularSeeds H data.selected seeds F ⊆ regularSeeds H data.selected data.seeds F :=
    filter_subset_across_decisions _ _ hsub
  have hfact (m : Nat) (hm : m < prime) : (m.factorial : K) ≠ 0 :=
    RCN347.factorial_cast_ne_zero_below_characteristic 2130706433 m hm
  obtain hcut | ⟨source,hd,hf,hB,hU,hT,_,_⟩ :=
    terminal_source_for_regular data hSize hPole hLead hfact p hvalid.1 hvalid.2
      H F (regularSeeds H data.selected seeds F) hseed g.r g.y g.t hr hy ht hfit hFT
  · exact Or.inl hcut
  · exact Or.inr ⟨source,hd,hf,hB,hU,hT⟩

private theorem biUnion_cover_across_decisions {A B : Type}
    {s : Finset B} {t : Finset A} {f : A → Finset B}
    (d₁ d₂ : DecidableEq B) (h : s ⊆ @Finset.biUnion A B d₁ t f) :
    s ⊆ @Finset.biUnion A B d₂ t f := by
  have eq : d₁ = d₂ := by
    funext a b
    exact Subsingleton.elim _ _
  cases eq
  exact h

theorem centered_terminal_bound
    (data : CenteredVirtualData x domain σ 131071 180960 81184 excess)
    (full : Finset I) (hfull : domain ⊆ full) (hcount : full.card = 262144)
    (hSize : Fintype.card I ≤ 262144)
    (hPole : data.d0.natDegree + affineDegree data.A0 ≤ poleWidth)
    (hLead : ∀ i ∈ domain, (data.A0 1).eval (x i) ≠ 0)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (remaining : Finset (RegularIndex H)) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1)
    (outer : Flag) (src : Sources) (price : Nat) (hprice : terminalPrice outer src = some price)
    (hfo : outer.ordered) (hyL : outer.y ≤ src.totalCap) (hLt : src.totalCap+outer.y ≤ outer.t)
    (hR : outer.r ≤ 20) (hY : outer.y ≤ 84) (hL : src.totalCap ≤ 3873)
    (hfit : (physicalFlag (regularProduct H remaining)).cumulativeLE outer)
    (hvalid : ∀ j : Fin 3, sourceWellFormed (shapeAt src j) = true ∧ sourceMargin (shapeAt src j))
    (hdiv : ∀ j : Fin 3, 3*(shapeAt src j).k+3 ∣ graphScale)
    (seeds : Finset K) (hsub : seeds ⊆ data.seeds)
    (hcover : seeds ⊆ remaining.biUnion (regularSeeds H data.selected seeds)) :
    seeds.card ≤ price := by
  have hshape (j : Fin 3) := (ordered_and_small (shapeAt src j) (hvalid j).1).1
  have hk (j : Fin 3) := (ordered_and_small (shapeAt src j) (hvalid j).1).2
  have hdata := (centered_terminalSeedData data full hfull hcount).subset hsub
  refine terminal_regular_family H hH remaining D hD hDchar hcontact outer src price hprice hfo hyL hLt
    hR hY hL hfit hshape hdiv hk full x _ _ data.selected seeds hdata (biUnion_cover_across_decisions _ _ hcover) ?_
  intro F _ hlarge scope hFfit _ _ j
  let p := shapeAt src j
  let g := padFlag scope 2
  have hcap := shape_total_le src j
  have hg : (physicalFlag F.1).cumulativeLE g :=
    ⟨hFfit.1.trans (below_pad scope 2).1,hFfit.2.1.trans (below_pad scope 2).2.1,
      hFfit.2.2.trans (below_pad scope 2).2.2⟩
  obtain ⟨hr,hy,ht⟩ := pad_shape scope 2
  have hposr : 1 ≤ g.r := (by decide : 1 ≤ 3).trans hr
  have hposy : 1 ≤ g.y := hposr.trans ((Nat.le_add_right g.r 2).trans hy)
  have hpost : 1 ≤ g.t := hposy.trans ((Nat.le_add_right g.y 2).trans ht)
  exact centered_terminal_route data hSize hPole hLead p (hvalid j) H F seeds hsub g hposr hposy hpost
    hg (hcap.trans_lt hlarge)

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
