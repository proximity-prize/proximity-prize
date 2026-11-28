import ProximityPrize.SubmissionLower.Z6970H2307CountCore
import ProximityPrize.SubmissionLower.Z6969Pack0851
import ProximityPrize.SubmissionLower.Z6970H2307Allocator
import ProximityPrize.SubmissionLower.Z6970H2307FatGeometry

namespace Height2307Allocation
open K1_13 (Row Shape shape)
open Low6969Prices (ActiveFits Messages ProperCut)
open Height2307Bands (start budget)
open scoped BigOperators

theorem index_le (P : Row 4) : K1_13.indexDegree P ≤ 2 * P.totalDegree + P.degreeOf 3 := by
  unfold K1_13.indexDegree
  apply Finset.sup_le
  intro m hm
  have h1 : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
  have h2 : m 3 ≤ P.degreeOf 3 := MvPolynomial.monomial_le_degreeOf 3 hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
  rw [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at h1 ⊢
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  omega

theorem allocation_of_tables {order : Order} {book : Height2307Bands.Band → Shape → Option ℕ}
    {G : Shape → ℕ} {Gated : ℕ → Shape → Prop}
    (excluded : Exclusions) (orders : OrderValid order) (companions : Companion order book)
    (table : PointTable order book G Gated)
    (hceil : Height2307Inventory.layerWidth*(Height2307Inventory.layerNeed-1) <
      ExpandedOrderH2307.sourceRank) :
    Height2307Count6970.Allocation budget 179 G Gated := by
  intro w Γ s hm top htop E d lowCost hlow
  let f := d.f
  let l := d.orders
  let parts := d.pieces
  have hz : d.zeros = Finset.univ.filter (fun i => l i = 0) := by
    ext i
    simp [d.zero_iff,l]
  have hr : Low6969RetainedCut.sumShape d.zeros (fun i=>shape (f i)) =
      P3_6_8.shapeSum (fun i=>shape (f i)) (Finset.univ.filter (fun i=>l i=0)) := by
    rw [hz]
    rfl
  have active (i : Fin d.n) : ActiveFits (f i) 179 := (Final50GeoCover.activeFits_iff _ _).mpr
    ((Finset.single_le_sum (fun j _=>Nat.zero_le (Final50GeoCover.activeDegree (f j)))
      (Finset.mem_univ i)).trans d.active_budget)
  apply total excluded orders companions table top htop d.n (fun i=>shape (f i)) l
    (fun i=>(parts i).card) lowCost hlow d.fits (fun i=>index_le (f i)) d.layers
  · intro i m hp hl k hk
    have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt (hp.trans_le hl)) ((d.zero_iff i).mp h)
    exact d.contracted i hn m hp hl 179 (active i) _ (hr.symm ▸ Height2307Bands.admits_floor hk)
  · intro i m u hp hl hu
    obtain ⟨Q,hproper,hbox,hw,ha,hcut⟩ := d.proper i (hp.trans_le hl)
    have cut : ProperCut (f i) (parts i) s m :=
      ⟨Q,hproper,hbox,hw,ha,fun γ hγ e he => hl.trans (hcut γ (d.subset i hγ) e he)⟩
    have selector : Low6969SharedChooseCut.Selector :=
      fun hm surfaces h => Low6969SharedShapeRank.exists_polynomial hm hceil surfaces h
    exact Low6969SharedCount.proof_of_selector selector w (parts i) s (hm.mono (d.subset i))
      (f i) (d.small i) 179 (active i) (d.on_factor i) m hp cut u hu
  · intro i m hp hl k hg
    have hn : i∉d.zeros := fun h=>(Nat.ne_of_gt (hp.trans_le hl)) ((d.zero_iff i).mp h)
    exact d.gated i hn m hp hl 179 (active i) k.val hg
  · intro i eligible
    exact Low6969FatCount.proof w (parts i) s (hm.mono (d.subset i)) (f i) (d.small i)
      (d.on_factor i) eligible E (d.fat i)

end Height2307Allocation
