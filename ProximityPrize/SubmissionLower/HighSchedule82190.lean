import ProximityPrize.SubmissionLower.HighPrefixGeometry82190

set_option Elab.async false

namespace HighFamily82190_3
open Front82190 (HighBand agreement)
open HighFamily82190 (Stage stages terminal fees fullCutoff)
open K1_14 (Shape)
private def fits (hi r : ℕ) (s : Shape) : Prop :=
  0 < s.m * agreement ∧ 2*hi*r ≤ fullCutoff s
private instance (hi r : ℕ) (s : Shape) : Decidable (fits hi r s) := by
  unfold fits
  infer_instance
private theorem stage_fits (b : HighBand) {s : Stage} (hs : s ∈ stages b) :
    fits (Front82190.row b).hi s.reserve s.free.shape ∧
    fits (Front82190.row b).hi s.reserve s.moving.shape := by
  have cert : (stages b).all (fun t => decide (fits (Front82190.row b).hi t.reserve t.free.shape ∧
      fits (Front82190.row b).hi t.reserve t.moving.shape)) = true := by cases b <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp cert s hs)
private theorem new_stage (b : HighBand) (i : ℕ) (hi : i < (stages b).length) :
    let s := stageAt b i
    BankGuard (Front82190.row b).hi s.reserve s.free.shape ∧
      BankGuard (Front82190.row b).hi s.reserve s.moving.shape := by
  obtain ⟨f,m⟩ := P3_7_3_3.stage_guard b i hi
  obtain ⟨f',m'⟩ := stage_fits b (stage_mem hi)
  exact ⟨⟨f.ode,f.seed_small,f'.1,f'.2⟩,⟨m.ode,m.seed_small,m'.1,m'.2⟩⟩
private theorem new_terminal (b : HighBand) : BankGuard (Front82190.row b).hi 0 (terminal b).shape := by
  have g := P3_7_3_3.terminal_guard b
  have f : fits (Front82190.row b).hi 0 (terminal b).shape := by cases b <;> decide +kernel
  exact ⟨g.ode,g.seed_small,f.1,f.2⟩
theorem schedule : c3 := by
  intro b
  have g := P3_7_3_3.proof b
  have seed : (fees b).lowSeed = (P3_7.fees b).lowSeed := by cases b <;> rfl
  have content : (fees b).content = (P3_7.fees b).content := by cases b <;> rfl
  exact ⟨g.stages_pos,g.zero,g.later_pos,g.small_reserve,g.stop_le,g.intro_pos,
    g.intro_asc,new_stage b,new_terminal b,g.initial_small,g.initial_e_ge,g.content_small,
    g.rank_guard,seed.symm ▸ g.low_seed,(HighPrefix82190.jet_exact b).le,
    (HighPrefix82190.fixed_exact b).le,content.symm ▸ g.content⟩
theorem ledger : c4 := by
  intro b
  have pt : (fees b).point = (P3_7.fees b).point := by cases b <;> rfl
  refine ⟨(P3_7_3_4.proof b).seed_small, pt.symm ▸ HighLoss82190.points b, ?_, ?_⟩
  · intro hb
    obtain ⟨a,h,valid,cost⟩ := HighLoss82190.discounted b hb
    refine ⟨a,h,?_,cost.trans (HighPrefix82190.loss_discount b hb)⟩
    intro i hi
    obtain ⟨g,hm⟩ := valid i hi
    exact ⟨⟨g.degree,g.height,g.interpolation⟩,hm⟩
  · intro hb
    have bound := HighLoss82190.direct b hb
    rw [HighPrefix82190.loss_direct b hb] at bound
    exact bound
end HighFamily82190_3
