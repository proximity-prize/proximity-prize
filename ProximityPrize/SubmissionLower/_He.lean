import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A
section ProximityFlatProofPort
variable {α β:Type*} {rα:α → α → Prop} {rβ:β → β → Prop} {a:α} {b:β}
namespace Prod
variable (rα rβ)
inductive GameAdd:α × β → α × β → Prop
 | fst {a₁ a₂ b}:rα a₁ a₂ → GameAdd (a₁,b) (a₂,b)
 | snd {a b₁ b₂}:rβ b₁ b₂ → GameAdd (a,b₁) (a,b₂)
theorem gameAdd_iff {rα rβ} {x y:α × β}:
   GameAdd rα rβ x y ↔ rα x.1 y.1∧x.2=y.2∨rβ x.2 y.2∧x.1=y.1:=by
 constructor
 · rintro (@⟨a₁,a₂,b,h⟩ | @⟨a,b₁,b₂,h⟩)
   exacts [Or.inl ⟨h,rfl⟩,Or.inr ⟨h,rfl⟩]
 · revert x y
   rintro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ (⟨h,rfl:b₁=b₂⟩ | ⟨h,rfl:a₁=a₂⟩)
   exacts [GameAdd.fst h,GameAdd.snd h]
theorem gameAdd_mk_iff {rα rβ} {a₁ a₂:α} {b₁ b₂:β}:
   GameAdd rα rβ (a₁,b₁) (a₂,b₂) ↔ rα a₁ a₂∧b₁=b₂∨rβ b₁ b₂∧a₁=a₂:=
 gameAdd_iff
@[simp]
theorem gameAdd_swap_swap:∀ a b:α × β,GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b:=
 fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ => by rw [Prod.swap,Prod.swap,gameAdd_mk_iff,gameAdd_mk_iff,or_comm]
theorem gameAdd_swap_swap_mk (a₁ a₂:α) (b₁ b₂:β):
   GameAdd rα rβ (a₁,b₁) (a₂,b₂) ↔ GameAdd rβ rα (b₁,a₁) (b₂,a₂):=
 gameAdd_swap_swap rβ rα (b₁,a₁) (b₂,a₂)
theorem gameAdd_le_lex:GameAdd rα rβ ≤ Prod.Lex rα rβ:=fun _ _ h =>
 h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)
theorem rprod_le_transGen_gameAdd:RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ)
 | _,_,h => h.rec (by
     intro _ _ _ _ hα hβ
     exact Relation.TransGen.tail (Relation.TransGen.single <| GameAdd.fst hα) (GameAdd.snd hβ))
end Prod
theorem Acc.prod_gameAdd (ha:Acc rα a) (hb:Acc rβ b):
   Acc (Prod.GameAdd rα rβ) (a,b):=by
 induction ha generalizing b with | _ a _ iha
 induction hb with | _ b hb ihb
 refine Acc.intro _ fun h => ?_
 rintro (⟨ra⟩ | ⟨rb⟩)
 exacts [iha _ ra (Acc.intro b hb),ihb _ rb]
theorem WellFounded.prod_gameAdd (hα:WellFounded rα) (hβ:WellFounded rβ):
   WellFounded (Prod.GameAdd rα rβ):=
 ⟨fun ⟨a,b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩
namespace Prod
@[elab_as_elim]
def GameAdd.recursion {C:α → β → Sort*} (hα:WellFounded rα) (hβ:WellFounded rβ)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a:α) (b:β):
   C a b:=
 @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
   (fun ⟨x₁,x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a',b'⟩) ⟨a,b⟩
@[deprecated (since:="2026-03-13")] alias GameAdd.fix:=GameAdd.recursion
theorem GameAdd.recursion_eq {C:α → β → Sort*} (hα:WellFounded rα) (hβ:WellFounded rβ)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a:α) (b:β):
   GameAdd.recursion hα hβ IH a b=IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b':=
 WellFounded.fix_eq _ _ _
@[deprecated (since:="2026-03-13")] alias GameAdd.fix_eq:=GameAdd.recursion_eq
@[deprecated GameAdd.recursion (since:="2026-03-13")]
theorem GameAdd.induction {C:α → β → Prop}:
   WellFounded rα →
     WellFounded rβ →
       (∀ a₁ b₁,(∀ a₂ b₂,GameAdd rα rβ (a₂,b₂) (a₁,b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b,C a b:=
 GameAdd.recursion
end Prod
namespace Sym2
def GameAdd (rα:α → α → Prop):Sym2 α → Sym2 α → Prop:=
 Sym2.lift₂
   ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)∨Prod.GameAdd rα rα (b₁,a₁) (a₂,b₂),
     fun a₁ b₁ a₂ b₂ => by
       dsimp
       rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂,Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
       simp [or_comm]⟩
theorem gameAdd_iff:∀ {x y:α × α},
   GameAdd rα s(x.1,x.2) s(y.1,y.2) ↔ Prod.GameAdd rα rα x y∨Prod.GameAdd rα rα x.swap y:=by
 rintro ⟨_,_⟩ ⟨_,_⟩
 rfl
theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂:α}:
   GameAdd rα s(a₁,b₁) s(a₂,b₂) ↔
     Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)∨Prod.GameAdd rα rα (b₁,a₁) (a₂,b₂):=
 Iff.rfl
theorem _root_.Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂:α} (h:Prod.GameAdd rα rα (a₁,b₁) (a₂,b₂)):
   Sym2.GameAdd rα s(a₁,b₁) s(a₂,b₂):=
 gameAdd_iff.2 <| Or.inl <| h
theorem GameAdd.fst {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(a₁,b) s(a₂,b):=
 (Prod.GameAdd.fst h).to_sym2
theorem GameAdd.snd {a b₁ b₂:α} (h:rα b₁ b₂):GameAdd rα s(a,b₁) s(a,b₂):=
 (Prod.GameAdd.snd h).to_sym2
theorem GameAdd.fst_snd {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(a₁,b) s(b,a₂):=by
 rw [Sym2.eq_swap]
 exact GameAdd.snd h
theorem GameAdd.snd_fst {a₁ a₂ b:α} (h:rα a₁ a₂):GameAdd rα s(b,a₁) s(a₂,b):=by
 rw [Sym2.eq_swap]
 exact GameAdd.fst h
end Sym2
theorem Acc.sym2_gameAdd {a b} (ha:Acc rα a) (hb:Acc rα b):
   Acc (Sym2.GameAdd rα) s(a,b):=by
 induction ha generalizing b with | _ a _ iha
 induction hb with | _ b hb ihb
 refine Acc.intro _ fun s => ?_
 induction s with | _ c d
 rw [Sym2.GameAdd]
 dsimp
 rintro ((rc | rd) | (rd | rc))
 · exact iha c rc ⟨b,hb⟩
 · exact ihb d rd
 · rw [Sym2.eq_swap]
   exact iha d rd ⟨b,hb⟩
 · rw [Sym2.eq_swap]
   exact ihb c rc
theorem WellFounded.sym2_gameAdd (h:WellFounded rα):WellFounded (Sym2.GameAdd rα):=
 ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩
namespace Sym2
attribute [local instance] Sym2.Rel.setoid
@[elab_as_elim]
def GameAdd.recursion {C:α → α → Sort*} (hr:WellFounded rα)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a b:α):
   C a b:=
 @WellFounded.fix (α × α) (fun x => C x.1 x.2)
   (fun x y↦Prod.GameAdd rα rα x y∨Prod.GameAdd rα rα x.swap y)
   (by simpa [←Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
   (fun ⟨x₁,x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a',b'⟩) (a,b)
@[deprecated (since:="2026-03-13")] alias GameAdd.fix:=GameAdd.recursion
theorem GameAdd.recursion_eq {C:α → α → Sort*} (hr:WellFounded rα)
   (IH:∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) (a b:α):
   GameAdd.recursion hr IH a b=IH a b fun a' b' _ => GameAdd.recursion hr IH a' b':=
 WellFounded.fix_eq ..
@[deprecated (since:="2026-03-13")] alias GameAdd.fix_eq:=GameAdd.recursion_eq
@[deprecated GameAdd.recursion (since:="2026-03-13")]
theorem GameAdd.induction {C:α → α → Prop}:
   WellFounded rα →
     (∀ a₁ b₁,(∀ a₂ b₂,Sym2.GameAdd rα s(a₂,b₂) s(a₁,b₁) → C a₂ b₂) → C a₁ b₁) →
       ∀ a b,C a b:=
 GameAdd.recursion
end Sym2
