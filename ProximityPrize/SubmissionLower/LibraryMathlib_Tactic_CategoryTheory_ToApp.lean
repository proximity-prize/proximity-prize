import ProximityPrize.Benchmark.TargetLower
set_option Elab.async false
/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

open CategoryTheory
namespace Mathlib.Tactic.CategoryTheory.ToApp
universe v u in
lemma toNatTrans_congr {C D : Cat.{v, u}} {F G : C ⟶ D} {η θ : F ⟶ G} (h : η = θ) :
  η.toNatTrans = θ.toNatTrans := congr(($h).toNatTrans)
end Mathlib.Tactic.CategoryTheory.ToApp
