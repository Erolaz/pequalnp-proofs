import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_367

private abbrev edges : List (Fin 6 × Fin 6) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]

private def independentSets : Fin 5 → Finset (Fin 6) :=
  ![{0, 2, 4}, {1, 3, 5}, {0, 3}, {1, 4}, {2, 5}]

private theorem independent (i : Fin 5) :
    ∀ e ∈ edges, ¬ (e.1 ∈ independentSets i ∧ e.2 ∈ independentSets i) := by
  revert i
  decide

private theorem conflictingSets : ∀ i j : Fin 5, i ≠ j →
    ∃ e ∈ edges, (e.1 ∈ independentSets i ∧ e.2 ∈ independentSets j) ∨
      (e.1 ∈ independentSets j ∧ e.2 ∈ independentSets i) := by
  decide

private theorem coverBound : PEqualNP.MetaComplexity.SingleLevel.vc edges ≤ 3 := by
  apply Nat.sInf_le
  exact ⟨({0, 2, 4} : Finset (Fin 6)), by decide, by decide⟩

end PEqualNP.Outside.L_meta_367

open PEqualNP.Outside.L_meta_367

theorem PEqualNP.Outside.L_meta_367 : ∀ E : List (Fin 6 × Fin 6),
    E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)] →
    ∀ O : Finset (Fin 6) → Finset (Fin 6 × Fin 6),
      (∀ J : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) →
        (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧
          (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧
            ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) →
      PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2)
        (vectorSpan (ZMod 2) {w : Fin 6 × Fin 6 → ZMod 2 | ∃ J : Finset (Fin 6),
          (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  subst E
  classical
  let w (i : Fin 5) (d : Fin 6 × Fin 6) : ZMod 2 :=
    if d ∈ O (independentSets i) then 1 else 0
  have distinctOrientations : Function.Injective (fun i => O (independentSets i)) := by
    intro i j hEq
    change O (independentSets i) = O (independentSets j) at hEq
    by_contra hij
    obtain ⟨e, he, hconflict⟩ := conflictingSets i j hij
    have hi := hO (independentSets i) (independent i)
    have hj := hO (independentSets j) (independent j)
    rcases (hi.2.1 e he).1 with hdir | hdir
    · rcases hconflict with ⟨_, h⟩ | ⟨_, h⟩
      · exact hj.2.2 e (hEq ▸ hdir) h
      · exact hi.2.2 e hdir h
    · rcases hconflict with ⟨h, _⟩ | ⟨h, _⟩
      · exact hi.2.2 (e.2, e.1) hdir h
      · exact hj.2.2 (e.2, e.1) (hEq ▸ hdir) h
  have distinctVectors : Function.Injective w := by
    intro i j hEq
    apply distinctOrientations
    ext d
    have hvalue := congrFun hEq d
    by_cases hi : d ∈ O (independentSets i) <;>
      by_cases hj : d ∈ O (independentSets j) <;> simp_all [w]
  let orientations : Set (Fin 6 × Fin 6 → ZMod 2) :=
    {z | ∃ J : Finset (Fin 6), (∀ e ∈ edges, ¬ (e.1 ∈ J ∧ e.2 ∈ J)) ∧
      z = fun d => if d ∈ O J then 1 else 0}
  have hw (i : Fin 5) : w i ∈ orientations := ⟨independentSets i, independent i, rfl⟩
  let W := vectorSpan (ZMod 2) orientations
  change PEqualNP.MetaComplexity.SingleLevel.vc edges ≤ Module.finrank (ZMod 2) W
  -- Translate the five orientations by the first one to count vectors in the span.
  let translated (i : Fin 5) : W :=
    ⟨w i - w 0, vsub_mem_vectorSpan (ZMod 2) (hw i) (hw 0)⟩
  have translatedInjective : Function.Injective translated := by
    intro i j hEq
    apply distinctVectors
    have hsub : w i - w 0 = w j - w 0 := congrArg Subtype.val hEq
    simpa using congrArg (fun v => v + w 0) hsub
  let : Fintype W := Fintype.ofFinite W
  have cardBound := Fintype.card_le_of_injective translated translatedInjective
  rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at cardBound
  apply coverBound.trans
  by_contra! hsmall
  have hp : (2 : ℕ) ^ Module.finrank (ZMod 2) W ≤ 2 ^ 2 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega
