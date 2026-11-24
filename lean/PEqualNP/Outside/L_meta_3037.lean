import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3037 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2],   have x4 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x4 : Finset (Fin x1)) (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide ¬∃ x7 ∈ x4, x2 x6 x7) (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) x5;   ∀ (x5 : Finset (Fin x1)), Fintype.card { x6 : Fin x1 // x4 x5 (Fin.natAdd x1 x6) = Bool.true } = x5.card ∧ ¬∃ (x6 : Fin x1) (x7 : Fin x1), x2 x6 x7 ∧ x4 x5 (Fin.castAdd x1 x6) = Bool.true ∧ x4 x5 (Fin.natAdd x1 x7) = Bool.true := by
  dsimp only
  intro n R _ lines
  constructor
  · rw [← Fintype.card_coe lines]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun l => by simp only [Fin.addCases_right, decide_eq_true_eq]))
  · rintro ⟨p,l,incident,pointOn,lineOn⟩
    simp only [Fin.addCases_left, decide_eq_true_eq] at pointOn
    simp only [Fin.addCases_right, decide_eq_true_eq] at lineOn
    exact pointOn ⟨l,lineOn,incident⟩
