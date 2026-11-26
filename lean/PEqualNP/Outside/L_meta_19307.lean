import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19307 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 5 => (7570494 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.not, [5]⟩,
      ⟨.and, [0, 10]⟩,
      ⟨.not, [0]⟩,
      ⟨.and, [12, 5]⟩,
      ⟨.or, [11, 13]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.and, [15, 16]⟩,
      ⟨.or, [14, 17]⟩], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
