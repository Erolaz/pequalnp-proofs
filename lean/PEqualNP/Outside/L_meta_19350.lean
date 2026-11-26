import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19350 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 5 => (7571262 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [1, 5]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.or, [7, 11]⟩,
      ⟨.or, [10, 12]⟩,
      ⟨.or, [2, 10]⟩,
      ⟨.and, [14, 12]⟩,
      ⟨.not, [15]⟩,
      ⟨.and, [13, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
