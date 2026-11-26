import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19305 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 5 => (3247678 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [5, 9]⟩,
      ⟨.and, [1, 10]⟩,
      ⟨.not, [5]⟩,
      ⟨.and, [0, 12]⟩,
      ⟨.or, [11, 13]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.or, [15, 4]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.and, [16, 17]⟩,
      ⟨.or, [14, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
