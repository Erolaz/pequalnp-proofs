import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19349 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
        PEqualNP.Represents.Represents
          (fun u v : Fin 5 => (7577398 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [0, 6]⟩,
      ⟨.or, [7, 10]⟩,
      ⟨.or, [1, 5]⟩,
      ⟨.or, [8, 12]⟩,
      ⟨.not, [13]⟩,
      ⟨.and, [11, 14]⟩,
      ⟨.not, [11]⟩,
      ⟨.and, [12, 16]⟩,
      ⟨.or, [15, 17]⟩], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
