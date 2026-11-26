import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19695 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3683421 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [4, 9]⟩,
      ⟨.or, [1, 10]⟩,
      ⟨.and, [5, 10]⟩,
      ⟨.or, [6, 12]⟩,
      ⟨.or, [3, 13]⟩,
      ⟨.or, [11, 14]⟩,
      ⟨.or, [0, 14]⟩,
      ⟨.not, [15]⟩,
      ⟨.and, [11, 16]⟩,
      ⟨.or, [17, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
