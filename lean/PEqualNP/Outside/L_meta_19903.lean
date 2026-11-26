import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19903 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (2045083468351882920 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[⟨.or, [13, 11]⟩,
      ⟨.or, [15, 16]⟩,
      ⟨.and, [0, 17]⟩,
      ⟨.or, [14, 9]⟩,
      ⟨.or, [19, 10]⟩,
      ⟨.and, [1, 20]⟩,
      ⟨.or, [13, 8]⟩,
      ⟨.or, [22, 9]⟩,
      ⟨.and, [2, 23]⟩,
      ⟨.or, [19, 8]⟩,
      ⟨.and, [3, 25]⟩,
      ⟨.or, [12, 10]⟩,
      ⟨.or, [15, 27]⟩,
      ⟨.and, [4, 28]⟩,
      ⟨.or, [12, 11]⟩,
      ⟨.or, [15, 30]⟩,
      ⟨.and, [5, 31]⟩,
      ⟨.or, [14, 22]⟩,
      ⟨.and, [6, 33]⟩,
      ⟨.or, [27, 11]⟩,
      ⟨.and, [7, 35]⟩,
      ⟨.or, [18, 21]⟩,
      ⟨.or, [37, 24]⟩,
      ⟨.or, [38, 26]⟩,
      ⟨.or, [39, 29]⟩,
      ⟨.or, [40, 32]⟩,
      ⟨.or, [41, 34]⟩,
      ⟨.or, [42, 36]⟩], 43⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
