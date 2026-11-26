import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19808 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839968994078334435 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨⟨[⟨.or, [1, 4]⟩,
      ⟨.or, [7, 16]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.or, [2, 18]⟩,
      ⟨.or, [1, 3]⟩,
      ⟨.or, [2, 16]⟩,
      ⟨.or, [6, 17]⟩,
      ⟨.or, [5, 19]⟩,
      ⟨.or, [7, 18]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.or, [8, 15]⟩,
      ⟨.or, [12, 13]⟩,
      ⟨.or, [10, 12]⟩,
      ⟨.or, [10, 11]⟩,
      ⟨.or, [14, 15]⟩,
      ⟨.or, [9, 14]⟩,
      ⟨.or, [8, 9]⟩,
      ⟨.or, [12, 32]⟩,
      ⟨.or, [11, 27]⟩,
      ⟨.or, [13, 31]⟩,
      ⟨.and, [24, 33]⟩,
      ⟨.and, [20, 28]⟩,
      ⟨.and, [23, 30]⟩,
      ⟨.and, [26, 36]⟩,
      ⟨.and, [25, 34]⟩,
      ⟨.and, [22, 35]⟩,
      ⟨.and, [21, 29]⟩,
      ⟨.or, [37, 38]⟩,
      ⟨.or, [39, 40]⟩,
      ⟨.or, [41, 42]⟩,
      ⟨.or, [43, 44]⟩,
      ⟨.or, [45, 46]⟩,
      ⟨.or, [47, 48]⟩], 49⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
