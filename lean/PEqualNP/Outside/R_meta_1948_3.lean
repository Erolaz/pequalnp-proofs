import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_1948_3
    (candidate : ∃ (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit),
      2 ≤ q ∧ N = q ^ 2 + q + 1 ∧
      (∀ l : Fin N, Nat.card {p : Fin N // I p l} = q + 1) ∧
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) ∧
      IsAO2 (N + N) C ∧ HasLineDegree (N + N) (Finset.range (N + N)) C 4 ∧
      (∀ p l : Fin N, I p l →
        readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true) ∧
      100 * C.size < N * q ∧
      ∀ S : Finset (Fin (N + N)), S.card ≤ 4 →
        (circuitFun (N + N) C (setInput S) = true ↔
          ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S))
    (boundedSupport : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      ∀ x : Fin n → Bool, circuitFun n C x = true ↔
        ∃ S : Finset (Fin n), S.card ≤ C.lineDeg n (Finset.range n) ∧
          (∀ i ∈ S, x i = true) ∧ circuitFun n C (setInput S) = true) :
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) := by
  classical
  intro bound
  obtain ⟨q, N, I, C, hq, hN, hline, hpair, hao, hdegree, hread, hsmall, htest⟩ :=
    candidate
  have support := boundedSupport (N + N) C hao
  have pairAccepted (p l : Fin N) (hi : I p l) :
      circuitFun (N + N) C (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
    have hcard : ({Fin.castAdd N p, Fin.natAdd N l} : Finset _).card ≤ 4 :=
      (Finset.card_insert_le _ _).trans (by simp)
    exact (htest _ hcard).mpr ⟨p, l, hi, by simp, by simp⟩
  have computed : ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) C x =
        decide (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro hx
      obtain ⟨S, hS, hsub, hval⟩ := (support x).mp hx
      obtain ⟨p, l, hp, hmp, hml⟩ := (htest S (hS.trans hdegree)).mp hval
      exact ⟨p, l, hp, hsub _ hmp, hsub _ hml⟩
    · rintro ⟨p, l, hp, hxp, hxl⟩
      let T : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
      obtain ⟨S, hS, hsub, hvalS⟩ := (support (setInput T)).mp (pairAccepted p l hp)
      refine (support x).mpr ⟨S, hS, ?_, hvalS⟩
      intro i hi
      have hit := hsub i hi
      change decide (i ∈ T) = true at hit
      simp only [decide_eq_true_eq, T, Finset.mem_insert, Finset.mem_singleton] at hit
      rcases hit with rfl | rfl
      · exact hxp
      · exact hxl
  have read : IsReadK (N + N) C 2 := by
    intro S hS
    have accepted := hS.1
    rw [computed, decide_eq_true_eq] at accepted
    change ∃ p l : Fin N, I p l ∧ decide (Fin.castAdd N p ∈ S) = true ∧
      decide (Fin.natAdd N l ∈ S) = true at accepted
    simp only [decide_eq_true_eq] at accepted
    obtain ⟨p, l, hp, hmp, hml⟩ := accepted
    let T : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
    have hTS : T ⊆ S := Finset.insert_subset_iff.mpr ⟨hmp, Finset.singleton_subset_iff.mpr hml⟩
    have hEq : T = S := by
      by_contra hne
      have hlt : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩
      have hrejected := hS.2 T (Finset.mem_ssubsets.mpr hlt)
      rw [pairAccepted p l hp] at hrejected
      contradiction
    rw [← hEq]
    exact hread p l hp
  have lineCard (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hline l
  exact (Nat.not_le_of_gt hsmall) (bound q N I C hq hN lineCard hpair hao computed read)
