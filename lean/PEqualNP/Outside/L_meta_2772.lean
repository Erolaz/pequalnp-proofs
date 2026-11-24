import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private def implication (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

private theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem append_imp {a b : List Bool} {u v : Bool} (len : a.length = b.length)
    (before : implication a b) (last : u = true → v = true) :
    implication (a ++ [u]) (b ++ [v]) := by
  intro i old
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi] at old
    rw [List.getD_append _ _ _ _ (len ▸ hi)]
    exact before i old
  · rw [List.getD_append_right _ _ _ _ (by omega)] at old
    rw [List.getD_append_right _ _ _ _ (by omega), ← len]
    cases offset : i - a.length with
    | zero => exact last (by simpa [offset] using old)
    | succ k => simp [offset] at old

private theorem op_imp {op : GateOp} (ao : op = GateOp.and ∨ op = GateOp.or)
    (pins : List ℕ) {a b : ℕ → Bool} (rows : ∀ i ∈ pins, a i = true → b i = true) :
    op.eval (pins.map a) = true → op.eval (pins.map b) = true := by
  rcases ao with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro old _ hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact rows i hi (old _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, old⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, rows i hi old⟩

private theorem run_imp (gs : List Gate)
    (ao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (len : a.length = b.length) (entries : implication a b) :
    implication (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact entries
  | cons g gs ih =>
    change implication (run gs (step a g)) (run gs (step b g))
    apply ih (fun t ht => ao t (List.mem_cons_of_mem _ ht)) (by simp [step, len])
    apply append_imp len entries
    exact op_imp (ao g List.mem_cons_self) g.inputs (fun i _ => entries i)

private theorem step_replace {w : List Bool} {op : GateOp} {pins : List ℕ} {b p q : ℕ}
    (ao : op = GateOp.and ∨ op = GateOp.or) (two : pins.length = 2) (pos : b < 2)
    (old : pins.getD b 0 = p) :
    (w.getD p false = true → w.getD q false = true) →
      implication (step w ⟨op, pins⟩) (step w ⟨op, pins.set b q⟩) := by
  intro more
  apply append_imp rfl (fun _ h => h)
  obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp two
  interval_cases b <;> rcases ao with rfl | rfl <;>
    simp [GateOp.eval, List.getD] at old more ⊢ <;> subst p <;> tauto

private theorem step_replace_eq {w : List Bool} {op : GateOp} {pins : List ℕ} {b p q : ℕ}
    (two : pins.length = 2) (pos : b < 2) (old : pins.getD b 0 = p)
    (bits : w.getD p false = w.getD q false) :
    step w ⟨op, pins.set b q⟩ = step w ⟨op, pins⟩ := by
  obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp two
  interval_cases b <;> simp [List.getD] at old bits <;> subst p <;> simp [step, bits]

private theorem replace_fold (gs : List Gate) (w : List Bool) (j b q : ℕ)
    (hj : j < gs.length) (pos : b < 2)
    (ao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (two : gs[j].inputs.length = 2)
    (hp : gs[j].inputs.getD b 0 < w.length + j) (hq : q < w.length + j) :
    let old := gs[j]
    let p := old.inputs.getD b 0
    let gs' := gs.set j ⟨old.op, old.inputs.set b q⟩
    ((run gs w).getD p false = true → (run gs w).getD q false = true) →
      implication (run gs w) (run gs' w) ∧
      ((run gs w).getD p false = (run gs w).getD q false → run gs' w = run gs w) := by
  induction gs generalizing j w with
  | nil => simp at hj
  | cons first tail ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at two hp hq
      dsimp only [List.getElem_cons_zero, List.set_cons_zero]
      intro more
      let p := first.inputs.getD b 0
      have p_value : (run (first :: tail) w).getD p false = w.getD p false :=
        run_keeps _ _ _ hp
      have q_value : (run (first :: tail) w).getD q false = w.getD q false :=
        run_keeps _ _ _ hq
      change ((run (first :: tail) w).getD p false = true →
        (run (first :: tail) w).getD q false = true) at more
      rw [p_value, q_value] at more
      refine ⟨?_, ?_⟩
      · apply run_imp tail (fun g hg => ao g (List.mem_cons_of_mem _ hg)) (by simp [step])
        exact step_replace (ao first List.mem_cons_self) two pos rfl more
      · intro same
        change (run (first :: tail) w).getD p false = (run (first :: tail) w).getD q false at same
        rw [p_value, q_value] at same
        change run tail (step w ⟨first.op, first.inputs.set b q⟩) = run tail (step w first)
        cases first
        rw [step_replace_eq two pos rfl same]
    | succ j =>
      have hj' : j < tail.length := by simpa using hj
      have hp' : tail[j].inputs.getD b 0 < (step w first).length + j := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
      have hq' : q < (step w first).length + j := by simp [step]; omega
      exact ih (step w first) j hj' (fun g hg => ao g (List.mem_cons_of_mem _ hg)) two hp' hq'

end PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.Outside.L_meta_2772
theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C j b p q hyp
  obtain ⟨⟨ao, back, arity⟩, _, hj, hb, hp, hq, raises, below⟩ := hyp
  let old := C.gates[j]
  let fresh : Gate := ⟨old.op, old.inputs.set b q⟩
  let D : Circuit := ⟨C.gates.set j fresh, C.output⟩
  have oldAt : gateAt C j = old := List.getD_eq_getElem _ _ hj
  rw [oldAt] at hp ⊢
  change IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size
  have oldMem : old ∈ C.gates := List.getElem_mem hj
  have two := arity old oldMem
  have sizes : D.gates.length = C.gates.length := by simp [D]
  have dAtSame : gateAt D j = fresh := by
    rw [gateAt, List.getD_eq_getElem _ _ (by rwa [sizes])]
    exact List.getElem_set_self _
  have dAtOther (k : ℕ) (hk : k < D.gates.length) (h : j ≠ k) : gateAt D k = gateAt C k := by
    have hk' : k < C.gates.length := by simpa only [sizes] using hk
    simp only [gateAt, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk']
    exact List.getElem_set_ne h _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, sizes⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with keep | rfl
    · exact ao g keep
    · exact ao old oldMem
  · intro k hk i hi
    by_cases he : j = k
    · subst k
      rw [dAtSame] at hi
      rcases List.mem_or_eq_of_mem_set hi with keep | rfl
      · exact back j hj i (by rwa [oldAt])
      · exact hq
    · rw [dAtOther k hk he] at hi
      exact back k (by rwa [sizes] at hk) i hi
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with keep | rfl
    · exact arity g keep
    · simpa [fresh] using two
  · funext x
    let w := List.ofFn x
    have hpMem : p ∈ old.inputs := by
      rw [← hp, List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have hp' := back j hj p (by rwa [oldAt])
    have hw : w.length = n := List.length_ofFn
    have h := replace_fold C.gates w j b q hj hb ao two (by rw [hp, hw]; exact hp') (by rwa [hw])
    change ((run C.gates w).getD (old.inputs.getD b 0) false = true →
      (run C.gates w).getD q false = true) →
      implication (run C.gates w) (run D.gates w) ∧
      ((run C.gates w).getD (old.inputs.getD b 0) false = (run C.gates w).getD q false →
        run D.gates w = run C.gates w) at h
    rw [hp] at h
    obtain ⟨more, same⟩ := h (raises x)
    change (run D.gates w).getD C.output false = (run C.gates w).getD C.output false
    cases he : (run C.gates w).getD C.output false
    · have noQ : (run C.gates w).getD q false = false := Bool.eq_false_iff.mpr (fun hq' => by
        have hit := below x hq'
        change (run C.gates w).getD C.output false = true at hit
        exact Bool.false_ne_true (he.symm.trans hit))
      have noP : (run C.gates w).getD p false = false := Bool.eq_false_iff.mpr (fun hp' => by
        have hit := raises x hp'
        change (run C.gates w).getD q false = true at hit
        exact Bool.false_ne_true (noQ.symm.trans hit))
      rw [same (noP.trans noQ.symm), he]
    · exact more C.output he
