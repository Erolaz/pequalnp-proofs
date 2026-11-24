import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private def replace (target : ℕ) (sigma : ℕ → ℕ) (r : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => if i = target then sigma r else i)⟩

private def rewire (target : ℕ) (sigma : ℕ → ℕ) (r : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => replace target sigma r g :: rewire target sigma (r + 1) gs

private theorem rewire_eq (target : ℕ) (sigma : ℕ → ℕ) (gs : List Gate) (r : ℕ) :
    rewire target sigma r gs = gs.mapIdx (fun j g => replace target sigma (r + j) g) := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih =>
    rw [rewire, List.mapIdx_cons, ih]
    have align (j : ℕ) : r + 1 + j = r + (j + 1) := by omega
    simp only [Nat.add_zero, align]

private theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem append_rel (P : Bool → Bool → Prop) (default : P false false)
    {a b : List Bool} {u v : Bool} (len : a.length = b.length)
    (old : ∀ i, P (a.getD i false) (b.getD i false)) (last : P u v) :
    ∀ i, P ((a ++ [u]).getD i false) ((b ++ [v]).getD i false) := by
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (len ▸ hi)]
    exact old i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), ← len]
    cases offset : i - a.length with
    | zero => simpa [offset] using last
    | succ k => simpa [offset] using default

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

private theorem op_eq (op : GateOp) (pins : List ℕ) {a b : ℕ → Bool}
    (rows : ∀ i ∈ pins, a i = b i) : op.eval (pins.map a) = op.eval (pins.map b) :=
  congrArg op.eval (List.map_congr_left rows)

private theorem fold_rel (P : Bool → Bool → Prop) (default : P false false)
    (follow : ∀ {a b c}, P a b → P b c → P a c)
    (gate_rel : ∀ op : GateOp, op = .and ∨ op = .or → ∀ (pins : List ℕ) (a b : ℕ → Bool),
      (∀ i ∈ pins, P (a i) (b i)) → P (op.eval (pins.map a)) (op.eval (pins.map b)))
    (n target : ℕ) (sigma : ℕ → ℕ) (earlier : ∀ r, sigma r < target)
    (gs : List Gate) (r : ℕ) (fresh old : List Bool)
    (len : old.length = n + r) (same : fresh.length = old.length)
    (prior : ∀ i, P (fresh.getD i false) (old.getD i false))
    (ao : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (back : ∀ j (hj : j < gs.length), target ∈ gs[j].inputs → target < n + (r + j))
    (cmp : ∀ j (hj : j < gs.length), target ∈ gs[j].inputs →
      P ((run gs old).getD (sigma (r + j)) false) ((run gs old).getD target false)) :
    ∀ i, P ((run (rewire target sigma r gs) fresh).getD i false) ((run gs old).getD i false) := by
  induction gs generalizing r fresh old with
  | nil => exact prior
  | cons g rest ih =>
    have nextStep : ∀ i, P ((step fresh (replace target sigma r g)).getD i false)
        ((step old g).getD i false) := by
      apply append_rel P default same prior
      have chosen := gate_rel g.op (ao g List.mem_cons_self) g.inputs
        (fun j => fresh.getD (if j = target then sigma r else j) false) (fun j => old.getD j false)
      simpa only [replace, List.map_map, Function.comp_def] using chosen (by
        intro p hp
        by_cases eq : p = target
        · subst p
          simp only [ite_true]
          have within : target < old.length := by simpa [len] using back 0 (by simp) hp
          have subWithin := (earlier r).trans within
          have compare := cmp 0 (by simp) hp
          simp only [Nat.add_zero] at compare
          rw [run_keeps _ _ _ subWithin, run_keeps _ _ _ within] at compare
          exact follow (prior (sigma r)) compare
        · simpa only [ite_eq_right eq] using prior p)
    change ∀ i, P ((run (rewire target sigma (r + 1) rest)
        (step fresh (replace target sigma r g))).getD i false) ((run rest (step old g)).getD i false)
    have align (j : ℕ) : r + (j + 1) = r + 1 + j := by omega
    apply ih (r + 1) _ _ (by simp [step, len, Nat.add_assoc]) (by simp [step, same]) nextStep
      (fun g hg => ao g (List.mem_cons_of_mem _ hg))
    · intro j hj hp
      have h := back (j + 1) (by simpa using hj) (by simpa using hp)
      rw [← align j]
      exact h
    · intro j hj hp
      have h := cmp (j + 1) (by simpa using hj) (by simpa using hp)
      rw [← align j]
      exact h

end PEqualNP.Outside.L_meta_3453_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.FactorSubst PEqualNP.Outside.L_meta_3453_aux

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hmodel _ hSigma
  obtain ⟨ao, back, _⟩ := hmodel
  let w := List.ofFn x
  let D := substReads C n u sigma
  have rewritten : rewire (n + u) sigma 0 C.gates = D.gates := by
    rw [rewire_eq]
    simp only [Nat.zero_add, D, substReads, replace]
  have gate_spec (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  have valid (j : ℕ) (hj : j < C.gates.length) (pin : n + u ∈ C.gates[j].inputs) :
      n + u < n + (0 + j) := by
    rw [Nat.zero_add]
    apply back j hj
    rwa [gate_spec j hj]
  have trace (P : Bool → Bool → Prop) (refl : ∀ b, P b b)
      (trans : ∀ {a b c}, P a b → P b c → P a c)
      (gate_rel : ∀ op : GateOp, op = .and ∨ op = .or → ∀ (pins : List ℕ) (a b : ℕ → Bool),
        (∀ i ∈ pins, P (a i) (b i)) → P (op.eval (pins.map a)) (op.eval (pins.map b)))
      (cmp : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
        P ((C.wires w).getD (sigma r) false) ((C.wires w).getD (n + u) false)) :
      ∀ i, P ((D.wires w).getD i false) ((C.wires w).getD i false) := by
    have witness := fold_rel P (refl false) trans gate_rel n (n + u) sigma hSigma C.gates 0 w w
      (by simp [w]) rfl (fun _ => refl _) ao valid (by
        intro j hj pin
        have h := cmp j hj ((gate_spec j hj).symm ▸ pin)
        change P ((run C.gates w).getD (sigma j) false) ((run C.gates w).getD (n + u) false) at h
        rwa [Nat.zero_add])
    rw [rewritten] at witness
    exact witness
  constructor
  · intro cmp
    exact trace (fun a b => a = true → b = true) (fun _ h => h) (fun first second h => second (first h))
      (fun _ op pins _ _ rows => op_imp op pins rows) cmp
  · intro cmp
    have eq := trace (fun a b => a = b) (fun _ => rfl) Eq.trans (fun op _ pins _ _ rows => op_eq op pins rows) cmp
    apply List.ext_getElem
    · change (run D.gates w).length = (run C.gates w).length
      simp only [run_length, D, substReads, List.length_mapIdx]
    · intro i hi hj
      have bit := eq i
      change ((substReads C n u sigma).wires (List.ofFn x)).getD i false =
        (C.wires (List.ofFn x)).getD i false at bit
      rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at bit
