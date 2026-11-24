import Mathlib
import PEqualNP.Defs

-- The gate simplifier and its evaluation invariant are adapted from L-meta-1908.
namespace PEqualNP.Outside.L_meta_3070

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def readsAny (fixed : List ℕ) (g : Gate) : Bool :=
  fixed.any fun i => g.inputs.contains i

theorem simplified_count (n : ℕ) (gs : List Gate) (fixed : List ℕ) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
      (∀ k ∈ fixed, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + (gs.filter (readsAny fixed)).length
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim]
  | cons g gs ih =>
    intro acc legal held
    have htail := ih (elimStep n acc g) (fun t ht => legal t (List.mem_cons_of_mem _ ht)) (by
      intro k hk
      obtain ⟨hkl, c, hc⟩ := held k hk
      refine ⟨by simp [elimStep]; omega, c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc)
    change (elim n gs (elimStep n acc g)).2.length + ((g :: gs).filter (readsAny fixed)).length ≤
      acc.2.length + (g :: gs).length
    cases hread : readsAny fixed g
    · simp only [List.filter_cons, hread, Bool.false_eq_true, ite_false, List.length_cons]
      have extra : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega
    · obtain ⟨k,hk,hpin⟩ : ∃ k ∈ fixed, k ∈ g.inputs := by
        simpa [readsAny, List.any_eq_true] using hread
      obtain ⟨_,c,hc⟩ := held k hk
      have hg := legal g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count _ _ _ hg.1.1 (by simpa using hg.1.2) (by intro h; simpa using hg.2 h)
        exact ⟨c, List.mem_map.mpr ⟨k,hpin,hc⟩⟩
      have extra : (elimStep n acc g).2.length = acc.2.length := by
        change (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]
        simp
      simp only [List.filter_cons, hread, ite_true, List.length_cons]
      omega

def rawStat {n : ℕ} (v : Option (Fin n)) : Stat := v.elim (Sum.inl false) fun i => Sum.inr i.val

theorem input_inv {n : ℕ} (layout : List (Option (Fin n))) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (layout.map (fun v => v.elim false x)) (layout.map rawStat, []) := by
  refine ⟨by simp,fun i => ?_⟩
  have h1 : (layout.map rawStat).getD i (Sum.inl false) = rawStat (layout.getD i none) :=
    List.getD_map layout none (n := i) rawStat
  have h2 : (layout.map (fun v => v.elim false x)).getD i false = (layout.getD i none).elim false x :=
    List.getD_map layout none (n := i) (fun v => v.elim false x)
  change ((layout.map rawStat).getD i (Sum.inl false)).Valid n ∧
    ((layout.map rawStat).getD i (Sum.inl false)).val (List.ofFn x) = _
  rw [h1,h2]
  cases layout.getD i none with
  | none => exact ⟨trivial,rfl⟩
  | some j =>
    refine ⟨j.isLt, ?_⟩
    change (List.ofFn x).getD j.val false = x j
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

theorem relevant_pins (g : Gate) (h : Ok g) : (normGate g).inputs =
    (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) := by
  have op := h.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
  rcases op with e | e | e <;> simp [normGate, e, GateOp.eval]

end PEqualNP.Outside.L_meta_3070

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3070

theorem PEqualNP.Outside.L_meta_3070 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 : List ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x6 ∈ x4, x3[x6]? = Option.some Option.none) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x7) x3) ≠ x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x8) x3)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x4.any fun (x10 : ℕ) => (if x9.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains x10) x2.gates).length ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.map (fun (x10 : Option (Fin x1)) => x10.elim Bool.false x9) x3) := by
  intro n C layout fixed allowed hfixed nonconstant
  let gates := C.gates.map normGate
  let acc : List Stat × List Gate := (layout.map rawStat, [])
  have legal : ∀ g ∈ gates, NOk g := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok t (allowed t ht)
  have counts : (gates.filter (readsAny fixed)).length = (C.gates.filter (fun g =>
      fixed.any (fun i => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i))).length := by
    simp only [gates, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro g hg
    simp [readsAny, relevant_pins g (allowed g hg)]
  have budget := simplified_count n gates fixed acc legal (by
    intro k hk
    have someNone := hfixed k hk
    have isValid : k < layout.length := by
      by_contra! beyond
      rw [List.getElem?_eq_none beyond] at someNone
      cases someNone
    refine ⟨by simpa [acc] using isValid, false, ?_⟩
    show (layout.map rawStat).getD k (Sum.inl false) = Sum.inl false
    have eq : (layout.map rawStat).getD k (Sum.inl false) = rawStat (layout.getD k none) :=
      List.getD_map layout none (n := k) rawStat
    rw [eq]
    have no : layout.getD k none = none := by
      rw [List.getD_eq_getElem?_getD, someNone]
      rfl
    rw [no]
    rfl)
  rw [counts, show gates.length = C.size from by simp [gates,Circuit.size]] at budget
  have basis := elim_ok n gates acc (by simp [acc])
  have eval (x : Fin n → Bool) := inv_elim n (List.ofFn x) (by simp) gates _ acc
    (fun g hg => (legal g hg).1) (input_inv layout x)
  generalize hres : elim n gates acc = res at basis eval budget
  cases hOut : res.1.getD C.output (Sum.inl false) with
  | inl b =>
    exfalso
    obtain ⟨x,y,ne⟩ := nonconstant
    have eq (a : Fin n → Bool) : b = C.eval (layout.map fun v => v.elim false a) := by
      have h := ((eval a).2 C.output).2
      rw [hOut, Stat.val] at h
      change b = (wiresFrom (C.gates.map normGate) _).getD C.output false at h
      rwa [wiresFrom_norm] at h
    exact ne ((eq x).symm.trans (eq y))
  | inr r =>
    refine ⟨⟨res.2,r⟩, basis, ?_, ?_⟩
    · simpa only [Circuit.size, acc, List.length_nil, Nat.zero_add] using budget
    · intro x
      have h := ((eval x).2 C.output).2
      rw [hOut, Stat.val] at h
      change (⟨res.2,r⟩ : Circuit).eval (List.ofFn x) =
        (wiresFrom (C.gates.map normGate) _).getD C.output false at h
      rwa [wiresFrom_norm] at h
