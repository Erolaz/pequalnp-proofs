import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19452

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

-- The evaluation lemmas below follow L-meta-5552, and the cone lemmas follow L-meta-5781.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma cone_trans {d : ℕ} {C : Circuit} {i k j : ℕ}
    (hik : InCone d C i k) (hkj : InCone d C k j) : InCone d C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj,w,hw,hm,hkw⟩ := (inCone_iff d C k j).mp hkj
    apply (inCone_iff d C i j).mpr
    refine ⟨hj,w,hw,hm,Or.inr ?_⟩
    rcases hkw with rfl | hkw
    · exact hik
    · exact ih w hw hkw

def Live (d : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  C.output = d+j ∨ (d ≤ C.output ∧ InCone d C j (C.output-d))

def Absent (d : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  C.output ≠ i ∧ ∀ g < C.gates.length, Live d C g →
    i ∉ (C.gates.getD g ⟨GateOp.and, []⟩).inputs

def Read (d : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  i = C.output ∨ ∃ j < C.gates.length, Live d C j ∧ i ∈ (gateAt C j).inputs

lemma absent_not_read {d : ℕ} {C : Circuit} {i : ℕ} (h : Absent d C i) :
    ¬ Read d C i := by
  rintro (hout | ⟨j,hj,hl,hm⟩)
  · exact h.1 hout.symm
  · apply h.2 j hj hl
    rw [show C.gates.getD j ⟨GateOp.and, []⟩ = gateAt C j by
      rw [gateAt_eq hj]; simp [List.getD_eq_getElem?_getD, hj]]
    exact hm

lemma live_input {d : ℕ} {C : Circuit} {k j : ℕ} (hj : j < C.gates.length)
    (hl : Live d C j) (hk : k < j) (hm : d+k ∈ (gateAt C j).inputs) :
    Live d C k := by
  have hc : InCone d C k j := (inCone_iff d C k j).mpr ⟨hj,k,hk,hm,Or.inl rfl⟩
  right
  rcases hl with ho | ⟨ho, hc'⟩
  · exact ⟨by omega, by rwa [show C.output-d = j by omega]⟩
  · exact ⟨ho,cone_trans hc hc'⟩

lemma live_compare {d : ℕ} {C : Circuit} {x y : List Bool}
    (hx : x.length = d) (hy : y.length = d) (R : Bool → Bool → Prop)
    (href : ∀ b, R b b)
    (hgate : ∀ g ∈ C.gates, ∀ p q : ℕ → Bool,
      (∀ i ∈ g.inputs, R (p i) (q i)) →
      R (g.op.eval (g.inputs.map p)) (g.op.eval (g.inputs.map q)))
    (hraw : ∀ i < d, Read d C i → R (x.getD i false) (y.getD i false)) :
    R (C.eval x) (C.eval y) := by
  have runs (j : ℕ) (hj : j < C.gates.length) (hl : Live d C j) :
      R (val C x (d+j)) (val C y (d+j)) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rw [val_gate hx hj,val_gate hy hj]
      apply hgate _ (gateAt_mem hj)
      intro i hm
      by_cases hi : i < d+j
      · rw [ite_eq_left hi, ite_eq_left hi]
        by_cases hrawIdx : i < d
        · rw [val_input hx hrawIdx,val_input hy hrawIdx]
          exact hraw i hrawIdx (Or.inr ⟨j,hj,hl,hm⟩)
        · let k := i-d
          have he : i = d+k := by dsimp [k]; omega
          have hk : k < j := by omega
          rw [he] at hm ⊢
          exact ih k hk (by omega) (live_input hj hl hk hm)
      · rw [ite_eq_right hi, ite_eq_right hi]
        exact href false
  rw [eval_eq_val,eval_eq_val]
  by_cases hrawIdx : C.output < d
  · rw [val_input hx hrawIdx,val_input hy hrawIdx]
    exact hraw C.output hrawIdx (Or.inl rfl)
  · by_cases hgateIdx : C.output < d+C.gates.length
    · let j := C.output-d
      have he : C.output = d+j := by dsimp [j]; omega
      have H := runs j (by omega) (Or.inl he)
      rwa [← he] at H
    · rw [val_ge hx (by omega),val_ge hy (by omega)]
      exact href false

lemma one_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n+m := by
  simp [oneEach]

lemma one_at {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n+m) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n+v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_eq_left, Option.getD_some,
      decide_eq_decide, Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have h' : i - n < m := by omega
    simp only [List.getD_eq_getElem?_getD, List.length_ofFn, List.getElem?_ofFn, h',
      dite_eq_left, Option.getD_some, decide_eq_decide, Fin.ext_iff]
    omega

lemma gate_eq (g : Gate) (p q : ℕ → Bool) (h : ∀ i ∈ g.inputs, p i = q i) :
    g.op.eval (g.inputs.map p) = g.op.eval (g.inputs.map q) := by
  rw [List.map_congr_left h]

end PEqualNP.Outside.L_meta_19452

open PEqualNP.Outside.L_meta_19452 in
theorem PEqualNP.Outside.L_meta_19452 :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit) (u u' : Fin n),
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.Represents.Represents A C →
      (C.output ≠ u.val ∧
        ∀ g < C.gates.length,
          (C.output = n + m + g ∨
           (n + m ≤ C.output ∧
            PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) →
          u.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) →
      (C.output ≠ u'.val ∧
        ∀ g < C.gates.length,
          (C.output = n + m + g ∨
           (n + m ≤ C.output ∧
            PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) →
          u'.val ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) →
      ∀ v : Fin m, A u v = A u' v := by
  intro n m A C u u' _ hrep hu hu' v
  change Absent (n+m) C u.val at hu
  change Absent (n+m) C u'.val at hu'
  rw [← hrep u v,← hrep u' v]
  apply live_compare (one_len u v) (one_len u' v) Eq (fun _ => rfl)
    (fun g _ => gate_eq g)
  intro i hi hread
  have hne : i ≠ u.val := fun h => absent_not_read hu (h ▸ hread)
  have hne' : i ≠ u'.val := fun h => absent_not_read hu' (h ▸ hread)
  rw [one_at u v i hi,one_at u' v i hi]
  simp [hne,hne']
