import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16303

namespace Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 270
-- Free complementation leaves four binary choices up to output polarity.
def norm (x : W) : W := if x.getLsbD 103 then ~~~x else x

theorem norm_or (w : W) : w = norm w ∨ w = ~~~(norm w) := by
  unfold norm
  split <;> simp

def rawOps (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def ops (x y : W) : List W := (rawOps x y).map norm
def sep (x : W) : BitVec 103 := ((x >>> 103) ^^^ x).setWidth 103
def cuts (ws : List W) : BitVec 103 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (~~~(0xffffffff80000000 : BitVec 64)) ++ (-1 : BitVec 103) ++ (0 : BitVec 103)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 103) (w : W) : Prop :=
  w.getLsbD (103+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 103) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  have hnorm : differs i (norm q) ↔ differs i q := by
    unfold norm differs
    split <;> simp [show 103+i.val < 270 by omega, show i.val < 270 by omega]
  have hd := hnorm.mp hd
  simp only [rawOps, List.mem_cons, List.not_mem_nil, or_false] at hq
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 103+i.val < 270 := by omega
  have hi' : i.val < 270 := by omega
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 103) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 103)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, rawOps, List.mem_toFinset, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  ((ops a b).filter (fun w => !(a::b::r).contains w)).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hfresh : z ∉ a::b::r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_filter.mpr ⟨List.mem_toFinset.mp hz, ?_⟩, ?_⟩
  · simpa using hfresh
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hnew : z ∉ a::b::r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hnew hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 270 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 270)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ rawOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z := by
    have used : norm w ∈ basicOps a b := List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
    refine .inr ⟨a,ha,b,hb,h,norm w,used,.inr (.inr ⟨norm w,Finset.mem_insert_self ..,?_⟩)⟩
    rcases hz with rfl | rfl
    · exact norm_or _
    · rcases norm_or w with eq | eq
      · exact .inr (congrArg (fun i => ~~~i) eq)
      · exact .inl (by simpa only [BitVec.not_not] using congrArg (fun i => ~~~i) eq)
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [rawOps] : a &&& b ∈ rawOps a b) _ (.inl rfl)
  · exact add _ (by simp [rawOps] : a &&& ~~~b ∈ rawOps a b) _ (.inl rfl)
  · exact add _ (by simp [rawOps] : b &&& ~~~a ∈ rawOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [rawOps] : a ||| b ∈ rawOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 270) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 270) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 270) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#270)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 1 && x 4) || (x 0 && x 3 && x 4) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 4 && x 5)

def insertWire (w : W) : List W → List W
  | [] => [w]
  | x::xs => if (w.toNat >>> 206) ≤ (x.toNat >>> 206) then w::x::xs else x::insertWire w xs

def sortBank : List W → List W
  | [] => []
  | w::ws => insertWire w (sortBank ws)

theorem insertWire_perm (w : W) (ws : List W) : (insertWire w ws).Perm (w::ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    unfold insertWire
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap ..)

theorem sortBank_perm (ws : List W) : (sortBank ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons w ws ih => exact (insertWire_perm w (sortBank ws)).trans (ih.cons w)

theorem sortBank_finset (ws : List W) : (sortBank ws).toFinset = ws.toFinset := by
  ext w
  simpa only [List.mem_toFinset] using (sortBank_perm ws).mem_iff (a := w)

theorem sortBank_nodup {ws : List W} (h : ws.Nodup) : (sortBank ws).Nodup :=
  (sortBank_perm ws).nodup_iff.mpr h

abbrev Mark := W × BitVec 103

def mark (w : W) : Mark := (w,sep w)

def markedCuts (ws : List Mark) : BitVec 103 := ws.foldr (fun w v => w.2 ||| v) 0

lemma markedCuts_eq (ws : List W) : markedCuts (ws.map mark) = cuts ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [markedCuts,cuts,mark] using congrArg (sep w ||| ·) ih

lemma unmark (ws : List W) : (ws.map mark).map Prod.fst = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [mark,ih]

lemma singles_map_eq {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a,r) => (f a,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [singles,ih,List.map_map,Function.comp_def]

lemma pairs_map_eq {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [pairs,ih,singles_map_eq,List.map_map,Function.comp_def]

def cachedSearch : ℕ → List Mark → Bool
  | 0, ws => (ws.map Prod.fst == [goal] || ws.map Prod.fst == [~~~goal])
  | t+1, ws => (ws.map Prod.fst == [goal] || ws.map Prod.fst == [~~~goal]) ||
      (pairs ws).any (fun (a,b,r) =>
        let base := markedCuts r
        let old := a.1 :: b.1 :: r.map Prod.fst
        ((ops a.1 b.1).filter (fun z => !old.contains z)).any fun z =>
          (sep z ||| base == -1) && cachedSearch t (mark z :: r))

lemma cachedSearch_eq (t : ℕ) (ws : List W) : cachedSearch t (ws.map mark) = optimized t 0 ws := by
  induction t generalizing ws with
  | zero => simp only [cachedSearch,optimized,unmark]
  | succ k ih =>
    simp only [cachedSearch,optimized,unmark,pairs_map_eq,List.any_map,Function.comp_def]
    congr 1
    apply List.any_congr rfl
    intro s
    obtain ⟨a,b,r⟩ := s
    simp only [mark,markedCuts_eq,dispatch]
    apply List.any_congr rfl
    intro z
    have same : cachedSearch k ((z,sep z)::r.map mark) = optimized k 0 (z::r) := ih (z::r)
    rw [same]
    simp

def allowedNext (table : ℕ → List W → Bool) (t : ℕ) (ws : List W) : Bool :=
  if t = 0 then ws == [goal] || ws == [~~~goal] else !table t (sortBank ws)

def closedState (table : ℕ → List W → Bool) : ℕ → List W → Bool
  | 0, _ => false
  | k+1, ws =>
    !(ws == [goal] || ws == [~~~goal] ||
      (pairs ws).any (fun (a,b,r) =>
        dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r))

theorem closed_sound (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    {g : W} (hg : g = goal ∨ g = ~~~goal) :
    ∀ t ws, ws.Nodup → live basicOps g t ws.toFinset → table t ws = false := by
  intro t
  induction t with
  | zero =>
    intro ws _ _
    cases ht : table 0 ws
    · rfl
    · have bad := closure 0 ws ht
      simp [closedState] at bad
  | succ k ih =>
    intro ws nd running
    cases current : table (k+1) ws
    · rfl
    · have blocked := closure _ _ current
      rcases first_live running with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
      · rcases hg with rfl | rfl <;> simp [closedState,singleton_list nd done] at blocked
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have attempt {a b : W} (perm : ws.Perm (a::b::r))
            (hs : ws.toFinset = insert a (insert b needed)) (hz : z ∈ basicOps a b) :
            dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm nd hs
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hs]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (hfin ▸ List.mem_toFinset.mpr hu))
          have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
          have hl : live basicOps g k (z::kept).toFinset := by simpa [hfin] using tail
          have q := live_card hl
          rw [List.toFinset_card_of_nodup hnd,List.length_cons] at q
          have q' := live_card running
          rw [List.toFinset_card_of_nodup nd] at q'
          have len := perm.length_eq
          simp only [List.length_cons] at len
          have hnew : z ∉ a::b::r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
          apply dispatch_complete (k := k) (extra := k+2-ws.length)
            (fun _ => allowedNext table k) hz hnew hk (by omega) (by omega) (cuts_full hg hl)
          by_cases done : k = 0
          · subst k
            rcases hg with rfl | rfl <;> simp [allowedNext,singleton_list hnd hl]
          · have cold := ih _ (sortBank_nodup hnd) ((sortBank_finset _).symm ▸ hl)
            simp [allowedNext,done,cold]
        have branch : (pairs ws).any (fun (a,b,r) =>
            dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r) = true := by
          apply List.any_eq_true.mpr
          rcases hm with direct | swap
          · exact ⟨(a,b,r),direct,attempt hp hs hz⟩
          · exact ⟨(b,a,r),swap,attempt (hp.trans (.swap _ _ _))
              (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
        simp [closedState,branch] at blocked

def rootClosed (table : ℕ → List W → Bool) (cap : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.all fun ws => !(decide (ws.length ≤ cap+1) &&
    (cuts ws == -1) && allowedNext table cap ws)

theorem rootClosed_sound (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    {g : W} (hg : g = goal ∨ g = ~~~goal) (cap : ℕ) (inputs : List W)
    (nd : inputs.Nodup) (root : rootClosed table cap inputs = true) :
    ¬ build basicOps g cap inputs.toFinset := by
  intro run
  classical
  obtain ⟨s,hs,hl⟩ := compress run
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hn := nd.filter (· ∈ s)
  have hl' : live basicOps g cap ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hn] at sz
  have fits : allowedNext table cap ws = true := by
    by_cases done : cap = 0
    · subst cap
      change ws.toFinset = {g} at hl'
      have only : ws = [g] := singleton_list (ws := ws) hn hl'
      rw [only]
      rcases hg with rfl | rfl <;> simp [allowedNext]
    · have cold := closed_sound table closure hg cap (sortBank ws) (sortBank_nodup hn)
        ((sortBank_finset ws).symm ▸ hl')
      simp [allowedNext,done,cold]
  unfold rootClosed at root
  have bad := List.all_eq_true.mp root ws (List.mem_sublists.mpr (List.filter_sublist ..))
  change ws.length ≤ cap + 1 at sz
  simp [sz,cuts_full hg hl',fits] at bad

def rows : List W := [0x2dbbdbdda1050252a606a40988bee131b8da6a1b505d3d7c17f35df6ff75bdd53eb3,
0x36dd6d6ec22624631bc7038adcd35e2471f06564cc37ca83fcbde67f0febc2eacddc,
0x38ee7e77f448488400284874230000c8000500802320f69be2de7a09a0da7e83906f,
0x3f0f8f87187070f818405b844be15ee9aa509d6d615a91e65996c59efb64e13efbc2,
0x3ff00ff81f807f002da023077609b08e472293229b5f09048ced976d5d0b557e45b6,
0x3ffff0001fff800036507c879406234c172d745493630af81f0895d61a6cdae8eb26]

inductive PackedBlocks where
  | leaf (index value : ℕ)
  | fork (index pivot : ℕ) (left right : PackedBlocks)

def PackedBlocks.byIndex : PackedBlocks → ℕ → ℕ
  | .leaf _ value, _ => value
  | .fork middle _ left right, i =>
    if i < middle then left.byIndex i else right.byIndex i

def PackedBlocks.byKey : PackedBlocks → ℕ → ℕ × ℕ
  | .leaf index value, _ => (index,value)
  | .fork _ pivot left right, k =>
    if k < pivot then left.byKey k else right.byKey k

structure PackedSeq where
  size : ℕ
  width : ℕ
  mask : ℕ
  blocks : PackedBlocks

def PackedSeq.inBlock (xs : PackedSeq) (b i : ℕ) : ℕ :=
  (b >>> (i * xs.width)) &&& xs.mask

def PackedSeq.at (xs : PackedSeq) (i : ℕ) : Option ℕ :=
  if i < xs.size then some (xs.inBlock (xs.blocks.byIndex (i / 32)) (i % 32)) else none

theorem PackedSeq.at_bound {xs : PackedSeq} {i key : ℕ} (h : xs.at i = some key) : i < xs.size := by
  by_contra bad
  simp [PackedSeq.at,bad] at h

def searchBlock (xs : PackedSeq) (value key : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | n+1, lo, hi =>
    if lo < hi then
      let i := (lo+hi)/2
      let x := xs.inBlock value i
      if x = key then i
      else if x < key then searchBlock xs value key n (i+1) hi
      else searchBlock xs value key n lo i
    else lo

def findKey (xs : PackedSeq) (key : ℕ) : Option ℕ :=
  let (j,value) := xs.blocks.byKey key
  let bound := min 32 (xs.size - 32*j)
  let i := 32*j + searchBlock xs value key 6 0 bound
  if xs.at i = some key then some i else none

theorem findKey_sound (xs : PackedSeq) (key i : ℕ) (h : findKey xs key = some i) : xs.at i = some key := by
  unfold findKey at h
  rcases selection : xs.blocks.byKey key with ⟨j,value⟩
  rw [selection] at h
  let k := 32 * j + searchBlock xs value key 6 0 (min 32 (xs.size - 32 * j))
  change (if xs.at k = some key then some k else none) = some i at h
  by_cases found : xs.at k = some key
  · rw [if_pos found] at h
    exact (Option.some.inj h) ▸ found
  · rw [if_neg found] at h
    cases h

def encodeBank (dict : PackedSeq) : List W → Option ℕ
  | [] => some 0
  | w::ws => do
    let i ← findKey dict (w.toNat >>> 206)
    let tail ← encodeBank dict ws
    return 4096 * tail + i + 1

set_option maxRecDepth 16000 in
def expanded : PackedSeq := ⟨1655, 270, 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, .fork 26 0x36fff00007ff800036507c8394062344152d645492230af81f0894d60a6cdae8eb24 (
.fork 13 0x92000001d8000002400200500002008060010001340000000001100100010000022 (
.fork 6 0x201000058980002410240100042100040d00101200001802001000000018000020 (
.fork 3 0xfffc0007ffb09a703086bf9dca3e8d28b2b6c1cd107e0f76229e583251614d8 (
.fork 1 0x422400048840028007023000080000000802000c003e0042209008200020048 (
.leaf 0 0x10890000908426040c0101047001000004803003000f80108824020800080120000042000007d0009a00300620110824000812008000000800402090002000200000000101c0001c3e020000c012f857286a14224a580024009005900228000800841000000402000070a80800030043411c8000008120200080024004000800000002004000000e040001c3e020000c012f857286a14224a58060441000080003840084504200000029120000210800080000028801188020a0b0008350400420800e0102515100100000a4000016c000080000088220208000a080800200410010000010000145000000000281000050980000000003200081880088092008110400020000e00021141000000008448001221000a001c08c000200000002008000d000010820028040900440040000188000037780980030048e9dc23e8528b2b481c010400210020450101140490000006200000dd4a261a0c2122e740cfa34a2cad2070041000840081140404501240000018800003700098003004009900240028322081c010400210020450101140490000006200000d1ec261c0c2123c57087a34224a5307004100084008114040450124000001880000327a8806830848f9dc31a8d28b2b401c01040021002045010114049000000620000099ce261e0c2123e770c7a3482cad30700410008400811404045012400000188000002528006800808b8c031a8d20a0b401c0104002100204501011404900000061c0000c3e020000c0127857086a14224a580624419004900038400845043000000180000030780800030048e15c21a85089294018010400000000410001140080000004200000918c261c0c2123457081834004813050000000840080140400001240000007800000f0001a0000020088002400202020804000080610221040304000410000001c38000201000a001c08000000000000200000190068100a8040248100400240000068c00004030187000800100000408000000c044001a0212221048300000418000001628000080a001a0020006200400208080800109000018420801044100410440000007e00000840008007001000000000000802000f40360126800a090200110490000001c000003e00000000027813086a140202580024009004900028000800041000000006c00000630007000808d04c2020d000004400c00360106000008000000048000000168000014a001a002022c100c6a34020250000d0000049200280408004400400000001cd88000001058040000004806051000030000000000000000000000000000000000720164000080001088000228180240000c0000000000000000000000000000000001850508800005804030000c8020090002100000000000000000000000000000000005121221000a121d08c000320001402008c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (
.fork 2 0xf87c00070fb080703084bf15ca1a8d089296418d10760966008e180211610c8 (
.leaf 1 0x3e1e8001c3ea201a0c212fc572c6a34224a58062d419025920238440845c43040000f87185070f808005b044be15ce9aa5099296118910640964008e100211610c000003e1c0001c3e020000c012f857286a14224a580624419025900238400845843000000f87000020700800030048e15c21a85009294018910640964008e100211610c000003e140001c14020000c012a854286a14224a500604410025900238400845842000000f8000007078080003004ae15ca1a8508929401801040084000841000116008000003e000001c00020000c01080442000002048000600410021000210400045802000000f7fe0006ce709af03786bd15ca060d001a06c14f403e0f76a29a593240314d9000039df8001221000a001c08c000200000002008003d00f8359a8268248900c41240000e70000048000020000022000080000000000000000080c402090002040200000000381c00010200000000000c0002000000000080024009025900228000800841000000deec000347b0987030848f15c21e8d089294c1cc107e0b562294583011604d8000037bb000099ce261e0c2123e770c7a3482cad3073041f82d588a5160c045813600000d86000030780800030048e15c21a850892940188106409440084100011600c0000035bf800091ce261e0c2123c570c7a34024a53053d00f82dda8a6964c800c53640000d6fc00024fb0987030849f15c21e8d009296c14d003e0b76229a583200214d8000035bb0000918c261c0c2123457081834004813053000f82d588a4160c000813600000d68000024000980030040011000400001200814000080a502290503000204900000341c000083e020000c0127857086a14024a580424009025900228400800843000000d06000020600800030048c15c202050012040108002409440080100000200c00000319b000000000000000000000000000000000003000f825188240208000801200000bdda00037528986830848b9d033e8d28b2b481c350400f34820e5112515149100002f768000c9ea201a0c2123e770c6a34a2cad0070d41003cd20839444945452440000bdda00026738987830848f9dc31e8d20b2b4c1c350400f34820e5112515149100002f768000094a001a002022e300c6a348282d0070d41003cd20839444945452440000bd800000200000000000008800000020202001c010400e1002045010514049000002e140000c1e020000c0123857086a14224a500604410024900038400845042000000b85000000500000000008a04021a85008094018110400924000e1002114108000002956800000000000000000000000000000000000d00003492002804090044004000094c80000042000600080890402020d000004014000000b14020050100000490000016080001c3e020000c012f857286a14224a580620419001000210400045803000000422400048840028007023000080000000802000c003e0042209008200020048) (
.leaf 2 0x3ffe8001ffea269a0c21afe772cfa34a2cada072d41b03dd28a7944c945c53440000fff00007ff809a003006be9dca3e8528b2b681c9106c0f74229e503251614d000003ffb0001fd8c269c0c21ab677289834a0c893073041f83d588a5160c145813600000ffda0007f5289a683086ab9d0b3e8d28b2b481c350480f74a29e5132517149100003ff68000994a261a0c2122e740c7a3482cad2070d41203dd28a7944c945c52440000ffd00007f5009a003006aa9d0a3e8528b2b481c110480f74229e5032516149000003fe00001fde026800c01aba7728fa14a2cad20700412039408a5140c145812400000ff800007f5289a683086ab9d0b3e8d28b2b481c010480e5022945030516049000003fe00001fc0026800c0188264209000a0c8820700412039408a5140c145812400000ff7e00078fc082803706be15ca1a85089a96018f507e0d66a09e192251710c900003fdc0001e3e020800c01af857286a14224a58062441b035908278408945843000000fefc00074fb098703084bf15ca1e8d089296c1cd107e0b76229e583211614d800003fbf000091cc261c0c2123c57087a34024a53073441f82dd88a7960c845853600000fef000074f8098003004be15ca1e8508929681c9106c0b74229e503211614d000003f9f0001c3e020000c012f857286a14224a58063441f825988278608845843200000fdfa00072fa880683084bf9dcb1a8d28b2b601cb50640f74828e511251714d100003f7e800089ca201a0c2123e770c6a3482cad0072d41903dd20a39444945c53440000fdf000072f8080003004be9dca1a8528b2b601c910640f74028e501251614d000003f768001c94a201a0c212ae742c6a34a2cad0070d41003dd20a39444945c52440000fd7a00070f8080003004be15ca1a85089296018b50640d64808e110251710c100003f3e0001c3e820180c212fc57286a34224a58072441902dd00a39404845853400000fa7400078fc082803706be15ca1a85089a96018d107e0966209e182211610c800003e9d0001d3e426040c012f857287a14224a5b063441f825988278608845843200000fa700007df809a003006be15ca3e850892968189106c0964209e102211610c000003e5c8001e3f020a00dc1af857286a14226a58062d419035920238440945c43040000f97200072f8880083004be9dcb1a8528b2b6018b50640d64808e110251710c100003e5c0001efe020800c01afa7728ea14a2cad80624419035900238400945843000000f8f000077f8098003004be9dca3e8528b2b681c910640b74028e501211614d000003e3c0001d3ec261c0c212fc57287a34224a5b072441902dd00a39404845853400000f8f000072fa880683084bf9dcb1a8d28b2b601c910640b74028e501211614d000003e1f8001c3f020200dc12f857286a14226a58063d41d8259a0238640845c43240000f87c00070fb080703084bf15ca1a8d089296418d10760966008e180211610c8))) (
.fork 4 0x9400480040042020600088892402030d060004000000010104012026080800800 (
.leaf 3 0x10800901200210002121c0040001000014020080830a0d800080000200080201200042002402200211041008000400e00000004440420c283600020000080020080480010800001ea000041416200000009000014111000800a00000000000000080200000040f87007070f818405b804be15ee1a8508d6d6018918640964008e100211690c00010000801c002a041016200050039000000111080020209000000000000000201000029001200100108000840000240111880808190000347803020880a01428013201000a400001660000004170000010050000340040000001e00c0002000010200088000028001005000980000580001200041880008092000106001020080a004200032000008400481200210002121c004000100001402008000d060080820028040a00440040018000003780529256948888b64331b8d86c5d4000006011000092022480002a000006000000de00004940520200180c0040219150000001804400024808920000a80000180000036007b1247108888f24e21b8d06c4d4400006011000092022480002a000006000000d401ea491a522223d93cc6e361b175000001804400024808920000a8000018000003000781040108008e04e21a8500c4d4000006011000092022480002a0000060000009c01ce491e122223d93cc6e361b175100001804400024808920000a8000018000000500528206840888b64131b8d868194000006011000092022480002a00000400000098018c491c022223493880c341911110000000400000480882000020000007000e0080004000800700000000000050080002066192200280000900a8100090001c000003e0000084010020018040040358040008008600800000000002a0000000006000c00600030207000880120000108060000420420120002000008002800008000140028014000a081a1022005804404221804000009060080020000040220400040000fffe0007ffc09a803706be9dca3e8528bab681cf507e0f76a29e593251714d900003fff8001ff5a26ba0de1aee742cfa34a2eada073d41f83dda8a7964c945c53640000fffe0007f8409a8037063099082400283a2281cf507e0f76a29e593251714d900003fff8001fdce269e0c21abe772cfa34a2cad3073d41f83dda8a7964c945c53640000fffe0007cff09af03786bf15ca1e8d089a96c1cf507e0f76a29e593251714d900003fff8001ebfa20ba0de1afe772c6a34a2ead8073d41f83dda8a7964c945c53640000fffe00076fb898783084bf9dcb1e8d28b2b6c1cf507e0f76a29e593251714d900003fff8001bbde26be0de1afe772c7a3482eadb073d41f83dda8a7964c945c53640000fffe0004ad6802e80782bb8c0b1a8d20a8b601cf507e0f76a29e593251714d900003fff800099ce261e0c2123e770c7a3482cad3073d41f83dda8a7964c945c53640000fffc0007ffb09a703086bf9dca3e8d28b2b6c1cd107e0f76229e583251614d8) (
.fork 5 0xfd007a02500729246848888f64f31b8d86c5d4000b4fa53124892a274a881ba41 (
.leaf 4 0x3f401681d4014a491b722222d90dc6e361b1750000d3e04c49224a89d2a206e80400fc007807400fa1246588889f24e61b8d06c4d600090e251124092a264a080ba40003e3e1c01c1c3e061016e012f857b86a14235b5806247994659026b8d92845aeb0000f8007007600fb1247588889f24e61b8d06c4d640090e251124092a264a000ba40003e001c01d403ea491b722227d93dc6e361b175800243894449024a89928002e90000f8007007000f81040588009e04e61a8500c4d600090e251124092a264a000ba40003e000001c00000410162000000090000001110000003804400024809920002a80000f7007e06e00e7124f48f889d24e6030d564c46420f69b72126812a2f0aa8198490039fe1f8121c3f020212dc12f857386a15626a580e3de7d8a59a0238740ae5e432400e7e77e048488400284870230000c0000500802020f69be2d66a09a0d22e8390490039c01f81200210002121c004000100001402008083da6d8849a0028340aa06412400e700000480000000048000000004000050000002002980200000000400a80800000383e1c0101c3e020012c012f857386a14224a580624619025900238500845a430000e0007004000800000480001000040000000002000908240124000a040200090400037801b00d801ec491c422223c93886e341b13510830b8dc44182480b920a02a92000de006c02700739247848888f64f31b8d86c5d4420c2e37110609202e48280aa480035b5bb0098918c6f1c0e23234d7881c341959130d30a0fc2d588ec1f8e0a0a336000d6007e02600739247808888f24e31b8d06c4d4420f68370126812a2f0a28198490035801f009803ec491c022227c93886e341b13590834a0dc049804a8b828a02612000d6006c02600631247008888d24e2030d064444420c2837010601202e082808848003580000098000049000202000808004001911000800a004000004809820a02200000d0006002000601040008008c04e202050044440008082501040120260800088400031801b0000000000000000000000000000000000830a0d8041800003000a02012000bdbdda00502528206840888bec131b8da6a1b401c357c13f348b2e775ad953e91002f401680de014a495a522222d90cc6e361b1750000d1e04c49224a89d2a204e80400bd005a035007a9246948888f64f31b8d86c5d4000347813124892a274a8813a01002f4016809c01ce491e122223d93cc6e361b1751000d1e04c49224a89d2a204e80400bd005a00500528206840888b64131b8d868194000347813124892a274a8813a01002f400000140000080010020018040040218040000001e04c00024809922200a80000b8005000000500000000008a04021a85008094000106011124092a264a0003a0000294016800000000000000000000000000000000000d060084920028140a2044004009400480040042020600088892402030d060004000000010104012026080800800) (
.leaf 5 0x80004016002c00908080048022800810080808480000000100400000005000008001000080387870027902403940ea106552a62129805080004210060040100400410004000200e1e080a985a902e507a845056a9884a4014200010840180100401001040010000803850702a786a40b941ea11655aa62129805080004210060040100400410004000200e001c009600800c502280191488080a6014200010840180100401001040010000803070603a787a40b941ea11451aa62129c05080004210060040100400410004000200818100c0e1c002a50480011468180023014200010840180100401001040010000801050202a606a409801ea110108a62121005080004210060040100400410004000000e1e00009840900e5018841054a18042400420001000010000000100000000ffff8007fff001bf05f80e20f93c2500fe776083c03fc93e502bb47678f96ae90003fc01f81fe035a497b73e226d90dc6e375b3758083dbedcc49a24a8bd2aa06e92400ff007e07f808412585cf081060340100d64d42020f6fb73126892a2f4aa81ba49003fc01f81fe01ce495f722223d93dc6e375b1751083dbedcc49a24a8bd2aa06e92400ff007e07e00ff124f58f889f24e61b8d56ccd6420f6fb73126892a2f4aa81ba49003fc01f81f403fa493b73e227d93dc6e375b3758083dbedcc49a24a8bd2aa06e92400ff007e07800fc104858f009e04e61a8550ccd6020f6fb73126892a2f4aa81ba49003fc01f81dc03ee491f722227d93dc6e361b1759083dbedcc49a24a8bd2aa06e92400ff007e06f00f7924fccf889f64f71b8dd6cdd6420f6fb73126892a2f4aa81ba49003fc01f8134035a083b31e226d905c6e375a2658083dbedcc49a24a8bd2aa06e92400ff007e02700739247848888f64f31b8d86c5d4420f6fb73126892a2f4aa81ba49003fc01f01fe03ec495d722227d93d86e375b17590834bedcc49824a8b92aa02e92000ff007a07f80fa9256dc8889f64f71b8dd6c5d6020b6fa53124892a274aa81ba41003fc01c01fe03e04941720227993d86e175b17580824be94c49024a8992aa02e90000ff006c07f806312575c8888d64f6030dd64544420c2fb7310609202e48a80aa48003fc01681fe014a495b722222d90dc6e375b1750080dbe04c49224a89d2aa06e80400ff005a02700529246848888b64331b8d86c5d402036f813124892a274aa81ba01003fc00001fe014a495b722222d90dc6e375b17500800be04c00024809922a02a80000ff000007f800012505c8080060340100d6454002002f81300009202648a80aa00003f801f01d803ec491d622227c93986e341b13590834b8dc449824a8b928a02e92000fe007c02600731247008888f24e21b8d06c4d4420d2e371126092a2e4a280ba48003f401e81d403ea491b722227d93dc6e361b1758002d3e94c49224a89d2a206e90400fd007a02500729246848888f64f31b8d86c5d4000b4fa53124892a274a881ba41)))) (
.fork 9 0x6110108022624631bc7038adcd35e2471f06564cc1708001c2184760f2180684d90 (
.fork 7 0xee7077e44808840028487021000040000500802220f69be25a7a01a0da3e81906d (
.leaf 6 0x381ffdf9021e3f020a00dc1af857286a15626a588e3dc7f8b79e8278668fe5c43b40e07e77e40848840028007023000080000500802220f61be2de7a09a09a3e83106d0381c1c39020201000a001c08000000000140200088198668920e80402687a0400b40e0700004080000000000000000000000050000022002180208100000081a800024038001c01000200000800000800000000000000008000002012048040028500000900dd606ec226046313c7008a9cd24e2471f06444cc25ca83f439627306eb82c08c5c0341bfbf0819d3ec2e1c0c2b7fcd7297e7c3a4a7b0f76c1f92fd89a7962c8f5853700d06fefc20624730b87030adcf35c25f9f06929cc3ddb07e4bf6269e58b23d614dc0341b5bb0818918c2e1c0c2b734d7091c7c1848330d7280f92f589a4162c0b0813700d06068c3070603a787a40b941ea11451aa62129c254a01a4292261048b02c0041c034181a30818100c0e1c002a50480011468180023095280690a48984122c0b0010700d060000206000002000002940200041120600080210a0004080040000802c00004034001a0080010000600000850000011048000022014200210a40984102c010010500c06060c000000000000000000000000000000000204201a0082201008a0280000c02ef41768414094a981a902622fb84c6e369a86d4014f1e05dcd63ca99d6f304f8c40b05fdfa10572faae06a709cbfffdb1b8daeb3b701dbd1e46f75868e5113dd714f102c16f768414094a981a902622fb84c6e369a86d4074f4701bcd61839444f75452c40b05058a3878202a616a40b941ea11415aa621290052c180661186004111cc1043102c141628e141c0a9e1a902e507a845956a9884a6014b060198461801044730410c40b05058a3070603a787a40b941ea11451aa62129c052c180661186004111cc1043102c141628414080a981a9026007a8440422988484014b060198461801044730410c40b05000010500002600240180062100100860101001081806001040000018c0002002c001600400080090008004002280000008080840142000118441801004510010c00a05050a0000000000000000000000000000000000024180240180000101c8100210241012200100008081800220048000042018000001420001084018010040300104004020204408080400280070200000000005008002204201a0082201008a0200000c010080810808100406040008500000110480000230810806802088040228080000300402000068a80000010000214000004052500008220020000080000000802000004010000801a00340006800008d0000019148000022800000200200804002800000010020101024080804002800702000000000050080020024180240180000101c010021008040408404080290029004003284400028084840009060090060000040700400840201000058980002410240100042100040d00101200001802001000000018000020) (
.fork 8 0xf07078e7880f0425a820733408a006452702829a256e19a6693a61049b1ec1043d (
.leaf 7 0x3c1c1e39e1c3c0e9e9e902ed07a845956a9884a7895b86699a4e984126c7b0410f40f07078e70f0e07a7afa47bb41ea11451af62929e256e19a6693a61049b1ec1043d03c1c1e39838301c0ebc01ead0480011469582023895b86699a4e984126c7b0410f40f07078e50d0a06a62ea479a01ea110108f629212256e19a6693a61049b1ec1043d03c1c1e38c1c180e9e1e902e507a845146a9884a7095b86699a4e984126c7b0410f40f07078c78f8f0327b7240bb41ea10655af62129e254a19a6693261048b1ec0043c03c1c1e29e3e3c0a9eda902ed07a845956bd884a6894b86219a46984106c7b0410d40f07078078f8f0027b02403b40ea106552f62129a250a1886691261040b1ec0043403c1c1c39e3e201098e091ced018841054b582424885b8669920e90402687b0400b40f07068c78f84032797240b9416210455ad60109e254a19a6293261048b1ac0043c03c1c1629e3e080a985a902e507a845056bd884a4894b86019a4618010647b0410d40f07058a3070202a606a40b941ea11411aa621290252e180669186004191ec1043503c1c1601e3e08009840900e503a841054bd884a4894286019a4418010247b0010d00f07010278f8200a610a403940ea114152f621292212e180648184000181ec1002503c1c0401e3e2c0098c0900ed03a841854bd884a488428601920410000207b0000900f07008078f870027902403940ea106552f62129a250a180629106004091ac0043403c1c0201e3e080a985a902e507a845056bd884a4894286018a4418010246b0010d00f07000078f80002610240394062104152d601092210a180608104000081ac0002403c181e31e183c0c9e9c802ed06a80195689880a7895280691a4c984122c5b0010f00f05ffda7857f52afa6a70bfebff1b7fdfaeb3bda1d3d1c86ff5a69e51b3dd714b503c141e29e143c0a9e9a902ed07a845956a9884a6814b06219a46984106c730410d40f05078a3050602a786a40b941ea11451aa621298052c1886691a61041b1cc1043503c141e01e143c009e80900ed03a841954a9884a6814206219a44984102c730010d00f05058a7850202a606a40b941ea11415aa621292052c180669186004191cc1043503c03ffc1e01ffe0b6808c0dffa7f29fb5ca2cafe876641b13fd49a7942cd55853d00f00ff807807f002da023037609b086452283229a1d090484ed1269450b155604b403c001e01e1e3c009ec0900ed03a841954a9884a6814200211a44984102c510010d00f0007807850f02a7a6a40bb41ea11655aa62129a05080084691261040b1440043403c001e01e003c009680800cd02280191488080a6814200211a44984102c510010d00f0000007800000240020031400200405200000920108000408104000081040002403b9f9df9121221000a121c08c000300001402008883da6f8b79e8268368fa0e41b40ee7077e44808840028487021000040000500802220f69be25a7a01a0da3e81906d) (
.leaf 8 0x18440000089800004900020a5008081044819112000c200070021158288201a124006100ff802007f0009a003027609908641228322881f09048ce5866d4d03057e4590184006200800dc0026000c0950264019048a0c8a207c241030861191340405f11640610010802002400098003025401100441200120881708000c2184640d0100684590180404000080818061000e01230578808140159100480000600210582c8200a126005b1d1d8a1050252a606a40988bee131b8da6a1b505d2d7c17611df65f359dd52eb1146f46368414094a981a902622fb84c6e369a86d4174f5f05ccd37dbfdd6a754fa445118bdda1050252a606a40988bee131b8da6a1b505d3d6415f34df6ff35a5553e91144606200414094a981a902622fb84c6e369a86d41742590548417d97c960550ba4051180000105000026002401800621001008601010410860150005d61a2480402a00144006200400080090008004002280000008080841742410108415917404055012405018180000000500000000008a04021a850080940580164110005965b2481142a8010440420001001080818002222490080c341800100542000508411d83c860100324020ff0000aff800012505c8294060344172d7454802202f81b00809202648aa8eb00080600002ade00004940520a50180c105ca1d1520008018064020248089200a1ac0020000000ab280001050108214000204072014448002000008008000000000284100080000002a00d40026000c09500440191c8244822008000020020000000000a104002000000083030281840138040411e00020095640002000008008000000000284100080000000888908467040e0951047811048015923008000020020000000000a1040010080800810101800001000002000018a009809004801640100018050040114220004020200040408429002900400b284462028286c412005900400060140100450880010080000991800024103401000421000608101010400060010001801004000022000400020026004c009000800400228008180a480841200410000004014000045000000fff00007ff800036507c8394062344152d645492210af8170810d2026c9ac0aa2403fe01fc1fc03fe0d781e20cf7a3b99fb5c8393fe816638b55ed4bce99bed102f9d00f07fffe3072673af87a70bdcfffd35f9fa6b3bdc3dff1fe6ff7a69e59b3fd714fd03c1fe1c1e3fc3e0b8409c0f7f9df696f5f7a4e7c8e66c791a7941238420ef5843900f07078e78f8f0427b82473b40ea106552f62929a256e19a6693a61049b1ec1043d03c1c1e39e3e281a98fa91eed07a845056bd8a4a4895b86699a4e984126c7b0410f40f07078e78f8603a797a40b941ea11455af62129e256e19a6693a61049b1ec1043d03c1c1e39e343c1a9eba91eed07a845956bd8a4a6895b86699a4e984126c7b0410f40f07078e7880f0425a820733408a006452702829a256e19a6693a61049b1ec1043d))) (
.fork 11 0x71180080bb78202b656b48b941ea31417aa7656904708601d2185f61e2580686f10 (
.fork 10 0x70b8185083030781840138048e15e21aa509d6d405a11641912c596fb64a13c7b80 (
.leaf 9 0x1c16060821c0c3e061016e0127857986a94275b5816a0799640216596c9204f3af007038181087030f818405b8049e15e61aa509d6d605a116419028596fb24a13c7b801c063fdfa0c1e3f061a04fc1af857a86a94277b5816bd59fe75bbe7feeda94fdef247018f87083070f8184013804be15ea1aa509d6d605a91665996c59efb24a13e7bc01c063e0020c1c1e061004e012b857a86a94275b501680590661216796c9204f9ae007018deec830347b19c7138848f15e21ead09d6d4c5ec167f9b5e7bf5fa7813e6fd81c06361820c0c1e061004e0123857886a94275b5016a0599665316796c9204f9af007018b85083030781840138048e15e21aa509d6d405a11641992c596fb24a13c7b801c06160820c1c3e061004e012f857a86a94275b5816a0599641216796c9204f9af007018381083070f8184013804be15ea1aa509d6d605a116419028596fb24a13c7b801c06062020c0d1ec671c4e2123c57887ab4275b531780590648616d97c9604f1be407018187083030f81840138049e15e21aa509d6d605a91665912c596fb24a13c7bc01c06060061c1c3e061016e112f857ba6a94275b585680590640216596c9204f1ae007018180083030781840138048e15e21aa509d6d405a0164190085965b24813c6b801c06060020c0c00061004e01000448000802559001680590640216596c9204f1ae007018180083000501040108008a04221aa501c4d405a0164190085965b24813c6b801c06060020c0000041004200000008000800511001680590640216596c9204f1ae007018180080030500800030048a15021aa509929405a0164190085965b24813c6b801c060600008081c061000e0123857886a14035b501680590640216596c9204f1ae0070180800830101810401080002002018a009c4d004a0164190085965a24813c6b001c06020020c040004100420000000800080251100128059064021659689204f1ac0070180000ab2800010501082140002040720144480420060190085961a2480286b001c06000026c60000d140d20400108c00182051504108018064021658689200a1ac0070180000837800012501480800603001208745400420060190085961a2480286b001c06000020c000004100420000000800080051100108018064021658689200a1ac00700018008003000080003004001100002009120005a0104080085045900013c41801b4585a30898918c6f1c0e2b734d7891c7c1959330dd2806f0a699dc3eae0ba1367061ff000027f800012505c8294060344112d645480230af81f0084d60a648ae8eb001875843b0898918c6f1c0e2b734d7891c7c1959330df2a0df0c791d83f860ba33760611800002378000125014829406030411286454800308601d0084d60a2480686b00184435bb0898918c6f1c0e2b734d7891c7c19593305f200ff2d799fc3e8e01a937606110108022624631bc7038adcd35e2471f06564cc1708001c2184760f2180684d90) (
.leaf 10 0x1c4600007ffe0000d941f21e50188d305cb5d1524d0c218074021758689201a1ac0071180000bb78000365034839406230417287454904308601d0085d61a2480686b001c4600002ec00000d100c20c500088101c805112410c218074021758689201a1ac0071180000b850000260024039406210417287010904308601d0085d61a2480686b001c46000028d800004900420a500808104c81d112010c218074021758689201a1ac00711800009350000364034818006230012087454104308601d0085d61a2480686b001c4600000c9c0000d900920e50188c1044a19152410c218074021758689201a1ac0071101880ba637633fc7238bdcdbfe2677f2f766dc5f09041c2185765f21817c4d901c4206202e46dc00b640dc0d5036c4191caa4cca617c259034861791741405f19e407100fffeb807f842da823737709b086472293a2b85ffd07ecf7ef6dfd93257f55d91c403fe02e01fc00b6808c0dd826c2191c8a4c8a617c241233961db5740c15f916407100f880b8077002d8023035609b08647229322985f09040ca5856c5d01017e45901c4037a02e00dc00b6008c0d5026c0191c8a4c8a617c241232961db5740c05f916407100bd80b8037002d8023035409b00647229322985f09040ce185645d01057c45901c4016a02e01fc00b6808c0dd826c2191c8a4c8a617c241230961db5740c05f9164071003980b807f002da023037609b08647229322985f09040c6185645d01057c45901c4007e02e00fc00b6808c0dd026c0191c8a4c8a617c241231861d95740c15f1164071001881f807f002da023077609b08e472293229b5f09040c2185645d01017c45901c4006202e00dc00b6008c0d5026c0191c8a4c8a617c241030861591740405f1164071001880b800200240020031408a00407221202905f09040c2185645d01017c45901c4006202800d00026000c09500440110c824482217c241030861591740405f116407100188090032002c0023014009b00002029322105f09040c2185645d01017c45901c4006200c009800b6008c0d5026c01104880c8a617c241030861591740405f1164071000000b800000240020031400200407201000904308000c0085441800006841001c3fc61fa1e0c3f061216fc127857986a95677b581ebdffdec4bb65befd2aef7ef2470ff000087f800012505c8080060340120d7454006202f81b0085961a648aa8eb001c3e3e1c21c1c3e061016e012f857b86a94275b5816a4799665b167bed9284fbef0070f8187087030f818405b8049e15e61aa509d6d605a91e65912c596fb64a13cfbc01c3e060021c0c1e061016e0123857986a94275b501680790640216596d9204f3ae0070f800008700000104058800000024002001444004200e0190085961a648028eb001c36061820c0c1e061004e0123857886a94275b5016a0799644316596d9204f3af0070b8185083030781840138048e15e21aa509d6d405a11641912c596fb64a13c7b80)) (
.fork 12 0x7b1d0000bb78000365034839406230417287454904308781f0095d61a2498e86b20 (
.leaf 11 0x1ec007602e00dc00b6008c0d5026c0191c8a4c8a617c241031865591740455f116c0751a0000fbf80003650348394062304172d745492630a601d0885d61a2c82686b041d4006a03e00fc00b6808c0dd026c0191c8a4c8a697c241230a61d95742c05f1165073190000fbf80003650348394062304172d7454924308781f0095d61a2498686b201cc006603e00fc00b6808c0dd026c0191c8a4c8a697c241031865591740455f116c071ff007ebff808436587cf395062344172d74d4b063fefb7f12edd6baf4aae9fb491c7fc0002ffe0000d941f20e50188d105cb5d152418c2be07c02175869922ba3ac0071f80000bf7800036507c839406234417287454904308e01d0085d61a648068eb001c79c63faf20de10b621adcd5426c1191c9e4e8ae1fffe7db8cfb593f744aff7576471de0000bb7800036503483940623041728745490630ae01d0085d61a6482e8eb001c6f40002ede0000d940d20e50188c105ca1d152410c21e07c021758699223a1ac00715a0000bff800036507c8394062344172d745490630ae01d0085d61a248268eb001c4e40002ffe0000d941f20e50188d105cb5d152410c21e07c021758689221a1ac00711f0000bbf80003650348394062304172d745490630a781f0085d61a248ae86b001c4639dfaedf2210d9e0d3cedc188e105ca1d352c10ff18ff75bbf7eeada91aded2471181880bb7b7003fd03783d40fb306572af776985f09641d2185f65f25817c6f901c4606202ede99ceff5ede2f73fffcd7ffe9fdff717c2590748617d97c9605f1be4071181880bb78252b656b48b9cbee335bffa7e5fd05f09641d2185f65f25817c6f901c4606202ede0800d940d20e503a8c105ca9d95a417c2590748617d97c9605f1be4071181880bb037783dc033835ce9fe27ef729f6fd85f09641d2185f65f25817c6f901c4606202e9cddceff1e9e2f73fffcdfffebfdff717c2590748617d97c9605f1be4071181880b853752af86a70bdcbff137fffafb3bd85f09641d2185f65f25817c6f901c4606202cdcd9eeff1ede2f73fffcd7efebfdff717c2590748617d97c9605f1be4071181880a36347b1bc7138adcf35e25fbf0fd6dcc5f09641d2185f65f25817c6f901c46062024d4c9eaf91ade2723fffcc6eb6bfdfd417c2590748617d97c9605f1be40711818803272673bfc7a78bdcffff35f9fa6f7fdc5f09641d2185f65f25817c6f901c4606002edec1e0f940de0f739dfc96fde3f5f7416c2590740217596c9205f1ae0071181080bb7a4633fd7378bdcd77f2477f87574dc5708601d2185f61f2580686f901c4602002ede4c00d940d20e503a8c185cabd95a412c259074021759689205f1ac0071180080bb7870037d03483940ea306572a7656984708601d2185f61e2580686f101c4600202ede100cdf5cd22e50588c115ea1d152711c2180748617d8789601a1bc4071180080bb78202b656b48b941ea31417aa7656904708601d2185f61e2580686f10) (
.leaf 12 0x243e0a1c61c143e0410162102f813ba6a9427135852247994449064bc9928452e9089028f87185070f808005b044be15ce9aa5099296158916641964188f104211632c2240a0a0461414260000160100c800326280260248520459004080603c0108450c8089028281000000100000000000200001880008090048116401020180f00421143202240a00006140000000016010000001200800400005000180040006004010000088089000f87180070f8080003044be15ca9aa5099296158910640964108f100211610c224000a006001400000000010080002200802400005200410000004014000045000088e27271f448488400284874230000c80005008023207619a24a3a01a09a3e81102f20b9c85fd121221000a121d08c000320001402008c83da6d8949e0028340fa0641ac8221f97344878fc08284b746be15ce9a85589a96318b51e42d65808e1103d1710e3208879dfd121221000a121d08c000320001402008c03d06f8b59e8268248f00c41ac82212113448488400284874230000c8000500802300341802421800a0103c01102320884844800000000000000000000000000000000000d060090860028040f004408c822100014480000000048040000004800050000030000180200100000001800002220800840500120000080001088000220000000000c000000010040000000500000888020f87104070f808004b044be15ce9a85089296118910640964008e100211610c22008080441010200000120100c0003200000000084004000000800028000800040087fff0000fff800036507c8394062344172d745492630af81f0895d61a6c9ae8eb241fc7c1c3befe2010d9e0d3ced0188c105cb5d352498db9e6fd22ff5c6afa7ba5acb47f1f0000fbf80003650348394062304172d745492630a781f0895d61a2c9ae86b241fc601e03ede3c00dfc0d20ed03a8c195ca9d95a691c218275a65fdc78be51a1bcd07f180000fb78000365034839406230417287454924308601d0895d61a2c90686b241fc1c7e3be20fc10b6a08dcdd026c0191c9e4e8a69fdbc76b9a6fd95766c7ff516f47f00ff80f807f002da023037609b086472293229a5f09048ced976d5d0b157e45b41fc007e03e00fc00b6808c0dd026c0191c8a4c8a697c241231a65d95742c55f116d07f001880f8037002d8023035409b006472293229a5f09040c2995645d09117c45b41f87c7c3b0e0e1f061a04fc1a3857886a95677b509e99df6ed22fe5d6efa7ef5aeb47d1e068cbb7840337d7348b9416230457a874549c674a61bd29a7f71eaf82e86f1c1f4780002ede0000d940d20e50188c105ca1d152418c29807422175868b20ba1ac107d001e80b8037002d8023035409b00647229322985f09048c2987655d0b017c45941ec74162aede080ad95ad22e507a8c505ea9d95a411cb1e07d8677d878d673a5bcc47b1d0000bb78000365034839406230417287454904308781f0095d61a2498e86b20))))) (
.fork 19 0x28ea7a75e408080400280070200000000005008002207619a2da7a01a0da3e81102f (
.fork 16 0x124424225a7274a919c15b8657411ecc43209564ad22c283e80ca209008a422ac14c (
.fork 14 0x9f2f0001fdf800026107c079406214c172d701093610a78070811c0100c1ac02226 (
.leaf 13 0x27c00be07e017c009680801cd82282391c8a480a6d34241211a44d85502c555010d89d2e2e9da56549b0387580e973200cddba0f809ad6d5b65a52b23e1f48f23d4361e26cb4b668414084a981a902600fa84466229a86c4134f5f01d8c6783d054f754d8cc92ff0001dff800036507c8580062348160d7454136002f81300119212649a80aa2224b58a5b76996d8cd99c8236ab6bbaa8db4bd9195da30e1dc141c4494b825e5221a892bd295a1050252a606a40988bee131b8da6a1b5048357c13525992f274bd953a23248a75bb7766918cb65dfc352355f5a19b7444c17d5301ef8ed5cea4561c60089be89229bdda1010252a406a40908bce131a8da0a1b505c357c03f359a0f5153d1536b3248a4a44f7676e1090e1f1d48c328728183e4a48cd20d5f00d086603c050f454c88c92292913dd9ca94a438fc75232ca1d98e0f1a9b3348357c03421980f0143d153223248a4a44f76608429043f01400b28566383c686c4d20d5f00d086603c050f454c88c92292913dd85b9c242878752328a0cb8e079a8b3348357c03421980f0143d153223248a4a44f7256e5290a3b1d48cb2876e383e6a6ccd20d5f00d086603c050f454c88c92292913d815b10a420a405222ca19b8e0a9a1b1348357c03421980f0143d153223248a4a44f5656a7290a3f1d48cb28766283e6a6ccd20d5f00d086603c050f454c88c92292913c58589c00285874232000c98a0598892348357c03421980f0143d153223248a4a44e5454a629003f0140cb28766282a686cc520d5f00d086603c050f454c88c922929135494a94a428ec75232ca1d9880f0a9b3348357c03421980f0143d153223248a4a44840408429002900400b284462028286c4120d5f00d086603c050f454c88c92292901dd9db0024307c05220ca1ca060f92121348017c0340118050041d142222248a4a04776742609041f0140c90872638366064cd2045f00c084603c010e450c88892292113dd9c88424387c75230421c8060d10903340347803421980b0143c013223248a4000776600009041f01400108520183440404d0001e00c0046004010600088889229000010100002400240100042100000800101040007803001180100418002222248a0a4477416e609081e0148ca2832e380a682ccd20459005084603c010d450c88892212913dc85b84242868752308a0ca060792823348351c02421900f0103d15102324803fe07601fc00b6808c158826c229180a4c886d70041203944ca5540c545812c89200f971d807bf82c2023056be9fcabae529b2b7358910640d65108f100351610e224800a4077216e1090a1a1d48c228328181e4a08cd2004100100440140005450008892002901d805b00242020052208a08a06029202134801040040110050001514002224800a4004000800900080040022800000080808412004100100440140005450008892000001d8000002400200500002008060010001340000000001100100010000022) (
.fork 15 0xff3f0001fff800036507c879406234c172d745493630a781f0895d61a2c9ae86b26 (
.leaf 14 0x3fc00fe07e01fc00b6808c1dd826c2391c8a4c8a6d7c241231a65d95742c55f116d8f3ff0001fff800036507c879406234c172d745493630af81f0095d61a649ae8eb223cce4844ffff2210d9e1f3dedc188f305cb5d352cd0cf1e07d0a775ae8d2f1a5ec8cf3390001fff800036507c879406234c172d7454934308781f0095d61a2498686b223cce40002ede0000d940d20e50188c105ca1d152410c21e07c025758689261a1ac88f3291881fd9b7002d907f07540db14e472f93329b5f097c0f2195e45d05197c67b23cc84e64ff21fe10b6a1addddc26c3391c9e4e8aed7cf470398e7593f444f5f556ccf3182901fb7db0036703487b60ea38e172af656934b09641d4095d65a24957c6b223cc600007ede0000d940d21e50188c305ca1d1524d0c218074025758689241a1ac88f300ff81f807f002da023077609b08e472293229b5f09048ce5976d5d03157e45b23cc00e607e01fc00b6808c1dd826c2391c8a4c8a6d7c241031865591740455f116c8f3003980b8037002d8023035409b00647229322985f09040c6195645d01157c45b23cc006207e00dc00b6008c1d5026c0391c8a4c8a6d7c241030865591740445f116c8f2393913c7878fc18685bf46be15ee9aa559ded635a357c1b429d96fb34bd3d7ba33c8e400077e60000d141f21400108d20183451504d0801e06c025658689260a1ac88f1380001bf7800036507c879406234c17287454914308601d0085d61a2480686b023c400e206e01dc00b6008c1d5826c2391c8a4c8a657c241030861591740405f11648f0f8387187070f818405b844be15ee9aa509d6d615a91e65912c596fb64a13cfbc23c0e3e1c61c1c3e061016e112f857ba6a94275b5856a4599665b167bec9284f9ef08f038381187070f818405b844be15ee9aa509d6d615a116419028596fb24a13c7b823c0e0e0420c0c1e061004e0123857886a94275b501684590640a165bec9284f1ee08f0382811870509810405884032002c98a009c4d214a116419028596fa24a13c7b023c0e060061c0c1e061016e11238579a6a94275b505680590640216596c9204f1ae08f0380001870000010405884000002480200144401420060190085961a2480286b023c060e0060c1c1e061004e112b857aa6a94275b505680590640216596c9204f1ae08f01828018305000104010840200028802009444014a0164190085965a24813c6b0238cc4c64d9b9b39c6fbd2ffbff4d7bb1c7d59793bc5cf060798e71dabcc6f1a576ccdb3d3d9a1050252a606a40988bee131b8da6a1b505d3d7c17631df6ff35bdd53eb334ef4e768414094a981a902622fb84c6e369a86d4174f5f05dcd77dbfdd6f754faccd339bdda1050252a606a40988bee131b8da6a1b505d3d7c17f35df6ff35bd553eb334ce4e648414094a981a902622fb84c6e369a86d4174f5f05d8c77dbfcd6f554facc9f2f0001fdf800026107c079406214c172d701093610a78070811c0100c1ac02226) (
.leaf 15 0x4910908959a9b29467a52fd9dd047b3104941792bc8b0a0fa0328824022908ab053124424224222242119c1038254411e04412005648c22c283e80ca209008a422ac14c491090807bebf40067c16e19d8044b391c9655922c880a0220320824002908ab041124424021efaf0a818505b8657411ecc07259564a3228282480c80080008422ac144491080007bea000041416218500009301c9451120c880a0020220000002108a30411244200002220000104000821400020401200444802202800808800000084228c104491010887bc1f6a067816e19dd047b391c825592ac0a020b20320824002900ab05112400ff81e807f0009a003067609908e472293228b1e010488ed8229450b453e4594490010807a01f40026800c19d80442391c8244822c08000220320824002900a9041124004200200240009800302540110044120012088020000880c8209000a402a4104490000007a00000000000018500000301c8040020c08000020220000002100a1041120ff000187f800012505c8480060348120d7454012202f81b0080920264caa8eb00483e101c61c1c3e061016e112f857ba6a94275b5840a4389645b026a899380abed0120f800018700000104058840000024802001444010200e0190080920264c028eb0048103e1c61c1c3e061016e112f857ba6a94275b5846a4619225b0023840184fb47012040402187070a818405b8443411ec80200956421028082480480080000402ac140481010080080808061000e010104780000001590000a020920120020000100ab0501204000018700000104058840000024802001444010200800800800000004028c100480010006001c00020000c1108044220080244800408000020120020000100a904010ee7477f448488400284874230000c8000500802320f69be25e7a09a0da7e83906d4391f9dfd121221000a121d08c000320001402008c83da6f8b79e8268269fa0e41b50e47472f448488400284874230000c8000500802320e69be24c3a09009a5e83806d4139d09fd121221000a121d08c000320001402008c83da6f8879a8268369aa0e41350442fa7544878fc08284b746be15ce9a85589a96338d387e09e6209e18a631690cc4110b9dfd121221000a121d08c000320001402008c83da0f8379a8268269980e413504424225448488400284874230000c8000500802320c283e00c2209008a4202804c411090890000000000000000000000000000000000830a0f803088240229080a0131044200014480000000048040000004800050000032002800008000000084200800441001080500120000080001088000220000000000c000002003008240029000800110040f87104070f808004b044be15ce9a85089296118918640964008e100611690c04010100841010200000120100c0003200000000084020209001000200001000a0100ff3f0001fff800036507c879406234c172d745493630a781f0895d61a2c9ae86b26))) (
.fork 17 0x165d652ec22624631bc7038adcd35e2471f06564cc37ca83fc3de67f0febc2eacddc (
.leaf 16 0x5954b5bb0898918c6f1c0e2b734d7891c7c1959330df2a0ff2f799fc3eaf09ab3771655252a422624631bc7038adcd35e2471f06564cc37ca83fc2da67f0fabc26acddc595094a90888908467040e09510478110480159230df2a0fb0b699b4362d09ab1771555a5aa554d4ad6a62eec7dabbee1f9b8df6a9b737dcbe7f52d27ff5fafc356aedc4bffc0007ffe0000d941f21e50188d305cb5d1524c8c2be07c22434809b36ba3ac912f470001fff800036507c879406234c172d745493230a980e08904000085ae8c1244bc03fe07e01fc00b6808c1dd826c2391c8a4c8a6c7c241233b649a5142d55f916d12f004781f807f002da023077609b08e472293229b0708008c6d9269040b546a45344b7591bb0898918c6f1c0e2b734d7891c7c19593309f2a0ff0f789ec1baf0bab35712d46d6ec22624631bc7038adcd35e2471f06564cc37ca83ecbde269058b42eac5dc4b5191ab0898908c6f1c0e2b514c781146819592309f2a0fb0b689a4122d0bab15712d4246a4222242119c1038254411e04412005648c27ca83ec2da269048b426ac55c4ad1516ae5d5caaaf91bfe370d7eff604a2bddd8c41eb269399661a0104573af15c5254242a422624231bc7038ad4531e0451a065648c27ca83ec2da269048b426ac55c493fd09ffbff221049e173dadc180f305cb5d3528c8bdbefec7baa6e8bfbaaafed3524ff0001eff800012505c869406034c172d7454832202f81b088092026ccaa8eb04493fc00009fe00004941720a50180d1044b5915200880be06c22024809b32aa3ac1124fa0001efa8000105058861400024c07251444832202e019088092026cc228eb044935909b0898918c6f1c0e2b734d7891c7c19593308b0a0fe073886c0bab0aab253124bd425be857d528ba6870efeb751bffff8f939cb0234789b1eca9ba27ee8ab7b05491680007bfe00004941721a50180d305cb5d1520c880b806422024808b308a3ac112442d6ec222246319c7038a5cd15e2461f00564cc36c283e8bde229058b422ac5dc4910af76fbea094a415b623872e309f6bfdc793f0cf8de1023ef208394659cf7565524424225efafd8419f85bf6770112ce472595e4ab22c283e80ca209008a422ac14c491090897beb221041e163d8dc000b301c9453128c8b0a0fa0328824022908ab053124424225efaa42119d15b8654411e4c472515648f22c283e80ca209008a422ac14c491090897be1f6b067a16fd9dd047b391c965792ac8b0a0fa0328824022908ab053124424225ec87d8409a84b76770110ce472591a0ab22c283e80ca209008a422ac14c491090897a89f48467840e19d9047a391c8255923c8b0a0fa0328824022908ab053124424225e7a7cad19e95bf677411ecc432595e4af22c283e80ca209008a422ac14c4910908971e1e2b061a16fd18d047b20081657908c8b0a0fa0328824022908ab053124424225a7274a919c15b8657411ecc43209564ad22c283e80ca209008a422ac14c) (
.fork 18 0x1b6ff0001fff800036507c879406234c172d7454936202f81b089192126cdaa8eb26 (
.leaf 17 0x6d9adacd8c8c98c6f7069e0d51b6fc5724a83dfe71abdfffad3aee27c279fcffcdbdb66b0001ffb800034507c871404234c072d1454936202f80b089180100c5a28e3266d801ac07e01fc00b6808c1dd826c2391c8a4c8a6d28041221324c25402954f90499b0f8687187070f818405b844be15ee9aa509d6d614a91e65916c19af264e13efb426c1a1a0c61c1c2e061016e110d847b26280275b4852a4799241a0623c01184fbcd0986e7637f448488400284874230000c8000500802320f69be25e7a09a0da7e83906f6198d8cdd121221000a121d08c000320001402008c83da6f8938e8268269f80e41bd7f5f0001fff800036507c879406234c172d745493630af81f0895d61a2cdae8eb245fc017e07e01fc00b6808c1dd826c2391c8a4c8a6d7c241231b65db5742d55f916d175ff0001fff800036507c879406234c172d745493630af81f0885d61a6ccae8eb045d5690897fff2210d9e1f3dedc188f305cb5d352cd8f2b8ff4329f7c6abb09abad31755a0001fff800036507c879406234c172d745493630ae01d0885d61a2cc268eb045d5680002ede0000d940d20e50188c105ca1d152418c2b807422175868b309a3ac1175425aa5fc87f842da86b777709b0ce472793a2bb7fcb87ec2da76d5d8b437ec5dc5d4600007ede0000d940d21e50188c305ca1d1524d0c21807422175868b301a1ac117500ff81f807f002da023077609b08e472293229b5f09048ced876d5d0b457e45945d4016a07e01fc00b6808c1dd826c2391c8a4c8a6d7c241230b61db5742d05f9165175005a80b8037002d8023035409b00647229322985f09048c2d876d5d0b417e45945d4006207e00dc00b6008c1d5026c0391c8a4c8a6d7c241030a61591742505f11651745a5a25c7878fc18685bf46be15ee9aa559ded637ac3e7f90ca79f5baec33eebcc5d1680007bea000041416218500009301c9451120d880b806422165868b308a3ac1171580001bf7800036507c879406234c17287454914308e01d0085d61a24c068eb005c4016206e01dc00b6008c1d5826c2391c8a4c8a657c2410309615b1740505f9164170f8587187070f818405b844be15ee9aa509d6d615a91e65916c59efb64e13efbc05c163e1c61c1c3e061016e112f857ba6a94275b5856a4799665b167bec9384fbef017058582187070f818405b844be15ee9aa509d6d615a81e65904859e5b24c13eebc05c16160820c0c1e061004e0123857886a94275b5016a0799641216796c9304fbaf0170581801870307818405b8448e15e69aa509d6d415a01e4190085965b24c13ceb805c16000061c000004101621000000920080051100508038064021658689300a3ac01701858018307078184013844ae15ea9aa509d6d415a01641904859e5b24c13e6b805b5595ab0898918c6f1c0e2b734d7891c7c1959330df2a0ff0b699fc3eaf0bab377165d652ec22624631bc7038adcd35e2471f06564cc37ca83fc3de67f0febc2eacddc) (
.leaf 18 0xa2e969768414080a981a9026007a8440422988484014f0601bcd61829144f30450ce8ae7a57e04800840008487001000040000500802020f69b62d27800a0d03e81906ba2af69568014014a081a102222d904c6e361a0650000d1e04f49624a89d2f204e88e8aa5fd7a00070f8080003004be15ca1a85089296018b51e42d65808e1503d9710e3a2a979df8001221000a001c08c000200000002008003d06f8b59e8268348f20c41ae8aa5bdda00002528006800808b8c031a8d20a0b401c351c02f35820e5513d9514b3a2a96956d121221000a121d08c000320001402008c00d0600b4960028140f204408e8aa5a55a00000000000000000000000000000000000341802d25800a0503c811023a2a9400000000000000000000000000000000000000000600800400001006200008a8a00a50000000000000000000000000000000000000000000c01000000014000022a0283e1c0001c3e020000c012f857286a14224a5806244190259002385008458430a80a0a05000000000000000000000000000000000000100000924000a040200010029e6700002ede0000d940d20e50188c105ca1d152410c218074021758699203a1ac0279009c80b8037002d8023035409b00647229322985f09040ca185645d01017c45909c26261020c0c1e061004e0123857886a94275b501680590664316596d9204f1ae02699494c822624631bc7038adcd35e2471f06564cc1708001cb1c4760f6180e84d90966727320414094a981a902622fb84c6e369a86d4174259056c517d97d960750ba424d9696cc20604430387000a9c92402471f06000cc354a01b4b966770feb82c00c9c92e565728414090a981a9026227b84c0c36988494054b0605bc571d83dc6730432c649d694ec02600631247008888d24e2030d064444435ca8374b164760fe182c08cd8926f65368014014a081a102222d904c6e361a0650054f1e05ecd33dabdd6a304fa464994d6ec00424630b870308c8d35c2070d061204c15c803f4b5667f0fe380c20cd892652f768010094a081a002222eb00c6e349a82d0074f41053cd31dbbdc697547246499494c80040042020600088892402030d060004015080014b144760f6180c00c90926500000010000008000002000800004001800000042000500011582982030020024900948000000000000000000000000000000000015080004a104640d0100400490902424100000010000000000220100808140000100400000424110582d820000220208848448000000000000000000000000000000000000000009040000040008000007ddec0007ffe0000d941f21e50188d305cb5d1524d8c2be07c22575868b369a3ac99f7007b81f807f002da023077609b08e472293229b5f09048c6d976d5d0b557e45b67c1e1e0c61c1c3e061016e112f857ba6a94275b5856a4799641a167bec9384fbef09b6ff0001fff800036507c879406234c172d7454936202f81b089192126cdaa8eb26)))) (
.fork 22 0x2fbbd00003270000364024839406230411286454904308781f0095d61a6498e86b22 (
.fork 20 0x2dbbd0001ddd800026107c0580062148160d701013410878170015d61a6498c02a22 (
.leaf 19 0xb6ef400004140000980090060018840040218040410421e05c00575869926300a88adbb9bdd21010250a400a40108ace131a85a0a1b505d3d7c17f35df6ff75bd553eb3b6ee2f74040009409000800422a38086a148282d4174659057cd57dbfd96d550facadba5bdda1000200240020010008a00000020202105d3d1c06f35d64fd513dd514b3b6e52f720410090898188026226b8080c34988094174241053c555d97d86575032cadb39bd921050252a606a40988bee131b8da6a1b505d3d7c17e31df6ff35bd553eb3b6ca6f64840408429002900400b284462028286c4174f5f01f8c7793f454f554dacedb18bd801050252a606a40988bee131b8da6a1b505d096415e115f65f2595542eb2b6c16f628414080a981a9026007a8440422988484174b4701b8475917444775412cedb00ff801007f002da023016209b08240028322185d090484e5176d5d03155604b2b6c03f7c0401cbe0b0008c052fa7f286a14a2cadc176641913dd55b3f404d55853cadb00bdda1000252a406a00908b8e031a8d20a0b505d3d0404f35d64fd11355514b3b6c02f6076016c009080801488228228180a48084d742410138455917404555012cadb00bd801000200240020010008a00000020202105d090404e115645d01155404b2b6c0000004000000900080040000800000000000410420001000551060004100008adabdbd5a00000500000000008a04021a85008094058357c13d25d96fb74bd953aa3b66f2f36001001480818002222c90086e341a0250174659056cd17dbfd968750fa4ad3b9b9d21050252a606a40988bee131b8da6a1b505d3d7c17f35df6ff75bd553eb3b4ae6e54840409429002900422b384c6a168286d4160d5f04f49765bedd2f454ea8ed1b8b8d01050252a606a40988bee131b8da6a1b505d196415b345f6ff65a1543e92b43e2e1c01c003e04101620027813986a1403135816247994649165bed928452eb0ad0bdb85a00500528206840888b64131b8d868194058357c13924d96fb74a9953a83b42e3e1c0001c3e020000c012f857286a14224a5816245994659167bed928458eb0ad0b8bdda00002528006800808b8c031a8d20a0b405c356411f34db6ff75a5153e93b42e2e1461414360000160102e8103a6a9426025856045904649165bed928450ea0ad0b8b85000000500000000008a04021a85008094058116411924596fb64a1143a82b42e000000000000000000000000000000000000010001804400165869920000a80ad000f87000070f8080003004be15ca1a8508929605891064096450cf900211610c2b4002e0000000000000000000000000000000000016004100200141164000450020acbb5b5da0040042020600088892402030d0600040153c1816f35c76af71bcc11cb3a6ab6b56840408429002900400b284462028286c4120d5f00f496603c150f654c88e8ea7a75e408080400280070200000000005008002207619a2da7a01a0da3e81102f) (
.fork 21 0x2dbffbdfe14d02d6a60eec7989bee171b8df6a9b707dffff77f37df6fff5bfd5befb (
.leaf 20 0xb6ffef7f849c09ced91e922623fbbcc6e369b97d51f7fffddfcdf7dbffd6ff56fbeedbffbdfe1050252a606a40988bee131b8da6a1b507dffff77f37df6fff5bfd5befbb6ffef7685fe094ad95bf22622fb8dc6e37db97d41f4fff05fcd77dbfdd6ff56facedbff000017f800036507c8180062340100d645410610af8170015d61a649ac0aa22b6ff6f7e85d40bead91bf22627fbbdc6e369b97dc176f7f95fcd77dbfdd6f756fbcedbbfbdde1070253a607a40988bee131b8da6a1b547d7f7d37f37df6fff5bfd53ebbb6ef7fff84152b5a98ba91e6aefb86c6e369aa6dc177f5ffdfddffffffdef75cfbeedbbdfffe1052673af87a709c8fffd31f8da6b3b5c5dfd7ff7f77ffffff7bdd73efbb6ef7fff8414094a981a902622fb84c6e369a86d4177f5ffdfddffffffdef75cfbeedbbdffda1057f52afa6a709eabff1b3f8daeb3b585d3d7c97f75fffff77bdd73eb3b6ef7fe00415fc00be809c07883ec609402b8cc8617425f25f945ffd7d9e7758bacadbbdfdfa10572faae06a709cbfffdb1b8daeb3b705dbd7e57f75dfeff75bdd73ef3b6ef6f7f841409ce981e902623fbb4c6e369a86d5177f5fddfcdf7dbffd6f754fbeedbbdbddbddd8252a616fc0d88bee179bedf7a1b535d3d7c17f35df6ff75bdd53eb3b6ef6f76f6156d4a989a9036aafb86eefb6be86d4d74f5f05fcd77dbfdd6f754facedbbdbddb95552daa606fc0d8bbee1f9badafa1b715d3d7c17f35df6ff75bdd53eb3b6ef6f76d5352b5a98bbb1f6aefb87e6e37daa6dcd74f5f05fcd77dbfdd6f754facedbbdbdda1050252a606a40988bee131b8da6a1b505d3d7c17f35df6ff75bdd53eb3b6ef6f768414080098009006003a8400402988484174f5f05fcd77dbfdd6f754facedbbdbdda10002502400200108a8e021a8520a0b505d3d7c17f35df6ff75bdd53eb3b6ef6f76801001480818002222c90086e341a0250174f5f05fcd77dbfdd6f754facedbbdbd921050210a600a401802ea111980a6a1b105d3d7c17e31df6ff75bdd53eb3b6ef6f600414080098009006003a840040298848417425f05f8457d97d967750bacadbbdb85010500502600240188a66121b85868195059197c179255d6fb64b9d43aa2b6ef6956841400009800900600188400402180404104f1e05f49775ae9d2f304e88edbbd94c81050042260624098896612030d860105055087817b155f61f6598c02eb2b6ef4e648414094a981a902622fb84c6e369a86d4174f5f05d8c77dbfdd6f754facedbbd29121050210a600a401802ea111980a6a1b10493d7c17421dd6fa74bdd53a23b6ef46200414094a981a902622fb84c6e369a86d417425f05c8457d97d966750bacadbbd058a1050202a606a409801ea110108a621210452c7817611df61e759cc12e33b6ef40168414014a981a902622d984c6e361a0654104f1e05c49775ae9d2e304e88edbbd0001ddd800026107c0580062148160d701013410878170015d61a6498c02a22) (
.leaf 21 0xbee96f76ae00dc00b6008c0d5026c0191c8a4c8a617cf4703bcf7593f544f7f556cefb18bd80bb7820036503483940ea304172a7656905f09641de195f65f25957c6fb2bec600002ede0000d940d20e50188c105ca1d152410c218074025758689241a1ac8afb00ff80b807f002da023037609b08647229322985f09048ce5976d5d03157e45b2bec02f607e01fc00b6808c1dd826c2391c8a4c8a6d7c241033865591740455f116cafb00bd80b8037002d8023035409b00647229322985f09040ce195645d01157c45b2bec02f602e0008009000800c502280101c88480a417c241033865591740455f116cafb00bd8090032002c0023014009b00002029322105f09040ce195645d01157c45b2bec02f600c009800b6008c0d5026c01104880c8a617c241033865591740455f116cafb001880b8037002d8023035409b00647229322985f09040c2195645d01117c45b2beaf6f56a0c0c1e061004e0123857886a94275b50168d5f06f4b765bedd2f6f5ee8ef1b80000bb78000365034839406230417287454904308601d0085d61a6480686b02bc402e202e00dc00b6008c0d5026c0191c8a4c8a617c241032861591740405f1164af0f8b87087030f818405b8049e15e61aa509d6d605a91e65992c596fb64a13cfbc2bc2e3e1c20c1c3e061004e012f857a86a94275b5816a4599665b167bed9284f9ef0af0b8b85187070f818405b844be15ee9aa509d6d615a11641992c596fb64a13c7b82bc2e2e1420c0c1e061004e0123857886a94275b501684590664b165bed9284f1ee0af0b8b85083000501040108008a04221aa501c4d405a11641992c596fb64a13c7b82bc2e2e142000c14020000c0122854086a94264a501684590664b165bed9284f1ee0af0b8b85002020701840038048e15e21a8500d6d405a11641992c596fb64a13c7b82bc2e060020c0c1e061004e0123857886a94275b501680590640216596d9204f1ae0af0b80000830000010401080000002000200144400420060190085961a6480286b02bc062e0020c0c1e061004e0123857886a94275b501680590660216596c9204f1ae0af018b8008300000104010800000020002001444005a0164198085965b24813c6b82b7efeff79434295a98ba91e6a2fb84c6e37daa6d49f5fdf6dfedffdffffeff54fafedfbfbfde3070653a787a40b9cbee135f9fa6a1bdc7d7f7db7fb7ff7ffffbfd53ebfb7efeff78414094a981a902622fb84c6e369a86d41f5fdf6dfedffdffffeff54fafedfbfbdda78f8252a616a40b9cbee135bdff6a1bd27d3f7c17fb5df6ff7dbfd53eb7b7efc0001e3e00009840900e5018841054b58042498429e05c20575869b26b00a89adfbdbfda7850f52a7a6a40bbcbee137fdfa6a1bda5d3d7c97fb5ff7ff7fbdd53eb7b7c02fe01e003c009680800cd02280191488080a6974241213a45d95742c555012dadbffbdfe14d02d6a60eec7989bee171b8df6a9b707dffff77f37df6fff5bfd5befb))) (
.fork 24 0x36dc6d6ec20024630987030a5cd15c2461f00120cc37ca83ecbde66d0dcb42eac5dc (
.fork 23 0x360d00000020000010400080000002000000044400020080180084160a60c028c900 (
.leaf 22 0xd80034000000800020000c0100044000000004800048000022121030240100a906034dd6d6ec0040042020600088892402030d060004035ca83f4bd667f0febc2c28cdccb71b1bb0898908c6f1c0e2b514c781146819592309f2a0fb2f789a4132d0bab15732cc6c66c222242119c1038254411e04412005648c22c283e89ce20900ca42aac14cc3b9f1df9120221000a121c084000100001402008883da6f8b79e8268369fa0e41b70ec7e77e40848840028007023000080000500802220f69be2de7a09a0da7e83906dc3b1f1db9020201000a001c0800000000014020008839a6f8b71e82403697a0e01b70dc6c6ec20604030387000a9412000451a060008c25ca83e4bd626904cb42c2845cc339f19f81200210002121c004000100001402008083da6f8a79a8268369aa0e41370cd6c66c02600631247008888d24e2030d064444420c283f09c621b02eac282884cc331bf9f0001c3e020000c012f857286a14224a580e34e1f8279882787298e5a43330cc6e77e00048840028007023000080000000802020f683e0de6a09a0da6683904dc331b5bb0000918c261c0c21234570818340048130d30a0f82f588a4172d0a0a13730cc6c66d448488400284874230000c8000500802320c283e09c620900ca4282804cc331b19b0000000000000000000000000000000000830a0f8271882403290a0a01330cc6000000000000000000000000000000000000020028000080000004842808004c300318000000000000000000000000000000000000000020230082400290008001300c0f87000070f8080003004be15ca1a85089296018918640964008e140611690c0c03030180000000000000000000000000000000000020209025100200101000a0102ffbf0000fbf80003650348394062304172d745492630a781f0895d61a6c9ae86b26bfc02fe03e00fc00b6808c0dd026c0191c8a4c8a697c241233a65d95742c55f116dafbff0000bff800036507c8394062344172d745490630af81f0095d61a649ae8eb22beef6f76aede094ad95ad22e72fb8cd6ffe9f97f417cf5f07fcf77dbfdd6f7f5fecefbbdbddab853752af86a70bdcbff137fffafb3bd85f3d7c1ff3ddf6ff75bdfd7fb3beef6f76a4d4c9eaf91ade2723fffcc6eb6bfdfd417cf5f07fcf77dbfdd6f7f5fecefbbdbdda3272673bfc7a78bdcffff35f9fa6f7fdc5f3d7c1ff3ddf6ff75bdfd7fb3beef6956aede0000d940d20e50188c105ca1d152410cf1e07f4b775ae9d2f3a5ec8efbbd0001fff800036507c879406234c172d7454934308781f0095d61a6498e86b22beef40002ede0000d940d20e50188c105ca1d152410c21e07c025758699263a1ac8afbbd0000b850000260024039406210417287010904308781f0095d61a6498e86b22beef400024d40000d900d20600188c004821d150410c21e07c025758699263a1ac8afbbd00003270000364024839406230411286454904308781f0095d61a6498e86b22) (
.leaf 23 0xdb71b5bb0800900026000c09500440110480048220df2a0fb2f799b4372d0bab17736d94d6c820424420b86030adc93502471f06120c81708009cbdc67f0f6bc0ea4d94db54b5a90898918c6f1c0e2b734d7891c7c1959330df2a0ff2b699fc3eaf09ab37736d46d6ac22624231bc7038ad4531e0451a065648c37ca83ecada66d0d8b42eac5dcdb50b5bb0888918c671c0e297345789187c0159330df2a0fb2f799b4362d09ab17736d42d6a4222242119c1038254411e04412005648c37ca83ecada66d0d8b426ac5dcdb50b5a90800900026000c09500440110480048220df2a0fb2b699b4362d09ab17736d10d68022624631bc7038adcd35e2471f06564cc1708009cad867f0f2bc06a4d94db41b5a30818900c2e1c0c2b504c40114681848230dd2806b2b699b4362d0ba916736d00ff81e807f0009a003067609908e472293228b1f09048ced866d4d0b457e4594db403fe00801fc0026800c09d8264219048a0c8a207c241233b619b5342d15f916536d00ff802002600098003025409900441220322881f09048ced866d4d0b457e4594db403fa00801d00026000c095804421104820482207c241232b619b5342d05f916536d00de802003700098003025409900641228322881f09048cad866d4d0b417e4594db4035bb0800918c261c0c297345709187c00483305f200fb2f799b4362d01a917736d00d681e807d0009a003067601108e472091208b1708008cad866d0d0b406a4594db4035a00800900026000c095004401104800482205c200232b619b4342d01a916536d0000002000000000000021400000401200000800308000c088444080840684104db35b59b0080818061000e01230578808140159100cb0a0fe273987c2fab0aab273369d4d4e802420621a460388c8d35e2030d06564401788825cb5c47e0f61c0eacdd0d974b4b90898918c6f1c0e2b734d7891c7c1959330df2a0ff2f799fc3faf09ab377364d2d264222246119c103825cc15e2461700564cc32c283f89ce61f0beac22ac9ccd87434380898918c6f1c0e2b734d7891c7c19593305e220972d711f83d8701ab374360ff000007f800012505c8080060340100d6454002202f81b0084960a64caa8eb00d83e341c01c083e061016e0127857986a14035b5804a4389665b127aad9380abef0360f800000700000104058800000024000000444000200e0190084960a64c028eb00d835b41b0098818c691c0e23234d7880c341959110cb0a0de25390782f830aab272360d0f87002070f8184003804be15ea1a8508d6d601a91865896c41eeb60e13ed9c0d83435bb0080918c671c0e212345788183401591305b020fe2d798fc3f8f00ab376360d0d06187070e818405b844bc15ee822509564611280825894c41e0b60c02ac9c0d83434180080818061000e012305788081401591004a0209625310782d8300ab270360d00000020000010400080000002000000044400020080180084160a60c028c900)) (
.fork 25 0x36dd6deec226347b1bc7038adcf35e25f9f0ed6dcc3fcb87fcbde67f4febc3fecddc (
.leaf 24 0xdb75b5bf889891ce6f1e0e2b73cd78d7e7c1b5b730dffa0ff2ffb9febfef8baf77776dd6d6edefea4631bd75b8edcd35e6c77f57564cf37ca83fcbde67f0febc2eacddcdb75b5bb7a99f58c6f9c0e3bfb4d7ab9dfc3d5933cdf2a0ff2f799fc3faf0bab37736dd6d6eda7674eb1bc75b8edfd35eec73f0f564ed37ca83fcbde67f0febc2eacddcdb75b5bb59b9b39c6fbd2ffbff4d7bb1c7d59793bcdf2a0ff2f799fc3faf0bab37736dd6d6ec22624631bc7038adcd35e2471f06564cc37ca83fcbde67f0febc2eacddcdb75b5bb089890006f000e0b500c48114481959220df2a0ff2f799fc3faf0bab37736dd6d6ec22600421246008a9c92422431f06444c037ca83fcbde67f0febc2eacddcdb75b5bb0880918067000e097305789185c0159320df2a0ff2f799fc3faf0bab37736dd6d6ec20424420b86030adc93502471f06120c837ca83fcbde67f0febc2eacddcdb75b5bb0090818869180e23234d7880c341959100df2a0ff2f799fc3faf0bab37736dd6d6a422624211bc10382d4431e04512065648c37ca83fcada67f0febc2eacddcdb75b5a0089890006f000e0b500c48114481959220dc2a0272b619fc3daf0bab36536dd6d06022620601a400382dcc35e2431706564c0338a825c9cc45e0b68c2eac9c4db75b1bb0898100c4f1c022a5048081146819112309f2a0ff2f799fc3baf0bab35736dd6c66c22600001240008294020204112064448023ca83fc9ce65f0aeac2eac94cdb75a532089801084918022a72490890c7c1911300dc2a0072e711d83da70ba336536dd652a422624631bc7038adcd35e2471f06564cc37ca83fc2da67f0febc2eacddcdb7591ab0898908c6f1c0e2b514c781146819592309f2a0ff0b699fc3baf0bab35736dd6422422624211bc10382d4431e04512065648c23ca83fc0ca65f0aeac2eac94cdb7584200898918c6f1c0e2b734d7891c7c1959330dc2a0070a611d83da70ba336536dd6068c226040313c7008a9412020451a064448c274a81bc29a6770eebc2e8cd1cdb75801b0898018c491c022a73493890c7c19113108f2a0df06391582ba30ba325336dd60001efe8000125058869402024c1725744483230a801c0884560a68c2e8c904db758000089800004900020a5008081044819112008c2a007022115829a30ba324136dd2d6e4222246119c103825cc15e2461700564cc37ca83fcbde67f0febc26acddcdb7435b80880918067000e097305789185c01593205e220b72f719fc3daf01ab37536dc6fffe2007f8409a8037277099086412283a2a83fff87ecffee6deddb67ffd5dddb71b7bb0800d00026000c09500440110482048220ff2e1fb2f799b5372d0ffb17736dc6d6ec222242119c1038254411e04412005648c37ca83ecbde66d0dcb42eac5dcdb71b5bb0818900c2e1c0c2b504c40114681848230df2a0fb2f799b4372d0bab17736dc6d6ec20024630987030a5cd15c2461f00120cc37ca83ecbde66d0dcb42eac5dc) (
.leaf 25 0xdbf5f5fb98b8b19c6fbc0febf34d7891c7d5979338dfba6ffbf7f9fc3fef7baf37f76fd7d7ee3272663bfc7a78bdcdfff3471fa6776dc37ee9bfefdfe7f0ffbdeebcdfddbf5f5fb8898918c6f1c0e2b734d7891c7c1959330dfba6ffbf7f9fc3fef7baf37f76fd7d6ec7afa4633fd7278bdcd77f2475fd6574de37ca9bfebdf67f0febdaeacdfcdbf5c0001ebe0000d940920e50188c1054b59152488c2a607822515829a36ba324936fd6d7ec7a62f633fe7238bfcdbfe2675f26766de37ca83fcfdf67f0febd6eacdfcdbc03fe01e01fc00b6808c0dd826c219148a0c8a687c241233b659b5342d55f916d36f00d7807802f002da023037409b006452203229a1708008ced966d0d0b546a45b4db7ff5bf889c91ce6f1e1e2b73dd7cd7e7e1b5f730dffbeffeffbbfebfffabafff776dffd6ec27fa4631bd75f8adcd75f6471fd6574cc37cafbffbde6ff0fefcaeaefdcdb7ff5bb089c918c6f1c1e2b735d7c91c7e195d330df2beffef79bfc3fbf2babbf736dffc67e27f808412585cf295060344112d64d4a023fefbff9eeedfaafeeaebfb4ddb7fc0007bfe00004941721a50180d305cb5d1520c8c2be07c22135829b32ba3ac136dff000027f800012505c8294060344112d645480230af81f0884d60a6ccae8eb04db7fc000089c00004900120a50180c1044a19152008c2be07c22135829b32ba3ac136dfed6fc27624fb1bc75b8addf35e65f9f06d6dec37dae3fdbfe6ffafefe2eaffdcdb7fb5bf089891cc6f1c0e2b73cd7897e7c1b5b730df6b8ff6ff9bfebfbf8babff736dfe0000276000012405882940202441120644480230ae01d0884d60a6cc2e8eb04db7df5bf89b8939c6f3d2feb774d7991c7d59793b0dffa6ffaffb9febfefabaf77776df7d6fe22624631bc7038adcd35e2471f06564cc37fe9bfebfee7faffbeaebdddddb77b5bb08de918c6f5c5e2b735d7c91c7e195d330df2b8ff6f79bfc3fbf0babbf736dded6ec236247b1bc7138adcf35e25f9f06d6dcc37cae3fdbde6ff0fefc2eaefdcdb77b5bb089c91ce6f1e1e2b73dd7cd7e7e1b5f730df2b8ff6f79bfc3fbf0babbf736dde0000237800012501482940603041128645480230ae01d0884d60a6cc2e8eb04db75f5bb889c918e6f1e1e2b735d7cd1c7e195d330dfba6ffaf7b9fc3fef2baf37776dd6fffe22626739bc7838adcfbde35f9f26f6fcc3fff87fcffee7feffbe7ffdddddb75bffb0899fd8c6f9c0e2bfb6f7a99c7cb9d9b30ff2e1ff3f799fd3faf1ffb37736dd6fefc22674fb1bc7038adff35ea5f9f0ed6dec3fdb87fcbfe67fefebe3fedddcdb75bfbf089891cc6f1c0e2b73cd7897e7c1b5b730ff6e1ff2ff99ffbfaf8ffb77736dd6f7fe2266ce71bef03faffd35ea471f065e4ec37fe83fcffee7faffbe6ebdddddb75bdff8898918c6f1c0e2b734d7891c7c1959330dffa0ff3ffb9febfef9baf77776dd6deec226347b1bc7038adcf35e25f9f0ed6dcc3fcb87fcbde67f4febc3fecddc)))))) (
.fork 39 0x3fde6fefc2002400098003025401100441200120887fdb87ecbfe76dfdcb63fed5de (
.fork 32 0x3f0b8f8518307078184013844ae15ea9aa509d6d415a11641996c59efb64e13e7b82 (
.fork 29 0x38effe77e02700739247848888f64f31b8d86c5d4420f6fbf3de7a9ba2fefe83ba6f (
.fork 27 0x37fdf0000fbf80003650348394062304172d745492630af81f0895d61a6cdae8eb24 (
.leaf 26 0xdfc037e03e00fc00b6808c0dd026c0191c8a4c8a697c241233b65db5742d55f916d37dff0000bff800036507c8394062344172d745490630af81f0885d61a6ccae8eb04df77b7bb28d8d1ec6f1c4e2b73cd7897efc3f5b731ff2f9ff6f79ffd7fbf0ffbbf737ddedeec3272673bfc7a78bdcffff35f9fa6f7fdc7fcbe7fdbde7ff5fefc3feefdcdf77b7bb089891cc6f1c0e2b73cd7897e7c1b5b731ff2f9ff6f79ffd7fbf0ffbbf737dded6ecbb7a4633fd7378bdcd77f2477f87574dc77cae3fdbde7ff1fefc2eaefdcdf77b19b2ede0000d940d20e50188c105ca1d152418f2b8ff6739f7c6bbb0babad337dde0001fff800036507c879406234c172d745493630ae01d0885d61a6cc2e8eb04df7780002ede0000d940d20e50188c105ca1d152418c2b807422175869b30ba3ac137dde0000a36000012401082940202041320744480630ae01d0885d61a6cc2e8eb04df7780000c9c0000d900920e50188c1044a19152418c2b807422175869b30ba3ac137dd6deecba637633fc7238bdcdbfe2677f2f766dc7fcb87fcbde77f5febc3fecddcdf71b7bb2e00dc00b6008c0d5026c0191c8a4c8a61ff2e1fb2f79db5772d0ffb17737d180000bb78000365034839406230417287454904308601d0885d61a2cc0686b04df403fe02e01fc00b6808c0dd826c2191c8a4c8a617c241233b61db5742d15f916537d00de81f807f002da023077609b08e472293229b5f09048cad876d5d0b417e4594df4037a02e00dc00b6008c0d5026c0191c8a4c8a617c241232b61db5742d05f916537d00de80a003400098003025401100443209120885f09048cad876d5d0b417e4594df4037a00c009800b6008c0d5026c01104880c8a617c241232b61db5742d05f916537d001880b8037002d8023035409b00647229322985f09040c2985645d09417c4594df37b79b20c0c1e061004e0123857886a94275b501eb0f9fe6739e7d6fbb0efbaf3371d80000bb78000365034839406230417287454904308e01d0085d61a64c068eb00dc4036202e00dc00b6008c0d5026c0191c8a4c8a617c2410329615b1740505f9164370f8d87087030f818405b8049e15e61aa509d6d605a91e65996c59efb64e13efbc0dc363e1c20c1c3e061004e012f857a86a94275b5816a4799665b167bed9384fbef0370d8d86187070f818405b844be15ee9aa509d6d615a81e65994c59e5b64c13eebc0dc36361820c0c1e061004e0123857886a94275b5016a0799665316796d9304fbaf0370d8d86002020701840038048e15e21a8500d6d405a81e65994c59e5b64c13eebc0dc36060020c0c1e061004e0123857886a94275b501680790640216596d9304f3ae0370d800008300000104010800000020002001444004200e0190085961a64c028eb00dc06360020c0c1e061004e0123857886a94275b501680590661216796c9304f9ae036fff00007ff800036507c8394062344152d645492230af81f0894d60a6cdae8eb24) (
.fork 28 0x38ee7070f448080400284874200000480005008003206699a2483a0100da5e81802f (
.leaf 27 0xe3b9c01fd1200210002121d004000120001402008c83da6d8869e0028361ea0641bf8ee700014480000000048040000004800050000032002980208100000485a808026e3b83ffc5101ffe026812c11afa773afa14a2cadac72461b03fd48a7952dd45a53db8ee0e771440488000204804230000c80000000023009082c0de5209a04a74029066e3b1b9db500120000080001088000220000000000c830a0f8371c82403295a0a01bb8ea5ffdb4007f5289a6830c6ab9d0bbe8d28b2b4b1c351c82ff5a29e55b7d9714b7e3a979d6d00120000080001088000220000000000c00d0620b7968268169f20c409f8e42e725448488400284874230000c8000500802320c283e0cc3209008a5602806ee38879c4d121221000a121d08c000320001402008c00d0620b3868268069f00c409f8e07e70f408480400280074220000880005008003206619a2cc3a09009a5e83002fe3803fe05001fc0026800c1188264229000a0c882c70041203b448a5142d545812db8e00ff7140078f8082003046be15ca9a850892963189106c0de5209e10a751610e6e38039dfd001221000a001d08c000220000002008c03d00f8379e8268269d00c41bf8e00e70140048000020000422000088000000000300000080cc1209000a54020026e3800000500000000000001000000020000000000c0000000020400000214000009b8cfee67d07640fb1247588c8bf24ee9b8d06c4d6520d2e3f19e629ba2eee282ba4ee339bfbf4101d3ec261d2c312fc573a7a34224a5b4f34e1f82fd88a7972d8e5a537b8ce6e67d040408000004804030000c8000000002120d283e09e6209a0ca6282904ee2bf795ec1d503ea491b72322fd93fe6e361b1758402d3e94f59626a89d3f20ee98f8ae5fdfb04072fa8806cb0c4bf9dcf9a8d28b2b611cb59e42f75828e5517d9794f3e2b9795ec1010200000120100c000320000000008402d2690b5960228141f20e418f84e2e275448488400284874230000c8000500802320d283e09e6209a0ca6202904ee0b8785cd121221000a121d08c000320001402008c02d2690b5960228141f00e418f80f8e07107040f8104058840be04ee9a8500c4d610090e25196409aa264e002ba42e039f81fc1210210002121d00c000320001402008483da6d8a59a0228341aa0e412f80e0f87104070f808004b044be15ce9a85089296118918640964008e140611690c2e03839dfc101221000a121d08c000320000002008403d20f8359a8268349900e412f80e0e071040408000004804030000c8000000002100908240964008a04060029042e038000041000000000120100000012000000000040002000000000001010002000b8000f87100070f8080003044be15ca9a85089296118910640964008e100611610c2e000380040010000000000100800022000000000040000000210002000010008000b7fdf0000fbf80003650348394062304172d745492630af81f0895d61a6cdae8eb24) (
.leaf 28 0xe3bfe956d1fe014a495b723222d90de6e375b1750c80dbe04f69624a89f3fa06e89f8eff000147f800012505c8480060348100d6454032002f813081092026cda80aa26e3bdf9dfd1b9239c49bd23f2af493ba0c35593119c83da6fcb79e86e8bebfa0e61bf8ee7ffff4487ffc09a84b746be9dcebe8578bab6b3cf79fe2ff7a29e5db7f9794ffe3b9ffffd121ff5a26bb2df1aee743efa35e2eadacf3de7f8bfde8a7976dfe5e53ff8ee7ffff4487f8409a84b74630990ca400783a22b3cf79fe2ff7a29e5db7f9794ffe3b9ffffd121f3fc26bd2df1afc573a7a35626a5bcf3de7f8bfde8a7976dfe5e53ff8ee7ffff4487afe882ecb7c6bf9dcf9a8d78bab633cf79fe2ff7a29e5db7f9794ffe3b9ffffd121bbde26bf2df1afe773e7a35c2eadbcf3de7f8bfde8a7976dfe5e53ff8ee7ffff4484ad6802ec87c2bb8c0f9a8d70a8b633cf79fe2ff7a29e5db7f9794ffe3b9ffff800099ce261e0c2123e770c7a3482cad30f3de7f8bfde8a7976dfe5e53ff8ee7ff7f44878fc08284b746be15ce9a85589a96338f79fe2de7a09e1da7f9790efe3b9fe1c5121c3e020012c112f8573a6a15624a58ce24e790a7940238521ee5a439b8ee7f7ff4486ce709af4b7c6bd15ce860d501a06f34f69be2ff7a29a5db7e8394ffe3b9f9dff363221000e161d08c000320181442008c83da6f8b79e8268369fa0e41bf8ee7e77fcc8598400284874230000ca060590802320f69be2de7a09a0da7e83906fe3b9f9dff161623000a161d08c000320081642008c83da6f8b79e8268369fa0e41bf8ee7e77f448488400284874230000c8000500802320f69be2de7a09a0da7e83906fe3b9f9dfd12000000001201000000120001400000c83da6f8b79e8268369fa0e41bf8ee7e77f40048000020000422000088000000000320f69be2de7a09a0da7e83906fe3b9f9dfc1010200000120100c000320000000008483da6f8b79e8268369fa0e41bf8ee7e77e40808040028007020000000000500800220f69be2de7a09a0da7e83906fe3b9f9df81200210002121c004000100001402008083da6f8b79e8268369fa0e41bf8ee7e77e00048840028007023000080000000802020f69be2de7a09a0da7e83906fe3b9f9df800000000000000000000000000000000083da6f8b79e8268369fa0e41bf8ee7e701448480000204804220000c8000500000320029882cc1209004a5e828026e3b9f81c51210200000120100c000320001400008c824a690a7940228121ea0a419b8ee7c66d44800000000480400000048000500000320c29be29c720900ca5a82806ee3b9e956d12000000001201000000120001400000c80da600b6960028161fa06409f8ee74225448488400284874230000c8000500802320c29be20c320900ca5a82806ee3b9c844d121221000a121d08c000320001402008c80da60092860028161fa06409f8ee7070f448080400284874200000480005008003206699a2483a0100da5e81802f))) (
.fork 30 0x3ae00e701e807d0009a003067601108e472091208b02000088cc9209000a542a4126 (
.leaf 29 0xe838381c61c1c2a061016e110d047b2008025590840a4209225b0022810180ab450b9eefef7fc58589c00285874232000c98a0598892368f7ffe3de7b89f0de7f97b26fe7bbfbdfd5252a5290a3b1d48cb28766203c2a6ccda3dfff8f79ee27c379fe5ec9bf9eefe77fdd9c88424387c75230421c8060d10903360f6fbe3de7b89b0de7e83b26fe7bbf9dff161221000a161d08c000320081442008d83dbef8f79ee26c379fa0ec9bf9eef0001dd9800024107c0500042148060d1010136002f803081180104c5a80a226e7b9fbdff7216e1090a1a1d48c228328181e4a08cda3de7f8b79ec27c369fe5e41bf9ee7ef7fc48588400284874230000c8020590802368f79fe2de7b09f0da7f97906fe7803bc076016c009080801488228228180a48084d20041203304c2540295458009b90e8e871850509800005804032000c98a009809214891e641964188f0446116b242e3f9f9ffdf3f3e109ee1b1dedc3a873954bd8a4aec97fa6f9bfde9a6936dfb0e51ff8fe7e7ff7cfca86a63eec7fb71ea1dc15af6292b325fe9be6ff7a69a4db7ec3947fe3f9f9ffdf353e1a9ebbb1fedc7a877956bd8a4aec97fa6f9bfde9a6936dfb0e51ff8fe7e7ff7c84f8425a868773708a0ce45270282bb25fe9be6ff7a69a4db7ec3947fe3f9f9ffdd3d3a1e9ebfb1fedc7a877146bd8a4afc97fa6f9bfde9a6936dfb0e51ff8fe7e7ff64e4c8703af487eb71200cc51a56080af25fe9be6ff7a69a4db7ec3947fe3f9f9ffd5352a1a98bbb1f68c7a8760423d8a48cc97fa6f9bfde9a6936dfb0e51ff8fe7e7fe3070603a787a40b941ea11451aa62129c25fe9be6ff7a69a4db7ec3947fe3f9f9e05f3f3c009ec1b01ed83a873954bd884a6c942a621bb449a4112d7b0a10db8fe7e77f7cfc88426386c77b70621cc152d6090b321fe9be6de7a49a0da7ec3906fe3f9e976df3e080a985bb03e507a857056bd884a4c94fa601bed61829165fb0650df8fe700017cf800026106c079406214c152d601093210a980608104000485ac08026e3e979f6de153c0a9e9a903ed87a867956a9884a6c14f0621bfd69a6916df30c50df8f00e7817804f0025a020073608a08e452202029b05080084ed1269040b54420436e3bff9dfd1ff235a49fb73f2aed90fe6e375b3758c83dbefcf79ea6e8bfbfa0ee9bf8effe77f47fc88412785cf4a30603c8100d64d42320f6fbf3de7a9ba2fefe83ba6fe3bff9dfd1f923fc49bd63f2afc93ba6e355b3359c83dbefcf79ea6e8bfbfa0ee9bf8effe77f47d48fe926edcfcabf64ff9b8dd6cdd6320f6fbf3de7a9ba2fefe83ba6fe3bff9dfd1e123f041a163d0af813ba6a15433358c83dbefcf79ea6e8bfbfa0ee9bf8effe77f46f48f7926fccfcabf64ff9b8dd6cdd6720f6fbf3de7a9ba2fefe83ba6fe3bff9dfd135235a08bb31f2aed907e6e375a2658c83dbefcf79ea6e8bfbfa0ee9bf8effe77e02700739247848888f64f31b8d86c5d4420f6fbf3de7a9ba2fefe83ba6f) (
.fork 31 0x3efd6f7ec22624631bc7038adcd35e2471f06564cc37ca83fcfdf67f0febd6eacdfe (
.leaf 30 0xfbc03fe05801fc0026800c19d8264239048a0c8a2c7c241233b659b5342d55f916dbef00f7816006c0009a003067601108c412001208b1708008ced966d0d0b546a45b6fbbdfddfd1a1a39061a12fd1af057ba0815417918ccbda6feb7bf87eafebfaaf67bfedf6f6fd26664e31bc74b8edfd35eec71f06564ed37da83fcbfe67fafebe2eadddefb7dbdbf0898918c6f1c0e2b734d7891c7c1959330df6a0ff2ff99febfaf8bab777be0f0f07106060e018404b844bc15ee820500564611290825896c41eab60e02ad9c2f7ffffffd5352b5a98bbb1f6aefb87e6e37daa6dcdf7ffffdffdffffffffff5efbffdffffffe1050252a606a40988bee131b8da6a1b507dfffff7ff7fffffffffd7befff7fff9dfd535221098a1b1d68c18872040358240cd87fbefdf79ff7eebfbfb0ee9bfdfffbddb54d0252a606ec0d88bee179b8df6a1b537d3ffc17fb5df6ff7dffd5beb7f7ffef768414094a981a902622fb84c6e369a86d41f4fff05fed77dbfdf7ff56fadfdfff000154d000026006c0580062148100d601013610af8170815d61a6cdac0aa26f7f9ffffd5212a1090a1a1d48c228320001c0a08cdf7fe7f9bfdfdb7f76dff5e53ffdfbdffdb5054a52a626a40daabee1b9b8da6a1b535d3d7c97ff5fffff7ffdd73eb7f7ef7ff68414094a981a902622fb84c6e369a86d4174f5f25ffd7ffffdfff75cfadfdf00ff815004a00242020052208a08800020202135d090484ed176d5d0b555604b6f7bfffdfd121235000a121d0ae8103a6a15422258de3dfffcf79fe7feffbfe5eebbfdeffe77f448488400284874230000c8000500802360f6fbf3de7f9fbafefe83ba6ff7b9ffdfd121221000a121d08c000320001402008de3de7f8b79fc37e769fe5e43bfdbfdfdfb14542d2a606ec0d8bbee1f9b8da6a1b715dbdfe57f75dfeff75fdd7bef3f6ff7f7e8414094a981a902622fb84c6e369a86d4176f7f95fdd77fbfdd7f75efbcfd0f8f87104040d0000048040ba040e9a8500809615891e65196459efb64e116bac2f3fdfdffd131231808b921f2ae4903a0c35582018cd7fa6fdbfdf9febfeffb0e73ffcfe7f7ff448488400284874230000c8000500802335fe9be6ff7e6daddb7ec394ffebbff9dffbff221049e173dadc180f305cb5d3528c8bdbefef7bea6e8bfbfaafedbfaeff0001eff800012505c869406034c172d7454832202f81b089092026cdaa8eb26ebb9f9dffbeb221041e163d8dc000b301c9453128c8bda6fab7be8268369faaf45bfaee7e77fec87d8409a84b76770110ce472591a0ab22f69beadefa09a0da7eabd16febb9f9dff1e1e2b061a16fd18d047b20081657908c8bda6fab7be8268369faaf45bfaee7e77f66a6ca519e94bf677411ecc412505e4af22f69beadefa09a0da7eabd16febb9c0007bea000041416218500009301c9451120c880a602822400001216aa3049bae00e701e807d0009a003067601108e472091208b02000088cc9209000a542a4126) (
.leaf 31 0xfc2e3e146001c14020000c112a8542a6a94264a505684590665b167bed9384f9ee0bf0b8f85000020500800030048a15021a8500929405a11641996c59efb64e13e7b82fc2e3e006001c00020000c11080442200802448005680590661216796d9304f9ae0bf0b8b85180000500000000408a04029aa501809415a11641992c596fb64e13c7b82fc2e0000600000000000001000000020080040000508018064021658699300a1ac0bf058f82187070f818405b844be15ee9aa509d6d615a81e65984859e5b24c13eebc2fc103e0861c1c2a061016e110d047b2008025590856a061922121431640104fb070bf038f81187070f818405b844be15ee9aa509d6d615a11641986859efb24e13e7b82fc0a3e046141c26020016c110c844326280264a485684590261a1633e41184f9ce0bf018f87183070f8184013844be15ea9aa509d6d615a91665996c59efb24e13e7bc2fc063e0060c1c1e061004e112b857aa6a94275b505680590661216796c9304f9ae0bf018f8018307000184013844201128802009564015a01641984859e5b24c13e6b82fc063e006001c14020000c112a8542a6a94264a505680590661216796c9304f9ae0bf018180183030781840138448e15e29aa509d6d415a0164190085965b24c13c6b82fc06000060c000004100421000000820080051100508018064021658689300a1ac0bf000ff818007f0009a003046209908a42029322095e010488e5872d5d03453e4592fc003e1c6001c3e020000c112f8572a6a94264a5856a4419225b1433e40184f9470bf000f8018007000080003044201108802009120015a01040884850c5900413e4182fc000000600000000000001000000020080040000508000020021410600100a1040beffff7fe22724739bc7878adcf75f35f9f86d7dcc37fefbfffffeffaffffeebfffffbfff9dfd9ff221049e173dadc180f3044b593528c8ffbefff7bfb7eabfbfbafedbfefff000167f800012505c869406034c112d645483230af81f0894d60a6cdae8eb26fbfdfdffd9b9b39c6fbd2ffbff4d7bb1c7d59793bcdffa6ffbfff9febfeffbaf77ffeff7f7fe22624631bc7038adcd35e2471f06564cc37fe9bfefffe7faffbfeebddfffbfdf9dfd9b9221049a123dadc080b30449593128c8ffa6ffb7bf97eabebfbaf65bfeff7d6ed66e24631bc74b8edcd35e6c71f56564cf37ca9bfebdf67f0febdaeacdfefbfdf5bb0898918c6f1c0e2b734d7891c7c1959330df2a6ffaf7d9fc3faf6bab37fbeff7000166e0000124048869402024c1125644483230a981e0894560a68dae8c926fbf9ffffd921fe1026a12dd9dc264339049e0e8aacfffe7fbbfff9b7b76dffff57ffefe7f7ff6486c8409a84b76770110cc412501a0ab37fe9beefffe6daddb7eebd5fffbf5bdfb5899b18c6f9c0e3bfb4d7ab1c7c195933cdf2a0ff3f7d9fc3faf5bab37fbefd6f7ec22624631bc7038adcd35e2471f06564cc37ca83fcfdf67f0febd6eacdfe)))) (
.fork 35 0x3f0fa000187a8000105058840000024802051444016202e0190085961a64c228eb02 (
.fork 33 0x3f0f84021870408010405884030002c802001444214280e25904859e1a64c02aeb42 (
.leaf 32 0xfc3e0e0461c1c3e061016e112f857ba6a94275b585684790640a165bed9384f3ee0bf0f8287187050f8104058840be04ee9aa509c4d614a91e65912c596fa64e13cfb42fc3e0a0461c14260410162100c800b262802713485284790640a165be99384f3ec0bf0f82811870508010405884030002c802009444214a11e419028596fa64e13cfb02fc3e0a0461c0004041016210008009262800713405284790640a165be99384f3ec0bf0f82801870508810405884030002c802009444214a01e4190085965a64c13ceb02fc3e0a0061c140004101621008000b20080251100528079064021659699304f3ac0bf0f828018700000104058840000024802001444014a01e4190085965a64c13ceb02fc3e080461c10200410162100c000b200800511085084380640a165ae99380a3ec0bf0f8187187030f818405b8449e15e69aa509d6d615a91e65912c596fb64e13cfbc2fc3e060061c0c1e061016e11238579a6a94275b505680790640216596d9304f3ae0bf0f81801870300018405b844001124802009564015a01e4190085965b64c13ceb82fc3e060061c0014041016210228109a6a940713505680790640216596d9304f3ae0bf0f818018700000104058840000024802001444015a01e4190085965b64c13ceb82fc3e020061c040604101621000800926280271340528079064021659699304f3ac0bf0f808018701000104058840000024802009444014a01e4190085965a64c13ceb02fc3e001c61c003e041016210278139a6a9407135850a4389644b165ae99380a3ed0bf0f800718700080104058840100024802001444214290e25912c596ba64e028fb42fc3e000861c002a0410162100500392008005110850a038964021658699300a3ad0bf0f80001cf88000105058840000024806051444034200e0190085961a64c028eb02fc3e00006bca000041416218500009301c8051120508038064021658699300a3ac0bf0f800019f1800034507c850004234806081454114200e0190085961a64c028eb02fc3e000061de00004941721200180d204821d1500508038064021658699300a3ac0bf0f80001870508810405884030002c802009444214200e0190085961a64c028eb02fc3e000061c000004101621000000920080051100508038064021658699300a3ac0bf0f800000200000104000800000020000000444004200e0190085961a64c028eb02fc383e1c6101c20020012c110c04432008024480856a4619225b1433e50184fb470bf0d8f8618307078184013844ae15ea9aa509d6d415a81e65994c59e5b64c13eebc2fc343e186081c18061000e112b057aa089425591056a0619625314796d8304fb270bf0b8f87180070f8080003044be15ca9aa509929615a91665996c59efb64e13e7bc2fc2e3e146141c36020016c112e8543a6a94264a585684590665b167bed9384f9ee0bf0b8f8518307078184013844ae15ea9aa509d6d415a11641996c59efb64e13e7b82) (
.fork 34 0x3f0f8f87083030781840138048e15e21aa509d6d405a91e65996c59efb64e13efbc2 (
.leaf 33 0xfc3e3e1c01c083e061016e0127857986a14035b5816a4799665b167bed9384fbef0bf0f8f87002070f8184003804be15ea1a8508d6d605a91e65996c59efb64e13efbc2fc3e3e1c008081c061000e0123857886a14035b5016a4799665b167bed9384fbef0bf0f8f861870706018405b844ac15ee822509564415a81e65994c59e5b64c13eebc2fc3e3e1461c1c14061016e112a854ba6a94275b505684790665b167bed9384fbee0bf0f8f82187070a818405b8443411ec802009564215a81e65984859e5b64c13eebc2fc3e3e0461c1c26061016e110c844b26280275b485684790661a167bed9384fbee0bf0f8f801870707818405b844ae15ee9aa509d6d415a01e41984859e5b64c13eeb82fc3e3e0061c1c00061016e1108044b200802559005680790661216796d9304fbae0bf0f8f801870400010405884020002c802001444015a01e41984859e5b64c13eeb82fc3e3a1c61c14260410162100c800b2628027134852a4799665b167be99384fbed0bf0f8e871870508010405884030002c802009444214a91e65996c59efa64e13efb42fc3e3a0061c140004101621008000b20080251100528079066121679699304fbac0bf0f8e77f8704884106858f4230002c8020014c42142f4e3f9d6ef9fbaf6e42bfb4bfc3e381c61c10200410162100c000b2008005110850a4389665b167ae99380abed0bf0f8e001870400010405884020002c802001444014200e01984859e1a64c02aeb02fc3e361861c0c1e061016e11238579a6a94275b5056a0799665316796d9304fbaf0bf0f8d061870206018405b8448c15e6822501564415280e25994c59e1b64c02aebc2fc3e301861c00000410162100000092008005110050a038966531678699300abad0bf0f8b87187000f81040588409e04e69aa501c4d615a91e65992c596fb64e13cfbc2fc3e2e1461c14360410162102e810ba6a942713585684790664b165bed9384f3ee0bf0f8b851870307818405b8448e15e69aa509d6d415a11e41992c596fb64e13cfb82fc3e2e1461c0014041016210228109a6a940713505684790664b165bed9384f3ee0bf0f8b8518700000104058840000024802001444015a11e41992c596fb64e13cfb82fc3e2e14008001404100020022810886a140313501684790664b165bed9384f3ee0bf0f8b801870500010405884020002c802009444015a01e4198085965b64c13ceb82fc3e2e0061c0000041016210000009200800511005680790660216596d9304f3ae0bf0f8a0518700000104058840000024802001444014210e01992c596ba64e028fb02fc3e1a0c61c1c2e061016e110d847b26280275b4852a4799641a167be99384fbed0bf0f8582187070f818405b844be15ee9aa509d6d615a81e65904859e5b64c13eebc2fc3e100861c1c2a061016e110d047b2008025590850a038964121678699300abad0bf0f84021870408010405884030002c802001444214280e25904859e1a64c02aeb42) (
.leaf 34 0xfc3e7e1ce1e1c3f061216fd12f857ba6a95677b5856ad7f96e5b367bedd3a4ffef0ff0f90001879800010505c8400040348020d1454014200f81b0085961a64c828eb02fc3e3fffe1c1f3fc67bd6ff1afc57ba7ab4277b5b57bd79fe7dfbeffffdf94ffff6ff0f8fff18707ff819e05b846be9deebea529f6f695e91e6d9f7c7bfff67e53effd2fc3e3fdfe1c1e3f061a16fd1af857ba6a94277b5856bd79fe75bbe7fefdb94ffef2ff0f8ff7187078f818605b846be15ee9aa509d6d615a91e6d9d6c79ffb66e53efbc2fc3e3fbf61c1d3ec671d6e312fc57ba7ab4275b5b57b479fe6df9effff9f84fbff6bf0f8fef187074f819c05b844be15ee9ea509d6d695e91e6d9b7c7bfff67e13effd2fc3e3f9f61c1c3e061016e112f857ba6a94275b5856b479fe65b9e7fef9b84fbef2bf0f8fdfb87072fa9846db8c4bf9def9aad29f6f615eb5e659f7cdbeff75e53fffd3fc3e3f5ee1c1c3e061016e112f857ba6a94275b5856ad799675b367bedd394ffef0ff0f8fcf987070fa18465b8c4bf15ee9aad09d6d615e91e659b7c5beff65e13effd2fc3e3e9d61c1e3f061a16fd1af857ba6a94277b5856b479fe65b9e7fef9b84fbef2bf0f8fa7587074f919c15b844be15ee9ea509d6d6d5ad1e7f996e79ffbe6e13efbcafc3e3e9c61c1f7e067816e11af857bafa94275b5a56a479b665b1e7fed9b84fbef0bf0f8f97387078fc18685bf46be15ee9aa509ded615ab5e659d6cd9efb74e53ffbc3fc3e3e3c61c1d3ec671d6e312fc57ba7ab4275b5b57a479966df16fbfd9784fbff4bf0f8f87f87070fc18485bf44be15ee9aa509ded615af5e77996ed9efbf4e13ffbcbfc3e3e1f61c1c3ec611d6e312fc57ba6ab4275b5956b479de65b967bef9384fbef2bf0f8f87b87070fa9846db8c4bf15ef9aad09d6d615ab5e65996cd9efb74e13ffbc3fc3e3e1c73e3c3e061416e112f857ba6b95675b58d6a4799665b167bed9384fbef0bf0f8f871cf079f818605b846be15eebae509d6d635a91e65996c59efb64e13efbc2fc3e3e1c71e1e3f061a16fd1af857ba6a95677b58d6a4799665b167bed9384fbef0bf0f8f87187070f818405b844be15ee9aa509d6d615a91e65996c59efb64e13efbc2fc3e3e1c61c1c20061016e110c044b2008025590856a4799665b167bed9384fbef0bf0f8f87187040d0104058840ba042e9aa501c4d615a91e65996c59efb64e13efbc2fc3e3e1c61c10200410162100c000b2008005110856a4799665b167bed9384fbef0bf0f8f871870207018405b8448e15e69aa501d6d415a91e65996c59efb64e13efbc2fc3e3e1c6101c34020012c112e8543a6a94264a5856a4799665b167bed9384fbef0bf0f8f8718207070184003844ae15ea9aa509d6d415a91e65996c59efb64e13efbc2fc3e3e1c418183c061012e112f857ba6a14035b5856a4799665b167bed9384fbef0bf0f8f87083030781840138048e15e21aa509d6d405a91e65996c59efb64e13efbc2))) (
.fork 37 0x3f4faf871c7870f818405b844be15ee9aa559d6d637a93e6599ec59efb6ce33efbc6 (
.fork 36 0x3f1f8f8f1a7674fb1bc75b8edff35eedfbf0fd6ded5f99e65db7c5feff65e17effd2 (
.leaf 35 0xfc7e3e3c65d5cbeaf91bfe372fffffe6eb6bfdfdc57e679976df17fbfd9785fbff4bf1f8f871bf7f0f83e507f87dfe77fedbf78fd7df15b99e65d96c5defb64e17efbc2fc7e381c6fdf0200d941f21e5c188f305ca1d152c50e6389765b177ae99381abed0bf1f80001bf7800036507c879406234c17287454914308e01d0085d61a64c068eb02fc7e00006fc00000d101e21c500089301c805112450c238074021758699301a3ac0bf1f80001a760000124058869402024c13207444814308e01d0085d61a64c068eb02fc7e000065d40000d901f21600188d204821d150450c238074021758699301a3ac0bf1e0f8f1bc077802d806b075709b0ce47229322b95f99864cb7c56cfd41617ed5d2fc4600006ede0000d940d21e50188c305ca1d152450c218074021758689301a1ac0bf100ff81b807f002da023077609b08e47229322995f09048ce5876d5d03457e4592fc403e206e01dc00b6008c1d5826c2391c8a4c8a657c2410329615b1740505f9164bf100f881a007400098003065601108c43209120895f09040ca5856c5d01417e4592fc403e206401c800b0008c150826c220080a4c88457c2410329615b1740505f9164bf1001881b8037002d8023075409b00e47229322995f09040c2185645d01417c4592fc3fffdfe1e1e3f061a16fd1af857ba6a95677b585ebdfffef5bbe7fefdbbeffef2ff0fff87f87870fc18485bf44be15ee9aa559ded617af7ff7b96ed9efbf4ebbffbcbfc3ffe1c61ffc3e069417e132f9d7fa6e977f5f585ea4ff96e5b167bed93aefbef0bf0fff87187870f818405b844be15ee9aa559d6d617a93fe5b96c59efb64ebbefbc2fc3ff81fe1ff0210496173d20c180f204835d350858bdbedee5bb67aebd3aaafed2ff0ff007f8780084104858f401000248020514c42162f6fb7b12ed96baf4eaa9fb4bfc3fc00061fe00004941721200180d204835d15005880be06c02165869932aa3ac0bf0ff00018780000104058840000024802051444016202f81b0085961a64caa8eb02fc3fbe1f61d9c3ec691d6e332fcd7ba6eb43f5b595eb4f9de65b967bef938efbef2bf0fef87d87070f818405b844be15ee9aa509d6d617ad3e77996e59efbe4e3befbcafc3f800061d8000049016212000809204801d11005880b806402165869930aa3ac0bf0fdf87b87570fa9a46df8ccbf75ff9bad8fd7d615ab5fe5b96cd9efb74e9bffbc3fc3f7e1ee1c1c3e061016e112f857ba6a94275b5856ad7f96e5b367bedd3a6ffef0ff0fd0001875000012405c848006034812087454014200f81b0085961a64c8a8eb02fc3ebe1d61e1c3f061216fd12f857ba6a95677b585eb4f9de65b967bef938cfbef2bf0faf87587270f918415b844be15ee9aa509d6d657ad3e77996e59efbe4e33efbcafc3ebe1c61ebc3e061416e112f857ba6a95675b585ea4f99665b167bed938cfbef0bf0fa000187a8000105058840000024802051444016202e0190085961a64c228eb02) (
.leaf 36 0xfd3eb89d7beb221041e163d8dc000b301c9453128d8b4b8fe67b9e7eebbb88abed3bf4fa4225c784884106858f4230002c8020514c42362c2e3f90ca79f1aeec22aeb4efd3e80007bea000041416218500009301c9451120d880b806422165869b308a3ac1bf4fa0001c780000104058840000024802051444036202e0190885961a6cc228eb06fd3e800069c8000041016218500009300c80511205880b806422165869b308a3ac1bf4f8fa71ef07df819e05b867fe15eefef709d6deb5a91e6d99ec79ffb6ee13efbc6fd3e3e9c71c1e3e061816e11af857ba6a94275b58d6a479b667b1e7fedbb84fbef1bf4f80001ef00000104058861400024c07201444834200e0190885961a6cc028eb06fd003e807a01f40026800c19d80442391c8244822d68041222321c35642904f9061bf3f90001fff800036507c879406234c172d7454934308f81f0095d61a64d868eb22fcc03e607e01fc00b6808c1dd826c2391c8a4c8a6d7c2410339655b1740555f916cbf2fff97fc7878fc18685bf46be15ee9aa559ded637af7ff7bd6fd9efbf4ffbffbebfcbfc00077fe0000d941f21600188d205835d1504d880be06c02565869936aa3ac8bf2f9ff7fc7878fc18685bf46be15ee9aa559ded635af5fffbd6ff9ffbf6fd3ffbebfcbe7e5cf1e1e3f061a16fd1af857ba6a95677b58d6ad7f96f5b767bedd3f4ffef8ff2f9f97397172f8bc40ff854bedfff9aa5a9f7f715ab5fe5bd6dd9efb74fd3ffbe3fcbe7e5ce1c1c3e061016e112f857ba6a94275b5856ad7f96f5b767bedd3f4ffef8ff2f9f871df9f0f83c507f854be57fe9ae5d9d7d735a91fe5b96d59efb64f93efbe2fcbe7e1c71e1c3e061016e112f857ba6a95675b58d6a47f96e5b567bed93e4fbef8bf2f9e173df9c88434787cf5230423c8060d14d43342b4fa5bd6dd9eba74fc2bfb63fcbe4844f1e1221041a163d08c000b20081453108d08d3e06d0a765ae9d3f0a7ec8ff2f90001df9800034507c8500042348060d1454134200f81b0095961a64d828eb22fcbe400071e000004101621000000920081451100d0803e06c025658699360a3ac8bf2f90001971000034407c850004234802081454114200f81b0095961a64d828eb22fcbe3e5c77c1efe0f181ee15afa7fbaeb94a7dbdcd6a4799675b567bed93d4fbef8bf2f8f971c7078f818605b846be15ee9aa509d6d635a91e659d6d59efb64f53efbe2fcbe0a4077c16c00d181e21488228b28180a59184d28079065025659699354f3ac8bf2f80001df00000344078850000224806001444134200e0190095961a64d028eb22fc803e407601ec00b0808c158826c228180a4c884d68041023125431640154f9068bf1ff0001bff800036507c879406234c172d745491630af81f0085d61a64cae8eb02fc7e3e3c6fc1dfe0f701ee1d7fa7fbbfbdca7dbfe57e679976df17fbfd9785fbff4bf1f8f8f1a7674fb1bc75b8edff35eedfbf0fd6ded5f99e65db7c5feff65e17effd2)) (
.fork 38 0x3fbbdfddb9057252ae06a70dcabff1b9badafb3b515f3d7c1ff7ddfeff75fdff7fb3 (
.leaf 37 0xfeef40006414000098009016001884204821c040450c21e07c025758699363a1ac8bfb00ff819007f002da023056209b08a42029322195f09048ce5976d5d03557e45b2fec03f607601ec00b0808c158826c228180a4c884d7c2410339655b1740555f916cbfb00fd81b8077002d8023075609b08e47229322995f09040ce5956c5d01557e45b2fec03f606401c800b0008c150826c220080a4c88457c2410339655b1740555f916cbfb00fd8010022002c0023014009b00000020322105f09040ce5956c5d01557e45b2fec02f6064000800900080140022802008084808457c241033865591740555f116cbfafffd7f87870fc18485bf44be15ee9aa559ded617af7ff7bd6fd9efbf4ffbffbebfebf7fdfe1c1e3f061a16fd1af857ba6a94277b5856bd7ffef5bfe7fefdbf6ffefaffafdfd7bc7878fc18685bf46be15ee9aa559ded635ab5fe5bd6dd9efb74fdbffbe3febf7f5ee1c1c3e061016e112f857ba6a94275b5856ad7f96f5b767bedd3f6ffef8ffafdf87187070f818405b844be15ee9aa509d6d615a91fe5b96d59efb64f9befbe2febf6956e1c000004101621000000920080051100508d3e06f4b765ae9d3f2a7ec8ffafd00018700000104058840000024802001444014200f81b0095961a64d8a8eb22febe3f5c61c1c3e061016e112f857ba6a94275b5856a4799675b567bed93d4fbef8bf9fcfcf987470fa1a465b8ccbf35ee9bad0fd6d615f99e65db7c5feff65e1feffd2fe7f000061d0000049016212000809204801d110050c238074021758699303a3ac0bf9f8fcf187070f818405b844be15ee9aa509d6d615f99e65db7c5feff65e17effd2fe403f206001c00020000c110804422008024480057c2410329615b1740505f9164bf8fcfc7987070f818405b844be15ee9aa509d6d615a91e65996c59efb64e1befbc2fdbefeddf1e1e3f061a16fd1af857ba6a95677b58debdfffef7bfe7feffbfcffefbff6fb0001ffb800034507c871404234c072d1454936202f81b0895961a6cda28eb26fd7e80007ffe0000d941f21e50188d305cb5d1524d8c2b807422175869b309a3ac1bf500fa81f807f002da023077609b08e472293229b5f09048cad876d5d0b417e4596fd3ffe9ff1e1e3f061a16fd1af857ba6a95677b58debdfffee7bbe7feffbaeffef3ff4ff0001eff800012505c869406034c172d7454836202f81b0885961a6ccaa8eb06fd3ebfdff1e1e3f061a16fd1af857ba6a95677b58debdf9fe77bbe7feffb9cffef3ff4fafa75c7878fc18685bf46be15ee9aa559ded637ad3e7f99ee79ffbeee33efbcefd3ebe9d69c9d3e467056e197f857bb7adc275b7b5eb4f9fe67b9e7fefbb8cfbef3bf4fafa7587070f818405b844be15ee9aa509d6d617ad3e7f99ee79ffbeee33efbcefd3ebe1c7bebc3e061416e197f857bb6bdd675b78dea4f99667b167bedb38cfbef1bf4faf871c7870f818405b844be15ee9aa559d6d637a93e6599ec59efb6ce33efbc6) (
.leaf 38 0xff75bfbb6899d18c6f1c0e3b7b4d7ab1cfc3d59335ff2e1ff2f79dfd7faf0ffb377bfdd6feec22624631bc7038adcd35e2471f06564cc7fcb87fcbde77f5febc3fecddeff403fe06801fc0026800c19d82642390c8a4c8a257c241233b61db5742d15f9165bfd00fe81e807d0009a003067601108e472091208b5f09048cad876d5d0b417e4596ff403fa06e01dc00b6008c1d5826c2391c8a4c8a657c241232b61db5742d05f9165bfd00fe81a007400098003065601108c43209120895f09048cad876d5d0b417e4596ff403fa00800900026000c095004401104800482217c241232b61db5742d05f9165bfcfffe7f87870fc18485bf44be15ee9aa559ded617af7fffb9eef9ffbfeebbffbcfff3fbfdfe1c1e3f061a16fd1af857ba6a94277b585ebdf9fe77bbe7feffb9effef3ffcfefefd87074fb19c75b8c4bf15ee9ead09d6d6d7ed3e7f9bfe7bfffefe3beffdeff3fbf9f71e1e3f061a16fd1af857ba6a95677b58deb4f9fe67b9e7fefbb8efbef3bfcfefe7d87070f818405b844be15ee9aa509d6d617ad3e7f99ee79ffbeee3befbceff3fbe1c61c1c3e061016e112f857ba6a94275b585ea4f99667b167bedb38efbef1bfcfec66d87000001040588400000248020014440162c2e3f99ce79f1aeec2aaeb4eff3f800061c0000041016210000009200800511005880b806422165869b30aa3ac1bfcf8fe7187070f818405b844be15ee9aa509d6d615a91e6d99ec79ffb6ee13efbc6feffc00065fe0000d941f21600188d204835d150458c2be07c02575869936ba3ac8bfbfdfdfb97572fabe46ff8dcbfffff9badaff7f715fbdfe5ff7ddfeff75fdfffff3feff7f7e849489caf91a9e2723fffcc6e369bdfd417ef7f97fdf77fbfdd7f7ffffcffbfdf87197570f83e407f85cbe77fe9ba58fd7d715b99fe5f96d5defb64f9fefbe2feff795ee5d50200d901f2160c188f204821d150c50ef3e97f5b777ae9d3f3afed8ffbfdbddb9750252b646fc8d88bee379bada7e5f515f3dfc1ff3ddf6ff75fdfdffb3feff4162e5d4080ad91bf236007a8d604a29d958451cb3e07d8677d879d773a7bccffbfd0001dfd800036507c8580062348160d7454134308f81f0095d61a64d8e8eb22feff40006fde0000d941f21e50188d305ca1d152450c23e07c025758699363a3ac8bfbfd0001975000036407c858006234812087454114308f81f0095d61a64d8e8eb22feff400004940000d900920600188c0040219150410c23e07c025758699363a3ac8bfbf8fdf197072f83c407b854be9fee9aa529f6f715f99e65df7d5feff65f57efff2fefe2f6065c00800d101e2140022892008085918457c2790778657d97d9755f3becbfbf800019700000344078850000224802001444114308e01d0095d61a64d068eb22fef97f7ee501ca00b001ac150c26c320080a4c88c57ef6793bdf75b3f545f7ff57cffbbdfddb9057252ae06a70dcabff1b9badafb3b515f3d7c1ff7ddfeff75fdff7fb3))))) (
.fork 45 0x3ffd0ffe1fa07f603de023877ec9feae67729766db5f8986dcfdd77f5f6bd57ecdf6 (
.fork 42 0x3ff00ff81f804a00242020073608a08c07221202935f09048ced976d5d0b557e45b6 (
.fork 40 0x3feff0001c7f800012505c8480060348120d7454036202f81b0895961a6cdaa8eb26 (
.leaf 39 0xffbfc00071e000004101621000000920081451100d880be06c22565869b36aa3ac9bfefeff7dc7078f818605b846be15ee9aa509d6d637ad3e7f9def79ffbeef7befbeeffbf7fdef1c1e3e061816e11af857ba6a94275b58d6ad7fb6f7b7e7fedfbf6ffef9ffefaff75c7878fc18685bf46be15ee9aa559ded637ad3e7f9def79ffbeef73efbeeffbe7fdcf1e1e3f061a16fd1af857ba6a95677b58d6ad7fb6f7b7e7fedfbf4ffef9ffef8ff7fc7078fc18685bf46be15ee9aa509ded635af5e7f9deff9ffbfef53ffbefffbe3fdc71c1e3e061816e11af857ba6a94275b58d6a479b677b5e7fedbbd4fbef9bfef8f871c7070f818405b844be15ee9aa509d6d635a91e6599ed59efb6cf13efbe6ffbe39c071c120004181621088000b20080051100d08038267325e7c69bb50abac9bfef80001c700000104058840000024802001444034200e0190895961a6cd028eb26ffb9ffdff121e21020a12dd18c044320081646808debde7fab7bfc37e769feff47bffee7e77fc48488400284874230000c8020510802362f69beadeff0db8da7eabd16fffaf7fd6f001e14020800c11aa8542a6a94264a50d68d5f26f7b7e7fedfbf6fdee9ffe18ff01c307878186013846ae15ea9aa509d6d435a016499cc979f5b2ed53e6ba6ff803fc07001e00020800c1188044220080244800d68041223325c35642954f9069bfdfffefe22724739bc7878adcf75f35f9f86d7dcc7fffffffbfefffffffebffffdfff7fc00069fe00004941721a50180d304cb5d152058c2be07c22175869b32ba3ac1bfdfefefda7674fb1bc75b8edff35eedfbf0fd6ded7fdbe7fdbfe7ffffefe3feffdeff7fbfbf089891cc6f1c0e2b73cd7897e7c1b5b731ff6f9ff6ff9fffffbf8ffbff7bfdfef871a7670f81a405b86dfe35eedbb70fd6de17b9be65d9ec5defb6ce3fefbc6ff7fb99f69d902004901621a5c080b304c81d112858f6b8ff67b9f7eebbb8babed3bfdfed6eda7624631bc75b8edcd35e6c73f07564cd77cae3fdbde7ff1fefc2eaefdeff7fb5bb0898918c6f1c0e2b734d7891c7c1959331df2b8ff6f79ffc7fbf0babbf7bfdfe068da76040313c7588e9412024c53a074448d674ae1bd29a7f71eefc2e8ef1eff7f80007bfa00004941621a500809305c95d1120d8c2b807422175869b30ba3ac1bfdfe0001bf7800036507c879406234c1728745491630ae01d0885d61a6cc2e8eb06ff7f800069d800004901621a500809304c81d112058c2b807422175869b30ba3ac1bfdfe0000226000012400082940202041120644480630ae01d0885d61a6cc2e8eb06ff7e3fbc69c1d3e067016e197f857bb7adc275b7a57e679b76ff1ffffdbf85fbff5bfdf80001a700000104058861400024c03201444814308e01d0885d61a6cc068eb06ff79bfbf6901d20026012c195c0443310c824482a5ff6e1fb2ff9db7f72d8ffb577bfde6fefc2002400098003025401100441200120887fdb87ecbfe76dfdcb63fed5de) (
.fork 41 0x3feffffffc787cff19ef5bfc6bf15ee9ead59ded6f7ef7fffbffffbfffffffbfffff (
.leaf 40 0xffbfffdff1e1e3f061a16fd1af857ba6a95677b58debdfffef7bfe7feffbfeffefbffeffff7fc78788418685bf4630112c8020595e4237af7fffbdeff9ffbfeffbffbefffbfffdff1e1235041a163d0ae810ba6a95473358debdfffef7bfe7feffbfeffefbffeffff7fc784884106858f4230002c8020514c4237af7fffbdeff9ffbfeffbffbefffbfffdff121e35020a12dd1ae8543a6a95666a58debdfffef7bfe7feffbfeffefbffeffff7f87070f818405b844be15ee9aa509d6d617af7fffbdeff9ffbfeffbffbefffbfffdfd1a1a3d061a12fd1af857ba6a15437b58debdfffef7bfe7feffbfeffefbffeffff7e02020701840038048e15e21a8500d6d407af7fffbdeff9ffbfeffbffbefffbfffdc71e1e3e061816e11af857ba6a95675b58dea4ffb6f7b5e7fedbbfefbef9bfeffff01c78780018605b84620112c802059564037a03fc9bcc979f5b6edfbeeba6ffbfff9f71e1c3e061016e112f857ba6a95675b58deb4fffee7bde7fefbbeefbefbbfefffd7bc7870f818405b844be15ee9aa559d6d637ab7fe5bdedd9efb7cffbffbe7ffbffe9d71e1e3f061a16fd1af857ba6a95677b58deb4fffee7bde7fefbbeefbefbbfefff973c7878fc18685bf46be15ee9aa559ded637ab7fe5bdedd9efb7cffbffbe7ffbffe1ff1e1c3f061216fd12f857ba6a95677b58debdffdee7bf67beff3eeffefbffefff871c7870f818405b844be15ee9aa559d6d637a93fe5b9ed59efb6cfbbefbe6ffbffbdff1e1627041a163d08c800b26281673348dabdfffef7bfe7febfbfeffedbffeffef7fc785884106858f4230002c8020594c4236af7fffbdeff9ffafeffbffb6fffbff9dffbeb221041e163d8dc000b301c9453128d8bdbefef7bfe7eebfbfaafedbffeffe77fdf9c88434787cf5230423c8060d14d43362f6fbfbdeff9fbafefeabfb6fffbff9dff1ff221049e173d28c180f204835d3508d8bdbefef7bfe7eebfbfaafedbffeffe77fc784884106858f4230002c8020514c42362f6fbfbdeff9fbafefeabfb6fffbff9dff121221000a121d08c000320081442008d8bdbefef7bfe7eebfbfaafedbffeffbd5bc7800501040588408a04269aa551c4d437a37fc1bdadd96fb7cffbdfba7ffbfef4071e000004101621000000920081451100de80ff06f2256596db37ef3ae9bfeff2913c78589c106858f4232002c98a059ccd236a37fc1b4a9d96fa7cffbdfb27ffbfca4071e160004181621088000b20081651100da80ff06d22565969b37ef3ac9bfeff1801c78307818405b8448e15e69aa559d6d437a03fc1b0895965b6cdbbceba6ffbfc1c3f1e0201041a163d080000920081453100d899be6ed22fe5c6bfb7aa7acbffeff0001efa8000105058861400024c07251444836202f81b0895961a6cdaa8eb26ffbfc00077e60000d141f21400108d20183451504d880be06c22565869b36aa3ac9bfeff0001c7f800012505c8480060348120d7454036202f81b0895961a6cdaa8eb26) (
.leaf 41 0xffc03fe07e009800b6008c1d5026c0311c884c8a6d7c241233b65db5742d55f916dbff00ff81e007c0009a003067601108c432091208b5f09048ced976d5d0b557e45b6ffc03fe07401e800b0808c158826c220080a4c884d7c241233b65db5742d55f916dbff00ff81b0076002d8023075609b08c43229322995f09048ced976d5d0b557e45b6ffc03fe05c01b800b6808c1dd826c23104880c8a6d7c241233b65db5742d55f916dbff00ff80b8037002d8023035409b00647229322985f09048ced976d5d0b557e45b6ffc03fe01e00bc00b6808c0dd026c01914880c8a697c241233b65db5742d55f916dbff00ff803007f002da023037609b08641228322985f09048ced976d5d0b557e45b6ffc03fe00c009800b6008c0d5026c01104880c8a617c241233b65db5742d55f916dbff00fe81f8074002d8023075601308c472091209b5f09048cad976d5d0b517e45b6ffc03f607e01c800b0008c1d5826c2301c8a4c8a4d7c241033b655b1742555f916dbff00f881f8077002d8023075609b08e472293229b5f09040cad956c5d09517e45b6ffc03e007e01c000b0008c1d5804c2301c8244824d6c241032325531642145f9069bff00e701f804800242020073600208c07201000934308008ccc974d180a546a4126ffc037a07e00dc00b6008c1d5026c0391c8a4c8a6d7c241232b65db5742d45f916dbff00d681f8024002d8023075401300c472011209b5708008cad976d1d0b506a45b6ffc02fe07e003c009680801cd02280391c88480a6d7c241233a65d95742d55f116dbff00bddbf800252a406a00f1cb8e03daff21a0bd35f3d040cfbdd64fd19757d55b7ffc02f607e016c009080801cd82282381c8a480a4d7c241033a65591742555f116dbff00bd81f8037002d8023075409b00e472293229b5f09040ce995645d09557c45b6ffc02f607e0008009000801c502280301c88480a4d7c241033a65591742555f116dbff00bd803000200240020031408a00401220202905f09040ce995645d09557c45b6ffc016a07e01fc00b6808c1dd826c2391c8a4c8a6d7c241230b65db5742d45f916dbff004201f807d002da023077601308e472091209b4308008c0c974d180a506a4126ffc00e607e01fc00b6808c1dd826c2391c8a4c8a6d7c241031a65591742555f116dbff002901f805b00242020073608a08e07229202934b09040c4895445808557c4126ffc007e07e00fc00b6808c1dd026c0391c8a4c8a6d7c241231a65d95742d55f116dbff001881f8037002d8023075409b00e472293229b5f09040c2995645d09517c45b6ffc006207e0008009000801c502280301c88480a4d7c241030a65591742545f116dbff000781f800f0025a020073408a00e472212029b4708008c6997651c0b54684536ffc000007e0000009000801c500080301c8040024d0c200030225510602141a1049bfeffffffc787cff19ef5bfc6bf15ee9ead59ded6f7ef7fffbffffbfffffffbfffff))) (
.fork 43 0x3ff08ff81f91ff002db03707760db18e472a93329b5f09648ded97ed5d0f557e67b6 (
.leaf 42 0xffc1fffffe21fe10b6a08ddddc26c2391c9e4e8aedfffc7fbbfffdb7f66dfffd57ffff07ff8ff887f042da823777609b08e472793a29b7f6f1daeedbf6d5d9b5fff45bfffc1ffe07e3ffc00bec09c1fd83ec6395cbfccca6dfc2c723bb65db5742d7ff916dbff07ff81f887f002da023077609b08e472793229b7f0b1c8eed976d5d0b5ffe45b6ffc1c0007e3e00009840901e501884305cb5c0424d8c28603822551060216ba1049bff06ff8df867f032fa7230ff61bb08e57a2f3229f7f4b05acedb76d5d8b57fe45beffc1bfe37e01fc00b6808c1dd826c2391c8a4c8a6dfd2c16b3b6ddb5762d5ff916fbff05ff8bf857f02afa6a70ff61fb19e57aaf3329b5f2d1c8eed9f6d5d1b5dff45b7ffc17fe2fe01fc00b6808c1dd826c2391c8a4c8a6d7cb4723bb67db5746d77fd16dfff02ff85f887f042da823777609b08e472793a29b7f4b05acedb76d5d8b577e45beffc0bfe17e09fc04b6848c1dd826c2391c8a4c8a7dfd2c16b3b6ddb5762d5df916fbff02ff81f8aff002db023077609b08e472793229b7f0b048ced976d5d0b577e45b6ffc07fe0fe21fc10b6a08dddd826c2391c9e4e8a6d7cb4723bb67db5746d75fd16dfff01ff83f817f00ada0a707760db19e472a93329b5f2d1c8eed9f6d5d1b5d7f45b7ffc07fe07e27fc00b6c09c1dd836c6391cbe4cca6d7c24723bb65db5742d75f916dbff00fffff807f842da823777709b08e472293a2bb5ffd07ecffff6dfd9b757f55ffffc03ffc7e01ffe0b6808c1dffa7f2bfbdca6cafed7e641b33ff5db7f42dd5f957dbff00fff1f807f802da023077709b08e47229322bb5f9906ccffd76dfd0b757e55f6ffc03ffb7e01fd8cb69c8c3dfb67f2b99fca4c8b7d7f241fb3f7ddb5762d55f917fbff00ffedf807f002da023077609b08e472293229b5fc907ecfdf76d5d8b557e45feffc03ff6fe01fd4ab69a8c3dfae7c2ffbfca6caf6d7cf41233ff7db7f46dd5fd56dfff00ffdbf807f002da023077609b08e472293229b5f3d048cffdf6dfd1b757f55b7ffc03fe97e01fe10b6a08ddddc26c2391c8a4e8aed7f241fb3b6ddb5762d55f917fbff00ffa5f807f212da123077649bc8e472293229f5fc907ecedb76d5d8b557e45feffc03fe87e01fea0b6808c1ddd26f2391c8a4c8aed7e241b33b65db5742d55f917dbff00ff93f807f842da823777709b08e472293a2bb5f3d048cef9f6dfd1b757f55b7ffc03fe3fe01fc10b6a08dddd826c2391c8a4e8a6d7db416b3b6fdb5766d55fd16ffff00ff81fd8ff002db07b077609b0ce472793229b5f09048ced976d5d0b557e45b6ffc03fe07f41fe20b681ec1ddc26c3391c8a4c8aed7c241233b65db5742d55f916dbff00ff81fc87f842da86b777709b0ce472793a2bb5f09048ced976d5d0b557e45b6ffc03fe07e01fc00b6808c1dd826c2391c8a4c8a6d7c241233b65db5742d55f916dbff00ff81f804a00242020073608a08c07221202935f09048ced976d5d0b557e45b6) (
.fork 44 0x3ff42fffffc87f842da86b777709b0ce472793a2bb7fff87ecffff6dfd9b777fd5ff (
.leaf 43 0xffd0bfe97f21fe10b6a1addddc26c3391c9e4e8aedff2e1fb3b6ddb5762d5dfb17fbff42ffa5fa27f213de123877649be8e472297669f7fcb87ecedb76d5d8b577ec5feffd0bfe97e01fc00b6808c1dd826c2391c8a4c8a6dff2e1fb3b6ddb5762d5dfb17fbff42ff81ffaff003df07b877609b2ce472797669b7f0b848ced976d5d0b577ec5b6ffd0bfe07f21fc00b681ac1dd826c3391c9e4c8a6dfc2e1233b65db5742d5dfb16dbff420001ffa8000345078871400224c0725144493630a800c08954418085268c126ffd03fe87fc1fea0f781ee1ddd26fb391c8a5d9aed7e261b33b65db5742d55fb17dbff40ffa1fc07f802da06b077709b0ce47229322bb5f8986cced976d5d0b557ec5f6ffce40007ffe0000d941f21e50188d305cb5d1524d0c21e07c22575868b361a1ac9bff29ff93fd9ff842db87f77770db1ce472f93b2bb5f3d7c8fef9fedfd1f7d7f77b7ffca7fe4fe05fc42b6829c1dd8b6c67f3caa6cee6d7cf5f23fbe7fb7f47df5fddedfff29ff81fd9ff002db07f07760db1ce472f93329b5f097c8fed97ed5d0f5d7e67b6ffca7fe07e05fc00b6809c1dd836c6391caa4cca6d7c25f23fb65fb5743d75f99edbff290001fd9800024107c071404214c072d1010934308780f0895c4180c58686326ffca3fe47f41fe60b681ec1ddca6c33f3c8a6caeed7c659237be5fb7f43dd5f9dedbff28ff81fd07f002da07b077609b0ce472293229b5f09648ded97ed5d0f557e67b6ffc9ffe7ff21fe10b6a1addddc26c3391c9e4e8aedfdfc76bbbefdb7f66dfffd56ffff21fffffc87f842da86b777709b0ce472793a2bb5ffd1feeffff6dfd9b7d7f55ffffc87fe4ff21fe10b6a1addddc26c3391c9e4e8aed7cf4723bbe7db7f46df5fd56dfff21ff93f807f002da023077609b08e472293229b5f3d1c8eef9f6dfd1b7d7f55b7ffc87fe07f21fc00b681ac1dd826c3391c9e4c8a6d7c24723bb65db5742d75f916dbff20ff91fc07f802da06b077709b0ce47229322bb5f19048cef976dfd0b757e55b6ffc7c0007efe0000d940d21e50188c305cb5d1524d8c29e07c22575868b36ba1ac9bff18ff81fb7ff003ff03787f60fb38e572af7769b5f09649ded97ff5f2fd57e6fb6ffc63fe07ec1fde0f780ce1dfba7fabfbdca7dbf6d7c259277b65ffd7cbf55f9bedbff18ff81f857f52afa6a70ffebff1bffffafb3bdb5f09649ded97ff5f2fd57e6fb6ffc639c07edf2000d9c0d21ed8188e305ca1d1524d0c218277325f7c68bb51a9ac9bff180001fb78000365034879406230c17287454934308601d0895d61a2cd0686b26ffc600007ec00000d100c21c500088301c8051124d0c21807422575868b341a1ac9bff180001f850000260024079406210c17287010934308601d0895d61a2cd0686b26ffc43fe07e99fd8cff9c8e3ffb6ffab9dfcbdd9b7d7c241273b65dfd7caf55f936dbff08ff81f91ff002db03707760db18e472a93329b5f09648ded97ed5d0f557e67b6) (
.leaf 44 0xfff1fffbfe21fc10b6a08dddd826c2391c9e4e8a6dffbe7fbbf7fdb5776d7fff17ffffc6fffff807f842da823777709b08e472293a2bb7fff87ecffff6dfddb77ffd5fffff1bffb7f21fe10b6a1addddc26c3391c9e4e8aedff2e1fb3f7ddb5772d5ffb17fbffc6ffedf807f002da023077609b08e472293229b7fcb87ecfdf76d5dcb57fec5fefff1bfe07e01fc00b6808c1dd826c2391c8a4c8a6dfc2e1233b65db5752d5ffb16dbffc0ffe1f807f002da023077609b08e472293229b5f8986ccfdd76d5d4b557ec5f6ffefc0007e3e00009840901e501884305cb5c0424d8c29e07c22575869b36ba1ac9bffbdffdbf857f52afa6a70ffebff1bffffafb3bdb5f3d7c9fffdfffff7ffdff7fb7ffef7ff68c14994abe1a9c2f72ffc4d7e7e9acef617cf5f27fff7ffffdfff7fdfedfffbdff81f857f002fa02707f60fb18e572af3329b5f097c9fed97ff5f6fddfe6fb6ffef79d6fe1520009880901ed81886305ca1c0424d0cf1e27f7b7f7ee9fbf3adec9fffbdbddbf850252a606a40f9cbee13dbffa7a1bd35f3d7c1ffbddf6ff7dfdfd7fb7ffef41e2fe143c0a9e9a903ed07a84795ea9c84a6d1cb1e27da67fdc79ff73a5bcdfffbd0001fdd800026107c079406214c172d7010934308781f0895d61a6cd8e86b26ffef40007ede0000d940d21e50188c305ca1d1524d0c21e07c22575869b363a1ac9bffbd0001f850000260024079406210c17287010934308781f0895d61a6cd8e86b26ffef40000c1400009800900e5018841044a18042410c21e07c22575869b363a1ac9bffb8ffd1f807f502da023077ea9f0afef729b2bdb5f19649dffd7ffff6ff57e7fb6ffee3fe07e01fc00b6808c1dd826c2391c8a4c8a6d7c259277b65ffd7dbf55f9bedbffb80001f800000240020071400200c07201000934308601d0895d61a6cd0686b26ffe9fff7fe21fc10b6a08dddd826c2391c9e4e8a6dfdfc76bbfffdb7f76dfffd56ffffa5fffff807f842da823777709b08e472293a2bb5ffd1feeffff6dfddb7dff55ffffe97ff6ff21fe10b6a1addddc26c3391c9e4e8aed7cf4723bff7db7f56df7fd56dfffa5ffdbf807f002da023077609b08e472293229b5f3d1c8effdf6dfd5b7dff55b7ffe97fe07e01fc00b6808c1dd826c2391c8a4c8a6d7c24723bb65db5752d77f916dbffa0ffd1f807f002da023077609b08e472293229b5f19048cffd76dfd4b757e55b6ffe53ff27e11fd08be988c3ffa6fc2b9dfcbcc8b6d7c241273f75dfd7daf57f936dbff84ffc9f807f002da023077609b08e472293229b5f09048cfdd76d5d4b55fe45b6ffd8ffedff21fe10b6a1addddc26c3391c9e4e8aedfffe7fbbbefdb7f66dfdff57ffff5a0001fff800036507c879406234c172d745493630ae01d0895d61a2cd268eb26ffd1ffebff21fe10b6a1addddc26c3391c9e4e8aedffbe7fbbb6fdb5766d7fff17ffff42fffffc87f842da86b777709b0ce472793a2bb7fff87ecffff6dfd9b777fd5ff)))) (
.fork 48 0x3ffff0781fff8f0037f07c87b40ea34e572f76569b670af89f6997f71e6fdee8ef36 (
.fork 46 0x3ffefff81fd9ff002db07f07760db1ce472f93329b7f0bfc8fed97ed5d4f5ffee7b6 (
.leaf 45 0xfff9ffffff21fe10b6a1addddc26c3391c9e4e8aedfffe7fbbfffdb7f76dffff57ffffe7fffffc84a84242868773708a0cc07271282b37fff9feeffff6dfddb7fffd5fffff9fffffe01fc00b6808c1dd826c2391c8a4c8a6dfffe7fbbfffdb7f76dffff57ffffe7ffffe487c8409a84b76770110cc432591a0ab7fff9feeffff6dfddb7fffd5fffff9fffff521ea10b0a1add58c26c320081e4e88cdfffe7fbbfffdb7f76dffff57ffffe7ffff7486e842da86b777709b0cc412703a2bb7fff9feeffff6dfddb7fffd5fffff9ffff8c009800b6008c0d5026c01104880c8a61fffe7fbbfffdb7f76dffff57ffffe7fff1fc87f802da06b077709b0ce47279322bb7f9b9eceffd76dfd4b7ffed5f6fff9fffb7f21fc00b681ac1dd826c3391c9e4c8a6dff2e7fbbf7ddb5772d7ffb17fbffe7ffdbfc87f002da06b077609b0ce472793229b7f3f9c8effdf6dfd5b7fffd5b7fff9ffe97f21fe10b6a1addddc26c3391c9e4e8aedff2e7fbbb6ddb5772d7ffb17fbffe7ff93fc87f842da86b777709b0ce472793a2bb7f3f9c8eef9f6dfd5b7fffd5b7fff9ffe3ff21fc10b6a1adddd826c3391c9e4e8a6dfdbe76bbb6fdb5776d7fff16ffffe7ff81fc87f002da06b077609b0ce472793229b7f0b9c8eed976d5d4b5ffec5b6fff9f9dfff21221090a1a1dcdc0083301c944202cd8ffa6fbb7bfd36e369fbaf45bfffe7bddbfc80200240068071408a04c07271202937f3f9c0efbdd64fd597ffdd5b7fff9c6207f20dc00b601ac1d5026c1391c9e4c8a6dfc2e7038a6559175256ff316dbffe70001fc80000240068071400204c0725100093630a980e08954418485ae8c126fff9bfff7f01fe00b681ac1ddc26c3391c8a4c8aedff6e1fb3ffddb7f72ddffb57fbffe5fffbfc07f802da06b077709b0ce47229322bb5fbd9eceffdf6dfd5b7dffd5f7fff8bffd7f21fe10b6a1addddc26c3391c9e4e8aedff6e1fb3ffddb7f72dddfb57fbffe1fff3fc87f842da86b777709b0ce472793a2bb5fbd9eceffdf6dfd5b7d7fd5f7fff83fffff01fe10b6a1addddc26c3391c8a4e8aed7ff61fb3fffdb7f76dd5ff57ffffe0fff1fc07f802da06b077709b0ce47229322bb5f9986ccffd76dfd4b757ed5f6fff83fe07f01fc00b681ac1dd826c3391c8a4c8a6d7c261233b65db5752d55fb16dbffde0001fb78000365034879406230c1728745493630ae01d0895d61a6cd2e8eb26fff5bffb7e99fd8cff9c8e3ffb6ffab9dfcbdd9b7dff2e1ff3f7ddfd7faf5ffb37fbffd6ffec32626633fc7238bdcdbfe2471f26766dc7fcb87fcfdf77f5febd7fecdfefff5bfe07e99fc00ff808e1fd82eca395c8bdd9a6dfc2e1273b65dfd7daf5ffb36dbffd6d6edfa624633fc7238fdcd37e2c77f07564df77ca83fcbdf77f1febd2eacdfefff580007e980000d900821e500888305c81d1124d8c2a007022555869a34ba3249bffd0ffe1fa07f603de023877ec9feae67729766db5f8986dcfdd77f5f6bd57ecdf6) (
.fork 47 0x3ffff000dfff800336577c8f9416234c17ad745497634af93f08b5d61aecdae8eb2e (
.leaf 46 0xffffc002fffe000ad95bf23e50588d705eb5d1524d8cbbe07c22775869f36ba7ac9fffff0001fffd90036707c87b60623ce172df45493630af81f0895d61a6cdae8eb26ffffc0007fff4220d941f21e5c188f305cb7d152cd8c2be07c22575869b36ba3ac9bffff0001fffc88436787cf7b70623cc172d74d4b3630af81f0895d61a6cdae8eb26ffffc0007ffe0000d941f21e50188d305cb5d1524d8c2be07c22575869b36ba3ac9bffff0001ff80000344078871400224c0725144493630af81f0895d61a6cdae8eb26ffffc0007f3400009801b01e501885305cb5c0424d8c2be07c22575869b36ba3ac9bffff0001fa70000364024879406230c1728745493630af81f0895d61a6cdae8eb26ffffc00079f800004901621a500809304c95d1120d8c2be07c22575869b36ba3ac9bffff0001d7d000036407c8580062348120d745413630af81f0895d61a6cdae8eb26ffffc0006ddc0000d901f21e50188d304ca1d152458c2be07c22575869b36ba3ac9bffff000176f000036406c879406234c112d645493630af81f0895d61a6cdae8eb26ffffc0002ede0000d940d20e50188c105ca1d152418c2be07c22575869b36ba3ac9bffff00007af80003650248394062304152d645492630af81f0895d61a6cdae8eb26ffffc0000dfe0000d941f20e50188d1044b59152418c2be07c22575869b36ba3ac9bffff0000327000036402483940623041128645490630af81f0895d61a6cdae8eb26ffffbfff7fd9ffecff9dee3fffeffbbfffcbfdbffdff6f9ff7ffdfffffbfdffbfffbfffe0001ff60000364078879402224c1720744493630ae01d0895d61a6cd2e8eb26ffff7ffeffd5ffeaff9bfe3fffffffffffebfdffed7ef7fb7fff7ffffdfff7ffffdffffd0001ff5000036407c879406234c17287454934308f81f0895d61a6cd8e8eb26fffe80007fea0000d141e21c500089301c9451124d8c2b807422575869b349a3ac9bfff90001ff9800034507c871404234c072d1454934308f81f0895d61a6cd868eb26fffe3ffc7fc1ffe0f781ee1dffa7fbbfbdca7dbfed7e679b77ff5ffffdbfd5fbffdbfff8ff81ff07f003de07b877609b2ce472297669b5f09e49ded97ff5f6fd57eefb6fffe3e1c7fc1c3e0f101ee1d7f85fbb6bdc275b7cd6e6799767b577bedb3c5fbef9bfff8e771ff0488034607887370022cc07201444b34398e2ddded7dfba6ef46afb66fffe01e07fc03c00d781e21cd02289391c88591a6d1c238275a65fdc79bf51a3bcdbfff80001ff7800036507c879406234c17287454934308e01d0895d61a6cd068eb26fffe00007fc00000d101e21c500089301c8051124d0c23807422575869b341a3ac9bfff7fffffee7fe73fef6bffffdbfeee77f7f7e6ff7fff9ffeffff7ffffbffffddfffffbffffff67fe10b6e1fddddc36c7391cbe4ecaedffffffbfffffb7f77dffffdfffffefff81fd9ff002db07f07760db1ce472f93329b7f0bfc8fed97ed5d4f5ffee7b6) (
.leaf 47 0xffffc1dffffe2210d9e1f3ded4188d305cb5d352cd8ffbeffd6bff5eebfbfba7edbfffff070ffff880436787cf7b406234c172d74d493636ef9bf48bfd71afedee9eb2fffffc1c07ffe2000d9c1f21ed0188d305cb5d1524d8c2be27d225f5c69bb7ba3ac9bffff068dfff840337d77c8f9416234c57ad74549f674af9bf29b7f71eefdae8ef3effffc1a07ffe1000df41f21e50188d315cb5d1526d9c2be27ca65fdc79bf6ba3bcdbffff060dfff800036507c879406234c172d745493634af9bf08b7d71aeedae8eb2effffc162fffe080ad95bf23e507a8d705ebdd95a4d9cbbe07da677d879f77ba7bcdfffff0581fff820036507c87940ea34c172f765693670af81f6995f61e6ddee8ef36ffffc142fffe0000d941f21e50188d305cb5d1524d8cbbe07d22775869f37ba7ac9fffff0489fff800236567c8f9416234c17ad745493670af81f2995f61e6ddae8ef36ffffc0817ffe2010d9e1f3ded0188d305cb5d3524d8d2be6fc22df5c6bbb6ba3acbbffff0205fff840137d17c879406234c572d74549f634af9bf08b7d71aeedae8eb2effffc0807ffe3400dfc1f21ed0188d395cb5d1526d8c2be27c225f5c69bb6ba3ac9bffff0103fff880436787cf7b406234c172d74d493632ef81f489dd61a7cdee9eb27ffffc040fffe0802d943f21e503a8d705cbdd95a4d8cbbe07d22775869f37ba7ac9fffff0101fff8b0036707c87b40ea34e172f765693630af81f4895d61a6cdee8eb26ffffc0207ffe1c00df41f21e503a8d395cbdd95a6d9c2be07ca657d879b76ba3bcdbffff0081fff840337d77c8f9416234c57ad74549f670af81f2995f61e6ddae8ef36ffffc0207ffe080ad95bf23e507a8d705ebdd95a4d9c2be07ca657d879b76ba3bcdbffff007ffff808436587cf79506234c172d74d4b363fefb7f1afdd6bafcfae9fb6fffffc01c7ffe03e0d941f21e7799bdb6fdf5f177cd8e6be97c6b575ae9b3eba3ed9bffff0071fff808036507c879506234c172d7454b3639afa5f1ad5d6ba6cfae8fb66ffffc01b7ffe018cd95df23e7359bdb0dff5d1535d8f2bedfc63d7586bb36ba3adbbffff006dfff800036507c879406234c172d74549363cafb7f18f5d61aecdae8eb6effffc016fffe014ad95bf23e72d98df6fff5f1774d8cfbe07c6b775ae9f3eba7ec9fffff005bfff800036507c879406234c172d745493633ef81f1addd6ba7cfae9fb27ffffc0097ffe0210d961f3de54188d305cb5d352cd8f2bedfc22d7586bb36ba3adbbffff0025fff802136517c8794462f4c172d74549763cafb7f08b5d61aecdae8eb6effffc0087ffe02a0d941f21e5518bd305cb5d152cd8e2be97c22575869b36ba3ad9bffff0013fff808436587cf79506234c172d74d4b3633ef81f0a9dd6ba7cfae9fb27ffffc003fffe0010d961f3de50188d305cb5d3524d8dbbe4fc22f7586bf36ba7acbfffff000dfff800336577c8f9416234c17ad745497634af93f08b5d61aecdae8eb2e))) (
.fork 50 0x3ffffd681fffa4003fd07f87d407334c572d75749b770af89fad97ff1f6fdaeaefb6 (
.fork 49 0x3ffff4225fffa4213fd17f87d4473f4c572d75749f63cafbff0cb7df1aeedaeaeb6e (
.leaf 48 0xffffd0897ffe0000d941f21e50188d305cb5d1524d8f2beffc32df7c6bbb6babadbbffff4201ffffd003ff07f87f60733ce572df5749b630af89f0c97df1a6edaeaeb26ffffd0807fff2000d9c1f21ed8188f305cb5d1524d8c2be27c325f7c69bb6babac9bffff4021ffff0a83e507f87d7473fcc172df574b3638afa5f0c95de1a6cdaeaeb66ffffd0087fff0200d941f21e5c188f305cb5d152cd8e2be97c32577869b36babad9bffff2f81fffdf0037f07c87b60ea3ce572ff6569b6f0bfc9f6997f75e6fdffcef36ffffca44ffff6e10d9e1f3dedc3a8f385cbfdb5acdacfff07d2a775be9f3fff7ec9fffff2913fff8210b650fc87942ea35d9f2f7e5f936b3ffc1f4a9dd6fa7cfffdfb27ffffca407fff6c00d9c1f21ed83a8f385cbfd95a4dac2ff07d22575969b37ff3ac9bffff2901fff820036507c87940ea34c172f7656936b0bfc1f4895d65a6cdffceb26ffffca047fff4260d941f21e5c988f367cb7f176cdac6ff07c2a575be9b3eff3ec9bffff2801fffd00036507c87960623cc172df454936b0bfc1f0895d65a6cdbfceb26ffffc9c7ffff2210d9e1f3dedc188f305cb5d352cd8dfbe6fd2aff5eebfbfba7ecbfffff217ffffc88436787cf7b70623cc172d74d4b363fefb7f5afdd6bafcfee9fb6fffffc844ffff2210d9e1f3dedc188f305cb5d352cd8cfbe07d2a775ae9f3fba7ec9fffff2113fff800036507c879406234c172d745493633ef81f4a9dd6ba7cfee9fb27ffffc8407fff2000d9c1f21ed8188f305cb5d1524d8c2be07d22575869b37ba3ac9bffff2011fffc08036507c87970623cc172d7454b3631af81f0a95d6ba6cfae8fb26ffffc6207ffedc00ff41fe1f503ecd395cbfddda6dfc2ff07ca657d97db76ff3bedbffff1881fff8252b656fc8f9cbee37dbfff7e5fd37f0bfc1f2995f65f6ddbfcefb6ffffc6207ffe0800d941f21e503a8d305cbdd95a4dfc2ff07ca657d97db76ff3bedbffff1801fffb0783e507f87dce77f6dbf7dfd7dd37b0bfc1f0895d65b6cdbfceba6ffffc4207ffe918cff5dfe3f735dfdb1dff5d5d37ddc2be07ca657d87db76ba3bedbffff0801fff930036507c87940ea34e172ff656936b0bfc1f0895d65a6cdbfceb26ffffc1e3fffe3c10dfe1f3ded03a8d395cbddb5a6d9dbbe6fda6ffdc7bff7ba7bcffffff078ffff8c0737ff7cffb416234c57ad74d49f676ef9bf69bff71effdee9ef3fffffc1e3fffe281ad9fbf3fed07a8d705ebddb5a4d9dbbe6fda6ffdc7bff7ba7bcffffff078ffff8603b7d7fc8f941ea35c57af76569f676ef9bf69bff71effdee9ef3fffffc1e38c9c180edf1e922e507a8c5146a9995a719dbbe6fda6ffdc7bff7ba7bcffffff078dfff8f0337f77c8fb41ea34e57af76569f674af9bf69b7f71eefdee8ef3effffc1e2fffe3c0adfdbf23ed07a8d795ebdd95a6d9cbbe27da67fdc79ff7ba7bcdfffff0781fff8f0037f07c87b40ea34e572f76569b670af89f6997f71e6fdee8ef36) (
.leaf 49 0xfffff4187ffe8180f941fe1f731dfdb0ddf5d5d34dce2be97e7357786db36babaf9bffffc76ffff880436787cf7b406234c172d74d49363eefbffdcffdf1afedeebeb6ffffff1bb7ffe100cdf5df23e50588d315eb5d1527d9f2beffef7dffc7bbf6babbdfbffffc67ffff808436587cf79506234c172d74d4b363fefbff9effdfbafefaebfb6ffffff19b7fff2210d9e1f3dedc188f305cb5d352cd8f2beffe73df7c6bbb6babadbbffffc66dfff800036507c879406234c172d74549363cafbff9cf7df1aeedaeaeb6efffff1807ffe0000d941f21e50188d305cb5d1524d8c2be27e325f7c69bb6babac9bffffc061fff800036507c879406234c172d745493638afa5f9cd5de1a6cdaeaeb66ffffefe07ffe3c00dfc1f21ed03a8d395cbdd95a6dfc2ff27fa65fdd7dbf7ff3bedbffffbddbfff8252b656fc8f9cbee37dbfff7e5fd37f3ffc1ffbddf6ff7dfffdffb7ffffef76fffe0800d941f21e503a8d305cbdd95a4dfcfff07fef77dbfdf7fff7fedfffffbdda3270252b646a48b9cbee335b9fa6e5fd07f3ffc1ffbddf6ff7dfffdffb7ffffef62fffe080ad95bf23e507a8d705ebdd95a4dfcbff07fa677d97df77ff7bedfffffbd81fffdb0036707c87b60ea3ce172ff656937f0bfc1fe995f65f6ddffcefb6ffffef607ffe0800d941f21e503a8d305cbdd95a4dfc2ff07fa657d97db77ff3bedbffffb851fff805036507c879ca6636dbf7d7c5dd37b1bfc1f9ad5d6fb6cfbfcfba6ffffee007ffe0000d941f21e50188d305cb5d1524dec2ff07e2257596db36ff3ae9bffffa75ffff880436787cf7b406234c172d74d493637ef9bfdaffd7bafefee9fb2fffffe976fffe080ad95bf23e507a8d705ebdd95a4d9cfbe07fef77daf9f7fba7fcdfffffa57ffff808436587cf79506234c172d74d4b363fefb7fdafdd6bafcfee9fb6fffffe956ffff2210d9e1f3dedc188f305cb5d352cd8cfbe07f6b775ae9f3fba7ec9fffffa55bfff800036507c879406234c172d745493633ef81fdaddd6ba7cfee9fb27ffffe9407ffe0000d941f21e50188d305cb5d1524d8c2be07f22575869b37ba3ac9bffffa051fff800036507c879406234c172d745493631af81f9ad5d6ba6cfae8fb26ffffe5327ffe0108d959f23e72598db0dff5d1534ddc2be07ee757d87db76ba3bedbffff9481fff800036507c879406234c172d745493770af81fa995f61f6ddae8efb6ffffe1127ffe0000d941f21e50188d305cb5d1524d8c2be07e63575869b36ba3ac9bffff6337fffc88436787cf7b70623cc172d74d4b363fefbff4ebfdfbafefeebfb6fffffd1cbffff2210d9e1f3dedc188f305cb5d352cd8fbbeffd32ff7c6bfb7bafadbfffff427ffffc88436787cf7b70623cc172d74d4b363fefbff1effdfbafefaebfb6fffffd0897fff2210d9e1f3dedc188f305cb5d352cd8f2beffc32df7c6bbb6babadbbffff4225fffa4213fd17f87d4473f4c572d75749f63cafbff0cb7df1aeedaeaeb6e)) (
.fork 51 0x3fffff801ffff0003e507f87d60733cc172df574937b0bfc1f8c95de5b6cdbfeeba6 (
.leaf 50 0xfffffdffffffb39cfffdffffff5dffb1dff5d7d3fddffbeffffffffefffffbafffffffffef7ffffdb8436787cf7b70ea3ce172ff6d6b36bffffffdeffdffafefffffb6ffffffbc07fff6c00d9c1f21ed83a8f385cbfd95a4dac2ff27f325f7d69bb7ffbac9bffffe7fffffcf8437f87cf7b70ea3ce572f76d6bb67fefbffffffffbefffeebff7ffffff9ffffff321cdffdf3fedc588f315eb5d352fd9ffbeffffffffefbfffbaffdffffffe7fffffca86b67efcffb71ea3dc17af76d6b367fefbffffffffbefffeebff7ffffff9e07fff3c00dfc1f21ed83a8f395cbdd95a6d9c2be27fb65ffc79bf7babbcdbffffe77ffffc88436787cf7b70623cc172d74d4b363fefbffdeffdfbafefeebfb6ffffff9dffffe0000d941f21e50188d305cb5d1524d8ffbefff7bff7eebfbfbafedbfffffe77fff84884346878f7370022cc072514c4b363fefbffdeffdfbafefeebfb6ffffff9dfff35221098a1b1dedc1887305cb5c242cd8ffbefff7bff7eebfbfbafedbfffffe77fe7e4884126858f6b70202cc132574c4a363fefbffdeffdfbafefeebfb6ffffff9dff5f52210d9a1f3d68c188f204835d350cd8ffbefff7bff7eebfbfbafedbfffffe77f76f488436686cf7b70623cc112d64d4b363fefbffdeffdfbafefeebfb6ffffff9df8c9c0000d900920e50188c1044a19152418ffbefff7bff7eebfbfbafedbfffffe771fffc88036707c87b70623cc172d7454b3639afadfded7dfba6efeeafb66fffff9db7fff2000d9c1f21ed8188f305cb5d1524d8f2befff73df7c6bbb7babadbbffffe75bfffc80036707c87b60623cc172d745493633ef89fdedfdfba7efeebfb27fffff9c97fff2210d9e1f3dedc188f305cb5d352cd8f2befff32df7c6bbb7babadbbffffe713fffc88436787cf7b70623cc172d74d4b3633ef89fce9fdfba7efeebfb27fffff9c3ffff2010d9e1f3ded8188f305cb5d3524d8dbbe6ff32ff7c6bfb7bafacbfffffe701fffc80036707c87b60623cc172d745493630af89fcc97df1a6edeeaeb26fffff99f7fff0200d941f21e5c188f305cb5d152cd8f6beffe7bdf7eebbbebabedbbffffe57bfffc08036507c87970623cc172d7454b363befa5fdedddeba7cfeebfb67fffff89d7fff2210d9e1f3dedc188f305cb5d352cd8f6beffe7bdf7eebbbebabedbbffffe173fffc88436787cf7b70623cc172d74d4b363befa5fdedddeba7cfeebfb67fffff81fffff0210d961f3de5c188f305cb5d352cd8ffbedfe7bf77aebf3ebafedbfffffe071fffc08036507c87970623cc172d7454b3639afa5f9ed5deba6cfaeafb66fffff8007fff0000d941f21e58188f305cb5d1524d8c2be07e32577869b36babac9bffffd6edfffa4633fd77f8fdcd77f6c77fd7574df77cafbffbdf7ff1fefdaeaeffefffff5bb0c9c918cff1c9e2f735dfc91c7e195d371df2beffef7dffc7fbf6babbffbffffd681fffa4003fd07f87d407334c572d75749b770af89fad97ff1f6fdaeaefb6) (
.leaf 51 0x3fffffffffffff843ff87ff7f70fb3ce572ff7f6bb7fffffffffffffffffffffffffffffffffffff2b5ad9fbf3fefefb8ff6fffdfb7fcdfffffffffffffffffffffffffffffffffffffca8436787cf7b70ea3cc172f76d6b37ffffffffffffffffffffffffffffffffffffe99ceff5ffe3f73fffdf7fffdfdff7dffffffffffffffffffffffffffffffffffff87ffc3de87bf77fe9feefef779feffb7fffffffffffffffffffffffffffffffffff35ff5abebbbdfffeffc7ffffffeeefedfffffffffffffffffffffffffffffffffffa77f73bfe7a78ffeffffbffffaff7fdf7ffffffffffffffffffffffffffffffffff9f9f3fc6fbd6ffbffcd7bb7efd7f7b7bdffffffffffffffffffffffffffffffffffd7d7afebe6efffdebfffff9badfffff737fffffffffffffffffffffffffffffffffeddddbeeff1ffe3f7ffffff7efebfdfff5ffffffffffffffffffffffffffffffffff76f6ef7bfefeffffffffffdf9ff6fffff7fffffffffffffffffffffffffffffffff8c9c99ceff1e9e2f73fffcd7e7e9bdff71fffffffffffffffffffffffffffffffffe22624731bc7038adcf35e25f9f06d6dcc7ffffffffffffffffffffffffffffffffc7fffffe0ffc1fe1fffbfffbffdfffdffedfe6ffb7fff5ffffdbffffbffdbffffffedfffff633ff77f8ffedfffee77fff776df7fcbfffffdf7ff5fefdffeeffefffffff6fffffd4affdbfe3ffaffcffffffffdff6dfcfff27fff7ffffdfffffffedfffffff81fffff003ff07f87f60fb3ce572ff7769b7f0bfc9fed97ff5f6fdffeefb6ffffffe07fff2800d9c1f21ed83a8f305cbdd95a4dfc2ff27fb65ffd7dbf7ffbbedbffffff7fffff8fc3e787ff7ffe77fedbf7dfdfdf37bffffffdeffdffbfefffffbefffffffbf7fffd3ecff5dfe3f7fddffb7fff7f5f7fdff6ffffeffdfffffbfeffbfffbfffffdfbffff2fabe56ff8fdffffffdbfffff7ff37fbffe5fffddfeff7dfffffff7fffffe1c7fffc3e0f941fe1f7f9dffb6fdf7f5f7cdee6ff97e7b577bedb3effbef9bfffff801ffff0003e507f87d60733cc172df574937b0bfc1f8c95de5b6cdbfeeba6))))))⟩

def decodeBank (dict : PackedSeq) : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, packed =>
    if packed = 0 then []
    else BitVec.ofNat 270 ((expanded.at ((packed % 4096) - 1)).getD 0) :: decodeBank dict n (packed / 4096)

def tableFrom (dict : PackedSeq) (banks : ℕ → PackedSeq) (t : ℕ) (ws : List W) : Bool :=
  match encodeBank dict ws with
  | none => false
  | some key =>
    match findKey (banks t) key with
    | none => false
    | some _ => ws == decodeBank dict 11 key

theorem tableFrom_sound (dict : PackedSeq) (banks : ℕ → PackedSeq) (t : ℕ) (ws : List W)
    (h : tableFrom dict banks t ws = true) :
    ∃ i key : ℕ, (banks t).at i = some key ∧ ws = decodeBank dict 11 key := by
  unfold tableFrom at h
  split at h
  · simp at h
  · next key e =>
    split at h
    · simp at h
    · next i hk => exact ⟨i,key,findKey_sound _ _ _ hk,beq_iff_eq.mp h⟩

def blockCheck (dict : PackedSeq) (banks : ℕ → PackedSeq) (t start count : ℕ) : Bool :=
  (List.range count).all fun i =>
    closedState (tableFrom dict banks) t (decodeBank dict 11 (((banks t).at (start+i)).getD 0))

theorem blockCheck_sound (dict : PackedSeq) (banks : ℕ → PackedSeq) {t start count i key : ℕ}
    (h : blockCheck dict banks t start count = true) (ilo : start ≤ i) (ihi : i < start+count)
    (hk : (banks t).at i = some key) : closedState (tableFrom dict banks) t (decodeBank dict 11 key) = true := by
  have idx : i-start ∈ List.range count := List.mem_range.mpr (by omega)
  have result := List.all_eq_true.mp h _ idx
  have back : start+(i-start) = i := by omega
  simpa [back,hk] using result


set_option maxRecDepth 16000 in
def dict : PackedSeq := ⟨1655, 64, 0xffffffffffffffff, .fork 26 0xdbffc0001ffe0000 (
.fork 13 0x2480000076000000 (
.fork 6 0x80400016260000 (
.fork 3 0x3fff0001ffec (
.fork 1 0x108900012210 (
.leaf 0 0x108900009084000010800001f4000000101c0001c3e0000010080001c2a000000e040001c3e000000a448000084200000a4000016c0000000a04000142600000084480012210000006200000dde0000006200000dd4a000006200000dc00000006200000d1ec000006200000c9ea00000620000099ce000006200000094a0000061c0000c3e0000006000000c1e0000004200000918c000001e000003c00000001c380002010000001a30000100c000001628000080a0000001f800002100000001c000003e00000001b0000018c000000168000014a00000000736200000000000072016400000000006141422000000000512122100000000000000000) (
.fork 2 0x3e1f0001c3ec (
.leaf 1 0x3e1e8001c3ea00003e1c6141c3e000003e1c0001c3e000003e1c000081c000003e140001c14000003e000001c1e000003e000001c00000003dff8001b39c000039df80012210000039c0000120000000381c00010200000037bb0000d1ec000037bb000099ce000036180000c1e0000035bf800091ce000035bf000093ec000035bb0000918c000035a0000090000000341c000083e000003418000081800000319b0000000000002f768000dd4a00002f768000c9ea00002f76800099ce00002f768000094a00002f600000080000002e140000c1e000002e140000014000002956800000000000253200000108000016080001c3e00000108900012210) (
.leaf 2 0x3ffe8001ffea00003ffc0001ffe000003ffb0001fd8c00003ff68001fd4a00003ff68000994a00003ff40001fd4000003fe00001fde000003fe00001fd4a00003fe00001fc0000003fdf8001e3f000003fdc0001e3e000003fbf0001d3ec00003fbf000091cc00003fbc0001d3e000003f9f0001c3e000003f7e8001cbea00003f7e800089ca00003f7c0001cbe000003f768001c94a00003f5e8001c3e000003f3e0001c3e800003e9d0001e3f000003e9d0001d3e400003e9c0001f7e000003e5c8001e3f000003e5c8001cbe200003e5c0001efe000003e3c0001dfe000003e3c0001d3ec00003e3c0001cbea00003e1f8001c3f000003e1f0001c3ec))) (
.fork 4 0x25001200100108 (
.leaf 3 0x1080090120021000108009008800840010800001ea000000103e1c01c1c3e00010000801c002a0000a400480040042000a400001660000000a00040140026000084004812002100006000000de014a0006000000de00000006000000d801ec0006000000d401ea0006000000c001e000060000009c01ce000600000014014a000400000098018c0001c003802000100001c000003e0000000180030018000c000140028014000a00003fff8001fff000003fff8001ff5a00003fff8001fe1000003fff8001fdce00003fff8001f3fc00003fff8001ebfa00003fff8001dbee00003fff8001bbde00003fff80012b5a00003fff800099ce00003fff0001ffec) (
.fork 5 0x3f401e809401ca (
.leaf 4 0x3f401681d4014a003f001e01d003e8003e3e1c01c1c3e0003e001c01d803ec003e001c01d403ea003e001c01c003e0003e000001c00000003dc01f81b8039c0039fe1f8121c3f00039f9df812122100039c01f812002100039c0000120000000383e1c0101c3e00038001c010002000037801b00d801ec0037801b009c01ce0035b5bb0098918c0035801f809801ce0035801f009803ec0035801b0098018c003580000098000000340018008001800031801b00000000002f6f768014094a002f401680de014a002f401680d401ea002f4016809c01ce002f40168014014a002f400000140000002e00140000014000294016800000000025001200100108) (
.leaf 5 0x80004016002c00004000200e1e1c00004000200e1e080a004000200e141c0a004000200e001c00004000200c1c180e004000200818100c004000200414080a004000000e1e0000003fffe001fffc00003fc01f81fe035a003fc01f81fe0210003fc01f81fe01ce003fc01f81f803fc003fc01f81f403fa003fc01f81e003f0003fc01f81dc03ee003fc01f81bc03de003fc01f8134035a003fc01f809c01ce003fc01f01fe03ec003fc01e81fe03ea003fc01c01fe03e0003fc01b01fe018c003fc01681fe014a003fc016809c014a003fc00001fe014a003fc00001fe0000003f801f01d803ec003f801f009801cc003f401e81d403ea003f401e809401ca)))) (
.fork 9 0x184404200898918c (
.fork 7 0x3b9c1df91202210 (
.leaf 6 0x381ffdf9021e3f00381f9df902122100381c1c3902020100381c00010200000038001c010002000037581bb0898118c0341bfbf0819d3ec0341bfbf081891cc0341b5bb0818918c034181a30c1c180e034181a30818100c0341800008180000034001a008001000030181830000000002ef41768414094a02c17f7e8415cbea02c16f768414094a02c141628e1e080a02c141628e141c0a02c141628c1c180e02c141628414080a02c140000414000002c00160040008000281414280000000024101220010000801008081102020100100808108081004010080001a2a0000010000801a003400008040409020201000804040840408020080400016260000) (
.fork 8 0x3c1c1e39e203c10 (
.leaf 7 0x3c1c1e39e1c3c0e03c1c1e39c3c381e03c1c1e39838301c03c1c1e39434281a03c1c1e38c1c180e03c1c1e31e3e3c0c03c1c1e29e3e3c0a03c1c1e01e3e3c0003c1c1c39e3e201003c1c1a31e3e100c03c1c1629e3e080a03c1c1628c1c080a03c1c1601e3e080003c1c0409e3e080203c1c0401e3e2c0003c1c0201e3e1c0003c1c0201e3e080a03c1c0001e3e000003c181e31e183c0c03c17ff69e15fd4a03c141e29e143c0a03c141e28c14180a03c141e01e143c0003c141629e14080a03c03ffc1e01ffe003c03fe01e01fc0003c001e01e1e3c0003c001e01e143c0a03c001e01e003c0003c000001e00000003b9f9df9121221003b9c1df91202210) (
.leaf 8 0x184400000898000018403fe00801fc00184006200800dc001840042008009000180404000080818016c747628414094a146f46368414094a14462f768414094a144606200414094a1446000004140000144006200400080014060600000001401044042000100108083fc0002bfe0000080600002ade0000080000002aca0000080000002a00d4000800000020c0c0a008000000088890840402020020404060040202000404084204020000264600000400020026004c0003ffc0001ffe000003fe01fc1fc03fe003c1ffff8c1c99ce03c1fe1c1e3fc3e003c1c1e39e3e3c1003c1c1e39e3e281a03c1c1e39e3e180e03c1c1e39e343c1a03c1c1e39e203c10))) (
.fork 11 0x1c4600202ede080a (
.fork 10 0x1c2e061420c0c1e0 (
.leaf 9 0x1c16060821c0c3e01c0e060421c0c3e01c063fdfa0c1e3f01c063e1c20c1c3e01c063e0020c1c1e01c0637bb20c0d1ec1c06361820c0c1e01c062e1420c0c1e01c06160820c1c3e01c060e0420c1c3e01c06062020c0d1ec1c06061c20c0c3e01c06060061c1c3e01c06060020c0c1e01c06060020c0c0001c06060020c001401c06060020c000001c0606002000c1401c060600008081c01c06020020c040601c06020020c040001c0600002aca00001c06000026c600001c06000020de00001c06000020c000001c0006002000c0001b4585a30898918c187fc00009fe00001875843b0898918c1846000008de0000184435bb0898918c184404200898918c) (
.leaf 10 0x1c4600007ffe00001c4600002ede00001c4600002ec000001c4600002e1400001c46000028d800001c46000024d400001c4600000c9c00001c4406202e98dd8c1c4206202e46dc001c403fffae01fe101c403fe02e01fc001c403e202e01dc001c4037a02e00dc001c402f602e00dc001c4016a02e01fc001c400e602e01fc001c4007e02e00fc001c4006207e01fc001c4006202e00dc001c4006202e0008001c4006202800d0001c4006202400c8001c4006200c0098001c4000002e0000001c3fc61fa1e0c3f01c3fc00021fe00001c3e3e1c21c1c3e01c3e061c21c0c3e01c3e060021c0c1e01c3e000021c000001c36061820c0c1e01c2e061420c0c1e0)) (
.fork 12 0x1ec740002ede0000 (
.leaf 11 0x1ec007602e00dc001d4680003efe00001d4006a03e00fc001cc640003efe00001cc006603e00fc001c7fc01faffe02101c7fc0002ffe00001c7e00002fde00001c79c63faf20de101c7780002ede00001c6f40002ede00001c5680002ffe00001c4e40002ffe00001c47c0002efe00001c4639dfaedf22101c4606202ededc001c4606202ede99ce1c4606202ede094a1c4606202ede08001c4606202ec0dde01c4606202e9cddce1c4606202e14dd4a1c4606202cdcd9ee1c46062028d8d1ec1c46062024d4c9ea1c4606200c9c99ce1c4606002edec1e01c4604202ede918c1c4602002ede4c001c4600202ede1c001c4600202ede100c1c4600202ede080a) (
.leaf 12 0x243e0a1c61c143e0240a3e1c6141c3e0240a0a0461414260240a0a0400000040240a00006140000024003e1c6001c3e024000a00600140002389c9c7d121221020b9c85fd121221020887e5cd121e3f0208879dfd121221020884844d121221020884844800000002088400051200000208008405001200020083e1c4101c3e020080804410102001fffc0003ffe00001fc7c1c3befe20101fc7c0003efe00001fc601e03ede3c001fc600003ede00001fc1c7e3be20fc101fc03fe03e01fc001fc007e03e00fc001fc006203e00dc001f87c7c3b0e0e1f01f4781a32ede100c1f4780002ede00001f4007a02e00dc001ec74162aede080a1ec740002ede0000))))) (
.fork 19 0xa3a9e9d790202010 (
.fork 16 0x4910908969c9d2a4 (
.fork 14 0x27cbc0007f7e0000 (
.leaf 13 0x27c00be07e017c00274b8ba76959526c26cb4b668414084a24bfc00077fe000024b58a5b76996d8c24af4a568414094a248a75bb7766918c248a6f768404094a248a4a44f7676e10248a4a44f7672a52248a4a44f7660842248a4a44f7616e70248a4a44f7256e52248a4a44f6056c42248a4a44f5656a72248a4a44f1616270248a4a44e5454a62248a4a44d5252a52248a4a4484040842248a4a4077676c00248a4a0477674260248a4844f7672210248a400077660000248a400004040000248a0a4477416e6024884a44f7216e1024803fe07601fc0024803e5c7601efe024800a4077216e1024800a4076016c0024800a40040008002480000076000000) (
.fork 15 0x3fcfc0007ffe0000 (
.leaf 14 0x3fc00fe07e01fc003cffc0007ffe00003cce4844ffff22103cce40007ffe00003cce40002ede00003cca46207f66dc003cc84e64ff21fe103cc60a407edf6c003cc600007ede00003cc03fe07e01fc003cc00e607e01fc003cc00e602e00dc003cc006207e00dc003c8e4e44f1e1e3f03c8e400077e600003c4e00006fde00003c400e206e01dc003c3e0e1c61c1c3e03c0e3e1c61c1c3e03c0e0e0461c1c3e03c0e0e0420c0c1e03c0e0a0461c142603c0e060061c0c1e03c0e000061c000003c060e0060c1c1e03c060a0060c1400038cc4c64d9b9b39c36cf4f668414094a34ef4e768414094a34ce6f768414094a34ce4e648414094a27cbc0007f7e0000) (
.leaf 15 0x4910908959a9b2944910908908889084491090807bebf400491090087bebc2a0491080007bea00004910800008880000491010887bc1f6a049003fe07a01fc00490010807a01f4004900108008009000490000007a000000483fc00061fe0000483e101c61c1c3e0483e000061c0000048103e1c61c1c3e04810100861c1c2a048101008008080804810000061c00000480010006001c00043b9d1dfd12122104391f9dfd12122104391d1cbd12122104139d09fd12122104110be9d5121e3f04110b9dfd1212210411090895121221041109089000000004110800051200000410010805001200040103e1c4101c3e040101008410102003fcfc0007ffe0000))) (
.fork 17 0x597594bb0898918c (
.leaf 16 0x5954b5bb0898918c595494a90898918c595094a908889084555696a955352b5a4bffc0007ffe00004bd1c0007ffe00004bc03fe07e01fc004bc011e07e01fc004b7591bb0898918c4b51b5bb0898918c4b5191ab0898908c4b5091a9088890844ad1516ae5d5caaa495090a90898908c493fd09ffbff2210493fc0007bfe0000493fc00009fe0000493e80007bea00004935909b0898918c492f5096fa15f54a491680007bfe00004910b5bb0888918c4910af76fbea094a491090897bebf610491090897beb2210491090897bea9084491090897be1f6b0491090897b21f610491090897a89f4844910908979e9f2b44910908971e1e2b04910908969c9d2a4) (
.fork 18 0x6dbfc0007ffe0000 (
.leaf 17 0x6d9adacd8c8c98c66d9ac0007fee00006d801ac07e01fc006c3e1a1c61c1c3e06c1a1a0c61c1c2e061b9d8dfd12122106198d8cdd12122105fd7c0007ffe00005fc017e07e01fc005d7fc0007ffe00005d5690897fff22105d5680007ffe00005d5680002ede00005d5096a97f21fe105d4600007ede00005d403fe07e01fc005d4016a07e01fc005d4016a02e00dc005d4006207e00dc005d16968971e1e3f05d1680007bea00005c5600006fde00005c4016206e01dc005c3e161c61c1c3e05c163e1c61c1c3e05c16160861c1c3e05c16160820c0c1e05c16060061c0c1e05c16000061c000005c06160060c1c1e05b5595ab0898918c597594bb0898918c) (
.leaf 18 0xa2e969768414080aa2b9e95f81200210a2af69568014014aa2a97f5e8001c3e0a2a979df80012210a2a96f768000094aa2a96956d1212210a2a9695680000000a2a9400000000000a280294000000000a0283e1c0001c3e0a0282814000000009e6700002ede00009e4027202e00dc009c26261020c0c1e09a6525320898918c966727320414094a9365a5b30818110c92e565728414090a9275a53b0098018c926f65368014014a926535bb0010918c92652f768010094a926525320010010892650000001000009240252000000000902424100000010082212112000000007ddec0007ffe00007dc01ee07e01fc007c1e1e0c61c1c3e06dbfc0007ffe0000)))) (
.fork 22 0xbeef40000c9c0000 (
.fork 20 0xb6ef400077760000 (
.leaf 19 0xb6ef400004140000b6ee6f7484040942b6ee2f7404000940b6e96f7684000800b6e52f7204100908b6ce6f648414094ab6ca6f6484040842b6c62f600414094ab6c16f628414080ab6c03fe00401fc00b6c03f7c0401cbe0b6c02f768400094ab6c02f6076016c00b6c02f6004000800b6c0000004000000b6af6f5680000140b66f2f3600100148b4ee6e748414094ab4ae6e5484040942b46e2e340414094ab43e2e1c01c003e0b42f6e168014014ab42e3e1c0001c3e0b42e2f768000094ab42e2e1461414360b42e2e1400000140b42e000000000000b4003e1c0001c3e0b4002e0000000000b2ed6d7680100108a6ab6b5684040842a3a9e9d790202010) (
.fork 21 0xb6ffef7f85340b5a (
.leaf 20 0xb6ffef7f849c09ceb6ffef7f8414094ab6ffef7685fe094ab6ffc00005fe0000b6ff6f7e85d40beab6efef77841c094eb6ef7fff84152b5ab6ef7fff841499ceb6ef7fff8414094ab6ef7ff68415fd4ab6ef7fe00415fc00b6ef7f7e8415cbeab6ef6f7f841409ceb6ef6f76f776094ab6ef6f76f6156d4ab6ef6f76e5554b6ab6ef6f76d5352b5ab6ef6f768414094ab6ef6f7684140800b6ef6f7684000940b6ef6f7680100148b6ef6f6484140842b6ef6f6004140800b6ef6e1404140140b6ef695684140000b6ef653204140108b6ef4e648414094ab6ef4a4484140842b6ef46200414094ab6ef41628414080ab6ef40168414014ab6ef400077760000) (
.leaf 21 0xbee96f76ae00dc00bec62f602ede0800bec600002ede0000bec03fe02e01fc00bec02f607e01fc00bec02f602e00dc00bec02f602e000800bec02f602400c800bec02f600c009800bec006202e00dc00beaf6f56a0c0c1e0bc6e00002ede0000bc402e202e00dc00bc3e2e1c21c0c3e0bc2e3e1c20c1c3e0bc2e2e1461c1c3e0bc2e2e1420c0c1e0bc2e2e1420c00140bc2e2e142000c140bc2e2e14008081c0bc2e060020c0c1e0bc2e000020c00000bc062e0020c0c1e0bc062e0020c00000b7efeff79434295ab7efeff78c1c194eb7efeff78414094ab7efef769e3e094ab7efc0001e3e0000b7ef6ff69e143d4ab7c02fe01e003c00b6ffef7f85340b5a))) (
.fork 24 0xdb71b5bb0800918c (
.fork 23 0xd834000000800000 (
.leaf 22 0xd800340000008000d375b5bb00100108cb71b1bb0898908ccb31b19b08889084c3b9f1df91202210c3b1f9df90212210c3b1f1db90202010c371b1bb0818100cc339f19f81200210c335b19b0098018cc331bf9f0001c3e0c331b9df80012210c331b5bb0000918cc331b19b51212210c331b19b00000000c331800000000000c300318000000000c0303e1c0001c3e0c030301800000000bfefc0003efe0000bfc02fe03e00fc00beffc0002ffe0000beef6f76aede094abeef6f76ae14dd4abeef6f76a4d4c9eabeef6f768c9c99cebeef6956aede0000beef40007ffe0000beef40002ede0000beef40002e140000beef400024d40000beef40000c9c0000) (
.leaf 23 0xdb71b5bb08009000db6535b208109108db54b5a90898918cdb51b5ab0898908cdb50b5bb0888918cdb50b5a908889084db50b5a908009000db4435a00898918cdb41b5a30818900cdb403fe07a01fc00db403fe00801fc00db403fe008009800db403fa00801d000db4037a00800dc00db4035bb0800918cdb4035a07a01f400db4035a008009000db40000008000000db35b59b00808180da75353a00908188d974b4b90898918cd934b49908889184d87434380898918cd83fc00001fe0000d83e341c01c083e0d83e000001c00000d835b41b0098818cd8343e1c0081c3e0d83435bb0080918cd834341861c1c3a0d834341800808180d834000000800000)) (
.fork 25 0xdb75b7bb0898d1ec (
.leaf 24 0xdb75b5bf889891cedb75b5bb7bfa918cdb75b5bb7a99f58cdb75b5bb69d9d3acdb75b5bb59b9b39cdb75b5bb0898918cdb75b5bb08989000db75b5bb08980108db75b5bb08809180db75b5bb08109108db75b5bb00908188db75b5a908989084db75b5a008989000db75b41808988180db75b1bb0898100cdb75b19b08980000db75a53208980108db7594a90898918cdb7591ab0898908cdb75908908989084db7584200898918cdb7581a30898100cdb75801b0898018cdb7580007bfa0000db75800008980000db74b5b908889184db7435b808809180db71bfff8801fe10db71b7bb0800d000db71b5bb08889084db71b5bb0818900cdb71b5bb0800918c) (
.leaf 25 0xdbf5f5fb98b8b19cdbf5f5fb8c9c998edbf5f5fb8898918cdbf5f5bb1ebe918cdbf5c0001ebe0000dbf5b5fb1e98bd8cdbc03fe01e01fc00dbc035e01e00bc00db7ff5bf889c91cedb7ff5bb09fe918cdb7ff5bb089c918cdb7ff19f89fe0210db7fc0007bfe0000db7fc00009fe0000db7fc000089c0000db7fb5bf09d893ecdb7fb5bf089891ccdb7f800009d80000db7df5bf89b8939cdb7df5bf8898918cdb77b5bb08de918cdb77b5bb08d891ecdb77b5bb089c91cedb77800008de0000db75f5bb889c918edb75bfff889899cedb75bffb0899fd8cdb75bfbf0899d3ecdb75bfbf089891ccdb75bdff8899b39cdb75bdff8898918cdb75b7bb0898d1ec)))))) (
.fork 39 0xff79bfbf08009000 (
.fork 32 0xfc2e3e1460c1c1e0 (
.fork 29 0xe3bff9df809c01ce (
.fork 27 0xdff7c0003efe0000 (
.leaf 26 0xdfc037e03e00fc00df7fc0002ffe0000df77b7bb28d8d1ecdf77b7bb0c9c99cedf77b7bb089891ccdf77b5bb2ede918cdf77b19b2ede0000df7780007ffe0000df7780002ede0000df77800028d80000df7780000c9c0000df75b7bb2e98dd8cdf71b7bb2e00dc00df4600002ede0000df403fe02e01fc00df4037a07e01fc00df4037a02e00dc00df4037a02800d000df4037a00c009800df4006202e00dc00df37b79b20c0c1e0dc7600002ede0000dc4036202e00dc00dc3e361c21c0c3e0dc363e1c20c1c3e0dc36361861c1c3e0dc36361820c0c1e0dc363618008081c0dc36060020c0c1e0dc36000020c00000dc06360020c0c1e0dbffc0001ffe0000) (
.fork 28 0xe3b9c1c3d1202010 (
.leaf 27 0xe3b9c01fd1200210e3b9c00051200000e3b83ffc5101ffe0e3b839dc51012200e3b1b9db50012000e3a97ff6d001fd4ae3a979d6d0012000e390b9c951212210e38879c4d1212210e381f9c3d0212010e3803fe05001fc00e3803fdc5001e3e0e38039dfd0012210e38039c050012000e380000050000000e33fb99f41d903ece339bfbf4101d3ece339b99f41010200e2bf795ec1d503eae2b97f7ec101cbeae2b9795ec1010200e138b89d51212210e0b8785cd1212210e03e381c41c103e0e039f81fc1210210e0383e1c4101c3e0e03839dfc1012210e038381c41010200e038000041000000e0003e1c4001c3e0e000380040010000dff7c0003efe0000) (
.leaf 28 0xe3bfe956d1fe014ae3bfc00051fe0000e3bdf9dfd1b9239ce3b9ffffd121fff0e3b9ffffd121ff5ae3b9ffffd121fe10e3b9ffffd121f3fce3b9ffffd121ebfae3b9ffffd121bbdee3b9ffffd1212b5ae3b9ffff800099cee3b9ffdfd121e3f0e3b9fe1c5121c3e0e3b9fdffd121b39ce3b9f9dff3632210e3b9f9dff3216610e3b9f9dff1616230e3b9f9dfd1212210e3b9f9dfd1200000e3b9f9dfd0012000e3b9f9dfc1010200e3b9f9df90202010e3b9f9df81200210e3b9f9df80012210e3b9f9df80000000e3b9f9c051212000e3b9f81c51210200e3b9f19b51200000e3b9e956d1200000e3b9d08951212210e3b9c844d1212210e3b9c1c3d1202010))) (
.fork 30 0xeb8039c07a01f400 (
.leaf 29 0xe838381c61c1c2a0e7bbfbdff1616270e7bbfbdfd5252a52e7bbf9dff7672210e7bbf9dff1612210e7bbc00077660000e7b9fbdff7216e10e7b9fbdff1216210e7803bc076016c00e43a3a1c61414260e3f9f9ffdf3f3e10e3f9f9ffdf3f2a1ae3f9f9ffdf353e1ae3f9f9ffdf213e10e3f9f9ffdd3d3a1ee3f9f9ffd939321ce3f9f9ffd5352a1ae3f9f9ff8c1c180ee3f9f9e05f3f3c00e3f9f9dfdf3f2210e3f9e976df3e080ae3f9c0005f3e0000e3e979f6de153c0ae3c039e05e013c00e3bff9dfd1ff235ae3bff9dfd1ff2210e3bff9dfd1f923fce3bff9dfd1f523fae3bff9dfd1e123f0e3bff9dfd1bd23dee3bff9dfd135235ae3bff9df809c01ce) (
.fork 31 0xfbf5bdfb0898918c (
.leaf 30 0xfbc03fe05801fc00fbc03de05801b000fbbdfddfd1a1a390fb7dbdbf4999938cfb7dbdbf0898918cf83c3c1c41818380f7ffffffd5352b5af7ffffff8414094af7fff9dfd5352210f7ffef76d534094af7ffef768414094af7ffc00055340000f7f9ffffd5212a10f7ef7ff6d415294af7ef7ff68414094af7c03fe054012800f7bfffdfd1212350f7bff9dfd1212210f7b9ffdfd1212210f6ff7f7ec5150b4af6ff7f7e8414094af43e3e1c41010340f3fdfdffd1312318f3f9fdffd1212210ebbff9dffbff2210ebbfc0007bfe0000ebb9f9dffbeb2210ebb9f9dffb21f610ebb9f9dff1e1e2b0ebb9f9dfd9a9b294ebb9c0007bea0000eb8039c07a01f400) (
.leaf 31 0xfc2e3e146001c140fc2e3e1400008140fc2e3e006001c000fc2e2e1460000140fc2e000060000000fc163e0861c1c3e0fc103e0861c1c2a0fc0e3e0461c1c3e0fc0a3e046141c260fc063e1c60c1c3e0fc063e0060c1c1e0fc063e0060c1c000fc063e006001c140fc06060060c0c1e0fc06000060c00000fc003fe06001fc00fc003e1c6001c3e0fc003e006001c000fc00000060000000fbfffdff889c91cefbfff9dfd9ff2210fbffc00059fe0000fbfdfdffd9b9b39cfbfdfdff8898918cfbfdf9dfd9b92210fbfdf5bb59b8918cfbfdf5bb0898918cfbfdc00059b80000fbf9ffffd921fe10fbf9fdffd921b210fbf5bdfb5899b18cfbf5bdfb0898918c)))) (
.fork 35 0xfc3e800061ea0000 (
.fork 33 0xfc3e100861c10200 (
.leaf 32 0xfc3e0e0461c1c3e0fc3e0a1c61c143e0fc3e0a0461c14260fc3e0a0461c14200fc3e0a0461c00040fc3e0a0061c14220fc3e0a0061c14000fc3e0a0061c00000fc3e080461c10200fc3e061c61c0c3e0fc3e060061c0c1e0fc3e060061c0c000fc3e060061c00140fc3e060061c00000fc3e020061c04060fc3e020061c04000fc3e001c61c003e0fc3e001c61c00200fc3e000861c002a0fc3e000073e20000fc3e00006bca0000fc3e000067c60000fc3e000061de0000fc3e000061c14220fc3e000061c00000fc3e000000800000fc383e1c6101c200fc363e1860c1c1e0fc343e186081c180fc2e3e1c6001c3e0fc2e3e146141c360fc2e3e1460c1c1e0) (
.fork 34 0xfc3e3e1c20c0c1e0 (
.leaf 33 0xfc3e3e1c01c083e0fc3e3e1c0081c3e0fc3e3e1c008081c0fc3e3e1861c1c180fc3e3e1461c1c140fc3e3e0861c1c2a0fc3e3e0461c1c260fc3e3e0061c1c1e0fc3e3e0061c1c000fc3e3e0061c10000fc3e3a1c61c14260fc3e3a1c61c14200fc3e3a0061c14000fc3e39dfe1c12210fc3e381c61c10200fc3e380061c10000fc3e361861c0c1e0fc3e341861c08180fc3e301861c00000fc3e2e1c61c003e0fc3e2e1461c14360fc3e2e1461c0c1e0fc3e2e1461c00140fc3e2e1461c00000fc3e2e1400800140fc3e2e0061c14000fc3e2e0061c00000fc3e281461c00000fc3e1a0c61c1c2e0fc3e160861c1c3e0fc3e100861c1c2a0fc3e100861c10200) (
.leaf 34 0xfc3e7e1ce1e1c3f0fc3e400061e60000fc3e3fffe1c1f3fcfc3e3ffc61c1ffe0fc3e3fdfe1c1e3f0fc3e3fdc61c1e3e0fc3e3fbf61c1d3ecfc3e3fbc61c1d3e0fc3e3f9f61c1c3e0fc3e3f7ee1c1cbeafc3e3f5ee1c1c3e0fc3e3f3e61c1c3e8fc3e3e9d61c1e3f0fc3e3e9d61c1d3e4fc3e3e9c61c1f7e0fc3e3e5ce1c1e3f0fc3e3e3c61c1d3ecfc3e3e1fe1c1c3f0fc3e3e1f61c1c3ecfc3e3e1ee1c1c3eafc3e3e1c73e3c3e0fc3e3e1c73c1e7e0fc3e3e1c71e1e3f0fc3e3e1c61c1c3e0fc3e3e1c61c1c200fc3e3e1c61c10340fc3e3e1c61c10200fc3e3e1c61c081c0fc3e3e1c6101c340fc3e3e1c6081c1c0fc3e3e1c418183c0fc3e3e1c20c0c1e0))) (
.fork 37 0xfd3ebe1c71e1c3e0 (
.fork 36 0xfc7e3e3c69d9d3ec (
.leaf 35 0xfc7e3e3c65d5cbeafc7e3e1c6fdfc3e0fc7e381c6fdf0200fc7e00006fde0000fc7e00006fc00000fc7e000069d80000fc7e000065d40000fc783e3c6f01de00fc4600006ede0000fc403fe06e01fc00fc403e206e01dc00fc403e206801d000fc403e206401c800fc4006206e00dc00fc3fffdfe1e1e3f0fc3ffe1fe1e1c3f0fc3ffe1c61ffc3e0fc3ffe1c61e1c3e0fc3ff81fe1ff0210fc3fc01fe1e00210fc3fc00061fe0000fc3fc00061e00000fc3fbe1f61d9c3ecfc3fbe1f61c1c3e0fc3f800061d80000fc3f7e1ee1d5c3eafc3f7e1ee1c1c3e0fc3f400061d40000fc3ebe1d61e1c3f0fc3ebe1d61c9c3e4fc3ebe1c61ebc3e0fc3e800061ea0000) (
.leaf 36 0xfd3eb89d7beb2210fd3e908971e12210fd3e80007bea0000fd3e800071e00000fd3e800069c80000fd3e3e9c7bc1f7e0fd3e3e9c71c1e3e0fd3e00007bc00000fd003e807a01f400fcfe40007ffe0000fcc03e607e01fc00fcbffe5ff1e1e3f0fcbfc00077fe0000fcbe7fdff1e1e3f0fcbe7e5cf1e1e3f0fcbe7e5ce5c5cbe2fcbe7e5ce1c1c3e0fcbe7e1c77e7c3e0fcbe7e1c71e1c3e0fcbe785cf7e72210fcbe4844f1e12210fcbe400077e60000fcbe400071e00000fcbe400065c40000fcbe3e5c77c1efe0fcbe3e5c71c1e3e0fcbe0a4077c16c00fcbe000077c00000fc803e407601ec00fc7fc0006ffe0000fc7e3e3c6fc1dfe0fc7e3e3c69d9d3ec)) (
.fork 38 0xfeef7f76e415c94a (
.leaf 37 0xfeef400064140000fec03fe06401fc00fec03f607601ec00fec03f606e01dc00fec03f606401c800fec03f6004008800fec02f6064000800febfff5fe1e1c3f0febf7fdfe1c1e3f0febf7f5ef1e1e3f0febf7f5ee1c1c3e0febf7e1c61c1c3e0febf6956e1c00000febf400061c00000febe3f5c61c1c3e0fe7f3f3e61d1c3e8fe7f000061d00000fe7e3f3c61c1c3e0fe403f206001c000fe3f3f1e61c1c3e0fdbefeddf1e1e3f0fdbec0007fee0000fd7e80007ffe0000fd403ea07e01fc00fd3ffe9ff1e1e3f0fd3fc0007bfe0000fd3ebfdff1e1e3f0fd3ebe9d71e1e3f0fd3ebe9d69c9d3e4fd3ebe9d61c1c3e0fd3ebe1c7bebc3e0fd3ebe1c71e1c3e0) (
.leaf 38 0xff75bfbb6899d18cff75bfbb0898918cff403fe06801fc00ff403fa07a01f400ff403fa06e01dc00ff403fa06801d000ff403fa008009000ff3fff9fe1e1c3f0ff3fbfdfe1c1e3f0ff3fbfbf61c1d3ecff3fbf9f71e1e3f0ff3fbf9f61c1c3e0ff3fbe1c61c1c3e0ff3fb19b61c00000ff3f800061c00000ff3e3f9c61c1c3e0feffc00065fe0000feff7f7ee5d5cbeafeff7f7e849489cafeff7e1c65d5c3e0feff795ee5d50200feff6f76e5d4094afeff4162e5d4080afeff400077f60000feff40006fde0000feff400065d40000feff400004940000fefe3f7c65c1cbe0fefe2f6065c00800fefe000065c00000fef97f7ee501ca00feef7f76e415c94a))))) (
.fork 45 0xfff43ff87e81fd80 (
.fork 42 0xffc03fe07e012800 (
.fork 40 0xffbfc00071fe0000 (
.leaf 39 0xffbfc00071e00000ffbfbfdf71c1e3e0ffbf7fdef1c1e3e0ffbebfdd71e1e3f0ffbe7fdcf1e1e3f0ffbe3fdff1c1e3f0ffbe3fdc71c1e3e0ffbe3e1c71c1c3e0ffbe39c071c12000ffbe000071c00000ffb9ffdff121e210ffb9f9dff1212210ffaf7fd6f001e140ff863fc070c1e1e0ff803fc07001e000ff7fffbf889c91ceff7fc00069fe0000ff7fbfbf69d9d3ecff7fbfbf089891ccff7fbe1c69d9c3e0ff7fb99f69d90200ff7fb5bb69d8918cff7fb5bb0898918cff7f81a369d8100cff7f80007bfa0000ff7f80006fde0000ff7f800069d80000ff7f800008980000ff7e3fbc69c1d3e0ff7e000069c00000ff79bfbf6901d200ff79bfbf08009000) (
.fork 41 0xffbffffff1e1f3fc (
.leaf 40 0xffbfffdff1e1e3f0ffbfffdff1e1e210ffbfffdff1e12350ffbfffdff1e12210ffbfffdff121e350ffbfffdfe1c1c3e0ffbfffdfd1a1a3d0ffbfffdf808081c0ffbfffdc71e1e3e0ffbfffc071e1e000ffbfff9f71e1c3e0ffbfff5ef1e1c3e0ffbffe9d71e1e3f0ffbffe5cf1e1e3f0ffbffe1ff1e1c3f0ffbffe1c71e1c3e0ffbffbdff1e16270ffbffbdff1e16210ffbff9dffbeb2210ffbff9dff7e72210ffbff9dff1ff2210ffbff9dff1e12210ffbff9dff1212210ffbfef56f1e00140ffbfef4071e00000ffbfca44f1e16270ffbfca4071e16000ffbfc60071e0c1e0ffbfc1c3f1e02010ffbfc0007bea0000ffbfc00077e60000ffbfc00071fe0000) (
.leaf 41 0xffc03fe07e009800ffc03fe07801f000ffc03fe07401e800ffc03fe06c01d800ffc03fe05c01b800ffc03fe02e00dc00ffc03fe01e00bc00ffc03fe00c01fc00ffc03fe00c009800ffc03fa07e01d000ffc03f607e01c800ffc03e207e01dc00ffc03e007e01c000ffc039c07e012000ffc037a07e00dc00ffc035a07e009000ffc02fe07e003c00ffc02f76fe00094affc02f607e016c00ffc02f607e00dc00ffc02f607e000800ffc02f600c000800ffc016a07e01fc00ffc010807e01f400ffc00e607e01fc00ffc00a407e016c00ffc007e07e00fc00ffc006207e00dc00ffc006207e000800ffc001e07e003c00ffc000007e000000ffbffffff1e1f3fc))) (
.fork 43 0xffc23fe07e47fc00 (
.leaf 42 0xffc1fffffe21fe10ffc1ffe3fe21fc10ffc1ffe07e3ffc00ffc1ffe07e21fc00ffc1c0007e3e0000ffc1bfe37e19fc0cffc1bfe37e01fc00ffc17fe2fe15fc0affc17fe2fe01fc00ffc0bfe17e21fc10ffc0bfe17e09fc04ffc0bfe07e2bfc00ffc07fe0fe21fc10ffc07fe0fe05fc02ffc07fe07e27fc00ffc03ffffe01fe10ffc03ffc7e01ffe0ffc03ffc7e01fe00ffc03ffb7e01fd8cffc03ffb7e01fc00ffc03ff6fe01fd4affc03ff6fe01fc00ffc03fe97e01fe10ffc03fe97e01fc84ffc03fe87e01fea0ffc03fe4fe01fe10ffc03fe3fe01fc10ffc03fe07f63fc00ffc03fe07f41fe20ffc03fe07f21fe10ffc03fe07e01fc00ffc03fe07e012800) (
.fork 44 0xffd0bfffff21fe10 (
.leaf 43 0xffd0bfe97f21fe10ffd0bfe97e89fc84ffd0bfe97e01fc00ffd0bfe07febfc00ffd0bfe07f21fc00ffd080007fea0000ffd03fe87fc1fea0ffd03fe87f01fe00ffce40007ffe0000ffca7fe4ff67fe10ffca7fe4fe05fc42ffca7fe07f67fc00ffca7fe07e05fc00ffca40007f660000ffca3fe47f41fe60ffca3fe07f41fc00ffc9ffe7ff21fe10ffc87fffff21fe10ffc87fe4ff21fe10ffc87fe4fe01fc00ffc87fe07f21fc00ffc83fe47f01fe00ffc7c0007efe0000ffc63fe07edffc00ffc63fe07ec1fde0ffc63fe07e15fd4affc639c07edf2000ffc600007ede0000ffc600007ec00000ffc600007e140000ffc43fe07e99fd8cffc23fe07e47fc00) (
.leaf 44 0xfff1fffbfe21fc10fff1bffffe01fe10fff1bffb7f21fe10fff1bffb7e01fc00fff1bfe07e01fc00fff03ff87e01fc00ffefc0007e3e0000ffef7ff6fe15fd4affef7ff68c14994affef7fe07e15fc00ffef79d6fe152000ffef6f76fe14094affef41e2fe143c0affef40007f760000ffef40007ede0000ffef40007e140000ffef40000c140000ffee3ff47e01fd40ffee3fe07e01fc00ffee00007e000000ffe9fff7fe21fc10ffe97ffffe01fe10ffe97ff6ff21fe10ffe97ff6fe01fc00ffe97fe07e01fc00ffe83ff47e01fc00ffe53ff27e11fd08ffe13ff27e01fc00ffd8ffedff21fe10ffd680007ffe0000ffd1ffebff21fe10ffd0bfffff21fe10)))) (
.fork 48 0xffffc1e07ffe3c00 (
.fork 46 0xfffbffe07f67fc00 (
.leaf 45 0xfff9ffffff21fe10fff9ffffff212a10fff9fffffe01fc00fff9fffff921f210fff9fffff521ea10fff9ffffdd21ba10fff9ffff8c009800fff9fffc7f21fe00fff9fffb7f21fc00fff9fff6ff21fc00fff9ffe97f21fe10fff9ffe4ff21fe10fff9ffe3ff21fc10fff9ffe07f21fc00fff9f9dfff212210fff9ef76ff200800fff9c6207f20dc00fff9c0007f200000fff9bfff7f01fe00fff97ffeff01fe00fff8bffd7f21fe10fff87ffcff21fe10fff83fffff01fe10fff83ffc7f01fe00fff83fe07f01fc00fff780007ede0000fff5bffb7e99fd8cfff5bffb0c98998cfff5bfe07e99fc00fff5b5bb7e98918cfff580007e980000fff43ff87e81fd80) (
.fork 47 0xffffc0037ffe000c (
.leaf 46 0xffffc002fffe000affffc0007fff6400ffffc0007fff4220ffffc0007fff2210ffffc0007ffe0000ffffc0007fe00000ffffc0007f340000ffffc0007e9c0000ffffc00079f80000ffffc00075f40000ffffc0006ddc0000ffffc0005dbc0000ffffc0002ede0000ffffc0001ebe0000ffffc0000dfe0000ffffc0000c9c0000ffffbfff7fd9ffecffff80007fd80000ffff7ffeffd5ffeaffff40007fd40000fffe80007fea0000fffe40007fe60000fffe3ffc7fc1ffe0fffe3fe07fc1fc00fffe3e1c7fc1c3e0fffe39dc7fc12200fffe01e07fc03c00fffe00007fde0000fffe00007fc00000fffdffffffb9ff9cfffbffffff67fe10fffbffe07f67fc00) (
.leaf 47 0xffffc1dffffe2210ffffc1c3fffe2010ffffc1c07ffe2000ffffc1a37ffe100cffffc1a07ffe1000ffffc1837ffe0000ffffc162fffe080affffc1607ffe0800ffffc142fffe0000ffffc1227ffe0008ffffc0817ffe2010ffffc0817ffe1004ffffc0807ffe3400ffffc040fffe2010ffffc040fffe0802ffffc0407ffe2c00ffffc0207ffe1c00ffffc0207ffe100cffffc0207ffe080affffc01ffffe0210ffffc01c7ffe03e0ffffc01c7ffe0200ffffc01b7ffe018cffffc01b7ffe0000ffffc016fffe014affffc016fffe0000ffffc0097ffe0210ffffc0097ffe0084ffffc0087ffe02a0ffffc004fffe0210ffffc003fffe0010ffffc0037ffe000c))) (
.fork 50 0xfffff5a07ffe9000 (
.fork 49 0xffffd0897ffe9084 (
.leaf 48 0xffffd0897ffe0000ffffd0807ffff400ffffd0807fff2000ffffd0087fffc2a0ffffd0087fff0200ffffcbe07fff7c00ffffca44ffff6e10ffffca44fffe0842ffffca407fff6c00ffffca407ffe0800ffffca047fff4260ffffca007fff4000ffffc9c7ffff2210ffffc85fffff2210ffffc844ffff2210ffffc844fffe0000ffffc8407fff2000ffffc8047fff0200ffffc6207ffedc00ffffc6207ffe094affffc6207ffe0800ffffc6007ffec1e0ffffc4207ffe918cffffc2007ffe4c00ffffc1e3fffe3c10ffffc1e3fffe301cffffc1e3fffe281affffc1e3fffe180effffc1e38c9c180effffc1e37ffe3c0cffffc1e2fffe3c0affffc1e07ffe3c00) (
.leaf 49 0xfffff4187ffe8180fffff1dbfffe2010fffff1bb7ffe100cfffff19ffffe0210fffff19b7fff2210fffff19b7ffe0000fffff1807ffe0000fffff0187ffe0000ffffefe07ffe3c00ffffef76fffe094affffef76fffe0800ffffef768c9c094affffef62fffe080affffef607fff6c00ffffef607ffe0800ffffee147ffe0140ffffee007ffe0000ffffe9d7fffe2010ffffe976fffe080affffe95ffffe0210ffffe956ffff2210ffffe956fffe0000ffffe9407ffe0000ffffe8147ffe0000ffffe5327ffe0108ffffe5207ffe0000ffffe1127ffe0000ffffd8cdffff2210ffffd1cbffff2210ffffd09fffff2210ffffd0897fff2210ffffd0897ffe9084)) (
.fork 51 0xfffffe007fffc000 (
.leaf 50 0xfffffdffffffb39cfffffbdfffff6e10fffffbc07fff6c00fffff9ffffff3e10fffff9ffffff321cfffff9ffffff2a1afffff9e07fff3c00fffff9dfffff2210fffff9dffffe0000fffff9dfffe12210fffff9dfff352210fffff9dff9f92210fffff9dff5f52210fffff9dfddbd2210fffff9df8c9c0000fffff9dc7fff2200fffff9db7fff2000fffff9d6ffff2000fffff9c97fff2210fffff9c4ffff2210fffff9c3ffff2010fffff9c07fff2000fffff99f7fff0200fffff95effff0200fffff89d7fff2210fffff85cffff2210fffff81fffff0210fffff81c7fff0200fffff8007fff0000fffff5bb7ffe918cfffff5bb0c9c918cfffff5a07ffe9000) (
.leaf 51 0xfffffffffffffe10ffffffffffff2b5affffffffffff2a10fffffffffffe99ceffffffffffe1fff0ffffffffff35ff5afffffffffe9dfdcefffffffff9f9f3fcfffffffff5f5ebfaffffffffeddddbeeffffffffddbdbbdeffffffff8c9c99ceffffffff889891ccfffffffc7fffffe0fffffffb7ffffd8cfffffff6fffffd4affffffe07ffffc00ffffffe07fff2800ffffffdfffffe3f0ffffffbf7fffd3ecffffff7effffcbeafffffe1c7fffc3e0fffffe007fffc000))))))⟩

set_option maxRecDepth 16000 in
def bank2 : PackedSeq := ⟨4, 35, 0x7ffffffff, .leaf 0 0xa3a60051f43cc00a3e85a70947d0b30428f⟩

set_option maxRecDepth 16000 in
def bank3 : PackedSeq := ⟨14, 47, 0x7fffffffffff, .leaf 0 0x2e028e98d947dc050f31b28fb80a1e51e34f70142d3b8a3ee0285990947dbd50b31b28fa169c463651f42d018c00a3e859f7980147ce140838f28f85271e60051f098e3cc00a3e0e9c7980147c1a38f30028f⟩

set_option maxRecDepth 16000 in
def bank4 : PackedSeq := ⟨160, 59, 0x7ffffffffffffff, .fork 2 0x54243238f32128f (
.fork 1 0x50b4db38f31b28f (
.leaf 0 0xa1663651e29c26740136ce3cc6ca3e7b20418d9478a74ee4da40838f28f9dc81071e51e29d3b9020e3ca3c28e712041c798d947cdd40838f31b28f9b686471e63651f36d020e3cc6ca3e6da041c79478ffcdb38f31b28f1289b481071e63651f2b9020e3cc6ca3e3aa041c798d947c2638f31b2f028f84c71e63651e29d098e3cc6ca3c2360d1c798d978147c1a38f31b28f14e83471e63651e11b04ce3cc6ca3c53a089c798d9478a740840638f30028f8107de71e60051f020fbce3cbeca3e041d998d9478a740838f34f31b28f81071e6365e851f020e3cc6ca3c531ca98d9478a7099b8f34f31b28f128) (
.leaf 1 0xa8485271e63651f50909ce3cc6ca3ea12131c798d947d4241d38f31b28fa8483a71e51e34f50906ce3cce0a3ea120d9c798d947d4241a38f31b28fa8483271e63651f50904ce3cc6ca3ea12089c798d947d424083ce31b28fa8481077263651f509020e3cd70a3ea12041c7992147d4240838f32128fa8481071e636519508e54c84a3c4cea11ca98d947899d4239531228f133a8471e6b851e251508e3cc84a3c4a2a11c798d954947d4238f31b28f1c7a8471e63651e261508e3cc6ca3c4b29fa801c798d947d3f40838f31b28fa5887071e63651f4b1098e3cc6ca3e91a1c1c798d947d0b4db38f31b28f)) (
.fork 3 0x54250b4493d931b (
.leaf 2 0xa84a1689260051f50942cfd8c6ca3ea12859e818d947d4250b3bf31b28fa84a1676663651f50942cec0c6ca3ea12859ca98d947d4250b38f32128fa84a1663656051f50942cc6ca3c736a128598d9478b4d4250b31b28f133a84a1489263651f509429000c6ca3ea12841c798d947d4250638f31b28fa84a009dc71e51f509400e3cc6ca32a1278a041c7947d424ee48b38f28fa849dc86471e51f5093b9024e3ca3ea12772041c7947d424ee40738f28fa849dc71e51e2515093b8e3ca3c366a126fa041c7947d4244638f31b28fa8486e71e63651f5090d4e3cc6ca3ea121a1c798d947d4243238f32128f) (
.fork 4 0x5c050b4ef31b28f (
.leaf 3 0xb80a1689263651f70142d124c00a3ee0285a249478d3dc050b40631b28fb80a167de63651f70142cc6ca3c99ee028598d9478cf5c050b31b28f133b80a1663651e20370142cc6ca3c392e028598d9478665c050b31b28f03eb80a1663651e01f7013b9020e3ca3ee02149c798d947dc042638f31b28fb8083a71e63651f701074e3ca3c69ee020d1c798d947dc04083d031b28fb8081077e63651f700e54c6ca3c4cedea041c798d947da950b44931b28fb3aa1689263651f60142d124c6ca3ebaa0f1c798d947d4251d38f31b28fa84a1e71e63651f50942d3d8c6ca3ea1285a771c7947d4250b4493d931b) (
.leaf 4 0xcd8a8481071e4e19b136d020e3ca3f35aa12801c7947e6b54240838f28fcb2b80a4063651f965701480c00a3f2cae02901478d3e5959d52031b28fcb2b00a4063651f965509480f64c6f2caa1290180147e5954251c31b28fcaca84a4063651f8ed701480c6ca3f1b2249c7980147e3244938f30028fc44b80a4063651f869124e3cc00a3f0c2249c7980147ddc5c05203d931bbb8b80a3c63651f771701440c6ca3eee2dfa9018d947ddc4e144938f28fbb889271e60051d771120e3cc00a3eee21c1c7980147dc94f544931b28fb80a40a1663651f701480c6ca3c03ee028622498d947dc050b4ef31b28f)))⟩

set_option maxRecDepth 16000 in
def bank5 : PackedSeq := ⟨2484, 71, 0x7fffffffffffffffff, .fork 39 0x5dc44938f31b28f156 (
.fork 19 0x54244938f35331b28f (
.fork 9 0x54240838f31b28f133 (
.fork 4 0x4e644938f31b28f14e (
.fork 2 0x44938f31b28f21114e (
.fork 1 0x44938f31b28f0a803e (
.leaf 0 0x89271e63651e1480ab124e3cc6ca3c2900fa249c798d947851028c4938f31b28f0a203e89271e63651e11c07d020fbce3cc6cbc0a3e041f79c798d947939c083ef38f31b28f14e8107de71e63651e1cf020fbce3cc6ca3c392041f79c798d947846c083ef38f31b28f08581071e63651e4ce29d020e3cc6ca3c67853a041c798d9478a7099c0838f31b28f14e12781071e63651e29c1c9020e3cc6ca3c538332041c798d9478a705e40838f31b28f14e03e71e63651e2be29c266e3cc6ca3c5384cc4a1c798d9478a709981f38f31b28f14e13300f000cb2b80a4063651e00170142d124c6ca3c002a128598d9478998005424ee40838f28f000a8484c71e63651e001509068e3cc6ca3c002a11ca98d9478998004db40838f31b28f) (
.leaf 1 0x89271e63651e3ba3ad124e3cc6ca3c77453a249c798d9478eb0afc4938f31b28f1d603e89271e63651e31a311124e3cc6ca3c63453a249c798d9478c40afc4938f31b28f18803e89271e63651e2f429d124e3cc6ca3c57c55a249c798d9478af8a744938f31b28f15f0ad89271e63651e2be151124e3cc6ca3c57c292249c798d9478af85144938f31b28f15f08889271e63651e2ac07d124e3cc6ca3c5540fa249c798d9478a709444938f31b28f14e06289271e63651e29c0bf124e3cc6ca3c538176249c798d9478a702bc4938f31b28f14e05589271e63651e29c0a3124e3cc6ca3c538116249c798d9478a701f44938f31b28f14e02b89271e63651e29c01f124e3cc6ca3c2b418a249c798d94785681f44938f31b28f0a803e)) (
.fork 3 0x44940838f31b28f189 (
.leaf 2 0x89281071e63651e311125020e3cc6ca3c55a24a041c798d9478a744940838f31b28f0ad89281071e63651e151125020e3cc6ca3c29224a041c798d94785144940838f31b28f0a08927d671e63651e29d124f80e3cc6ca3c57e249e39c798d9478a744939538f31b28f14e89271e6ce63651e29d124e3cd60d40c6ca3e249c79ac18d9478a744938f35031b28f15f89271e6a063651e07d124e3ccccc6ca3c53a249c798d97b1478afc4938f31b2f628f03e89271e6365e851e07d124e3cc6cb10aeca3e249c798d9621478a744938f31b2c328f14e89271e63657651e2bf124e3cc6caeca3c0fa249c798d95d1478afc4938f31b28f23523089271e63651e46a29d124e3cc6ca3c8c057e249c798d94791801f44938f31b28f21114e) (
.leaf 3 0x9cc89271e63651e14936d125020e3cc6ca3e6da249c798d9478afcdb44938f31b28f0559b689271e63651e07d31d2f1124e3cc6ca3e63a249c798d9478a74c744938f31b28f0a297889281071e63651f2f1124e3cc6ca3c57e5e2249c798d947828cbc44938f31b28f03e97489281071e63651f279124e3cc6ca3c53a45a249c798d9478a747d47644938f31b28f8fa89271e63651e29d1f1124e3cc6ca3c53a3b224a041c798d947c7644938f31b28f15f8ec89271e63651e07d1cd125020e3cc6ca3e362249c798d9478a744943238f31b28f14e89281071e6a063651f125020e3cce8c6ca3e24a041c798d97b147c4940838f31b2bb28f89281071e63651e461125020e3cc6ca3c86a24a041c798d9478eb44940838f31b28f189))) (
.fork 6 0x54238f31b28f15f0f9 (
.fork 5 0x54238f31b28f0ec05d (
.leaf 4 0xa8471e63651e1d807d508e3cc48a3c4cc03ea11c098d94789981f53844940838f31b28fa7089271e63651e2bf4e1124e3cc6ca3c18a9c2249c798d94781f53044938f31b28f03ea5889281071e63651f4b1124e3cc6ca3ca02962249c798d9478afd2c44938f31b28f0a5a5889271e63651e07d4b1124e3cc6ca3c0a2932249c798d94781f52544940838f31b28fa4a89271e63651e2bf495124e3cc6ca3c0fa91a249c798d94780452050038f31b28f14ea4081071e63651e29d480e3cc6ca3c57c53a901c798d9478a702bd2038f31b28f14e03ea1689271e63651e29d405124e3cc6ca3c53a802249c798d9478a74ef4db40838f31b28f9de81071e63651e29d3bd020e3cc6ca3c2927326da249c798d947ce644938f31b28f14e) (
.leaf 5 0xa8471e63651e2be1ed508e3cc6ca3c57c3b2a11c798d9478af87354238f31b28f15f0cfa8471e63651e28e267508e3cc6ca3c51450ea11c798d9478a281f54238f31b28f145010a8471e63651e27a251508e3cc6ca3c4f40faa11c798d94789989454238f31b28f133062a8471e63651e2660bf508e3cc6ca3c4cc176a11c798d94789982d54238f31b28f133057a8471e63651e2660ab508e3cc6ca3c4cc146a11c798d94789981f54238f31b28f133035a8471e63651e266055508e3cc6ca3c4cc03ea11c798d947894093d4238f31b28f128115a8471e63651e25021b508e3cc6ca3c4a0392a11c798d94789406654238f31b28f12803ea8471e63651e25001f508e3cc6ca3c3f018aa11c798d94787e01f54238f31b28f0ec05d)) (
.fork 7 0x54238f31b2c228f133 (
.leaf 6 0xa8471e63656055651f508e3cc6cac0a3c57ea11c798d95814781f54238f31b2b028f026a8471e63655e51e2bf508e3cc6ca3c99c4a2a11c798d94793009454238f31b28f235227a8471e63651e46a267508e3cc6ca3c8b04cea11c798d94791391254238f31b28f22715fa8471e63651e44e07d508e3cc6ca3c89c08aa11c798d947908899d4238f31b28f1dd1cda8471e63651e3ba267508e3cc6ca3c7484cea11c798d9478e68e4d4238f31b28f1cd15fa8471e63651e39a07d508e3cc6ca3c734072a11c798d9478e58afd4238f31b28f19e128a8471e63651e31a267508e3cc6ca3c5e8516a11c798d9478bd099d4238f31b28f15f145a8471e63651e2be27b508e3cc6ca3c57c4cea11c798d9478af87e54238f31b28f15f0f9) (
.fork 8 0x54240838f28f19e0d8 (
.leaf 7 0xa8481063651e2661bf509000ff0e3cc6ca3ea12001c798d9478afd4240038f31b28f05da8480071e63651e07d509000e3cc6ca3c0f2a11fb1f91c798d947d423f638f31b28f15fa847ec71e63651e07d508fd8e3cc6ca3c0eea11fa9c798d9478afd423ef38f31b28f128a8475271e63651e251508e54e3cc6ca3c4cea11ca9c798d94789454239531b28f13303ea8472a63651e26601f508e3cd9cc6ca3c4cea11c79b398d94789454238f35e31b28f128a8471e6b068c63651f508e3cd60c6ca3c4cea11c79ab98d947899d4238f34634331b28fa8471e68c63651e2bf508e3cd18c6ca3c0faa11c79a318d947819d4238f33331b28f133a8471e64251e26601f508e3cc6cb10ac0a3ea11c798d962147899d4238f31b2c228f133) (
.leaf 8 0xa8481071e63651e24f509020e3cc6ca3c456a12041c798d947886d4240838f31b28f101a8481071e63651e1fb509020e3cc6ca3c3f2a12041c798d94787cd4240838f31b28f0f6a8481071e63651e1dd509020e3cc6ca3c3b2a12041c798d94787254240838f31b28f0e0a8481071e63651e1b5509020e3cc6ca3c34aa12041c798d94786654240838f31b28f0caa8481071e63651e185509020e3cc6ca3c302a12041c798d94785e54240838f31b28f0b9a8481071e63651e13d509020e3cc6ca3c15ea12041c798d94782ad4240838f31b28f03ea8481071e63651e075509020e3cc6ca3c096a12041c798d94780cd4240838f31b28f00fa8481071e6364ce1a1509020e3cc6c99c332a12041c794793390b54240838f28f19e0d8))))) (
.fork 14 0x54244938f31b28f04a (
.fork 11 0x54241e38f31b28f280 (
.fork 10 0x54240838f34631b28f (
.leaf 9 0xa8481071e67e63651f509020e3ccecc6ca3ea12041c799c98d947d4240838f32531b28fa8481071e6365ca51f509020e3cc6cac0a3ea12041c798d947941d4240838f31b28f271a8481071e63651e4e1509020e3cc6ca3c9b2a12041c798d947935d4240838f31b28f26aa8481071e63651e4d1509020e3cc6ca3c99ea12041c798d94793254240838f31b28f260a8481071e63651e49d509020e3cc6ca3c8f2a12041c798d947913d4240838f31b28f219a8481071e63651e3e5509020e3cc6ca3c736a12041c798d9478d8d4240838f31b28f1a0a8481071e63651e33f509020e3cc6ca3c67aa12041c798d9478ced4240838f31b28f19aa8481071e63651e2d3509020e3cc6ca3c516a12041c798d94789ed4240838f31b28f133) (
.leaf 10 0xa8483c71e63651e355509078e3cc6ca3c57ea120f1c798d947852d4241e38f31b28f03ea8483c71e63651e051509078e3cc6ca3c066a120d1c798d9478d1d4241640838f31b28fa8482c71e63651e2bf509058e3cc6ca3c0faa120b1c798d947807d4241038f31b28f03ea8481a71e63651e1f9509021018e3cc6ca3ea12042021c798d947d4240840038f31b28fa848107f471e63651f509020fe0e3cc6ca3ea12041fb1c798d947d424083f038f31b28fa848107de71e63651f509020f40e3cc6ca3ea12041e59c798d947d424083bf38f31b28fa8481076e71e63651f509020ecce3cc6ca3ea12041d81c798d947d424083a938f31b28fa8481072a71e63651f509020e3cd9cc6ca3ea12041c79af18d947d4240838f34631b28f)) (
.fork 12 0x54243e40738f31b28f (
.leaf 11 0xa8487c71e63651e2bf5090f8e3cc6ca3c18aa121f1c798d94781f54243e38f31b28f03da8487081071e63651f5090e0e3cc6cc20a3ea121c1c798d9478fe54243838f31b28f15fa8487071e63651e0b15090e0e3cc6ca3c0faa121c1c798d94781d54243838f31b28f030a848647de71e63651f5090c8e3cc6ca3c99ea12191c798d9478cf54243238f31b28f133a8486471e63651e1c95090c8e3cc6ca3c332a12191c798d94781f54243238f31b28f00fa8485e71e63651e07d5090a9020e3cc6ca3ea12151c798d94794054242a38f31b28f15fa8485471e63651e14b5090a8e3cc6ca3c0faa12151c798d94781454242a38f31b28f025a8484c71e63651e4e7509088e3cc6ca3c0faa120f2041c798d947d4241e38f31b28f280) (
.fork 13 0x54244938f31b28f013 (
.leaf 12 0xa8489271e63651e025509124e3cc6ca3c042a12249c798d947807d4244938f31b1dd1c2a8489271e6363842bf509124e3cc6c7080faa12249c798914781f54244938f31228f00fa8489271e61c51e07d509124e3cc04a3c57ea12249c79801478afd4244938f30028f03ea8489271e5f651e2bf509124e3cbeca3c0faa12249c794791a90fd4244938f28f21f15fa8489271e51e43e07d509124e3ca3c85857ea12249c794790b01f54244938f28f1a715fa8489271e51e34e07d509124e20c6ca3c582a12249c418d9478afd4244938831b28f062a8489271063651e07d509124c6ca3c59c57ea122498d9478b38ad54244931b28f167062a8489263651e2ce07d509124c6ca3c59c04aa121f2041c798d947d4243e40738f31b28f) (
.leaf 13 0xa8489271e63651e093509124e3cc6ca3c122a12249c798d947823d4244938f31b28f046a8489271e63651e08b509124e3cc6ca3c112a12249c798d947821d4244938f31b28f042a8489271e63651e083509124e3cc6ca3c102a12249c798d94781fd4244938f31b28f03ea8489271e63651e07b509124e3cc6ca3c0f2a12249c798d94781dd4244938f31b28f035a8489271e63651e069509124e3cc6ca3c0cea12249c798d94781954244938f31b28f031a8489271e63651e05d509124e3cc6ca3c0aea12249c798d94781554244938f31b28f029a8489271e63651e04d509124e3cc6ca3c08aa12249c798d94780f54244938f31b28f01ca8489271e63651e02f509124e3cc6ca3c05aa12249c798d94780a54244938f31b28f013)))) (
.fork 16 0x54244938f31b28f173 (
.fork 15 0x54244938f31b28f098 (
.leaf 14 0xa8489271e63651e129509124e3cc6ca3c1f6a12249c798d947835d4244938f31b28f06aa8489271e63651e0d1509124e3cc6ca3c19ea12249c798d94783354244938f31b28f065a8489271e63651e0c9509124e3cc6ca3c18aa12249c798d947830d4244938f31b28f060a8489271e63651e0bf509124e3cc6ca3c176a12249c798d94782e54244938f31b28f05ba8489271e63651e0b5509124e3cc6ca3c166a12249c798d94782bd4244938f31b28f056a8489271e63651e0ab509124e3cc6ca3c152a12249c798d947829d4244938f31b28f052a8489271e63651e0a3509124e3cc6ca3c142a12249c798d947827d4244938f31b28f04ea8489271e63651e09b509124e3cc6ca3c132a12249c798d947825d4244938f31b28f04a) (
.leaf 15 0xa8489271e63651e2e5509124e3cc6ca3c5baa12249c798d9478b254244938f31b28f163a8489271e63651e2c5509124e3cc6ca3c586a12249c798d9478b054244938f31b28f15fa8489271e63651e2bd509124e3cc6ca3c576a12249c798d9478ae54244938f31b28f15ba8489271e63651e2b5509124e3cc6ca3c51ea12249c798d9478a1d4244938f31b28f12ba8489271e63651e255509124e3cc6ca3c4a6a12249c798d94789454244938f31b28f125a8489271e63651e247509124e3cc6ca3c44ea12249c798d94788954244938f31b28f107a8489271e63651e20d509124e3cc6ca3c3b6a12249c798d94787454244938f31b28f0e0a8489271e63651e1b5509124e3cc6ca3c346a12249c798d94785bd4244938f31b28f098)) (
.fork 17 0x54244938f31b28f1df (
.leaf 16 0xa8489271e63651e3bd509124e3cc6ca3c776a12249c798d9478ee54244938f31b28f1d9a8489271e63651e3b1509124e3cc6ca3c74aa12249c798d9478e8d4244938f31b28f1c9a8489271e63651e375509124e3cc6ca3c696a12249c798d9478cdd4244938f31b28f197a8489271e63651e323509124e3cc6ca3c63ea12249c798d9478c754244938f31b28f18da8489271e63651e319509124e3cc6ca3c62ea12249c798d9478c2d4244938f31b28f184a8489271e63651e305509124e3cc6ca3c606a12249c798d9478bfd4244938f31b28f17da8489271e63651e2f7509124e3cc6ca3c5eaa12249c798d9478bcd4244938f31b28f177a8489271e63651e2ed509124e3cc6ca3c5d6a12249c798d9478ba54244938f31b28f173) (
.fork 18 0x54244938f31b2be28f (
.leaf 17 0xa8489271e63656a51f509124e3cc6caaca3ea12249c798d94b147d4244938f31b28f276a8489271e63651e4cb509124e3cc6ca3c976a12249c798d94792b54244938f31b28f254a8489271e63651e489509124e3cc6ca3c906a12249c798d94791cd4244938f31b28f237a8489271e63651e46d509124e3cc6ca3c8d6a12249c798d94791a54244938f31b28f232a8489271e63651e459509124e3cc6ca3c8aea12249c798d94791254244938f31b28f21ca8489271e63651e425509124e3cc6ca3c846a12249c798d94790854244938f31b28f20fa8489271e63651e419509124e3cc6ca3c82aa12249c798d9478fad4244938f31b28f1f3a8489271e63651e3d3509124e3cc6ca3c78ea12249c798d9478f0d4244938f31b28f1df) (
.leaf 18 0xa8489271e69663651f509124e3cd0cc6ca3ea12249c79a098d947d4244938f33833228fa8489271e67051e2bf509124e3cce0a3c0faa12249c799c14781954244938f33531b28fa8489271e66863651f509124e3ccccc6ca3ea12249c799918d947d4244938f32f31b28fa8489271e65851e2bf509124e3cca4c6ca3ea12249c79949478d3d4244938f32428f03ea8489271e64251e07d509124e3cc84a3c03ea12249c798d974947d4244938f31b2e728fa8489271e6365ac51f509124e3cc6cb3ca3ea12249c798d966947d4244938f31b2cb28fa8489271e63658c51f509124e3cc6cb14a3ea12249c798d962147d4244938f31b2c328fa8489271e63658451f509124e3cc6cb04a3ea12249c798d95f947d4244938f31b2be28f)))))) (
.fork 29 0x54252050238f31b28f (
.fork 24 0x5424b638f31b28f03e (
.fork 21 0x54244940a38f31b28f (
.fork 20 0x5424493d831b28f15f (
.leaf 19 0xa8489279071e63651f509124f1ce3cc6ca3ea12249e318d9478afd424493bd31b28f15fa8489275a63651e2bf509124e9cc6ca3c57ea12249ce9c798d947d4244939c38f31b28fa8489273471e63651f509124e64e3cc6ca3ea12249cc1c798d947d4244939638f31b28fa8489272a71e63651f509124e54d94c6ca3ea12249ca98d947899d4244939531b28f00fa8489272871e63651f509124e3cdf8c6ca3ea12249c79bd98d947d4244938f37531b28fa8489271e6e063651f509124e3cdb4c6ca3ea12249c79b398d947d4244938f36331b28fa8489271e6c263651f509124e3cd7cc6ca3ea12249c79ad18d947d4244938f35931b28fa8489271e6b063651f509124e3cd5cc6ca3ea12249c79ab18d947d4244938f35331b28f) (
.leaf 20 0xa8489281271e63651f509125020fa4e3ca3ea1224a041ec9c798dd424494083cf31b28fa8489281077863651f509125020e3cce0a3ea1224a041c798d947d4244940838f31b1c2a8489281071e60051f509125020e3cbeca3ea1224a041c794790fd4244940838f28f217a8489281071e51e42d509125020e3ca3c69ea1224a041c418d947d4244940831b2db28fa8489281063651e3d9509125020c6ca3c59ea1224a0418d94787154244940738f31b28fa848927f871e63651f509124fc8e3cc6ca3ea12249f61c798d947d424493eb38f31b28fa848927d271e51e46b509124fa4e3ca3c57ea12249f49c794781f5424493e831b28f15fa848927b271e6363bb509124f64e3cc6c57ea12249ec9c798d81f5424493d831b28f15f)) (
.fork 22 0x54246c38f31b28f267 (
.leaf 21 0xa848d871e63651e2675091b0e3cc6ca3c332a1235a249c798d947d4246a40838f31b28fa848d089271e63651f50919d020e3cc6ca3ea1232a249c798d947d4246144938f31b28fa848c271e63651e1d950917d124e3cc6ca3ea122e2041c798d947d4245c38f31b28f15fa848b871e63651e0af509170e3cc6ca3c0faa122d2041c798d947d4245a38f31b28f15fa848b471e63651e0ab5091250cce3cc6ca3ea1224a191c798d947d4244943138f31b28fa8489285c71e63651f509125098e3cc6ca3ea1224a129c798d947d4244942138f31b28fa8489283471e63651f509125060e3cc6ca3ea1224a079c798d947d4244940e38f31b28fa8489281a71e63651f509125030e3cc6ca3ea1224a059c798d947d4244940a38f31b28f) (
.fork 23 0x54249238f31b28f15f (
.leaf 22 0xa8492471e63651e091509248e3cc6ca3c0faa1246a249c798d947d4248c44938f31b28fa8491689271e63651f50922ce3cc6ca3c99ea12459c798d9478cf54248b38f31b28f133a8491671e63651e199509229124e3cc6ca3ea1244a249c798d947d4248644938f31b28fa8490a89271e63651f50920d124e3cc6ca3ea1240a041c798d947d4247e44938f31b28fa848fa89271e63651f5091f4e3cc6ca3c4cea123e2249c798d947d4247b44938f31b28fa848f489271e63651f5091e1124e3cc6ca3ea1238a359c798d947d4247140838f31b28fa848e271e63651e2bf5091c4e3cc6ca3c10aa12389c798d94781f54247040838f31b28fa848dc89271e63651f5091b5124e3cc6ca3ea12362249c798d947d4246c38f31b28f267) (
.leaf 23 0xa8496889271e63651f5092cd124e3cc6ca3ea1258a041c798d947d424b044938f31b28fa8495689271e63651f5092a9124e3cc6ca3ea1253a249c798d947d424a549d38f31b28fa8494a81071e63651f509294e3cc6cb10a3ea12529c798d9478afd424a538f31b28f04ba8494a71e63651e07d509291020e3cc6ca3ea12512041c798d947d424a044938f31b28fa8493e89271e63651f509279124e3cc6ca3ea124f1f79c798d947d4249e38f31b28f133a8493c71e63651e1c9509275124e3cc6ca3ea124e2249c798d947d4249b40838f31b28fa8493289271e63651f509261020e3cc6ca3ea124ba249c798d947d4249444938f31b28fa8492491471e63651f509249020e3cc6ca3ea12491c79ac18d947d4249238f31b28f15f)))) (
.fork 26 0x5424f844938f31b28f (
.fork 25 0x5424e040838f31b28f (
.leaf 24 0xa849b681071e63651f50935ce3cc6ca3c57ea126aa691c798d947d424d540838f31b28fa849aa71e63651e3bb509354e3cc6ca3c57ea126a9c798d9478295424d538f31b28f03ea849a689271e63651f509349124e3cc6ca3ea12682249c798d947d424cc44938f31b28fa8499681071e6364cf509329124e3cc6ca3ea12652041c798d947d424ca38f31b28f0cca8499289271e63651f509321124e3cc6ca3ea1263a249c798d947d424c738f31b28f267a8498e71e63651e26750931ce3cc6ca3c332a12632249c798d947d424c444938f31b28fa8498689271e63651f509301124e3cc6ca3ea125b2599c798d947d424b640838f31b28fa8496c71e63651e46b5092d8e3cc6ca3c57ea125b1c798d947826d424b638f31b28f03e) (
.leaf 25 0xa849ee89271e63651f5093d9020e3cc6ca3ea127aa24a0418d947d424f240838f31b28fa849e089271e63651f5093bd22ce3cc6ca3ea1277a191c798d947d424ef40838f31b28fa849de81071e51e3ff5093bd020e3ca3c67aa12779c798d9478945424ef38f31b28f0daa849dc9ca89271e51f5093b9125020e3ca3ea12772249c79478afd424ee44938f28f054a849dc89271e51e07d5093b9020e3cc6ca3ea12772041c7947933d424ed40838f31b28fa849d889271e63651f5093ad020e3ca3c67aa1275224a041c7947d424e944938f31b28fa849d089271e63651f50939d124e3cc6ca3ea12732249c798d947d424e638f31b28f133a849ca89271e63651f509391020e3cc6ca3ea1271a249c798d947d424e040838f31b28f)) (
.fork 27 0x54250b38f31b28f133 (
.leaf 26 0xa84a1671e63651e1c950942ce3cc6ca3c332a12859c798d94781f54250b38f31b28f00fa84a1663651e266251509411124e3cc6ca3ea12821c798d94781f54250344938f31b28fa84a0489271e63651f509405124e3cc6ca3ea12802791c798d947d425004ef38f31b28fa84a0089271e63651f509400fbce3cc6ca3ea12801c798d947938d4250038f31b28f267a84a0071e63651e363509400e3cc6ca3c67aa12801c798d947899d4250038f31b28f0e4a84a0071e63651e199509400e3cc6ca3c2f2a12801c798d94785cd4250038f31b28f057a84a0071e63651e07d5093e93dce3cc6ca3ea127d2041c798d947d424fa38f31b28f17aa849f471e63651e2bf5093e8e3cc6ca3c15aa127d1c798d94781f5424f844938f31b28f) (
.fork 28 0x54252038f31b28f057 (
.leaf 27 0xa84a4071e63651e0ab509480e3cc6ca3c146a12901c798d94781f54252038f31b28f00fa84a4063651e2be267509480c6ca3c4cc4a2a129018d94789982bd4252031b28f13303ea84a4063651e26601f509445400e3cc6ca3ea1288a041c798d947d4251138f31b28f15fa84a2271e63651e07d509439124e3cc6ca3ea1286a249c798d947d4250c44938f31b28fa84a169de71e63651f50942d124f68c6ca3ea1285a249c798d947d4250b44936531b28fa84a168926365a451f50942d124c6ca3c79ea1285a2498d9478afd4250b44931b28f133a84a1689263651e25150942d124c6ca3c486a1285a2498d94784b54250b40831b28f133a84a167de71e63651f50942ce3cc6ca3c99ea12859c798d9478cf54250b38f31b28f133) (
.leaf 28 0xa84a40a0271e63651f509481400e3cc6ca3ea129028018d947899d425204e638f31b28fa84a4098e71e63651f509481278e3cc6ca3ea12902459c798d947d4252047d38f31b28fa84a408d871e63651f5094810c8e3cc6ca3ea12902041c798d947d4252040831b28f133a84a4072a71e63651f509480e3cd9cc6ca3ea12901c79ac18d947d4252038f33331b28fa84a4071e63658851f509480e3cc6ca3c8d6a12901c798d947908d4252038f31b28f1dda84a4071e63651e31b509480e3cc6ca3c5eaa12901c798d9478afd4252038f31b28f128a84a4071e63651e1c1509480e3cc6ca3c1aea12901c798d947833d4252038f31b28f066a84a4071e63651e0c5509480e3cc6ca3c17ea12901c798d94782ed4252038f31b28f057))))) (
.fork 34 0x5c754244938f31b28f (
.fork 31 0x59a54244938f31b28f (
.fork 30 0x56e44940838f31b28f (
.leaf 29 0xadc89271e6b063651f5b9124e3cc6ca3c57eb72249c798d94781f56a54244938f31b28facca8489271e63651f595509480e3cc6ca3eb2aa12389c798d947d6554244938f31b28facaa847ec71e63651f595508e3cc6ca3c4ceb2a249c798d9478a756454244938f31b28fac8a8471e63651e26758d509124e3cc6ca3eb0a249c798d9478afd6044940838f31b28fabe8fa89271e63651f57d125020e3cc6ca3eafa249c798d9478afd5f44938f31b28f03eaa289281071e63651f545124e3cc6ca3c57ea8a249c798d94781f54f44938f31b28f03ea9089271e63651e07d5094bd124e3cc6ca3ea1291a041c798d947d4252243838f31b28fa84a40a1671e63651f509481410e3cc6ca3ea12902819c798d947d4252050238f31b28f) (
.leaf 30 0xb2ca8489271e63651f651509124e3cc6ca3ec9aa12249c798d947d9254244938f31b28fb22a84a4071e63651f645509124e3cc6ca3ec8aa12001c798d947d9154238f31b28f133b22a8471e63651e1d9645124e3cc6ca3c9cec8a249c798d9478a759144938f31b28f085b20a8489271e63651f639125020e3cc6ca3ec6aa12249c798d947d8944940838f31b28fb1289271e63651e46b625124e3cc6ca3c57ec4a249c798d94781f58354244938f31b28fb0089281071e63651f601124e3cc6cb10a3ec02249c798d9478afd8044938f31b28f03eaf0a8489271e63651f5d5125020e3cc6ca3ebaa249c798d984147d7544938f31b28f15faea89271e63651e07d5d5124e3cc6ca3c0c2b8a24a041c798d947d6e44940838f31b28f)) (
.fork 32 0x5c044938f28f1a715f (
.leaf 31 0xb8089271e51e34e07d701124c6ca3c57c53ae022498d9478a701f5c040840638f31b28fb808107de71e63651f701020e3cc6ca3c99ee02041c798d9478cf5c040838f31b28f133b8081071e63651e203701020e3cc6ca3c392e02041c798d9478665c040838f31b28f03eb8071e63651e2be267700e3cc6ca3c4cc4a2e01c798d94789981f5c038f31b28f13300fb6889271e63651e07d6cd125020e3cc6ca3ed9a249c798d9478afdb344938f31b28f03eb64a8489263651e2bf6a5125020e3cc6ca3ed4a249c798d9478c6da944938f31b28f15fb5289271e63651e07d6a1125020e3cc6ca3ed3aa12249c798d947d9d44940838f31b28fb3a89271e63651e3bb675124e3cc6ca3c57ecea249c798d94781f59a54244938f31b28f) (
.fork 33 0x5c044940838f31b28f (
.leaf 32 0xb8089281071e60051f701125020e3ca3c69ee0224a0418d9478a75c044940831b28f0dfb8089272a71e63651f701124e3cd9cc6ca3ee02249c79ac18d947dc044938f33331b28fb8089271e65263651f701124e3cca4a3c69ee02249c798d962147dc044938f31b28f235b8089271e63651e423701124e3cc6ca3c832e02249c798d9478eedc044938f31b28f18db8089271e63651e2f5701124e3cc6ca3c57ee02249c798d9478945c044938f31b28f06bb8089271e63651e0d5701124e3cc6ca3c18ae02249c798d94782fdc044938f31b28f05db8089271e63651e0af701124e3cc6ca3c156e02249c798d947828dc044938f31b28f03eb8089271e63651e01f701124e3cc00a3c57ee02249c798014781f5c044938f28f1a715f) (
.leaf 33 0xb8ca8489271e63651f719509020e3cc6ca3ee32a11c798d9478725c554244938f31b28fb88b8089271e63651f711509480e3cc6ca3ee22a12249c798d947dc45423ef38f31b28fb88a8471e63651e267711508e3cc6ca3c392e22249c798d9478a75c059144938f31b28fb80aca89271e63651f70150942d124c6ca3ee02902801c798d947dc052040838f31b28fb80a4071e63651e2bf701480e3cc6ca3c15ee02901c798d94781f5c050b44940831b28fb80a1689271e63651f701401124e3cc6ca3ee0277a041c798d947dc04e644938f31b28fb8098e89271e63651f701279124e3cc6ca3ee0245a249c798d947dc047d44938f31b28fb808d889271e63651f7011250c8e3cc6ca3ee0224a051c798d947dc044940838f31b28f)))) (
.fork 36 0x5dc38f31b2bb2b028f (
.fork 35 0x5db54252038f31b28f (
.leaf 34 0xbb6a8489271e63651f769701124e3cc6ca3eed2a12249c798d947dd954244938f31b28fbb0a84a4071e63651f761509124e3cc6ca3eebaa12901c798d947dd754244938f31b28fbaca8489271e63651f755509124e3cc6ca3eea2a12249c798d947dd354244938f31b28fba4a8489271e63651f745701124e3cc6ca3ee8aa12901c798d947dd154244938f31b28fba2a8489271063651f745509124c6ca3c59ee8aa121f1c798d947dd154238f31b28f133ba2a8471e63651e1f97454e1124e3cc6ca3ee8a249c798d9478a75d144938f31b28f0adb9ea8489271e63651f735509124e3cc6ca3ee62a12249c798d947dcb54244938f31b28fb92a4489271e63651f725124fb8e3cc6ca3ee4a041f79c798d947dc754244938f31b28f) (
.leaf 35 0xbb871e63657651e267770e3cc6cae4a3c4ceee1c798d9581478a75dc38f31b2ae28f14ebb871e63651e46044f770e3cc6ca3c8c04ceee1c798d9479138a75dc38f31b28f1d61cdbb871e63651e3ac267770e3cc6ca3c73453aee1c798d9478c4099ddc38f31b28f15613dbb871e63651e2ac267770e3cc6ca3c538516ee1c798d9478a709eddc38f31b28f14e133bb871e63651e29c1f9770e3cc6ca3c5383e6ee1c798d9478a707b5dc38f31b28f14e0f1bb871e63651e29c1d9770e3cc6ca3c53833aee1c798d947899856ddc38f31b28f1330a8bb871e63651e266149770e3cc6ca3c4cc28aee1c798d9478998495dc38f31b28f133087bb871e63651e1f815b770e3cc6ca3c3d82a2edae02249c798d947ddb54252038f31b28f)) (
.fork 37 0x5dc44938f2f028f0ad (
.leaf 36 0xbb889271e51e46043f771124e3ca3c87c53aee2249c794790f0a75dc44938f28f21614ebb889271e51e34e29d771124e20c6ca3c53eee2249c418d9478a75dc44938831b28f0adbb889263651e2ce29d771124c6ca3c59c52aee22498d9478b3856ddc44931b28f167072bb887c71e63651e29d7710f8e3cc6ca3c2b6ee21c1c798d978147ddc43838f31b28f14ebb887071e63651e11b7710a8e3cc6ca3c53aee2151c798d9478545dc41e38f31b28f14ebb882c71e63651e29d771054e3cc6ca3c53aee2001c798d947939ddc40038f31b28f14ebb880071e63651e10b770fd8e3cc6ca3c53aee1c79a81a318d947ddc38f35031b28f133bb871e69e63651e267770e3cd18c6ca3c53aee1c798d97b147899ddc38f31b2bb2b028f) (
.fork 38 0x5dc44938f31b28f0a1 (
.leaf 37 0xbb889271e63651e141771124e3cc6ca3c27eee2249c798d94784eddc44938f31b28f09cbb889271e63651e125771124e3cc6ca3c246ee2249c798d947847ddc44938f31b28f08ebb889271e63651e111771124e3cc6ca3c21eee2249c798d9478435dc44938f31b28f077bb889271e63651e0eb771124e3cc6ca3c1d2ee2249c798d9478395dc44938f31b1d61c2bb889271e63638429d771124e3cc00a3c9f6ee2249c7980147939ddc44938f30028f1a7bb889271e60051e347771124e3cc00a3c53aee2249c798014784dddc44938f30028f085bb889271e60051e0e7771124e3cc00a3c1c6ee2249c7980147834ddc44938f30028f058bb889271e5f651e29d771124e3cbeca3c26eee2249c79781478d3ddc44938f2f028f0ad) (
.leaf 38 0xbb889271e63651e2ab771124e3cc6ca3c552ee2249c798d9478a9ddc44938f31b28f152bb889271e63651e2a3771124e3cc6ca3c542ee2249c798d9478a7ddc44938f31b28f14ebb889271e63651e29b771124e3cc6ca3c532ee2249c798d9478a5ddc44938f31b28f14abb889271e63651e23f771124e3cc6ca3c47aee2249c798d9478845dc44938f31b28f0b7bb889271e63651e16d771124e3cc6ca3c2d2ee2249c798d947859ddc44938f31b28f0b2bb889271e63651e161771124e3cc6ca3c2beee2249c798d947856ddc44938f31b28f0acbb889271e63651e157771124e3cc6ca3c2a2ee2249c798d947853ddc44938f31b28f0a6bb889271e63651e149771124e3cc6ca3c28eee2249c798d9478515dc44938f31b28f0a1))))))) (
.fork 58 0x5dc54251638f31b28f (
.fork 48 0x5dc54238f31b2aa28f (
.fork 43 0x5dc4ee4da44938f28f (
.fork 41 0x5dc4493a038f31b28f (
.fork 40 0x5dc44938f31b2b428f (
.leaf 39 0xbb889271e63651e4a7771124e3cc6ca3c90eee2249c798d94791c5dc44938f31b28f233bb889271e63651e463771124e3cc6ca3c8c2ee2249c798d947917ddc44938f31b28f22ebb889271e63651e455771124e3cc6ca3c86aee2249c798d947906ddc44938f31b28f1e0bb889271e63651e3b7771124e3cc6ca3c76aee2249c798d9478ebddc44938f31b28f1d6bb889271e63651e3ab771124e3cc6ca3c752ee2249c798d9478e85dc44938f31b28f1bcbb889271e63651e315771124e3cc6ca3c626ee2249c798d9478c45dc44938f31b28f187bb889271e63651e307771124e3cc6ca3c602ee2249c798d9478bf5dc44938f31b28f17cbb889271e63651e2f1771124e3cc6ca3c562ee2249c798d9478abddc44938f31b28f156) (
.leaf 40 0xbb889273663651e29d771124e3cdc4c6ca3eee2249c79b718d947ddc44938f36031b28fbb889271e6a863651f771124e3cd48c6ca3eee2249c79a898d947ddc44938f35031b28fbb889271e69e63651f771124e3cd38c6ca3eee2249c79a698d947ddc44938f34a31b28fbb889271e67463651f771124e3cce0bc0a3eee2249c799c1478a75dc44938f33828f0adbb889271e63660a51f771124e3cc6cbdca3eee2249c798d97b147ddc44938f31b2f528fbb889271e6365e851f771124e3cc6cbcca3eee2249c798d966147ddc44938f31b2c028fbb889271e63657a51f771124e3cc6caf0a3eee2249c798d95d947ddc44938f31b2ba28fbb889271e63657251f771124e3cc6cae0a3eee2249c798d95b947ddc44938f31b2b428f)) (
.fork 42 0x5dc49238f35031b28f (
.leaf 41 0xbb892471e63651e29d7711e5124e3cc6ca3eee23ba249c798d947ddc47644938f31b28fbb88ec71e63651e2677711d5124e3cc6ca3eee23a2249c798d947ddc47344938f31b28fbb88e271e63651e29d771170e3cc6ca3c53aee22d1c798d9478a75dc44940638f30028fbb88927de71e60051f771124fbce3cbeca3eee2249f69c79478a75dc4493e938f28f230bb88927d271e51e29d771124f90e3cc6ca3eee2249f198d9478a75dc4493e038f31b28fbb88927b271e6363ad771124f64e3cc6c53aee2249ea18d9478a75dc4493c531b28f14ebb889277463651e29d771124eccc6ca3c53aee2249d41c798d947ddc4493a638f31b28fbb889274a71e63651f771124e8ce3cc6ca3eee2249d09c798d947ddc4493a038f31b28f) (
.leaf 42 0xbb89dc89271e51e29d7713b9124e3ca3c28eee2712249c798d947ddc4de44938f31b28fbb89ba89271e63651f771371124e3cc6ca3eee26da249c798d947ddc4db44938f28f1ffbb89b681071e63651f77136ce3cc6ca3c4ceee26d9c798d947877ddc4da44938f31b28fbb89aa71e63651e3ad771354e3cc6ca3c53aee2612249c798d947ddc4bf44938f31b28fbb897c89271e63651f7712f5124e3cc6ca3eee25e2249c798d947ddc4bc38f31b28f267bb897871e63651e2677712f0e3cc6ca3c332ee25da249c798d947ddc4ba44938f31b28fbb896c71e63651e4617712d8e3cc6ca3c53aee2572249c798d947ddc4a944938f31b28fbb894a71e63657651f771294e3cc6ca3c53aee24b2249c798d947ddc49238f35031b28f))) (
.fork 45 0x5dc54231b28f1670fc (
.fork 44 0x5dc52b44938f31b28f (
.leaf 43 0xbb8a5489271e63651f7714a1124e3cc6ca3eee2932249c798d947ddc52552038f31b28fbb8a4a8b871e63651f771495124e3cc6ca3eee292a0b1c798d947ddc52538f31b28f133bb8a4889271e63651f77148136ce3cc6ca3eee29025e1c798d947ddc52047638f31b28fbb8a4071e6a063651f771480e3cc6cbd8a3eee2901c798d95d947ddc52038f31b28f230bb8a4071e63651e3ad771480e3cc6ca3c622ee2901c798d9478ab5dc52038f31b28f14ebb8a4071e63651e167771480e3cc6ca3c2caee2901c798d947856ddc52038f31b28f0a8bb8a4071e63651e149771480e3cc6ca3c28aee29018d9478a7099ddc51138f31b28f156bb8a2271e63651e29d7713e8e3cc6ca3c53aee27b22498d9478a75dc4ee4da44938f28f) (
.leaf 44 0xbb8a8463651e2ce177771505124e3cc6ca3eee2a02249c798d947ddc53f52038f31b28fbb8a7e89271e63651f7714f9480e3cc6ca3eee29f2249c798d947ddc53d44938f31b28fbb8a7889271e63651f7714ed124e3cc6ca3eee29d2249c798d947ddc53944938f31b28fbb8a70a4071e63651f7714e1124e3cc6ca3eee29c2249c418d947ddc53844931b28f167bb8a7087c71e63651f7714e0e3cc6ca3c4ceee29c1c798d94787e5dc53744938f31b28fbb8a6c89271e63651f7714d5124e3cc6ca3eee2992249c798d947ddc53044938f31b28fbb8a5c89271e63651f7714b5124e3cc6ca3eee2962901c798d947ddc52c44938f31b28fbb8a5885471e63651f7714b0e3cc6ca3c4ceee2961c798d94787b5dc52b44938f31b28f)) (
.fork 46 0x5dc54238f31b28f0f1 (
.leaf 45 0xbb8a8471e63651e1e1771508e3cc6ca3c3b2ee2a11c798d947875ddc54238f31b28f0eabb8a8471e63651e1d3771508e3cc6ca3c39aee2a11c798d947872ddc54238f31b28f0d7bb8a8471e63651e19f771508e3cc6ca3c33aee2a11c798d947866ddc54238f31b28f0bfbb8a8471e63651e17d771508e3cc6ca3c2f6ee2a11c798d94785dddc54238f31b1cd1c2bb8a8471e636384267771508e3cc48a3c4ceee2a11c7981147899ddc54238f30028f133bb8a8471e5f651e267771508e3cb78a3c4ceee2a11c794791390fddc54238f28f21f133bb8a8471e51e42c267771508e3ca3c69c4ceee2a11c418d94789a5dc54238831b28f133bb8a8471063651e1f9771508c6ca3c59c4ceee2a118d9478b38975dc54231b28f1670fc) (
.fork 47 0x5dc54238f31b28f13c (
.leaf 46 0xbb8a8471e63651e277771508e3cc6ca3c4eaee2a11c798d94789cddc54238f31b28f138bb8a8471e63651e26f771508e3cc6ca3c4daee2a11c798d94789addc54238f31b28f134bb8a8471e63651e267771508e3cc6ca3c4caee2a11c798d947898ddc54238f31b28f12fbb8a8471e63651e25d771508e3cc6ca3c4b6ee2a11c798d9478845dc54238f31b28f106bb8a8471e63651e20b771508e3cc6ca3c412ee2a11c798d947881ddc54238f31b28f102bb8a8471e63651e201771508e3cc6ca3c3feee2a11c798d94787e5dc54238f31b28f0fbbb8a8471e63651e1f5771508e3cc6ca3c3e6ee2a11c798d94787b5dc54238f31b28f0f5bb8a8471e63651e1e9771508e3cc6ca3c3ceee2a11c798d9478795dc54238f31b28f0f1) (
.leaf 47 0xbb8a8471e63651e4a5771508e3cc6ca3c90aee2a11c798d94791eddc54238f31b28f22dbb8a8471e63651e453771508e3cc6ca3c8a2ee2a11c798d947913ddc54238f31b28f226bb8a8471e63651e44b771508e3cc6ca3c88eee2a11c798d94790a5dc54238f31b28f1d3bb8a8471e63651e39f771508e3cc6ca3c73aee2a11c798d9478e6ddc54238f31b28f1ccbb8a8471e63651e397771508e3cc6ca3c72aee2a11c798d9478e45dc54238f31b28f1bfbb8a8471e63651e30d771508e3cc6ca3c522ee2a11c798d9478a35dc54238f31b28f145bb8a8471e63651e289771508e3cc6ca3c50aee2a11c798d9478a0ddc54238f31b28f140bb8a8471e63651e27f771508e3cc6ca3c4faee2a11c798d94789eddc54238f31b28f13c))))) (
.fork 53 0x5dc54244938f31828f (
.fork 50 0x5dc54242038f31b28f (
.fork 49 0x5dc5423bf31b28f133 (
.leaf 48 0xbb8a8476c71e63651f771508ed4e3cc6ca3eee2a11da1c798d947ddc5423b238f31b28fbb8a8475e71e63651f771508eb8e3cc6ca3eee2a11d61c798d947ddc5423aa38f31b28fbb8a8474863651e267771508e54c6ca3c4ceee2a11c79ae147899ddc54238f34c31b28fbb8a8471e69263651f771508e3cd20c6ca3eee2a11c79a398d947ddc54238f34631b28fbb8a8471e68a63651f771508e3cd10c6ca3eee2a11c79a118d947ddc54238f33828f133bb8a8471e65651e267771508e3cc84a3c4ceee2a11c798d95b147ddc54238f31b2b328fbb8a8471e63656451f771508e3cc6cac4a3eee2a11c798d958147ddc54238f31b2af28fbb8a8471e63655c51f771508e3cc6cab4a3eee2a11c798d956147ddc54238f31b2aa28f) (
.leaf 49 0xbb8a8483e71e63651f771509078e3cc6ca3eee2a120e1c798d947ddc54241a38f31b28fbb8a8482e71e63651f771509058e3cc6ca3eee2a120a9c798d947ddc54241438f31b28fbb8a8482471e63651f771509014e3cc6ca3eee2a12019c798d947ddc54240238f31b28fbb8a8480271e63651f771509000e3cc6ca3eee2a11ff9c798d947ddc5423fe38f31b28fbb8a847fa71e63651f771508fece3cc6ca3eee2a11fc9c798d947ddc5423f738f31b28fbb8a847ec71e63651f771508fd4e3cc6ca3eee2a11fa1c798d947ddc5423f338f31b28fbb8a847d271e51e44f771508fa4e3ca3c4ceee2a11ef18d947899ddc5423d938f31b1cdbb8a847b271e636267771508f40c6ca3c4ceee2a11e218d947899ddc5423bf31b28f133)) (
.fork 51 0x5dc54244931b28f16a (
.leaf 50 0xbb8a8489263651e2cf771509124c6ca3c38aee2a12241c798d947ddc54244738f31b28fbb8a8488a71e63651f771509110e3cc6ca3eee2a12219c798d947ddc54244238f31b28fbb8a8488271e63651f771509100e3cc6ca3eee2a121f9c798d947ddc54243e38f31b28fbb8a8487c71e51e1ad7715090f8e20c6ca3eee2a121f18d9478b3ddc54243d38f31b28fbb8a8487871e63651f7715090ece3cc6ca3eee2a121d1c798d947ddc54243938f31b28fbb8a8487071e63651f7715090d8e3cc6ca3eee2a12181c798d947ddc54242d38f31b28fbb8a8485871e63651f7715090ace3cc6ca3eee2a12151c798d947ddc54242838f31b28fbb8a8484c71e63651f771509090e3cc6ca3eee2a12119c798d947ddc54242038f31b28f) (
.fork 52 0x5dc54244938f28f1bc (
.leaf 51 0xbb8a8489271e51e375771509124e3ca3c6e2ee2a12249c79478dbddc54244938f28f1b5bb8a8489271e51e369771509124e3ca3c6caee2a12249c79478d3ddc54244938f28f1a4bb8a8489271c63651f771509124e34c6ca3eee2a12249c618d947ddc54244938b31b28fbb8a8489271463651f771509124e24c6ca3eee2a12249c418d947ddc54244938831b118bb8a848927105e051f771509124e20a3c68eee2a12249c4147890ddc54244931b2dc28fbb8a848926365b651f771509124c6ca3c8eeee2a122498d94790eddc54244931b28f1edbb8a8489263651e3d9771509124c6ca3c71aee2a122498d9478c35dc54244931b28f178bb8a8489263651e2e5771509124c6ca3c5c2ee2a122498d9478b65dc54244931b28f16a) (
.leaf 52 0xbb8a8489271e62e51f771509124e3cc58a3eee2a12249c798a947ddc54244938f31228fbb8a8489271e61e51f771509124e3cc38a3eee2a12249c7983947ddc54244938f30328fbb8a8489271e60451f771509124e3cc04a3eee2a12249c7980147ddc54244938f2fe28fbb8a8489271e5fa51f771509124e3cbf0a3eee2a12249c797d947ddc54244938f2fa28fbb8a8489271e5d851f771509124e3cb78a3eee2a12249c79479205dc54244938f28f222bb8a8489271e51e443771509124e3ca3c882ee2a12249c794790fddc54244938f28f21ebb8a8489271e51e431771509124e3ca3c85eee2a12249c794790b5dc54244938f28f215bb8a8489271e51e427771509124e3ca3c71aee2a12249c79478dfddc54244938f28f1bc)))) (
.fork 55 0x5dc5424493e938828f (
.fork 54 0x5dc54244938f32428f (
.leaf 53 0xbb8a8489271e64451f771509124e3cc84a3eee2a12249c7990147ddc54244938f31b2a6bb8a8489271e63653f771509124e3cc6ca6eee2a12249c798d94c5dc54244938f31b294bb8a8489271e63651f771509124e3cc6ca3aee2a12249c798d946ddc54244938f31b28cbb8a8489271e636517771509124e3cc6ca1aee2a12249c798d93fddc54244938f31b27bbb8a8489271e6364df771509124e3cc6c902ee2a12249c798d90eddc54244938f31b214bb8a8489271e63641b771509124e3cc6c82aee2a12249c798d904ddc54244938f31b206bb8a8489271e636407771509124e3cc6c716ee2a12249c798d8e25dc54244938f31b1c3bb8a8489271e636385771509124e3cc68a3eee2a12249c798c947ddc54244938f31828f) (
.leaf 54 0xbb8a848927d251e243771509124f98e3ca3eee2a12249f09c7947ddc5424493dc38f28fbb8a848927b271e637771509124f64e3cbc2ee2a12249ec9c78d1ddc5424493d938f121bb8a848927b2710637771509124f64c6c462ee2a12249eb1c798dddc5424493d238f31bbb8a8489279e63651f771509124f38c6ca3eee2a12249e61c798dddc5424493c931b28fbb8a8489277863651f771509124ee4c6ca3eee2a12249c918d947ddc54244939131b28fbb8a8489272063651f771509124e3cd70a3eee2a12249c799f147ddc54244938f33828fbb8a8489271e66c51f771509124e3ccc0a3eee2a12249c7996947ddc54244938f32c28fbb8a8489271e65651f771509124e3cca8a3eee2a12249c7994147ddc54244938f32428f)) (
.fork 56 0x5dc54247138f31b28f (
.leaf 55 0xbb8a848de71e63651f7715091a4e3cc6ca3eee2a12331c798d947ddc54246438f31b28fbb8a848c671e63651f771509188e3cc6ca3eee2a12301c798d947ddc54245e38f31b28fbb8a848b871e63651f77150916ce3cc6ca3eee2a122d1c798d947ddc54245938f31b28fbb8a848b071e63651f771509158e3cc6ca3eee2a122a9c798d947ddc54245438f31b28fbb8a848a671e63651f771509148e3cc6ca3eee2a12289c798d947ddc54245038f31b28fbb8a8489e71e63651f771509138e3cc6ca3eee2a12269c798d947ddc54244c38f31b28fbb8a8489671e63651f771509128e3cc6ca3eee2a12249f69c7947ddc5424493ea3d938fbb8a848927d27b471f771509124fa4e3ca3eee2a12249f49c788c5dc5424493e938828f) (
.fork 57 0x5dc5424d838f31b28f (
.leaf 56 0xbb8a849ae71e63651f771509358e3cc6ca3eee2a126a9ec9c798dddc5424d538f31b28fbb8a849aa71e636385771509350e3cc6ca3eee2a12689c798d947ddc5424b938f31b28fbb8a8497071e63651f7715092dce3cc6ca3eee2a125b1f49c7947ddc5424b638f31b28fbb8a8496c71e51e43f7715092d4e3cc6ca3eee2a12591c798d947ddc5424af38f31b28fbb8a8495a71e63651f7715092b0e3cc6ca3eee2a12541c798d947ddc5424a638f31b28fbb8a8494a71e63651f77150928ce3cc6ca3eee2a12509c798d947ddc54249a38f31b28fbb8a8492a71e63651f77150924ce3cc6ca3eee2a12491c798d947ddc54249038f31b28fbb8a8491c71e63651f77150921ce3cc6ca3eee2a12391c798d947ddc54247138f31b28f) (
.leaf 57 0xbb8a84a2a71e63651f771509450e3cc6ca3eee2a12899c798d947ddc54251238f31b28fbb8a84a2271e63651f771509440e3cc6ca3eee2a128598d947899ddc54250938f31b28fbb8a84a0e71e63651f771509414e3cc6ca3eee2a127f9c798d947ddc5424fe38f31b28fbb8a849fa71e63651f7715093f0e3cc6ca3eee2a127d9c798d947ddc5424fa38f31b28fbb8a849f271e63651f7715093d8c6ca3c4ceee2a127aa2498d947ddc5424f438f31b28fbb8a849e671e63651f7715093c5124e3ca3eee2a12772249c7947ddc5424ee43e38f28fbb8a849dc81071e51f7715093b8e3ca3c4ceee2a12771c7947877ddc5424ee38f28f0d6bb8a849d489271e51f77150937d124e3ca3eee2a126c9c798d947ddc5424d838f31b28f)))))) (
.fork 68 0x5ff54244938f31b28f (
.fork 63 0x5dc5b544938f31b28f (
.fork 60 0x5dc55144938f31b28f (
.fork 59 0x5dc54252038f31b1c2 (
.leaf 58 0xbb8a84a4071e63051f771509480e3cc58a3eee2a12901c7980147ddc54252038f2fb28fbb8a84a4071e51e43f771509480e3ca3c85aee2a12901c7947909ddc54252038f28f1b5bb8a84a4071e51e365771509480e3ca3c69eee2a12901c418d947ddc54252031b2d828fbb8a84a406365aa51f771509480c6ca3c7aaee2a129018d9478f45dc54252031b28f16dbb8a84a4063651e2d3771509480c6ca3c5a2ee2a129018d9478b3ddc54252031b28f166bb8a84a4063651e267771509480c6ca3c25eee2a128f9c798d947ddc54251e38f31b28fbb8a84a3871e63651f77150946ce3cc6ca3eee2a128d9c418d947ddc54251a38f31b28fbb8a84a3271e63651f771509460e3cc6ca3eee2a128b9c798d947ddc54251638f31b28f) (
.leaf 59 0xbb8aa282c71e63651f771544e3cc6ca3c4ceee2a7a249c798d947ddc54d44938f31b28fbb8a9689271e63651f771529124e3cc6ca3eee2a4a249c798d947ddc54844938f31b28fbb8a8e89271e63651f771519124e3cc6ca3eee2a2a249c798d947ddc54444938f31b28fbb8a8689271e63651f771509484e3cc6ca3eee2a12902771c7947ddc5425203e938f28fbb8a84a407b271e637771509480f60c6ca3eee2a12901ea18d947ddc5425203bd31b28fbb8a84a4077463651f771509480eccc6ca3eee2a12901d898d947ddc5425203b031b28fbb8a84a4075a63651f771509480e3cce0a3eee2a12901c798d947ddc54252038f31b28dbb8a84a4071e636519771509480e3cc6c81aee2a12901c798d901ddc54252038f31b1c2)) (
.fork 61 0x5dc57544938f31b28f (
.leaf 60 0xbb8aea71e63651e2677715d1124e3cc6ca3eee2b8a249c798d947ddc57044938f31b28fbb8ade89271e63651f7715b9480e3cc6ca3eee2b72491c798d947ddc56e44938f31b28fbb8adc89271e5e051f7715b9124e3ca3c69eee2b71c79a318d947ddc56e38f31b28f133bb8ada89271e63651f7715b1124e3cc6ca3eee2b5a249c798d947ddc56144938f31b28fbb8ac089271e63651f77157d480e3cc6ca3eee2afa249c798d947ddc55f38f31b28f133bb8aba89271e63651f771569124e3cc6ca3eee2ac2249c798d947ddc55744938f31b28fbb8aac89271e63651f771555124e3cc6ca3eee2aa2249c798d947ddc55344938f31b28fbb8aa489271e63651f771545480e3cc6ca3eee2a8a2e1c798d947ddc55144938f31b28f) (
.fork 62 0x5dc59c44938f31b28f (
.leaf 61 0xbb8b3689271e63651f771661124e3cc6c9ceee2c72249c798d947ddc58c44938f31b28fbb8b1689271e63651f771629124e3cc6ca3eee2c4a901c798d947ddc5894b638f31b28fbb8b128927d271e51f771625124e3cc6ca3eee2c4a249c794790fddc58938f31b28f227bb8b1271e63651e267771621124e3cc6ca3eee2c3a249c798d947ddc58544938f31b28fbb8b0889271e63651f771609124e3cc6ca3eee2c0a249c798d947ddc58052038f31b28fbb8b0094a71e63651f771601124e3cc6ca3eee2c02249c797d147ddc58044938f28f1a4bb8b0071e63656051f771600e3cc6ca3c4ceee2bf2249c798d947ddc57c44938f31b28fbb8af289271e63651f7715dd124e3cc6ca3eee2baa901c798d947ddc57544938f31b28f) (
.leaf 62 0xbb8b6889271e63651f7716cd480e3cc6ca3eee2d9a889c798d947ddc5b344938f31b28fbb8b6671e63651e27b7716cce3cc6ca3c4ceee2d92a129018d947ddc5b244931b28f14ebb8b6289271e63651f7716c1124e3cc6ca3eee2d72249c798d947ddc5ad44938f31b28fbb8b5889271e63651f7716ad124e3cc6ca3eee2d52249c798d947ddc5a952038f31b28fbb8b5289271e63651f7716a4e3cc6ca3c4ceee2d42249c798d947ddc5a044938f31b28fbb8b3e89271e63651f771679124e3cc6ca3eee2cea901c798d947ddc59d4d538f31b28fbb8b3a8927b271e637771675124e3cc6ca3eee2cea249c798d8e15dc59d44938f30028fbb8b3a89271e51e347771674e3cc6ca3c736ee2ce9c798d947899ddc59c44938f31b28f)))) (
.fork 65 0x5dc5c044938f31b1c2 (
.fork 64 0x5dc5c042a38f31b28f (
.leaf 63 0xbb8b8083c71e63651f771701058e3cc6ca3eee2e02001c798d947ddc5c03f638f31b28fbb8b8071e68c63651f771700e3cc6cac0a3eee2e01c798d947913ddc5c038f31b28f1cdbb8b8071e63651e28b771700e3cc6ca3c4f6ee2e01c798d947899ddc5c038f31b28f105bb8b8071e63651e205771700e3cc6ca3c3f2ee2e01c798d94787cddc5c038f31b28f0f6bb8b8071e63651e1d9771700e3cc00a3c4ceee2e01c79478d3899ddc5c031b28f14e133bb8b7e89271e63651f7716f9124e3cc6ca3eee2df2249c418d947ddc5bd44938f31b28fbb8b7889271e63651f7716ed124e3cc6ca3eee2dd2249c798d947ddc5b944938f31b28fbb8b7089271e63651f7716dd124e3cc6ca3eee2db2249c798d947ddc5b544938f31b28f) (
.leaf 64 0xbb8b8089271e63451f771701124e3cc60a3eee2e02249c798b947ddc5c044938f30328fbb8b8089271e60451f771701124e3cc04a3eee2e02249c7980147ddc5c044938f2fb28fbb8b8089271e51e43f771701124e3ca3c85aee2e02249c79478dc5dc5c044938f28f1b5bb8b8089271e51e369771701124e3ca3c69eee2e02249c418d947ddc5c044931b2da28fbb8b8089263651e475771701124c6ca3c7aeee2e022498d9478b8ddc5c044931b28f16dbb8b8089263651e2d7771701124c6ca3c59eee2e022498d9478acddc5c044931b28f14ebb8b8089263651e1bf771701124c00a3c53aee2e02249478d38a75dc5c044838f31b28fbb8b8088871e63651f7717010f8e3cc6ca3eee2e021c1c798d947ddc5c042a38f31b28f)) (
.fork 66 0x5dc5c052031b28f133 (
.leaf 65 0xbb8b80a4063651e243771701480c6ca3c0e2ee2e02889c798d947ddc5c050b44931b28fbb8b809f471e63651f7717013b9124e3ca3eee2e026a9c798d947ddc5c04b638f31b28fbb8b8094a71e63651f771701248e3cc6ca3eee2e02389c798d947ddc5c045c38f31b28fbb8b808b471e63651f771701124fa4e3ca3eee2e02249ec9c798dddc5c04493d031b28fbb8b8089279463651f771701124efcc6ca3eee2e02249d398d947ddc5c04493a431b28fbb8b8089274463651f771701124e78c6ca3eee2e02249c799c147ddc5c044938f32c28fbb8b8089271e65651f771701124e3cca8a3eee2e02249c798d947ddc5c044938f31b28ebb8b8089271e63651b771701124e3cc6c826ee2e02249c798d9035dc5c044938f31b1c2) (
.fork 67 0x5ef54244938f31b28f (
.leaf 66 0xbdca84a4071e63651f7b9509124e3cc6ca3ef6ae02249c798d947ded54252038f31b28fbdaa848e271e63651f7b5509124e3cc6ca3ef6aa11fb1c798d947ded54238f31b28f133bda89271e63651e29d7ad509124e3cc6ca3ef4aa12249c798d947de754244938f31b28fbcca8489271e63651f795509124e3cc6ca3ef22a12249c798d947de354244938f31b28fbc4a8489271e63651f785509124e3cc6ca3ef02a12249c798d947ddf54244938f31b28fbbca8489271e63651f775509124e3cc6ca3eee2e12249c798d947ddc5c144938f31b28fbb8b80a407b463651f771701480e3cc6ca3eee2e02901c7980147ddc5c052038f28f1a7bb8b80a406365a451f771701480c6ca3c79eee2e029018d9478a75dc5c052031b28f133) (
.leaf 67 0xbfea8471e63651e2677fd1d9124e3cc6ca3effa249c798d9478a75fe54244938f31b28fbfab8089271e63651f7f5509480e3cc6ca3efeaa12249c798d947dfd54238f31b28f133bfa89271e63651e29d7f1509124e3cc6ca3efdaa12249c798d947dfa5c044938f31b28fbf4a84a4071e63651f7e9509124e3cc6ca3efd2a12041c798d947dfa54238f31b28f133bf4a8471e63651e1ed7e9124e3cc6ca3c53afcaa12249c798d947df854244938f31b28fbeea8489271e63651f7d9509124e3cc6ca3efaaa12249c798d947df454244938f31b28fbe6a8489271e63651f7c9509124e3cc6ca3ef8aa12249c798d947df054252038f31b28fbe0a8489271e63651f7c1124e3cc6ca3c53af7aa12901c798d947def54244938f31b28f))))) (
.fork 73 0x65854244938831b28f (
.fork 70 0x6225424a538f31b28f (
.fork 69 0x61254238f34631b28f (
.leaf 68 0xc24a8471e63651e267849124e3cd40c6ca3f092249c798d9478a761154244938f31b28fc20a8489271e63651f83d509124e3cc6ca3f062a12249c798d947e0c44938f31b28f14ec12a8489271e63651f825124e3cc6ca3c53b042e02249c798d947e0854244938f31b28fc0ea8489271e63651f819509124e3cc6ca3f02aa12249c798d947e0554238f31b28f0fcc08a8489271e63651f80d509124e3cc6ca3f012a12249c798d947e0254238f31b28f0ecc02b8089271e63651f805509480e3cc6ca3f00aa12249c798d947e0154240838f31b28fc02a8471e63651e267805508e3cc6ca3c3e700a249c798d9478a760054244938f31b28fbfeb8089271e63651f7fd57d124e3cc6ca3effaa12901c798d947dff54244938f31b28f) (
.leaf 69 0xc44a8489271e63651f889508e3cc6cac0a3f112a11c798d947899e2244938f31b2bb28fc4489271e63651e29d881509124e3cc6ca3f0f2a12249c798d947e1c54244938f31b28fc36a8489271e63651f869701124e3cc6ca3f0d2e02249c79478d3e1a54244938f31b28fc34a8489271e51e34f861701124e3cc6ca3f0c2a12901c798d947e1854244938f31b28fc30a8483471e63651f861508e3cc6ca3c4cf0c2a11c798d94787961844938f31b2f028fc3089271e63651e29d861124e3cc6ca3c2370baa12249c798d947e1554244938f31b28fc28a8489271e63651f84d509124e3cc6ca3f092e02249c798d947e1256e44938f31b28fc24a84a4071e63651f849509248e3cc6ca3f092a12249c798d947e1254238f34631b28f)) (
.fork 71 0x63252c44938f31b28f (
.leaf 70 0xc6489271e6365e051f8c9124e3cc6ca3c53b192249c798d947852e3244938f31b28f08dc60a8489271e63651f8bd509124e3cc6ca3f172a12249c798d947e2e54238f31b28f133c5aa8489271e63651f8b1509124e3cc6ca3f15ae02249c798d947e2b58944938f31b28fc56a84a4071e63651f8ad5092d8e3cc6ca3f15aa12249f49c7947e2b54244938f31b28fc56a8489271e51e43f8ad508e3cc6ca3c89f15aa11c798d947899e2b44938f31b28f230c5689271e63651e29d8a9509124e3cc6ca3f14aa12249c798d947e2754244938f31b28fc4ca8489271e63651f895509124e3cc6ca3f122a12249c798d947e2354244938f31b28fc44b8089271e63651f889601124e3cc6ca3f112a12901c798d947e225424a538f31b28f) (
.fork 72 0x64454244938f31b28f (
.leaf 71 0xc86a8483c71e63651f8fd509124e3cc6ca3f1f2a12249c798d947e3e54238f31b28f133c7aa8489271e63651f8f1509124e3cc6ca3f1dae02249c798d947e3b59d44938f31b28fc76a84a4071e63651f8ed509354e3cc6ca3f1daa12249ec9c798de3b54244938f31b28fc76a8489271e6363858ed508e3cc6ca3c7371daa11c798d947899e3b44938f31b28f1d6c7689271e63651e29d8e9509124e3cc6ca3f1caa12249c798d947e3854244938f31b28fc6ea8487071e63651f8d9701124e3cc6ca3f1b2a12249c798d947e3454244938f31b28fc66a8489271e63651f8c9701124e3cc6ca3f192a12901c798d947e3254244938f31b28fc64a8484c71e63651f8c9508e3cc6ca3c4cf192a11c798d94787a63252c44938f31b28f) (
.leaf 72 0xcaea8489271e63651f959509124e3cc6ca3f2aaa12249c798d947e5454244938f31b28fca6a8489271e63651f949509124e3cc6ca3f28aa12249c798d947e5054244938f31b28fc9ea8489271e63651f939509124e3cc6ca3f26aa12249c798d947e4c54244938f31b28fc96b8089271e63651f92d509480e3cc6ca3f25aa127d1c798d947e4b54244938f31b28fc96a8471e63651e28b92d508e3cc6ca3c4cf25a249c798d9478a764a54244938f31b28fc92a8489271e63651f921509124e3cc6ca3f23aa12249c798d947e4654244938f31b28fc8ab8089271e63651f9156a5124e3cc6ca3f22aa12901c798d947e4554244938f31b28fc8aa8471e63651e267915124e3cc6ca3c62322a249c798d9478a764454244938f31b28f)))) (
.fork 75 0x65954244938f28f21f (
.fork 74 0x65954238f31b28f105 (
.leaf 73 0xcb2a8471e63651e209965508e3cc6ca3c3f32caa11c798d94787ce5954238f31b28f0f6cb2a8471e63651e1d9965508c6ca3c57c4cf2caa0a249c798d947e5953844938f31b28fcb2a5889271e63651f965495124e3cc6ca3f2ca901c798d9478a76594db44938f31b28fcb297889271e63651f9651d9124e3cc6ca3f2ca249c79a818d947e5944938f31b2f628fcb289271e6365e651f965124e3cc6caeca3f2ca249c798d94791865944938f31b28f1d6cb289271e63651e311965124e3cc6ca3c55b2ca249c798d9478a765944938f31b28f0b6cb289271e63651e15b965124e3cc6ca3c2a32ca249c798d94785265944938f31b28f0a2cb289263651e2be29d964e3cc6ca3c5384cf2c2a12249c798d947e5854244938831b28f) (
.leaf 74 0xcb2a8489271e51e42d965509124e3ca3c6e32caa12249c79478dbe5954244938f28f1a7cb2a8489271063651f965509124c6cb68a3f2caa122498d9478f5e5954244931b28f171cb2a8489263651e2df965509124c6ca3c59f2caa122498d9478b365954244931b28f165cb2a8489263651e2bf965509124c6ca3c3872caa12241c798d947e5954244738f31b28fcb2a8487c71e63651f9655090e0e3cc6ca3f2caa121b1c798d947e5954242a38f31b28fcb2a8483c71e63651f965509058e3cc6ca3f2caa12001c798d947e595423f638f31b28fcb2a8471e68c63651f965508e3cc6cac0a3f2caa11c798d947913e5954238f31b28f1cdcb2a8471e63651e28b965508e3cc6ca3c4f72caa11c798d947899e5954238f31b28f105)) (
.fork 76 0x65954252031b28f096 (
.leaf 75 0xcb2a84a2271e63651f9655093e8e3cc6ca3f2caa127b22498d947e595424ee44938f28fcb2a849aa71e63651f9655092d8e3cc6ca3f2caa12529c798d947e5954249238f31b28fcb2a848e271e63651f965509170e3cc6ca3f2caa122d1c798d947e5954245038f31b28fcb2a848927d271e51f965509124f64e3cc6f2caa12249e818d947e595424493bf31b28fcb2a8489273663651f965509124e5cc6ca3f2caa12249ca98d947e5954244939331b28fcb2a8489271e67051f965509124e3cc84a3f2caa12249c798d947e5954244938f31b28ecb2a8489271e636413965509124e3cc6c70b2caa12249c798d147e5954244938f31928fcb2a8489271e62451f965509124e3cc00a3f2caa12249c797d947e5954244938f28f21f) (
.fork 77 0x65c54244938f31b28f (
.leaf 76 0xcb6a8489271e63651f969509124e3cc6ca3f2d2a11c798d947899e595dc5c052031b28fcb2b80a84a4063651f965701481124c6ca3f2cae02901c798d947e595c044938f31b28fcb2b8089271e60051f965701124e3ca3c69f2cae022498d9478afe595c044931b28f14ecb2b8089263651e1bd965700e3cc6ca3c4cf2cad9a249c798d947e595a944938f31b28fcb2b3a89271e63651f965625124e3cc6ca3f2cac02249c798d947e5957744938f31b28fcb2aea89271e63651f9655b9124e3cc6ca3f2caafa249c798d947e5955144938f31b28fcb2a84a407b463651f965509480e3cc6ca3f2caa129018d969147e5954252031b28f1e7cb2a84a4063651e2bf965509480c6ca3c4cf2caa129018d947890e5954252031b28f096) (
.leaf 77 0xceebb889271e60051f9d5509124e3cc6ca3f382a12801c798d947e7054240838f31b28fcd8bb8a8489271e4e19b1771509124484463362ee26da249c7947e6c5424ef40838f28fcd6bb8a84a4071e51f9ad771509124e3ca3f33aee2249c7980147e6754242a38f31b28fccea8483c71e63651f99d4b1124e3cc6ca3f33a91a249c798d947e6654244938f31b28fcbea8489271e63651f979509124e3cc6ca3f2eaa12249c798d947e5c54244938f31b28f)))))))⟩

set_option maxRecDepth 16000 in
def bank6 : PackedSeq := ⟨1741, 83, 0x7ffffffffffffffffffff, .fork 27 0x5dc54244938f31b28f1bd (
.fork 13 0x5dc44938f31b28f14e08d (
.fork 6 0x54244938f31b28f15f085 (
.fork 3 0x5dc54244938831b28f (
.fork 1 0x54244938f36731b28f (
.leaf 0 0xa8489271e6b063651e001509124e3ccccc6ca3c002a12249c798d96214780054244938f31b28f235000a8489271e63651e422001509124e3cc6ca3c774002a12249c798d9478c680054244938f31b28f17a000a8489271e63651e2be001509124e3cc6ca3c4a0002a12249c798d94783100054244938f31b28f05f000a8489271e63651e0ba001509124e3cc6ca3c15c002a12249c798d94782a80054244938f31b28f051000a8489271e63651e07c001509124e3cc6ca3c03c002a12041f79c798d94780054240838f31b28f267000a8481071e63651e33c001509020e3cc6ca3c4cc002a12041c798d94787200054240838f31b28f0cc000a8481071e63651e07c001508e3cc6ca3c57c4cc002a11c798d94789989400054238f31b28f13303e000a8471e63651e26601e001125020e3cc6ca3c538002249c798d9478af8a700044938f31b28f14e03e) (
.fork 2 0x5dc44938f31b28f188 (
.leaf 1 0xbb889271e63651e2ac001771124e3cc6ca3c538002ee2249c798d9478568005dc44938f31b28f0a8000bb889271e63651e148001771124e3cc6ca3c288002ee1c798d9478a70998005d154244938f31b28f000b88a8489271e63651e001701125020e3cc6ca3c002e02249c798d9478af8005c044938f31b28f03e000b22a8489271e63651e001595509124e3cc6ca3c002a12902801c798d94780054252040838f31b28f000a84a4071e63651e2be001509480e3cc6ca3c15c002a12901c798d94781f00054250b44938f31b28f000a84a0089271e63651e0015093bd020e3cc6ca3c002a12732249c798d9478005424c744938f31b28f000a8493c89271e63651e00150922d124e3cc6ca3c002a123ea249c798d94780054246c44938f31b28f000a8489286471e63651e001509125020e3cc6ca3c002a12249ca9c798d94780054244938f36731b28f) (
.leaf 2 0xbb8a8489263651e2ce0017715090f8e3cc6ca3c002ee2a121c1c798d9478005dc54242a38f31b28f000bb8a8483c71e63651e001771509058e3cc6ca3c002ee2a12001c798d9478005dc5423f638f31b28f000bb8a8471e68c63651e001771508e3cc6cac0a3c002ee2a11c798d9479138005dc54238f31b28f1cd000bb8a8471e63651e28a001771508e3cc6ca3c4f4002ee2a11c798d9478998005dc54238f31b28f0fc000bb8a8471e63651e1f2001771508e3cc6ca3c3d8002ee2a11c798d9478760005dc53844938f31b28f000bb8a5889271e63651e001771495124e3cc6ca3c002ee2901c798d9478a70005dc4db44938f31b28f000bb897889271e63651e0017711d9124e3cc6ca3c002ee2249c79a818d9478005dc44938f31b2f628f000bb889271e63657651e001771124e3cc6ca3c8c0002ee2249c798d9478eb0005dc44938f31b28f188))) (
.fork 4 0x5dc5c044931b28f14e (
.leaf 3 0xbb8b8071e63651e2660017716cd124e3cc6ca3c002ee2d4a249c798d9478005dc59d44938f31b28f000bb8b1289271e63651e001771601124e3cc6ca3c002ee2baa249c798d9478005dc56e44938f31b28f000bb8abe89271e63651e001771545124e3cc6ca3c002ee2a12901c798d9478005dc54252031b28f133000bb8a84a2271e63651e0017715093e8e3cc6ca3c002ee2a12772249c79478005dc5424d538f31b28f000bb8a8496c71e63651e001771509294e3cc6ca3c002ee2a12491c798d9478005dc54247138f31b28f000bb8a848b871e63651e001771509168e3cc6ca3c002ee2a12249f49c79478005dc5424493d938f31b000bb8a8489271e67051e001771509124e3cc6c708002ee2a12249c79801478005dc54244938f2fb28f000bb8a8489271e51e43e001771509124e3ca3c858002ee2a12249c79478d38005dc54244938831b28f) (
.fork 5 0x54244938f31b28f03e02d (
.leaf 4 0xa8489271e63651e07c051509124e3cc6ca3c0f8096a12249c798d94781f00ed4244938f31b28f03e019a8489271e63651e07c01f509124e3cc6ca3c0f8022a12249c798d94781f000d4244938f31b28f030028000cb2b8089271e63651e001965509480e3cc6ca3c0032caa12249c798d94780065954244931b28f15f000cb2a8471e63651e266001965124e3cc6ca3c53800325aa12249c798d94780064554244938f31b28f000c76a8489271e63651e0018c9509124e3cc6ca3c00315aa12249c798d94780062254244938f31b28f000c30a8489271e63651e001849509124e3cc6ca3c00300aa12249c798d9478005ff54244938f31b28f000bfaa8489271e63651e0017e9509124e3cc6ca3c002f6aa12249c798d9478005dc5c052038f31b28f000bb8b8089271e63651e001771701124e3cc00a3c002ee2e02249c79478d38005dc5c044931b28f14e) (
.leaf 5 0xa8489271e63651e2be0ed509124e3cc6ca3c57c162a12249c798d9478af81f54244938f31b28f15f038a8489271e63651e2be061509124e3cc6ca3c57c0a2a12249c798d9478af800d4244938f31b28f14e03ea8489271e63651e266251509124e3cc6ca3c4cc0faa12249c798d947899807d4244938f31b28f12103ea8489271e63651e23007d509124e3cc6ca3c3bc0faa12249c798d94787201f54244938f31b28f0de03ea8489271e63651e1ac07d509124e3cc6ca3c3300faa12249c798d94785282c54244938f31b28f0a503ea8489271e63651e14a061509124e3cc6ca3c26c0faa12249c798d94784b01f54244938f31b28f08d03ea8489271e63651e10a07d509124e3cc6ca3c1600faa12249c798d94782c01454244938f31b28f03e03aa8489271e63651e07c071509124e3cc6ca3c0f80daa12249c798d94781f01854244938f31b28f03e02d)))) (
.fork 9 0x5424493da38f31b28f15f (
.fork 7 0x54244938f31b28f1e703e (
.leaf 6 0xa8489271e63651e35c2bf509124e3cc6ca3c6b80faa12249c798d9478d50afd4244938f31b28f1aa03ea8489271e63651e354061509124e3cc6ca3c68c57ea12249c798d9478d181f54244938f31b28f19e15fa8489271e63651e33c07d509124e3cc6ca3c65457ea12249c798d9478ca81f54244938f31b28f15f14ea8489271e63651e2be293509124e3cc6ca3c57c4cea12249c798d9478af89454244938f31b28f15f121a8489271e63651e2be241509124e3cc6ca3c57c462a12249c798d9478af88bd4244938f31b28f15f111a8489271e63651e2be217509124e3cc6ca3c57c3bea12249c798d9478af87254244938f31b28f15f0dea8489271e63651e2be1ad509124e3cc6ca3c57c332a12249c798d9478af85c54244938f31b28f15f0a5a8489271e63651e2be137509124e3cc6ca3c57c25aa12249c798d9478af846d4244938f31b28f15f085) (
.fork 8 0x54244938f31b2d228f03e (
.leaf 7 0xa8489271e63659451e2bf509124e3cc6cb10a3c79ea12249c798d94a94781f54244938f31b28f28303ea8489271e63651e5003f9509124e3cc6ca3ca0057ea12249c798d94794002c54244938f31b28f28003ea8489271e63651e500061509124e3cc6ca3c9cc846a12249c798d9479398afd4244938f31b28f27303ea8489271e63651e4ce2bf509124e3cc6ca3c99c0faa12249c798d94792d8afd4244938f31b28f259235a8489271e63651e4b22bf509124e3cc6ca3c9640faa12249c798d9479248afd4244938f31b28f24903ea8489271e63651e3fe2bf509124e3cc6ca3c7fc0faa12249c798d9478fe0afd4244938f31b28f1fc0a5a8489271e63651e3f807d509124e3cc6ca3c7f00a2a12249c798d9478fc0afd4244938f31b28f1f803ea8489271e63651e3e22bf509124e3cc6ca3c7c40faa12249c798d9478f38afd4244938f31b28f1e703e) (
.leaf 8 0xa848927b471e63651e07d509124e54e3cc6ca3c0faa12249c79c098d94781f54244938f37f31b28f15fa8489271e6fe63651e07d509124e3cdd8c6ca3c57ea12249c79b998d9478bd54244938f37331b28f15fa8489271e6e663651e07d509124e3cd9cc6ca3c57ea12249c79b298d9478c6d4244938f36531b28f15fa8489271e6ca63651e07d509124e3cd6cc6ca3c57ea12249c79ac18d9478cad4244938f33331b28f1a3a8489271e64a63651e07d509124e3cc6cc2ca3c0faa12249c798d98414794054244938f31b30828f1aaa8489271e63661051e2bf509124e3cc6cc20a3c296a12249c798d98414781f54244938f31b30828f028a8489271e6365e051e2bf509124e3cc6cbc0a3c0faa12249c798d9711478afd4244938f31b2e228f03ea8489271e6365a851e2bf509124e3cc6cb48a3c776a12249c798d9691478afd4244938f31b2d228f03e))) (
.fork 11 0x54247d44938f31b28f0de (
.fork 10 0x54244940838f31b28f195 (
.leaf 9 0xa8489281071e63651e2bf509125020e3cc6ca3c53aa1224a041c798d947899d4244940838f31b28f128a8489281071e63651e243509125020e3cc6ca3c462a1224a041c798d947877d4244940838f31b28f0e7a8489281071e63651e1c9509125020e3cc6ca3c37ea1224a041c798d94786f54244940838f31b28f0d8a8489281071e63651e1ad509125020e3cc6ca3c342a1224a041c798d94786654244940838f31b28f0a5a8489281071e63651e137509125020e3cc6ca3c26aa1224a041c798d94784b54244940838f31b28f08da8489281071e63651e10b509125020e3cc6ca3c162a1224a041c798d94781f54244940838f31b28f038a8489281071e63651e061509125020e3cc6ca3c0a2a1224a041c798d947800d424493ef38f31b28f15fa848927de71e63651e07d509124fa8e3cc6ca3c57ea12249f51c798d94781f5424493da38f31b28f15f) (
.leaf 10 0xa848d889271e63651e1c9509125020fbce3cc6ca3ea1224a041f71c798d947d424494083ea38f31b28fa848928107b471e63651f509125020e3cdfcc6ca3ea1224a041c79b998d947d4244940838f36531b28fa8489281071e6c863651f509125020e3cc6cc20a3ea1224a041c798d978147d4244940838f31b2e228fa8489281071e6365c251f509125020e3cc6cb48a3ea1224a041c798d94794054244940838f31b28f273a8489281071e63651e4cf509125020e3cc6ca3c99aa1224a041c798d94792cd4244940838f31b28f249a8489281071e63651e3ff509125020e3cc6ca3c7f2a1224a041c798d9478fc54244940838f31b28f1f1a8489281071e63651e3df509125020e3cc6ca3c79ea1224a041c798d9478d754244940838f31b28f1aaa8489281071e63651e347509125020e3cc6ca3c67aa1224a041c798d9478ce54244940838f31b28f195)) (
.fork 12 0x59954244938f31b28f03e (
.leaf 11 0xad2a8489271e63651e2bf595509124e3cc6ca3c25aa82a12249c798d94781f54252344938f31b28f03ea84a4489281071e63651f509489124e3cc6ca3ca02a12912249c798d9478afd4252244938f31b28f0a5a84a4489271e63651e07d509489124e3cc6ca3c0a2a12902802249c798d947d4252044940838f31b28fa84a4089271e63651e2bf509481124e3cc6ca3c15ea12902249c798d94781f54250b44940838f31b28fa849de9cc89271e63651f5093bd125020e3cc6ca3ea1277a249c798d9478afd424ef44938f31b28f055a849de89271e63651e07d5093ad125020e3cc6ca3ea1267a63a249c798d947d424cf44940838f31b28fa8499e89271e63651e2bf50933d124e3cc6ca3c146a1267a249c798d94781f5424cb44940838f31b28fa8493c89271e63651e19950922d124e3cc6ca3c35aa123fa249c798d9478afd4247d44938f31b28f0de) (
.leaf 12 0xbb889271e63651e29c10b771124e3cc6ca3c538162ee2249c798d9478a701f5dc44938f31b28f14e038bb889271e63651e29c061771124e3cc6ca3c5380a2ee2249c798d9478a700addc44938f31b28f14e001bb889271e63651e1c8137771124e3cc6ca3c294216ee2249c798d94785282c5dc44938f31b28f09b08dbb889271e63651e13610b771124e3cc6ca3c234216ee2249c798d94784682c5ca5c454244938f31b28fb94a8489281071e63651f729509124e3cc6ca3c57ee52a12249c798d94782fdca54244938f31b28f03eb92a8489281071e63651f701509125020e3cc6ca3ee02a12249c798d9478afdc054244938f31b28f03eb4ca8489281071e63651f699509124e3cc6ca3c57ed32a12249c798d94781f59959154244938f31b28fb32a8489281071e63651f665509124e3cc6ca3c57eccaa12249c798d94782ed9954244938f31b28f03e))))) (
.fork 20 0x5dc54244938f31b1ff1ae (
.fork 16 0x5dc54238f31b28f13300f (
.fork 14 0x5dc44938f31b28f24914e (
.leaf 13 0xbb889271e63651e3fe29d771124e3cc6ca3c7f053aee2249c798d9478fc0a75dc44938f31b28f1f8085bb889271e63651e3e229d771124e3cc6ca3c79c53aee2249c798d9478d70a75dc44938f31b28f1aa14ebb889271e63651e34629d771124e3cc6ca3c68c236ee2249c798d9478cf0a75dc44938f31b28f19514ebb889271e63651e2be29d771124e3cc6ca3c538526ee2249c798d9478a7099ddc44938f31b28f14e127bb889271e63651e29c243771124e3cc6ca3c538476ee2249c798d9478a708c5dc44938f31b28f14e116bb889271e63651e29c221771124e3cc6ca3c53842aee2249c798d9478a7077ddc44938f31b28f14e0e4bb889271e63651e29c1bd771124e3cc6ca3c53835aee2249c798d9478a70665dc44938f31b28f14e0bcbb889271e63651e29c14b771124e3cc6ca3c53826eee2249c798d9478a704b5dc44938f31b28f14e08d) (
.fork 15 0x5dc44938f37f31b28f156 (
.leaf 14 0xbb889271e6fe63651e29d771124e3cdccc6ca3c53aee2249c79b498d9478a75dc44938f36531b28f188bb889271e6ca63651e29d771124e3cd54c6ca3c53aee2249c79a818d9478caddc44938f31b30828f14ebb889271e6365ec51e355771124e3cc6cbc0a3c9ceee2249c798d9781478d1ddc44938f31b2f028f14ebb889271e6365e051e137771124e3cc6cbc0a3c216ee2249c798d97814782c5dc44938f31b2e228f14ebb889271e6365ae51e29d771124e3cc6cb48a3c75aee2249c798d9691478a75dc44938f31b2c928f14ebb889271e63657651e3cf771124e3cc6ca3ca0053aee2249c798d9479398fc5dc44938f31b28f27314ebb889271e63651e4e614b771124e3cc6ca3c9cc26eee2249c798d947939846ddc44938f31b28f26714ebb889271e63651e4bc29d771124e3cc6ca3c9648c2ee2249c798d94792c8a75dc44938f31b28f24914e) (
.leaf 15 0xbb8a8471e63651e266003771508e3cc6ca3c3bc392ee2a11c798d9478778665dc54238f31b28f0ef03ebb8a8471e63651e1c8199771508e3cc6ca3c39026eee2a11c798d94786b0665dc52544938f31b28f038bb8a4489271e63651e4e7771489124e3cc6ca3c53aee2912249c798d947842ddc52244938f31b28f058bb8a4089271e63651e29d7713bd36d124e3cc6ca3eee277a249c798d9478a75dc4ef44938f31b28f0a4bb899e97889271e63651f77133d124e3cc6ca3c53aee267a249c798d9478515dc48244938f31b28f14ebb88ec89271e63651e1bd771125020e3cc6ca3c53aee2249f79c798d978147ddc4493ef38f31b28f273bb88927de71e63651e29d771124fbce3cc6ca3c392ee2249f79c798d947846ddc4493ef38f31b28f085bb88927d471e63651e29d771124f68e3cc6ca3c53aee2249cf9c798d9478a75dc44938f37f31b28f156))) (
.fork 18 0x5dc54238f36531b28f133 (
.fork 17 0x5dc54238f31b28f1aa133 (
.leaf 16 0xbb8a8471e63651e346267771508e3cc6ca3c6784ceee2a11c798d9478cf077ddc54238f31b28f19e0d6bb8a8471e63651e32a267771508e3cc6ca3c57c4ceee2a11c798d9478a7099ddc54238f31b28f133128bb8a8471e63651e26624f771508e3cc6ca3c4cc486ee2a11c798d94789988e5dc54238f31b28f133118bb8a8471e63651e26622b771508e3cc6ca3c4cc43eee2a11c798d947899886ddc54238f31b28f1330efbb8a8471e63651e2661c9771508e3cc6ca3c4cc37aee2a11c798d94789986b5dc54238f31b28f1330ccbb8a8471e63651e26614b771508e3cc6ca3c4cc26eee2a11c798d94789984b5dc54238f31b28f13308dbb8a8471e63651e26610b771508e3cc6ca3c4cc1ceee2a11c798d94789982c5dc54238f31b28f13303ebb8a8471e63651e266071771508e3cc6ca3c4cc0c2ee2a11c798d9478998145dc54238f31b28f13300f) (
.leaf 17 0xbb8a8471e6bc63651e267771508e3cd18c6ca3c656ee2a11c798d984147899ddc54238f31b2f028f133bb8a8471e6365c451e4cf771508e3cc6cb88a3c67aee2a11c798d971147899ddc54238f31b2e228f0ccbb8a8471e6365b251e267771508e3cc6cb48a3c736ee2a11c798d969147899ddc54238f31b2c828f133bb8a8471e63656051e3cf771508e3cc6ca3ca004ceee2a11c798d947939899ddc54238f31b28f2671f1bb8a8471e63651e4ce267771508e3cc6ca3c99c3beee2a11c798d9479338725dc54238f31b28f2670d6bb8a8471e63651e4c0267771508e3cc6ca3c96489eee2a11c798d94792c899ddc54238f31b28f249133bb8a8471e63651e3fe267771508e3cc6ca3c7f04ceee2a11c798d9478fc099ddc54238f31b28f1f1133bb8a8471e63651e3e2199771508e3cc6ca3c79c4ceee2a11c798d9478d7099ddc54238f31b28f1aa133)) (
.fork 19 0x5dc54244931b2d228f118 (
.leaf 18 0xbb8a8489263651e4b23cf771509124c6ca3c964486ee2a122498d9478f388c5dc54244931b28f195121bb8a8489263651e2be071771509124c6ca3c53825aee2a122498d94789986f5dc54244931b28f121118bb8a8483c71e63651e061771509058e3cc6ca3c0e2ee2a12041f79c798d947ddc54240838f31b28f267bb8a8481071e63651e33d771509020e3cc6ca3c4ceee2a12041c798d9478725dc54240838f31b28f0ccbb8a8481071e63651e07d771508fd8e3cc6ca3c25aee2a11f79c798d947933ddc5423ef38f31b28f133bb8a847de71e63651e1df771508fbce3cc6ca3c332ee2a11f79c798d94784dddc5423ea38f31b28f133bb8a847b471e63651e267771508eace3cc6ca3c4ceee2a11d49c798d947899ddc54238f37f31b28f13dbb8a8471e6fe63651e267771508e3cdccc6ca3c516ee2a11c79b998d947899ddc54238f36531b28f133) (
.leaf 19 0xbb8a8489271e6363f8051771509124e3cc6c7e0216ee2a12249c798d8f88665dc54244938f31b1e7118bb8a8489271e63635c231771509124e3cc20a3c0c2ee2a12249c797d947842ddc54244938f2f02d228fbb8a8489271e5e051e3ff771509124e3cbc0a3c656ee2a12249c7978147846ddc54244938f2e228f0d6bb8a8489271e5a451e347771509124e3cb48a3c486ee2a12249c794793390b5dc54244938f28f25921fbb8a8489271e51e4923ff771509124e3ca3c7fc6baee2a12249c79478ff8d1ddc54244938f28f1ff121bb8a8489271e51e3fe1ad771509124e3ca3c6a80c2ee2a12249c79478d18caddc54244938f28f1a308dbb8a8489271e51e33c1ad771509124e3ca3c654486ee2a12249bf98d94781c5dc54244937331b28f096bb8a848926ca63651e1bd771509124c6cb48a3c966ee2a122498d9691478caddc54244931b2d228f118)))) (
.fork 23 0x5dc54244938f31b28f0aa (
.fork 21 0x5dc54244938f31b28f024 (
.leaf 20 0xbb8a8489271e63651e047771509124e3cc6ca3c086ee2a12249c798d9478105dc54244938f31b28f01fbb8a8489271e63651e03b771509124e3cc6ca3c06eee2a12249c798d94780d5dc54244938f31b28f019bb8a8489271e63651e031771509124e3cc6ca3c056ee2a12249c798d947808ddc54244938f31b28f00fbb8a8489271e63651e01d771509124e3cc6ca3c036ee2a12249c798d9478065dc54244938f31b28f00bbb8a8489271e63651e015771509124e3cc6ca3c026ee2a12249c798d9478045dc54244938f31b28f007bb8a8489271e63651e00d771509124e3cc6ca3c016ee2a12249c798d9478025dc54244938f31b28f003bb8a8489271e63651e005771509124e3cc6ca3c006ee2a12249c798d9400145dc54244938f31b273085bb8a8489271e6364ce199771509124e3cc6c964462ee2a12249c798d9248d75dc54244938f31b1ff1ae) (
.fork 22 0x5dc54244938f31b28f078 (
.leaf 21 0xbb8a8489271e63651e0ed771509124e3cc6ca3c1ceee2a12249c798d947838ddc54244938f31b28f070bb8a8489271e63651e0df771509124e3cc6ca3c1baee2a12249c798d947836ddc54244938f31b28f06cbb8a8489271e63651e0d3771509124e3cc6ca3c18eee2a12249c798d9478315dc54244938f31b28f05fbb8a8489271e63651e0bd771509124e3cc6ca3c176ee2a12249c798d94782c5dc54244938f31b28f057bb8a8489271e63651e0ab771509124e3cc6ca3c146ee2a12249c798d94781f5dc54244938f31b28f03abb8a8489271e63651e073771509124e3cc6ca3c0e2ee2a12249c798d94781bddc54244938f31b28f036bb8a8489271e63651e061771509124e3cc6ca3c0beee2a12249c798d947816ddc54244938f31b28f02cbb8a8489271e63651e051771509124e3cc6ca3c09eee2a12249c798d947812ddc54244938f31b28f024) (
.leaf 22 0xbb8a8489271e63651e153771509124e3cc6ca3c2a2ee2a12249c798d947852ddc54244938f31b28f0a4bb8a8489271e63651e145771509124e3cc6ca3c27aee2a12249c798d94784dddc54244938f31b28f09abb8a8489271e63651e133771509124e3cc6ca3c25eee2a12249c798d94784b5dc54244938f31b28f095bb8a8489271e63651e127771509124e3cc6ca3c242ee2a12249c798d947846ddc54244938f31b28f08cbb8a8489271e63651e117771509124e3cc6ca3c22aee2a12249c798d947844ddc54244938f31b28f085bb8a8489271e63651e109771509124e3cc6ca3c20eee2a12249c798d9478415dc54244938f31b28f081bb8a8489271e63651e101771509124e3cc6ca3c1feee2a12249c798d94783f5dc54244938f31b28f07cbb8a8489271e63651e0f7771509124e3cc6ca3c1eaee2a12249c798d94783cddc54244938f31b28f078))) (
.fork 25 0x5dc54244938f31b28f11a (
.fork 24 0x5dc54244938f31b28f0de (
.leaf 23 0xbb8a8489271e63651e1bb771509124e3cc6ca3c372ee2a12249c798d94786dddc54244938f31b28f0d8bb8a8489271e63651e1ad771509124e3cc6ca3c356ee2a12249c798d94786a5dc54244938f31b28f0d3bb8a8489271e63651e1a5771509124e3cc6ca3c342ee2a12249c798d9478665dc54244938f31b28f0cbbb8a8489271e63651e195771509124e3cc6ca3c326ee2a12249c798d9478645dc54244938f31b28f0c7bb8a8489271e63651e18d771509124e3cc6ca3c316ee2a12249c798d9478625dc54244938f31b28f0c3bb8a8489271e63651e185771509124e3cc6ca3c306ee2a12249c798d9478605dc54244938f31b28f0bcbb8a8489271e63651e175771509124e3cc6ca3c2e6ee2a12249c798d94785c5dc54244938f31b28f0b5bb8a8489271e63651e163771509124e3cc6ca3c2baee2a12249c798d947856ddc54244938f31b28f0aa) (
.leaf 24 0xbb8a8489271e63651e233771509124e3cc6ca3c462ee2a12249c798d94788bddc54244938f31b28f116bb8a8489271e63651e22b771509124e3cc6ca3c452ee2a12249c798d947888ddc54244938f31b28f110bb8a8489271e63651e21f771509124e3cc6ca3c43aee2a12249c798d947886ddc54244938f31b28f10cbb8a8489271e63651e217771509124e3cc6ca3c42aee2a12249c798d947884ddc54244938f31b28f101bb8a8489271e63651e1fd771509124e3cc6ca3c3f6ee2a12249c798d94787e5dc54244938f31b28f0f9bb8a8489271e63651e1f1771509124e3cc6ca3c3deee2a12249c798d94787b5dc54244938f31b28f0efbb8a8489271e63651e1dd771509124e3cc6ca3c3b2ee2a12249c798d947873ddc54244938f31b28f0e4bb8a8489271e63651e1c7771509124e3cc6ca3c386ee2a12249c798d94786fddc54244938f31b28f0de)) (
.fork 26 0x5dc54244938f31b28f192 (
.leaf 25 0xbb8a8489271e63651e321771509124e3cc6ca3c636ee2a12249c798d9478c45dc54244938f31b28f17abb8a8489271e63651e2e3771509124e3cc6ca3c5beee2a12249c798d9478b6ddc54244938f31b28f16bbb8a8489271e63651e2d3771509124e3cc6ca3c5a2ee2a12249c798d9478b3ddc54244938f31b28f166bb8a8489271e63651e2cb771509124e3cc6ca3c57eee2a12249c798d9478acddc54244938f31b28f156bb8a8489271e63651e29d771509124e3cc6ca3c526ee2a12249c798d9478a2ddc54244938f31b28f13dbb8a8489271e63651e267771509124e3cc6ca3c4a2ee2a12249c798d947893ddc54244938f31b28f126bb8a8489271e63651e249771509124e3cc6ca3c48aee2a12249c798d947890ddc54244938f31b28f120bb8a8489271e63651e23b771509124e3cc6ca3c472ee2a12249c798d94788dddc54244938f31b28f11a) (
.leaf 26 0xbb8a8489271e63651e377771509124e3cc6ca3c6e6ee2a12249c798d9478db5dc54244938f31b28f1b3bb8a8489271e63651e363771509124e3cc6ca3c6c2ee2a12249c798d9478d7ddc54244938f31b28f1aebb8a8489271e63651e35b771509124e3cc6ca3c6b2ee2a12249c798d9478d5ddc54244938f31b28f1aabb8a8489271e63651e353771509124e3cc6ca3c6a2ee2a12249c798d9478d3ddc54244938f31b28f1a6bb8a8489271e63651e347771509124e3cc6ca3c68aee2a12249c798d9478d0ddc54244938f31b28f1a0bb8a8489271e63651e33f771509124e3cc6ca3c67aee2a12249c798d9478ceddc54244938f31b28f19cbb8a8489271e63651e335771509124e3cc6ca3c666ee2a12249c798d9478cc5dc54244938f31b28f196bb8a8489271e63651e32b771509124e3cc6ca3c652ee2a12249c798d9478c9ddc54244938f31b28f192)))))) (
.fork 41 0x5dc54252038f31b2e228f (
.fork 34 0x5dc54244938f37331b28f (
.fork 30 0x5dc54244938f31b28f278 (
.fork 28 0x5dc54244938f31b28f200 (
.leaf 27 0xbb8a8489271e63651e3ff771509124e3cc6ca3c7faee2a12249c798d9478feddc54244938f31b28f1fcbb8a8489271e63651e3f7771509124e3cc6ca3c7eaee2a12249c798d9478fcddc54244938f31b28f1f8bb8a8489271e63651e3ef771509124e3cc6ca3c7daee2a12249c798d9478fa5dc54244938f31b28f1f2bb8a8489271e63651e3e3771509124e3cc6ca3c7c2ee2a12249c798d9478f7ddc54244938f31b28f1eebb8a8489271e63651e3d7771509124e3cc6ca3c7aaee2a12249c798d9478f45dc54244938f31b28f1e7bb8a8489271e63651e3cd771509124e3cc6ca3c796ee2a12249c798d9478f25dc54244938f31b28f1e2bb8a8489271e63651e3bb771509124e3cc6ca3c75aee2a12249c798d9478e6ddc54244938f31b28f1c2bb8a8489271e63651e383771509124e3cc6ca3c702ee2a12249c798d9478df5dc54244938f31b28f1bd) (
.fork 29 0x5dc54244938f31b28f250 (
.leaf 28 0xbb8a8489271e63651e49f771509124e3cc6ca3c93aee2a12249c798d947926ddc54244938f31b28f24cbb8a8489271e63651e497771509124e3cc6ca3c92aee2a12249c798d947924ddc54244938f31b28f248bb8a8489271e63651e48f771509124e3cc6ca3c91aee2a12249c798d947922ddc54244938f31b28f23fbb8a8489271e63651e47d771509124e3cc6ca3c8f2ee2a12249c798d94791d5dc54244938f31b28f235bb8a8489271e63651e461771509124e3cc6ca3c89eee2a12249c798d94790fddc54244938f31b28f21bbb8a8489271e63651e433771509124e3cc6ca3c85aee2a12249c798d947908ddc54244938f31b28f20ebb8a8489271e63651e417771509124e3cc6ca3c822ee2a12249c798d947903ddc54244938f31b28f205bb8a8489271e63651e409771509124e3cc6ca3c80aee2a12249c798d947900ddc54244938f31b28f200) (
.leaf 29 0xbb8a8489271e63651e4ef771509124e3cc6ca3c9d6ee2a12249c798d94793a5dc54244938f31b28f273bb8a8489271e63651e4e5771509124e3cc6ca3c9c6ee2a12249c798d9479385dc54244938f31b28f26ebb8a8489271e63651e4db771509124e3cc6ca3c9b2ee2a12249c798d947935ddc54244938f31b28f26abb8a8489271e63651e4d3771509124e3cc6ca3c9a2ee2a12249c798d947933ddc54244938f31b28f266bb8a8489271e63651e4c9771509124e3cc6ca3c98eee2a12249c798d9479315dc54244938f31b28f261bb8a8489271e63651e4c1771509124e3cc6ca3c97eee2a12249c798d94792f5dc54244938f31b28f25cbb8a8489271e63651e4b7771509124e3cc6ca3c96aee2a12249c798d94792cddc54244938f31b28f258bb8a8489271e63651e4af771509124e3cc6ca3c956ee2a12249c798d947928ddc54244938f31b28f250))) (
.fork 32 0x5dc54244938f31b2ea28f (
.fork 31 0x5dc54244938f31b2a528f (
.leaf 30 0xbb8a8489271e63654851f771509124e3cc6ca8ca3eee2a12249c798d951147ddc54244938f31b2a128fbb8a8489271e63654051f771509124e3cc6ca78a3eee2a12249c798d94e947ddc54244938f31b29c28fbb8a8489271e63653451f771509124e3cc6ca64a3eee2a12249c798d94b947ddc54244938f31b29528fbb8a8489271e63652651f771509124e3cc6ca48a3eee2a12249c798d948947ddc54244938f31b29028fbb8a8489271e63651e515771509124e3cc6ca3ca26ee2a12249c798d9479445dc54244938f31b28f287bb8a8489271e63651e50b771509124e3cc6ca3ca12ee2a12249c798d947941ddc54244938f31b28f282bb8a8489271e63651e503771509124e3cc6ca3ca02ee2a12249c798d94793f5dc54244938f31b28f27dbb8a8489271e63651e4f9771509124e3cc6ca3c9eaee2a12249c798d94793cddc54244938f31b28f278) (
.leaf 31 0xbb8a8489271e6365d051f771509124e3cc6cb98a3eee2a12249c798d972947ddc54244938f31b2e428fbb8a8489271e6365c651f771509124e3cc6cb88a3eee2a12249c798d970947ddc54244938f31b2e028fbb8a8489271e6365be51f771509124e3cc6cb74a3eee2a12249c798d96d147ddc54244938f31b2d928fbb8a8489271e6365b051f771509124e3cc6cb5ca3eee2a12249c798d96a947ddc54244938f31b2d428fbb8a8489271e6365a651f771509124e3cc6cb48a3eee2a12249c798d9690e15dc54244938f31b2d128fbb8a8489271e6365a051f771509124e3cc6cb38a3eee2a12249c798d965147ddc54244938f31b2c928fbb8a8489271e63659051f771509124e3cc6cb1ca3eee2a12249c798d962147ddc54244938f31b2bb28fbb8a8489271e63656051f771509124e3cc6caa0a3eee2a12249c798d953947ddc54244938f31b2a528f)) (
.fork 33 0x5dc54244938f32731b28f (
.leaf 32 0xbb8a8489271e64c63651f771509124e3cc94c6ca3eee2a12249c799198d947ddc54244938f31f31b28fbb8a8489271e63c63651f771509124e3cc74c6ca3eee2a12249c798e18d947ddc54244938f31b31428fbb8a8489271e63662651f771509124e3cc6cc44a3eee2a12249c798d988147ddc54244938f31b30d28fbb8a8489271e63661851f771509124e3cc6cc2ca3eee2a12249c798d985147ddc54244938f31b30928fbb8a8489271e63661051f771509124e3cc6cc18a3eee2a12249c798d980147ddc54244938f31b2ff28fbb8a8489271e6365f651f771509124e3cc6cbe4a3eee2a12249c798d97c147ddc54244938f31b2f628fbb8a8489271e6365e451f771509124e3cc6cbc4a3eee2a12249c798d978147ddc54244938f31b2ef28fbb8a8489271e6365dc51f771509124e3cc6cbb4a3eee2a12249c798d975947ddc54244938f31b2ea28f) (
.leaf 33 0xbb8a8489271e6e463651f771509124e3cdbcc6ca3eee2a12249c79b618d947ddc54244938f36b31b28fbb8a8489271e6d463651f771509124e3cda4c6ca3eee2a12249c79b418d947ddc54244938f36731b28fbb8a8489271e6cc63651f771509124e3cd94c6ca3eee2a12249c79b218d947ddc54244938f36231b28fbb8a8489271e6bc63651f771509124e3cd74c6ca3eee2a12249c79ad98d947ddc54244938f35831b28fbb8a8489271e6aa63651f771509124e3cd40c6ca3eee2a12249c79a318d947ddc54244938f34031b28fbb8a8489271e67e63651f771509124e3ccf4c6ca3eee2a12249c799e18d947ddc54244938f33b31b28fbb8a8489271e67263651f771509124e3cce0c6ca3eee2a12249c799c147842ddc54244938f33731b28fbb8a8489271e66663651f771509124e3ccc4c6ca3eee2a12249c799718d947ddc54244938f32731b28f)))) (
.fork 37 0x5dc54244941e38f31b28f (
.fork 35 0x5dc5424493b138f31b28f (
.leaf 34 0xbb8a8489276071e63651f771509124eb4e3cc6ca3eee2a12249d59c798d947ddc5424493a938f31b28fbb8a8489274e71e63651f771509124e90e3cc6ca3eee2a12249d11c798d947ddc54244939f38f31b28fbb8a8489273c71e63651f771509124e6ce3cc6ca3eee2a12249cb9c798d947ddc54244939538f31b28fbb8a8489272671e63651f771509124e3ce20c6ca3eee2a12249c79c398d947ddc54244938f38631b28fbb8a8489271e70a63651f771509124e3ce10c6ca3eee2a12249c79c198d947ddc54244938f38231b28fbb8a8489271e70263651f771509124e3ce00c6ca3eee2a12249c79bf98d947ddc54244938f37d31b28fbb8a8489271e6f863651f771509124e3cde8c6ca3eee2a12249c79bc98d947ddc54244938f37831b28fbb8a8489271e6ee63651f771509124e3cdd8c6ca3eee2a12249c79ba18d947ddc54244938f37331b28f) (
.fork 36 0x5dc5424493da38f31b259 (
.leaf 35 0xbb8a848927b471e6363cf771509124f68e3cc6c6baee2a12249ed18d94792cddc5424493da31b28f118bb8a848927b271e6365a5771509124f64e3cc6ca3eee2a12249ec1c798d947ddc5424493d738f31b28fbb8a848927aa71e63651f771509124f50e3cc6ca3eee2a12249e99c798d947ddc5424493d138f31b28fbb8a848927a071e63651f771509124f34e3cc6ca3eee2a12249e59c798d947ddc5424493ca38f31b28fbb8a8489278c71e63651f771509124f14e3cc6ca3eee2a12249e21c798d947ddc5424493c338f31b28fbb8a8489278471e63651f771509124f04e3cc6ca3eee2a12249e01c798d947ddc5424493bf38f31b28fbb8a8489277c71e63651f771509124ef4e3cc6ca3eee2a12249dd9c798d947ddc5424493ba38f31b28fbb8a8489277071e63651f771509124edce3cc6ca3eee2a12249d99c798d947ddc5424493b138f31b28f) (
.leaf 36 0xbb8a8489282c71e63651f771509125040e3cc6ca3eee2a1224a041c798d947ddc54244940638f31b28fbb8a8489280871e63651f771509125000e3cc6ca3eee2a12249fd1c798d947ddc5424493f838f31b28fbb8a848927ec71e63651f771509124fc4e3cc6ca3eee2a12249f81c798d947ddc5424493ef38f31b28fbb8a848927dc71e63651f771509124fa8e3cc6ca3eee2a12249f51c7969147ddc5424493ea38f28f1ffbb8a848927d471e51e32b771509124fa8c6cb48a3eee2a12249f518d947890ddc5424493e938f31b28fbb8a848927d271e51e4b3771509124fa0e3cc6ca3eee2a12249f39c798d947ddc5424493e538f31b28fbb8a848927c671e63651f771509124f88e3cc6ca3eee2a12249ef9c798d947ddc5424493de38f31b28fbb8a848927ba71e63651f771509124f6ce3cc6ca3eee2a12249ed1c798d947ddc5424493da38f31b259))) (
.fork 39 0x5dc5424ee44938f31b28f (
.fork 38 0x5dc54249844938f31b28f (
.leaf 37 0xbb8a8492489271e63651f771509248e3cc6ca3c656ee2a1248a249c798d947ddc54248f44938f31b28fbb8a8491689271e63651f771509221124e3cc6ca3eee2a12422249c798d947ddc54248244938f31b28fbb8a8490289271e63651f771509201124e3cc6ca3eee2a123fa249c798d947ddc54247d44938f31b28fbb8a848ec89271e63651f7715091c5124e3cc6ca3eee2a12389c798d94784b5dc54247044938f31b28fbb8a848d889271e63651f7715091a9124e3cc6ca3eee2a1233a249c798d947ddc54245d44938f31b28fbb8a848b889271e63651f771509170e3cc6ca3c0e2ee2a122d2249c798d947ddc54245a38f31b28f030bb8a848ae89271e63651f7715091250f8e3cc6ca3eee2a1224a1c1c798d947ddc54244943238f31b28fbb8a8489285e71e63651f7715091250a8e3cc6ca3eee2a1224a111c798d947ddc54244941e38f31b28f) (
.leaf 38 0xbb8a849dc89271e51e4cf7715093b5124e3cc6ca3eee2a1275a249c798d947ddc5424e644938f31b28fbb8a849c889271e63651f771509381124e3cc6ca3eee2a126da249c798d947ddc5424d544938f31b28fbb8a849aa71e6365a451f77150933d124e3cc6ca3eee2a1267a249c798d933ddc5424cf44938f31b1f1bb8a8499e71e63651e4cf77150933ce3cc6ca3c4ceee2a12679c798d9478665dc5424ce44938f31b28fbb8a8499a89271e63651f77150932d124e3cc6ca3eee2a1263a249c798d947ddc5424c544938f31b28fbb8a8498289271e63651f7715092f1124e3cc6ca3eee2a125b2249c798d947ddc5424b638f31b28f259bb8a8496289271e63651f771509295124e3cc6ca3eee2a12529c798d9478f3ddc5424a444938f31b28fbb8a8494489271e63651f771509279124e3cc6ca3eee2a124da249c798d947ddc54249844938f31b28f)) (
.fork 40 0x5dc54252038f31b28f0b9 (
.leaf 39 0xbb8a84a4071e63651e171771509480e3cc6ca3c2c6ee2a12901c798d947852ddc54252038f31b28f09bbb8a84a4071e63651e12d771509480e3cc6ca3c236ee2a12901c798d947842ddc54252038f31b28f058bb8a84a4071e63651e0af771509480e3cc6ca3c0faee2a12901c798d94781c5dc54252038f31b28f030bb8a84a4071e63651e051771509480e3cc6ca3c006ee2a1288a249c798d947ddc54251138f37f31b28fbb8a84a1689271e63651f771509401124e3cc6ca3eee2a127d2249c798d947ddc5424fa38f37331b28fbb8a849ec89271e63651f7715093c9124e3cc6ca3eee2a1277a249c798d947ddc5424ef44938f2e228fbb8a849de89271e51e3ff7715093bd124e3ca3c67aee2a1277a041c798d947ddc5424ef38f31b2e228fbb8a849de71e63651e2677715093bce3cc6ca3c3beee2a12779c798d94786b5dc5424ee44938f31b28f) (
.leaf 40 0xbb8a84a4071e6365a451f771509480e3cc6ca3ca02ee2a12901c798d947939ddc54252038f31b28f271bb8a84a4071e63651e4cf771509480e3cc6ca3c966ee2a12901c798d947924ddc54252038f31b28f202bb8a84a4071e63651e3ff771509480e3cc6ca3c7f2ee2a12901c798d9478fc5dc54252038f31b28f1f1bb8a84a4071e63651e3cf771509480e3cc6ca3c6c6ee2a12901c798d9478d75dc54252038f31b28f1aabb8a84a4071e63651e347771509480e3cc6ca3c67aee2a12901c798d9478caddc54252038f31b28f15fbb8a84a4071e63651e29d771509480e3cc6ca3c4ceee2a12901c798d947890ddc54252038f31b28f118bb8a84a4071e63651e1df771509480e3cc6ca3c392ee2a12901c798d94786f5dc54252038f31b28f0d6bb8a84a4071e63651e199771509480e3cc6ca3c2f2ee2a12901c798d94785d5dc54252038f31b28f0b9))))) (
.fork 48 0x6355dc54244938f31b28f (
.fork 44 0x5dc5b254244938f31b28f (
.fork 42 0x5dc55054244938f31b28f (
.leaf 41 0xbb8a9ca8489271e63651f771531509124e3cc6ca3eee2a129c2249c798d947ddc54253444938f31b28fbb8a84a6689271e63651f7715094c5124e3cc6ca3eee2a12962249c798d947ddc54252944938f31b28fbb8a84a4e89271e63651f771509495124e3cc6ca3eee2a1291a249c798d947ddc54252252038f31b28fbb8a84a4489271e63651f771509488e3cc6ca3c4ceee2a12902801c798d947ddc5425204f238f31b28fbb8a84a409de71e63651f77150948133ce3cc6ca3eee2a12902249c798d947ddc54252044936531b28fbb8a84a4089263651e267771509481020e3cc6ca3eee2a12901f79c798d947ddc5425203ea38f31b28fbb8a84a407b471e63651f771509480e3cdfcc6ca3eee2a12901c79b998d947ddc54252038f36531b28fbb8a84a4071e63661051f771509480e3cc6cbc0a3eee2a12901c798d977147ddc54252038f31b2e228f) (
.fork 43 0x5dc59154244938f31b28f (
.leaf 42 0xbb8b1ea8489271e63651f771625509124e3cc6ca3eee2c4a249c798d94792cddc58654244938f31b28fbb8b00a8489271e63651f771601124e3cc6ca3c79eee2bfaa12249c798d947ddc57d54244938f31b28fbb8af6a8489271e63651f7715e9509124e3cc6ca3eee2bb2a12249c798d947ddc57554244938f31b28fbb8aea89271e63651e3557715cd509124e3cc6ca3eee2b92a12249c798d947ddc56e54244938f31b28fbb8adc89271e63651e32b7715a5509124e3cc6ca3eee2b42a12249c798d947ddc56854238f31b28f133bb8acea8489271e63651f771595509124e3cc6ca3eee2b12a12249c798d947ddc55f54244938f31b28fbb8abe89271e63651e1bd771579509124e3cc6ca3eee2ae2a12249c798d947ddc55b54244938f31b28fbb8ab2a8489271e63651f771545509124e3cc6ca3eee2a8a249c798d94781c5dc55054244938f31b28f) (
.leaf 43 0xbb8b5ea8489271e63651f7716a5509124e3cc6ca3eee2d4a249c79b298d947ddc5a654252038f31b28fbb8b4ca8489271e63651f771699509124e3cbc0a3eee2d32a12249c79478d1ddc5a654238f31b28f133bb8b4c89271e6365e051f771699124e3cc6ca3c53aee2d32249c798d947846ddc5a554244938f31b28fbb8b48a8489271e63651f77168d509124e3cc6ca3eee2d12a12249c798d947ddc5a154244938f31b28fbb8b3aa8489271e63651f771675124e3cc6cb48a3eee2ccaa12901c798d947ddc59954244938f31b28fbb8b32a8489271e6364e7771665509124e3cc6c7e2ee2ccaa12001c798d947ddc59954238f31b28f133bb8b32a8471e63651e1d9771665124e3cc6ca3c9ceee2cca249c798d9478a75dc59944938f31b28f085bb8b30a8489271e63651f77165d509124e3cc6ca3eee2caaa12249c798d947ddc59154244938f31b28f))) (
.fork 46 0x5dc5c052244938f31b28f (
.fork 45 0x5dc5c044938f31b28f1a3 (
.leaf 44 0xbb8b8089271e63651e33d771701124e3cc6ca3c656ee2e02249c798d9478afddc5c044938f31b28f14ebb8b8089271e63651e267771701124e3cc6ca3c486ee2e02249c798d94788c5dc5c044938f31b28f101bb8b8089271e63651e1df771701124e3cc6ca3c392ee2e02249c798d94786f5dc5c044938f31b28f0d6bb8b8089271e63651e199771701124e3cc6ca3c296ee2e02249c798d94784dddc5c044938f31b28f096bb8b8089271e63651e11b771701124e3cc6ca3c216ee2e02249c798d94783b5dc5c044938f31b28f073bb8b8089271e63651e0e3771701124e3cc6ca3c1c2ee2e02249c798d947834ddc5c044938f31b28f058bb8b8089271e63651e07d771701124e3cc6ca3c0e2ee2e02249c798d9478185dc5c044938f31b28f028bb8b8089271e63651e0037716cd509124e3cc6ca3eee2d9a249c79bf98d947ddc5b254244938f31b28f) (
.leaf 45 0xbb8b80a4089271e63651f7717013bd124e3cc6ca3eee2e0267a249c798d947ddc5c044940838f31b28fbb8b8089280c71e63651f771701124fbce3cc6ca3eee2e02249f51c798d947ddc5c04493da38f31b28fbb8b8089271e6fe63651f771701124e3cdccc6ca3eee2e02249c79b298d947ddc5c044938f31b30828fbb8b8089271e63660051f771701124e3cc6cbc0a3eee2e02249c798d971147ddc5c044938f31b2d228fbb8b8089271e63651e501771701124e3cc6ca3c9f6ee2e02249c798d947939ddc5c044938f31b28f267bb8b8089271e63651e4b3771701124e3cc6ca3c926ee2e02249c798d947902ddc5c044938f31b28f1ffbb8b8089271e63651e3f9771701124e3cc6ca3c7e2ee2e02249c798d9478f8ddc5c044938f31b28f1e7bb8b8089271e63651e35d771701124e3cc6ca3c6aaee2e02249c798d9478d3ddc5c044938f31b28f1a3)) (
.fork 47 0x5ed5dc54244938f31b28f (
.leaf 46 0xbdaa8489271e63651e12d7b1771509124e3cc6ca3ef52ee2a12249c798d947de85dc54244938f31b28fbb8ba2a8489271e63651f771741509124e3cc6ca3eee2e72a12249c798d947ddc5ca5c044938f31b28fbb8b94a84a4071e63651f771729509124e3cc6ca3eee2e52a11f79c798d947ddc5ca54238f31b28f133bb8b94a8471e63651e1c9771729124fbce3cc6ca3eee2e52249c798d9478a75dc5ca44938f31b28f09bbb8b92a8489271e63651f771721509124e3cc6ca3eee2e22a12249c798d947ddc5c35c044938f31b28fbb8b86a8489271e63651f7717016bd124e3cc6ca3eee2e02d32249c798d947ddc5c059944938f31b28fbb8b80a84a4071e63651f771701509124e3cc6ca3eee2e02a12249c7980147ddc5c054244938f28f1a7bb8b80a848926e663651f771701509124c6ca3c53aee2e02a11c798d947899ddc5c052244938f31b28f) (
.leaf 47 0xc64bb8a8489271e63651f8c9509124e3cc6ca3c9cf18aee2a12249c798d947e2b5dc54244938f31b28fc56a8489271e63651e4b38a1771509124e3cc6ca3f112ee2a12249c798d947e2254244938f31b28f1e7c42bb8a8489271e63651f87d771509124e3cc6ca3f0eaee2a12249c798d947e195dc54244938f31b28fc30bb8a8489271e63651f861509124e3cc6ca3c68f0b2ee2a12249c798d947e125dc54244938f31b28fc24a8489271e63651e32b839771509124e3cc6ca3f072ee2249c798d9478a760d5dc54244938f31b28fc16bb8a8489271e63651f82d771508e3cc6ca3c4cf052ee2a12249c798d947e015dc54244938f31b28fc02a8489271e63651e1c97fd771509124e3cc6ca3effaa12249c798d94786f5fd5dc54244938f31b28fbfaa8489271e63651e1ad7e9771509124e3cc6ca3efd2a12249c798d9478665ed5dc54244938f31b28f)))) (
.fork 51 0x65954244943238f31b28f (
.fork 49 0x6435dc54244938f31b28f (
.leaf 48 0xc86bb8a8489271e61051f90d771509124e3ca3c6ab21aee2a11c798d947899e435dc44938f31b28f14ec86a8489281071e63651f90d509124e3cc6cc20a3f21aa12249c798d9478afe4354244938f31b28f03ec86a8489271e63651e061909771509124e3cc6ca3f20aee2a12249c798d947e405dc54244938f31b28fc76bb8a8489271e63651f8ed509124e3cc6cb48a3f1baee2e02249c798d947e375dc54252038f31b28fc6ebb8a8489271e63651f8dd771509124e3cc6ca031baee2a12249c798d8fe6375dc54242a38f31b28fc6ebb8a8471e63651e2678dd771508e3cc6ca3c3db1baee2962249c798d947e375dc44938f31b28f14ec6ebb889271e63651e1518dd509125020e3cc6ca3f1baa12249c798d94794063754244938f31b28f15fc6ea8489271e63651e14b8dd509124e3cc6ca3c0fb1baa12249c798d9478146355dc54244938f31b28f) (
.fork 50 0x65954244938f31b28f14e (
.leaf 49 0xcb2a8489271e63651e267965509124e3cc6ca3c4872caa12249c798d94788c65954244938f31b28f0f8cb2a8489271e63651e1df965509124e3cc6ca3c3932caa12249c798d94786f65954244938f31b28f0d6cb2a8489271e63651e199965509124e3cc6ca3c2d72caa12249c798d947852e5954244938f31b28f09bcb2a8489271e63651e12d965509124e3cc6ca3c2372caa12249c798d947842e5954244938f31b28f058cb2a8489271e63651e07d965509124e3cc6ca3c0e32caa12249c798d94781865954244938f31b28f028cb2a8489271e63651e02b965509124e3cc6ca3c0472caa12249c798d947807e5954244938f31b28f00ecb2a8489271e63651e00392d771509124e3cc6ca3f25aa12249c79b998d947e455dc54244938f31b28fc8aa8489271e6ca63651f90d771701124e3cc6ca3f21aee2a12901c798d947e435dc54244938f31b28f) (
.leaf 50 0xcb2a8489281071e63651f965509124fbce3cc6ca3f2caa12249f51c798d947e595424493da38f31b28fcb2a8489271e6fe63651f965509124e3cdccc6ca3f2caa12249c79b298d947e5954244938f31b31128fcb2a8489271e63661051f965509124e3cc6cbc0a3f2caa12249c798d971147e5954244938f31b2d228fcb2a8489271e63651e511965509124e3cc6ca3ca032caa12249c798d947939e5954244938f31b28f267cb2a8489271e63651e4b3965509124e3cc6ca3c9272caa12249c798d94790465954244938f31b28f1ffcb2a8489271e63651e3f9965509124e3cc6ca3c7e32caa12249c798d9478f8e5954244938f31b28f1e7cb2a8489271e63651e35d965509124e3cc6ca3c6af2caa12249c798d9478d565954244938f31b28f1a3cb2a8489271e63651e33d965509124e3cc6ca3c6572caa12249c798d9478afe5954244938f31b28f14e))) (
.fork 53 0x66c54244938f31b28f15f (
.fork 52 0x66265954244938f31b28f (
.leaf 51 0xcc4bb8b8089271e63651f989771509480e3cc6ca3f312ee2a12249c798d947e625dc54240838f31b28fcc4bb8a8471e63651e267989771508e3cc6ca3c3bf312ee2249c798d9478a766254244940838f31b28fcc4a8489271e63651e2bf989509124e3cc6ca3c0fb30aee2a12249c798d947e6065954244938f31b28fcc0bb8a8489271e63651f96590d509124e3cc6ca3f2cb1baa12249c798d947e595dc5c044938f31b28fcb2bb8a84a4071e63651f965771509124e3cc6ca3f2caee2a12249bf98d947e595dc54244931b28f15fcb2bb8a8471e63651e267965771124e3cc6ca3c53b2cae52a12249c798d947e595c054244938f31b28fcb2b4ca8489271e63651f965665509124e3cc6ca3f2caa1299a249c798d947e5954252244938f31b28fcb2a84a4089271e63651f9655093bd124e3cc6ca3f2caa1267a249c798d947e5954244943238f31b28f) (
.leaf 52 0xcd8a8489271e63651e0c59b1509124e3cc6ca3c0fb352ee2a12249c798d947e695dc54244938f31b28fcd0bb8a8489271e63651f99d965509124e3cc6ca3f33b1baa12249c798d947e675dc5c044938f31b28fccebb8a84a4071e63651f99d771509124e3cc6ca3f33aee2a121c1c798d947e675dc54238f31b28f133ccebb8a8471e63651e1f399d771489124e3cc6ca3f33aee2249c798d978147e675dc44938f31b28f14eccebb889271e63651e14b99d771124e3cc6ca3c23733aa12912249c798d947e6754244940838f31b28fccea8489271e63661051f99d509124e3cc6ca3c7f333aa12249c798d9478afe6754244938f31b28f058ccea8489271e63651e07d99d509124e3cc6ca3c0c332b2caa12249c798d947e655dc54252038f31b28fccabb8a8489271e63651f991771509124e3cc6ca3f31aee2a12249c798d947e6265954244938f31b28f)) (
.fork 54 0x6705dc54252038f31b28f (
.leaf 53 0xce0bb8a8489271e63651f9bd771509480e3cc6ca3f37aee2a12249c798d947e6e5dc54244938f31b28fcdabb8a8489271e63651f9b1965509124e3cc6ca3f362ee2e02249c798d947e6c5dc54252038f31b28fcd8bb8a849de89271e51f9b1771509124fa8e3ca3f362ee2a12249ed1c798de6c5dc54244938f31b28fcd8bb8a8489271e6364939b1771509124e3cc6c7ff362ee2a12249c798d88c66c5dc54244938f2f028fcd8bb8a8489271e51e4939b1771509124e3ca3c6bb362ee2a12249c79478d1e6c5dc54244938f28f121cd8bb8a8489271e51e1ad9b1771509124e20c6ca3f362ee2a122498d9478b3e6c5dc54243e38f31b28fcd8bb8a8471e63651e2679b1771508e3cc6ca3c3f3362ee29c2249c798d947e6c5dc44938f31b28f14ecd8bb889271e63651e15b9b1745509124e3cc6ca3f362a1224a041c798d947e6c54244938f31b28f15f) (
.leaf 54 0x67765954244938f31b28fceebb8b8089271e63651f9dd771509124e3cc6ca3f3b32caa12249c798d947e765dc54244938f31b28fce8bb8a8489271e63651f9cd771701124e3cc6ca3f39aee2a12901c798d947e735dc54244938f31b28fce4bb8b8089271e63651f9c9771509124e3cc6ca3f38aee2a12249c798d947e705dc54252038f31b28f))))))⟩

set_option maxRecDepth 16000 in
def bank7 : PackedSeq := ⟨68, 83, 0x7ffffffffffffffffffff, .fork 1 0x5dc54244938f31b28f1ae (
.leaf 0 0xbb8a8489271e63651e355771509124e3cc6ca3c68eee2a12249c798d9478cf5dc54244938f31b28f195bb8a8489271e63651e2bf771509124e3cc6ca3c53aee2a12249c798d947899ddc54244938f31b28f121bb8a8489271e63651e231771509124e3cc6ca3c3beee2a12249c798d9478725dc54244938f31b28f0debb8a8489271e63651e1ad771509124e3cc6ca3c332ee2a12249c798d947852ddc54244938f31b28f09bbb8a8489271e63651e12d771509124e3cc6ca3c236ee2a12249c798d947842ddc54244938f31b28f058bb8a8489271e63651e07d771509124e3cc6ca3c0e2ee2a12249c798d9478185dc54244938f31b28f028000cb2a8489271e63651e001771701124e3cc6ca3c002ee2a12901c798d9478005dc54238f31b28f133000bb889271e63651e29c001509125020e3cc6ca3c002a12249c798d9478af80054244938f31b28f03e) (
.fork 2 0x6595dc54244938f31b28f (
.leaf 1 0xc86bb8a8489271e63651f8dd771509124e3cc6ca3eee2e52a12249c798d947ddc5c054244938f31b28fbb8b4ca8489271e63651f771665509124e3cc6ca3eee2a12912249c798d947ddc54252044938f31b28fbb8a849de89271e63651f77150933d124e3cc6ca3eee2a1224a041c798d947ddc5424493ef38f31b28fbb8a848927d471e63651f771509124f68e3cc6ca3eee2a12249c79bf98d947ddc54244938f37331b28fbb8a8489271e6ca63651f771509124e3cc6cc20a3eee2a12249c798d978147ddc54244938f31b2e228fbb8a8489271e6365a451f771509124e3cc6ca3ca02ee2a12249c798d947939ddc54244938f31b28f267bb8a8489271e63651e4b3771509124e3cc6ca3c926ee2a12249c798d9478ffddc54244938f31b28f1fcbb8a8489271e63651e3f1771509124e3cc6ca3c7c6ee2a12249c798d9478f3ddc54244938f31b28f1ae) (
.leaf 2 0xcd8bb8a8489271e63651f99d771509124e3cc6ca3f312ee2a12249c798d947e595dc54244938f31b28f))⟩

set_option maxRecDepth 16000 in
def bank8 : PackedSeq := ⟨1, 71, 0x7fffffffffffffffff, .leaf 0 0x5dc54244938f31b28f⟩

def buckets (t : ℕ) : PackedSeq :=
  if t = 2 then bank2 else
  if t = 3 then bank3 else
  if t = 4 then bank4 else
  if t = 5 then bank5 else
  if t = 6 then bank6 else
  if t = 7 then bank7 else
  if t = 8 then bank8 else
  ⟨0, 0, 0, .leaf 0 0⟩

theorem bound_from_closure (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    (root : rootClosed table 8 inputs = true)
    (sample : ∀ k : Fin 270, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 270) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rootClosed_sound table closure ht 8 inputs nd root (lift low run)

def table := tableFrom dict buckets

theorem tableClosure
    (h2 : blockCheck dict buckets 2 0 4 = true)
    (h3 : blockCheck dict buckets 3 0 14 = true)
    (h4 : blockCheck dict buckets 4 0 160 = true)
    (h5 : blockCheck dict buckets 5 0 2484 = true)
    (h6 : blockCheck dict buckets 6 0 1741 = true)
    (h7 : blockCheck dict buckets 7 0 68 = true)
    (h8 : blockCheck dict buckets 8 0 1 = true)
    : ∀ t ws, table t ws = true → closedState table t ws = true := by
  intro t ws belongs
  obtain ⟨i,key,hk,rfl⟩ := tableFrom_sound _ _ _ _ belongs
  have ih := PackedSeq.at_bound hk
  have ready : blockCheck dict buckets t 0 (buckets t).size = true := by
    have ready2 : t = 2 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h2
    have ready3 : t = 3 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h3
    have ready4 : t = 4 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h4
    have ready5 : t = 5 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h5
    have ready6 : t = 6 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h6
    have ready7 : t = 7 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h7
    have ready8 : t = 8 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h8
    by_cases eq2 : t=2
    · exact ready2 eq2
    by_cases eq3 : t=3
    · exact ready3 eq3
    by_cases eq4 : t=4
    · exact ready4 eq4
    by_cases eq5 : t=5
    · exact ready5 eq5
    by_cases eq6 : t=6
    · exact ready6 eq6
    by_cases eq7 : t=7
    · exact ready7 eq7
    by_cases eq8 : t=8
    · exact ready8 eq8
    have empty : buckets t = ⟨0, 0, 0, .leaf 0 0⟩ := by simp [buckets,eq2,eq3,eq4,eq5,eq6,eq7,eq8]
    simp [empty,blockCheck]
  exact blockCheck_sound _ _ ready (Nat.zero_le _) (by simpa using ih) hk

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem sampleOK : ∀ k : Fin 270, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem joinChecks (t s a b : ℕ)
    (left : blockCheck dict buckets t s a = true)
    (right : blockCheck dict buckets t (s+a) b = true) :
    blockCheck dict buckets t s (a+b) = true := by
  unfold blockCheck at *
  apply List.all_eq_true.mpr
  intro i hi
  have bound := List.mem_range.mp hi
  by_cases cut : i < a
  · exact List.all_eq_true.mp left i (List.mem_range.mpr cut)
  · have upper : i-a < b := by omega
    have back : s+a+(i-a) = s+i := by omega
    simpa only [back] using List.all_eq_true.mp right (i-a) (List.mem_range.mpr upper)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held2Part0 : blockCheck dict buckets 2 0 4 = true := by
  decide +kernel

theorem held2 : blockCheck dict buckets 2 0 4 = true :=
  held2Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held3Part0 : blockCheck dict buckets 3 0 14 = true := by
  decide +kernel

theorem held3 : blockCheck dict buckets 3 0 14 = true :=
  held3Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part0 : blockCheck dict buckets 4 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part32 : blockCheck dict buckets 4 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part64 : blockCheck dict buckets 4 64 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part96 : blockCheck dict buckets 4 96 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part128 : blockCheck dict buckets 4 128 32 = true := by
  decide +kernel

theorem held4 : blockCheck dict buckets 4 0 160 = true :=
  (joinChecks 4 0 64 96 (joinChecks 4 0 32 32 held4Part0 held4Part32) (joinChecks 4 64 32 64 held4Part64 (joinChecks 4 96 32 32 held4Part96 held4Part128)))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part0 : blockCheck dict buckets 5 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part32 : blockCheck dict buckets 5 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part64 : blockCheck dict buckets 5 64 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part96 : blockCheck dict buckets 5 96 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part128 : blockCheck dict buckets 5 128 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part160 : blockCheck dict buckets 5 160 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part192 : blockCheck dict buckets 5 192 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part224 : blockCheck dict buckets 5 224 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part256 : blockCheck dict buckets 5 256 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part288 : blockCheck dict buckets 5 288 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part320 : blockCheck dict buckets 5 320 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part352 : blockCheck dict buckets 5 352 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part384 : blockCheck dict buckets 5 384 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part416 : blockCheck dict buckets 5 416 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part448 : blockCheck dict buckets 5 448 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part480 : blockCheck dict buckets 5 480 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part512 : blockCheck dict buckets 5 512 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part544 : blockCheck dict buckets 5 544 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part576 : blockCheck dict buckets 5 576 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part608 : blockCheck dict buckets 5 608 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part640 : blockCheck dict buckets 5 640 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part672 : blockCheck dict buckets 5 672 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part704 : blockCheck dict buckets 5 704 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part736 : blockCheck dict buckets 5 736 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part768 : blockCheck dict buckets 5 768 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part800 : blockCheck dict buckets 5 800 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part832 : blockCheck dict buckets 5 832 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part864 : blockCheck dict buckets 5 864 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part896 : blockCheck dict buckets 5 896 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part928 : blockCheck dict buckets 5 928 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part960 : blockCheck dict buckets 5 960 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part992 : blockCheck dict buckets 5 992 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1024 : blockCheck dict buckets 5 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1056 : blockCheck dict buckets 5 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1088 : blockCheck dict buckets 5 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1120 : blockCheck dict buckets 5 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1152 : blockCheck dict buckets 5 1152 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1184 : blockCheck dict buckets 5 1184 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1216 : blockCheck dict buckets 5 1216 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1248 : blockCheck dict buckets 5 1248 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1280 : blockCheck dict buckets 5 1280 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1312 : blockCheck dict buckets 5 1312 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1344 : blockCheck dict buckets 5 1344 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1376 : blockCheck dict buckets 5 1376 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1408 : blockCheck dict buckets 5 1408 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1440 : blockCheck dict buckets 5 1440 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1472 : blockCheck dict buckets 5 1472 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1504 : blockCheck dict buckets 5 1504 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1536 : blockCheck dict buckets 5 1536 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1568 : blockCheck dict buckets 5 1568 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1600 : blockCheck dict buckets 5 1600 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1632 : blockCheck dict buckets 5 1632 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1664 : blockCheck dict buckets 5 1664 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1696 : blockCheck dict buckets 5 1696 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1728 : blockCheck dict buckets 5 1728 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1760 : blockCheck dict buckets 5 1760 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1792 : blockCheck dict buckets 5 1792 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1824 : blockCheck dict buckets 5 1824 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1856 : blockCheck dict buckets 5 1856 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1888 : blockCheck dict buckets 5 1888 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1920 : blockCheck dict buckets 5 1920 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1952 : blockCheck dict buckets 5 1952 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part1984 : blockCheck dict buckets 5 1984 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2016 : blockCheck dict buckets 5 2016 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2048 : blockCheck dict buckets 5 2048 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2080 : blockCheck dict buckets 5 2080 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2112 : blockCheck dict buckets 5 2112 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2144 : blockCheck dict buckets 5 2144 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2176 : blockCheck dict buckets 5 2176 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2208 : blockCheck dict buckets 5 2208 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2240 : blockCheck dict buckets 5 2240 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2272 : blockCheck dict buckets 5 2272 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2304 : blockCheck dict buckets 5 2304 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2336 : blockCheck dict buckets 5 2336 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2368 : blockCheck dict buckets 5 2368 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2400 : blockCheck dict buckets 5 2400 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2432 : blockCheck dict buckets 5 2432 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part2464 : blockCheck dict buckets 5 2464 20 = true := by
  decide +kernel

theorem held5 : blockCheck dict buckets 5 0 2484 = true :=
  (joinChecks 5 0 1248 1236 (joinChecks 5 0 608 640 (joinChecks 5 0 288 320 (joinChecks 5 0 128 160 (joinChecks 5 0 64 64 (joinChecks 5 0 32 32 held5Part0 held5Part32) (joinChecks 5 64 32 32 held5Part64 held5Part96)) (joinChecks 5 128 64 96 (joinChecks 5 128 32 32 held5Part128 held5Part160) (joinChecks 5 192 32 64 held5Part192 (joinChecks 5 224 32 32 held5Part224 held5Part256)))) (joinChecks 5 288 160 160 (joinChecks 5 288 64 96 (joinChecks 5 288 32 32 held5Part288 held5Part320) (joinChecks 5 352 32 64 held5Part352 (joinChecks 5 384 32 32 held5Part384 held5Part416))) (joinChecks 5 448 64 96 (joinChecks 5 448 32 32 held5Part448 held5Part480) (joinChecks 5 512 32 64 held5Part512 (joinChecks 5 544 32 32 held5Part544 held5Part576))))) (joinChecks 5 608 320 320 (joinChecks 5 608 160 160 (joinChecks 5 608 64 96 (joinChecks 5 608 32 32 held5Part608 held5Part640) (joinChecks 5 672 32 64 held5Part672 (joinChecks 5 704 32 32 held5Part704 held5Part736))) (joinChecks 5 768 64 96 (joinChecks 5 768 32 32 held5Part768 held5Part800) (joinChecks 5 832 32 64 held5Part832 (joinChecks 5 864 32 32 held5Part864 held5Part896)))) (joinChecks 5 928 160 160 (joinChecks 5 928 64 96 (joinChecks 5 928 32 32 held5Part928 held5Part960) (joinChecks 5 992 32 64 held5Part992 (joinChecks 5 1024 32 32 held5Part1024 held5Part1056))) (joinChecks 5 1088 64 96 (joinChecks 5 1088 32 32 held5Part1088 held5Part1120) (joinChecks 5 1152 32 64 held5Part1152 (joinChecks 5 1184 32 32 held5Part1184 held5Part1216)))))) (joinChecks 5 1248 608 628 (joinChecks 5 1248 288 320 (joinChecks 5 1248 128 160 (joinChecks 5 1248 64 64 (joinChecks 5 1248 32 32 held5Part1248 held5Part1280) (joinChecks 5 1312 32 32 held5Part1312 held5Part1344)) (joinChecks 5 1376 64 96 (joinChecks 5 1376 32 32 held5Part1376 held5Part1408) (joinChecks 5 1440 32 64 held5Part1440 (joinChecks 5 1472 32 32 held5Part1472 held5Part1504)))) (joinChecks 5 1536 160 160 (joinChecks 5 1536 64 96 (joinChecks 5 1536 32 32 held5Part1536 held5Part1568) (joinChecks 5 1600 32 64 held5Part1600 (joinChecks 5 1632 32 32 held5Part1632 held5Part1664))) (joinChecks 5 1696 64 96 (joinChecks 5 1696 32 32 held5Part1696 held5Part1728) (joinChecks 5 1760 32 64 held5Part1760 (joinChecks 5 1792 32 32 held5Part1792 held5Part1824))))) (joinChecks 5 1856 320 308 (joinChecks 5 1856 160 160 (joinChecks 5 1856 64 96 (joinChecks 5 1856 32 32 held5Part1856 held5Part1888) (joinChecks 5 1920 32 64 held5Part1920 (joinChecks 5 1952 32 32 held5Part1952 held5Part1984))) (joinChecks 5 2016 64 96 (joinChecks 5 2016 32 32 held5Part2016 held5Part2048) (joinChecks 5 2080 32 64 held5Part2080 (joinChecks 5 2112 32 32 held5Part2112 held5Part2144)))) (joinChecks 5 2176 160 148 (joinChecks 5 2176 64 96 (joinChecks 5 2176 32 32 held5Part2176 held5Part2208) (joinChecks 5 2240 32 64 held5Part2240 (joinChecks 5 2272 32 32 held5Part2272 held5Part2304))) (joinChecks 5 2336 64 84 (joinChecks 5 2336 32 32 held5Part2336 held5Part2368) (joinChecks 5 2400 32 52 held5Part2400 (joinChecks 5 2432 32 20 held5Part2432 held5Part2464)))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part0 : blockCheck dict buckets 6 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part32 : blockCheck dict buckets 6 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part64 : blockCheck dict buckets 6 64 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part96 : blockCheck dict buckets 6 96 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part128 : blockCheck dict buckets 6 128 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part160 : blockCheck dict buckets 6 160 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part192 : blockCheck dict buckets 6 192 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part224 : blockCheck dict buckets 6 224 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part256 : blockCheck dict buckets 6 256 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part288 : blockCheck dict buckets 6 288 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part320 : blockCheck dict buckets 6 320 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part352 : blockCheck dict buckets 6 352 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part384 : blockCheck dict buckets 6 384 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part416 : blockCheck dict buckets 6 416 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part448 : blockCheck dict buckets 6 448 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part480 : blockCheck dict buckets 6 480 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part512 : blockCheck dict buckets 6 512 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part544 : blockCheck dict buckets 6 544 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part576 : blockCheck dict buckets 6 576 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part608 : blockCheck dict buckets 6 608 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part640 : blockCheck dict buckets 6 640 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part672 : blockCheck dict buckets 6 672 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part704 : blockCheck dict buckets 6 704 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part736 : blockCheck dict buckets 6 736 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part768 : blockCheck dict buckets 6 768 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part800 : blockCheck dict buckets 6 800 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part832 : blockCheck dict buckets 6 832 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part864 : blockCheck dict buckets 6 864 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part896 : blockCheck dict buckets 6 896 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part928 : blockCheck dict buckets 6 928 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part960 : blockCheck dict buckets 6 960 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part992 : blockCheck dict buckets 6 992 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1024 : blockCheck dict buckets 6 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1056 : blockCheck dict buckets 6 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1088 : blockCheck dict buckets 6 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1120 : blockCheck dict buckets 6 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1152 : blockCheck dict buckets 6 1152 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1184 : blockCheck dict buckets 6 1184 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1216 : blockCheck dict buckets 6 1216 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1248 : blockCheck dict buckets 6 1248 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1280 : blockCheck dict buckets 6 1280 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1312 : blockCheck dict buckets 6 1312 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1344 : blockCheck dict buckets 6 1344 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1376 : blockCheck dict buckets 6 1376 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1408 : blockCheck dict buckets 6 1408 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1440 : blockCheck dict buckets 6 1440 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1472 : blockCheck dict buckets 6 1472 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1504 : blockCheck dict buckets 6 1504 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1536 : blockCheck dict buckets 6 1536 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1568 : blockCheck dict buckets 6 1568 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1600 : blockCheck dict buckets 6 1600 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1632 : blockCheck dict buckets 6 1632 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1664 : blockCheck dict buckets 6 1664 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1696 : blockCheck dict buckets 6 1696 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1728 : blockCheck dict buckets 6 1728 13 = true := by
  decide +kernel

theorem held6 : blockCheck dict buckets 6 0 1741 = true :=
  (joinChecks 6 0 864 877 (joinChecks 6 0 416 448 (joinChecks 6 0 192 224 (joinChecks 6 0 96 96 (joinChecks 6 0 32 64 held6Part0 (joinChecks 6 32 32 32 held6Part32 held6Part64)) (joinChecks 6 96 32 64 held6Part96 (joinChecks 6 128 32 32 held6Part128 held6Part160))) (joinChecks 6 192 96 128 (joinChecks 6 192 32 64 held6Part192 (joinChecks 6 224 32 32 held6Part224 held6Part256)) (joinChecks 6 288 64 64 (joinChecks 6 288 32 32 held6Part288 held6Part320) (joinChecks 6 352 32 32 held6Part352 held6Part384)))) (joinChecks 6 416 224 224 (joinChecks 6 416 96 128 (joinChecks 6 416 32 64 held6Part416 (joinChecks 6 448 32 32 held6Part448 held6Part480)) (joinChecks 6 512 64 64 (joinChecks 6 512 32 32 held6Part512 held6Part544) (joinChecks 6 576 32 32 held6Part576 held6Part608))) (joinChecks 6 640 96 128 (joinChecks 6 640 32 64 held6Part640 (joinChecks 6 672 32 32 held6Part672 held6Part704)) (joinChecks 6 736 64 64 (joinChecks 6 736 32 32 held6Part736 held6Part768) (joinChecks 6 800 32 32 held6Part800 held6Part832))))) (joinChecks 6 864 448 429 (joinChecks 6 864 224 224 (joinChecks 6 864 96 128 (joinChecks 6 864 32 64 held6Part864 (joinChecks 6 896 32 32 held6Part896 held6Part928)) (joinChecks 6 960 64 64 (joinChecks 6 960 32 32 held6Part960 held6Part992) (joinChecks 6 1024 32 32 held6Part1024 held6Part1056))) (joinChecks 6 1088 96 128 (joinChecks 6 1088 32 64 held6Part1088 (joinChecks 6 1120 32 32 held6Part1120 held6Part1152)) (joinChecks 6 1184 64 64 (joinChecks 6 1184 32 32 held6Part1184 held6Part1216) (joinChecks 6 1248 32 32 held6Part1248 held6Part1280)))) (joinChecks 6 1312 224 205 (joinChecks 6 1312 96 128 (joinChecks 6 1312 32 64 held6Part1312 (joinChecks 6 1344 32 32 held6Part1344 held6Part1376)) (joinChecks 6 1408 64 64 (joinChecks 6 1408 32 32 held6Part1408 held6Part1440) (joinChecks 6 1472 32 32 held6Part1472 held6Part1504))) (joinChecks 6 1536 96 109 (joinChecks 6 1536 32 64 held6Part1536 (joinChecks 6 1568 32 32 held6Part1568 held6Part1600)) (joinChecks 6 1632 64 45 (joinChecks 6 1632 32 32 held6Part1632 held6Part1664) (joinChecks 6 1696 32 13 held6Part1696 held6Part1728))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part0 : blockCheck dict buckets 7 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part32 : blockCheck dict buckets 7 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part64 : blockCheck dict buckets 7 64 4 = true := by
  decide +kernel

theorem held7 : blockCheck dict buckets 7 0 68 = true :=
  (joinChecks 7 0 32 36 held7Part0 (joinChecks 7 32 32 4 held7Part32 held7Part64))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held8Part0 : blockCheck dict buckets 8 0 1 = true := by
  decide +kernel

theorem held8 : blockCheck dict buckets 8 0 1 = true :=
  held8Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem checkedRoot : rootClosed table 8 rows = true := by
  decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 8 < binaryCost gs :=
  bound_from_closure rows rfl (by decide) table
    (tableClosure held2 held3 held4 held5 held6 held7 held8) checkedRoot sampleOK gs o hg he

end Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upper : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [6, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241888 * 2 ^ 32 + 3941130464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem upper_mono : Monotone2 upper := by
  intro g mem
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_correct : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel
theorem agree : ∀ x : Fin 6 → Bool, target x = Signed.F x := by decide +kernel

end PEqualNP.Outside.L_meta_16303

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16303 in
theorem PEqualNP.Outside.L_meta_16303 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3941130464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3941130464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨D,fit,sz,comp⟩ := h
  by_cases hasNot : ∃ g ∈ D.gates, g.op = GateOp.not
  · obtain ⟨g,mem,op⟩ := hasNot
    have short : Signed.binaryCost D.gates < D.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,mem,by simp [Signed.isBinary,op]⟩
    have legal : ∀ a ∈ D.gates, Signed.legal a := by
      intro a am
      have ready := fit a am
      simpa [Signed.legal] using ready
    have lower := Signed.bound D.gates D.output legal (fun x => (comp x).trans (agree x))
    have usize : upper.size = 10 := rfl
    change D.gates.length ≤ s at sz
    exact ⟨upper,upper_mono,by omega,upper_correct⟩
  · refine ⟨D, ?_,sz,comp⟩
    intro g mem
    have fitG := fit g mem
    refine ⟨?_,fitG.2⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *
    rcases fitG.1 with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hasNot ⟨g,mem,hn⟩).elim
