import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16853

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
abbrev W := BitVec 190
-- Free complementation leaves four binary choices up to output polarity.
def norm (x : W) : W := if x.getLsbD 63 then ~~~x else x

theorem norm_or (w : W) : w = norm w ∨ w = ~~~(norm w) := by
  unfold norm
  split <;> simp

def rawOps (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def ops (x y : W) : List W := (rawOps x y).map norm
def sep (x : W) : BitVec 63 := ((x >>> 63) ^^^ x).setWidth 63
def cuts (ws : List W) : BitVec 63 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (~~~(0xffffffffffe00000 : BitVec 64)) ++ (-1 : BitVec 63) ++ (0 : BitVec 63)
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

def differs (i : Fin 63) (w : W) : Prop :=
  w.getLsbD (63+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 63) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  have hnorm : differs i (norm q) ↔ differs i q := by
    unfold norm differs
    split <;> simp [show 63+i.val < 190 by omega, show i.val < 190 by omega]
  have hd := hnorm.mp hd
  simp only [rawOps, List.mem_cons, List.not_mem_nil, or_false] at hq
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 63+i.val < 190 := by omega
  have hi' : i.val < 190 := by omega
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 63) :
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
  change (cuts ws)[j] = (BitVec.allOnes 63)[j]
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
  · change reachable av (BitVec.allOnes 190 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 190)
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

private def bit (k : Fin 190) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 190) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 190) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#190)[k.val] = false; simp
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 3) || (x 0 && x 2 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5)

def insertWire (w : W) : List W → List W
  | [] => [w]
  | x::xs => if (w.toNat >>> 126) ≤ (x.toNat >>> 126) then w::x::xs else x::insertWire w xs

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

abbrev Mark := W × BitVec 63

def mark (w : W) : Mark := (w,sep w)

def markedCuts (ws : List Mark) : BitVec 63 := ws.foldr (fun w v => w.2 ||| v) 0

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

def rows : List W := [0x2adb6db5dde80084850f47f0010a65020f1dffed0b16da27,
0x336db6d96eb809110820b8001c501a0410e3f0b21ea9741d,
0x3c71c71e7732a22630df0000628760d870ea1242f5dec5f0,
0x3f81f81f87c4cc381290200036f090a96f0c0564ede129d2,
0x3ffe001ff8070fc02d20c000d43d816378002981f87f03c6,
0x3fffffe00007f00032400000e0a4801860100e190169a238]

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
    let i ← findKey dict (w.toNat >>> 126)
    let tail ← encodeBank dict ws
    return 4096 * tail + i + 1

set_option maxRecDepth 16000 in
def expanded : PackedSeq := ⟨179, 190, 0x3fffffffffffffffffffffffffffffffffffffffffffffff, .fork 3 0x3c70821e72120200200000004005004070e20002f4de05d0 (
.fork 1 0x3fe3fe00007700022400000c024801000100e190029a228 (
.leaf 0 0xe3fff800017c000490000028282006000403864048688e038e79e00005f00012400000a0a0801800100e190121a2280e38e380001540000800000200820000004030640084882038e30c1888d0dd10d20f8009c789b270801e9b10a21320f0e380006201437003483000250e2048c2000a60420840818380380180c44c1802002000147090210f040524082128020c30c304222024442082e00071406810000782c02884c03428a28a188c80080850047f0010805020f15edad0a001a0701f81f80000cc000810000030010004000402864002208a007e05a0782b03c4ad2fc7f0c10f65421011fa89121ed22501f80001e00c0f00b4830003003405084000a2044078081007a07a0783a2286a54f47f0410f655210f3fa8b121ed62501c01c01c0c88818813c0001001d814043884808407b108006c06c0683801010820980008000a0410e3f0921208540d0168168160a00212143d1fc0042994080047ea24085b4894001ffe00730f02612df00002282609800fa165a0580e4380007ff800003c000490000008200006000401860040280e0001ff0007f0e03e12df200022c2709807ee16660580ec300007f6801fa300f24a7c9fc08f09d2201c7759b01e03e0c4001f80007c0c0381290200022c01088070c0464058028100007df001ee280dc437ce000ab09ea7003af49c81e03d0e4001efa007f8a02690df07f02382649807ffd66e0780dc3100071c001cc28098437c00008a09826003a84908160310c0001b6c006b800110000380008401a0400e3d032068074190005b68017a00012003c1fc0040990001c7759b00c03608400041000100a02610df00002282609800080240010080200000007fe0003f00348300005064058c60008603e0580718000001f87c00c3800902000165010a10f0c0164ec8009c200000079dcc00898027c0000080d830043a8410bd2591700000001dfff809958d2ffff01d5a7f061feff1e61e965c0700000065bae024442082e00071406810438fc2887a0150140000015dde80084850f47f0010a65020f0df1e40a165807) (
.fork 2 0x1db6000eb0070fc02d20c000d43d816378000901f07f03c2 (
.leaf 1 0x7603603a0d1330e04a408000dbc242a5bc3015139784a749c30c30e3312a22630df0000628760d870ea0242f5de85f055fa5f80001fc000c9000003829200618040286401a688e157e000a78070fc02d20c000d43d816370002881f07f03c454924900001fc000c9000003829200618000004001a48061524001ff8070fc02d20c000d43d816378002180f87f01c654900028801c3d00a082000350d60185c0000003c1a40701500901f87c4cc381290200036f090a96f0c0164ece129d254024028081330e04a408000dbc242a58000000393848741470870a7232a22630df0000628760d870e21202f4dec5f050820879dcca8898c37c00018a1d8361c3a8410bd3791741420820a2212a22230d00000628500d870e20002f4c805d045b25b21a8e024442082e00071406810438fc2485aa5d07512492596eb809110820b8001c501a0410e3f0b21ea9741d44924920884024442082e000714068104388004852a49060f9e79e00007f00032400000e0a4801860100e190161a2283e78001e601c3f00b483000350f6058da000a607a1dc0f18f80780781c4cc381290200036f090a96f0c0564e96129c233f8001be01c1f00b483000300b6058de000a607c1780f18c9249200007f00032400000e0a4801860100e09014082203248007fe01c3f00b483000350f6058de000a607e1580f18c920006900706c025004000c02d816368000901e05603c23207e01a1f1310e04a4080008b8242a5bc3015939700a748c80481f87c4cc381290200036f090a96f0c0564edc009c23201201a051310a04a4000008a8202a5bc30151385002708c10411e7732a22630df0000628760d870ea1242f5d6c5e030410418440a8898c37c00018a1d836180200903855a0780c10000610020200200000004005004060000000e05601c02a69a69667200212143d1fc0042994083c77bfb42c5a689c8924935dde80084850f47f0010a65020f1dffed0b16da272249249245000212143d1fc0042994083c703d34045a28883fe3fe00007700022400000c024801000100e190029a228) (
.leaf 2 0xf1c0007fe0083f00b48300015074058de0008603e178071bc70001e77320226209f0000420760c070ea1042f4de45c0f1c00079d8c808008000000100140101c388400bd3791703c70001e70020200200000004005004070000000f05e01c0f007007e1f0230e042408000db4042a5bc300593b700274bc01c01e77308226109f0000228360c870ea1042f5d645d0f00700781c020080424000008a0002218020010397000743bfffffdfff809958d2ffff01d5a7f061fffffff1fbffe3fefffffe5bae024442082e0007140681043cffaec7ea7d8f7bfffff5dde80084850f47f0010a65020f1dfffd0b3ffa3fefffff800000000000000000000000000040386404a688e3bedfeddeff809110820b8001c501a041feff5f61fa97c1febefbef7ffe00212143d1fc0042994087fffffbc7e7b78df37fb7e00003300020400000c004001000100a190029a238cdb7df65bee2a4dc63fee000fb49ea7043afcbc87ea7d0f736db6d96eb809110820b8001c501a0410e3f0b21ea9741dcdb6db000000000000000000000000000000004000a4806336c00196800090008208000141000001000208018290004cc06c0641a00204000008000514040000000008032848043061c7186730a02610df00002282609810ea12421588c430c186186198c0000000000000000000004388400852211042eda0017d80706c025004000c02d816368002981e85603c6ba05a05e171310a04a4000008a8202a5bc301593a500270abdf7de000055000020000008020800000100e190121a228ab6db6d777a00212143d1fc0042994083c77ffb42c5b689eadb6da000000000000000000000000000100e0901008220ab6800576000020014010000002004082000a6042058081aa81681585c0000000000000000000000f0c056409000802a145145154800010003c00000009800000204900045b008224924914ca8000000000000000000000001f0a00a00500576db6d80001fc000c9000003829200618040386405a688e1db6000eb0070fc02d20c000d43d816378000901f07f03c2))) (
.fork 4 0x3f81ffff87c4fc3812d0200036f090b96f1c077cede1a9fa (
.leaf 3 0xfe07fb7e1ff330e44a40e000fbc26ab5bfbf55dbbf85f76ff81f81feffccd391ab0b8003ef09aad7feff5e6ffe17dd7fe07e07e1f1330e04a408000dbc242a5bc301593b784a74bf81f8068144c4281290000022a080a96f0c0544e16129d2fe07e0000013000048000000828200218000100005848043f81681f85c40c0000000000143080216f0c0564e96109c2fe01207e051330a04a400000dac202a5bc301513a584270bf80001ff8040fc00d20c0001439816378002180f87701c6fe00007e1f1030e00240800059c24285bc300593b384270bf80001f80040c00000000001430802168000100e86101c2fdf7df7dfeeaacdce3fee001fb5deb71c3afcbcbffffd7f7f7df7de7732a22630df0000628760d870ea1252f5ffe5f8fdf6db7dfae82c44a082e00171546911c38fc2cbfbfdd777f7c001f78020b00282080005415004070002080f87f01c4fbefbeffffea8a9ad77d1fc18e3d9769ffffffbfff7b7fdfefbefbe7732a22630df0000628760d870fa1e4bf5dec7f0fbe8007fe0080a009401000100340509e000a607e1780f1bef1ef1ff7f2a22630df0000628760d87fee1766fddecdf2fa07a07e1f020080424000008a000221bc301593b700274be79e79f7fbaa22630df0000628760d870ebf2e2ffded5f5f5d00079c01c3d00a082000350d60185c0000003c1fc0703cf2001ef00706c025004000c02d816378000901f05e03c2f207207a1d1310a04a4000008a8202a5bc3015139700274bc7fc7fe7733b22630df0000e28760d870fa1a5bf5dec7f8f1f80079e00c0f00b483000300340509c000a207c1780f13c71fffe7732f22632df0000628760d870fa165af5dee5f8f1c7bef9dfea889ac37c1fc18e1d9361dfff59bbdf7b77c7c71c71e7732a22630df0000628760d870ea1242f5dec5f0f1c71c00000a8000c10000018210006180000800052200c3c71861e76320200200000004005004070e21002f4de45d0f1c20879c84a8888c34000018a140361c388000bd3781743c70821e72120200200000004005004070e20002f4de05d0) (
.fork 5 0x3fffb01ffe870fd02d20e000d47d9163780029a1fcff23d6 (
.leaf 4 0xfffe187ff8dc3f00b483000350f6058de388e60ff3fd1f5bfff6dbffdef0fc4ad2fc7f0d53fe5637f1dffedfb7fdbe7fffdb6ffe01c3f00b483000350f6058de040be27e5fe0f9bfff681ffdc70fc02d20c000d43d81637f0c2de5f97f0bc6fffc927ff2bc3f00b483000350f6058de007e687e9fd4f1fffe925ffa170fd12d20f800dc7d9b6778e22993fcff27defff8e3ffe01d7f00bc83000350f6058de040b667e1fc8f3bffe381ff8c74fd82f20e000d47d91637f042da5f87f2bc6fff8c37fe23c3f44b483e00371f66d9de007a6c7e9fccf3fffe28bff8cf0fc0ad20c7f0d53d85637f15edadfa7f1bc7fff81fffe01cff00b583000350f605cde040ae67e1fe0fbbffe06dff83f0fc12d20d800dc3d8b6778e3f993fa7f57cffff8007ffafc3f44b483e00371f66d9de38fe68ffbfd5f1fffe001ff8070fc02d20c000d43d816378002981f87f03c6fff80079c01c08008000000300960101c0002007c1fc0f03ffe0006900706c025004000c02d816368000901e07f03c2fff80000001c000080000003009200018000200401a40803ff1ff1ff7f6ee3e32df200076f7f0f97fee1766fdffedf2ffc0007fc01838008000000150d60185e0000403e1fc070bfedfedfeffccd391ab0b8003ef09aad7feff5f6ffe97ddfffb7fb7e1f1330e04a408000dbc242a5bc3015d3b7a4a76bfedf81fefc4cd381ab0a00036f090a97f0c25e4fde929d6ff87f87f9fd330e04a408000dbc242a5ffb8559bf7a5b74bfdbfdbfdfecccbc979f67f037faf5ab6f1dffedeff7fbf7ff6ff6fe1f1330e04a408000dbc242a5bc703db7b786afcbfda001fd8040c80050040001438812368002981e87703c6ff27f27f3fb330e04a408000dbc242a5bc37d793bf85e75ffa5fa5fa7d4cd391ab0b8003ef09aad7fee0576fde92ddafe48007e401c3b009401000350f6058da0002407a1dc0f0bf8ff8ff87c5dc3812902000b6f090a96f1c0d7dede12bdafe37e37e3f3334e46ac2e000fbc26ab5bc3797d3bf84e77ff81ffff87c4fc3812d0200036f090b96f1c077cede1a9fa) (
.leaf 5 0x3ffffffff807ffc03f60c000f4bd817b78102f99f97fa3fefffffffe1f1ff0e0cb408003dbd242e5bc703df7b7a6afebffffffe7737f22632df0000e2a7e0d870fa1e5bf5ffe7f8fffffff9d8dfc800c900000382960161c3c8786fd7ff9fe3ffffffe7007f20032400000e0a5805870100e19f17fa3f8fffffff81c1fc080cb4000038a9202618060396797a68fe3ffffff96ebff9113a60b800fcf49a1c70f3febb1fe9f63dffffffe198dfc000c900000382920061c3c8786c57a798e3ffffff5ddeff084b74f47f0e1aee51a6f1dfffd0b7ffa3fffffffd6171fc000c900000382920061bc703df425a6a8ebffffff14caff00032400000e0a480186011feb90b69f23dffffffa8885fc888cb4000038a960361c3c8386fd7a69fe3fffffe68147f42832d00000e2a480b96f1c0f5de169abfaffffff80001fc000c9000003829200618040386405a688e3ffff81fffc7cff83fb0e000f6fd91eb7f0c2de5fdff2bd6ffff1c7ffcdebf98f7ff0003daff87ede3a8ef0ff7ff1fdbfffb6dffebf0fd12d20f800dc7d9b6778e3f9b3feff77dffffedb7fe01c3f00b483000350f6058de000a647e1fc8f7bfffb01ffe870fd02d20e000d47d9163780029a1fcff23d6)))⟩

def decodeBank (dict : PackedSeq) : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, packed =>
    if packed = 0 then []
    else BitVec.ofNat 190 ((expanded.at ((packed % 4096) - 1)).getD 0) :: decodeBank dict n (packed / 4096)

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
def dict : PackedSeq := ⟨179, 64, 0xffffffffffffffff, .fork 3 0xf1c20879c8480800 (
.fork 1 0xff8ff80001dc000 (
.leaf 0 0xe3fff800017c0000e39e7800017c0000e38e380001540000e38c306223437440e380006201437000e00e006031130600c30c304222024440a28a2862320020201f81f80000cc00001f81681e0ac0f1201f80001e00c0f0001e81e81e0e88a1a01c01c01c0c8881801b01b01a0e004040168168160a002120007ff801cc3c0980007ff800003c0000007fc001fc380f80007f6801fa300f20007e0001f0300e00007df001ee280dc0007be801fe2809a00071c001cc280980006db001ae000440005b68017a0001200010400040280980000007fe0003f000000007e1f0030e000000079dcc0089800000077ffe0265600000065bae024440000005777a00212) (
.fork 2 0x76d8003ac01c3f00 (
.leaf 1 0x7603603a0d1330e070c30c38cc4a889855fa5f80001fc00055f80029e01c3f0054924900001fc0005490007fe01c3f0054900028801c3d005402407e1f1330e054024028081330e051c21c29c8ca889850820879dcca889850820828884a888845b25b21a8e0244444924965bae0244444924920884024443e79e780001fc0003e78001e601c3f003e01e01e071330e033f8001be01c1f0032492480001fc0003248007fe01c3f003248001a401c1b003207e01a1f1310e03201207e1f1330e03201201a051310a030410479dcca889830410418440a889830400018400808002a69a69667200212224924d777a0021222492492450002120ff8ff80001dc000) (
.leaf 2 0xf1c0007fe0083f00f1c00079dcc80898f1c00079d8c80800f1c00079c0080800f007007e1f0230e0f0070079dcc20898f00700781c020080effffff7ffe02656efffffe5bae02444efffffd777a00212efffff8000000000efb7fb77bfe02444ebefbef7ffe00212cdfedf80000cc000cdb7df65bee2a4dccdb6db65bae02444cdb6db0000000000cdb00065a0002400cc06c0641a002040c1871c619cc28098c186186198c00000bb68005f601c1b00ba05a05e171310a0af7df78000154000ab6db6d777a00212ab6db68000000000ab68005760000200aa05a05617000000a1451451548000108924924532a0000076db6d80001fc00076d8003ac01c3f00))) (
.fork 4 0xfe07fffe1f13f0e0 (
.leaf 3 0xfe07fb7e1ff330e4fe07e07fbff334e4fe07e07e1f1330e0fe07e01a051310a0fe07e00000130000fe05a07e17103000fe01207e051330a0fe00007fe0103f00fe00007e1f1030e0fe00007e00103000fdf7df7dfeeaacdcfdf7df79dcca8898fdf6db7dfae82c44fdf0007de0082c00fbefbeffffea8a9afbefbef9dcca8898fbe8007fe0080a00fbc7bc7fdfca8898fa07a07e1f020080f9e79e7dfeea8898f5d00079c01c3d00f3c8007bc01c1b00f207207a1d1310a0f1ff1ff9dccec898f1f80079e00c0f00f1c7fff9dccbc898f1c7bef9dfea889af1c71c79dcca8898f1c71c00000a8000f1c61879d8c80800f1c20879c84a8888f1c20879c8480800) (
.fork 5 0xfffec07ffa1c3f40 (
.leaf 4 0xfffe187ff8dc3f00fffdb6fff7bc3f12fffdb6ffe01c3f00fffda07ff71c3f00fffc927ff2bc3f00fffa497fe85c3f44fff8e3ffe01d7f00fff8e07fe31d3f60fff8c37fe23c3f44fff8a2ffe33c3f02fff81fffe01cff00fff81b7fe0fc3f04fff8007ffafc3f44fff8007fe01c3f00fff80079c01c0800fff8001a401c1b00fff80000001c0000ffc7fc7fdfdbb8f8ffc0007fc0183800ffb7fb7fbff334e4ffb7fb7e1f1330e0ffb7e07fbf1334e0ff87f87f9fd330e0ff6ff6ff7fb332f2ff6ff6fe1f1330e0ff68007f60103200ff27f27f3fb330e0fe97e97e9f5334e4fe48007e401c3b00fe3fe3fe1f1770e0fe37e37e3f3334e4fe07fffe1f13f0e0) (
.leaf 5 0xffffffffe01fff00fffffffe1f1ff0e0fffffff9dcdfc898fffffff9d8dfc800fffffff9c01fc800fffffff81c1fc080ffffffe5baffe444ffffffe198dfc000ffffffd777bfc212ffffffd6171fc000ffffffc532bfc000ffffffa8885fc888ffffff9a051fd0a0ffffff80001fc000ffffe07fff1f3fe0ffff1c7ffcdebf98fffedb7ffafc3f44fffedb7fe01c3f00fffec07ffa1c3f40)))⟩

set_option maxRecDepth 16000 in
def bank4 : PackedSeq := ⟨11, 56, 0xffffffffffffff, .leaf 0 0xb007e063051048ac07e05d051048a807e05d051048a608d074065048a608d063051048a607e063051048a607e061051048a607e05e051048a607e05d054051a60630510480287e06305104801f⟩

set_option maxRecDepth 16000 in
def bank5 : PackedSeq := ⟨142, 68, 0xfffffffffffffffff, .fork 2 0xa6093065051048040 (
.fork 1 0xa607e06505104803b (
.leaf 0 0xa607e065051048030a607e06505104802ea607e06505104802ca607e06505104802ba607e065051048025a607e065051048011a607e06505104800fa607e06505104800ea607e06505104800ca607e06505104800ba607e06505104800aa607e065051048007a607e05d05104c048a607e05d051048035a607e05d05104801aa607e05d05104800aa607e05d051048004a606505d051048028a606505104802b028a606505104802800a9307e0650560510489307e0650530510489307e0650510490489307e0650510480429307e06505104803e9307e0650510480319307e0650510480219307e0650510480209307e065051048003930650530510480287e06505d051048020000a607e063051048) (
.leaf 1 0xa6093065051048039a609306505104802fa609306505104802aa6093065051048029a6093065051048028a6093065051048017a6093065051048015a609207e065051048a609107e065051048a608e07e065051048a608d06505d051048a608d06505104802ba608d06505104800aa608707e065051048a608407e065051048a607e079065051048a607e074065051048a607e073065051048a607e07205d051048a607e070065051048a607e06c065051048a607e06b065051048a607e068065051048a607e065063051048a607e065060051048a607e06505d051048a607e065052051048a607e06505104d048a607e06505104b048a607e065051048041a607e06505104803da607e06505104803b)) (
.fork 3 0xa609307e075051048 (
.leaf 2 0xa609307e071051048a609307e06f051048a609307e06d051048a609307e069051048a609307e067051048a609307e066051048a609307e065058048a609307e065057051a609307e065055048a609307e065054051a609307e065051024a609307e065051023a609307e065048034a609307e065048033a609307e063051048a609307e062051048a609307e05f051048a609307e05b051048a609307e05104803fa609307e051048037a609307e051048036a609307e051048027a609307e05104801da609307d065051048a609307b065051048a609307a065051048a6093078065051048a609306e065051048a609306a065051048a609306505c051048a609306505104a048a6093065051048040) (
.fork 4 0xa60a307e063051048 (
.leaf 3 0xa60a307e05104801da60a3065051048028a60a207e065051048a60a107e065051048a60a007e065051048a609e07e065051048a609d07e065051048a609c07e065051048a609b07e065051048a609a07e065051048a609907e065051048a609807e065051048a609707e065051048a609607e065051048a609507e065051048a609407e065051048a609308d065059048a609308d065051048a609308d065048032a609308d065048028a609308c065051048a609308b065051048a609308a065051048a6093088065051048a6093086065051048a6093085065051048a6093083065051048a6093082065051048a6093081065051048a6093080065051048a609307f065051048a609307e075051048) (
.leaf 4 0xb10a607e05d051048af09307e065051048af07e06505d051048ae09307e065051048ac09307e065051048aa09307e065051048a909307e065051048a809307e065051048a709307e065051048a7093065051048028a60a308d065051048a60a307e065051048a60a307e06504802ba60a307e063051048)))⟩

set_option maxRecDepth 16000 in
def bank6 : PackedSeq := ⟨66, 80, 0xffffffffffffffffffff, .fork 1 0xa609307e065051048035 (
.leaf 0 0xa609307e065051048032a609307e06505104802da609307e06505104802ba609307e065051048028a609307e065051048026a609307e065051048022a609307e06505104801ea609307e06505104801ca609307e06505104801ba609307e06505104801aa609307e065051048019a609307e065051048018a609307e065051048016a609307e065051048014a609307e065051048013a609307e065051048012a609307e065051048010a609307e06505104800da609307e06505104800aa609307e065051048009a609307e065051048008a609307e065051048006a609307e065051048005a609307e065051048004a609307e065051048002a609307e065051048001000a60a307e065051048000a609308d065051048000a6093065051048028000a607e06505d051048000a607e06505104802b000a607e06505104800a) (
.fork 2 0xb20a609307e065051048 (
.leaf 1 0xb10a609307e065051048ad0a609307e065051048ab0a609307e065051048a60a509307e065051048a60a409307e065051048a60a309307e065051048a609f09307e065051048a609309007e065051048a609308f07e065051048a609308d07e065051048a609308907e065051048a609307e07c065051048a609307e077065051048a609307e076065051048a609307e072065051048a609307e065064051048a609307e06505d051048a609307e06505a051048a609307e065059051048a609307e065051050048a609307e06505104f048a609307e06505104e048a609307e06505104c048a609307e065051048047a609307e065051048046a609307e065051048045a609307e065051048044a609307e065051048043a609307e06505104803ca609307e06505104803aa609307e065051048038a609307e065051048035) (
.leaf 2 0xb30a609307e065051048b20a609307e065051048))⟩

set_option maxRecDepth 16000 in
def bank7 : PackedSeq := ⟨1, 68, 0xfffffffffffffffff, .leaf 0 0xa609307e065051048⟩

def buckets (t : ℕ) : PackedSeq :=
  if t = 4 then bank4 else
  if t = 5 then bank5 else
  if t = 6 then bank6 else
  if t = 7 then bank7 else
  ⟨0, 0, 0, .leaf 0 0⟩

theorem bound_from_closure (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    (root : rootClosed table 7 inputs = true)
    (sample : ∀ k : Fin 190, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 190) :
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
  exact rootClosed_sound table closure ht 7 inputs nd root (lift low run)

def table := tableFrom dict buckets

theorem tableClosure
    (h4 : blockCheck dict buckets 4 0 11 = true)
    (h5 : blockCheck dict buckets 5 0 142 = true)
    (h6 : blockCheck dict buckets 6 0 66 = true)
    (h7 : blockCheck dict buckets 7 0 1 = true)
    : ∀ t ws, table t ws = true → closedState table t ws = true := by
  intro t ws belongs
  obtain ⟨i,key,hk,rfl⟩ := tableFrom_sound _ _ _ _ belongs
  have ih := PackedSeq.at_bound hk
  have ready : blockCheck dict buckets t 0 (buckets t).size = true := by
    have ready4 : t = 4 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h4
    have ready5 : t = 5 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h5
    have ready6 : t = 6 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h6
    have ready7 : t = 7 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h7
    by_cases eq4 : t=4
    · exact ready4 eq4
    by_cases eq5 : t=5
    · exact ready5 eq5
    by_cases eq6 : t=6
    · exact ready6 eq6
    by_cases eq7 : t=7
    · exact ready7 eq7
    have empty : buckets t = ⟨0, 0, 0, .leaf 0 0⟩ := by simp [buckets,eq4,eq5,eq6,eq7]
    simp [empty,blockCheck]
  exact blockCheck_sound _ _ ready (Nat.zero_le _) (by simpa using ih) hk

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem sampleOK : ∀ k : Fin 190, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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
theorem held4Part0 : blockCheck dict buckets 4 0 11 = true := by
  decide +kernel

theorem held4 : blockCheck dict buckets 4 0 11 = true :=
  held4Part0

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
theorem held5Part128 : blockCheck dict buckets 5 128 14 = true := by
  decide +kernel

theorem held5 : blockCheck dict buckets 5 0 142 = true :=
  (joinChecks 5 0 64 78 (joinChecks 5 0 32 32 held5Part0 held5Part32) (joinChecks 5 64 32 46 held5Part64 (joinChecks 5 96 32 14 held5Part96 held5Part128)))

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
theorem held6Part64 : blockCheck dict buckets 6 64 2 = true := by
  decide +kernel

theorem held6 : blockCheck dict buckets 6 0 66 = true :=
  (joinChecks 6 0 32 34 held6Part0 (joinChecks 6 32 32 2 held6Part32 held6Part64))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part0 : blockCheck dict buckets 7 0 1 = true := by
  decide +kernel

theorem held7 : blockCheck dict buckets 7 0 1 = true :=
  held7Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem checkedRoot : rootClosed table 7 rows = true := by
  decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 7 < binaryCost gs :=
  bound_from_closure rows rfl (by decide) table
    (tableClosure held4 held5 held6 held7) checkedRoot sampleOK gs o hg he

end Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upper : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [12, 13]⟩], 14⟩
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277071598 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem upper_mono : Monotone2 upper := by
  intro g mem
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_correct : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel
theorem agree : ∀ x : Fin 6 → Bool, target x = Signed.F x := by decide +kernel

end PEqualNP.Outside.L_meta_16853

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16853 in
theorem PEqualNP.Outside.L_meta_16853 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4209568456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    have usize : upper.size = 9 := rfl
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
