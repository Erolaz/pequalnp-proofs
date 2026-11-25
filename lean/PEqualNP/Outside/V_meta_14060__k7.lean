import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

namespace PEqualNP.Outside.V_meta_14060__k7

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ForestCore

-- Binary gate bound adapted from L_meta_10976.
open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 16
abbrev Row := Fin 16

def zero : Sig := 0

def one : Sig := BitVec.allOnes 16

def neg (a : Sig) : Sig := ~~~a

def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)

def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d

theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))

theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]

theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)

theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩

theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩

theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 16) (a : Sig) : Bool := a.getLsbD i.val

private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]

private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp

private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]

private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a

theorem nrm_false (a : Sig) : nrm false a = a := rfl

theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]

theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]

theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]

theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']

theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])

theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h

def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b

theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]

theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this

theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)

theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))

theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem restoreInput {α : Type} [DecidableEq α] (U : Finset α) (a : α) :
    (if a ∈ U then insert a (U.erase a) else U.erase a) = U := by
  by_cases ha : a ∈ U
  · rw [if_pos ha, Finset.insert_erase ha]
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]

theorem restoreInputs {α : Type} [DecidableEq α] (U : Finset α) (a b : α) (hab : a ≠ b) :
    let s := (U.erase a).erase b
    let t := if b ∈ U then insert b s else s
    (if a ∈ U then insert a t else t) = U := by
  have member : b ∈ U.erase a ↔ b ∈ U := by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨Ne.symm hab, h⟩⟩
  have inner : (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U.erase a := by
    by_cases hb : b ∈ U
    · rw [if_pos hb, Finset.insert_erase (member.mpr hb)]
    · rw [if_neg hb, Finset.erase_eq_of_notMem (fun h => hb (member.mp h))]
  dsimp only
  rw [inner]
  exact restoreInput U a


theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))


def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬ Live u T k S

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne (Ne.symm hab), Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)


def roots : List Sig := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def target : Sig := 142

def probePairs : List (Row × Row) :=
  [(0,1),(0,2),(1,5),(1,9),(2,6),(2,10),(5,7),(6,7),(7,15)]

def separates (T : Sig) (ws : List Sig) : Bool :=
  probePairs.all fun (r,s) => bit r T == bit s T || ws.any (fun w => bit r w != bit s w)

theorem live_separates {T : Sig} {k : Nat} {ws : List Sig} (h : Live true T k ws.toFinset) :
    separates T ws = true := by
  unfold separates
  apply List.all_eq_true.mpr
  rintro ⟨r,s⟩ _
  by_cases eq : bit r T = bit s T
  · simp [eq]
  · obtain ⟨w, m, neq⟩ := live_row_difference h eq
    have z : ws.any (fun v => bit r v != bit s v) = true :=
      List.any_eq_true.mpr ⟨w, List.mem_toFinset.mp m, by simpa using neq⟩
    simp [z]

def states : Nat → List (List Sig)
  | 4 => [roots]
  | 3 => [[0xaa,0xcccc,0xf0f0,0xff00],[0xcc,0xaaaa,0xf0f0,0xff00],
          [0xf0,0xaaaa,0xcccc,0xff00],[0xaaaa,0xcccc,0xff00,0xfff0],
          [0xaaaa,0xf0f0,0xff00,0xffcc],[0xcccc,0xf0f0,0xff00,0xffaa]]
  | 2 => [[0xaa,0xcc,0xf0f0],[0xaa,0xcccc,0xfff0],[0xcc,0xaaaa,0xfff0]]
  | _ => []

def sameSet (xs ys : List Sig) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {xs ys : List Sig} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  rw [sameSet, Bool.and_eq_true] at h
  ext x
  simp only [List.mem_toFinset]
  constructor
  · intro hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h.1 x hx)
  · intro hy
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h.2 x hy)

def rejected (cap : Nat) (ws : List Sig) : Bool :=
  if cap = 0 then !(ws.contains target)
  else !separates target ws || (states cap).any (sameSet ws)

def closure (cap : Nat) (ws : List Sig) : Bool :=
  !(ws.contains target) &&
  ws.all fun a => ws.all fun b => (List.range 4).all fun d =>
    [false,true].all fun ka => [false,true].all fun kb =>
      let v := bin d a b
      let next := childTwo ws a b d ka kb
      if a ≠ b ∧ v ∉ ws ∧ v ≠ zero ∧ v ≠ one ∧ next.length ≤ cap
      then rejected (cap-1) next else true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ cap : Fin 5, (states cap.val).all (closure cap.val) = true :=
  by decide +kernel

theorem closed (cap : Nat) (hc : cap ≤ 4) :
    ∀ ws ∈ states cap, Impossible true target cap ws.toFinset := by
  induction cap with
  | zero => simp [states]
  | succ cap ih =>
    intro ws mem
    have basic := List.all_eq_true.mp (checked ⟨cap+1,by omega⟩) ws mem
    simp only [closure,Bool.and_eq_true] at basic
    have hn : ws.Nodup := by
      have all : ∀ k : Fin 5, (states k.val).all (fun xs => decide xs.Nodup) = true := by decide +kernel
      have m := List.all_eq_true.mp (all ⟨cap+1,by omega⟩) ws mem
      exact of_decide_eq_true m
    apply enum_step hn (by simpa using basic.1)
    intro a ma b mb d hd ka kb ne fresh good len
    have dm : d ∈ List.range 4 := List.mem_range.mpr (by unfold allowed at hd; omega)
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp basic.2 a ma) b mb) d dm
    have h := List.all_eq_true.mp h ka (by cases ka <;> simp)
    have h := List.all_eq_true.mp h kb (by cases kb <;> simp)
    have nxt : rejected cap (childTwo ws a b d ka kb) = true := by
      simpa [ne,fresh,good.1,good.2,len] using h
    cases cap with
    | zero =>
      intro k hk live
      have eq : k = 0 := by omega
      subst k
      exact (by simpa [rejected] using nxt : target ∉ childTwo ws a b d ka kb)
        (List.mem_toFinset.mp (live.1.symm ▸ Finset.mem_singleton_self target))
    | succ k =>
      simp only [rejected,Nat.succ_ne_zero,ite_false,Bool.or_eq_true,Bool.not_eq_true] at nxt
      rcases nxt with sep | h
      · intro j hj run
        simp [live_separates run] at sep
      · obtain ⟨ys, my, sy⟩ := List.any_eq_true.mp h
        rw [sameSet_sound sy]
        exact ih (by omega) ys my

def cube (r : Row) (i : Fin 4) : Bool := r.val.testBit i.val

theorem cube_input (r : Row) : List.ofFn (cube r) = roots.map (bit r) :=
  (by decide +kernel : ∀ r : Row, List.ofFn (cube r) = roots.map (bit r)) r

def f (x : Fin 4 → Bool) : Bool := (142 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)

theorem cube_output (r : Row) : f (cube r) = bit r target :=
  (by decide +kernel : ∀ r : Row, f (cube r) = bit r target) r

theorem goalEq (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = f x) :
    (execute C.gates roots).getD C.output zero = target := by
  apply bit_ext
  intro r
  rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← cube_input]
  exact (comp (cube r)).trans (cube_output r)

theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = f x) :
    5 ≤ C.gates.countP (fun g => !isNot g) := by
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq C fit comp] at out
  unfold Repr at out
  have pg : bit 0 target = false := by decide +kernel
  rw [nrm_id pg] at out
  have hp : proper target := by unfold proper; decide +kernel
  obtain ⟨k,S,hk,run,sub⟩ := extract (u := true) C.gates roots fit (by simp) hp
    (out.resolve_right (fun h => h hp))
  have normalized : roots.map (nrm true) = roots := by decide +kernel
  rw [normalized] at sub
  have all : ∀ a ∈ roots, a ∈ S := by
    intro a ma
    simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at ma
    rcases ma with rfl | rfl | rfl | rfl
    · apply raw_required run roots _ sub 0 1 (by decide +kernel)
      intro v m h
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl | rfl | rfl
      · exact (h rfl).elim
      all_goals decide +kernel
    · apply raw_required run roots _ sub 0 2 (by decide +kernel)
      intro v m h
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl | rfl | rfl
      · decide +kernel
      · exact (h rfl).elim
      all_goals decide +kernel
    · apply raw_required run roots _ sub 1 5 (by decide +kernel)
      intro v m h
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl | rfl | rfl
      · decide +kernel
      · decide +kernel
      · exact (h rfl).elim
      · decide +kernel
    · apply raw_required run roots _ sub 1 9 (by decide +kernel)
      intro v m h
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl | rfl | rfl
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · exact (h rfl).elim
  have eq : roots.toFinset = S := by
    ext a
    simp only [List.mem_toFinset]
    exact ⟨all a, sub a⟩
  by_contra! bound
  exact closed 4 (by omega) roots (by simp [states]) k (by omega) (eq.symm ▸ run)

def NoFall (a b : Row) (v : Sig) : Prop := bit a v = true → bit b v = true
def Ordered (a b : Row) (w : List Sig) : Prop := ∀ v ∈ w, NoFall a b v

theorem read_order {a b w} (h : Ordered a b w) (i : Nat) :
    NoFall a b (w.getD i zero) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : w[i]? with
  | none => simp [NoFall,bit_zero]
  | some v => exact h v (List.mem_of_getElem? he)

theorem prime_order {a b v t} (d : Bool) (hv : NoFall a b v) (ht : NoFall a b t) :
    NoFall a b (prime d v t) := by
  unfold NoFall at *
  cases d <;> simp [bit_prime] at * <;> tauto

theorem fold_order {a b w} (d : Bool) (h : Ordered a b w) (ins : List Nat) :
    NoFall a b ((ins.map fun i => w.getD i zero).foldr (prime d) (if d then zero else one)) := by
  induction ins with
  | nil => cases d <;> simp [NoFall,bit_zero,bit_one]
  | cons i ins ih =>
    simp only [List.map_cons,List.foldr_cons]
    exact prime_order d (read_order h i) ih

theorem gate_order {a b w g} (h : Ordered a b w)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hn : isNot g = false) :
    NoFall a b (gv w g) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at legal
  rcases legal with rfl | rfl | rfl
  · exact fold_order false h ins
  · exact fold_order true h ins
  · simp [isNot] at hn

theorem ordered_snoc {a b w v} (h : Ordered a b w) (hv : NoFall a b v) :
    Ordered a b (w ++ [v]) := by
  intro x m
  simp only [List.mem_append,List.mem_singleton] at m
  rcases m with m | rfl
  · exact h _ m
  · exact hv

theorem neg_guard {w g} (mid : Ordered 5 7 w)
    (hg : g.op = .not) : NoFall 1 5 (gv w g) ∨ NoFall 7 15 (gv w g) := by
  obtain ⟨op, ins⟩ := g
  change op = .not at hg
  subst op
  cases ins with
  | nil => simp [gv,NoFall,bit_neg,bit_zero]
  | cons i ins =>
    have middle := read_order mid i
    change NoFall 1 5 (neg (w.getD i zero)) ∨ NoFall 7 15 (neg (w.getD i zero))
    unfold NoFall at *
    rw [bit_neg,bit_neg,bit_neg,bit_neg]
    cases h5 : bit 5 (w.getD i zero) <;> cases h7 : bit 7 (w.getD i zero) <;>
      simp_all

theorem execute_order {a b} (gs : List Gate) (w : List Sig) (h : Ordered a b w)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (none : gs.countP isNot = 0) : Ordered a b (execute gs w) := by
  induction gs generalizing w with
  | nil => exact h
  | cons g gs ih =>
    rw [List.countP_cons] at none
    have hg : isNot g = false := by cases e : isNot g <;> simp_all
    have rest : gs.countP isNot = 0 := by simpa [hg] using none
    have h' := ordered_snoc h (gate_order h (legal g (by simp)) hg)
    exact ih _ h' (fun x m => legal x (by simp [m])) rest

theorem execute_one_not (gs : List Gate) (w : List Sig)
    (a : Ordered 1 5 w) (m : Ordered 5 7 w) (b : Ordered 7 15 w)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (count : gs.countP isNot ≤ 1) :
    Ordered 1 5 (execute gs w) ∨ Ordered 7 15 (execute gs w) := by
  induction gs generalizing w with
  | nil => exact Or.inl a
  | cons g gs ih =>
    rw [List.countP_cons] at count
    have gl := legal g (by simp)
    have rest : ∀ x ∈ gs, x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun x hx => legal x (by simp [hx])
    cases ng : isNot g with
    | false =>
      have lift {i j} (h : Ordered i j w) := ordered_snoc h (gate_order h gl ng)
      exact ih _ (lift a) (lift m) (lift b) rest (by simpa [ng] using count)
    | true =>
      have nc : gs.countP isNot = 0 := by
        have hc : gs.countP isNot + 1 ≤ 1 := by simpa only [ng, ite_true] using count
        omega
      have op : g.op = .not := by cases e : g.op <;> simp_all [isNot]
      rcases neg_guard m op with h | h
      · exact Or.inl (execute_order gs _ (ordered_snoc a h) rest nc)
      · exact Or.inr (execute_order gs _ (ordered_snoc b h) rest nc)

theorem notLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = f x) :
    2 ≤ C.gates.countP isNot := by
  by_contra! bound
  have one : C.gates.countP isNot ≤ 1 := by omega
  have h := execute_one_not C.gates roots
    (by
      intro v hv
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> unfold NoFall <;> decide +kernel)
    (by
      intro v hv
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> unfold NoFall <;> decide +kernel)
    (by
      intro v hv
      simp only [roots,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> unfold NoFall <;> decide +kernel)
    (fun g m => (fit g m).1) one
  rcases h with h | h
  · have r := read_order h C.output
    rw [goalEq C fit comp] at r
    exact (by unfold NoFall; decide +kernel : ¬ NoFall 1 5 target) r
  · have r := read_order h C.output
    rw [goalEq C fit comp] at r
    exact (by unfold NoFall; decide +kernel : ¬ NoFall 7 15 target) r

theorem gate_counts (gs : List Gate) :
    gs.countP isNot + gs.countP (fun g => !isNot g) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.countP_cons,List.countP_cons,List.length_cons]
    cases isNot g <;> simp <;> omega

def C : Circuit :=
  ⟨[⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.not,[2]⟩,⟨.not,[3]⟩,
    ⟨.and,[5,6]⟩,⟨.or,[4,8]⟩,⟨.and,[7,9]⟩],10⟩

theorem exactCost : HasCircuitSize 4 f 7 ∧ ∀ t : ℕ, HasCircuitSize 4 f t → 7 ≤ t := by
  refine ⟨⟨C, by simp [C, FanInTwo], by decide, by decide +kernel⟩, ?_⟩
  intro t h
  obtain ⟨D, fit, sz, comp⟩ := h
  have b := binaryLower D fit comp
  have n := notLower D fit comp
  have total := gate_counts D.gates
  change D.gates.length ≤ t at sz
  omega

end ForestCore
end PEqualNP.Outside.V_meta_14060__k7

theorem PEqualNP.Outside.V_meta_14060__k7 :
    PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (142 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 7 ∧
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (142 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 7 ≤ t :=
  PEqualNP.Outside.V_meta_14060__k7.ForestCore.exactCost
