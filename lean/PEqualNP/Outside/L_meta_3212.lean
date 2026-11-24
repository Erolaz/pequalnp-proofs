import Mathlib
import PEqualNP.Defs

-- The cofactor lower bound uses the checked theta certificate from L_meta_1672.

namespace PEqualNP.Outside.L_meta_3212
namespace Base1007
namespace Theta
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
inductive Run {α : Type} (inv : α->α) (meet join : α->α->α) (y : α) : ℕ->List α->Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs->Run inv meet join y s xs->Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)
theorem kept_map {α β : Type} (e : α->β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e=kept b (e x) (xs.map e):= by cases b <;> simp [kept]
lemma Run.map {α β : Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
    {inv' : β->β} {meet' join' : β->β->β}
    (hi : ∀ a,e (inv a)=inv' (e a)) (hm : ∀ a b,e (meet a b)=meet' (e a) (e b))
    (hj : ∀ a b,e (join a b)=join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e):= by
  induction h with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e):= by
      cases neg <;> simp [kept_map,hi]
    rw [e1] at ih; exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)):= by
      cases conj <;> simp [kept_map,hm,hj]
    rw [e1] at ih; exact Run.two conj ka kb ih
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) : xs.length ≤ s+1:= by
  induction h with
  | done=>simp
  | perm hp _ ih=>rwa [←hp.length_eq]
  | one _ save _ ih=>cases save <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat):=Run (·^^^m) (·&&&·) (·|||·)
lemma q29 {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i=m.testBit j) (hw : ∀ w ∈ xs,w.testBit i=w.testBit j) :
    y.testBit i=y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | one neg save _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)
def lo (k : Nat):=2^k - 1
def mask (k : Nat):=lo (k+k)
def goal (k : Nat):=lo k<<<k
def se : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def q7 : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def qe : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000
lemma yx : se=lo 232:= by decide +kernel
lemma vb : q7=mask 232:= by decide +kernel
lemma vc : qe=goal 232:= by decide +kernel
lemma u4 (k i : Nat) : (lo k).testBit i=decide (i<k):= by
  simp [lo,Nat.testBit_two_pow_sub_one]
lemma zn (k i : Nat) : (mask k).testBit i=decide (i<k+k):= by
  simp [mask,u4]
lemma xo (k i : Nat) :
    (goal k).testBit i=(decide (k ≤ i)&&decide (i - k<k)):= by
  simp [goal,Nat.testBit_shiftLeft,u4]
def vd (w : Nat) : Nat:=w^^^(w>>>232)
def s9 : List Nat->Nat | []=>0 | a :: t=>vd a|||s9 t
lemma q11 (i : Nat) (ws : List Nat) : (s9 ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i ≠ a.testBit (232+i):= by
  induction ws with
  | nil=>simp [s9]
  | cons a t ih =>
    simp only [s9,Nat.testBit_or,Bool.or_eq_true,ih,vd,Nat.testBit_xor,Nat.testBit_shiftRight,List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
lemma vl {s ws} (h : NatRun q7 qe s ws) :
    (s9 ws&&&se)=se:= by
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hm : (mask 232).testBit i=(mask 232).testBit (232+i):= by
      simp [zn,show i<464 by omega,show 232+i<464 by omega]
    have hy : (goal 232).testBit i ≠ (goal 232).testBit (232+i):= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (s9 ws).testBit i=true:= by
      apply (q11 i ws).2; by_contra! hh; exact hy (q29 h i (232+i) hm hh)
    simp [hc]
  · simp [u4,hi]
lemma q34 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1) (i j : Nat)
    (hw : ∀ a ∈ ws,a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (hp.length_eq.trans hl) (fun a ha=>hw a (hp.mem_iff.1 ha))
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had; simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true,Bool.false_eq_true,ite_false,Nat.testBit_or,Nat.testBit_and] <;> grind
    · exact hw _ (by simp [ht])
def sq (w : Nat) : Nat:=(w>>>232)&&&(w^^^se)
def rd : List Nat->Nat | []=>0 | a :: t=>sq a|||rd t
lemma zu (i : Nat) (hi : i<232) (ws : List Nat) : (rd ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i=false/\a.testBit (232+i)=true:= by
  induction ws with
  | nil=>simp [rd]
  | cons a t ih=>simp [rd,sq,yx,u4,hi,ih,and_comm]
lemma rl {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    (rd ws&&&se)=se:= by
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hy : ¬ (goal 232).testBit (232+i) ≤ (goal 232).testBit i:= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i=true:= by
      apply (zu i hi ws).2; by_contra! hh; apply hy
      apply q34 h hl; intro a ha; specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
    simp [hc]
  · simp [u4,hi]
lemma y1 {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):= by cases b <;> simpa [kept] using p
def vy (s : Nat) (ws : List Nat) (f : Bool->List Nat->Bool) : Bool :=
  let len:=ws.length
  let slack:=s+2 - len
  let t0:=decide (len=s+2)
  let t1:=decide (len=s+1)
  let t2:=decide (len=s)
  ws.any fun a =>
    let ra:=ws.erase a
    let da:=vd a
    let dau:=sq a
    (slack ≥ 1 &&
      (let cra:=if t1&&slack==1 then 0 else s9 ra
       let crau:=if t1||t2 then rd ra else 0
       [false,true].any fun neg =>
        let w:=if neg then a^^^q7 else a
        (((if t1 then sq w|||crau else vd w|||cra)&&&se==se)&&f t1 (w :: ra)) ||
        (slack ≥ 2 &&
          ((if t2 then sq w|||(dau|||crau) else vd w|||(da|||cra))&&&se==se) &&
          f t2 (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b &&
      (let r:=ra.erase b
       let db:=vd b
       let dbu:=sq b
       let cr:=if t0 then 0 else s9 r
       let cru:=if t0||t1||t2 then rd r else 0
       [false,true].any fun conj =>
        let w:=if conj then a&&&b else a|||b
        let dw:=if t0 then 0 else vd w
        let dwu:=if t0||t1||t2 then sq w else 0
        (((if t0 then dwu|||cru else dw|||cr)&&&se==se)&&f t0 (w :: r)) ||
        (slack ≥ 1 &&
          ((((if t1 then dwu|||(dau|||cru) else dw|||(da|||cr))&&&se==se)&&f t1 (w :: a :: r)) ||
           (((if t1 then dwu|||(dbu|||cru) else dw|||(db|||cr))&&&se==se)&&f t1 (w :: b :: r)))) ||
        (slack ≥ 2 &&
          ((if t2 then dwu|||(dau|||(dbu|||cru)) else dw|||(da|||(db|||cr)))&&&se==se) &&
          f t2 (w :: a :: b :: r)))
lemma q08 {a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun q7 qe s ((if neg then a^^^q7 else a) :: kept save a rest))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a):=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrun:=Run.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha]; omega
    rw [hlen] at ht
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h1,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [hcov,ht]
  | true =>
    simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2-ws.length:= by omega
    have hlen : ((if neg then a^^^q7 else a) :: a :: ws.erase a).length=ws.length+1:= by
      simp [List.length_erase_of_mem ha]; omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hlen_eq] at ht
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · have h1 : ws.length ≠ s+1:= by omega
      simp only [h1,h2,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma u9 {a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq; omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrun:=Run.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    by_cases h0 : ws.length=s+2
    · have hcu:=rl hrun (by omega)
      simp only [h0,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,decide_false,s9] at ht hcov ⊢
      simp [hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: b :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr]; omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr]; omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=ws.length+1:= by
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h2,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma q07 {a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  rcases le_total a b with hab | hba
  · exact u9 hab p h f hf
  · apply u9 (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a&&&b else a|||b)=(if conj then b&&&a else b|||a):= by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
lemma q1f {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t=0->ws=[y]:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one=>simp
  | two=>simp
lemma y0 {t ws} (h : NatRun q7 qe t ws) :
    ∀ s,t=s+1->∀ zs,ws.Perm zs->∀ f : Bool->List Nat->Bool,
      (∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true)->vy s zs f=true:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | one _ _ h _=>intro s he zs p f hf; cases he; exact q08 p h f hf
  | two _ _ _ h _=>intro s he zs p f hf; cases he; exact q07 p h f hf
def xs517 : List ℕ:=[0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517,0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827,0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248,0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0,0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418,0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800,0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]
lemma yn : ∀ zs ∈ xs517.sublists,zs ≠ xs517 →
    (s9 zs&&&se) ≠ se:= by decide +kernel
def r2 (tag d w : Nat) : Nat:=((w&&&tag)<<<d)|||((w>>>d)&&&tag)
lemma q3l (tag d i w : Nat) (h : (tag&&&(tag<<<d))=0) :
    (r2 tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag<<<d).testBit i then w.testBit (i-d) else false):= by
  have ht:=congrArg (fun v : Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [r2,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at*<;> grind
lemma yw (tag d : Nat) (h : (tag&&&(tag<<<d))=0) (a b : Nat) :
    r2 tag d (a&&&b)=(r2 tag d a&&&r2 tag d b) ∧
    r2 tag d (a|||b)=(r2 tag d a|||r2 tag d b) ∧
    r2 tag d (a^^^b)=(r2 tag d a^^^r2 tag d b):= by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,q3l tag d i _ h] <;>
    split_ifs <;> simp
lemma q0b {s ws} (h : NatRun q7 qe s ws) (tag d : Nat)
    (hz : (tag&&&(tag<<<d))=0) (hm : r2 tag d q7=q7)
    (hy : r2 tag d qe=qe) :
    NatRun q7 qe s (ws.map (r2 tag d)):= by
  rw [← hy]
  exact Run.map _ (fun a=>(yw tag d hz a q7).2.2.trans (by rw [hm]))
    (fun a b=>(yw tag d hz a b).1) (fun a b=>(yw tag d hz a b).2.1) h
def q3e : Nat:=0x3ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff
def q3d : Nat:=0xfffffffffffffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffffffffff
def q38 (xs : List Nat):=xs.map (r2 q3e 58)
def q37 (xs : List Nat):=xs.map (r2 q3d 116)
lemma q3j {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q38 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma q3i {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q37 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
def vf (a b c d e f : Bool) : Nat :=
  let x:=b.toNat+c.toNat; let y:=(!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)
lemma q0q : ∀ a b c d e f g h i j l m : Bool,
    vf (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q1g : ∀ a b c d e f g h i j l m : Bool,
    vf (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q05 {l r : List Nat} (h : l.Perm r) : l.sum=r.sum:= by
  induction h with
  | nil=>rfl
  | cons _ _ ih=>simp [ih]
  | swap=>simp; omega
  | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma q01 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (v : Nat->Nat) (hand : ∀ a b,v (a&&&b) ≤ v a+v b)
    (hor : ∀ a b,v (a|||b) ≤ v a+v b) : v y ≤ (ws.map v).sum:= by
  induction h with
  | done=>simp
  | perm p _ ih=>rw [← q05 (p.map v)]; exact ih (p.length_eq.trans hl)
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc,← hand]; exact ih' | grw [← Nat.add_assoc,← hor]; exact ih'
def yz (a b c d e f v : Nat) : Nat :=
  if v.testBit a then
    if v.testBit d then (!v.testBit e).toNat+(!v.testBit f).toNat
    else
      let x:=(v.testBit b).toNat+(v.testBit c).toNat
      let y:=(!v.testBit e).toNat+(!v.testBit f).toNat
      max x (max y (x+y - 1))
  else
    if v.testBit d then 0
    else (v.testBit b).toNat+(v.testBit c).toNat
lemma q0e (a b c d e f v : Nat) :
    yz a b c d e f v=vf (v.testBit a) (v.testBit b) (v.testBit c)
      (v.testBit d) (v.testBit e) (v.testBit f):= by
  unfold yz vf
  cases v.testBit a <;> cases v.testBit d <;> rfl
lemma q0f {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (a b c d e f : Nat) : yz a b c d e f y ≤ (ws.map (yz a b c d e f)).sum:= by
  apply q01 h hl
  · intro v w; simp only [q0e,Nat.testBit_and]; exact q0q _ _ _ _ _ _ _ _ _ _ _ _
  · intro v w; simp only [q0e,Nat.testBit_or]; exact q1g _ _ _ _ _ _ _ _ _ _ _ _
def q26 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(462,447,452,215,221,207),(453,441,440,220,193,181),(445,410,360,199,216,201),(460,410,440,178,229,217),(459,461,454,220,89,205),(370,438,302,215,216,211),(457,410,418,199,207,201),(403,428,450,207,201,220),(457,429,450,218,207,201),(456,452,454,219,201,199)]
lemma zy : q26.all (fun t =>
    yz t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 qe==3)=true:= by decide +kernel
def yh (a b c d e f : Nat) : Nat->List Nat->Bool
  | acc,[]=>decide (acc<3)
  | acc,w :: t =>
    let acc':=acc+yz a b c d e f w
    if acc' ≥ 3 then false else yh a b c d e f acc' t
lemma zo (a b c d e f : Nat) (ws : List Nat) (acc : Nat)
    (h : yh a b c d e f acc ws=true) : acc+(ws.map (yz a b c d e f)).sum<3:= by
  induction ws generalizing acc with
  | nil=>simpa [yh] using h
  | cons w t ih =>
    simp only [yh] at h
    split at h
    · contradiction
    · have ih':=ih _ h
      simp only [List.map_cons,List.sum_cons]
      omega
def q0x (ws : List Nat) : Bool :=
  q26.any (fun t=>yh t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 0 ws)
lemma q1n {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    q0x ws=false:= by
  rw [Bool.eq_false_iff]; intro hk
  obtain ⟨t,ht,hlt⟩:=List.any_eq_true.mp hk
  have hg:=beq_iff_eq.mp (List.all_eq_true.mp zy t ht)
  have hb:=q0f h hl t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2
  have hs:=zo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ws 0 hlt
  rw [hg] at hb; omega
def span (f : Nat->Bool) : Nat->Nat->Bool
  | 0,_=>true
  | n+1,i=>f i&&span f n (i+1)
theorem span_ok {f n o} (h : span f n o=true) : ∀ i,o ≤ i->i<o+n->f i=true:= by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o=true) (hb : span f b (o+a)=true) :
    span f (a+b) o=true:= by
  induction a generalizing o with
  | zero=>simpa using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha; rw [Nat.succ_add,span,Bool.and_eq_true]
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩
lemma q10 {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r):= by
  induction t,hle using Nat.le_induction with
  | base=>exact h
  | succ _ _ ih=>exact Run.one false false ih
def q36 : Nat->Nat
  | 0=>0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517
  | 1=>0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827
  | 2=>0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248
  | 3=>0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0
  | 4=>0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418
  | 5=>0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800
  | 6=>0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688
  | 7=>0
  | 8=>q7
  | 9=>0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0
  | _=>0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0
def q24 : Nat->Nat
  | 0=>0x2e0060280e268192c8192a0162b81918806200192a019000081000503005188191880917801268a50013001001001280180a1481912811230110080214811218110300219811200110280616805020051e015000ec018011c8151481a16819178151a8150300a1981503006188150000017809030121680902812000ac01802148150000c10009118191281501006118150200a0b80910011030160f0150200602811098010d001028050a8050b811030150a8090280d098090300d08805028090780503011068050200d0580502009
  | 1=>0xb80e01806419520b952099521f152549510004c1d812531e91f00e520163d00d33951231511d8160027c00801000044e01601805268052a005380a51881610012421b2498fa3601206816188121f0c6068c62b0121e15129012380c50022801002440c5001482481242812030010b8120011829016308161f016078163e81a01809338c5001e802002188053081a1f01a178050581a0e81a0881a0d01a38019001bc0100536819001b0028011e0193481920002338190003432819320060280a3101900184020012f819168062e819
  | 2=>0x378a62080a1f00a1b80a0b80a0780a0d00a0d80a0c00a7ca290e80a0800a0700a7a80900074368096a132338097800914806230090b8a60d0a6260a61f0a6748a500068368a5730a50005c001703d0a514801708a5000f8002e8440a50030414809378c637812378161e0056b8051780a3781a1180519809200093200514805378013b00e2b00e2980e590ad1f80e530ad612e93d80e581b21a00e3c80e1100e613052600e0300e5d9b25eae95e9293600e5dae90d00e0200e0c00e580ad0900e0d80e0800e0600e591292900e582bd
  | _=>0x5e9327780e001f4000185200a9e8fa000540001412802000102b0023b002290026a802378021d80a0b80214802110029fc691f0029ec6906802090020c0020800207002060022a00652006591be6a80e6900e3780e6800e1d806002701a806260064f80a1780606806100060a806360060b80692006030090880642806078060e806730054f81a450053d0058d005028021680a1880a778124180a0680a148126e812260121000a778163600a14816360a6260163d8a63b00a2b00a2900a2880a0980a290a61480a
def zf : Nat->Nat->Nat
  | 0,_=>0
  | fuel+1,i =>
    if i<11 then q36 i
    else
      let k:=i - 11
      let c:=(q24 (k/83)>>>(20*(k % 83)))&&&1048575
      let op:=c&&&3
      let a:=(c>>>2)&&&511
      if op=0 then zf fuel a^^^q7
      else let b:=c>>>11; if op=1 then zf fuel a&&&zf fuel b else zf fuel a|||zf fuel b
def q2a : Nat->Nat
  | 0=>0x181dc00005ff70000179dc00005ef70000175dc00005cf70000171dc00005bf7000016ddc00005af70000169dc00005977000022fec000085fb004b86de40000857b0000211ec000081fb0050205e80000817b0000203ec0144807a0000201ec00007d7b00001fbec00007e7b00001f7ec00007cfb00001f1ec008b977c3d91c83f0014493fc0000295f80000a4fe000028ff80000a37e0000289f80000a07e0000285f80000a0fe000027ff800009efe0000279f800009dfe0000275f800009cfe0000001fc0000907d00001efec00007afb00001e9ec000079fb00001e5ec0146787a00001e1ec00006efe00001b5f400006cfd000015fec0000577b000015bec0000567b0030cabcc01332af3000a8abcc00b32af30029cabcc00b12af3002f8abcc00bc2af300518abe801442afa00500abe800002afb0000157ec0000527b0000147ec00c34ff5004cd3fd4002a4ff5002cd3fd400a74ff5002c53fd400be4ff5002f13fd454554ff10000139f400004d770000125f8000048fe0030c65d801331976000a865d800b319760029c65d800b119760031865d800be1976002f065d80110197a0042065e80102197a0040065e800fa197a004b865f00128197c0049c65f00000197e003c065e8545519720015465e8549f19740027c65f0aa9f1978000011fec000046fe0000115f800003efe0011ceff40000393f00000defc0000363f00000d6fc000034bf00000cefc0000323f00000c2fc00002fbf00000b8fc00002dbf00154b6ec00002cbf000c8b2f8014d2b9f00194ae7c005d2b9f0020cae7c014b2baf00240aebc002a2bb70033caedc010a2bbb0049caef4014a2bbe00000aefc00552bbb0027caef400322bbe000009fdc013e1fee002947f9c00001f5f000a8775c00001ddf328d8306c00be0c5700440316c011888cb00435b92c00c84bc70053d2d3801375355004f94d58012b515525cf8498801538c630030db98c013754e500001519c01509bf10051657c401509f720054e8dc8004785f9002f8ae5c01102b9b
  | 1=>0x45fc014b086f000c021bc002a08770000021fc0055087b0027c21f40032087e0000041fc014b0f6f000b83dbc002a0f77003e83dec00000f7f001543dec00320f7e0054436fc014d0ddf00104377c014b0def000a837dc00bc0df70010437f400000dff0015437ec009f0dfd000c837f800000eff0000039fc00000d7f0000033fc00000bff000002bfc000009ff0000023fc000007ff000001bfc002a04770000011fc0055047b000c811fa9b4b154700536973c014d6e4f0052db73c00dc6dcfa6d2cab2e9b4b194e005351d3c014d43cf005350b3c005d42cf0030e1b5c014d155700434555c01336dd7000a9b75e9a2a2ad3000b1455c00b05157000a9455e9a2a4fd5002c13d5c002a4f57000a9295e9a2a19560052d073c008e41cf000a9075c007b40cf0052d033c002a40d70029d035c014b156700450559c01131567004cdb99c002a6e67a58a8ab8c00b054e7000a9539c002a4ae7a58a86598002a4767002cd1d9c002a4467000a90f9c002a42e7002c50b9c00c345f3000b28bcc014558730030c49cc00c31b730030e5dd4004b95f50012e7dd80000aa7700002a7dc000061f70000017dc00009b77000026bdc00009a770051a67d8000099f70000265dc000087770000219dc000083770000209dc0153787300001dfdc0000777700001dbdc000076770051455cc011615730044055cc010915730041c55cc010215730040055cc00fa1573004c455d4012e1575004ac55d4012815750049c55d4013e15760052055d8014615760051055d8014015760000055dc00f21573003c055cc000075f700001d3dc0000747700001cbdc000071f700001c1dc00c3387300001a1dc000067f7000019ddc010959f30052167d8000059f7000019bdc012b5df50000199dc010253f30007d4fd4014053f6000014fdc000065f70000195dc000064f7004acbbd4013e2ef60000191dc00000577000018fdc010058f30049d63d4014458f60000163dc00006377000018bdc000062770000183dc01105f73004a17dd400005f77
  | 2=>0x1a5fc000068ff000009dfc00002d7f000a8abcc002a2af700024abec00472afb00000abec01382afb00098abec00412afb000d0abec00022afb00280abec00362afb00000abfc002a2afb001c0abec005a2afb00154abec000050ff000a93fd4002a4ff70000137fc00554dfb0000133fc00004c7f000a85ddc0047177f000005dfc0055177b0000127fc002a1977000a865d80009197e0011c65f8014b197e0011065f8008b197e0046c65f80000197f0009865f80058197e0010465f80034197e0000865f80000197e0028065f80119197e0019465f80036197e0000c65f8002a197e0013465f80070197e0015465ec0055197a0015465f8009f197e0027c65f00099197e000b865f80093197e000c865f8002a18770011c61fc0000187f0015461ec009f187d000c861f80000467f000010bfc0000427f000a843dc000010ff0015443ec003210fe0000107fc0000417f0000103fc0000407f00000fffc00003e7f00000f5fc00323d7e00000f3fc00003c7f00000effc00003b7f00000ebfc00003a7f00000e7fc014d03df0052c0fbc002a03f7000000ffc005503fb0027c0ff4003203fe00000aefc00412bbf00000affc00002b7f00154adec00002a7f00000a5fc0032297e00000a3fc003228fe00000a1fc0000267f000a895dc0000257f0000093fc0000247f000a88ddc0000237f000008bfc000021ff0000085fc0000207f005447efc00781fbf005347f7c00811fdf001ec7fbc014b1fef0007c7fbc002a1ff70029c7fdc01021ffb0007c7ff401401ffe000007ffc00551ffb0027c7ff400321ffe0000073fc00001c7f000006ffc00001aff0000067fc003219fe00534317c00650c5f00174317c00210c5f000a831dc00b10c770040031ec01440c7e0000031fc00550c7b000c831f800530c3f0000063fc000017ff000005bfc002a15f70000057fc000014ff0000051fc000013ff000004bfc0151093f00534257c0065095f0052c25bc002a09770019425ec0000097f0015425ec009f097d000c825f8000011ff
  | _=>0x7f0000055dc000023ff0000001fc0000137f0000083fc00001a7f0000005fc0000507f000006dfc000001ff0000055fc0000387f00000abec00002aff000005dfc0000197f0000065f80000187f0000043fc000003ff000007ffc00000c7f0000025fc0000087f000003dfc00000dff00536973c014d15570052c559c002c25f70000187dc004b58770000267dc00091577000b055dc004b15770054455dc007b15770053455dc004715770052c55dc004415770022c55dc011b15770050c55dc000115770000055dc00b01577003c455dc002615770007c55dc00411577000d055dc000215770028055dc002415770045455dc006515770043c55dc00361577000e855dc010515770000c55dc002a1577000a9c9dc002a6f770030c9bdc002a26f7004cce1dc002a3877000a9a5dc00b06177000a985dc000059f7002c177dc002a5df7000014fdc002c2ef7002c0bbdc002a2ef700308bbdc000058f7000017ddc00005e770012c6dec00261b7b001946dec0000817b0000201ec00007d7b0011c89f8004745fe000028df800448dfe0000289f80000a07e0000013fc0000a97f0000155fc0000a77f00000d5fc0000347f0000299fc000023ff0000287fc0000007f00000bdfc00009c7f0000261fc0000337f000025ffc000078ff000004dfc0000977f000025bfc0000307f0000259fc00002c7f0000255fc007b20ff0000083fc000094ff0000251fc00001a7f000024ffc0000937f0000249fc000091ff0000245fc000090ff0000005fc00008fff000023dfc00008eff0000239fc0047507e0000141fc00008d7f000007bfc00006c7f0000233fc00008aff0000225fc000087ff000006dfc00001d7f000020bfc0000817f0000201fc00007fff00001fdfc00007d7f0000007fc0047787b00001e1ec0000787f0000055fc0000737f00001c9fc000070ff00001bffc00006f7f00001b7fc00006bff00001adfc00006aff00001a9fc000069ff00098e1ec0065387b00098e1f40146387e00000e1fc004d387b
def xl (code k : Nat) (acc : List Nat) : List Nat :=
  if (code>>>k)&&&1==1 then q36 k :: acc else acc
def z0 (e : Nat) (acc : List Nat) : List Nat :=
  if e==0 then acc else zf 4 (e - 1) :: acc
def q3k (i : Nat) : List Nat :=
  if i<6 then []
  else
    let j:=i - 6
    let code:=(q2a (j/176)>>>(34*(j % 176)))&&&0x3ffffffff
    let acc:=z0 ((code>>>25)&&&511) (z0 ((code>>>16)&&&511) (z0 ((code>>>7)&&&511) []))
    xl code 0 (xl code 1 (xl code 2 (xl code 3 (xl code 4 (xl code 5 (xl code 6 acc))))))
def q25 : Nat->Nat
  | 0=>1 | 1=>1 | 2=>1 | 3=>1 | 4=>1 | 5=>1
  | 6=>19 | 7=>292 | 8=>365 | 9=>26 | 10=>1 | _=>0
def q3t : Nat->Nat
  | 0=>0 | 1=>1 | 2=>2 | 3=>3 | 4=>4 | 5=>5
  | 6=>6 | 7=>25 | 8=>317 | 9=>682 | 10=>708 | _=>0
def vj (s i : Nat) : List Nat:=q3k (q3t s+i)
def sg (salt : Nat) : List Nat->Nat
  | []=>0
  | w :: t=>let x:=(w % 1048573+317+salt) % 1048573; (x*x*x) % 1048573+sg salt t
def q18 : Nat->Nat
  | 6=>0x2d510a29c920dd8c26046a45edcab10e217235801e802cc829b
  | 7=>0xba020271000f0d789715b90b1b40d05ca2d4a2b20600798bac5c7e51085e9a4554cdd8e3980600005246e24e7704c2f50005cd6d23c0e8ee0943e87206f17bbbe2205918c9ad6d8c4dd10000ca1d4a0086754ac52a4592ac768220bc3fc1f922c761b4a30630003be5e00833f0d0d88b41f41811e4783cf36e2dc004002e0fbd5d8007d4b20a617c1680000029e1429da3348d12e9adfc1e03a65ca0c0b8279042040b6832081c4a94630e90120006c8e7618c585e8478000000e0b5e3abee6724d0dc28a4f63f1783c6676dd56abce0000e08019e42acc8c20d74cc7606228d6fa4e030800778001c584c7764b0a4ac49105d1a648c4486522847d50cc6e20a0c4d4e35f0901710e0cf40515302009b2095a0370e248f4c04163a3ab0e2840000aa000b85763445f112a350607800000029000006d184643c45988fb302401912822c64a9d0e0251912f598a0f42b8671a88181a41b0d04218a2434643e58a8f31b8394262fda061372b12394e130690d75503ca3d8870b697b212c6a301b50092181d0146e85e85835b2103bcf84497750e5ff1886ee6a8460501e2ebd824067cd205840001d91dcb18003c8b01d480c8280d067c358d0e1c820064b038188b0c722360a82b46ecd1d3fb780008508e3d453439e0ab8c320211da96c49235238a77476931a93a75666c63f3553f2880e4054184a210f404408b042709674c3e1af888398a483c3b7302460aa0ba8f06319693b13a3a09d00888a0a912af60582b10c1d65990a588472078ca40e9987a0801342287b47757e41d838d2941b3c228ff1c54020aac9092059006afd1a425090c482c4850b8cf9379f87621756ebdc27d118652a69049007e8914bf0f0b012a684ab49f802050ea22623a
  | 8=>0x138c54934604ac03d9da53893a963200001f918326961401461089814d14c94c238451f64d35929b4ffaf00002f2588000001a6d1c3b8e552048160000c7da4508a12ea26db16296bd4174c85145c2c45633c2b20c82402f83540b8c291ccda0a2c69e6c9eca21c2a0b32380b2a0ac60a180095d0bdd04b246a3d513ace3aa972874da6d12706ca58000a1009a100ee43944337528b29fa491af5485ec98a38a278ca0421a2b04903aa0829c0915225ecb49060815d8002cecf16671685a93052a10eaaae5249586bf0f0aeca69a030a2190e0e420b1707a822828a486a0ae27e4f50b56214a3320d56cc656d4d911c53d81c0725307c8d2be5faaad16f4d8a258091347291cdca1ed5dec5685f09208d2be2b0f502b18c1101fd8bd580c6170a10af63b6318d13b231385cca428188a62b26c28e949168927081b0890e0aba9e0040269400f2c59014d6670b590016363c59c58138de07c8391f105e2808a0c869d46aed6a82117f42080ed12ba0f4b08151da27cb0f180e20dc9fc0023e5a74085eeb944fafa110bfa19830b40f68686160013b2a22082398f4d442f04a620c4000002211d407031a26c888514480034f1ec65800402a400009c1dd13a932c83919f0c00c2376858002822bc3b9462330991510e6a11296a7530cb8219c518464554899170005ac7f05a12d2600002d1fe000000ac43043324a781ff1c1670760b312c69b2299d1e869c551c62a085d028515a82d93ea730a41d9582a81a063800064be426b5cda8b35174b0a59ccc19eb0245b5245d516d8cf57e4544e80150494c2cf8955b0486364e79f2176764c5478cc4ba000900101ed355380392a1d0c118ee1e423a000d31ba36028c1d118b2471a0c4a48007988d1162e80315e2742680a1598944bc9701e1a83102201b47e05816d544fc03083d4a2082920003001556e38c3f44a4407c0b76562d488805032b9427aaa016464000c1819282a82a618a37e140351d5b805d33781b1956d8ad29e01d930119822ac0560012e9fb018131e24d99695c1669c70006f92a2f4950b72cc325400c21231616587088b0ae90ab9002000855500f60005c2a99970ac8911b97e567000260a0514712600cc4367782c01f106669099ad2f73c6dc179d7f360515401b83e8990e65933865e276a50ac4592ae0cc5c09959456c2e2ea5d640f052e4008538372c1ca41de619665ae3b03b725475bc0369359ab3324d26b08f0005715f1e84df000cf83393c7b87923c256875510243753e0a908db9dac89d023a20b44cc289be83c53bec083f3780ccda9df0013f63a4a274ca400001181acf03821d7b6c547d43c
  | 9=>0xa197f9864cac828bcc96272d000622a0801403cb48d000b1ebd4114d11504f80408a7451700016502d6981bb801d1148e240e1f1b0344d9ea8d30f4e10
  | _=>0
def q17 : Nat->Nat
  | 6=>0x6d235ea20
  | 7=>0x234342c80020021d2500aec0506cac86608011a05070243405480089c0601bd838e5329f00e0429190060a0788c0230151a47435248086e14000c806004980012037e2603c050381010011a978040100000c03a0388c0e461502408295081442751882c1a0000038001c00000240503018180003014000d098080233
  | 8=>0x20e334d381e85e0400d6900336c4f00e1846c1e225571d8f3650040e03b0143103c0112c380e421004c3088010408f0104101c02228630140e03c0f00c2b18c01018020f002008e13181403001164360218b004672203d074b7000000904100c3117008118960500812827084700004a000b30d4020ac01000b606003004170041a01c0810c5c00827034690d80d04c1206c000100700431038000182b02801040000640515c37008013400f0180102c330140d02c0000816078000100b000ad000000000102c20010040004800016
  | 9=>0xd16e05d801451001402c9040
  | _=>0
def q16 (s : Nat) (zs : List Nat) : Nat :=
  match s with
  | 6 =>
    let h:=sg 11 zs % 1048573
    let d:=(q17 6>>>(5*(h % 7)))&&&31
    let slot:=((h*1001) % 1048573+d) % 29
    (q18 6>>>(7*slot))&&&127
  | 7 =>
    let h:=sg 0 zs % 1048573
    let d:=(q17 7>>>(9*(h % 110)))&&&511
    let slot:=((h*17) % 1048573+d) % 463
    (q18 7>>>(11*slot))&&&2047
  | 8 =>
    let h:=sg 1 zs % 1048573
    let d:=(q17 8>>>(10*(h % 166)))&&&1023
    let slot:=((h*1) % 1048573+d) % 695
    (q18 8>>>(11*slot))&&&2047
  | 9 =>
    let h:=sg 13 zs % 1048573
    let d:=(q17 9>>>(6*(h % 16)))&&&63
    let slot:=((h*31) % 1048573+d) % 71
    (q18 9>>>(7*slot))&&&127
  | _=>0
def yd (g : Nat) (ws : List Nat) :=
  if g=0 then ws else if g=1 then q38 ws else if g=2 then q37 ws else q38 (q37 ws)
lemma q0v (g : Nat) {s ws} (h : NatRun q7 qe s ws) :
    NatRun q7 qe s (yd g ws):= by
  unfold yd; split
  · exact h
  · split
    · exact q3j h
    · split
      · exact q3i h
      · exact q3j (q3i h)
def qh : Nat->Nat->Bool
  | 0,i=>!(vj 0 i==[qe])
  | s+1,i =>
    let ws:=vj (s+1) i
    !(vy s ws fun tight zs =>
      !(tight&&q0x zs) &&
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4)))))
lemma zc {s i} (hb : qh s i=true)
    (h : NatRun q7 qe s (vj s i)) :
    ∃ q<s,∃ j<q25 q,NatRun q7 qe q (vj q j):= by
  cases s with
  | zero=>simp [qh,q1f h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat):=!(tight&&q0x zs) &&
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length=s+1)) zs=true:= by
      simp only [F,Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length=s+1
        · simp [hl,q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj; by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN:=y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F)=true at hb; rw [hN] at hb; contradiction
lemma q0k {cap : Nat}
    (hc : ∀ s ≤ cap,∀ i<q25 s,qh s i=true) :
    ∀ s ≤ cap,∀ i<q25 s,¬ NatRun q7 qe s (vj s i):= by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩:=zc (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h
set_option maxHeartbeats 0 in lemma q3h :
    qh 0 0=true/\qh 1 0=true/\qh 2 0=true ∧
    qh 3 0=true/\qh 4 0=true/\qh 5 0=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma z6 : span (qh 6) 19 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3s : span (qh 7) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3r : span (qh 7) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3q : span (qh 7) 92 200=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3p : span (qh 8) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3o : span (qh 8) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3n : span (qh 8) 100 200=true:= by decide +kernel
set_option maxRecDepth 20000 in set_option maxHeartbeats 0 in lemma q3m : span (qh 8) 65 300=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma z9 : span (qh 9) 26 0=true:= by decide +kernel
set_option maxHeartbeats 0 in lemma q3z : span (qh 10) 1 0=true:= by decide +kernel
lemma z7 : span (qh 7) 292 0=true:=(@span_join (qh 7) 100 0 192 q3s (@span_join (qh 7) 100 100 92 q3r q3q))
lemma z8 : span (qh 8) 365 0=true:=(@span_join (qh 8) 200 0 165 (@span_join (qh 8) 100 0 100 q3p q3o) (@span_join (qh 8) 100 200 65 q3n q3m))
lemma q2x (s : Nat) (hs : s ≤ 10) : ∀ i<q25 s,qh s i=true:= by
  interval_cases s
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.2
  · exact fun i hi=>span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok q3z i (Nat.zero_le i) hi
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False:= by
  rw [← vb,← vc] at h
  have h10 : NatRun q7 qe 10 xs517:=q10 h hs
  have p : xs517.Perm (vj 10 0):= by decide +kernel
  exact q0k q2x 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False:= by
  by_cases eq : ws=xs517
  · subst ws; exact noRunFull _ hs h
  · rw [← vb,← vc] at h
    exact yn _ (List.mem_sublists.2 hsub) eq (vl h)
end Theta
end Base1007
namespace Main1672
abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
lemma lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
lemma lxor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp; omega, hu, hT⟩
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def raw0 : Sig := (0xc4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0x15115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0x218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xc50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x1a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x60000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x2a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0x2883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x6c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0x1100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0x3703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0xa00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x3383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x3403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0x3c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def symKey1 : Nat := 0x32799cc653399bc965b2b9acee5e25108bc5a2b1488c66271887c3ab558afd7abb5cacd86b760abd5a9d4ca9d4aa350a6d569f54a5d2a3d1c91c8a43208ec963f248dc6afd7cc1e0b0380bee16ff84bddeae570bbddaeb74b8de6e778b7dba0d0485c2a130882c360f0c81c0a6d349dcea73389acf66f3c99cca552897cba5b2c94cc6573093c9acd64b5daad368b2db6cf6cb1d8b1588c7e3b1b8cc4e471790c3e1a8540a3d1a8b44a0d2687489fcf90a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
def symKey2 : Nat := 0x32995cce6b3796c9e63399dcbe4a411f8ec6a43259247a471b8e48a592b94c9a5b31984aa5f27944bab95bacd5abb61b056abf57ac57ad167b2d8ad36db659ad763b25aae973b8dbaeb79bc5caef6fb85da71379acca733d9e4da77339a4ea291388c3a2b198c44a2f0f8845aa14fa6d2aa355aa53aa74ba654b017fbedeb0385c25fb077bbe60b198bc4e1b1b91c862b1f87c463a8943a0cfa8b49a450a8f3fa051a110782c0a130d8641a17038242972b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
def posKey4 : Nat := 0x5dad9eeb158ab158f678bad3e9f4ca6528947a365b2d369bb5da7c3b1c4c85f2d96caa5567144a24d269349a4d269349a4d269349a3c1b35c6231160b190271389c4e271389c4e271389c4ed56806834150a84020100804020100804020100835196cb62b15747b3d9d56070382e166b74f278b45a2a1515a90480ec76981a8d4602b15a304c26130984c26130984c2613099369648a552a8e0683410080402010080402010080402112893a1d0743a3198ce6592c8a854502815cae532998032192b1489c05028140a05028140a05028140a38178bc6e140a0a4520c060a00402010080402010080402010082e0a0501c0e070381c0e070381c0e07038442209020100804020100804020100804000000000000000000000000000
def negKey4 : Nat := 0x5bac9e6ed56ba552f376ba5e69a76a55d29179bb5a8e967bcdda77391b8c05c6a1599e52653149cf376b5184b74d1dce456260df2437193519e2d650a18af376b5184b74d1dce4561b89724d467b282cc508bcddad4612dd3477391586e0ec93519eca653156eb23b9c95aa9372dd64b7592695a56549495aa946a686e95488c85a8d14225e6ed6a2dd34873b9c8ac3712e49349548a692a8d44825e6ed6a2dd34873b9c8ac37036491a893b9c8ee373b980e4722b1b8506e27180ac5c29180b8162b1489cf376b516e9a3b9c8ac4c1b80f2437190b46e32088b4502d048a1e6ed6a2dd3477391586e25006482c1104bcddad45ba68ee722b0dc1c06c9058220979bb5a8b74d1dce4561b818079279bb5a8b74d1dce4561b80c0192
def posKey0 : Nat := 0xf68011960702a38581a189545653038984c260ca389a35178984e080d1d0080526acc582a0d041582903bd120293ab406a742a8eca4cb1d89c542f1325136101889da0086981c4c8e56250aa31480bc0e05028146a8e13864a605268112874040984e38561c12810161500ef415950e6d00c9d0629e1834d3c4d3814c0a1a4d840aa4d68134aa10029c4a85369b2ce01a080984c260c9c408354a098102729a7c9a05020f0a8902981c52ac081d854ac7b3406a9f659ed9c553d8212094130bcf80769821a027188404c71148bd96d3152502005028146a71040643405021345e9f1389810b6148ac5e072a0b02076380b1eed00ca7da63a758c47404158680a533e01d9604
def negKey0 : Nat := 0xe076480d92c901984c2193285acf292a522b23bb3ca4b2391c994a91b9dc0603652c9e6774d0395237033cd1a2d3933c647229268a4f31bb08503216ba534cf67b3c1d920364b240661308b8e92933c5a280b0dceecf168dce472748a1647743a1dd237799dd340e142c80cf346948e4cf2e1c85a9a16bcd64c254970a4ca4d33d9ecf076498592c93080c0648949d2cf650a064374d33d943779bcca42859268984c290dce49a3b83850b2611c8dce979b3d22f3651dd9472590195291748b4eecf67b3c1d926164b24c2030182c2d6533dd2a92e2c934cf74ac9e6f316aa46e9a128945ab239268ee0e548dd847237329e6cf0b3cdd277749c86e061405994523bb3d9ecf
def rawPermCodes : Fin 12 → Nat := ![0x876543210, 0x267143850, 0x374268501, 0x364872105, 0x547068321, 0x146072385, 0x846375012, 0x247361058, 0x64175832, 0x74561238, 0x567840123, 0x176240583]
def perm1 : Fin 9 → Nat := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
def perm2 : Fin 9 → Nat := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
def gOfV : Fin 9 → Fin 12 := ![0, 2, 6, 10, 0, 4, 2, 4, 8]
def recipeFuel : Nat := 12
def recipeBuckets : Nat := 128
def recipeWidth : Nat := 8
def recipeMask : Nat := 255
def recipeEntryBits : Nat := 48
def recipeEntryMask : Nat := 0xffffffffffff
def recipeShift : Nat := 0x1090409000301000500000002030803000000000101000201000c150a060404010000000000020000000300000d00010000000000030000010000000000030000000200040000020200000001010505000002000005050201010000000001000b0000010104000000010200000000000000000000000102000000010802
def recipeData : Nat := 0xc2900000bc36c29000000000000000000ac6c21000000000000000000000000000c1bc19c640000cac6c24900000000ac69000000cac2970000000c4c630000c1cac6230000000000a300000bc19c64000000cac2360000000b1c64000000cac633000000000c230000cac2c634000000000c3900000000ac16c3bcac297c29000000cac3640000000c9c160000000c6c2900000bc63c140000000c1c36000000cac2610000000c4c2300bcac297c2900000000ac13000000000001cbcac297c299000000cac16900000bc29c1400000cc13c6400000cc36c2400000000000000000000ac19000000cac64200000bc14c2600000000000000000000000200000000000000000000ac630000000c2c6300000c4c1c9600000bc94c160000000000000000000000000000000000000000000c2c4100cac9c14c9400000000000000000000000000000000000000000000000000000000000000000cc92c64000000000000c1bcac297c2900cac2c41c24000000000c3400000c9c2c61000000cac264000000cac16100000000ac120000000000040000000000000000000000000000000000000000c1cac9270000000c4c6900cac2c63c26000000bac6340000000000070000000c9c1400000000000600000cc19c2400000000000000000000000000000000000900000000000000000000000000000000000000cac4c63c460000c1cac4150000c3cac638cbcac927c925000000000000000000cac6380000cac2c631cbcac297c2980000c3cac92700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ac940000c9cac145000000cac14500000000000000000000000000000000ac26000000000000000000000000000000000000000000cac36600000bc16c260000000c6c410000cac2c6380000c3cac1450000c1cac269000000000c1400000000ac2400000bc14c64000000000c640000000000050000000c3c140000cac2c63900000000ac6400000000ac14000000000000000000000000000000000000000000ac6c41000000000c240000000c9c360000000000000000000000000000000000000000000000000000c9cac461000000000c2600cac2c46c2600cac2c63c63000000000000000000000c940000000000000000000000000000000c1c390000000000000000000000000000c9cac4660000000000000000000000000000c4cac297000000000000000000000000000c7bc19c64000000000000000000000000000000000000c4bcac927c92000000cac46100000cc41c3900cac4c63c630000c3cac4610000000000a90000000000a6c6bcac927c92000c3bc19c64000000000000000000000000000000cac623000000000000000000000000000000000000000000000000000000000000000000000c120000000000a400000000ac340000000000080000000c3c920000cac2c64300000c3c6c210000c1cac622000000000000cbcac927c9220000c2cac4150000000c3c1200cac3c14c34000000000000000000000000000000cac1630000000b1c2600000bc14c240000000c9c34000000cac644000000cac14400000cc26c39000000cac639000000000c63000000cac6430000000000000000000000000000000000a2000000000000000000000c19000000cac466000000000000000000000000000000000c16000000000c130000000000000000000000000000000000000000000000a100000cc14c2600000000000000000bc26c3900000000000000000000000000cac2c63c2300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000bc41c39000000000000000000000000000000000000000000000c6900000000000300bcac145c140000000c1c92000000cac3620000000c6c2100000000000000000bc12c9400000000000000000000000000000000000000000000000000000000ac290000000c2c64000000000000000000cac64900000000000000000000000000000bc19c24000000000000000000cac631000000000000000000ac2c640000000000000000000c4c29000000bac641
def wireCount : Nat := 161
def wireEntryBits : Nat := 10
def wireEntryMask : Nat := 1023
def wireTable0 : Nat := 0x3de7fffffffffffc003fffffffffffc000003fffbdefbc077c0077ffbef7bbddf7bdbb03fd83c1fdd003f07bfef41de1bf7b802f1bf000000000ffffff000ffffffffffffffffff39cff9fe73ffe7f937fff91dffff9fbf2fff1faffffff3e39ffff8cfbffffff7d77c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fbdef777def76e8000003ff7fdfef0000000001fffefeffb2ff000000fff000ffffffffffffffffffffffff00000000000000007def7bffdf7bffef7bef77bbddf775efbbef7bdffef7bffffef3ffffffffffffffc003fffffffffffc0000001f07dfe83fef03dfdf7bdc0f03de1df7bef77bbeefbbae81e07fa0fa183dfd86fceffffffffffffffffff000000fffffffff000f7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3bcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7003ffbb0001ffef606ff7600f77fdf7a0037ff768003b7f000000000000000000000000000000000000000f87ff807f1fc3ff803e180103ff8000000600007c620801207e1040021ff81000480000000003ffc000003ffc000000000000000a52fe4294ff117e40c630000a3181014bf9440188a03028a7ffca12004311004800fff0000000000000000000000000000000004a53fa1295fc89fa03e8800009fa0014a7f48007c220829257ffa420001f81002887ffc003ffc000000003ffc000000000003ffd284a28425092252904a128982528b37fffffc00902414fffffffffe02052120d020000000000000000000fff0000000000000006018a000c0280c5003e140303ff8240318633007c4a0407f8fe11fc821ff8501173c003ffc003ffffffffc000003fffffffffffff6f837b7e81dfc36e0dc37f6fc37e2884108bdc1f07c717e1f805f1df7c3c3f9feefffffffffffffffffffff000fffffffff000f7bc87fdee23fe47f91f47fbbe47f47fffffff723c8f4fffffffffff75e4747d1738003ffc003ffffffffc000003ffffffffc002d6b017b5a80dd816e05c1766d817408000003dc0f03c30000000001dd781c1f0d0cffffff000fff000000000000ffffff000000ffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff120034c000000000003fffffc003ffc000003fffffc00000000000000007000e73300016e80000016600554d0000000001768002b7b18e000000000ffffff000000000fffffffff000318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff436dffffffc003fffffc003fffffc003ffffffffffffffffffffffffe5fcbf4338ff27efe32fe7f3fafffefc731cff3be6cff7fdfbbffff000fffffffff000ffffffffffffffffff7bdffbfef7ffeffb77fffb3fffffbfffffffffaffffff3ffffffffffbffffff7c01c000000000000000000000000003ffffffffc6018a030c0318c600f8820300fe2621802980c1f20cc4306018cc30c60fe46d9003000000000000000000000000000000ffffff18c7f8fe31ffe3f80220880c038818920012090442199241806090c118388096753ffffffc003ffc003ffc000003fffffffffffffffffffffffffffeaffe33f4ffffe25adfdaaddff8ee7b7f5ffedf8df7ffc6f9143000000000fff000fff000000000000fffffff93e290df20c7f190a3108fc3f8c7882144221146411145f87f017c179f8c09e4084000000000000000003ffc000000000003ffca02a20014090152004a52050fd283214bf9440091241428a7ffca120a7d2120df73ffffffffffff000fffffffff000000ffffffffffffffffffffffcff9fefe7ffe7fdffffff9dfe7f9fffffffffff9fbffcf9ffcc7fffffffffffc000003fffffc000000003fffffffffffffffffff1fe3f899a7f8bf7fffffe33f8fe3efffffffffe22c7f3e0f831fff000000000000000ffffff000000000fff4a53fa1295fc89fa07e0f80441f80f918c31908fc3f0f230cc318c688a1f8f83e087ffc000000000000003ffc000000000003fffe8fa2857d092fd28048120108520324630c64009024148c330c631a02452120df6fffffffffffff000ffffff000ffffffffffffffffffffffffffffebffceff3ffffcdffffffb77febbdffffffffffb7dfff5bf75fffffffc003ffc003ffffffffffffffffffffffffffffffffffffebffff3f5fffffe5effdeefffffeffbff7ffeffaffffffefffb0fffffffffffffff000ffffff000000000000ffffffffffffffffd610f702e0840779cc19dccc23cceb306c10cc3c83084e418f38000003fffffffffffc000003ffffffffc0008420842108211045effc0feeffffc1b9dfb99cdff09c173cdffdce5dd7ffc5f038c000000fffffffff000000000ffffff000000210821084208441173ff0313bfff806c67ec4627fc26018237ff601625fff1603e03ffffffffffffffc000000000000000000003ffffffffffffffff48421c0a821001e31063311088322c41904310d004210100fbcfffffffffffffff000ffffffffffff00000027c9f7fa4ffbc4f7f7fff713ffff877deffddeefffeeeba27fffe83ea7ffff61bdfffffffffffffc003fffffffffffffffffffffffffffffffffffffbffffbfdffffff7fffffefffffefffffffffffeffffffeff3cf000000ffffffffffff000000fffffffffffff93e290df20c7f197bff0bffbffff8ee77ee6737fc3715dfb7ff77d77dfff1fe4b0c000003ffc003fffffc000000000003ffffffe0f82017c010fc2160842ffafc21e3a9412994411054557e9f815f55e7c20379921fff000000fff000000fff000000000000ffffb3eab1df62cff5b03f0480421fc0c918c319007e0b05230cc318c68091fc58375cffffffc003ffc003ffffffffc000003fffffffffffffffffffffe3fc7f3f1fff1fe4e71cee77f9fe7f9ff3fc67fa7efff3e7f963fff000000fff000ffffff000000000fffffffb3eab1df62cff5b0bf148fc3ffc7c939c73b117e4b1567fcff19fe979ffc59f4ac4000003ffc003ffc003fffffc000000003ffc210fe00847f007e15f83ec1b07e03fa520a5523f0fd3c482a0852172287e3f0f900fff000000fff0000000000000000000000006318a318c628cc53023100303f8c20129452a0046400025fc7f097e021f8c0000404000000003ffc000000000000000000003ffca52fe4294ff117e408c62050fe302200110000119842400a1fc00100a7e30209131000000000fff000000ffffff000000000fff294bf90a53fc45f907f0f80461fc0f810c21108fe3f0f0208c3108488b1fcf83ff0bfffffffffffffffffc000000000003ffc003ffffffffffffffff68421faa8211c1eb506bb55088363d7590435ed544210170beefff000fffffffffffffff000fffffffff0006318a318c628cc537bff43fbbffff47ffffff737fca747ffffffffff75fff57d3cf7fffffffffffc000003fffffffffffc003fffffffffffffffffff9ffff8ddfffebf7fffffebbfffebefffffffffeabffffe8f6df000ffffff000ffffff000fffffffffffffff9ce75ce739d733acfc0fbfffde03fbee73ce6ff81f5fbdcf33ce7397fee03afee4b3ffc000003ffc000003ffc003fffffc0000018c628c6318a3314c8ffd0044fffe1056bfd6489ff2890acb7ffeb1a897ffd484ba0fff000fffffffff000fff000000000000000ffffffd8c6aacc53fffffffffffffff9ce39d407e1a44338ee39ce7c011fcd412483ffc000003ffc000003ffc0000000000000018c628c6318a3314c0fc1000087f0104630c6401f828108c330c631a0047f1404101000000000fff000000000000000000000ffff93e290df20c7f1903f0080421fc088004200007e030101084310440091fc1827673fffffc003fffffc000003ffffffffc000003fffffffffffffffedb5ad40782d60cc210423bb6edbaa8411042109a1c2ded82dd3ffffff000fffffffff000fff000000ffffffffffffffffffffff9e10bdcce0845bb084108ddc235dbe1044108425db084adef70bfffffc003ffffffffc000000000003ffc003fffffffffffffffe68421722821140c2104235508836384110421095442101705df000fff000fffffffff000ffffffffffffffffdff7deffbdf7fbdbef7bdfdffbdfba210422ffdff7fbc5f87e017c7fffbfbfeedffffc003fffffc003fffffffffffffffffffffedffec7fdff3ffedbfffebfdffffff7fffffceffffcfdfffffffffeffffffeff12d000000000fff000000fff000ffffff000fff290aa908522c455923ff48153fff8c852fe51227fcb250a29fff284a2dfff5a356f4003ffc003fffffc003fffffffffffc003ffcb72ff7a96ffd17f6dffff457fffe3e94bf947bbffffbe28a7ffca13abfffff8f4f3000fff000000ffffffffffff000000fffffffcfffce7f9ff3ffc9fe1fdfcfff87fa318633ddfc7fdfc7f8fe11fcdfbff8fdffef7ffffffffffffffc003fffffffffffc003ffd3f4fffea7fff27ffdffbfc9f27febffffffffbbfeffbeffffffffffa387fff8f5bd000fff000ffffff000ffffffffffff000fff0dc3fdea1bff41fdb7f6fd05c1fd8fa108211eeffbfef8208821084e8e1fffe3d2c4003ffc000003ffc003fffffc000000003ffc330ff38867fc07f25f83f41307e03e842084733f0ff3e08220842132287e3f0ffbcfffffffffffffff000ffffffffffff00000067d9f7facffbccf7f7fff733ffffa77ffffffeefffeeebfffffffffea7ffff61bef3ffffffffffffffc003fffffffffffc0000011f47dfea3fef23dfdf7bdc8f23de9dfffffffbbeefbbaffffffffffa183dfd864d3000fff000000ffffff000fff000000fffffffcff5ce7f9d73fac9c21bdfcff087ba210422dd8475dbc5f87e017c5fbf08aded30c003ffc000003fffffc000000000003fffffff2f83397e01cfc32608437f2fc21e2884108b5411074717e1f805f15e7c20379ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe0ffeec1f87ffbd83bfddfc3fdff7de821dffdda1f8fdfff7bfffffffffffffffffc003fffffffffffc003fff19ffffc6ff8dffffc9fffffffc9fffffbbffff1bcbfffffffdedfffffcdf2fceffffffffffffffffff000000fffffffff000f7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c177c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fffef777ffff6e909f903ffffdfef2085ffc801fffffeffb5ce000fff000fffffffff000000fffffffff000b5ac25ed6a0b7615bbff05d9bfffd02427e40f77fc2f0c8217ff200775fff17c3fbbffffffffffffffffffffc003ffffffffc003def29ff7b8aff95feffd1feeffffd1fffffffddff2bd3ffffffffffdd7ffd5f4ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe8ffeec9fa7ffffffffddfc3fdfffffffffffdda1f8fdffbebffffffffc003ffffffffffffffc003ffc003ffd31bfffccee99bf6319fff318dd9ffffffffec4335bffffffffffff91899764da000fff000000ffffff000ffffff000fff000ffe444ffff133224fc8425ffc421523ff9000ff9104d2ffff8840007fe42225cbb8bffffffffc003ffffffffc000000003ffc0035ad21bd6b08ee91b64211faa2109d1fffffff54802353ffffffffff540101174fceffffffffffffffffff000000fffffffff000f7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3adbffffffffc003ffc003fffffc003fffffc0005b175bf8b7ff8b9b510bdc2b08425dff227f7f222fffaf85a10be2fe48847fd6006000000000000000000000000000ffffff0001004000c200c6200004200080210900600860300883300c100423083102111b43ac7ffffffffc003ffc003fffffc000000003ffc3b0ffbc877fe07fb5f83fc1b07e03fe720e7733f0ff3ec83a08721f2287e3f0f001000000000000000000000000000000000fff08022800100c011803e0080401f8088000200007c030100080210040081f818274c7fffffc003ffc000003fffffc000000003ffffffffffffffffffe1fc3f01187f03e4630c6633f8fe3e8c330c631a22c7f3e0fd3dffffff000fff000000ffffffffffff000fffffffffffffffffffa7fffc157fff8f95aff59aeffffafab2dfffac6aafffffa3fc83fffffffffffc000003ffc000000000000003ffffffffffffffff0c631888a318917fffffe1188a232fffffffffe004311004f2cffffffffffff000000fff000ffffff000000ffffffffffffffffe3ffc6333fffa45ffffffa67feaacbfffffffffa25fff52113cc003ffc000003fffffffffffc000003fffffe739ff39ce7fccff27f83f73307e17e842084777f0ff7f08220842137687e3f7f5ff000fff000fffffffffffffffffffffffffffbdeffdef7bff77fdbffffdddffffdfa52fe51ffffffffca29fff284fffffffffc4b0000000003ffc000003ffc003fffffc0000008422842108a111448ffd0044fffe1014bf94489ff289028a7ffca12897ffd484b3dfff000ffffff000000ffffffffffff000fff6b5bfb1ad7fccdfb67fffa377fffafdffffff2affff2f3fffffffffaafffffa3fbcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7423ffbb2109fffffffff7680f77fffffffffff768103b7f4d3000fff000000ffffff000fff000000ffffff9ce75ce739d733ac9c00bdccc0005ba000000dd8035dbc0000000005da000adec5fc000000003ffc003fffffffffffffffffffffe5ffe43fcff1ffe4bfffe3f5fffffe1cff9cceffffcfd3fe7ffcff2ffffffeffeb0fffffffff000fff000ffffff00000000000046d1d6f28df388e6d508f722c842277ffffffcca03ccebfffffffffc82040e41977c003ffc003ffffffffc003ffffffffffffffff7fdf7bfef7dfef6fffef7f7ffffee98df98bffffdfef37e5ffcdf1fffffeffb490000fff000000fff000000fff00000000000004c154e209d300a49400b500c000032000000cc8034ca8000000000482000a40977c003ffc003ffffffffc003ffffffffffffffef7bdf7fdefffdef6fbdef777def76efc027c3ff7fffeff84010be21fffeffffb55d000fff000fff000fff000fffffffff000fffad6b6d095b0855bdafffacd57fffca8427e4027ffc22bc8217ff20026ffff12afdf7fffffffffffc003ffffffffffffffc003fffbdefbc677ca377ffbfffbbddffffbb7fffffc9fff28bffffffffffe9bfffd4afa24fff000fff000000000fff000000fff000000421082188428c842414a42220a52a45ffffff20288a243fffffffffa002515213fe7ffffffffffffffffffffffffffc000003fffffffff477e8a77ffffffffffffffffffffffd1fdd613fffffffffff1bf7bb12ff79ffffffffffff000ffffffffffff000000fffef7bef11df209dffefbdeef77def6edffffff07f7480fffffffffff86fdee40bca00000003ffc003ffc0000000000000000000014a524b000208000145294caa294ad5a1082110000410042088210850000021007d9000fffffffffffffff000ffffff000000fffffffffc15b8215bdffffffffffffffe84208447d7504bd08220842146fdae84ae09bffc000000000000003ffc000003fffffc000000000fa91f7a908000000000000005ef7deee0a2bed0bdf77def7ae40945ed4559000fff000fff000fff000ffffff000000fffad6b6d015b0015bdaeb5acd575ad4a800000007d7400bc00000000006fdae00ac2dc000000000003ffc003fffffc003ffffffffc631fe3f8c7ff8fe05f8be4330fe27efc22fc7e3f2fffcf86218fe33e68fe7fdf59e000fff000ffffff000000ffffffffffff00015c575fe2bffe2b5b6d6b509c2b5933f009f0fedbbffabe10042f887962b7ff4bf9fffffffffffffffffffffc000003fffffffffffffffffffffffff6def7ffaff7bf7ffffffff5bbfff7fffffffffffe7f77ffdfa6fffffffffffffff000fff000000ffffff000ffffffffffffffffd35ad72aaad6b57fffffffc6abffcbffffffffff912d5ff53d8ffffffffffffc003fffffc000000003ffffffffffffffffffffff2ce73bf8ff39f37fffffe5599a677fffffffffe5e7f3127ddc7ffffff000fffffffff000000000fffffffffffffffffffffffff9a739dfcbf9cf9bf94dfafd4efff9fffc7f2ffe7f9f9dffe41cc000000000000003ffffffffc000003ffffffe1ffe01fc7f0ffe03f87e3f1ffe1fe0c618cc67f1fc7d1fe3f847f27effe3e7f14f000000000fff000fff000000fffffffffffff93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be556c003ffc003ffc003ffc003fffffc003fffffff5fdb417ec10fef6bad6b3f5feb5ea08410885f5d046f17e1f805f05ffeb827baf7fff000fff000ffffffffffff000ffffffffffafffafff5fffffa5febfbfefffaffffffffff9fcffff7fffffffffffbff9fffeadfffc003ffc003ffc003fffffc003ffffffffd6b5febfad7ffafe95fabecbb2feafffffffffe3f2fffcffffffffffe68fe7fdfa73fff000fff000000fffffffff000000fffffffa7ffa17f5fcbffa4fe9fafe7ffa7fdffffff19fc7f1f7fffffffff9fbff8f9fc3dc000000000003fffffffffffc003fffffffffe3ffe3ffc7ffffe07f8fe7f3ffe3fefc63fcfe7f3fffdffe3f8fff3feffe7fffbeffff000fffffffffffffff000fffffffffffffbbebbfff6ffff5b7bff5bffbffffdffffffffb7ffff57fffffffffffdffffff6ebbffc003ffffffffc003ffc003ffffffffc001ce72cffb9bffb94dcffd4ceefffed5fffffffe9ffffd0ffffffffffed7ffffd4b6ffff000ffffff000ffffff000fffffffffffffb3eab1df62cff5b6bff4aff3ffffcdffffff337fcb357fffffffffb7dfff5bf473c000000003ffffffffc000003ffffffffffffe6f8e7ffcbfffc64effc67f6ffffe6fcdffcbedffffc5ffe5fffff1ff7fffff9ae7fff000fff000fffffffff000000ffffffffffabe9afff4ffff4a596b5bfebf5afdffffffff92cfff57fffffffffff9f59fff7ce3fffffffffffc000003ffffffffc0000000011d479c423c8223df9e73988d239c997fffffc1bcc203afffffffffe018399006fbefffffffffffffff000fffffffffffffff00057d5f7feafffeaf7f7def72bcaf7b77fffffffefbbffebffffffffff962f7ff5bdeffffffffffffc003fffffffffffc003fffffffdffbc57fc92ffffbef7bbfdffbdfb7fffffc5fdd247ffffffffffe5fffb927f5df000fff000fffffffff000ffffffffffffffffdff7dfffbffffbdbef7bdfdffbdfbbf10df2ffdffffbfff87e2ffc7fffbfffede60003fffffffffffc000003fffffc000000003ffffff002e0802d7ffffffffffffffa1082111b4c412a420882108501829a1020c7000000000000ffffff000000000ffffffffff8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe5460003ffc003ffc000000003fffffc000000000150594002c0002d69a52900502940800000001b4c002a0000000000018298002aa6fff000fff000fff000fff000000ffffff000529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff5361bfffffc003fffffc000000000003fffffc003fffffffffffffffe494a54228a5244fe127e3f12affe2fc5114bf29e44a57fd0500000fff000fff000000000000000000000000ad6b6d015b0015bd821084002084000000000044200088000000000001084000298fffc003ffc000003fffffc000000003ffffffe8fa2857d092fd2924a52bf8fd29f37fffffc44912455fffffffffe5e7d2127dd43ffffff000fff000fff000000000000ffffffffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e5400003ffc003ffc0000000000000000000000001705d7a82f6d02d608421000021000000000211088222000000000000021000011c000000000fff000000000fffffffff0000002948610a5318443127ff20157fff82052fe402affc6220a29fff2002affff3208a60000003ffc003ffc000003fffffc000000003ffffff294e480083ffffffffffffffb5ac211aa4451086aaea31085ab908a902a38fff000fff000000000fffffffff0000000006b50c21ad7308862658c62374c63265ffffff2ab10c063fffffffffaae462601bb6bffffffffc003fffffc003fffffc003ffc003ffd11bfffc4ee89bf2109fff1085c9ffe46bbfe44134bfffe2135edff9088972443000fff000000000fff000000000000fffffffc3f0c25f8453f8c8a318cfc3f0878929452a95466199c5f87e017c179f0809e44f4000000003ffc000003fffffffffffc003ffca52fe4294ff117e49fffe055fffe3e14bf944abfffcbc28a7ffca12abffffe8fa31fff000fff000000000ffffff000000000fff4a53fa1295fc89fa47e8fa2649fa2fdffffff08fc3f0f3fffffffff88a1f8f83ecb3ffc003fffffc000003ffc003fffffc0000018c628c6318a3314d8ffd08ccfffe917fffffc89ff2890fffffffffe897ffd484458000fff000000000fff000ffffff000000000ffe1447fff5110a4feb5acffd421421ffd52affd7659bffff9840107fec22208bbf3ffffffffc003fffffffffffffffffc00000318c618c63186631bffffff8f61cf9dfffffffffffffffffffffffffb1a1cfda6e60fffffffff000000ffffff000000000000000c63186318c6198c6cb39cee21842645ffffff9566699dffffffffff8408404091bf0003fffffc003fffffffffffffffffc0000021084108421044213ffffff0f41cf1dfffffffffffffff690e43da47b1a1cfda6440000fff000000000fff00000000000000000084210421084110848a318cc0100040129452a95466199c0401000100408000083403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000280000000fff000fff000000000000000000000ffffffc000820000ffffffffffffffe8420844000104010822084214000008401100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020a20fff000fff000000000fff0000000000000004210821084208842410842220842245ffffff002008043fffffffff8000404010060000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff908880210c000000000fff000000000000ffffff000000210821084208441123ff00113fff800427e40227fc22008217ff200225fff1200218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0043000000000000000fff000000000000fffffff83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e40c4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f
def wireTable1 : Nat := 0x3fff3af3af3af3af3af3af3af3af3af3af3af3affffffe07fc007fffffffffffffffff83ff83c1fff003f07ffffc1fe1ffffc03f00077d77d77d77d77d77d77d77d77d77d77d77d0001f87e00ffe0f803fff8003fff879f07ff0f87fffff3e007fff80781fffff1fffff93f93f93f93f93f93f93f93f93f93f93f93ffffffffffffffffffffffffffffff8000003ffffffff0000000001ffffffffffff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffdf71f71f71f71f71f71f71f71f71f71f71f701f07fff83fff83fffffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc7fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3fffe5be5be5be5be5be5be5be5be5be5be5be5bfffffffffffffffff003ffff0001ffffe07fffe00fffffffe003fffff8003fff000d61d61d61d61d61d61d61d61d61d61d61d61f83ff801f0fc1ff803e000003ff8000000000007c000000007e0000001ff800000014254254254254254254254254254254254240007e00003f003e000000000000000001f800000000000001ffc0000000000000005495495495495495495495495495495495490001f80000fc00f803e0000000f8000007e00007c000000007ff0000000f8000000006c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000000063063063063063063063063063063063063000000000000000003e000003ff8000000000007c000001f87e007c001ff80003ffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c307e1f801f1fffc1c1f8fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3ffea82a82a82a82a82a82a82a82a82a82a82a83fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8000f69f69f69f69f69f69f69f69f69f69f69f69ffffffffffffffff03ff00003fff800007e00007fc00000007ff000001fff0003ffc2102102102102102102102102102102102100000000000000003f003ffff0001ff8000003fe00ffff0000000001ff8003fff00037d37d37d37d37d37d37d37d37d37d37d37d0000007e00ffe00003ff00003fff801f07ff0f87ffff03e007fff80781fffff00003d53d53d53d53d53d53d53d53d53d53d53d53fffffffffffffffc0f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc700077f77f77f77f77f77f77f77f77f77f77f77f0001f87e00ffe0f803fff8003fff879fffffff87fffff3ffffffffff81fffff1c00010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e00000007007007007007007007007007007007007000001f87e00ffe0f80000000000000000000000000000000000000000000000000003dafdafdafdafdafdafdafdafdafdafdafdaffffffffffffffffc0ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00000a40a40a40a40a40a40a40a40a40a40a40a4000000000000000000000000fc0000001f800000000000001ffc000007c00000000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7fffffffffffffffff03e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ffffffffffffffffc0f83e00003e01e7fffffc01f0fc3cfffffffffe0003e3e070005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81c002002002002002002002002002002002002003e0f80007c0007c00000000000000000000000000000000000000000000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff007c3ffff81ffffff007fc0003fffffffff879fff00e0003dbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbffffffffffffffffc0fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3fffff94f94f94f94f94f94f94f94f94f94f94f94fffffffffffffffffc00ff83c00007fff81ffff803ffffe07800f83f86000ff1fffc3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec0000000000000003fffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fff0f90f90f90f90f90f90f90f90f90f90f90f90000000000000000ffff0783ffff807ffffffffffc0f0fe07ffff83f87fff0703fffe43e43e43e43e43e43e43e43e43e43e43e43fffffffffffffffff0001e0f000001ffe07fffe0003c3f81e003e0fe180001c0fff7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffe07ffff83f87fffff1c003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3ffff8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fbf83e0001f0001f00ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffe2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2cfe0f80007c0007c03f0001ffffc01e1ffe07fffe0003c3fffff83ffffffc001f8000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80000003d9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9ffffffffffffffffc0f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f000863863863863863863863863863863863863f83e0001f0001f0003e0007c3ff8780000000007c000001f87e007c079ff800e3ffd7517517517517517517517517517517517500007e00003f003e3ff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc70000230230230230230230230230230230230230000000000000000000000003f000000000000000000001f87e007c001f0000000014854854854854854854854854854854854840007e00003f003e000000000fc00000000000000000000001f80000007c000000005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81ffffe4be4be4be4be4be4be4be4be4be4be4be4bfffffffffffffffff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8fff0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0000000000000000ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e0003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe000fffe1e7fffffc01fffc3cfffffffffe007fffe07ffffbffbffbffbffbffbffbffbffbffbffbffbffffffffffffffffffc1fffffff07fffffffffff83ffffffffffffffffff07fffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe000000007c000000000000000000f8000000010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e0000000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80003ffff13f13f13f13f13f13f13f13f13f13f13f13fffffffffffffffffffffe0f03fe1f8000003ffffffff0000000001e183fffc7ffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffffffe03e03e03e03e03e03e03e03e03e03e03e03fffffffffffffffff0001fff0001e18000003fe0003c30000000001ff80001f8ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffffffffffffffe000000ffffffffc1f87e007c7ffffffffc0035ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ffe0ffe007c3f07fe00fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3f000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0003ffdfb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb41f07fff83fff83fffffffe0ffffe1f801f803ffffffff0001ffc001e1fffffc7ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffe0fffffff87fe000000fffc3fffc1f87e007c7ffff8ffffffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7fff7c47c47c47c47c47c47c47c47c47c47c47c407c1fffe0fffe0ffffffff83c0ff87e000000ffffffffc0000000007860ffff1fffdf11f11f11f11f11f11f11f11f11f11f11f101f07fff83fff83ffff83fe0f03e01f8000003fff0ffff0000000001e183e3fc7fff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffffffffffff87fffff1fffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7ffffa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fffffffffffffffffc00ffffff007fe000000ff803fffc1f87e007c7fff00ffffffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff0001ffffc01e18000003fe0003c307e1f801f1fffc001f8ffffd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6ffffffffffffffffffe0ffffc0f87ffff81fffffc3fffffff800fffffe0f8ffffffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fffafbafbafbafbafbafbafbafbafbafbafbafbfffe07ffff03ff07ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffffb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ffffffffffffffffffffffffffffff801f803ffffffff0001ffc001ffffffffffffae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9fffe07ffff03ff07ffff07fffffff86007e00ffffc0f0c0007ff0007fffff07e3ffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8ffffdffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffffe0ffffc0f87fffffffffffc3fffffffffffffffe0f8ffffffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffa92a92a92a92a92a92a92a92a92a92a92a92fffe07ffff03ff07fc0007ffc000787ff8000ff8000f0ffff8000007fe00007e3ffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbffffe07ffffffff07fc1f07ffff07f87ffffffff83fff0ffffffffffffff07ffe3ffde51e51e51e51e51e51e51e51e51e51e51e501f07fff83fff83fff003fe0f00001fffe07fffe00fffff81e003e0fe18003fc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffdf51f51f51f51f51f51f51f51f51f51f51f501f07fff83fff83ffff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc7000040040040040040040040040040040040040000000000000000003e0000000f8000000000007c000000000000000000f80000003d13d13d13d13d13d13d13d13d13d13d13d13fffffffffffffffc0f83e00003e01e000000001f0fc3c00000000000003e3e07000f6df6df6df6df6df6df6df6df6df6df6df6dffffffffffffffff03fff8003fff878007e00007fff0f00007ff000001ffff81c003c6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6ffffffffffffffffc000000000000007fffffc00000000fffffffffe000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff00003fff801ffffff007fc0003fffffffff801fff0003ffff13f13f13f13f13f13f13f13f13f13f13f13ffffffffffffffffff83ffff03e1ff8000003fff0ffff0000000001ff83e3fffffffedfedfedfedfedfedfedfedfedfedfedfedffffffffffffffffffffffffffffffe007e00ffffffffc0007ff0007ffffffffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc00000057f57f57f57f57f57f57f57f57f57f57f57f0001f80000fc00f803fff8003fff879ffffff007fff0f3fffffffff801ffff81ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffff003ffff0001ffffffffffe00ffffffffffffffff8003fffffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffc0035bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bfe0ffe007c3f07fe00fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3ffff79f79f79f79f79f79f79f79f79f79f79f79f07c1fffe0fffe0fffc00ff83c00007fffffffff803ffffffffffffff86000ff1fffffbffbffbffbffbffbffbffbffbffbffbffbfffffffffffffffffffffffffffffff801f803ffffffff07e1ffc1f1ffffffffffff78478478478478478478478478478478478407c1fffe0fffe0fffc00ff83c00007e000000ff803fffc000000000786000ff1fffffd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fffffffffffffffffffffffffffffffc007c3fffffffff800003e01ffffffffffffce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ffffff81ff001fffffffffffffffffe007e0007ffc00fc0007ff00007ffff00fffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03f00001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003fff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbffffff81ff001ffffffffffffffffffffffff07ffc00fffffffffff87ffff00fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc000c7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7c000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc001d51d51d51d51d51d51d51d51d51d51d51d500007e1f803ff83e00f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc7fff7d47d47d47d47d47d47d47d47d47d47d47d407c1fffe0fffe0ffffffff83c0ff87ff001f0fffffffffe00000f807860ffff1c003cffcffcffcffcffcffcffcffcffcffcffcfffffffffffffffffc000001f0fc01e07ffffffe000ffc0fffffffffffe7c03ff8000f1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1fffffffffffffffff000000000000001fffffff8003ff03ffffffffff80000ff00003cefcefcefcefcefcefcefcefcefcefcefceffffffffffffffffc000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f37f37f37f37f37f37f37f37f37f37f37f37ffffffffffffffff0000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe000359f59f59f59f59f59f59f59f59f59f59f59fe0ffe007c3f07fe00f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f00086b86b86b86b86b86b86b86b86b86b86b86bf83e0001f0001f0003ff007c3ffff80007e00007fc00001f87ff07c079fff00e3fff38f38f38f38f38f38f38f38f38f38f38f38ffffffe07fc007fffffffffffffffff80000001fff003f07e1f801f01ffffc03f000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff83ff87ff0fffff803e0f87c3ff87f9fffffff87c3fff3fffffffffff9ff8fffc001d7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7c0007e1f803ff83e00f83e00003e01e7ffffffe1f0fffcffffffffffe003e3fc7000d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ff83ff801f0fc1ff803e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003ddfddfddfddfddfddfddfddfddfddfddfddfe0ffe1ffc3ffffe00f83e1f0ffe1fe7c007c3e1f0fffcffe1f83ff1fe7fe3fff000b7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ff83e007ff0ffff0003ff007c3ffff81fffffff87ffff03fffffffffff9fffffe0000dfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfc000001f803ff80000ffc0000fffe007ffffffe1ffffc0ffffffffffe07ffffc000087b87b87b87b87b87b87b87b87b87b87b87bf83e0001f0001f0003ff007c3ffff81ffffff007fc0003fffffffff879fff00e0002dfedfedfedfedfedfedfedfedfedfedfedffe0f801ffc3fffc000ffc01f0ffffe07c1ffc3e1ffffc0ffe1fffff1fe7fffff8000b3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3ff83e007ff0ffff000000007c3f00781fffffff8003ff03fffffffffff9f00ffe3ffd36d36d36d36d36d36d36d36d36d36d36d36c1f07fe003c0003fffffffe0f03fe1fffffffc1fff003ffffffffffe0183fc007fff7df7df7df7df7df7df7df7df7df7df7df7df07c1fffe0fffe0ffffffff83c0ff87ffffffffffffffffffffffffff860ffff1ffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ffffffffffffffffffffffffffffffff001f0fffffffffff87e0ffc7ffffffffffff383383383383383383383383383383383383fffffe003c0003ffffffffffffffff80000001fff003f00000000000183fc007000b37b37b37b37b37b37b37b37b37b37b37b37f83e007ff0ffff000000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe3ffd3013013013013013013013013013013013001f07fe003c0003fffffffe0f03fe1f80000001fff003f00000000000183fc00700031f31f31f31f31f31f31f31f31f31f31f31f0000007e00ffe000000000000000001fffffff8003ff03ffffffffff80000ff00003c53c53c53c53c53c53c53c53c53c53c53c53fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0000c00c00c00c00c00c00c00c00c00c00c00c00ffffff81ff001fff00000000000000000000000000000000000000000000000000020ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0efe0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f23f23f23f23f23f23f23f23f23f23f23f23ffffffffffffffff0000007c3f007800000000000000001f87e007c079f0000e0001c01c01c01c01c01c01c01c01c01c01c01c001f07fff83fff83fc000000000000000000000000000000000000000000000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000003383383383383383383383383383383383383fffffe0000000003ffffffffffffff800000000000000000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffea4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015b55b55b55b55b55b55b55b55b55b55b55b40007e00003f003e00fffe000fffe1e001f80001fffc3c0001ffc000007fffe0700055f55f55f55f55f55f55f55f55f55f55f55f0001f80000fc00f803e0f80000f8079ffffff007c3f0f3fffffffff8000f8f81c0001ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec00000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000000a92a92a92a92a92a92a92a92a92a92a92a92ffc0007fff000000fc00007fc000001ff8000ff8000003fff8000007fe0000003ffc37c37c37c37c37c37c37c37c37c37c37c37c0000000000000003fffffe0f03fe1ffffffffffffffffffffffffffe183fffc700001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffc3703703703703703703703703703703703700000000000000003fffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe00000000000000000000000000000000000003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000000002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000000c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
def frontierCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 341
  | 10, 1 => 12
  | 11, 0 => 253
  | 11, 1 => 230
  | 11, 2 => 81
  | 11, 3 => 6
  | 12, 0 => 25
  | 12, 1 => 34
  | 12, 2 => 34
  | 12, 3 => 17
  | 12, 4 => 3
  | 13, 0 => 3
  | 13, 1 => 4
  | 13, 2 => 4
  | 13, 3 => 4
  | 13, 4 => 4
  | 13, 5 => 1
  | _, _ => 0
def leafCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 339
  | 10, 1 => 12
  | 11, 0 => 223
  | 11, 1 => 228
  | 11, 2 => 81
  | 11, 3 => 6
  | _, _ => 0
def frontierSlotBits : Nat → Nat → Nat
  | 9, 0 => 104
  | 10, 0 => 114
  | 10, 1 => 104
  | 11, 0 => 124
  | 11, 1 => 114
  | 11, 2 => 104
  | 11, 3 => 94
  | 12, 0 => 114
  | 12, 1 => 114
  | 12, 2 => 114
  | 12, 3 => 104
  | 12, 4 => 94
  | 13, 0 => 104
  | 13, 1 => 104
  | 13, 2 => 104
  | 13, 3 => 104
  | 13, 4 => 104
  | 13, 5 => 94
  | _, _ => 0
def frontierData : Nat → Nat → Nat
  | 9, 0 => 0x151201e1500201421068099000151404803802014210680990004c1201e0380201421068099130161201e038020142106809a000150481e0340111022090099054280481e034011102209009a0541207840038020182209009a0f0160481e034020182209009a0e0160481e038010182209009a000150d01e0340101822090099054340a01e034010182209009a0002c0481e03401018220900990c0160481e034010182209009a0b0160481e034010182209009a0b0280481e034010182209009a
  | 10, 0 => 0x150481e0340101822090099000150a0120780d004060882402686c180120784003930018220680ab1803c0481e8f00e4c0060881a02ac94058120780e8e002018220680ab0e0160481e100022f0060881a02ac3805812078403405c018220680ab1b0380481e10002170060881a02ae34058120780e0085c018220680ab1b0160481e03802740060881a02ac3805812078404c074018220680ab250160481e10002018680881a02ad98058120780e008061a0220680ab1b0160481e03802019ac0881a02ad28058120780e008060881a8c00ab0e0160481e038020182206a2c02ac00000150481e100b44c05c0680990012805812078402d1300181a0268000e0160481e101301700606809a00114058120780e4c05c0181a0269140e0160481e039301700606809b300160481e1000e4c05c0181a026e180581207840039301700606809b000000e1280481e101300141a0264600581207840039e04c02206809b000600f0120780d781300881a026800250160481e100021702206809a2506005812078400085c0881a026c9405812078402d0021702206809b300160481e100b40085c0881a026c150481e820402d0021702206809b05412078408a0b40085c0881a026c0005412078402d0028902206809a05412078402d002172240881a026c150481e100b40085c7402206809b0009405812078404c0060881a0268940e0160481e101300182206809b2506005812078404c0060881a026c380581207908101300182206809b250160481e100b44c0060881a026d1405812078402d1300182206809b860160481e100b44c0060881a026c150481e820402d1300182206809b0541207908100b44c0060881a026c941803c0481e039300182206809b450600f0120780e4c0060881a026c600f0120792c039300182206809b660160481e1000e4c0060881a026e1c0581207840039300182206809b05812078408800e4c0060881a026e1c1803c0481e035300182206809b182180f0120780d4c0060881a026c380581207840781300182206809b000600f0120780d850060881a0268600f0120780d4c2140182206809b180160481e1000e840060881a026c00058120784003a100182206809a058120784003930840060881a026c600f0120780d4c2100182206809b000150481e100b4730060881a026800180160481e039cc0182206809a180160481e1000e730060881a026c150481e100b44c1cc0182206809b180160481e03930730060881a026e0c250160481e100020182206809b830380581207840008060881a026c380581207a08100020182206809b250160481e4b040008060881a026c1504a04078402d0020182206809b054127201e100b4008060881a026c007c0160481e038020182206809a7c094058120780e008060881a026c1504a000780e780020182206809b054127f01e039e0008060881a026c38058120780e770020182206809b000160481e039dc008060881a026815049f80780e2e0020182206809b055f40481e2d130008060881a026df0058120780e4c0020182206809b054127b01e03930008060881a026c15049e80780e4c0020182206809b05412078b403930008060881a026c160481e039dc4c0020182206809b250160481e039e4008060881a026c00058120780e790020182206809a058120780e4c1e4008060881a026c94058120780e6c0020182206809b058120780e781b0008060881a026c160481e039dc6c0020182206809b054125901e10002170060881a026c3805812079180085c0182206809b000160481e46002170060881a0268160481e101180085c0182206809b054127601e03802170060881a026c151201e1000e0085c0182206809b054120784003802170060881a026c380581207840009d40182206809b0e0160481e10002740060881a026dc00e0160481e101300142206809b0e0160481e4b0404c0050881a026c3805812078404c1b00142206809b000380581207840730050881a02683805812078404c1cc0142206809b0003805812079b8008050881a026800000160481e6e002014220680994a0160496407840008050881a026c38058127201e100020142206809b00038058126d00e008050881a02680000016049b4038020142206809900016049bc0780e008050881a0269280584807840038020142206809b4a0160481e1000e008050881a026c3805812079b84c0020142206809b000160481e6e130008050881a02683805812079604c0020142206809b0e016049b403930008050881a026c00058126d00e4c0020142206809a440380481e03930008050881a026dc4058120780e4c0020142206809b0e0160481e03930008050881a026c38058120792c6c0020142206809b0e0160481e6e1b0008050881a026c0005812079b86c0020142206809a0e016049b4039b0008050881a026c00058126d00e6c0020142206809a700160481e039b0008050881a026c16049bc0780e6c0020142206809b05812079b84c1b0008050881a026c16049b4039306c0020142206809b05412078402d130019ac0881a026c60058120780d2e0026a02206809b1803c0481e03402019a80881a026ca4058120780d008066a02206809b0e0160481e10002015a40881a026d14058120780e008056902206809b450160481e03802015a00881a026c38058120780e008056802206809b0f0160481e03802015a00881a026c160481e1000e008056802206809b000600f0120780d0099c0841a026860058125b01e1000e0182106809b180160481e1000e610060841a026c001803c0481e035840182106809a000a4058120780d610060841a0268a4180160481e035840182106809b660940581207840008060841a026c60058125901e100020182106809b000940581207994008060841a026800000160481e6500201821068099250160481e10194008060841a026c000581207840650020182106809a520160481e100b4008060841a026c600581207990038020182106809b180161201e1000e008060841a026d781801207840038020182106809b180160481e1000e008060841a026c00620600481e034020182106809a62178180120780d008060841a026d78290600481e034020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e630020182106809b0e0160481e580b8008060841a026d100e0120780e2e0020182106809b0e0160481e038b8008060841a026c94058120780e610020182106809b620600481e03584008060841a026c60058120780d610020182106809b250160481e03920008060841a026c60058120780e600020182106809b05812078b403980008060841a026d7c5e0600481e038010182106809b00104180120780e004060841a026978250600481e038010182106809b00094058120780e004060841a0268000581207900038010182106809a250160481e2d00e004060841a026c160481e400b4038010182106809b0e0160481e100025d0060841a026c38058120780e005740182106809b450160481e038025c0060841a026c38058120780e009700182106809b0f0160481e038025c0060841a026c160481e1000e009700182106809b00038058125b01e100050841a026954058125b01e1000e0142106809b450160496c07840038050841a026c000e0160481e101200142106809a00114058120780e480050841a0269140e0160481e039200142106809b0003c058120780e480050841a0268000581207840039200142106809a00038058120791c008050841a0268000e0161201e100020142106809a000155a04807840008050841a026800440380481e100020142106809a001480e01207840008050841a026800560160481e100020142106809a560380581207840008050841a026c000e0160481e100020142106809a000151216407840008050841a026958058125901e100020142106809b450160496407840008050841a026c00054125901e100020142106809a0e0160481e47040008050841a026d140e0160481e580020142106809b0e0160481e47160008050841a026c00450160481e570020142106809a00038058120795c008050841a0268000581207840570020142106809a00114058480780e008050841a026800450165301e038020142106809a000380594c0780e008050841a0268000f0165301e038020142106809a00148450120780e008050841a026954440380481e038020142106809b001480e0120780e008050841a026910450380481e038020142106809b001480f0120780e008050841a026800560160481e038020142106809a00154058120780e008050841a026800450160481e038020142106809a56038058120780e008050841a026d140e0160481e038020142106809b5503c058120780e008050841a026c00058120791c038020142106809a540161201e1000e008050841a026d480584807840038020142106809b450161201e1000e008050841a026c000544807840038020142106809a000165301e1000e008050841a0269480581207840038020142106809b450160481e1000e008050841a026c160481e47040038020142106809b0e0160481e47120008050841a026c38058120780e480020142106809b001100e0120780e004050841a026800054120780d0045c0182209009a054280481e034011700608824026c00000150481e034020142106808900015049440780d008050841a022800054120780d340020142106808a054125101e034d0008050841a022c001b0160481e034010142106808a00000058120780d004050841a02246c058120780d004050841a3e008b000160481e0340101421068f8022800054120780e004060841a0293ca054125001e03801018210680a4f2c150481e2d00e004060841a0293cb000150481e0380201821068094d2815049380780e008060841a02534b05412078b40380201821068094d2c380581207840340050841a0290cb1b0380481e10002014210680a432c3805812078404c0050881a0250cb0e0160481e4b0020142206809432c384a01207840008050881a0250cb0e1280481e038010142206809432d24058120780e004050881a0250cb250160481e100020182106809432c94058120780e004060841a0250cb0e0160481e101200142106809432c38058120791c008050841a0250cb440380481e100020142106809432c380581207840008050841a0250cb0e0160481e460020142106809432c000581207918008050841a0250ca0581207840460020142106809432d14058120780e008050841a0250cb440380481e038010142106809432c160481e100b4008060841a024fcb1803c0481e0380201821068093f2ca4058120780e008060841a024fcb05812079080380201821068093f2d04180120780e004060841a024fcb05812079000380101821068093f2c6c180120780d3400201821068d4b1b0380481e038d0008050841a352c6c0e0120780e004050841a3e0d4b1b0600481e034b8008210680a352ca8180120780d008060841a028d4b1b0940481e03801018210680a352c6c0e01207840008050841a028d4b1b0380481e3d001014210680a352c6c0e0123700e004050841a028d4b26016048dc03801014210680a352c6c3c0120780e004050841a028d4b1b0380481e03801014210680a352c6c3b0120780e004050841a028d4b0e0ec0481e03801014210680a352c003b0120780e004050841a028d4a260160481e03801014210680a352c6c3a0123700d004050841a028d4b1b0e4048dc03401014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c6c058123800d004050841a028d4b00016048e003401014210680a352816048dc3800d004050841a028d4b05812370d803401014210680a352c6c058120780d004061a02206870b230160481e034d0008060841a1c2c6c058120780d340020182106870b058120780d340021d0060841a1c2c8c058120780d004060841a33070b1b0160481e0340101821068cc1c2c160481e034011d0060841a33070b180160481e03401170220680a1c2cc8058120780d004060881a02870b310160481e03401018220680a1c2cc0058120780d004060881a02870b058120780d004bc018220680a1c2c60058120780d2e0020841a02870b05812078b4038011d0210680a1c2c8c058120780d004b00841a02870b180160481e034012c0210680a1c2c160481e034011d0b00841a02870b1803c0481e03402018210680a1c2cac058120780d008060841a02870b2a0160481e03402018210680a1c2ca4058120780d008060841a02870b058120780d28002018210680a1c2c6c0e0120780e004060841a02870b270160481e03801018210680a1c2c98058120780e004060841a02870b250160481e03801018210680a1c2c160481e2400e004060841a02870b230160487803401018210680a1c2c6c058121e00d004060841a02870b180160487803401018210680a1c2c8c220120780d004060841a02870b1b0880481e03401018210680a1c2c60220120780d004060841a02870b210160481e03401018210680a1c2c80058120780d004060841a02870b058120780d0047c018210680a1c2c1604878034011d0060841a02870b1b0160481e03401014680881a192c60058120780d0045c0881a02458b
  | 10, 1 => 0x58120784003a100182206809a0003c0481e0361001822068099058120780e770020182206809a000160481e101b001422068099000160481e6e0020142206809900016049b4038020142206809905812079b86c0020142206809a058126d00e6c0020142206809a520161201e038020142106809a0e0123700e004050841a028d4a3a0123700d004050841a028d4a390123700d004050841a028d4a
  | 11, 0 => 0x1b0160481e1000e0085c018220680ac180160481e1000e008061a0220680ac0000005412078402d0021702206809a0000005412078402d1300182206809a000600581207840039300182206809b000001803c0481e035300182206809a00094058120780e4c0020182206809b0003805812078400085c0182206809b000000e0160481e101300142206809a00000058120780e6c0020142206809a0e0160481e039306c0020142206809c000160481e039306c0020142206809b00000250160481e100020182106809a00060058120780d610020182106809b00000054125901e100020142106809a000000544807840038020142106809a000000541207840038020142106809a00038058120780e480020142106809b00000440380481e038010142106809a000000e0160481e038010142106809a000380581207840008050841a0250cb00038058120780e004050841a0250cb000160481e2d00e004060841a024fcb0006c0e0120780e004050841a028d4b0006c058123700d004050841a028d4b0006c058120780d004050841a028d4b0008c058120780d004060841a02870b0006c058120780d004060841a02870b00060058120780d004060841a02870b000160481e034011d0060841a02870b4a0160481e1000e00874018220680ac0f0160481e9100e00874018220680ac0e0160481e038b8008061a0220680ac0003c05812078b4039300182206809b0012805812078402d0020182206809b000150481e4b0402d0020182206809b000150481e102282d0020182206809b000000541207a08038020182206809a0003c0581207a28038020182206809b0021805812078b4038020182206809b8612805812078b4038020182206809c0f0160481e8a0b4038020182206809c00038058120780e780020182206809b000150481e8200e780020182206809b000150481e4b00e780020182206809b000150481e4200e780020182206809b000150481e8a00e780020182206809b000380581207a442e0020182206809b000384a0120780e2e0020182206809b00124058120780e2e0020182206809b49038058120780e2e0020182206809c49128058120780e2e0020182206809c000150481e8200e2e0020182206809b4a0160481e4200e2e0020182206809c290160481e9100e2e0020182206809c0541207a089100e2e0020182206809c0e0160481e039e02e0020182206809c0541207a08039e02e0020182206809c0541207908039e02e0020182206809c25060058120780e4c0020182206809c000150481e8200e4c0020182206809b250160481e2d00e4c0020182206809c860160481e2d00e4c0020182206809c0541207a082d00e4c0020182206809c0e0160481e039e04c0020182206809c0541207a08039e04c0020182206809c054120792c039e04c0020182206809c00114058120780e0085c0182206809b45038058120780e0085c0182206809c4503c058120780e0085c0182206809c000150481e8200e0085c0182206809b300160481e1000e0085c0182206809c0541207a081000e0085c0182206809c0f0160481e8a00e0085c0182206809c0e0160481e039e00085c0182206809c0541207a08039e00085c0182206809c0541207a28039e00085c0182206809c00000054120780e009d00182206809a000150481e03802171d00182206809b054120784003802171d00182206809c00000054120780e00a640182206809a000150481e038b800a640182206809b0541207a44038b800a640182206809c000000e0160481e4b0020142206809a000000e1280481e100020142206809a001240e0160481e100020142206809b00038058120792c100020142206809b001140e0160481e910020142206809b00038058120792c910020142206809b001140e1280481e038020142206809b00038861280481e038020142206809b00000700160481e038020142206809a001c0860160481e038020142206809b00124860160481e038020142206809b001c04a0160481e038020142206809b702184a0160481e038020142206809c492184a0160481e038020142206809c001c0058120792c038020142206809b00114058120792c038020142206809b00124058120792c038020142206809b00218058120792c038020142206809b001c00581207840038020142206809b701280581207840038020142206809c700160481e4b040038020142206809c450160481e4b040038020142206809c001280581207a60038020142206809b000000581207a60038020142206809a4a0160481e10260038020142206809c000160481e10260038020142206809b001c00581207a44038020142206809b701240581207a44038020142206809c7003c0581207a44038020142206809c700160481e4b244038020142206809c490160481e4b244038020142206809c000000581207a5c038020142206809a0f0160481e9125c038020142206809c000160481e9125c038020142206809b00038058120792c4c0020142206809b001c0058120780e4c0020142206809b70038058120780e4c0020142206809c70218058120780e4c0020142206809c700160481e4b00e4c0020142206809c860160481e4b00e4c0020142206809c00000054120780e008066b02206809a000150481e03930008066b02206809b05412078b403930008066b02206809c00094180160481e100020182106809b0009405812078402d0020182106809b0011405812078402d0020182106809b000941803c0481e038020182106809b001141803c0481e038020182106809b00000660160481e038020182106809a00198250160481e038020182106809b00198290160481e038020182106809b00094290160481e038020182106809b00198180160481e038020182106809b66094180160481e038020182106809c660a4180160481e038020182106809c250a4180160481e038020182106809c001980581207908038020182106809b000940581207908038020182106809b001140581207908038020182106809b000a40581207908038020182106809b001980581207840038020182106809b660600581207840038020182106809c660160481e42040038020182106809c450160481e42040038020182106809c000600581207a20038020182106809b000000581207a20038020182106809a180160481e10220038020182106809c000160481e10220038020182106809b0019805812078b4038020182106809b6609405812078b4038020182106809c660160481e420b4038020182106809c250160481e420b4038020182106809c000a41803c0481e034020182106809b00000182580481e034020182106809a000600f2580481e034020182106809b000000f2580481e034020182106809a00000002580481e034020182106809900198058120780e2e0020182106809b66038058120780e2e0020182106809c660a4058120780e2e0020182106809c660160481e4200e2e0020182106809c290160481e4200e2e0020182106809c00038058120780e950020182106809b00000058120780e950020182106809a0e0160481e038b8950020182106809c000160481e038b8950020182106809b00000058120780d610020182106809a0003c058120780d00a500182106809b00000058120780d00a500182106809a00038058120780e005740182106809b00000058120780e005740182106809a001140e0160481e100020142106809b000000e0160481e460020142106809a00000000160481e4600201421068099000380581207840460020142106809b000000581207840460020142106809a00000000151201e038020142106809900000520160481e038020142106809a001480581207840038020142106809b0003c058120795c038020142106809b00000058120795c038020142106809a000009303c0481e034020142106809a000000f0160481e034020142106809a00000058120780e480020142106809a0f0160481e8f00e008050841a02a48c000160481e8f00e008050841a02a48b0f0160481e03402170060881a02648c000160481e03402170060881a02648b0f0160481e9100e008050881a02648c000160481e9100e008050881a02648b0f0160481e2d00e008060841a02648c000160481e2d00e008060841a02648b000600f0120780d008060841a02648b000a4058120780d008060841a02648b2903c058120780d008060841a02648c0f0160481e03402940060841a02648c000160481e03402940060841a02648b00114058120780e008050841a02648b4503c058120780e008050841a02648c0f0160481e5700e008050841a02648c000160481e5700e008050841a02648b0024c0f0120780d008050841a02648b0003c058120780d008050841a02648b0e0160481e038d0008050841a0290cc000160481e038d0008050841a0290cb0e0160481e03801170060881a0250cc000160481e03801170060881a0250cb0e0160481e03930008050881a0250cc000160481e03930008050881a0250cb000384a0120780e004050881a0250cb00124058120780e004050881a0250cb49038058120780e004050881a0250cc0e0160481e03801015a40881a0250cc000160481e03801015a40881a0250cb0e0160481e038b8008060841a0250cc000160481e038b8008060841a0250cb00094058120780e004060841a0250cb25038058120780e004060841a0250cc0e0160481e038015d0060841a0250cc000160481e038015d0060841a0250cb00114058120780e008050841a0250cb45038058120780e008050841a0250cc0e0160481e03920008050841a0250cc000160481e03920008050841a0250cb001100e0120780e004050841a0250cb00124058120780e004050881a02640b49038058120780e004050881a02640c00038058120780e004050881a02640b00000058120780e004050881a02640a490160481e9100e004050881a02640c000160481e9100e004050881a02640b00094058120780e004060841a024fcb00000058120780e004060841a024fca250160481e2d00e004060841a024fcc1b0160481e034b8008060841a028d4c000160481e034b8008060841a028d4b1b0160481e2d00e004060841a028d4c000160481e2d00e004060841a028d4b1b0160481e1000e008050841a028d4c000160481e1000e008050841a028d4b00098058120780e004050841a028d4b2606c058120780e004050841a028d4c1b0160481e3d00e004050841a028d4c000160481e3d00e004050841a028d4b00000058123700d004050841a028d4a0006c390120780d004050841a028d4b2306c058120780d004060841a02870c23060058120780d004060841a02870c00000058120780d004060841a02870a230160481e034011d0060841a02870c
  | 11, 1 => 0x160481e039b0008050881a026800058123700d004050841a028d4a000150481e100b40085c0881a02680005412078402d1300182206809a180160481e1000e4c0060881a026c3c05812078b4039300182206809b000600f0120780d4c0060881a02692805812078402d0020182206809b054120792c100b4008060881a026c150481e102282d0020182206809b000150481e8200e008060881a02683c0581207a28038020182206809b860160481e2d00e008060881a026c38058120780e780020182206809b0541207a08039e0008060881a026c150481e4b00e780020182206809b0541207908039e0008060881a026c150481e8a00e780020182206809b0e0160481e910b8008060881a026c384a0120780e2e0020182206809b490160481e038b8008060881a026c150481e8200e2e0020182206809b250160481e03930008060881a026c150481e8200e4c0020182206809b0e0160481e10002170060881a026d14058120780e0085c0182206809b0541207a0803802170060881a026c00054120780e009d00182206809a054120780e0085c740060881a026c00054120780e00a640182206809a054120780e2e002990060881a026c000e0160481e101300142206809a00038058120792c008050881a0268000e1280481e100020142206809a490380581207840008050881a026c38058120792c100020142206809b450380581207a44008050881a026c38058120792c910020142206809b450384a0120780e008050881a026c38861280481e038020142206809b001c0058120780e008050881a0269c0860160481e038020142206809b49218058120780e008050881a026dc04a0160481e038020142206809b700160481e4b00e008050881a026d14058120792c038020142206809b490160481e4b00e008050881a026e18058120792c038020142206809b700160481e1000e008050881a026d280581207a60038020142206809b000160481e9800e008050881a0268160481e10260038020142206809b700160481e9100e008050881a026c000581207a5c038020142206809a0581207a449700e008050881a026c38058120792c4c0020142206809b700160481e03930008050881a026c160481e039306c0020142206809b000150481e03802019ac0881a0268150481e03930008066b02206809b000940581207840008060841a026894180160481e100020182106809b250160481e100b4008060841a026d1405812078402d0020182106809b250600f0120780e008060841a026d141803c0481e038020182106809b00198058120780e008060841a026998250160481e038020182106809b660a4058120780e008060841a026c94290160481e038020182106809b66060058120780e008060841a026d980581207908038020182106809b250160481e4200e008060841a026d140581207908038020182106809b290160481e4200e008060841a026d980581207840038020182106809b180160481e8800e008060841a026c000581207a20038020182106809a05812078408800e008060841a026d9805812078b4038020182106809b290600f0120780d008060841a026c00182580481e034020182106809a1803c960120780d008060841a026c000f2580481e034020182106809a00000960120780d008060841a026598058120780e2e0020182106809b0e0160481e03a54008060841a026c00058120780e950020182106809a058120780e2e254008060841a026c60058120780d610020182106809b000160481e03584008060841a02683c058120780d00a500182106809b000160481e03402940060841a026838058120780e005740182106809b000160481e038015d0060841a0269140e0160481e100020142106809b000150496407840008050841a0268000e0160481e460020142106809a000000581207918008050841a0264380581207840460020142106809b000160481e10118008050841a026800000151201e038020142106809900148058120780e008050841a0268000544807840038020142106809a520160481e1000e008050841a026c000541207840038020142106809a0f0160481e5700e008050841a026c00058120795c038020142106809a0024c0f0120780d008050841a0268000f0160481e034020142106809a0e0160481e03920008050841a026c00058120780e480020142106809a001100e0120780e004050841a0268000e0160481e038010142106809a002830481e034b8008060841a9ee800a0c12078b4038010182106a7ba000120780d340021d0060841a9ee800a0c1207840038020142106a7ba000120780d8e002014220680a9ee81207a3c03930008050881a02a7bb0481e036384c002014220680a9eec120780d2e002018680881a02a7bb0481e1000e008051a0220680a9eec120780d8e002014680881a02a7bb000120780d2e0d0018210680a9ee8000481e034a0008060841a02a7ba0481e8f00e2e002018210680a9eec120780d280b8008060841a02a7bb0481e2d00e34002018210680a9eec120780d280d0008060841a02a7bb0001207a3c2d001018210680a9ee8000481e2400e004060841a02a7ba0481e240b403801018210680a9eec1207840038021d0060841a02a7bb0481e034a000874018210680a9eec1207890038011d0060841a02a7bb000129bc1e8f00e014210680a9ee8000481e1000e340050841a02a7ba0001207a7c03802014210680a9ee81207a7c1000e008050841a02a7bb0481e9f23c03802014210680a9eec0004a6b078d0008050841a02a7ba0481e9f00e34002014210680a9eec1207a44038b8008060881a0267bb0481e2d00e4c00201822068099eec0004a6f0780d170060881a0267ba0481e1000e0085c01822068099eec0004a6f07a44038050881a0267ba00012078400393001422068099ee8000481e4b00e008050881a0267ba0481e4b0400380201422068099eec120792c9100e008050881a0267bb000129ac1e4c00201422068099ee8120792c03930008050881a0267bb0000004a739bc1e03421068099ee40004a7307840038020841a0267ba0000004a739ac1e00421068099ee40004a6f078b4038060841a0267ba00012078402d00201821068099ee8000481e4200e008060841a0267ba0481e420400380201821068099eec12079082d00e008060841a0267bb000129ac1e2e00201821068099ee81207908038b8008060841a0267bb0000004a6f9ac1e01421068099ee4160481e8f00e008050841a02a48b058120780d0085c0182206809922c160481e9100e008050881a02648b0f01604a730780d0082106809922c00058129cc1e034020841a02648a05812078b4038020182106809922c00180120780d008060841a02648a1803c0481e034020182106809922ca4058120780d008060841a02648b058120780d00a500182106809922c3c058129ac1e008050841a02648b0001604a6b078020142106809922914058120780e008050841a02648b058120795c038020142106809922c00930120780d008050841a02648a9303c0481e034020142106809922c3c058120780d008050841a02648b058120780e34002014210680a432c3805a770481e038010141a0250cb000169dc120780e00405068094328160481e03801170060881a0250cb058120780e4c0020142206809432c384a0120780e004050881a0250cb001280481e038010142206809432924058120780e004050881a0250cb058120780e004056902206809432c38058129cc1e038010841a0250cb0001604a730780e00421068094328160481e038b8008060841a0250cb250160481e038010182106809432c160481e038015d0060841a0250cb0e01604a6f0780e0142106809432c00058129bc1e038050841a0250ca0e0160481e100020142106809432c000581207840008050841a0250ca450160481e038020142106809432c160481e03920008050841a0250cb001100481e0380101421068094329100e0120780e004050841a0250cb0e0160481e038010142106809432d24058120780e004050881a02640b0e0160481e038010142206809902c00058120780e004050881a02640a0581207a44038010142206809902c94058120780e004060841a024fcb000160481e0380101821068093f28160481e2d00e004060841a024fcb058120780d2e002018210680a352c160481e2d00e004060841a028d4b058120784003802014210680a352c6c058129ac1e004050841a028d4b0001604a6b07801014210680a35286c0e0120780e004050841a028d4b000380481e03801014210680a352898058120780e004050841a028d4b05812078f403801014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c00390120780d004050841a028d4a1b0160481e03401014210680a352c8c058120780d004060841a02870b1b0160481e03401018210680a1c2c60058120780d004060841a02870b000160481e03401018210680a1c28160481e034011d0060841a02870b
  | 11, 2 => 0x5412078402d0021702206809a05412078402d1300182206809a1803c0481e035300182206809a0541207a08038020182206809a054120780e009d00182206809a054120780e00a640182206809a0e0160481e101300142206809a0e0160481e4b0020142206809a0e1280481e100020142206809a700160481e038020142206809a0581207a60038020142206809a0581207a5c038020142206809a058120780e6c0020142206809a054120780e008066b02206809a250160481e100020182106809a660160481e038020182106809a0581207a20038020182106809a182580481e034020182106809a0f2580481e034020182106809a002580481e0340201821068099058120780e950020182106809a058120780d610020182106809a058120780d00a500182106809a058120780e005740182106809a054125901e100020142106809a0e0160481e460020142106809a000160481e46002014210680990581207840460020142106809a000151201e0380201421068099520160481e038020142106809a0544807840038020142106809a0541207840038020142106809a058120795c038020142106809a9303c0481e034020142106809a0f0160481e034020142106809a058120780e480020142106809a440380481e038010142106809a0e0160481e038010142106809aa0c120780d2e0020182106a7baa0c12078b4038010182106a7ba0481e034d0008740182106a7baa0c1207840038020142106a7ba0481e03638008050881a02a7ba0481e034b8340060841a02a7ba0481e034a0008060841a02a7ba0481e8f0b4004060841a02a7ba0481e2400e004060841a02a7ba04a6f07a3c038050841a02a7ba0481e1000e340050841a02a7ba0481e9f00e008050841a02a7ba04a6b078d0008050841a02a7ba04a6f0780d170060881a0267ba04a6f07a44038050881a0267ba0481e1000e4c0050881a0267ba0481e4b00e008050881a0267ba04a6b07930008050881a0267ba000129ce6f0780d0841a0267b904a7307840038020841a0267ba000129ce6b078010841a0267b904a6f078b4038060841a0267ba0481e100b4008060841a0267ba0481e4200e008060841a0267ba04a6b078b8008060841a0267ba000129be6b078050841a0267b9058129cc1e034020841a02648a180120780d008060841a02648a058129ac1e008050841a02648a930120780d008050841a02648a05a770481e038010141a0250ca4a0120780e004050881a0250ca058129cc1e038010841a0250ca058129bc1e038050841a0250ca0581207840008050841a0250ca440120780e004050841a0250ca058120780e004050881a02640a058120780e004060841a024fca058129ac1e004050841a028d4a0e0120780e004050841a028d4a058123700d004050841a028d4a390120780d004050841a028d4a058120780d004060841a02870a
  | 11, 3 => 0x960120780d008060841a0264160481e4600201421068099054480780e008050841a0264129ce6f0780d0841a0267b904a739ac1e00421068099ee4129be6b078050841a0267b9
  | 12, 0 => 0x150481e9100e2e0020182206809b05412078b403930008060881a026c150481e1000e0085c0182206809b4a0160481e1000e008050881a026c3c0581207a44038020142206809b0e0160481e03930008050881a026c600581207840038020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e2e0020182106809b290160481e034b8008060841a026c00250160481e038010182106809a250160481e2d00e004060841a026c000e0160481e100020142106809a00114058120780e008050841a0269140e0160481e038020142106809b4503c058120780e008050841a026d140581207840038020142106809b0f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 1 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 2 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 3 => 0x1803c0481e034020182106809a290160481e034020182106809a250160481e038010182106809a0e0160481e100020142106809a450160481e038020142106809a002830481e034010142106a7b90481e034d0008050841a02a7ba0481e8f00e004050841a02a7ba0481e03530008050881a0267ba0481e034b8008060841a0267ba0481e2d00e004060841a0267ba000129bc1e034050841a0267b90481e1000e008050841a0267ba000129ac1e004050841a0267b9058120780d008050841a02648a058120780e004050841a0250ca058120780d004050841a028d4a
  | 12, 4 => 0x2830481e034010142106a7b904a6f0780d01421068099ee4129ac1e004050841a0267b9
  | 13, 0 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a
  | 13, 1 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 2 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 3 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 4 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 5 => 0x120780d004050841a0267b9
  | _, _ => 0
def tableData : Nat → Nat → Nat
  | 9, 0 => 0xa0940000b100004200009a00004936ab18308d00880000002b000d1e0c0055243d072a0000009f007900192587061f316d937e12611301998e00725b664e
  | 10, 0 => 0xde1f79e356d990d750000000000000000000000000000000000000000000000000000000000000f850000000a9e4d0003cd2920000000000000007433310d91b1000000a15f93000000d2d000000000f3050619900043f000000000000000000f61000000ae1aca00027100000000000000033d0000001459be457eca000b278b7558f92c5c6ebaa57db2dd6c10008a2000000516000d995f0901ccd4cb22922b000000000000000000000000000000000e86829c88e6ee059d6fc166e0000006bb3d9c26a5bec589e240000691000000000000000000aff000d39667000f880001c9000000000e580007ea96b00001900052d841000000c83000b4d33a32bf19d15000fa23855469a46aa0005240006d7704000617000a210008e4dce000000000e56000000a9f000000abe2f2000000000a4f8350004e12883087709fdeba1390000000003791f99b2f31d8b00068b00000000000062c2ad0790000008f5a61d611810000004b00002954220000000000006a3b33b8900000036100054df4a6f88aae6520541672140900000000000000000000081db06e10211955c1958ff7767a000b29e7d049f91000000000000000000000000000c9d000000000af700000000054ec6700085300000000000018d9b0000000593000000f9f0006da000e41000f9e00000000060d000000000d818e900000000021d6e300000000000000039d00031f000f2200000083b0000000000006a92ce98c34f00000000015d000fcd4bcf3fcf1000000000f9d000000b9d7bdabb0000000000007edb7d7f6560241ab1000000e4b235000f18ca9f0055700000027000059c0000000000005cc0000000000000fdcce53f0000002c2000a37000000000000000000000b8ad5a0008a19800006cd00000000000000003d8196e58c512d30d0f11159755d1c9bf67515bc5692025f0ae9e589de63a9679f23d7500000000027d00000069b000000000000ded000000294d14dda00074b355f16df8bf50000000000008c2000000618e59cfdfe7000000518000db1000000885ed1267000b5700000000000077c000000000000000000000e4e000000000a6e64f5450003910008b54986389b5175f589311d58790cd50f34974f00afa436dd458050000000000000003b5b7e535e890000000000c12f593db1b000000000000577ea1b110000007818ad548000000000000dc93d309dbdd28b715a6c061a97fbf000d92000fa00000000002d1ac9d090000000000000000000000000007dc000000000737000d38edda81ef73c19bcb71000fad7d2594a75bc6000000000000000000000000000000000000000000bf3c770009193e50005fc4787ff000000000000e330001690004a4000000000000000655a5d7a6bad23e78df6dfa99e2e71151dbdfaa00024d000000a43000a51000d3d505000a3900000000000000000076400000000000006d000eb9e280000000005e40005b91ed9cad550000000004ed30754060e2374bf000000f24000000000000abd00000000094a0000000000009f1000f44000f73000000000286571460c6d0000000000004e7b35fb566dce51e1bdb121000000000000000000758000000aeb0000000000000000000000000000000004db9e5000892620665f6b00000000009100000000027fb053f10e5000000000e11697f0f5170000008d1000000000fe11bdad5cbcb59000000000799584e950006e486d000000000f25000000000000000b41000000055c36000cf20000000000000005a8a7351058a00000000000056cd6ecc2b65c0de57f1b343689000000bd10000000000000000004840007090006df000e2937fd7a5473160005b4000000a2b000000000ba1000fd90b5000998000207000000ff3031000df9000a8d000259000500dd5d8d265e1dcd9000000e7a738000000000000000000744c41000949000000a0900000000000000f000109c49000000eeb53600060800000000000000044bbb97b169cc01000000000000000000000000000da5d2181ee1c886d4ecc846c8cf21f000b3f3fd6af85926e000000643fab289d5d925eb600000042e1a5000000000000ee0000085000000000000d69f8600000000000032c0002a10000000004d5d5100000071c
  | 10, 1 => 0x377534900000089002400000000190022000000000000000d0f000000002a0000002b7d00000000478e00006d2c003d005f0000001b0000553b316129000001
  | 11, 0 => 0x62f48da470be8b4bad8ec99a07a2032967f7282a6934200088d0000000000000004a2bd11f309700000088904b1e1a000007de0009ecaed00030e6bf8950000000000000005597e18b100000021825e26a0000000000882d1542a6d3fd0000005110000000000008e9000a2e0cd58912d90520c422679052000000000b157396559fe0006be8b800000051d3d288835a241000000b8b00000000000000000009d000000000000000b47baa000ad59910000000000000002ad000000000246ba17bb4ba28e07834e4ed00000007907319f00000000000061cb2f3ed0000009b68860007150000004be54a2b94e148107bb210000006360000000008dbbaf3910007240000002dd33106a0aebae42100000060345da507bd00000066b24d989786000000000000aa581d0000fa2f9862000949b05229aa10000000603de000336000000ae16538a10000008eb0000635d172b0001b10000004094c6000439b5761e0000006b50000007d3000000000000000000000a460000008bd0a3000000871000031000000000000726a3991a9165a933d7eb0000002c5a09ab14758d13670003b57f90005cc1a50009e02ba77a14500000000000093100000093d0930004695d20006e565f2590000009039900001d00006f1b841ff00000087f60d00020500000000900022c6340000009145b9bab0009115dd1dc00000000000000000000000000000000000000000000069d49a7849879ff16300000064e1694d52350b55b506700000000000000000000000000000000000027100000000083534900000000079206d4c9049000661000000ac83799ad0ee000000000a51a4a0baba5000000000980000000000000000000000000000015000000000000000b888117ea4511ab98c00000079e02da0db3d5c5913325995a15a0aa3a5e93590002be0000000000000000001ed18d0000000000002db00000039d0009a831fb8a5e65cb000b410006490000000000002a200000000000000000068e1f722a000a28000000b4d00026500035c0000003020210b266d971abf55f0000000008af7a227d8600000006230001bd00000041500000000064c87d0000006cd000000000000000000a7d00000015d0007ae0000000000000009fd13f0007900002ed0000000000002a60000000572d60007ed2cab99a5db7f0000000003c17dcb8f0000000000000000000000001e700000000095e89e0000000003cd0003660000000000009f64990917699d1b4999f00000000005e82b577211000000000000000ba21d553521e086289000845bc9000309b7d0000000007c400000000011c00000052958f982000000000000157a950008f70000006d90001753714b1a229f89dd86912806c5657a5a1299d08598e07688b95400029a54ebb90002e20000000000000000000000000000000000000873855950000000000000000000000000009853d91ea000054000583000000000000a89000000929b7100006f000000445000000000899000000000a370005f59e600000000054174f00080e0002e95a71811f90000000000000000000009d94bd76296a000000000b0b0005de00000000000063d737a1003da43182bc52e7935000000000a4e2a1000affb59b95976000b2d0005a17c900042e0003f1000000000000000b860002207f40000009a435b000000000b8d000000000a1600000000000000000000000000000000009f709151851000000000110000000000ac300014b9a65b30000000000007564f92c630100000000069ba1307c8dd2f51040a900057d1330006010c18f500000000000000000094b0000000000006c100068f000000ae795685d00000000086e5ad8c92950000000000000000000339e3bba50618e0000000001c90000008aa000000000abd0006b20617b80000000000550007d5000000000000000962000000a450000000000008b631521d3193658adbbb3a92b27368d578d00000076e000000000000000000000252000276707ac930d9594a6b65000a40000000000000000000a54000000000000ac60000009c500052a00036890180500097986c8290009749e20d9b898a85ef452000000000961000000000000000000000199952000af9000000000139
  | 11, 1 => 0xa832b90af998a996fd0b60000000009e200094729a5be98900000025e00000000000020b0c700000098506f1f9a3048d92e5710000008574450000000000000000000000009310009950002290000000000000002e954175e0005290000000000004ed0003d7186139a5e09d9ad0e57812188414150760005430005d58290008a100085699c5e2a2e73967228e39a24d0000009b70002d20000000005370000000000003e77f33b200012d1929d93a4a960000002ad00000000007fa8d4cb33190b2520845ca0ab72d1b70b55334f100000000064368d38542d0000009fe40b00087d51d00070a7662c50006f10b75ed000721000000000499000a9b62500088c0004fd3665ad0000d2000a9a0002d67fb6cda8c90d0002654508d69d183f00000000000003d00000000000000038d00000059503900000000067e0005b200055b1754938270000000005110007c98930001d50000006a971200000081b18d00000084d00000092300049f000000000000000a820000000000000000000000000550003f500034988ea690004397a100093b5b9000061a394726e53915fb0006550000007c42c6a281f31c98ca3de0000000000000000001ca3560c36d92e27ca8338719ab5395104382209d80000000000000009a40000000b4805000211000000000000000000000000a977d57b10004790001e80000000000000000000000000000000000000000000000000008d4a2f4fe1639cf0004211990008220007ad24100054d0b200004b4510000000000000000002710009790000855c50009f530d8e207971506d3dd8353fd3cb09c4c860d000106000000000a86000a910000000000000000000000000002d10004440000150000004d600056e9a89610006c100093a1be9d43257bda3d69936d50e8ee9dda45a3a5a17e15e1a6a2ca00000000000008e0002051a50000000002f348c00058f6313f19f03a39b67de7c30007ed81d2834c90000000002a200042000000000020f000000000000a5853833d8110003790005e40000003020000d60930000000000003b399350f0002958f20000000000000000000006b50005590008200000005050000000000000002dd00000900000015d0008fe000000000000000a2d1573118e02f90000000000000002a60000000002ee00093d4b3a7900099f00014b9bb92c6613ca33a00000000045d00028f32b1ff18700000000000000000066d16f4e35fa0000000000000000000c18b9a197f59e700000000000096f0a908b0000000004ab000a8e1e13bf00075123634a0004d532c30999d4ea09f53591400000000000000048174578700000000000000000002d0000000000008650000003a6000605000a25a5212827d8f59d6000a422de9e598708250200000000076a000000aa500000000000000000039b00000000000000061978d0000000000000000000000000000006799cd00007820277b0000003520000213ff00000094900007b00000000000000000000036a000000a671f631200000047e75d0008b700095e31a2f500079f000000000000000000709049a213c10009ca00000000059b1ed3817d60005560004b589fa40ab1000000a730002890000000002a1a8a583565314a7551a21d6410009197990000004e569d0000009a65320000000002389440000a39ec5e300046f1459b93d90a8000a460000000003e50000000000000000000000000003190002be00000011c4be0000000974ae0009ee7ab00000000000000000000030100000033e22ca430b80004091100cd0a677513f0000000007f90000000000000000000000001930000008590000000004bd00017b0000003550000007a509045c00048239d000000000057a2baa60000000001a60003cd3653610000000000000000000913329080000000000000009250000000003890009c2000000a810000004e100099a5899912355f989eaa76492b216948a8dd0000008be00000000000000000054f26a5132763d60000d9000000abd181a700000000000000004b10000000003b53e209a000000a0d0007469a94c65fc95500000000096d00051f087a2a9b50f17e76c20000002829c12590000004e00000000000001b135e57d4a51bd313151
  | 11, 2 => 0x34c000000000000003b52d400001ed000000037700000918000000028800000000000000000000000000000000d60d1814005d400000000000000000003610036d003ad00000000000005b7554200000000006340037d4f6f473000001c83d19f3d0c6b96ce6a001d7002510000000000003210000000000af8000002b000006ac00308000000072c0000000c7ce0398000cdba72534000000000000000000000000000000000000000000000001c1d2400001369d521a9ecd000002a40000000000000000000000bd40097400c0400f059900000ede8900000001028d40000000003b60000031add000000000000180000000000000000000ee00000000004a779000000000000000000008e906001ef000d2238000000000000000000000000000b44000000000000000000000d4e40067c00000000000047485001ea0000000000064000016100000000e500241dae177e4d4ea400246a5000009aead6d4000000000000000005588b00374000370000000000155510f2e90039e3c80000000251cd00000000000000000000c94ba000000000000000000006b800c4c0000000000000000000000000000000000000000500003a00000000000000000000000005a4000000000000c5400784000000f60400000003c4000030d0c18c003914b425000cdd6800f08000014550d554067d3f400000000000000000000000000000000000000000000000304000240000202495b1003850021ddaa69000d91ebc318509d5400000000039d002290000078c0000000538000b800cc4001b4000000000000a5400002234cc005755a003192bc0000000000009b00000000000000000009c000000073000454ae0009d000000000000000000003ea111e40069400
  | 11, 3 => 0xe0000100140003a00031420000800a4c80000068000f40000c00000
  | 12, 0 => 0x728000000578000000001dc00785680000000000122d960a84006e001fc00aa4300000008000000cd00065e27962b24f400002104a0000001ac4954b497a001e841c60000001ec000000000000000214d591458000018c25d20000000a85a2980000002a8000000003f49400000000083003840000391b40000003f80000000000873001840000000000000000013c67
  | 12, 1 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 2 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 3 => 0xc63c000000009d0000250000000000009600970049bd84552c7e0000000000000000a30000000076000000000000410078005e009b00823200000000a80000009e0000000031006d91c1793b4aca00a70d9200007300000000b500003a00000000616556853d000000000400009c0000000000c900a900001959b9000000
  | 12, 4 => 0x19000211341
  | 13, 0 => 0x800c001b0402000000046400003c04dd18000001500d391
  | 13, 1 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 2 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 3 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 4 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 5 => 0x24103750
  | _, _ => 0
def tableDisplacements : Nat → Nat → Nat
  | 9, 0 => 0x3420400c3000000000141000081003080000000002000000
  | 10, 0 => 0x1000070000000000000000040000002000000040000802000000040003c0000800000000000100000000000000000001000030080000000008010000000006000000000000c0000000000000000000000000000000000000000020000000001000000040000800000000000000001000010000200000000020080000000000090040700005000000000400000000000000000001000000000000000000000000000000004000000000000000000040e00c01000000040000400000000000000800000000100000c040080001c000000000c0000c0001400000000040000004000010040200800000000080000001004000000000000000000040001000008000000000000000000000000000000000000000000000000000000000000010080000000000000000000000000000000000000000000000600000000000000000004000000000000000008000000000003000000000000c00000000000000000000000080000000000000000000001000000000000c0000c00000000080000000000000000000000000000000000000000000080000000000010000000401000000000001000000000000000000000000040300000000000040000c010000000400000000000000001000000000100000000000000300001000000000100000000050040000000000000000000c00000000000000402000000040200403000000000000001000000000000400000000000000000000000000000c010000000c00000010000200001004000000000003004000000100000000000000000001008000080000000000000080100000000000000000000000000040000400004000000000c000000000800000000040000000000000000100000004000000000000
  | 10, 1 => 0x40000000000000000000000000000000000000000
  | 11, 0 => 0x2c00000000040000400000000040000406000020080200000004000000000000000010000000c00000000000000000000000000000401000040000000000004010080000801008000000000401000010000001405000010000000402000000000000007000000040001400008000000000000000000000100004000000000000c00000000080100000000000040200000000000040200000004000000000400000010000000c000000000000004000000000000000000000300000010000000000405000010000000000000020000100001004000000000000004000000002002000000040000002000020080000c000080000400000000000000800004000000000400000000000000402000010040000000000000000000003000010000000000000000000200000000000000000004000000000000001000000000000001000000000700000000000000000400000000040000000008030000000000000000000000800000050040100003000000000000000000000000000000000000040000000000000080000000000000000000c0100001000000000300000008000000000c00004000000000000000000000000000000000000300000000000000000001000010000000000008000000000000000000000000000000000000000000000000000000000000000040000000000050000000000000020000000800000000000000800000000000100000000000000000000000000000000000000010000100000000000000000000000000000100000000000040000000000000000300001000000040000000000020000000000000000000000000000000040000000004000000000c0000000000000000400000000000000000000000010000000000
  | 11, 1 => 0x1400010000040400400000000040200c0900400004000000600c0000000004000080000000000000000000001030000000000000004000000000000004000000000400000000000c00003010000000000000000000000000000018000000000000000030000000000014000000000000000000000000001000020000100000000000040000001004000000100000000000000100800000000000000000008000000100400000000000000000000000040000001000000000100000010010000000000000000000001000000010000100001000000000000000000000000702c0100000004010000300002004000000100000000000100000000008000000000000008000000000000014000000100000000000000000000000000000000003008030000000002000000000001000000000000000400000000000000001000000000000004000000000000801000000000000001000000000000000000000000000000010000000000401000000000000000000010000000800000000000000000000000000000800000000000000400008000000000000000000000100000000000000000000000000000000000004000000000000000030000000000000000040100000000000000000000000010000000000000000000000000008000000000000000000040000000000000000000001004000000000c0000000008000000000c000000000000000000000000000000000000200000000000000000003000010000000000000000000001c00000030000000000000000000000000000010040100000000000000000001000000000001000000000080100000004000000200000000000000000000000000100600001000000080000001000000000000000
  | 11, 2 => 0x40000000000001000000000000000001000000003000000000000000200010000000000000000000000000010000000000040003010040000000000200000000000000000000000000000000000000000000000000000000000000000000040800008000000008000000000000204000000600000000000000000001000000000008000001000000002000000200000000000000000002000000000000000000000000000000000000000040000000000000000040000008000000000040000000000000000000000000000000000000000018000200000000000010000000000000000000000000000000000008000000008000000000000000000000000000000000000000000000000000000000000008000000000040000000000000
  | 11, 3 => 0x0
  | 12, 0 => 0x8000000000004100020000100001000000000020000200000000000000000008002000000000002000008000000000000000
  | 12, 1 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 2 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 3 => 0xc000040000002000000200000040000300000000000000000000002000000000000000000000000000000000000000000000000000000
  | 12, 4 => 0x8
  | 13, 0 => 0x8402000000000000000
  | 13, 1 => 0x801014010000010000
  | 13, 2 => 0x801014010000010000
  | 13, 3 => 0x801014010000010000
  | 13, 4 => 0x801014010000010000
  | 13, 5 => 0x880
  | _, _ => 0
def tableBuckets : Nat → Nat → Nat
  | 9, 0 => 32
  | 10, 0 => 512
  | 10, 1 => 32
  | 11, 0 => 512
  | 11, 1 => 512
  | 11, 2 => 256
  | 11, 3 => 16
  | 12, 0 => 64
  | 12, 1 => 64
  | 12, 2 => 64
  | 12, 3 => 64
  | 12, 4 => 4
  | 13, 0 => 16
  | 13, 1 => 16
  | 13, 2 => 16
  | 13, 3 => 16
  | 13, 4 => 16
  | 13, 5 => 4
  | _, _ => 1
def tableMultiplier : Nat → Nat → Nat
  | 9, 0 => 1000
  | 10, 0 => 1000
  | 10, 1 => 1000
  | 11, 0 => 1000
  | 11, 1 => 1000
  | 11, 2 => 1000
  | 11, 3 => 1000
  | 12, 0 => 1001
  | 12, 1 => 1001
  | 12, 2 => 1001
  | 12, 3 => 1000
  | 12, 4 => 1002
  | 13, 0 => 1000
  | 13, 1 => 1000
  | 13, 2 => 1000
  | 13, 3 => 1000
  | 13, 4 => 1000
  | 13, 5 => 1000
  | _, _ => 1
def tableSalt (_ _ : Nat) : Nat := 0
def tableBits : Nat → Nat → Nat × Nat
  | 9, 0 => (6, 8)
  | 10, 0 => (10, 12)
  | 10, 1 => (6, 8)
  | 11, 0 => (10, 12)
  | 11, 1 => (10, 12)
  | 11, 2 => (9, 10)
  | 11, 3 => (5, 7)
  | 12, 0 => (7, 9)
  | 12, 1 => (7, 9)
  | 12, 2 => (7, 9)
  | 12, 3 => (7, 8)
  | 12, 4 => (3, 6)
  | 13, 0 => (5, 6)
  | 13, 1 => (5, 6)
  | 13, 2 => (5, 6)
  | 13, 3 => (5, 6)
  | 13, 4 => (5, 6)
  | 13, 5 => (3, 4)
  | _, _ => (1, 1)
def sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel
lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates raw raw_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ raw_valid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)
lemma wire9_sig (g0 : Gate) (gs : List Gate)
    (hg0 : g0.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hw9 : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g0 :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) :
    gv raw g0 = bin false raw4 raw6 := by
  have hv : Valid (gv raw g0) := gv_valid raw_valid g0
  have hv46 : Valid (bin false raw4 raw6) :=
    valid_bin (raw_valid raw4 (by simp [raw])) (raw_valid raw6 (by simp [raw]))
  have hbit (s : Bool) (i : Fin 414) : bit s i (gv raw g0) = bit s i (bin false raw4 raw6) := by
    have h1 := hw9 (sample s i)
    simp only [Circuit.wires, List.foldl_cons] at h1
    have hlen : (List.ofFn (sample s i)).length = 9 := by simp
    have hlt : 9 < (List.ofFn (sample s i) ++ [g0.op.eval (g0.inputs.map fun j =>
        (List.ofFn (sample s i)).getD j false)]).length := by simp
    rw [foldl_append_getD _ gs _ 9 hlt false] at h1
    have hget : (List.ofFn (sample s i) ++ [g0.op.eval (g0.inputs.map fun j =>
        (List.ofFn (sample s i)).getD j false)]).getD 9 false =
        g0.op.eval (g0.inputs.map fun j => (List.ofFn (sample s i)).getD j false) := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget, sample_list] at h1
    rw [run_bit s i g0 raw raw_valid hg0, h1, bit_bin]
    rfl
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 414
    · simpa [bit] using hbit true ⟨i, hi⟩
    · rw [hv.1 i (by omega), hv46.1 i (by omega)]
  · apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 414
    · simpa [bit] using hbit false ⟨i, hi⟩
    · rw [hv.2 i (by omega), hv46.2 i (by omega)]
def index9 (key : Nat) (j : Nat) : Nat := (key >>> (9 * j)) &&& 511
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
lemma reindexLoop_testBit (f : Fin 414 → Fin 414) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 414 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 414
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 414 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 414 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 414
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_comp (f g : Fin 414 → Fin 414) (x : Nat) :
    reindex f (reindex g x) = reindex (fun j => g (f j)) x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, reindex_testBit, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_id {x : Nat} (hx : Valid1 x) : reindex (fun j => j) x = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 414 → Fin 414) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)
def compHom (h1 h2 : SigHom) : SigHom where
  fn a := h1.fn (h2.fn a)
  valid a := h1.valid (h2.fn a)
  hneg ha := by rw [h2.hneg ha, h1.hneg (h2.valid _)]
  hbin d a b := by rw [h2.hbin, h1.hbin]
  hzero := by rw [h2.hzero, h1.hzero]
  hone := by rw [h2.hone, h1.hone]
  htarget := by rw [h2.htarget, h1.htarget]
def sym1 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey1 j.val)
def sym2 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey2 j.val)
set_option maxRecDepth 20000 in
lemma sym1_invol : ∀ j : Fin 414, sym1 (sym1 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym2_invol : ∀ j : Fin 414, sym2 (sym2 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym11_eq : ∀ j : Fin 414,
    sym1 (sym2 (sym1 (sym2 (sym1 (sym2 j))))) = sym2 (sym1 (sym2 (sym1 (sym2 (sym1 j))))) := by
  decide +kernel
def hom1 : SigHom := pairHom sym1 sym1
def hom2 : SigHom := pairHom sym2 sym2
abbrev action1 (a : Sig) : Sig := hom1.fn a
abbrev action2 (a : Sig) : Sig := hom2.fn a
lemma action1_invol {a : Sig} (ha : Valid a) : action1 (action1 a) = a := by
  apply Prod.ext <;> dsimp [action1, hom1, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym1_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action2_invol {a : Sig} (ha : Valid a) : action2 (action2 a) = a := by
  apply Prod.ext <;> dsimp [action2, hom2, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym2_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action11_swap (a : Sig) :
    action1 (action2 (action1 (action2 (action1 (action2 a))))) =
    action2 (action1 (action2 (action1 (action2 (action1 a))))) := by
  apply Prod.ext <;> dsimp [action1, action2, hom1, hom2, pairHom] <;>
    simp only [reindex_comp] <;>
    exact congrArg (fun f => reindex f _) (funext fun j => (sym11_eq j).symm)
def homG (g : Fin 12) : SigHom :=
  match g.val with
  | 0 => pairHom id id
  | 1 => hom1
  | 2 => hom2
  | 3 => compHom hom1 hom2
  | 4 => compHom hom2 hom1
  | 5 => compHom hom1 (compHom hom2 hom1)
  | 6 => compHom hom2 (compHom hom1 hom2)
  | 7 => compHom hom1 (compHom hom2 (compHom hom1 hom2))
  | 8 => compHom hom2 (compHom hom1 (compHom hom2 hom1))
  | 9 => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 hom1)))
  | 10 => compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2)))
  | _ => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2))))
abbrev action (g : Fin 12) (a : Sig) : Sig := (homG g).fn a
def invG (g : Fin 12) : Fin 12 :=
  ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 11] g
lemma action0_eq {a : Sig} (ha : Valid a) : action 0 a = a :=
  Prod.ext (reindex_id ha.1) (reindex_id ha.2)
lemma action_valid (g : Fin 12) (a : Sig) : Valid (action g a) := (homG g).valid a
lemma action_neg (g : Fin 12) {a : Sig} (ha : Valid a) : action g (neg a) = neg (action g a) :=
  (homG g).hneg ha
lemma action_bin (g : Fin 12) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := (homG g).hbin d a b
lemma action_zero (g : Fin 12) : action g zero = zero := (homG g).hzero
lemma action_one (g : Fin 12) : action g one = one := (homG g).hone
lemma action_target (g : Fin 12) : action g target = target := (homG g).htarget
lemma action_inv (g : Fin 12) {a : Sig} (ha : Valid a) :
    action (invG g) (action g a) = a := by
  fin_cases g
  · exact (action0_eq (action_valid 0 a)).trans (action0_eq ha)
  · exact action1_invol ha
  · exact action2_invol ha
  · change action2 (action1 (action1 (action2 a))) = a
    rw [action1_invol (hom2.valid a), action2_invol ha]
  · change action1 (action2 (action2 (action1 a))) = a
    rw [action2_invol (hom1.valid a), action1_invol ha]
  · change action1 (action2 (action1 (action1 (action2 (action1 a))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action2 (action1 (action2 a))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 a))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 a))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 (action1 a))))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 (action2 a))))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 a))))))))))) = a
    rw [action11_swap]
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
lemma invG_inv (g : Fin 12) : invG (invG g) = g := by fin_cases g <;> rfl
lemma action_inj {g : Fin 12} {a b : Sig} (ha : Valid a) (hb : Valid b)
    (he : action g a = action g b) : a = b := by
  have := congrArg (action (invG g)) he
  rwa [action_inv g ha, action_inv g hb] at this
lemma action_proper (g : Fin 12) {a : Sig} (ha : proper a) : proper (action g a) := by
  refine ⟨action_valid g a, ?_, ?_⟩
  · intro h0; exact ha.2.1 (action_inj ha.1 valid_zero (h0.trans (action_zero g).symm))
  · intro h1; exact ha.2.2 (action_inj ha.1 valid_one (h1.trans (action_one g).symm))
def rawImage (g : Fin 12) (i : Fin 9) : Sig :=
  raw.getD ((rawPermCodes g >>> (4 * i.val)) &&& 15) zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw1_eq : ∀ i : Fin 9, raw.getD (perm1 i) zero = action1 (raw.getD i.val zero) := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw2_eq : ∀ i : Fin 9, raw.getD (perm2 i) zero = action2 (raw.getD i.val zero) := by
  decide +kernel
def p1 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm1 i)
def p2 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm2 i)
lemma rawImage_eq (g : Fin 12) (i : Fin 9) : rawImage g i = action g (raw.getD i.val zero) := by
  have h1 : ∀ j : Fin 9, hom1.fn (raw.getD j.val zero) = raw.getD (p1 j).val zero := fun j =>
    (raw1_eq j).symm.trans (by fin_cases j <;> rfl)
  have h2 : ∀ j : Fin 9, hom2.fn (raw.getD j.val zero) = raw.getD (p2 j).val zero := fun j =>
    (raw2_eq j).symm.trans (by fin_cases j <;> rfl)
  fin_cases g
  · have hr0 : rawImage ⟨0, by decide⟩ i = raw.getD i.val zero := by
      unfold rawImage; apply congrArg (fun k => raw.getD k zero); revert i; decide
    exact hr0.trans (action0_eq (valid_getD raw_valid i.val)).symm
  all_goals
    dsimp only [action, homG, compHom]
    simp only [h1, h2]
    unfold rawImage
    apply congrArg (fun k => raw.getD k zero)
    revert i; decide
lemma rawImage_mem (g : Fin 12) (i : Fin 9) : rawImage g i ∈ raw := by
  fin_cases g <;> fin_cases i <;> simp [rawImage, rawPermCodes, raw]
lemma action_raw_subset (g : Fin 12) : raw.toFinset.image (action g) ⊆ raw.toFinset := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [List.mem_toFinset] at hb ⊢
  have hex : ∃ i : Fin 9, raw.getD i.val zero = b := by
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
  obtain ⟨i, rfl⟩ := hex
  rw [← rawImage_eq g i]
  exact rawImage_mem g i
def Feasible (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image H.fn
lemma feasible_mono {H : SigHom} {k k' : Nat} {S : Finset Sig}
    (h : Feasible H k S) (hk : k ≤ k') : Feasible H k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm.trans hk, t, T, hl, hs⟩
lemma feasible_subset {H : SigHom} {k : Nat} {S S' : Finset Sig}
    (h : Feasible H k S) (hsub : S.image H.fn ⊆ S'.image H.fn) : Feasible H k S' := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm, t, T, hl, hs.trans hsub⟩
lemma neg_rep (w : List Sig) {a : Sig} (hva : Valid a) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases hva (Or.inl ha : represented w a) with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.2.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
lemma feasible_pull {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g) ∨ witness (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image H.fn).toList ++ [H.fn g] := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩
lemma feasible_free {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma pull_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (h : Feasible H q (insert (neg a) U)) : Feasible H (q + 1) (insert a U) := by
  apply feasible_pull (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hneg hva]
  exact neg_rep _ (H.valid a) (by simp)
lemma pull_binary {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible H q (insert (bin d a b) U)) : Feasible H (q + 1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin]
  exact bin_rep _ (H.valid a) (H.valid b) (Or.inl (by simp)) (Or.inl (by simp))
lemma free_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (neg a) U)) :
    Feasible H q (insert a U) := by
  apply feasible_free (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2.2 (by rw [H.hneg hva, hz, neg_laws.1]))
  · exact Or.inr (fun hp => hp.2.1 (by rw [H.hneg hva, ho, neg_laws.2]))
  · simp at hm
lemma free_binary_left {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin, bin_comm]
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.2.1 (bin_laws (H.valid b)).2.2.1)
    · rw [(bin_laws (H.valid b)).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws (H.valid b)).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2.2 (bin_laws (H.valid b)).2.2.2.1)
  · simp at hm
lemma free_binary_right {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (H.fn b)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h
lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom) :
    Feasible H k S := by
  induction h with
  | stop => refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩; simp [H.htarget]
  | unary ha _ _ ih => exact pull_unary ha.1 ih
  | binary _ _ _ _ _ ih => exact pull_binary ih
lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a : Sig) (ha : a ∈ S) (hc : ¬ proper (H.fn a)) :
    ∃ q < k, Feasible H q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, H.htarget]; exact target_proper)).elim
  | @unary k t U b hp _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hp.1 hc (feasible_live tail H)⟩
    · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q + 1, by omega, pull_unary hp.1 h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail H)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail H)⟩
      · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q + 1, by omega, pull_binary h⟩
lemma not_proper_bin_consts {H : SigHom} {a b : Sig} (d : Bool)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ¬ proper (H.fn (bin d a b)) := by
  rw [H.hbin]
  rcases operand_cases (H.valid a) (Or.inr hca : represented [] (H.fn a)) with ha0 | ha1 | hm
  · rw [ha0, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.2.1
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_one).2.2.1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.1
    · simp at hm'
  · rw [ha1, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).1
      · exact fun hp => hp.2.2 (bin_laws valid_zero).2.2.2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.2 (bin_laws valid_one).1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.2.2.1
    · simp at hm'
  · simp at hm
lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible H q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hpc.1 hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hpc.1 hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hpc.1 hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩
def posIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey4 (if j.val < 252 then j.val else 0))
def negIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey4 (if j.val < 252 then j.val else 0))
def homProject4 : SigHom := pairHom posIdx4 negIdx4
abbrev project4 (a : Sig) : Sig := homProject4.fn a
def posIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey0 (if j.val < 232 then j.val else 232))
def negIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey0 (if j.val < 232 then j.val else 232))
def homProject0 : SigHom := pairHom posIdx0 negIdx0
abbrev project0 (a : Sig) : Sig := homProject0.fn a
def leafIdx (j : Fin 414) : Fin 414 :=
  if h : j.val < 232 then ⟨j.val, by omega⟩ else ⟨0, by omega⟩
def homProjectLeaf : SigHom := pairHom leafIdx leafIdx
abbrev projectLeaf (a : Sig) : Sig := homProjectLeaf.fn a
def homProject (i : Fin 9) : SigHom :=
  if i.val = 4 ∨ i.val = 6 ∨ i.val = 7 then compHom homProject4 (homG (gOfV i))
  else compHom homProject0 (homG (gOfV i))
abbrev project (i : Fin 9) (a : Sig) : Sig := (homProject i).fn a
def lo232 : Nat := 2^232 - 1
def thetaWord (a : Sig) : Nat := ((a.1 &&& lo232) <<< 232) ||| (a.2 &&& lo232)
lemma thetaWord_bit (a : Sig) (j : Nat) :
    (thetaWord a).testBit j =
      if j < 232 then a.2.testBit j else if j < 464 then a.1.testBit (j - 232) else false := by
  simp only [thetaWord, lo232, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hj : j < 232
  · simp [hj, show ¬ 232 ≤ j by omega]
  · by_cases hk : j < 464
    · simp [hj, hk, show 232 ≤ j by omega, show j - 232 < 232 by omega]
    · simp [hj, hk, show 232 ≤ j by omega, show ¬ j - 232 < 232 by omega]
lemma thetaWord_target : thetaWord target = Base1007.Theta.goal 232 := by decide +kernel
lemma testBit_thetaMask (j : Nat) :
    (Base1007.Theta.mask 232).testBit j = decide (j < 464) := by
  change (2 ^ (232 + 232) - 1).testBit j = decide (j < 464)
  rw [Nat.testBit_two_pow_sub_one]
lemma thetaWord_neg {a : Sig} :
    thetaWord (neg a) = thetaWord a ^^^ Base1007.Theta.mask 232 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, thetaWord_bit, thetaWord_bit, testBit_thetaMask]
  by_cases hl : j < 232
  · simp [hl, neg, testBit_bnot_lt _ (show j < 414 by omega), show j < 464 by omega]
  · by_cases hh : j < 464
    · simp [hl, hh, neg, testBit_bnot_lt _ (show j - 232 < 414 by omega)]
    · simp [hl, hh]
lemma thetaWord_bin (d : Bool) (a b : Sig) :
    thetaWord (bin d a b) =
      if d then thetaWord a ||| thetaWord b else thetaWord a &&& thetaWord b := by
  apply Nat.eq_of_testBit_eq; intro j
  cases d <;> simp only [bin, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_or,
    Nat.testBit_and, thetaWord_bit] <;> split_ifs <;> rfl
lemma live_thetaRun {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup) (he : v.toFinset = S) :
    Base1007.Theta.NatRun (Base1007.Theta.mask 232) (Base1007.Theta.goal 232) k (v.map thetaWord) := by
  induction h generalizing v with
  | stop =>
    have hp : ([target] : List Sig).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    have hp' := hp.map thetaWord
    simp only [List.map_cons, List.map_nil, thetaWord_target] at hp'
    exact Base1007.Theta.Run.perm hp' Base1007.Theta.Run.done
  | @unary k t U a ha hf _ ih =>
    let rest := dropped [a] v
    have ham : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn, eq⟩ := edit_list (del := [a]) hv (by simp) (by simpa using he)
    let save := decide (a ∈ U)
    have hkeep : Base1007.Theta.kept save a rest = keepOf U [a] ++ rest := by
      by_cases hm : a ∈ U <;> simp [save, Base1007.Theta.kept, keepOf, hm]
    rw [← hkeep] at hn eq
    have hs : (neg a :: Base1007.Theta.kept save a rest).toFinset = insert (neg a) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (neg a :: Base1007.Theta.kept save a rest).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem ?_), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (recover_perm [a] v hv (by simp) (by simpa using ham)).symm.map thetaWord
    have hdone := ih _ hnd hs
    have hmap : (neg a :: Base1007.Theta.kept save a rest).map thetaWord =
        (thetaWord a ^^^ Base1007.Theta.mask 232) ::
          Base1007.Theta.kept save (thetaWord a) (rest.map thetaWord) := by
      cases save <;> simp [Base1007.Theta.kept, thetaWord_neg]
    rw [hmap] at hdone
    exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.one true save hdone)
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest := dropped [a, b] v
    have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) hv (by simp [hab]) (by simpa using he)
    let sa := decide (a ∈ U)
    let sb := decide (b ∈ U)
    have hkeep : Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest) = keepOf U [a, b] ++ rest := by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;>
        simp [sa, sb, Base1007.Theta.kept, keepOf, ham, hbm]
    rw [← hkeep] at hn eq
    have hs : (bin d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).toFinset =
        insert (bin d a b) U := by rw [List.toFinset_cons, eq]
    have hnd : (bin d a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (recover_perm [a, b] v hv (by simp [hab]) (by simp [ah, bh])).symm.map thetaWord
    have hdone := ih _ hnd hs
    have hkeptMap (x : Sig) (l : List Sig) (fl : Bool) :
        (Base1007.Theta.kept fl x l).map thetaWord =
        Base1007.Theta.kept fl (thetaWord x) (l.map thetaWord) := by
      cases fl <;> simp [Base1007.Theta.kept]
    cases d
    · have hmap : (bin false a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).map thetaWord =
          (thetaWord a &&& thetaWord b) ::
            Base1007.Theta.kept sa (thetaWord a) (Base1007.Theta.kept sb (thetaWord b) (rest.map thetaWord)) := by
        simp [List.map_cons, thetaWord_bin, hkeptMap]
      rw [hmap] at hdone
      exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.two true sa sb hdone)
    · have hmap : (bin true a b :: Base1007.Theta.kept sa a (Base1007.Theta.kept sb b rest)).map thetaWord =
          (thetaWord a ||| thetaWord b) ::
            Base1007.Theta.kept sa (thetaWord a) (Base1007.Theta.kept sb (thetaWord b) (rest.map thetaWord)) := by
        simp [List.map_cons, thetaWord_bin, hkeptMap]
      rw [hmap] at hdone
      exact Base1007.Theta.Run.perm p (Base1007.Theta.Run.two false sa sb hdone)
def thetaOrder : List Sig := [raw2, raw8, raw3, raw1, raw6, raw7, raw5]
def thetaInputs : List Sig := thetaOrder.map (fun a => projectLeaf (project0 a))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma project0_raw0 : project0 raw0 = zero := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectLeaf_project0_raw4 : projectLeaf (project0 raw4) = zero := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaInputs_word : thetaInputs.map thetaWord = Base1007.Theta.xs517 := by decide +kernel
lemma thetaWords_nodup : Base1007.Theta.xs517.Nodup := by decide +kernel
lemma thetaInputs_nd : thetaInputs.Nodup := by
  have h := thetaWords_nodup
  rw [← thetaInputs_word] at h
  exact List.Nodup.of_map _ h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bit232_unique : raw.all (fun a => decide (a = raw4) || !(sep true (project0 a)).testBit 232) = true := by
  decide +kernel
lemma root_project0_impossible : ¬ Feasible homProject0 11 raw.toFinset := by
  rintro ⟨m, hm, t, T, hl, hsub⟩
  have h4 : project0 raw4 ∈ T := by
    obtain ⟨x, hxT, hsep⟩ := live_sep hl 232 (by omega)
    obtain ⟨a, haRaw, rfl⟩ := Finset.mem_image.mp (hsub hxT)
    have hsw := sep_weaken t (live_proper hl _ hxT).1 232 (by omega) hsep
    have hall := List.all_eq_true.mp bit232_unique a (List.mem_toFinset.mp haRaw)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hall
    rcases hall with rfl | hf
    · exact hxT
    · exact False.elim (by rw [hsw] at hf; contradiction)
  have hz4 : ¬ proper (homProjectLeaf.fn (project0 raw4)) := fun hp =>
    hp.2.1 projectLeaf_project0_raw4
  obtain ⟨q, hq, m', hm', t', T', hl', hT'⟩ := feasible_const hl homProjectLeaf (project0 raw4) h4 hz4
  have hsubTheta : ∀ a ∈ T', a ∈ thetaInputs := by
    intro a ha
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp (hT' ha)
    obtain ⟨c, hcRaw, rfl⟩ := Finset.mem_image.mp (hsub hbT)
    have hcm := List.mem_toFinset.mp hcRaw
    by_cases hc0 : c = raw0
    · subst c
      have h0 : projectLeaf (project0 raw0) = zero := by
        rw [project0_raw0]; exact homProjectLeaf.hzero
      exact False.elim ((live_proper hl' _ ha).2.1 h0)
    by_cases hc4 : c = raw4
    · subst c
      exact False.elim ((live_proper hl' _ ha).2.1 projectLeaf_project0_raw4)
    · have hmem : c ∈ thetaOrder := by
        simp only [raw, thetaOrder, List.mem_cons, List.not_mem_nil, or_false] at hcm ⊢
        rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      exact List.mem_map_of_mem hmem
  let v := thetaInputs.filter (fun a => decide (a ∈ T'))
  have he : v.toFinset = T' := by
    ext a; simp only [v, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨hsubTheta _ ha, ha⟩⟩
  have hrun := live_thetaRun hl' v (thetaInputs_nd.filter _) he
  apply Base1007.Theta.noSub (show m' ≤ 10 by omega) _ hrun
  have sub := List.Sublist.map thetaWord (List.filter_sublist (l := thetaInputs) (p := fun a => decide (a ∈ T')))
  rwa [thetaInputs_word] at sub

open PEqualNP.MetaComplexity

private def readsFixed (g : Gate) : Bool :=
  [0, 9].any fun i => g.inputs.contains i

private theorem fixed_gate_rep (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (unary : g.op = GateOp.not → g.inputs.length ≤ 1)
    (fixed : ∀ i ∈ [0, 9], w.getD i zero = zero ∨ w.getD i zero = one)
    (read : readsFixed g = true) : represented w (gv w g) := by
  obtain ⟨op, l⟩ := g
  have hread : ∃ i ∈ l, w.getD i zero = zero ∨ w.getD i zero = one := by
    obtain ⟨i,hi,hl⟩ : ∃ i ∈ [0, 9], i ∈ l := by
      simpa [readsFixed, List.any_eq_true] using read
    exact ⟨i, hl, fixed i hi⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  obtain ⟨hop, hlen⟩ := hg
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  match l with
  | [] => simp at hread
  | [i] =>
    have hc : w.getD i zero = zero ∨ w.getD i zero = one := by simpa using hread
    rcases hop with rfl | rfl | rfl
    · change represented w (bin false (w.getD i zero) one)
      rw [(bin_laws (valid_getD hw i)).1]
      exact get_rep w i
    · change represented w (bin true (w.getD i zero) zero)
      rw [(bin_laws (valid_getD hw i)).2.1]
      exact get_rep w i
    · change represented w (neg (w.getD i zero))
      rcases hc with h | h
      · rwa [h, neg_laws.1]
      · rwa [h, neg_laws.2]
  | [i, j] =>
    have hc : (w.getD i zero = zero ∨ w.getD i zero = one) ∨
        (w.getD j zero = zero ∨ w.getD j zero = one) := by simpa using hread
    obtain ⟨i1,i0,iz,io,_,_⟩ := bin_laws (valid_getD hw i)
    obtain ⟨j1,j0,jz,jo,_,_⟩ := bin_laws (valid_getD hw j)
    rcases hop with rfl | rfl | rfl
    · change represented w (bin false (w.getD i zero) (bin false (w.getD j zero) one))
      rw [j1]
      rcases hc with (h | h) | (h | h)
      · rw [h, bin_comm, jz]; exact rz
      · rw [h, bin_comm, j1]; exact get_rep _ _
      · rw [h, iz]; exact rz
      · rw [h, i1]; exact get_rep _ _
    · change represented w (bin true (w.getD i zero) (bin true (w.getD j zero) zero))
      rw [j0]
      rcases hc with (h | h) | (h | h)
      · rw [h, bin_comm, j0]; exact get_rep _ _
      · rw [h, bin_comm, jo]; exact ro
      · rw [h, i0]; exact get_rep _ _
      · rw [h, io]; exact ro
    · have h := unary rfl
      simp at h
  | _ :: _ :: _ :: _ => simp at hlen

private theorem extract_count (gs : List Gate) (w : List Sig)
    (hw : ∀ a ∈ w, Valid a) (wf : ∀ i ∈ [0, 9], i < w.length)
    (fixed : ∀ i ∈ [0, 9], w.getD i zero = zero ∨ w.getD i zero = one)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (unary : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k + (gs.filter readsFixed).length ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hg := legal g (by simp)
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k,t,S,hk,run,sub⟩ := ih (w ++ [gv w g]) hw'
      (fun i hi => Nat.lt_of_lt_of_le (wf i hi) (by simp))
      (fun i hi => by rw [List.getD_append _ _ _ _ (wf i hi)]; exact fixed i hi)
      (fun g' hg' => legal g' (by simp [hg']))
      (fun g' hg' => unary g' (by simp [hg']))
      hout
    cases read : readsFixed g
    · obtain ⟨l,u,T,hl,hT,hsub⟩ := pull_gate run (gate_rep hw g hg) sub
      exact ⟨l,u,T,by simp [read]; omega,hT,hsub⟩
    · have rep := fixed_gate_rep w hw g hg (unary g (by simp)) fixed read
      refine ⟨k,t,S,by simp [read]; omega,run,?_⟩
      intro v hv
      rcases (by simpa using sub v hv : v ∈ w ∨ v = gv w g) with h | rfl
      · exact h
      · exact rep.resolve_right (fun hn => hn (live_proper run _ hv))

private def cofactor (x : Fin 8 → Bool) : Bool :=
  ([1,10,19,5,14,23,38,47,60] : List ℕ).any fun l =>
    x (Fin.ofNat 8 (l / 8)) && x (Fin.ofNat 8 (l % 8))

private def start : List Sig := raw.map project0 ++ [one]

private def restrictedRow (s : Bool) (i : Fin 414) : Fin 414 :=
  if s then posIdx0 i else negIdx0 i

private def assignment (s : Bool) (i : Fin 414) (j : Fin 8) : Bool :=
  sample s (restrictedRow s i) j.succ

private theorem projected_bit (s : Bool) (i : Fin 414) (a : Sig) :
    bit s i (project0 a) = bit s (restrictedRow s i) a := by
  cases s <;> simp [bit, project0, homProject0, pairHom, reindex_testBit, i.isLt, restrictedRow]

private theorem sample_zero (s : Bool) (i : Fin 414) : sample s (restrictedRow s i) 0 = false := by
  have h := projected_bit s i raw0
  rw [project0_raw0, bit_zero] at h
  exact h.symm

private theorem cofactor_correct (s : Bool) (i : Fin 414) : cofactor (assignment s i) = s := by
  have zero := sample_zero s i
  have full := sample_ok s (restrictedRow s i)
  have he : cofactor (assignment s i) = edgeF (sample s (restrictedRow s i)) := by
    simp [cofactor, assignment, edgeF, zero, Fin.ofNat, List.any, Bool.or_assoc]
  exact he.trans full

private theorem start_bits (s : Bool) (i : Fin 414) :
    start.map (bit s i) = false :: List.ofFn (assignment s i) ++ [true] := by
  unfold start
  rw [List.map_append, List.map_map]
  have eq : (fun a => bit s i (project0 a)) = bit s (restrictedRow s i) := by
    funext a; exact projected_bit s i a
  rw [show bit s i ∘ project0 = fun a => bit s i (project0 a) from rfl, eq,
      ← sample_list, List.ofFn_succ]
  simp [assignment, sample_zero, bit_one]

private theorem start_valid : ∀ a ∈ start, Valid a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact homProject0.valid b
  · obtain rfl : a = one := by simpa using ha
    exact valid_one

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem start_constants : start.getD 0 zero = zero ∧ start.getD 9 zero = one := by
  constructor
  · change project0 raw0 = zero
    exact project0_raw0
  · rfl

private theorem target_in_execution (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 8 → Bool, C.eval (false :: List.ofFn x ++ [true]) = cofactor x) :
    target ∈ execute C.gates start := by
  let w := execute C.gates start
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates start start_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates start).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ start_valid (fun g hg => (fan g hg).1), start_bits]
    exact (correct (assignment s i)).trans (cofactor_correct s i)
  have hvout := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private theorem main (C : Circuit) (fan : FanInTwo C)
    (unary : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (budget : (C.gates.filter readsFixed).length = 2)
    (correct : ∀ x : Fin 8 → Bool, C.eval (false :: List.ofFn x ++ [true]) = cofactor x) :
    14 ≤ C.size := by
  by_contra! small
  have wlen : start.length = 10 := by rfl
  obtain ⟨k,t,S,hk,run,sub⟩ := extract_count C.gates start start_valid
    (fun i hi => by rcases (by simpa using hi : i = 0 ∨ i = 9) with rfl | rfl <;> simp [wlen])
    (fun i hi => by
      rcases (by simpa using hi : i = 0 ∨ i = 9) with rfl | rfl
      · exact Or.inl start_constants.1
      · exact Or.inr start_constants.2)
    fan unary (target_in_execution C fan correct)
  apply root_project0_impossible
  refine ⟨k, ?_, t, S, run, ?_⟩
  · change C.gates.length < 14 at small
    omega
  · intro a ha
    have pm : a ∈ raw.map project0 := by
      rcases List.mem_append.mp (sub a ha) with h | h
      · exact h
      · obtain rfl : a = one := by simpa using h
        exact False.elim ((live_proper run _ ha).2.2 rfl)
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp pm
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)

end Main1672
end PEqualNP.Outside.L_meta_3212

theorem PEqualNP.Outside.L_meta_3212 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5) x1.gates).length = (2 : ℕ) → (∀ (x5 : Fin (8 : ℕ) → Bool), x1.eval (Bool.false :: List.ofFn x5 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (8 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (8 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  exact PEqualNP.Outside.L_meta_3212.Main1672.main
