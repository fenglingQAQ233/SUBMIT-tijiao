import DigitPairs

namespace BCMP430.Dominant

abbrev Word := List Int
/-- Strict alternating comparison: a proper prefix alone gives no verdict. -/
def ltWord (rev : Bool) : Word → Word → Prop
  | x::xs, y::ys => if x=y then ltWord (!rev) xs ys else if rev then y<x else x<y
  | _, _ => False

def Tail (w z : Word) := ∃ p, p ≠ [] ∧ z ≠ [] ∧ w=p++z
def Dom (w : Word) := w ≠ [] ∧ w.length%2=0 ∧ ∀ z, Tail w z → ltWord true w z

def copies (w z : Word) : Nat → Word
  | 0 => z
  | n+1 => w ++ copies w z n

private theorem extendCmp {b : Bool} {w z : Word} (h : ltWord b w z) (u v : Word) :
    ltWord b (w++u) (z++v) := by
  induction w generalizing z b with
  | nil => cases z <;> contradiction
  | cons x xs ih =>
    cases z with
    | nil => contradiction
    | cons y ys =>
      by_cases he : x=y
      · simp only [List.cons_append, ltWord, he, ite_true] at h ⊢
        exact ih h
      · simpa only [List.cons_append, ltWord, he, ite_false] using h

private theorem sameEven (p : Word) (he : p.length%2=0) {w z : Word} (h : ltWord true w z) :
    ltWord true (p++w) (p++z) := by
  match p with
  | [] => exact h
  | [_] => simp at he
  | x::y::rest =>
    have hrest : rest.length%2=0 := by simp only [List.length_cons] at he; omega
    simpa only [List.cons_append, ltWord, ite_true, Bool.not_true, Bool.not_false] using
      sameEven rest hrest h

private theorem tailTrans {u v w : Word} (h : Tail u v) (hh : Tail v w) : Tail u w := by
  obtain ⟨a,ha,_,rfl⟩ := h
  obtain ⟨b,_,hw,rfl⟩ := hh
  exact ⟨a++b,by simp [ha],hw,List.append_assoc .. |>.symm⟩

/-- Every proper suffix starts at a copy boundary or inside one original block. -/
private theorem cuts {w b : Word} (hb : Tail w b) (m : Nat) (z : Word) (hz : Tail (copies w b m) z) :
    (∃ j<m, z=copies w b j) ∨ (∃ t u, Tail w t ∧ z=t++u) := by
  induction m generalizing z with
  | zero => exact Or.inr ⟨z,[],tailTrans hb hz,by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hz',he⟩ := hz
    change w++copies w b m = a++z at he
    rcases List.append_eq_append_iff.mp he with ⟨p,hp,eq⟩ | ⟨p,hp,eq⟩
    · by_cases hn : p=[]
      · subst p; exact Or.inl ⟨m,by omega,by simpa using eq.symm⟩
      · rcases ih z ⟨p,hn,hz',eq⟩ with ⟨j,hj,hj'⟩ | hh
        · exact Or.inl ⟨j,by omega,hj'⟩
        · exact Or.inr hh
    · by_cases hn : p=[]
      · subst p; exact Or.inl ⟨m,by omega,by simpa using eq⟩
      · exact Or.inr ⟨p,copies w b m,⟨a,ha,hn,hp⟩,eq⟩

private theorem atBoundary {w b : Word} (hw : Dom w) (hb : Tail w b) (m j : Nat) (hj : j<m) :
    ltWord true (copies w b m) (copies w b j) := by
  induction j generalizing m with
  | zero =>
    cases m with
    | zero => omega
    | succ m => simpa [copies] using extendCmp (hw.2.2 b hb) (copies w b m) []
  | succ j ih =>
    cases m with
    | zero => omega
    | succ m => exact sameEven w hw.2.1 (ih m (by omega))

private theorem length_copies (w b : Word) (m : Nat) :
    (copies w b m).length = m*w.length+b.length := by
  induction m with
  | zero => simp [copies]
  | succ m ih => simp only [copies,List.length_append,ih,Nat.succ_mul]; omega

/-- CT lemma 32, with the suffix explicitly required to be nonempty and even. -/
theorem suffix_amplification {w b : Word} (hw : Dom w) (hb : Tail w b) (even : b.length%2=0)
    (m : Nat) (hm : 0<m) : Dom (copies w b m) := by
  cases m with
  | zero => omega
  | succ m =>
    refine ⟨by simp [copies,hw.1],?_,?_⟩
    · rw [length_copies,Nat.add_mod,Nat.mul_mod,hw.2.1,even]; simp
    · intro z hz
      rcases cuts hb (m+1) z hz with ⟨j,hj,rfl⟩ | ⟨t,u,ht,rfl⟩
      · exact atBoundary hw hb _ j hj
      · exact extendCmp (hw.2.2 t ht) (copies w b m) u

private theorem runEnds (a : Int) (xs : Word) :
    (∃ pre, a::xs=pre++[a]) ∨ (∃ pre b tail, a::xs=pre++a::b::tail ∧ b≠a) := by
  induction xs with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons x xs ih =>
    by_cases hx : x=a
    · subst x
      rcases ih with ⟨pre,h⟩ | ⟨pre,b,tail,h,hn⟩
      · exact Or.inl ⟨a::pre, congrArg (List.cons a) h⟩
      · exact Or.inr ⟨a::pre,b,tail,congrArg (List.cons a) h,hn⟩
    · exact Or.inr ⟨[],x,xs,rfl,hx⟩

/-- CT lemma 33. A maximal run of equal first digits gives incompatible suffix tests. -/
theorem distinct_heads {a b : Int} {xs : Word} (hw : Dom (a::b::xs)) : a ≠ b := by
  intro h; subst b
  rcases runEnds a xs with ⟨pre,h⟩ | ⟨pre,b,tail,h,hba⟩
  · have lt := hw.2.2 [a] ⟨a::pre,by simp,by simp, congrArg (List.cons a) h⟩
    simp [ltWord] at lt
  · have ht : Tail (a::a::xs) (a::b::tail) := ⟨a::pre,by simp,by simp,congrArg (List.cons a) h⟩
    have ht' : Tail (a::b::tail) (b::tail) := ⟨[a],by simp,by simp,rfl⟩
    have h₁ := hw.2.2 _ ht
    have h₂ := hw.2.2 _ (tailTrans ht ht')
    simp [ltWord,Ne.symm hba] at h₁ h₂
    omega

#print axioms suffix_amplification
#print axioms distinct_heads
end BCMP430.Dominant
