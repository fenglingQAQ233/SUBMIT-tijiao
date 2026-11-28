import DominantOrbit
import NeutralAmplify

namespace BCMP430.DominantWindow
open Dominant Amplify Direct Original WordWindow Witness Germ Filter
open scoped Topology

private theorem flat_cat (p q : Pairs) : flatten (p++q) = flatten p ++ flatten q := by
  induction p with
  | nil => rfl
  | cons z t ih => obtain ⟨a,b⟩ := z; simp [flatten,ih]

private theorem nonempty_flat {p : Pairs} (h : p ≠ []) : flatten p ≠ [] := by
  cases p with
  | nil => contradiction
  | cons z t => obtain ⟨a,b⟩ := z; simp [flatten]

/-- (s,1) is the least two-digit block in alternating order; no longer bounded
    dominant word may end in it, even though a general bounded word can. -/
theorem no_terminal_zero_pair {s : ℤ} {p : Pairs} (hp : p ≠ [])
    (hd : Dom (flatten (p++[(s,1)]))) (bd : Bounded s (flatten (p++[(s,1)]))) : False := by
  have suff : Tail (flatten (p++[(s,1)])) [s,1] := ⟨flatten p,nonempty_flat hp,by simp,flat_cat ..⟩
  have cmp := hd.2.2 _ suff
  cases p with
  | nil => contradiction
  | cons z ts =>
    obtain ⟨a,b⟩ := z
    change ltWord true (a::b::flatten (ts++[(s,1)])) [s,1] at cmp
    have aa := bd a (by simp [flatten])
    have bb := bd b (by simp [flatten])
    by_cases e : a=s
    · subst a
      by_cases f : b=1
      · subst b; simp [ltWord] at cmp
      · simp [ltWord,f] at cmp; omega
    · simp [ltWord,e] at cmp; omega

private theorem pair_val {s : ℤ} (hs : 2≤s) (a b : ℤ) (v : ℝ) :
    branch s a (branch s b v) = Tape.consDigit s (s-a) (Tape.consDigit s (b-1) v) := by
  have hn : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  unfold branch Tape.consDigit; push_cast; field_simp; ring

/-- A two-digit terminal pair with its at most one padding zero. -/
private def lastWord (s a b : ℤ) : ClockTotal.Word :=
  if b=1 then .one (s-a) else .two (s-a) (b-1)
private def build (s : ℤ) : Pairs → ℤ → ℤ → ClockTotal.Word
  | [], a,b => lastWord s a b
  | (c,d)::p, a,b => .more (s-c) (d-1) (build s p a b)

private theorem identities {s : ℤ} (hs : 2≤s) (p : Pairs) (a b : ℤ) :
    Tape.val s (build s p a b) = eval s (flatten (p++[(a,b)])) 0 ∧
    ClockTotal.padded (build s p a b) = BCMP430.decode s (p++[(a,b)]) := by
  induction p with
  | nil =>
    simp only [List.nil_append,flatten,eval,build,BCMP430.decode,pair_val hs]
    by_cases e : b=1
    · subst b; simp [lastWord,ClockTotal.padded,Tape.val,Tape.consDigit]
    · simp [lastWord,e,ClockTotal.padded,Tape.val]
  | cons z p ih =>
    obtain ⟨c,d⟩ := z
    simp only [List.cons_append,flatten,eval,build,BCMP430.decode,ClockTotal.padded,Tape.val,pair_val hs,ih.1,ih.2,and_self]

private theorem canonicalGood {s a b : ℤ} (p : Pairs)
    (bv : Bounded s (flatten (p++[(a,b)]))) (lastOK : (a,b) ≠ (s,1)) :
    ClockTotal.Good s (build s p a b) := by
  induction p with
  | nil =>
    have ha := bv a (by simp [flatten])
    have hb := bv b (by simp [flatten])
    by_cases e : b=1
    · subst b; have ne : a≠s := fun h => lastOK (by rw [h])
      have h₁ : 0 < s-a := by omega
      have h₂ : s-a < s := by omega
      exact (show ClockTotal.Good s (.one (s-a)) from ⟨h₁,h₂⟩)
    · simp only [build,lastWord,e,ite_false,ClockTotal.Good]; omega
  | cons z p ih =>
    obtain ⟨c,d⟩ := z
    have hc := bv c (by simp [flatten])
    have hdd := bv d (by simp [flatten])
    exact ⟨by omega,by omega,by omega,by omega,ih (fun v h => bv v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))⟩

/-- Direct bridge from a bounded dominant CF word to stable matching of the
    original map. The lone exceptional pair has decoded value 0, not an interior center. -/
theorem dominant_window {s : ℤ} (hs : 2≤s) (p : Pairs) (a b : ℤ)
    (hd : Dom (flatten (p++[(a,b)]))) (bv : Bounded s (flatten (p++[(a,b)])))
    (notOrigin : p++[(a,b)] ≠ [(s,1)]) :
    let W := p++[(a,b)]
    let x := eval s (flatten W) 0
    0<x ∧ x<1 ∧ ∃ i j : ℕ, (i:ℤ)-j=(s+1)*ctIndex W ∧
      ∀ᶠ η in 𝓝 x, Meets s η i j ∧
        ∀ u ≤ i, ∀ v ≤ j, Meets s η u v → (u:ℤ)-v=(s+1)*ctIndex W := by
  have terminalOK : (a,b) ≠ (s,1) := by
    intro e
    have ea : a=s := congrArg Prod.fst e
    have eb : b=1 := congrArg Prod.snd e
    subst a; subst b
    by_cases hn : p=[]
    · subst p; exact notOrigin rfl
    · exact no_terminal_zero_pair hn hd bv
  have good := canonicalGood p bv terminalOK
  obtain ⟨eqV,eqD⟩ := identities hs p a b
  have unit := Tape.in_unit hs _ good
  rw [eqV] at unit
  have clear := dominant_clear hs hd bv unit.1 unit.2
  rw [←eqV] at clear
  obtain ⟨i,j,lag,H⟩ := window_of_word hs _ good clear
  rw [eqD,index_decode] at lag H
  rw [eqV] at H
  refine ⟨unit.1,unit.2,i,j,lag,?_⟩
  filter_upwards [H] with η h using ⟨h.1,h.2.2.2⟩

#print axioms no_terminal_zero_pair
#print axioms dominant_window
end BCMP430.DominantWindow
