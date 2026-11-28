import Lean

namespace BCMP430.Streams

abbrev Digits := Nat → Int

def decode (s : Int) (a : Digits) : Digits := fun i =>
  if i % 2 = 0 then s - a i else a i - 1

def encode (s : Int) (d : Digits) : Digits := fun i =>
  if i % 2 = 0 then s - d i else d i + 1

def shift (a : Digits) : Digits := fun i => a (i+1)
def twisted (s : Int) (d : Digits) : Digits := fun i => s-1-d (i+1)

def run (f : Digits → Digits) (a : Digits) : Nat → Digits
  | 0 => a
  | k+1 => f (run f a k)

def BeforeEq (a b : Digits) (i : Nat) := ∀ j, j < i → a j = b j

def LexLt (a b : Digits) := ∃ i, BeforeEq a b i ∧ a i < b i

def AltLt (a b : Digits) := ∃ i, BeforeEq a b i ∧
  (if i % 2 = 0 then a i > b i else a i < b i)

theorem inverse_decode (s : Int) (a : Digits) : encode s (decode s a) = a := by
  funext i
  by_cases h : i % 2 = 0 <;> simp [encode, decode, h] <;> omega

theorem inverse_encode (s : Int) (d : Digits) : decode s (encode s d) = d := by
  funext i
  by_cases h : i % 2 = 0 <;> simp [encode, decode, h] <;> omega

theorem valid_digits_iff (s : Int) (a : Digits) :
    (∀ i, 0 ≤ decode s a i ∧ decode s a i < s) ↔ (∀ i, 1 ≤ a i ∧ a i ≤ s) := by
  constructor <;> intro h i <;> specialize h i <;> by_cases he : i % 2 = 0 <;>
    simp only [decode, he, ite_true, ite_false] at * <;> omega

theorem step (s : Int) (a : Digits) : decode s (shift a) = twisted s (decode s a) := by
  funext i
  by_cases h : i % 2 = 0
  · have h' : (i+1) % 2 ≠ 0 := by omega
    simp only [decode, shift, twisted, h, h', ite_true, ite_false]; omega
  · have h' : (i+1) % 2 = 0 := by omega
    simp only [decode, shift, twisted, h, h', ite_true, ite_false]; omega

theorem steps (s : Int) (a : Digits) (k : Nat) :
    decode s (run shift a k) = run (twisted s) (decode s a) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [run, step, ih]

private theorem before_iff (s : Int) (a b : Digits) (i : Nat) :
    BeforeEq (decode s a) (decode s b) i ↔ BeforeEq a b i := by
  constructor <;> intro h j hj <;> specialize h j hj <;> by_cases he : j % 2 = 0 <;>
    simp only [decode, he, ite_true, ite_false] at * <;> omega

theorem order_iff (s : Int) (a b : Digits) : LexLt (decode s a) (decode s b) ↔ AltLt a b := by
  constructor <;> rintro ⟨i,hp,hi⟩
  · refine ⟨i,(before_iff s a b i).mp hp,?_⟩
    by_cases h : i % 2 = 0 <;> simp only [decode, h, ite_true, ite_false] at * <;> omega
  · refine ⟨i,(before_iff s a b i).mpr hp,?_⟩
    by_cases h : i % 2 = 0 <;> simp only [decode, h, ite_true, ite_false] at * <;> omega

theorem orbit_min_iff (s : Int) (a : Digits) :
    (∀ k, ¬ AltLt (run shift a k) a) ↔
    (∀ k, ¬ LexLt (run (twisted s) (decode s a) k) (decode s a)) := by
  simp only [← steps, order_iff]

#print axioms valid_digits_iff
#print axioms steps
#print axioms inverse_decode
#print axioms inverse_encode
#print axioms order_iff
#print axioms orbit_min_iff

end BCMP430.Streams
