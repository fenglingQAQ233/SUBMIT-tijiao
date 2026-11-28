import Lean

namespace BCMP430

abbrev Pairs := List (Int × Int)

def decode (s : Int) : Pairs → List Int
  | [] => []
  | (a,b) :: ps => (s-a) :: (b-1) :: decode s ps

def weight (s : Int) : List Int → Int
  | [] => 0
  | d :: ds => (s - 1 - 2*d) + weight s ds

def ctIndex : Pairs → Int
  | [] => 0
  | (a,b) :: ps => (a-b) + ctIndex ps

theorem weight_decode (s : Int) (ps : Pairs) :
    weight s (decode s ps) = ctIndex ps + ctIndex ps := by
  induction ps with
  | nil => rfl
  | cons pair ps ih =>
    obtain ⟨a,b⟩ := pair
    simp only [decode, weight, ctIndex, ih]
    omega

def indexFromDigits (s : Int) (ds : List Int) : Int :=
  ((s + 1) * weight s ds) / 2

theorem index_decode (s : Int) (ps : Pairs) :
    indexFromDigits s (decode s ps) = (s + 1) * ctIndex ps := by
  unfold indexFromDigits
  rw [weight_decode, Int.mul_add]
  omega

theorem digits_in_range (s a b : Int) (ha : 1 ≤ a ∧ a ≤ s)
    (hb : 1 ≤ b ∧ b ≤ s) :
    (0 ≤ s-a ∧ s-a < s) ∧ (0 ≤ b-1 ∧ b-1 < s) := by
  omega

#print axioms weight_decode
#print axioms index_decode
#print axioms digits_in_range

end BCMP430
