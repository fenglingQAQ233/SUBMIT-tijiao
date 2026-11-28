import WordNeighborhood

namespace BCMP430.Origin
open Original Tape ClockTotal WordWindow Adic Witness Germ Filter
open scoped Topology

/-- n=0 is the word 01; increasing n inserts two leading zero digits. -/
def spike : ℕ → Word
  | 0 => .two 0 1
  | n+1 => .more 0 0 (spike n)

private theorem good {s : ℤ} (hs : 2 ≤ s) (n : ℕ) : Good s (spike n) := by
  induction n with
  | zero => exact ⟨by omega,by omega,by omega,by omega⟩
  | succ n ih => exact ⟨by omega,by omega,by omega,by omega,ih⟩

private theorem scaled {s : ℤ} (hs : 2 ≤ s) (n : ℕ) :
    (s:ℝ)^(2*n+2)*val s (spike n)=1 := by
  have h : (s:ℝ)≠0 := by exact_mod_cast (show s≠0 by omega)
  induction n with
  | zero => change (s:ℝ)^2*consDigit s 0 (consDigit s 1 0)=1; unfold consDigit; push_cast; field_simp; ring
  | succ n ih =>
    change (s:ℝ)^(2*(n+1)+2)*consDigit s 0 (consDigit s 0 (val s (spike n)))=1
    rw [show 2*(n+1)+2=(2*n+2)+2 by omega,pow_add]
    unfold consDigit; push_cast; field_simp
    simpa only [mul_zero, zero_add] using ih

private theorem grid_g {s : ℤ} {n : ℕ} {x : ℝ} (h : GridAt s n x) : GridAt s n (g s x) := by
  obtain ⟨c,hc⟩ := h
  refine ⟨-s*c-s^n*⌊-(s:ℝ)*x⌋,?_⟩
  unfold g Int.fract; push_cast; rw [←hc]; ring

/-- The first negative-base iterate already lies on a coarser grid; consequently every
    positive iterate is strictly larger than this particular center, or is zero. -/
private theorem clear {s : ℤ} (hs : 2≤s) (n : ℕ) : Clear s (val s (spike n)) (val s (spike n)) := by
  let x := val s (spike n)
  let k := 2*n+1
  have s1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp : (0:ℝ)<s := lt_trans zero_lt_one s1
  have hp : (s:ℝ)^k*(s*x)=1 := by rw [←mul_assoc,←pow_succ]; exact scaled hs n
  have hfirst : GridAt s k (g s x) := by
    refine ⟨-1-s^k*⌊-(s:ℝ)*x⌋,?_⟩
    unfold g Int.fract; push_cast; rw [mul_sub,neg_mul,mul_neg,hp]
  intro j
  have mem : GridAt s k ((g s)^[j+1] x) := by
    induction j with
    | zero => exact hfirst
    | succ j ih => rw [Function.iterate_succ_apply']; exact grid_g ih
  obtain ⟨c,hc⟩ := mem
  have hpos : (0:ℝ)<(s:ℝ)^k := pow_pos sp _
  have hnon : 0≤(g s)^[j+1] x := by rw [Function.iterate_succ_apply']; exact Int.fract_nonneg _
  by_cases he : (g s)^[j+1] x=0
  · exact Or.inl he
  · right
    have hcp : (0:ℝ)<c := hc ▸ mul_pos hpos (lt_of_le_of_ne hnon (Ne.symm he))
    have hc1 : (1:ℝ)≤c := by exact_mod_cast (show (1:ℤ)≤c by exact_mod_cast hcp : (1:ℤ)≤c)
    have hx : 0<x := (in_unit hs _ (good hs n)).1
    change x < _
    apply (mul_lt_mul_iff_of_pos_left hpos).mp
    rw [hc]; nlinarith [mul_pos (sub_pos.mpr s1) (mul_pos hpos hx)]

private theorem half {s : ℤ} (n : ℕ) : halfWeight s (spike n) = ((n:ℤ)+1)*(s-1)-1 := by
  induction n with
  | zero => simp [spike,halfWeight]
  | succ n ih => simp only [spike,halfWeight,ih,Nat.cast_succ]; ring

private theorem wt (s : ℤ) (n : ℕ) : weight s (padded (spike n))=2*(((n:ℤ)+1)*(s-1)-1) := by
  induction n with
  | zero => simp [spike,padded,weight]; ring
  | succ n ih => simp only [spike,padded,weight,ih,Nat.cast_succ]; ring

def lag (s : ℤ) (n : ℕ) := (s+1)*(((n:ℤ)+1)*(s-1)-1)

private theorem index_eq (s : ℤ) (n : ℕ) : indexFromDigits s (padded (spike n))=lag s n := by
  unfold indexFromDigits lag; rw [wt,show (s+1)*(2*(((n:ℤ)+1)*(s-1)-1))=(s+1)*(((n:ℤ)+1)*(s-1)-1)*2 by ring]; exact Int.mul_ediv_cancel _ (by decide : (2:ℤ)≠0)

theorem increasing {s : ℤ} (hs : 2≤s) : StrictMono (lag s) := by
  apply strictMono_nat_of_lt_succ; intro n
  have hp : 0<(s+1)*(s-1) := mul_pos (by omega) (by omega)
  unfold lag; push_cast; linarith only [hp]

theorem centers_tendsto {s : ℤ} (hs : 2≤s) : Tendsto (fun n => val s (spike n)) atTop (𝓝 0) := by
  have h1 : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  let r := (s:ℝ)⁻¹
  have hp : 0<r := inv_pos.mpr (lt_trans zero_lt_one h1)
  have hh : r<1 := inv_lt_one_of_one_lt₀ h1
  have hs' : r^2 < 1 := by nlinarith [mul_pos hp (sub_pos.mpr hh)]
  have eq (n : ℕ) : val s (spike n) = (r^2)^n * r^2 := by
    have he := scaled hs n
    have hne : (s:ℝ)^(2*n+2)≠0 := ne_of_gt (pow_pos (lt_trans zero_lt_one h1) _)
    have hx := congrArg (fun y : ℝ => ((s:ℝ)^(2*n+2))⁻¹*y) he
    simp only [←mul_assoc, inv_mul_cancel₀ hne,one_mul,mul_one] at hx
    rw [hx]; dsimp [r]; rw [←inv_pow,pow_add,pow_mul]
  simp_rw [eq]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg r) hs').mul_const (r^2)

theorem local_matching {s : ℤ} (hs : 2≤s) (n : ℕ) :
    ∃ i j : ℕ, (i:ℤ)-j=lag s n ∧ ∀ᶠ η in 𝓝 (val s (spike n)), Meets s η i j ∧
      ∀ u ≤ i, ∀ v ≤ j, Meets s η u v → (u:ℤ)-v=lag s n := by
  obtain ⟨i,j,hg,H⟩ := window_of_word hs (spike n) (good hs n) (clear hs n)
  rw [index_eq] at hg H
  refine ⟨i,j,hg,?_⟩; filter_upwards [H] with η h using ⟨h.1,h.2.2.2⟩

#print axioms increasing
#print axioms centers_tendsto
#print axioms local_matching
end BCMP430.Origin
