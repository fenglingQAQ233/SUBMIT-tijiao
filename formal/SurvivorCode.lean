import OriginalReturn

namespace BCMP430.Survivor
open Original Streams RealPrefix Filter
open scoped Topology BigOperators

noncomputable def pos (s : ℤ) (x : ℝ) (i : ℕ) := (g s)^[i] x
noncomputable def digit (s : ℤ) (y : ℝ) : ℤ := s+1+⌊-(s:ℝ)*y⌋
noncomputable def code (s : ℤ) (x : ℝ) : Digits := fun i => digit s (pos s x i)

private theorem recu (s : ℤ) (x : ℝ) (i : ℕ) :
    (s:ℝ)*pos s x i + pos s x (i+1) = (s:ℝ)+1-code s x i := by
  simp only [pos,Function.iterate_succ_apply',code,digit,g,Int.fract,Int.cast_add,Int.cast_one]
  ring

private theorem pos_add (s : ℤ) (x : ℝ) (k j : ℕ) :
    pos s (pos s x k) j = pos s x (j+k) := (Function.iterate_add_apply ..).symm

private theorem run_eq (A : Digits) (k j : ℕ) : run shift A k j = A (j+k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => change run shift A k (j+1) = _; rw [ih]; congr 1; omega

private theorem code_shift (s : ℤ) (x : ℝ) (k : ℕ) :
    run shift (code s x) k = code s (pos s x k) := by
  funext i; rw [run_eq]; simp only [code,pos_add]

private theorem antitone_digit {s : ℤ} (hs : 2≤s) {x y : ℝ} (h : x ≤ y) :
    digit s y ≤ digit s x := by
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast (show 0≤s by omega)
  have := Int.floor_mono (show -(s:ℝ)*y ≤ -(s:ℝ)*x from mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hs'))
  unfold digit; omega

theorem no_reverse {s : ℤ} (hs : 2≤s) {x y : ℝ} (hxy : x ≤ y) : ¬AltLt (code s y) (code s x) := by
  rintro ⟨k,pre,hlt⟩
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast (show 0≤s by omega)
  have cmp (i : ℕ) (hi : i ≤ k) : if i%2=0 then pos s x i ≤ pos s y i else pos s y i ≤ pos s x i := by
    induction i with
    | zero => exact hxy
    | succ i ih =>
      have hprev := ih (by omega)
      have eq := pre i (by omega)
      have rx := recu s x i
      have ry := recu s y i
      rw [eq] at ry
      by_cases hp : i%2=0
      · have hn : (i+1)%2 ≠ 0 := by omega
        simp only [hp,ite_true] at hprev
        simp only [hn,ite_false]; linarith [mul_le_mul_of_nonneg_left hprev hs']
      · have hn : (i+1)%2=0 := by omega
        simp only [hp,ite_false] at hprev
        simp only [hn,ite_true]; linarith [mul_le_mul_of_nonneg_left hprev hs']
  have h := cmp k (by omega)
  by_cases hp : k%2=0
  · simp only [hp,ite_true] at h hlt
    exact (not_lt_of_ge (antitone_digit hs h)) hlt
  · simp only [hp,ite_false] at h hlt
    exact (not_lt_of_ge (antitone_digit hs h)) hlt

private theorem bounded_pos {s : ℤ} {x : ℝ} (hx : 0<x) (hx' : x<1)
    (surv : ∀ k, x ≤ pos s x k) (i : ℕ) : 0 < pos s x i ∧ pos s x i < 1 := by
  refine ⟨lt_of_lt_of_le hx (surv _),?_⟩
  cases i with
  | zero => exact hx'
  | succ i =>
    rw [pos,Function.iterate_succ_apply']
    exact Int.fract_lt_one (-(s:ℝ)*(g s)^[i] x)

private theorem valid_code {s : ℤ} (hs : 2≤s) {x : ℝ} (hx : 0<x) (hx' : x<1)
    (surv : ∀ k, x ≤ pos s x k) (i : ℕ) : 1 ≤ code s x i ∧ code s x i ≤ s := by
  obtain ⟨hl,hr⟩ := bounded_pos hx hx' surv i
  have hs' : (0:ℝ) < s := by exact_mod_cast (show 0<s by omega)
  have lo : -s ≤ ⌊-(s:ℝ)*pos s x i⌋ := by apply Int.le_floor.mpr; push_cast; nlinarith [mul_lt_mul_of_pos_left hr hs']
  have up : ⌊-(s:ℝ)*pos s x i⌋ < 0 := by apply Int.floor_lt.mpr; push_cast; nlinarith [mul_pos hs' hl]
  unfold code digit; omega

noncomputable def rem (s : ℤ) (x : ℝ) (i : ℕ) :=
  if i%2=0 then pos s x i else 1-pos s x i

private theorem decode_recu (s : ℤ) (x : ℝ) (i : ℕ) :
    (s:ℝ)*rem s x i = (Streams.decode s (code s x) i : ℝ) + rem s x (i+1) := by
  have h := recu s x i
  by_cases hp : i%2=0
  · have hn : (i+1)%2≠0 := by omega
    simp only [rem,Streams.decode,hp,hn,ite_true,ite_false,Int.cast_sub]; linarith
  · have hn : (i+1)%2=0 := by omega
    simp only [rem,Streams.decode,hp,hn,ite_true,ite_false,Int.cast_sub,Int.cast_one]; linarith [mul_sub (s:ℝ) 1 (pos s x i),mul_one (s:ℝ)]

/-- The real orbit itself constructs the bounded code, including for nonperiodic x.
    No approximation, initial choice of expansion, or density theorem is assumed. -/
theorem positive_survivor {s : ℤ} (hs : 2≤s) {x : ℝ} (hx : 0<x) (hx' : x<1)
    (surv : ∀ k, x ≤ pos s x k) :
    (∀ i, 1 ≤ code s x i ∧ code s x i ≤ s) ∧
    (∀ k, ¬AltLt (run shift (code s x) k) (code s x)) ∧
    value s (Streams.decode s (code s x)) = x := by
  have valid := valid_code hs hx hx' surv
  refine ⟨valid, fun k => by rw [code_shift]; exact no_reverse hs (surv k), ?_⟩
  let d := Streams.decode s (code s x)
  let r : ℝ := (s:ℝ)⁻¹
  have hsr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have hsp : (0:ℝ)<s := by linarith
  have hr : 0≤r := inv_nonneg.mpr hsp.le
  have hr' : r<1 := inv_lt_one_of_one_lt₀ hsr
  have hbound (i : ℕ) : 0≤rem s x i ∧ rem s x i ≤ 1 := by
    have h := bounded_pos hx hx' surv i
    unfold rem; split <;> constructor <;> linarith [h.1,h.2]
  have hp (n : ℕ) : (∑ i ∈ Finset.range n, term s d i) + r^n*rem s x n = x := by
    induction n with
    | zero => simp [rem,pos]
    | succ n ih =>
      have H : (s:ℝ)*rem s x n = (d n:ℝ)+rem s x (n+1) := decode_recu s x n
      have I : r*(s:ℝ)=1 := inv_mul_cancel₀ hsp.ne'
      have H' : r*(d n:ℝ)+r*rem s x (n+1) = rem s x n := by
        rw [←mul_add,←H,←mul_assoc,I,one_mul]
      have H'' := congrArg (fun u : ℝ => r^n*u) H'
      change r^n*(r*(d n:ℝ)+r*rem s x (n+1)) = r^n*rem s x n at H''
      rw [Finset.sum_range_succ]
      change (_ + (d n:ℝ)*r*r^n) + r^(n+1)*rem s x (n+1) = x
      rw [pow_succ]
      linarith only [H'', ih]
  have hlim : Tendsto (fun n => r^n*rem s x n) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (pow_nonneg hr _) (hbound n).1)
      (fun n => by simpa using mul_le_mul_of_nonneg_left (hbound n).2 (pow_nonneg hr n))
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr')
  have hd := (valid_digits_iff s _).mpr valid
  have hnon (i : ℕ) : 0≤term s d i := by
    have hz : (0:ℝ) ≤ d i := by exact_mod_cast (hd i).1
    unfold term; positivity
  apply HasSum.tsum_eq
  apply (hasSum_iff_tendsto_nat_of_nonneg hnon _).mpr
  have eq (n : ℕ) : (∑ i ∈ Finset.range n, term s d i) = x-r^n*rem s x n := by linarith only [hp n]
  simp_rw [eq]
  simpa using (tendsto_const_nhds (x := x)).sub hlim

#print axioms positive_survivor
end BCMP430.Survivor
