import UntunedTarget
import SurvivorCode

namespace BCMP430.FirstDrop
open Original Adic UntunedTarget Set Survivor

/-- A congruence retaining the integer part also at discontinuities. -/
theorem iterate_lift (s : ℤ) (x : ℝ) (k : ℕ) :
    ∃ a : ℤ, (-(s:ℝ))^k*x = (a:ℝ)+(g s)^[k] x := by
  induction k with
  | zero => exact ⟨0,by simp⟩
  | succ k ih =>
    obtain ⟨a,ha⟩ := ih
    refine ⟨-s*a+⌊-(s:ℝ)*(g s)^[k] x⌋,?_⟩
    rw [pow_succ',mul_assoc,ha,Function.iterate_succ_apply']; unfold g Int.fract; push_cast; ring

private theorem unit_pos_iter (s : ℤ) (x : ℝ) {k : ℕ} (hk : 0<k) :
    (g s)^[k] x ∈ Ico (0:ℝ) 1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

private theorem iterate_eq_frac (s : ℤ) (x : ℝ) {k : ℕ} (hk : 0<k) :
    (g s)^[k] x=Int.fract ((-(s:ℝ))^k*x) := by
  obtain ⟨c,hc⟩ := iterate_lift s x k
  have u := unit_pos_iter s x hk
  symm; exact Int.fract_eq_iff.mpr ⟨u.1,u.2,c,by linarith⟩

private theorem scaled_integer (r : ℝ) (a : ℤ) (ha : a≠0) (h : ∃ b : ℤ, (a:ℝ)*r=b) (hr : 0<r) :
    1 ≤ |(a:ℝ)| * r := by
  obtain ⟨b,hb⟩ := h
  have bn : b≠0 := by intro e; rw [e,Int.cast_zero] at hb; exact (mul_ne_zero (by exact_mod_cast ha) hr.ne') hb
  have hab : (1:ℤ)≤|b| := by rcases lt_or_gt_of_ne bn with l|l <;> simp [abs_of_neg,abs_of_pos,l] <;> omega
  have eq := congrArg abs hb
  rw [abs_mul,abs_of_pos hr] at eq
  rw [eq]; exact_mod_cast hab

/-- Interior points of a rational grid cannot wrap when moved by less than one mesh. -/
private theorem transport {C : ℤ} {v y : ℝ} (hc : C≠0) (hv : v∈Ioo (0:ℝ) 1)
    (hy : y∈Ico (0:ℝ) 1) (grid : ∃ b : ℤ, (C:ℝ)*v=b) :
    v+y/(C:ℝ) ∈ Ioo (0:ℝ) 1 := by
  have lo := scaled_integer v C hc grid hv.1
  obtain ⟨b,hb⟩ := grid
  have hi := scaled_integer (1-v) C hc ⟨C-b,by push_cast; linarith only [hb]⟩ (by linarith [hv.2])
  have pos : 0 < |(C:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
  have step : |y/(C:ℝ)| < 1/|(C:ℝ)| := by rw [abs_div,abs_of_nonneg hy.1]; exact (div_lt_div_iff_of_pos_right pos).mpr hy.2
  have l : 1/|(C:ℝ)| ≤ v := (div_le_iff₀ pos).mpr (by linarith only [lo])
  have u : 1/|(C:ℝ)| ≤ 1-v := (div_le_iff₀ pos).mpr (by linarith only [hi])
  obtain ⟨l',u'⟩ := abs_lt.mp step; constructor <;> linarith

/-- If k is the first drop, the k-grid point obtained by deleting the final
    remainder has no strictly positive iterate below itself. The other early
    time in the proof is k-i, not a comparison of rounded floating point values. -/
theorem rounded_avoids {s : ℤ} (hs : 2≤s) {x : ℝ} {k : ℕ} (hk : 0<k)
    (first : ∀ i : ℕ, 0 < i → i < k → x ≤ (g s)^[i] x) (drop : (g s)^[k] x<x)
    {z : ℝ} {a : ℤ} (grid : (-(s:ℝ))^k*z=a)
    (diff : (-(s:ℝ))^k*(x-z)=(g s)^[k] x) (zu : z<1) :
    ∀ i : ℕ, (g s)^[i+1] z ∉ Ioo 0 z := by
  intro j bad
  let i := j+1
  let v := (g s)^[i] z
  change 0<v ∧ v<z at bad
  let y := (g s)^[k] x
  have yr : y∈Ico (0:ℝ) 1 := unit_pos_iter s x hk
  have z0 : (g s)^[k] z=0 := by rw [iterate_eq_frac s z hk,grid,Int.fract_intCast]
  by_cases large : k ≤ i
  · have eqv : v=0 := by
      change (g s)^[i] z=0
      rw [show i=(i-k)+k by omega,Function.iterate_add_apply,z0]
      exact Function.iterate_fixed (by simp [g] : g s 0=0) _
    exact bad.1.ne' eqv
  have hi : 0 < i := Nat.zero_lt_succ _
  let A : ℤ := (-s)^k
  let B : ℤ := (-s)^i
  let C : ℤ := (-s)^(k-i)
  have An : A≠0 := pow_ne_zero _ (by omega)
  have Cn : C≠0 := pow_ne_zero _ (by omega)
  have Cr : (C:ℝ)≠0 := by exact_mod_cast Cn
  have fac : C*B=A := by dsimp [A,B,C]; rw [←pow_add,show k-i+i=k by omega]
  have fac' : (C:ℝ)*(B:ℝ)=A := by exact_mod_cast fac
  have gridA : (A:ℝ)*z=a := by simpa [A] using grid
  have diffA : (A:ℝ)*(x-z)=y := by simpa [A,y] using diff
  obtain ⟨b,hb⟩ := iterate_lift s z i
  change (-(s:ℝ))^i*z=(b:ℝ)+v at hb
  have bz : (B:ℝ)*z=(b:ℝ)+v := by simpa [B] using hb
  have cv : (C:ℝ)*v=(a-C*b:ℤ) := by
    have eq := congrArg (fun t : ℝ => (C:ℝ)*t) bz
    change (C:ℝ)*((B:ℝ)*z)=(C:ℝ)*((b:ℝ)+v) at eq
    rw [←mul_assoc,fac',gridA,mul_add] at eq; push_cast; linarith only [eq]
  have gridGap : ∃ l : ℤ, (A:ℝ)*(z-v)=l := by
    refine ⟨a-B*(a-C*b),?_⟩
    rw [mul_sub,gridA,←fac',mul_comm (C:ℝ) (B:ℝ),mul_assoc,cv]; push_cast; ring
  have sep := scaled_integer (z-v) A An gridGap (sub_pos.mpr bad.2)
  have absdiff : |(A:ℝ)| * |x-z|=y := by simpa only [abs_mul,abs_of_nonneg yr.1] using congrArg abs diffA
  have ag : 0 < |(A:ℝ)| := abs_pos.mpr (by exact_mod_cast An)
  have delta : |x-z|<z-v := (mul_lt_mul_iff_of_pos_left ag).mp (by linarith only [absdiff,yr.2,sep])
  have vx : v<x := by linarith [(abs_lt.mp delta).1]
  have bu : v+y/(C:ℝ) ∈ Ioo (0:ℝ) 1 := transport Cn ⟨bad.1,bad.2.trans zu⟩ yr ⟨_,cv⟩
  have dx : (B:ℝ)*(x-z)=y/(C:ℝ) := by apply (eq_div_iff Cr).mpr; calc
      _ = ((C:ℝ)*(B:ℝ))*(x-z) := by ring
      _ = _ := by rw [fac',diffA]
  have val_i : (g s)^[i] x = v+y/(C:ℝ) := by
    rw [iterate_eq_frac s x hi]; apply Int.fract_eq_iff.mpr; refine ⟨bu.1.le,bu.2,b,?_⟩
    have castB : (-(s:ℝ))^i=(B:ℝ) := by simp [B]
    rw [castB]; linarith only [dx,bz]
  have ge := first i hi (by omega)
  rw [val_i] at ge
  have Cp : (0:ℝ)<C := by
    by_contra! neg
    have h := div_nonpos_of_nonneg_of_nonpos yr.1 neg
    linarith
  have cy : (C:ℝ)*(x-v) ≤ y := by
    have q : x-v ≤ y/(C:ℝ) := by linarith
    have zq := (le_div_iff₀ Cp).mp q; linarith only [zq]
  have val_other : (g s)^[k-i] x = (C:ℝ)*(x-v) := by
    rw [iterate_eq_frac s x (by omega)]; apply Int.fract_eq_iff.mpr
    refine ⟨(mul_pos Cp (sub_pos.mpr vx)).le,cy.trans_lt yr.2,a-C*b,?_⟩
    have castC : (-(s:ℝ))^(k-i)=(C:ℝ) := by simp [C]
    rw [castC]; linarith only [cv]
  have ge' := first (k-i) (by omega) (by omega)
  rw [val_other] at ge'; exact (not_le_of_gt drop) (ge'.trans cy)

#print axioms rounded_avoids
end BCMP430.FirstDrop
