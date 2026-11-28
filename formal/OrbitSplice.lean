import ConstantTailCoverage

namespace BCMP430.OrbitSplice
open Original FirstDrop UntunedTarget Set ConstantTailCoverage

/-- The set of accumulation parameters is closed; the old-component blacklist is kept
    unchanged when passing through the intermediate point. -/
theorem accum_near {s : ℤ} {x : ℝ} (near : ∀ ε > 0, ∃ z, dist z x < ε ∧ Accum s z) : Accum s x := by
  intro ε he old
  obtain ⟨z,dx,A⟩ := near (ε/2) (half_pos he)
  obtain ⟨y,d,dy,R⟩ := A (ε/2) (half_pos he) old
  exact ⟨y,d,(dist_triangle y z x).trans_lt (by linarith only [dx,dy]),R⟩

private theorem unit {s : ℤ} {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) (i : ℕ) : (g s)^[i] x ∈ Ico (0:ℝ) 1 := by
  cases i with
  | zero => exact hx
  | succ i => rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

/-- If the actual orbit passes close to the top fixed point, moving its endpoint to
    that fixed point changes all earlier residues by no more than the endpoint error. -/
theorem top_in_orbit_closure {s : ℤ} (hs : 2≤s) {x : ℝ} (xp : 0<x) (xt : x<(s:ℝ)/(s+1))
    (surv : ∀ i : ℕ, x≤(g s)^[i] x)
    (approach : ∀ δ > 0, ∃ n : ℕ, |(g s)^[n] x-(s:ℝ)/(s+1)|<δ) : Accum s x := by
  let h := (s:ℝ)/(s+1)
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp := zero_lt_one.trans sr
  have hp : 0<h := div_pos sp (by linarith)
  have h1 : h<1 := (div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith)
  have hid : h*((s:ℝ)+1)=s := div_mul_cancel₀ _ (by linarith)
  have fix : g s h=h := Int.fract_eq_iff.mpr ⟨hp.le,h1,-s,by push_cast; linarith only [hid]⟩
  change x<h at xt
  let R := fun i : ℕ => (g s)^[i] x
  have unitR (i : ℕ) : R i ∈ Ico (0:ℝ) 1 := unit ⟨xp.le,(xt.trans h1)⟩ i
  have guard (i : ℕ) : R i≤1-x/(s:ℝ) := by
    have nxt := surv (i+1); rw [Function.iterate_succ_apply'] at nxt; change x≤g s (R i) at nxt
    have eq : g s (R i)=Int.fract ((s:ℝ)*(1-R i)) := by apply Int.fract_eq_fract.mpr; exact ⟨-s,by push_cast; ring⟩
    rw [eq,Int.fract] at nxt
    have fl := Int.floor_nonneg.mpr (mul_nonneg sp.le (sub_nonneg.mpr (unitR i).2.le))
    have fl' : (0:ℝ)≤(⌊(s:ℝ)*(1-R i)⌋:ℝ) := by exact_mod_cast fl
    have le : x/(s:ℝ)≤1-R i := (div_le_iff₀ sp).mpr (by linarith only [fl',nxt])
    linarith only [le]
  apply accum_near
  intro ε he
  let δ := min (min ε (h-x)) (min x (x/(s:ℝ)))
  have dp : 0<δ := lt_min (lt_min he (sub_pos.mpr xt)) (lt_min xp (div_pos xp sp))
  obtain ⟨n,hn⟩ := approach δ dp
  change |R n-h|<δ at hn
  let P := fun i : ℕ => (-(s:ℝ))^i
  let D := (h-R n)/P n
  let Y := fun i : ℕ => R i + P i*D
  have pn : P n ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr sp.ne')
  have eqn : P n * D = h-R n := by dsimp [D]; field_simp
  have err (i : ℕ) (le : i≤n) : |P i*D|<δ := by
    rw [abs_mul]; have mono : |P i|≤|P n| := by dsimp [P]; simp only [abs_pow,abs_neg,abs_of_pos sp]; exact pow_le_pow_right₀ sr.le le
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right mono (abs_nonneg D))
    rw [←abs_mul,eqn,abs_sub_comm]; exact hn
  have dε : δ≤ε := (min_le_left ..).trans (min_le_left ..)
  have dh : δ≤h-x := (min_le_left ..).trans (min_le_right ..)
  have dx : δ≤x := (min_le_right ..).trans (min_le_left ..)
  have dg : δ≤x/(s:ℝ) := (min_le_right ..).trans (min_le_right ..)
  have inY (i : ℕ) (le : i≤n) : Y i∈Ioo (0:ℝ) 1 := by
    have E := abs_lt.mp (err i le); have low : x≤R i := surv i
    dsimp only [Y]; constructor <;> linarith only [E.1,E.2,guard i,low,dx,dg]
  have orb (i : ℕ) (le : i≤n) : (g s)^[i] (Y 0)=Y i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply',ih (by omega)]
      apply Int.fract_eq_iff.mpr
      refine ⟨(inY _ le).1.le,(inY _ le).2,⌊-(s:ℝ)*R i⌋,?_⟩
      have E : R (i+1)=Int.fract (-(s:ℝ)*R i) := Function.iterate_succ_apply' ..
      dsimp only [Y,P]; rw [E,Int.fract,pow_succ]; ring
  let I := Finset.range (n+1)
  have mem (i : ℕ) (l : i≤n) : i∈I := Finset.mem_range.mpr (by omega)
  obtain ⟨k,hk,least⟩ := Finset.exists_min_image I Y ⟨0,mem 0 (Nat.zero_le _)⟩
  have kn : k≤n := by have l := Finset.mem_range.mp hk; omega
  let z := Y k
  have zx : z ≤ Y 0 := least 0 (mem 0 (Nat.zero_le _))
  have z0 : 0<z := (inY k kn).1
  have dif0 := abs_lt.mp (err 0 (Nat.zero_le _))
  have difk := abs_lt.mp (err k kn)
  have Y0 : Y 0=x+P 0*D := rfl
  have lowk : x≤R k := surv k
  have lower : x-δ<z := by change x-δ<R k+P k*D; linarith only [difk.1,lowk]
  have upper : z<x+δ := by linarith only [zx,Y0,dif0.2]
  have zh : z<h := by linarith only [upper,dh]
  have endp : Y n=h := by change R n+P n*D=h; rw [eqn]; ring
  have run (i : ℕ) : (g s)^[i] z=(g s)^[i+k] (Y 0) := by rw [Function.iterate_add_apply,orb k kn]
  have fixed (i : ℕ) (le : n ≤ i) : (g s)^[i] (Y 0)=h := by
    rw [show i=(i-n)+n by omega,Function.iterate_add_apply,orb n le_rfl,endp,Function.iterate_fixed fix]
  have S (i : ℕ) : z≤(g s)^[i] z := by
    rw [run]; by_cases le : i+k≤n
    · rw [orb _ le]; exact least _ (mem _ le)
    · rw [fixed _ (by omega)]; exact zh.le
  have E : (g s)^[n-k] z=h := by rw [run,fixed _ (by omega)]
  refine ⟨z,?_,(top_preperiodic hs z0 zh S E).2⟩
  rw [Real.dist_eq,abs_lt]; constructor <;> linarith only [lower,upper,dε]

#print axioms top_in_orbit_closure
end BCMP430.OrbitSplice
