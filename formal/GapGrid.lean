import OrbitSplice

namespace BCMP430.GapGrid
open Original FirstDrop Adic UntunedTarget Set

private theorem frac_it (s : ℤ) (y : ℝ) {k : ℕ} (pos : 0<k) : (g s)^[k] y=Int.fract ((-(s:ℝ))^k*y) := by
  obtain ⟨a,ha⟩ := iterate_lift s y k
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  have U : (g s)^[i+1] y ∈ Ico (0:ℝ) 1 := by rw [Function.iterate_succ_apply']; exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  exact (Int.fract_eq_iff.mpr ⟨U.1,U.2,a,by linarith only [ha]⟩).symm

/-- A floor cannot increase between u and v without crossing the next integer. -/
private theorem same_floor {u v : ℝ} (le : u≤v) (no : ∀ z : ℤ, u < z → ¬(z:ℝ)≤v) : ⌊v⌋=⌊u⌋ := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(Int.floor_le _).trans le,lt_of_not_ge (by simpa only [Int.cast_add,Int.cast_one] using no (⌊u⌋+1) (by push_cast; exact Int.lt_floor_add_one _))⟩

private theorem before {s : ℤ} (hs : 2≤s) {a b : ℝ} (sa : ∀ i : ℕ, a≤(g s)^[i] a)
    (sb : ∀ i : ℕ, b≤(g s)^[i] b) (k : ℕ) (kp : 0<k)
    (none : ∀ z ∈ Ioo a b, ¬GridAt s k z) {y : ℝ} (Y : y∈Ioo a b) : y < (g s)^[k] y := by
  let S := (s:ℝ)^k
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have S1 : 1<S := one_lt_pow₀ sr kp.ne'
  have sp : 0<S := zero_lt_one.trans S1
  rcases Nat.even_or_odd k with E|E
  · have F : ⌊S*y⌋=⌊S*a⌋ := by
      apply same_floor (mul_le_mul_of_nonneg_left Y.1.le sp.le); intro z hz hz'
      have Z : (z:ℝ)/S∈Ioo a b := ⟨(lt_div_iff₀ sp).mpr (by linarith only [hz]),((div_le_iff₀ sp).mpr (by linarith only [hz'])).trans_lt Y.2⟩
      exact none _ Z ⟨z,by change S*((z:ℝ)/S)=z; field_simp⟩
    have L := sa k
    rw [frac_it _ _ kp,E.neg_pow] at L ⊢
    change a≤S*a-(⌊S*a⌋:ℝ) at L
    change y<S*y-(⌊S*y⌋:ℝ); rw [F]; nlinarith only [L,mul_pos (sub_pos.mpr S1) (sub_pos.mpr Y.1)]
  · have F : ⌊-S*y⌋=⌊-S*b⌋ := by
      apply same_floor (mul_le_mul_of_nonpos_left Y.2.le (neg_nonpos.mpr sp.le)); intro z hz hz'
      have Z : (-(z:ℝ))/S∈Ioo a b := ⟨Y.1.trans_le ((le_div_iff₀ sp).mpr (by linarith only [hz'])),(div_lt_iff₀ sp).mpr (by linarith only [hz])⟩
      exact none _ Z ⟨-z,by change S*((-(z:ℝ))/S)=((-z:ℤ):ℝ); push_cast; field_simp⟩
    have L := sb k
    rw [frac_it _ _ kp,E.neg_pow] at L ⊢
    change b≤ -S*b-(⌊-S*b⌋:ℝ) at L
    change y< -S*y-(⌊-S*y⌋:ℝ); rw [F]; nlinarith only [L,Y.2,mul_pos sp (sub_pos.mpr Y.2)]

/-- At the least mesh level meeting the gap, *any* mesh point in the gap works.
    Earlier odd iterates compare with b; earlier even iterates compare with a. -/
theorem center {s : ℤ} (hs : 2≤s) {a b : ℝ} (ha : 0≤a) (ab : a<b) (hb : b≤(s:ℝ)/(s+1))
    (sa : ∀ i : ℕ, a≤(g s)^[i] a) (sb : ∀ i : ℕ, b≤(g s)^[i] b) :
    ∃ c : Center s, c.x∈Ioo a b ∧ ∀ y∈Ioo a b, ∀ j : ℕ, 0<j → j<c.depth → y≤(g s)^[j] y := by
  classical
  have sr : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have sp := zero_lt_one.trans sr
  have b1 : b<1 := hb.trans_lt ((div_lt_one (by linarith : 0<(s:ℝ)+1)).mpr (by linarith))
  let M := fun n : ℕ => ∃ z ∈ Ioo a b, GridAt s n z
  have H : ∃ n, M n := by
    obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ab) (inv_lt_one_of_one_lt₀ sr)
    let S := (s:ℝ)^n
    have s0 : 0<S := pow_pos sp _
    let v : ℤ := ⌊S*a⌋+1
    have h₁ : S*a < (v:ℝ) := by dsimp [v]; push_cast; exact Int.lt_floor_add_one _
    have h₂ : (v:ℝ)≤S*a+1 := by dsimp [v]; push_cast; linarith only [Int.floor_le (S*a)]
    have mesh : 1/S<b-a := by simpa [S,one_div,inv_pow] using hn
    have gap := (div_lt_iff₀ s0).mp mesh
    exact ⟨n,(v:ℝ)/S,⟨(lt_div_iff₀ s0).mpr (by linarith only [h₁]),(div_lt_iff₀ s0).mpr (by nlinarith only [h₂,gap])⟩,v,by change S*((v:ℝ)/S)=v; field_simp⟩
  let n := Nat.find H
  obtain ⟨z,Z,cg⟩ := Nat.find_spec H
  change GridAt s n z at cg
  have zp := ha.trans_lt Z.1
  have zu := Z.2.trans b1
  have nn : 0<n := by
    by_contra! le; have e : n=0 := by omega
    obtain ⟨t,ht⟩ := e ▸ cg
    simp only [pow_zero,one_mul] at ht
    have l : (0:ℤ)<t := by exact_mod_cast (ht ▸ zp : 0<(t:ℝ))
    have u : t<(1:ℤ) := by exact_mod_cast (ht ▸ zu : (t:ℝ)<1)
    omega
  have pre (j : ℕ) (h : j<n) (y : ℝ) (Y : y∈Ioo a b) : ¬GridAt s j y := fun gy => Nat.find_min H h ⟨y,Y,gy⟩
  have early (y : ℝ) (Y : y∈Ioo a b) (j : ℕ) (jp : 0<j) (lt : j<n) := before hs sa sb j jp (pre j lt) Y
  have avoid (j : ℕ) : (g s)^[j+1] z∉Ioo 0 z := by
    by_cases small : j+1<n
    · exact fun bad => (not_lt_of_ge (early z Z _ (Nat.zero_lt_succ _) small).le) bad.2
    · have le : n≤j+1 := le_of_not_gt small
      obtain ⟨t,ht⟩ := cg
      have stop : (g s)^[n] z=0 := by
        rw [frac_it _ _ nn]; rcases Nat.even_or_odd n with E|E
        · rw [E.neg_pow,ht,Int.fract_intCast]
        · rw [E.neg_pow,neg_mul,ht,←Int.cast_neg,Int.fract_intCast]
      have ez : (g s)^[j+1] z=0 := by rw [show j+1=(j+1-n)+n by omega,Function.iterate_add_apply,stop]; exact Function.iterate_fixed (by simp [g]) _
      exact fun bad => bad.1.ne' ez
  have id : n-1+1=n := by omega
  let c : Center s := ⟨z,n-1,⟨zp,Z.2.trans_le hb⟩,id ▸ cg,pre _ (by omega : n-1<n) _ Z,avoid⟩
  refine ⟨c,Z,fun y Y j jp jl => (early y Y j jp ?_).le⟩
  change j<n-1+1 at jl; omega

#print axioms center
end BCMP430.GapGrid
