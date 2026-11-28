import UnboundedLags

namespace BCMP430.MetricLocus
open Direct Dominant Amplify Unbounded Filter Witness
open scoped Topology

/-- A stable meeting with delay d, including agreement of any coordinatewise earlier witness. -/
def DelayNear (s : ℤ) (x : ℝ) (d : ℤ) := ∃ i j : ℕ, (i:ℤ)-j=d ∧
  ∀ᶠ η in 𝓝 x, Meets s η i j ∧ ∀ u ≤ i, ∀ v ≤ j, Meets s η u v → (u:ℤ)-v=d

def Rich (s : ℤ) (x : ℝ) := ∀ ε > 0, ∀ bad : Finset ℤ, ∃ y d, dist y x < ε ∧
    d ≠ 0 ∧ d ∉ bad ∧ DelayNear s y d

private theorem value_range {s : ℤ} (hs : 2≤s) {w : Word} (hw : Bounded s w) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) : eval s w x ∈ Set.Icc (0:ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have h := hw a (by simp)
    have hv := ih (fun z hz => hw z (List.mem_cons_of_mem _ hz))
    have pos : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
    have h₁ : (1:ℝ)≤a := by exact_mod_cast h.1
    have h₂ : (a:ℝ)≤s := by exact_mod_cast h.2
    exact ⟨div_nonneg (by linarith [hv.2]) pos.le,(div_le_one pos).mpr (by linarith [hv.1])⟩

private theorem cat (s : ℤ) (w v : Word) (x : ℝ) : eval s (w++v) x=eval s w (eval s v x) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.cons_append,eval,ih]

private theorem flat_cat (p q : Pairs) : flatten (p++q)=flatten p++flatten q := by
  induction p with
  | nil => rfl
  | cons x xs ih => obtain ⟨a,b⟩ := x; simp [flatten,ih]

private theorem affine (s : ℤ) (w : Word) (x y : ℝ) : eval s w x-eval s w y =
    (-(s:ℝ)⁻¹)^w.length*(x-y) := by
  induction w with
  | nil => simp [eval]
  | cons a w ih =>
    simp only [eval,branch,List.length_cons,pow_succ,div_eq_mul_inv]
    calc
      _ = -(s:ℝ)⁻¹ * (eval s w x - eval s w y) := by ring
      _ = _ := by rw [ih]; ring

/-- Fixed point in the real parameter segment of the inverse branches of an even word. -/
private theorem fixed_exists {s : ℤ} (hs : 2≤s) {w : Word} (hd : Dom w) (hw : Bounded s w) :
    ∃ x ∈ Set.Icc (0:ℝ) 1, eval s w x=x := by
  let c := eval s w 0
  let b : ℝ := (-(s:ℝ)⁻¹)^w.length
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have len := List.length_pos_iff.mpr hd.1
  have norm : |b|<1 := by
    dsimp [b]; rw [abs_pow,abs_neg,abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one sp))]
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ sp) (by omega)
  have den : 0<1-b := by linarith [abs_lt.mp norm]
  have hv := value_range hs hw (x:=0) (by simp)
  have hi := value_range hs hw (x:=1) (by simp)
  have eq := affine s w 1 0
  change eval s w 1-c=b*(1-0) at eq
  refine ⟨c/(1-b),⟨div_nonneg hv.1 den.le,(div_le_one den).mpr (by linarith [hi.2])⟩,?_⟩
  have e := affine s w (c/(1-b)) 0
  change eval s w (c/(1-b))-c=b*(c/(1-b)-0) at e
  have he := div_mul_cancel₀ c den.ne'
  linarith only [e,he]

private theorem rep_eval {s : ℤ} {P : Pairs} (K : ℕ) {x u : ℝ} (fix : eval s (flatten P) x=x) :
    eval s (flatten (repeatPairs P K)) u-x =
      ((-(s:ℝ)⁻¹)^(flatten P).length)^K*(u-x) := by
  induction K with
  | zero => simp [repeatPairs,flatten,eval]
  | succ K ih =>
    rw [repeatPairs,flat_cat,cat]
    have hh := affine s (flatten P) (eval s (flatten (repeatPairs P K)) u) x
    rw [fix,ih] at hh
    rw [hh,pow_succ]; ring

/-- For every radius and every finite list of delays to exclude, there is a stable matching
    center inside the radius with a nonzero delay outside the list. The target is the
    real periodic point, not the terminating center used for the witness. -/
theorem rich_fixed {s a b : ℤ} {q : Pairs} (hs : 2≤s) (hq : q≠[])
    (hd : Dom (flatten ((a,b)::q))) (hb : Bounded s (flatten ((a,b)::q)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hfix : eval s (flatten ((a,b)::q)) x=x) : Rich s x := by
  let w := (a,b)::q
  let R := |(-(s:ℝ)⁻¹)^(flatten w).length|
  have sp : (1:ℝ)<s := by exact_mod_cast (show 1<s by omega)
  have r1 : R<1 := by
    dsimp [R]; rw [abs_pow,abs_neg,abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one sp))]
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ sp) (by simpa using hd.1)
  intro ε hε bad
  obtain ⟨K,hK⟩ := exists_pow_lt_of_lt_one hε r1
  obtain ⟨seq,hinj,hw⟩ := infinitely_many_lags hs hq hd hb K
  let L := fun n => (s+1)*ctIndex (seq n)
  have outside : ∃ n, L n ∉ insert 0 bad := by
    by_contra! h
    exact (Set.infinite_range_of_injective hinj) ((insert 0 bad).finite_toSet.subset (by rintro z ⟨n,rfl⟩; exact h n))
  obtain ⟨n,hn⟩ := outside
  obtain ⟨⟨tail,he⟩,bv,_,matchData⟩ := hw n
  have boundedTail : Bounded s (flatten tail) := by rw [he,flat_cat] at bv; exact fun z hz => bv z (List.mem_append_right _ hz)
  let v := eval s (flatten tail) 0
  have hv := value_range hs boundedTail (x:=0) (by simp)
  have hdist : |v-x|≤1 := abs_sub_le_iff.mpr ⟨by linarith [hv.2,hx.1],by linarith [hv.1,hx.2]⟩
  refine ⟨eval s (flatten (seq n)) 0,L n,?_,?_,?_,matchData⟩
  · rw [Real.dist_eq,he,flat_cat,cat,rep_eval K hfix,abs_mul,abs_pow]
    change R^K*|v-x| < ε
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hdist (pow_nonneg (abs_nonneg _) K)).trans_eq (mul_one (R^K))) hK
  · exact fun h => hn (Finset.mem_insert.mpr (Or.inl h))
  · exact fun h => hn (Finset.mem_insert.mpr (Or.inr h))

/-- Real parameter set handled by this construction (two or more digit pairs). -/
def roots (s : ℤ) : Set ℝ := {x | ∃ (a b : ℤ) (q : Pairs), q≠[] ∧ Dom (flatten ((a,b)::q)) ∧
  Bounded s (flatten ((a,b)::q)) ∧ x∈Set.Icc (0:ℝ) 1 ∧ eval s (flatten ((a,b)::q)) x=x}

theorem rich_closure {s : ℤ} (hs : 2≤s) {x : ℝ} (hx : x ∈ closure (roots s)) : Rich s x := by
  intro ε hε bad
  obtain ⟨z,hz,dist₁⟩ := Metric.mem_closure_iff.mp hx (ε/2) (half_pos hε)
  obtain ⟨a,b,q,hq,hd,hb,rangeZ,fixZ⟩ := hz
  obtain ⟨y,d,dist₂,hn,hb',md⟩ := rich_fixed hs hq hd hb rangeZ fixZ (ε/2) (half_pos hε) bad
  rw [dist_comm x z] at dist₁
  exact ⟨y,d,lt_of_le_of_lt (dist_triangle y z x) (by linarith),hn,hb',md⟩

theorem word_fixed_point {s : ℤ} (hs : 2 ≤ s) {w : Word} (hd : Dom w) (hw : Bounded s w) :
    ∃ x ∈ Set.Icc (0:ℝ) 1, eval s w x=x := fixed_exists hs hd hw

theorem word_difference (s : ℤ) (w : Word) (x y : ℝ) : eval s w x-eval s w y =
    (-(s:ℝ)⁻¹)^w.length*(x-y) := affine s w x y

#print axioms fixed_exists
#print axioms rich_fixed
#print axioms rich_closure
end BCMP430.MetricLocus
