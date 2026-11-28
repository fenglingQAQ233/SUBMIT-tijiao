import OrbitSplice

namespace BCMP430.GapTopology
open Set Original UntunedTarget

noncomputable def top (s : ℤ) : ℝ := (s : ℝ) / (s + 1)

def P (s : ℤ) : Set ℝ := {x | x ∈ Icc 0 (top s) ∧
  (∀ i : ℕ, x ≤ (g s)^[i] x) ∧ ∃ N : ℕ, (g s)^[N] x = top s}

def C (s : ℤ) : Set ℝ := closure (insert 0 (P s))

theorem mem_accum {s : ℤ} (hs : 2 ≤ s) {x : ℝ} (hx : x ∈ C s)
    (hp : 0 < x) (ht : x < top s) : Accum s x := by
  apply OrbitSplice.accum_near
  intro ε he
  let δ := min ε (min x (top s - x))
  have hd : 0 < δ := lt_min he (lt_min hp (sub_pos.mpr ht))
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hd
  have dxy : dist y x < δ := (dist_comm y x).trans_lt hxy
  have bounds := abs_lt.mp (show |y - x| < δ by simpa only [Real.dist_eq] using dxy)
  have dx : δ ≤ x := (min_le_right ..).trans (min_le_left ..)
  have dt : δ ≤ top s - x := (min_le_right ..).trans (min_le_right ..)
  have yp : 0 < y := by linarith only [bounds.1, dx]
  have yt : y < top s := by linarith only [bounds.2, dt]
  rcases mem_insert_iff.mp hy with h0 | hyP
  · exact (yp.ne' h0).elim
  · obtain ⟨_, surv, N, hit⟩ := hyP
    exact ⟨y, dxy.trans_le (min_le_left ..),
      (ConstantTailCoverage.top_preperiodic hs yp yt surv hit).2⟩

private theorem top_mem_P {s : ℤ} (hs : 2 ≤ s) : top s ∈ P s := by
  have sp : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have den : 0 < (s : ℝ) + 1 := by linarith
  have pos : 0 < top s := div_pos sp den
  have small : top s < 1 := (div_lt_one den).mpr (by linarith)
  have eqn : top s * ((s : ℝ) + 1) = s := div_mul_cancel₀ _ den.ne'
  have fix : g s (top s) = top s := Int.fract_eq_iff.mpr
    ⟨pos.le, small, -s, by push_cast; linarith only [eqn]⟩
  exact ⟨⟨pos.le, le_rfl⟩, fun i => (Function.iterate_fixed fix i).ge, 0, rfl⟩

private theorem closure_P_untuned {s : ℤ} (hs : 2 ≤ s) : closure (P s) ⊆ UT s := by
  have pu : P s ⊆ UT s := by
    rintro z ⟨dom, surv, N, hit⟩
    exact TrappedReturn.eventual_top_untuned hs dom surv hit
  intro z hz
  refine ⟨closure_minimal (fun y (hy : y ∈ P s) => (pu hy).1) isClosed_Icc hz, ?_⟩
  intro c
  exact closure_minimal (t := (Ioo c.T c.R)ᶜ) (fun y hy => (pu hy).2 c)
    isOpen_Ioo.isClosed_compl hz

private theorem positive_mem_closure_P {s : ℤ} {z : ℝ} (hz : z ∈ C s) (hp : 0 < z) :
    z ∈ closure (P s) := by
  have sub : insert 0 (P s) ⊆ ({0} : Set ℝ) ∪ closure (P s) := by
    intro y hy
    rcases mem_insert_iff.mp hy with e | hyP
    · exact Or.inl (mem_singleton_iff.mpr e)
    · exact Or.inr (subset_closure hyP)
  rcases closure_minimal sub (isClosed_singleton.union isClosed_closure) hz with h0 | hP
  · exact (hp.ne' (mem_singleton_iff.mp h0)).elim
  · exact hP

theorem gap {s : ℤ} (hs : 2 ≤ s) {x : ℝ} (hp : 0 < x) (ht : x < top s)
    (hx : x ∉ C s) : ∃ a b : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ top s ∧
      (∀ i : ℕ, a ≤ (g s)^[i] a) ∧ (∀ i : ℕ, b ≤ (g s)^[i] b) ∧
      b ∈ closure (P s) ∧ (∀ y ∈ Ioo a b, y ∉ P s) := by
  have inc : closure (P s) ⊆ C s := closure_mono (subset_insert 0 (P s))
  have hc : IsClosed (C s) := isClosed_closure
  have h0 : (0 : ℝ) ∈ C s := subset_closure (mem_insert 0 (P s))
  have htop : top s ∈ P s := top_mem_P hs
  have left : IsCompact (Icc 0 x ∩ C s) := isCompact_Icc.inter_right hc
  have right : IsCompact (Icc x (top s) ∩ closure (P s)) :=
    isCompact_Icc.inter_right isClosed_closure
  obtain ⟨a, ha⟩ := left.exists_isGreatest ⟨0, ⟨le_rfl, hp.le⟩, h0⟩
  obtain ⟨b, hb⟩ := right.exists_isLeast ⟨top s, ⟨ht.le, le_rfl⟩, subset_closure htop⟩
  have ax : a < x := ha.1.1.2.lt_of_ne (fun e => hx (e ▸ ha.1.2))
  have xb : x < b := hb.1.1.1.lt_of_ne (fun e => hx (e.symm ▸ inc hb.1.2))
  refine ⟨a, b, ha.1.1.1, ax, xb, hb.1.1.2, ?_, ?_, hb.1.2, ?_⟩
  · rcases eq_or_lt_of_le ha.1.1.1 with e | ap
    · subst a
      have fix : g s 0 = 0 := by simp [g]
      exact fun i => (Function.iterate_fixed fix i).ge
    · exact DropWindow.ut_survives hs (closure_P_untuned hs (positive_mem_closure_P ha.1.2 ap))
        ap (ax.trans ht)
  · rcases lt_or_eq_of_le hb.1.1.2 with bt | e
    · exact DropWindow.ut_survives hs (closure_P_untuned hs hb.1.2) (hp.trans xb) bt
    · subst b
      exact htop.2.1
  · intro y hy hyP
    have hycl : y ∈ closure (P s) := subset_closure hyP
    rcases le_total y x with yx | xy
    · exact (not_le_of_gt hy.1) (ha.2 ⟨⟨hyP.1.1, yx⟩, inc hycl⟩)
    · exact (not_le_of_gt hy.2) (hb.2 ⟨⟨xy, hyP.1.2⟩, hycl⟩)

#print axioms mem_accum
#print axioms gap
end BCMP430.GapTopology
