import GapTopology
import GapPullback
import GapFence

namespace BCMP430.Final430
open Set Original UntunedTarget GapTopology

/-- The open tuning-window complement is covered by the closure of the orbit minima
    that eventually hit the top fixed point, together with zero. -/
theorem cover {s : ℤ} (hs : 2 ≤ s) {x : ℝ} (hu : x ∈ UT s) (hp : 0 < x) (ht : x < top s) :
    x ∈ C s := by
  by_contra outside
  obtain ⟨a,b,ha,ax,xb,hb,sa,sb,near,empty⟩ := GapTopology.gap hs hp ht outside
  obtain ⟨c,hc,early⟩ := GapGrid.center hs ha (ax.trans xb) hb sa sb
  have br : c.R ≤ b := by
    apply le_of_not_gt; intro bad
    have ord := endpoint_order hs c
    obtain ⟨k,_,hk⟩ := SurvivorWindow.gap_drop hs c ⟨ord.2.1.trans hc.2,bad⟩
    exact (not_lt_of_ge (sb k)) hk
  have branch (right : Bool) {v : ℝ} (hv : v ∈ P s) {y : ℝ} (hy : y ∈ Ioo a b)
      (eq : y = GapPullback.y c right v) (lt : y < v) : y ∈ P s := by
    have yp := ha.trans_lt hy.1
    have H := GapPullback.pull hs c right (yp.trans lt) hv.1.2 hv.2.1 hv.2.2
      (eq ▸ lt.le) (fun j jp jl => eq ▸ early y hy j jp jl)
    exact ⟨⟨yp.le,hy.2.le.trans hb⟩,eq.symm ▸ H⟩
  obtain ⟨R,T⟩ := GapFence.fence hs c hc br near empty
    (fun _ hv _ hy eq lt => branch true hv hy eq lt)
    (fun _ hv _ hy eq lt => branch false hv hy eq lt)
  exact hu.2 c ⟨T.trans_lt ax,xb.trans_eq R⟩

/-- BCMP, author version, Conjecture 4.30. No density, recurrence, coding, or
    extra endpoint assumption is an argument of this theorem. -/
theorem bcmp_conjecture_4_30 (s : ℤ) (hs : 2 ≤ s) : FullTarget s := by
  intro x hu ne
  rcases eq_or_lt_of_le hu.1.1 with e|hp
  · subst x; exact origin_components hs
  · have ht := lt_of_le_of_ne hu.1.2 ne
    exact GapTopology.mem_accum hs (cover hs hu hp ht) hp ht

#print axioms cover
#print axioms bcmp_conjecture_4_30
end BCMP430.Final430
