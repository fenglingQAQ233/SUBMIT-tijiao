import DigitTape
import ParameterStability

namespace BCMP430.RealClock
open Clock Original ClockTotal Germ Witness Tape

private theorem marked_translate (s γ r : ℝ) (v : ℤ) (c : ℕ) :
    let H := max (gate γ r) v
    let N := (H-v).toNat
    (MatchLag.advance s γ)^[N] (c,r+(v:ℝ)) = (c,r+(H:ℝ)) := by
  let H := max (gate γ r) v
  let N := (H-v).toNat
  have T := translations_to_gate s γ r v
  have aux (j : ℕ) (hj : j ≤ N) :
      (MatchLag.advance s γ)^[j] (c,r+(v:ℝ)) = (c,(Q s γ)^[j] (r+(v:ℝ))) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have h : j<N := by omega
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih (by omega)]
      exact Prod.ext (ite_eq_left (T.2.2 j h)) rfl
  exact (aux N le_rfl).trans (congrArg (fun x : ℝ => (c,x)) T.1)

private theorem after_B {s : ℤ} {r γ : ℝ} (h : ℤ) (c : ℕ) :
    let u := g s r
    let m := gate γ u
    let b := level s r
    let H := height s m b h
    let N := (H-(b-s*h)).toNat
    (MatchLag.advance s γ)^[N] (c,1+(s:ℝ)*(1-(r+(h:ℝ)))) = (c,u+(H:ℝ)) := by
  have hf : Int.fract (1+(s:ℝ)*(1-r)) = g s r := by
    apply Int.fract_eq_fract.mpr; exact ⟨1+s,by push_cast; ring⟩
  have pt : 1+(s:ℝ)*(1-(r+(h:ℝ))) = g s r + ((level s r-s*h:ℤ):ℝ) := by
    rw [←hf,Int.fract,level]; push_cast; ring
  rw [pt]; exact marked_translate ..

private theorem marked_step {s h : ℤ} {γ r : ℝ} (c : ℕ) (above : γ<r+(h:ℝ)) :
    let u := g s r
    let m := gate γ u
    let b := level s r
    (MatchLag.advance s γ)^[steps s m b h] (c,r+(h:ℝ)) = (c+1,u+(height s m b h:ℝ)) := by
  dsimp only
  unfold steps; rw [Function.iterate_succ_apply]
  change (MatchLag.advance s γ)^[_] (if r+(h:ℝ)≤γ then c else c+1,Q s γ (r+(h:ℝ))) = _
  rw [ite_eq_right (not_le_of_gt above),Q,ite_eq_right (not_le_of_gt above)]; exact after_B ..

def exec (s : ℤ) : List (ℤ × ℤ) → State → State
  | [], p => p
  | (m,b)::ops,p => exec s ops (ClockTotal.advance s m b p)

private theorem exec_program (s : ℤ) (w : Word) (p : State) : exec s (program s w) p=finish s w p := by
  induction w generalizing p with
  | one => rfl
  | two => rfl
  | more a b t ih => exact ih _

private def Realized (s : ℤ) (γ r : ℝ) (p : State) :=
    ∃ i j c : ℕ, path s γ true i = (c,r+(p.right:ℝ)) ∧
      path s γ false j = (c,r+(p.left:ℝ)) ∧ (i:ℤ)-j=p.gap ∧
      γ<r+(p.right:ℝ) ∧ γ<r+(p.left:ℝ)

private theorem path_add (s γ : ℝ) (r : Bool) (i t : ℕ) :
    path s γ r (t+i)=(MatchLag.advance s γ)^[t] (path s γ r i) := Function.iterate_add_apply ..

private theorem run {s : ℤ} {γ z : ℝ} (ops : List (ℤ×ℤ)) {r : ℝ} {p : State}
    (follows : Follows s γ ops r z) (atR : Realized s γ r p) : Realized s γ z (exec s ops p) := by
  induction ops generalizing p r with
  | nil => exact follows ▸ atR
  | cons op rest ih =>
    obtain ⟨m,b⟩ := op
    obtain ⟨hm,hb,htail⟩ := follows
    subst m; subst b
    apply ih htail
    obtain ⟨i,j,c,pr,pl,eq,ar,al⟩ := atR
    refine ⟨steps s (gate γ (g s r)) (level s r) p.right+i,
      steps s (gate γ (g s r)) (level s r) p.left+j,c+1,?_,?_,?_,?_,?_⟩
    · rw [path_add,pr]; exact marked_step c ar
    · rw [path_add,pl]; exact marked_step c al
    · dsimp only [ClockTotal.advance]; push_cast; linarith only [eq]
    · exact (above_iff ..).mpr (le_max_left ..)
    · exact (above_iff ..).mpr (le_max_left ..)

/-- The initial plus branch is forced by the right-hand limit, not by Q(γ).
    The minus branch has already used one translation when it first enters B. -/
private theorem launch {s : ℤ} (γ : ℝ) :
    let m := gate γ (g s γ)
    let b := level s γ
    Realized s γ (g s γ) (ClockTotal.advance s m b ⟨0,1,-1⟩) := by
  let u := g s γ
  let m := gate γ u
  let b := level s γ
  let N := (height s m b 0-(b-s*0)).toNat
  refine ⟨N,steps s m b 1,1,?_,?_,?_,?_,?_⟩
  · have he := after_B (s:=s) (γ:=γ) (r:=γ) 0 1
    simpa only [path,seed,ClockTotal.advance,N,m,b,u,Int.cast_zero,add_zero,ite_true] using he
  · have he := marked_step (s:=s) (h:=1) (r:=γ) 0 (by push_cast; linarith : γ < γ+((1:ℤ):ℝ))
    simpa only [path,seed,ClockTotal.advance,m,b,u,Int.cast_one,Bool.false_eq_true,ite_false,Nat.zero_add] using he
  · change (N:ℤ)-(steps s m b 1:ℤ) = -1+(steps s m b 0:ℤ)-(steps s m b 1:ℤ)
    have hh : steps s m b 0=N+1 := rfl
    rw [hh]; push_cast; ring
  · exact (above_iff ..).mpr (le_max_left ..)
  · exact (above_iff ..).mpr (le_max_left ..)

/-- For any admissible terminating word, its clock produces an actual marked
    meeting of the one-sided trajectories, with the prescribed signed delay. -/
theorem marked_word {s : ℤ} (hs : 2≤s) (w : Word) (hw : Good s w)
    (clear : Clear s (val s w) (val s w)) :
    ∃ i j : ℕ, path s (val s w) true i=path s (val s w) false j ∧
      (i:ℤ)-j=indexFromDigits s (padded w) := by
  let γ := val s w
  have unit := in_unit hs w hw
  have fol := word_follows hs unit.1.le unit.2 w hw clear
  have nonempty : program s w ≠ [] := by cases w <;> simp [program]
  have real : Realized s γ 0 (exec s (program s w) ⟨0,1,-1⟩) := by
    cases eqn : program s w with
    | nil => exact False.elim (nonempty eqn)
    | cons op tail =>
      obtain ⟨m,b⟩ := op
      rw [eqn] at fol
      obtain ⟨hm,hb,ht⟩ := fol
      subst m; subst b
      exact run tail ht (launch γ)
  rw [exec_program] at real
  obtain ⟨i,j,c,hi,hj,hgap,_,_⟩ := real
  obtain ⟨r,l,E⟩ := summed_clock hs w hw
  rw [r] at hi; rw [l] at hj
  exact ⟨i,j,hi.trans hj.symm,hgap.trans E⟩

#print axioms marked_word
end BCMP430.RealClock
