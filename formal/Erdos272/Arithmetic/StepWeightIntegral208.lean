module

public import Erdos272.Arithmetic.StepWeightTail208

@[expose] public section

/-! The actual semiconvex short tail has a 5/2 error per unit interval. -/
namespace JSP233.StepWeightIntegral208
open UniformSourceCore208 StepWeightShape208 StepWeightTail208 MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
set_option maxHeartbeats 0

theorem quadratic_integral (a b c2 c1 c0 : ℝ) :
    (∫ x in a..b, c2*x^2+c1*x+c0) =
      c2*(b^3-a^3)/3+c1*(b^2-a^2)/2+c0*(b-a) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y => c2/3*y^3+c1/2*y^2+c0*y)
      (c2*x^2+c1*x+c0) x := by
    intro x
    convert ((((hasDerivAt_id x).pow 3).const_mul (c2/3)).add
      (((hasDerivAt_id x).pow 2).const_mul (c1/2))).add ((hasDerivAt_id x).const_mul c0)
      using 1 <;> first | rfl | (try funext y); dsimp; ring
  have hint : IntervalIntegrable (fun x : ℝ => c2*x^2+c1*x+c0) volume a b :=
    (show Continuous (fun x : ℝ => c2*x^2+c1*x+c0) by fun_prop).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint]
  ring

def Majorant (s a x : ℝ) : ℝ :=
  (a+1-x)*w s a+(x-a)*w s (a+1)+15*(x-a)*(a+1-x)

theorem majorant_integral (s a : ℝ) :
    (∫ x in a..a+1, Majorant s a x) = (w s a+w s (a+1))/2+5/2 := by
  have he : Majorant s a = fun x => (-15)*x^2+
      (w s (a+1)-w s a+30*a+15)*x+
        ((a+1)*w s a-a*w s (a+1)-15*a*(a+1)) := by
    funext x
    unfold Majorant
    ring
  rw [he, quadratic_integral]
  ring

theorem w_intervalIntegrable {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 < a)
    (hsa : s < 6*a) (hab : a ≤ b) : IntervalIntegrable (w s) volume a b := by
  apply ((max5_continuous s).intervalIntegrable a b).congr_uIoo
  intro x hx
  have hh : a < x ∧ x < b := by simpa only [uIoo_of_le hab, mem_Ioo] using hx
  exact max5_eq_w hs (by linarith only [ha, hh.1])
    (step_le_five hs (by linarith only [ha, hh.1]) (by linarith only [hsa, hh.1]))

theorem unit_trapezoid {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hsa : s < 6*a) :
    (∫ x in a..a+1, w s x) ≤ (w s a+w s (a+1))/2+5/2 := by
  have hw := w_intervalIntegrable hs ha hsa (by linarith : a ≤ a+1)
  have hm : IntervalIntegrable (Majorant s a) volume a (a+1) :=
    (show Continuous (Majorant s a) by unfold Majorant; fun_prop).intervalIntegrable a (a+1)
  have hh := intervalIntegral.integral_mono_on (by linarith : a ≤ a+1) hw hm
    (fun x hx => semiconvex_chord hs ha hx.1 hx.2
      (step_le_five hs (by linarith only [ha, hx.1]) (by linarith only [hsa, hx.1])))
  rw [majorant_integral] at hh
  exact hh

theorem average_telescope (f : ℕ → ℝ) (n k : ℕ) :
    (∑ j ∈ Finset.range k, (f (n+j)+f (n+j+1))/2) =
      (∑ j ∈ Finset.range k, f (n+j))+(f (n+k)-f n)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Nat.add_assoc]
    ring

theorem tail_trapezoid {s : ℝ} {n k : ℕ} (hs : 0 ≤ s) (hn : 0 < n)
    (hsn : s < 6*n) :
    (∫ x in (n : ℝ)..(n+k : ℕ), w s x) ≤
      (∑ j ∈ Finset.range k, w s (n+j : ℕ))+
        (w s (n+k : ℕ)-w s n)/2+5/2*k := by
  have hi : ∀ j, j < k → IntervalIntegrable (w s) volume (n+j : ℕ) (n+j+1 : ℕ) := by
    intro j hj
    apply w_intervalIntegrable hs (by positivity)
      (by push_cast; nlinarith only [hsn, show (0 : ℝ) ≤ (j : ℝ) by positivity])
      (by push_cast; linarith)
  have hint := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((n+j : ℕ) : ℝ)) hi
  have hbound : (∑ j ∈ Finset.range k,
      ∫ x in (n+j : ℕ)..(n+j+1 : ℕ), w s x) ≤
      ∑ j ∈ Finset.range k, ((w s (n+j : ℕ)+w s (n+j+1 : ℕ))/2+5/2) := by
    apply Finset.sum_le_sum
    intro j hj
    have hh := unit_trapezoid (a := ((n+j : ℕ) : ℝ)) hs (by positivity)
      (by push_cast; nlinarith only [hsn, show (0 : ℝ) ≤ (j : ℝ) by positivity])
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have heq : (∑ j ∈ Finset.range k, (w s (n+j : ℕ)+w s (n+j+1 : ℕ))/2) =
      (∑ j ∈ Finset.range k, w s (n+j : ℕ))+(w s (n+k : ℕ)-w s n)/2 :=
    average_telescope (fun j => w s (j : ℝ)) n k
  rw [Finset.sum_add_distrib, heq] at hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  have hint' : (∑ j ∈ Finset.range k, ∫ x in (n+j : ℕ)..(n+j+1 : ℕ), w s x) =
      ∫ x in (n : ℝ)..(n+k : ℕ), w s x := by
    simpa only [Nat.add_zero, Nat.add_assoc] using hint
  rw [hint'] at hbound
  nlinarith only [hbound]

#print axioms unit_trapezoid
#print axioms tail_trapezoid
end
end JSP233.StepWeightIntegral208
