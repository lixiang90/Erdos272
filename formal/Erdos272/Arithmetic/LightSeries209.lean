import Erdos272.Arithmetic.LightPhaseAnalytic209
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace JSP233.LightSeries209
open LightPhaseAnalytic209
open scoped BigOperators
open MeasureTheory Set intervalIntegral
noncomputable section
set_option maxHeartbeats 0

theorem square_step {x B : ℝ} (hx : 0<x) (hB : 0<B) :
    1/(x+B)^2≤(1/B)*(1/x-1/(x+B)) := by
  have hxB : 0<x+B := add_pos hx hB
  apply (div_le_iff₀ (sq_pos_of_pos hxB)).mpr
  field_simp [ne_of_gt hx,ne_of_gt hB,ne_of_gt hxB]
  nlinarith only [hB]

theorem square_tail {A B : ℝ} (hA : 0<A) (hB : 0<B) (n : ℕ) :
    (∑j∈Finset.range n,1/(A+(j+1:ℕ)*B)^2)≤
      (1/B)*(1/A-1/(A+(n:ℝ)*B)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : 0<A+(n:ℝ)*B := by positivity
    have hs := square_step hx hB
    have he : A+(n+1:ℕ)*B=(A+(n:ℝ)*B)+B := by push_cast; ring
    rw [he]
    calc
      _≤(1/B)*(1/A-1/(A+(n:ℝ)*B))+
          (1/B)*(1/(A+(n:ℝ)*B)-1/((A+(n:ℝ)*B)+B)) := add_le_add ih hs
      _=_ := by ring

theorem square_tail_le {A B : ℝ} (hA : 0<A) (hB : 0<B) (n : ℕ) :
    (∑j∈Finset.range n,1/(A+(j+1:ℕ)*B)^2)≤1/(B*A) := by
  have hs := square_tail hA hB n
  calc
    _≤(1/B)*(1/A-1/(A+(n:ℝ)*B)) := hs
    _≤(1/B)*(1/A) := mul_le_mul_of_nonneg_left
      (sub_le_self _ (by positivity)) (by positivity)
    _=1/(B*A) := by simp only [one_div,mul_inv_rev]; ring

theorem coeff_nonneg {V E k : ℝ} (hE : 0≤E) (hEV : E<V) (hk : 0<k) :
    0≤Coeff V E k := by
  have hC : 0<V-E := sub_pos.mpr hEV
  have hV : 0<V := hE.trans_lt hEV
  unfold Coeff
  by_cases hc : V-E≤k
  · rw [max_eq_right (by linarith : V-E-k≤0)]
    simp only [zero_pow (by decide : 2≠0),zero_div,sub_zero]
    positivity
  · rw [max_eq_left (by linarith : 0≤V-E-k)]
    apply sub_nonneg.mpr
    have hck : 0<V-E-k := by linarith
    have hb : (V-E-k)^2≤V*(V-E) := by
      have hm : 0≤k*(2*(V-E)-k) := mul_nonneg hk.le (by linarith)
      nlinarith only [mul_nonneg hE hC.le,hm]
    calc
      _≤(V*(V-E))/(2*(V-E)*k^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _=V/(2*k^2) := by field_simp [ne_of_gt hC,ne_of_gt hk]

theorem coeff_le {V E k : ℝ} (hEV : E<V) (hk : 0<k) :
    Coeff V E k≤V/(2*k^2) := by
  have hC : 0<V-E := sub_pos.mpr hEV
  unfold Coeff
  exact sub_le_self _ (by positivity)

/-- The entire finite phase sum is bounded by a fixed rational prefix plus
one telescoping square tail. No infinite-series axiom or numerical oracle. -/
theorem coeff_prefix_tail {A B V E : ℝ} (hA : 0<A) (hB : 0<B)
    (hE : 0≤E) (hEV : E<V) (L m : ℕ) (hL : 1≤L) :
    (∑r∈Finset.range m,Coeff V E (A+(r:ℝ)*B))≤
      (∑r∈Finset.range L,Coeff V E (A+(r:ℝ)*B))+
        V/(2*B*(A+(L-1:ℕ)*B)) := by
  have hV : 0≤V := hE.trans hEV.le
  have hK (r : ℕ) : 0<A+(r:ℝ)*B := by positivity
  by_cases hm : m≤L
  · have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      (fun r _ _ => coeff_nonneg hE hEV (hK r))
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · have hLm : L≤m := by omega
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hLm
    rw [Finset.sum_range_add]
    apply add_le_add le_rfl
    have hbase : 0<A+(L-1:ℕ)*B := hK (L-1)
    have he (j : ℕ) : A+(L+j:ℕ)*B=(A+(L-1:ℕ)*B)+(j+1:ℕ)*B := by
      have hnat : ((L-1:ℕ):ℝ)+1=(L:ℝ) := by exact_mod_cast (Nat.sub_add_cancel hL)
      push_cast
      rw [←hnat]
      ring
    calc
      _≤∑j∈Finset.range n,V/(2*(A+(L+j:ℕ)*B)^2) := by
        apply Finset.sum_le_sum
        intro j hj
        exact coeff_le hEV (hK (L+j))
      _=(V/2)*(∑j∈Finset.range n,1/((A+(L-1:ℕ)*B)+(j+1:ℕ)*B)^2) := by
        simp_rw [he]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hp : 0<(A+(L-1:ℕ)*B)+(j+1:ℕ)*B := by positivity
        field_simp [ne_of_gt hp]
        <;> ring
      _≤(V/2)*(1/(B*(A+(L-1:ℕ)*B))) :=
        mul_le_mul_of_nonneg_left (square_tail_le hbase hB n) (by positivity)
      _=_ := by field_simp [ne_of_gt hbase,ne_of_gt hB] <;> ring

theorem reciprocal_integral {A B : ℝ} (hA : 0<A) (hB : 0<B) (n : ℕ) :
    (∫x in (0:ℝ)..n,1/(A+B*x))=(Real.log (A+B*n)-Real.log A)/B := by
  have hp (x : ℝ) (hx : x∈uIcc (0:ℝ) n) : 0<A+B*x := by
    rw [uIcc_of_le (by positivity : (0:ℝ)≤n)] at hx
    exact add_pos_of_pos_of_nonneg hA (mul_nonneg hB.le hx.1)
  have hd : ∀x∈uIcc (0:ℝ) n,
      HasDerivAt (fun x:ℝ => Real.log (A+B*x)/B) (1/(A+B*x)) x := by
    intro x hx
    have hh := (((hasDerivAt_id x).const_mul B).const_add A).log (ne_of_gt (hp x hx))
    convert hh.div_const B using 1 <;> first | rfl | (dsimp; field_simp [ne_of_gt hB])
  have hc : ContinuousOn (fun x:ℝ => 1/(A+B*x)) (uIcc (0:ℝ) n) := by
    apply continuousOn_const.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro x hx
    exact ne_of_gt (hp x hx)
  have hi : IntervalIntegrable (fun x:ℝ => 1/(A+B*x)) volume 0 n := hc.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  simp only [mul_zero,add_zero]
  ring

/-- Only phases with A+rB≤N occur. Their reciprocal sum has the exact
local logarithm used by the frozen analytic light recipe. -/
theorem reciprocal_prefix {A B N : ℝ} (hA : 0<A) (hB : 0<B) (hAN : A≤N)
    (n : ℕ) (hlast : ∀r<n,A+(r:ℝ)*B≤N) :
    (∑r∈Finset.range n,1/(A+(r:ℝ)*B))≤1/A+Real.log (N/A)/B := by
  have hlog : 0≤Real.log (N/A) := Real.log_nonneg ((one_le_div hA).mpr hAN)
  cases n with
  | zero => simp; positivity
  | succ n =>
    have hf : AntitoneOn (fun x:ℝ => 1/(A+B*x)) (Icc (0:ℝ) n) := by
      intro x hx y hy hxy
      exact div_le_div_of_nonneg_left (by norm_num)
        (add_pos_of_pos_of_nonneg hA (mul_nonneg hB.le hx.1))
        (by nlinarith only [hxy,hB])
    have hs := AntitoneOn.sum_le_integral (a:=n) (x₀:=0)
      (f:=fun x:ℝ => 1/(A+B*x)) (by simpa using hf)
    have hsplit : (∑r∈Finset.range (n+1),1/(A+(r:ℝ)*B))=
        1/A+∑r∈Finset.range n,1/(A+B*(r+1:ℕ)) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero,zero_mul,add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [mul_comm B]
    simp only [zero_add] at hs
    rw [reciprocal_integral hA hB n] at hs
    have hln := Real.log_le_log (by positivity : 0<A+B*(n:ℝ))
      (by simpa only [mul_comm B] using hlast n (by omega))
    have hN : 0<N := hA.trans_le hAN
    rw [hsplit,Real.log_div (ne_of_gt hN) (ne_of_gt hA)]
    exact add_le_add le_rfl (hs.trans (div_le_div_of_nonneg_right (by linarith only [hln]) hB.le))

#print axioms square_tail
#print axioms coeff_prefix_tail
#print axioms reciprocal_prefix
end
end JSP233.LightSeries209
