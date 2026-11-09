module

public import Erdos272.Arithmetic.StepWeightMoment208
public import Erdos272.Arithmetic.SigmaConvolution208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! The finite W bound and the exact short tail control every physical prefix. -/
namespace JSP233.UniformMoment208
open UniformSourceCore208 StepWeightShape208 StepWeightIntegral208 StepWeightMoment208
open SigmaConvolution208 MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
set_option maxHeartbeats 0

def PrefixW (s m : ℕ) : ℝ := ∑ q ∈ Finset.Ico 1 m, w s q

theorem shifted_sum (f : ℕ→ℝ) (n k : ℕ) :
    (∑ j ∈ Finset.range k, f (n+j)) = ∑ q ∈ Finset.Ico n (n+k), f q := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,ih,show n+(k+1)=n+k+1 by omega,
      Finset.sum_Ico_succ_top (by omega : n≤n+k)]

theorem prefix_mono (s : ℕ) {n m : ℕ} (hnm : n≤m) : PrefixW s n≤PrefixW s m := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_Ico] at hq ⊢
    omega
  · intro q hq hnot
    apply w_nonneg (by positivity)
    have hq1 := (Finset.mem_Ico.mp hq).1
    exact_mod_cast (by omega : 0<q)

theorem integer_prefix_bound {s n : ℕ} (hs : 0<s) (hn : 0<n) (hns : n≤s)
    (hsn : (s : ℝ)<6*n)
    (hW : (SigmaPrefix209.W s : ℝ) ≤ UniformSourceCore208.Sigma*(s : ℝ)^3/6-
      (s : ℝ)^2/4+14/5*s) :
    PrefixW s n ≤ I s n-(s : ℝ)^2/4-w s n/2+53/10*s := by
  have ht := tail_trapezoid (s := (s : ℝ)) (n := n) (k := s-n) (by positivity) hn hsn
  rw [Nat.add_sub_of_le hns,shifted_sum (fun q : ℕ => w (s : ℝ) q) n (s-n),
    Nat.add_sub_of_le hns,w_self (by positivity)] at ht
  have hi := integral_eq_moment (s := (s : ℝ)) (m := (n : ℝ)) (by positivity)
    (by positivity) (by exact_mod_cast hns) hsn
  rw [hi] at ht
  have hf := Finset.sum_Ico_consecutive (fun q => w (s : ℝ) q) (by omega : 1≤n) hns
  have he : PrefixW s n+(∑ q ∈ Finset.Ico n s, w s q)=(SigmaPrefix209.W s : ℝ) := by
    rw [W_eq_weight_sum]
    exact hf
  have hsub : (s-n : ℕ)≤s := Nat.sub_le _ _
  have hsubR : ((s-n : ℕ) : ℝ)≤s := by exact_mod_cast hsub
  nlinarith only [ht,he,hW,hsubR]

theorem moment_mono {s a b : ℝ} (hs : 0≤s) (ha : 0<a) (hab : a≤b)
    (hbs : b≤s) (hsa : s<6*a) : I s a≤I s b := by
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hsb : s<6*b := by linarith only [hsa,hab]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (w_intervalIntegrable hs ha hsa hab) (w_intervalIntegrable hs hb hsb hbs)
  have hn : 0≤∫ x in a..b, w s x := intervalIntegral.integral_nonneg hab
    (fun x hx => w_nonneg hs (lt_of_lt_of_le ha hx.1))
  rw [integral_eq_moment hs ha (hab.trans hbs) hsa,integral_eq_moment hs hb hbs hsb] at hi
  linarith only [hi,hn]

theorem real_prefix_bound {s m0 : ℕ} {m : ℝ} (hs : 31≤s)
    (hm0 : (m0 : ℝ)≤m) (hm : (s : ℝ)/5≤m) (hms : m≤s)
    (hW : (SigmaPrefix209.W s : ℝ)≤UniformSourceCore208.Sigma*(s : ℝ)^3/6-
      (s : ℝ)^2/4+14/5*s) :
    PrefixW s m0≤I s m-(s : ℝ)^2/4-w s m/2+53/10*s := by
  let n := Nat.floor m
  have hsR : (31 : ℝ)≤s := by exact_mod_cast hs
  have hmpos : 0<m := by linarith only [hsR,hm]
  have hnR : (n : ℝ)≤m := Nat.floor_le hmpos.le
  have hmhi : m<(n : ℝ)+1 := Nat.lt_floor_add_one m
  have hn : 0<n := by
    have hh : 1≤Nat.floor m := (Nat.one_le_floor_iff m).mpr (by linarith only [hsR,hm])
    exact lt_of_lt_of_le Nat.zero_lt_one hh
  have hns : n≤s := by exact_mod_cast (hnR.trans hms)
  have hsn : (s : ℝ)<6*n := by linarith only [hmhi,hm,hsR]
  have hm0n : m0≤n := Nat.le_floor hm0
  have hb := integer_prefix_bound (by omega : 0<s) hn hns hsn hW
  have hI := moment_mono (by positivity : (0 : ℝ)≤s) (by positivity : (0 : ℝ)<n) hnR hms hsn
  have hw := w_antitone (by positivity : (0 : ℝ)<s) (by positivity : (0 : ℝ)<n) hnR
  have hp := prefix_mono s hm0n
  linarith only [hb,hI,hw,hp]

#print axioms integer_prefix_bound
#print axioms real_prefix_bound
end
end JSP233.UniformMoment208
