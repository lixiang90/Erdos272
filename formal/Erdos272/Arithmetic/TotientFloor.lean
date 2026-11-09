module

public import Erdos272.Arithmetic.MobiusUniform
public import Erdos272.Foundation.StaircaseCertificate
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace JSP233.TotientFloor29
open scoped BigOperators
open ArithmeticFunction
noncomputable section
set_option maxHeartbeats 1000000

def divisorError (r : Nat) : Real := ∑ d ∈ r.divisors, |(moebius d : Real)|

theorem divisors_eq_filter_Icc (n R : Nat) (hn : 0 < n) (hnR : n ≤ R) :
    n.divisors = (Finset.Icc 1 R).filter (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · intro hd
    exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd),
      (Nat.le_of_dvd hn hd.1).trans hnR⟩,hd.1⟩
  · exact fun hd => ⟨hd.2,by omega⟩

theorem multiples_eq_image (R d : Nat) (hd : 0 < d) :
    (Finset.Icc 1 R).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (R/d)).image (fun k => d*k) := by
  ext n
  simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_image]
  constructor
  · intro hn
    refine ⟨n/d,⟨?_,?_⟩,Nat.mul_div_cancel' hn.2⟩
    · exact Nat.div_pos (Nat.le_of_dvd hn.1.1 hn.2) hd
    · exact Nat.div_le_div_right hn.1.2
  · rintro ⟨k,⟨hk,hkR⟩,rfl⟩
    refine ⟨⟨by nlinarith,?_⟩,dvd_mul_right d k⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkR

theorem sum_multiples_reindex (R d : Nat) (hd : 0 < d) (f : Nat → Real) :
    (∑ n ∈ Finset.Icc 1 R, if d ∣ n then f (n/d) else 0) =
      ∑ k ∈ Finset.Icc 1 (R/d), f k := by
  rw [← Finset.sum_filter,multiples_eq_image R d hd,Finset.sum_image]
  · simp only [Nat.mul_div_cancel_left _ hd]
  · intro x hx y hy heq
    exact Nat.eq_of_mul_eq_mul_left hd heq

theorem divisor_sum_prefix (R : Nat) (f : Nat → Nat → Real) :
    (∑ n ∈ Finset.Icc 1 R, ∑ d ∈ n.divisors, f d (n/d)) =
      ∑ d ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc 1 (R/d), f d k := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 R, ∑ d ∈ Finset.Icc 1 R,
          if d ∣ n then f d (n/d) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [divisors_eq_filter_Icc n R (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
        Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_multiples_reindex R d (Finset.mem_Icc.mp hd).1 (f d)

theorem divisor_sum_prefix_const (R : Nat) (f : Nat → Real) :
    (∑ n ∈ Finset.Icc 1 R, ∑ d ∈ n.divisors, f d) =
      ∑ d ∈ Finset.Icc 1 R, f d * ((R/d : Nat):Real) := by
  simpa [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul,mul_comm] using
    divisor_sum_prefix R (fun d _ => f d)

theorem totient_moebius_identity (n : Nat) (hn : 0 < n) :
    (Nat.totient n : Real) =
      ∑ d ∈ n.divisors, (moebius d : Real) * ((n/d : Nat):Real) := by
  have hs : ∀ m : Nat, 0 < m → (∑ i ∈ m.divisors, (Nat.totient i : Real)) = (m : Real) := by
    intro m hm
    exact_mod_cast Nat.sum_totient m
  have h := ((sum_eq_iff_sum_mul_moebius_eq
    (f := fun m => (Nat.totient m : Real)) (g := fun m => (m : Real))).mp hs n hn).symm
  rwa [Nat.sum_divisorsAntidiagonal (fun d k => (moebius d : Real)*(k:Real))] at h

theorem normalized_totient_identity (n : Nat) (hn : 0 < n) :
    (Nat.totient n : Real) / n = ∑ d ∈ n.divisors, (moebius d : Real) / d := by
  rw [totient_moebius_identity n hn]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos : (0:Real) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hnpos : (0:Real) < n := by exact_mod_cast hn
  rw [Nat.cast_div hdvd (ne_of_gt hdpos)]
  field_simp

theorem normalized_totient_prefix_floor (R : Nat) :
    (∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real) / n) =
      ∑ d ∈ Finset.Icc 1 R, (moebius d : Real) / d * ((R/d : Nat):Real) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 R, ∑ d ∈ n.divisors, (moebius d : Real) / d := by
      apply Finset.sum_congr rfl
      intro n hn
      exact normalized_totient_identity n (Finset.mem_Icc.mp hn).1
    _ = _ := divisor_sum_prefix_const R _

theorem sum_Icc_cast (q : Nat) :
    (∑ k ∈ Finset.Icc 1 q, (k : Real)) = (q:Real)*((q:Real)+1)/2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih]
    push_cast
    ring

theorem totient_prefix_floor (R : Nat) :
    (∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real)) =
      (1/2:Real) * ∑ d ∈ Finset.Icc 1 R,
        (moebius d : Real) * ((R/d : Nat):Real) * (((R/d : Nat):Real)+1) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 R,
        ∑ d ∈ n.divisors, (moebius d : Real)*((n/d : Nat):Real) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact totient_moebius_identity n (Finset.mem_Icc.mp hn).1
    _ = ∑ d ∈ Finset.Icc 1 R,
        ∑ k ∈ Finset.Icc 1 (R/d), (moebius d : Real)*(k:Real) :=
          divisor_sum_prefix R (fun d k => (moebius d : Real)*(k:Real))
    _ = _ := by
      simp_rw [← Finset.mul_sum,sum_Icc_cast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem nat_div_bounds (R d : Nat) (hd : 0 < d) :
    ((R/d : Nat):Real) ≤ (R:Real)/d ∧ (R:Real)/d ≤ ((R/d : Nat):Real)+1 := by
  refine ⟨Nat.cast_div_le,?_⟩
  have hp : (0:Real) < d := by exact_mod_cast hd
  apply (div_le_iff₀ hp).mpr
  have hnat := Nat.lt_mul_div_succ R hd
  have hcast : (R:Real) < (d:Real) * (((R/d:Nat):Real)+1) := by exact_mod_cast hnat
  nlinarith

theorem signed_floor_lower (R d : Nat) (hd : 0 < d) (m : Real) :
    m*((R:Real)/d) - |m| ≤ m*((R/d:Nat):Real) := by
  obtain ⟨hlo,hhi⟩ := nat_div_bounds R d hd
  by_cases hm : 0 ≤ m
  · rw [abs_of_nonneg hm]
    have h := mul_le_mul_of_nonneg_left hhi hm
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hm)]
    have h := mul_le_mul_of_nonpos_left hlo (le_of_lt (lt_of_not_ge hm))
    nlinarith

theorem triangular_floor_error (R d : Nat) (hd : 0 < d) :
    -((R:Real)/d) ≤ ((R/d:Nat):Real)*(((R/d:Nat):Real)+1)-((R:Real)/d)^2 ∧
    ((R/d:Nat):Real)*(((R/d:Nat):Real)+1)-((R:Real)/d)^2 ≤ (R:Real)/d := by
  obtain ⟨hlo,hhi⟩ := nat_div_bounds R d hd
  have hq : (0:Real) ≤ ((R/d:Nat):Real) := Nat.cast_nonneg _
  have ht : (0:Real) ≤ (R:Real)/d := by positivity
  have hp := mul_nonneg (show 0 ≤ ((R/d:Nat):Real)+1-(R:Real)/d by linarith)
    (show 0 ≤ ((R/d:Nat):Real)+(R:Real)/d by positivity)
  have hu := mul_le_mul hlo (show ((R/d:Nat):Real)+1 ≤ (R:Real)/d+1 by linarith)
    (show 0 ≤ ((R/d:Nat):Real)+1 by positivity) ht
  constructor <;> nlinarith

theorem moebius_abs_real_le_one (d : Nat) : |(moebius d : Real)| ≤ 1 := by
  exact_mod_cast (abs_moebius_le_one (n := d))

theorem normalized_floor_term_lower (R d : Nat) (hd : 0 < d) :
    (R:Real)*(moebius d : Real)/(d:Real)^2 - 1/(d:Real) ≤
      (moebius d : Real)/(d:Real)*((R/d:Nat):Real) := by
  have hs := signed_floor_lower R d hd (moebius d : Real)
  have hb := moebius_abs_real_le_one d
  have hp : (0:Real) < d := by exact_mod_cast hd
  have hdiv := div_le_div_of_nonneg_right (show
    (moebius d : Real)*((R:Real)/d)-1 ≤ (moebius d : Real)*((R/d:Nat):Real) by linarith)
      (le_of_lt hp)
  calc
    _ = ((moebius d : Real)*((R:Real)/d)-1)/(d:Real) := by
      field_simp [ne_of_gt hp]
    _ ≤ ((moebius d : Real)*((R/d:Nat):Real))/(d:Real) := hdiv
    _ = _ := by ring

theorem normalized_totient_floor_lower (R : Nat) :
    (R:Real)*MobiusUniform28.partialSum R -
      (∑ d ∈ Finset.Icc 1 R, (1:Real)/d) ≤
        ∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real)/n := by
  rw [normalized_totient_prefix_floor]
  have hs := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 R) =>
    normalized_floor_term_lower R d (Finset.mem_Icc.mp hd).1)
  calc
    _ = ∑ d ∈ Finset.Icc 1 R,
        ((R:Real)*(moebius d : Real)/(d:Real)^2 - 1/(d:Real)) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      unfold MobiusUniform28.partialSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := hs

theorem normalized_totient_prefix_lower (R : Nat) (hR : 1 ≤ R) :
    (607/1000:Real)*(R:Real)-1-(∑ d ∈ Finset.Icc 1 R, (1:Real)/d) ≤
      ∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real)/n := by
  have hr : (0:Real) < R := by exact_mod_cast hR
  have hs := mul_le_mul_of_nonneg_left
    (MobiusUniform28.actual_moebius_partial_sum_ge R hR) (le_of_lt hr)
  have heq : (R:Real)*((607/1000:Real)-1/(R:Real)) = (607/1000:Real)*R-1 := by
    field_simp [ne_of_gt hr]
  rw [heq] at hs
  exact (sub_le_sub_right hs _).trans (normalized_totient_floor_lower R)

theorem signed_triangular_floor_lower (R d : Nat) (hd : 0 < d) (m : Real)
    (hm : |m| ≤ 1) :
    m*((R:Real)/d)^2-(R:Real)/d ≤
      m*((R/d:Nat):Real)*(((R/d:Nat):Real)+1) := by
  obtain ⟨hlo,hhi⟩ := triangular_floor_error R d hd
  have ht : (0:Real) ≤ (R:Real)/d := by positivity
  obtain ⟨hmlo,hmhi⟩ := abs_le.mp hm
  by_cases hsign : 0 ≤ m
  · have hp := mul_nonneg hsign (show 0 ≤
      ((R/d:Nat):Real)*(((R/d:Nat):Real)+1)-((R:Real)/d)^2+(R:Real)/d by linarith)
    have hq := mul_nonneg (show 0 ≤ 1-m by linarith) ht
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ -m by linarith) (show 0 ≤
      (R:Real)/d-(((R/d:Nat):Real)*(((R/d:Nat):Real)+1)-((R:Real)/d)^2) by linarith)
    have hq := mul_nonneg (show 0 ≤ m+1 by linarith) ht
    nlinarith

theorem totient_floor_lower (R : Nat) :
    (R:Real)^2/2*MobiusUniform28.partialSum R -
      (R:Real)/2*(∑ d ∈ Finset.Icc 1 R, (1:Real)/d) ≤
        ∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real) := by
  have hmain : (∑ d ∈ Finset.Icc 1 R, (moebius d : Real)*((R:Real)/d)^2) =
      (R:Real)^2*MobiusUniform28.partialSum R := by
    unfold MobiusUniform28.partialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have herr : (∑ d ∈ Finset.Icc 1 R, (R:Real)/d) =
      (R:Real)*(∑ d ∈ Finset.Icc 1 R, (1:Real)/d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hs := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 R) =>
    signed_triangular_floor_lower R d (Finset.mem_Icc.mp hd).1
      (moebius d : Real) (moebius_abs_real_le_one d))
  calc
    _ = (1/2:Real)*((∑ d ∈ Finset.Icc 1 R, (moebius d : Real)*((R:Real)/d)^2) -
        (∑ d ∈ Finset.Icc 1 R, (R:Real)/d)) := by rw [hmain,herr]; ring
    _ = (1/2:Real)*(∑ d ∈ Finset.Icc 1 R,
        ((moebius d : Real)*((R:Real)/d)^2-(R:Real)/d)) := by rw [Finset.sum_sub_distrib]
    _ ≤ (1/2:Real)*(∑ d ∈ Finset.Icc 1 R,
        (moebius d : Real)*((R/d:Nat):Real)*(((R/d:Nat):Real)+1)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := (totient_prefix_floor R).symm

theorem totient_prefix_lower (R : Nat) (hR : 1 ≤ R) :
    (607/2000:Real)*(R:Real)^2-(R:Real)/2-
      (R:Real)/2*(∑ d ∈ Finset.Icc 1 R, (1:Real)/d) ≤
        ∑ n ∈ Finset.Icc 1 R, (Nat.totient n : Real) := by
  have hr : (0:Real) < R := by exact_mod_cast hR
  have hs := mul_le_mul_of_nonneg_left
    (MobiusUniform28.actual_moebius_partial_sum_ge R hR)
      (show 0 ≤ (R:Real)^2/2 by positivity)
  have heq : (R:Real)^2/2*((607/1000:Real)-1/(R:Real)) =
      (607/2000:Real)*(R:Real)^2-(R:Real)/2 := by field_simp; ring
  rw [heq] at hs
  exact (sub_le_sub_right hs _).trans (totient_floor_lower R)

theorem divisorError_prefix_floor (R : Nat) :
    (∑ r ∈ Finset.Icc 1 R, divisorError r) =
      ∑ d ∈ Finset.Icc 1 R, |(moebius d : Real)| * ((R/d:Nat):Real) := by
  exact divisor_sum_prefix_const R (fun d => |(moebius d : Real)|)

theorem divisorError_prefix_upper (R : Nat) :
    (∑ r ∈ Finset.Icc 1 R, divisorError r) ≤
      (R:Real)*(∑ d ∈ Finset.Icc 1 R, (1:Real)/d) := by
  rw [divisorError_prefix_floor,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hb := moebius_abs_real_le_one d
  have hdiv : ((R/d:Nat):Real) ≤ (R:Real)/d := Nat.cast_div_le
  have h := mul_le_mul hb hdiv (Nat.cast_nonneg (R/d)) (by norm_num : (0:Real) ≤ 1)
  simpa only [one_mul,mul_one_div] using h

#print axioms divisors_eq_filter_Icc
#print axioms multiples_eq_image
#print axioms sum_multiples_reindex
#print axioms divisor_sum_prefix
#print axioms divisor_sum_prefix_const
#print axioms totient_moebius_identity
#print axioms normalized_totient_identity
#print axioms normalized_totient_prefix_floor
#print axioms sum_Icc_cast
#print axioms totient_prefix_floor
#print axioms nat_div_bounds
#print axioms signed_floor_lower
#print axioms triangular_floor_error
#print axioms moebius_abs_real_le_one
#print axioms normalized_floor_term_lower
#print axioms normalized_totient_floor_lower
#print axioms normalized_totient_prefix_lower
#print axioms signed_triangular_floor_lower
#print axioms totient_floor_lower
#print axioms totient_prefix_lower
#print axioms divisorError_prefix_floor
#print axioms divisorError_prefix_upper
end
end JSP233.TotientFloor29
