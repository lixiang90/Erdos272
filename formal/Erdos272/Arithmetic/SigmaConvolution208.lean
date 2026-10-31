import Erdos272.Arithmetic.SigmaPrefix209
import Erdos272.Arithmetic.TotientConvolution208
import Erdos272.Resources.UniformAbel208

/-! The finite divisor convolution is the full physical step-weight sum. -/
namespace JSP233.SigmaConvolution208
open PureSource208 APInterval208 TotientConvolution208 UniformSourceCore208 UniformAbel208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem change_variables (s : ℕ) :
    (∑ p ∈ Products s, p.1 * (s - p.1 * p.2)) =
      ∑ p ∈ Divisors s, p.2 * (s - p.1) := by
  apply Finset.sum_bij (fun p _ => (p.1 * p.2, p.1))
  · rintro ⟨q, d⟩ hp
    obtain ⟨hq, hqs, hd, hds, hprod⟩ := mem_products.mp hp
    exact mem_divisors.mpr ⟨by nlinarith, hprod, hq, hqs, dvd_mul_right q d⟩
  · rintro ⟨q, d⟩ hp ⟨r, e⟩ hr he
    have hqr : q = r := congrArg Prod.snd he
    have hprod : q*d=r*e := congrArg Prod.fst he
    have hq : 0 < q := by have hh := (mem_products.mp hp).1; omega
    apply Prod.ext hqr
    rw [← hqr] at hprod
    exact Nat.eq_of_mul_eq_mul_left hq hprod
  · rintro ⟨n, q⟩ hp
    obtain ⟨hn, hns, hq, hqs, hdiv⟩ := mem_divisors.mp hp
    have hqn := Nat.le_of_dvd hn hdiv
    have hqd : q*(n/q)=n := Nat.mul_div_cancel' hdiv
    refine ⟨(q,n/q), ?_, Prod.ext hqd rfl⟩
    exact mem_products.mpr ⟨hq,hqs,Nat.div_pos hqn hq,(Nat.div_le_self n q).trans hns,by omega⟩
  · intro p hp
    rfl

theorem convolution (s : ℕ) :
    (∑ q ∈ Finset.Icc 1 s, q*intervalMultiplicity s q) =
      ∑ n ∈ Finset.Icc 1 s, (s-n)*SigmaSieve209.sigmaOne n := by
  have hprod : (∑ q ∈ Finset.Icc 1 s, q*intervalMultiplicity s q) =
      ∑ p ∈ Products s, p.1*(s-p.1*p.2) := by
    unfold intervalMultiplicity Products
    rw [Finset.sum_filter]
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hqd : q*d≤s
    · simp only [if_pos hqd,Nat.mul_comm d q]
    · simp only [if_neg hqd,Nat.mul_comm d q,Nat.sub_eq_zero_of_le (by omega : s≤q*d),Nat.mul_zero]
  rw [hprod,change_variables]
  unfold Divisors
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = ∑ q ∈ (Finset.Icc 1 s).filter (·∣n), q*(s-n) := (Finset.sum_filter _ _).symm
    _ = ∑ q ∈ n.divisors, q*(s-n) := by rw [divisor_row hn]
    _ = _ := by rw [← Finset.sum_mul,← SigmaSieve209.sigmaOne_eq_sum]; ring

theorem W_eq_Icc (s : ℕ) :
    SigmaPrefix209.W s = ∑ n ∈ Finset.Icc 1 s, (s-n)*SigmaSieve209.sigmaOne n := by
  rw [SigmaPrefix209.W_eq_sum]
  have heq : insert 0 (Finset.Icc 1 s) = Finset.range (s+1) := by
    ext n
    simp only [Finset.mem_insert,Finset.mem_Icc,Finset.mem_range]
    omega
  have hnot : 0 ∉ Finset.Icc 1 s := by simp
  have hh := Finset.sum_insert hnot (f := fun n => (s-n)*SigmaSieve209.sigmaOne n)
  rw [heq,Finset.sum_range_succ] at hh
  simpa using hh

theorem W_eq_weight_sum (s : ℕ) :
    (SigmaPrefix209.W s : ℝ) = ∑ q ∈ Finset.Ico 1 s, w s q := by
  have he : (SigmaPrefix209.W s : ℝ) = ∑ q ∈ Finset.Icc 1 s, w s q := by
    rw [W_eq_Icc,← convolution]
    push_cast
    apply Finset.sum_congr rfl
    intro q hq
    exact (physical_weight s q (by have := (Finset.mem_Icc.mp hq).1; omega)).symm
  rw [he]
  by_cases hs : 0<s
  · have heq : Finset.Icc 1 s=insert s (Finset.Ico 1 s) := by
      ext q
      simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ico]
      omega
    rw [heq,Finset.sum_insert (by simp)]
    rw [physical_weight s s hs,intervalMultiplicity_self]
    simp
  · have hs0 : s=0 := by omega
    simp [hs0]

#print axioms W_eq_weight_sum
end
end JSP233.SigmaConvolution208
