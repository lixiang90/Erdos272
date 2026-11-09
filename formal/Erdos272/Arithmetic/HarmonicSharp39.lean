module

public import Erdos272.Resources.ShortPayment37

@[expose] public section

/-! A fully finite harmonic estimate.  Each dyadic interval beyond 64 is
partitioned into 64 equal integer blocks and bounded by the genuine rational
sum from 64 through 127.  The prefix through 63 is evaluated by ordinary
kernel-checked rational arithmetic.  No logarithm or exponential estimate is
assumed. -/
namespace JSP233.HarmonicSharp39
open scoped BigOperators
noncomputable section

theorem uniform_reciprocal_block (i b : ℕ) (hi : 0 < i) (hb : 0<b) :
    (∑ k∈Finset.Ico (i*b) ((i+1)*b),(1:ℝ)/k)≤1/(i:ℝ) := by
  have hib : 0 < i*b := Nat.mul_pos hi hb
  have hs : (∑ k∈Finset.Ico (i*b) ((i+1)*b),(1:ℝ)/k)≤
      ∑ _k∈Finset.Ico (i*b) ((i+1)*b),(1:ℝ)/(i*b:ℕ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact one_div_le_one_div_of_le (by exact_mod_cast hib)
      (by exact_mod_cast (Finset.mem_Ico.mp hk).1)
  have hlen : (i+1)*b-i*b=b := by simp only [Nat.add_mul,one_mul,Nat.add_sub_cancel_left]
  have hiR : (i:ℝ)≠0 := by exact_mod_cast hi.ne'
  have hbR : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
  have he : (∑ _k∈Finset.Ico (i*b) ((i+1)*b),(1:ℝ)/(i*b:ℕ))=1/(i:ℝ) := by
    rw [Finset.sum_const,Nat.card_Ico,hlen]
    simp only [nsmul_eq_mul,Nat.cast_mul]
    field_simp
  exact hs.trans_eq he

theorem initial_blocks (b n : ℕ) (hb : 0<b) :
    (∑ k∈Finset.Ico (64*b) ((64+n)*b),(1:ℝ)/k)≤
      ∑ i∈Finset.Ico 64 (64+n),(1:ℝ)/i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstart : 64*b≤(64+n)*b := Nat.mul_le_mul_right b (by omega)
    have hstep : (64+n)*b≤(64+(n+1))*b := Nat.mul_le_mul_right b (by omega)
    rw [←Finset.sum_Ico_consecutive (fun k:ℕ=>(1:ℝ)/k) hstart hstep]
    have he : 64+(n+1)=(64+n)+1 := by omega
    rw [he]
    rw [Finset.sum_Ico_succ_top (by omega : 64≤64+n) (fun i:ℕ=>(1:ℝ)/i)]
    have hs := uniform_reciprocal_block (64+n) b (by omega) hb
    linarith

theorem reciprocal_64_certificate :
    (∑ i∈Finset.Ico (64:ℕ) 128,(1:ℝ)/i)<7/10 := by
  norm_num [Finset.sum_Ico_eq_sum_range,Finset.sum_range_succ]

theorem sixty_four_blocks (b : ℕ) (hb : 0<b) :
    (∑ k∈Finset.Ico (64*b) (128*b),(1:ℝ)/k)≤7/10 := by
  exact (initial_blocks b 64 hb).trans (le_of_lt reciprocal_64_certificate)

theorem dyadic_after_six (h : ℕ) :
    (∑ k∈Finset.Ico (2^(6+h):ℕ) (2^(7+h)),(1:ℝ)/k)≤7/10 := by
  have hs := sixty_four_blocks (2^h) (by positivity)
  simpa only [pow_add,show (2:ℕ)^6=64 by norm_num,show (2:ℕ)^7=128 by norm_num] using hs

theorem prefix_six_certificate :
    (∑ i∈Finset.Ico (1:ℕ) (2^6),(1:ℝ)/i)≤473/100 := by
  norm_num [Finset.sum_Ico_eq_sum_range,Finset.sum_range_succ]

theorem prefix_six_plus (h : ℕ) :
    (∑ i∈Finset.Ico (1:ℕ) (2^(6+h)),(1:ℝ)/i)≤473/100+(7/10:ℝ)*h := by
  induction h with
  | zero => simpa using prefix_six_certificate
  | succ h ih =>
    have hpos : 0<(2:ℕ)^(6+h) := by positivity
    have hnext : (2:ℕ)^(6+h)≤2^(7+h) := by
      exact Nat.pow_le_pow_right (by omega : 1≤2) (by omega)
    have he : 6+(h+1)=7+h := by omega
    rw [he,←Finset.sum_Ico_consecutive (fun i:ℕ=>(1:ℝ)/i) (by omega : 1≤2^(6+h)) hnext]
    have hs := dyadic_after_six h
    push_cast
    linarith

theorem reciprocal_prefix_tight (J : ℕ) :
    (∑ i∈Finset.Ico (1:ℕ) (2^J),(1:ℝ)/i)≤53/100+(7/10:ℝ)*J := by
  by_cases hJ : 6≤J
  · obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le hJ
    have hs := prefix_six_plus h
    push_cast
    linarith
  · have hJ' : J<6 := by omega
    interval_cases J <;> norm_num [Finset.sum_Ico_eq_sum_range,Finset.sum_range_succ]

theorem reciprocal_prefix_seven_tenths (J : ℕ) :
    (∑ i∈Finset.Ico (1:ℕ) (2^J),(1:ℝ)/i)≤1+(7/10:ℝ)*J := by
  have hh := reciprocal_prefix_tight J
  linarith

theorem actual_harmonic_tight (N J : ℕ) (hN : N<2^J) :
    HarmonicAbel29.Harmonic N≤53/100+(7/10:ℝ)*J := by
  have hsub : Finset.Icc 1 N⊆Finset.Ico (1:ℕ) (2^J) := by
    intro i hi
    obtain ⟨hil,hiN⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Ico.mpr ⟨hil,hiN.trans_lt hN⟩
  have hs : HarmonicAbel29.Harmonic N≤∑ i∈Finset.Ico (1:ℕ) (2^J),(1:ℝ)/i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  exact hs.trans (reciprocal_prefix_tight J)

theorem actual_harmonic_seven_tenths (N J : ℕ) (hN : N<2^J) :
    HarmonicAbel29.Harmonic N≤1+(7/10:ℝ)*J := by
  have hh := actual_harmonic_tight N J hN
  linarith

#print axioms uniform_reciprocal_block
#print axioms initial_blocks
#print axioms reciprocal_64_certificate
#print axioms sixty_four_blocks
#print axioms dyadic_after_six
#print axioms prefix_six_certificate
#print axioms prefix_six_plus
#print axioms reciprocal_prefix_tight
#print axioms reciprocal_prefix_seven_tenths
#print axioms actual_harmonic_tight
#print axioms actual_harmonic_seven_tenths
end
end JSP233.HarmonicSharp39
