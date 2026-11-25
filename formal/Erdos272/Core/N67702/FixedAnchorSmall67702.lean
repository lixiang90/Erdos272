module

public import Erdos272.Core.N82427.FixedAnchorSingleton82427
public import Erdos272.Core.N82427.FixedAnchorNoSingleton82427

@[expose] public section

namespace JSP233.FixedAnchorSmall67702
open StarCompletion SparseSmall39 SmallKernel112
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem one_le_price {N a m : ℕ} (hN : 2*m+3≤N) (ha : a≤m) :
    (1 : ℝ)≤(FixedSmallScalars82427.Coefficient a m : ℝ)*N-
      FixedSmallScalars82427.Credit a m := by
  have hNR : 2*(m : ℝ)+3≤N := by exact_mod_cast hN
  have hp := mul_le_mul_of_nonneg_left hNR (show (0 : ℝ)≤(m : ℝ)+1 by positivity)
  have hc := FixedSmallScalars82427.credit_double 0 m
  norm_num only [Nat.cast_zero, zero_mul, zero_add] at hc
  have hbase : (1 : ℝ)≤(FixedSmallScalars82427.Coefficient 0 m : ℝ)*N-
      FixedSmallScalars82427.Credit 0 m := by
    simp only [FixedSmallScalars82427.Coefficient, zero_add, one_mul,
      Nat.cast_add, Nat.cast_one]
    nlinarith only [hp, hc, Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ)]
  exact hbase.trans (FixedSmallScalars82427.anchor_mono hN (Nat.zero_le a) ha)

theorem actual_fixed_anchor_small_credit {N L T : ℕ} {F : Finset (Finset ℤ)}
    (hL : 2≤L) (hTL : T≤L) (hN : 2*L+1≤N)
    (hgap : L+1+(L-1)^2/4≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hsmall : (Small F T).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L)=∅) :
    (F.card : ℝ)≤(FixedSmallScalars82427.Coefficient (T-1) (L-1) : ℝ)*N-
      FixedSmallScalars82427.Credit (T-1) (L-1) := by
  have hN' : 2*(L-1)+3≤N := by omega
  have hT' : T-1≤L-1 := Nat.sub_le_sub_right hTL 1
  by_cases hone : F.card≤1
  · have hfR : (F.card : ℝ)≤1 := by exact_mod_cast hone
    exact hfR.trans (one_le_price hN' hT')
  have htwo : 2≤F.card := by omega
  obtain ⟨A,hAS⟩ := hsmall
  obtain ⟨hAF,hAT⟩ := Finset.mem_filter.mp hAS
  have hAL : A.card≤L := hAT.trans hTL
  have hASL : A∈Small F L := Finset.mem_filter.mpr ⟨hAF,hAL⟩
  have hAN := actual_member_nonempty_of_two hlegal htwo hAF
  have hpay : (F.card : ℝ)≤
      (FixedSmallScalars82427.Coefficient (A.card-1) (L-1) : ℝ)*N-
        FixedSmallScalars82427.Credit (A.card-1) (L-1) := by
    by_cases hsing : ∃ B∈Small F L, ∃ c : ℤ, A∩B={c}
    · obtain ⟨B,hBS,c,hAB⟩ := hsing
      obtain ⟨hBF,hBL⟩ := Finset.mem_filter.mp hBS
      have hcA : c∈A := (Finset.mem_inter.mp (show c∈A∩B by rw [hAB]; simp)).1
      obtain ⟨U,hUS,hcU⟩ := actual_omitter_of_empty_kernel hkernel c (hlegal.1 A hAF hcA)
      obtain ⟨hUF,hUL⟩ := Finset.mem_filter.mp hUS
      exact FixedAnchorSingleton82427.actual_fixed_singleton_credit hL hN hlegal hbad
        hAF hBF hAL hBL hAB hUF hUL hcU
    · exact FixedAnchorNoSingleton82427.actual_fixed_no_singleton_credit hL hN hgap
        hlegal hbad hASL hAN hkernel hsing
  exact hpay.trans (FixedSmallScalars82427.anchor_mono hN'
    (Nat.sub_le_sub_right hAT 1) hT')

#print axioms one_le_price
#print axioms actual_fixed_anchor_small_credit
end
end JSP233.FixedAnchorSmall67702
