module

public import Erdos272.Core.N82427.FixedAnchorSingleton82427
public import Erdos272.Core.N82427.FixedAnchorNoSingleton82427
public import Erdos272.Resources.N84364.SmallCredit84364

@[expose] public section

namespace JSP233.SmallCredit82427
open StarCompletion SparseSmall39 SmallKernel112
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_small_empty_kernel86 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1893≤N) (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hsmall : (Small F 86).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 86)=∅) :
    (F.card : ℝ)≤7311*(N : ℝ)-632402 := by
  have hvalue : 86+1+(86-1)^2/4=1893 := by norm_num
  have hb := SmallCredit84364.actual_small_empty_kernel_credit (by decide : 2≤86)
    (by omega : 2*86+1≤N) (by rw [hvalue]; exact hN) hlegal hbad hsmall hkernel
  norm_num [SmallCreditScalars84364.Coefficient, SmallCreditScalars84364.Credit,
    Nat.choose_two_right] at hb
  exact hb

theorem actual_small87_with_small86 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1937≤N) (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hsmall : (Small F 86).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 87)=∅) :
    (F.card : ℝ)≤7397*(N : ℝ)-643540 := by
  have hn : (1937 : ℝ)≤N := by exact_mod_cast hN
  by_cases hone : F.card≤1
  · have hfR : (F.card : ℝ)≤1 := by exact_mod_cast hone
    linarith only [hn, hfR]
  have htwo : 2≤F.card := by omega
  obtain ⟨A, hAS⟩ := hsmall
  obtain ⟨hAF, hAL⟩ := Finset.mem_filter.mp hAS
  have hAN := actual_member_nonempty_of_two hlegal htwo hAF
  have hAS87 : A∈Small F 87 := Finset.mem_filter.mpr ⟨hAF, by omega⟩
  have hpay : (F.card : ℝ)≤
      (FixedSmallScalars82427.Coefficient (A.card-1) 86 : ℝ)*N-
        FixedSmallScalars82427.Credit (A.card-1) 86 := by
    by_cases hsing : ∃ B∈Small F 87, ∃ c : ℤ, A∩B={c}
    · obtain ⟨B, hBS, c, hAB⟩ := hsing
      obtain ⟨hBF, hBL⟩ := Finset.mem_filter.mp hBS
      have hcA : c∈A := (Finset.mem_inter.mp (show c∈A∩B by rw [hAB]; simp)).1
      obtain ⟨T, hTS, hcT⟩ := actual_omitter_of_empty_kernel hkernel c (hlegal.1 A hAF hcA)
      obtain ⟨hTF, hTL⟩ := Finset.mem_filter.mp hTS
      exact FixedAnchorSingleton82427.actual_fixed_singleton_credit (by decide : 2≤87)
        (by omega) hlegal hbad hAF hBF (by omega) hBL hAB hTF hTL hcT
    · exact FixedAnchorNoSingleton82427.actual_fixed_no_singleton_credit (by decide : 2≤87)
        (by omega) (by norm_num; exact hN) hlegal hbad hAS87 hAN hkernel hsing
  have hmono := FixedSmallScalars82427.anchor_mono
    (by omega : 2*86+3≤N) (by omega : A.card-1≤85) (by decide : 85≤86)
  have hclosed : (FixedSmallScalars82427.Coefficient 85 86 : ℝ)*N-
      FixedSmallScalars82427.Credit 85 86=7397*(N : ℝ)-643540 := by
    norm_num [FixedSmallScalars82427.Coefficient, FixedSmallScalars82427.Credit,
      Nat.choose_two_right]
  exact (hpay.trans hmono).trans_eq hclosed

#print axioms actual_small_empty_kernel86
#print axioms actual_small87_with_small86
end
end JSP233.SmallCredit82427
