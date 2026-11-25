module

public import Erdos272.Resources.N84364.SingletonSmallCredit84364
public import Erdos272.Resources.N84364.NoSingletonSmallCredit84364

@[expose] public section

namespace JSP233.SmallCredit84364
open StarCompletion SparseSmall39 SmallKernel112 SmallCreditScalars84364
open SingletonSmallCredit84364 NoSingletonSmallCredit84364
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_small_empty_kernel_credit {N L : ℕ} {F : Finset (Finset ℤ)}
    (hL : 2≤L) (hN : 2*L+1≤N) (hgap : L+1+(L-1)^2/4≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hsmall : (Small F L).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F L)=∅) :
    (F.card : ℝ)≤(Coefficient L : ℝ)*N-Credit L := by
  by_cases hone : F.card≤1
  · have hfR : (F.card : ℝ)≤1 := by exact_mod_cast hone
    exact hfR.trans (trivial_credit_L hL hN)
  have htwo : 2≤F.card := by omega
  obtain ⟨A, hAS⟩ := hsmall
  obtain ⟨hAF, hAL⟩ := Finset.mem_filter.mp hAS
  have hAN := actual_member_nonempty_of_two hlegal htwo hAF
  by_cases hsing : ∃ B ∈ Small F L, ∃ c : ℤ, A∩B={c}
  · obtain ⟨B, hBS, c, hAB⟩ := hsing
    obtain ⟨hBF, hBL⟩ := Finset.mem_filter.mp hBS
    have hcA : c∈A := (Finset.mem_inter.mp (show c∈A∩B by rw [hAB]; simp)).1
    obtain ⟨T, hTS, hcT⟩ := actual_omitter_of_empty_kernel hkernel c (hlegal.1 A hAF hcA)
    obtain ⟨hTF, hTL⟩ := Finset.mem_filter.mp hTS
    exact actual_singleton_small_credit hL hN hlegal hbad hAF hBF hAL hBL hAB hTF hTL hcT
  · exact actual_fixed_no_singleton_credit hL hN hgap hlegal hbad hAS hAN hkernel hsing

theorem actual_small_empty_kernel87 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1937≤N) (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hsmall : (Small F 87).Nonempty)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 87)=∅) :
    (F.card : ℝ)≤7483*(N : ℝ)-654763 := by
  have hvalue : 87+1+(87-1)^2/4=1937 := by norm_num
  have hb := actual_small_empty_kernel_credit (by decide : 2≤87)
    (by omega : 2*87+1≤N) (by rw [hvalue]; exact hN) hlegal hbad hsmall hkernel
  norm_num [Coefficient, Credit, Nat.choose_two_right] at hb
  exact hb

#print axioms actual_small_empty_kernel_credit
#print axioms actual_small_empty_kernel87
end
end JSP233.SmallCredit84364
