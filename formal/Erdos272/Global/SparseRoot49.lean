module

public import Erdos272.Global.SparseSmall39
public import Erdos272.Resources.WeightedTail39

@[expose] public section

/-! Actual sparse-family common root from the certified small and large budgets.
The remaining public inputs are the explicit uniform number-theoretic gates. -/
namespace JSP233.SparseRoot49
open StarCompletion SparseSmall39 WeightedTail39
open scoped Classical BigOperators
noncomputable section

def LargeMembers (F : Finset (Finset ℤ)) (K : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => ¬S.card≤16*K)

theorem actual_small_large_partition (F : Finset (Finset ℤ)) (K : ℕ) :
    (SmallMembers F K).card+(LargeMembers F K).card=F.card := by
  exact Finset.card_filter_add_card_filter_not (s:=F) (fun S => S.card≤16*K)

theorem seed49_budget_coefficient :
    ((2*(28:ℝ)-1)/(2*(28:ℝ)^2))+1/32+
      (174/5+16*Seed49Sigma)/185363≤1/12-1/1000 := by
  norm_num [Seed49Sigma]

theorem actual_seed49_large_complement_bound {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hKl : 185363≤K) (hKu : K≤262144)
    (hbad : ∀ S∈F,¬IsAP S)
    (homega : ∀ m≤N,m.primeFactors.card≤13)
    (hratio : ∀ m≤N,(m:ℝ)≤Seed49Ratio*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤21) :
    ((LargeMembers F K).card:ℝ)≤
      ((174/5+16*Seed49Sigma)/185363)*(N:ℝ)^2 := by
  let L := LargeMembers F K
  have hLF : L⊆F := Finset.filter_subset _ _
  have hLL : Legal (Ground N) L := ⟨fun S hS => hlegal.1 S (hLF hS),
    fun S hS T hT hne => hlegal.2 S (hLF hS) T (hLF hT) hne⟩
  have hlow : ∀ S∈L,16*K+1≤S.card := by
    intro S hS
    have hh := (Finset.mem_filter.mp hS).2
    omega
  have hb := actual_seed49_large_budget N K L hLL hKl hKu
    (fun S hS => hbad S (hLF hS)) hlow homega hratio hproduct
  have hKlR : (185363:ℝ)≤K := by exact_mod_cast hKl
  have hm := mul_le_mul_of_nonneg_left hKlR (show (0:ℝ)≤L.card by positivity)
  change (L.card:ℝ)≤_
  nlinarith only [hb,hm]

theorem actual_seed49_empty_kernel_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hlegal : Legal (Ground N) F)
    (hKl : 185363≤K) (hKu : K≤262144) (hthin : 16384*K^2≤N)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅)
    (homega : ∀ m≤N,m.primeFactors.card≤13)
    (hratio : ∀ m≤N,(m:ℝ)≤Seed49Ratio*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤21) :
    (F.card:ℝ)≤(1/12-1/1000)*(N:ℝ)^2 := by
  have hs := actual_small_empty_kernel_rational hN (by norm_num : 2≤28)
    (by omega : 0<K) hlegal hbad hsize hkernel
  have hl := actual_seed49_large_complement_bound hlegal hKl hKu hbad homega hratio hproduct
  have hp := congrArg (fun m : ℕ => (m:ℝ)) (actual_small_large_partition F K)
  simp only [Nat.cast_add] at hp
  have hthinR : (16384:ℝ)*(K:ℝ)^2≤N := by exact_mod_cast hthin
  have ht := mul_le_mul_of_nonneg_right hthinR (show (0:ℝ)≤N by positivity)
  have hc := mul_le_mul_of_nonneg_right seed49_budget_coefficient (sq_nonneg (N:ℝ))
  have hN0 : (0:ℝ)≤N := by positivity
  norm_num only [Nat.cast_ofNat] at hs
  nlinarith only [hs,hl,hp,ht,hc,hN0]

theorem seed49_density_exceeds_empty_kernel_budget {N : ℕ} (hN : 2^49≤N) :
    (1/12-1/1000)*(N:ℝ)^2 < (N:ℝ)^2/12-6343*(N:ℝ)-3 := by
  have hNR : (562949953421312:ℝ)≤N := by
    exact_mod_cast (show 562949953421312≤N by norm_num at hN ⊢; exact hN)
  have hpos : (0:ℝ)<N := by linarith
  have hl : (6344:ℝ)<(N:ℝ)/1000 := by linarith
  have hm := mul_lt_mul_of_pos_right hl hpos
  nlinarith only [hm,hNR]

theorem actual_seed49_sparse_kernel_nonempty {N K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F)
    (hKl : 185363≤K) (hKu : K≤262144) (hthin : 16384*K^2≤N)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hdense : (N:ℝ)^2/12-6343*(N:ℝ)-3≤F.card)
    (homega : ∀ m≤N,m.primeFactors.card≤13)
    (hratio : ∀ m≤N,(m:ℝ)≤Seed49Ratio*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤21) :
    (PrivateFinset.Kernel (Ground N) F).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have h4 : 4≤N := (by norm_num : 4≤(2:ℕ)^49).trans hN
  have hb := actual_seed49_empty_kernel_budget h4 hlegal hKl hKu hthin hbad hsize he
    homega hratio hproduct
  have hc := seed49_density_exceeds_empty_kernel_budget hN
  linarith

theorem actual_seed49_sparse_common_root {N K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hlegal : Legal (Ground N) F)
    (hKl : 185363≤K) (hKu : K≤262144) (hthin : 16384*K^2≤N)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,28*S.card≤N)
    (hdense : (N:ℝ)^2/12-6343*(N:ℝ)-3≤F.card)
    (homega : ∀ m≤N,m.primeFactors.card≤13)
    (hratio : ∀ m≤N,(m:ℝ)≤Seed49Ratio*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤21) :
    ∃ c∈Ground N,∀ S∈F,c∈S := by
  obtain ⟨c,hc⟩ := actual_seed49_sparse_kernel_nonempty hN hlegal hKl hKu hthin
    hbad hsize hdense homega hratio hproduct
  exact ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩

#print axioms actual_small_large_partition
#print axioms seed49_budget_coefficient
#print axioms actual_seed49_large_complement_bound
#print axioms actual_seed49_empty_kernel_budget
#print axioms seed49_density_exceeds_empty_kernel_budget
#print axioms actual_seed49_sparse_kernel_nonempty
#print axioms actual_seed49_sparse_common_root

end
end JSP233.SparseRoot49
