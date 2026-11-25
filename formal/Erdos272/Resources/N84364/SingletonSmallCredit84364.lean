module

public import Erdos272.Counting.N84364.SingletonRank84364

@[expose] public section

namespace JSP233.SingletonSmallCredit84364
open StarCompletion SparseSmall39 SmallCreditScalars84364 SingletonRank84364
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_singleton_small_credit {N L : ℕ} {F : Finset (Finset ℤ)}
    {A B T : Finset ℤ} {c : ℤ} (hL : 2≤L) (hN : 2*L+1≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hA : A∈F) (hB : B∈F) (hAL : A.card≤L) (hBL : B.card≤L) (hAB : A∩B={c})
    (hT : T∈F) (hTL : T.card≤L) (hTc : c∉T) :
    (F.card : ℝ)≤(Coefficient L : ℝ)*N-Credit L := by
  have hav := actual_singleton_avoider_price hL hN hlegal hbad hA hB hAL hBL hAB
  have hd := (actual_degree_from_omitter hlegal hbad hT hTc).trans (degreeBudget_mono N hTL)
  have hclosed := degreeBudget_closed N L (by omega : 2≤N) (by omega : L+1≤N)
  have hbudget : DegreeBudget N L+L.choose 2+2*L=L*N := by
    calc
      _=L*(N-2)+2*L := by rw [hclosed]
      _=L*((N-2)+2) := by ring
      _=L*N := by rw [Nat.sub_add_cancel (by omega : 2≤N)]
  have hroot : (RootPart F c).card+L.choose 2+2*L≤L*N := by omega
  have hrootR : ((RootPart F c).card : ℝ)+(L.choose 2 : ℝ)+2*(L : ℝ)≤(L : ℝ)*N := by
    exact_mod_cast hroot
  have hpartR : ((RootPart F c).card : ℝ)+((Avoiders F c).card : ℝ)=(F.card : ℝ) := by
    exact_mod_cast root_avoider_card_partition F c
  have havR : ((Avoiders F c).card : ℝ)+((L-1 : ℕ) : ℝ)^2*
      (((L-1 : ℕ) : ℝ)+2)≤((L-1 : ℕ) : ℝ)^2*N := hav
  have hrel : ((L-1 : ℕ) : ℝ)+2=(L : ℝ)+1 := by
    exact_mod_cast (by omega : L-1+2=L+1)
  rw [hrel] at havR
  unfold Coefficient Credit
  push_cast
  nlinarith only [havR, hrootR, hpartR]

#print axioms actual_singleton_small_credit
end
end JSP233.SingletonSmallCredit84364
