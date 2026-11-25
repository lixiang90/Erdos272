module

public import Erdos272.Counting.N84364.SingletonRank84364
public import Erdos272.Counting.N82427.FixedSmallScalars82427

@[expose] public section

namespace JSP233.FixedAnchorSingleton82427
open StarCompletion SparseSmall39 SingletonRank84364
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_fixed_singleton_credit {N L : ℕ} {F : Finset (Finset ℤ)}
    {A B T : Finset ℤ} {c : ℤ} (hL : 2≤L) (hN : 2*L+1≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hA : A∈F) (hB : B∈F) (hAL : A.card≤L) (hBL : B.card≤L)
    (hAB : A∩B={c}) (hT : T∈F) (hTL : T.card≤L) (hTc : c∉T) :
    (F.card : ℝ)≤(FixedSmallScalars82427.Coefficient (A.card-1) (L-1) : ℝ)*N-
      FixedSmallScalars82427.Credit (A.card-1) (L-1) := by
  let a := (A.erase c).card
  let b := (B.erase c).card
  let m := L-1
  have hc : c∈A∩B := by rw [hAB]; simp
  have haeq : a=A.card-1 := Finset.card_erase_of_mem (Finset.mem_inter.mp hc).1
  have hbeq : b=B.card-1 := Finset.card_erase_of_mem (Finset.mem_inter.mp hc).2
  have ha : a≤m := by dsimp only [m]; rw [haeq]; exact Nat.sub_le_sub_right hAL 1
  have hb : b≤m := by dsimp only [m]; rw [hbeq]; exact Nat.sub_le_sub_right hBL 1
  have hN' : 2*m+3≤N := by dsimp only [m]; omega
  have hRank := actual_singleton_rank_budget hlegal hbad hA hB hAB
  change (Avoiders F c).card+3*a*b+b*a.choose 2+a*b.choose 2≤a*b*N at hRank
  have hRankR : ((Avoiders F c).card : ℝ)+3*(a : ℝ)*b+
      (b : ℝ)*(a.choose 2 : ℝ)+(a : ℝ)*(b.choose 2 : ℝ)≤(a : ℝ)*b*N := by
    exact_mod_cast hRank
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hRankR
  have hAvoid : 2*((Avoiders F c).card : ℝ)+(a : ℝ)*b*((a : ℝ)+b+4)≤
      2*(a : ℝ)*b*N := by nlinarith only [hRankR]
  have hd := (actual_degree_from_omitter hlegal hbad hT hTc).trans (degreeBudget_mono N hTL)
  have hclosed := degreeBudget_closed N L (by omega : 2≤N) (by omega : L+1≤N)
  have hbudget : DegreeBudget N L+L.choose 2+2*L=L*N := by
    calc
      _=L*(N-2)+2*L := by rw [hclosed]
      _=L*((N-2)+2) := by ring
      _=L*N := by rw [Nat.sub_add_cancel (by omega : 2≤N)]
  have hRoot : (RootPart F c).card+L.choose 2+2*L≤L*N := by omega
  have hRootR : ((RootPart F c).card : ℝ)+(L.choose 2 : ℝ)+2*(L : ℝ)≤(L : ℝ)*N := by
    exact_mod_cast hRoot
  rw [Nat.cast_choose_two] at hRootR
  have hRootL : 2*((RootPart F c).card : ℝ)+(L : ℝ)*((L : ℝ)+3)≤2*(L : ℝ)*N := by
    nlinarith only [hRootR]
  have hmL : (m : ℝ)+1=(L : ℝ) := by
    exact_mod_cast (show m+1=L from Nat.sub_add_cancel (by omega : 1≤L))
  have hRootM : 2*((RootPart F c).card : ℝ)+((m : ℝ)+1)*((m : ℝ)+4)≤
      2*((m : ℝ)+1)*N := by
    rw [←hmL] at hRootL
    convert hRootL using 1 <;> ring
  have hpart : (F.card : ℝ)=(RootPart F c).card+(Avoiders F c).card := by
    exact_mod_cast (root_avoider_card_partition F c).symm
  have hpay := FixedSmallScalars82427.singleton_credit hN' ha hb hpart hRootM hAvoid
  simpa only [haeq] using hpay

#print axioms actual_fixed_singleton_credit
end
end JSP233.FixedAnchorSingleton82427
