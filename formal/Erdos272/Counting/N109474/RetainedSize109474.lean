module

public import Erdos272.Resources.N291012.RetainedStart291012

@[expose] public section
namespace JSP233.InitialPreparation109474
open StarCompletion DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false

theorem retained_near {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 15853 ≤ N) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    (N : ℝ)^2/2 ≤ (Retained N 12 F).card+146*(N : ℝ) := by
  have hd := RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := actual_deletion_card_identity N 12 F
  have hdR : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by exact_mod_cast hd
  have hpR : ((Retained N 12 F).card : ℝ)+(Deleted N 12 F).card = F.card := by exact_mod_cast hp
  have hn : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by unfold B at hcard; omega)
  rw [Nat.cast_choose_two] at hn
  have hnr : (15853 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hdR, hpR, hn, hnr]

theorem actual_retained_above_cross_gap {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 15853 ≤ N) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    17*(N : ℝ)^2/36 < (Retained N 12 F).card := by
  have hb := retained_near hN hF hcard
  have hn : (15853 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := mul_pos (show (0 : ℝ) < (N : ℝ)-5256 by linarith only [hn])
    (show (0 : ℝ) < N by linarith only [hn])
  nlinarith only [hb, hp]

theorem actual_retained_card_two {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 15853≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(Retained N 12 F).card := by
  have hb := actual_retained_above_cross_gap hN hF hcard
  have hn : (2 : ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  by_contra hh
  have hc : ((Retained N 12 F).card : ℝ)≤1 := by
    exact_mod_cast (by omega : (Retained N 12 F).card≤1)
  have hp := mul_nonneg (show (0 : ℝ)≤(N : ℝ)-2 by linarith only [hn])
    (show (0 : ℝ)≤(N : ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

#print axioms actual_retained_above_cross_gap
end
end JSP233.InitialPreparation109474
