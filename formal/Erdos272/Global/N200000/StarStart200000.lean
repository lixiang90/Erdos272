module

public import Erdos272.Global.N233811.StarStart233811
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace JSP233.StarStart200000
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29 DenseDeletion40
open LowSteps32 APGeometry RecoveryCaps213 StarStart233811
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem actual_small_kernel_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 200000 ≤ N) (hhi : N ≤ 642498) (hc : c ∈ Ground N) (hF : Legal (Ground N) F)
    (htwo : 2 ≤ (Avoiders F c).card) (hkernel : (CommonKernel (Ground N) F c).card ≤ 1)
    (hcount : (Avoiders F c).card ≤ 144*N+1296) : F.card ≤ B N := by
  by_contra hn
  have hcounter : N.choose 2+1 ≤ F.card := by unfold B at hn; omega
  have hlow := StarWindow212.actual_AP_lower (by omega : 65536 ≤ N) hc hF htwo hkernel hcounter
  let A := APLarge (RootPart F c)
  have hground : ∀ S ∈ A, S ⊆ Ground N := fun S hS =>
    hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hAP : ∀ S ∈ A, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀ S ∈ A, 4 ≤ S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have htotal := StarStart233811.actual_AP_total N c A hground hAP hroot hlarge hc
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hh : Harmonic (N-1) ≤ 14 := (harmonic_mono (Nat.sub_le N 1)).trans
    (caps.harmonic_le.trans (by norm_num [HCap, LogCap]))
  have hHpay := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) by positivity)
  have hb := StarStart233811.actual_budget_with_low_surpluses hc hF
  have hcountR : ((Avoiders F c).card : ℝ) ≤ 144*((N-1 : ℕ) : ℝ)+1440 := by
    have hx : ((Avoiders F c).card : ℝ) ≤ 144*(N : ℝ)+1296 := by exact_mod_cast hcount
    have he : (N : ℝ) = ((N-1 : ℕ) : ℝ)+1 := by exact_mod_cast (show N = N-1+1 by omega)
    linarith only [hx, he]
  have hkR : ((CommonKernel (Ground N) F c).card : ℝ) ≤ 1 := by exact_mod_cast hkernel
  have hcounterR : ((N-1).choose 2 : ℝ)+((N-1 : ℕ) : ℝ)+1 ≤ F.card := by
    have hid := StarBudget30.small_budget_identity N (by omega : 1 ≤ N)
    have hx : (N.choose 2 : ℝ)+1 ≤ F.card := by exact_mod_cast hcounter
    have hi : (N.choose 2 : ℝ)+1 = (N : ℝ)+((N-1).choose 2 : ℝ) := by exact_mod_cast hid.symm
    have he : (N : ℝ) = ((N-1 : ℕ) : ℝ)+1 := by exact_mod_cast (show N = N-1+1 by omega)
    linarith only [hx, hi, he]
  have hnR : (199999 : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by exact_mod_cast (show 199999 ≤ N-1 by omega)
  have hp := mul_nonneg (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ)-199999 by linarith only [hnR])
    (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ) by positivity)
  change (((N-1 : ℕ) : ℝ)^2/18)-(7/2 : ℝ)*((N-1 : ℕ) : ℝ)-2*(Avoiders F c).card+1 ≤ A.card at hlow
  change (F.card : ℝ)+((∑ d ∈ LowActiveSeven c A,
    ((StepClass A (trueStep c) (d : ℤ)).card : ℝ))-7000000)/21 ≤ _ at hb
  nlinarith only [hlow, htotal, hHpay, hb, hcountR, hkR, hcounterR, hp, hnR]

theorem actual_retained_star_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 200000≤N) (hhi : N≤642498)
    (hc : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : Rooted (Retained N 12 F) c) : F.card≤B N := by
  have hsub : Avoiders F c⊆Deleted N 12 F := by
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    by_contra hnd
    exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF,hnd⟩))
  have hbad : ∀S∈Avoiders F c,¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp (hsub hS)).2.1
  have hdel := RootModel291012.deleted_affine (by omega : 15853≤N) hF
  have hcount : (Avoiders F c).card≤144*N+1296 := (Finset.card_le_card hsub).trans hdel
  by_cases htwo : 2≤(Avoiders F c).card
  · by_cases hk : 2≤(CommonKernel (Ground N) F c).card
    · have hb := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc hF htwo hk hbad
      omega
    · exact actual_small_kernel_window hN hhi hc hF htwo (by omega) hcount
  · apply AnchorCompletion38.actual_crooked_omitter_middle_window N F c (by omega) hc hF hbad
    omega



#print axioms actual_small_kernel_window
#print axioms actual_retained_star_window
end
end JSP233.StarStart200000
