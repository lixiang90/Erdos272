module

public import Erdos272.Resources.StarWindow212
public import Erdos272.Arithmetic.RecoveryCaps213
public import Erdos272.Resources.N291012.RootModel291012
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace JSP233.StarStart243614
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29 DenseDeletion40
open LowSteps32 APGeometry RecoveryCaps213
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem reciprocal_square_tail (n : ℕ) :
    (∑ d∈Finset.Icc 8 n, (1:ℝ)/(d:ℝ)^2)≤1/7 := by
  by_cases hn : 7≤n
  · have hs : (∑ d∈Finset.Icc 8 n, (1:ℝ)/(d:ℝ)^2)≤1/7-1/(n:ℝ) := by
      induction n,hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hh := reciprocal_square_step n (by omega)
        push_cast
        linarith
    have hp : (0:ℝ)≤1/(n:ℝ) := by positivity
    linarith
  · have he : Finset.Icc 8 n=∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he]
    norm_num

theorem finite_class_total (n : ℕ) (J : Finset ℕ) (a : ℕ→ℝ) (active : ℕ→Prop)
    (L R : ℝ) (hL : 0≤L) (hR : 0≤R) (hJ : J⊆Finset.Icc 1 n)
    (hcount : ∀ d∈J, a d≤(if active d then L*R/(d:ℝ)^2 else 0)+2*(n:ℝ)/(d:ℝ)+1) :
    (∑ d∈J, a d)≤(∑ d∈J.filter (fun d => active d ∧ d≤7), a d)
      +L*R/7+2*(n:ℝ)*Harmonic n+n := by
  let low := J.filter (fun d => active d ∧ d≤7)
  let rest := J\low
  let B := rest.filter active
  have hrJ : rest⊆Finset.Icc 1 n := (Finset.sdiff_subset).trans hJ
  have hB : B⊆Finset.Icc 8 n := by
    intro d hd
    obtain ⟨hdr,hact⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdJ,hdlow⟩ := Finset.mem_sdiff.mp hdr
    obtain ⟨hd1,hdn⟩ := Finset.mem_Icc.mp (hJ hdJ)
    have hd5 : ¬d≤7 := by
      intro hh
      exact hdlow (Finset.mem_filter.mpr ⟨hdJ,hact,hh⟩)
    exact Finset.mem_Icc.mpr ⟨by omega,hdn⟩
  have htail : (∑ d∈B, (1:ℝ)/(d:ℝ)^2)≤1/7 := by
    calc
      _≤∑ d∈Finset.Icc 8 n, (1:ℝ)/(d:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hB (by intro d hd hn; positivity)
      _≤1/7 := reciprocal_square_tail n
  have hprod : (∑ d∈rest, if active d then L*R/(d:ℝ)^2 else 0)≤L*R/7 := by
    rw [←Finset.sum_filter]
    change (∑ d∈B, L*R/(d:ℝ)^2)≤L*R/7
    have he (d : ℕ) : L*R/(d:ℝ)^2=L*R*((1:ℝ)/(d:ℝ)^2) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    simpa only [one_div,div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left htail (mul_nonneg hL hR)
  have hhar : (∑ d∈rest, (1:ℝ)/(d:ℝ))≤Harmonic n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hrJ (by intro d hd hn; positivity)
  have hlin : (∑ d∈rest, 2*(n:ℝ)/(d:ℝ))≤2*(n:ℝ)*Harmonic n := by
    have he (d : ℕ) : 2*(n:ℝ)/(d:ℝ)=2*(n:ℝ)*((1:ℝ)/(d:ℝ)) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hhar (by positivity)
  have hcard : (rest.card:ℝ)≤n := by
    have hh := Finset.card_le_card hrJ
    have hI : (Finset.Icc 1 n).card=n := by simp
    rw [hI] at hh
    exact_mod_cast hh
  have hrest := Finset.sum_le_sum (s:=rest) (fun d hd => hcount d (Finset.mem_sdiff.mp hd).1)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hrest
  have hpart := Finset.sum_sdiff (f:=a) (Finset.filter_subset (fun d => active d ∧ d≤7) J)
  change (∑ d∈rest,a d)+(∑ d∈low,a d)=∑ d∈J,a d at hpart
  change (∑ d∈J,a d)≤(∑ d∈low,a d)+L*R/7+2*(n:ℝ)*Harmonic n+n
  linarith

def LowActiveSeven (c : ℤ) (F : Finset (Finset ℤ)) : Finset ℕ :=
  (NatLabels c F).filter (fun d => (d : ℤ) ∈ APActiveSteps c F ∧ d ≤ 7)

theorem actual_AP_total (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) (hc : c∈Ground N) :
    (F.card:ℝ)≤(∑ d∈LowActiveSeven c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(((N-1:ℕ):ℝ)^2/28)+2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
  have hcI : 1≤c ∧ c≤(N:ℤ) := by
    rw [StarBoundConcrete30.ground_eq_Icc] at hc
    exact Finset.mem_Icc.mp hc
  have hl : (leftCapacity c:ℤ)=c-1 := Int.toNat_of_nonneg (by omega)
  have hr : (rightCapacity N c:ℤ)=(N:ℤ)-c := Int.toNat_of_nonneg (by omega)
  have hcap : leftCapacity c+rightCapacity N c=N-1 := by omega
  have hcapR : (leftCapacity c:ℝ)+(rightCapacity N c:ℝ)=((N-1:ℕ):ℝ) := by exact_mod_cast hcap
  have hJ := nat_labels_bound N c F hground hAP hroot hlarge
  have hh := finite_class_total (N-1) (NatLabels c F)
    (fun d => ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
    (fun d => (d:ℤ)∈APActiveSteps c F) (leftCapacity c:ℝ) (rightCapacity N c:ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ (by
      intro d hd
      have hdpos : 0<d := by have := (Finset.mem_Icc.mp (hJ hd)).1; omega
      have hb := actual_class_count N c F hground hAP hroot hlarge hc d hdpos
      rw [hcapR] at hb
      by_cases ha : (d:ℤ)∈APActiveSteps c F
      · simpa only [if_pos ha] using hb
      · simpa only [if_neg ha] using hb)
  rw [sum_nat_class_card c F hAP hroot] at hh
  have hp : (leftCapacity c:ℝ)*(rightCapacity N c:ℝ)≤((N-1:ℕ):ℝ)^2/4 := by
    nlinarith [sq_nonneg ((leftCapacity c:ℝ)-(rightCapacity N c:ℝ))]
  have hh' : (F.card:ℝ)≤(∑ d∈LowActiveSeven c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(leftCapacity c:ℝ)*(rightCapacity N c:ℝ)/7
      +2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
    convert hh using 1
    congr 4
    ext d
    simp only [LowActiveSeven,Finset.mem_filter]
  linarith

theorem actual_budget_with_low_surpluses {N : ℕ} {c : ℤ}
    {F : Finset (Finset ℤ)} (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    (F.card:ℝ)+((∑d∈LowActiveSeven c (APLarge (RootPart F c)),
      ((StepClass (APLarge (RootPart F c)) (trueStep c) (d:ℤ)).card:ℝ))-7000000)/21≤
        (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
          ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 := by
  let A := APLarge (RootPart F c)
  let L := LowActiveSeven c A
  let P : Finset ℕ := L.filter (fun d:ℕ=>1000000<(StepClass A (trueStep c) (d:ℤ)).card)
  let D := P.image (fun d:ℕ=>(d:ℤ))
  have hAP : ∀S∈A,IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hroot : Rooted A c := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hlarge : ∀S∈A,4≤S.card := fun S hS => (Finset.mem_filter.mp hS).2.2
  have hground : ∀S∈A,S⊆Ground N := fun S hS =>
    hF.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hD : D⊆APActiveSteps c A := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1
  have hbig : ∀d∈D,1000000<(StepClass A (trueStep c) d).card := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp he).2
  have hb := StarWindow212.actual_budget_with_many_surpluses hc hF D hD hbig
  have hsumD : (∑d∈D,((StepClass A (trueStep c) d).card:ℝ))=
      ∑d∈P,((StepClass A (trueStep c) (d:ℤ)).card:ℝ) := by
    dsimp only [D]
    rw [Finset.sum_image]
    intro i _ j _ hij
    change (i:ℤ)=(j:ℤ) at hij
    exact_mod_cast hij
  have hsub : L⊆Finset.Icc 1 7 := by
    intro d hd
    have hdata := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (nat_labels_bound N c A hground hAP hroot hlarge hdata.1)).1,
       hdata.2.2⟩
  have hcard : L.card≤7 := by simpa using Finset.card_le_card hsub
  have hpoint : ∀d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ)≤
      (if 1000000<(StepClass A (trueStep c) (d:ℤ)).card then
        ((StepClass A (trueStep c) (d:ℤ)).card:ℝ) else 0)+1000000 := by
    intro d _
    split_ifs with hd
    · linarith
    · have hh : ((StepClass A (trueStep c) (d:ℤ)).card:ℝ)≤1000000 := by
        exact_mod_cast (show (StepClass A (trueStep c) (d:ℤ)).card≤1000000 by omega)
      linarith only [hh]
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul] at hs
  have hcR : (L.card:ℝ)≤7 := by exact_mod_cast hcard
  change (∑d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))≤
    (∑d∈P,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))+(L.card:ℝ)*1000000 at hs
  change (F.card:ℝ)+(∑d∈D,((StepClass A (trueStep c) d).card:ℝ))/21≤
      (Avoiders F c).card+(CommonKernel (Ground N) F c).card+
        ((N-1).choose 2:ℕ)+((N-1:ℕ):ℝ)/4 at hb
  rw [hsumD] at hb
  change (F.card:ℝ)+((∑d∈L,((StepClass A (trueStep c) (d:ℤ)).card:ℝ))-7000000)/21≤_
  linarith only [hs,hcR,hb]


theorem actual_small_kernel_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 243614 ≤ N) (hhi : N ≤ 642498) (hc : c ∈ Ground N) (hF : Legal (Ground N) F)
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
  have htotal := actual_AP_total N c A hground hAP hroot hlarge hc
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hh : Harmonic (N-1) ≤ 14 := (harmonic_mono (Nat.sub_le N 1)).trans
    (caps.harmonic_le.trans (by norm_num [HCap, LogCap]))
  have hHpay := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ 2*((N-1 : ℕ) : ℝ) by positivity)
  have hb := actual_budget_with_low_surpluses hc hF
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
  have hnR : (243613 : ℝ) ≤ ((N-1 : ℕ) : ℝ) := by exact_mod_cast (show 243613 ≤ N-1 by omega)
  have hp := mul_nonneg (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ)-243613 by linarith only [hnR])
    (show (0 : ℝ) ≤ ((N-1 : ℕ) : ℝ) by positivity)
  change (((N-1 : ℕ) : ℝ)^2/18)-(7/2 : ℝ)*((N-1 : ℕ) : ℝ)-2*(Avoiders F c).card+1 ≤ A.card at hlow
  change (F.card : ℝ)+((∑ d ∈ LowActiveSeven c A,
    ((StepClass A (trueStep c) (d : ℤ)).card : ℝ))-7000000)/21 ≤ _ at hb
  nlinarith only [hlow, htotal, hHpay, hb, hcountR, hkR, hcounterR, hp, hnR]

theorem actual_retained_star_window {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (hN : 243614≤N) (hhi : N≤642498)
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



#print axioms reciprocal_square_tail
#print axioms finite_class_total
#print axioms actual_AP_total
#print axioms actual_budget_with_low_surpluses
#print axioms actual_small_kernel_window
#print axioms actual_retained_star_window
end
end JSP233.StarStart243614
