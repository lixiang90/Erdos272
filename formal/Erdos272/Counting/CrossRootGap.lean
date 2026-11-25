module

public import Erdos272.Counting.NonIntervalAP47
public import Erdos272.Counting.OneSided47

@[expose] public section
namespace JSP233.CrossRootGap
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RestrictedWitness44 ResiduePool46 NonIntervalAP47 Straddling47 OneSided47 RootedIntervals46
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sparse_rooted {N : ℕ} {F : Finset (Finset ℤ)} {c a k : ℤ} {P : Finset ℤ}
    (hN : 6 ≤ N) {e : ℝ} (cap : (WitnessException (Ground N) c : ℝ) ≤ e*N) (hcN : c ∈ Ground N)
    (hF : Legal (Ground N) F) (hP : P ∈ F) (hcP : c ∉ P)
    (hc : ∀ S ∈ F, ¬IsAP S → c ∈ S) (hk : 3 ≤ k) (hAP : APAt k a P) :
    ((PrivatePairExistence.CrookedMembers F).card : ℝ)+(RootedIntervals F c).card ≤
      5*(N : ℝ)^2/18+(e+5)*N := by
  obtain ⟨u, v, hE, hj⟩ := actual_avoider_crooked_interval_budget c P hF hP hcP hc
  have hr : ((PrivatePairExistence.CrookedMembers F).card : ℝ)+(StraddledIntervals F c).card ≤
      (IntervalPool (Ground N) c u v P).card+(WitnessException (Ground N) c : ℝ) := by
    exact_mod_cast hj
  obtain ⟨hu, huc, hcv, hv⟩ := actual_supported_envelope_ground hcN hF hE
  obtain ⟨_hk, lo, hi, hm⟩ := hAP
  have hp := actual_interval_pool_sparse_residue (by omega : 6 ≤ N) hcN (hF.1 P hP)
    hcP hu huc hcv hv hk (fun x hx => ((hm x).mp hx).2.2)
  have hb : ((RootedIntervals F c).card : ℝ) ≤ (StraddledIntervals F c).card+2*N := by
    exact_mod_cast actual_legal_rooted_intervals_card_le N F c hF
  nlinarith only [hr, hp, hb, cap]

theorem large_step {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c a k : ℤ} (hN : 6 ≤ N) {e : ℝ} (cap : (WitnessException (Ground N) c : ℝ) ≤ e*N) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hc : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→(∃ x∈S,x<c) ∧ ∃ y∈S,c<y)
    (hP : P∈F) (hcP : c∉P) (hk : 3≤k) (hAP : APAt k a P) :
    (F.card:ℝ)≤4*(N:ℝ)^2/9+(N:ℝ)*HarmonicAbel29.Harmonic N+(e+6)*N := by
  have hroot : ∀ S∈F,IsInterval S→c∈S := by
    intro S hS hI
    by_contra hn
    exact hn (actual_interval_straddled_root hI (hcross S hS hn))
  have hp : ((PrivatePairExistence.CrookedMembers F).card:ℝ)+
      (RootedIntervals46.RootedIntervals F c).card+
      (F.filter (fun S=>IsAP S ∧ ¬IsInterval S)).card=F.card := by
    exact_mod_cast actual_family_three_part hroot
  have hCE := sparse_rooted hN cap hcN hF hP hcP hc hk hAP
  have hA := actual_noninterval_part_count hF
  nlinarith only [hp,hCE,hA]

theorem two_step {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 6 ≤ N) {e : ℝ} (cap : (WitnessException (Ground N) c : ℝ) ≤ e*N) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) (hout : ∃ P∈F,c∉P) :
    (F.card:ℝ)≤7*(N:ℝ)^2/16+(e+3)*N+1 := by
  obtain ⟨hdata,hO⟩ := actual_no_large_step_budget hF hroot hcross hno
  obtain ⟨P,hPF,hcP⟩ := hout
  have hPA : P∈Avoiders F c := Finset.mem_filter.mpr ⟨hPF,hcP⟩
  have hPP : P⊆OppositeParity N c := (hdata P hPA).2.2
  let R := RootPart F c
  have hRF : R⊆F := Finset.filter_subset _ _
  have hlegalR : Legal (Ground N) R :=
    ⟨fun S hS=>hF.1 S (hRF hS),fun S hS T hT hn=>hF.2 S (hRF hS) T (hRF hT) hn⟩
  have hrootR : Rooted R c := fun S hS=>(Finset.mem_filter.mp hS).2
  have hmet : ∀ S∈R,(S∩OppositeParity N c).Nonempty := by
    intro S hS
    have hcS := hrootR S hS
    have hSP : S≠P := by intro he; exact hcP (he ▸ hcS)
    obtain ⟨x,hx⟩ := isAP_nonempty (hF.2 S (hRF hS) P hPF hSP)
    obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
    exact ⟨x,Finset.mem_inter.mpr ⟨hxS,hPP hxP⟩⟩
  have hm : ∀ S ∈ R, (S ∩ ResidueRoot47.Outside (Ground N) c 2).Nonempty := by
    simpa only [ResidueRoot47.Outside, OppositeParity, Nat.cast_ofNat] using hmet
  have hr := ResidueRoot47.actual_rooted_residue_count hlegalR hrootR hm
  have hrR : (R.card : ℝ) ≤ (ResidueRoot47.MeetingPool (Ground N) c
      (ResidueRoot47.Outside (Ground N) c 2)).card+2*N+(WitnessException (Ground N) c : ℝ) := by
    exact_mod_cast hr
  have hp : ((ResidueRoot47.MeetingPool (Ground N) c (ResidueRoot47.Outside (Ground N) c 2)).card : ℝ) ≤
      3*(N : ℝ)^2/8+(N : ℝ)/2 := by
    have parity : ResidueRoot47.Outside (Ground N) c 2 = OppositeParity N c := by
      ext x
      simp only [ResidueRoot47.Outside, OppositeParity, Finset.mem_filter, Nat.cast_ofNat]
    rw [parity]
    exact actual_opposite_parity_pool N c
  have hR : (R.card : ℝ) ≤ 3*(N : ℝ)^2/8+(5/2 : ℝ)*N+e*N := by
    nlinarith only [hrR, hp, cap]
  have hpart : (R.card:ℝ)+(Avoiders F c).card=F.card := by
    exact_mod_cast root_avoider_card_partition F c
  nlinarith only [hR,hO,hpart]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 6 ≤ N) {e : ℝ} (cap : (WitnessException (Ground N) c : ℝ) ≤ e*N)
    (harm : Harmonic N ≤ 12) (stepGap : 36*(e+18) ≤ N) (parityGap : 144*(e+4) ≤ 5*N) (hc : c ∈ Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hcross : ∀ S ∈ F, c ∉ S → StraddlesRoot c S) (hout : ∃ P ∈ F, c ∉ P) :
    (F.card : ℝ) ≤ 17*(N : ℝ)^2/36 := by
  have hn : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P, hP, hcP, d, hd, a, hAP⟩ := hlarge
    have hb := large_step hN cap hc hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
    have hp := mul_le_mul_of_nonneg_left harm hn0
    have hg := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)/36-(e+18) by linarith only [stepGap]) hn0
    nlinarith only [hb, hp, hg]
  · have hb := two_step hN cap hc hF hroot hcross hlarge hout
    have hg := mul_nonneg (show (0 : ℝ) ≤ (5/144 : ℝ)*N-(e+4) by linarith only [parityGap]) hn0
    nlinarith only [hb, hg, hn]

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 6 ≤ N) {e : ℝ} (cap : (WitnessException (Ground N) c : ℝ) ≤ e*N)
    (harm : Harmonic N ≤ 12) (stepGap : 36*(e+18) ≤ N) (parityGap : 144*(e+4) ≤ 5*N) (hc : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hnear : 17*(N : ℝ)^2/36<F.card) :
    Rooted F c ∨ ∃P∈F,c∉P ∧ ((∀x∈P,x<c) ∨ ∀x∈P,c<x) := by
  by_cases hr : Rooted F c
  · exact Or.inl hr
  · apply Or.inr
    by_contra hn
    have hcross := actual_no_one_sided_cross hn
    have hout : ∃P∈F,c∉P := by
      change ¬∀P∈F,c∈P at hr
      push Not at hr
      exact hr
    have hb := actual_all_cross_root_gap hN cap harm stepGap parityGap hc hF hroot hcross hout
    linarith only [hb,hnear]

#print axioms actual_near_one_sided_reduction
end
end JSP233.CrossRootGap
