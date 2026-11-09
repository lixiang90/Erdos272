module

public import Erdos272.Arithmetic.RecoveryCaps213
public import Erdos272.Arithmetic.SimplexMoment57
public import Erdos272.Counting.NonIntervalAP47
public import Erdos272.Counting.OneSided47

@[expose] public section

namespace JSP233.CrossGap200000
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 WitnessInterval43
open RestrictedWitness44 ResiduePool46 NonIntervalAP47 Straddling47 OneSided47
open RootedIntervals46 RecoveryCaps213 HarmonicLog55
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exception_cap {N : ℕ} {c : ℤ} (hN : 200000 ≤ N) (hhi : N ≤ 642498)
    (hc : c ∈ Ground N) : (WitnessException (Ground N) c : ℝ) ≤ 1700*N := by
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hell : Real.log (N : ℝ) ≤ 14 := caps.log_le.trans (by norm_num [LogCap])
  have hh : Harmonic N ≤ 14 := caps.harmonic_le.trans (by norm_num [HCap, LogCap])
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have h := SimplexMoment57.actual_simplex_exception hc
  have hp : SimplexPolynomial (Real.log N) (Harmonic N) ≤ SimplexPolynomial 14 14 := by
    dsimp only [SimplexPolynomial]
    gcongr
  have hpay := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) N)
  norm_num [SimplexPolynomial] at hpay
  dsimp only [SimplexPolynomial] at h
  nlinarith only [h, hpay, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem sparse_rooted {N : ℕ} {F : Finset (Finset ℤ)} {c a k : ℤ} {P : Finset ℤ}
    (hN : 200000 ≤ N) (hhi : N ≤ 642498) (hcN : c ∈ Ground N)
    (hF : Legal (Ground N) F) (hP : P ∈ F) (hcP : c ∉ P)
    (hc : ∀ S ∈ F, ¬IsAP S → c ∈ S) (hk : 3 ≤ k) (hAP : APAt k a P) :
    ((PrivatePairExistence.CrookedMembers F).card : ℝ)+(RootedIntervals F c).card ≤
      5*(N : ℝ)^2/18+1705*N := by
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
  have hw := exception_cap hN hhi hcN
  nlinarith only [hr, hp, hb, hw]

theorem large_step {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c a k : ℤ} (hN : 200000≤N) (hhi : N≤642498) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hc : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→(∃ x∈S,x<c) ∧ ∃ y∈S,c<y)
    (hP : P∈F) (hcP : c∉P) (hk : 3≤k) (hAP : APAt k a P) :
    (F.card:ℝ)≤4*(N:ℝ)^2/9+(N:ℝ)*HarmonicAbel29.Harmonic N+1706*N := by
  have hroot : ∀ S∈F,IsInterval S→c∈S := by
    intro S hS hI
    by_contra hn
    exact hn (actual_interval_straddled_root hI (hcross S hS hn))
  have hp : ((PrivatePairExistence.CrookedMembers F).card:ℝ)+
      (RootedIntervals46.RootedIntervals F c).card+
      (F.filter (fun S=>IsAP S ∧ ¬IsInterval S)).card=F.card := by
    exact_mod_cast actual_family_three_part hroot
  have hCE := sparse_rooted hN hhi hcN hF hP hcP hc hk hAP
  have hA := actual_noninterval_part_count hF
  linarith only [hp,hCE,hA]

theorem two_step {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 200000≤N) (hhi : N≤642498) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S→c∈S)
    (hcross : ∀ S∈F,c∉S→StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) (hout : ∃ P∈F,c∉P) :
    (F.card:ℝ)≤7*(N:ℝ)^2/16+1703*N+1 := by
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
    have hparity : ResidueRoot47.Outside (Ground N) c 2 = OppositeParity N c := by
      ext x
      simp only [ResidueRoot47.Outside, OppositeParity, Finset.mem_filter, Nat.cast_ofNat]
    rw [hparity]
    exact actual_opposite_parity_pool N c
  have hw := exception_cap hN hhi hcN
  have hR : (R.card : ℝ) ≤ 3*(N : ℝ)^2/8+(5/2 : ℝ)*N+1700*N := by
    linarith only [hrR, hp, hw]
  have hpart : (R.card:ℝ)+(Avoiders F c).card=F.card := by
    exact_mod_cast root_avoider_card_partition F c
  linarith only [hR,hO,hpart]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 200000 ≤ N) (hhi : N ≤ 642498) (hc : c ∈ Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hcross : ∀ S ∈ F, c ∉ S → StraddlesRoot c S) (hout : ∃ P ∈ F, c ∉ P) :
    (F.card : ℝ) ≤ 17*(N : ℝ)^2/36 := by
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hh : Harmonic N ≤ 14 := caps.harmonic_le.trans (by norm_num [HCap, LogCap])
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P, hP, hcP, d, hd, a, hAP⟩ := hlarge
    have hb := large_step hN hhi hc hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
    have hp := mul_le_mul_of_nonneg_left hh hn0
    have hg := mul_nonneg (show (0 : ℝ) ≤ (N : ℝ)/36-1720 by linarith only [hn]) hn0
    nlinarith only [hb, hp, hg]
  · have hb := two_step hN hhi hc hF hroot hcross hlarge hout
    have hg := mul_nonneg (show (0 : ℝ) ≤ (5/144 : ℝ)*N-1704 by linarith only [hn]) hn0
    nlinarith only [hb, hg, hn]

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 200000≤N) (hhigh : N≤642498) (hc : c∈Ground N)
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
    have hb := actual_all_cross_root_gap hN hhigh hc hF hroot hcross hout
    linarith only [hb,hnear]

#print axioms exception_cap
#print axioms sparse_rooted
#print axioms large_step
#print axioms two_step
#print axioms actual_all_cross_root_gap
#print axioms actual_near_one_sided_reduction
end
end JSP233.CrossGap200000
