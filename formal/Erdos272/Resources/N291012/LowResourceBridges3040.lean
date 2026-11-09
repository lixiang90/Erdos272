module

public import Erdos272.Global.N291012.WindowPayment291012
public import Erdos272.Arithmetic.PrimorialRatio39
public import Erdos272.Arithmetic.RecoveryCaps213
public import Erdos272.Arithmetic.PrefixTableA131
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.LowResourceBridges3040
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
open PrimorialRatio39 WindowData291012 SourceFloorSound291012 PureSource208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem primorial_seven : Primorial 7 = 510510 := by
  norm_num [Primorial, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime]

theorem ratio_six : Ratio 6 = (1001/192 : ℝ) := by
  norm_num [Ratio, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime]

theorem finite_totient_ratio {N m : ℕ} (hN : N < 510510) (hm : m ≤ N) :
    192*m ≤ 1001*Nat.totient m := by
  have hcut : N < Primorial (6+1) := by
    change N < Primorial 7
    rw [primorial_seven]
    exact hN
  have hr := (uniform_omega_and_ratio N 6 hcut).2 m hm
  rw [ratio_six] at hr
  have hn : 192*(m : ℝ) ≤ 1001*Nat.totient m := by nlinarith only [hr]
  exact_mod_cast hn

theorem local_caps {N : ℕ} (hN : 100000 ≤ N) (hhi : N ≤ 291011) :
    RecoveryCaps213.Caps (63/5) (5271/400) N := by
  have hl := PrefixLog131.log_endpoint_upper (by decide : 0 < PrefixTable131.grid)
    PrefixTable131.state_494 (by decide : 0 < 494) (by omega : 0 < N) hhi
  norm_num [PrefixTable131.grid] at hl
  have hlog : Real.log (N : ℝ) ≤ (63/5 : ℝ) := by linarith only [hl]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  exact ⟨hlog, by nlinarith only [hlog, hh]⟩

theorem ground_mono {N ambient : ℕ} (hN : N ≤ ambient) : Ground N ⊆ Ground ambient := by
  intro z hz
  have h := (mem_ground N z).mp hz
  exact (mem_ground ambient z).mpr ⟨h.1, h.2.trans (by exact_mod_cast hN)⟩

theorem legal_ambient {N ambient : ℕ} {F : Finset (Finset ℤ)}
    (hN : N ≤ ambient) (hF : Legal (Ground N) F) : Legal (Ground ambient) F :=
  ⟨fun S hS => (hF.1 S hS).trans (ground_mono hN), hF.2⟩

theorem source_below_window {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w < 13) (hN : N ≤ (info w).low) (hF : Legal (Ground N) F)
    (hAF : A ⊆ F) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ F, ((IntrinsicTriples208.Pool S).card : ℝ))+(info w).fee := by
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hF.1 S (hAF hS),
      fun S hS T hT hST => hF.2 S (hAF hS) T (hAF hT) hST⟩
  exact WindowPayment291012.actual_source hw le_rfl (gates hw).low_high
    (legal_ambient hN hA) hbad hsize (fun S hS => (hsparse S hS).trans hN) hAF

theorem physical_defect_mono {s a b : ℕ} (hab : a ≤ b) : physicalK s a ≤ physicalK s b := by
  unfold physicalK
  apply Finset.sum_le_sum_of_subset
  intro q hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hq
  exact Finset.mem_Ico.mpr ⟨by omega, hhi⟩

theorem floor_weaken_defect {T U a b target smaller : ℕ}
    (hT : T ≤ U) (he : a ≤ b) (hb : smaller ≤ target) (hf : Floor T a target) :
    Floor U b smaller := by
  intro s hs hbig
  exact hb.trans ((hf s (hT.trans hs) hbig).trans (physical_defect_mono he))

#print axioms primorial_seven
#print axioms ratio_six
#print axioms finite_totient_ratio
#print axioms local_caps
#print axioms ground_mono
#print axioms legal_ambient
#print axioms source_below_window
#print axioms physical_defect_mono
#print axioms floor_weaken_defect
end
end JSP233.LowResourceBridges3040
