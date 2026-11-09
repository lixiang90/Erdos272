module

public import Erdos272.Resources.N250262.Layer250262
public import Erdos272.Arithmetic.N291012.NearSparse291012
public import Erdos272.Global.RootQuadratic208
public import Erdos272.Retention.N250262.RecoveryCertificates250262
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.ResearchMethods3066
open StarCompletion APGeometry DenseDeletion40 NearAP36 SevenFamily208 SourceCertified208 SourceBridge208 IntrinsicTriples208
open CrossBandCredit208 CrossBandCredit208.System CleanupMachineSound208
open HarmonicAbel29
open ActualUnitRecipe208 UnitRecipeStatic208 CleanupRows250262 RowStatic291012
open RootQuadratic208 Layer250262 Recovery208 RecoveryCaps213 RecoveryParameters291012 RecoveryCertificates250262
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem actual_upper {N k ell : ℕ} {psi : ℕ → ℝ} {A : Finset (Finset ℤ)} (hk : k < 28)
    (hlo : (data k).row.low ≤ N) (hhi : N ≤ (data k).row.high)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (data k).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hpot : psi (ell+1) = ((data k).potential : ℝ)) :
    ((PoolNear A psi ell).card : ℝ) ≤ Upper N k := by
  have hp := RowGeometry250262.parameters hk
  have hf : Facts k := CleanupFacts250262.all_facts hk
  let p := recipe hk hhi hlegal hpot hf
  obtain ⟨s, hsN, hsD, hsM, hse, hsF, hmap, hv⟩ :=
    ActualUnitCut291012.actual_system p hp.member_two hp.defect_two hp.defect_lt
      hlegal hbad hsize hsparse
  let hlen : (toRow (data k).row).bands.length = 7 := by
    simpa only [toRow, List.length_map] using hp.length
  have hmatch : ∀ d ∈ Finset.Icc 1 s.D, ∀ b : Band,
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).T = s.T d b ∧
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).E = s.E d b ∧
      (ActualCleanupEval208.At (toRow (data k).row) hlen b).U = s.U d b ∧
      CleanupEval208.block (ActualCleanupEval208.At (toRow (data k).row) hlen b) d = s.B d b := by
    intro d _hd b
    rw [←ActualUnitLayer208.evalData_at hp.length b]
    exact ⟨(hmap d b).1.symm, (hmap d b).2.1.symm, (hmap d b).2.2.1.symm, (hmap d b).2.2.2.symm⟩
  have hDn : s.D ≤ (data k).steps := by
    rw [hsD, hp.steps]
    exact Nat.div_le_div_right hhi
  have hb := ActualCleanupEval208.actual_family_bound hv (toRow (data k).row) hlen hf hDn hmatch
    (by change 0 < (data k).row.grid; rw [hp.grid]; decide) hp.low_pos
    (by simpa only [hsN, toRow] using hlo) (by simpa only [hsN, toRow] using hhi)
    (by change s.e ≤ (data k).row.i; exact hse.le)
  have hr := mul_le_mul_of_nonneg_left (ResidualRows250262.bound hk) (sq_nonneg (N : ℝ))
  have hbill : ((PoolNear A psi ell).card : ℝ) ≤ Upper N k := by
    simp only [hsN, hsM, hse, hsF, toRow, toTotals, hp.grid, Nat.cast_ofNat] at hb
    dsimp only [Upper]
    nlinarith only [hb, hr]
  exact hbill

#print axioms actual_upper

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 220000 ≤ N) (hhi : N ≤ 250261) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 594 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn : (220000 : ℝ) ≤ N := by exact_mod_cast hN
  have hnr : (N : ℝ) ≤ 250261 := by exact_mod_cast hhi
  have hTF := (Finset.mem_filter.mp hT).1
  have hcT := (Finset.mem_filter.mp hT).2
  have ht := hsparse T hTF
  have hts : T.card+1 ≤ N := by omega
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hH : Harmonic N ≤ 14 := caps.harmonic_le.trans (by norm_num [HCap, LogCap])
  have hhr : Harmonic N/(N : ℝ) ≤ (14/220000 : ℝ) := calc
    _ ≤ 14/(N : ℝ) := div_le_div_of_nonneg_right hH hNp.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 14) (by norm_num) hn
  have hsub : Avoiders G c ⊆ G := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (Avoiders G c) :=
    ⟨fun S hS => hF.1 S (hsub hS), fun S hS U hU he => hF.2 S (hsub hS) U (hsub hU) he⟩
  have hmax : ∀ S ∈ Avoiders G c, S.card < 21000 := by
    intro S hS
    have hh := hsparse S (hsub hS)
    omega
  have hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) := by
    by_cases h256 : 256*T.card ≤ N
    · have hr := actual_normalized_root (by omega : 2 ≤ N) hF hbad hTF hcT hts
        (z := (1/256 : ℝ)) (by
          apply (div_le_iff₀ hNp).mpr
          have hh : 256*(T.card : ℝ) ≤ N := by exact_mod_cast h256
          linarith only [hh]) (by norm_num)
      have ha := NearSparse291012.actual_family_normalized (K := 198) (J := 6) hlegal
        (by decide) (by omega : 0 < N) (by intro S hS; have hh := hmax S hS; norm_num; omega)
        (fun S hS => hbad S (hsub hS)) (by intro S hS; have hh := hmin S hS; omega)
      norm_num at hr ha
      have hp := actual_partition_payment hr ha
      norm_num [Q] at hp
      simp only [mul_div_assoc] at hp
      nlinarith only [hp, hnr, hhr]
    by_cases h32 : 32*T.card ≤ N
    · have hr := actual_normalized_root (by omega : 2 ≤ N) hF hbad hTF hcT hts
        (z := (1/32 : ℝ)) (by
          apply (div_le_iff₀ hNp).mpr
          have hh : 32*(T.card : ℝ) ≤ N := by exact_mod_cast h32
          linarith only [hh]) (by norm_num)
      have ha := NearSparse291012.actual_family_normalized (K := 286) (J := 5) hlegal
        (by decide) (by omega : 0 < N) (by intro S hS; have hh := hmax S hS; norm_num; omega)
        (fun S hS => hbad S (hsub hS)) (by intro S hS; have hh := hmin S hS; omega)
      norm_num at hr ha
      have hp := actual_partition_payment hr ha
      norm_num [Q] at hp
      simp only [mul_div_assoc] at hp
      nlinarith only [hp, hnr, hhr]
    · have hr := actual_normalized_root (by omega : 2 ≤ N) hF hbad hTF hcT hts
        (z := (1/12 : ℝ)) (by
          apply (div_le_iff₀ hNp).mpr
          have hh : 12*(T.card : ℝ) ≤ N := by exact_mod_cast ht
          linarith only [hh]) (by norm_num)
      have ha := NearSparse291012.actual_family_normalized (K := 2291) (J := 2) hlegal
        (by decide) (by omega : 0 < N) (by intro S hS; have hh := hmax S hS; norm_num; omega)
        (fun S hS => hbad S (hsub hS)) (by intro S hS; have hh := hmin S hS; omega)
      norm_num at hr ha
      have hp := actual_partition_payment hr ha
      norm_num [Q] at hp
      simp only [mul_div_assoc] at hp
      nlinarith only [hp, hnr, hhr]
  exact (div_le_iff₀ (sq_pos_of_pos hNp)).mp hwhole

#print axioms actual_high_root

theorem coarse_left_4 : StageCertificate 224211 CoarseA GlobalB HCap 2168 (1/4 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_4

theorem coarse_left_5 : StageCertificate 224211 CoarseA (LocalB 4) HCap 2168 (1/5 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_5

theorem coarse_left_6 : StageCertificate 224211 CoarseA (LocalB 5) HCap 2168 (1/6 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_6

theorem coarse_left_7 : StageCertificate 224211 CoarseA (LocalB 6) HCap 2168 (1/7 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_7

theorem coarse_left_8 : StageCertificate 224211 CoarseA (LocalB 7) HCap 2168 (1/8 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_8

theorem coarse_left_9 : StageCertificate 224211 CoarseA (LocalB 8) HCap 2168 (1/9 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_9

theorem coarse_left_10 : StageCertificate 224211 CoarseA (LocalB 9) HCap 2168 (1/10 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_left_10

theorem coarse_width : StageCertificate 224211 CoarseA (LocalB 10) HCap 2168 (1/10 : ℝ) (1/6 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms coarse_width

theorem strong_left_11 : StageCertificate 224211 StrongA (LocalB 10) HCap 872 (1/11 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_11

theorem strong_left_12 : StageCertificate 224211 StrongA (LocalB 11) HCap 872 (1/12 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_12

theorem strong_left_13 : StageCertificate 224211 StrongA (LocalB 12) HCap 872 (1/13 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_13

theorem strong_left_14 : StageCertificate 224211 StrongA (LocalB 13) HCap 872 (1/14 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_14

theorem strong_left_15 : StageCertificate 224211 StrongA (LocalB 14) HCap 872 (1/15 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_15

theorem strong_left_16 : StageCertificate 224211 StrongA (LocalB 15) HCap 872 (1/16 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_16

theorem strong_left_17 : StageCertificate 224211 StrongA (LocalB 16) HCap 872 (1/17 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_left_17

theorem strong_width : StageCertificate 224211 StrongA (LocalB 17) HCap 872 (1/17 : ℝ) (2/21 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms strong_width

theorem fine_left_18 : StageCertificate 224211 FineA (LocalB 17) FineW250262 FineC250262 (1/18 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_18

theorem fine_left_19 : StageCertificate 224211 FineA (LocalB 18) FineW250262 FineC250262 (1/19 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_19

theorem fine_left_20 : StageCertificate 224211 FineA (LocalB 19) FineW250262 FineC250262 (1/20 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_20

theorem fine_left_21 : StageCertificate 224211 FineA (LocalB 20) FineW250262 FineC250262 (1/21 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_21

theorem fine_left_22 : StageCertificate 224211 FineA (LocalB 21) FineW250262 FineC250262 (1/22 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_22

theorem fine_left_23 : StageCertificate 224211 FineA (LocalB 22) FineW250262 FineC250262 (1/23 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_23

theorem fine_left_24 : StageCertificate 224211 FineA (LocalB 23) FineW250262 FineC250262 (1/24 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_24

theorem fine_left_25 : StageCertificate 224211 FineA (LocalB 24) FineW250262 FineC250262 (1/25 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_25

theorem fine_left_26 : StageCertificate 224211 FineA (LocalB 25) FineW250262 FineC250262 (1/26 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_26

theorem fine_left_27 : StageCertificate 224211 FineA (LocalB 26) FineW250262 FineC250262 (1/27 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_27

theorem fine_left_28 : StageCertificate 224211 FineA (LocalB 27) FineW250262 FineC250262 (1/28 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_28

theorem fine_left_29 : StageCertificate 224211 FineA (LocalB 28) FineW250262 FineC250262 (1/29 : ℝ) 1 := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_left_29

theorem fine_width : StageCertificate 224211 FineA (LocalB 29) FineW250262 FineC250262 (1/29 : ℝ) (1/17 : ℝ) := by
  norm_num [StageCertificate, LeftCentre, WidthCentre, ShiftEnergy, CoarseA, StrongA,
    FineA, FineW250262, FineC250262, GlobalB, LocalB, HCap, LogCap]
#print axioms fine_width

end
end JSP233.ResearchMethods3066
