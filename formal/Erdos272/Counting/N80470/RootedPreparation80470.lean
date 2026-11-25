module

public import Erdos272.Counting.N80470.RootedShort80470
public import Erdos272.Resources.LocalRecovery208

@[expose] public section

namespace JSP233.RootedPreparation80470
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35
open PrivatePairExistence ActualPreparation208 ActualExterior208 LocalRecovery208
open EndpointFinite208 NoHighTerminalResource208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_preparation {N c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 19≤N) (hhigh : N≤853476)
    (hc : (c : ℤ)∈Ground N) (hG : Legal (Ground N) G)
    (hcL : c<L) (hLN : L≤N)
    (hroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S)
    (hP : P∈G) (hcP : (c : ℤ)∉P) (hLP : ∀ z∈P,(L : ℤ)≤z)
    (hsmall : ∀ S∈SmallAP G,(c : ℤ)∈S) :
    (G.card : ℝ)≤(PreparedCrooked G c L).card+(PreparedAP G c L).card+
      PreparationCost N L-(N : ℝ)/2+c := by
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hc1 : 1≤c := by omega
  have hL : 2≤L := by omega
  have hcLow : (c : ℤ)∈Ground (L-1) := by
    apply (mem_ground (L-1) (c : ℤ)).mpr
    omega
  have hp := actual_preparation_count (L:=(L : ℤ)) hG hroot
  have hpR : (G.card : ℝ)≤(PreparedCrooked G c L).card+(PreparedAP G c L).card+N+
      (CrookedMembers G\HighMembers G c L).card+(LowCut G c).card+
      (HighCut G c L).card+(SmallAP G).card := by exact_mod_cast hp
  have hs := RootedShort80470.actual_rooted_small_count hc
    (F:=SmallAP G) (fun S hS => hG.1 S (actual_small_AP_member hS).1)
    (fun S hS => (actual_small_AP_member hS).2.1)
    (fun S hS => (actual_small_AP_member hS).2.2) hsmall
  norm_num only [Int.cast_natCast] at hs
  have hNo : ((CrookedMembers G\HighMembers G c L).card : ℝ)≤
      (L : ℝ)*(Harmonic L+5) := by
    simpa only [NoHigh208.Failure] using
      actual_failure_five_local hG hroot hP hcP hLP hcLow
  have hLow := actual_low_cut48_25 hG (by omega : 2≤N) hhigh hc1 (show c≤N by omega)
  have hHigh := actual_high_cut48_25 (c:=c) hG hL (hLN.trans hhigh)
  dsimp only [PreparationCost]
  nlinarith only [hpR,hs,hNo,hLow,hHigh]

theorem actual_losses {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (x p : Finset ℤ→ℤ) (hN : 19≤N) (hhigh : N≤853476)
    (hc : (c : ℤ)∈Ground N) (hG : Legal (Ground N) G)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S)
    (hP : P∈G) (hcP : (c : ℤ)∉P) (hLP : ∀ z∈P,(L : ℤ)≤z)
    (houtside : ∀ S∈G,(c : ℤ)∉S→
      (∃ u∈S,u≤(L : ℤ))∧∃ v∈S,(R : ℤ)≤v)
    (hW : ∀ S∈PreparedCrooked G c L,
      IntrinsicPair c S {x S,p S} ∧ x S≤(R : ℤ) ∧ x S≠(L : ℤ) ∧
      ((c : ℤ)<x S→x S<(L : ℤ)→(R : ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S))))
    (hsmall : ∀ S∈SmallAP G,(c : ℤ)∈S) :
    (G.card : ℝ)≤(CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      ((R : ℝ)+(129/200)*L)*(N-R)+GeometryCost N L ((L : ℝ)+(N-R))-(N : ℝ)/2 := by
  have hp := actual_preparation hN hhigh hc hG hcL (hLR.trans hRN) hroot hP hcP hLP hsmall
  have hm := actual_prepared_middle_reduction_width x p hG hcL hLR hRN hP hLP hroot houtside hW
  have hLC : ((L-c : ℕ) : ℝ)=(L : ℝ)-c := by rw [Nat.cast_sub hcL.le]
  dsimp only [PreparationCost] at hp
  dsimp only [GeometryCost]
  nlinarith only [hp,hm,hLC]

#print axioms actual_preparation
#print axioms actual_losses
end
end JSP233.RootedPreparation80470
