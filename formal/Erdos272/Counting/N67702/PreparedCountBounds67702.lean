module

public import Erdos272.Counting.N67702.PreparedJoint67702

@[expose] public section

namespace JSP233.PreparationBounds67702
open StarCompletion APGeometry APPrepare49 PreparedWitness48 PreparedClasses50
open LongTerminal35 RestrictedWitness44 PrivatePairExistence ActualPreparation208
open HarmonicAbel29 EndpointFinite208 NoHighTerminalResource208 LocalRecovery208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem actual_preparation_custom {N c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ} {s : ℝ}
    (hN : 19≤N) (hhigh : N≤853476) (hc : (c : ℤ)∈Ground N)
    (hG : Legal (Ground N) G) (hcL : c<L) (hLN : L≤N)
    (hroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S)
    (hP : P∈G) (hcP : (c : ℤ)∉P) (hLP : ∀ z∈P,(L : ℤ)≤z)
    (hsmall : ((SmallAP G).card : ℝ)≤2*(N : ℝ)+s) :
    (G.card : ℝ)≤(PreparedCrooked G c L).card+(PreparedAP G c L).card+PreparationCost N L+s := by
  have hcN := (mem_ground N (c : ℤ)).mp hc
  have hc1 : 1≤c := by omega
  have hL : 2≤L := by omega
  have hcLow : (c : ℤ)∈Ground (L-1) := by apply (mem_ground (L-1) (c : ℤ)).mpr;omega
  have hp := actual_preparation_count (L:=(L : ℤ)) hG hroot
  have hpR : (G.card : ℝ)≤(PreparedCrooked G c L).card+(PreparedAP G c L).card+N+
      (CrookedMembers G\HighMembers G c L).card+(LowCut G c).card+(HighCut G c L).card+(SmallAP G).card := by exact_mod_cast hp
  have hNo : ((CrookedMembers G\HighMembers G c L).card : ℝ)≤(L : ℝ)*(Harmonic L+5) := by
    simpa only [NoHigh208.Failure] using actual_failure_five_local hG hroot hP hcP hLP hcLow
  have hLow := actual_low_cut48_25 hG (by omega : 2≤N) hhigh hc1 (show c≤N by omega)
  have hHigh := actual_high_cut48_25 (c:=c) hG hL (hLN.trans hhigh)
  dsimp only [PreparationCost]
  nlinarith only [hpR,hsmall,hNo,hLow,hHigh]

theorem actual_middle_custom {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (x p : Finset ℤ→ℤ) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hP : P∈G) (hLP : ∀ z∈P,(L : ℤ)≤z)
    (hroot : ∀ S∈G,¬IsAP S→(c : ℤ)∈S)
    (houtside : ∀ S∈G,(c : ℤ)∉S→(∃u∈S,u≤(L : ℤ))∧∃v∈S,(R : ℤ)≤v)
    (hW : ∀ S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S}∧x S≤(R : ℤ)∧x S≠(L : ℤ)∧
      ((c : ℤ)<x S→x S<(L : ℤ)→(R : ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S}∨¬IsAP (S∩Finset.Icc (x S) (p S)))) :
    ((PreparedCrooked G c L).card : ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+(R : ℝ)*((N : ℝ)-R)+2*((L : ℝ)-c) := by
  have hc := actual_prepared_corner_reduction x p hG hcL hLR hP hLP hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.1,(hW S hS).2.2.1⟩)
  have hr := PreparedJoint67702.actual_prepared_right_joint x p hG hcL hLR hRN hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.2.2⟩)
  have he := actual_EB_count (by omega : c<R) houtside
  have hpoly : c*(N-R)+(R-L)*(N-R)+(L-c)*(N-R)=R*(N-R) := by
    rw [←Nat.add_mul,←Nat.add_mul]
    congr 1
    omega
  have hh : (PreparedCrooked G c L).card+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+R*(N-R)+2*(L-c) := by omega
  have hhR : ((PreparedCrooked G c L).card : ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+((R*(N-R) : ℕ) : ℝ)+((2*(L-c) : ℕ) : ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_mul,Nat.cast_sub hRN,Nat.cast_sub hcL.le,Nat.cast_ofNat] using hhR

#print axioms actual_preparation_custom
#print axioms actual_middle_custom
end
end JSP233.PreparationBounds67702
