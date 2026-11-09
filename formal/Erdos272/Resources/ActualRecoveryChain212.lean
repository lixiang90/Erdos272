module

public import Erdos272.Resources.ActualRecoveryChain208
public import Erdos272.Arithmetic.RecoveryScalar212
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.ActualRecoveryChain212
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open LocalRecovery208 LocalResourceRecovery208 FrontierSum208 RecoveryPrefix208 RecoveryGates208 Recovery208
open ActualRecoveryChain208 AlignedPlans212 RecoveryOmitters212 RecoveryScalar212
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
structure Geometry (N c L R : ℕ) (F : Finset (Finset ℤ)) (P T : Finset ℤ) : Prop where
  low : 656184≤N
  high : N≤705097
  root_mem : (c : ℤ) ∈ Ground N
  legal : Legal (Ground N) F
  near_card : B N ≤ F.card
  root_left : c<L
  left_right : L≤R
  right_ground : R≤N
  root : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ)∈S
  right_member : P∈Retained N 11 F
  right_avoids : (c : ℤ)∉P
  right_lower : ∀z∈P,(L : ℤ)≤z
  left_member : T∈Retained N 11 F
  left_avoids : (c : ℤ)∉T
  left_upper : ∀z∈T,z≤(R : ℤ)
  outside : ∀S∈Retained N 11 F,(c : ℤ)∉S →
    (∃u∈S,u≤(L : ℤ)) ∧ ∃v∈S,(R : ℤ)≤v
  interval_core : ∃H∈Retained N 11 F, Finset.Icc (L : ℤ) (R : ℤ) ⊆ H

theorem initial_global_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ initialA*N+initialL*L+initialW*((L : ℝ)+(N-R))+initialC := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hLN := g.left_right.trans g.right_ground
  have hh := harmonic_cap (by omega : 100000≤N) g.high
  have hhl := (ActualRecoveryChain208.harmonic_mono hLN).trans hh
  have hl := log_cap hL (hLN.trans g.high)
  have hpoly := polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) hl
  have hr := actual_original_initial_profile_local (by omega : 10902≤N) (by omega : N≤853476)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hL0,hRN]
  have hn := mul_le_mul_of_nonneg_right hh hN0
  have hw := mul_le_mul_of_nonneg_right hh hw0
  have hll := mul_le_mul_of_nonneg_right hhl hL0
  have hpl := mul_le_mul_of_nonneg_right hpoly hL0
  norm_num [initialA,initialL,initialW,initialC,HCap,LogCap,FrontierSum208.Polynomial] at hr hn hw hll hpl ⊢
  nlinarith only [hr,hn,hw,hll,hpl]


theorem initial_reprice {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) (hj : j≤7)
    (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ A 0*N+
      RecoveryLocalization212.LocalCoeff j*L+W 0*((L : ℝ)+(N-R))+C 0 := by
  have hlow := g.low
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hh := harmonic_cap (by omega : 100000≤N) g.high
  have hl := RecoveryLocalization212.local_payment hL g.high hj hleft
  have hr := actual_original_initial_profile_local (by omega : 10902≤N) (by have ht := g.high; omega : N≤853476)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hn := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) N)
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
    linarith only [hRN,hL0]
  have hw := mul_le_mul_of_nonneg_right hh hw0
  norm_num [A,W,C,initialA,initialW,initialC,HCap] at hr hn hw ⊢
  nlinarith only [hr,hl,hn,hw]

theorem actual_local_affine {N c L R r j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) (hr1 : 1≤r) (hr3 : r≤3)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth r) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ A r*N+
      RecoveryLocalization212.LocalCoeff j*L+W r*((L : ℝ)+(N-R))+C r := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hh := harmonic_cap (by omega : 100000≤N) g.high
  have hl := RecoveryLocalization212.local_payment hL g.high hj hleft
  have he := RecoveryOmitters212.actual_preparation_omission_count (c := c) g.low hr1 hr3 hL
    g.left_right g.right_ground g.legal g.interval_core hwidth
  have hr := actual_original_raw_profile_local (by omega : 19≤N) (by omega : N≤853476)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
    linarith only [hRN,hL0]
  have hn := mul_le_mul_of_nonneg_right hh hN0
  have hw := mul_le_mul_of_nonneg_right hh hw0
  dsimp only [MiddleCost,GeometryCost] at hr
  have hr0 : r≠0 := by omega
  simp only [A,W,C,if_neg hr0]
  nlinarith only [hr,he,hn,hw,hl,hN0]

theorem actual_four_stage {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) :
    (L : ℝ)<(N : ℝ)/50 ∧ ((L : ℝ)+(N-R))<(N : ℝ)/(2951/100) := by
  have hn : (656184 : ℝ)≤N := by exact_mod_cast g.low
  have hg : WidthProfile L ((L : ℝ)+(N-R)) ≤ A 0*N+
      initialL*L+W 0*((L : ℝ)+(N-R))+C 0 := by
    simpa [A,W,C] using initial_global_affine g hi
  have h0 := initial_weak hn hg
  have h1 := initial_update hn (initial_reprice g hi (by decide : 0≤7) h0)
  have h2 := initial_final hn (initial_reprice g hi (by decide : 1≤7) h1)
  have h3 := first_weak hn (actual_local_affine (r:=1) g hi (by decide) (by decide) (by decide : 1≤7) h2.1 h2.2)
  have h4 := first_update hn (actual_local_affine (r:=1) g hi (by decide) (by decide) (by decide : 2≤7) h3 h2.2)
  have h5 := first_final hn (actual_local_affine (r:=1) g hi (by decide) (by decide) (by decide : 3≤7) h4 h2.2)
  have h6 := second_weak hn (actual_local_affine (r:=2) g hi (by decide) (by decide) (by decide : 4≤7) h5.1 h5.2)
  have h7 := second_update hn (actual_local_affine (r:=2) g hi (by decide) (by decide) (by decide : 5≤7) h6 h5.2)
  have h8 := second_final hn (actual_local_affine (r:=2) g hi (by decide) (by decide) (by decide : 6≤7) h7 h5.2)
  have h9 := third_weak hn (actual_local_affine (r:=3) g hi (by decide) (by decide) (by decide : 6≤7) h8.1 h8.2)
  have ht := third_final hn (actual_local_affine (r:=3) g hi (by decide) (by decide) (by decide : 7≤7) h9 h8.2)
  simpa [RecoveryLocalization212.Div] using ht
#print axioms initial_global_affine
#print axioms initial_reprice
#print axioms actual_local_affine
#print axioms actual_four_stage
end
end JSP233.ActualRecoveryChain212
