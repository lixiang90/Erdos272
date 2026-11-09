module

public import Erdos272.Resources.LocalResourceRecovery208
public import Erdos272.Arithmetic.RecoveryPrefix208
public import Erdos272.Resources.RecoveryOmitters208
public import Erdos272.Resources.RecoveryGates208
public import Erdos272.Arithmetic.HarmonicCorrect118
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Four actual recovery preparations. The resource at each step is proved
before its consequent geometric gate is used at the following step. -/
namespace JSP233.ActualRecoveryChain208
open StarCompletion APGeometry HarmonicAbel29 APPrepare49 PreparedClasses50
open PreparedWitness48 RestrictedWitness44 MiddleCoordinates51 LongTerminal35 DenseDeletion40
open LocalRecovery208 LocalResourceRecovery208 FrontierSum208 RecoveryPrefix208
open RecoveryOmitters208 AlignedPlans208 RecoveryGates208 Recovery208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def LeftDiv (r : ℕ) : ℝ := match r with | 1 => 97/5 | 2 => 137/4 | _ => 248/5

def LocalLog (r : ℕ) : ℝ := LogCap-LogLeft r

def LocalHarmonic (r : ℕ) : ℝ := LocalLog r+1

theorem left_div_pos (r : ℕ) : 0<LeftDiv r := by
  unfold LeftDiv
  split <;> norm_num

theorem log_left {r : ℕ} (hr1 : 1≤r) (hr3 : r≤3) : LogLeft r ≤ Real.log (LeftDiv r) := by
  interval_cases r
  · exact log_left1
  · exact log_left2
  · exact log_left3

theorem harmonic_cap {N : ℕ} (hN : 100000≤N) (hhigh : N≤705097) : Harmonic N ≤ HCap := by
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hl := log_cap (by omega : 1≤N) hhigh
  have hc : LogCap+231/400=HCap := by norm_num [LogCap,HCap]
  linarith only [hh,hl,hc]

theorem harmonic_mono {L N : ℕ} (hLN : L≤N) : Harmonic L ≤ Harmonic N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hLN⟩
  · intro d _ _
    positivity

theorem log_local {N L r : ℕ} (hL : 1≤L) (hhigh : N≤705097)
    (hr1 : 1≤r) (hr3 : r≤3) (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r) :
    Real.log L ≤ LocalLog r := by
  have hLpos : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hmpos := left_div_pos r
  have hprod : (L : ℝ)*LeftDiv r ≤ N := (le_div_iff₀ hmpos).mp hleft.le
  have hNpos : 0<N := by
    have hh : (0 : ℝ)<N := (mul_pos hLpos hmpos).trans_le hprod
    exact_mod_cast hh
  have hlog := Real.log_le_log (mul_pos hLpos hmpos) hprod
  rw [Real.log_mul hLpos.ne' hmpos.ne'] at hlog
  have htop := log_cap (by omega : 1≤N) hhigh
  have hbot := log_left hr1 hr3
  dsimp only [LocalLog]
  linarith only [hlog,htop,hbot]

theorem harmonic_local {N L r : ℕ} (hL : 1≤L) (hhigh : N≤705097)
    (hr1 : 1≤r) (hr3 : r≤3) (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r) :
    Harmonic L ≤ LocalHarmonic r := by
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hl := log_local hL hhigh hr1 hr3 hleft
  dsimp only [LocalHarmonic]
  linarith only [hh,hl]

theorem polynomial_mono {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : FrontierSum208.Polynomial x ≤ FrontierSum208.Polynomial y := by
  dsimp only [FrontierSum208.Polynomial]
  gcongr

theorem polynomial_local {N L r : ℕ} (hL : 1≤L) (hhigh : N≤705097)
    (hr1 : 1≤r) (hr3 : r≤3) (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r) :
    FrontierSum208.Polynomial (Real.log L) ≤ FrontierSum208.Polynomial (LocalLog r) :=
  polynomial_mono (Real.log_nonneg (by exact_mod_cast hL)) (log_local hL hhigh hr1 hr3 hleft)

structure Geometry (N c L R : ℕ) (F : Finset (Finset ℤ)) (P T : Finset ℤ) : Prop where
  low : 659912≤N
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

theorem initial_actual_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤ initialA*N+initialL*L+initialW*((L : ℝ)+(N-R))+initialC := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hLN := g.left_right.trans g.right_ground
  have hh := harmonic_cap (by omega : 100000≤N) g.high
  have hhl := (harmonic_mono hLN).trans hh
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

theorem actual_local_affine {N c L R r : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) (hr1 : 1≤r) (hr3 : r≤3)
    (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth r) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (HCap+229/50)*(N : ℝ)+
      (102/25+2*LocalHarmonic r+FrontierSum208.Polynomial (LocalLog r))*(L : ℝ)+
      (HCap+PreparationA r+(PreparationP r : ℝ)-1)*((L : ℝ)+(N-R))+
      (25+PreparationB r-(PreparationP r : ℝ)+1) := by
  have hlow := g.low
  have hhigh := g.high
  have hcL := g.root_left
  have hL : 1≤L := by omega
  have hh := harmonic_cap (by omega : 100000≤N) g.high
  have hhl := harmonic_local hL g.high hr1 hr3 hleft
  have hpoly := polynomial_local hL g.high hr1 hr3 hleft
  have he := actual_preparation_omission_count (c := c) g.low hr1 hr3 hL g.left_right g.right_ground
    g.legal g.interval_core hwidth
  have hr := actual_original_raw_profile_local (by omega : 19≤N) (by omega : N≤853476)
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
  dsimp only [MiddleCost,GeometryCost] at hr
  nlinarith only [hr,he,hn,hw,hll,hpl,hN0]

theorem actual_four_stage {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : TotientInputs N) :
    (L : ℝ)<(5/251 : ℝ)*N ∧ ((L : ℝ)+(N-R))<(5/148 : ℝ)*N := by
  have hn : (659912 : ℝ) ≤ N := by exact_mod_cast g.low
  have hfirst := initial_bounds hn (initial_actual_affine g hi)
  have hpaid1 := actual_local_affine (r := 1) g hi (by decide) (by decide)
    (by norm_num [LeftDiv]; nlinarith only [hfirst.1])
    (by norm_num [PreparationWidth]; nlinarith only [hfirst.2])
  have hp1 : WidthProfile L ((L : ℝ)+(N-R)) ≤
      after265A*N+after265L*L+after265W*((L : ℝ)+(N-R))+after265C := by
    norm_num [HCap,LocalHarmonic,LocalLog,LogCap,LogLeft,FrontierSum208.Polynomial,PreparationA,
      PreparationP,PreparationB,after265A,after265L,after265W,after265C] at hpaid1 ⊢
    exact hpaid1
  have hsecond := after265_bounds hn hp1
  have hpaid2 := actual_local_affine (r := 2) g hi (by decide) (by decide)
    (by norm_num [LeftDiv]; nlinarith only [hsecond.1])
    (by norm_num [PreparationWidth]; nlinarith only [hsecond.2])
  have hp2 : WidthProfile L ((L : ℝ)+(N-R)) ≤
      after24A*N+after24L*L+after24W*((L : ℝ)+(N-R))+after24C := by
    norm_num [HCap,LocalHarmonic,LocalLog,LogCap,LogLeft,FrontierSum208.Polynomial,PreparationA,
      PreparationP,PreparationB,after24A,after24L,after24W,after24C] at hpaid2 ⊢
    exact hpaid2
  have hthird := after24_bounds hn hp2
  have hpaid3 := actual_local_affine (r := 3) g hi (by decide) (by decide)
    (by norm_num [LeftDiv]; nlinarith only [hthird.1])
    (by norm_num [PreparationWidth]; nlinarith only [hthird.2])
  have hp3 : WidthProfile L ((L : ℝ)+(N-R)) ≤
      after18A*N+after18L*L+after18W*((L : ℝ)+(N-R))+after18C := by
    norm_num [HCap,LocalHarmonic,LocalLog,LogCap,LogLeft,FrontierSum208.Polynomial,PreparationA,
      PreparationP,PreparationB,after18A,after18L,after18W,after18C] at hpaid3 ⊢
    exact hpaid3
  exact after18_bounds hn hp3

#print axioms harmonic_cap
#print axioms log_local
#print axioms initial_actual_affine
#print axioms actual_local_affine
#print axioms actual_four_stage
end
end JSP233.ActualRecoveryChain208
