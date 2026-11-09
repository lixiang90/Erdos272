module

public import Erdos272.Resources.RegionalBootstrap209
public import Erdos272.Resources.FiniteRecovery209
public import Erdos272.Resources.OriginalTerminal208
public import Erdos272.Global.NonInterval53
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.RegionalRecovery209
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 NonIntervalAP47
open HarmonicAbel29 Recovery208 RegionalBootstrap209 AlignedPlans208 RecoveryOmitters208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Geometry (N c L R : ℕ) (F : Finset (Finset ℤ)) (P T : Finset ℤ) : Prop where
  low : 705098 ≤ N
  high : N ≤ 2000000
  root_mem : (c : ℤ) ∈ Ground N
  legal : Legal (Ground N) F
  near_card : B N ≤ F.card
  root_left : c < L
  left_right : L ≤ R
  right_ground : R ≤ N
  root : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S
  right_member : P ∈ Retained N 11 F
  right_avoids : (c : ℤ) ∉ P
  right_lower : ∀ z ∈ P, (L : ℤ) ≤ z
  left_member : T ∈ Retained N 11 F
  left_avoids : (c : ℤ) ∉ T
  left_upper : ∀ z ∈ T, z ≤ (R : ℤ)
  outside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
    (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v

def HCap : ℝ := 151/10
def InitialA : ℝ := HCap+503/4
def RestoredA : ℝ := HCap+19/4
def RowCap (r : ℕ) : ℝ := match r with | 1 => 100 | 2 => 94 | _ => 91
def LeftDiv (r : ℕ) : ℝ := match r with | 1 => 20 | 2 => 137/4 | _ => 248/5
def LogCap (r : ℕ) : ℝ := match r with | 1 => 58/5 | 2 => 11 | _ => 107/10
def StageW (r : ℕ) : ℝ := HCap+PreparationA r+(PreparationP r : ℝ)-1
def StageC (r : ℕ) : ℝ := 7+PreparationB r-(PreparationP r : ℝ)+1

theorem initial_certificate :
    StageCertificate 705098 InitialA 106 HCap 975 (1/20) (50/573) := by
  norm_num [StageCertificate,InitialA,HCap,LeftCentre,WidthCentre,ShiftEnergy]

theorem restored1_certificate :
    StageCertificate 705098 RestoredA 100 (StageW 1) (StageC 1) (4/137) (20/401) := by
  norm_num [StageCertificate,RestoredA,HCap,StageW,StageC,PreparationA,PreparationB,PreparationP,
    LeftCentre,WidthCentre,ShiftEnergy]

theorem restored2_certificate :
    StageCertificate 705098 RestoredA 94 (StageW 2) (StageC 2) (5/248) (4/117) := by
  norm_num [StageCertificate,RestoredA,HCap,StageW,StageC,PreparationA,PreparationB,PreparationP,
    LeftCentre,WidthCentre,ShiftEnergy]

theorem restored3_certificate :
    StageCertificate 705098 RestoredA 91 (StageW 3) (StageC 3) (1/50) (5/148) := by
  norm_num [StageCertificate,RestoredA,HCap,StageW,StageC,PreparationA,PreparationB,PreparationP,
    LeftCentre,WidthCentre,ShiftEnergy]

theorem coefficient_of_log {L : ℕ} {x y : ℝ} (hL : 1 ≤ L)
    (hlog : Real.log L ≤ x)
    (hnum : 9/2+2*(1+x)+FrontierSum208.Polynomial x ≤ y) :
    9/2+2*Harmonic L+FrontierSum208.Polynomial (Real.log L) ≤ y := by
  have hlog0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hx0 : 0 ≤ x := hlog0.trans hlog
  have hp : FrontierSum208.Polynomial (Real.log L) ≤ FrontierSum208.Polynomial x := by
    dsimp only [FrontierSum208.Polynomial]
    gcongr
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  linarith only [hh,hlog,hp,hnum]

theorem actual_local_caps {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) :
    Harmonic N ≤ HCap ∧ 25*L ≤ 27721728 ∧
      9/2+2*Harmonic L+FrontierSum208.Polynomial (Real.log L) ≤ 106 := by
  have hN : 10902 ≤ N := by have := g.low; omega
  have hleft := RegionalBootstrap209.actual_initial_left hN g.high g.root_mem g.legal
    g.near_card g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hH := RegionalBootstrap209.harmonic_cap hN g.high
  have hL : 1 ≤ L := by have := g.root_left; omega
  have hl := HarmonicLog55.actual_refined_log_upper (J := 17) hL hleft.1
  have hcap : HarmonicLog55.LogUpper 17 170000 ≤ (121/10 : ℝ) := by
    norm_num [HarmonicLog55.LogUpper]
  refine ⟨hH,(by omega : 25*L ≤ 27721728),?_⟩
  exact coefficient_of_log hL (hl.trans hcap) (by norm_num [FrontierSum208.Polynomial])

theorem staged_log {N c L R r : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r) : Real.log L ≤ LogCap r := by
  have hN : (N : ℝ) ≤ 2000000 := by exact_mod_cast g.high
  have hL : 1 ≤ L := by have := g.root_left; omega
  interval_cases r
  · have hlR : (L : ℝ)<100000 := by norm_num [LeftDiv] at hleft; nlinarith only [hleft,hN]
    have hlN : L<100000 := by exact_mod_cast hlR
    have hl := HarmonicLog55.actual_refined_log_upper (J := 17) hL hlN
    apply hl.trans
    norm_num [HarmonicLog55.LogUpper,LogCap]
  · have hlR : (L : ℝ)<58395 := by norm_num [LeftDiv] at hleft; nlinarith only [hleft,hN]
    have hlN : L<58395 := by exact_mod_cast hlR
    have hl := HarmonicLog55.actual_refined_log_upper (J := 16) hL hlN
    apply hl.trans
    norm_num [HarmonicLog55.LogUpper,LogCap]
  · have hlR : (L : ℝ)<40323 := by norm_num [LeftDiv] at hleft; nlinarith only [hleft,hN]
    have hlN : L<40323 := by exact_mod_cast hlR
    have hl := HarmonicLog55.actual_refined_log_upper (J := 15) hL hlN
    apply hl.trans
    norm_num [HarmonicLog55.LogUpper,LogCap]

theorem staged_coefficient {N c L R r : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r) :
    9/2+2*Harmonic L+FrontierSum208.Polynomial (Real.log L) ≤ RowCap r := by
  apply coefficient_of_log (by have := g.root_left; omega : 1 ≤ L)
    (staged_log g hr1 hr3 hleft)
  interval_cases r <;> norm_num [LogCap,RowCap,FrontierSum208.Polynomial]

theorem actual_initial_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      InitialA*N+106*L+HCap*((L : ℝ)+(N-R))+975 := by
  obtain ⟨hH,hcut,hlocal⟩ := actual_local_caps g
  have hH19 : Harmonic N ≤ 19 := hH.trans (by norm_num [HCap])
  have hr := FiniteRecovery209.actual_original_initial_profile_local
    (by have := g.low; omega : 10902 ≤ N) hH19 hcut g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hn := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  have hl := mul_le_mul_of_nonneg_right hlocal (Nat.cast_nonneg (α := ℝ) L)
  have hrn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  have hw := mul_le_mul_of_nonneg_right hH
    (add_nonneg (Nat.cast_nonneg L) (sub_nonneg.mpr hrn))
  dsimp only [InitialA]
  nlinarith only [hr,hn,hl,hw]

theorem actual_initial_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    (L : ℝ)<(N : ℝ)/20 ∧ (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth 1 := by
  have hh := actual_stage_bounds (by exact_mod_cast g.low : (705098 : ℝ) ≤ N)
    initial_certificate (actual_initial_affine g hi)
  norm_num [PreparationWidth]
  constructor <;> nlinarith only [hh.1,hh.2]

theorem actual_avoiders_are_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/20) :
    ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), IsInterval S := by
  intro S hS
  by_contra hno
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hret := actual_retained_legal (r := 11) g.legal
  have hlow : ∀ U ∈ Avoiders (Retained N 11 F) (c : ℤ),∃ a ∈ U,a ≤ (L : ℤ) := by
    intro U hU
    exact (g.outside U (Finset.mem_filter.mp hU).1 (Finset.mem_filter.mp hU).2).1
  have hb := NonInterval53.actual_noninterval_family_count hret g.root g.root_left.le
    (g.left_right.trans g.right_ground) hlow hSG hcS hno
  have hd := DenseDeletion208.actual_retained11_near (by have := g.low; omega : 10902 ≤ N)
    g.legal g.near_card
  have he := DivisorMoment45.actual_exception_harmonic g.root_mem
  have hH : Harmonic N ≤ 16 := (actual_local_caps g).1.trans (by norm_num [HCap])
  have hH0 := harmonic_nonneg N
  have hH3 : Harmonic N^3 ≤ (16 : ℝ)^3 := by gcongr
  have hlin := mul_le_mul_of_nonneg_left hH (show (0 : ℝ) ≤ 2*N by positivity)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0 : ℝ) ≤ 6*N by positivity)
  have hLN2 := mul_le_mul_of_nonneg_right hleft.le (Nat.cast_nonneg (α := ℝ) N)
  have hn : (705098 : ℝ) ≤ N := by exact_mod_cast g.low
  have hn1 : (1 : ℝ) ≤ N := by linarith only [hn]
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have hgap : (24752 : ℝ) < (1/24 : ℝ)*N := by linarith only [hn]
  have hgap2 := mul_lt_mul_of_pos_right hgap hn0
  norm_num at hlin hcube
  nlinarith only [hb,hd,he,hlin,hcube,hLN2,hgap2,hn1]

theorem actual_avoiders_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/20) :
    ∀ S ∈ Avoiders (Retained N 11 F) (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  have hF := actual_retained_legal (r := 11) g.legal
  intro S hS
  obtain ⟨a,b,hrep⟩ := actual_avoiders_are_intervals g hleft S hS
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  obtain ⟨⟨u,hu,huL⟩,v,hv,hRv⟩ := g.outside S hSG hcS
  have huI : a≤u ∧ u≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hvI : a≤v ∧ v≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hab : a≤b := huI.1.trans huI.2
  have haS : a∈S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
  have hbS : b∈S := by rw [hrep]; exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  have haN := (mem_ground N a).mp (hF.1 S hSG haS)
  have hbN := (mem_ground N b).mp (hF.1 S hSG hbS)
  have hca : (c : ℤ)<a := by
    by_contra hn
    apply hcS
    rw [hrep]
    have hcL := g.root_left
    have hLR := g.left_right
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have ha : (a.toNat : ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hb : (b.toNat : ℤ)=b := Int.toNat_of_nonneg (by omega)
  refine ⟨a.toNat,b.toNat,by omega,by omega,by omega,by omega,?_⟩
  simpa only [Interval,ha,hb] using hrep

theorem actual_interval_core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/20) :
    ∃ H ∈ Retained N 11 F, Finset.Icc (L : ℤ) (R : ℤ) ⊆ H := by
  have hP : P∈Avoiders (Retained N 11 F) (c : ℤ) :=
    Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩
  obtain ⟨a,b,_,haL,hRb,_,hrep⟩ := actual_avoiders_intervals g hleft P hP
  refine ⟨P,g.right_member,?_⟩
  rw [hrep]
  intro z hz
  obtain ⟨hLz,hzR⟩ := Finset.mem_Icc.mp hz
  apply Finset.mem_Icc.mpr
  have haLZ : (a : ℤ)≤L := by exact_mod_cast haL
  have hRbZ : (R : ℤ)≤b := by exact_mod_cast hRb
  exact ⟨haLZ.trans hLz,hzR.trans hRbZ⟩

theorem actual_stage_affine {N c L R r : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hleft : (L : ℝ)<(N : ℝ)/LeftDiv r)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth r) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      RestoredA*N+RowCap r*L+StageW r*((L : ℝ)+(N-R))+StageC r := by
  obtain ⟨hH,hcut,_⟩ := actual_local_caps g
  have hH19 : Harmonic N ≤ 19 := hH.trans (by norm_num [HCap])
  have hlocal := staged_coefficient g hr1 hr3 hleft
  have hfirst := actual_initial_bounds g hi
  have he := actual_preparation_omission_count (c := c)
    (by have := g.low; omega : 659912 ≤ N) hr1 hr3
    (by have := g.root_left; omega : 1 ≤ L) g.left_right g.right_ground g.legal
    (actual_interval_core g hfirst.1) hwidth
  have hr := FiniteRecovery209.actual_original_raw_profile_local
    (by have := g.low; omega : 19 ≤ N) hH19 hcut g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hn := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  have hl := mul_le_mul_of_nonneg_right hlocal (Nat.cast_nonneg (α := ℝ) L)
  have hrn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  have hw := mul_le_mul_of_nonneg_right hH
    (add_nonneg (Nat.cast_nonneg L) (sub_nonneg.mpr hrn))
  dsimp only [FiniteRecovery209.MiddleCost,UniversalRecovery209.GeometryCost] at hr
  dsimp only [RestoredA,StageW,StageC]
  nlinarith only [hr,he,hn,hl,hw]

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    F.card ≤ B N := by
  have hn : (705098 : ℝ) ≤ N := by exact_mod_cast g.low
  have hfirst := actual_initial_bounds g hi
  have hpaid1 := actual_stage_affine g hi (r := 1) (by decide) (by decide)
    (by simpa only [LeftDiv] using hfirst.1) hfirst.2
  have hsecond := actual_stage_bounds hn restored1_certificate hpaid1
  have hpaid2 := actual_stage_affine g hi (r := 2) (by decide) (by decide)
    (by norm_num [LeftDiv]; nlinarith only [hsecond.1])
    (by norm_num [PreparationWidth]; nlinarith only [hsecond.2])
  have hthird := actual_stage_bounds hn restored2_certificate hpaid2
  have hpaid3 := actual_stage_affine g hi (r := 3) (by decide) (by decide)
    (by norm_num [LeftDiv]; nlinarith only [hthird.1])
    (by norm_num [PreparationWidth]; nlinarith only [hthird.2])
  have hfinal := actual_stage_bounds hn restored3_certificate hpaid3
  have hhigh := g.high
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  apply OriginalTerminal208.actual_deleted_restore (by have := g.low; omega : 659912 ≤ N)
    (by norm_num; omega : N<2^50) hc g.root_left g.left_right g.right_ground _ g.legal
    (show (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty from
      ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩)
    (actual_avoiders_intervals g hfirst.1)
  nlinarith only [hfinal.2]

#print axioms initial_certificate
#print axioms restored1_certificate
#print axioms restored2_certificate
#print axioms restored3_certificate
#print axioms actual_initial_affine
#print axioms actual_stage_affine
#print axioms actual_recovered_original
end
end JSP233.RegionalRecovery209
