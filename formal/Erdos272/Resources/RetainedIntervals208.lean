module

public import Erdos272.Resources.OriginalTerminal208
public import Erdos272.Global.NonInterval53
public import Erdos272.Resources.DenseDeletion208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The initial resource is independent of intervalization.  Its first left
bound excludes noninterval retained avoiders; only then is the interval core
installed for the later four-stage recovery. -/
namespace JSP233.RetainedIntervals208
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 NonIntervalAP47
open HarmonicAbel29 LocalResourceRecovery208 RecoveryGates208 Recovery208
open RecoveryPrefix208 ActualRecoveryChain208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure InitialGeometry (N c L R : ℕ) (F : Finset (Finset ℤ))
    (P T : Finset ℤ) : Prop where
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

theorem initial_actual_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hi : TotientInputs N) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      initialA*N+initialL*L+initialW*((L : ℝ)+(N-R))+initialC := by
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
  norm_num [initialA,initialL,initialW,initialC,HCap,LogCap,FrontierSum208.Polynomial]
    at hr hn hw hll hpl ⊢
  nlinarith only [hr,hn,hw,hll,hpl]

theorem actual_avoiders_are_intervals {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 659912≤N) (hhigh : N≤705097) (hcN : (c : ℤ)∈Ground N)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c : ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders (Retained N 11 F) (c : ℤ),∃a∈S,a≤(L : ℤ))
    (hleft : (L : ℝ)<(5/97 : ℝ)*N) :
    ∀S∈Avoiders (Retained N 11 F) (c : ℤ),IsInterval S := by
  intro S hS
  by_contra hno
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hret := actual_retained_legal (r := 11) hF
  have hb := NonInterval53.actual_noninterval_family_count hret hroot hcL hLN hlow hSG hcS hno
  have hd := DenseDeletion208.actual_retained11_near (by omega : 10902≤N) hF hcard
  have he := DivisorMoment45.actual_exception_harmonic hcN
  have hH := harmonic_cap (by omega : 100000≤N) hhigh
  have hH15 : Harmonic N≤15 := hH.trans (by norm_num [HCap])
  have hH0 := harmonic_nonneg N
  have hH3 : Harmonic N^3≤(15 : ℝ)^3 := by gcongr
  have hlin := mul_le_mul_of_nonneg_left hH15 (show (0 : ℝ)≤2*N by positivity)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0 : ℝ)≤6*N by positivity)
  have hLN2 := mul_le_mul_of_nonneg_right hleft.le (Nat.cast_nonneg (α := ℝ) N)
  have hn : (659912 : ℝ)≤N := by exact_mod_cast hN
  have hn1 : (1 : ℝ)≤N := by linarith only [hn]
  have hn0 : (0 : ℝ)<N := by linarith only [hn]
  have hgap : (20427 : ℝ)<(91/2328 : ℝ)*N := by linarith only [hn]
  have hgap2 := mul_lt_mul_of_pos_right hgap hn0
  norm_num at hlin hcube
  nlinarith only [hb,hd,he,hlin,hcube,hLN2,hgap2,hn1]

theorem actual_avoiders_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T)
    (hleft : (L : ℝ)<(5/97 : ℝ)*N) :
    ∀S∈Avoiders (Retained N 11 F) (c : ℤ),∃a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  have hlow : ∀S∈Avoiders (Retained N 11 F) (c : ℤ),∃a∈S,a≤(L : ℤ) := by
    intro S hS
    obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
    exact (g.outside S hSG hcS).1
  have hright : ∀S∈Avoiders (Retained N 11 F) (c : ℤ),∃b∈S,(R : ℤ)≤b := by
    intro S hS
    obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
    exact (g.outside S hSG hcS).2
  have hi := actual_avoiders_are_intervals g.low g.high g.root_mem g.legal g.near_card
    g.root g.root_left.le (g.left_right.trans g.right_ground) hlow hleft
  have hF := actual_retained_legal (r := 11) g.legal
  have hcL := g.root_left
  have hLR := g.left_right
  intro S hS
  obtain ⟨a,b,hrep⟩ := hi S hS
  obtain ⟨u,hu,huL⟩ := hlow S hS
  obtain ⟨v,hv,hRv⟩ := hright S hS
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have huI : a≤u ∧ u≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hvI : a≤v ∧ v≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hab : a≤b := huI.1.trans huI.2
  have haS : a∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
  have hbS : b∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  have haN := (mem_ground N a).mp (hF.1 S hSG haS)
  have hbN := (mem_ground N b).mp (hF.1 S hSG hbS)
  have hca : (c : ℤ)<a := by
    by_contra hn
    apply hcS
    rw [hrep]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have ha : (a.toNat : ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hb : (b.toNat : ℤ)=b := Int.toNat_of_nonneg (by omega)
  refine ⟨a.toNat,b.toNat,by omega,by omega,by omega,by omega,?_⟩
  simpa only [Interval,ha,hb] using hrep

theorem actual_interval_core {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T)
    (hleft : (L : ℝ)<(5/97 : ℝ)*N) :
    ∃H∈Retained N 11 F, Finset.Icc (L : ℤ) (R : ℤ)⊆H := by
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

theorem geometry_of_initial_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T)
    (hprofile : WidthProfile L ((L : ℝ)+(N-R)) ≤
      initialA*N+initialL*L+initialW*((L : ℝ)+(N-R))+initialC) :
    Geometry N c L R F P T := by
  have hn : (659912 : ℝ)≤N := by exact_mod_cast g.low
  have hleft := (initial_bounds hn hprofile).1
  exact ⟨g.low,g.high,g.root_mem,g.legal,g.near_card,g.root_left,g.left_right,g.right_ground,
    g.root,g.right_member,g.right_avoids,g.right_lower,g.left_member,g.left_avoids,g.left_upper,
    g.outside,actual_interval_core g hleft⟩

theorem actual_geometry {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hi : TotientInputs N) :
    Geometry N c L R F P T := geometry_of_initial_affine g (initial_actual_affine g hi)

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : InitialGeometry N c L R F P T) (hi : TotientInputs N) : F.card≤B N := by
  have hprofile := initial_actual_affine g hi
  have hn : (659912 : ℝ)≤N := by exact_mod_cast g.low
  have hleft := (initial_bounds hn hprofile).1
  have hne : (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩
  exact OriginalTerminal208.actual_recovered_original (geometry_of_initial_affine g hprofile) hi hne
    (actual_avoiders_intervals g hleft)

#print axioms initial_actual_affine
#print axioms actual_avoiders_are_intervals
#print axioms actual_avoiders_intervals
#print axioms actual_interval_core
#print axioms actual_geometry
#print axioms actual_recovered_original
end
end JSP233.RetainedIntervals208
