module

public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Global.N233811.InitialPreparation233811
public import Erdos272.Global.NonInterval53
public import Erdos272.Global.N233811.CrossGap233811
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.RetainedIntervals233811
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 NonIntervalAP47
open HarmonicAbel29 LocalResourceRecovery208 Recovery208
open RecoveryPrefix208 RecoveryResource213
open ActualRecoveryChain208 (harmonic_cap)
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem actual_avoiders_are_intervals {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 233811≤N) (hhigh : N≤642498) (hcN : (c : ℤ)∈Ground N)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hroot : ∀S∈Retained N 12 F,¬IsAP S→(c : ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders (Retained N 12 F) (c : ℤ),∃a∈S,a≤(L : ℤ))
    (hleft : (L : ℝ)<(1/16 : ℝ)*N) :
    ∀S∈Avoiders (Retained N 12 F) (c : ℤ),IsInterval S := by
  intro S hS
  by_contra hno
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hret := actual_retained_legal (r := 12) hF
  have hb := NonInterval53.actual_noninterval_family_count hret hroot hcL hLN hlow hSG hcS hno
  have hd := InitialPreparation233811.retained_near hN hF hcard
  have he := CrossGap233811.exception_cap hN hhigh hcN
  have caps := RecoveryCaps213.actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hH14 : Harmonic N ≤ 14 := caps.harmonic_le.trans
    (by norm_num [RecoveryCaps213.HCap, RecoveryCaps213.LogCap])
  have hlin := mul_le_mul_of_nonneg_left hH14 (show (0 : ℝ) ≤ 2*N by positivity)
  have hLN2 := mul_le_mul_of_nonneg_right hleft.le (Nat.cast_nonneg (α := ℝ) N)
  have hn : (233811 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have hgap : (1895 : ℝ) < (N : ℝ)/48 := by linarith only [hn]
  have hp := mul_lt_mul_of_pos_right hgap hn0
  nlinarith only [hb, hd, he, hlin, hLN2, hp, hn]

theorem actual_avoiders_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T) (hN : 233811≤N) (hhigh : N≤642498)
    (hleft : (L : ℝ)<(1/16 : ℝ)*N) :
    ∀S∈Avoiders (Retained N 12 F) (c : ℤ),∃a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  have hlow : ∀S∈Avoiders (Retained N 12 F) (c : ℤ),∃a∈S,a≤(L : ℤ) := by
    intro S hS
    obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
    exact (g.outside S hSG hcS).1
  have hright : ∀S∈Avoiders (Retained N 12 F) (c : ℤ),∃b∈S,(R : ℤ)≤b := by
    intro S hS
    obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
    exact (g.outside S hSG hcS).2
  have hi := actual_avoiders_are_intervals hN (by omega : N≤642498) g.root_mem g.legal g.near_card
    g.root g.root_left.le (g.left_right.trans g.right_ground) hlow hleft
  have hF := actual_retained_legal (r := 12) g.legal
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
    (g : RootModel291012.Start N c L R F P T) (hN : 233811≤N) (hhigh : N≤642498)
    (hleft : (L : ℝ)<(1/16 : ℝ)*N) :
    ∃H∈Retained N 12 F, Finset.Icc (L : ℤ) (R : ℤ)⊆H := by
  have hP : P∈Avoiders (Retained N 12 F) (c : ℤ) :=
    Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩
  obtain ⟨a,b,_,haL,hRb,_,hrep⟩ := actual_avoiders_intervals g hN hhigh hleft P hP
  refine ⟨P,g.right_member,?_⟩
  rw [hrep]
  intro z hz
  obtain ⟨hLz,hzR⟩ := Finset.mem_Icc.mp hz
  apply Finset.mem_Icc.mpr
  have haLZ : (a : ℤ)≤L := by exact_mod_cast haL
  have hRbZ : (R : ℤ)≤b := by exact_mod_cast hRb
  exact ⟨haLZ.trans hLz,hzR.trans hRbZ⟩



#print axioms actual_avoiders_are_intervals
#print axioms actual_avoiders_intervals
#print axioms actual_interval_core
end
end JSP233.RetainedIntervals233811
