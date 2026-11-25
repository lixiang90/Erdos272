module

public import Erdos272.Counting.N67702.LowAPNonInterval67702
public import Erdos272.Retention.N86412.RetainedIntervals86412

@[expose] public section

namespace JSP233.RetainedIntervals67702
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 NonIntervalAP47
open HarmonicAbel29 LocalResourceRecovery208 Recovery208 WitnessInterval43
open RecoveryPrefix208 RecoveryResource213
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_avoiders_are_intervals {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 56400≤N) (hhigh : N≤88403) (hcN : (c : ℤ)∈Ground N)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hroot : ∀S∈Retained N 12 F,¬IsAP S→(c : ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders (Retained N 12 F) (c : ℤ),∃a∈S,a≤(L : ℤ))
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) :
    ∀S∈Avoiders (Retained N 12 F) (c : ℤ),IsInterval S := by
  intro S hS
  by_contra hno
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hret := actual_retained_legal (r := 12) hF
  have hc0 : 1≤c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp hcN).1
  have hn : (56400 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)<N := by linarith only [hn]
  have hhalf : 2*L≤N := by
    have hh : (2 : ℝ)*L≤N := by nlinarith only [hleft,hn]
    exact_mod_cast hh
  have hb := LowAPNonInterval67702.actual_noninterval_family_count (by omega : 1≤L)
    hhalf hret hroot hcL hLN hlow hSG hcS hno
  have hd := RetainedIntervals86412.retained_near hN (by omega : N≤2^18) hF hcard
  have he := Exception86412.exception_cap (by omega : 10000≤N) hhigh hcN
  have hcaps := LocalRecovery86412.actual_caps (k:=0) (by decide) (by omega : 10000≤N) hhigh
  have hH12 : Harmonic N≤12 := by
    have ht := hcaps.harmonic_le
    norm_num [LocalRecovery86412.HLocal,LocalRecovery86412.LogLocal] at ht
    exact ht
  have hlin := mul_le_mul_of_nonneg_left hH12 (Nat.cast_nonneg (α:=ℝ) N)
  have hquad : (L : ℝ)*((N : ℝ)-L)≤(14/225 : ℝ)*(N : ℝ)^2 := by
    have hp := mul_nonneg
      (show (0 : ℝ)≤(N : ℝ)/15-L by linarith only [hleft])
      (show (0 : ℝ)≤(N : ℝ)-(N : ℝ)/15-L by linarith only [hleft,hn])
    nlinarith only [hp]
  have hgap : (1097 : ℝ)<(1019/45000 : ℝ)*N := by linarith only [hn]
  have hp := mul_lt_mul_of_pos_right hgap hn0
  nlinarith only [hb,hd,he,hlin,hquad,hp,hn]

theorem actual_avoiders_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : RootModel291012.Start N c L R F P T) (hN : 56400≤N) (hhigh : N≤88403)
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) :
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
  have hi := actual_avoiders_are_intervals hN (by omega : N≤88403) g.root_mem g.legal g.near_card
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

#print axioms actual_avoiders_are_intervals
#print axioms actual_avoiders_intervals
end
end JSP233.RetainedIntervals67702
