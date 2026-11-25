module

public import Erdos272.Counting.N67702.RawProfile67702
public import Erdos272.Counting.N67702.ReaddedEX67702
public import Erdos272.Counting.N67702.ReaddedShort67702
public import Erdos272.Resources.N67702.LocalRecovery67702

@[expose] public section

namespace JSP233.ProfileCount67702
open StarCompletion APGeometry APPrepare49 PreparedClasses50 RootModel291012
open HarmonicAbel29 LocalRecovery67702 RecoveryProfiles291012 RecoveryCaps213
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem readded_legal {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) : Legal (Ground N) (GenericRecovery291012.Readded N 12 F (c : ℤ)) :=
  ⟨fun S hS=>g.legal.1 S (Finset.sdiff_subset hS),
   fun S hS U hU hne=>g.legal.2 S (Finset.sdiff_subset hS) U (Finset.sdiff_subset hU) hne⟩

theorem readded_outside {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) :
    ∀S∈GenericRecovery291012.Readded N 12 F (c : ℤ),(c : ℤ)∉S→
      (∃u∈S,u≤(L : ℤ))∧∃v∈S,(R : ℤ)≤v := by
  intro S hS hcS
  have hv : S∈Avoiders (GenericRecovery291012.Readded N 12 F (c : ℤ)) (c : ℤ) :=
    Finset.mem_filter.mpr ⟨hS,hcS⟩
  rw [GenericRecovery291012.Readded,TerminalDeficit51.actual_avoider_readdition] at hv
  exact g.outside S (Finset.mem_filter.mp hv).1 hcS

theorem global_raw {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {rho : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (he : ((Omitted N c F).card : ℝ)≤rho*N) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+433/100+rho-8/3)*N+(Coeff L+1)*L+
      (HLocal 0-10493/5000)*Width N L R+872-2*c := by
  have hG := readded_legal g
  have hs := GenericRecovery291012.actual_retained_subset_readded N 12 F (c : ℤ)
  have hex := ReaddedEX67702.actual_prepared_global (by omega : 2000≤N)
    g.root_left g.left_right g.right_ground hG (hs g.right_member) g.right_lower (readded_outside g)
  have hsmall := ActualPreparation208.actual_small_AP_cut_count (by omega : 19≤N) hG
  have hsmallR : ((SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ))).card : ℝ)≤2*(N : ℝ)+0 := by
    have hh : ((SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ))).card : ℝ)≤((2*N-1 : ℕ) : ℝ) := by exact_mod_cast hsmall
    have ht : ((2*N-1 : ℕ) : ℝ)≤2*(N : ℝ) := by exact_mod_cast (Nat.sub_le (2*N) 1)
    linarith only [hh,ht]
  have hexR : ((EX (PreparedAP (GenericRecovery291012.Readded N 12 F (c : ℤ)) c L) R).card : ℝ)≤
      (129/200 : ℝ)*L*((N : ℝ)-R)+Width N L R*Harmonic N+N-
        (2/3 : ℝ)*N-(10493/5000 : ℝ)*Width N L R+0 := by
    dsimp only [Width] at *
    nlinarith only [hex]
  have hr := RawProfile67702.actual_raw_with_bounds g (by omega : 19≤N) (by omega : N≤720896) hsmallR hexR
  have hc := LocalRecovery67702.actual_caps (k:=0) (by decide) (by omega) hhi
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α:=ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  dsimp only [Coeff,CovarianceFamily214.MiddleCost,LocalRecovery208.GeometryCost] at *
  nlinarith only [hr,he,hnpaid,hwpaid]

theorem short_raw {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {e : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) (hspan : L+3≤R)
    (k : Fin 2) (hw : Width N L R≤EXOneHole67702.WidthCap k*N)
    (he : ((Omitted N c F).card : ℝ)≤e) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+112/100)*N+(Coeff L+1/2)*L+
      (HLocal 0-1-EXLog67702.Beta k)*Width N L R+874+e-c := by
  have hG := readded_legal g
  have hs := GenericRecovery291012.actual_retained_subset_readded N 12 F (c : ℤ)
  have hex := ReaddedEX67702.actual_prepared_cap (by omega : 2000≤N)
    g.root_left g.left_right g.right_ground hG (hs g.right_member) g.right_lower (readded_outside g) k hw
  have hsmall := ReaddedShort67702.actual_readded_small g (by omega) (by omega) hleft hspan
  have hsmallR : ((SmallAP (GenericRecovery291012.Readded N 12 F (c : ℤ))).card : ℝ)≤
      2*(N : ℝ)+(-(N : ℝ)/2-(L : ℝ)/2-Width N L R+c+1) := by linarith only [hsmall]
  have hexR : ((EX (PreparedAP (GenericRecovery291012.Readded N 12 F (c : ℤ)) c L) R).card : ℝ)≤
      (129/200 : ℝ)*L*((N : ℝ)-R)+Width N L R*Harmonic N+N-
        (71/100 : ℝ)*N-EXLog67702.Beta k*Width N L R+1 := by
    dsimp only [Width] at *
    nlinarith only [hex]
  have hr := RawProfile67702.actual_raw_with_bounds g (by omega : 19≤N) (by omega : N≤720896) hsmallR hexR
  have hc := LocalRecovery67702.actual_caps (k:=0) (by decide) (by omega) hhi
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α:=ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  dsimp only [Coeff,CovarianceFamily214.MiddleCost,LocalRecovery208.GeometryCost] at *
  nlinarith only [hr,he,hnpaid,hwpaid]

theorem actual_global_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {rho : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (he : ((Omitted N c F).card : ℝ)≤rho*N) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+433/100+rho-8/3)*N+(BGlobal 0+1)*L+
      (HLocal 0-10493/5000)*Width N L R+872-2*c := by
  have hr := global_raw g hN hhi he
  have hp : RawProfile N L (Width N L R) (HLocal 0+433/100+rho-8/3)
      (HLocal 0-10493/5000) (872+(L : ℝ)-2*c) := by
    dsimp only [RawProfile]
    linarith only [hr]
  have hh := global_profile (k:=0) (LocalRecovery67702.actual_caps (by decide) (by omega) hhi)
    (by have h:=g.root_left;omega) (g.left_right.trans g.right_ground) hp
  linarith only [hh]

theorem actual_local_global_profile {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {rho : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (hj : 4≤j) (hjhi : j≤33) (hB : (38 : ℝ)≤BLocal 0 j)
    (hl : (L : ℝ)<(N : ℝ)/j) (he : ((Omitted N c F).card : ℝ)≤rho*N) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+433/100+rho-8/3)*N+(BLocal 0 j+1)*L+
      (HLocal 0-10493/5000)*Width N L R+872-2*c := by
  have hr := global_raw g hN hhi he
  have hp : RawProfile N L (Width N L R) (HLocal 0+433/100+rho-8/3)
      (HLocal 0-10493/5000) (872+(L : ℝ)-2*c) := by
    dsimp only [RawProfile]
    linarith only [hr]
  have hh := local_profile (k:=0) (LocalRecovery67702.actual_caps (by decide) (by omega) hhi)
    (by have h:=g.root_left;omega) hj hjhi hB hl hp
  linarith only [hh]

theorem actual_local_short_profile {N c L R j : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {e : ℝ}
    (g : Start N c L R F P T) (hN : 67702≤N) (hhi : N≤80469)
    (hleft : (L : ℝ)<(1/15 : ℝ)*N) (hspan : L+3≤R)
    (q : Fin 2) (hw : Width N L R≤EXOneHole67702.WidthCap q*N)
    (hj : 4≤j) (hjhi : j≤33) (hB : (38 : ℝ)≤BLocal 0 j)
    (hl : (L : ℝ)<(N : ℝ)/j) (he : ((Omitted N c F).card : ℝ)≤e) :
    Recovery208.WidthProfile L (Width N L R)≤
      (HLocal 0+112/100)*N+(BLocal 0 j+1/2)*L+
      (HLocal 0-1-EXLog67702.Beta q)*Width N L R+874+e-c := by
  have hr := short_raw g hN hhi hleft hspan q hw he
  have hp : RawProfile N L (Width N L R) (HLocal 0+112/100)
      (HLocal 0-1-EXLog67702.Beta q) (874+e-c+(L : ℝ)/2) := by
    dsimp only [RawProfile]
    linarith only [hr]
  have hh := local_profile (k:=0) (LocalRecovery67702.actual_caps (by decide) (by omega) hhi)
    (by have h:=g.root_left;omega) hj hjhi hB hl hp
  linarith only [hh]

#print axioms readded_legal
#print axioms readded_outside
#print axioms global_raw
#print axioms short_raw
#print axioms actual_global_profile
#print axioms actual_local_global_profile
#print axioms actual_local_short_profile
end
end JSP233.ProfileCount67702
