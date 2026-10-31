import Erdos272.Resources.GlobalBootstrap209
import Erdos272.Resources.FiniteRecovery209
import Erdos272.Resources.OriginalTerminal208
import Erdos272.Global.NonInterval53

/-! The same physical endpoints and the same original family pass through
one actual restoration, uniformly between two million and the global window. -/
namespace JSP233.GlobalRecovery209
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 NonIntervalAP47
open HarmonicAbel29 Recovery208 GlobalBootstrap209 AlignedPlans208 RecoveryOmitters208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Geometry (N c L R : ℕ) (F : Finset (Finset ℤ)) (P T : Finset ℤ) : Prop where
  low : 2000000 ≤ N
  high : N ≤ 62443451
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

theorem initial_certificate :
    StageCertificate 2000000 (579/4) 135 19 975 (1/30) (1/19) := by
  norm_num [StageCertificate,LeftCentre,WidthCentre,ShiftEnergy]

theorem after265_certificate :
    StageCertificate 2000000 (95/4) 135 (272477/504) (-81293/168) (1/65) (1/38) := by
  norm_num [StageCertificate,LeftCentre,WidthCentre,ShiftEnergy]

theorem actual_local_caps {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) :
    Harmonic N ≤ 19 ∧ 25*L ≤ 27721728 ∧
      9/2+2*Harmonic L+FrontierSum208.Polynomial (Real.log L) ≤ 135 := by
  have hN : 10902 ≤ N := by have := g.low; omega
  have hleft := GlobalBootstrap209.actual_initial_left hN g.high g.root_mem g.legal
    g.near_card g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hH := GlobalBootstrap209.harmonic_cap hN g.high
  have hHL := (GlobalBootstrap209.harmonic_mono (g.left_right.trans g.right_ground)).trans hH
  have hL : 1 ≤ L := by have := g.root_left; omega
  have hl := HarmonicLog55.actual_refined_log_upper (J := 20) hL hleft.1
  have hcap : HarmonicLog55.LogUpper 20 1101000 ≤ (14 : ℝ) := by
    norm_num [HarmonicLog55.LogUpper]
  have hlog : Real.log L ≤ 14 := hl.trans hcap
  have hlog0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hp : FrontierSum208.Polynomial (Real.log L) ≤ FrontierSum208.Polynomial 14 := by
    dsimp only [FrontierSum208.Polynomial]
    gcongr
  refine ⟨hH,(by omega : 25*L ≤ 27721728),?_⟩
  norm_num [FrontierSum208.Polynomial] at hp ⊢
  linarith only [hHL,hp]

theorem actual_initial_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (579/4 : ℝ)*N+135*L+19*((L : ℝ)+(N-R))+975 := by
  obtain ⟨hH,hcut,hlocal⟩ := actual_local_caps g
  have hr := FiniteRecovery209.actual_original_initial_profile_local
    (by have := g.low; omega : 10902 ≤ N) hH hcut g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hn := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  have hl := mul_le_mul_of_nonneg_right hlocal (Nat.cast_nonneg (α := ℝ) L)
  have hw := mul_le_mul_of_nonneg_right hH
    (show (0 : ℝ) ≤ (L : ℝ)+(N-R) by
      have hrn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
      exact add_nonneg (Nat.cast_nonneg L) (sub_nonneg.mpr hrn))
  nlinarith only [hr,hn,hl,hw]

theorem actual_initial_bounds {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    (L : ℝ)<(N : ℝ)/30 ∧ (L : ℝ)+(N-R)<(N : ℝ)/19 := by
  have hh := actual_stage_bounds (by exact_mod_cast g.low : (2000000 : ℝ) ≤ N)
    initial_certificate (actual_initial_affine g hi)
  constructor <;> nlinarith only [hh.1,hh.2]

theorem actual_avoiders_are_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/30) :
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
  have hH := (actual_local_caps g).1
  have hH0 := harmonic_nonneg N
  have hH3 : Harmonic N^3 ≤ (19 : ℝ)^3 := by gcongr
  have hlin := mul_le_mul_of_nonneg_left hH (show (0 : ℝ) ≤ 2*N by positivity)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0 : ℝ) ≤ 6*N by positivity)
  have hLN2 := mul_le_mul_of_nonneg_right hleft.le (Nat.cast_nonneg (α := ℝ) N)
  have hn : (2000000 : ℝ) ≤ N := by exact_mod_cast g.low
  have hn1 : (1 : ℝ) ≤ N := by linarith only [hn]
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have hgap : (41336 : ℝ) < (5/72 : ℝ)*N := by linarith only [hn]
  have hgap2 := mul_lt_mul_of_pos_right hgap hn0
  norm_num at hlin hcube
  nlinarith only [hb,hd,he,hlin,hcube,hLN2,hgap2,hn1]

theorem actual_avoiders_intervals {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/30) :
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
    (g : Geometry N c L R F P T) (hleft : (L : ℝ)<(N : ℝ)/30) :
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

theorem actual_after265_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (95/4 : ℝ)*N+135*L+(272477/504 : ℝ)*((L : ℝ)+(N-R))+(-81293/168) := by
  obtain ⟨hH,hcut,hlocal⟩ := actual_local_caps g
  have hfirst := actual_initial_bounds g hi
  have hcore := actual_interval_core g hfirst.1
  have hwidth : (L : ℝ)+(N-R)<(N : ℝ)/PreparationWidth 1 := by
    norm_num [PreparationWidth]
    have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith only [hfirst.2,hn0]
  have he := actual_preparation_omission_count (c := c) (r := 1)
    (by have := g.low; omega : 659912 ≤ N) (by decide) (by decide)
    (by have := g.root_left; omega : 1 ≤ L) g.left_right g.right_ground g.legal hcore hwidth
  have hr := FiniteRecovery209.actual_original_raw_profile_local
    (by have := g.low; omega : 19 ≤ N) hH hcut g.root_mem g.legal g.near_card
    g.root_left g.left_right g.right_ground g.root g.right_member g.right_avoids
    g.right_lower g.left_member g.left_avoids g.left_upper g.outside hi
  have hn := mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg (α := ℝ) N)
  have hl := mul_le_mul_of_nonneg_right hlocal (Nat.cast_nonneg (α := ℝ) L)
  have hw := mul_le_mul_of_nonneg_right hH
    (show (0 : ℝ) ≤ (L : ℝ)+(N-R) by
      have hrn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
      exact add_nonneg (Nat.cast_nonneg L) (sub_nonneg.mpr hrn))
  norm_num [PreparationA,PreparationP,PreparationB] at he
  dsimp only [FiniteRecovery209.MiddleCost,UniversalRecovery209.GeometryCost] at hr
  nlinarith only [hr,he,hn,hl,hw]

theorem actual_recovered_original {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Geometry N c L R F P T) (hi : FiniteRecovery209.TotientInputs 1540096) :
    F.card ≤ B N := by
  have hfirst := actual_initial_bounds g hi
  have hfinal := actual_stage_bounds (by exact_mod_cast g.low : (2000000 : ℝ) ≤ N)
    after265_certificate (actual_after265_affine g hi)
  have hhigh := g.high
  have hc : 1 ≤ c := by exact_mod_cast ((mem_ground N (c : ℤ)).mp g.root_mem).1
  apply OriginalTerminal208.actual_deleted_restore (by have := g.low; omega : 659912 ≤ N)
    (by norm_num; omega : N<2^50) hc g.root_left g.left_right g.right_ground _ g.legal
    (show (Avoiders (Retained N 11 F) (c : ℤ)).Nonempty from
      ⟨P,Finset.mem_filter.mpr ⟨g.right_member,g.right_avoids⟩⟩)
    (actual_avoiders_intervals g hfirst.1)
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith only [hfinal.2,hn0]

#print axioms initial_certificate
#print axioms after265_certificate
#print axioms actual_initial_affine
#print axioms actual_after265_affine
#print axioms actual_recovered_original
end
end JSP233.GlobalRecovery209
