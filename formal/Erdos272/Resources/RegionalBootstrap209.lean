module

public import Erdos272.Resources.UniversalRecovery209
public import Erdos272.Arithmetic.HarmonicLog55

@[expose] public section

/-! An actual, all-N legacy middle bootstrap.  Only the temporary left
endpoint is bounded here; no finite totient estimate is used. -/
namespace JSP233.RegionalBootstrap209
open StarCompletion APGeometry HarmonicAbel29 DenseDeletion40
open Recovery208 UniversalRecovery209
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem harmonic_mono {L N : ℕ} (hLN : L ≤ N) : Harmonic L ≤ Harmonic N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans hLN⟩
  · intro d _ _
    positivity

theorem harmonic_cap16 {N : ℕ} (hlo : 10902 ≤ N) (hhi : N ≤ 2000000) :
    Harmonic N ≤ 16 := by
  have hh := HarmonicLog55.actual_refined_harmonic_upper (J := 21)
    (by omega : 63 ≤ N) (by omega : N < 2000001)
  have hc : HarmonicLog55.HarmonicUpper 21 2000001 ≤ (16 : ℝ) := by
    norm_num [HarmonicLog55.HarmonicUpper, HarmonicLog55.LogUpper]
  exact hh.trans hc

theorem harmonic_cap {N : ℕ} (hlo : 10902 ≤ N) (hhi : N ≤ 2000000) :
    Harmonic N ≤ (151/10 : ℝ) := by
  have hh := HarmonicLog55.actual_refined_harmonic_upper (J := 21)
    (by omega : 63 ≤ N) (by omega : N < 2000001)
  have hc : HarmonicLog55.HarmonicUpper 21 2000001 ≤ (151/10 : ℝ) := by
    norm_num [HarmonicLog55.HarmonicUpper,HarmonicLog55.LogUpper]
  exact hh.trans hc

theorem affine_of_caps {N L R : ℕ}
    (hLR : L ≤ R) (hRN : R ≤ N) (hH : Harmonic N ≤ 16)
    (hprofile : WidthProfile L ((L : ℝ)+(N-R)) ≤
      LegacyMiddleCost N + GeometryCost N L ((L : ℝ)+(N-R)) +
      (485/4 : ℝ)*N + 968) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (4791/4 : ℝ)*N + (73/2 : ℝ)*L + 16*((L : ℝ)+(N-R)) + 972 := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) ≤ (L : ℝ)+(N-R) := by
    have hrn : (R : ℝ) ≤ N := by exact_mod_cast hRN
    exact add_nonneg hL0 (sub_nonneg.mpr hrn)
  have hH0 := harmonic_nonneg N
  have hHL := (harmonic_mono (hLR.trans hRN)).trans hH
  have hHsq : Harmonic N ^ 2 ≤ (16 : ℝ)^2 := by
    nlinarith only [mul_self_le_mul_self hH0 hH]
  have hlegacy : (4*Harmonic N+2)*Harmonic N ≤ (1056 : ℝ) := by
    nlinarith only [hHsq,hH]
  have hm := mul_le_mul_of_nonneg_right hlegacy hN0
  have hn := mul_le_mul_of_nonneg_right hH hN0
  have hl := mul_le_mul_of_nonneg_right hHL hL0
  have hw := mul_le_mul_of_nonneg_right hH hw0
  dsimp only [LegacyMiddleCost,GeometryCost] at hprofile
  nlinarith only [hprofile,hm,hn,hl,hw]

theorem left_of_affine {N : ℕ} {L w : ℝ} (hhi : N ≤ 2000000)
    (hprofile : WidthProfile L w ≤
      (4791/4 : ℝ)*N + (73/2 : ℝ)*L + 16*w + 972) : L < 170000 := by
  apply Recovery208.actual_left_bound hprofile
  · norm_num [LeftCentre]
  · have hn : (N : ℝ) ≤ 2000000 := by exact_mod_cast hhi
    norm_num [LeftCentre,WidthCentre,ShiftEnergy]
    nlinarith only [hn]

theorem actual_initial_affine {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hlo : 10902 ≤ N) (hhi : N ≤ 2000000)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    WidthProfile L ((L : ℝ)+(N-R)) ≤
      (4791/4 : ℝ)*N + (73/2 : ℝ)*L + 16*((L : ℝ)+(N-R)) + 972 := by
  exact affine_of_caps hLR hRN (harmonic_cap16 hlo hhi)
    (UniversalRecovery209.actual_original_initial_profile_local_cuts hlo hc hF hcard
      hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside)

theorem actual_initial_left {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hlo : 10902 ≤ N) (hhi : N ≤ 2000000)
    (hc : (c : ℤ) ∈ Ground N) (hF : Legal (Ground N) F)
    (hcard : B N ≤ F.card) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → (c : ℤ) ∈ S)
    (hP : P ∈ Retained N 11 F) (hcP : (c : ℤ) ∉ P)
    (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hT : T ∈ Retained N 11 F) (hcT : (c : ℤ) ∉ T)
    (hTR : ∀ z ∈ T, z ≤ (R : ℤ))
    (houtside : ∀ S ∈ Retained N 11 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    L < 170000 ∧ 3*L < 2*1670000 := by
  have hh := left_of_affine hhi (actual_initial_affine hlo hhi hc hF hcard hcL hLR hRN
    hroot hP hcP hLP hT hcT hTR houtside)
  have hl : L < 170000 := by exact_mod_cast hh
  exact ⟨hl,by omega⟩

#print axioms harmonic_cap16
#print axioms actual_initial_affine
#print axioms actual_initial_left
end
end JSP233.RegionalBootstrap209
