module

public import Erdos272.Arithmetic.N291012.GenericRecovery291012
public import Erdos272.Retention.N291012.RecoveryProfiles291012
public import Erdos272.Counting.UnitAvoider218

@[expose] public section

namespace JSP233.RootModel291012
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 WitnessInterval43
open UnitCount218 RecoveryCaps213 RecoveryParameters291012 RecoveryProfiles291012
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Start (N c L R : ℕ) (F : Finset (Finset ℤ)) (P T : Finset ℤ) : Prop where
  root_mem : (c : ℤ) ∈ Ground N
  legal : Legal (Ground N) F
  near_card : B N ≤ F.card
  root_left : c < L
  left_right : L ≤ R
  right_ground : R ≤ N
  root : ∀ S ∈ Retained N 12 F, ¬IsAP S → (c : ℤ) ∈ S
  right_member : P ∈ Retained N 12 F
  right_avoids : (c : ℤ) ∉ P
  right_lower : ∀ z ∈ P, (L : ℤ) ≤ z
  left_member : T ∈ Retained N 12 F
  left_avoids : (c : ℤ) ∉ T
  left_upper : ∀ z ∈ T, z ≤ (R : ℤ)
  outside : ∀ S ∈ Retained N 12 F, (c : ℤ) ∉ S →
    (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v

def Width (N L R : ℕ) : ℝ := (L : ℝ)+((N : ℝ)-R)

def Omitted (N c : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)

theorem deleted_affine {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 15853 ≤ N) (hF : Legal (Ground N) F) : (Deleted N 12 F).card ≤ 144*N+1296 := by
  have hsub := actual_deleted_subset N 12 F
  have hlegal : Legal (Ground N) (Deleted N 12 F) :=
    ⟨fun S hS => hF.1 S (hsub hS), fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
  have hbad : ∀ S ∈ Deleted N 12 F, ¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp hS).2.1
  have hdense : ∀ S ∈ Deleted N 12 F, N < 12*S.card :=
    fun S hS => (Finset.mem_filter.mp hS).2.2
  have hb := DenseDeletion208.actual_dense_all_pair_budget (by decide : 0 < 12)
    (by omega : 12 < N) hlegal hbad hdense
  norm_num at hb
  by_contra hh
  have hl : 144*(N : ℝ)+1297 ≤ (Deleted N 12 F).card := by
    exact_mod_cast (by omega : 144*N+1297 ≤ (Deleted N 12 F).card)
  have hn : (15853 : ℝ) ≤ N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ (N : ℝ)-12 by linarith only [hn])
  nlinarith only [hb, hm, hn]

theorem omitted_affine {N c : ℕ} {F : Finset (Finset ℤ)}
    (hN : 15853 ≤ N) (hF : Legal (Ground N) F) : (Omitted N c F).card ≤ 144*N+1296 :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (deleted_affine hN hF)

theorem avoiding_eq_omitted {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) :
    F.filter (fun S => ¬IsAP S ∧ c ∉ S) = TerminalDeficit51.OmittedAvoiders N 12 F c := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSF, hbad, hcS⟩ := Finset.mem_filter.mp hS
    have hd : S ∈ Deleted N 12 F := by
      by_contra hnot
      exact hcS (hroot S (Finset.mem_sdiff.mpr ⟨hSF, hnot⟩) hbad)
    exact Finset.mem_filter.mpr ⟨hd, hcS⟩
  · intro hS
    obtain ⟨hSD, hcS⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨actual_deleted_subset N 12 F hSD,
      (Finset.mem_filter.mp hSD).2.1, hcS⟩

theorem family_partition {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) :
    (RootCrooked F c).card+(TerminalDeficit51.OmittedAvoiders N 12 F c).card+
      (F.filter IsAP).card = F.card := by
  let C := F.filter fun S => ¬IsAP S
  have h1 : C.filter (fun S => c ∈ S) = RootCrooked F c := by
    ext S
    simp only [C, RootCrooked, Finset.mem_filter]
    tauto
  have h2 : C.filter (fun S => ¬c ∈ S) = TerminalDeficit51.OmittedAvoiders N 12 F c := by
    rw [← avoiding_eq_omitted hroot]
    ext S
    simp only [C, Finset.mem_filter]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := C) (fun S => c ∈ S)
  rw [h1, h2] at hc
  have hf := Finset.card_filter_add_card_filter_not (s := F) IsAP
  change (F.filter IsAP).card+C.card = F.card at hf
  omega

theorem width_nonnegative {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) : 0 ≤ Width N L R := by
  have hr : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  dsimp only [Width]
  linarith only [hr, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

theorem raw_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start N c L R F P T)
    (hN : 19 ≤ N) (hhi : N ≤ 642498) (hc : Caps LogCap HCap N)
    (hE : ((Omitted N c F).card : ℝ) ≤ alpha*N+beta*Width N L R+constant) :
    RawProfile N L (Width N L R) (HCap+433/100+alpha) (HCap+beta) (872+constant) := by
  have hr := GenericRecovery291012.actual_original_raw_profile_local hN (by omega : N ≤ 720896)
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α := ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  change ((TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)).card : ℝ) ≤ _ at hE
  dsimp only [RawProfile, Coeff, Width, CovarianceFamily214.MiddleCost, LocalRecovery208.GeometryCost] at *
  nlinarith only [hr, hE, hnpaid, hwpaid]

theorem coarse_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) (hN : 291012 ≤ N) (hhi : N ≤ 642498)
    (hc : Caps LogCap HCap N) : RawProfile N L (Width N L R) CoarseA HCap 2168 := by
  have he : ((Omitted N c F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast omitted_affine (by omega : 15853 ≤ N) g.legal
  have hp := raw_profile (alpha := 144) (beta := 0) (constant := 1296) g
    (by omega : 19 ≤ N) hhi hc (by simpa only [zero_mul, add_zero] using he)
  convert hp using 1 <;> norm_num [CoarseA, HCap, LogCap]

#print axioms deleted_affine
#print axioms omitted_affine
#print axioms avoiding_eq_omitted
#print axioms family_partition
#print axioms width_nonnegative
#print axioms raw_profile
#print axioms coarse_profile
end
end JSP233.RootModel291012
