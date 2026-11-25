module

public import Erdos272.Resources.DenseDeletion208

@[expose] public section
namespace JSP233.RootModel291012
open StarCompletion DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false

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

#print axioms deleted_affine
end
end JSP233.RootModel291012
