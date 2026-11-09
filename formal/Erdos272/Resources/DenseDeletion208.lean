module

public import Erdos272.Global.DenseDeletion40
public import Erdos272.Counting.TerminalDeficit51
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! All ordered pairs of each actual dense crooked member are counted.
The capacity at each ground pair is inherited from the two-point AP anchor
theorem.  In particular, the result concerns the original `Deleted` filter. -/
namespace JSP233.DenseDeletion208
open StarCompletion DenseDeletion40 AnchorCompletion38
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_all_pair_capacity {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) {a b : ℤ} (hab : a ≠ b) :
    (F.filter (fun S => a ∈ S ∧ b ∈ S)).card ≤ N - 2 := by
  let D := F.filter (fun S => a ∈ S ∧ b ∈ S)
  by_cases hD : D.Nonempty
  · have hDF : D ⊆ F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) D :=
      ⟨fun S hS => hF.1 S (hDF hS),
       fun S hS T hT hST => hF.2 S (hDF hS) T (hDF hT) hST⟩
    have hb := actual_two_point_crooked_ground_capacity (Ground N) D a b hab hD
      hlegal (fun S hS => hbad S (hDF hS))
      (fun S hS => (Finset.mem_filter.mp hS).2.1)
      (fun S hS => (Finset.mem_filter.mp hS).2.2)
    rw [ground_card] at hb
    change D.card ≤ N - 2
    omega
  · have he : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    change D.card ≤ N - 2
    simp [he]

theorem actual_dense_all_pair_budget {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0 < r) (hN : r < N) (hF : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hdense : ∀ S ∈ F, N < r * S.card) :
    (F.card : ℝ) * ((N : ℝ) - r) ≤
      (r : ℝ)^2 * ((N : ℝ) - 1) * ((N : ℝ) - 2) := by
  let rel : Finset ℤ → ℤ × ℤ → Prop := fun S p => p.1 ∈ S ∧ p.2 ∈ S
  have hNr : (r : ℝ) < N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have habove : ∀ S ∈ F,
      (Ground N).offDiag.bipartiteAbove rel S = S.offDiag := by
    intro S hS
    ext p
    simp only [Finset.mem_bipartiteAbove, Finset.mem_offDiag, rel]
    constructor
    · rintro ⟨⟨_, _, hne⟩, ha, hb⟩
      exact ⟨ha, hb, hne⟩
    · rintro ⟨ha, hb, hne⟩
      exact ⟨⟨hF.1 S hS ha, hF.1 S hS hb, hne⟩, ha, hb⟩
  have hcard (S : Finset ℤ) : (S.offDiag.card : ℝ) = (S.card : ℝ)^2 - S.card := by
    rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  have hsupply : ∀ S ∈ F,
      (N : ℝ) * ((N : ℝ) - r) / (r : ℝ)^2 ≤
        ((Ground N).offDiag.bipartiteAbove rel S).card := by
    intro S hS
    rw [habove S hS, hcard]
    have hd : (N : ℝ) ≤ (r : ℝ) * S.card := by
      exact_mod_cast (hdense S hS).le
    have hc0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hleft : 0 ≤ (N : ℝ) - r := sub_nonneg.mpr hNr.le
    have hright : (N : ℝ) - r ≤ (r : ℝ) * ((S.card : ℝ) - 1) := by linarith
    have hp := mul_le_mul hd hright hleft (by positivity : (0 : ℝ) ≤ (r : ℝ) * S.card)
    apply (div_le_iff₀ (sq_pos_of_pos hrR)).mpr
    nlinarith only [hp]
  have hcapacity : ∀ p ∈ (Ground N).offDiag,
      ((F.bipartiteBelow rel p).card : ℝ) ≤ (N : ℝ) - 2 := by
    intro p hp
    have hne := (Finset.mem_offDiag.mp hp).2.2
    have hc := actual_all_pair_capacity hF hbad hne
    have hcR : ((F.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by
      exact_mod_cast hc
    simpa only [Finset.bipartiteBelow, rel, Nat.cast_sub hN2, Nat.cast_ofNat] using hcR
  have hd := Finset.card_nsmul_le_card_nsmul (R := ℝ) (r := rel)
    (s := F) (t := (Ground N).offDiag) hsupply hcapacity
  simp only [nsmul_eq_mul] at hd
  rw [hcard, ground_card] at hd
  have hdiv : (F.card : ℝ) * ((N : ℝ) * ((N : ℝ) - r)) / (r : ℝ)^2 ≤
      ((N : ℝ)^2 - N) * ((N : ℝ) - 2) := by
    simpa only [mul_div_assoc] using hd
  have hmul := (div_le_iff₀ (sq_pos_of_pos hrR)).mp hdiv
  have hgoal : (N : ℝ) * ((F.card : ℝ) * ((N : ℝ) - r)) ≤
      (N : ℝ) * ((r : ℝ)^2 * ((N : ℝ) - 1) * ((N : ℝ) - 2)) := by
    nlinarith only [hmul]
  exact (mul_le_mul_iff_right₀ hN0).mp hgoal

theorem actual_deleted11_affine {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 10902 ≤ N) (hF : Legal (Ground N) F) :
    (Deleted N 11 F).card ≤ 121 * N + 968 := by
  have hb := actual_dense_all_pair_budget (r := 11) (by decide) (by omega)
    (actual_deleted_legal hF)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)
  have hn : (10902 : ℝ) ≤ N := by exact_mod_cast hN
  have hstrict : ((Deleted N 11 F).card : ℝ) < 121 * (N : ℝ) + 969 := by
    by_contra hh
    have hge : 121 * (N : ℝ) + 969 ≤ (Deleted N 11 F).card := le_of_not_gt hh
    have hm := mul_le_mul_of_nonneg_right hge (by linarith : (0 : ℝ) ≤ N - 11)
    norm_num at hb
    nlinarith only [hb, hm, hn]
  have hi : (Deleted N 11 F).card < 121 * N + 969 := by exact_mod_cast hstrict
  omega

theorem actual_omitted11_affine {N : ℕ} {F : Finset (Finset ℤ)} (c : ℤ)
    (hN : 10902 ≤ N) (hF : Legal (Ground N) F) :
    (TerminalDeficit51.OmittedAvoiders N 11 F c).card ≤ 121 * N + 968 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (actual_deleted11_affine hN hF)

theorem actual_retained11_affine {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 10902 ≤ N) (hF : Legal (Ground N) F) :
    F.card ≤ (Retained N 11 F).card + 121 * N + 968 := by
  have hb := actual_deleted11_affine hN hF
  have he := actual_deletion_card_identity N 11 F
  omega

theorem actual_retained11_near {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 10902 ≤ N) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
    (N : ℝ)^2 / 2 ≤ (Retained N 11 F).card + 123 * (N : ℝ) := by
  have hb := actual_retained11_affine hN hF
  have hbR : (F.card : ℝ) ≤ (Retained N 11 F).card + 121 * (N : ℝ) + 968 := by
    exact_mod_cast hb
  have hc : N.choose 2 + 1 ≤ F.card := by unfold B at hcard; omega
  have hcR : (N : ℝ) * ((N : ℝ) - 1) / 2 + 1 ≤ F.card := by
    have hh : (N.choose 2 : ℝ) + 1 ≤ F.card := by exact_mod_cast hc
    simpa only [Nat.cast_choose_two] using hh
  have hNR : (10902 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hbR, hcR, hNR]

#print axioms actual_all_pair_capacity
#print axioms actual_dense_all_pair_budget
#print axioms actual_deleted11_affine
#print axioms actual_omitted11_affine
#print axioms actual_retained11_affine
#print axioms actual_retained11_near
end
end JSP233.DenseDeletion208
