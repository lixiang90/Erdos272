import Erdos272.Global.RootBranch112
import Erdos272.Counting.NearFarJoint113

/-! Fully paid actual common-Small root branch.

The minimum actual omitter and its scale are chosen once.  All actual avoiders
are then repartitioned at that same scale, with the full new Far price and the
full Near linear error.  No assumption on B<=beta or on an AP-only omitter
family is made, and all root-bearing Large members remain in RootPart.
-/
namespace JSP233.RootPaid113
open StarCompletion NearAP36 NearWhole112 NearFarJoint113 RootBranch112 RootEnvelope112
open scoped Classical BigOperators
noncomputable section

theorem actual_root_paid_budget
    {N r K J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4 ≤ N) (hr : 2 ≤ r) (hK : 0 < K) (hNJ : N < 2 ^ J)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬ IsAP S)
    (hsize : ∀ S ∈ F, r * S.card ≤ N)
    (hsmall : ∀ S ∈ F, S.card ≤ 3 * K → c ∈ S)
    (homitter : ∃ T ∈ F, c ∉ T) :
    (F.card : ℝ) / (N : ℝ) ^ 2 ≤
      max ((6 * (K : ℝ) / N) + (Nu K + G N K))
        (((2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2)) +
          (6 * (K : ℝ) / N) * (Nu K + G N K) /
            ((2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2))) + Eta N J := by
  obtain ⟨T, hTV, h, hlo, hhi, hlow⟩ := actual_first_omitter_scale hK hsmall homitter
  obtain ⟨hTF, hTc⟩ := Finset.mem_filter.mp hTV
  have hroot := actual_root_normalized_min (L := 3 * K) (h := h)
    hN hr hlegal hbad hsize hTF hTc (by
      dsimp only [Scale] at hhi
      nlinarith only [hhi])
  have hlinear : 2 * ((3 * K : ℕ) : ℝ) / (N : ℝ) = 6 * (K : ℝ) / N := by
    push_cast
    ring
  rw [hlinear] at hroot
  have hVF : Avoiders F c ⊆ F := Finset.filter_subset _ _
  have hVL : Legal (Ground N) (Avoiders F c) :=
    ⟨fun S hS => hlegal.1 S (hVF hS),
      fun S hS U hU he => hlegal.2 S (hVF hS) U (hVF hU) he⟩
  have hk : 0 < Scale K h := by unfold Scale; positivity
  have hav := NearFarJoint113.actual_whole_normalized hVL hk (by omega) hNJ
    (fun S hS => hbad S (hVF hS)) hlow
  rw [nu_scale] at hav
  have hg := g_scale_le (N := N) hK h
  have havoid : ((Avoiders F c).card : ℝ) / (N : ℝ) ^ 2 ≤
      Nu K / (2 : ℝ) ^ h + G N K / ((2 : ℝ) ^ h) ^ 3 + Eta N J := by
    have hpow : (2 : ℝ) ^ (3 * h) = ((2 : ℝ) ^ h) ^ 3 := by
      rw [Nat.mul_comm 3 h, pow_mul]
    rw [hpow] at hg
    linarith
  have hβ : 0 < (2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    apply div_pos (by linarith) (by positivity)
  exact root_partition_bound_of_estimates hβ (by unfold Nu; positivity)
    (by unfold G; positivity) (one_le_pow₀ (by norm_num)) hroot havoid

theorem actual_root_paid_budget_explicit
    {N r K J : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4 ≤ N) (hr : 2 ≤ r) (hK : 0 < K) (hNJ : N < 2 ^ J)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬ IsAP S)
    (hsize : ∀ S ∈ F, r * S.card ≤ N)
    (hsmall : ∀ S ∈ F, S.card ≤ 3 * K → c ∈ S)
    (homitter : ∃ T ∈ F, c ∉ T) :
    (F.card : ℝ) / (N : ℝ) ^ 2 ≤
      max ((6 * (K : ℝ) / N) +
          ((2303 / 200 : ℝ) / K + 2 * (N : ℝ) / ((FarJoint113.Mass K : ℝ) * FarJoint113.Cutoff K)))
        (((2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2)) +
          (6 * (K : ℝ) / N) *
            ((2303 / 200 : ℝ) / K + 2 * (N : ℝ) / ((FarJoint113.Mass K : ℝ) * FarJoint113.Cutoff K)) /
            ((2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2))) + (7 / 2 : ℝ) * J ^ 2 / N := by
  exact actual_root_paid_budget hN hr hK hNJ hlegal hbad hsize hsmall homitter

#print axioms actual_root_paid_budget
#print axioms actual_root_paid_budget_explicit

end
end JSP233.RootPaid113
