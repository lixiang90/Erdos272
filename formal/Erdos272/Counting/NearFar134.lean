import Erdos272.Resources.FarCut134
import Erdos272.Counting.NearWhole112

/-! Fully paid actual Near/Far whole-family and rebased tail estimates.
The same complete source family is partitioned anew at each scale.  Linear
Near error is retained in full; it is never divided by the tail scale.
-/
namespace JSP233.NearFar134
open StarCompletion APGeometry NearAP36 NearWhole112 FarCut134
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Nu (K : ℕ) : ℝ := (2303 / 200 : ℝ) / K
def G (N K : ℕ) : ℝ :=
  2 * (N : ℝ) / ((FarCut134.Mass K : ℝ) * FarCut134.Cutoff K)
def Eta (N J : ℕ) : ℝ := (7 / 2 : ℝ) * (J : ℝ) ^ 2 / N

/-- Every actual source, including all Large members, receives one complete
Near/Far payment.  The Far term has no hypothesis left over from geometry. -/
theorem actual_whole_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) (hN : 0 < N) (hJ : N < 2 ^ J)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hsize : ∀ S ∈ F, 3 * K ≤ S.card) :
    (F.card : ℝ) / (N : ℝ) ^ 2 ≤ Nu K + G N K + Eta N J := by
  let H := F.filter (fun S => ¬ HasNearAPCore K S)
  have hsub : H ⊆ F := Finset.filter_subset _ _
  have hHL : Legal (Ground N) H := ⟨fun S hS => hF.1 S (hsub hS),
    fun S hS T hT hne => hF.2 S (hsub hS) T (hsub hT) hne⟩
  have hfar := FarCut134.actual_far_normalized111 hHL hK hN
    (fun S hS => hsize S (hsub hS)) (fun S hS => (Finset.mem_filter.mp hS).2)
  have hwhole := NearWhole112.actual_whole_normalized hF hK hJ hN hbad hsize
  change (H.card : ℝ) / (N : ℝ) ^ 2 ≤ G N K at hfar
  change (F.card : ℝ) / (N : ℝ) ^ 2 ≤ Nu K + Eta N J + (H.card : ℝ) / (N : ℝ) ^ 2 at hwhole
  linarith

/-- Complete actual tail, with no assumption that a previously filtered
family still has an empty kernel or retains a chosen omitter. -/
theorem actual_tail_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) (hN : 0 < N) (hJ : N < 2 ^ J)
    (hbad : ∀ S ∈ F, ¬ IsAP S) :
    ((Tail F K).card : ℝ) / (N : ℝ) ^ 2 ≤ Nu K + G N K + Eta N J := by
  have hsub : Tail F K ⊆ F := Finset.filter_subset _ _
  have hTL : Legal (Ground N) (Tail F K) := ⟨fun S hS => hF.1 S (hsub hS),
    fun S hS T hT hne => hF.2 S (hsub hS) T (hsub hT) hne⟩
  exact actual_whole_normalized hTL hK hN hJ
    (fun S hS => hbad S (hsub hS)) (fun S hS => (Finset.mem_filter.mp hS).2)

theorem scale_cutoff_lower (K h : ℕ) :
    2 ^ h * FarCut134.Cutoff K ≤ FarCut134.Cutoff (Scale K h) := by
  unfold FarCut134.Cutoff
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 70)).mpr
  have hh := Nat.mul_le_mul_left (2 ^ h) (Nat.div_mul_le_self (111 * K) 70)
  simpa only [Scale] using
    (show 2 ^ h * (111 * K / 70) * 70 ≤ 111 * (2 ^ h * K) by nlinarith [hh])

theorem mass_scale_lower {K s : ℕ} (hK : 0 < K) (hs : 1 ≤ s) :
    s ^ 2 * FarCut134.Mass K ≤ FarCut134.Mass (s * K) := by
  have hK2 : 1 ≤ 2 * K := by omega
  have hsK : 1 ≤ 2 * (s * K) := by nlinarith
  have hinner : s * (2 * K - 1) ≤ 2 * (s * K) - 1 := by
    have h1 := Nat.sub_add_cancel hK2
    have h2 := Nat.sub_add_cancel hsK
    have heq : s * (2 * K - 1) + s = 2 * (s * K) := by nlinarith
    omega
  calc
    s ^ 2 * FarCut134.Mass K = (s * K) * (s * (2 * K - 1)) := by
      unfold FarCut134.Mass
      ring
    _ ≤ (s * K) * (2 * (s * K) - 1) := Nat.mul_le_mul_left _ hinner
    _ = FarCut134.Mass (s * K) := rfl

theorem nu_scale (K h : ℕ) : Nu (Scale K h) = Nu K / (2 : ℝ) ^ h := by
  simp only [Nu, Scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Stronger Long mass scales by at least the square of the scale and the
integer cutoff by at least its first power.  Full Far still decays by 1/8. -/
theorem g_scale_le {N K : ℕ} (hK : 0 < K) (h : ℕ) :
    G N (Scale K h) ≤ G N K / (2 : ℝ) ^ (3 * h) := by
  have hs : 1 ≤ 2 ^ h := Nat.succ_le_of_lt (by positivity : 0 < 2 ^ h)
  have hm := mass_scale_lower hK hs
  have ht := scale_cutoff_lower K h
  have hd : (2 ^ h) ^ 3 * (FarCut134.Mass K * FarCut134.Cutoff K) ≤
      FarCut134.Mass (Scale K h) * FarCut134.Cutoff (Scale K h) := by
    calc
      (2 ^ h) ^ 3 * (FarCut134.Mass K * FarCut134.Cutoff K) =
          ((2 ^ h) ^ 2 * FarCut134.Mass K) * (2 ^ h * FarCut134.Cutoff K) := by ring
      _ ≤ FarCut134.Mass (2 ^ h * K) * FarCut134.Cutoff (Scale K h) :=
        Nat.mul_le_mul hm ht
      _ = FarCut134.Mass (Scale K h) * FarCut134.Cutoff (Scale K h) := rfl
  have hdR : ((FarCut134.Mass K : ℝ) * FarCut134.Cutoff K) *
      (2 : ℝ) ^ (3 * h) ≤
      (FarCut134.Mass (Scale K h) : ℝ) * FarCut134.Cutoff (Scale K h) := by
    have hh : (((2 ^ h) ^ 3 * (FarCut134.Mass K * FarCut134.Cutoff K) : ℕ) : ℝ) ≤
        ((FarCut134.Mass (Scale K h) * FarCut134.Cutoff (Scale K h) : ℕ) : ℝ) := by
      exact_mod_cast hd
    push_cast at hh
    have hp : ((2 : ℝ) ^ h) ^ 3 = (2 : ℝ) ^ (3 * h) := by
      rw [← pow_mul, Nat.mul_comm h 3]
    rw [hp] at hh
    calc
      ((FarCut134.Mass K : ℝ) * FarCut134.Cutoff K) * (2 : ℝ) ^ (3 * h) =
          (2 : ℝ) ^ (3 * h) * ((FarCut134.Mass K : ℝ) * FarCut134.Cutoff K) := by ring
      _ ≤ _ := hh
  have hmass : 0 < (FarCut134.Mass K : ℝ) := by exact_mod_cast FarCut134.mass_pos hK
  have hcutN : 0 < FarCut134.Cutoff K := by
    have := (FarCut134.cutoff_arithmetic hK).2.1
    omega
  have hcut : 0 < (FarCut134.Cutoff K : ℝ) := by exact_mod_cast hcutN
  unfold G
  rw [div_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdR

/-- Repartition the same complete original family at Kh, then pay its whole
tail.  Full Eta is retained at every h. -/
theorem actual_scaled_tail_normalized {N K J : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hK : 0 < K) (hN : 0 < N) (hJ : N < 2 ^ J)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (h : ℕ) :
    ((Tail F (Scale K h)).card : ℝ) / (N : ℝ) ^ 2 ≤
      Nu K / (2 : ℝ) ^ h + G N K / (2 : ℝ) ^ (3 * h) + Eta N J := by
  have hk : 0 < Scale K h := by unfold Scale; positivity
  have hh := actual_tail_normalized hF hk hN hJ hbad
  rw [nu_scale] at hh
  have hg := g_scale_le (N := N) hK h
  linarith

#print axioms actual_whole_normalized
#print axioms actual_tail_normalized
#print axioms scale_cutoff_lower
#print axioms mass_scale_lower
#print axioms nu_scale
#print axioms g_scale_le
#print axioms actual_scaled_tail_normalized

end
end JSP233.NearFar134
