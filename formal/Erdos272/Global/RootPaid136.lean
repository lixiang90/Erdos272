import Erdos272.Global.RootBranch112
import Erdos272.Counting.NearFar136
namespace JSP233.RootPaid136
open StarCompletion NearAP36 NearWhole112 NearFar136 RootBranch112 RootEnvelope112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_root_paid_budget {N r K:ℕ} {F:Finset (Finset ℤ)} {c:ℤ}
    (hN:63≤N) (hhiN:N≤74320000) (hr:11≤r) (hK:600≤K)
    (hlegal:Legal (Ground N) F) (hbad:∀S∈F,¬IsAP S)
    (hsize:∀S∈F,r*S.card≤N)
    (hsmall:∀S∈F,S.card≤3*K→c∈S) (homitter:∃T∈F,c∉T) :
    (F.card:ℝ)/(N:ℝ)^2≤
      max (6*(K:ℝ)/N+(Nu K+G N K))
        ((2*(r:ℝ)-1)/(2*(r:ℝ)^2)+
          (6*(K:ℝ)/N)*(Nu K+G N K)/((2*(r:ℝ)-1)/(2*(r:ℝ)^2)))+Eta N := by
  obtain ⟨T, hTV, h, hlo, hhi, hlow⟩ := actual_first_omitter_scale (by omega : 0<K) hsmall homitter
  obtain ⟨hTF, hTc⟩ := Finset.mem_filter.mp hTV
  have hroot := actual_root_normalized_min (L := 3 * K) (h := h)
    (by omega : 4≤N) (by omega : 2≤r) hlegal hbad hsize hTF hTc (by
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
  have hk : 600≤Scale K h := hK.trans (Nat.le_mul_of_pos_left K (by positivity))
  have hupper : ∀S∈F,11*S.card≤N := fun S hS =>
    (Nat.mul_le_mul_right S.card hr).trans (hsize S hS)
  have hav := NearFar136.actual_whole_normalized hVL hk hN hhiN
    (fun S hS => hbad S (hVF hS)) (fun S hS => hupper S (hVF hS)) hlow
  rw [nu_scale] at hav
  have hg := g_scale_le (N := N) (by omega : 0<K) h
  have havoid : ((Avoiders F c).card : ℝ) / (N : ℝ) ^ 2 ≤
      Nu K / (2 : ℝ) ^ h + G N K / ((2 : ℝ) ^ h) ^ 3 + Eta N := by
    have hpow : (2 : ℝ) ^ (3 * h) = ((2 : ℝ) ^ h) ^ 3 := by
      rw [Nat.mul_comm 3 h, pow_mul]
    rw [hpow] at hg
    linarith
  have hβ : 0 < (2 * (r : ℝ) - 1) / (2 * (r : ℝ) ^ 2) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast (show 2≤r by omega)
    apply div_pos (by linarith) (by positivity)
  have hnu : 0≤Nu K := div_nonneg (by norm_num [FiniteNear136.NuNumerator]) (Nat.cast_nonneg K)
  exact root_partition_bound_of_estimates hβ hnu
    (by unfold G; positivity) (one_le_pow₀ (by norm_num)) hroot havoid

#print axioms actual_root_paid_budget
end
end JSP233.RootPaid136
