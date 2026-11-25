module

public import Erdos272.Capacity.N88404.SieveCapacity88404
public import Erdos272.Capacity.N88404.SieveClassBounds88404
public import Erdos272.Counting.N88404.APTailSeven88404

@[expose] public section

namespace JSP233.SevenShadow88404
open StarCompletion APGeometry IntrinsicTriples208 HarmonicAbel29 APShadowCapacity16858
open APClasses88404 SieveConstants88404 SieveClassBounds88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem actual_joint {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 1000 ≤ N) (hg : 0 < g) (hcap : 3*g*((N : ℝ)-1) ≤ 1)
    (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800+3*g : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N+
        Alpha 1*g*((N : ℝ)-1)^3+1/(432*(Alpha 1*g)^2) := by
  let n : ℝ := (N : ℝ)-1
  let R : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(p : ℝ)
  let Q : ℝ := ∑ p ∈ Selected, (1 : ℝ)/(4*(p : ℝ)^2)
  let c := fun p => ((StepAP F p).card : ℝ)
  let s := fun p => ((APShadow (StepAP F p)).card : ℝ)
  have hu := unit_bound (by omega : 1 ≤ N) hg hF
  change c 1-6*g*Alpha 1*s 1 ≤ (1+g)*n+1/(432*(g*Alpha 1)^2) at hu
  have hsum : (∑ p ∈ Selected, c p)-6*g*(∑ p ∈ Selected, Alpha p*s p) ≤
      (1+g)*n*R+n^2*Q-g*n^3*(1-Alpha 1) := by
    exact selected_sum (by omega : 1 ≤ N) hg hcap hF
  have hc := SieveCapacity88404.actual_capacity hN hF
  have hcg := mul_le_mul_of_nonneg_left hc hg.le
  have ha := APTailSeven88404.actual_AP_count (by omega : 13 ≤ N) hF
  have hnot : 1 ∉ Selected := by norm_num [Selected]
  rw [Steps, Finset.sum_insert hnot] at ha hcg
  change ((F.filter IsAP).card : ℝ) ≤ c 1+(∑ p ∈ Selected, c p)+
    (129/800-Q)*(N : ℝ)^2+(N : ℝ)*(Harmonic N-1-R)+1 at ha
  change g*(6*(∑ S ∈ F, ((Pool S).card : ℝ))+
    6*(Alpha 1*s 1+(∑ p ∈ Selected, Alpha p*s p))) ≤
      g*(n^3-n+3*(N : ℝ)^2) at hcg
  have hn : 0 ≤ n := by
    have hh : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    dsimp only [n]
    linarith only [hh]
  have hR : 0 ≤ R := Finset.sum_nonneg (fun p _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun p _ => by positivity)
  have hgn0 := mul_nonneg hg.le hn
  have hgn : g*n ≤ 1 := by change 3*g*n ≤ 1 at hcap; nlinarith only [hcap, hgn0]
  have hlin := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgn) hR
  have hsq : n^2 ≤ (N : ℝ)^2 := by dsimp only [n]; nlinarith only [hn]
  have hquad := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) hQ
  have hnN : n = (N : ℝ)-1 := rfl
  change _ ≤ (129/800+3*g : ℝ)*(N : ℝ)^2+(N : ℝ)*Harmonic N+
    Alpha 1*g*n^3+1/(432*(Alpha 1*g)^2)
  have hfee : 1/(432*(g*Alpha 1)^2) = 1/(432*(Alpha 1*g)^2) := by rw [mul_comm g]
  rw [hfee] at hu
  rw [hnN] at hu hsum hcg hlin hquad ⊢
  nlinarith only [hu, hsum, ha, hcg, hlin, hquad]

#print axioms actual_joint
end
end JSP233.SevenShadow88404
