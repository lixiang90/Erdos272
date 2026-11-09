module

public import Erdos272.Resources.APJoint208

@[expose] public section

/-! Discrete scalar support for the actual unit-AP shadow response.
No integral or asymptotic theorem is used. These declarations do not yet
assert the endpoint encoding of an actual interval family. -/
namespace JSP233.UnitShadowScalar218
open StarCompletion IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem bounded_column_moment (n : ℕ) (f : ℕ → ℝ) (R : ℝ)
    (_hR : 0 ≤ R) (hf : ∀ i < n, 0 ≤ f i ∧ f i ≤ R) :
    (∑ i ∈ Finset.range n, f i)^2 ≤
      R * ∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1) * f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hn := hf n (by omega)
    have hs : (∑ i ∈ Finset.range n, f i) ≤ (n : ℝ) * R := by
      calc
        _ ≤ ∑ _i ∈ Finset.range n, R :=
          Finset.sum_le_sum (fun i hi => (hf i (by have := Finset.mem_range.mp hi; omega)).2)
        _ = _ := by simp
    have hsr := mul_nonneg (sub_nonneg.mpr hs) hn.1
    have hrr := mul_nonneg hn.1 (sub_nonneg.mpr hn.2)
    simp only [Finset.sum_range_succ]
    nlinarith only [hp, hsr, hrr]

theorem quartic_identity (a y : ℝ) :
    a^4 - 4*a*y^3 + 3*y^4 =
      (a-y)^2 * (a^2+2*a*y+3*y^2) := by ring

theorem side_cube_payment {a y X : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hX : 0 ≤ X) (hm : y^4 ≤ 2*a*X) :
    4*y^3 ≤ a^3+6*X := by
  by_cases haz : a = 0
  · have hy4 : y^4 = 0 := by
      apply le_antisymm
      · simpa only [haz, mul_zero, zero_mul] using hm
      · positivity
    have hyz : y = 0 := eq_zero_of_pow_eq_zero hy4
    simp only [haz, hyz, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_add]
    positivity
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hs : 0 ≤ a^4-4*a*y^3+3*y^4 := by
      rw [quartic_identity]
      positivity
    have hp : 0 ≤ a*(a^3+6*X-4*y^3) := by
      nlinarith only [hs, hm]
    have hh := nonneg_of_mul_nonneg_right hp hap
    linarith only [hh]

theorem discrete_shadow_mass {L R K y X Y h : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hy : 0 ≤ y)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : y^2 = K)
    (hmX : K^2 ≤ 2*R*X) (hmY : K^2 ≤ 2*L*Y)
    (hshadow : 6*h = L^3+R^3-L-R+6*(X+Y)) :
    8*y^3 ≤ 6*h+L+R := by
  have hK2 : y^4 = K^2 := by
    calc
      _ = (y^2)^2 := by ring
      _ = _ := by rw [hK]
  have hx := side_cube_payment hR hy hX (hK2 ▸ hmX)
  have hy' := side_cube_payment hL hy hY (hK2 ▸ hmY)
  linarith only [hx, hy', hshadow]

theorem cubic_tangent_identity (N y : ℝ) :
    y^3-3*N*y^2/4+N^3/16 = (y-N/2)^2*(y+N/4) := by ring

theorem zero_main_response {N y g : ℝ}
    (hN : 0 ≤ N) (hy : 0 ≤ y) (hg : 0 ≤ g)
    (ht : 6*g*N ≤ 1) (hyN : y^2 ≤ N^2/4) :
    y^2+g*N^3-8*g*y^3 ≤ N^2/4 := by
  have hs : 0 ≤ y^3-3*N*y^2/4+N^3/16 := by
    rw [cubic_tangent_identity]
    positivity
  have hsg := mul_nonneg (show 0 ≤ 8*g by positivity) hs
  have hc := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hyN)
  nlinarith only [hsg, hc]

theorem zero_joint_response {N y u H h g : ℝ}
    (hN : 0 ≤ N) (hy : 0 ≤ y) (hg : 0 ≤ g)
    (ht : 6*g*N ≤ 1) (hyN : y^2 ≤ N^2/4)
    (hu : u ≤ y^2+N) (hmass : 8*y^3 ≤ 6*h+N)
    (hcapacity : 6*H+6*h ≤ N^3) :
    u+6*g*H ≤ N^2/4+N+g*N := by
  have hm : 6*H ≤ N^3-8*y^3+N := by linarith only [hmass, hcapacity]
  have hmg := mul_le_mul_of_nonneg_left hm hg
  have hmain := zero_main_response hN hy hg ht hyN
  nlinarith only [hu, hmg, hmain]

def APShadow (U : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  U.biUnion fun P => P.powersetCard 3

theorem actual_AP_family_capacity {Ω : Finset ℤ} {F U : Finset (Finset ℤ)}
    (hF : Legal Ω F) (hUF : U ⊆ F) (hAP : ∀ P ∈ U, IsAP P) :
    (∑ S ∈ F, (Pool S).card) + (APShadow U).card ≤ Ω.card.choose 3 := by
  have hd : Disjoint (F.biUnion Pool) (APShadow U) := by
    apply Finset.disjoint_left.mpr
    intro Q hQ hQU
    obtain ⟨P, hPU, hQP⟩ := Finset.mem_biUnion.mp hQU
    exact Finset.disjoint_left.mp
      (disjoint_actual_AP hF (hUF hPU) (hAP P hPU)) hQ hQP
  have hs : APShadow U ⊆ Ω.powersetCard 3 := by
    intro Q hQ
    obtain ⟨P, hPU, hQP⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQP
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans (hF.1 P (hUF hPU)), hcard⟩
  have hsub : F.biUnion Pool ∪ APShadow U ⊆ Ω.powersetCard 3 :=
    Finset.union_subset (union_subset_triples hF.1) hs
  calc
    _ = (F.biUnion Pool).card + (APShadow U).card := by
      rw [Finset.card_biUnion (pools_pairwise_disjoint hF)]
    _ = (F.biUnion Pool ∪ APShadow U).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (Ω.powersetCard 3).card := Finset.card_le_card hsub
    _ = _ := Finset.card_powersetCard 3 Ω

#print axioms bounded_column_moment
#print axioms quartic_identity
#print axioms side_cube_payment
#print axioms discrete_shadow_mass
#print axioms cubic_tangent_identity
#print axioms zero_main_response
#print axioms zero_joint_response
#print axioms actual_AP_family_capacity
end
end JSP233.UnitShadowScalar218
