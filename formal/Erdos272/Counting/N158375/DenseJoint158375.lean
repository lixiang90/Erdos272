module

public import Erdos272.Resources.N158375.DensePool158375
public import Erdos272.Global.DenseDeletion40
public import Erdos272.Resources.SevenFamily208
public import Erdos272.Arithmetic.N200000.ExactResponse200000

@[expose] public section

namespace JSP233.DenseJoint158375
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_deleted_pool {N : ℕ} {F : Finset (Finset ℤ)}
    (hlo : 15000 ≤ N) (hhi : N ≤ 2^18) (hF : Legal (Ground N) F)
    {S : Finset ℤ} (hS : S ∈ Deleted N 12 F) :
    180200 ≤ (Pool S).card := by
  obtain ⟨hSF, hbad, hdense⟩ := Finset.mem_filter.mp hS
  exact DensePool158375.actual_large_member hhi (hF.1 S hSF) hbad (by omega)

theorem actual_deleted_payment {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hlo : 15000 ≤ N) (hhi : N ≤ 2^18) (hF : Legal (Ground N) F)
    (hg : 0 ≤ g) (hpay : 1 ≤ 6*g*180200) :
    ((Deleted N 12 F).card : ℝ) ≤
      6*g*(∑ S ∈ Deleted N 12 F, ((Pool S).card : ℝ)) := by
  have hpoint : ∀ S ∈ Deleted N 12 F, (1 : ℝ) ≤ 6*g*((Pool S).card : ℝ) := by
    intro S hS
    have hp : (180200 : ℝ) ≤ ((Pool S).card : ℝ) := by
      exact_mod_cast actual_deleted_pool hlo hhi hF hS
    exact hpay.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  calc
    ((Deleted N 12 F).card : ℝ) = ∑ _S ∈ Deleted N 12 F, (1 : ℝ) := by simp
    _ ≤ ∑ S ∈ Deleted N 12 F, 6*g*((Pool S).card : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = 6*g*(∑ S ∈ Deleted N 12 F, ((Pool S).card : ℝ)) := by
      rw [Finset.mul_sum]

theorem actual_sparse_disjoint_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) : Disjoint A (Deleted N 12 F) := by
  apply Finset.disjoint_left.mpr
  intro S hSA hSD
  have hdense := (Finset.mem_filter.mp hSD).2.2
  have hs := hsparse S hSA
  omega

theorem actual_inner_payment_with_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    {g Q : ℝ} (hlo : 15000 ≤ N) (hhi : N ≤ 2^18)
    (hF : Legal (Ground N) F) (hAF : A ⊆ F)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hg : 0 ≤ g)
    (hpay : 1 ≤ 6*g*180200)
    (hinner : (A.card : ℝ) ≤ 6*g*(∑ S ∈ A, ((Pool S).card : ℝ))+Q) :
    (A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      6*g*(∑ S ∈ F, ((Pool S).card : ℝ))+Q := by
  have hd := actual_deleted_payment hlo hhi hF hg hpay
  have hdis := actual_sparse_disjoint_deleted (F := F) hsparse
  have hm := SourceFees208.pool_sum_subset
    (Finset.union_subset hAF (actual_deleted_subset N 12 F))
  rw [Finset.sum_union hdis] at hm
  have hscaled := mul_le_mul_of_nonneg_left hm (show 0 ≤ 6*g by positivity)
  nlinarith only [hinner, hd, hscaled]

theorem actual_unit_source_with_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    {g u eta light : ℝ} (hlo : 15000 ≤ N) (hhi : N ≤ 2^18)
    (hF : Legal (Ground N) F) (hAF : A ⊆ F)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hg : 0 ≤ g)
    (hpay : 1 ≤ 6*g*180200)
    (hfee : SevenFamily208.UnitNearObligation N A g u eta light) :
    (A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      6*g*(∑ S ∈ F, ((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light := by
  have hi := SevenFamily208.actual_unit_source (le_refl A) hg hfee
  have h := actual_inner_payment_with_deleted hlo hhi hF hAF hsparse hg hpay
    (Q := u*(N : ℝ)^2+eta*N+light) (by simpa only [add_assoc] using hi)
  simpa only [add_assoc] using h

theorem actual_AP_inner_with_deleted {N : ℕ} {A F : Finset (Finset ℤ)}
    {g Q : ℝ} (hlo : 15000 ≤ N) (hhi : N ≤ 2^18)
    (hF : Legal (Ground N) F) (hAF : A ⊆ F)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hg : 0 < g)
    (hpay : 1 ≤ 6*g*180200)
    (hinner : (A.card : ℝ) ≤ 6*g*(∑ S ∈ A, ((Pool S).card : ℝ))+Q) :
    ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (129/800 : ℝ)*(N : ℝ)^2+g*((N-1 : ℕ) : ℝ)^3+
        1/(432*g^2)+(N : ℝ)*Harmonic N+Q := by
  have hi := actual_inner_payment_with_deleted hlo hhi hF hAF hsparse hg.le hpay hinner
  have hj := ExactResponse200000.actual_joint_exact (by omega : 2 ≤ N) hg hF
  linarith only [hi, hj]

theorem actual_flat_AP_deleted {N : ℕ} {F : Finset (Finset ℤ)}
    (hlo : 15000 ≤ N) (hhi : N ≤ 179999) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (329/800 : ℝ)*(N : ℝ)^2+(Harmonic N-1/2)*N+1/4 := by
  have hx : 0 < (N : ℝ)-1 := by exact_mod_cast (show 0 < (N : ℤ)-1 by omega)
  have hcap : (N : ℝ)-1 ≤ 180200 := by
    have h : (N : ℝ) ≤ 179999 := by exact_mod_cast hhi
    linarith only [h]
  have hg : 0 < 1/(6*((N : ℝ)-1)) := by positivity
  have hpay : 1 ≤ 6*(1/(6*((N : ℝ)-1)))*180200 := by
    have he : 6*(1/(6*((N : ℝ)-1)))*180200 = 180200/((N : ℝ)-1) := by
      field_simp [hx.ne']
      <;> ring
    rw [he]
    exact (le_div_iff₀ hx).mpr (by simpa using hcap)
  have hd := actual_deleted_payment hlo (by omega : N ≤ 2^18) hF hg.le hpay
  have hm := SourceFees208.pool_sum_subset (actual_deleted_subset N 12 F)
  have hscaled := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 6*(1/(6*((N : ℝ)-1))) by positivity)
  have hj := ExactResponse200000.actual_joint_exact (by omega : 2 ≤ N) hg hF
  have hcast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hj
  have he : (1/(6*((N : ℝ)-1)))*((N : ℝ)-1)^3+
      1/(432*(1/(6*((N : ℝ)-1)))^2) = (1/4 : ℝ)*((N : ℝ)-1)^2 := by
    field_simp [hx.ne']
    <;> ring
  nlinarith only [hd, hj, hscaled, he]

#print axioms actual_deleted_pool
#print axioms actual_deleted_payment
#print axioms actual_sparse_disjoint_deleted
#print axioms actual_inner_payment_with_deleted
#print axioms actual_unit_source_with_deleted
#print axioms actual_AP_inner_with_deleted
#print axioms actual_flat_AP_deleted
end
end JSP233.DenseJoint158375
