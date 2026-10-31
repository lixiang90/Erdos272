import Erdos272.Resources.ResidualSpan208
import Erdos272.Resources.ResidualPool208

namespace JSP233.ResidualOccupancy208
open StarCompletion APGeometry NearAP36 CommonCapacity208 ResidualSpan208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_single_span {N a : ℕ} {S P : Finset ℤ} {d t : ℤ}
    (hground : S ⊆ Ground N) (hP : P ⊆ S) (hAt : APAt d t P)
    (ht : t ∈ P) (hcard : a+1 ≤ P.card) : d*(a : ℤ) ≤ (N : ℤ)-1 := by
  have hPS : P ⊆ Finset.Icc 1 (N : ℤ) := fun x hx =>
    Finset.mem_Icc.mpr ((mem_ground N x).mp (hground (hP hx)))
  have hs := apAt_card_span hAt ⟨t,ht⟩ hPS
  have ha : (a : ℤ) ≤ (P.card : ℤ)-1 := by
    have hc : (a : ℤ)+1 ≤ P.card := by exact_mod_cast hcard
    omega
  have hh := mul_le_mul_of_nonneg_left ha hAt.1.le
  omega

theorem actual_cumulative_occupancy {N a b p : ℕ} {F : Finset (Finset ℤ)}
    {d t : ℤ} (hF : Legal (Ground N) F) (hp : 2 ≤ p)
    (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, APAt d t (core S)) (ht : ∀ S ∈ F, t ∈ core S)
    (hcard : ∀ S ∈ F, a+1 ≤ (core S).card)
    (hmax : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (core S).card)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ)*delta ≤ d)
    (x : ℤ) :
    (F.filter (fun S => x ∈ S \ core S ∧ (S \ core S).card < b)).card ≤
      (if d*(a : ℤ) ≤ (N : ℤ)-1 then 1 else 0)+
      (if d*(Span a b p : ℤ) ≤ (N : ℤ)-1 then 1 else 0) := by
  let H := F.filter (fun S => x ∈ S \ core S ∧ (S \ core S).card < b)
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hH : Legal (Ground N) H := ⟨fun S hS => hF.1 S (hHF hS),
    fun S hS T hT hST => hF.2 S (hHF hS) T (hHF hT) hST⟩
  change H.card ≤ _
  by_cases hsingle : d*(a : ℤ) ≤ (N : ℤ)-1
  · simp only [if_pos hsingle]
    by_cases hpair : d*(Span a b p : ℤ) ≤ (N : ℤ)-1
    · simp only [if_pos hpair]
      exact actual_common_point_card_le_two hH core (fun S hS => hcore S (hHF hS))
        (fun S hS => hAt S (hHF hS)) (fun S hS => ht S (hHF hS))
        (fun S hS => (Finset.mem_filter.mp hS).2.1)
    · simp only [if_neg hpair,add_zero]
      apply Finset.card_le_one.mpr
      intro S hS T hT
      by_contra hST
      obtain ⟨_,hxS,hs⟩ := Finset.mem_filter.mp hS
      obtain ⟨_,hxT,_⟩ := Finset.mem_filter.mp hT
      exact hpair (actual_pair_span hF (hHF hS) (hHF hT) hST hp
        (hcore S (hHF hS)) (hcore T (hHF hT))
        (hAt S (hHF hS)) (hAt T (hHF hT)) (ht S (hHF hS)) (ht T (hHF hT))
        hxS hxT (hcard S (hHF hS)) (hcard T (hHF hT)) hs hproper
        (hmax S (hHF hS)) (hmax T (hHF hT)))
  · have hzero : H=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hsingle (actual_single_span (hF.1 S (hHF hS)) (hcore S (hHF hS)).1
        (hAt S (hHF hS)) (ht S (hHF hS)) (hcard S (hHF hS)))
    rw [hzero]
    exact Nat.zero_le _

#print axioms actual_single_span
#print axioms actual_cumulative_occupancy
end
end JSP233.ResidualOccupancy208
