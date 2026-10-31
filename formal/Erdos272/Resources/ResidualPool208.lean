import Erdos272.Resources.CoreCleanup208

namespace JSP233.ResidualPool208
open StarCompletion APGeometry NearAP36 CoreCleanup208 CommonCapacity208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_cleaned_capacity {ι : Type*} [DecidableEq ι]
    {Ω : Finset ℤ} {F : Finset (Finset ℤ)} (hF : Legal Ω F)
    (core : Finset ℤ → Finset ℤ) (d : ℤ)
    (hAP : ∀ S ∈ F, ∃ a : ℤ, APAt d a (core S))
    (hne : ∀ S ∈ F, (core S).Nonempty)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (U : Finset ℤ) (hU : ∀ S ∈ F, core S ⊆ U)
    (label : Finset ℤ → ι) (I : Finset ι) (hmap : ∀ S ∈ F, label S ∈ I)
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → label S=label T →
      Disjoint (S \ core S) (T \ core T))
    (E : ℕ) (hE : ∀ S ∈ F, (S \ core S).card ≤ E) :
    ∃ t : ℤ, ∃ G : Finset (Finset ℤ), G ⊆ F ∧
      (∀ S ∈ G, t ∈ core S) ∧
      (∀ S ∈ G, Disjoint (S \ core S) U) ∧
      F.card ≤ G.card+I.card*(U.card+E) ∧
      (∀ x : ℤ, (G.filter (fun S => x ∈ S \ core S)).card ≤ 2) := by
  obtain ⟨t,G,hGF,ht,havoid,hpay⟩ := actual_two_cleanup hF core d hAP hne
    (fun S hS => (hcore S hS).1) U hU label I hmap hdis E hE
  refine ⟨t,G,hGF,ht,havoid,hpay,?_⟩
  intro x
  let H := G.filter (fun S => x ∈ S \ core S)
  have hHF : H ⊆ F := (Finset.filter_subset _ _).trans hGF
  have hHG : H ⊆ G := Finset.filter_subset _ _
  have hH : Legal Ω H := ⟨fun S hS => hF.1 S (hHF hS),
    fun S hS T hT hST => hF.2 S (hHF hS) T (hHF hT) hST⟩
  apply actual_common_point_card_le_two hH core (fun S hS => hcore S (hHF hS))
  · intro S hS
    obtain ⟨a,hAt⟩ := hAP S (hHF hS)
    exact apAt_rebase hAt (ht S (hHG hS))
  · exact fun S hS => ht S (hHG hS)
  · exact fun S hS => (Finset.mem_filter.mp hS).2

theorem incidence_identity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α → Finset β)
    (hsub : ∀ S ∈ F, piece S ⊆ Ω) :
    (∑ S ∈ F, (piece S).card) = ∑ x ∈ Ω, (F.filter (fun S => x ∈ piece S)).card := by
  have hone : ∀ S ∈ F, (piece S).card = ∑ x ∈ Ω, if x ∈ piece S then 1 else 0 := by
    intro S hS
    rw [← Finset.sum_filter]
    have he : Ω.filter (fun x => x ∈ piece S)=piece S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub S hS h,h⟩⟩
    rw [he]
    simp
  calc
    _ = ∑ S ∈ F, ∑ x ∈ Ω, if x ∈ piece S then 1 else 0 := Finset.sum_congr rfl hone
    _ = ∑ x ∈ Ω, ∑ S ∈ F, if x ∈ piece S then 1 else 0 := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]

theorem incidence_capacity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α → Finset β) (c : ℕ)
    (hsub : ∀ S ∈ F, piece S ⊆ Ω)
    (hcap : ∀ x ∈ Ω, (F.filter (fun S => x ∈ piece S)).card ≤ c) :
    (∑ S ∈ F, (piece S).card) ≤ c*Ω.card := by
  rw [incidence_identity F Ω piece hsub]
  have hh := Finset.sum_le_sum hcap
  simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using hh

#print axioms actual_cleaned_capacity
#print axioms incidence_identity
#print axioms incidence_capacity
end
end JSP233.ResidualPool208
