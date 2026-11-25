module

public import Erdos272.Global.SparseSmall39

@[expose] public section

namespace JSP233.FirstHitCapacity84364
open StarCompletion AnchorCompletion38 SparseSmall39
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def HitBucket (H : Finset (Finset ℤ)) (T : Finset ℤ) (x : ℤ) :
    Finset (Finset ℤ) := H.filter (fun S => Hit T S=x)

theorem hit_bucket_spec {H : Finset (Finset ℤ)} {T S : Finset ℤ} {x : ℤ}
    (hhit : ∀ S ∈ H, (S∩T).Nonempty) (hS : S∈HitBucket H T x) :
    x∈S∩T ∧ Disjoint S (Earlier T x) := by
  obtain ⟨hSH, he⟩ := Finset.mem_filter.mp hS
  have hs := hit_spec (hhit S hSH)
  refine ⟨he ▸ hs.1, ?_⟩
  apply Finset.disjoint_left.mpr
  intro y hyS hyE
  obtain ⟨hyT, hyx⟩ := Finset.mem_filter.mp hyE
  have hh := hs.2 y (Finset.mem_inter.mpr ⟨hyS, hyT⟩)
  rw [he] at hh
  omega

theorem actual_bucket_capacity {Ω D T : Finset ℤ} {H : Finset (Finset ℤ)} {u x : ℤ}
    (hlegal : Legal Ω H) (hbad : ∀ S ∈ H, ¬IsAP S)
    (hu : u∈Ω) (hD : D⊆Ω) (hT : T⊆Ω)
    (huD : u∉D) (huT : u∉T) (hDT : Disjoint D T)
    (hroot : ∀ S ∈ H, u∈S) (havoid : ∀ S ∈ H, Disjoint S D)
    (hhit : ∀ S ∈ H, (S∩T).Nonempty) (hx : x∈T) :
    (HitBucket H T x).card+D.card+(Earlier T x).card+2≤Ω.card := by
  let C := HitBucket H T x
  let R := D∪Earlier T x
  let U := Ω\R
  have hCF : C⊆H := Finset.filter_subset _ _
  have hEu : u∉Earlier T x := fun hh => huT (Finset.mem_filter.mp hh).1
  have hxD : x∉D := fun hh => Finset.disjoint_left.mp hDT hh hx
  have hEx : x∉Earlier T x := by simp only [Earlier, Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
  have huU : u∈U := Finset.mem_sdiff.mpr ⟨hu, by simp only [R, Finset.mem_union]; tauto⟩
  have hxU : x∈U := Finset.mem_sdiff.mpr ⟨hT hx, by simp only [R, Finset.mem_union]; tauto⟩
  have hux : u≠x := fun he => huT (he.symm ▸ hx)
  have hLC : Legal U C := by
    constructor
    · intro S hS y hy
      apply Finset.mem_sdiff.mpr
      refine ⟨hlegal.1 S (hCF hS) hy, ?_⟩
      intro hyR
      rcases Finset.mem_union.mp hyR with hyD | hyE
      · exact Finset.disjoint_left.mp (havoid S (hCF hS)) hy hyD
      · exact Finset.disjoint_left.mp (hit_bucket_spec hhit hS).2 hy hyE
    · intro S hS V hV hne
      exact hlegal.2 S (hCF hS) V (hCF hV) hne
  have hcap : C.card+2≤U.card := by
    by_cases hC : C.Nonempty
    · exact actual_two_point_crooked_ground_capacity U C u x hux hC hLC
        (fun S hS => hbad S (hCF hS))
        (fun S hS => hroot S (hCF hS))
        (fun S hS => (Finset.mem_inter.mp (hit_bucket_spec hhit hS).1).1)
    · have hCe : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      have hpair : ({u,x} : Finset ℤ)⊆U := by
        intro y hy
        rcases Finset.mem_insert.mp hy with he | hy
        · rw [he]
          exact huU
        · rw [Finset.mem_singleton.mp hy]
          exact hxU
      have hp := Finset.card_le_card hpair
      simpa only [hCe, Finset.card_empty, Nat.zero_add, Finset.card_pair hux] using hp
  have hER : Earlier T x⊆T := Finset.filter_subset _ _
  have hdis : Disjoint D (Earlier T x) := Finset.disjoint_of_subset_right hER hDT
  have hRcard : R.card=D.card+(Earlier T x).card := Finset.card_union_of_disjoint hdis
  have hRsub : R⊆Ω := Finset.union_subset hD (hER.trans hT)
  have hcard := Finset.card_sdiff_add_card_eq_card hRsub
  change U.card+R.card=Ω.card at hcard
  rw [hRcard] at hcard
  change C.card+D.card+(Earlier T x).card+2≤Ω.card
  omega

#print axioms hit_bucket_spec
#print axioms actual_bucket_capacity
end
end JSP233.FirstHitCapacity84364
