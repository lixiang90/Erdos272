module

public import Erdos272.Resources.OrdinaryTruncate208

@[expose] public section

namespace JSP233.RightWindows208
open StarCompletion APGeometry NearAP36 ClippedWindows208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem right_index_iff {A J B q r : ℕ} (hB : 0 < B) (hA : A ≤ q) :
    (A+r*B ≤ q ∧ q ≤ J+r*B) ↔
      (q-J+B-1)/B ≤ r ∧ r ≤ (q-A)/B := by
  have hu : A+r*B ≤ q ↔ r ≤ (q-A)/B := by
    rw [Nat.le_div_iff_mul_le hB]
    omega
  have hl : q ≤ J+r*B ↔ (q-J+B-1)/B ≤ r := by
    constructor
    · intro h
      have hm : q-J+B-1 < (r+1)*B := by
        rw [Nat.add_mul]
        omega
      have hd := (Nat.div_lt_iff_lt_mul hB).mpr hm
      omega
    · intro h
      have hd : (q-J+B-1)/B < r+1 := by omega
      have hm := (Nat.div_lt_iff_lt_mul hB).mp hd
      rw [Nat.add_mul] at hm
      omega
  exact ⟨fun h => ⟨hl.mp h.2,hu.mp h.1⟩,fun h => ⟨hu.mpr h.2,hl.mpr h.1⟩⟩

theorem actual_right_injective {N d B V : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (family : (ℕ × ℕ) → Finset (Finset ℤ))
    (core : Finset ℤ → Finset ℤ) (W : ℕ → ℕ)
    (hres : ∀ q ∈ H, q.1 < d)
    (hcore : ∀ q ∈ H, ∀ S ∈ family q, core S ⊆ Window N d B V q)
    (hdis : ∀ q ∈ H, ∀ S ∈ family q, ∀ T ∈ family q, S ≠ T →
      Disjoint (S \ core S) (T \ core T))
    (hcross : ∀ q ∈ H, ∀ t ∈ H, ∀ S ∈ family q, ∀ T ∈ family t,
      (S ∩ T).Nonempty)
    (hsmall : ∀ q ∈ H, ∀ S ∈ family q, S.card ≤ W q.2)
    (hwindow : ∀ q ∈ H, (Window N d B V q).card ≤ W q.2)
    (hheavy : ∀ q ∈ H, W q.2 < (family q).card) :
    Set.InjOn Prod.snd (H : Set (ℕ × ℕ)) := by
  intro q hq t ht he
  have hst : ∀ S ∈ family t, S.card ≤ W q.2 := by
    intro S hS
    simpa only [he] using hsmall t ht S hS
  have hwt : (Window N d B V q).card < (family t).card := by
    have hh := hheavy t ht
    rw [←he] at hh
    exact (hwindow q hq).trans_lt hh
  have hint := heavy_core_pools_intersect core (hcore q hq) (hcore t ht)
    (hdis q hq) (hdis t ht) (hcross q hq t ht) hst (hheavy q hq) hwt
  exact fixed_block_window_eq hd (hres q hq) (hres t ht) rfl he.symm hint

theorem code_census {H : Finset (ℕ × ℕ)} {lo hi : ℕ}
    (hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)))
    (hindex : ∀ q ∈ H, q.2 ∈ Finset.Icc lo hi) : H.card ≤ hi+1-lo := by
  have hh := Finset.card_le_card_of_injOn Prod.snd hindex hinj
  simpa only [Nat.card_Icc] using hh

theorem code_weight_sum {H : Finset (ℕ × ℕ)} {lo hi : ℕ} (w : ℕ → ℕ)
    (hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)))
    (hindex : ∀ q ∈ H, q.2 ∈ Finset.Icc lo hi) :
    ∑ q ∈ H, w q.2 ≤ ∑ r ∈ Finset.Icc lo hi, w r := by
  have hsub : H.image Prod.snd ⊆ Finset.Icc lo hi := by
    intro r hr
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hr
    exact hindex q hq
  calc
    _ = ∑ r ∈ H.image Prod.snd, w r := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)

theorem actual_right_union {N d B V E lo hi : ℕ} {H : Finset (ℕ × ℕ)}
    (hd : 0 < d) (hE : 1 ≤ E)
    (hinj : Set.InjOn Prod.snd (H : Set (ℕ × ℕ)))
    (hindex : ∀ q ∈ H, q.2 ∈ Finset.Icc lo hi) :
    (H.biUnion (Window N d B V)).card ≤
      ∑ r ∈ Finset.Icc lo hi, min V (N/d-r*B+E) := by
  calc
    _ ≤ ∑ q ∈ H, (Window N d B V q).card := Finset.card_biUnion_le
    _ ≤ ∑ q ∈ H, min V (N/d-q.2*B+E) := by
      apply Finset.sum_le_sum
      intro q hq
      exact actual_clipped_threshold hd hE q
    _ ≤ _ := code_weight_sum (fun r => min V (N/d-r*B+E)) hinj hindex

#print axioms right_index_iff
#print axioms actual_right_injective
#print axioms code_census
#print axioms actual_right_union
end
end JSP233.RightWindows208
