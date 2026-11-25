module

public import Erdos272.Core.N200000.ActualCorePairs200000

@[expose] public section

/-! If all but one point lie in one residue class, an AP containing that
exceptional point has at most three points. A covering triple is centered
at the exception. This is actual AP geometry, not a numerical sieve. -/
namespace JSP233.OffGridProgressions20258
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem grid {T : Finset ℤ} (hT : IsAP T) :
    ∃ b t : ℤ, 0 < t ∧ T = (Finset.range T.card).image (fun i : ℕ => b + t * (i : ℤ)) := by
  obtain ⟨t, p, ht, hp⟩ := (isAP_iff_exists_APAt T).mp hT
  have hne : T.Nonempty := ⟨p, hp⟩
  exact ⟨T.min' hne, t, ht.1, apAt_eq_range ht hne⟩

theorem grid_dvd_sub {T : Finset ℤ} {b t y z : ℤ}
    (hg : T = (Finset.range T.card).image (fun i : ℕ => b + t * (i : ℤ)))
    (hy : y ∈ T) (hz : z ∈ T) : t ∣ z - y := by
  rw [hg] at hy hz
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(j : ℤ) - i, by ring⟩

theorem adjacent_avoids {T : Finset ℤ} {b t : ℤ}
    (hg : T = (Finset.range T.card).image (fun i : ℕ => b + t * (i : ℤ)))
    (ht : 0 < t) (hfour : 4 ≤ T.card) (x : ℤ) :
    ∃ y z : ℤ, y ∈ T ∧ z ∈ T ∧ y ≠ x ∧ z ≠ x ∧ z - y = t := by
  have hmem (i : ℕ) (hi : i < 4) : b + t * (i : ℤ) ∈ T := by
    rw [hg]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have h0 : b ∈ T := by simpa only [Nat.cast_zero, mul_zero, add_zero] using hmem 0 (by decide)
  have h1 : b + t ∈ T := by simpa only [Nat.cast_one, mul_one] using hmem 1 (by decide)
  have h2 : b + 2 * t ∈ T := by convert hmem 2 (by decide) using 1; ring
  have h3 : b + 3 * t ∈ T := by convert hmem 3 (by decide) using 1; ring
  have hp : (b ≠ x ∧ b + t ≠ x) ∨ (b + 2 * t ≠ x ∧ b + 3 * t ≠ x) := by omega
  rcases hp with hp | hp
  · exact ⟨b, b + t, h0, h1, hp.1, hp.2, by ring⟩
  · exact ⟨b + 2 * t, b + 3 * t, h2, h3, hp.1, hp.2, by ring⟩

theorem offphase_card_le_three {T : Finset ℤ} {d p x : ℤ} (hT : IsAP T) (hx : x ∈ T)
    (hrest : ∀ y ∈ T, y ≠ x → d ∣ y - p) (hnot : ¬d ∣ x - p) : T.card ≤ 3 := by
  by_contra hn
  obtain ⟨b, t, ht, hg⟩ := grid hT
  obtain ⟨y, z, hy, hz, hyx, hzx, hdiff⟩ := adjacent_avoids hg ht (by omega) x
  have hdt : d ∣ t := by
    have hh := dvd_sub (hrest z hz hzx) (hrest y hy hyx)
    have he : (z - p) - (y - p) = z - y := by ring
    simpa only [he, hdiff] using hh
  have hxy : d ∣ x - y := hdt.trans (grid_dvd_sub hg hy hx)
  apply hnot
  have hh := dvd_add hxy (hrest y hy hyx)
  have he : (x - y) + (y - p) = x - p := by ring
  simpa only [he] using hh

theorem grid_three_mem {T : Finset ℤ} {b t y : ℤ}
    (hg : T = (Finset.range T.card).image (fun i : ℕ => b + t * (i : ℤ))) (hc : T.card = 3) :
    y ∈ T ↔ y = b ∨ y = b + t ∨ y = b + 2 * t := by
  rw [hg, hc]
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hib : i < 3 := Finset.mem_range.mp hi
    interval_cases i <;> norm_num
    omega
  · rintro (rfl | rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by decide, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by decide, by simp⟩
    · exact Finset.mem_image.mpr ⟨2, by decide, by ring⟩

theorem offphase_cover_midpoint {T : Finset ℤ} {d p x a c : ℤ} (hT : IsAP T)
    (hx : x ∈ T) (ha : a ∈ T) (hc : c ∈ T) (hac : a ≠ c)
    (hrest : ∀ y ∈ T, y ≠ x → d ∣ y - p) (hnot : ¬d ∣ x - p)
    (hap : d ∣ a - p) (hcp : d ∣ c - p) : a + c = 2 * x := by
  have hxa : x ≠ a := by intro he; exact hnot (he ▸ hap)
  have hxc : x ≠ c := by intro he; exact hnot (he ▸ hcp)
  have hlow : 3 ≤ T.card := by
    have hsub : ({x, a, c} : Finset ℤ) ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ha
      exact (Finset.mem_singleton.mp hz) ▸ hc
    have hh := Finset.card_le_card hsub
    have he : ({x, a, c} : Finset ℤ).card = 3 := by simp [hxa, hxc, hac]
    simpa only [he] using hh
  have hcard : T.card = 3 := by have hh := offphase_card_le_three hT hx hrest hnot; omega
  obtain ⟨b, t, ht, hg⟩ := grid hT
  have hmem (y : ℤ) := grid_three_mem (y := y) hg hcard
  have hb : b ∈ T := (hmem b).mpr (Or.inl rfl)
  have hb1 : b + t ∈ T := (hmem (b + t)).mpr (Or.inr (Or.inl rfl))
  have hb2 : b + 2 * t ∈ T := (hmem (b + 2 * t)).mpr (Or.inr (Or.inr rfl))
  rcases (hmem x).mp hx with hx0 | hx1 | hx2
  · have hdt : d ∣ t := by
      have hh := dvd_sub (hrest (b + 2 * t) hb2 (by omega)) (hrest (b + t) hb1 (by omega))
      have he : (b + 2 * t - p) - (b + t - p) = t := by ring
      simpa only [he] using hh
    have hxb : d ∣ x - (b + t) := hdt.trans (grid_dvd_sub hg hb1 hx)
    have hh := dvd_add hxb (hrest (b + t) hb1 (by omega))
    have he : (x - (b + t)) + (b + t - p) = x - p := by ring
    exact (hnot (by simpa only [he] using hh)).elim
  · rcases (hmem a).mp ha with ha0 | ha1 | ha2 <;>
      rcases (hmem c).mp hc with hc0 | hc1 | hc2 <;> omega
  · have hdt : d ∣ t := by
      have hh := dvd_sub (hrest (b + t) hb1 (by omega)) (hrest b hb (by omega))
      have he : (b + t - p) - (b - p) = t := by ring
      simpa only [he] using hh
    have hxb : d ∣ x - b := hdt.trans (grid_dvd_sub hg hb hx)
    have hh := dvd_add hxb (hrest b hb (by omega))
    have he : (x - b) + (b - p) = x - p := by ring
    exact (hnot (by simpa only [he] using hh)).elim

#print axioms grid
#print axioms grid_dvd_sub
#print axioms adjacent_avoids
#print axioms offphase_card_le_three
#print axioms grid_three_mem
#print axioms offphase_cover_midpoint
end
end JSP233.OffGridProgressions20258
