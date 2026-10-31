import Erdos272.Core.NearAP36

/-! Actual maximal-core geometry for the Far slot argument.

The sources below are distinct members of one actual Legal family.  A core is
inclusion maximal inside its source, not an AP member of the family.  No slot
capacity is assumed.  This module does not assert the final Far count or a new
universal extremal threshold.
-/
namespace JSP233.FarSlot112
open StarCompletion APGeometry NearAP36
open scoped Classical
noncomputable section

/-- A common shell point prevents containment, including equal chosen cores. -/
theorem actual_core_not_subset {Ω S T P Q : Finset ℤ} {F : Finset (Finset ℤ)}
    {x : ℤ} (hF : Legal Ω F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hP : MaximalAPCore S P) (hQ : Q ⊆ T)
    (hxS : x ∈ S) (hxT : x ∈ T) (hxP : x ∉ P) : ¬ P ⊆ Q := by
  intro hPQ
  have hPI : P ⊆ S ∩ T := fun y hy =>
    Finset.mem_inter.mpr ⟨hP.1 hy, hQ (hPQ hy)⟩
  have hEq : S ∩ T = P := hP.2.2 (S ∩ T) hPI Finset.inter_subset_left
    (hF.2 S hS T hT hne)
  exact hxP (hEq ▸ Finset.mem_inter.mpr ⟨hxS, hxT⟩)

/-- The actual chosen cores at a fixed physical shell point form an antichain. -/
theorem actual_shell_core_antichain {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ) (x : ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S)) :
    ∀ S ∈ F, ∀ T ∈ F, S ≠ T → x ∈ S \ core S → x ∈ T \ core T →
      ¬ core S ⊆ core T := by
  intro S hS T hT hne hxS hxT
  exact actual_core_not_subset hF hS hT hne (hcore S hS) (hcore T hT).1
    (Finset.mem_sdiff.mp hxS).1 (Finset.mem_sdiff.mp hxT).1 (Finset.mem_sdiff.mp hxS).2

/-- A bounded residue segment, with no assumption that it is an actual member. -/
def Segment (d a lo hi : ℤ) : Finset ℤ :=
  (Finset.Icc lo hi).filter (fun y => d ∣ y - a)

theorem mem_segment {d a lo hi y : ℤ} :
    y ∈ Segment d a lo hi ↔ lo ≤ y ∧ y ≤ hi ∧ d ∣ y - a := by
  simp only [Segment, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem segment_APAt {d a lo hi : ℤ} (hd : 0 < d) :
    APAt d a (Segment d a lo hi) := by
  exact ⟨hd, lo, hi, fun y => mem_segment⟩

/-- Primitive completion of an overlap plus a shell point is contained in the
actual AP intersection.  Its step is constructed by gcd, not postulated. -/
theorem primitive_segment_subset {R : Finset ℤ} {a d l r x : ℤ}
    (hR : IsAP R) (ha : a ∈ R) (hb : a + d ∈ R)
    (hl : l ∈ R) (hr : r ∈ R) (hx : x ∈ R) :
    Segment (Int.gcd d (x - a) : ℤ) a (min l x) (max r x) ⊆ R := by
  obtain ⟨e, p, hAt, _⟩ := (isAP_iff_exists_APAt R).mp hR
  have hed : e ∣ d := by
    have hh := apAt_dvd_sub hAt ha hb
    simpa only [add_sub_cancel_left] using hh
  have hex : e ∣ x - a := apAt_dvd_sub hAt ha hx
  have heg : e ∣ (Int.gcd d (x - a) : ℤ) := Int.dvd_coe_gcd hed hex
  have hlo : min l x ∈ R := by
    by_cases h : l ≤ x
    · simpa only [min_eq_left h] using hl
    · simpa only [min_eq_right (le_of_not_ge h)] using hx
  have hhi : max r x ∈ R := by
    by_cases h : r ≤ x
    · simpa only [max_eq_right h] using hx
    · simpa only [max_eq_left (le_of_not_ge h)] using hr
  intro y hy
  obtain ⟨hyl, hyr, hgy⟩ := mem_segment.mp hy
  have hey : e ∣ y - a := dvd_trans heg hgy
  have helo : e ∣ min l x - a := apAt_dvd_sub hAt ha hlo
  apply apAt_fill hAt hlo hhi hyl hyr
  rw [show y - min l x = (y - a) - (min l x - a) by ring]
  exact dvd_sub hey helo

/-- A same-grid shell point is private relative to every other actual member
containing the adjacent core edge, with no condition on that member's core. -/
theorem actual_on_grid_shell_private {Ω S T P : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x : ℤ} (hF : Legal Ω F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hP : MaximalAPCore S P) (hAt : APAt d a P)
    (ha : a ∈ P) (hb : a + d ∈ P) (hxS : x ∈ S) (hxP : x ∉ P)
    (hax : d ∣ x - a) (haT : a ∈ T) (hbT : a + d ∈ T) : x ∉ T := by
  intro hxT
  let R := S ∩ T
  have hR : IsAP R := hF.2 S hS T hT hne
  have haR : a ∈ R := Finset.mem_inter.mpr ⟨hP.1 ha, haT⟩
  have hbR : a + d ∈ R := Finset.mem_inter.mpr ⟨hP.1 hb, hbT⟩
  have hxR : x ∈ R := Finset.mem_inter.mpr ⟨hxS, hxT⟩
  let H := Segment d a (min a x) (max (a + d) x)
  have hd : 0 < d := hAt.1
  have hHAt : APAt d a H := segment_APAt hAt.1
  have haH : a ∈ H := mem_segment.mpr ⟨min_le_left _ _,
    le_trans (by omega : a ≤ a + d) (le_max_left _ _), by simp⟩
  have hxH : x ∈ H := mem_segment.mpr ⟨min_le_right _ _, le_max_right _ _, hax⟩
  have hHR : H ⊆ R := by
    obtain ⟨e, p, hRAt, _⟩ := (isAP_iff_exists_APAt R).mp hR
    have hed : e ∣ d := by
      simpa only [add_sub_cancel_left] using apAt_dvd_sub hRAt haR hbR
    have hlo : min a x ∈ R := by
      by_cases h : a ≤ x
      · simpa only [min_eq_left h] using haR
      · simpa only [min_eq_right (le_of_not_ge h)] using hxR
    have hhi : max (a + d) x ∈ R := by
      by_cases h : a + d ≤ x
      · simpa only [max_eq_right h] using hxR
      · simpa only [max_eq_left (le_of_not_ge h)] using hbR
    intro y hy
    obtain ⟨hyl, hyr, hdy⟩ := mem_segment.mp hy
    apply apAt_fill hRAt hlo hhi hyl hyr
    have hya : e ∣ y - a := dvd_trans hed hdy
    have hloa : e ∣ min a x - a := apAt_dvd_sub hRAt haR hlo
    rw [show y - min a x = (y - a) - (min a x - a) by ring]
    exact dvd_sub hya hloa
  have hUAt : APAt d a (P ∪ H) := by
    simpa only [APAt, Finset.mem_union] using
      PrivateUnion.union_APAt d a (fun y => y ∈ P) (fun y => y ∈ H) hAt hHAt ha haH
  have hUAP : IsAP (P ∪ H) := (isAP_iff_exists_APAt _).mpr
    ⟨d, a, hUAt, Finset.mem_union_left _ ha⟩
  have hEq : P ∪ H = P := hP.2.2 (P ∪ H) Finset.subset_union_left
    (Finset.union_subset hP.1 (hHR.trans Finset.inter_subset_left)) hUAP
  exact hxP (hEq ▸ Finset.mem_union_right P hxH)

/-- The on-grid slot has actual capacity one, not an assumed resource bound. -/
theorem actual_on_grid_slot_card_le_one {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x : ℤ} (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, APAt d a (core S))
    (ha : ∀ S ∈ F, a ∈ core S) (hb : ∀ S ∈ F, a + d ∈ core S)
    (hx : ∀ S ∈ F, x ∈ S \ core S) (hax : d ∣ x - a) : F.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro S hS T hT
  by_contra hne
  exact actual_on_grid_shell_private hF hS hT hne (hcore S hS) (hAt S hS)
    (ha S hS) (hb S hS) (Finset.mem_sdiff.mp (hx S hS)).1
    (Finset.mem_sdiff.mp (hx S hS)).2 hax ((hcore T hT).1 (ha T hT))
    ((hcore T hT).1 (hb T hT)) (Finset.mem_sdiff.mp (hx T hT)).1

theorem ap_mem_of_bounds {P : Finset ℤ} {d a l r y : ℤ}
    (hP : APAt d a P) (hl : l ∈ P) (hr : r ∈ P)
    (hly : l ≤ y) (hyr : y ≤ r) (hdy : d ∣ y - a) : y ∈ P := by
  apply apAt_fill hP hl hr hly hyr
  have hdl : d ∣ l - a := by
    obtain ⟨_, lo, hi, hrep⟩ := hP
    exact ((hrep l).mp hl).2.2
  rw [show y - l = (y - a) - (l - a) by ring]
  exact dvd_sub hdy hdl

/-- Three actual users ordered by both endpoints force an AP extension of
the middle core.  The gcd segment is built from their actual intersections. -/
theorem actual_no_ordered_three_slot
    {Ω S₁ S₂ S₃ P₁ P₂ P₃ : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x l₁ l₂ l₃ r₁ r₂ r₃ : ℤ}
    (hF : Legal Ω F) (hS₁ : S₁ ∈ F) (hS₂ : S₂ ∈ F) (hS₃ : S₃ ∈ F)
    (hne₁₂ : S₁ ≠ S₂) (hne₂₃ : S₂ ≠ S₃)
    (hP₁ : P₁ ⊆ S₁) (hP₂ : MaximalAPCore S₂ P₂) (hP₃ : P₃ ⊆ S₃)
    (hAt₁ : APAt d a P₁) (hAt₂ : APAt d a P₂) (hAt₃ : APAt d a P₃)
    (ha₁ : a ∈ P₁) (ha₂ : a ∈ P₂) (ha₃ : a ∈ P₃)
    (hb₁ : a + d ∈ P₁) (hb₂ : a + d ∈ P₂) (hb₃ : a + d ∈ P₃)
    (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂) (hx₃ : x ∈ S₃) (hxP₂ : x ∉ P₂)
    (hl₁ : l₁ ∈ P₁) (hl₂ : l₂ ∈ P₂) (hl₃ : l₃ ∈ P₃)
    (hr₁ : r₁ ∈ P₁) (hr₂ : r₂ ∈ P₂) (hr₃ : r₃ ∈ P₃)
    (hbds₁ : ∀ y ∈ P₁, l₁ ≤ y ∧ y ≤ r₁)
    (hbds₂ : ∀ y ∈ P₂, l₂ ≤ y ∧ y ≤ r₂)
    (hbds₃ : ∀ y ∈ P₃, l₃ ≤ y ∧ y ≤ r₃)
    (hl₁₂ : l₁ ≤ l₂) (hl₂₃ : l₂ ≤ l₃)
    (hr₁₂ : r₁ ≤ r₂) (hr₂₃ : r₂ ≤ r₃) : False := by
  have hd : 0 < d := hAt₂.1
  have hl₂P₁ : l₂ ∈ P₁ := ap_mem_of_bounds hAt₁ hl₁ hr₁ hl₁₂
    (by have := hbds₂ a ha₂; have := hbds₁ a ha₁; omega)
    (apAt_dvd_sub hAt₂ ha₂ hl₂)
  have hr₁P₂ : r₁ ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂
    (by have := hbds₂ a ha₂; have := hbds₁ a ha₁; omega) hr₁₂
    (apAt_dvd_sub hAt₁ ha₁ hr₁)
  have hl₃P₂ : l₃ ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂ hl₂₃
    (by have := hbds₃ a ha₃; have := hbds₂ a ha₂; omega)
    (apAt_dvd_sub hAt₃ ha₃ hl₃)
  have hr₂P₃ : r₂ ∈ P₃ := ap_mem_of_bounds hAt₃ hl₃ hr₃
    (by have := hbds₃ a ha₃; have := hbds₂ a ha₂; omega) hr₂₃
    (apAt_dvd_sub hAt₂ ha₂ hr₂)
  let g : ℤ := Int.gcd d (x - a)
  have hg : 0 < g := by
    dsimp [g]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (x - a) (by omega : d ≠ 0)
  have hgd : g ∣ d := Int.gcd_dvd_left d (x - a)
  have hgx : g ∣ x - a := Int.gcd_dvd_right d (x - a)
  let H₁₂ := Segment g a (min l₂ x) (max r₁ x)
  let H₂₃ := Segment g a (min l₃ x) (max r₂ x)
  have hH₁₂ : H₁₂ ⊆ S₁ ∩ S₂ := primitive_segment_subset
    (hF.2 S₁ hS₁ S₂ hS₂ hne₁₂)
    (Finset.mem_inter.mpr ⟨hP₁ ha₁, hP₂.1 ha₂⟩)
    (Finset.mem_inter.mpr ⟨hP₁ hb₁, hP₂.1 hb₂⟩)
    (Finset.mem_inter.mpr ⟨hP₁ hl₂P₁, hP₂.1 hl₂⟩)
    (Finset.mem_inter.mpr ⟨hP₁ hr₁, hP₂.1 hr₁P₂⟩)
    (Finset.mem_inter.mpr ⟨hx₁, hx₂⟩)
  have hH₂₃ : H₂₃ ⊆ S₂ ∩ S₃ := primitive_segment_subset
    (hF.2 S₂ hS₂ S₃ hS₃ hne₂₃)
    (Finset.mem_inter.mpr ⟨hP₂.1 ha₂, hP₃ ha₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hb₂, hP₃ hb₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hl₃P₂, hP₃ hl₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hr₂, hP₃ hr₂P₃⟩)
    (Finset.mem_inter.mpr ⟨hx₂, hx₃⟩)
  have hxH₁₂ : x ∈ H₁₂ := mem_segment.mpr ⟨min_le_right _ _, le_max_right _ _, hgx⟩
  have hxH₂₃ : x ∈ H₂₃ := mem_segment.mpr ⟨min_le_right _ _, le_max_right _ _, hgx⟩
  have hl₂H : l₂ ∈ H₁₂ := mem_segment.mpr ⟨min_le_left _ _,
    le_trans (by have := hbds₂ a ha₂; have := hbds₁ a ha₁; omega) (le_max_left _ _),
    dvd_trans hgd (apAt_dvd_sub hAt₂ ha₂ hl₂)⟩
  have hr₂H : r₂ ∈ H₂₃ := mem_segment.mpr ⟨
    le_trans (min_le_left _ _) (by have := hbds₃ a ha₃; have := hbds₂ a ha₂; omega),
    le_max_left _ _, dvd_trans hgd (apAt_dvd_sub hAt₂ ha₂ hr₂)⟩
  have hUAt : APAt g x (H₁₂ ∪ H₂₃) := by
    simpa only [APAt, Finset.mem_union] using
      PrivateUnion.union_APAt g x (fun y => y ∈ H₁₂) (fun y => y ∈ H₂₃)
        (apAt_rebase (segment_APAt hg) hxH₁₂)
        (apAt_rebase (segment_APAt hg) hxH₂₃) hxH₁₂ hxH₂₃
  have hP₂U : P₂ ⊆ H₁₂ ∪ H₂₃ := by
    intro y hy
    apply apAt_fill hUAt (Finset.mem_union_left _ hl₂H) (Finset.mem_union_right _ hr₂H)
      (hbds₂ y hy).1 (hbds₂ y hy).2
    exact dvd_trans hgd (apAt_dvd_sub hAt₂ hl₂ hy)
  have hUS₂ : H₁₂ ∪ H₂₃ ⊆ S₂ := Finset.union_subset
    (hH₁₂.trans Finset.inter_subset_right) (hH₂₃.trans Finset.inter_subset_left)
  have hUAP : IsAP (H₁₂ ∪ H₂₃) := (isAP_iff_exists_APAt _).mpr
    ⟨g, x, hUAt, Finset.mem_union_left _ hxH₁₂⟩
  have hEq := hP₂.2.2 (H₁₂ ∪ H₂₃) hP₂U hUS₂ hUAP
  exact hxP₂ (hEq ▸ Finset.mem_union_left H₂₃ hxH₁₂)

/-- Without any residue restriction the actual slot capacity is at most two.
The endpoint ordering is derived from maximal-core noncontainment. -/
theorem actual_slot_card_le_two {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x : ℤ} (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, APAt d a (core S))
    (ha : ∀ S ∈ F, a ∈ core S) (hb : ∀ S ∈ F, a + d ∈ core S)
    (hx : ∀ S ∈ F, x ∈ S \ core S) : F.card ≤ 2 := by
  let lo : Finset ℤ → ℤ := fun S =>
    if h : (core S).Nonempty then (core S).min' h else 0
  let hi : Finset ℤ → ℤ := fun S =>
    if h : (core S).Nonempty then (core S).max' h else 0
  have hlo : ∀ S ∈ F, lo S ∈ core S := by
    intro S hS
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [lo, dif_pos hn] using Finset.min'_mem (core S) hn
  have hhi : ∀ S ∈ F, hi S ∈ core S := by
    intro S hS
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [hi, dif_pos hn] using Finset.max'_mem (core S) hn
  have hbds : ∀ S ∈ F, ∀ y ∈ core S, lo S ≤ y ∧ y ≤ hi S := by
    intro S hS y hy
    have hn : (core S).Nonempty := ⟨a, ha S hS⟩
    simpa only [lo, hi, dif_pos hn] using
      And.intro (Finset.min'_le (core S) y hy) (Finset.le_max' (core S) y hy)
  have horder : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → lo S ≤ lo T → hi S ≤ hi T := by
    intro S hS T hT hne hl
    by_contra hr
    have hsub : core T ⊆ core S := by
      intro y hy
      apply ap_mem_of_bounds (hAt S hS) (hlo S hS) (hhi S hS)
      · exact hl.trans (hbds T hT y hy).1
      · exact (hbds T hT y hy).2.trans (le_of_not_ge hr)
      · exact apAt_dvd_sub (hAt T hT) (ha T hT) hy
    exact actual_core_not_subset hF hT hS hne.symm (hcore T hT) (hcore S hS).1
      (Finset.mem_sdiff.mp (hx T hT)).1 (Finset.mem_sdiff.mp (hx S hS)).1
      (Finset.mem_sdiff.mp (hx T hT)).2 hsub
  have hno : ∀ S ∈ F, ∀ T ∈ F, ∀ U ∈ F, S ≠ T → T ≠ U →
      lo S ≤ lo T → lo T ≤ lo U → False := by
    intro S hS T hT U hU hST hTU hSTlo hTUlo
    exact actual_no_ordered_three_slot hF hS hT hU hST hTU
      (hcore S hS).1 (hcore T hT) (hcore U hU).1
      (hAt S hS) (hAt T hT) (hAt U hU)
      (ha S hS) (ha T hT) (ha U hU) (hb S hS) (hb T hT) (hb U hU)
      (Finset.mem_sdiff.mp (hx S hS)).1 (Finset.mem_sdiff.mp (hx T hT)).1
      (Finset.mem_sdiff.mp (hx U hU)).1 (Finset.mem_sdiff.mp (hx T hT)).2
      (hlo S hS) (hlo T hT) (hlo U hU) (hhi S hS) (hhi T hT) (hhi U hU)
      (hbds S hS) (hbds T hT) (hbds U hU) hSTlo hTUlo
      (horder S hS T hT hST hSTlo) (horder T hT U hU hTU hTUlo)
  by_contra hcard
  obtain ⟨S, T, U, hS, hT, hU, hST, hSU, hTU⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge hcard)
  rcases le_total (lo S) (lo T) with hSTlo | hTSlo
  · rcases le_total (lo T) (lo U) with hTUlo | hUTlo
    · exact hno S hS T hT U hU hST hTU hSTlo hTUlo
    · rcases le_total (lo S) (lo U) with hSUlo | hUSlo
      · exact hno S hS U hU T hT hSU hTU.symm hSUlo hUTlo
      · exact hno U hU S hS T hT hSU.symm hST hUSlo hSTlo
  · rcases le_total (lo S) (lo U) with hSUlo | hUSlo
    · exact hno T hT S hS U hU hST.symm hSU hTSlo hSUlo
    · rcases le_total (lo T) (lo U) with hTUlo | hUTlo
      · exact hno T hT U hU S hS hTU hSU.symm hTUlo hUSlo
      · exact hno U hU T hT S hS hTU.symm hST.symm hUTlo hTSlo

/-- The exact 1/2 physical-slot bound, for complete actual Legal users. -/
theorem actual_slot_capacity {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x : ℤ} (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, APAt d a (core S))
    (ha : ∀ S ∈ F, a ∈ core S) (hb : ∀ S ∈ F, a + d ∈ core S)
    (hx : ∀ S ∈ F, x ∈ S \ core S) :
    F.card ≤ if d ∣ x - a then 1 else 2 := by
  split_ifs with hgrid
  · exact actual_on_grid_slot_card_le_one hF core hcore hAt ha hb hx hgrid
  · exact actual_slot_card_le_two hF core hcore hAt ha hb hx

/-- All actual users of the physical adjacent edge and shell point.  This
filter does not select a favourable subset of the users. -/
def SlotUsers (F : Finset (Finset ℤ)) (core : Finset ℤ → Finset ℤ)
    (a d x : ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => APAt d a (core S) ∧ a ∈ core S ∧ a + d ∈ core S ∧
    x ∈ S \ core S)

/-- The complete slot filter in the original actual family has capacity 1/2.
All geometry is proved above from Legal and inclusion-maximal AP cores. -/
theorem actual_all_slot_users_capacity {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S)) (a d x : ℤ) :
    (SlotUsers F core a d x).card ≤ if d ∣ x - a then 1 else 2 := by
  have hsub : SlotUsers F core a d x ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal Ω (SlotUsers F core a d x) :=
    ⟨fun S hS => hF.1 S (hsub hS),
      fun S hS T hT hne => hF.2 S (hsub hS) T (hsub hT) hne⟩
  apply actual_slot_capacity hlegal core (fun S hS => hcore S (hsub hS))
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.1
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.1
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.2.1
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.2.2

#print axioms actual_core_not_subset
#print axioms actual_shell_core_antichain
#print axioms mem_segment
#print axioms segment_APAt
#print axioms primitive_segment_subset
#print axioms actual_on_grid_shell_private
#print axioms actual_on_grid_slot_card_le_one
#print axioms ap_mem_of_bounds
#print axioms actual_no_ordered_three_slot
#print axioms actual_slot_card_le_two
#print axioms actual_slot_capacity
#print axioms actual_all_slot_users_capacity

end
end JSP233.FarSlot112
