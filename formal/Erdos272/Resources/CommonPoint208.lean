import Erdos272.Core.FarSlot112

namespace JSP233.CommonPoint208
open StarCompletion APGeometry NearAP36 FarSlot112
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem primitive_segment_subset_at {R : Finset ℤ} {a u d l r x : ℤ}
    (hR : IsAP R) (ha : a ∈ R) (hu : u ∈ R) (hv : u+d ∈ R)
    (hl : l ∈ R) (hr : r ∈ R) (hx : x ∈ R) :
    Segment (Int.gcd d (x-a) : ℤ) a (min l x) (max r x) ⊆ R := by
  obtain ⟨e,p,hAt,_⟩ := (isAP_iff_exists_APAt R).mp hR
  have hed : e ∣ d := by simpa only [add_sub_cancel_left] using apAt_dvd_sub hAt hu hv
  have hex : e ∣ x-a := apAt_dvd_sub hAt ha hx
  have heg : e ∣ (Int.gcd d (x-a) : ℤ) := Int.dvd_coe_gcd hed hex
  have hlo : min l x ∈ R := by
    by_cases h : l≤x
    · simpa only [min_eq_left h] using hl
    · simpa only [min_eq_right (le_of_not_ge h)] using hx
  have hhi : max r x ∈ R := by
    by_cases h : r≤x
    · simpa only [max_eq_right h] using hx
    · simpa only [max_eq_left (le_of_not_ge h)] using hr
  intro y hy
  obtain ⟨hyl,hyr,hgy⟩ := mem_segment.mp hy
  have hey : e ∣ y-a := dvd_trans heg hgy
  have helo : e ∣ min l x-a := apAt_dvd_sub hAt ha hlo
  apply apAt_fill hAt hlo hhi hyl hyr
  rw [show y-min l x=(y-a)-(min l x-a) by ring]
  exact dvd_sub hey helo

theorem no_ordered_three
    {Ω S₁ S₂ S₃ P₁ P₂ P₃ : Finset ℤ} {F : Finset (Finset ℤ)}
    {a d x l₁ l₂ l₃ r₁ r₂ r₃ : ℤ}
    (hF : Legal Ω F) (hS₁ : S₁ ∈ F) (hS₂ : S₂ ∈ F) (hS₃ : S₃ ∈ F)
    (hne₁₂ : S₁ ≠ S₂) (hne₂₃ : S₂ ≠ S₃)
    (hP₁ : P₁ ⊆ S₁) (hP₂ : MaximalAPCore S₂ P₂) (hP₃ : P₃ ⊆ S₃)
    (hAt₁ : APAt d a P₁) (hAt₂ : APAt d a P₂) (hAt₃ : APAt d a P₃)
    (ha₁ : a ∈ P₁) (ha₂ : a ∈ P₂) (ha₃ : a ∈ P₃)
    (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂) (hx₃ : x ∈ S₃) (hxP₂ : x ∉ P₂)
    (hl₁ : l₁ ∈ P₁) (hl₂ : l₂ ∈ P₂) (hl₃ : l₃ ∈ P₃)
    (hr₁ : r₁ ∈ P₁) (hr₂ : r₂ ∈ P₂) (hr₃ : r₃ ∈ P₃)
    (hbds₁ : ∀ y ∈ P₁, l₁ ≤ y ∧ y ≤ r₁)
    (hbds₂ : ∀ y ∈ P₂, l₂ ≤ y ∧ y ≤ r₂)
    (hbds₃ : ∀ y ∈ P₃, l₃ ≤ y ∧ y ≤ r₃)
    (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃) (hr₁₂ : r₁ < r₂) (hr₂₃ : r₂ < r₃) : False := by
  have hd : 0 < d := hAt₂.1
  have hleft : l₂ ≤ a-d := by
    have hp : 0 < a-l₂ := by have hh := hbds₃ a ha₃; omega
    have hh := Int.le_of_dvd hp (apAt_dvd_sub hAt₂ hl₂ ha₂)
    omega
  have hright : a+d ≤ r₂ := by
    have hp : 0 < r₂-a := by have hh := hbds₁ a ha₁; omega
    have hh := Int.le_of_dvd hp (apAt_dvd_sub hAt₂ ha₂ hr₂)
    omega
  have hprev₁ : a-d ∈ P₁ := ap_mem_of_bounds hAt₁ hl₁ hr₁
    (by omega) (by have hh := hbds₁ a ha₁; omega) ⟨-1,by ring⟩
  have hprev₂ : a-d ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂ hleft
    (by have hh := hbds₂ a ha₂; omega) ⟨-1,by ring⟩
  have hnext₂ : a+d ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂
    (by have hh := hbds₂ a ha₂; omega) hright ⟨1,by ring⟩
  have hnext₃ : a+d ∈ P₃ := ap_mem_of_bounds hAt₃ hl₃ hr₃
    (by have hh := hbds₃ a ha₃; omega) (by omega) ⟨1,by ring⟩
  have hl₂P₁ : l₂ ∈ P₁ := ap_mem_of_bounds hAt₁ hl₁ hr₁ hl₁₂.le
    (by have hh := hbds₂ a ha₂; have hh' := hbds₁ a ha₁; omega) (apAt_dvd_sub hAt₂ ha₂ hl₂)
  have hr₁P₂ : r₁ ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂
    (by have hh := hbds₂ a ha₂; have hh' := hbds₁ a ha₁; omega) hr₁₂.le (apAt_dvd_sub hAt₁ ha₁ hr₁)
  have hl₃P₂ : l₃ ∈ P₂ := ap_mem_of_bounds hAt₂ hl₂ hr₂ hl₂₃.le
    (by have hh := hbds₃ a ha₃; have hh' := hbds₂ a ha₂; omega) (apAt_dvd_sub hAt₃ ha₃ hl₃)
  have hr₂P₃ : r₂ ∈ P₃ := ap_mem_of_bounds hAt₃ hl₃ hr₃
    (by have hh := hbds₃ a ha₃; have hh' := hbds₂ a ha₂; omega) hr₂₃.le (apAt_dvd_sub hAt₂ ha₂ hr₂)
  let g : ℤ := Int.gcd d (x-a)
  have hg : 0 < g := by dsimp [g]; exact_mod_cast Int.gcd_pos_of_ne_zero_left (x-a) (by omega : d≠0)
  have hgd : g ∣ d := Int.gcd_dvd_left d (x-a)
  have hgx : g ∣ x-a := Int.gcd_dvd_right d (x-a)
  let H₁₂ := Segment g a (min l₂ x) (max r₁ x)
  let H₂₃ := Segment g a (min l₃ x) (max r₂ x)
  have hH₁₂ : H₁₂ ⊆ S₁ ∩ S₂ := primitive_segment_subset_at
    (hF.2 S₁ hS₁ S₂ hS₂ hne₁₂) (Finset.mem_inter.mpr ⟨hP₁ ha₁,hP₂.1 ha₂⟩)
    (Finset.mem_inter.mpr ⟨hP₁ hprev₁,hP₂.1 hprev₂⟩)
    (by simpa only [sub_add_cancel] using (Finset.mem_inter.mpr ⟨hP₁ ha₁,hP₂.1 ha₂⟩))
    (Finset.mem_inter.mpr ⟨hP₁ hl₂P₁,hP₂.1 hl₂⟩)
    (Finset.mem_inter.mpr ⟨hP₁ hr₁,hP₂.1 hr₁P₂⟩) (Finset.mem_inter.mpr ⟨hx₁,hx₂⟩)
  have hH₂₃ : H₂₃ ⊆ S₂ ∩ S₃ := primitive_segment_subset_at
    (hF.2 S₂ hS₂ S₃ hS₃ hne₂₃) (Finset.mem_inter.mpr ⟨hP₂.1 ha₂,hP₃ ha₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 ha₂,hP₃ ha₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hnext₂,hP₃ hnext₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hl₃P₂,hP₃ hl₃⟩)
    (Finset.mem_inter.mpr ⟨hP₂.1 hr₂,hP₃ hr₂P₃⟩) (Finset.mem_inter.mpr ⟨hx₂,hx₃⟩)
  have hxH₁₂ : x ∈ H₁₂ := mem_segment.mpr ⟨min_le_right _ _,le_max_right _ _,hgx⟩
  have hxH₂₃ : x ∈ H₂₃ := mem_segment.mpr ⟨min_le_right _ _,le_max_right _ _,hgx⟩
  have hl₂H : l₂ ∈ H₁₂ := mem_segment.mpr ⟨min_le_left _ _,
    le_trans (by have hh := hbds₂ a ha₂; have hh' := hbds₁ a ha₁; omega) (le_max_left _ _),
    dvd_trans hgd (apAt_dvd_sub hAt₂ ha₂ hl₂)⟩
  have hr₂H : r₂ ∈ H₂₃ := mem_segment.mpr ⟨
    le_trans (min_le_left _ _) (by have hh := hbds₃ a ha₃; have hh' := hbds₂ a ha₂; omega),
    le_max_left _ _,dvd_trans hgd (apAt_dvd_sub hAt₂ ha₂ hr₂)⟩
  have hUAt : APAt g x (H₁₂ ∪ H₂₃) := by
    simpa only [APAt,Finset.mem_union] using PrivateUnion.union_APAt g x
      (fun y => y∈H₁₂) (fun y => y∈H₂₃) (apAt_rebase (segment_APAt hg) hxH₁₂)
      (apAt_rebase (segment_APAt hg) hxH₂₃) hxH₁₂ hxH₂₃
  have hPU : P₂ ⊆ H₁₂ ∪ H₂₃ := by
    intro y hy
    apply apAt_fill hUAt (Finset.mem_union_left _ hl₂H) (Finset.mem_union_right _ hr₂H)
      (hbds₂ y hy).1 (hbds₂ y hy).2
    exact dvd_trans hgd (apAt_dvd_sub hAt₂ hl₂ hy)
  have hUS : H₁₂ ∪ H₂₃ ⊆ S₂ := Finset.union_subset
    (hH₁₂.trans Finset.inter_subset_right) (hH₂₃.trans Finset.inter_subset_left)
  have hAP : IsAP (H₁₂ ∪ H₂₃) := (isAP_iff_exists_APAt _).mpr
    ⟨g,x,hUAt,Finset.mem_union_left _ hxH₁₂⟩
  have hEq := hP₂.2.2 _ hPU hUS hAP
  exact hxP₂ (hEq ▸ Finset.mem_union_left H₂₃ hxH₁₂)

#print axioms primitive_segment_subset_at
#print axioms no_ordered_three
end
end JSP233.CommonPoint208
