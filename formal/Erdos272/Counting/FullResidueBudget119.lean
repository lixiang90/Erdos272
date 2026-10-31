import Erdos272.Counting.OffResidueDensity118
import Mathlib.Data.Nat.ModEq

/-! Complete off-residue classes with moduli at most twelve.  The ordinary
classes use the finite dual.  The exceptional prime moduli force every
other class to have the same modulus by the Chinese remainder theorem.
The result is an exact 330-point capacity for the span bound of a 360-block.
It still requires globally disjoint complete classes; actual AP traces are
connected to it in a separate geometric module. -/
namespace JSP233.FullResidueBudget119
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def AllCodes : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 12).biUnion
    (fun d => ((Finset.range d).erase 0).image (fun r => (d,r)))

theorem mem_allCodes {c : ℕ × ℕ} :
    c ∈ AllCodes ↔ 2 ≤ c.1 ∧ c.1 ≤ 12 ∧ 0 < c.2 ∧ c.2 < c.1 := by
  rcases c with ⟨d,r⟩
  simp only [AllCodes, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_erase, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    rcases hab with ⟨rfl,rfl⟩
    exact ⟨ha.1,ha.2,by omega,hb.2⟩
  · rintro ⟨hd2,hd12,hr0,hrd⟩
    exact ⟨d,⟨hd2,hd12⟩,r,⟨by omega,hrd⟩,rfl,rfl⟩

theorem disjoint_codes_not_coprime {C : Finset (ℕ × ℕ)}
    (hC : C ⊆ AllCodes)
    (hdisj : ∀ z : ℕ, (C.filter (fun c => z % c.1 = c.2)).card ≤ 1)
    {a b : ℕ × ℕ} (ha : a ∈ C) (hb : b ∈ C) (hne : a ≠ b) :
    ¬ Nat.Coprime a.1 b.1 := by
  intro hco
  have hvalidA := mem_allCodes.mp (hC ha)
  have hvalidB := mem_allCodes.mp (hC hb)
  let z := Nat.chineseRemainder hco a.2 b.2
  have hza : (z:ℕ) % a.1 = a.2 := by
    have hh := z.property.1
    change (z:ℕ) % a.1 = a.2 % a.1 at hh
    simpa only [Nat.mod_eq_of_lt hvalidA.2.2.2] using hh
  have hzb : (z:ℕ) % b.1 = b.2 := by
    have hh := z.property.2
    change (z:ℕ) % b.1 = b.2 % b.1 at hh
    simpa only [Nat.mod_eq_of_lt hvalidB.2.2.2] using hh
  exact hne ((Finset.card_le_one.mp (hdisj z)) a
    (Finset.mem_filter.mpr ⟨ha,hza⟩) b (Finset.mem_filter.mpr ⟨hb,hzb⟩))

theorem special_coprime_table :
    ∀ p ∈ ({7,11} : Finset ℕ), ∀ d ∈ Finset.Icc 2 12,
      d ≠ p → Nat.Coprime p d := by
  decide

theorem all_same_modulus_of_special {C : Finset (ℕ × ℕ)}
    (hC : C ⊆ AllCodes)
    (hdisj : ∀ z : ℕ, (C.filter (fun c => z % c.1 = c.2)).card ≤ 1)
    {p : ℕ} (hp : p ∈ ({7,11} : Finset ℕ))
    (hex : ∃ a ∈ C, a.1 = p) : ∀ b ∈ C, b.1 = p := by
  obtain ⟨a,ha,hap⟩ := hex
  intro b hb
  by_cases hab : a = b
  · simpa only [hab] using hap
  · by_contra hbp
    have hn := disjoint_codes_not_coprime hC hdisj ha hb hab
    have hv := mem_allCodes.mp (hC hb)
    rw [hap] at hn
    exact hn (special_coprime_table p hp b.1 (Finset.mem_Icc.mpr ⟨hv.1,hv.2.1⟩) hbp)

theorem same_modulus_card {C : Finset (ℕ × ℕ)} (hC : C ⊆ AllCodes)
    {p : ℕ} (hp : 0 < p) (hmod : ∀ c ∈ C, c.1 = p) : C.card ≤ p-1 := by
  have hsub : C.image Prod.snd ⊆ (Finset.range p).erase 0 := by
    intro r hr
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hr
    have hv := mem_allCodes.mp (hC hc)
    exact Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by simpa only [hmod c hc] using hv.2.2.2)⟩
  have hinj : Set.InjOn Prod.snd (↑C : Set (ℕ × ℕ)) := by
    intro a ha b hb he
    exact Prod.ext ((hmod a ha).trans (hmod b hb).symm) he
  have hi := Finset.card_image_of_injOn hinj
  have hh := Finset.card_le_card hsub
  rw [hi,Finset.card_erase_of_mem (Finset.mem_range.mpr hp),Finset.card_range] at hh
  exact hh

theorem ordinary_span_table :
    ∀ d ∈ ({2,3,4,5,6,8,9,10,12} : Finset ℕ), 359/d+1 = 360/d := by
  decide

theorem full_residue_span_budget (C : Finset (ℕ × ℕ))
    (hC : C ⊆ AllCodes)
    (hdisj : ∀ z : ℕ, (C.filter (fun c => z % c.1 = c.2)).card ≤ 1) :
    ∑ c ∈ C, (359/c.1+1) ≤ 330 := by
  by_cases hex : ∃ a ∈ C, a.1 ∈ ({7,11} : Finset ℕ)
  · obtain ⟨a,ha,hap⟩ := hex
    have hmod := all_same_modulus_of_special hC hdisj hap ⟨a,ha,rfl⟩
    have hp : a.1 = 7 ∨ a.1 = 11 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hap
    have hpos : 0 < a.1 := by omega
    have hcard := same_modulus_card hC hpos hmod
    have he : (∑ c ∈ C, (359/c.1+1)) = C.card*(359/a.1+1) := by
      calc
        _ = ∑ c ∈ C, (359/a.1+1) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [hmod c hc]
        _ = _ := by simp
    rw [he]
    have hm := Nat.mul_le_mul_right (359/a.1+1) hcard
    rcases hp with hp | hp <;> rw [hp] at hm ⊢ <;> norm_num at hm ⊢ <;> omega
  · have hsub : C ⊆ OffResidueDensity118.codes := by
      intro c hc
      have hv := mem_allCodes.mp (hC hc)
      have h7 : c.1 ≠ 7 := by intro he;exact hex ⟨c,hc,by simp only [he,Finset.mem_insert,Finset.mem_singleton];tauto⟩
      have h11 : c.1 ≠ 11 := by intro he;exact hex ⟨c,hc,by simp only [he,Finset.mem_insert,Finset.mem_singleton];tauto⟩
      have hd : c.1 ∈ ({2,3,4,5,6,8,9,10,12} : Finset ℕ) := by
        have hl := hv.1
        have hu := hv.2.1
        interval_cases c.1 <;> norm_num at *
      apply Finset.mem_biUnion.mpr
      refine ⟨c.1,hd,Finset.mem_image.mpr ?_⟩
      exact ⟨c.2,Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr hv.2.2.2⟩,Prod.eta c⟩
    have hb := OffResidueDensity118.disjoint_residue_budget C hsub (fun z _ => hdisj z)
    have he : (∑ c ∈ C, (359/c.1+1)) = ∑ c ∈ C, 360/c.1 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hv := Finset.mem_biUnion.mp (hsub hc)
      obtain ⟨d,hd,hr⟩ := hv
      obtain ⟨r,_hr,he⟩ := Finset.mem_image.mp hr
      have he' : d = c.1 := congrArg Prod.fst he
      exact ordinary_span_table c.1 (he' ▸ hd)
    rwa [he]

#print axioms mem_allCodes
#print axioms disjoint_codes_not_coprime
#print axioms special_coprime_table
#print axioms all_same_modulus_of_special
#print axioms same_modulus_card
#print axioms ordinary_span_table
#print axioms full_residue_span_budget
end
end JSP233.FullResidueBudget119
