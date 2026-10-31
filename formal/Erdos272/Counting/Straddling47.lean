import Erdos272.Counting.APCount41
import Erdos272.Resources.MeetingPool46
import Erdos272.Geometry.FamilyReflect43

/-! Actual cross-root AP classification, opposite parity and finite budgets. -/
namespace JSP233.Straddling47
open StarCompletion APGeometry APCount41 WitnessInterval43
open scoped Classical
noncomputable section

def StraddlesRoot (c : ℤ) (S : Finset ℤ) : Prop :=
  (∃ x∈S,x<c) ∧ ∃ y∈S,c<y

def LargeStepAvoider (F : Finset (Finset ℤ)) (c : ℤ) : Prop :=
  ∃ P∈F,c∉P ∧ ∃ d:ℕ,3≤d ∧ ∃ p:ℤ,APAt (d:ℤ) p P

def OppositeParity (N : ℕ) (c : ℤ) : Finset ℤ :=
  (Ground N).filter (fun x=>¬(2:ℤ)∣x-c)

theorem actual_not_straddling_one_sided {c : ℤ} {S : Finset ℤ}
    (hc : c∉S) (hn : ¬StraddlesRoot c S) :
    (∀ x∈S,x<c) ∨ ∀ x∈S,c<x := by
  by_cases hl : ∃ x∈S,x<c
  · left
    intro y hy
    have hne : y≠c := by intro he; exact hc (he ▸ hy)
    by_contra hnot
    exact hn ⟨hl,y,hy,by omega⟩
  · right
    intro y hy
    have hne : y≠c := by intro he; exact hc (he ▸ hy)
    by_contra hnot
    exact hl ⟨y,hy,by omega⟩

theorem actual_straddling_card_two {c : ℤ} {S : Finset ℤ}
    (hs : StraddlesRoot c S) : 2≤S.card := by
  obtain ⟨⟨x,hx,hxc⟩,y,hy,hcy⟩ := hs
  by_contra hn
  have he := Finset.card_le_one.mp (by omega : S.card≤1) x hx y hy
  omega

theorem actual_straddling_step_ge_two {c : ℤ} {S : Finset ℤ}
    (hc : c∉S) (hs : StraddlesRoot c S) (hAP : IsAP S) : 2≤Step S := by
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  by_contra hn
  have he : Step S=1 := by omega
  rw [he] at hp
  obtain ⟨⟨x,hx,hxc⟩,y,hy,hcy⟩ := hs
  exact hc (apAt_fill hp hx hy hxc.le hcy.le (by simp))

theorem actual_straddling_avoids_residue {c d p : ℤ} {S : Finset ℤ}
    (hc : c∉S) (hs : StraddlesRoot c S) (hp : APAt d p S) :
    ∀ x∈S,¬d∣x-c := by
  obtain ⟨⟨a,ha,hac⟩,b,hb,hcb⟩ := hs
  intro x hx hd
  have hxa := apAt_dvd_sub hp ha hx
  have hca : d∣c-a := by
    convert Int.dvd_sub hxa hd using 1
    ring
  exact hc (apAt_fill hp ha hb hac.le hcb.le hca)

theorem actual_straddling_two_step_opposite {N : ℕ} {c p : ℤ} {S : Finset ℤ}
    (hground : S⊆Ground N) (hc : c∉S) (hs : StraddlesRoot c S)
    (hp : APAt 2 p S) : S⊆OppositeParity N c := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨hground hx,actual_straddling_avoids_residue hc hs hp x hx⟩

theorem actual_opposite_parity_card (N : ℕ) (c : ℤ) :
    2*(OppositeParity N c).card≤N+1 := by
  let f : ℤ→ℕ := fun x=>(x.toNat-1)/2
  have hm : Set.MapsTo f (OppositeParity N c : Set ℤ) (Finset.range ((N+1)/2) : Set ℕ) := by
    intro x hx
    obtain ⟨hxN,_⟩ := Finset.mem_filter.mp hx
    have hb := (mem_ground N x).mp hxN
    apply Finset.mem_range.mpr
    dsimp [f]
    omega
  have hi : Set.InjOn f (OppositeParity N c : Set ℤ) := by
    intro x hx y hy he
    obtain ⟨hxN,hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyN,hyp⟩ := Finset.mem_filter.mp hy
    have hbX := (mem_ground N x).mp hxN
    have hbY := (mem_ground N y).mp hyN
    rw [Int.dvd_iff_emod_eq_zero] at hxp hyp
    dsimp [f] at he
    omega
  have hc := Finset.card_le_card_of_injOn f hm hi
  simp only [Finset.card_range] at hc
  omega

theorem actual_opposite_parity_pool (N : ℕ) (c : ℤ) :
    (((((Ground N).erase c).powersetCard 2).filter
      (fun Q=>¬Disjoint Q (OppositeParity N c))).card:ℝ)≤3*(N:ℝ)^2/8+(N:ℝ)/2 := by
  have hP : OppositeParity N c⊆(Ground N).erase c := by
    intro x hx
    obtain ⟨hxN,hxp⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_erase.mpr ⟨?_,hxN⟩
    intro he
    subst x
    exact hxp (by simp)
  have he := MeetingPool46.actual_meeting_pairs_card_real hP
  have hcount : 2*((OppositeParity N c).card:ℝ)≤(N:ℝ)+1 := by
    exact_mod_cast actual_opposite_parity_card N c
  have hU : (((Ground N).erase c).card:ℝ)≤N := by
    exact_mod_cast (show ((Ground N).erase c).card≤N by
      have hh : ((Ground N).erase c).card≤(Ground N).card := Finset.card_erase_le
      simpa only [ground_card] using hh)
  have hPN : ((OppositeParity N c).card:ℝ)≤N := by
    exact_mod_cast (show (OppositeParity N c).card≤N by
      have hh := Finset.card_le_card (show OppositeParity N c⊆Ground N from Finset.filter_subset _ _)
      simpa only [ground_card] using hh)
  have h0 : (0:ℝ)≤(OppositeParity N c).card := Nat.cast_nonneg _
  by_cases hn : N=0
  · subst N
    have hp0 : (OppositeParity 0 c).card=0 := by
      have hh : (OppositeParity 0 c).card≤0 := by exact_mod_cast hPN
      omega
    rw [he,hp0]
    norm_num
  · have hnR : (1:ℝ)≤N := by exact_mod_cast (by omega : 1≤N)
    have hmain := mul_nonneg
      (show 0≤(N:ℝ)+1-2*(OppositeParity N c).card by linarith)
      (show 0≤3*(N:ℝ)-1-2*(OppositeParity N c).card by linarith)
    have hUcost := mul_le_mul_of_nonneg_left hU h0
    rw [he]
    nlinarith only [hmain,hUcost,h0,hnR]

theorem actual_no_large_step_two {F : Finset (Finset ℤ)} {c : ℤ}
    (hroot : ∀ S∈F,¬IsAP S → c∈S)
    (hcross : ∀ S∈F,c∉S → StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) :
    ∀ S∈Avoiders F c,Step S=2 ∧ ∃ p:ℤ,APAt 2 p S := by
  intro S hS
  obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
  have hAP : IsAP S := by by_contra hn; exact hcS (hroot S hSF hn)
  have htwo := actual_straddling_step_ge_two hcS (hcross S hSF hcS) hAP
  obtain ⟨_,p,hp⟩ := actual_step hAP
  have he : Step S=2 := by
    by_contra hn
    exact hno ⟨S,hSF,hcS,Step S,by omega,p,hp⟩
  exact ⟨he,p,by simpa only [he,Nat.cast_ofNat] using hp⟩

theorem actual_two_step_avoiders_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F)
    (hstep : ∀ S∈Avoiders F c,∃ p:ℤ,APAt 2 p S)
    (hne : ∀ S∈Avoiders F c,S.Nonempty) :
    ((Avoiders F c).card:ℝ)≤(N:ℝ)^2/16+(N:ℝ)/2+1 := by
  have hAF : Avoiders F c⊆F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (Avoiders F c) :=
    ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hn=>hF.2 S (hAF hS) T (hAF hT) hn⟩
  have hb := actual_same_step_count (d:=2) (by decide) hlegal hne hstep
  norm_num only [Nat.cast_ofNat,show (4:ℝ)*2^2=16 by norm_num] at hb
  exact hb

theorem actual_no_large_step_budget {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S → c∈S)
    (hcross : ∀ S∈F,c∉S → StraddlesRoot c S)
    (hno : ¬LargeStepAvoider F c) :
    (∀ S∈Avoiders F c,Step S=2 ∧ (∃ p:ℤ,APAt 2 p S) ∧ S⊆OppositeParity N c) ∧
      ((Avoiders F c).card:ℝ)≤(N:ℝ)^2/16+(N:ℝ)/2+1 := by
  have htwo := actual_no_large_step_two hroot hcross hno
  constructor
  · intro S hS
    obtain ⟨he,p,hp⟩ := htwo S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    exact ⟨he,⟨p,hp⟩,actual_straddling_two_step_opposite (hF.1 S hSF) hcS (hcross S hSF hcS) hp⟩
  · apply actual_two_step_avoiders_count hF (fun S hS=>(htwo S hS).2)
    intro S hS
    obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
    obtain ⟨x,hx,_⟩ := (hcross S hSF hcS).1
    exact ⟨x,hx⟩

theorem actual_cross_root_alternative {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S → c∈S)
    (hcross : ∀ S∈F,c∉S → StraddlesRoot c S) :
    LargeStepAvoider F c ∨
      ((∀ S∈Avoiders F c,Step S=2 ∧ (∃ p:ℤ,APAt 2 p S) ∧ S⊆OppositeParity N c) ∧
        ((Avoiders F c).card:ℝ)≤(N:ℝ)^2/16+(N:ℝ)/2+1) := by
  by_cases hbig : LargeStepAvoider F c
  · exact Or.inl hbig
  · exact Or.inr (actual_no_large_step_budget hF hroot hcross hbig)

theorem actual_no_one_sided_cross {F : Finset (Finset ℤ)} {c : ℤ}
    (hno : ¬∃ P∈F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)) :
    ∀ S∈F,c∉S → StraddlesRoot c S := by
  intro S hS hcS
  by_contra hn
  exact hno ⟨S,hS,hcS,actual_not_straddling_one_sided hcS hn⟩

theorem actual_one_sided_or_cross_root_alternative {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F)
    (hroot : ∀ S∈F,¬IsAP S → c∈S) :
    (∃ P∈F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)) ∨
      ((∀ S∈F,c∉S → StraddlesRoot c S) ∧
        (LargeStepAvoider F c ∨
          ((∀ S∈Avoiders F c,Step S=2 ∧ (∃ p:ℤ,APAt 2 p S) ∧ S⊆OppositeParity N c) ∧
            ((Avoiders F c).card:ℝ)≤(N:ℝ)^2/16+(N:ℝ)/2+1))) := by
  by_cases hside : ∃ P∈F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)
  · exact Or.inl hside
  · have hx := actual_no_one_sided_cross hside
    exact Or.inr ⟨hx,actual_cross_root_alternative hF hroot hx⟩

#print axioms actual_not_straddling_one_sided
#print axioms actual_straddling_card_two
#print axioms actual_straddling_step_ge_two
#print axioms actual_straddling_avoids_residue
#print axioms actual_straddling_two_step_opposite
#print axioms actual_opposite_parity_card
#print axioms actual_opposite_parity_pool
#print axioms actual_no_large_step_two
#print axioms actual_two_step_avoiders_count
#print axioms actual_no_large_step_budget
#print axioms actual_cross_root_alternative
#print axioms actual_no_one_sided_cross
#print axioms actual_one_sided_or_cross_root_alternative
end
end JSP233.Straddling47
