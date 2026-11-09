module

public import Erdos272.Resources.BandSystem208
public import Erdos272.Resources.LightActualPrice208

@[expose] public section

namespace JSP233.BandLabels208
open StarCompletion APGeometry SourceBridge208 ShiftedBlocks208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def Swap (q : ℕ × ℕ) : ℕ × ℕ := (q.2,q.1+1)

theorem swap_injective : Function.Injective Swap := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  simp only [Swap,Prod.mk.injEq] at he
  have hac : a=c := by omega
  exact Prod.ext hac he.1

theorem label_swap (a : Finset ℤ → ℕ) (d B : ℕ) (S : Finset ℤ) :
    LightPhases208.Label a d B S=Swap (Code d B (a S)) := rfl

theorem fiber_eq (F : Finset (Finset ℤ)) (a : Finset ℤ → ℕ) (d B : ℕ) (q : ℕ × ℕ) :
    F.filter (fun S => LightPhases208.Label a d B S=Swap q)=BandSystem208.Fiber F d B a q := by
  ext S
  simp only [BandSystem208.Fiber,Finset.mem_filter,label_swap,swap_injective.eq_iff]

theorem actual_heavy_image {N d T E B U : ℕ} {F : Finset (Finset ℤ)} (a : Finset ℤ → ℕ)
    (hmap : ∀ S ∈ F, LightPhases208.Label a d B S ∈ LightPhases208.Indices N d (T-E) B) :
    (BandSystem208.Heavy N d B U E F a).image Swap=
      LightPhases208.Heavy N d T E B (U+B-3) F a := by
  ext i
  constructor
  · intro hi
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hqimage,hqheavy⟩ := Finset.mem_filter.mp hq
    obtain ⟨S,hSF,hSq⟩ := Finset.mem_image.mp hqimage
    have hm : Swap q ∈ LightPhases208.Indices N d (T-E) B := by
      simpa only [label_swap,hSq] using hmap S hSF
    apply Finset.mem_filter.mpr
    refine ⟨hm,?_⟩
    rw [fiber_eq]
    exact hqheavy
  · intro hi
    obtain ⟨hiI,hiH⟩ := Finset.mem_filter.mp hi
    have hp : 0 < (F.filter (fun S => LightPhases208.Label a d B S=i)).card := by omega
    obtain ⟨S,hS⟩ := Finset.card_pos.mp hp
    obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
    have heq : Swap (Code d B (a S))=i := by simpa only [label_swap] using hSi
    apply Finset.mem_image.mpr
    refine ⟨Code d B (a S),Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S,hSF,rfl⟩,?_⟩,heq⟩
    rw [←heq] at hiH
    rw [fiber_eq] at hiH
    exact hiH

theorem actual_heavy_card {N d T E B U : ℕ} {F : Finset (Finset ℤ)} (a : Finset ℤ → ℕ)
    (hmap : ∀ S ∈ F, LightPhases208.Label a d B S ∈ LightPhases208.Indices N d (T-E) B) :
    (LightPhases208.Heavy N d T E B (U+B-3) F a).card=
      (BandSystem208.Heavy N d B U E F a).card := by
  rw [←actual_heavy_image a hmap]
  exact Finset.card_image_of_injective _ swap_injective

#print axioms actual_heavy_image
#print axioms actual_heavy_card
end
end JSP233.BandLabels208
