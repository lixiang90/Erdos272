import Erdos272.Arithmetic.DivisorMoment45
import Mathlib.Data.Int.Interval

/-! Actual cardinality payment for residue classes with step at least three. -/
namespace JSP233.ResidueSpacing46
open scoped Classical
noncomputable section

theorem actual_residue_interval_spacing {S : Finset ℤ} {a k u v : ℤ}
    (hk : 3≤k) (hsub : S⊆Finset.Icc u v)
    (hmod : ∀ x∈S,k∣x-a) :
    3*S.card≤(Finset.Icc u v).card+3 := by
  by_cases huv : u≤v
  · let code : ℤ→ℤ := fun x=>(x-u)/3
    have hm : ∀ x∈S,code x∈Finset.Icc 0 ((v-u)/3) := by
      intro x hx
      have hh := Finset.mem_Icc.mp (hsub hx)
      dsimp [code]
      exact Finset.mem_Icc.mpr (by omega)
    have hi : Set.InjOn code (S:Set ℤ) := by
      intro x hx y hy he
      have hd : k∣y-x := by
        have heq : y-x=(y-a)-(x-a) := by ring
        rw [heq]
        exact dvd_sub (hmod y hy) (hmod x hx)
      dsimp [code] at he
      by_cases hxy : x<y
      · have hb := Int.le_of_dvd (by omega : 0<y-x) hd
        omega
      · by_cases hyx : y<x
        · have hdn : k∣x-y := by simpa only [neg_sub] using dvd_neg.mpr hd
          have hb := Int.le_of_dvd (by omega : 0<x-y) hdn
          omega
        · omega
    have hc : S.card≤(Finset.Icc 0 ((v-u)/3)).card :=
      Finset.card_le_card_of_injOn code hm hi
    rw [Int.card_Icc] at hc ⊢
    omega
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := Finset.mem_Icc.mp (hsub hx)
      omega
    simp only [he,Finset.card_empty,mul_zero]
    omega

theorem actual_ground_residue_parts {N : ℕ} {P : Finset ℤ} {a k c u v : ℤ}
    (hcN : c∈Ground N) (hP : P⊆Ground N) (hcP : c∉P)
    (hu : 1≤u) (huc : u≤c) (hcv : c≤v) (hv : v≤N)
    (hk : 3≤k) (hmod : ∀ x∈P,k∣x-a) :
    3*(P\((Finset.Icc u v).erase c)).card≤
        (((Ground N).erase c)\((Finset.Icc u v).erase c)).card+6 ∧
      3*(P∩((Finset.Icc u v).erase c)).card≤
        ((Finset.Icc u v).erase c).card+4 := by
  let B := (Finset.Icc u v).erase c
  let O := P\B
  let L := O.filter (fun x=>x<u)
  let R := O.filter (fun x=>¬x<u)
  have hcB : c∈Finset.Icc u v := Finset.mem_Icc.mpr ⟨huc,hcv⟩
  have hBU : B⊆(Ground N).erase c := by
    intro x hx
    obtain ⟨hxc,hx⟩ := Finset.mem_erase.mp hx
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_erase.mpr ⟨hxc,(mem_ground N x).mpr (by omega)⟩
  have hO : ∀ x∈O,x<u ∨ v<x := by
    intro x hx
    obtain ⟨hxP,hxB⟩ := Finset.mem_sdiff.mp hx
    have hxc : x≠c := fun he=>hcP (he ▸ hxP)
    by_contra hh
    apply hxB
    exact Finset.mem_erase.mpr ⟨hxc,Finset.mem_Icc.mpr (by omega)⟩
  have hL : L⊆Finset.Icc 1 (u-1) := by
    intro x hx
    obtain ⟨hxO,hxu⟩ := Finset.mem_filter.mp hx
    have hxP := (Finset.mem_sdiff.mp hxO).1
    have hxN := (mem_ground N x).mp (hP hxP)
    exact Finset.mem_Icc.mpr (by omega)
  have hR : R⊆Finset.Icc (v+1) N := by
    intro x hx
    obtain ⟨hxO,hxu⟩ := Finset.mem_filter.mp hx
    have hxN := (mem_ground N x).mp (hP (Finset.mem_sdiff.mp hxO).1)
    have hh := hO x hxO
    exact Finset.mem_Icc.mpr (by omega)
  have hl := actual_residue_interval_spacing hk hL
    (fun x hx=>hmod x (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1)
  have hr := actual_residue_interval_spacing hk hR
    (fun x hx=>hmod x (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1)
  have hi := actual_residue_interval_spacing hk
    (show P∩B⊆Finset.Icc u v from fun x hx=>
      (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2)
    (fun x hx=>hmod x (Finset.mem_inter.mp hx).1)
  have hpart : L.card+R.card=O.card :=
    Finset.card_filter_add_card_filter_not (s:=O) (fun x=>x<u)
  have hBc : B.card+1=(Finset.Icc u v).card := by
    exact Finset.card_erase_add_one hcB
  have hUc : ((Ground N).erase c).card+1=N := by
    simpa only [ground_card] using Finset.card_erase_add_one hcN
  have hUB : (((Ground N).erase c)\B).card+B.card=((Ground N).erase c).card :=
    Finset.card_sdiff_add_card_eq_card hBU
  rw [Int.card_Icc] at hl hr hi hBc
  constructor <;> dsimp only [O,B] at * <;> omega

#print axioms actual_residue_interval_spacing
#print axioms actual_ground_residue_parts
end
end JSP233.ResidueSpacing46
