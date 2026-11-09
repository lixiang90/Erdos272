module

public import Erdos272.Counting.FullResidueBudget119
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Cast.Field

@[expose] public section

/-! A finite dual for the ordinary moduli at most eleven. The exceptional
prime moduli seven and eleven force all disjoint classes to share that modulus. -/
namespace JSP233.PhaseDensity208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Ordinary : Finset ℕ := {2,3,4,5,6,8,9,10}

def Weight (z : ℕ) : ℕ := match Nat.gcd z 360 with
  | 1 => 21 | 2 => 43 | 3 => 45 | 4 => 34 | 5 => 36
  | 12 => 33 | 18 => 12 | 24 => 27 | _ => 0

def Codes : Finset (ℕ×ℕ) := (Finset.Icc 2 11).biUnion
  (fun d => ((Finset.range d).erase 0).image (fun r => (d,r)))

def OrdinaryCodes : Finset (ℕ×ℕ) := Ordinary.biUnion
  (fun d => ((Finset.range d).erase 0).image (fun r => (d,r)))

def Mass (c : ℕ×ℕ) : ℕ := ∑z∈Finset.range 360, if z%c.1=c.2 then Weight z else 0

theorem weight_check : (∑z∈Finset.range 360, Weight z)=7776 := by decide +kernel

theorem mass_check : ∀c∈OrdinaryCodes, 24*(360/c.1) ≤ Mass c := by decide +kernel

theorem mem_codes {c : ℕ×ℕ} : c∈Codes ↔ 2≤c.1 ∧ c.1≤11 ∧ 0<c.2 ∧ c.2<c.1 := by
  rcases c with ⟨d,r⟩
  simp only [Codes, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_erase, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    rcases hab with ⟨rfl,rfl⟩
    exact ⟨ha.1,ha.2,by omega,hb.2⟩
  · rintro ⟨hd2,hd11,hr0,hrd⟩
    exact ⟨d,⟨hd2,hd11⟩,r,⟨by omega,hrd⟩,rfl,rfl⟩

theorem codes_subset : Codes ⊆ FullResidueBudget119.AllCodes := by
  intro c hc
  have hh := mem_codes.mp hc
  exact FullResidueBudget119.mem_allCodes.mpr ⟨hh.1,by omega,hh.2.2⟩

theorem ordinary_budget (C : Finset (ℕ×ℕ)) (hC : C⊆OrdinaryCodes)
    (hdisj : ∀z∈Finset.range 360,(C.filter (fun c => z%c.1=c.2)).card≤1) :
    ∑c∈C,360/c.1≤324 := by
  have hs := Finset.sum_le_sum (fun c hc => mass_check c (hC hc))
  have hlocal : ∀z∈Finset.range 360,
      (∑c∈C, if z%c.1=c.2 then Weight z else 0)≤Weight z := by
    intro z hz
    have he : (∑c∈C,if z%c.1=c.2 then Weight z else 0)=
        (C.filter (fun c => z%c.1=c.2)).card*Weight z := by
      rw [←Finset.sum_filter]
      simp
    rw [he]
    have hh := Nat.mul_le_mul_right (Weight z) (hdisj z hz)
    simpa only [one_mul] using hh
  have hb := Finset.sum_le_sum hlocal
  have he : (∑c∈C,Mass c)=∑z∈Finset.range 360,∑c∈C,
      if z%c.1=c.2 then Weight z else 0 := by
    unfold Mass
    exact Finset.sum_comm
  rw [←he,weight_check] at hb
  rw [←Finset.mul_sum] at hs
  omega

theorem ordinary_divides : ∀d∈Ordinary, d∣360 := by decide

theorem actual_disjoint_density (C : Finset (ℕ×ℕ)) (hC : C⊆Codes)
    (hdisj : ∀z : ℕ,(C.filter (fun c => z%c.1=c.2)).card≤1) :
    (∑c∈C,1/(c.1 : ℝ))≤10/11 := by
  have hC12 := hC.trans codes_subset
  by_cases hex : ∃a∈C, a.1∈({7,11} : Finset ℕ)
  · obtain ⟨a,ha,hap⟩ := hex
    have hmod := FullResidueBudget119.all_same_modulus_of_special hC12 hdisj hap ⟨a,ha,rfl⟩
    have hp : a.1=7 ∨ a.1=11 := by simpa using hap
    have hpos : 0<a.1 := by omega
    have hc := FullResidueBudget119.same_modulus_card hC12 hpos hmod
    have he : (∑c∈C,1/(c.1 : ℝ))=(C.card : ℝ)/a.1 := by
      calc
        _ = ∑_c∈C,1/(a.1 : ℝ) := Finset.sum_congr rfl (fun c hc => by rw [hmod c hc])
        _ = _ := by simp [div_eq_mul_inv]
    rw [he]
    rcases hp with hp | hp
    · rw [hp] at hc ⊢
      have hcr : (C.card : ℝ)≤6 := by exact_mod_cast hc
      norm_num
      linarith only [hcr]
    · rw [hp] at hc ⊢
      have hcr : (C.card : ℝ)≤10 := by exact_mod_cast hc
      norm_num
      linarith only [hcr]
  · have hsub : C⊆OrdinaryCodes := by
      intro c hc
      have hv := mem_codes.mp (hC hc)
      have h7 : c.1≠7 := by intro h;exact hex ⟨c,hc,by simp [h]⟩
      have h11 : c.1≠11 := by intro h;exact hex ⟨c,hc,by simp [h]⟩
      have hd : c.1∈Ordinary := by
        have hl := hv.1
        have hu := hv.2.1
        interval_cases c.1 <;> norm_num [Ordinary] at *
      exact Finset.mem_biUnion.mpr ⟨c.1,hd,Finset.mem_image.mpr
        ⟨c.2,Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr hv.2.2.2⟩,Prod.eta c⟩⟩
    have hb := ordinary_budget C hsub (fun z _ => hdisj z)
    have he : (∑c∈C, ((360/c.1 : ℕ) : ℝ))=360*(∑c∈C,1/(c.1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have ho := Finset.mem_biUnion.mp (hsub hc)
      obtain ⟨d,hd,hr⟩ := ho
      obtain ⟨r,hr,hEq⟩ := Finset.mem_image.mp hr
      have heqd : d=c.1 := congrArg Prod.fst hEq
      have hdiv := ordinary_divides c.1 (heqd ▸ hd)
      have hd0 : (c.1 : ℝ)≠0 := by
        have hh := (mem_codes.mp (hC hc)).1
        have hp : (0 : ℝ)<c.1 := by exact_mod_cast (show 0<c.1 by omega)
        exact hp.ne'
      rw [Nat.cast_div hdiv hd0]
      norm_num only [Nat.cast_ofNat]
      ring
    have hbR : (∑c∈C,((360/c.1 : ℕ) : ℝ))≤324 := by exact_mod_cast hb
    rw [he] at hbR
    linarith only [hbR]

#print axioms weight_check
#print axioms mass_check
#print axioms actual_disjoint_density
end
end JSP233.PhaseDensity208
