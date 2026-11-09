module

public import Erdos272.Geometry.BlockAP119
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic

@[expose] public section

/-! Compatible actual truncated APs pay their overlap in integer unit
segments. A common point repeats with period d*e, or d when d=e. -/
namespace JSP233.PhaseOverlap208
open StarCompletion APGeometry PeriodOff117
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Period (d e : ℕ) : ℕ := if d=e then d else d*e

theorem period_pos {d e : ℕ} (hd : 0<d) (he : 0<e) : 0<Period d e := by
  unfold Period
  split_ifs <;> positivity

theorem period_dvd_left (d e : ℕ) : d∣Period d e := by
  unfold Period
  split_ifs
  · exact dvd_refl d
  · exact dvd_mul_right d e

theorem period_dvd_right (d e : ℕ) : e∣Period d e := by
  unfold Period
  split_ifs with h
  · rw [h]
  · exact dvd_mul_left e d

theorem actual_overlap_card {S T : Finset ℤ} {d e : ℕ} {a b lo hi low high : ℤ}
    (hd : 0<d) (he : 0<e) (hS : APAt (d : ℤ) a S) (hT : APAt (e : ℤ) b T)
    (hlo : lo∈S) (hhi : hi∈S) (hlow : low∈T) (hhigh : high∈T)
    (hpair : (S∩T).card≤1)
    (hcompat : ∃z : ℤ,(d : ℤ)∣z-a ∧ (e : ℤ)∣z-b) :
    ((Finset.Ico lo hi)∩Finset.Ico low high).card≤2*Period d e := by
  obtain ⟨z,hzd,hze⟩ := hcompat
  let A := max lo low
  let B := min hi high
  have hspan : (Finset.Ico lo hi)∩Finset.Ico low high=Finset.Ico A B := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_Ico,A,B,max_le_iff,lt_min_iff]
    tauto
  by_contra hbig
  have hbig' : 2*Period d e≤((Finset.Ico lo hi)∩Finset.Ico low high).card := by omega
  rw [hspan,Int.card_Ico] at hbig'
  have hp := period_pos hd he
  have hsize : (Period d e : ℤ)*2≤B-A+1 := by omega
  obtain ⟨H,hH,hHc,hHz⟩ := interval_period_holes (Period d e) 2 A B z hp hsize
  have hdp : (d : ℤ)∣(Period d e : ℤ) := by exact_mod_cast period_dvd_left d e
  have hep : (e : ℤ)∣(Period d e : ℤ) := by exact_mod_cast period_dvd_right d e
  have hsub : H⊆S∩T := by
    intro x hx
    have hxb := Finset.mem_Icc.mp (hH hx)
    have hxl : lo≤x ∧ low≤x := by
      have hh := hxb.1
      dsimp only [A] at hh
      exact max_le_iff.mp hh
    have hxu : x≤hi ∧ x≤high := by
      have hh := hxb.2
      dsimp only [B] at hh
      exact le_min_iff.mp hh
    have hxd := Int.dvd_add (dvd_trans hdp (hHz x hx)) hzd
    have hxe := Int.dvd_add (dvd_trans hep (hHz x hx)) hze
    apply Finset.mem_inter.mpr
    constructor
    · apply apAt_fill hS hlo hhi hxl.1 hxu.1
      have hh := Int.dvd_sub hxd (OffResidue44.origin_dvd hS hlo)
      convert hh using 1 <;> ring
    · apply apAt_fill hT hlow hhigh hxl.2 hxu.2
      have hh := Int.dvd_sub hxe (OffResidue44.origin_dvd hT hlow)
      convert hh using 1 <;> ring
  have hc := Finset.card_le_card hsub
  omega

theorem period_weight {d e : ℕ} (hd : 2≤d) (hd11 : d≤11) (he : 2≤e) (he11 : e≤11) :
    min (1/(d : ℝ)) (1/(e : ℝ))*(2*(Period d e : ℝ))≤20 := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have heR : (0 : ℝ)<e := by exact_mod_cast (show 0<e by omega)
  by_cases hde : d=e
  · subst e
    simp only [Period,ite_true,min_self,Nat.cast_mul,Nat.cast_ofNat]
    have hid : 1/(d : ℝ)*(2*(d : ℝ))=2 := by field_simp
    rw [hid]
    norm_num
  · simp only [Period,if_neg hde,Nat.cast_mul]
    rcases le_total d e with hle | hle
    · have hd10 : d≤10 := by omega
      have hm := mul_le_mul_of_nonneg_right (min_le_right (1/(d : ℝ)) (1/(e : ℝ)))
        (show (0 : ℝ)≤2*((d : ℝ)*e) by positivity)
      have hid : 1/(e : ℝ)*(2*((d : ℝ)*e))=2*(d : ℝ) := by field_simp
      rw [hid] at hm
      have hu : (d : ℝ)≤10 := by exact_mod_cast hd10
      linarith only [hm,hu]
    · have he10 : e≤10 := by omega
      have hm := mul_le_mul_of_nonneg_right (min_le_left (1/(d : ℝ)) (1/(e : ℝ)))
        (show (0 : ℝ)≤2*((d : ℝ)*e) by positivity)
      have hid : 1/(d : ℝ)*(2*((d : ℝ)*e))=2*(e : ℝ) := by field_simp
      rw [hid] at hm
      have hu : (e : ℝ)≤10 := by exact_mod_cast he10
      linarith only [hm,hu]

theorem actual_overlap_weight {S T : Finset ℤ} {d e : ℕ} {a b lo hi low high : ℤ}
    (hd : 2≤d) (hd11 : d≤11) (he : 2≤e) (he11 : e≤11)
    (hS : APAt (d : ℤ) a S) (hT : APAt (e : ℤ) b T)
    (hlo : lo∈S) (hhi : hi∈S) (hlow : low∈T) (hhigh : high∈T)
    (hpair : (S∩T).card≤1)
    (hcompat : ∃z : ℤ,(d : ℤ)∣z-a ∧ (e : ℤ)∣z-b) :
    min (1/(d : ℝ)) (1/(e : ℝ))*
      (((Finset.Ico lo hi)∩Finset.Ico low high).card : ℝ)≤20 := by
  have hc := actual_overlap_card (by omega : 0<d) (by omega : 0<e)
    hS hT hlo hhi hlow hhigh hpair hcompat
  have hcR : (((Finset.Ico lo hi)∩Finset.Ico low high).card : ℝ)≤2*(Period d e : ℝ) := by
    exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hcR
    (show (0 : ℝ)≤min (1/(d : ℝ)) (1/(e : ℝ)) by positivity)
  exact hm.trans (period_weight hd hd11 he he11)

#print axioms actual_overlap_card
#print axioms period_weight
#print axioms actual_overlap_weight
end
end JSP233.PhaseOverlap208
