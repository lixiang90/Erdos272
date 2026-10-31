import Erdos272.Counting.PeriodOff117
import Erdos272.Retention.BadFringe115
import Mathlib.Data.Int.ModEq

/-! Actual360-point blocks of truncated arithmetic progressions. Complete
classes are derived from actual AP endpoints. A repeated compatible class
would manufacture two actual intersection points inside the same block. -/
namespace JSP233.BlockAP119
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Block (A : ℤ) : Finset ℤ := Finset.Icc A (A+359)

def Complete (S : Finset ℤ) (d : ℕ) (a A : ℤ) : Prop :=
  ∀z∈Block A,z∈S ↔ (d:ℤ)∣z-a

def Code (d : ℕ) (a y : ℤ) : ℕ×ℕ :=
  (d,((a-y)%(d:ℤ)).toNat)

theorem block_card (A : ℤ) : (Block A).card=360 := by
  simp only [Block,Int.card_Icc]
  omega

theorem actual_complete_of_endpoints {S : Finset ℤ} {d : ℕ} {a A lo hi : ℤ}
    (hAP : APAt (d:ℤ) a S) (hlo : lo∈S) (hhi : hi∈S)
    (hl : lo≤A) (hh : A+359≤hi) : Complete S d a A := by
  intro z hz
  have hzB := Finset.mem_Icc.mp hz
  constructor
  · exact OffResidue44.origin_dvd hAP
  · intro hzmod
    have hmod := Int.dvd_sub hzmod (OffResidue44.origin_dvd hAP hlo)
    apply apAt_fill hAP hlo hhi (by omega) (by omega)
    convert hmod using 1
    ring

theorem actual_complete_classes_separated {S T : Finset ℤ} {d e : ℕ} {a b A : ℤ}
    (hd : 0<d) (he : 0<e) (hdU : d≤12) (heU : e≤12)
    (hS : Complete S d a A) (hT : Complete T e b A)
    (hpair : (S∩T).card≤1) :
    ∀z:ℤ,¬((d:ℤ)∣z-a ∧ (e:ℤ)∣z-b) := by
  intro z hz
  have hD : 0<d*e := Nat.mul_pos hd he
  have hsize : ((d*e:ℕ):ℤ)*2≤(A+359)-A+1 := by
    have hmul : d*e≤144 := Nat.mul_le_mul hdU heU
    have hc : ((d*e:ℕ):ℤ)*2≤360 := by exact_mod_cast (show (d*e)*2≤360 by omega)
    omega
  obtain ⟨H,hHB,hHc,hmod⟩ := PeriodOff117.interval_period_holes (d*e) 2 A (A+359) z hD hsize
  have hsub : H⊆S∩T := by
    intro x hx
    have hxB : x∈Block A := hHB hx
    have hdx : (d:ℤ)∣x-z := dvd_trans (by exact ⟨(e:ℤ),by simp⟩) (hmod x hx)
    have hex : (e:ℤ)∣x-z := dvd_trans (by exact ⟨(d:ℤ),by simp [mul_comm]⟩) (hmod x hx)
    apply Finset.mem_inter.mpr
    constructor
    · apply (hS x hxB).mpr
      convert Int.dvd_add hdx hz.1 using 1
      ring
    · apply (hT x hxB).mpr
      convert Int.dvd_add hex hz.2 using 1
      ring
  have hc := Finset.card_le_card hsub
  omega

theorem code_cast {d : ℕ} (hd : 0<d) (a y : ℤ) :
    ((Code d a y).2:ℤ)=(a-y)%(d:ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd.ne'))

theorem code_residue_iff {d : ℕ} (hd : 0<d) (a y : ℤ) (z : ℕ) :
    (d:ℤ)∣(y+(z:ℤ))-a ↔ z%d=(Code d a y).2 := by
  have he : (y+(z:ℤ))-a=(z:ℤ)-(a-y) := by ring
  rw [he,Int.dvd_iff_emod_eq_zero,←Int.emod_eq_emod_iff_emod_sub_eq_zero]
  rw [←code_cast hd a y]
  norm_cast

theorem actual_off_code_bounds {d : ℕ} {a y : ℤ}
    (hd : 0<d) (hdu : d≤12) (hoff : ¬(d:ℤ)∣y-a) :
    2≤d ∧ d≤12 ∧ 1≤(Code d a y).2 ∧ (Code d a y).2<d := by
  have hpos : (0:ℤ)<d := by exact_mod_cast hd
  have hr := code_cast hd a y
  have hrem0 := Int.emod_nonneg (a-y) (by omega : (d:ℤ)≠0)
  have hremlt := Int.emod_lt_of_pos (a-y) hpos
  have hrlt : (Code d a y).2<d := by omega
  have hne : (Code d a y).2≠0 := by
    intro hz
    have he : (a-y)%(d:ℤ)=0 := by omega
    have hh := Int.dvd_iff_emod_eq_zero.mpr he
    apply hoff
    convert Int.dvd_neg.mpr hh using 1
    ring
  have hd2 : 2≤d := by
    by_contra hh
    have he : d=1 := by omega
    apply hoff
    simp only [he,Nat.cast_one,one_dvd]
  exact ⟨hd2,hdu,by omega,hrlt⟩

theorem actual_complete_code_injective {F : Finset (Finset ℤ)}
    (T : Finset ℤ→Finset ℤ) (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ) (y A : ℤ)
    (hd : ∀S∈F,0<d S ∧ d S≤12)
    (hc : ∀S∈F,Complete (T S) (d S) (a S) A)
    (hoff : ∀S∈F,¬((d S:ℕ):ℤ)∣y-a S)
    (hpair : ∀S∈F,∀U∈F,S≠U→((T S)∩(T U)).card≤1) :
    Set.InjOn (fun S=>Code (d S) (a S) y) F := by
  intro S hS U hU heq
  by_contra hne
  have hs := actual_complete_classes_separated (hd S hS).1 (hd U hU).1
    (hd S hS).2 (hd U hU).2 (hc S hS) (hc U hU) (hpair S hS U hU hne)
  let z := (Code (d S) (a S) y).2
  have hbd := actual_off_code_bounds (hd S hS).1 (hd S hS).2 (hoff S hS)
  have hdz : z%d S=z := Nat.mod_eq_of_lt hbd.2.2.2
  have hcodeD : d S=d U := congrArg Prod.fst heq
  have hcodeR : (Code (d S) (a S) y).2=(Code (d U) (a U) y).2 := congrArg Prod.snd heq
  have hzS : (d S:ℤ)∣(y+(z:ℤ))-a S := (code_residue_iff (hd S hS).1 _ _ z).mpr hdz
  have hzU : (d U:ℤ)∣(y+(z:ℤ))-a U := (code_residue_iff (hd U hU).1 _ _ z).mpr (by
    calc
      z%d U=z%d S := by rw [hcodeD]
      _=z := hdz
      _=(Code (d U) (a U) y).2 := hcodeR)
  exact hs (y+(z:ℤ)) ⟨hzS,hzU⟩

theorem actual_block_trace_card {S : Finset ℤ} {d : ℕ} {a A : ℤ}
    (hd : 0<d) (hAP : APAt (d:ℤ) a S) :
    (S∩Block A).card≤359/d+1 := by
  by_cases hne : (S∩Block A).Nonempty
  · have hp := BadFringe115.restrict_APAt (a:=A) (z:=A+359) hAP
    change APAt (d:ℤ) a (S∩Block A) at hp
    have hspan := apAt_span_eq hp hne
    have hlo := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2
    have hhi := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.max'_mem _ hne)).2
    have hcardpos := Finset.card_pos.mpr hne
    have hsub : (((S∩Block A).card-1:ℕ):ℤ)=((S∩Block A).card:ℤ)-1 := by omega
    have hsize : (d:ℤ)*(((S∩Block A).card-1:ℕ):ℤ)≤359 := by
      rw [hsub]
      omega
    have hm : ((S∩Block A).card-1)*d≤359 := by
      have he : (((S∩Block A).card-1:ℕ):ℤ)*(d:ℤ)≤359 := by nlinarith only [hsize]
      exact_mod_cast he
    have hb : (S∩Block A).card-1≤359/d := (Nat.le_div_iff_mul_le hd).mpr hm
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.zero_le]

#print axioms block_card
#print axioms actual_complete_of_endpoints
#print axioms actual_complete_classes_separated
#print axioms code_cast
#print axioms code_residue_iff
#print axioms actual_off_code_bounds
#print axioms actual_complete_code_injective
#print axioms actual_block_trace_card
end
end JSP233.BlockAP119
