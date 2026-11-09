module

public import Erdos272.Core.TracePacking43

@[expose] public section

/-! A common actual off-residue point forces one-point intersections of
interval traces, including traces with different steps. -/
namespace JSP233.OffResidue44
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section

theorem origin_dvd {d a x : ℤ} {S : Finset ℤ} (h : APAt d a S) (hx : x∈S) : d∣x-a := by
  obtain ⟨_,lo,hi,hr⟩ := h
  exact ((hr x).mp hx).2.2

theorem overlap_forces_alignment {S J : Finset ℤ} {L R d a y x z : ℤ}
    (htrace : APAt d a (S∩Finset.Icc L R)) (hJ : IsAP J) (hJS : J⊆S)
    (hy : y∈J) (hx : x∈J∩Finset.Icc L R) (hz : z∈J∩Finset.Icc L R)
    (hxz : x<z) : d∣y-a := by
  obtain ⟨g,b,hg,_hb⟩ := (isAP_iff_exists_APAt J).mp hJ
  have hxJ := (Finset.mem_inter.mp hx).1
  have hzJ := (Finset.mem_inter.mp hz).1
  have hxI := Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2
  have hzI := Finset.mem_Icc.mp (Finset.mem_inter.mp hz).2
  have hgz : g∣z-x := apAt_dvd_sub hg hxJ hzJ
  have hgle : g≤z-x := Int.le_of_dvd (by omega : 0<z-x) hgz
  have hnext : x+g∈J := apAt_fill hg hxJ hzJ (by linarith [hg.1]) (by omega) (by simp)
  have hxS : x∈S∩Finset.Icc L R := Finset.mem_inter.mpr ⟨hJS hxJ,(Finset.mem_inter.mp hx).2⟩
  have hnS : x+g∈S∩Finset.Icc L R := Finset.mem_inter.mpr
    ⟨hJS hnext,Finset.mem_Icc.mpr ⟨by linarith [hg.1],by omega⟩⟩
  have hdg : d∣g := by
    have hh := apAt_dvd_sub htrace hxS hnS
    convert hh using 1
    ring
  have hdy : d∣y-x := dvd_trans hdg (apAt_dvd_sub hg hxJ hy)
  have hda : d∣x-a := origin_dvd htrace hxS
  have hh := Int.dvd_add hdy hda
  convert hh using 1
  ring

theorem off_point_trace_inter_card {S T : Finset ℤ} {L R d a y : ℤ}
    (htrace : APAt d a (S∩Finset.Icc L R)) (hpair : IsAP (S∩T))
    (hyS : y∈S) (hyT : y∈T) (hoff : ¬d∣y-a) :
    ((S∩Finset.Icc L R)∩(T∩Finset.Icc L R)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx z hz
  have hxJ : x∈(S∩T)∩Finset.Icc L R := Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2⟩
  have hzJ : z∈(S∩T)∩Finset.Icc L R := Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).1⟩,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2⟩
  have hyJ : y∈S∩T := Finset.mem_inter.mpr ⟨hyS,hyT⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hoff (overlap_forces_alignment htrace hpair Finset.inter_subset_left hyJ hxJ hzJ h)
  · exact hoff (overlap_forces_alignment htrace hpair Finset.inter_subset_left hyJ hzJ hxJ h)

def OffPoint (F : Finset (Finset ℤ)) (d a : Finset ℤ→ℤ) (y : ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S=>y∈S ∧ ¬d S∣y-a S)

def OffMembers (F : Finset (Finset ℤ)) (d a : Finset ℤ→ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S=>∃ y∈S,¬d S∣y-a S)

theorem actual_off_point_capacity (Ω : Finset ℤ) (F : Finset (Finset ℤ)) (L R : ℤ)
    (d a : Finset ℤ→ℤ) (y : ℤ) (p : ℕ) (hp : 0<p) (hN : p^3≤Ω.card)
    (hlegal : Legal Ω F) (htrace : ∀ S∈F,APAt (d S) (a S) (S∩Finset.Icc L R))
    (hlong : ∀ S∈F,Ω.card<p*(S∩Finset.Icc L R).card) :
    (OffPoint F d a y).card≤p := by
  apply TracePacking43.actual_long_trace_capacity_cubic Ω (OffPoint F d a y)
    (fun S=>S∩Finset.Icc L R) p hp hN
  · intro S hS x hx
    exact hlegal.1 S (Finset.mem_filter.mp hS).1 (Finset.mem_inter.mp hx).1
  · intro S hS
    exact hlong S (Finset.mem_filter.mp hS).1
  · intro S hS T hT hne
    obtain ⟨hSF,hyS,hoff⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF,hyT,_hoffT⟩ := Finset.mem_filter.mp hT
    exact off_point_trace_inter_card (htrace S hSF) (hlegal.2 S hSF T hTF hne) hyS hyT hoff

theorem actual_off_residue_count (Ω : Finset ℤ) (F : Finset (Finset ℤ)) (L R : ℤ)
    (d a : Finset ℤ→ℤ) (p : ℕ) (hp : 0<p) (hN : p^3≤Ω.card)
    (hlegal : Legal Ω F) (htrace : ∀ S∈F,APAt (d S) (a S) (S∩Finset.Icc L R))
    (hlong : ∀ S∈F,Ω.card<p*(S∩Finset.Icc L R).card) :
    (OffMembers F d a).card≤p*(Ω\Finset.Icc L R).card := by
  have hcover : OffMembers F d a⊆(Ω\Finset.Icc L R).biUnion (OffPoint F d a) := by
    intro S hS
    obtain ⟨hSF,y,hyS,hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y∉Finset.Icc L R := by
      intro hyI
      exact hoff (origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hlegal.1 S hSF hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hSF,hyS,hoff⟩⟩
  calc
    _≤((Ω\Finset.Icc L R).biUnion (OffPoint F d a)).card := Finset.card_le_card hcover
    _≤∑ y∈Ω\Finset.Icc L R,(OffPoint F d a y).card := Finset.card_biUnion_le
    _≤∑ _y∈Ω\Finset.Icc L R,p := Finset.sum_le_sum (by
      intro y hy
      exact actual_off_point_capacity Ω F L R d a y p hp hN hlegal htrace hlong)
    _=p*(Ω\Finset.Icc L R).card := by simp [Nat.mul_comm]

#print axioms origin_dvd
#print axioms overlap_forces_alignment
#print axioms off_point_trace_inter_card
#print axioms actual_off_point_capacity
#print axioms actual_off_residue_count
end
end JSP233.OffResidue44
