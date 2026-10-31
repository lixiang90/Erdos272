import Erdos272.Foundation.StaircaseSupply
import Erdos272.Foundation.Staircase249Block000
import Erdos272.Foundation.Staircase249Block025
import Erdos272.Foundation.Staircase249Block050
import Erdos272.Foundation.Staircase249Block075
import Erdos272.Foundation.Staircase249Block100
import Erdos272.Foundation.Staircase249Block125
import Erdos272.Foundation.Staircase249Block150
import Erdos272.Foundation.Staircase249Block175
import Erdos272.Foundation.Staircase249Block200
import Erdos272.Foundation.Staircase249Block225
import Erdos272.Foundation.Staircase249Edge

/-! Ordinary-kernel finite certificate and its actual unit-interval-family
consequence. The tables are candidates; all arithmetic and gcd recurrence
conditions are proved by decide in separately checked blocks. -/
namespace JSP233.Staircase249
open JSP233.StaircaseCertificate JSP233.StaircaseGeometry
open JSP233.StaircaseSupply JSP233.Staircase249Counts
open JSP233.Staircase249Data

theorem row_certificate (r : Fin 250) : Block r 1 := by
  by_cases h0 : (r:Nat) < 25
  · have heq : 0+((r:Nat)-0) = (r:Nat) := by omega
    simpa only [heq] using (block000.row ⟨(r:Nat)-0,by omega⟩)
  by_cases h1 : (r:Nat) < 50
  · have heq : 25+((r:Nat)-25) = (r:Nat) := by omega
    simpa only [heq] using (block025.row ⟨(r:Nat)-25,by omega⟩)
  by_cases h2 : (r:Nat) < 75
  · have heq : 50+((r:Nat)-50) = (r:Nat) := by omega
    simpa only [heq] using (block050.row ⟨(r:Nat)-50,by omega⟩)
  by_cases h3 : (r:Nat) < 100
  · have heq : 75+((r:Nat)-75) = (r:Nat) := by omega
    simpa only [heq] using (block075.row ⟨(r:Nat)-75,by omega⟩)
  by_cases h4 : (r:Nat) < 125
  · have heq : 100+((r:Nat)-100) = (r:Nat) := by omega
    simpa only [heq] using (block100.row ⟨(r:Nat)-100,by omega⟩)
  by_cases h5 : (r:Nat) < 150
  · have heq : 125+((r:Nat)-125) = (r:Nat) := by omega
    simpa only [heq] using (block125.row ⟨(r:Nat)-125,by omega⟩)
  by_cases h6 : (r:Nat) < 175
  · have heq : 150+((r:Nat)-150) = (r:Nat) := by omega
    simpa only [heq] using (block150.row ⟨(r:Nat)-150,by omega⟩)
  by_cases h7 : (r:Nat) < 200
  · have heq : 175+((r:Nat)-175) = (r:Nat) := by omega
    simpa only [heq] using (block175.row ⟨(r:Nat)-175,by omega⟩)
  by_cases h8 : (r:Nat) < 225
  · have heq : 200+((r:Nat)-200) = (r:Nat) := by omega
    simpa only [heq] using (block200.row ⟨(r:Nat)-200,by omega⟩)
  have heq : 225+((r:Nat)-225) = (r:Nat) := by omega
  simpa only [heq] using (block225.row ⟨(r:Nat)-225,by omega⟩)

theorem count_certificate : CountCertificate 249 250 Mix := by
  constructor
  · intro r
    simpa only [Nat.add_zero] using (row_certificate r).countzero ⟨0,by omega⟩
  · intro r n
    simpa only [Nat.add_zero] using (row_certificate r).countstep ⟨0,by omega⟩ n

theorem reflected_local_certificate :
    LocalCertificate 249 250 1 Score Potential Suffix := by
  refine ⟨base,?_,?_,?_,terminal⟩
  · intro r h
    simpa only [Nat.add_zero] using
      (row_certificate ⟨r,by omega⟩).majorize ⟨0,by omega⟩
        (by simpa only [Nat.add_zero] using r.isLt) h
  · intro r h
    simpa only [Nat.add_zero] using
      (row_certificate ⟨r,by omega⟩).descending ⟨0,by omega⟩
        (by simpa only [Nat.add_zero] using r.isLt) h
  · intro r h
    simpa only [Nat.add_zero] using
      (row_certificate ⟨r,by omega⟩).step ⟨0,by omega⟩
        (by simpa only [Nat.add_zero] using r.isLt) h

theorem local_certificate :
    LocalCertificate 249 250 1 ColumnScore Potential Suffix :=
  true_localCertificate count_certificate leftCertificate (by decide) reflected_local_certificate

theorem profiles_score_le_one (p : Nat → Nat)
    (hp : ∀ r ≤ 249, p r ≤ 250)
    (hmono : ∀ r < 249, p (r+1) ≤ p r) :
    ProfileScore ColumnScore p 249 ≤ 1 :=
  local_certificate_sound local_certificate p hp hmono

theorem original_defect_le_one {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) (hwidth : Width C ≤ 249)
    (hheight : Height C ≤ 249) :
    ((Family C).card : Int) - (PrimitivePool (Family C)).card ≤ 1 := by
  apply (original_defect_le_profileScore hvalid).trans
  rw [profileScore_eq_padded C 249 hwidth]
  apply profiles_score_le_one (Profile C)
  · intro r hr
    have hp := profile_height_bound C r
    omega
  · intro r hr
    exact profile_antitone C (by omega)

theorem actual_family_defect_le_one (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card ∧
      l ≤ 249 ∧ r ≤ 249) :
    (F.card : Int) - (PrimitivePool F).card ≤ 1 := by
  obtain ⟨C,hC,hvalid⟩ := exists_coordinates F (by
    intro S hS
    obtain ⟨l,r,heq,hlarge,hl,hr⟩ := hF S hS
    exact ⟨l,r,heq,hlarge⟩)
  have hcoords : ∀ p ∈ C, p.1 ≤ 249 ∧ p.2 ≤ 249 := by
    intro p hp
    have hmem : Window p.1 p.2 ∈ F := by
      rw [← hC]
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    obtain ⟨l,r,heq,hlarge,hl,hr⟩ := hF _ hmem
    have hpq : p = (l,r) := window_injective heq
    simpa only [hpq] using And.intro hl hr
  have hw : Width C ≤ 249 := Finset.sup_le fun p hp => (hcoords p hp).2
  have hh : Height C ≤ 249 := Finset.sup_le fun p hp => (hcoords p hp).1
  rw [← hC]
  exact original_defect_le_one hvalid hw hh

#print axioms row_certificate
#print axioms count_certificate
#print axioms reflected_local_certificate
#print axioms local_certificate
#print axioms profiles_score_le_one
#print axioms original_defect_le_one
#print axioms actual_family_defect_le_one
end JSP233.Staircase249
