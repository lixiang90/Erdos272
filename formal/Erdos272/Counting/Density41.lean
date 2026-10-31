import Erdos272.Counting.APCount41
import Erdos272.Core.DenseSharper41
import Erdos272.Global.StartupSeeds40
import Mathlib.Data.Nat.Choose.Cast

/-! The actual original family supplies its sparse crooked density internally. -/
namespace JSP233.Density41
open StarCompletion DenseDeletion40 DenseSharper41 APCount41
open scoped Classical BigOperators
noncomputable section

def APPart (F : Finset (Finset ℤ)) : Finset (Finset ℤ) := F.filter IsAP

def SparseCrooked (N r : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (Retained N r F).filter (fun S => ¬IsAP S)

theorem actual_sparse_membership {N r : ℕ} {F : Finset (Finset ℤ)} {S : Finset ℤ} :
    S∈SparseCrooked N r F ↔ S∈F ∧ ¬IsAP S ∧ r*S.card≤N := by
  constructor
  · intro hS
    obtain ⟨hG,hbad⟩ := Finset.mem_filter.mp hS
    exact ⟨(Finset.mem_sdiff.mp hG).1,hbad,actual_retained_crooked_sparse hG hbad⟩
  · rintro ⟨hSF,hbad,hsparse⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hSF,?_⟩,hbad⟩
    intro he
    have hh := (Finset.mem_filter.mp he).2.2
    omega

theorem actual_sparse_subset (N r : ℕ) (F : Finset (Finset ℤ)) : SparseCrooked N r F⊆F := by
  intro S hS
  exact (actual_sparse_membership.mp hS).1

theorem actual_sparse_legal {N r : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) : Legal (Ground N) (SparseCrooked N r F) :=
  ⟨fun S hS => hlegal.1 S (actual_sparse_subset N r F hS),
    fun S hS T hT hne => hlegal.2 S (actual_sparse_subset N r F hS)
      T (actual_sparse_subset N r F hT) hne⟩

theorem actual_AP_part_legal {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) : Legal (Ground N) (APPart F) :=
  ⟨fun S hS => hlegal.1 S (Finset.mem_filter.mp hS).1,
    fun S hS T hT hne => hlegal.2 S (Finset.mem_filter.mp hS).1
      T (Finset.mem_filter.mp hT).1 hne⟩

theorem actual_AP_part_retained (N r : ℕ) (F : Finset (Finset ℤ)) :
    (Retained N r F).filter IsAP=APPart F := by
  ext S
  constructor
  · intro hS
    obtain ⟨hG,hAP⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hG).1,hAP⟩
  · intro hS
    obtain ⟨hSF,hAP⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨actual_ap_retained hSF hAP,hAP⟩

theorem actual_retained_partition (N r : ℕ) (F : Finset (Finset ℤ)) :
    (APPart F).card+(SparseCrooked N r F).card=(Retained N r F).card := by
  have hh := Finset.card_filter_add_card_filter_not (s:=Retained N r F) IsAP
  rwa [actual_AP_part_retained] at hh

theorem actual_original_three_part_partition (N r : ℕ) (F : Finset (Finset ℤ)) :
    (APPart F).card+(SparseCrooked N r F).card+(Deleted N r F).card=F.card := by
  rw [actual_retained_partition]
  exact actual_deletion_card_identity N r F

theorem actual_sparse_density_from_deleted_bound {N r J D : ℕ} {F : Finset (Finset ℤ)} {d : ℝ}
    (hN : N<2^J) (hlegal : Legal (Ground N) F) (hdense : d≤F.card)
    (hdel : (Deleted N r F).card≤D*N) :
    d-5*(N:ℝ)^2/12-(7/10:ℝ)*(N:ℝ)*J-((D:ℝ)+2)*N-1≤
      (SparseCrooked N r F).card := by
  have hAP := actual_AP_count_dyadic hN (actual_AP_part_legal hlegal)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hpart := actual_original_three_part_partition N r F
  have hpartR : ((APPart F).card:ℝ)+(SparseCrooked N r F).card+(Deleted N r F).card=F.card := by
    exact_mod_cast hpart
  have hdelR : ((Deleted N r F).card:ℝ)≤(D:ℝ)*N := by exact_mod_cast hdel
  nlinarith only [hAP,hpartR,hdelR,hdense]

theorem actual_counterexample_density {N : ℕ} {F : Finset (Finset ℤ)}
    (hcounter : B N<F.card) : (N:ℝ)^2/2-(N:ℝ)≤F.card := by
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter; omega
  have hr : (N.choose 2:ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hr
  have hN0 : (0:ℝ)≤N := by positivity
  nlinarith only [hr,hN0]

theorem actual_sparse_density_old {N r J : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hNr : 4*r≤N) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    (N:ℝ)^2/12-((8*(r:ℝ)^2)+(7/10:ℝ)*J+3)*N-1≤(SparseCrooked N r F).card := by
  have hh := actual_sparse_density_from_deleted_bound hN hlegal
    (actual_counterexample_density hcounter) (actual_dense_deletion_bound hr hNr hlegal)
  push_cast at hh
  nlinarith only [hh]

theorem actual_sparse_density_sharp {N r J : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hNr : (4*r^2+1)*(2*r-1)≤N) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    (N:ℝ)^2/12-((4*(r:ℝ)^2+1)+(7/10:ℝ)*J+3)*N-1≤(SparseCrooked N r F).card := by
  have hh := actual_sparse_density_from_deleted_bound hN hlegal
    (actual_counterexample_density hcounter) (actual_deleted_sharp hr hNr hlegal)
  push_cast at hh
  nlinarith only [hh]

theorem actual_sparse_density_original_budget {N r J : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hNr : 4*r≤N) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcounter : B N<F.card) :
    (N:ℝ)^2/12-(8*(r:ℝ)^2+J+21)*N-3≤(SparseCrooked N r F).card := by
  have hh := actual_sparse_density_old hr hNr hN hlegal hcounter
  have hp := mul_nonneg (show (0:ℝ)≤N by positivity) (show (0:ℝ)≤J by positivity)
  have hN0 : (0:ℝ)≤N := by positivity
  nlinarith only [hh,hp,hN0]

theorem actual_original_sparse_root28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hcounter : B N<F.card) : ∃ c∈Ground N,∀ S∈SparseCrooked N 28 F,c∈S := by
  have hNr : (4*28^2+1)*(2*28-1)≤N := (by norm_num : (4*28^2+1)*(2*28-1)≤(2:ℕ)^49).trans hNl
  have hd := actual_sparse_density_sharp (by decide : 0<28) hNr hNu hlegal hcounter
  have hN0 : (0:ℝ)≤N := by positivity
  have hdense : (N:ℝ)^2/12-6372*(N:ℝ)-3≤(SparseCrooked N 28 F).card := by
    norm_num only [Nat.cast_ofNat] at hd
    nlinarith only [hd,hN0]
  apply StartupSeeds40.actual_sparse_common_root hNl hNu (actual_sparse_legal hlegal)
    (fun S hS => (actual_sparse_membership.mp hS).2.1)
    (fun S hS => (actual_sparse_membership.mp hS).2.2) hdense

theorem actual_original_retained_crooked_root28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hcounter : B N<F.card) :
    ∃ c∈Ground N,∀ S∈Retained N 28 F,¬IsAP S → c∈S := by
  obtain ⟨c,hc,hroot⟩ := actual_original_sparse_root28 hNl hNu hlegal hcounter
  exact ⟨c,hc,fun S hS hbad => hroot S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩

theorem actual_original_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hNl : 2^49≤N) (hNu : N<2^79) (hlegal : Legal (Ground N) F)
    (hcounter : B N<F.card) :
    ∃ c∈Ground N,(∀ S∈Retained N 28 F,¬IsAP S → c∈S) ∧
      Legal (Ground N) (Retained N 28 F) ∧ F.card≤(Retained N 28 F).card+3137*N ∧
      (∀ S∈F,IsAP S → S∈Retained N 28 F) := by
  obtain ⟨c,hc,hroot⟩ := actual_original_retained_crooked_root28 hNl hNu hlegal hcounter
  have hNr : (4*28^2+1)*(2*28-1)≤N := (by norm_num : (4*28^2+1)*(2*28-1)≤(2:ℕ)^49).trans hNl
  refine ⟨c,hc,hroot,actual_retained_legal hlegal,?_,fun _ hS hAP=>actual_ap_retained hS hAP⟩
  simpa only [show 4*28^2+1=3137 by norm_num] using
    actual_retained_sharp_lower (by decide : 0<28) hNr hlegal

#print axioms actual_sparse_membership
#print axioms actual_sparse_subset
#print axioms actual_sparse_legal
#print axioms actual_AP_part_legal
#print axioms actual_AP_part_retained
#print axioms actual_retained_partition
#print axioms actual_original_three_part_partition
#print axioms actual_sparse_density_from_deleted_bound
#print axioms actual_counterexample_density
#print axioms actual_sparse_density_old
#print axioms actual_sparse_density_sharp
#print axioms actual_sparse_density_original_budget
#print axioms actual_original_sparse_root28
#print axioms actual_original_retained_crooked_root28
#print axioms actual_original_reduction28

end
end JSP233.Density41
