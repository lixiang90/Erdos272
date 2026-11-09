module

public import Erdos272.Counting.Density41
public import Erdos272.Counting.EndpointDensity54
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
An actual original-family AP and sparse-crooked density bound.  The AP fiber
count is re-summed with the already kernel-proved 329/200 reciprocal-square
bound.  All actual AP members remain in Retained; no AP count, deleted fee,
or sparse density is supplied to the final original-family endpoints.
-/
namespace JSP233.APDensity112
open StarCompletion APGeometry APCount41 HarmonicAbel29
open DenseDeletion40 DenseSharper41 Density41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem square_reciprocal_refined (N : ℕ) : SquareReciprocal N≤329/200 := by
  simpa only [SquareReciprocal,CoprimeDensity52.reciprocalSquareSum,one_div] using
    EndpointDensity54.reciprocal_square_upper N

theorem actual_AP_two_or_more_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hAP : ∀S∈F,IsAP S) (htwo : ∀S∈F,2≤S.card) :
    (F.card:ℝ)≤(329/800:ℝ)*(N:ℝ)^2+(N:ℝ)*Harmonic N+N := by
  have hmaps : ∀S∈F,Step S∈Finset.Icc 1 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(actual_step (hAP S hS)).1,
      actual_step_bound (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀d∈Finset.Icc 1 N,
      ((F.filter (fun S => Step S=d)).card:ℝ)≤
        (N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1 := by
    intro d hd
    let C := F.filter (fun S => Step S=d)
    have hCF : C⊆F := Finset.filter_subset _ _
    have hLC : Legal (Ground N) C :=
      ⟨fun S hS => hlegal.1 S (hCF hS),fun S hS T hT hne =>
        hlegal.2 S (hCF hS) T (hCF hT) hne⟩
    apply actual_same_step_count (Finset.mem_Icc.mp hd).1 hLC
      (fun S hS => isAP_nonempty (hAP S (hCF hS)))
    intro S hS
    obtain ⟨_,p,hp⟩ := actual_step (hAP S (hCF hS))
    exact ⟨p,by rwa [(Finset.mem_filter.mp hS).2] at hp⟩
  have hsum : (∑d∈Finset.Icc 1 N,
      ((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1))=
      (N:ℝ)^2/4*SquareReciprocal N+(N:ℝ)*Harmonic N+N := by
    have ht : ∀d:ℕ,(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1=
        (N:ℝ)^2/4*(1/(d:ℝ)^2)+(N:ℝ)*(1/(d:ℝ))+1 := by
      intro d
      ring
    simp_rw [ht]
    simp [SquareReciprocal,Harmonic,Finset.sum_add_distrib,←Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left (square_reciprocal_refined N)
    (show (0:ℝ)≤(N:ℝ)^2/4 by positivity)
  calc
    (F.card:ℝ)=(∑d∈Finset.Icc 1 N,
      ((F.filter (fun S => Step S=d)).card:ℝ)) := by exact_mod_cast he
    _≤∑d∈Finset.Icc 1 N,((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1) :=
      Finset.sum_le_sum hclass
    _≤_ := by rw [hsum];nlinarith only [hs]

theorem actual_AP_count_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hAP : ∀S∈F,IsAP S) :
    (F.card:ℝ)≤(329/800:ℝ)*(N:ℝ)^2+(N:ℝ)*Harmonic N+N+1 := by
  let A := F.filter (fun S => 2≤S.card)
  let C := F.filter (fun S => ¬2≤S.card)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hCF : C⊆F := Finset.filter_subset _ _
  have hLA : Legal (Ground N) A :=
    ⟨fun S hS => hlegal.1 S (hAF hS),fun S hS T hT hne =>
      hlegal.2 S (hAF hS) T (hAF hT) hne⟩
  have hLC : Legal (Ground N) C :=
    ⟨fun S hS => hlegal.1 S (hCF hS),fun S hS T hT hne =>
      hlegal.2 S (hCF hS) T (hCF hT) hne⟩
  have ha := actual_AP_two_or_more_count hLA (fun S hS=>hAP S (hAF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hc := actual_singleton_family_count hLC (fun S hS=>by
    have hh := (Finset.mem_filter.mp hS).2
    omega)
  have hpart := Finset.card_filter_add_card_filter_not (s:=F) (fun S => 2≤S.card)
  change A.card+C.card=F.card at hpart
  have hpartR : (A.card:ℝ)+C.card=F.card := by exact_mod_cast hpart
  have hcR : (C.card:ℝ)≤1 := by exact_mod_cast hc
  linarith only [ha,hpartR,hcR]

theorem actual_harmonic_le_J {N J : ℕ} (hJ : 4≤J) (hN : N<2^J) :
    Harmonic N≤(J:ℝ) := by
  have hh := HarmonicSharp39.actual_harmonic_seven_tenths N J hN
  have hj : (4:ℝ)≤J := by exact_mod_cast hJ
  linarith only [hh,hj]

theorem actual_AP_count_dyadic {N J : ℕ} {F : Finset (Finset ℤ)}
    (hJ : 4≤J) (hN : N<2^J) (hlegal : Legal (Ground N) F)
    (hAP : ∀S∈F,IsAP S) :
    (F.card:ℝ)≤(329/800:ℝ)*(N:ℝ)^2+(J:ℝ)*N+N+1 := by
  have ha := actual_AP_count_harmonic hlegal hAP
  have hh := mul_le_mul_of_nonneg_left (actual_harmonic_le_J hJ hN)
    (Nat.cast_nonneg N : (0:ℝ)≤N)
  nlinarith only [ha,hh]

theorem actual_AP_part_count {N J : ℕ} {F : Finset (Finset ℤ)}
    (hJ : 4≤J) (hN : N<2^J) (hlegal : Legal (Ground N) F) :
    ((APPart F).card:ℝ)≤(329/800:ℝ)*(N:ℝ)^2+(J:ℝ)*N+N+1 := by
  exact actual_AP_count_dyadic hJ hN (actual_AP_part_legal hlegal)
    (fun S hS => (Finset.mem_filter.mp hS).2)

theorem actual_original_card_lower {N : ℕ} {F : Finset (Finset ℤ)}
    (hcard : B N≤F.card) : (N:ℝ)^2/2-(N:ℝ)+1≤F.card := by
  have hchoose : N.choose 2+1≤F.card := by unfold B at hcard;omega
  have hr : (N.choose 2:ℝ)+1≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hr
  have hN0 : (0:ℝ)≤N := by positivity
  nlinarith only [hr,hN0]

theorem actual_original_crooked_density {N J : ℕ} {F : Finset (Finset ℤ)}
    (hJ : 4≤J) (hN : N<2^J) (hlegal : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    (71/800:ℝ)*(N:ℝ)^2-((J:ℝ)+2)*N≤(F.filter (fun S => ¬IsAP S)).card := by
  have hAP := actual_AP_part_count hJ hN hlegal
  have hf := actual_original_card_lower hcard
  have hpart := Finset.card_filter_add_card_filter_not (s:=F) IsAP
  have hpartR : ((APPart F).card:ℝ)+(F.filter (fun S => ¬IsAP S)).card=F.card := by
    exact_mod_cast hpart
  nlinarith only [hAP,hf,hpartR]

theorem actual_sparse_density {N r J : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hNr : (4*r^2+1)*(2*r-1)≤N)
    (hJ : 4≤J) (hN : N<2^J) (hlegal : Legal (Ground N) F)
    (hcard : B N≤F.card) :
    (71/800:ℝ)*(N:ℝ)^2-(4*(r:ℝ)^2+3+J)*N≤(SparseCrooked N r F).card := by
  have hAP := actual_AP_part_count hJ hN hlegal
  have hf := actual_original_card_lower hcard
  have hd := actual_deleted_sharp hr hNr hlegal
  have hdR : ((Deleted N r F).card:ℝ)≤(4*(r:ℝ)^2+1)*N := by
    exact_mod_cast hd
  have hpart := actual_original_three_part_partition N r F
  have hpartR : ((APPart F).card:ℝ)+(SparseCrooked N r F).card+
      (Deleted N r F).card=F.card := by exact_mod_cast hpart
  nlinarith only [hAP,hf,hdR,hpartR]

theorem actual_sparse_density11 {N J : ℕ} {F : Finset (Finset ℤ)}
    (hNr : 10185≤N) (hJ : 4≤J) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcard : B N≤F.card) :
    (71/800:ℝ)*(N:ℝ)^2-((487:ℝ)+J)*N≤(SparseCrooked N 11 F).card := by
  have hh := actual_sparse_density (r:=11) (by decide : 0<11)
    (by norm_num;exact hNr) hJ hN hlegal hcard
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith only [hh]

theorem actual_sparse_density11_normalized {N J : ℕ} {F : Finset (Finset ℤ)}
    (hNr : 10185≤N) (hJ : 4≤J) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcard : B N≤F.card) :
    (71/800:ℝ)-((487:ℝ)+J)/N≤((SparseCrooked N 11 F).card:ℝ)/(N:ℝ)^2 := by
  have hh := actual_sparse_density11 hNr hJ hN hlegal hcard
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  have he : ((71/800:ℝ)-((487:ℝ)+J)/N)*(N:ℝ)^2=
      (71/800:ℝ)*(N:ℝ)^2-((487:ℝ)+J)*N := by field_simp [hp.ne']
  rwa [he]

/-- The same original family, all AP members, actual deleted crofts, and all
sparse crofts are retained in this package. -/
theorem actual_original_package11 {N J : ℕ} {F : Finset (Finset ℤ)}
    (hNr : 10185≤N) (hJ : 4≤J) (hN : N<2^J)
    (hlegal : Legal (Ground N) F) (hcard : B N≤F.card) :
    (Deleted N 11 F).card≤485*N ∧
    (∀S∈F,IsAP S→S∈Retained N 11 F) ∧
    Legal (Ground N) (Retained N 11 F) ∧
    SparseCrooked N 11 F⊆F ∧ Legal (Ground N) (SparseCrooked N 11 F) ∧
    (∀S∈SparseCrooked N 11 F,¬IsAP S ∧ 11*S.card≤N) ∧
    (APPart F).card+(SparseCrooked N 11 F).card+(Deleted N 11 F).card=F.card ∧
    (71/800:ℝ)*(N:ℝ)^2-((487:ℝ)+J)*N≤(SparseCrooked N 11 F).card := by
  have hd := actual_deleted_sharp (r:=11) (by decide : 0<11)
    (by norm_num;exact hNr) hlegal
  norm_num only [show 4*11^2+1=485 by norm_num] at hd
  exact ⟨hd,fun _ hS hAP => actual_ap_retained hS hAP,actual_retained_legal hlegal,
    actual_sparse_subset _ _ _,actual_sparse_legal hlegal,
    fun _ hS => (actual_sparse_membership.mp hS).2,
    actual_original_three_part_partition _ _ _,actual_sparse_density11 hNr hJ hN hlegal hcard⟩

#print axioms square_reciprocal_refined
#print axioms actual_AP_two_or_more_count
#print axioms actual_AP_count_harmonic
#print axioms actual_harmonic_le_J
#print axioms actual_AP_count_dyadic
#print axioms actual_AP_part_count
#print axioms actual_original_card_lower
#print axioms actual_original_crooked_density
#print axioms actual_sparse_density
#print axioms actual_sparse_density11
#print axioms actual_sparse_density11_normalized
#print axioms actual_original_package11
end
end JSP233.APDensity112
