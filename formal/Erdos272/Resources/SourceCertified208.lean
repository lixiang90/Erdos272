import Erdos272.Arithmetic.SourcePrefixExact208
import Erdos272.Resources.SourceBridge208
import Erdos272.Resources.SelectedLayer208
import Erdos272.Arithmetic.BatchSourceBlocks208

/-! The fourteen exact unit-source rows apply to actual finite sets.
The finite prefix and analytic tail cover every physical source below 2^50;
the same actual intrinsic-triple pool then pays all defect layers jointly. -/
namespace JSP233.SourceCertified208
open StarCompletion IntrinsicTriples208 SourceBridge208 PureSource208
open SourcePrefixSpecs208 SourceTargetOrder208 SourceTargets208
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def floorAt (i : Fin 14) (e : ℕ) : ℕ :=
  (rowTargets i)[min e 184]'(by rw [rowTargets_length]; omega)

theorem targetAt_mem (i : Fin 14) : targetAt i ∈ Targets :=
  List.getElem_mem (by rw [targets_length]; exact i.isLt)

theorem floorAt_physical (i : Fin 14) {s e : ℕ}
    (hs : rowStart i ≤ s) (hhi : s < 2^50) :
    floorAt i e ≤ physicalK s (min e 184) := by
  by_cases hsmall : s ≤ 32753
  · exact SourcePrefixExact208.physical_floor i (min e 184) (by omega) s hs hsmall
  · apply checked_tail_floor (targetAt_mem i) _ (by unfold Cutoff; omega) hhi
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by rw [targetAt_length]; omega)

/-- This conclusion uses the actual longest AP of the actual set. -/
theorem actual_source (i : Fin 14) {S : Finset ℤ} {e : ℕ}
    (hs : rowStart i ≤ S.card) (hhi : S.card < 2^50)
    (he : min e 184 ≤ Defect S) : floorAt i e ≤ (Pool S).card := by
  have htwo : 2 ≤ S.card := (by have := SourcePrefixExact208.rowStart_ge i; omega)
  exact (floorAt_physical i hs hhi).trans (actual_source_of_defect htwo he)

def DefectCheck : Bool := Targets.all fun row => (List.range 184).all fun e =>
  decide ((row.2[e]?).getD 0 ≤ (row.2[e+1]?).getD 0)

private theorem defect_adjacent_check :
    Targets.all (fun row => BatchSourceBlocks208.rowLE
      (row.2.take 184) (row.2.drop 1)) = true := by decide +kernel

theorem defect_check : DefectCheck = true := by
  unfold DefectCheck
  apply List.all_eq_true.mpr
  intro row hrow
  apply List.all_eq_true.mpr
  intro e he
  have he0 : e < 184 := List.mem_range.mp he
  have hlen : row.2.length = 185 := target_row_length hrow
  have hel : e < row.2.length := by omega
  have hel1 : e + 1 < row.2.length := by omega
  have hc := (List.all_eq_true.mp defect_adjacent_check) row hrow
  have hh := BatchSourceBlocks208.rowLE_get hc e
    (by simp only [List.length_take, hlen]; omega)
    (by simp only [List.length_drop, hlen]; omega)
  apply decide_eq_true
  simpa only [List.getElem_take, List.getElem_drop, Nat.add_comm,
    List.getElem?_eq_getElem hel, List.getElem?_eq_getElem hel1,
    Option.getD_some] using hh

theorem floorAt_step (i : Fin 14) (e : ℕ) : floorAt i e ≤ floorAt i (e+1) := by
  by_cases he : e < 184
  · have hr := List.all_eq_true.mp defect_check (targetAt i) (targetAt_mem i)
    have hh := of_decide_eq_true (List.all_eq_true.mp hr e (List.mem_range.mpr he))
    have hlen := targetAt_length i
    simpa only [floorAt, rowTargets, min_eq_left (by omega : e ≤ 184),
      min_eq_left (by omega : e+1 ≤ 184),
      List.getElem?_eq_getElem (by omega : e < (targetAt i).2.length),
      List.getElem?_eq_getElem (by omega : e+1 < (targetAt i).2.length),
      Option.getD_some] using hh
  · have hm : min e 184 = 184 := min_eq_right (by omega)
    have hm' : min (e+1) 184 = 184 := min_eq_right (by omega)
    simp only [floorAt, hm, hm', le_refl]

theorem floorAt_monotone (i : Fin 14) : Monotone (floorAt i) :=
  monotone_nat_of_le_succ (floorAt_step i)

def potential (i : Fin 14) (e : ℕ) : ℝ := floorAt i e

theorem potential_monotone (i : Fin 14) : Monotone (potential i) := by
  intro e f hef
  change (floorAt i e : ℝ) ≤ (floorAt i f : ℝ)
  exact_mod_cast floorAt_monotone i hef

/-- The checked source value and suffix increments form an actual cover. -/
theorem actual_pointwise_cover (i : Fin 14) (cap : ℕ) {S : Finset ℤ}
    (hs : rowStart i ≤ S.card) (hhi : S.card < 2^50) :
    potential i cap ≤ ((Pool S).card : ℝ) + ∑ j ∈ Finset.range cap,
      (potential i (j+1) - potential i j) * (if Defect S < j+1 then 1 else 0) := by
  apply LayerPayment208.pointwise_cover_of_potential (potential i) cap (Defect S)
    ((Pool S).card : ℝ) (potential_monotone i)
  change (floorAt i (Defect S) : ℝ) ≤ ((Pool S).card : ℝ)
  exact_mod_cast actual_source i (e := Defect S) hs hhi (min_le_left _ _)

def near (F : Finset (Finset ℤ)) (j : ℕ) : Finset (Finset ℤ) :=
  F.filter fun S => Defect S < j+1

/-- Near-layer fees are charged against a single actual global triple pool.
Only the separate combinatorial near-family bounds remain as fee inputs. -/
theorem actual_family_payment (i : Fin 14) (cap : ℕ)
    {Ω : Finset ℤ} {F : Finset (Finset ℤ)} (fee : ℕ → ℝ)
    (hF : Legal Ω F)
    (hs : ∀ S ∈ F, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range cap, ((near F j).card : ℝ) ≤ fee j) :
    potential i cap * F.card ≤ (Ω.card.choose 3 : ℝ) +
      ∑ j ∈ Finset.range cap, (potential i (j+1) - potential i j) * fee j := by
  apply LayerPayment208.actual_layer_payment (Finset.range cap) (near F)
    (fun j => potential i (j+1) - potential i j) fee (potential i cap) hF
  · intro j _
    exact Finset.filter_subset _ F
  · intro j _
    exact LayerPayment208.increments_nonneg (potential i) (potential_monotone i) j
  · intro S hS
    simpa only [near, Finset.mem_filter, hS, true_and] using
      actual_pointwise_cover i cap (hs S hS).1 (hs S hS).2
  · exact hfee

theorem actual_family_payment_with_AP (i : Fin 14) (cap : ℕ)
    {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {P : Finset ℤ} (fee : ℕ → ℝ)
    (hF : Legal Ω F) (hP : P ∈ F) (hAP : IsAP P)
    (hs : ∀ S ∈ F, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range cap, ((near F j).card : ℝ) ≤ fee j) :
    potential i cap * F.card ≤ (Ω.card.choose 3 : ℝ) - (P.card.choose 3 : ℝ) +
      ∑ j ∈ Finset.range cap, (potential i (j+1) - potential i j) * fee j := by
  apply LayerPayment208.actual_layer_payment_with_AP (Finset.range cap) (near F)
    (fun j => potential i (j+1) - potential i j) fee (potential i cap) hF hP hAP
  · intro j _
    exact Finset.filter_subset _ F
  · intro j _
    exact LayerPayment208.increments_nonneg (potential i) (potential_monotone i) j
  · intro S hS
    simpa only [near, Finset.mem_filter, hS, true_and] using
      actual_pointwise_cover i cap (hs S hS).1 (hs S hS).2
  · exact hfee


def selectedNear (F : Finset (Finset ℤ)) (nodes : ℕ → ℕ) (j : ℕ) : Finset (Finset ℤ) :=
  F.filter fun S => Defect S < nodes (j+1)

theorem actual_selected_cover (i : Fin 14) (nodes : ℕ → ℕ)
    (hnodes : Monotone nodes) (hzero : nodes 0 = 0) (n : ℕ) {S : Finset ℤ}
    (hs : rowStart i ≤ S.card) (hhi : S.card < 2^50) :
    potential i (nodes n) ≤ ((Pool S).card : ℝ) + ∑ j ∈ Finset.range n,
      (potential i (nodes (j+1)) - potential i (nodes j)) *
        (if Defect S < nodes (j+1) then 1 else 0) := by
  apply SelectedLayer208.sampled_pointwise_cover (potential i) nodes (potential_monotone i) hnodes
    n (Defect S) ((Pool S).card : ℝ)
  · change (floorAt i (nodes 0) : ℝ) ≤ ((Pool S).card : ℝ)
    exact_mod_cast actual_source i (e := nodes 0) hs hhi (by rw [hzero]; omega)
  · intro j _ hj
    change (floorAt i (nodes j) : ℝ) ≤ ((Pool S).card : ℝ)
    exact_mod_cast actual_source i (e := nodes j) hs hhi ((min_le_left _ _).trans hj)

theorem actual_selected_payment (i : Fin 14) (nodes : ℕ → ℕ)
    (hnodes : Monotone nodes) (hzero : nodes 0 = 0) (n : ℕ)
    {Ω : Finset ℤ} {F : Finset (Finset ℤ)} (fee : ℕ → ℝ)
    (hF : Legal Ω F)
    (hs : ∀ S ∈ F, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range n, ((selectedNear F nodes j).card : ℝ) ≤ fee j) :
    potential i (nodes n) * F.card ≤ (Ω.card.choose 3 : ℝ) +
      ∑ j ∈ Finset.range n,
        (potential i (nodes (j+1)) - potential i (nodes j)) * fee j := by
  apply LayerPayment208.actual_layer_payment (Finset.range n) (selectedNear F nodes)
    (fun j => potential i (nodes (j+1)) - potential i (nodes j)) fee
    (potential i (nodes n)) hF
  · intro j _
    exact Finset.filter_subset _ F
  · intro j _
    exact sub_nonneg.mpr (potential_monotone i (hnodes (by omega)))
  · intro S hS
    simpa only [selectedNear, Finset.mem_filter, hS, true_and] using
      actual_selected_cover i nodes hnodes hzero n (hs S hS).1 (hs S hS).2
  · exact hfee

theorem actual_selected_payment_with_AP (i : Fin 14) (nodes : ℕ → ℕ)
    (hnodes : Monotone nodes) (hzero : nodes 0 = 0) (n : ℕ)
    {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {P : Finset ℤ} (fee : ℕ → ℝ)
    (hF : Legal Ω F) (hP : P ∈ F) (hAP : IsAP P)
    (hs : ∀ S ∈ F, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range n, ((selectedNear F nodes j).card : ℝ) ≤ fee j) :
    potential i (nodes n) * F.card ≤ (Ω.card.choose 3 : ℝ) - (P.card.choose 3 : ℝ) +
      ∑ j ∈ Finset.range n,
        (potential i (nodes (j+1)) - potential i (nodes j)) * fee j := by
  apply LayerPayment208.actual_layer_payment_with_AP (Finset.range n) (selectedNear F nodes)
    (fun j => potential i (nodes (j+1)) - potential i (nodes j)) fee
    (potential i (nodes n)) hF hP hAP
  · intro j _
    exact Finset.filter_subset _ F
  · intro j _
    exact sub_nonneg.mpr (potential_monotone i (hnodes (by omega)))
  · intro S hS
    simpa only [selectedNear, Finset.mem_filter, hS, true_and] using
      actual_selected_cover i nodes hnodes hzero n (hs S hS).1 (hs S hS).2
  · exact hfee

#print axioms floorAt_physical
#print axioms actual_source
#print axioms defect_check
#print axioms actual_pointwise_cover
#print axioms actual_family_payment
#print axioms actual_family_payment_with_AP
#print axioms actual_selected_payment
#print axioms actual_selected_payment_with_AP
end
end JSP233.SourceCertified208
