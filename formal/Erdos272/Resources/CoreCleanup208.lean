module

public import Erdos272.Resources.CommonCapacity208
public import Erdos272.Resources.HeavyWindows208

@[expose] public section

namespace JSP233.CoreCleanup208
open StarCompletion APGeometry NearAP36 FarSlot112 CommonCapacity208 APCount41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem piece_budget {ι : Type*} [DecidableEq ι] {F A : Finset (Finset ℤ)}
    (label : Finset ℤ → ι) (I : Finset ι) (piece : Finset ℤ → Finset ℤ) (U : Finset ℤ)
    (hAF : A ⊆ F) (hmap : ∀ S ∈ F, label S ∈ I)
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → label S=label T → Disjoint (piece S) (piece T))
    (hhit : ∀ S ∈ A, (piece S ∩ U).Nonempty) : A.card ≤ I.card*U.card := by
  have hpart : A.card=∑ i∈I, (A.filter (fun S => label S=i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun S hS => hmap S (hAF hS))
  have hb : ∀ i ∈ I, (A.filter (fun S => label S=i)).card ≤ U.card := by
    intro i hi
    apply disjoint_pieces_hit_card _ piece U
    · intro S hS T hT hST
      exact hdis S (hAF (Finset.mem_filter.mp hS).1) T (hAF (Finset.mem_filter.mp hT).1) hST
        ((Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hT).2.symm)
    · intro S hS
      exact hhit S (Finset.mem_filter.mp hS).1
  rw [hpart]
  have hs := Finset.sum_le_sum hb
  simpa using hs

theorem same_step_intersection_high {P Q : Finset ℤ} {d a b : ℤ}
    (hP : APAt d a P) (hQ : APAt d b Q) (hPn : P.Nonempty) (hQn : Q.Nonempty)
    (hh : High P ≤ High Q) (hint : (P ∩ Q).Nonempty) : High P ∈ Q := by
  obtain ⟨u,hu⟩ := hint
  obtain ⟨huP,huQ⟩ := Finset.mem_inter.mp hu
  have hpH := (high_spec hPn).1
  have hqH := (high_spec hQn).1
  have huH := (high_spec hPn).2 u huP
  apply apAt_fill hQ huQ hqH huH hh
  exact apAt_dvd_sub hP huP hpH

def Trim (F : Finset (Finset ℤ)) (core : Finset ℤ → Finset ℤ) (U : Finset ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => Disjoint (S \ core S) U)

theorem actual_two_cleanup {ι : Type*} [DecidableEq ι] {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) (core : Finset ℤ → Finset ℤ) (d : ℤ)
    (hAP : ∀ S ∈ F, ∃ a : ℤ, APAt d a (core S)) (hne : ∀ S ∈ F, (core S).Nonempty)
    (hcore : ∀ S ∈ F, core S ⊆ S) (U : Finset ℤ) (hU : ∀ S ∈ F, core S ⊆ U)
    (label : Finset ℤ → ι) (I : Finset ι) (hmap : ∀ S ∈ F, label S ∈ I)
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → label S=label T →
      Disjoint (S \ core S) (T \ core T))
    (E : ℕ) (hE : ∀ S ∈ F, (S \ core S).card ≤ E) :
    ∃ t : ℤ, ∃ G : Finset (Finset ℤ), G ⊆ F ∧
      (∀ S ∈ G, t ∈ core S) ∧ (∀ S ∈ G, Disjoint (S \ core S) U) ∧
      F.card ≤ G.card+I.card*(U.card+E) := by
  let R := Trim F core U
  have hRF : R ⊆ F := Finset.filter_subset _ _
  have hfirst : (F \ R).card ≤ I.card*U.card := by
    apply piece_budget label I (fun S => S \ core S) U Finset.sdiff_subset hmap hdis
    intro S hS
    obtain ⟨hSF,hSR⟩ := Finset.mem_sdiff.mp hS
    have hnd : ¬Disjoint (S \ core S) U := by
      intro hd
      exact hSR (Finset.mem_filter.mpr ⟨hSF,hd⟩)
    exact Finset.not_disjoint_iff_nonempty_inter.mp hnd
  have hpart1 := Finset.card_sdiff_add_card_eq_card hRF
  rcases R.eq_empty_or_nonempty with he | hr
  · refine ⟨0,∅,Finset.empty_subset _,by simp,by simp,?_⟩
    have hz : R.card=0 := by rw [he]; rfl
    have hm := Nat.mul_le_mul_left I.card (Nat.le_add_right U.card E)
    simp only [Finset.card_empty,zero_add]
    omega
  · obtain ⟨P,hPR,hmin⟩ := Finset.exists_min_image R (fun S => High (core S)) hr
    let t := High (core P)
    let G := R.filter (fun S => t ∈ core S)
    have hGR : G ⊆ R := Finset.filter_subset _ _
    have htP : t ∈ core P := (high_spec (hne P (hRF hPR))).1
    have hsecond : (R \ G).card ≤ I.card*E := by
      have hb : (R \ G).card ≤ I.card*(P \ core P).card := by
        apply piece_budget label I (fun S => S \ core S) (P \ core P)
          (Finset.sdiff_subset.trans hRF) hmap hdis
        intro S hS
        obtain ⟨hSR,hSG⟩ := Finset.mem_sdiff.mp hS
        have hSF := hRF hSR
        have htS : t ∉ core S := by intro ht; exact hSG (Finset.mem_filter.mpr ⟨hSR,ht⟩)
        have hSP : S ≠ P := by intro heq; subst S; exact htS htP
        obtain ⟨a,hPAt⟩ := hAP P (hRF hPR)
        obtain ⟨b,hSAt⟩ := hAP S hSF
        have hcoreDis : Disjoint (core P) (core S) := by
          apply Finset.disjoint_left.mpr
          intro x hxP hxS
          exact htS (same_step_intersection_high hPAt hSAt (hne P (hRF hPR)) (hne S hSF)
            (hmin S hSR) ⟨x,Finset.mem_inter.mpr ⟨hxP,hxS⟩⟩)
        obtain ⟨x,hx⟩ := isAP_nonempty (hF.2 S hSF P (hRF hPR) hSP)
        obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
        have hSPU := (Finset.mem_filter.mp hSR).2
        have hPPU := (Finset.mem_filter.mp hPR).2
        have hxSC : x ∉ core S := by
          intro hxC
          by_cases hxPC : x ∈ core P
          · exact Finset.disjoint_left.mp hcoreDis hxPC hxC
          · exact Finset.disjoint_left.mp hPPU (Finset.mem_sdiff.mpr ⟨hxP,hxPC⟩) (hU S hSF hxC)
        have hxPC : x ∉ core P := by
          intro hxC
          exact Finset.disjoint_left.mp hSPU (Finset.mem_sdiff.mpr ⟨hxS,hxSC⟩) (hU P (hRF hPR) hxC)
        exact ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS,hxSC⟩,
          Finset.mem_sdiff.mpr ⟨hxP,hxPC⟩⟩⟩
      exact hb.trans (Nat.mul_le_mul_left I.card (hE P (hRF hPR)))
    have hpart2 := Finset.card_sdiff_add_card_eq_card hGR
    refine ⟨t,G,hGR.trans hRF,?_,?_,?_⟩
    · intro S hS; exact (Finset.mem_filter.mp hS).2
    · intro S hS; exact (Finset.mem_filter.mp (hGR hS)).2
    · have heq : I.card*(U.card+E)=I.card*U.card+I.card*E := Nat.mul_add _ _ _
      omega

#print axioms piece_budget
#print axioms same_step_intersection_high
#print axioms actual_two_cleanup
end
end JSP233.CoreCleanup208
