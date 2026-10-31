import Erdos272.Resources.ResidualGlobal208

namespace JSP233.PartitionCleanup208
open StarCompletion APGeometry NearAP36 CoreCleanup208 ResidualStratum208
open ResidualGlobal208 ResidualAggregate208 ResidualTwoCensus208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_step_cleanup {ι : Type*} [DecidableEq ι]
    {N D e : ℕ} {F : Finset (Finset ℤ)} (hF : Legal (Ground N) F)
    (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ)
    (hstep : ∀ S ∈ F, step S ∈ Finset.Icc 1 D)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ a : ℤ, APAt (step S : ℤ) a (core S))
    (hne : ∀ S ∈ F, (core S).Nonempty)
    (U : ℕ → Finset ℤ) (hU : ∀ S ∈ F, core S ⊆ U (step S))
    (label : Finset ℤ → ι) (I : ℕ → Finset ι)
    (hlabel : ∀ S ∈ F, label S ∈ I (step S))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → step S=step T → label S=label T →
      Disjoint (S \ core S) (T \ core T))
    (hsmall : ∀ S ∈ F, (S \ core S).card < e) :
    ∃ G : Finset (Finset ℤ), ∃ point : ℕ → ℤ, G ⊆ F ∧
      (∀ S ∈ G, point (step S) ∈ core S) ∧
      F.card ≤ G.card+∑ d ∈ Finset.Icc 1 D, (I d).card*((U d).card+(e-1)) := by
  have hex : ∀ d : ℕ, ∃ t : ℤ, ∃ A : Finset (Finset ℤ),
      A ⊆ F.filter (fun S => step S=d) ∧
      (∀ S ∈ A, t ∈ core S) ∧ (∀ S ∈ A, Disjoint (S \ core S) (U d)) ∧
      (F.filter (fun S => step S=d)).card ≤ A.card+(I d).card*((U d).card+(e-1)) := by
    intro d
    let A := F.filter (fun S => step S=d)
    have hAF : A ⊆ F := Finset.filter_subset _ _
    have hA : Legal (Ground N) A := ⟨fun S hS => hF.1 S (hAF hS),
      fun S hS T hT hST => hF.2 S (hAF hS) T (hAF hT) hST⟩
    have hAP : ∀ S ∈ A, ∃ a : ℤ, APAt (d : ℤ) a (core S) := by
      intro S hS
      simpa only [(Finset.mem_filter.mp hS).2] using hAt S (hAF hS)
    have hU' : ∀ S ∈ A, core S ⊆ U d := by
      intro S hS
      simpa only [(Finset.mem_filter.mp hS).2] using hU S (hAF hS)
    have hlabel' : ∀ S ∈ A, label S ∈ I d := by
      intro S hS
      simpa only [(Finset.mem_filter.mp hS).2] using hlabel S (hAF hS)
    exact actual_two_cleanup hA core d hAP (fun S hS => hne S (hAF hS))
      (fun S hS => (hcore S (hAF hS)).1) (U d) hU' label (I d) hlabel'
      (fun S hS T hT hST heq => hdis S (hAF hS) T (hAF hT) hST
        ((Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hT).2.symm) heq)
      (e-1) (fun S hS => by have hh := hsmall S (hAF hS); omega)
  choose point J hJsub hJpoint hJavoid hJcard using hex
  let G := (Finset.Icc 1 D).biUnion J
  have hGF : G ⊆ F := by
    intro S hS
    obtain ⟨d,hd,hSJ⟩ := Finset.mem_biUnion.mp hS
    exact (Finset.mem_filter.mp (hJsub d hSJ)).1
  have hGd : ∀ d ∈ Finset.Icc 1 D, G.filter (fun S => step S=d)=J d := by
    intro d hd
    ext S
    constructor
    · intro hS
      obtain ⟨hSG,hstepS⟩ := Finset.mem_filter.mp hS
      obtain ⟨k,hk,hSJ⟩ := Finset.mem_biUnion.mp hSG
      have hstepK := (Finset.mem_filter.mp (hJsub k hSJ)).2
      have heq : k=d := hstepK.symm.trans hstepS
      simpa only [heq] using hSJ
    · intro hSJ
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨d,hd,hSJ⟩,
        (Finset.mem_filter.mp (hJsub d hSJ)).2⟩
  have hFpart : F.card=∑ d ∈ Finset.Icc 1 D, (F.filter (fun S => step S=d)).card :=
    Finset.card_eq_sum_card_fiberwise hstep
  have hGpart : G.card=∑ d ∈ Finset.Icc 1 D, (J d).card := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 D, (G.filter (fun S => step S=d)).card :=
        Finset.card_eq_sum_card_fiberwise (fun S hS => hstep S (hGF hS))
      _ = _ := Finset.sum_congr rfl (fun d hd => congrArg Finset.card (hGd d hd))
  have hs := Finset.sum_le_sum (fun d (hd : d ∈ Finset.Icc 1 D) => hJcard d)
  rw [Finset.sum_add_distrib,←hFpart,←hGpart] at hs
  refine ⟨G,point,hGF,?_,hs⟩
  intro S hS
  obtain ⟨d,hd,hSJ⟩ := Finset.mem_biUnion.mp hS
  have heq := (Finset.mem_filter.mp (hJsub d hSJ)).2
  simpa only [heq] using hJpoint d S hSJ

#print axioms actual_step_cleanup
end
end JSP233.PartitionCleanup208
