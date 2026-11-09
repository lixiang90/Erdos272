module

public import Erdos272.Retention.DenseAligned117

@[expose] public section
namespace JSP233.DensePhase137
open StarCompletion APGeometry Relative13Fringe116
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def StepClass (E:Finset (Finset ℤ)) (K:Finset ℤ→Key) (M:ℕ) (L:ℤ) (d:ℕ) :
    Finset (Finset ℤ) := E.filter (fun S=>Aligned K M L S ∧ (K S).1=d)

theorem origins_congruent {S T:Finset ℤ} {d o p:ℤ}
    (hinter:(S∩T).Nonempty) (hS:∀y∈S,d∣y-o) (hT:∀y∈T,d∣y-p) : d∣p-o := by
  obtain ⟨z,hz⟩:=hinter
  obtain ⟨hzS,hzT⟩:=Finset.mem_inter.mp hz
  rw [show p-o=(z-o)-(z-p) by ring]
  exact dvd_sub (hS z hzS) (hT z hzT)

theorem exists_common_origin {Ω:Finset ℤ} {F:Finset (Finset ℤ)} {d:ℤ}
    (hF:Legal Ω F) (origin:Finset ℤ→ℤ) (halign:∀S∈F,∀y∈S,d∣y-origin S) :
    ∃o:ℤ,∀S∈F,d∣origin S-o := by
  by_cases hne:F.Nonempty
  · obtain ⟨T,hT⟩:=hne
    refine ⟨origin T,?_⟩
    intro S hS
    by_cases he:S=T
    · subst S
      simp
    · exact origins_congruent (isAP_nonempty (hF.2 T hT S hS (Ne.symm he)))
        (halign T hT) (halign S hS)
  · exact ⟨0,fun S hS=>False.elim (hne ⟨S,hS⟩)⟩

theorem exists_common_residue {Ω:Finset ℤ} {F:Finset (Finset ℤ)} {d:ℤ}
    (hF:Legal Ω F) (origin:Finset ℤ→ℤ) (halign:∀S∈F,∀y∈S,d∣y-origin S) :
    ∃o:ℤ,∀S∈F,∀y∈S,d∣y-o := by
  obtain ⟨o,ho⟩:=exists_common_origin hF origin halign
  refine ⟨o,?_⟩
  intro S hS y hy
  rw [show y-o=(y-origin S)+(origin S-o) by ring]
  exact dvd_add (halign S hS y hy) (ho S hS)

theorem step_class_legal {N M d:ℕ} {E:Finset (Finset ℤ)} {K:Finset ℤ→Key} {L:ℤ}
    (hlegal:Legal (Ground N) E) : Legal (Ground N) (StepClass E K M L d) := by
  have hsub:StepClass E K M L d⊆E:=Finset.filter_subset _ _
  exact ⟨fun S hS=>hlegal.1 S (hsub hS),fun S hS T hT he=>hlegal.2 S (hsub hS) T (hsub hT) he⟩

theorem actual_step_class_common_residue {N M d:ℕ} {E:Finset (Finset ℤ)}
    {K:Finset ℤ→Key} {L:ℤ} (hlegal:Legal (Ground N) E) :
    ∃o:ℤ,∀S∈StepClass E K M L d,∀y∈S,(d:ℤ)∣y-o := by
  apply exists_common_residue (step_class_legal hlegal) (fun S=>Origin M L (K S))
  intro S hS y hy
  obtain ⟨_hSE,hA,hd⟩:=Finset.mem_filter.mp hS
  simpa only [hd] using hA y hy

theorem actual_step_class_rank {N M d r:ℕ} {E:Finset (Finset ℤ)}
    {K:Finset ℤ→Key} {L:ℤ} (hlegal:Legal (Ground N) E)
    (hbad:∀S∈E,¬IsAP S) (hdense:∀S∈E,N<r*S.card)
    (hkeys:∀S∈E,K S∈Keys) (hne:(StepClass E K M L d).Nonempty) : 0<d ∧ d<r := by
  obtain ⟨S,hS⟩:=hne
  obtain ⟨hSE,hA,he⟩:=Finset.mem_filter.mp hS
  have hdpos:0<(K S).1:=by
    have hh:1≤(K S).1:=(Finset.mem_Icc.mp (Finset.mem_sigma.mp (hkeys S hSE)).1).1
    omega
  have hlt:=DenseAligned117.actual_dense_crooked_modulus_lt hdpos
    (hlegal.1 S hSE) (hbad S hSE) (hdense S hSE) hA
  exact ⟨by omega,by omega⟩

#print axioms origins_congruent
#print axioms exists_common_origin
#print axioms exists_common_residue
#print axioms step_class_legal
#print axioms actual_step_class_common_residue
#print axioms actual_step_class_rank
end
end JSP233.DensePhase137
