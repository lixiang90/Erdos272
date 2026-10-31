import Erdos272.Arithmetic.IntegerUniformQueries209
import Erdos272.Resources.ActualUnitSystem208

namespace JSP233.IntegerUniformSystem209
open StarCompletion APGeometry NearAP36 SourceBridge208 SourcePrefixSpecs208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 SevenFamily208
open UniformQuery208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Fixed physical integer bands, with certified actual uniform-source rows.
All family counts and coordinates are subsequently constructed from A. -/
structure Recipe (N M e k : ℕ) (psi : ℕ→ℝ) where
  data : Band→CleanupEval208.Band
  query : Band→Query
  query_mem : ∀b,query b∈IntegerUniformQueries209.queries
  query_M : ∀b,(query b).M=M
  query_T : ∀b,(query b).T=(data b).T
  query_E : ∀b,(query b).z=(data b).E
  height : ∀b,psi (k+1)≤((query b).q : ℝ)
  M_le : ∀b,M≤(data b).T
  E_le : ∀b,(data b).E≤e
  TU : ∀b,(data b).T<(data b).U
  cover : ∀n : ℕ,M≤n→11*n≤N→∃b,(data b).T≤n ∧ n<(data b).U
  physical : ∀d∈Finset.Icc 1 (N/(M-e)),∀b : Band,
    let B:=CleanupEval208.block (data b) d
    2≤B ∧ B≤(data b).T-(data b).E ∧
      ((StepClass208.PrimeGate d-1)*((data b).T-(data b).E+1-B)≥(data b).E ∨
        StepClass208.PrimeGate d*B≤(StepClass208.PrimeGate d-1)*((data b).T-(data b).E+1))

theorem actual_cut {N M e k : ℕ} {psi : ℕ→ℝ} {A : Finset (Finset ℤ)}
    (p : Recipe N M e k psi) (hN : 2≤N) (b : Band) {S : Finset ℤ}
    (hground : S⊆Ground N) (hT : (p.data b).T≤S.card)
    (hS : S∈JointNear N A 1 M psi k) : Defect S<(p.data b).E := by
  by_contra hn
  have hE : (p.data b).E≤Defect S := by omega
  have hh := IntegerUniformQueries209.actual_bound (p.query b) (p.query_mem b) hN hground
    (by simpa only [p.query_T b] using hT) (by simpa only [p.query_E b] using hE)
  rw [p.query_M b] at hh
  have hnear := (Finset.mem_filter.mp hS).2
  change UniformCapacity208.JointMass N 1 M S<1^2*psi (k+1) at hnear
  norm_num only [one_pow,one_mul] at hnear
  linarith only [hh,hnear,p.height b]

theorem actual_system {N M e k : ℕ} {A : Finset (Finset ℤ)} {psi : ℕ→ℝ}
    (p : Recipe N M e k psi) (hM : 2≤M) (he : 2≤e) (heM : e<M) (hN : 2≤N)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,M≤S.card) (hsparse : ∀S∈A,11*S.card≤N) :
    ∃s : System,s.N=N ∧ s.D=N/(M-e) ∧ s.M=M ∧ s.e=e ∧ s.F=JointNear N A 1 M psi k ∧
      (∀d b,s.T d b=(p.data b).T ∧ s.E d b=(p.data b).E ∧
        s.U d b=(p.data b).U ∧ s.B d b=CleanupEval208.block (p.data b) d) ∧ Valid s := by
  let F:=JointNear N A 1 M psi k
  have hFA : F⊆A := Finset.filter_subset _ _
  have hc : ∀S : Finset ℤ,∃b : Band,S∈F→(p.data b).T≤S.card ∧ S.card<(p.data b).U := by
    intro S
    by_cases hSF : S∈F
    · obtain ⟨b,hb⟩ := p.cover S.card (hsize S (hFA hSF)) (hsparse S (hFA hSF))
      exact ⟨b,fun _=>hb⟩
    · exact ⟨0,fun h=>False.elim (hSF h)⟩
  choose band hband using hc
  have hsmall_band : ∀S∈F,Defect S<(p.data (band S)).E := by
    intro S hS
    exact actual_cut p hN (band S) (hlegal.1 S (hFA hS)) (hband S hS).1 hS
  have hsmall : ∀S∈F,Defect S<e := fun S hS=>(hsmall_band S hS).trans_le (p.E_le (band S))
  have hlow : ∀S∈F,M≤S.card := fun S hS=>hsize S (hFA hS)
  have hground : ∀S∈F,S⊆Ground N := fun S hS=>hlegal.1 S (hFA hS)
  have hcrooked : ∀S∈F,¬IsAP S := fun S hS=>hbad S (hFA hS)
  obtain ⟨start,step,hcore⟩ := CoreCoordinates208.actual_coordinate_selection (U := N+1) hM heM.le
    hground hcrooked hlow (fun S hS=>by
      have hh:=Finset.card_le_card (hground S hS);rw [ground_card] at hh;omega) hsmall
  let s : System := ⟨N,N/(M-e),M,e,F,step,band,start,
    fun _ b=>(p.data b).T,fun _ b=>(p.data b).E,
    fun d b=>CleanupEval208.block (p.data b) d,fun _ b=>(p.data b).U⟩
  refine ⟨s,rfl,rfl,rfl,rfl,rfl,fun _ _=>⟨rfl,rfl,rfl,rfl⟩,?_⟩
  have hstep : ∀S∈F,step S∈Finset.Icc 1 (N/(M-e)) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(hcore S hS).1,
      ActualUnitSystem208.actual_step_bound heM (hcore S hS).2.1 (hground S hS) (hlow S hS) (hsmall S hS)⟩
  have hL : Legal (Ground N) F :=
    ⟨hground,fun S hS T hT hST=>hlegal.2 S (hFA hS) T (hFA hT) hST⟩
  refine ⟨hL,hstep,(fun S hS=>(hcore S hS).2.1),hcrooked,he,heM,
    (fun _ _ b=>p.M_le b),(fun _ _ b=>p.E_le b),?_,
    (fun _ _ b=>p.TU b),?_,?_,?_,?_,?_,?_⟩
  · intro d hd b
    have hE:=p.E_le b
    have hT:=p.M_le b
    change (p.data b).E<(p.data b).T
    omega
  · intro d hd b;exact (p.physical d hd b).1
  · intro d hd b;exact (p.physical d hd b).2.1
  · intro d hd b;exact (p.physical d hd b).2.2
  · intro d hd b S hS
    have hmem:=Finset.mem_filter.mp hS
    have hh:=(hband S hmem.1).1
    have hb : band S=b := hmem.2.2
    change (p.data b).T≤S.card
    simpa only [hb] using hh
  · intro d hd b S hS
    have hmem:=Finset.mem_filter.mp hS
    have hh:=(hband S hmem.1).2
    have hb : band S=b := hmem.2.2
    change S.card<(p.data b).U
    simpa only [hb] using hh
  · intro d hd b S hS
    have hmem:=Finset.mem_filter.mp hS
    have hh:=hsmall_band S hmem.1
    have hb : band S=b := hmem.2.2
    change Defect S<(p.data b).E
    simpa only [hb] using hh

#print axioms actual_cut
#print axioms actual_system
end
end JSP233.IntegerUniformSystem209
