module

public import Erdos272.Foundation.TwoTraceGlobal
public import Erdos272.Foundation.PrimeKernel
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

/-! Uniform prime-step capacity. The actual AP geometry forces the pair
steps; the only selection lemmas reused are the finite private-point and
joint-injection lemmas. No numerical payment hypothesis is supplied. -/

namespace JSP233.PrimeCapacity

open StarCompletion PrivateFinset

/-- A reusable two-class selection lemma, independent of primality. -/
theorem two_step_tail_bound
    (Ω I : Finset Int) (D : Finset (Finset Int)) (a d : Int)
    (haI : a ∈ I) (hI : PrivateUnion.APAt 1 a (fun x => x ∈ I))
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (haD : ∀ S ∈ D, a ∈ S)
    (hfine : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → I ⊆ S → I ⊆ T →
      PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T))
    (hcore : ∀ S ∈ D, ¬ I ⊆ S →
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ I))
    (hcoarse : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → ¬ I ⊆ S →
      PrivateUnion.APAt d a (fun x => x ∈ S ∧ x ∈ T)) :
    D.card ≤ (Ω \ I).card := by
  classical
  apply TwoTraceGlobal.joint_private_card_bound Ω I D (fun S => I ⊆ S) hground
  intro S hS
  by_cases hSI : I ⊆ S
  · let Fine := D.filter (fun T => I ⊆ T)
    have haF : ∀ T ∈ Fine, a ∈ T := by
      intro T hT
      exact (Finset.mem_filter.mp hT).2 haI
    have hcoreS : PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ I) := by
      apply PrivateUnion.APAt_congr 1 a _ _ hI
      intro x
      exact ⟨fun hx => ⟨hSI hx,hx⟩,fun hx => hx.2⟩
    have hp : ∀ T ∈ Fine, S ≠ T →
        PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
      intro T hT hne
      exact hfine S hS T (Finset.mem_filter.mp hT).1 hne hSI
        (Finset.mem_filter.mp hT).2
    rcases TwoTraceGlobal.private_exterior_finset Fine S I 1 a (haD S hS)
      haI haF (hcrooked S hS) hcoreS hp with ⟨x,hx,hxI,hpriv⟩
    refine ⟨x,hx,hxI,?_⟩
    intro T hT hne hclass
    exact hpriv T (Finset.mem_filter.mpr
      ⟨hT,hclass.resolve_left (not_not.mpr hSI)⟩) hne
  · rcases TwoTraceGlobal.private_exterior_finset D S I d a (haD S hS)
      haI haD (hcrooked S hS) (hcore S hS hSI)
      (fun T hT hne => hcoarse S hS T hT hne hSI) with ⟨x,hx,hxI,hpriv⟩
    exact ⟨x,hx,hxI,fun T hT hne _ => hpriv T hT hne⟩

theorem positive_divisor_prime (p : Nat) (hp : p.Prime)
    (q : Int) (hq : 0 < q) (hdiv : q ∣ (p : Int)) :
    q = 1 ∨ q = (p : Int) := by
  have hnat := hp.eq_one_or_self_of_dvd q.natAbs (Int.dvd_natCast.mp hdiv)
  have habs : (q.natAbs : Int) = q := Int.ofNat_natAbs_of_nonneg (by omega)
  rcases hnat with h | h
  · have hc := congrArg (fun n : Nat => (n : Int)) h
    exact Or.inl (by omega)
  · have hc := congrArg (fun n : Nat => (n : Int)) h
    exact Or.inr (by omega)

/-- Common points at prime distance force the real step to be one or p. -/
theorem step_one_or_prime (p : Nat) (hp : p.Prime) (a : Int) (S : Finset Int)
    (hS : IsAP S) (ha : a ∈ S) (hnext : a+(p : Int) ∈ S) :
    PrivateUnion.APAt 1 a (fun x => x ∈ S) ∨
    PrivateUnion.APAt (p : Int) a (fun x => x ∈ S) := by
  rcases PrimeKernel.step_dvd_gap S a (a+(p : Int)) hS ha hnext with
    ⟨q,hq,hdiv,hstep⟩
  have hdiv' : q ∣ (p : Int) := by simpa using hdiv
  rcases positive_divisor_prime p hp q hq hdiv' with rfl | rfl
  · exact Or.inl hstep
  · exact Or.inr hstep

/-- A nonfine member rules out the unit step for any of its intersections. -/
theorem nonfine_pair_step_prime (p : Nat) (hp : p.Prime)
    (a b : Int) (S T : Finset Int)
    (ha : a ∈ S ∩ T) (hnext : a+(p : Int) ∈ S ∩ T) (hb : b ∈ S ∩ T)
    (hnf : ¬ Finset.Icc a b ⊆ S) (hpair : IsAP (S ∩ T)) :
    PrivateUnion.APAt (p : Int) a (fun x => x ∈ S ∧ x ∈ T) := by
  rcases step_one_or_prime p hp a (S ∩ T) hpair ha hnext with h1 | hp
  · exact False.elim (hnf (fun x hx => (Finset.mem_inter.mp
      (PrimeKernel.unit_step_contains_interval (S ∩ T) a a b h1 ha hb hx)).1))
  · simpa only [Finset.mem_inter] using hp

/-- With a fine member, the coarse trace is a genuine step-p AP. -/
theorem coarse_trace_step_prime (p : Nat) (hp : p.Prime)
    (D : Finset (Finset Int)) (a b : Int) (S : Finset Int)
    (hS : S ∈ D) (ha : ∀ T ∈ D, a ∈ T)
    (hnext : ∀ T ∈ D, a+(p : Int) ∈ T) (hb : ∀ T ∈ D, b ∈ T)
    (hf : ∃ T ∈ D, Finset.Icc a b ⊆ T)
    (hpair : ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hnf : ¬ Finset.Icc a b ⊆ S) :
    PrivateUnion.APAt (p : Int) a (fun x => x ∈ S ∧ x ∈ Finset.Icc a b) := by
  rcases hf with ⟨T,hT,hTf⟩
  have hne : S ≠ T := by
    intro he
    exact hnf (he.symm ▸ hTf)
  have hstep := nonfine_pair_step_prime p hp a b S T
    (Finset.mem_inter.mpr ⟨ha S hS,ha T hT⟩)
    (Finset.mem_inter.mpr ⟨hnext S hS,hnext T hT⟩)
    (Finset.mem_inter.mpr ⟨hb S hS,hb T hT⟩) hnf (hpair T hT hne)
  rcases hstep with ⟨hpos,lo,hi,hrep⟩
  have hal := ((hrep a).mp ⟨ha S hS,ha T hT⟩).1
  have hbh := ((hrep b).mp ⟨hb S hS,hb T hT⟩).2.1
  refine ⟨hpos,a,b,?_⟩
  intro x
  constructor
  · rintro ⟨hxS,hxI⟩
    have hx := Finset.mem_Icc.mp hxI
    exact ⟨hx.1,hx.2,((hrep x).mp ⟨hxS,hTf hxI⟩).2.2⟩
  · rintro ⟨hxa,hxb,hd⟩
    exact ⟨((hrep x).mpr ⟨by omega,by omega,hd⟩).1,
      Finset.mem_Icc.mpr ⟨hxa,hxb⟩⟩

/-- Joint prime-tail injection stated with actual shared endpoint witnesses. -/
theorem prime_joint_tail_bound (p : Nat) (hp : p.Prime)
    (Ω : Finset Int) (D : Finset (Finset Int)) (a b : Int)
    (hab : a ≤ b) (hnextb : a+(p : Int) ≤ b)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (ha : ∀ S ∈ D, a ∈ S) (hnext : ∀ S ∈ D, a+(p : Int) ∈ S)
    (hb : ∀ S ∈ D, b ∈ S) (hf : ∃ S ∈ D, Finset.Icc a b ⊆ S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card ≤ (Ω \ Finset.Icc a b).card := by
  have hp2 := hp.two_le
  apply two_step_tail_bound Ω (Finset.Icc a b) D a (p : Int)
    (Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
    ⟨by omega,a,b,by intro x; simp⟩ hground hcrooked ha
  · intro S hS T hT hne hSI hTI
    apply PrimeKernel.shared_adjacent_forces_step S T a (hpair S hS T hT hne)
    · exact Finset.mem_inter.mpr ⟨ha S hS,ha T hT⟩
    · have hx : a+1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      exact Finset.mem_inter.mpr ⟨hSI hx,hTI hx⟩
  · intro S hS hnf
    exact coarse_trace_step_prime p hp D a b S hS ha hnext hb hf (hpair S hS) hnf
  · intro S hS T hT hne hnf
    exact nonfine_pair_step_prime p hp a b S T
      (Finset.mem_inter.mpr ⟨ha S hS,ha T hT⟩)
      (Finset.mem_inter.mpr ⟨hnext S hS,hnext T hT⟩)
      (Finset.mem_inter.mpr ⟨hb S hS,hb T hT⟩) hnf (hpair S hS T hT hne)

/-- Strict capacity for an actual prime-step kernel. The endpoint and hull
premises describe the actual finite kernel; no cardinal capacity is assumed. -/
theorem prime_actual_kernel_bound (p : Nat) (hp : p.Prime)
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a b : Int)
    (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (ha : a ∈ Kernel Ω D) (hnext : a+(p : Int) ∈ Kernel Ω D)
    (hb : b ∈ Kernel Ω D) (hkhull : Kernel Ω D ⊆ Finset.Icc a b)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  classical
  have haD : ∀ S ∈ D, a ∈ S := (Finset.mem_filter.mp ha).2
  have hnD : ∀ S ∈ D, a+(p : Int) ∈ S := (Finset.mem_filter.mp hnext).2
  have hbD : ∀ S ∈ D, b ∈ S := (Finset.mem_filter.mp hb).2
  have hab := (Finset.mem_Icc.mp (hkhull ha)).2
  have hnb := (Finset.mem_Icc.mp (hkhull hnext)).2
  by_cases hf : ∃ S ∈ D, Finset.Icc a b ⊆ S
  · have hgr : ∀ S ∈ D, S ⊆ Ω.erase c := by
      intro S hS x hx
      exact Finset.mem_erase.mpr
        ⟨by intro he; exact havoid S hS (he ▸ hx),hground S hS hx⟩
    have htail := prime_joint_tail_bound p hp (Ω.erase c) D a b hab hnb
      hgr hcrooked haD hnD hbD hf hpair
    rcases hf with ⟨S,hS,hSI⟩
    have hI : Finset.Icc a b ⊆ Ω.erase c := fun x hx => hgr S hS (hSI hx)
    have hslots := Finset.card_sdiff_add_card_eq_card hI
    rw [Finset.card_erase_of_mem hc] at hslots
    have hKcard := Finset.card_le_card hkhull
    have hΩpos := Finset.card_pos.mpr ⟨c,hc⟩
    omega
  · apply same_step_avoiders_card_bound Ω D c (p : Int) a hc hm hground havoid
      hcrooked haD
    intro S hS T hT hne
    apply nonfine_pair_step_prime p hp a b S T
      (Finset.mem_inter.mpr ⟨haD S hS,haD T hT⟩)
      (Finset.mem_inter.mpr ⟨hnD S hS,hnD T hT⟩)
      (Finset.mem_inter.mpr ⟨hbD S hS,hbD T hT⟩)
      (by intro hSI; exact hf ⟨S,hS,hSI⟩) (hpair S hS T hT hne)

/-- Canonical actual prime progression; t is the number of gaps. -/
def Progression (p : Nat) (a : Int) (t : Nat) : Finset Int :=
  (Finset.range (t+1)).image (fun i : Nat => a+(p : Int)*(i : Int))

/-- Convenient exact-kernel form, with k=t+1 at least two and any prime p. -/
theorem prime_progression_kernel_bound (p : Nat) (hp : p.Prime)
    (Ω : Finset Int) (D : Finset (Finset Int)) (c a : Int) (t : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hm : 2 ≤ D.card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hkernel : Kernel Ω D = Progression p a t)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T)) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  have ha : a ∈ Progression p a t := by
    exact Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (by omega),by simp⟩
  have hn : a+(p : Int) ∈ Progression p a t := by
    exact Finset.mem_image.mpr ⟨1,Finset.mem_range.mpr (by omega),by simp⟩
  have hb : a+(p : Int)*(t : Int) ∈ Progression p a t := by
    exact Finset.mem_image.mpr ⟨t,Finset.mem_range.mpr (by omega),rfl⟩
  have hsub : Progression p a t ⊆ Finset.Icc a (a+(p : Int)*(t : Int)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i,hi,rfl⟩
    have hit : (i : Int) ≤ (t : Int) := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hp0 : (0 : Int) ≤ (p : Int) := by omega
    have hprod : 0 ≤ (p : Int)*(i : Int) := mul_nonneg hp0 (by omega)
    have hprodle := mul_le_mul_of_nonneg_left hit hp0
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  apply prime_actual_kernel_bound p hp Ω D c a (a+(p : Int)*(t : Int))
    hc hm hground havoid hcrooked
  · simpa only [hkernel] using ha
  · simpa only [hkernel] using hn
  · simpa only [hkernel] using hb
  · simpa only [hkernel] using hsub
  · exact hpair

/-- The uniform prime theorem pays for the original legal family, with the
starred upper bound still supplied as an explicit external premise. -/
theorem prime_avoiders_payment (p : Nat) (hp : p.Prime)
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a : Int) (t B : Nat)
    (ht : 1 ≤ t) (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hkernel : Kernel Ω (Avoiders F c) = Progression p a t) :
    F.card + 1 ≤ B := by
  have hcap := prime_progression_kernel_bound p hp Ω (Avoiders F c) c a t
    ht hc hm
    (fun S hS => hF.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2) hcrooked hkernel
    (fun S hS T hT hne => hF.2 S (Finset.mem_filter.mp hS).1 T
      (Finset.mem_filter.mp hT).1 hne)
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms two_step_tail_bound
#print axioms positive_divisor_prime
#print axioms step_one_or_prime
#print axioms nonfine_pair_step_prime
#print axioms coarse_trace_step_prime
#print axioms prime_joint_tail_bound
#print axioms prime_actual_kernel_bound
#print axioms prime_progression_kernel_bound
#print axioms prime_avoiders_payment

end JSP233.PrimeCapacity
