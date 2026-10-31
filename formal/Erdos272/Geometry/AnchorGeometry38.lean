import Erdos272.Core.AnchorAssembly37

/-! Actual divisor traces constructed from integer AP anchors.
No downset, prefix key, shell count or physical-cell budget is assumed. -/
namespace JSP233.AnchorGeometry38
open StarCompletion APGeometry AnchorCapacity33 FactorCells34 DivisorCells34 AnchorAssembly37
open scoped Classical BigOperators
noncomputable section

def LiftCoordinate (g : ℕ) (a : PrimeCoordinates g) : ℕ→₀ℕ :=
  Finsupp.onFinset g.primeFactors (fun p => if hp : p∈g.primeFactors then a ⟨p,hp⟩ else 0)
    (by intro p hp; by_contra hn; simp [hn] at hp)

theorem liftCoordinate_at (g : ℕ) (a : PrimeCoordinates g) (p : ↥g.primeFactors) :
    LiftCoordinate g a p.val=a p := by
  simp only [LiftCoordinate,Finsupp.onFinset_apply,dif_pos p.property]

theorem exponent_box_surjective (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors)
    (a : PrimeCoordinates g) (ha : a≤Exponent g d) :
    ∃ e∈g.divisors, Exponent g e=a ∧ d∣e := by
  have hle : LiftCoordinate g a≤(g/d).factorization := by
    intro p
    by_cases hp : p∈g.primeFactors
    · simpa only [LiftCoordinate,Finsupp.onFinset_apply,dif_pos hp,Exponent] using ha ⟨p,hp⟩
    · simp only [LiftCoordinate,Finsupp.onFinset_apply,dif_neg hp]
      exact Nat.zero_le _
  obtain ⟨e,he,heq⟩ := quotient_factorization_surjective g hg (LiftCoordinate g a)
    (hle.trans (quotient_factorization_le_base g d hg hd))
  have hexp : Exponent g e=a := by
    funext p
    change (g/e).factorization p.val=a p
    rw [heq,liftCoordinate_at]
  refine ⟨e,he,hexp,?_⟩
  apply (exponent_le_iff g e d hg he hd).mp
  rwa [hexp]

theorem actualExponent_le_iff (g n d e : ℕ) (hc : g.primeFactors.card=n+1)
    (hg : 0<g) (hd : d∈g.divisors) (he : e∈g.divisors) :
    ActualExponent g n hc d≤ActualExponent g n hc e ↔ e∣d := by
  constructor
  · intro hh
    apply (exponent_le_iff g d e hg hd he).mp
    intro p
    obtain ⟨i,rfl⟩ := (OrderedPrime g n hc).surjective p
    exact hh i
  · intro hh i
    exact ((exponent_le_iff g d e hg hd he).mpr hh) (OrderedPrime g n hc i)

theorem actualExponent_box_surjective (g n d : ℕ) (hc : g.primeFactors.card=n+1)
    (hg : 0<g) (hd : d∈g.divisors) (a : AnchorAssembly37.Point n)
    (ha : a≤ActualExponent g n hc d) :
    ∃ e∈g.divisors, ActualExponent g n hc e=a ∧ d∣e := by
  let b : PrimeCoordinates g := fun p => a ((OrderedPrime g n hc).symm p)
  have hb : b≤Exponent g d := by
    intro p
    have hh := ha ((OrderedPrime g n hc).symm p)
    simpa only [ActualExponent,OrderIso.apply_symm_apply,b] using hh
  obtain ⟨e,he,hex,hde⟩ := exponent_box_surjective g d hg hd b hb
  refine ⟨e,he,?_,hde⟩
  funext i
  change Exponent g e (OrderedPrime g n hc i)=a i
  rw [hex]
  simp only [b,OrderIso.symm_apply_apply]

def ActualSteps (S : Finset ℤ) (u v : ℤ) (g : ℕ) : Finset ℕ :=
  g.divisors.filter (fun d => AnchorTrace u v (d:ℤ)⊆S)

def ActualTrace (S : Finset ℤ) (u v : ℤ) (g n : ℕ)
    (hc : g.primeFactors.card=n+1) : Finset (AnchorAssembly37.Point n) :=
  (ActualSteps S u v g).image (ActualExponent g n hc)

theorem mem_actualSteps {S : Finset ℤ} {u v : ℤ} {g d : ℕ} :
    d∈ActualSteps S u v g ↔ d∈g.divisors ∧ AnchorTrace u v (d:ℤ)⊆S := by
  simp only [ActualSteps,Finset.mem_filter]

theorem actualSteps_subset_divisors (S : Finset ℤ) (u v : ℤ) (g : ℕ) :
    ActualSteps S u v g⊆g.divisors := fun _ hd => (mem_actualSteps.mp hd).1

theorem actualSteps_monotone {S T : Finset ℤ} {u v : ℤ} {g : ℕ} (hST : S⊆T) :
    ActualSteps S u v g⊆ActualSteps T u v g := by
  intro d hd
  exact mem_actualSteps.mpr ⟨(mem_actualSteps.mp hd).1,(mem_actualSteps.mp hd).2.trans hST⟩

theorem actualSteps_upward {S : Finset ℤ} {u v : ℤ} {g d e : ℕ}
    (hd : d∈ActualSteps S u v g) (he : e∈g.divisors) (hde : d∣e) :
    e∈ActualSteps S u v g := by
  exact mem_actualSteps.mpr ⟨he,(anchorTrace_antitone (by exact_mod_cast hde)).trans (mem_actualSteps.mp hd).2⟩

theorem actualTrace_downclosed (S : Finset ℤ) (u v : ℤ) (g n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g) :
    DownClosed (ActualTrace S u v g n hc) := by
  intro a ha b hba
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨e,he,heq,hde⟩ := actualExponent_box_surjective g n d hc hg (mem_actualSteps.mp hd).1 b hba
  exact Finset.mem_image.mpr ⟨e,actualSteps_upward hd he hde,heq⟩

theorem actualSteps_inter (S T : Finset ℤ) (u v : ℤ) (g : ℕ) :
    ActualSteps (S∩T) u v g=ActualSteps S u v g∩ActualSteps T u v g := by
  ext d
  simp only [mem_actualSteps,Finset.mem_inter]
  constructor
  · rintro ⟨hd,hs⟩
    exact ⟨⟨hd,fun x hx => (Finset.mem_inter.mp (hs hx)).1⟩,
      ⟨hd,fun x hx => (Finset.mem_inter.mp (hs hx)).2⟩⟩
  · rintro ⟨⟨hd,hs⟩,⟨_,ht⟩⟩
    exact ⟨hd,fun x hx => Finset.mem_inter.mpr ⟨hs hx,ht hx⟩⟩

theorem actualTrace_inter (S T : Finset ℤ) (u v : ℤ) (g n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g) :
    ActualTrace (S∩T) u v g n hc=ActualTrace S u v g n hc∩ActualTrace T u v g n hc := by
  rw [ActualTrace,actualSteps_inter]
  ext a
  constructor
  · intro ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨d,(Finset.mem_inter.mp hd).1,rfl⟩,
      Finset.mem_image.mpr ⟨d,(Finset.mem_inter.mp hd).2,rfl⟩⟩
  · intro ha
    obtain ⟨d,hd,hda⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
    obtain ⟨e,he,hea⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).2
    have hde : d=e := actualExponent_injective g n hc hg (mem_actualSteps.mp hd).1
      (mem_actualSteps.mp he).1 (hda.trans hea.symm)
    subst e
    exact Finset.mem_image.mpr ⟨d,Finset.mem_inter.mpr ⟨hd,he⟩,hda⟩

theorem actualTrace_nonempty {S : Finset ℤ} {u v : ℤ} {g n : ℕ}
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hK : AnchorTrace u v (g:ℤ)⊆S) :
    (ActualTrace S u v g n hc).Nonempty := by
  exact Finset.image_nonempty.mpr ⟨g,mem_actualSteps.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_refl g,hg.ne'⟩,hK⟩⟩

theorem actualTrace_physical_principal {S : Finset ℤ} {u v : ℤ} {g n q : ℕ}
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hspan : u+(g:ℤ)≤v)
    (hq : q∈g.divisors) (htrace : S∩Finset.Icc u v=AnchorTrace u v (q:ℤ)) :
    ActualTrace S u v g n hc=Finset.Iic (ActualExponent g n hc q) := by
  ext a
  constructor
  · intro ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hdg,hds⟩ := mem_actualSteps.mp hd
    have hsub : AnchorTrace u v (d:ℤ)⊆AnchorTrace u v (q:ℤ) := by
      rw [←htrace]
      exact fun x hx => Finset.mem_inter.mpr ⟨hds hx,(Finset.mem_filter.mp hx).1⟩
    have hqd : q∣d := by
      have hh := (anchorTrace_subset_iff (by exact_mod_cast hg) hspan
        (by exact_mod_cast Nat.pos_of_mem_divisors hdg)
        (by exact_mod_cast Nat.dvd_of_mem_divisors hdg)).mp hsub
      exact_mod_cast hh
    exact Finset.mem_Iic.mpr ((actualExponent_le_iff g n d q hc hg hdg hq).mpr hqd)
  · intro ha
    obtain ⟨d,hd,heq,hqd⟩ := actualExponent_box_surjective g n q hc hg hq a (Finset.mem_Iic.mp ha)
    refine Finset.mem_image.mpr ⟨d,mem_actualSteps.mpr ⟨hd,?_⟩,heq⟩
    intro x hx
    have hh := anchorTrace_antitone (by exact_mod_cast hqd : (q:ℤ)∣(d:ℤ)) hx
    rw [←htrace] at hh
    exact (Finset.mem_inter.mp hh).1

theorem actual_pair_trace_principal {S T : Finset ℤ} {u v : ℤ} {g n : ℕ}
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hspan : u+(g:ℤ)≤v)
    (hpair : IsAP (S∩T)) (hu : u∈S∩T) (hug : u+(g:ℤ)∈S∩T) (hv : v∈S∩T) :
    Principal (ActualTrace S u v g n hc∩ActualTrace T u v g n hc) := by
  obtain ⟨q,hq,hqg,htrace⟩ := actual_pair_anchor_trace hpair hu hug hv
  have hqcast : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hq.le
  have hqN : q.toNat∈g.divisors := Nat.mem_divisors.mpr ⟨by
    exact_mod_cast (show (q.toNat:ℤ)∣(g:ℤ) by rwa [hqcast]),hg.ne'⟩
  rw [←actualTrace_inter S T u v g n hc hg]
  refine ⟨ActualExponent g n hc q.toNat,?_⟩
  exact actualTrace_physical_principal hc hg hspan hqN (by simpa only [hqcast] using htrace)

theorem actual_pair_trace_joinClosed {S T : Finset ℤ} {u v : ℤ} {g n : ℕ}
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hspan : u+(g:ℤ)≤v)
    (hpair : IsAP (S∩T)) (hu : u∈S∩T) (hug : u+(g:ℤ)∈S∩T) (hv : v∈S∩T) :
    JoinClosed (ActualTrace S u v g n hc∩ActualTrace T u v g n hc) := by
  obtain ⟨a,ha⟩ := actual_pair_trace_principal hc hg hspan hpair hu hug hv
  rw [ha]
  exact principal_joinClosed a

theorem actual_nonprivate_nat_trace_union {D : Finset (Finset ℤ)} {S : Finset ℤ}
    {u v : ℤ} {g : ℕ} (hg : 0<g) (hS : S∈D)
    (hu : ∀ T∈D, u∈T) (hug : ∀ T∈D, u+(g:ℤ)∈T) (hv : ∀ T∈D, v∈T)
    (hpair : ∀ T∈D, ∀ R∈D, T≠R → IsAP (T∩R))
    (hcover : ∀ x∈S, ∃ T∈D, T≠S ∧ x∈T) :
    S∩Finset.Icc u v=(ActualSteps S u v g).biUnion (fun d => AnchorTrace u v (d:ℤ)) := by
  have hunion := actual_nonprivate_trace_union (by exact_mod_cast hg) hS hu hug hv hpair hcover
  ext x
  constructor
  · intro hx
    rw [hunion] at hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hd1,hdg,hdiv,hsub⟩ := (mem_divisorSteps S u v (g:ℤ) d).mp hd
    have hdcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg (by omega)
    have hdN : d.toNat∈g.divisors := Nat.mem_divisors.mpr ⟨by
      exact_mod_cast (show (d.toNat:ℤ)∣(g:ℤ) by rwa [hdcast]),hg.ne'⟩
    exact Finset.mem_biUnion.mpr ⟨d.toNat,mem_actualSteps.mpr ⟨hdN,by simpa only [hdcast] using hsub⟩,
      by simpa only [hdcast] using hxd⟩
  · intro hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_inter.mpr ⟨(mem_actualSteps.mp hd).2 hxd,(Finset.mem_filter.mp hxd).1⟩

theorem actual_retained_nat_trace_union {D : Finset (Finset ℤ)} {S : Finset ℤ}
    {u v : ℤ} {g : ℕ} (hg : 0<g) (hS : S∈Retained D)
    (hu : ∀ T∈D, u∈T) (hug : ∀ T∈D, u+(g:ℤ)∈T) (hv : ∀ T∈D, v∈T)
    (hpair : ∀ T∈D, ∀ R∈D, T≠R → IsAP (T∩R)) :
    S∩Finset.Icc u v=(ActualSteps S u v g).biUnion (fun d => AnchorTrace u v (d:ℤ)) := by
  obtain ⟨hSD,hcover⟩ := Finset.mem_filter.mp hS
  exact actual_nonprivate_nat_trace_union hg hSD hu hug hv hpair hcover

theorem actual_trace_principal_pure {S : Finset ℤ} {u v : ℤ} {g n : ℕ}
    (hc : g.primeFactors.card=n+1) (hg : 0<g)
    (hunion : S∩Finset.Icc u v=(ActualSteps S u v g).biUnion (fun d => AnchorTrace u v (d:ℤ)))
    (hp : Principal (ActualTrace S u v g n hc)) :
    ∃ d : ℕ, d∈ActualSteps S u v g ∧ TailSelection34.PureTrace u v (g:ℤ) (d:ℤ) S := by
  obtain ⟨a,ha⟩ := hp
  have hamem : a∈ActualTrace S u v g n hc := by rw [ha]; exact Finset.mem_Iic.mpr le_rfl
  obtain ⟨d,hd,hda⟩ := Finset.mem_image.mp hamem
  refine ⟨d,hd,by exact_mod_cast Nat.pos_of_mem_divisors (mem_actualSteps.mp hd).1,
    by exact_mod_cast Nat.dvd_of_mem_divisors (mem_actualSteps.mp hd).1,?_⟩
  rw [hunion]
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hx
    have hea : ActualExponent g n hc e≤a := by
      apply Finset.mem_Iic.mp
      rw [←ha]
      exact Finset.mem_image.mpr ⟨e,he,rfl⟩
    have hde : d∣e := (actualExponent_le_iff g n e d hc hg (mem_actualSteps.mp he).1
      (mem_actualSteps.mp hd).1).mp (by rwa [hda])
    exact anchorTrace_antitone (by exact_mod_cast hde) hxe
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨d,hd,hx⟩

theorem actual_cell_subset_of_step {S : Finset ℤ} {u : ℤ} {g M d : ℕ}
    (hd : d∈ActualSteps S u (u+((g*M:ℕ):ℤ)) g) : Cell u g M d⊆S := by
  intro x hx
  apply (mem_actualSteps.mp hd).2
  exact (trace_mem_iff_label_dvd hx (Nat.dvd_of_mem_divisors (mem_actualSteps.mp hd).1)).mpr (dvd_refl d)

theorem actual_retained_cells_exact {D : Finset (Finset ℤ)} {S : Finset ℤ}
    {u : ℤ} {g M : ℕ} (hg : 0<g) (hS : S∈Retained D)
    (hu : ∀ T∈D, u∈T) (hug : ∀ T∈D, u+(g:ℤ)∈T)
    (hv : ∀ T∈D, u+((g*M:ℕ):ℤ)∈T)
    (hpair : ∀ T∈D, ∀ R∈D, T≠R → IsAP (T∩R)) :
    S∩Finset.Icc u (u+((g*M:ℕ):ℤ))=
      (ActualSteps S u (u+((g*M:ℕ):ℤ)) g).biUnion (Cell u g M) := by
  have hunion := actual_retained_nat_trace_union hg hS hu hug hv hpair
  ext x
  constructor
  · intro hx
    have hxI := (Finset.mem_inter.mp hx).2
    rw [hunion] at hx
    obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hx
    let d := Int.gcd (x-u) (g:ℤ)
    have hxc : x∈Cell u g M d := Finset.mem_filter.mpr ⟨hxI,rfl⟩
    have hdg := Nat.mem_divisors.mpr ⟨cell_label_dvd hxc,hg.ne'⟩
    have hed : e∣d := (trace_mem_iff_label_dvd hxc
      (Nat.dvd_of_mem_divisors (mem_actualSteps.mp he).1)).mp hxe
    exact Finset.mem_biUnion.mpr ⟨d,actualSteps_upward he hdg hed,hxc⟩
  · intro hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_inter.mpr ⟨actual_cell_subset_of_step hd hxd,(Finset.mem_filter.mp hxd).1⟩

theorem anchor_points (u : ℤ) (g M : ℕ) (hg : 0<g) (hM : 0<M) :
    u∈AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) ∧
      u+(g:ℤ)∈AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) ∧
      u+((g*M:ℕ):ℤ)∈AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) := by
  have hgm : g≤g*M := by simpa only [mul_one] using Nat.mul_le_mul_left g (by omega : 1≤M)
  have hgZ : (0:ℤ)<g := by exact_mod_cast hg
  have hgmZ : (g:ℤ)≤((g*M:ℕ):ℤ) := by exact_mod_cast hgm
  refine ⟨(mem_anchorTrace _ _ _ _).mpr ⟨le_rfl,by omega,by simp⟩,
    (mem_anchorTrace _ _ _ _).mpr ⟨by omega,by omega,by simp⟩,
    (mem_anchorTrace _ _ _ _).mpr ⟨by omega,le_rfl,?_⟩⟩
  simp only [add_sub_cancel_left,Nat.cast_mul]
  exact dvd_mul_right (g:ℤ) (M:ℤ)

theorem actual_retained_anchor_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (g M n : ℕ) (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆S)
    (hret : (Retained D).Nonempty) :
    (Retained D).card+(M+1)≤((Retained D).biUnion id).card := by
  classical
  let v := u+((g*M:ℕ):ℤ)
  let R := Retained D
  let tr := fun S => ActualTrace S u v g n hc
  let P := R.filter (fun S => Principal (tr S))
  let F := R.filter (fun S => ¬Principal (tr S))
  let A := R.biUnion (fun S => ActualSteps S u v g)
  have hRD : R⊆D := Finset.filter_subset _ _
  have hPD : P⊆D := (Finset.filter_subset _ _).trans hRD
  have hFD : F⊆D := (Finset.filter_subset _ _).trans hRD
  have hdecomp : P∪F=R := by
    ext S
    simp only [P,F,Finset.mem_union,Finset.mem_filter]
    tauto
  have hdis : Disjoint P F := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    exact (Finset.mem_filter.mp hT).2 (Finset.mem_filter.mp hS).2
  have hpts := anchor_points u g M hg hM
  have hu : ∀ S∈D, u∈S := fun S hS => hanchor S hS hpts.1
  have hug : ∀ S∈D, u+(g:ℤ)∈S := fun S hS => hanchor S hS hpts.2.1
  have hv : ∀ S∈D, v∈S := fun S hS => hanchor S hS hpts.2.2
  have hspan : u+(g:ℤ)≤v := ((mem_anchorTrace _ _ _ _).mp hpts.2.1).2.1
  have hunion : ∀ S∈R, S∩Finset.Icc u v=
      (ActualSteps S u v g).biUnion (fun d => AnchorTrace u v (d:ℤ)) := by
    intro S hS
    exact actual_retained_nat_trace_union hg hS hu hug hv hlegal.2
  have hppure : ∀ S∈P, ∃ d : ℕ, d∈ActualSteps S u v g ∧ TailSelection34.PureTrace u v (g:ℤ) (d:ℤ) S := by
    intro S hS
    exact actual_trace_principal_pure hc hg (hunion S (Finset.mem_filter.mp hS).1)
      (Finset.mem_filter.mp hS).2
  let step := fun S => if hs : S∈P then (hppure S hs).choose else g
  have hstep : ∀ S∈P, step S∈ActualSteps S u v g ∧ TailSelection34.PureTrace u v (g:ℤ) (step S:ℤ) S := by
    intro S hS
    simpa only [step,dif_pos hS] using (hppure S hS).choose_spec
  have hA : A⊆g.divisors := by
    intro d hd
    obtain ⟨S,hS,hdS⟩ := Finset.mem_biUnion.mp hd
    exact (mem_actualSteps.mp hdS).1
  have hsteps : ∀ S∈P, step S∈A := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨S,(Finset.mem_filter.mp hS).1,(hstep S hS).1⟩
  have hsub : ∀ S∈F, tr S⊆A.image (ActualExponent g n hc) := by
    intro S hS a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨d,Finset.mem_biUnion.mpr ⟨S,(Finset.mem_filter.mp hS).1,hd⟩,rfl⟩
  have hcell : (A.erase g).biUnion (Cell u g M)⊆(P∪F).biUnion id := by
    intro x hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨S,hS,hdS⟩ := Finset.mem_biUnion.mp (Finset.mem_erase.mp hd).2
    rw [hdecomp]
    exact Finset.mem_biUnion.mpr ⟨S,hS,actual_cell_subset_of_step hdS hxd⟩
  have hanc : AnchorTrace u v (g:ℤ)⊆(P∪F).biUnion id := by
    obtain ⟨S,hS⟩ := hret
    intro x hx
    rw [hdecomp]
    exact Finset.mem_biUnion.mpr ⟨S,hS,hanchor S (hRD hS) hx⟩
  have hcap := actual_mixed_union_capacity u g M n hc hg hM P F step tr
    (fun S hS => (hstep S hS).2) (fun S hS => hbad S (hPD hS))
    (fun S hS T hT hne => hlegal.2 S (hPD hS) T (hPD hT) hne) A hA hsteps hsub
    (fun S hS => actualTrace_nonempty hc hg (hanchor S (hFD hS)))
    (fun S _ => actualTrace_downclosed S u v g n hc hg)
    (fun S hS => (Finset.mem_filter.mp hS).2)
    (fun S hS T hT hne => actual_pair_trace_joinClosed hc hg hspan
      (hlegal.2 S (hFD hS) T (hFD hT) hne)
      (Finset.mem_inter.mpr ⟨hu S (hFD hS),hu T (hFD hT)⟩)
      (Finset.mem_inter.mpr ⟨hug S (hFD hS),hug T (hFD hT)⟩)
      (Finset.mem_inter.mpr ⟨hv S (hFD hS),hv T (hFD hT)⟩)) hcell hanc
  rw [hdecomp] at hcap
  have he := Finset.card_union_of_disjoint hdis
  rw [hdecomp] at he
  change R.card+(M+1)≤(R.biUnion id).card
  omega

theorem removed_original_private_point {D : Finset (Finset ℤ)} {S : Finset ℤ}
    (hS : S∈D\Retained D) :
    ∃ x∈S, ∀ T∈D, T≠S → x∉T := by
  classical
  obtain ⟨hSD,hSn⟩ := Finset.mem_sdiff.mp hS
  have hh : ¬∀ x, x∈S → ∃ T∈D, T≠S ∧ x∈T := by
    intro hc
    exact hSn (Finset.mem_filter.mpr ⟨hSD,hc⟩)
  obtain ⟨x,hx⟩ := not_forall.mp hh
  have hxS : x∈S := by
    by_contra hn
    exact hx (fun hs => (hn hs).elim)
  refine ⟨x,hxS,?_⟩
  intro T hT hTS hxT
  exact hx (fun _ => ⟨T,hT,hTS,hxT⟩)

theorem actual_simultaneous_private_peeling (D : Finset (Finset ℤ)) (K : Finset ℤ)
    (hD : 2≤D.card) (hcommon : ∀ S∈D, K⊆S)
    (hretcap : (Retained D).Nonempty → (Retained D).card+K.card≤((Retained D).biUnion id).card) :
    D.card+K.card≤(D.biUnion id).card := by
  classical
  let R := Retained D
  let E := D\R
  let U := D.biUnion id
  let V := R.biUnion id∪K
  have hRD : R⊆D := Finset.filter_subset _ _
  have hp : ∀ S∈E, ∃ x∈S, ∀ T∈D, T≠S → x∉T := fun S hS => removed_original_private_point hS
  let point := fun S => if hs : S∈E then (hp S hs).choose else 0
  have hpoint : ∀ S∈E, point S∈S ∧ ∀ T∈D, T≠S → point S∉T := by
    intro S hS
    simpa only [point,dif_pos hS] using (hp S hS).choose_spec
  have hpointK : ∀ S∈E, point S∉K := by
    intro S hS hx
    obtain ⟨T,hT,hTS⟩ := Finset.exists_mem_ne (by omega : 1<D.card) S
    exact (hpoint S hS).2 T hT hTS (hcommon T hT hx)
  have hinj : Set.InjOn point (E : Set (Finset ℤ)) := by
    intro S hS T hT he
    by_contra hST
    have hxT : point S∈T := he ▸ (hpoint T hT).1
    exact (hpoint S hS).2 T (Finset.mem_sdiff.mp hT).1 (fun hh => hST hh.symm) hxT
  have hVU : V⊆U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxK
    · obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hxR
      exact Finset.mem_biUnion.mpr ⟨S,hRD hS,hxS⟩
    · obtain ⟨S,hS⟩ := Finset.card_pos.mp (by omega : 0<D.card)
      exact Finset.mem_biUnion.mpr ⟨S,hS,hcommon S hS hxK⟩
  have hXU : E.image point⊆U := by
    intro x hx
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨S,(Finset.mem_sdiff.mp hS).1,(hpoint S hS).1⟩
  have hdis : Disjoint V (E.image point) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_union.mp hx with hxR | hxK
    · obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hxR
      have hTS : T≠S := by
        intro he
        exact (Finset.mem_sdiff.mp hS).2 (he ▸ hT)
      exact (hpoint S hS).2 T (hRD hT) hTS hxT
    · exact hpointK S hS hxK
  have hresource := Finset.card_le_card (Finset.union_subset hVU hXU)
  rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injOn hinj] at hresource
  have hV : R.card+K.card≤V.card := by
    by_cases hr : R.Nonempty
    · have hK : K⊆R.biUnion id := by
        obtain ⟨S,hS⟩ := hr
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨S,hS,hcommon S (hRD hS) hx⟩
      have heq : V=R.biUnion id := Finset.union_eq_left.mpr hK
      rw [heq]
      exact hretcap hr
    · have heq : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hr
      simp only [V,heq,Finset.card_empty,Finset.biUnion_empty,Finset.empty_union,zero_add,le_refl]
  have hcards := Finset.card_sdiff_add_card_eq_card hRD
  change E.card+R.card=D.card at hcards
  change D.card+K.card≤U.card
  omega

theorem actual_anchor_isAP (u : ℤ) (g M : ℕ) (hg : 0<g) :
    IsAP (AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)) := by
  refine ⟨(g:ℤ),u,by exact_mod_cast hg,u,u+((g*M:ℕ):ℤ),?_,?_⟩
  · intro x
    exact mem_anchorTrace _ _ _ _
  · exact (mem_anchorTrace _ _ _ _).mpr ⟨le_rfl,by omega,by simp⟩

theorem actual_anchor_capacity_with_coordinates (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (g M n : ℕ) (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (hD : D.Nonempty) (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆S) :
    D.card+(M+1)≤(D.biUnion id).card := by
  let K := AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)
  have hK : K.card=M+1 := anchor_trace_card u g M hg
  by_cases htwo : 2≤D.card
  · have hh := actual_simultaneous_private_peeling D K htwo hanchor (by
      intro hr
      rw [hK]
      exact actual_retained_anchor_capacity Ω D u g M n hc hg hM hlegal hbad hanchor hr)
    rwa [hK] at hh
  · obtain ⟨S,hS⟩ := hD
    have hKAP : IsAP K := actual_anchor_isAP u g M hg
    have hne : K≠S := by intro he; exact hbad S hS (he ▸ hKAP)
    have hstrict : K⊂S := ⟨hanchor S hS,fun hs => hne (Finset.Subset.antisymm (hanchor S hS) hs)⟩
    have hlt := Finset.card_lt_card hstrict
    have hsub : S⊆D.biUnion id := fun x hx => Finset.mem_biUnion.mpr ⟨S,hS,hx⟩
    have hle := Finset.card_le_card hsub
    have hpos := Finset.card_pos.mpr ⟨S,hS⟩
    omega

theorem actual_unit_anchor_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (M : ℕ) (hM : 0<M) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((1*M:ℕ):ℤ)) 1⊆S) :
    D.card+(M+1)≤(D.biUnion id).card := by
  classical
  let v := u+((1*M:ℕ):ℤ)
  let K := AnchorTrace u v 1
  let U := D.biUnion id
  have hKI : K=Finset.Icc u v := by
    ext x
    simp only [K,mem_anchorTrace,Finset.mem_Icc,one_dvd,and_true]
  have hpure : ∀ S∈D, TailSelection34.PureTrace u v 1 (1:ℕ) S := by
    intro S hS
    refine ⟨by norm_num,by norm_num,?_⟩
    rw [←hKI]
    exact Finset.inter_eq_right.mpr (hanchor S hS)
  have hspan : u+1≤v := by dsimp [v]; omega
  obtain ⟨tail,ht,hinj⟩ := PureTailCollision35.actual_pure_unit_anchor_no_collision D (fun _ => 1)
    u v hspan hpure hbad hlegal.2
  have hKU : K⊆U := by
    obtain ⟨S,hS⟩ := hD
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨S,hS,hanchor S hS hx⟩
  have hTU : D.image tail⊆U := by
    intro x hx
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨S,hS,(ht S hS).1⟩
  have hdis : Disjoint K (D.image tail) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hy
    exact (ht S hS).2.1 (hKI ▸ hx)
  have hcard := Finset.card_le_card (Finset.union_subset hKU hTU)
  rw [Finset.card_union_of_disjoint hdis,hinj] at hcard
  have hK : K.card=M+1 := anchor_trace_card u 1 M (by norm_num)
  change D.card+(M+1)≤U.card
  omega

theorem actual_anchor_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (g M : ℕ) (hg : 0<g) (hM : 0<M) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆S) :
    D.card+(M+1)≤(D.biUnion id).card := by
  by_cases hg1 : g=1
  · subst g
    exact actual_unit_anchor_capacity Ω D u M hM hD hlegal hbad hanchor
  · obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hg1
    have hpf : g.primeFactors.Nonempty := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpg,hg.ne'⟩⟩
    have hcard : 0<g.primeFactors.card := hpf.card_pos
    let n := g.primeFactors.card-1
    have hc : g.primeFactors.card=n+1 := by dsimp [n]; omega
    exact actual_anchor_capacity_with_coordinates Ω D u g M n hc hg hM hD hlegal hbad hanchor

theorem actual_fixed_AP_anchor_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (g M : ℕ) (hg : 0<g) (hM : 0<M) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆S) :
    D.card+(AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)).card≤(D.biUnion id).card := by
  rw [anchor_trace_card u g M hg]
  exact actual_anchor_capacity Ω D u g M hg hM hD hlegal hbad hanchor

theorem actual_fixed_AP_anchor_ground_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (u : ℤ) (g M : ℕ) (hg : 0<g) (hM : 0<M) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S)
    (hanchor : ∀ S∈D, AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆S) :
    D.card+(AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)).card≤Ω.card := by
  have hsub : D.biUnion id⊆Ω := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    exact hlegal.1 S hS hxS
  exact (actual_fixed_AP_anchor_capacity Ω D u g M hg hM hD hlegal hbad hanchor).trans
    (Finset.card_le_card hsub)

theorem actual_AP_anchor_representation (K : Finset ℤ) (hK : IsAP K) (htwo : 2≤K.card) :
    ∃ u : ℤ, ∃ g M : ℕ, 0<g ∧ 0<M ∧ K=AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) := by
  obtain ⟨d,p,hAP,_⟩ := (isAP_iff_exists_APAt K).mp hK
  obtain ⟨a,b,ha,_,hb,hbounds,hspan⟩ := apAt_adjacent_min hAP htwo
  have hdcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hAP.1.le
  have hg : 0<d.toNat := by have hdpos := hAP.1; omega
  have hM : 0<K.card-1 := by omega
  have hMcast : ((K.card-1:ℕ):ℤ)=(K.card:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤K.card),Nat.cast_one]
  have hbEq : b=a+((d.toNat*(K.card-1):ℕ):ℤ) := by
    rw [Nat.cast_mul,hdcast,hMcast]
    linarith
  have hKI : K∩Finset.Icc a b=K := Finset.inter_eq_left.mpr
    (fun x hx => Finset.mem_Icc.mpr (hbounds x hx))
  have htrace := TailSelection34.APAt_trace_eq (apAt_rebase hAP ha) ha hb
  rw [hKI] at htrace
  refine ⟨a,d.toNat,K.card-1,hg,hM,?_⟩
  rw [←hbEq,hdcast]
  exact htrace

theorem actual_arbitrary_AP_anchor_capacity (Ω K : Finset ℤ) (D : Finset (Finset ℤ))
    (hK : IsAP K) (hk : 2≤K.card) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S) (hanchor : ∀ S∈D, K⊆S) :
    D.card+K.card≤(D.biUnion id).card := by
  obtain ⟨u,g,M,hg,hM,hrep⟩ := actual_AP_anchor_representation K hK hk
  rw [hrep] at hanchor ⊢
  exact actual_fixed_AP_anchor_capacity Ω D u g M hg hM hD hlegal hbad hanchor

theorem actual_arbitrary_AP_anchor_ground_capacity (Ω K : Finset ℤ) (D : Finset (Finset ℤ))
    (hK : IsAP K) (hk : 2≤K.card) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S) (hanchor : ∀ S∈D, K⊆S) :
    D.card+K.card≤Ω.card := by
  have hsub : D.biUnion id⊆Ω := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    exact hlegal.1 S hS hxS
  exact (actual_arbitrary_AP_anchor_capacity Ω K D hK hk hD hlegal hbad hanchor).trans
    (Finset.card_le_card hsub)

theorem actual_avoiding_AP_anchor_capacity (Ω K : Finset ℤ) (D : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ω) (hK : IsAP K) (hk : 2≤K.card) (hD : D.Nonempty)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S) (hanchor : ∀ S∈D, K⊆S)
    (havoid : ∀ S∈D, c∉S) : D.card+K.card+1≤Ω.card := by
  have hsub : D.biUnion id⊆Ω.erase c := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_erase.mpr ⟨by intro he; exact havoid S hS (he ▸ hxS),hlegal.1 S hS hxS⟩
  have hcap := (actual_arbitrary_AP_anchor_capacity Ω K D hK hk hD hlegal hbad hanchor).trans
    (Finset.card_le_card hsub)
  rw [Finset.card_erase_of_mem hc] at hcap
  have hp := Finset.card_pos.mpr ⟨c,hc⟩
  omega

theorem actual_kernel_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ))
    (hm : 2≤D.card) (hk : 2≤(PrivateFinset.Kernel Ω D).card)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S) :
    D.card+(PrivateFinset.Kernel Ω D).card≤Ω.card := by
  have hne : (PrivateFinset.Kernel Ω D).Nonempty := Finset.card_pos.mp (by omega)
  have hK : IsAP (PrivateFinset.Kernel Ω D) := actual_common_kernel_isAP Ω D hlegal.1 hlegal.2 hm hne
  exact actual_arbitrary_AP_anchor_ground_capacity Ω _ D hK hk (Finset.card_pos.mp (by omega)) hlegal hbad
    (fun S hS x hx => (Finset.mem_filter.mp hx).2 S hS)

theorem actual_avoiding_kernel_capacity (Ω : Finset ℤ) (D : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ω) (hm : 2≤D.card) (hk : 2≤(PrivateFinset.Kernel Ω D).card)
    (hlegal : Legal Ω D) (hbad : ∀ S∈D, ¬IsAP S) (havoid : ∀ S∈D, c∉S) :
    D.card+(PrivateFinset.Kernel Ω D).card+1≤Ω.card := by
  have hne : (PrivateFinset.Kernel Ω D).Nonempty := Finset.card_pos.mp (by omega)
  have hK : IsAP (PrivateFinset.Kernel Ω D) := actual_common_kernel_isAP Ω D hlegal.1 hlegal.2 hm hne
  exact actual_avoiding_AP_anchor_capacity Ω _ D c hc hK hk (Finset.card_pos.mp (by omega)) hlegal hbad
    (fun S hS x hx => (Finset.mem_filter.mp hx).2 S hS) havoid

theorem general_crooked_avoiders_payment (Ω : Finset ℤ) (F : Finset (Finset ℤ)) (c : ℤ) (B : ℕ)
    (hc : c∈Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2≤(Avoiders F c).card) (hk : 2≤(CommonKernel Ω F c).card)
    (hbad : ∀ S∈Avoiders F c, ¬IsAP S) : F.card+1≤B := by
  have hlegal : Legal Ω (Avoiders F c) := ⟨
    fun S hS => hF.1 S (Finset.mem_filter.mp hS).1,
    fun S hS T hT hne => hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne⟩
  have hcap := actual_avoiding_kernel_capacity Ω (Avoiders F c) c hc hm hk hlegal hbad
    (fun S hS => (Finset.mem_filter.mp hS).2)
  change (Avoiders F c).card+(CommonKernel Ω F c).card+1≤Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms liftCoordinate_at
#print axioms exponent_box_surjective
#print axioms actualExponent_le_iff
#print axioms actualExponent_box_surjective
#print axioms mem_actualSteps
#print axioms actualSteps_subset_divisors
#print axioms actualSteps_monotone
#print axioms actualSteps_upward
#print axioms actualTrace_downclosed
#print axioms actualSteps_inter
#print axioms actualTrace_inter
#print axioms actualTrace_nonempty
#print axioms actualTrace_physical_principal
#print axioms actual_pair_trace_principal
#print axioms actual_pair_trace_joinClosed
#print axioms actual_nonprivate_nat_trace_union
#print axioms actual_retained_nat_trace_union
#print axioms actual_trace_principal_pure
#print axioms actual_cell_subset_of_step
#print axioms actual_retained_cells_exact
#print axioms anchor_points
#print axioms actual_retained_anchor_capacity
#print axioms removed_original_private_point
#print axioms actual_simultaneous_private_peeling
#print axioms actual_anchor_isAP
#print axioms actual_anchor_capacity_with_coordinates
#print axioms actual_unit_anchor_capacity
#print axioms actual_anchor_capacity
#print axioms actual_fixed_AP_anchor_capacity
#print axioms actual_fixed_AP_anchor_ground_capacity
#print axioms actual_AP_anchor_representation
#print axioms actual_arbitrary_AP_anchor_capacity
#print axioms actual_arbitrary_AP_anchor_ground_capacity
#print axioms actual_avoiding_AP_anchor_capacity
#print axioms actual_kernel_capacity
#print axioms actual_avoiding_kernel_capacity
#print axioms general_crooked_avoiders_payment
end
end JSP233.AnchorGeometry38
