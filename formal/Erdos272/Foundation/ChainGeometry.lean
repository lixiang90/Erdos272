module

public import Erdos272.Foundation.TwoTraceGlobal
public import Erdos272.Foundation.PrimeKernel
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! A genuine private point from divisibility-comparable actual AP steps.
No trace classification, private-point oracle, or capacity is assumed. -/

namespace JSP233.ChainGeometry

open StarCompletion PrivateFinset

def IsPairStep (D : Finset (Finset Int)) (d : Int) : Prop :=
  ∃ S ∈ D, ∃ T ∈ D, S ≠ T ∧ ∃ r,
    PrivateUnion.APAt d r (fun x => x ∈ S ∧ x ∈ T)

def PairStepChain (D : Finset (Finset Int)) : Prop :=
  ∀ d e, IsPairStep D d → IsPairStep D e → d ∣ e ∨ e ∣ d

theorem IsPairStep.mono {D E : Finset (Finset Int)} (hED : E ⊆ D)
    {d : Int} (hd : IsPairStep E d) : IsPairStep D d := by
  rcases hd with ⟨S,hS,T,hT,hne,r,hr⟩
  exact ⟨S,hED hS,T,hED hT,hne,r,hr⟩

theorem PairStepChain.mono {D E : Finset (Finset Int)} (hD : PairStepChain D)
    (hED : E ⊆ D) : PairStepChain E := by
  intro d e hd he
  exact hD d e (hd.mono hED) (he.mono hED)

theorem pair_step_bounds (D : Finset (Finset Int)) (a b d : Int)
    (hab : a < b) (ha : ∀ S ∈ D, a ∈ S) (hb : ∀ S ∈ D, b ∈ S)
    (hd : IsPairStep D d) : 0 < d ∧ d ≤ b-a := by
  rcases hd with ⟨S,hS,T,hT,_,r,hrep⟩
  have hreb := PrivateUnion.APAt_rebase d r a _ hrep ⟨ha S hS,ha T hT⟩
  rcases hreb with ⟨hpos,lo,hi,hiff⟩
  exact ⟨hpos,Int.le_of_dvd (by omega) ((hiff b).mp ⟨hb S hS,hb T hT⟩).2.2⟩

/-- Restricting an actual anchored AP between two of its actual points. -/
theorem restrict_APAt (d a b : Int) (P : Int → Prop)
    (hP : PrivateUnion.APAt d a P) (ha : P a) (hb : P b) :
    PrivateUnion.APAt d a (fun x => P x ∧ x ∈ Finset.Icc a b) := by
  rcases hP with ⟨hd,lo,hi,hr⟩
  have hal := ((hr a).mp ha).1
  have hbh := ((hr b).mp hb).2.1
  refine ⟨hd,a,b,?_⟩
  intro x
  constructor
  · rintro ⟨hx,hI⟩
    have hbounds := Finset.mem_Icc.mp hI
    exact ⟨hbounds.1,hbounds.2,((hr x).mp hx).2.2⟩
  · rintro ⟨hxa,hxb,hdx⟩
    exact ⟨(hr x).mpr ⟨by omega,by omega,hdx⟩,Finset.mem_Icc.mpr ⟨hxa,hxb⟩⟩

/-- All actual pair steps form a finite set: they are positive divisors of
the fixed actual common gap. -/
noncomputable def Steps (D : Finset (Finset Int)) (a b : Int) : Finset Int := by
  classical
  exact (Finset.Icc 1 (b-a)).filter (IsPairStep D)

theorem mem_steps_iff (D : Finset (Finset Int)) (a b d : Int)
    (hab : a < b) (ha : ∀ S ∈ D, a ∈ S) (hb : ∀ S ∈ D, b ∈ S) :
    d ∈ Steps D a b ↔ IsPairStep D d := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hd
    have hbounds := pair_step_bounds D a b d hab ha hb hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hbounds.2⟩,hd⟩

theorem chain_private_exists
    (D : Finset (Finset Int)) (a b : Int)
    (hm : 2 ≤ D.card) (hab : a < b)
    (ha : ∀ S ∈ D, a ∈ S) (hb : ∀ S ∈ D, b ∈ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hchain : PairStepChain D) :
    ∃ S ∈ D, ∃ x ∈ S, ∀ T ∈ D, T ≠ S → x ∉ T := by
  classical
  let Q := Steps D a b
  have hQiff : ∀ q, q ∈ Q ↔ IsPairStep D q :=
    fun q => mem_steps_iff D a b q hab ha hb
  have hQne : Q.Nonempty := by
    rcases Finset.card_pos.mp (show 0 < D.card by omega) with ⟨S,hS⟩
    have he : (D.erase S).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hS]
      omega
    rcases he with ⟨T,hT⟩
    have hTD := (Finset.mem_erase.mp hT).2
    have hne := Ne.symm (Finset.mem_erase.mp hT).1
    rcases PrimeKernel.step_dvd_gap (S ∩ T) a b (hpair S hS T hTD hne)
      (Finset.mem_inter.mpr ⟨ha S hS,ha T hTD⟩)
      (Finset.mem_inter.mpr ⟨hb S hS,hb T hTD⟩) with ⟨q,_,_,hq⟩
    exact ⟨q,(hQiff q).mpr ⟨S,hS,T,hTD,hne,a,by simpa only [Finset.mem_inter] using hq⟩⟩
  let d := Q.min' hQne
  have hdQ : d ∈ Q := Finset.min'_mem Q hQne
  have hdreal := (hQiff d).mp hdQ
  have hdpos := (pair_step_bounds D a b d hab ha hb hdreal).1
  have hdall : ∀ q ∈ Q, d ∣ q := by
    intro q hq
    rcases hchain d q hdreal ((hQiff q).mp hq) with h | h
    · exact h
    · have hqd := Int.le_of_dvd hdpos h
      have hdq := Finset.min'_le Q q hq
      have heq : d = q := by omega
      simp [heq]
  by_cases hout : ∃ S ∈ D, ∃ x ∈ S, ¬ d ∣ x-a
  · rcases hout with ⟨S,hS,x,hx,hnot⟩
    refine ⟨S,hS,x,hx,?_⟩
    intro T hT hne hxT
    rcases PrimeKernel.step_dvd_gap (S ∩ T) a b (hpair S hS T hT (Ne.symm hne))
      (Finset.mem_inter.mpr ⟨ha S hS,ha T hT⟩)
      (Finset.mem_inter.mpr ⟨hb S hS,hb T hT⟩) with ⟨q,_,_,hq⟩
    have hqQ : q ∈ Q := (hQiff q).mpr
      ⟨S,hS,T,hT,Ne.symm hne,a,by simpa only [Finset.mem_inter] using hq⟩
    rcases hq with ⟨_,lo,hi,hr⟩
    exact hnot (dvd_trans (hdall q hqQ)
      ((hr x).mp (Finset.mem_inter.mpr ⟨hx,hxT⟩)).2.2)
  have hres : ∀ S ∈ D, ∀ x ∈ S, d ∣ x-a := by
    intro S hS x hx
    by_contra hn
    exact hout ⟨S,hS,x,hx,hn⟩
  rcases hdreal with ⟨S₀,hS₀,T₀,hT₀,_,r,hdrep⟩
  have hdrep' := PrivateUnion.APAt_rebase d r a _ hdrep ⟨ha S₀ hS₀,ha T₀ hT₀⟩
  have hfill : ∀ x, x ∈ Finset.Icc a b → d ∣ x-a → x ∈ S₀ := by
    intro x hI hdx
    rcases hdrep' with ⟨_,lo,hi,hr⟩
    have hal := ((hr a).mp ⟨ha S₀ hS₀,ha T₀ hT₀⟩).1
    have hbh := ((hr b).mp ⟨hb S₀ hS₀,hb T₀ hT₀⟩).2.1
    have hbounds := Finset.mem_Icc.mp hI
    exact ((hr x).mpr ⟨by omega,by omega,hdx⟩).1
  have htrace : ∀ S ∈ D, ∃ q ∈ Q,
      PrivateUnion.APAt q a (fun x => x ∈ S ∧ x ∈ Finset.Icc a b) := by
    intro S hS
    by_cases he : S = S₀
    · subst S
      refine ⟨d,hdQ,hdpos,a,b,?_⟩
      intro x
      constructor
      · rintro ⟨hx,hI⟩
        have hbounds := Finset.mem_Icc.mp hI
        exact ⟨hbounds.1,hbounds.2,hres S₀ hS₀ x hx⟩
      · rintro ⟨hxa,hxb,hdx⟩
        exact ⟨hfill x (Finset.mem_Icc.mpr ⟨hxa,hxb⟩) hdx,
          Finset.mem_Icc.mpr ⟨hxa,hxb⟩⟩
    · rcases PrimeKernel.step_dvd_gap (S ∩ S₀) a b (hpair S hS S₀ hS₀ he)
        (Finset.mem_inter.mpr ⟨ha S hS,ha S₀ hS₀⟩)
        (Finset.mem_inter.mpr ⟨hb S hS,hb S₀ hS₀⟩) with ⟨q,_,_,hq⟩
      have hqQ : q ∈ Q := (hQiff q).mpr
        ⟨S,hS,S₀,hS₀,he,a,by simpa only [Finset.mem_inter] using hq⟩
      refine ⟨q,hqQ,?_⟩
      have hr := restrict_APAt q a b (fun x => x ∈ S ∩ S₀) hq
        (Finset.mem_inter.mpr ⟨ha S hS,ha S₀ hS₀⟩)
        (Finset.mem_inter.mpr ⟨hb S hS,hb S₀ hS₀⟩)
      apply PrivateUnion.APAt_congr q a _ _ hr
      intro x
      simp only [Finset.mem_inter]
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,
        fun hx => ⟨⟨hx.1,hfill x hx.2 (hres S hS x hx.1)⟩,hx.2⟩⟩
  let R := Q.filter (fun q => ∃ S ∈ D,
    PrivateUnion.APAt q a (fun x => x ∈ S ∧ x ∈ Finset.Icc a b))
  have hRne : R.Nonempty := by
    rcases htrace S₀ hS₀ with ⟨q,hq,htr⟩
    exact ⟨q,Finset.mem_filter.mpr ⟨hq,S₀,hS₀,htr⟩⟩
  let M := R.max' hRne
  have hMR : M ∈ R := Finset.max'_mem R hRne
  have hMQ : M ∈ Q := (Finset.mem_filter.mp hMR).1
  rcases (Finset.mem_filter.mp hMR).2 with ⟨S,hS,hMtrace⟩
  have hMpos := (pair_step_bounds D a b M hab ha hb ((hQiff M).mp hMQ)).1
  have hMle := (pair_step_bounds D a b M hab ha hb ((hQiff M).mp hMQ)).2
  have hMdiv : ∀ T ∈ D, ∃ q,
      PrivateUnion.APAt q a (fun x => x ∈ T ∧ x ∈ Finset.Icc a b) ∧ q ∣ M := by
    intro T hT
    rcases htrace T hT with ⟨q,hq,htr⟩
    refine ⟨q,htr,?_⟩
    have hqR : q ∈ R := Finset.mem_filter.mpr ⟨hq,T,hT,htr⟩
    rcases hchain q M ((hQiff q).mp hq) ((hQiff M).mp hMQ) with h | h
    · exact h
    · have hMq := Int.le_of_dvd (pair_step_bounds D a b q hab ha hb ((hQiff q).mp hq)).1 h
      have hqM := Finset.le_max' R q hqR
      have heq : q = M := by omega
      simp [heq]
  have hnext : ∀ T ∈ D, a+M ∈ T := by
    intro T hT
    rcases hMdiv T hT with ⟨q,⟨_,lo,hi,hr⟩,hqM⟩
    have hal := ((hr a).mp ⟨ha T hT,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩).1
    have hbh := ((hr b).mp ⟨hb T hT,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩).2.1
    exact ((hr (a+M)).mpr ⟨by omega,by omega,by simpa using hqM⟩).1
  have hsame : ∀ T ∈ D, S ≠ T →
      PrivateUnion.APAt M a (fun x => x ∈ S ∧ x ∈ T) := by
    intro T hT hne
    apply PrivateUnion.IsAP_same_step_of_adjacent M a (fun x => x ∈ S)
      (fun x => x ∈ S ∧ x ∈ T) hMpos
      (by simpa only [Finset.mem_inter] using (isAP_iff_predicate _).mp (hpair S hS T hT hne))
      ⟨ha S hS,ha T hT⟩ ⟨hnext S hS,hnext T hT⟩ (fun _ hx => hx.1)
    intro x hax hxm hx
    rcases hMtrace with ⟨_,lo,hi,hr⟩
    have hdx := ((hr x).mp ⟨hx,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩).2.2
    have hle := Int.le_of_dvd (show 0 < x-a by omega) hdx
    omega
  rcases TwoTraceGlobal.private_exterior_finset D S (Finset.Icc a b) M a
    (ha S hS) (Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩) ha (hcrooked S hS)
    hMtrace hsame with ⟨x,hx,_,hpriv⟩
  exact ⟨S,hS,x,hx,fun T hT hne => hpriv T hT (Ne.symm hne)⟩

#print axioms IsPairStep.mono
#print axioms PairStepChain.mono
#print axioms pair_step_bounds
#print axioms restrict_APAt
#print axioms mem_steps_iff
#print axioms chain_private_exists

end JSP233.ChainGeometry
