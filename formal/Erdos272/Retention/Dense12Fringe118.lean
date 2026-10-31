import Erdos272.Retention.Relative12Fringe118
import Erdos272.Retention.DenseAligned117
import Erdos272.Counting.PeriodOff117

/-! A second actual trace grid. The same dense11 sources remain on Ground N.
The twelve-denominator ceil grid needs28 aligned classes after the true
modulus exclusion; shared period holes give11 off classes. -/
namespace JSP233.Dense12Fringe118
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def DenseShortKeys (r : ℕ) : Finset (Σ _d:ℕ,ℕ) :=
  (Finset.Icc 1 (r-1)).sigma (fun d=>Finset.Icc 1 (11/d))

theorem dense_short_keys_card11 : (DenseShortKeys 11).card=28 := by
  norm_num [DenseShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem dense_short_keys_card9 : (DenseShortKeys 9).card=26 := by
  norm_num [DenseShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem actual_aligned_count {N M r : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Relative12Fringe118.Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (hkeys : ∀S∈E,K S∈Relative12Fringe118.Keys)
    (hanchor : ∀S∈E,Relative12Fringe118.HasAnchor M L R (K S) S) :
    (E.filter (Relative12Fringe118.Aligned K M L)).card≤
      (DenseShortKeys r).card*(Ground N\Finset.Icc L R).card := by
  let A := E.filter (Relative12Fringe118.Aligned K M L)
  have hex := Relative12Fringe118.actual_aligned_private K hlegal hbad hanchor
  choose Y hY using hex
  have hshort : ∀S∈A,(⟨(K S).1,(K S).2.2⟩:Σ _d:ℕ,ℕ)∈DenseShortKeys r := by
    intro S hS
    have hSE : S∈E := (Finset.mem_filter.mp hS).1
    obtain ⟨hd,hrj⟩ := Finset.mem_sigma.mp (hkeys S hSE)
    have hdpos : 0<(K S).1 := by have hh := (Finset.mem_Icc.mp hd).1;omega
    have hstep : (K S).1<r := DenseAligned117.actual_dense_crooked_modulus_lt hdpos
      (hlegal.1 S hSE) (hbad S hSE) (hdense S hSE)
      ((Finset.mem_filter.mp hS).2)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr
      ⟨by change 1≤(K S).1;omega,by change (K S).1≤r-1;omega⟩,
      (Finset.mem_product.mp hrj).2⟩
  have hc : A.card≤((DenseShortKeys r).product (Ground N\Finset.Icc L R)).card := by
    apply Finset.card_le_card_of_injective (f:=fun S:A=>
      (⟨(⟨(K S.val).1,(K S.val).2.2⟩,Y S.val S.property),Finset.mem_product.mpr
        ⟨hshort S.val S.property,Finset.mem_sdiff.mpr
          ⟨hlegal.1 S.val (Finset.mem_filter.mp S.property).1 (hY S.val S.property).1,
            (hY S.val S.property).2.1⟩⟩⟩ : ↥((DenseShortKeys r).product (Ground N\Finset.Icc L R))))
    intro S T he
    apply Subtype.ext
    by_contra hne
    have hcode := congrArg Subtype.val he
    have hd : (K S.val).1=(K T.val).1 := congrArg (fun z:(Σ _d:ℕ,ℕ)×ℤ=>z.1.1) hcode
    have hj : (K S.val).2.2=(K T.val).2.2 := congrArg (fun z:(Σ _d:ℕ,ℕ)×ℤ=>z.1.2) hcode
    have hy : Y S.val S.property=Y T.val T.property := congrArg Prod.snd hcode
    obtain ⟨hds,hrjs⟩ := Finset.mem_sigma.mp (hkeys S.val (Finset.mem_filter.mp S.property).1)
    obtain ⟨hdt,hrjt⟩ := Finset.mem_sigma.mp (hkeys T.val (Finset.mem_filter.mp T.property).1)
    have hrs := Finset.mem_Icc.mp (Finset.mem_product.mp hrjs).1
    have hrt := Finset.mem_Icc.mp (Finset.mem_product.mp hrjt).1
    have hAS : Relative12Fringe118.Aligned K M L S.val := (Finset.mem_filter.mp S.property).2
    have hAT : Relative12Fringe118.Aligned K M L T.val := (Finset.mem_filter.mp T.property).2
    have hresS := Relative12Fringe118.residue_dvd (hAS _ (hY S.val S.property).1)
    have hresT := Relative12Fringe118.residue_dvd (hAT _ (hY T.val T.property).1)
    rw [←hy,←hd] at hresT
    have hrt' : 1≤(K T.val).2.1 ∧ (K T.val).2.1≤(K S.val).1 := by omega
    have hrho := JointFringe44.bounded_residue_eq
      (by have hh := (Finset.mem_Icc.mp hds).1;omega) hrs hrt' hresS hresT
    have hkEq : K S.val=K T.val := Sigma.ext hd (heq_of_eq (Prod.ext hrho hj))
    have hyT : Y S.val S.property∈T.val := by rw [hy];exact (hY T.val T.property).1
    exact (hY S.val S.property).2.2 T.val T.property hkEq.symm (Ne.symm hne) hyT
  exact hc.trans_eq (Finset.card_product (DenseShortKeys r) (Ground N\Finset.Icc L R))

theorem actual_long_trace_fringe_bound {N L R r : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (_hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/12+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤((DenseShortKeys r).card+11)*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  let M := R-L+1
  have hI : 12^3≤(Finset.Icc (L:ℤ) (R:ℤ)).card := by
    rw [Relative12Fringe118.interval_card hLR]
    norm_num at *
    omega
  have hpair : ∀S∈E,IsAP (S∩H) := by
    intro S hS
    exact hlegal.2 S (hEF hS) H hHF (by intro hh;exact hbad S hS (hh ▸ hHAP))
  have hcover : ∀S∈E,∃k∈Relative12Fringe118.Keys,
      Relative12Fringe118.HasAnchor M (L:ℤ) (R:ℤ) k S := by
    intro S hS
    exact Relative12Fringe118.actual_trace_anchor hL hLR (by omega)
      (hpair S hS) hKH (hm S hS)
  let K : Finset ℤ→Relative12Fringe118.Key :=
    fun S=>if h:S∈E then Classical.choose (hcover S h) else ⟨1,1,1⟩
  have hK : ∀S∈E,K S∈Relative12Fringe118.Keys ∧
      Relative12Fringe118.HasAnchor M (L:ℤ) (R:ℤ) (K S) S := by
    intro S hS
    simpa only [K,dif_pos hS] using Classical.choose_spec (hcover S hS)
  have hELegal : Legal (Ground N) E := ⟨fun S hS=>hlegal.1 S (hEF hS),
    fun S hS T hT hn=>hlegal.2 S (hEF hS) T (hEF hT) hn⟩
  let d : Finset ℤ→ℤ := fun S=>(K S).1
  let a : Finset ℤ→ℤ := fun S=>Relative12Fringe118.Origin M (L:ℤ) (K S)
  have hlong : ∀S∈E,(Finset.Icc (L:ℤ) (R:ℤ)).card<
      12*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card := by
    intro S hS
    have hh := Nat.lt_mul_div_succ M (by decide : 0<12)
    have hhm := hm S hS
    rw [Relative12Fringe118.interval_card hLR]
    change M<12*(S∩Finset.Icc (L:ℤ) (R:ℤ)).card
    omega
  have hsteps : ∀S∈E,d S≤11 := by
    intro S hS
    have hh := Finset.mem_Icc.mp (Finset.mem_sigma.mp (hK S hS).1).1
    dsimp only [d]
    exact_mod_cast hh.2
  have ho := PeriodOff117.actual_off_residue_count_pred (p:=12) (D:=27720) (h:=54) d a
    hLR (by decide) (by decide) (by decide) (by omega : 27720*54≤R-L+1) hELegal
    (fun S hS=>(hK S hS).2.1) (by
      intro S hS
      have hpos := (hK S hS).2.1.1
      change 0<d S at hpos
      have hstep := hsteps S hS
      have hd : ∀e:ℤ,1≤e→e≤11→e∣27720 := by
        intro e he heu
        interval_cases e <;> norm_num
      exact hd (d S) (by omega) hstep) hm
  have ha := actual_aligned_count K hELegal hbad hdense
    (fun S hS=>(hK S hS).1) (fun S hS=>(hK S hS).2)
  have he : E.filter (fun S=>¬Relative12Fringe118.Aligned K M (L:ℤ) S)=
      OffResidue44.OffMembers E d a := by
    ext S
    simp [Relative12Fringe118.Aligned,OffResidue44.OffMembers,d,a]
  have hc := Finset.card_filter_add_card_filter_not (s:=E) (Relative12Fringe118.Aligned K M (L:ℤ))
  rw [he] at hc
  nlinarith only [ha,ho,hc]


theorem actual_long_trace_fringe_bound39 {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hdense : ∀S∈E,N<11*S.card)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hm : ∀S∈E,(R-L+1)/12+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    E.card≤39*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have h := actual_long_trace_fringe_bound hL hLR hRN hM hlegal hEF hbad hdense hcore hm
  simpa only [dense_short_keys_card11,Nat.reduceAdd,Nat.reduceSub] using h

#print axioms dense_short_keys_card11
#print axioms dense_short_keys_card9
#print axioms actual_aligned_count
#print axioms actual_long_trace_fringe_bound
#print axioms actual_long_trace_fringe_bound39
end
end JSP233.Dense12Fringe118
