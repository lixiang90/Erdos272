module

public import Erdos272.Retention.Relative13Fringe116
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Dense actual crooked members cannot be globally aligned at step11 or
larger.  The full original ground set, not merely the core interval, is used
in this exclusion.  It removes two genuine linear key classes from the p13
aligned private-point count. -/
namespace JSP233.DenseAligned117
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_dense_crooked_modulus_lt {N d r : ℕ} {S : Finset ℤ} {o : ℤ}
    (hd : 0<d) (hS : S⊆Ground N) (hbad : ¬IsAP S)
    (hdense : N<r*S.card) (halign : ∀y∈S,(d:ℤ)∣y-o) : d<r := by
  by_contra hn
  have hdr : r≤d := by omega
  have hcardpos : 0<S.card := by
    by_contra hn
    have hz : S.card=0 := by omega
    rw [hz,mul_zero] at hdense
    omega
  have hne : S.Nonempty := Finset.card_pos.mp hcardpos
  obtain ⟨p,hp⟩ := hne
  let C := (Ground N).filter (fun y=>(d:ℤ)∣y-o)
  have hSC : S⊆C := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨hS hy,halign y hy⟩
  have hpC : p∈C := hSC hp
  have hCAP : APAt (d:ℤ) o C := by
    refine ⟨by exact_mod_cast hd,1,N,?_⟩
    intro y
    simp only [C,Finset.mem_filter,mem_ground]
    tauto
  have hCisAP : IsAP C :=
    (isAP_iff_exists_APAt C).mpr ⟨d,p,apAt_rebase hCAP hpC,hpC⟩
  have hstrict : S⊂C := Finset.ssubset_iff_subset_ne.mpr ⟨hSC,by
    intro he
    exact hbad (he ▸ hCisAP)⟩
  have hcard := Finset.card_lt_card hstrict
  have hCne : C.Nonempty := ⟨p,hpC⟩
  have hspan := apAt_span_eq hCAP hCne
  have hlo := (mem_ground N _).mp
    ((Finset.mem_filter.mp (Finset.min'_mem C hCne)).1)
  have hhi := (mem_ground N _).mp
    ((Finset.mem_filter.mp (Finset.max'_mem C hCne)).1)
  have hcardZ : (S.card:ℤ)≤(C.card:ℤ)-1 := by omega
  have hm := mul_le_mul_of_nonneg_left hcardZ
    (show (0:ℤ)≤d by exact_mod_cast hd.le)
  have hdenseZ : (N:ℤ)<r*(S.card:ℤ) := by exact_mod_cast hdense
  have hdrZ : (r:ℤ)≤d := by exact_mod_cast hdr
  have hmul := mul_le_mul_of_nonneg_right hdrZ
    (show (0:ℤ)≤S.card by positivity)
  nlinarith only [hspan,hlo.1,hhi.2,hm,hdenseZ,hmul]

theorem actual_dense_crooked_modulus_le10 {N d : ℕ} {S : Finset ℤ} {o : ℤ}
    (hd : 0<d) (hS : S⊆Ground N) (hbad : ¬IsAP S)
    (hdense : N<11*S.card) (halign : ∀y∈S,(d:ℤ)∣y-o) : d≤10 := by
  have h := actual_dense_crooked_modulus_lt hd hS hbad hdense halign
  omega

def DenseShortKeys (r : ℕ) : Finset (Σ _d:ℕ,ℕ) :=
  (Finset.Icc 1 (r-1)).sigma (fun d=>Finset.Icc 1 (12/d))

theorem dense_short_keys_card11 : (DenseShortKeys 11).card=33 := by
  norm_num [DenseShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem dense_short_keys_card9 : (DenseShortKeys 9).card=31 := by
  norm_num [DenseShortKeys,Finset.card_sigma,Finset.sum_Icc_succ_top]

theorem actual_aligned_count {N M r : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Relative13Fringe116.Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (hkeys : ∀S∈E,K S∈Relative13Fringe116.Keys)
    (hanchor : ∀S∈E,Relative13Fringe116.HasAnchor M L R (K S) S) :
    (E.filter (Relative13Fringe116.Aligned K M L)).card≤
      (DenseShortKeys r).card*(Ground N\Finset.Icc L R).card := by
  let A := E.filter (Relative13Fringe116.Aligned K M L)
  have hex := Relative13Fringe116.actual_aligned_private K hlegal hbad hanchor
  choose Y hY using hex
  have hshort : ∀S∈A,(⟨(K S).1,(K S).2.2⟩:Σ _d:ℕ,ℕ)∈DenseShortKeys r := by
    intro S hS
    have hSE : S∈E := (Finset.mem_filter.mp hS).1
    obtain ⟨hd,hrj⟩ := Finset.mem_sigma.mp (hkeys S hSE)
    have hdpos : 0<(K S).1 := by have hh := (Finset.mem_Icc.mp hd).1;omega
    have hstep : (K S).1<r := actual_dense_crooked_modulus_lt hdpos
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
    have hAS : Relative13Fringe116.Aligned K M L S.val := (Finset.mem_filter.mp S.property).2
    have hAT : Relative13Fringe116.Aligned K M L T.val := (Finset.mem_filter.mp T.property).2
    have hresS := Relative13Fringe116.residue_dvd (hAS _ (hY S.val S.property).1)
    have hresT := Relative13Fringe116.residue_dvd (hAT _ (hY T.val T.property).1)
    rw [←hy,←hd] at hresT
    have hrt' : 1≤(K T.val).2.1 ∧ (K T.val).2.1≤(K S.val).1 := by omega
    have hrho := JointFringe44.bounded_residue_eq
      (by have hh := (Finset.mem_Icc.mp hds).1;omega) hrs hrt' hresS hresT
    have hkEq : K S.val=K T.val := Sigma.ext hd (heq_of_eq (Prod.ext hrho hj))
    have hyT : Y S.val S.property∈T.val := by rw [hy];exact (hY T.val T.property).1
    exact (hY S.val S.property).2.2 T.val T.property hkEq.symm (Ne.symm hne) hyT
  exact hc.trans_eq (Finset.card_product (DenseShortKeys r) (Ground N\Finset.Icc L R))

theorem actual_aligned_count33 {N M : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Relative13Fringe116.Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<11*S.card)
    (hkeys : ∀S∈E,K S∈Relative13Fringe116.Keys)
    (hanchor : ∀S∈E,Relative13Fringe116.HasAnchor M L R (K S) S) :
    (E.filter (Relative13Fringe116.Aligned K M L)).card≤
      33*(Ground N\Finset.Icc L R).card := by
  simpa only [dense_short_keys_card11] using actual_aligned_count K hlegal hbad hdense hkeys hanchor

theorem actual_aligned_count31 {N M : ℕ} {E : Finset (Finset ℤ)} {L R : ℤ}
    (K : Finset ℤ→Relative13Fringe116.Key) (hlegal : Legal (Ground N) E)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<9*S.card)
    (hkeys : ∀S∈E,K S∈Relative13Fringe116.Keys)
    (hanchor : ∀S∈E,Relative13Fringe116.HasAnchor M L R (K S) S) :
    (E.filter (Relative13Fringe116.Aligned K M L)).card≤
      31*(Ground N\Finset.Icc L R).card := by
  simpa only [dense_short_keys_card9] using actual_aligned_count K hlegal hbad hdense hkeys hanchor

#print axioms actual_dense_crooked_modulus_lt
#print axioms actual_dense_crooked_modulus_le10
#print axioms dense_short_keys_card11
#print axioms dense_short_keys_card9
#print axioms actual_aligned_count
#print axioms actual_aligned_count33
#print axioms actual_aligned_count31
end
end JSP233.DenseAligned117
