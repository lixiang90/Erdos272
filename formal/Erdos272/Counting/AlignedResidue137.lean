module

public import Erdos272.Geometry.ResidueInterval137
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.AlignedResidue137
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open Relative13Fringe116 DenseAligned117 DensePhase137 ResidueInterval137
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def ResiduePool (r:ℕ) (O:Finset ℤ) (phase:ℕ→ℤ) : Finset (Σ (_k:Σ _d:ℕ,ℕ),ℤ) :=
  (DenseShortKeys r).sigma (fun k=>O.filter (fun y=>(k.1:ℤ)∣y-phase k.1))

theorem residue_pool_card (r:ℕ) (O:Finset ℤ) (phase:ℕ→ℤ) :
    (ResiduePool r O phase).card=
      ∑d∈Finset.Icc 1 (r-1),(12/d)*(O.filter (fun y=>(d:ℤ)∣y-phase d)).card := by
  rw [ResiduePool,Finset.card_sigma,DenseShortKeys,Finset.sum_sigma]
  simp [Finset.sum_const,Nat.card_Icc]

theorem actual_aligned_count_residue {N M r:ℕ} {E:Finset (Finset ℤ)} {L R:ℤ}
    (K:Finset ℤ→Key) (hlegal:Legal (Ground N) E)
    (hbad:∀S∈E,¬IsAP S) (hdense:∀S∈E,N<r*S.card)
    (hkeys:∀S∈E,K S∈Keys) (hanchor:∀S∈E,Relative13Fringe116.HasAnchor M L R (K S) S) :
    ∃phase:ℕ→ℤ,(E.filter (Aligned K M L)).card≤
      ∑d∈Finset.Icc 1 (r-1),(12/d)*(ResidueOutside N L R d (phase d)).card := by
  let A:=E.filter (Aligned K M L)
  have hphases (d:ℕ):∃o:ℤ,∀S∈StepClass E K M L d,∀y∈S,(d:ℤ)∣y-o:=
    actual_step_class_common_residue hlegal
  choose phase hphase using hphases
  have hex:=Relative13Fringe116.actual_aligned_private K hlegal hbad hanchor
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
  have hc:A.card≤(ResiduePool r (Ground N\Finset.Icc L R) phase).card:=by
    apply Finset.card_le_card_of_injective (f:=fun S:A=>
      (⟨⟨(⟨(K S.val).1,(K S.val).2.2⟩:Σ _d:ℕ,ℕ),Y S.val S.property⟩,
        Finset.mem_sigma.mpr ⟨hshort S.val S.property,Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr
            ⟨hlegal.1 S.val (Finset.mem_filter.mp S.property).1 (hY S.val S.property).1,
              (hY S.val S.property).2.1⟩,
            hphase (K S.val).1 S.val (Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp S.property).1,(Finset.mem_filter.mp S.property).2,rfl⟩)
              (Y S.val S.property) (hY S.val S.property).1⟩⟩⟩:
        ↥(ResiduePool r (Ground N\Finset.Icc L R) phase)))
    intro S T he
    apply Subtype.ext
    by_contra hne
    have hcode := congrArg Subtype.val he
    have hd : (K S.val).1=(K T.val).1 := congrArg (fun z:Σ (_k:Σ _d:ℕ,ℕ),ℤ=>z.1.1) hcode
    have hj : (K S.val).2.2=(K T.val).2.2 := congrArg (fun z:Σ (_k:Σ _d:ℕ,ℕ),ℤ=>z.1.2) hcode
    have hy : Y S.val S.property=Y T.val T.property := congrArg (fun z:Σ (_k:Σ _d:ℕ,ℕ),ℤ=>z.2) hcode
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
  refine ⟨phase,?_⟩
  simpa only [A,ResidueOutside] using hc.trans_eq (residue_pool_card r (Ground N\Finset.Icc L R) phase)

#print axioms residue_pool_card
#print axioms actual_aligned_count_residue
end
end JSP233.AlignedResidue137
