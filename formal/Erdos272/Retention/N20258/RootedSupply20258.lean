module

public import Erdos272.Counting.N20258.RootedExterior20258
public import Erdos272.Arithmetic.N20258.ShortSupplyProfile20258
public import Erdos272.Arithmetic.N20258.DyadicWidth20258
public import Erdos272.Counting.N67702.ReaddedProfile67702

@[expose] public section
namespace JSP233.RootedSupply20258
open StarCompletion APGeometry APCount41 APPrepare49 PreparedClasses50
open HarmonicAbel29 LocalRecovery208 CovarianceFamily214 RootModel291012
open scoped Classical
noncomputable section
set_option autoImplicit false

theorem actual_gates {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (g : Start N c L R F P T)
    (left : 6*L < N) (count : (Omitted N c F).card+1 ≤ L+(N-R))
    (unit : ∀ S ∈ F, IsAP S → (c : ℤ) ∉ S → Step S=1) :
    ShortSupplyProfile20258.Gates N c L (N-R) := by
  let G := GenericRecovery291012.Readded N 12 F (c : ℤ)
  have sub : G ⊆ F := Finset.sdiff_subset
  have legal : Legal (Ground N) G :=
    ⟨fun S hS => g.legal.1 S (sub hS),fun S hS T hT => g.legal.2 S (sub hS) T (sub hT)⟩
  have small := ActualPreparation208.actual_small_AP_cut_count (by omega : 19 ≤ N) legal
  have smallR : ((SmallAP G).card : ℝ) ≤ 2*N+0 := by
    exact_mod_cast (show (SmallAP G).card ≤ 2*N+0 by omega)
  have ex := RootedExterior20258.actual (L := L) g.right_ground legal (fun S hS => unit S (sub hS))
  let b : ℝ := (N : ℝ)-R
  let adj := (129/200 : ℝ)*((c : ℝ)-L)*b
  have cL : (c : ℝ) ≤ L := by exact_mod_cast g.root_left.le
  have adjBound : ((EX (PreparedAP G c L) R).card : ℝ) ≤
      (129/200 : ℝ)*L*((N : ℝ)-R)+Width N L R*Harmonic N+N-
      0*N-0*Width N L R+adj := by
    dsimp only [Width,adj,b]
    have harm := mul_le_mul_of_nonneg_right cL (harmonic_nonneg N)
    linarith only [ex,harm]
  have raw := RawProfile67702.actual_raw_with_bounds g (by omega : 19 ≤ N)
    (by omega : N ≤ 720896) smallR adjBound
  have rn : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  have hn : Harmonic N ≤ 12 :=
    (HarmonicSharp39.actual_harmonic_tight N 16 hi).trans (by norm_num)
  have nterm := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) N)
  have wterm := mul_le_mul_of_nonneg_left hn
    (add_nonneg (Nat.cast_nonneg (α := ℝ) L) (sub_nonneg.mpr rn))
  have cl := g.root_left
  have lterm := mul_le_mul_of_nonneg_left
    (DyadicWidth20258.coefficient_fringe (by omega : 1 ≤ L) (by omega : L < 2^14))
    (Nat.cast_nonneg (α := ℝ) L)
  have e : ((Omitted N c F).card : ℝ)+1 ≤ L+((N : ℝ)-R) := by
    have h : ((Omitted N c F).card : ℝ)+1 ≤ (L : ℝ)+(N-R : ℕ) := by exact_mod_cast count
    simpa only [Nat.cast_sub g.right_ground] using h
  apply ShortSupplyProfile20258.of_rooted_exterior lo cl.le
  rw [Nat.cast_sub g.right_ground]
  dsimp only [ShortSupplyProfile20258.alpha,ShortSupplyProfile20258.kappa]
  dsimp only [Recovery208.WidthProfile,MiddleCost,CovarianceScalar213.Polynomial,
    GeometryCost,Width,adj,b] at raw
  unfold DyadicWidth20258.coefficient at lterm
  linarith only [raw,nterm,wterm,lterm,e,rn,Nat.cast_nonneg (α := ℝ) N,
    Nat.cast_nonneg (α := ℝ) L,Nat.cast_nonneg (α := ℝ) c]

#print axioms actual_gates
end
end JSP233.RootedSupply20258
