module

public import Erdos272.Capacity.LowSteps32
public import Erdos272.Arithmetic.HarmonicSharp39

@[expose] public section
namespace JSP233.RootHeight20258
open StarCompletion StarResources30 CrossLine30 AffineLine30 LowSteps32
open StaircaseGeometry StaircaseTailBridge29 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The increments of the harmonic sum decrease through the slope (1/k). -/
theorem harmonic_tangent (n k : ℕ) (hk : 0 < k) :
    Harmonic n ≤ Harmonic (k-1)+((n : ℝ)-((k-1 : ℕ) : ℝ))/k := by
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : k-1 ≤ n
  · induction n,h using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have step : (1 : ℝ)/((n : ℝ)+1) ≤ 1/k := by
        apply one_div_le_one_div_of_le kp
        exact_mod_cast (show k ≤ n+1 by omega)
      rw [QuantitativeTail31.harmonic_succ]
      push_cast
      rw [show ((n : ℝ)+1-((k-1 : ℕ) : ℝ))/k = ((n : ℝ)-((k-1 : ℕ) : ℝ))/k+1/k by ring]
      linarith only [ih,step]
  · have up (j : ℕ) (nj : n ≤ j) (jk : j ≤ k-1) :
        Harmonic n+((j : ℝ)-n)/k ≤ Harmonic j := by
      induction j,nj using Nat.le_induction with
      | base => simp
      | succ j nj ih =>
        have prev := ih (by omega)
        have step : (1 : ℝ)/k ≤ 1/((j : ℝ)+1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (show j+1 ≤ k by omega)
        rw [QuantitativeTail31.harmonic_succ]
        push_cast
        rw [show ((j : ℝ)+1-n)/k = ((j : ℝ)-n)/k+1/k by ring]
        linarith only [prev,step]
    have top := up (k-1) (by omega) le_rfl
    rw [show ((n : ℝ)-((k-1 : ℕ) : ℝ))/k = -((((k-1 : ℕ) : ℝ)-n)/k) by ring]
    linarith only [top]

private theorem harmonic_1024 (n : ℕ) :
    Harmonic n ≤ 167193/25600+(n : ℝ)/1024 := by
  have base := HarmonicSharp39.actual_harmonic_tight 1023 10 (by decide)
  have t := harmonic_tangent n 1024 (by decide)
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at t base
  linarith only [t,base]

theorem harmonic_sixty : Harmonic 60 ≤ 7493/1600 := by
  have base := HarmonicSharp39.actual_harmonic_tight 63 6 (by decide)
  have t := harmonic_tangent 60 64 (by decide)
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at t base
  linarith only [t,base]

def quadratic : ℝ := 103356163/79176704
def linear : ℝ := 3482184585/79176704
def constant : ℝ := 479295387641/3167068160

/-- Twice the number of actual windows can be paid with primitive pairs and
a quadratic function of their maximum left extent. -/
theorem coordinates {C : Finset (ℕ × ℕ)} (valid : ∀ p ∈ C, Valid p)
    (thickL : 2 ≤ Height C) (thickR : 2 ≤ Width C) :
    2*((Family C).card : ℝ) ≤ (PrimitivePool (Family C)).card+
      quadratic*(Height C : ℝ)^2+linear*(Height C : ℝ)+constant := by
  let H : ℝ := Height C
  let W : ℝ := Width C
  have h0 : 0 ≤ H := Nat.cast_nonneg _
  have w0 : 0 ≤ W := Nat.cast_nonneg _
  have rect : ((Family C).card : ℝ) ≤ (H+1)*(W+1) := by
    dsimp only [H,W]
    exact_mod_cast QuantitativeTail31.family_card_le_rectangle C
  have defect := QuantitativeTail31.actual_defect_le_harmonic valid thickL thickR
  unfold rationalQuadraticLoss at defect
  have hw := mul_le_mul_of_nonneg_left (harmonic_1024 (Width C)) h0
  have hh := mul_le_mul_of_nonneg_left (harmonic_1024 (Height C)) h0
  have ww := mul_le_mul_of_nonneg_left (harmonic_1024 (Width C)) w0
  let D : ℝ := 77321/256000
  let G : ℝ := 178429/128000
  let p : ℝ := 680779/51200
  have square := mul_nonneg (show 0 ≤ D by norm_num [D])
    (sq_nonneg (W-(G*H+p)/(2*D)))
  dsimp only [D,G,p,H,W,quadratic,linear,constant] at *
  ring_nf at square defect rect hw hh ww ⊢
  linarith only [defect,rect,hw,hh,ww,square]

/-- Use the actual ground position to bound the left extent of one active
class of progressions of spacing (d). -/
theorem actual_class {N c d : ℕ} {F : Finset (Finset ℤ)} (hc : (c : ℤ) ∈ Ground N)
    (hd : 0 < d) (ground : ∀ S ∈ F, S ⊆ Ground N) (ap : ∀ S ∈ F, IsAP S)
    (root : Rooted F (c : ℤ)) (large : ∀ S ∈ F, 4 ≤ S.card)
    (active : (d : ℤ) ∈ APActiveSteps (c : ℤ) F) :
    let U := StepClass F (trueStep (c : ℤ)) (d : ℤ)
    2*(U.card : ℝ) ≤ (gcdStepPool (c : ℤ) (d : ℤ) U).card+
      quadratic*(((c : ℝ)-1)/d)^2+linear*(((c : ℝ)-1)/d)+constant := by
  have dz : (0 : ℤ) < d := by exact_mod_cast hd
  have dr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C,eq,valid,bounds⟩ :=
    actual_class_coordinates N (c : ℤ) F ground ap root large hc d hd
  have arm (x : ℤ) (hit : ∃ S ∈ StepClass F (trueStep (c : ℤ)) (d : ℤ),
      affine (c : ℤ) (d : ℤ) x ∈ S) : ∃ p ∈ C, x ∈ Window p.1 p.2 := by
    rw [←eq] at hit
    obtain ⟨S,hS,hx⟩ := hit
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact ⟨p,hp,(mem_mapSet _ _ dz _ _).mp hx⟩
  obtain ⟨_,left,right⟩ := Finset.mem_filter.mp active
  obtain ⟨u,hu,xu⟩ := arm (-2) (by simpa [affine,sub_eq_add_neg,mul_comm] using left)
  obtain ⟨v,hv,yv⟩ := arm 2 (by simpa [affine,mul_comm] using right)
  have thickL : 2 ≤ Height C := by
    have e := (mem_window _ _ _).mp xu
    have le : u.1 ≤ Height C := Finset.le_sup (f := Prod.fst) hu
    omega
  have thickR : 2 ≤ Width C := by
    have e := (mem_window _ _ _).mp yv
    have le : v.2 ≤ Width C := Finset.le_sup (f := Prod.snd) hv
    omega
  have cap : Height C ≤ leftCapacity (c : ℤ)/d :=
    Finset.sup_le (fun p hp => (Nat.le_div_iff_mul_le hd).mpr (bounds p hp).1)
  have natBound := (Nat.le_div_iff_mul_le hd).mp cap
  have one : 1 ≤ c := by exact_mod_cast ((mem_ground N _).mp hc).1
  have a : leftCapacity (c : ℤ) = c-1 := by unfold leftCapacity; omega
  rw [a] at natBound
  have height : (Height C : ℝ) ≤ ((c : ℝ)-1)/d := by
    apply (le_div_iff₀ dr).mpr
    have hz : (Height C : ℝ)*d ≤ (c-1 : ℕ) := by exact_mod_cast natBound
    simpa only [Nat.cast_sub one,Nat.cast_one] using hz
  have square := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) (Height C)) height
  have q := mul_le_mul_of_nonneg_left square (show 0 ≤ quadratic by norm_num [quadratic])
  have l := mul_le_mul_of_nonneg_left height (show 0 ≤ linear by norm_num [linear])
  have src := coordinates valid thickL thickR
  dsimp only
  rw [←eq,mapFamily_card _ _ dz,gcdStepPool_mapFamily_card _ _ dz]
  linarith only [src,q,l]

#print axioms actual_class
end
end JSP233.RootHeight20258
