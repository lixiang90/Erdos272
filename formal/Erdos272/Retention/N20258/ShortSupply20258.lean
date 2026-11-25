module

public import Erdos272.Arithmetic.N20258.ShortSupplyProfile20258
public import Erdos272.Retention.N65968.CoreSupplyBounds65968

@[expose] public section

/-! Only the physical root of the retained family enters the endpoint
matching. Steps larger than `L-c` miss the exterior rectangle and need
neither of the two totient supplies. -/
namespace JSP233.ShortSupply20258

open ShortSupplyProfile20258
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure AtRoot (N c L R : ℕ) : Prop where
  wide : 2*L ≤ R+c
  long : ∀ d u : ℕ, 0 < d → d ≤ L-c → (R-c)/d < u → u ≤ N/d →
    ((L-c)/d+1)+(c-1)/d+1 ≤ Nat.totient u
  «prefix» : ∀ d h m : ℕ, 0 < d → d ≤ L-c → R < c+m*d → c+m*d ≤ N →
    R+c < 2*(c+h*d) → ∃ j, L ≤ c+j*d ∧ j ≤ h ∧ Nat.Coprime j m

theorem AtRoot.cutoff {N c L R d : ℕ} (h : AtRoot N c L R) (hc : c < L)
    (hd : 0 < d) (hs : d ≤ L-c) : 2 ≤ (R-c)/d :=
  (Nat.le_div_iff_mul_le hd).mpr (by have := h.wide; omega)

theorem of_core {N c L R : ℕ} (hc : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (h : ActualSupply65968.Core N L R) : AtRoot N c L R where
  wide := ActualSupply65968.wide hLR hRN h
  long d u hd hs := h.long c d u hc hLR hRN hd (by omega)
  «prefix» d h' m hd hs := h.prefix_supply c d h' m hc hLR hRN hd (by omega)

private theorem long_supply {N c L R d u : ℕ} (hN : N < 510510) (hc : c < L)
    (hRN : R ≤ N) (hcR : c ≤ R) (hd : 0 < d) (hs : d ≤ L-c)
    (g : Gates N c L (N-R)) (hu : (R-c)/d < u) (huN : u ≤ N/d) :
    ((L-c)/d+1)+(c-1)/d+1 ≤ Nat.totient u := by
  let f := ((L-c)/d+1)+(c-1)/d+1
  change f ≤ _
  have hdiff := Nat.sub_add_cancel hRN
  have hroot := Nat.sub_add_cancel hcR
  have hshort : d+c ≤ L := by omega
  have hdf : d*f ≤ L+2*d := by
    have h₁ := Nat.mul_div_le (L-c) d
    have h₂ := Nat.mul_div_le (c-1) d
    have h₃ : (L-c)+(c-1) ≤ L := by omega
    dsimp only [f]
    nlinarith only [h₁,h₂,h₃]
  have hdu := (Nat.div_lt_iff_lt_mul hd).mp hu
  have huNd := (Nat.le_div_iff_mul_le hd).mp huN
  by_contra h
  have hphi := Nat.mul_le_mul_left d (show Nat.totient u+1 ≤ f by omega)
  by_cases h210 : 210*d ≤ N
  · have hratio := Nat.mul_le_mul_left d (CoreSupplyFinite3043.totient_ratio hN
      (huN.trans (Nat.div_le_self N d)))
    nlinarith only [hdf,hphi,hratio,hdu,hroot,hdiff,g.longLow,h210]
  by_cases h30 : 30*d ≤ N
  · have hu210 : u < 210 := by nlinarith only [huNd,h210,hd]
    have hratio := Nat.mul_le_mul_left d (CoreSupply142758.small_totient_ratio hu210)
    nlinarith only [hdf,hphi,hratio,hdu,hroot,hdiff,g.longMid,h30]
  · have hu30 : u < 30 := by nlinarith only [huNd,h30,hd]
    have hratio := Nat.mul_le_mul_left d (ActualSupply65968.tiny_totient_ratio hu30)
    nlinarith only [hdf,hphi,hratio,hdu,hroot,hdiff,g.longHigh,hshort]

private theorem prefix_supply {N c L R d h m : ℕ} (hN : N < 510510) (hc : c < L)
    (hRN : R ≤ N) (hd : 0 < d) (hs : d ≤ L-c) (g : Gates N c L (N-R))
    (hmR : R < c+m*d) (hmN : c+m*d ≤ N) (hhalf : R+c < 2*(c+h*d)) :
    ∃ j, L ≤ c+j*d ∧ j ≤ h ∧ Nat.Coprime j m := by
  let a := (L-c)/d+1
  let q := 2*a+(m-2*h)
  have hroot := Nat.sub_add_cancel hc.le
  have hdiff := Nat.sub_add_cancel hRN
  have hshort : d+c ≤ L := by omega
  have hmNd : m*d ≤ N := by omega
  have hmN' : m ≤ N := (Nat.le_mul_of_pos_right m hd).trans hmNd
  have ha : d*a ≤ L-c+d := by
    dsimp only [a]
    nlinarith only [Nat.mul_div_le (L-c) d]
  have hmid : d*(m-2*h) ≤ N-R := by
    by_cases hle : 2*h ≤ m
    · have he := congrArg (fun z => d*z) (Nat.sub_add_cancel hle)
      nlinarith only [he,hdiff,hmN,hhalf]
    · simp only [Nat.sub_eq_zero_of_le (by omega : m ≤ 2*h),Nat.mul_zero,Nat.zero_le]
  have hq : d*q+2*c ≤ 2*L+2*d+(N-R) := by
    dsimp only [q]
    nlinarith only [ha,hmid,hroot]
  have hphi : q < Nat.totient m := by
    by_contra hbad
    have hpd := Nat.mul_le_mul_left d (show Nat.totient m ≤ q by omega)
    by_cases h210 : 210*d ≤ N
    · have hr := Nat.mul_le_mul_left d (CoreSupplyFinite3043.totient_ratio hN hmN')
      nlinarith only [hpd,hr,hq,hmR,hdiff,g.prefixLow,h210]
    by_cases h30 : 30*d ≤ N
    · have hm210 : m < 210 := by nlinarith only [hmNd,h210,hd]
      have hr := Nat.mul_le_mul_left d (CoreSupply142758.small_totient_ratio hm210)
      nlinarith only [hpd,hr,hq,hmR,hdiff,g.prefixMid,h30]
    · have hm30 : m < 30 := by nlinarith only [hmNd,h30,hd]
      have hr := Nat.mul_le_mul_left d (ActualSupply65968.tiny_totient_ratio hm30)
      nlinarith only [hpd,hr,hq,hmR,hdiff,g.prefixHigh,hshort]
  have hm : ∃ j, a ≤ j ∧ j ≤ h ∧ Nat.Coprime j m := by
    by_contra hh
    have hbound := CoprimeMiddle36.totient_le_of_no_coprime_middle
      (m := m) (a := a) (h := h) (fun j hja hjh hcop => hh ⟨j,hja,hjh,hcop⟩)
    exact (Nat.not_le_of_gt hphi) hbound
  obtain ⟨j,haj,hjh,hcop⟩ := hm
  have hj : (L-c)/d < j := haj
  have hjd := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j,by omega,hjh,hcop⟩

theorem of_gates {N c L R : ℕ} (hhi : N < 120120)
    (hc : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (g : Gates N c L (N-R)) : AtRoot N c L R := by
  exact ⟨by have hw := g.wide; omega,
    fun _ _ hd hs => long_supply (by omega) hc hRN (hc.le.trans hLR) hd hs g,
    fun _ _ _ hd hs => prefix_supply (by omega) hc hRN hd hs g⟩

theorem of_profile {N c L R : ℕ} (hN : 11400 ≤ N) (hhi : N < 120120)
    (hc : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hp : profile L (N-R : ℕ) c ≤ price*N+884) : AtRoot N c L R :=
  of_gates hhi hc hLR hRN (ShortSupplyProfile20258.of_profile hN hc.le hp)

end JSP233.ShortSupply20258
