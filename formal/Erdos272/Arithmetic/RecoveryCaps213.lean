module

public import Erdos272.Arithmetic.RecoveryLocalization212
public import Erdos272.Resources.AlignedPlans212
public import Erdos272.Resources.RecoveryOmitters212

@[expose] public section
namespace JSP233.RecoveryCaps213
open HarmonicAbel29 PrefixState131 PrefixCert131 PrefixTable131 AlignedPlans212
open RecoveryOmitters212 (PreparationP)
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem state_810 : Valid grid 810 ⟨66970339325,66970344729,306451504279,306451505088,1260017481440,1260017574790,3354870062351,5558⟩ := by
  exact chunk_sound [⟨8,13504390,13504391,367359180⟩,⟨8,13486178,13486179,367111550⟩,⟨2,13468015,13468016,366864420⟩,⟨16,13449901,13449902,366617788⟩,⟨4,13431835,13431836,366371653⟩,⟨4,13413818,13413819,366126013⟩,⟨6,13395849,13395850,365880867⟩,⟨12,13377928,13377929,365636213⟩,⟨4,13360055,13360056,365392048⟩,⟨16,13342230,13342231,365148372⟩,⟨2,13324452,13324453,364905183⟩,⟨10,13306721,13306722,364662479⟩,⟨4,13289038,13289039,364420259⟩,⟨8,13271402,13271403,364178521⟩,⟨4,13253812,13253813,363937263⟩,⟨24,13236269,13236270,363696484⟩,⟨2,13218772,13218773,363456183⟩,⟨4,13201322,13201323,363216357⟩,⟨8,13183917,13183918,362977005⟩,⟨16,13166558,13166559,362738126⟩,⟨2,13149245,13149246,362499717⟩,⟨8,13131978,13131979,362261779⟩,⟨4,13114755,13114756,362024308⟩,⟨6,13097578,13097579,361787303⟩,⟨12,13080446,13080447,361550764⟩,⟨4,13063359,13063360,361314687⟩,⟨4,13046316,13046317,361079073⟩,⟨18,13029317,13029318,360843919⟩,⟨2,13012363,13012364,360609223⟩,⟨16,12995453,12995454,360374986⟩,⟨4,12978587,12978588,360141204⟩,⟨6,12961764,12961765,359907876⟩,⟨2,12944985,12944986,359675001⟩,⟨12,12928250,12928251,359442578⟩,⟨6,12911557,12911558,359210605⟩,⟨8,12894908,12894909,358979080⟩,⟨8,12878301,12878302,358748002⟩,⟨4,12861738,12861739,358517370⟩,⟨4,12845216,12845217,358287182⟩,⟨24,12828738,12828739,358057438⟩,⟨4,12812301,12812302,357828134⟩,⟨8,12795907,12795908,357599270⟩,⟨8,12779554,12779555,357370845⟩,⟨15,12763243,12763244,357142858⟩,⟨4,12746974,12746975,356915306⟩,⟨8,12730746,12730747,356688188⟩,⟨2,12714559,12714560,356461503⟩,⟨6,12698414,12698415,356235250⟩,⟨4,12682309,12682310,356009428⟩,⟨8,12666246,12666247,355784034⟩,⟨4,12650223,12650224,355559068⟩,⟨24,12634240,12634241,355334528⟩,⟨4,12618298,12618299,355110413⟩,⟨4,12602396,12602397,354886721⟩,⟨8,12586534,12586535,354663452⟩,⟨6,12570711,12570712,354440603⟩,⟨2,12554929,12554930,354218174⟩,⟨16,12539186,12539187,353996163⟩,⟨4,12523483,12523484,353774569⟩,⟨18,12507819,12507820,353553391⟩,⟨6,12492194,12492195,353332627⟩,⟨4,12476607,12476608,353112276⟩,⟨4,12461060,12461061,352892337⟩,⟨12,12445552,12445553,352672808⟩,⟨8,12430082,12430083,352453689⟩,⟨8,12414650,12414651,352234977⟩,⟨4,12399257,12399258,352016672⟩,⟨8,12383902,12383903,351798773⟩,⟨2,12368585,12368586,351581277⟩,⟨20,12353306,12353307,351364185⟩] (by decide) (by decide) PrefixTable131.state_740 (by decide +kernel)

def LogCap : ℝ := (146465543922323/10935000000000 : ℝ)
def HCap : ℝ := LogCap+231/400

structure Caps (ell h : ℝ) (N : ℕ) : Prop where
  log_le : Real.log N ≤ ell
  harmonic_le : Harmonic N ≤ h

theorem log_cap {N : ℕ} (hN : 1≤N) (hhigh : N≤656184) : Real.log N≤LogCap := by
  have hh := PrefixLog131.log_endpoint_upper (by decide : 0<grid) state_810
    (by decide : 0<810) (by omega : 0<N) hhigh
  norm_num [grid,LogCap] at hh ⊢
  exact hh

theorem actual_caps {N : ℕ} (hN : 100000≤N) (hhigh : N≤656184) : Caps LogCap HCap N := by
  have hl := log_cap (by omega : 1≤N) hhigh
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  exact ⟨hl,by dsimp only [HCap];linarith only [hl,hh]⟩

def LocalLog (ell : ℝ) (j : ℕ) : ℝ := ell-RecoveryLocalization212.Lower j
def LocalCoeff (ell : ℝ) (j : ℕ) : ℝ :=
  102/25+2*(LocalLog ell j+1)+FrontierSum208.Polynomial (LocalLog ell j)
def GlobalCoeff (ell h : ℝ) : ℝ := 102/25+2*h+FrontierSum208.Polynomial ell
def A (h : ℝ) (r : ℕ) : ℝ := if r=0 then h+6279/50 else h+229/50
def W (h : ℝ) (r : ℕ) : ℝ := if r=0 then h else h+PreparationA r+(PreparationP r : ℝ)-1
def C (r : ℕ) : ℝ := if r=0 then 993 else 26+PreparationB r-(PreparationP r : ℝ)

theorem log_local {ell h : ℝ} {N L j : ℕ} (hc : Caps ell h N) (hL : 1≤L)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j) :
    Real.log L≤LocalLog ell j := by
  have hLp : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hd := RecoveryLocalization212.div_pos j
  have hm : (L : ℝ)*RecoveryLocalization212.Div j≤N := (le_div_iff₀ hd).mp hleft.le
  have hh := Real.log_le_log (mul_pos hLp hd) hm
  rw [Real.log_mul hLp.ne' hd.ne'] at hh
  have hb := RecoveryLocalization212.lower_log hj
  have ht := hc.log_le
  dsimp only [LocalLog]
  linarith only [hh,hb,ht]

theorem local_payment {ell h : ℝ} {N L j : ℕ} (hc : Caps ell h N) (hL : 1≤L)
    (hj : j≤7) (hleft : (L : ℝ)<(N : ℝ)/RecoveryLocalization212.Div j) :
    (102/25+2*Harmonic L+FrontierSum208.Polynomial (Real.log L))*(L : ℝ) ≤
      LocalCoeff ell j*L := by
  have hl := log_local hc hL hj hleft
  have hh := HarmonicAbel29.harmonic_le_one_add_log L
  have hp := ActualRecoveryChain208.polynomial_mono
    (Real.log_nonneg (by exact_mod_cast hL)) hl
  have h1 := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) L)
  have h2 := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) L)
  have h3 := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) L)
  dsimp only [LocalCoeff]
  nlinarith only [h1,h2,h3]
#print axioms state_810
#print axioms log_cap
#print axioms actual_caps
#print axioms log_local
#print axioms local_payment
end
end JSP233.RecoveryCaps213
