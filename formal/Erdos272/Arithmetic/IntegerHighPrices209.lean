import Erdos272.Arithmetic.SevenPrices208
namespace JSP233.IntegerHighPrices209
open ReciprocalPrice208 SevenPrices208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 200000
def M (w : Fin 11) : ℕ := [250,254,260,269,283,306,344,410,533,792,1432].getD w.val 0
def Lower (w : Fin 11) : ℕ := [705098,722829,757443,810885,897646,1049770,1327223,1886457,3190603,7051527,23074964].getD w.val 0
def Upper (w : Fin 11) : ℕ := [727351,762585,813981,902923,1054723,1328903,1890795,3200816,7055374,23102619,62443451].getD w.val 0
def BaseLevels (w : Fin 11) : ℕ := [12,12,12,12,12,13,13,13,14,15,16].getD w.val 0
def MaxIndex (w : Fin 11) : ℕ := [8,8,8,8,8,8,8,9,10,11,11].getD w.val 0
def K (w : Fin 11) (j : ℕ) : ℕ := M w*2^j/3
def Levels (w : Fin 11) (j : ℕ) : ℕ := BaseLevels w-j
def High (w : Fin 11) (j : ℕ) (n : ℝ) : ℝ :=
  Price (2/((K w j : ℝ)*((5*K w j/3 : ℕ) : ℝ)^2))
    (2303/(200*(K w j : ℝ))+(if j≤6 then 0 else Beta))
    ((7/2 : ℝ)*(Levels w j : ℝ)*19+142+(if j≤6 then ((2*M w*2^j : ℕ) : ℝ) else 0)) 0 n
theorem data_range (w : Fin 11) : 250≤M w ∧ 705098≤Lower w ∧ Upper w≤62443451 ∧ Lower w≤Upper w := by
  fin_cases w <;> norm_num [M,Lower,Upper]
theorem direct_budget (w : Fin 11) : 800*((M w-1)^2+142)<71*Lower w := by
  fin_cases w <;> norm_num [M,Lower]
theorem next_overlap (w : Fin 10) : Lower ⟨w.val+1,by omega⟩≤Upper ⟨w.val,by omega⟩+1 := by
  fin_cases w <;> norm_num [Lower,Upper]
theorem max_index_bound (w : Fin 11) : Upper w<11*M w*2^(MaxIndex w+1) := by
  fin_cases w <;> norm_num [Upper,M,MaxIndex]
theorem scale_index {N j : ℕ} (w : Fin 11) (hN : N≤Upper w) (hs : 11*M w*2^j≤N) : j≤MaxIndex w := by
  by_contra h
  have hp:=Nat.pow_le_pow_right (by decide : 1≤2) (show MaxIndex w+1≤j by omega)
  have hm:=Nat.mul_le_mul_left (11*M w) hp
  have hb:=max_index_bound w
  omega
theorem high_00 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (705098 : ℝ)≤n) (hh : n≤727351) : High ⟨0,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_01 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (722829 : ℝ)≤n) (hh : n≤762585) : High ⟨1,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_02 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (757443 : ℝ)≤n) (hh : n≤813981) : High ⟨2,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_03 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (810885 : ℝ)≤n) (hh : n≤902923) : High ⟨3,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_04 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (897646 : ℝ)≤n) (hh : n≤1054723) : High ⟨4,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_05 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (1049770 : ℝ)≤n) (hh : n≤1328903) : High ⟨5,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_06 (j : ℕ) (hj : 2≤j) (hu : j≤8)
    {n : ℝ} (hl : (1327223 : ℝ)≤n) (hh : n≤1890795) : High ⟨6,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_07 (j : ℕ) (hj : 2≤j) (hu : j≤9)
    {n : ℝ} (hl : (1886457 : ℝ)≤n) (hh : n≤3200816) : High ⟨7,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_08 (j : ℕ) (hj : 2≤j) (hu : j≤10)
    {n : ℝ} (hl : (3190603 : ℝ)≤n) (hh : n≤7055374) : High ⟨8,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_09 (j : ℕ) (hj : 2≤j) (hu : j≤11)
    {n : ℝ} (hl : (7051527 : ℝ)≤n) (hh : n≤23102619) : High ⟨9,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_10 (j : ℕ) (hj : 2≤j) (hu : j≤11)
    {n : ℝ} (hl : (23074964 : ℝ)≤n) (hh : n≤62443451) : High ⟨10,by decide⟩ j n≤Budget := by
  interval_cases j <;> unfold High <;> apply window (by norm_num) hl hh
  all_goals norm_num [K,Levels,M,Lower,Upper,BaseLevels,MaxIndex,Price,Budget,Beta]
theorem high_window (w : Fin 11) (j : ℕ) (hj : 2≤j) (hmax : j≤MaxIndex w)
    {n : ℝ} (hl : (Lower w : ℝ)≤n) (hu : n≤Upper w) : High w j n≤Budget := by
  fin_cases w
  · exact high_00 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_01 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_02 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_03 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_04 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_05 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_06 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_07 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_08 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_09 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
  · exact high_10 j hj (by norm_num [MaxIndex] at hmax;exact hmax) hl hu
theorem minimum_size (w : Fin 11) (j : ℕ) (hj : 2≤j) (hmax : j≤MaxIndex w) :
    0<K w j ∧ 3*K w j≤M w*2^j ∧ 1≤5*K w j/3 := by
  fin_cases w <;> norm_num [MaxIndex] at hmax <;> interval_cases j <;> norm_num [K,M]
theorem level_cutoff (w : Fin 11) (j : ℕ) (hj : 2≤j) (hmax : j≤MaxIndex w) :
    Upper w<3*K w j*2^(Levels w j) := by
  fin_cases w <;> norm_num [MaxIndex] at hmax <;> interval_cases j <;> norm_num [K,M,Upper,Levels,BaseLevels]
#print axioms high_window
#print axioms minimum_size
#print axioms level_cutoff
#print axioms direct_budget
#print axioms scale_index
end
end JSP233.IntegerHighPrices209
