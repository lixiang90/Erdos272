import Erdos272.Arithmetic.ReciprocalPrice208
import Erdos272.Arithmetic.APCoupling208

/-! Exact continuous seven-price arithmetic for the last mathematical window.
These constants are kernel checked as rational numbers. The actual source and
cleanup bounds that justify their use for a family remain separate theorems. -/
namespace JSP233.SevenPrices208
open ReciprocalPrice208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Budget : ℝ := 71 / 800 - 1 / 10000000000
def Loss : ℝ := 13863 / 100
def Beta : ℝ := 21 / 242

def G242 : ℝ := (1 / 8681676 : ℝ)
def U242 : ℝ := (4651284248633737 / 723473000000000000 : ℝ)
def Eta242 : ℝ := (1603 / 1 : ℝ)
def Light242 : ℝ := (18407980876177928 / 723473 : ℝ)
def G243 : ℝ := (1 / 8809656 : ℝ)
def U243 : ℝ := (939993172754907 / 146827600000000000 : ℝ)
def Eta243 : ℝ := (1602 / 1 : ℝ)
def Light243 : ℝ := (18651263127496843 / 734138 : ℝ)
def UniformG : ℝ := (1195 / 10173442356 : ℝ)
def UniformU : ℝ := (79027729043351413 / 1251161250000000000 : ℝ)
def UniformEta : ℝ := (758 / 1 : ℝ)
def Single (n : ℝ) : ℝ := Price (0) (0) (57841+Loss) ((13968602 / 1 : ℝ)) n
def Multiple (n : ℝ) : ℝ := Price (0) (0) (57840+Loss) ((13958720 / 1 : ℝ)) n
def Whole (n : ℝ) : ℝ := Price (APCoupling208.Kappa*G242) (U242) (Eta242+Loss) (-Light242) n
def RootExact (n : ℝ) : ℝ := Price (APCoupling208.Kappa*G242) (U242) (Eta242+242+Loss) (-Light242) n
def RootTail (n : ℝ) : ℝ := Price (APCoupling208.Kappa*G243) (U243) (Eta243+483+Loss) (-Light243) n
def RootTwo (n : ℝ) : ℝ := Price (UniformG/8) (UniformU/2) (968+UniformEta+Loss) (0) n
def RootLow2 (n : ℝ) : ℝ := Price (UniformG/8) (UniformU/2) (968+UniformEta+Loss) ((468512 / 1 : ℝ)) n
def RootLow4 (n : ℝ) : ℝ := Price (UniformG/64) (UniformU/4) (1936+UniformEta+Loss) ((1874048 / 1 : ℝ)) n
def RootLow8 (n : ℝ) : ℝ := Price (UniformG/512) (UniformU/8) (3872+UniformEta+Loss) ((7496192 / 1 : ℝ)) n
def RootLow16 (n : ℝ) : ℝ := Price (UniformG/4096) (UniformU/16) (7744+UniformEta+Loss) ((29984768 / 1 : ℝ)) n
def RootLow32 (n : ℝ) : ℝ := Price (UniformG/32768) (UniformU/32) (15488+UniformEta+Loss) ((119939072 / 1 : ℝ)) n
def RootLow64 (n : ℝ) : ℝ := Price (UniformG/262144) (UniformU/64) (30976+UniformEta+Loss) ((479756288 / 1 : ℝ)) n
def RootLow128 (n : ℝ) : ℝ := Price (UniformG/2097152) (UniformU/128) (61952+UniformEta+Loss) ((1919025152 / 1 : ℝ)) n
def RootCap128 (n : ℝ) : ℝ := Price (UniformG/2097152) (Beta+UniformU/128) (UniformEta+Loss) (0) n
def RootCap256 (n : ℝ) : ℝ := Price (UniformG/16777216) (Beta+UniformU/256) (UniformEta+Loss) (0) n

theorem single_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    Single n ≤ Budget := by
  unfold Single
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem multiple_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    Multiple n ≤ Budget := by
  unfold Multiple
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem whole_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    Whole n ≤ Budget := by
  unfold Whole
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootexact_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootExact n ≤ Budget := by
  unfold RootExact
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem roottail_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootTail n ≤ Budget := by
  unfold RootTail
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem roottwo_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootTwo n ≤ Budget := by
  unfold RootTwo
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow2_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow2 n ≤ Budget := by
  unfold RootLow2
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow4_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow4 n ≤ Budget := by
  unfold RootLow4
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow8_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow8 n ≤ Budget := by
  unfold RootLow8
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow16_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow16 n ≤ Budget := by
  unfold RootLow16
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow32_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow32 n ≤ Budget := by
  unfold RootLow32
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow64_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootLow64 n ≤ Budget := by
  unfold RootLow64
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootlow128_window {n : ℝ} (hl : 681472 ≤ n) (hu : n ≤ 705097) :
    RootLow128 n ≤ Budget := by
  unfold RootLow128
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootcap128_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 681472) :
    RootCap128 n ≤ Budget := by
  unfold RootCap128
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

theorem rootcap256_window {n : ℝ} (hl : 659912 ≤ n) (hu : n ≤ 705097) :
    RootCap256 n ≤ Budget := by
  unfold RootCap256
  apply window (by norm_num) hl hu
  all_goals norm_num [Price, Budget, Loss, Beta, APCoupling208.Kappa, G242, U242, Eta242, Light242, G243, U243, Eta243, Light243, UniformG, UniformU, UniformEta]

#print axioms single_window
#print axioms rootexact_window
#print axioms rootlow128_window
#print axioms rootcap128_window
end
end JSP233.SevenPrices208
