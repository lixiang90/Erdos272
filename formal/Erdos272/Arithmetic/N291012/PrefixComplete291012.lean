module

public import Erdos272.Arithmetic.N291012.PrefixCalibration291012
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G00
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G01
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G02
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G03
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G04
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G05
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G06
public import Erdos272.Arithmetic.N291012.PrefixRecurrence291012G07
public import Erdos272.Arithmetic.N291012.PrefixTableSound291012

@[expose] public section

namespace JSP233.PrefixComplete291012
open PrefixData291012 PrefixTableSound291012 SourceMoment291012
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem all_recurrences {n : ℕ} (hn : n < 29435) :
    p (n+1) = p n + FastDecode208.phi n ∧ q (n+1) = q n + n * FastDecode208.phi n := by
  have hblock : n / 256 < 115 := by omega
  interval_cases hb : n / 256
  · exact check_sound PrefixRecurrence291012G00.checked_0 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_256 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_512 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_768 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_1024 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_1280 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_1536 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_1792 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_2048 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_2304 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_2560 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_2816 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_3072 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_3328 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_3584 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G00.checked_3840 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_4096 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_4352 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_4608 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_4864 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_5120 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_5376 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_5632 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_5888 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_6144 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_6400 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_6656 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_6912 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_7168 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_7424 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_7680 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G01.checked_7936 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_8192 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_8448 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_8704 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_8960 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_9216 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_9472 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_9728 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_9984 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_10240 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_10496 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_10752 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_11008 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_11264 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_11520 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_11776 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G02.checked_12032 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_12288 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_12544 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_12800 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_13056 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_13312 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_13568 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_13824 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_14080 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_14336 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_14592 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_14848 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_15104 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_15360 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_15616 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_15872 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G03.checked_16128 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_16384 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_16640 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_16896 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_17152 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_17408 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_17664 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_17920 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_18176 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_18432 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_18688 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_18944 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_19200 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_19456 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_19712 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_19968 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G04.checked_20224 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_20480 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_20736 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_20992 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_21248 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_21504 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_21760 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_22016 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_22272 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_22528 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_22784 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_23040 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_23296 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_23552 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_23808 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_24064 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G05.checked_24320 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_24576 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_24832 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_25088 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_25344 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_25600 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_25856 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_26112 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_26368 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_26624 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_26880 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_27136 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_27392 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_27648 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_27904 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_28160 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G06.checked_28416 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G07.checked_28672 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G07.checked_28928 (by omega) (by omega)
  · exact check_sound PrefixRecurrence291012G07.checked_29184 (by omega) (by omega)

theorem table_correct : ∀ n, n ≤ 29435 →
    p n = Prefix Nat.totient n ∧ q n = Moment Nat.totient n :=
  recurrence_correct (by decide) PrefixCalibration291012.p_zero PrefixCalibration291012.q_zero
    (fun _ hn => all_recurrences hn)

#print axioms all_recurrences
#print axioms table_correct
end JSP233.PrefixComplete291012
