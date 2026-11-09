module

public import Erdos272.Arithmetic.FastLookupBridge209
public import Erdos272.Arithmetic.SplitChecks209

@[expose] public section
namespace JSP233.FullCoverBlock209_001
open FastFullLookup209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked_41_32770 : MarkerSieve209.checkMultiples marked 41 (41 * 32770) 7962 = true := by
  decide +kernel
#print axioms checked_41_32770
theorem checked_43_2_part_0 : MarkerSieve209.checkMultiples marked 43 (43 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_43_2_part_0
theorem checked_43_2_part_8192 : MarkerSieve209.checkMultiples marked 43 (43 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_43_2_part_8192
theorem checked_43_2_part_16384 : MarkerSieve209.checkMultiples marked 43 (43 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_43_2_part_16384
theorem checked_43_2_part_24576 : MarkerSieve209.checkMultiples marked 43 (43 * 24578) 8192 = true := by
  decide +kernel
#print axioms checked_43_2_part_24576
theorem checked_43_2 : MarkerSieve209.checkMultiples marked 43 (43 * 2) 32768 = true := by
  exact (SplitChecks209.marked_join marked 43 (43 * 2) 8192 24576 checked_43_2_part_0 (SplitChecks209.marked_join marked 43 (43 * 8194) 8192 16384 checked_43_2_part_8192 (SplitChecks209.marked_join marked 43 (43 * 16386) 8192 8192 checked_43_2_part_16384 checked_43_2_part_24576)))
#print axioms checked_43_2
theorem checked_43_32770 : MarkerSieve209.checkMultiples marked 43 (43 * 32770) 6068 = true := by
  decide +kernel
#print axioms checked_43_32770
theorem checked_47_2_part_0 : MarkerSieve209.checkMultiples marked 47 (47 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_47_2_part_0
theorem checked_47_2_part_8192 : MarkerSieve209.checkMultiples marked 47 (47 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_47_2_part_8192
theorem checked_47_2_part_16384 : MarkerSieve209.checkMultiples marked 47 (47 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_47_2_part_16384
theorem checked_47_2_part_24576 : MarkerSieve209.checkMultiples marked 47 (47 * 24578) 8192 = true := by
  decide +kernel
#print axioms checked_47_2_part_24576
theorem checked_47_2 : MarkerSieve209.checkMultiples marked 47 (47 * 2) 32768 = true := by
  exact (SplitChecks209.marked_join marked 47 (47 * 2) 8192 24576 checked_47_2_part_0 (SplitChecks209.marked_join marked 47 (47 * 8194) 8192 16384 checked_47_2_part_8192 (SplitChecks209.marked_join marked 47 (47 * 16386) 8192 8192 checked_47_2_part_16384 checked_47_2_part_24576)))
#print axioms checked_47_2
theorem checked_47_32770 : MarkerSieve209.checkMultiples marked 47 (47 * 32770) 2762 = true := by
  decide +kernel
#print axioms checked_47_32770
theorem checked_53_2_part_0 : MarkerSieve209.checkMultiples marked 53 (53 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_53_2_part_0
theorem checked_53_2_part_8192 : MarkerSieve209.checkMultiples marked 53 (53 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_53_2_part_8192
theorem checked_53_2_part_16384 : MarkerSieve209.checkMultiples marked 53 (53 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_53_2_part_16384
theorem checked_53_2_part_24576 : MarkerSieve209.checkMultiples marked 53 (53 * 24578) 6932 = true := by
  decide +kernel
#print axioms checked_53_2_part_24576
theorem checked_53_2 : MarkerSieve209.checkMultiples marked 53 (53 * 2) 31508 = true := by
  exact (SplitChecks209.marked_join marked 53 (53 * 2) 8192 23316 checked_53_2_part_0 (SplitChecks209.marked_join marked 53 (53 * 8194) 8192 15124 checked_53_2_part_8192 (SplitChecks209.marked_join marked 53 (53 * 16386) 8192 6932 checked_53_2_part_16384 checked_53_2_part_24576)))
#print axioms checked_53_2
theorem checked_59_2_part_0 : MarkerSieve209.checkMultiples marked 59 (59 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_59_2_part_0
theorem checked_59_2_part_8192 : MarkerSieve209.checkMultiples marked 59 (59 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_59_2_part_8192
theorem checked_59_2_part_16384 : MarkerSieve209.checkMultiples marked 59 (59 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_59_2_part_16384
theorem checked_59_2_part_24576 : MarkerSieve209.checkMultiples marked 59 (59 * 24578) 3728 = true := by
  decide +kernel
#print axioms checked_59_2_part_24576
theorem checked_59_2 : MarkerSieve209.checkMultiples marked 59 (59 * 2) 28304 = true := by
  exact (SplitChecks209.marked_join marked 59 (59 * 2) 8192 20112 checked_59_2_part_0 (SplitChecks209.marked_join marked 59 (59 * 8194) 8192 11920 checked_59_2_part_8192 (SplitChecks209.marked_join marked 59 (59 * 16386) 8192 3728 checked_59_2_part_16384 checked_59_2_part_24576)))
#print axioms checked_59_2
theorem checked_61_2_part_0 : MarkerSieve209.checkMultiples marked 61 (61 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_61_2_part_0
theorem checked_61_2_part_8192 : MarkerSieve209.checkMultiples marked 61 (61 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_61_2_part_8192
theorem checked_61_2_part_16384 : MarkerSieve209.checkMultiples marked 61 (61 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_61_2_part_16384
theorem checked_61_2_part_24576 : MarkerSieve209.checkMultiples marked 61 (61 * 24578) 2800 = true := by
  decide +kernel
#print axioms checked_61_2_part_24576
theorem checked_61_2 : MarkerSieve209.checkMultiples marked 61 (61 * 2) 27376 = true := by
  exact (SplitChecks209.marked_join marked 61 (61 * 2) 8192 19184 checked_61_2_part_0 (SplitChecks209.marked_join marked 61 (61 * 8194) 8192 10992 checked_61_2_part_8192 (SplitChecks209.marked_join marked 61 (61 * 16386) 8192 2800 checked_61_2_part_16384 checked_61_2_part_24576)))
#print axioms checked_61_2
theorem checked_67_2_part_0 : MarkerSieve209.checkMultiples marked 67 (67 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_67_2_part_0
theorem checked_67_2_part_8192 : MarkerSieve209.checkMultiples marked 67 (67 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_67_2_part_8192
theorem checked_67_2_part_16384 : MarkerSieve209.checkMultiples marked 67 (67 * 16386) 8192 = true := by
  decide +kernel
#print axioms checked_67_2_part_16384
theorem checked_67_2_part_24576 : MarkerSieve209.checkMultiples marked 67 (67 * 24578) 348 = true := by
  decide +kernel
#print axioms checked_67_2_part_24576
theorem checked_67_2 : MarkerSieve209.checkMultiples marked 67 (67 * 2) 24924 = true := by
  exact (SplitChecks209.marked_join marked 67 (67 * 2) 8192 16732 checked_67_2_part_0 (SplitChecks209.marked_join marked 67 (67 * 8194) 8192 8540 checked_67_2_part_8192 (SplitChecks209.marked_join marked 67 (67 * 16386) 8192 348 checked_67_2_part_16384 checked_67_2_part_24576)))
#print axioms checked_67_2
theorem checked_71_2_part_0 : MarkerSieve209.checkMultiples marked 71 (71 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_71_2_part_0
theorem checked_71_2_part_8192 : MarkerSieve209.checkMultiples marked 71 (71 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_71_2_part_8192
theorem checked_71_2_part_16384 : MarkerSieve209.checkMultiples marked 71 (71 * 16386) 7136 = true := by
  decide +kernel
#print axioms checked_71_2_part_16384
theorem checked_71_2 : MarkerSieve209.checkMultiples marked 71 (71 * 2) 23520 = true := by
  exact (SplitChecks209.marked_join marked 71 (71 * 2) 8192 15328 checked_71_2_part_0 (SplitChecks209.marked_join marked 71 (71 * 8194) 8192 7136 checked_71_2_part_8192 checked_71_2_part_16384))
#print axioms checked_71_2
theorem checked_73_2_part_0 : MarkerSieve209.checkMultiples marked 73 (73 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_73_2_part_0
theorem checked_73_2_part_8192 : MarkerSieve209.checkMultiples marked 73 (73 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_73_2_part_8192
theorem checked_73_2_part_16384 : MarkerSieve209.checkMultiples marked 73 (73 * 16386) 6491 = true := by
  decide +kernel
#print axioms checked_73_2_part_16384
theorem checked_73_2 : MarkerSieve209.checkMultiples marked 73 (73 * 2) 22875 = true := by
  exact (SplitChecks209.marked_join marked 73 (73 * 2) 8192 14683 checked_73_2_part_0 (SplitChecks209.marked_join marked 73 (73 * 8194) 8192 6491 checked_73_2_part_8192 checked_73_2_part_16384))
#print axioms checked_73_2
theorem checked_79_2_part_0 : MarkerSieve209.checkMultiples marked 79 (79 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_79_2_part_0
theorem checked_79_2_part_8192 : MarkerSieve209.checkMultiples marked 79 (79 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_79_2_part_8192
theorem checked_79_2_part_16384 : MarkerSieve209.checkMultiples marked 79 (79 * 16386) 4754 = true := by
  decide +kernel
#print axioms checked_79_2_part_16384
theorem checked_79_2 : MarkerSieve209.checkMultiples marked 79 (79 * 2) 21138 = true := by
  exact (SplitChecks209.marked_join marked 79 (79 * 2) 8192 12946 checked_79_2_part_0 (SplitChecks209.marked_join marked 79 (79 * 8194) 8192 4754 checked_79_2_part_8192 checked_79_2_part_16384))
#print axioms checked_79_2
theorem checked_83_2_part_0 : MarkerSieve209.checkMultiples marked 83 (83 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_83_2_part_0
theorem checked_83_2_part_8192 : MarkerSieve209.checkMultiples marked 83 (83 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_83_2_part_8192
theorem checked_83_2_part_16384 : MarkerSieve209.checkMultiples marked 83 (83 * 16386) 3735 = true := by
  decide +kernel
#print axioms checked_83_2_part_16384
theorem checked_83_2 : MarkerSieve209.checkMultiples marked 83 (83 * 2) 20119 = true := by
  exact (SplitChecks209.marked_join marked 83 (83 * 2) 8192 11927 checked_83_2_part_0 (SplitChecks209.marked_join marked 83 (83 * 8194) 8192 3735 checked_83_2_part_8192 checked_83_2_part_16384))
#print axioms checked_83_2
theorem checked_89_2_part_0 : MarkerSieve209.checkMultiples marked 89 (89 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_89_2_part_0
theorem checked_89_2_part_8192 : MarkerSieve209.checkMultiples marked 89 (89 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_89_2_part_8192
theorem checked_89_2_part_16384 : MarkerSieve209.checkMultiples marked 89 (89 * 16386) 2379 = true := by
  decide +kernel
#print axioms checked_89_2_part_16384
theorem checked_89_2 : MarkerSieve209.checkMultiples marked 89 (89 * 2) 18763 = true := by
  exact (SplitChecks209.marked_join marked 89 (89 * 2) 8192 10571 checked_89_2_part_0 (SplitChecks209.marked_join marked 89 (89 * 8194) 8192 2379 checked_89_2_part_8192 checked_89_2_part_16384))
#print axioms checked_89_2
theorem checked_97_2_part_0 : MarkerSieve209.checkMultiples marked 97 (97 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_97_2_part_0
theorem checked_97_2_part_8192 : MarkerSieve209.checkMultiples marked 97 (97 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_97_2_part_8192
theorem checked_97_2_part_16384 : MarkerSieve209.checkMultiples marked 97 (97 * 16386) 831 = true := by
  decide +kernel
#print axioms checked_97_2_part_16384
theorem checked_97_2 : MarkerSieve209.checkMultiples marked 97 (97 * 2) 17215 = true := by
  exact (SplitChecks209.marked_join marked 97 (97 * 2) 8192 9023 checked_97_2_part_0 (SplitChecks209.marked_join marked 97 (97 * 8194) 8192 831 checked_97_2_part_8192 checked_97_2_part_16384))
#print axioms checked_97_2
theorem checked_101_2_part_0 : MarkerSieve209.checkMultiples marked 101 (101 * 2) 8192 = true := by
  decide +kernel
#print axioms checked_101_2_part_0
theorem checked_101_2_part_8192 : MarkerSieve209.checkMultiples marked 101 (101 * 8194) 8192 = true := by
  decide +kernel
#print axioms checked_101_2_part_8192
theorem checked_101_2_part_16384 : MarkerSieve209.checkMultiples marked 101 (101 * 16386) 149 = true := by
  decide +kernel
#print axioms checked_101_2_part_16384
theorem checked_101_2 : MarkerSieve209.checkMultiples marked 101 (101 * 2) 16533 = true := by
  exact (SplitChecks209.marked_join marked 101 (101 * 2) 8192 8341 checked_101_2_part_0 (SplitChecks209.marked_join marked 101 (101 * 8194) 8192 149 checked_101_2_part_8192 checked_101_2_part_16384))
#print axioms checked_101_2
end JSP233.FullCoverBlock209_001
